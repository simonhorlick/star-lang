import {
  Ann,
  Star,
  Pi,
  Self,
  Par,
  App,
  Abs,
  Ref,
  Case,
  Branch,
  Origin,
  AbsI,
  Identifier,
  If,
  Let,
  identifier2str,
  Syntax,
  Label,
  Term,
  Var,
  Expression,
  Cons,
  Nil,
  IntMul,
  IntPlus,
  IntSub,
  Comp,
  IntNeg,
  IntDiv,
  Idx,
  Cat,
  Gt,
  Lt,
  Gte,
  Lte,
  And,
  Neq,
  Or,
  Eq,
} from "./pratt";
import { Context, addTermToCtx } from "./context";
import {
  ADT,
  ASTNode,
  Classification,
  Constructor,
  Def,
  Def2,
  File,
  Origin2,
  classifyParams,
  typeArguments,
} from "./ast";
import { desugarExpression, Ann as Ann2 } from "./sugar";
import { TypecheckError } from "./typecheck";

const reverse = <T>(l: Array<T>) => [...l].reverse();

const wrapOrigin = (
  term: Expression,
  from: Origin | Identifier
): Expression => {
  if (from._ == "orig") {
    return Origin(from.start, from.end, term);
  } else {
    return term;
  }
};

// validateADT checks that an ADT declaration is well-formed, throwing a
// TypecheckError if it isn't.
export const validateADT = (adt: ADT): void => {
  const cls = classifyParams(adt);
  if (cls.indices.length == 0) {
    return;
  }
  const typeName = identifier2str(adt.name);
  for (const con of adt.constructors) {
    // The indices of a type aren't in scope in its constructors, so a
    // constructor can only return the type by supplying values for them.
    if (con.typ === null) {
      const origin = con.name._ == "orig" ? con.name : adt.name;
      throw TypecheckError(
        `constructor ${identifier2str(con.name)} must declare its return type ` +
          `as ${typeName} is an indexed type (${cls.indices
            .map((i) => i.name)
            .join(", ")})`,
        origin._ == "orig" ? origin.start : 0,
        origin._ == "orig" ? origin.end : 0
      );
    }
  }
};

const processNode = (n: ASTNode, errors: TypecheckError[]): ASTNode[] => {
  switch (n._) {
    case "adt": {
      // Generates type definition and constructors for an ADT.
      const adt = ADT(n.name, n.params, n.constructors);
      try {
        validateADT(adt);
      } catch (e) {
        if ((e as TypecheckError)._ == "typecheckerror") {
          errors.push(e as TypecheckError);
          return [];
        }
        throw e;
      }
      const td = buildType(adt);
      const defs = n.constructors.map((con, i) => {
        return Def(
          identifier2str(con.name),
          // This is used for tooling to be able to provide jump-to-definition
          // for type constructors.
          Ann(
            wrapOrigin(GenerateConstructorTerm(adt, i), con.name),
            GenerateConstructorType(adt, i)
          )
        );
      });
      return [td].concat(defs);
    }
    default:
      return [n];
  }
};

// Build the nth constructor function for a datatype with the given
// constructors. The nth constructor just returns the value of the nth
// argument.
export const buildConstructor = (
  constructors: string[],
  constructorIndex: number
) => {
  /*
      constructor1 : T = (P) (c1) (c2) ... (cN) c1
      constructor2 : T = (P) (c1) (c2) ... (cN) c2
      ...
      constructorN : T = (P) (c1) (c2) ... (cN) cN
    */

  const rc = reverse(constructors);

  const wrapN = (n: number): Abs | Var => {
    if (n == 0) {
      return Var(
        `${constructors[constructorIndex]}`,
        constructors.length - constructorIndex - 1
      );
    }
    return Abs(`${rc[n - 1]}`, wrapN(n - 1));
  };

  return Abs("P", wrapN(constructors.length));
};

// Build the type of the branch for one constructor in the eliminator:
//
//   Πa:A. Πb:B. P(constructorN(p1,...,pm,a,b))
//
// where p1...pm are the parameters of the type. For indexed types the motive
// is also applied to the index values from the constructor's return type:
//
//   Πa:A. Πb:B. P(i1,...,ik,constructorN(p1,...,pm,a,b))
const buildTypeArgSignature = (
  cls: Classification,
  constructor: Constructor,
  acc: Term
): Term => {
  const constructorName = identifier2str(constructor.name);
  const args = constructor.args;

  // constructorN(p1,...,pm,a,b,...): the constructor applied to the parameters
  // of the type, then to its own arguments.
  const cN = args.reduce<Term>(
    (acc, curr) => App(acc, Par(curr.name)),
    cls.parameters.reduce<Term>(
      (acc, curr) => App(acc, Par(curr.name)),
      Ref(constructorName)
    )
  );

  // The index values come from the constructor's return type, so for
  // vext(n Nat, ...) : VectBool(succ(n)) the index value is succ(n). A
  // constructor without a return type can only exist in a type without
  // indices.
  const indexValues =
    constructor.typ !== null
      ? (typeArguments(constructor.typ).filter(
          (_, i) => cls.isIndex[i]
        ) as Term[])
      : [];

  // P(i1,...,ik,constructorN(...))
  const PcN = App(
    indexValues.reduce<Term>((acc, index) => App(acc, index), Par("P")),
    cN
  );

  // Build Πa:A. Πb:B. ... P(...)
  const Pis = reverse(args).reduce(
    (acc: Term, curr) => Pi(curr.name, curr.type, acc),
    PcN
  );

  return Pi("", Pis, acc);
};

/*
    T : Type = ιt. ΠP:T→*.
    P(constructor1) →
    P(constructor2) →
    ...
    P(constructorN) →
    P(t)

    For a type with parameters p1..pm and indices i1..ik (see classifyParams):

    T : Π(p1:P1) ... Π(ik:Ik) ★
      = λp1 ... λik ιt. ΠP:(Πi1:I1 ... Πik:Ik Πx:T(p1,...,ik) ★).
        (Πargs1. P(index values of constructor1, constructor1(p1,...,pm,args1))) →
        ...
        (ΠargsN. P(index values of constructorN, constructorN(p1,...,pm,argsN))) →
        P(i1,...,ik,t)

    For example, VectBool(sz Nat) has a single index sz:

    VectBool : Πsz:Nat ★
      = λsz ιt. ΠP:(Πsz:Nat Πx:VectBool(sz) ★).
        P(zero,vnil) →
        (Πn:Nat Πhead:Bool Πtail:VectBool(n) P(succ(n),vext(n,head,tail))) →
        P(sz,t)

    and Equal(A *, a A, b A) has parameters A and a and index b:

    Equal : ΠA:★ Πa:A Πb:A ★
      = λA λa λb ιt. ΠP:(Πb:A Πx:Equal(A,a,b) ★).
        P(a,refl(A,a)) →
        P(b,t)
  */
export const buildType = (adt: ADT): Def => {
  const cls = classifyParams(adt);
  const typeName = identifier2str(adt.name);

  // T(h1,...,hn): the type applied to every header variable.
  const typ = adt.params.reduce<Term>(
    (acc, paramN) => App(acc, Par(paramN.name)),
    Ref(typeName)
  );

  // The motive abstracts over the indices and the value being eliminated:
  //   Πi1:I1 ... Πik:Ik Πx:T(h1,...,hn) ★
  // For a type without indices this is simply T(h1,...,hn) → ★.
  const motiveType = reverse(cls.indices).reduce<Term>(
    (acc, index) => Pi(index.name, index.type as Term, acc),
    Pi(cls.indices.length > 0 ? "x" : "", typ, Star())
  );

  // P(i1,...,ik,t)
  const Pt = App(
    cls.indices.reduce<Term>(
      (acc, index) => App(acc, Par(index.name)),
      Par("P")
    ),
    Par("t")
  );

  const self = // ιt.
    Self(
      "t",
      Pi(
        "P",
        motiveType,
        // P(constructor1) → (Πa:A. P(constructor2(a))) → ... P(constructorN) → P(t)
        reverse(adt.constructors).reduce<Term>(
          (acc, constructorN) => buildTypeArgSignature(cls, constructorN, acc),
          Pt
        )
      )
    );

  return Def(
    typeName,
    // This is used for tooling to be able to provide jump-to-definition for
    // types. `name` contains the source location where the constructor was
    // defined, so any refs that mention this constructor can follow this origin
    // back to the source text.
    Ann(
      wrapOrigin(
        processPars(
          adt.params.reduceRight<Term>(
            (acc, paramN) => Abs(paramN.name, acc),
            self
          ),
          []
        ),
        adt.name
      ),
      // Ensure that type-constructors such as Maybe have type arguments here.
      // Maybe does not have type * - instead it has type A->*.
      adt.params.reduceRight<Term>(
        (acc, curr) => Pi(curr.name, curr.type, acc),
        Star()
      )
    )
  );
};

// processADTs replaces every ADT declaration in the file with the generated
// type definition and constructor functions. Declarations that are not
// well-formed are dropped and the error is appended to errors.
export const processADTs = (
  f: File,
  errors: TypecheckError[] = []
): File => {
  return {
    _: "file",
    content: f.content.flatMap((node) => processNode(node, errors)),
  };
};

// TODO: Re-think this. There's a lot of places where we're doing thing kind of
// thing.
export const desugarTerm = (
  t: Expression,
  ann: Expression | undefined,
  ctx: Context
): Expression => {
  switch (t._) {
    case "ann":
      const desugaredType = desugarTerm(t.type, undefined, ctx);
      return Ann(desugarTerm(t.term, desugaredType, ctx), desugaredType);
    case "app":
      return App(
        desugarTerm(t.func, undefined, ctx),
        desugarTerm(t.arg, undefined, ctx)
      );
    case "lam":
      // The type in this context is not important so just set it as *.
      return AbsI(
        t.name,
        desugarTerm(
          t.body,
          undefined,
          addTermToCtx(ctx, identifier2str(t.name), Star())
        )
      );
    case "par":
      for (let i = 0; i < ctx.length; i++) {
        const binding = ctx[ctx.length - i - 1];
        if (binding.name == t.name) {
          return Var(binding.name, i);
        }
      }
      throw "undefined variable " + t.name;
    case "pi":
      return Pi(
        t.name,
        desugarTerm(t.from, undefined, ctx),
        desugarTerm(t.body, undefined, addTermToCtx(ctx, t.name, Star()))
      );
    case "self":
      return Self(
        t.name,
        desugarTerm(t.body, undefined, addTermToCtx(ctx, t.name, Star()))
      );
    case "case":
      // We can't desugar case expressions at this point because we need to
      // infer the type of the term we're destructuring. This can only happen
      // while we're typechecking.
      return Case(
        desugarTerm(t.name, undefined, ctx),
        t.branches.map((b) =>
          Branch(b.constructor, desugarTerm(b.term, undefined, ctx))
        )
      );
    case "let":
      // the type of the newly created bound variable is required when adding it
      // to the context, so we must defer processing this let statement to the
      // typechecking stage.
      return Let(
        t.name,
        desugarTerm(t.expr, undefined, ctx),
        desugarTerm(
          t.body,
          undefined,
          addTermToCtx(ctx, identifier2str(t.name), Star())
        )
      );

    case "if":
      /*
        func F:Bool->* = λb if b then Bool else Nat
        func i:(b Bool)->F(b) = λb if b then false else 2
        // desugars to
        //   i:(b Bool)->F(b) = λb (case b of false -> 2 ; true -> false):F(b)
      */
      // FIXME: let b = t.condition; case b ...
      // FIXME: This is going to give horrible error messages in the situation
      //  that b is not a Bool.
      return Case(desugarTerm(t.condition, undefined, ctx), [
        Branch(Identifier("false"), desugarTerm(t.falseBranch, undefined, ctx)),
        Branch(Identifier("true"), desugarTerm(t.trueBranch, undefined, ctx)),
      ]);
    case "ref":
      // At this point we're still unsure whether this node is a Var or a Ref.
      // So look it up first and if a Var exists then use that.
      for (let i = 0; i < ctx.length; i++) {
        const binding = ctx[ctx.length - i - 1];
        if (binding.name == t.name) {
          return Var(binding.name, i);
        }
      }
      return t;
    case "star":
    case "var":
    case "id":
    case "key":
    case "hole":
      return t;
    case "int": {
      let term: Term = Ref("zero");
      for (let i = 0; i < t.num; i++) {
        term = App(Ref("succ"), term);
      }
      return term;
    }
    case "str": {
      // TODO: How can we keep this as a string literal rather than expanding
      // into scons terms?
      // - Retain the StringLit term, if it's ever applied then reduce it
      //   lazily.
      return t;
      // return stringLiteralToTerm(t.str);
    }
    case "orig":
      return Origin(t.start, t.end, desugarTerm(t.child, ann, ctx));
    case "syn":
      return Syntax(t.syntax, desugarTerm(t.child, ann, ctx));
    case "label":
      return Label(t.label, desugarTerm(t.child, ann, ctx));
    case "err":
      return t;
    // case "rel":
    //   throw "desugarTerm: unexpected Rel";
    case "cons":
      return Cons(
        desugarTerm(t.head, undefined, ctx),
        desugarTerm(t.tail, undefined, ctx)
      );
    case "nil":
      return t;
    case "add":
      return IntPlus(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "sub":
      return IntSub(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "mul":
      return IntMul(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "div":
      return IntDiv(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "neg":
      return IntNeg(desugarTerm(t.exp, undefined, ctx));
    case "comp":
      return Comp(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "idx":
      return Idx(
        desugarTerm(t.arr, undefined, ctx),
        desugarTerm(t.idx, undefined, ctx)
      );
    case "cat":
      return Cat(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "gt":
      return Gt(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "lt":
      return Lt(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "gte":
      return Gte(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "lte":
      return Lte(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "eq":
      return Eq(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "neq":
      return Neq(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "and":
      return And(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    case "or":
      return Or(
        desugarTerm(t.lhs, undefined, ctx),
        desugarTerm(t.rhs, undefined, ctx)
      );
    // default:
    //   throw new Error(`desugarTerm: unexpected ${t._}`);
  }
};

export const desugar = (def: Def, start?: number, end?: number): Def2 => {
  return Def2(
    def.name,
    desugarExpression(desugarTerm(def.term, undefined, [])) as Ann2,
    start,
    end
  );
};

// processPars removes all Par nodes from the tree t.
export const processPars = (t: Expression, ctx: Context): Expression => {
  switch (t._) {
    case "ann":
      return Ann(processPars(t.term, ctx), processPars(t.type, ctx));
    case "app":
      return App(processPars(t.func, ctx), processPars(t.arg, ctx));
    case "lam":
      // The type in this context is not important so just set it as *.
      return AbsI(
        t.name,
        processPars(t.body, addTermToCtx(ctx, identifier2str(t.name), Star()))
      );
    case "par":
      for (let i = 0; i < ctx.length; i++) {
        const binding = ctx[ctx.length - i - 1];
        if (binding.name == t.name) {
          return Var(binding.name, i);
        }
      }
      throw "undefined variable " + t.name;
    case "pi":
      return Pi(
        t.name,
        processPars(t.from, ctx),
        processPars(t.body, addTermToCtx(ctx, t.name, Star()))
      );
    case "self":
      return Self(
        t.name,
        processPars(t.body, addTermToCtx(ctx, t.name, Star()))
      );
    case "orig":
      return Origin(t.start, t.end, processPars(t.child, ctx));
    case "syn":
      return Syntax(t.syntax, processPars(t.child, ctx));
    case "case":
      return Case(
        processPars(t.name, ctx),
        t.branches.map((branch) =>
          Branch(branch.constructor, processPars(branch.term, ctx))
        )
      );
    case "let":
      return Let(
        t.name,
        processPars(t.expr, ctx),
        processPars(t.body, addTermToCtx(ctx, identifier2str(t.name), Star()))
      );

    case "if":
      return If(
        processPars(t.condition, ctx),
        processPars(t.trueBranch, ctx),
        processPars(t.falseBranch, ctx)
      );
    case "label":
      return Label(t.label, processPars(t.child, ctx));
    case "ref":
    case "star":
    case "var":
    case "id":
    case "key":
    case "hole":
    case "int":
    case "str":
    case "err":
      return t;
    // case "rel":
    //   throw "processPars: unexpected Rel";
    default:
      throw new Error(`processPars: unexpected ${t._}`);
  }
};

export const GenerateConstructorType = (adt: ADT, i: number): Expression => {
  // nil : (T *) → List(T)
  // cons : (T *) → (head T) → (tail List(T)) → List(T)

  // For indexed types the constructor's explicit return type is used, and
  // only the parameters of the type are prepended:
  // vnil : VectBool(zero)
  // vext : (n:Nat) → (head:Bool) → (tail:VectBool(n)) → VectBool(succ(n))
  // refl : (A:*) → (a:A) → Equal(A,a,a)
  const cls = classifyParams(adt);
  const constructor = adt.constructors[i];

  const returnType: Term =
    constructor.typ !== null
      ? (constructor.typ as Term)
      : adt.params.reduce<Term>(
          (acc, curr) => App(acc, Par(curr.name)),
          Ref(identifier2str(adt.name))
        );

  // For example
  // (head T) → (tail List(T)) → List(T)
  const withArgs = constructor.args.reduceRight<Term>(
    (acc, curr) => Pi(curr.name, curr.type as Term, acc),
    returnType
  );

  // Prepend the parameters of the type.
  const withParams = cls.parameters.reduceRight<Term>(
    (acc, curr) => Pi(curr.name, curr.type as Term, acc),
    withArgs
  );

  return processPars(withParams, []);
};

export const GenerateConstructorTerm = (adt: ADT, i: number): Expression => {
  /*
    cons = <A> (head) (tail) <P> (nil) (cons) cons(head)(tail)
    nil = <A> <P> (nil) (cons) nil

    For indexed types the parameters of the type are abstracted but the
    indices are not, as they are determined by the constructor:
    vnil = <P> (vnil) (vext) vnil
    vext = (n) (head) (tail) <P> (vnil) (vext) vext(n)(head)(tail)
    refl = <A> (a) <P> (refl) refl
  */
  const cls = classifyParams(adt);
  const constructors = adt.constructors;
  const constructor = constructors[i];

  // Working from right to left.

  // Apply all arguments to the constructor
  const apps = constructor.args.reduce<Term>(
    (acc, curr) => App(acc, Par(curr.name)),
    Par(identifier2str(constructor.name))
  );

  // Abstract constructors
  const absConstructors = constructors.reduceRight<Term>(
    // Passing curr.name to AbsI here will expose the source locations of the
    // type constructors to tooling, i.e. the constructor `true` would have
    // a span for `true:P(true)`.
    (acc, curr) => Abs(identifier2str(curr.name), acc),
    apps
  );

  // Abstract P
  const absP = Abs("P", absConstructors);

  // Abstract arguments
  const absArgs = constructor.args.reduceRight<Term>(
    (acc, curr) => Abs(curr.name, acc),
    absP
  );

  // Abstract the parameters of the type.
  const absParams = cls.parameters.reduceRight<Term>(
    (acc, curr) => Abs(curr.name, acc),
    absArgs
  );

  return processPars(absParams, []);
};
