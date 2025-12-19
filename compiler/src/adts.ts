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
  Argument,
  ASTNode,
  Constructor,
  Def,
  Def2,
  File,
  Origin2,
} from "./ast";
import { desugarExpression, Ann as Ann2 } from "./sugar";

const reverse = <T>(l: Array<T>) => [...l].reverse();

// Extract the index arguments from a constructor's return type
// For VectBool(zero), returns [zero]
// For VectBool(succ(n)), returns [succ(n)]
const extractIndices = (returnType: Expression): Term[] => {
  const indices: Term[] = [];
  let current = returnType;

  // Walk down the App chain to collect all the arguments
  while (current._ === "app") {
    indices.unshift(current.arg as Term);
    current = current.func;
  }

  return indices;
};

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

const processNode = (n: ASTNode): ASTNode[] => {
  switch (n._) {
    case "adt":
      // Generates type definition and constructors for an ADT.
      const adt = ADT(n.name, n.params, n.constructors);
      const td = buildType(adt);
      const defs = n.constructors.map((con, i) => {
        return Def(
          identifier2str(con.name),
          // This is used for tooling to be able to provide jump-to-definition
          // for type constructors.
          Ann(
            wrapOrigin(
              GenerateConstructorTerm(n.params, n.constructors, i),
              con.name
            ),
            GenerateConstructorType(
              identifier2str(n.name),
              n.params,
              n.constructors[i]
            )
          )
        );
      });
      return [td].concat(defs);
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

// a1 → a2 → P(constructor1)
// For indexed types: a1 → a2 → P(index)(constructor1)
const buildTypeArgSignature = (
  parameters: Argument[],
  constructor: Constructor,
  acc: Term
): Term => {
  // Build the syntax tree for the type Πa:A. Πb:B. P(constructorN(a,b)).
  // For indexed types: Πa:A. Πb:B. P(index)(constructorN(a,b))

  const constructorName = identifier2str(constructor.name);
  const args = constructor.args;
  const isIndexed = constructor.typ !== null;

  // Apply all type parameters to the constructor first (for non-indexed types).
  // For indexed types, don't apply params since they're indices, not type params.
  const cNParams = isIndexed
    ? Ref(constructorName)
    : parameters.reduce(
        (acc: Term, curr) =>
          // We need to add args.length as there will be that many Pi nodes wrapping this.
          App(acc, Par(curr.name)),
        Ref(constructorName)
      );

  // Build constructorN(a,b,...) which is
  //   App(App(Ref(constructor), Var(a)), Var(b))
  const cN = args.reduce(
    (acc: Term, curr) => App(acc, Par(curr.name)),
    cNParams
  );

  // For indexed types, we need to extract the index from the return type
  // and apply P to it first
  // P(index)(constructorN(a,b,...))
  // For non-indexed: P(constructorN(a,b,...))
  const PcN =
    isIndexed && constructor.typ
      ? // Extract indices from return type and apply P to them first, then to constructor
        // P(zero)(vbnil) or P(succ(n))(vbext(n,head,tail))
        App(
          extractIndices(constructor.typ).reduce<Term>(
            (acc, index) => App(acc, index),
            Par("P")
          ),
          cN
        )
      : App(Par("P"), cN);

  // Build Πa:A. Πb:B. ... P(constructorN(a,b,...))
  // Pi("a", A, Pi("b", B, App(P, App(App(Ref(constructorN), a), b))))
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
    
    For indexed types:
    T : Type = λindex. ιt. ΠP:(Πn:Index (Πx:T(n) ★)).
    P(index1)(constructor1) →
    P(index2)(constructor2) →
    ...
    P(indexN)(constructorN) →
    P(index)(t)
  */
export const buildType = (adt: ADT): Def => {
  // Check if this is an indexed type (any constructor has explicit return type)
  const isIndexed = adt.constructors.some((c) => c.typ !== null);

  // T(A,B,C)
  const typ = adt.params.reduce<Term>(
    (acc, paramN) => App(acc, Par(paramN.name)),
    Ref(identifier2str(adt.name))
  );

  // For indexed types, the motive P is indexed:
  // P : (Πn:Nat (Πx:VectBool(n) ★))
  // For non-indexed types, the motive is simple:
  // P : T → ★
  const motiveType = isIndexed
    ? adt.params.reduceRight<Term>(
        (acc, paramN) =>
          Pi(
            paramN.name,
            paramN.type as Term,
            Pi("x", App(Ref(identifier2str(adt.name)), Par(paramN.name)), acc)
          ),
        Star()
      )
    : Pi("", typ, Star());

  const self = // ιt.
    Self(
      "t",
      Pi(
        "P",
        motiveType,
        // P(constructor1) → (Πa:A. P(constructor2(a))) → ... P(constructorN) → P(t)
        reverse(adt.constructors).reduce<Term>(
          (acc, constructorN) =>
            buildTypeArgSignature(adt.params, constructorN, acc),
          // For indexed types: P(index1)...(indexN)(t)
          // For non-indexed: P(t)
          isIndexed
            ? App(
                adt.params.reduce<Term>(
                  (acc, paramN) => App(acc, Par(paramN.name)),
                  Par("P")
                ),
                Par("t")
              )
            : App(Par("P"), Par("t"))
        )
      )
    );

  return Def(
    identifier2str(adt.name),
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

export const processADTs = (f: File): File => {
  return { _: "file", content: f.content.flatMap((node) => processNode(node)) };
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

export const GenerateConstructorType = (
  typeName: string,
  params: Argument[],
  constructor: Constructor
) => {
  // nil : (T *) → List(T)
  // cons : (T *) → (head T) → (tail List(T)) → List(T)

  // For indexed types:
  // vbnil : VectBool(zero)
  // vbext : (n:Nat) → (head:Bool) → (tail:VectBool(n)) → VectBool(succ(n))

  // Use the constructor's explicit type if provided (for indexed types)
  // Otherwise use the default: type applied to all params
  const returnType: Term =
    constructor.typ !== null
      ? (constructor.typ as Term) // Indexed types specify exact return type
      : params.reduce<Term>(
          (acc, curr) => App(acc, Par(curr.name)),
          Ref(typeName)
        );

  // For example
  // (head T) → (tail List(T)) → List(T)
  // or
  // (n:Nat) → (head:Bool) → (tail:VectBool(n)) → VectBool(succ(n))
  const prependConstructorArgs = constructor.args.reduceRight<Term>(
    (acc, curr) => Pi(curr.name, curr.type as Term, acc),
    returnType
  );

  // Prepend type parameters for non-indexed types
  // For indexed types (where typ is specified), params become constructor arguments, not type params
  const typeParams =
    constructor.typ !== null
      ? prependConstructorArgs // Indexed: no type params to prepend
      : params.reduceRight<Term>(
          (acc, curr) => Pi(curr.name, curr.type as Term, acc),
          prependConstructorArgs
        );

  return processPars(typeParams, []);
};

export const GenerateConstructorTerm = (
  params: Argument[],
  constructors: Constructor[],
  i: number
): Expression => {
  /*
    cons = <A> (head) (tail) <P> (nil) (cons) cons(head)(tail)
    nil = <A> <P> (nil) (cons) nil
    
    For indexed types:
    vbnil = <P> (vbnil) (vbext) vbnil
    vbext = (n) (head) (tail) <P> (vbnil) (vbext) vbext(n)(head)(tail)
  */
  // Working from right to left.

  // Apply all arguments to the constructor
  const apps = constructors[i].args.reduce<Term>(
    (acc, curr) => App(acc, Par(curr.name)),
    Par(identifier2str(constructors[i].name))
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
  const absArgs = constructors[i].args.reduceRight<Term>(
    (acc, curr) => Abs(curr.name, acc),
    absP
  );

  // For indexed types (where constructor has explicit return type),
  // don't prepend the ADT params as lambdas - they're indices, not type params
  const absParams =
    constructors[i].typ !== null
      ? absArgs // Indexed: params are indices, not abstracted
      : params.reduceRight<Term>((acc, curr) => Abs(curr.name, acc), absArgs);

  return processPars(absParams, []);
};
