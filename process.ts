import {
  Context,
  Ann,
  Star,
  Pi,
  Self,
  Type,
  Par,
  Term,
  App,
  Abs,
  Var,
  Ref,
  File,
  Pkg,
  Com,
  Def,
  ADT,
  Space,
  Newline,
  Argument,
  Constructor,
  Case,
  Branch,
  Origin,
  ASTNode,
  AbsI,
  Identifier,
  If,
} from "./ast";
import { addTermToCtx, identifier, shift } from "./check";
import { pretty } from "./pretty";

const reverse = <T>(l: Array<T>) => [...l].reverse();

const wrapOrigin = (term: Term, from: Origin | Identifier): Term => {
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
      const td = buildType(n.name, n.params, n.constructors);
      const defs = n.constructors.map((con, i) => {
        return Def(
          identifier(con.name),
          // This is used for tooling to be able to provide jump-to-definition
          // for type constructors.
          wrapOrigin(
            GenerateConstructorTerm(n.params, n.constructors, i),
            con.name
          ),
          GenerateConstructorType(
            identifier(n.name),
            n.params,
            n.constructors[i]
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
const buildTypeArgSignature = (
  parameters: Argument[],
  constructorName: string,
  args: Argument[],
  acc: Term
): Term => {
  // Build the syntax tree for the type Πa:A. Πb:B. P(constructorN(a,b)).

  // Apply all type parameters to the constructor first.
  const cNParams = parameters.reduce(
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

  // Build P(constructorN(a,b,...))
  const PcN = App(Par("P"), cN);

  // Build Πa:A. Πb:B. ... P(constructorN(a,b,...))
  // Pi("a", A, Pi("b", B, App(P, App(App(Ref(constructorN), a), b))))
  const Pis = args.reduce(
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
  */
export const buildType = (
  name: Origin | Identifier,
  parameters: Argument[],
  constructors: Constructor[]
): Def => {
  // T(A,B,C)
  const typ = parameters.reduce<Term>(
    (acc, paramN) => App(acc, Par(paramN.name)),
    Ref(identifier(name))
  );

  const self = // ιt.
    Self(
      "t",
      Pi(
        "P",
        // ΠP:T→*.
        Pi("", typ, Star()),
        // P(constructor1) → (Πa:A. P(constructor2(a))) → ... P(constructorN) → P(t)
        reverse(constructors).reduce<Term>(
          (acc, constructorN) =>
            buildTypeArgSignature(
              parameters,
              identifier(constructorN.name),
              constructorN.args,
              acc
            ),
          App(Par("P"), Par("t")) // P(t)
        )
      )
    );

  return Def(
    identifier(name),
    // This is used for tooling to be able to provide jump-to-definition for
    // types. `name` contains the source location where the constructor was
    // defined, so any refs that mention this constructor can follow this origin
    // back to the source text.
    wrapOrigin(
      processPars(
        parameters.reduce<Term>((acc, paramN) => Abs(paramN.name, acc), self),
        []
      ),
      name
    ),
    // Ensure that type-constructors such as Maybe have type arguments here.
    // Maybe does not have type * - instead it has type A->*.
    parameters.reduce<Term>(
      (acc, curr) => Pi(curr.name, curr.type, acc),
      Star()
    )
  );
};

export const processADTs = (f: File): File => {
  return { _: "file", content: f.content.flatMap((node) => processNode(node)) };
};

// TODO: Re-think this. There's a lot of places where we're doing thing kind of
// thing.
export const desugarTerm = (
  t: Term,
  ann: Term | undefined,
  adts: Map<string, ADT>,
  ctx: Context
): Term => {
  switch (t._) {
    case "ann":
      const desugaredType = desugarTerm(t.typ, undefined, adts, ctx);
      return Ann(desugarTerm(t.term, desugaredType, adts, ctx), desugaredType);
    case "app":
      return App(
        desugarTerm(t.left, undefined, adts, ctx),
        desugarTerm(t.right, undefined, adts, ctx)
      );
    case "lam":
      // The type in this context is not important so just set it as *.
      return AbsI(
        t.name,
        desugarTerm(
          t.body,
          undefined,
          adts,
          addTermToCtx(ctx, identifier(t.name), Star())
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
        desugarTerm(t.from, undefined, adts, ctx),
        desugarTerm(t.to, undefined, adts, addTermToCtx(ctx, t.name, Star()))
      );
    case "self":
      return Self(
        t.name,
        desugarTerm(t.body, undefined, adts, addTermToCtx(ctx, t.name, Star()))
      );
    case "case":
      return Case(
        desugarTerm(t.name, undefined, adts, ctx),
        t.branches.map((b) =>
          Branch(b.constructor, desugarTerm(b.term, undefined, adts, ctx))
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
      return Case(desugarTerm(t.condition, undefined, adts, ctx), [
        Branch(
          Identifier("false"),
          desugarTerm(t.falseBranch, undefined, adts, ctx)
        ),
        Branch(
          Identifier("true"),
          desugarTerm(t.trueBranch, undefined, adts, ctx)
        ),
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
      return t;
    case "orig":
      return Origin(t.start, t.end, desugarTerm(t.child, ann, adts, ctx));
  }
};

export const desugar = (def: Def, adts: Map<string, ADT>): Def => {
  return Def(
    def.name,
    desugarTerm(def.term, undefined, adts, []),
    desugarTerm(def.typ, undefined, adts, [])
  );
};

// processPars removes all Par nodes from the tree t.
export const processPars = (t: Term, ctx: Context): Term => {
  switch (t._) {
    case "ann":
      return Ann(processPars(t.term, ctx), processPars(t.typ, ctx));
    case "app":
      return App(processPars(t.left, ctx), processPars(t.right, ctx));
    case "lam":
      // The type in this context is not important so just set it as *.
      return AbsI(
        t.name,
        processPars(t.body, addTermToCtx(ctx, identifier(t.name), Star()))
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
        processPars(t.to, addTermToCtx(ctx, t.name, Star()))
      );
    case "self":
      return Self(
        t.name,
        processPars(t.body, addTermToCtx(ctx, t.name, Star()))
      );
    case "orig":
      return Origin(t.start, t.end, processPars(t.child, ctx));
    case "case":
      return Case(
        processPars(t.name, ctx),
        t.branches.map((branch) =>
          Branch(branch.constructor, processPars(branch.term, ctx))
        )
      );
    case "if":
      return If(
        processPars(t.condition, ctx),
        processPars(t.trueBranch, ctx),
        processPars(t.falseBranch, ctx)
      );
    case "ref":
    case "star":
    case "var":
    case "id":
      return t;
  }
};

export const GenerateConstructorType = (
  typeName: string,
  params: Argument[],
  constructor: Constructor
) => {
  // nil : (T *) → List<T>
  // cons : (T *) → (head T) → (tail List<T>) → List<T>

  // The type and all params. i.e. List(T), or Pair(A,B)
  const apps = params.reduce<Term>(
    (acc, curr) => App(acc, Par(curr.name)),
    Ref(typeName)
  );

  // For example
  // (head T) → (tail List<T>) → List<T>
  const prependConstructorArgs = constructor.args.reduceRight<Term>(
    (acc, curr) => Pi(curr.name, curr.type, acc),
    apps
  );

  // Prepend type parameters, for example
  // (T *) → (head T) → (tail List<T>) → List<T>
  const typeParams = params.reduce<Term>(
    (acc, curr) => Pi(curr.name, curr.type, acc),
    prependConstructorArgs
  );

  return processPars(typeParams, []);
};

export const GenerateConstructorTerm = (
  params: Argument[],
  constructors: Constructor[],
  i: number
) => {
  /*
    cons = <A> (head) (tail) <P> (nil) (cons) cons(head)(tail)
    nil = <A> <P> (nil) (cons) nil
  */
  // Working from right to left.

  // Apply all arguments to the constructor
  const apps = constructors[i].args.reduce<Term>(
    (acc, curr) => App(acc, Par(curr.name)),
    Par(identifier(constructors[i].name))
  );

  // Abstract constructors
  const absConstructors = constructors.reduceRight<Term>(
    // Passing curr.name to AbsI here will expose the source locations of the
    // type constructors to tooling, i.e. the constructor `true` would have
    // a span for `true:P(true)`.
    (acc, curr) => Abs(identifier(curr.name), acc),
    apps
  );

  // Abstract P
  const absP = Abs("P", absConstructors);

  // Abstract arguments
  const absArgs = constructors[i].args.reduceRight<Term>(
    (acc, curr) => Abs(curr.name, acc),
    absP
  );

  // Abstract type parameters
  const absParams = params.reduceRight<Term>(
    (acc, curr) => Abs(curr.name, acc),
    absArgs
  );

  return processPars(absParams, []);
};
