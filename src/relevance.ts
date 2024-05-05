import {
  AbsI,
  Ann,
  App,
  If,
  Let,
  Origin,
  Pi,
  Rel,
  Self,
  Syntax,
  Term,
} from "./ast";

// const addBinder = (env: number[]) = env
const head = (l: number[]) => l[0];
const tail = (l: number[]) => l.slice(1);
const last = (l: number[]) => l[l.length - 1];
const init = (l: number[]) => l.slice(0, l.length - 1);

type Ret = {
  term: Term;
  env: number[];
};

export const relevance = (t: Term, env: number[]): Ret => {
  // TODO: Annotate every Pi type with a relevance annotation.
  // TODO: every time we encounter a lambda we need to count the occurances in
  //  the body.

  //
  //   λa
  //   | {a:0}
  //   λb
  //   | {b:0}
  //   λc
  //   | {c:0}
  //   ap
  //  /  \
  // 1    2
  //[0,1,0]
  //      [1,0,0]

  const plus = (env1: number[], env2: number[]): number[] => {
    if (env1.length != env2.length) {
      throw "env lengths differ";
    }
    return env1.map((v, i) => v + env2[i]);
  };

  switch (t._) {
    case "lam": {
      const body = relevance(t.body, env.concat([0]));
      const upd = AbsI(t.name, body.term);
      // pop the last variable from the env and return everything else
      return {
        term: Rel(upd, last(body.env)),
        env: init(body.env),
      };
    }
    case "var": {
      const ne = [...env];
      ne[env.length - 1 - t.index]++;
      return {
        term: t,
        env: ne,
      };
    }
    case "self": {
      const body = relevance(t.body, env.concat([0]));
      const upd = Self(t.name, body.term);
      return {
        term: Rel(upd, last(body.env)),
        env: init(body.env),
      };
    }
    case "app": {
      const left = relevance(t.func, env);
      const right = relevance(t.arg, env);
      const upd = App(left.term, right.term);
      return {
        term: upd,
        env: plus(left.env, right.env),
      };
    }
    case "ann": {
      const term = relevance(t.term, env);
      const typ = relevance(t.typ, env);
      const upd = Ann(term.term, typ.term);
      return {
        term: upd,
        env: plus(term.env, typ.env),
      };
    }
    case "pi": {
      const from = relevance(t.from, env);
      const to = relevance(t.body, env.concat([0]));
      const upd = Pi(t.name, from.term, to.term);
      return {
        term: Rel(upd, last(to.env)),
        env: plus(from.env, init(to.env)),
      };
    }
    case "par":
    case "star":
    case "ref":
    case "id":
    case "key":
    case "hole":
    case "int":
    case "str":
    case "label":
    case "err": {
      return {
        term: t,
        env: env, // return the env unchanged
      };
    }
    case "orig": {
      const child = relevance(t.child, env);
      const upd = Origin(t.start, t.end, child.term);
      return {
        term: upd,
        env: child.env,
      };
    }
    case "syn": {
      const child = relevance(t.child, env);
      const upd = Syntax(t.syntax, child.term);
      return {
        term: upd,
        env: child.env,
      };
    }
    case "case": {
      // TODO: implement this
      return {
        term: t,
        env: env,
      };
      // return Case(
      //   relevance(t.name),
      //   t.branches.map((b) =>
      //     Branch(relevance(b.constructor) as Identifier, relevance(b.term))
      //   )
      // );
    }
    case "let": {
      const body = relevance(t.body, env);
      const expr = relevance(t.expr, env);
      const upd = Let(t.name, expr.term, body.term);
      return {
        term: upd,
        env: plus(body.env, expr.env),
      };
    }
    case "if": {
      const cnd = relevance(t.condition, env);
      const tru = relevance(t.trueBranch, env);
      const fls = relevance(t.falseBranch, env);
      const upd = If(cnd.term, tru.term, fls.term);
      return {
        term: upd,
        env: plus(cnd.env, plus(tru.env, fls.env)),
      };
    }
    case "rel": {
      throw "relevance: unexpected rel";
    }
  }
};

export const simplify = (term: Term): Term => {
  return term;
};
