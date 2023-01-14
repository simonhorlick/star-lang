// A bound variable.
export type Var = {
  _: "var";

  // The variable name for pretty printing.
  name: string;

  // The de Bruijn index of this node. The number index stands for “the variable
  // bound by the index’th enclosing λ.”
  index: number;
};

export const Var = (name: string, index: number): Var => ({
  _: "var",
  name: name,
  index: index,
});

// A reference.
export type Ref = {
  _: "ref";

  // The name of the definition being referenced.
  name: string;
};

export const Ref = (name: string): Ref => ({
  _: "ref",
  name: name,
});

// Abs is a lambda abstraction.
export type Abs = {
  _: "lam";
  name: string; // name of the binder
  body: Term; // the body of the abstraction
};

export const Abs = (name: string, body: Term): Abs => ({
  _: "lam",
  name: name,
  body: body,
});

// App is a function application.
export type App = {
  _: "app";
  left: Term;
  right: Term;
};

export const App = (left: Term, right: Term): App => ({
  _: "app",
  left: left,
  right: right,
});

export type Term = Abs | App | Var | Ref;

// A top-level definition.
export type Def = {
  _: "def";
  name: string;
  term: Term;
};

export const Def = (name: string, term: Term): Def => ({
  _: "def",
  name: name,
  term: term,
});
