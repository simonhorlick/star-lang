import { Abs, Ann, App, Pi, Ref, Self, Star, Var } from "./sugar";
import { Def2 } from "./ast";

// and : * -> * -> *
// and = λp. λq. Πc:*. (p -> q -> c) -> c
export const and = Def2(
  "and",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Pi(
          "c",
          Star(),
          Pi(
            "",
            Pi("", Var("p", 2), Pi("", Var("q", 2), Var("c", 2))),
            Var("c", 1)
          )
        )
      )
    ),
    Pi("", Star(), Pi("", Star(), Star()))
  ),
  undefined,
  undefined
);

// conj : Πp:*. Πq:*. p -> q -> and p q
// conj = λp. λq. λx. λy. λc. λf. f x y
export const conj = Def2(
  "conj",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "x",
          Abs(
            "y",
            Abs("c", Abs("f", App(App(Var("f", 0), Var("x", 3)), Var("y", 2))))
          )
        )
      )
    ),
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi(
          "",
          Var("p", 1),
          Pi("", Var("q", 1), App(App(Ref("and"), Var("p", 3)), Var("q", 2)))
        )
      )
    )
  ),
  undefined,
  undefined
);

// proj1 : Πp:*. Πq:*. and p q → p
// proj1 : λp. λq. λa. a p (λx. λy. x)
export const proj1 = Def2(
  "proj1",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(App(Var("a", 0), Var("p", 2)), Abs("x", Abs("y", Var("x", 1))))
        )
      )
    ),
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi("", App(App(Ref("and"), Var("p", 1)), Var("q", 0)), Var("p", 2))
      )
    )
  ),
  undefined,
  undefined
);

// proj2 : Πp:*. Πq:*. and p q → q
// proj2 = λp.   λq. λa. a q (λx. λy. y)
export const proj2 = Def2(
  "proj2",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(App(Var("a", 0), Var("q", 1)), Abs("x", Abs("y", Var("y", 0))))
        )
      )
    ),
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi("", App(App(Ref("and"), Var("p", 1)), Var("q", 0)), Var("q", 1))
      )
    )
  ),
  undefined,
  undefined
);

// and_commutes : Πp:*. Πq:*. and p q → and q p
// and_commutes = λp. λq. λa. conj q p (proj2 p q a) (proj1 p q a)
export const andCommutes = Def2(
  "and_commutes",
  Ann(
    Abs(
      "p",
      Abs(
        "q",
        Abs(
          "a",
          App(
            App(
              App(App(Ref("conj"), Var("q", 1)), Var("p", 2)),
              App(App(App(Ref("proj2"), Var("p", 2)), Var("q", 1)), Var("a", 0))
            ),
            App(App(App(Ref("proj1"), Var("p", 2)), Var("q", 1)), Var("a", 0))
          )
        )
      )
    ),
    Pi(
      "p",
      Star(),
      Pi(
        "q",
        Star(),
        Pi(
          "",
          App(App(Ref("and"), Var("p", 1)), Var("q", 0)),
          App(App(Ref("and"), Var("q", 1)), Var("p", 2))
        )
      )
    )
  ),
  undefined,
  undefined
);

// func VectBool : (sz:Nat) -> *
//           = λsz ιt
//             (P:((n:Nat) -> (x:VectBool(n)) -> *)) ->
//             (cnil:P(zero,vnil)) ->
//             (cext:((n:Nat) -> (head:Bool) -> (tail:VectBool(n)) -> P(succ(n),ext(n,head,tail)))) ->
//             P(sz,t)
export const vectBool = Def2(
  "VectBool",
  Ann(
    // λsz
    Abs(
      "sz",
      // ιt
      Self(
        "t",
        // ΠP:(Πn:Nat Πx:VectBool(n) ★)
        Pi(
          "P",
          Pi(
            "n",
            Ref("Nat"),
            Pi("x", App(Ref("VectBool"), Var("n", 0)), Star())
          ),
          // Πcnil:P(zero)(vnil)
          Pi(
            "cnil",
            App(App(Var("P", 0), Ref("zero")), Ref("vnil")),
            // Πcext:(Πn:Nat Πhead:Bool Πtail:VectBool(n) P(succ(n))(ext(n)(head)(tail)))
            Pi(
              "cext",
              Pi(
                "n",
                Ref("Nat"),
                Pi(
                  "head",
                  Ref("Bool"),
                  Pi(
                    "tail",
                    App(Ref("VectBool"), Var("n", 1)),
                    // P(succ(n))(ext(n)(head)(tail))
                    App(
                      App(Var("P", 4), App(Ref("succ"), Var("n", 2))),
                      App(
                        App(App(Ref("ext"), Var("n", 2)), Var("head", 1)),
                        Var("tail", 0)
                      )
                    )
                  )
                )
              ),
              // P(sz,t)
              App(App(Var("P", 2), Var("sz", 4)), Var("t", 3))
            )
          )
        )
      )
    ),
    Pi("sz", Ref("Nat"), Star())
  ),
  undefined,
  undefined
);

// func vbnil : VectBool(zero)
//     = λP λcnil λcext cnil
export const vbnil = Def2(
  "vbnil",
  Ann(
    // λP λcnil λcext cnil
    Abs("P", Abs("cnil", Abs("cext", Var("cnil", 1)))),
    // VectBool(zero)
    App(Ref("VectBool"), Ref("zero"))
  ),
  undefined,
  undefined
);

// func vbext : (n:Nat) -> (head:Bool) -> (tail:VectBool(n)) -> VectBool(succ(n))
//     = λn λhead λtail λP λcnil λcext cext(n,head,tail)
export const vbext = Def2(
  "vbext",
  Ann(
    // λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
    Abs(
      "n",
      Abs(
        "head",
        Abs(
          "tail",
          Abs(
            "P",
            Abs(
              "cnil",
              Abs(
                "cext",
                App(
                  App(App(Var("cext", 0), Var("n", 5)), Var("head", 4)),
                  Var("tail", 3)
                )
              )
            )
          )
        )
      )
    ),
    // Πn:Nat Πhead:Bool Πtail:VectBool(n) VectBool(succ(n))
    Pi(
      "n",
      Ref("Nat"),
      Pi(
        "head",
        Ref("Bool"),
        Pi(
          "tail",
          App(Ref("VectBool"), Var("n", 1)),
          App(Ref("VectBool"), App(Ref("succ"), Var("n", 2)))
        )
      )
    )
  ),
  undefined,
  undefined
);

// A vector is essentially a List, but with the length encoded as
// part of the type. In the following tests we hard-code the type argument of
// the Vector to be Bool as it slightly simplifies the tests.
//
// Vect : Πsz:Nat ★
//      = λsz ιt
//        ΠP:(Πn:Nat Πx:Vect(n) ★)
//        Πcnil:P(zero)(vnil)
//        Πcext:(Πn:Nat Πhead:Bool Πtail:Vect(n) P(succ(n))(ext(n)(head)(tail))
//        P(sz)(t)
// vnil : Vect(zero)
//      = λP λcnil λcext cnil
//  ext : Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
//      = λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
export const vect = Def2(
  "Vect",
  Ann(
    // λsz
    Abs(
      "sz", // the length of the tail Vector
      // ιt
      Self(
        "t",
        // ΠP:(Πn:Nat Vect(n)→★)
        Pi(
          "P",
          Pi("n", Ref("Nat"), Pi("x", App(Ref("Vect"), Var("n", 0)), Star())),
          // Πcnil:P(zero)(vnil)
          Pi(
            "cnil",
            App(App(Var("P", 0), Ref("zero")), Ref("vnil")),
            // Πcext:(Πn:Nat Πhead:Bool Πtail:Vect(n) P(succ(n))(ext(n)(head)(tail))
            Pi(
              "cext",
              Pi(
                "n",
                Ref("Nat"),
                Pi(
                  "head",
                  Ref("Bool"),
                  Pi(
                    "tail",
                    App(Ref("Vect"), Var("n", 1)),
                    // P(succ(n))(ext(n)(head)(tail))
                    App(
                      App(Var("P", 4), App(Ref("succ"), Var("n", 2))),
                      App(
                        App(App(Ref("ext"), Var("n", 2)), Var("head", 1)),
                        Var("tail", 0)
                      )
                    )
                  )
                )
              ),
              App(App(Var("P", 2), Var("sz", 4)), Var("t", 3))
            )
          )
        )
      )
    ),
    Pi("sz", Ref("Nat"), Star())
  ),
  undefined,
  undefined
);

//  ext : Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
//      = λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
export const ext = Def2(
  "ext",
  Ann(
    // λn λhead λtail λP λcnil λcext cext(n)(head)(tail)
    Abs(
      "n",
      Abs(
        "head",
        Abs(
          "tail",
          Abs(
            "P",
            Abs(
              "cnil",
              Abs(
                "cext",
                App(
                  App(App(Var("cext", 0), Var("n", 5)), Var("head", 4)),
                  Var("tail", 3)
                )
              )
            )
          )
        )
      )
    ),
    // Πn:Nat Πhead:Bool Πtail:Vect(n) Vect(succ(n))
    Pi(
      "n",
      Ref("Nat"),
      Pi(
        "head",
        Ref("Bool"),
        Pi(
          "tail",
          App(Ref("Vect"), Var("n", 1)),
          App(Ref("Vect"), App(Ref("succ"), Var("n", 2)))
        )
      )
    )
  ),
  undefined,
  undefined
);

// vnil : Vect(zero)
//      = λP λcnil λcext cnil
export const vnil = Def2(
  "vnil",
  Ann(
    // λP λcnil λcext cnil
    Abs("P", Abs("cnil", Abs("cext", Var("cnil", 1)))),
    // Vect(zero)
    App(Ref("Vect"), Ref("zero"))
  ),
  undefined,
  undefined
);
