import { Ref } from "./pratt";
import { App, type Expression } from "./pratt";

// Transform expression nodes into native code, i.e. function applications of
// standard library functions. For example `x > y` becomes `gt(x,y)`.
const desugar = (expression: Expression): Expression => {
  switch (expression._) {
    case "ref":
    case "int":
    case "err":
    case "app":
    case "pi":
    case "ann":
      return expression;
    case "neg":
      return App(Ref("neg"), desugar(expression.exp));
    case "add":
      return App(
        App(Ref("add"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "sub":
      return App(
        App(Ref("sub"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "mul":
      return App(
        App(Ref("mul"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "div":
      return App(
        App(Ref("div"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "idx":
      return App(App(Ref("idx"), desugar(expression.idx)), expression.arr);
    case "cat":
      return App(
        App(Ref("cat"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "gt":
      return App(
        App(Ref("gt"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "lt":
      return App(
        App(Ref("lt"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "gte":
      return App(
        App(Ref("gte"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "lte":
      return App(
        App(Ref("lte"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "eq":
      return App(
        App(Ref("eq"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "neq":
      return App(
        App(Ref("neq"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "and":
      return App(
        App(Ref("and"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "or":
      return App(
        App(Ref("or"), desugar(expression.lhs)),
        desugar(expression.rhs)
      );
    case "cons":
      return App(
        App(Ref("cons"), desugar(expression.head)),
        desugar(expression.tail)
      );
    case "nil":
      return Ref("nil");
    case "comp":
    default:
      throw `expected expression; got ${expression._}`;
  }
};
