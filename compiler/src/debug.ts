import util from "node:util";
import { pretty } from "./pretty";
import { Expression } from "./pratt";

// Provide a custom inspection that will appear in the debugger.
export interface Inspectable {
  [util.inspect.custom](): string;
}

// Attach the pretty printer to the custom inspection.
export function withInspect<T extends Expression>(obj: T): T & Inspectable {
  Object.defineProperty(obj, util.inspect.custom, {
    value: function (this: T) {
      return pretty(this);
    },
    enumerable: false,
  });
  return obj as T & Inspectable;
}
