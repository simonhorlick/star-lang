import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  TextDocumentSyncKind,
  WorkspaceFolder,
  Range,
  TextDocumentPositionParams,
  CompletionItem,
  HoverParams,
  MarkupContent,
  MarkupKind,
  Position,
  SemanticTokensRegistrationOptions,
  SemanticTokensRegistrationType,
  SemanticTokensLegend,
  SemanticTokensClientCapabilities,
  SemanticTokensBuilder,
  SemanticTokenModifiers,
  SemanticTokenTypes,
  DiagnosticSeverity,
  Diagnostic,
  CompletionItemKind,
  TextEdit,
  ClientCapabilities,
  InsertTextFormat,
  Location,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import { ADT, Def } from "star-lang/ast";
import { Context } from "star-lang/context";
import {
  Span,
  TermAndCtx,
  complete,
  foldTreeCtx,
  hoverMessage,
  definitionLocation,
  inferType,
  printMultilineDiagnostic,
} from "star-lang/inspect";
import { inspect, inspectASTNodes } from "star-lang/inspect";
import { indexToLineCol } from "star-lang/parser";
import { build } from "star-lang/build";
import { listFiles, stripFileProtocol, loadFromFilesystem, uri } from "./files";
import { TypecheckError } from "star-lang/typecheck";
import { pretty, printCtx } from "star-lang/pretty";
import { CTerm, Case, Branch, Ref, strip, Identifier } from "star-lang/sugar";
import { If, identifier2str } from "star-lang/pratt";

// connection handles messages between this LSP server and the client.
let connection = createConnection(ProposedFeatures.all);

type Uri = string;

var workspaceFolders: WorkspaceFolder[];

let semanticTokensLegend: SemanticTokensLegend | undefined;

const serverTokenTypes = new Set<string>(Object.values(SemanticTokenTypes));
const serverTokenModifiers = new Set<string>(
  Object.values(SemanticTokenModifiers)
);

function intersect<A>(a: Set<A>, b: Set<A>): Set<A> {
  return new Set([...a].filter((i) => b.has(i)));
}

function computeLegend(
  capability: SemanticTokensClientCapabilities
): SemanticTokensLegend {
  const clientTokenTypes = new Set<string>(capability.tokenTypes);
  const clientTokenModifiers = new Set<string>(capability.tokenModifiers);

  return {
    tokenTypes: [...intersect(clientTokenTypes, serverTokenTypes)],
    tokenModifiers: [...intersect(clientTokenModifiers, serverTokenModifiers)],
  };
}

let capabilities: ClientCapabilities;

connection.onInitialize(async (params) => {
  if (params.workspaceFolders) {
    workspaceFolders = params.workspaceFolders;
  }

  capabilities = params.capabilities;

  if (params.capabilities.textDocument?.semanticTokens) {
    semanticTokensLegend = computeLegend(
      params.capabilities.textDocument.semanticTokens
    );
  }

  // Notify the LSP client what capabilities this server provides.
  return {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Incremental,
      definitionProvider: true,
      completionProvider: {
        resolveProvider: true,
      },
      hoverProvider: true,
    },
  };
});

let sources = new Map<Uri, TextDocument>();

let initialCheck = false;

connection.onInitialized(async () => {
  if (semanticTokensLegend != undefined) {
    const registrationOptions: SemanticTokensRegistrationOptions = {
      documentSelector: ["star"],
      legend: semanticTokensLegend,
      range: false,
      full: {
        delta: false,
      },
    };
    connection.client.register(
      SemanticTokensRegistrationType.type,
      registrationOptions
    );
  } else {
    console.log("no support for SemanticTokens");
  }

  for (const workspace of workspaceFolders) {
    // Load all sources under each of the workspaces.
    console.log(`checking workspace: ${workspace.name}`);

    let workspaceFiles = await listFiles(stripFileProtocol(workspace.uri));
    let sourceFiles = workspaceFiles.filter((file) => file.endsWith(".st"));

    // TODO: This should be part of a build library that knows how to compile
    // star modules.

    // TODO: Don't just read all of the files, read the module file and figure
    // out the build from there.

    // Read all source files into memory.
    for (const filename of sourceFiles) {
      let doc = await loadFromFilesystem(filename);
      sources.set(filename, doc);
      // TODO: Parse all files and send any parse diagnostics to vscode.
    }

    // TODO: Do an initial typecheck of all the defs in the workspace.
    initialCheck = true;
  }
});

// documents stores the contents of all documents that are open in the
// editor. Changes are sent from the editor incrementally and are resolved by
// TextDocuments.
let documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

// Handle files being opened in the editor.
documents.onDidOpen(async (event) => {
  console.log(`document opened ${event.document.uri}`);
  // If the file is open in the editor its contents are taken from
  // `documents` instead of `filesystemSources`.
  sources.delete(event.document.uri);
});

const versions = new Map<uri, number>();

// Handle file edits by running the typechecker.
documents.onDidChangeContent((change) => {
  console.log(`document changed ${change.document.uri}`);
  const uri = change.document.uri;
  const version = change.document.version;

  if (!initialCheck) return;

  // Check if the file actually changed - we get spurious change events from
  // vscode on hover.
  if (versions.get(uri) === version) {
    console.log(`already checked ${uri} version ${version}`);
    return;
  }
  versions.set(uri, version);

  const src = change.document.getText();

  let diagnostics: Diagnostic[] = [];

  console.log(`building ${change.document.uri}`);

  const result = build(src, false);

  for (const err of result.parseErrors) {
    diagnostics.push({
      severity: DiagnosticSeverity.Error,
      range: {
        start: change.document.positionAt(err.start),
        end: change.document.positionAt(err.end + 1),
      },
      message: `parse: ${err.msg}`,
    });
  }

  for (const err of result.checkerErrors) {
    console.log(`check(${err.start}-${err.end}): ${err.msg}`);
    diagnostics.push({
      severity: DiagnosticSeverity.Error,
      range: {
        start: change.document.positionAt(err.start),
        end: change.document.positionAt(err.end + 1),
      },
      message: `check(${err.start}-${err.end}): ${err.msg}`,
    });
  }

  connection.sendDiagnostics({
    uri: uri,
    diagnostics: diagnostics,
    version: change.document.version,
  });
});

documents.onDidClose(async (e) => {
  console.log(`document closed ${e.document.uri}`);
  // The document is no longer available from `documents`, so retrieve the
  // saved version from the filesystem.
  let doc = await loadFromFilesystem(e.document.uri);
  sources.set(e.document.uri, doc);
});

// Look up the definition of the symbol at the given source position.
connection.onDefinition((params) => {
  const start = process.hrtime.bigint();

  // Find whatever is under the cursor at this location.
  const uri = params.textDocument.uri;
  const doc = documents.get(uri);
  if (doc == undefined) {
    console.log(`document not found: ${uri}`);
    return null;
  }
  const offset = doc.offsetAt(params.position);
  const src = doc.getText();

  var spans: Span[] = [];

  try {
    const result = build(src, false);

    const loc = definitionLocation(src, result.defs, offset);
    if (loc.length == 0) {
      return [];
    }

    const sp = indexToLineCol(src, loc[0].start);
    const ep = indexToLineCol(src, loc[0].end);
    const range = Range.create(
      Position.create(sp.line, sp.col),
      Position.create(ep.line, ep.col)
    );

    let loc2: Location = {
      uri: uri,
      range: range,
    };

    const millis = Number(process.hrtime.bigint() - start) / 1e6;
    console.log(`handled references for ${uri} in ${millis}ms`);

    return loc2;
  } catch (err) {
    console.error(err);
  }
});

connection.onHover((params: HoverParams) => {
  const start = process.hrtime.bigint();
  console.log(
    `hover request for ${params.textDocument.uri} position ${params.position.line} ${params.position.character}`
  );

  // Find whatever is under the cursor at this location.
  const uri = params.textDocument.uri;
  const doc = documents.get(uri);
  if (doc == undefined) {
    console.log(`document not found: ${uri}`);
    return null;
  }
  const offset = doc.offsetAt(params.position);
  const src = doc.getText();

  try {
    const result = build(src, false);
    const defs = result.defs;
    const f = result.file;

    const msg = hoverMessage(src, defs, result.nondefs, offset);

    if (msg == null) {
      console.log(`nothing to report at offset ${offset}`);
      return null;
    }

    const sp = indexToLineCol(src, msg.range.start);
    const ep = indexToLineCol(src, msg.range.end);
    const range = Range.create(
      Position.create(sp.line, sp.col),
      Position.create(ep.line, ep.col)
    );

    let markdown: MarkupContent = {
      kind: MarkupKind.Markdown,
      value: msg.msg,
    };

    const millis = Number(process.hrtime.bigint() - start) / 1e6;
    console.log(`handled hover for ${uri} in ${millis}ms`);

    return { contents: markdown, range: range };
  } catch (err) {
    console.error(err);
  }
});

// Takes a variable `name` and returns a case statement that ranges over all of
// its constructors.
const buildCaseStatement = (adt: ADT, name: CTerm): string => {
  const statement = Case(
    name,
    adt.constructors.map((c, i) =>
      Branch(Identifier(identifier2str(c.name)), Ref("${" + (i + 1) + ":todo}"))
    )
  );

  // Serialise the case statement into a string.
  return pretty(statement);
};

// Takes a variable `name` and returns an if statement with the variable as the
// condition.
const buildIfStatement = (name: CTerm): string => {
  const statement = If(name, Ref("${1:todo}"), Ref("${0:todo}"));

  // Serialise the case statement into a string.
  return pretty(statement);
};

// Converts a character offset in a given file into a vscode Position.
const indexToPosition = (src: string, offset: number): Position => {
  const lineCol = indexToLineCol(src, offset);
  return Position.create(lineCol.line, lineCol.col);
};

const isAllowedLocationForCase = (nodesAtCursor: Span[]): boolean => {
  // Case statements are not allowed in the conditions of if statements.
  const insideIfCondition = nodesAtCursor.some(
    (n) => n.term._ == "label" && n.term.label == "if-condition"
  );

  return !insideIfCondition;
};

const isAllowedLocationForIf = (nodesAtCursor: Span[]): boolean => {
  if (nodesAtCursor.length == 0) {
    return false;
  }

  // If statements are allowed directly within function bodies.
  if (nodesAtCursor[0].term._ == "lam") {
    return true;
  }

  // If statements may be nested. It's syntactically valid to have an if
  // statement within the condition of another if statement, but it's such an
  // edge case that we shouldn't suggest an autocompletion for it.
  if (
    nodesAtCursor[0].term._ == "label" &&
    (nodesAtCursor[0].term.label == "if-true" ||
      nodesAtCursor[0].term.label == "if-false")
  ) {
    return true;
  }

  return false;
};

// Provide a list of possible completions that the user can auto-complete.
connection.onCompletion(
  (params: TextDocumentPositionParams): CompletionItem[] => {
    console.log(
      `completion request for ${params.textDocument.uri} position ${params.position.line} ${params.position.character}`
    );

    // Find whatever is under the cursor at this location.
    const uri = params.textDocument.uri;
    const doc = documents.get(uri);
    if (doc == undefined) {
      console.log(`document not found: ${uri}`);
      return [];
    }
    const offset = doc.offsetAt(params.position);
    const src = doc.getText();

    try {
      const result = build(src, false);
      const defs = result.defs;
      const f = result.file;

      const typ = inferType(src, defs, offset);

      const completions = complete(src, defs, offset, typ);
      let completionsList = completions.map(
        (x) =>
          ({
            label: x.label,
            kind: x.kind,
            sortText: x.sortText,
            detail: x.detail,
          } as CompletionItem)
      );

      if (
        capabilities.textDocument?.completion?.completionItem?.snippetSupport
      ) {
        // Provide a snippet that will give a template of a case statement
        // complete with the appropriate branches. The user can trigger
        // this completion by providing an identifier followed by the string
        // ".case".

        // Another option is to push a list of snippets labelled "case <id> of"
        // for every identifier in scope. This is not what's implemented here.

        // If the node to the left of the cursor is a Var, then insert a case
        // completion in the list.

        const nodesAtCursor = Array.from(defs.values())
          .flatMap((n) => inspect(n, defs))
          // Ensure the end can overlap the offset, because we need to be
          // able to trigger insertion after typing the identifier.
          .filter((n) => n.start <= offset && n.end >= offset);

        // Sort by length of span.
        nodesAtCursor.sort((a, b) => {
          const lenA = a.end - a.start;
          const lenB = b.end - b.start;
          return lenA - lenB;
        });

        for (const v of nodesAtCursor) {
          // If the cursor is on top or after a var.
          if (v.term._ == "var" && v.type != null) {
            // Check that this var is an ADT.
            const typ = strip(v.type);
            if (typ._ != "ref") {
              continue;
            }
            const adt = result.adts.get(typ.name);
            if (adt == null) {
              continue;
            }

            if (isAllowedLocationForCase(nodesAtCursor)) {
              // The identifier needs to be at the front of the label or
              // else it won't show in vscode.
              completionsList = completionsList.concat([
                {
                  label: `${v.term.name}.case`,
                  kind: CompletionItemKind.Snippet,
                  insertTextFormat: InsertTextFormat.Snippet,
                  textEdit: TextEdit.replace(
                    // Replace the Var with the Case statement.
                    Range.create(
                      indexToPosition(src, v.start),
                      indexToPosition(src, v.end)
                    ),
                    buildCaseStatement(adt, v.term)
                  ),
                },
              ]);
            }

            if (isAllowedLocationForIf(nodesAtCursor) && typ.name == "Bool") {
              // The identifier needs to be at the front of the label or
              // else it won't show in vscode.
              completionsList = completionsList.concat([
                {
                  label: `${v.term.name}.if`,
                  kind: CompletionItemKind.Snippet,
                  insertTextFormat: InsertTextFormat.Snippet,
                  textEdit: TextEdit.replace(
                    // Replace the Var with the If statement.
                    Range.create(
                      indexToPosition(src, v.start),
                      indexToPosition(src, v.end)
                    ),
                    buildIfStatement(v.term)
                  ),
                },
              ]);
            }
          }
        }

        if (isAllowedLocationForIf(nodesAtCursor)) {
          const characterPreceedingCursor = src.charAt(offset - 1);
          let replaceChars = 0;
          if (characterPreceedingCursor == "i") {
            replaceChars = 1;
          } else if (characterPreceedingCursor == "f") {
            replaceChars = 2;
          }

          completionsList = completionsList.concat([
            {
              label: "if",
              kind: CompletionItemKind.Snippet,
              insertTextFormat: InsertTextFormat.Snippet,
              textEdit: TextEdit.replace(
                Range.create(
                  Position.create(
                    params.position.line,
                    params.position.character - replaceChars
                  ),
                  params.position
                ),
                "if ${1} then ${2:todo} else ${3:todo}"
              ),
            } as CompletionItem,
          ]);
        }
      }

      return completionsList;
    } catch (e) {
      console.error(e);
      return [];
    }
  }
);

// This handler resolves additional information for the item selected in
// the completion list. There's currently no additional information so just
// return the original completion unchanged.
connection.onCompletionResolve((item) => item);

function _encodeTokenType(tokenType: string): number {
  const tokenTypes = semanticTokensLegend?.tokenTypes!;
  const index = tokenTypes.indexOf(tokenType);
  if (index == -1) {
    return 0;
  }
  return index;
}

function _encodeTokenModifiers(strTokenModifiers: string[]): number {
  let result = 0;
  for (let i = 0; i < strTokenModifiers.length; i++) {
    const tokenModifier = strTokenModifiers[i];
    const tokenModifiers = semanticTokensLegend?.tokenModifiers!;
    const index = tokenModifiers.indexOf(tokenModifier);
    if (index != -1) {
      result = result | (1 << index);
    }
  }
  return result;
}

connection.languages.semanticTokens.on((params) => {
  console.log(`semantictokens request`);
  const uri = params.textDocument.uri;
  const doc = documents.get(uri);

  const tokensBuilder = new SemanticTokensBuilder();

  if (doc == undefined) {
    console.log(`document not found: ${uri}`);
    return tokensBuilder.build();
  }

  const src = doc.getText();

  try {
    const result = build(src, false);
    const defs = result.defs;
    const f = result.file;

    type Token = {
      start: number;
      end: number;
      type: string;
      modifiers: string[];
    };

    const nonDefTokens: Token[] = [];
    const nondefs = f.content.filter((node) => node._ != "def");
    for (const node of nondefs) {
      const spans2 = inspectASTNodes(node);
      for (const [k, v] of spans2) {
        const msg = `${k.start}-${k.end} is a ${v.term._}`;
        console.log(msg);
        switch (v.term._) {
          case "com":
            nonDefTokens.push({
              start: k.start,
              end: k.end,
              type: SemanticTokenTypes.comment,
              modifiers: [],
            });
            break;
          case "pkg":
            nonDefTokens.push({
              start: k.start,
              end: k.end,
              type: SemanticTokenTypes.namespace,
              modifiers: [],
            });
            break;
          default:
            console.log(`ast node not handled: ${v.term._}`);
        }
      }
    }

    // TODO: List all tokens
    const defTokens = Array.from(defs.values()).flatMap((def) =>
      foldTreeCtx(
        (acc: Token[], curr: TermAndCtx): Token[] => {
          if (curr.start == undefined || curr.end == undefined) {
            return acc;
          }
          switch (curr.term._) {
            case "var":
              return acc.concat([
                {
                  start: curr.start,
                  end: curr.end,
                  type: SemanticTokenTypes.variable,
                  modifiers: [SemanticTokenModifiers.readonly],
                },
              ]);
            case "key":
              return acc.concat([
                {
                  start: curr.start,
                  end: curr.end,
                  type: SemanticTokenTypes.keyword,
                  modifiers: [],
                },
              ]);
            case "ref": {
              let tokenType = SemanticTokenTypes.variable;
              let tokenModifiers: SemanticTokenModifiers[] = [];
              const ref = defs.get(curr.term.name);
              if (ref != undefined) {
                const type = ref.term.type._;
                if (type == "star") {
                  tokenType = SemanticTokenTypes.type;
                } else if (type == "pi") {
                  tokenType = SemanticTokenTypes.function;
                } else if (type == "ref") {
                  tokenType = SemanticTokenTypes.variable;
                  tokenModifiers = [SemanticTokenModifiers.readonly];
                } else {
                  console.log(`got ${type} when resolving ref`);
                }
              }
              return acc.concat([
                {
                  start: curr.start,
                  end: curr.end,
                  type: tokenType,
                  modifiers: tokenModifiers,
                },
              ]);
            }
            case "id":
              return acc.concat([
                {
                  start: curr.start,
                  end: curr.end,
                  type: SemanticTokenTypes.parameter,
                  modifiers: [SemanticTokenModifiers.declaration],
                },
              ]);
            case "orig":
            case "lam":
              return acc;
            default:
              console.log(`token not handled: ${curr.term._}`);
              return acc;
          }
        },
        [],
        def.term
      )
    );

    const tokens = nonDefTokens.concat(defTokens);
    tokens.sort((a, b) => a.start - b.start);

    for (const token of tokens) {
      const startlc = indexToLineCol(src, token.start);
      const length = token.end - token.start;

      const encodedType = _encodeTokenType(token.type);
      const encodedModifiers = _encodeTokenModifiers(token.modifiers);
      tokensBuilder.push(
        startlc.line,
        startlc.col,
        length,
        encodedType,
        encodedModifiers
      );
    }
  } catch (err) {
    console.error(err);
  }
  return tokensBuilder.build();
});

connection.onRequest((p) => {
  console.log(`request ${p} (not implemented)`);
});

// Handle document change events.
documents.listen(connection);

// Listen for LSP clients.
connection.listen();
