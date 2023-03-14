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
} from "vscode-languageserver";
import { TextDocument } from "vscode-languageserver-textdocument";
import { listFiles, stripFileProtocol, loadFromFilesystem, uri } from "./files";

// connection handles messages between this LSP server and the client.
let connection = createConnection(ProposedFeatures.all);

type Uri = string;

let sources = new Map<Uri, TextDocument>();

let initialCheck = false;

connection.onInitialized(async () => {
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

var workspaceFolders: WorkspaceFolder[];

connection.onInitialize(async (params) => {
  if (params.workspaceFolders) {
    workspaceFolders = params.workspaceFolders;
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

// documents stores the contents of all documents that are open in the
// editor. Changes are sent from the editor incrementally and are resolved by
// TextDocuments.
let documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

// Handle files being opened in the editor.
documents.onDidOpen(async (event) => {
  // If the file is open in the editor its contents are taken from
  // `documents` instead of `filesystemSources`.
  sources.delete(event.document.uri);
});

const versions = new Map<uri, number>();

// Handle file edits by running the typechecker.
documents.onDidChangeContent((change) => {
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

  const text = change.document.getText();

  // for (const [uri, diag] of result.entries()) {
  //   connection.sendDiagnostics({
  //     uri: uri,
  //     diagnostics: diag,
  //     version: change.document.version,
  //   });
  // }

  console.log(`handled change for ${uri}`);
});

documents.onDidClose(async (e) => {
  // The document is no longer available from `documents`, so retrieve the
  // saved version from the filesystem.
  let doc = await loadFromFilesystem(e.document.uri);
  sources.set(e.document.uri, doc);
});

// Look up the definition of the symbol at the given source position.
connection.onDefinition((what) => {
  const start = process.hrtime.bigint();

  const uri = what.textDocument.uri;
  const doc = documents.get(uri);
  if (doc == undefined) {
    console.log(`document not found: ${uri}`);
    return null;
  }
  const offset = doc.offsetAt(what.position);

  // TODO: Find out what exists that this source location.
  // TODO: Follow the reference to it's definition.

  const millis = Number(process.hrtime.bigint() - start) / 1e6;
  console.log(`handled references for ${uri} in ${millis}ms`);

  const definitionUri = "";
  const definitionRange = Range.create(
    Position.create(0, 0),
    Position.create(0, 0)
  );

  return [
    {
      uri: definitionUri,
      range: definitionRange,
    },
  ];
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

  // TODO: Compute the type of the term underneath the cursor.

  const messages: string[] = [];

  if (messages.length == 0) return null;

  let markdown: MarkupContent = {
    kind: MarkupKind.Markdown,
    value: messages.join("\n"),
  };

  const millis = Number(process.hrtime.bigint() - start) / 1e6;
  console.log(`handled hover for ${uri} in ${millis}ms`);

  return { contents: markdown };
});

// Provide a list of possible completions that the user can auto-complete.
connection.onCompletion(
  (position: TextDocumentPositionParams): CompletionItem[] => {
    // TODO: Collect all top-level definitions that are visible from this
    //  context.
    // TODO: Compute all Vars that are in scope at this position.
    return [];
  }
);

// This handler resolves additional information for the item selected in
// the completion list. There's currently no additional information so just
// return the original completion unchanged.
connection.onCompletionResolve((item) => item);

// Handle document change events.
documents.listen(connection);

// Listen for LSP clients.
connection.listen();
