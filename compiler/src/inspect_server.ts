#!/usr/bin/env ./node_modules/.bin/ts-node-script

import * as http from "http";
import * as path from "path";
import { promises as fs } from "fs";
import { build } from "./build";
import { astToHtml } from "./inspect";

const port = 3000;
const serveRootPath = path.normalize(process.argv[2] || process.cwd());

console.log(`serving from ${serveRootPath}`);

const handler = async (req: http.IncomingMessage, res: http.ServerResponse) => {
  const url = req.url as string;
  const normalized = path.normalize(url);
  const absolute = path.join(serveRootPath, normalized);

  try {
    await fs.access(absolute);
  } catch (e) {
    res.writeHead(404);
    res.end();
    return;
  }

  console.log(`reading ${absolute}`);
  const src = await fs.readFile(absolute, "utf8");

  const built = build(src);

  res.writeHead(200, { "Content-Type": "text/html" });
  res.write(astToHtml(src, built));
  res.end();
};

http.createServer(handler).listen(port, () => {
  console.log(`App is running on port ${port}`);
});
