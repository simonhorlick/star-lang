/**
 * Simple logger that prefixes messages with the module name.
 * Usage:
 *   import { createLogger } from './logger';
 *   const log = createLogger('ModuleName');
 *   log.info('message');
 *   log.error('error message');
 *   log.warn('warning message');
 */

const level = process.env.LOG_LEVEL || "info";

export interface Logger {
  info: (message: string, ...args: any[]) => void;
  error: (message: string | Error, ...args: any[]) => void;
  warn: (message: string, ...args: any[]) => void;
  debug: (message: string, ...args: any[]) => void;
}

export function createLogger(moduleName: string): Logger {
  const prefix = `[${moduleName}]`;

  return {
    info: (message: string, ...args: any[]) => {
      console.log(prefix, message, ...args);
    },
    error: (message: string | Error, ...args: any[]) => {
      if (message instanceof Error) {
        console.error(prefix, message.message, ...args);
        if (message.stack) {
          console.error(message.stack);
        }
      } else {
        console.error(prefix, message, ...args);
      }
    },
    warn: (message: string, ...args: any[]) => {
      console.warn(prefix, message, ...args);
    },
    debug: (message: string, ...args: any[]) => {
      if (level !== "debug") {
        return;
      }
      console.log(prefix, "[DEBUG]", message, ...args);
    },
  };
}
