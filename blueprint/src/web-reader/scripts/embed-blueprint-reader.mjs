#!/usr/bin/env node

import { readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';

const root = path.resolve(import.meta.dirname, '../../../..');
const output = path.join(root, 'blueprint/web');

export async function embedBlueprintReader() {
  const templatePath = path.join(output, 'index.template.html');
  const indexPath = path.join(output, 'index.html');
  let index;
  try {
    index = await readFile(templatePath, 'utf8');
  } catch (error) {
    if (error.code !== 'ENOENT') throw error;
    index = await readFile(indexPath, 'utf8');
  }
  const dataPlaceholder = '__BLUEPRINT_DATA__';
  if (index.split(dataPlaceholder).length !== 2) {
    throw new Error(`blueprint reader: expected one ${dataPlaceholder} placeholder`);
  }
  const data = JSON.stringify(JSON.parse(
    await readFile(path.join(output, 'data.json'), 'utf8'),
  )).replaceAll('<', '\\u003c');
  await writeFile(indexPath, index.replace(dataPlaceholder, data));
}

if (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(import.meta.filename)) {
  embedBlueprintReader().catch(error => {
    console.error(error);
    process.exitCode = 1;
  });
}
