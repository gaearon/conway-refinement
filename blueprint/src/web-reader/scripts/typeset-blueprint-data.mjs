#!/usr/bin/env node

import { createRequire } from 'node:module';
import { readFile, writeFile } from 'node:fs/promises';

const require = createRequire(import.meta.url);
const root = new URL('../../../../', import.meta.url);
const dataUrl = new URL('blueprint/web/data.json', root);
const cssUrl = new URL('blueprint/web/mathjax.css', root);

const macros = {
  Kser: 'K((\\mathbb R^{\\le 0}))', Kfin: 'K(\\mathbb R^{\\le 0})',
  Ph: '\\widehat{\\mathrm P}', Prin: '\\mathrm P',
  RVh: '\\widehat{\\mathrm{RV}}', RV: '\\mathrm{RV}', rv: '\\operatorname{rv}',
  vJ: 'v_J', trunc: ['#1^{|#2}', 2], nsum: '\\oplus', nprod: '\\odot',
  hplus: '\\mathbin{\\hat+}', ot: '\\operatorname{ot}',
  supp: '\\operatorname{supp}', On: '\\mathbf{On}', Oz: '\\mathbf{Oz}',
  No: '\\mathbf{No}', Lsig: '\\mathbf L_\\sigma', Nn: '\\mathrm{Fun}_{0^-}',
  mono: '\\mathsf m', calB: '\\mathcal B', Eser: 'E((\\mathbb R^{\\le 0}))',
  hdot: '\\mathbin{\\hat\\cdot}', partGE: ['{#1}_{\\ge #2}', 2],
  partLT: ['{#1}_{< #2}', 2], nsub: '\\ominus', pol: '\\operatorname{pol}',
  utrunc: ['{#1}_{>#2}', 2], lifts: 'b_{\\mathcal B}', KX: 'K[X]', EX: 'E[X]',
  Fun: '\\mathrm{Fun}_{0^-}', calT: '\\mathcal T',
};

const MathJax = await require('mathjax').init({
  loader: { load: ['input/tex', 'output/chtml'] },
  tex: { macros },
  chtml: { adaptiveCSS: false, fontURL: './mathjax/fonts/woff-v2' },
});
const adaptor = MathJax.startup.adaptor;

function decodeEntities(value) {
  return value
    .replace(/&#x([0-9a-f]+);/gi, (_, hex) => String.fromCodePoint(Number.parseInt(hex, 16)))
    .replace(/&#([0-9]+);/g, (_, decimal) => String.fromCodePoint(Number(decimal)))
    .replaceAll('&lt;', '<').replaceAll('&gt;', '>').replaceAll('&quot;', '"')
    .replaceAll('&#x27;', "'").replaceAll('&amp;', '&');
}

function math(tex, display) {
  const node = MathJax.tex2chtml(decodeEntities(tex), { display });
  return adaptor.outerHTML(node);
}

function typeset(html) {
  return html
    .replace(/\\\[([\s\S]*?)\\\]/g, (_, tex) => math(tex, true))
    .replace(/\\\(([\s\S]*?)\\\)/g, (_, tex) => math(tex, false));
}

function escapeHtml(value) {
  return value.replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;');
}

function descriptionHtml(description) {
  let result = '';
  let cursor = 0;
  for (const match of description.matchAll(/\$([^$\n]+)\$/g)) {
    result += escapeHtml(description.slice(cursor, match.index));
    result += math(match[1], false);
    cursor = match.index + match[0].length;
  }
  return result + escapeHtml(description.slice(cursor));
}

function titleHtml(title) {
  const escaped = title.replaceAll('---', '—').replaceAll('--', '–')
    .replaceAll('\\lbrack', '[').replaceAll('\\rbrack', ']')
    .replaceAll('&', '&amp;').replaceAll('<', '&lt;').replaceAll('>', '&gt;');
  return typeset(escaped.replace(/\$([^$]+)\$/g, '\\($1\\)'));
}

const data = JSON.parse(await readFile(dataUrl, 'utf8'));
data.highlights.descriptionHtml = descriptionHtml(data.highlights.description);
for (const phase of data.phases) {
  phase.descriptionHtml = descriptionHtml(phase.description);
}
for (const node of data.nodes) {
  node.titleHtml = titleHtml(node.title);
  node.statement = typeset(node.statement);
  node.proof = typeset(node.proof);
}
await writeFile(dataUrl, `${JSON.stringify(data, null, 2)}\n`);
await writeFile(cssUrl, `${adaptor.textContent(MathJax.chtmlStylesheet())}\n`);
