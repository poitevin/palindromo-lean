import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile, writeFile } from 'node:fs/promises';

const snapshot = await readFile(new URL('./versos.js', import.meta.url));
const publishedHash = 'b09f72b387e37f0c3a6187aca6b7546c97f52e4fbecc007d161d1ed19721f3bf';
assert.equal(createHash('sha256').update(snapshot).digest('hex'), publishedHash);

const source = snapshot.toString('utf8');
const exportedPairs = source.match(/^export const pares = (\[[\s\S]*\]);\s*$/m);
assert.ok(exportedPairs, 'Expected a JSON array exported as pares');
const pairs = JSON.parse(exportedPairs[1]);
assert.ok(Array.isArray(pairs));
assert.equal(pairs.length, 100);
for (const pair of pairs) {
  assert.ok(Array.isArray(pair));
  assert.equal(pair.length, 2);
  for (const verse of pair) {
    assert.equal(typeof verse, 'string');
    assert.equal(verse, verse.normalize('NFC'));
    assert.ok(/^[A-Za-zÁÉÍÓÚÜÑáéíóúüñ ,.;:!?¡¿"'(){}\[\]<>…—-]+$/u.test(verse),
      `Unexpected character in verse: ${verse}`);
  }
}

const rows = pairs.map(([first, second]) =>
  `  (${JSON.stringify(first)}, ${JSON.stringify(second)})`);
const generated = `-- Generated from versos.js by verify-source.mjs.
import Std

namespace Palindromo

/-- Verse pairs in the order used by the published reader. -/
def versePairs : Vector (String × String) 100 := #v[
${rows.join(',\n')}
]

end Palindromo
`;
const leanData = new URL('./Palindromo/Versos.lean', import.meta.url);
const [argument, ...rest] = process.argv.slice(2);
assert.equal(rest.length, 0, 'Usage: node verify-source.mjs [--write | path-to-versos.js]');
if (argument === '--write') {
  await writeFile(leanData, generated);
} else {
  assert.equal(await readFile(leanData, 'utf8'), generated, 'Lean verse data differs from the snapshot');
  if (argument) {
    assert.ok(snapshot.equals(await readFile(argument)), 'Supplied file differs from the snapshot');
  }
  console.log(`Verse data verified (SHA-256 ${publishedHash})`);
}
