import { cp, mkdir, rm } from 'node:fs/promises';
import { resolve } from 'node:path';

const jscoqSource = resolve('node_modules/jscoq');
const jscoqDestination = resolve('_build/html/_static/vendor/jscoq');
const examplesSource = resolve('examples');
const examplesDestination = resolve('_build/html/_static/rocq/examples');

await mkdir(resolve('_build/html/_static/vendor'), { recursive: true });
await rm(jscoqDestination, { recursive: true, force: true });
await cp(jscoqSource, jscoqDestination, { recursive: true, force: true });

await rm(examplesDestination, { recursive: true, force: true });
await cp(examplesSource, examplesDestination, {
  recursive: true,
  force: true,
  filter: source => !['.aux', '.glob', '.vo', '.vok', '.vos']
    .some(extension => source.endsWith(extension)),
});

console.log(`jsCoq assets copied to ${jscoqDestination}`);
console.log(`Coq examples copied to ${examplesDestination}`);
