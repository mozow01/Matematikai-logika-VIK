import { cp, mkdir, rm } from 'node:fs/promises';
import { resolve } from 'node:path';

const jscoqSource = resolve('node_modules/jscoq');
const jscoqDestination = resolve('_build/html/_static/vendor/jscoq');
const examplesSource = resolve('examples');
const examplesDestination = resolve('_build/html/_static/rocq/examples');
const lessonTenSource = resolve('10');
const lessonTenDestination = resolve('_build/html/10');

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

await rm(lessonTenDestination, { recursive: true, force: true });
await cp(lessonTenSource, lessonTenDestination, { recursive: true, force: true });

console.log(`jsCoq assets copied to ${jscoqDestination}`);
console.log(`Coq examples copied to ${examplesDestination}`);
console.log(`Lesson 10 materials copied to ${lessonTenDestination}`);
