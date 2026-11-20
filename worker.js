'use strict';
importScripts('engine.js?v=1');
onmessage=e=>{try{let puzzle;for(let attempt=0;attempt<12;attempt++){puzzle=NumberoxEngine.generate(e.data.size,e.data.difficulty,e.data.seed+(attempt?'-'+attempt:''));if(puzzle.rating.label===e.data.difficulty)break;}postMessage({puzzle});}catch(err){postMessage({error:'generation-failed'});}};
