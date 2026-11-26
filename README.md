# Complex Plane Grapher

A website for graphing complex numbers, loci and regions on the Argand diagram. It has no dependencies and works offline.

**Live site:** https://lukehv.github.io/complex-plane/

**To open it:** double-click `index.html`. You can also serve the folder, e.g. `python3 -m http.server`, and visit http://localhost:8000.

## What you can type (one thing per line)

| You type | You get |
|---|---|
| `3 + 4i`, `2e^(iπ/3)`, `cis(π/4)` | a point, with its modulus and argument |
| `a = 1 + 2i` | a named point you can **drag** |
| `a + b`, `a b`, `conj(a)` | arithmetic on points |
| `\|z - 1 - i\| = 2` | circle (described in words under the line) |
| `\|z - 2\| = \|z + 2i\|` | perpendicular bisector |
| `arg(z - 1) = π/4` | half-line |
| `\|z - 2\| + \|z + 2\| = 6` | ellipse |
| `arg(z - 2) - arg(z + 2) = π/3` | arc |
| `\|z\| < 3 and 0 ≤ arg(z) ≤ π/3` | shaded region (dashed edge for < and >, solid for ≤ and ≥) |
| `\|z\| = 2 and Re(z) ≥ 0` | part of a curve |
| `\|z - 1\| = 2 and arg(z) = π/4` | intersection points |
| `z^5 = 1`, `z^2 = conj(z)` | solutions, plotted and listed |
| `z = 2e^(it)` | parametric curve (you can edit the t range) |
| `r = 1.5` | slider, with a ▶ button to animate it and **+ i** to make it complex |
| `c = 1 + 2i`, `w = 2e^(πi/3)` | complex sliders: Re / Im or modulus / argument (switchable); also draggable |
| `f(z) = z^2 + 1`, then `\|f(z)\| = 2` | your own functions |
| `(z^2 - 1)/(z^2 + 1)` | domain colouring |
| `y = x^2` | Cartesian curves (x = Re z, y = Im z) |

Typing `pi`, `<=` and `>=` turns them into π, ≤ and ≥. Writing `45°` also works.

When you aren't editing a line, it is shown as typeset maths: stacked fractions, real square-root signs, powers, |modulus| bars and conjugate bars. While you type, a live preview appears under the box. Results are given exactly where possible, e.g. `√3/2`, `π/4` and `√13 ≈ 3.606`.

## Using the graph

- Drag to pan. Scroll or pinch to zoom. With the graph focused, arrow keys pan, + / − zoom and 0 resets.
- Hover a line (or edit it) to highlight its graph.
- Double-click the graph to add a point there.
- Click a line's coloured dot to hide it or change its colour.
- Use **Examples** for ready-made graphs, **Display** for the grid and labels, **Share** to copy a link to the graph, and **Save image** to download a PNG.
- Your work is saved in the browser automatically.

## Files

- `index.html`: the page and the help text
- `style.css`: the styling
- `js/complex.js`: complex arithmetic and number formatting
- `js/parser.js`: the expression language: tokenizer, parser and compiler
- `js/mathrender.js`: typesets expressions as HTML maths and formats exact values
- `js/app.js`: analysing each line, drawing (marching squares for loci, Newton's method for solutions) and the interface

## Publishing updates

Run `./scripts/publish-site.sh`. It copies the site files into `upload/complex-plane-grapher` (drag that folder onto Netlify's **Deploys** page) and pushes them to the public [complex-plane](https://github.com/LukeHV/complex-plane) repository that serves the GitHub Pages site. This repository stays private.
