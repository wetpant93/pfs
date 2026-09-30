# Formalization of Proofs in Graph Theory Using Lean 4
This repository contains the Lean 4 source code accompanying the master's thesis *"A Formalization of Proofs in Graph Theory using Lean 4"*.

## Formalized Proofs:
  * Tutte's characterization of 3-connected graphs
  * auxiliary of the Edmonds-Gallai structure theorem (Theorem 2.2.3 from Diestel's Book).

The main results can be found in `three_connected.lean` and `edmonds_gallai.lean`, respectively.

## Key Theorems
- `three_connected.lean`: tutte_3_connected
- `edmonds_gallai.lean`: aux

In the following let $G = (V, E)$ be a simple graph.

## Overview of Files
* `IsClosed.lean`: Defines *closed* sets (a subset $S \subset V$ is closed if $G$ has no edge between $S$ and $S^c$). Proves that for closed sets the identity $q(G) = q(G[S]) + q(G[S^c])$ holds.
* `IsSeparator.lean` : Defines *vertex-separators* along with elementary lemmas about them.
* `IsVertexConnected.lean` : Defines *vertex-connectivity* using separators; includes basic lemmas concerning `completeGraph` and vertex degrees. 
* `three_connected.lean` : Contains the proof of Tutte's characterization; defines edge contractions on `SimpleGraph`.
* `edmonds_gallai.lean` : Contains the proof of Theorem 2.2.3 from Diestel. Proves it for Edmonds-Gallai sets (i.e., maximal sets where $q(G[S^c]) - |S|$ is maximized).

Aside from the imported Mathlib code, all code is written by me.
