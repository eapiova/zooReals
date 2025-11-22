**Equivalence Classes of Reals — Lattice Diagrams**

Legend
- Solid arrow: provable embedding in plain Cubical Agda (no CC/LEM).
- Dashed arrow: relationship that typically requires countable choice or classical principles.
- “quotient” label: representation coincides with Cauchy after quotienting appropriate equivalence.

Mermaid: Plain Cubical Agda (no CC/LEM)

```mermaid
flowchart TB
  %% Dedekind-type
  subgraph A[Dedekind-type]
    R_D[ℝ_D]
    R_formal[ℝ_formal (locale/formal)]
    R_RNO[Sheaf/internal RNO]
    I_subset[[[0,1] ⊆ ℝ_D]]
    Rp_subset[[ℝ⁺ ⊆ ℝ_D]]
  end

  %% Cauchy/HIT-type
  subgraph B[Cauchy / HIT-type]
    R_C[ℝ_C]
    R_FC[ℝ_FC]
    R_I[ℝ_I]
    R_H[ℝ_H]
    R_init[ℝ_init]
    R_ES[ℝ_ES]
  end

  %% Representation-based (raw)
  subgraph C[Representations (raw)]
    R_CF[ℝ_CF]
    R_b[ℝ_b]
    R_SD[ℝ_SD]
  end

  %% Coalgebraic subspaces
  subgraph D[Coalgebraic subspaces]
    I_coalg[[[0,1]_coalg]]
    Rp_coalg[[ℝ⁺_coalg]]
  end

  %% Generalized cuts (weaker)
  subgraph E[Generalized cuts]
    R_L[ℝ_L]
    R_U[ℝ_U]
    R_M[ℝ_M]
  end

  %% Domain-theoretic
  subgraph F[Domain-theoretic]
    R_ID[ℝ_ID]
  end

  %% Axiomatic / universal characterizations
  subgraph G[Axiomatic / universal]
    R_term[ℝ_term]
    R_DedComp[ℝ_DedComp]
    R_Tarski[ℝ_Tarski]
    R_CauComp[ℝ_CauComp]
  end

  %% Isolated/uncertain
  subgraph H[Isolated]
    R_E[ℝ_E (Eudoxus)]
  end

  %% Proven embeddings (solid)
  R_C -->|embed| R_D
  R_FC <--> R_C
  R_I <--> R_C
  R_CF -->|quotient| R_C
  R_b  -->|quotient| R_C
  R_SD -->|quotient| R_C
  R_D --> R_L
  R_D --> R_U
  R_D --> R_M

  %% Subspaces via coalgebras (constructive caveats)
  I_coalg -.->|to [0,1] subspace| I_subset
  Rp_coalg -.->|to ℝ⁺ subspace| Rp_subset

  %% Axiomatic / domain / eudoxus — conditional or unknown
  R_term -.-> R_D
  R_DedComp -.-> R_D
  R_Tarski -.-> R_D
  R_CauComp -.-> R_C
  R_ID -.-> R_D
  R_E -.-> R_C
  R_E -.-> R_D
```

Mermaid: With Countable Choice (illustrative collapse)

```mermaid
flowchart TB
  %% Mainstream reals collapse
  subgraph Main[Mainstream reals]
    R_unified[≃ Dedekind ≃ Cauchy ≃ HIT ≃ (repr. quotients) ≃ axiomatic]
  end

  subgraph Cuts[Generalized cuts]
    R_L[ℝ_L]
    R_U[ℝ_U]
    R_M[ℝ_M]
  end

  subgraph Domain[Domain-theoretic]
    R_ID[ℝ_ID]
  end

  R_unified --> R_L
  R_unified --> R_U
  R_unified --> R_M
  R_ID -.-> R_unified
```

ASCII (plain Cubical Agda)

```
Representations (raw) --quotient--> ℝ_C --embed--> ℝ_D --embed--> ℝ_L, ℝ_U, ℝ_M
     |                               \
     |                                \-- (subspaces) [0,1], ℝ⁺ (via coalgebras; caveats)
     +-- ℝ_CF, ℝ_b, ℝ_SD                

Cauchy/HIT-type: ℝ_C, ℝ_FC, ℝ_I, [ℝ_H, ℝ_init (distinct from ℝ_D constructively)], ℝ_ES

Axiomatic: ℝ_term, ℝ_DedComp, ℝ_Tarski, ℝ_CauComp  ... (classically collapse to mainstream)

Domain-theoretic: ℝ_ID  ... (related to ℝ_D; not provably equivalent)

Eudoxus: ℝ_E  ... (isolated; classically related to Cauchy/Dedekind)
```

Notes
- The arrows ℝ_D → ℝ_L, ℝ_U reflect taking lower/upper cuts; the reverse is not constructive.
- Raw coinductive streams coincide with Cauchy after quotienting; without quotienting, they are not fields.
- HIT/universal (ℝ_H, ℝ_init) remain separate from ℝ_D constructively; embeddings/equivalences require extra principles.
- Axiomatic characterizations (ℝ_term, ℝ_DedComp, ℝ_Tarski, ℝ_CauComp) coincide with mainstream reals classically; constructively they should be kept separate.
- Interval domain ℝ_ID is domain-theoretic; relation to ℝ_D inside Cubical Agda requires additional structure, so it is kept distinct.

