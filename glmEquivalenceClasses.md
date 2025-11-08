

Of course. Here is a summary of the first 23 definitions of real numbers, grouped into their equivalence classes within **Cubical Agda**, along with a description of the relationships between these classes.

---

### **Equivalence Classes of Real Numbers (Definitions 1-23)**

The definitions fall into four distinct equivalence classes. The most important distinction is between the Dedekind and Cauchy constructions, which are not provably equivalent in a constructive setting.

---

### **Equivalence Class 1: The Dedekind Reals (`ℝ_D`)**

This class comprises definitions based on cuts of the rational numbers. They are topologically complete (every inhabited bounded subset has a supremum) and form a complete lattice. In constructive mathematics, this is the standard "real numbers object" in a topos.

**Members:**
1.  **`ℝ_D` (Dedekind Reals):** Located Dedekind cuts in ℚ.
8.  **`ℝ_ID` (Interval Domain Reals):** Maximal elements of the interval domain.
14. **`ℝ_formal` (Formal Reals):** Points of the locale of real numbers.
17. **`ℝ_DedComp` (Dedekind Complete Ordered Field):** The axiomatic characterization.
19. **`ℝ_Tarski` (Archimedean Tarski Group Reals):** Constructively characterizes `ℝ_D`.
16. **`ℝ_term` (Terminal Archimedean Ordered Field):** `ℝ_D` has this terminal property.
20. **`[0,1]_coalg` (Unit Interval as Terminal Coalgebra):** Equivalent to the subset `[0,1]` of `ℝ_D`.
21. **`ℝ⁺_coalg` (Positive Reals as Terminal Coalgebra):** Equivalent to the subset `ℝ⁺` of `ℝ_D`.
22. **Sheaf-Theoretic Reals:** The internal real numbers object in a topos is `ℝ_D`.
23. **Real Numbers Object (in a topos):** Same as above.

---

### **Equivalence Class 2: The Cauchy Reals (`ℝ_C`)**

This class consists of definitions based on sequences with explicit convergence information. They are analytically complete (every Cauchy sequence converges) and form the *initial* sequentially Cauchy-complete Archimedean ordered field.

**Members:**
2.  **`ℝ_C` (Cauchy Reals):** Modulated Cauchy sequences of ℚ, quotiented.
3.  **`ℝ_E` (Eudoxus Reals):** Almost-homomorphisms ℤ → ℤ.
4.  **`ℝ_FC`, `ℝ_I` (Fast Cauchy / Interval Reals):** Cauchy sequences with explicit error bounds.
12. **`ℝ_H` (HIT / HoTT Book Reals):** Defined by a universal property.
13. **`ℝ_ES` (Escardó–Simpson Reals):** The least Cauchy-complete subset of `ℝ_D`.
15. **`ℝ_init` (Initial Sequentially Modulated...):** The universal property defining `ℝ_H`.
18. **`ℝ_CauComp` (Cauchy Complete Ordered Field):** The axiomatic characterization.

---

### **Equivalence Class 3: Representations (Quotiented to Cauchy)**

These definitions use infinite streams of digits to represent real numbers. The raw stream type is not a field due to non-unique representations (e.g., `0.999...` vs. `1.000...`). However, the **quotient** of this type by the appropriate equivalence relation is equivalent to the Cauchy reals.

**Members:**
5.  **`ℝ_CF` (Continued Fraction Reals):** Infinite continued fractions.
6.  **`ℝ_b` (Coinductive Base-b Reals):** Infinite decimal/binary streams.
7.  **`ℝ_SD` (Signed-Digit Reals):** Infinite streams over `{−1, 0, 1}`.

---

### **Equivalence Class 4: Generalized Cuts (Strictly Weaker)**

These are constructive generalizations of the Dedekind reals, formed by removing essential axioms like locatedness. They are strictly larger and less well-behaved than the Dedekind reals and are not equivalent to any other class.

**Members:**
9.  **`ℝ_L` (Lower Reals):** Rounded lower subsets of ℚ (no locatedness).
10. **`ℝ_U` (Upper Reals):** The dual of lower reals.
11. **`ℝ_M` (MacNeille Reals):** Double-negation closed cuts.

---

### **Relations Between the Equivalence Classes**

| Class 1: Dedekind (`ℝ_D`) | Class 2: Cauchy (`ℝ_C`) | Class 3: Representations | Class 4: Generalized Cuts |
| :------------------------ | :---------------------- | :----------------------- | :------------------------ |
| `ℝ_D`, `ℝ_ID`, `ℝ_formal` | `ℝ_C`, `ℝ_E`, `ℝ_H`    | `ℝ_CF`, `ℝ_b`, `ℝ_SD`   | `ℝ_L`, `ℝ_U`, `ℝ_M`      |

1.  **Class 1 (Dedekind) vs. Class 2 (Cauchy): Not Equivalent**
    *   There is a canonical, provable embedding **`ℝ_C → ℝ_D`**. Every Cauchy real defines a located Dedekind cut.
    *   The reverse map **`ℝ_D → ℝ_C`** is **not provable** in Cubical Agda. Constructing a Cauchy sequence from an arbitrary Dedekind cut requires the **Axiom of Countable Choice**, which is not a theorem of constructive type theory.
    *   Therefore, `ℝ_D` and `ℝ_C` are distinct objects. `ℝ_D` is generally "larger" or more general in the sense that it contains limits of more sequences (e.g., Specker sequences).

2.  **Class 3 (Representations) → Class 2 (Cauchy): Quotient Equivalence**
    *   The types in Class 3 are *pre-real* types. There is a quotient map from each of these types onto the Cauchy reals.
    *   **`Quotient(ℝ_CF) ≃ ℝ_C`**, **`Quotient(ℝ_b) ≃ ℝ_C`**, etc.
    *   The relationship is that the representations are a concrete, computational way to describe Cauchy reals, modulo the ambiguity of non-unique digit expansions.

3.  **Class 4 (Generalized Cuts) vs. All Others: Distinct and Weaker**
    *   The types in Class 4 are fundamentally different and not equivalent to `ℝ_D` or `ℝ_C`.
    *   There are embeddings **`ℝ_L → ℝ_D`** and **`ℝ_U → ℝ_D`**, but they are not surjections. `ℝ_L` and `ℝ_U` contain "fuzzy" reals that cannot be pinpointed by a cut, and `ℝ_M` is a different kind of completion altogether.
    *   They are intentionally weaker objects, useful in certain constructive contexts but not a suitable definition for the archimedean field of real numbers.