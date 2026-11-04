module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.NoninjectiveAlgebra
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.AffineTwistSections
public import StacksFrontier.LinearAlgebra.SymmetricPower.QuotientPresentation

/-!
# `Sym¹(ℰ) → π_* 𝒪(1)` need not be injective

Stacks 01OC is the example showing that the canonical map
`Symⁿ(ℰ) → π_* 𝒪_{𝐏(ℰ)}(n)` of Stacks 01OB, an isomorphism for `ℰ` locally free, need not even
be injective for `n = 1`.

The base is the affine scheme `S = Spec A` with
`A = k[u, v, s₁, s₂, t₁, t₂] / (-u s₁ + v t₁ + u t₂, v s₁ + u s₂ - v t₂, v s₂, u t₁)`,
the module is `M = (A x ⊕ A y) / A(ū x + v̄ y)` and `ℰ = M̃`, so that the projective bundle is
`P = Proj(Sym_A(M))` — this is the absolute `Proj` of a graded ring, which is how the source
writes it. The distinguished element is the class `m` of `ū s̄₁ x + v̄ t̄₂ y`. The two displayed
congruences of the source force `x m = y m = 0` in `Sym_A(M)`, hence `m` dies on both charts and
so in `Γ(P, 𝒪_P(1))`, while `m ≠ 0`.

## Main definitions

* `symAlgebra`, `symGen`, `symCoeff`: `Sym_A(M)`, its two degree-one generators `x, y`, and the
  images of the classes of the six variables.

## Main results

* `symGen_zero_mul_counterexampleSection` and `symGen_one_mul_counterexampleSection`:
  **`x m = y m = 0` in `Sym_A(M)`**, which is what the two displayed congruences of the source
  say once `ū x + v̄ y` is killed; `symι_mul_counterexampleSection_eq_zero` is the same for every
  degree-one generator.
* `counterexampleSection_mapsTo_zero`: **`m` maps to zero in `Γ(P, 𝒪_P(1))`.**
* `not_injective_toTwistSections`: **`M = Sym¹(ℰ) → Γ(P, 𝒪_P(1))` is not injective**, which is
  the conclusion of the example.
* `isSymmetricAlgebra_toQuotientAlgebra`: **`Sym(M) = A[x, y] / (ū x + v̄ y)`**, the displayed
  identity of the source, with `symmetricAlgebra_relationForm_eq` identifying the relation and
  `symAlgebraEquiv` the resulting algebra isomorphism.
* `iSup_basicOpen_symGen_eq_top` and `basicOpen_symGen_sup_eq_top`: **`P = D₊(x) ∪ D₊(y)`**, the
  affine open covering of `P` the source records.

## Implementation notes

The non-injectivity is stated for the map on global sections over the affine base, which is
where the content is: `π_* 𝒪_P(1)` evaluated on `S = Spec A` is `Γ(P, 𝒪_P(1))` and `Sym¹(ℰ)`
evaluated on `S` is `M`, so a failure of injectivity there is exactly a failure of injectivity
of the map of module sheaves. Stating it on the sheaves themselves would need the twists
`𝒪(n)` of a *relative* `Proj`, which this repository states (as
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`) but does not construct; over the
affine base of this example nothing is lost, since the absolute `Proj` of `Sym_A(M)` is the
projective bundle.

The source takes the base ring to be a field; `CommRing` with `Nontrivial` is enough, and that
is what is assumed here.

## References

* [Stacks Project, Tag 01OC](https://stacks.math.columbia.edu/tag/01OC)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.ProjectiveBundle.Noninjective

variable (R : Type*) [CommRing R]

/-- The symmetric algebra `Sym_A(M)` of Stacks 01OC. Its `Proj` is the projective bundle
`P = 𝐏(ℰ)` of the example. -/
public abbrev symAlgebra := SymmetricAlgebra (coefficientRing R) (presentedModule R)

/-- The canonical map `M → Sym_A(M)`. -/
public abbrev symι : presentedModule R →ₗ[coefficientRing R] symAlgebra R :=
  SymmetricAlgebra.ι (coefficientRing R) (presentedModule R)

/-- The two degree-one generators `x` and `y` of `Sym_A(M)`, the images of the two basis vectors
of `A x ⊕ A y`. -/
public def symGen (i : Fin 2) : symAlgebra R := symι R ((relationSubmodule R).mkQ (Pi.single i 1))

/-- The image in `Sym_A(M)` of the class in `A` of the `i`-th variable. -/
public abbrev symCoeff (i : Fin 6) : symAlgebra R :=
  algebraMap (coefficientRing R) (symAlgebra R) (coefficient R i)

/-- Every vector of `A²` is the combination of the two standard basis vectors. -/
private lemma eq_smul_single_add_smul_single (w : Fin 2 → coefficientRing R) :
    w = w 0 • Pi.single 0 1 + w 1 • Pi.single (1 : Fin 2) 1 := by
  ext i; fin_cases i <;> simp

private lemma symι_mkQ (w : Fin 2 → coefficientRing R) :
    symι R ((relationSubmodule R).mkQ w) = w 0 • symGen R 0 + w 1 • symGen R 1 := by
  conv_lhs => rw [eq_smul_single_add_smul_single R w]
  rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, symGen, symGen]

section SymRelations

private lemma symCoeff_relation_one :
    -(symCoeff R 0 * symCoeff R 2) + symCoeff R 1 * symCoeff R 4 +
      symCoeff R 0 * symCoeff R 5 = 0 := by
  simpa using congrArg (algebraMap (coefficientRing R) (symAlgebra R))
    (coefficient_relation_one R)

private lemma symCoeff_relation_two :
    symCoeff R 1 * symCoeff R 2 + symCoeff R 0 * symCoeff R 3 -
      symCoeff R 1 * symCoeff R 5 = 0 := by
  simpa using congrArg (algebraMap (coefficientRing R) (symAlgebra R))
    (coefficient_relation_two R)

private lemma symCoeff_relation_three : symCoeff R 1 * symCoeff R 3 = 0 := by
  simpa using congrArg (algebraMap (coefficientRing R) (symAlgebra R))
    (coefficient_relation_three R)

private lemma symCoeff_relation_four : symCoeff R 0 * symCoeff R 4 = 0 := by
  simpa using congrArg (algebraMap (coefficientRing R) (symAlgebra R))
    (coefficient_relation_four R)

end SymRelations

/-- The defining relation of `M`, read in `Sym_A(M)`: `ū x + v̄ y = 0`. -/
public theorem symCoeff_mul_symGen_add_eq_zero :
    symCoeff R 0 * symGen R 0 + symCoeff R 1 * symGen R 1 = 0 := by
  have h0 : (relationSubmodule R).mkQ (relationVector R) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, relationSubmodule]
    exact Submodule.mem_span_singleton_self _
  have h := symι_mkQ R (relationVector R)
  rw [h0, map_zero] at h
  simp only [relationVector, Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def] at h
  exact h.symm

/-- The section `m` of Stacks 01OC, read in `Sym_A(M)`: `m = ū s̄₁ x + v̄ t̄₂ y`. -/
public theorem symι_counterexampleSection :
    symι R (counterexampleSection R) =
      symCoeff R 0 * symCoeff R 2 * symGen R 0 + symCoeff R 1 * symCoeff R 5 * symGen R 1 := by
  rw [counterexampleSection, symι_mkQ]
  simp [Algebra.smul_def, map_mul]

/-- **`x m = 0` in `Sym_A(M)`.** This is the first displayed congruence of Stacks 01OC,
`x (ū s̄₁ x + v̄ t̄₂ y) = (s̄₁ x + s̄₂ y)(ū x + v̄ y)`, together with the vanishing of
`ū x + v̄ y`. -/
public theorem symGen_zero_mul_counterexampleSection :
    symGen R 0 * symι R (counterexampleSection R) = 0 := by
  rw [symι_counterexampleSection]
  linear_combination (symCoeff R 2 * symGen R 0 + symCoeff R 3 * symGen R 1) *
      symCoeff_mul_symGen_add_eq_zero R -
    symGen R 0 * symGen R 1 * symCoeff_relation_two R -
    symGen R 1 ^ 2 * symCoeff_relation_three R

/-- **`y m = 0` in `Sym_A(M)`.** This is the second displayed congruence of Stacks 01OC,
`y (ū s̄₁ x + v̄ t̄₂ y) = (t̄₁ x + t̄₂ y)(ū x + v̄ y)`, together with the vanishing of
`ū x + v̄ y`. -/
public theorem symGen_one_mul_counterexampleSection :
    symGen R 1 * symι R (counterexampleSection R) = 0 := by
  rw [symι_counterexampleSection]
  linear_combination (symCoeff R 4 * symGen R 0 + symCoeff R 5 * symGen R 1) *
      symCoeff_mul_symGen_add_eq_zero R -
    symGen R 0 * symGen R 1 * symCoeff_relation_one R -
    symGen R 0 ^ 2 * symCoeff_relation_four R

/-- **Every degree-one generator of `Sym_A(M)` kills `m`.** -/
public theorem symι_mul_counterexampleSection_eq_zero (z : presentedModule R) :
    symι R z * symι R (counterexampleSection R) = 0 := by
  obtain ⟨w, rfl⟩ := (relationSubmodule R).mkQ_surjective z
  rw [symι_mkQ, add_mul, smul_mul_assoc, smul_mul_assoc,
    symGen_zero_mul_counterexampleSection, symGen_one_mul_counterexampleSection,
    smul_zero, smul_zero, add_zero]

/-- The linear form of the relation vector `(ū, v̄)` is `ū x + v̄ y`. -/
public theorem symmetricAlgebra_relationForm_eq :
    SymmetricAlgebra.relationForm (coefficientRing R) (relationVector R) = relationForm R := by
  rw [SymmetricAlgebra.relationForm, Fintype.linearCombination_apply, Fin.sum_univ_two,
    relationForm, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul]
  rfl

/-- **`Sym(M) = A[x, y] / (ū x + v̄ y)`.** This is the displayed identity of Stacks 01OC that
makes the example concrete: `M` is `A x ⊕ A y` modulo the single relation `ū x + v̄ y`, so its
symmetric algebra is the polynomial ring `A[x, y]` modulo the ideal generated by that same
linear form, which `symmetricAlgebra_relationForm_eq` identifies. -/
@[stacks 01OC "the presentation of the symmetric algebra of the module"]
public theorem isSymmetricAlgebra_toQuotientAlgebra :
    IsSymmetricAlgebra
      (SymmetricAlgebra.toQuotientAlgebra (coefficientRing R) (relationVector R)) :=
  SymmetricAlgebra.isSymmetricAlgebra_toQuotientAlgebra _ _

/-- The algebra isomorphism `Sym(M) ≃ A[x, y] / (ū x + v̄ y)` of Stacks 01OC. -/
public def symAlgebraEquiv :
    symAlgebra R ≃ₐ[coefficientRing R]
      SymmetricAlgebra.quotientAlgebra (coefficientRing R) (relationVector R) :=
  SymmetricAlgebra.quotientAlgebraEquiv (coefficientRing R) (relationVector R)

/-- **`m` maps to zero in `Γ(P, 𝒪_P(1))`.** -/
@[stacks 01OC "the section maps to zero in the first twist"]
public theorem counterexampleSection_mapsTo_zero :
    SymmetricAlgebra.toTwistSections (coefficientRing R) (presentedModule R)
      (counterexampleSection R) = 0 :=
  SymmetricAlgebra.toTwistSections_eq_zero_of_forall_mul_eq_zero _ _
    (symι_mul_counterexampleSection_eq_zero R)

/-- **`P = D₊(x) ∪ D₊(y)`**: the two standard opens of the degree-one generators cover the
projective bundle. This is the affine open covering Stacks 01OC records. -/
@[stacks 01OC "the two-chart affine open covering of the projective bundle"]
public theorem iSup_basicOpen_symGen_eq_top :
    ⨆ i : Fin 2, Proj.basicOpen
      (SymmetricAlgebra.grading (coefficientRing R) (presentedModule R)) (symGen R i) = ⊤ := by
  refine SymmetricAlgebra.iSup_basicOpen_eq_top_of_span (coefficientRing R) (presentedModule R)
    (fun i : Fin 2 => (relationSubmodule R).mkQ (Pi.single i 1)) ?_
  have hrange : Set.range (fun i : Fin 2 => (relationSubmodule R).mkQ (Pi.single i 1))
      = (relationSubmodule R).mkQ ''
        Set.range (fun i : Fin 2 => (Pi.single i 1 : Fin 2 → coefficientRing R)) := by
    rw [← Set.range_comp]; rfl
  have hb : Submodule.span (coefficientRing R)
      (Set.range fun i : Fin 2 => (Pi.single i 1 : Fin 2 → coefficientRing R)) = ⊤ := by
    refine le_antisymm le_top fun w _ => ?_
    rw [eq_smul_single_add_smul_single R w]
    exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  rw [hrange, ← Submodule.map_span, hb, Submodule.map_top, Submodule.range_mkQ]

/-- `P = D₊(x) ∪ D₊(y)`, written as a binary union. -/
@[stacks 01OC "the two-chart affine open covering of the projective bundle"]
public theorem basicOpen_symGen_sup_eq_top :
    Proj.basicOpen (SymmetricAlgebra.grading (coefficientRing R) (presentedModule R))
        (symGen R 0) ⊔
      Proj.basicOpen (SymmetricAlgebra.grading (coefficientRing R) (presentedModule R))
        (symGen R 1) = ⊤ := by
  rw [← iSup_basicOpen_symGen_eq_top R]
  refine le_antisymm (sup_le ?_ ?_) (iSup_le fun i => ?_)
  · exact le_iSup (fun i : Fin 2 => Proj.basicOpen
      (SymmetricAlgebra.grading (coefficientRing R) (presentedModule R)) (symGen R i)) 0
  · exact le_iSup (fun i : Fin 2 => Proj.basicOpen
      (SymmetricAlgebra.grading (coefficientRing R) (presentedModule R)) (symGen R i)) 1
  · fin_cases i
    · exact le_sup_left
    · exact le_sup_right

section Nontrivial

variable [Nontrivial R]

/-- **The map `M = Sym¹(ℰ) → Γ(P, 𝒪_P(1))` is not injective.** This is the conclusion of
Stacks 01OC: `m` is a nonzero global section of `ℰ` whose image in `Γ(P, 𝒪_P(1))` is zero, so
the canonical map `Sym¹(ℰ) → π_* 𝒪_{𝐏(ℰ)}(1)` of Stacks 01OB is not injective, and in
particular not an isomorphism. -/
@[stacks 01OC "the map from the first symmetric power is not injective"]
public theorem not_injective_toTwistSections :
    ¬ Function.Injective
      (SymmetricAlgebra.toTwistSections (coefficientRing R) (presentedModule R)) :=
  SymmetricAlgebra.not_injective_toTwistSections _ _ (counterexampleSection_ne_zero R)
    (symι_mul_counterexampleSection_eq_zero R)

end Nontrivial

end Stacks.ProjectiveBundle.Noninjective

end
