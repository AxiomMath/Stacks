module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.UnitHom
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingFirstCohomologyDimension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingRiemannRoch
import StacksCore.Tactic.StacksAttribute

/-!
# `χ(X, 𝒪_X) = -χ(X, ω_X)` for the dualizing sheaf of a proper curve

In Situation [Stacks, Tag 0B5D] — a field `k` and a proper one-dimensional `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k` — let `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` be the dualizing sheaf of
[Stacks, Tag 0BS2]. This file proves, for that sheaf and with nothing left over,

* the duality `Hⁱ(X, ω_X) = Hom_k(H^{1-i}(X, 𝒪_X), k)` in the two degrees `i = 0, 1` that the
  proof of Lemma 53.5.1 of Section [Stacks, Tag 0B5B] reads off `Hⁱ(X, ω_X^•) =
  Hom_k(H^{-i}(X, 𝒪_X), k)`, and
* **Lemma 53.5.1 itself: `χ(X, 𝒪_X) = -χ(X, ω_X)`.**

`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingRiemannRoch.lean` states the
same two results for an arbitrary `ω` together with the two isomorphisms as data, which is what
a consumer carrying a dualizing sheaf of its own needs; here those data are produced, so
nothing is left to supply.

## Main definitions

The elided prefix is `AlgebraicGeometry.CohenMacaulayCurveSituation`.

* `FirstCohomologyDuality.dualLinearEquiv`: clause (5) of [Stacks, Tag 0BS2] as an isomorphism
  of `k`-vector spaces, `Hom(ℱ, ω) ≃ₗ[k] Hom_k(H¹(X, ℱ), k)`.
* `cohomologyOverFieldZeroDualizingSheafLinearEquiv`: **the duality at `i = 1`**,
  `H⁰(X, ω_X) ≃ₗ[k] Hom_k(H¹(X, 𝒪_X), k)`.
* `cohomologyOverFieldOneDualizingSheafLinearEquiv`: **the duality at `i = 0`**,
  `H¹(X, ω_X) ≃ₗ[k] Hom_k(H⁰(X, 𝒪_X), k)`.

## Main results

* `finrank_cohomologyOverField_zero_dualizingSheaf_eq_finrank_unit_one`:
  `dim_k H⁰(X, ω_X) = dim_k H¹(X, 𝒪_X)`.
* `finsum_alternating_finrank_unit_eq_neg_dualizingSheaf`: **`χ(X, 𝒪_X) = -χ(X, ω_X)`.**

## Where the two dualities come from

**At `i = 1`, from clause (5).** Clause (5) of [Stacks, Tag 0BS2] — proved unconditionally as
`firstCohomologyDuality_dualizingSheafOverField` — says `Hom(ℱ, ω_X) = Hom_k(H¹(X, ℱ), k)` for
quasi-coherent `ℱ`. At `ℱ = 𝒪_X` the left-hand side is `H⁰(X, ω_X)`, by
`AlgebraicGeometry.unitHomLinearEquivCohomologyOverFieldZero`. Clause (5) is stated as an
isomorphism of abelian groups, which counts no dimension over `k`; its `k`-linearity is
`FirstCohomologyDuality.dual_smul`, and that is its own naturality at `a • 𝟙 ℱ` together with
`AlgebraicGeometry.rightDerived_evaluation_map_smul_id_apply`, which says `H¹(X, a • 𝟙)` is
multiplication by `a`. No Cohen--Macaulay hypothesis and no [Stacks, Tag 0BS3] enters: clause
(5) needs only that `ω_X^•` has no cohomology below degree `-1`.

**At `i = 0`, from clause (4) and the two dimension counts.** Clause (4) of [Stacks, Tag 0BS2]
in degree zero identifies `Hom_{D(𝒪_X)}(𝒪_X[0], ω_X^•)` with `Hom_k(H⁰(X, 𝒪_X), k)`, which is a
line (`finrank_hom_unit_dualizingComplex_eq_one`), and `H¹(X, ω_X)` embeds `k`-linearly in that
morphism group along the canonical map `ω_X[0]⟦1⟧ = τ^{≤ -1}(ω_X^•) ⟶ ω_X^•`
(`exists_injective_firstCohomology_to_hom_dualizingComplex`). Since `H¹(X, ω_X)` is a line too
(`finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one`), that embedding is
surjective, and the composite is the required isomorphism. Identifying `ω_X^•` with `ω_X[1]`,
which is [Stacks, Tag 0BS3], would make the embedding an isomorphism directly; it is not used
and is not available here.

## Why the Euler characteristics are written as alternating sums

`AlgebraicGeometry.eulerCharacteristic` is the alternating sum `∑ₙ (-1)ⁿ dim_k Hⁿ(X, ℱ)` by
`AlgebraicGeometry.eulerCharacteristic_eq_finsum`, but its signature demands
`SheafOfModules.IsCoherent ℱ`. For `ω_X` that is the coherence assertion of clause (2) of
[Stacks, Tag 0BS2]; `Stacks.Duality.isCoherent_homology_of_isDualizingComplex` gives it only
once `f^×(𝒪_{Spec k})` is known to be a dualizing complex, which is clause (4)(a) of
[Stacks, Section 0AU3] (`Stacks.Duality.isDualizingComplex_upperShriek_obj`, read at `f^× = f^!`
for the proper `f`); that reading is not carried out here. The
conclusion below is therefore stated with both Euler characteristics written out as the sums
that define them, so that only the quasi-coherence of `ω_X`
(`Stacks.Duality.isQuasicoherent_dualizingSheafOverField`) is needed. A consumer that does have
the coherence instance obtains the statement in the `AlgebraicGeometry.eulerCharacteristic`
spelling from `eulerCharacteristic_unit_eq_neg_eulerCharacteristic_of_unitDual` applied to the
two isomorphisms of this file.

## References

* [Stacks Project, Tag 0B5B](https://stacks.math.columbia.edu/tag/0B5B)
* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Duality.DerivedPushforward (derivedStructureSheaf)

universe u

namespace AlgebraicGeometry

namespace CohenMacaulayCurveSituation

variable {S : CohenMacaulayCurveSituation.{u}}

/-! ### Clause (5) of Tag 0BS2 as an isomorphism of `k`-vector spaces -/

/-- **Clause (5) of [Stacks, Tag 0BS2] commutes with the action of `k`.** Writing `a • φ` as
`(a • 𝟙 ℱ) ≫ φ` and applying the naturality
`AlgebraicGeometry.CohenMacaulayCurveSituation.FirstCohomologyDuality.dual_comp` turns the
scalar into `H¹(X, a • 𝟙 ℱ)`, which is multiplication by `a` because `H¹(X, -)` is a `k`-linear
functor (`AlgebraicGeometry.rightDerived_evaluation_map_smul_id_apply`). -/
theorem FirstCohomologyDuality.dual_smul {ω : S.X.Modules} (hdual : S.FirstCohomologyDuality ω)
    (F : S.X.Modules) (hF : F.IsQuasicoherent) (a : S.k) (φ : F ⟶ ω) :
    letI := Scheme.Modules.linearOverBase S.f
    hdual.dual F hF (a • φ) = a • hdual.dual F hF φ := by
  let := Scheme.Modules.linearOverBase S.f
  have hsmul : a • φ = (a • 𝟙 F) ≫ φ := by
    rw [Linear.smul_comp, Category.id_comp]
  refine Eq.trans (congrArg (fun z => hdual.dual F hF z) hsmul) ?_
  refine Eq.trans (hdual.dual_comp F F hF hF (a • 𝟙 F) φ) ?_
  refine LinearMap.ext fun x => ?_
  have hx : (cohomologyOverFieldMap S.k S.f (a • 𝟙 F) 1).hom x = a • x := by
    with_unfolding_all exact rightDerived_evaluation_map_smul_id_apply S.f 1 a F x
  exact (congrArg (hdual.dual F hF φ) hx).trans (map_smul _ a x)

/-- **Clause (5) of [Stacks, Tag 0BS2] as an isomorphism of `k`-vector spaces**:
`Hom(ℱ, ω) ≃ₗ[k] Hom_k(H¹(X, ℱ), k)` for a quasi-coherent `ℱ`. This is the bijection carried by
`AlgebraicGeometry.CohenMacaulayCurveSituation.FirstCohomologyDuality` together with its
`k`-linearity, and it is the form in which clause (5) counts dimensions over `k`. -/
def FirstCohomologyDuality.dualLinearEquiv {ω : S.X.Modules}
    (hdual : S.FirstCohomologyDuality ω) (F : S.X.Modules) (hF : F.IsQuasicoherent) :
    letI := Scheme.Modules.linearOverBase S.f
    (F ⟶ ω) ≃ₗ[S.k] (cohomologyOverField S.k S.f F 1 →ₗ[S.k] S.k) :=
  letI := Scheme.Modules.linearOverBase S.f
  { __ := hdual.dual F hF
    map_smul' := fun a φ => hdual.dual_smul F hF a φ }

/-! ### The duality at `i = 1` -/

/-- **`H⁰(X, ω_X) ≃ₗ[k] Hom_k(H¹(X, 𝒪_X), k)`** in Situation [Stacks, Tag 0B5D], at the
dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` of [Stacks, Tag 0BS2].

This is the `i = 1` half of the duality `Hⁱ(X, ω_X^•) = Hom_k(H^{-i}(X, 𝒪_X), k)` that the proof
of Lemma 53.5.1 of Section [Stacks, Tag 0B5B] uses, read in the Cohen--Macaulay case
`ω_X^• = ω_X[1]`. It is clause (5) of [Stacks, Tag 0BS2] at `ℱ = 𝒪_X`, which is proved
unconditionally as `firstCohomologyDuality_dualizingSheafOverField`, together with the
identification of `Hom(𝒪_X, ω_X)` with `H⁰(X, ω_X)`. -/
def cohomologyOverFieldZeroDualizingSheafLinearEquiv (S : CohenMacaulayCurveSituation.{u}) :
    cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 0 ≃ₗ[S.k]
      (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 1 →ₗ[S.k] S.k) :=
  letI := Scheme.Modules.linearOverBase S.f
  (unitHomLinearEquivCohomologyOverFieldZero S.f
      (Stacks.Duality.dualizingSheafOverField S.f)).symm.trans
    ((firstCohomologyDuality_dualizingSheafOverField S).dualLinearEquiv
      (Stacks.Ample.unitModule S.X)
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit S.X))

/-! ### The duality at `i = 0` -/

/-- **`H¹(X, ω_X) ≃ₗ[k] Hom_k(H⁰(X, 𝒪_X), k)`** in Situation [Stacks, Tag 0B5D], at the
dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` of [Stacks, Tag 0BS2].

This is the `i = 0` half of the duality `Hⁱ(X, ω_X^•) = Hom_k(H^{-i}(X, 𝒪_X), k)` that the proof
of Lemma 53.5.1 of Section [Stacks, Tag 0B5B] uses. It is the `k`-linear injection of
`exists_injective_firstCohomology_to_hom_dualizingComplex`, which composes `H¹(X, ω_X) =
Hom_{D(𝒪_X)}(𝒪_X[0], ω_X[0]⟦1⟧)` with the canonical map `ω_X[0]⟦1⟧ = τ^{≤ -1}(ω_X^•) ⟶ ω_X^•`,
followed by clause (4) of [Stacks, Tag 0BS2] in degree zero read `k`-linearly
(`Stacks.Duality.dualityLinearEquivZero`). The injection is surjective because both sides are
lines: the source by `finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one` and the
target by `finrank_hom_unit_dualizingComplex_eq_one`. [Stacks, Tag 0BS3], which would identify
`ω_X^•` with `ω_X[1]` and make the injection an isomorphism directly, is not used.

[Stacks, Tag 0B5B] (not registered here: this is not the whole statement of the tag): the
identification H^1(X, omega_X) = Hom_k(H^0(X, O_X), k) that the proof of Lemma 53.5.1 of this
section reads off the duality H^i(X, omega^bullet) = Hom_k(H^(-i)(X, O_X), k) at i = 0, at the
canonical dualizing sheaf omega_X = H^(-1)(f^x(O_Spec k)) of Tag 0BS2 and with nothing left to
supply: it is clause (4) of Tag 0BS2 in degree zero, proved k-linearly, against the canonical
injection of H^1(X, omega_X) into Hom_D(O_X[0], omega^bullet), which is onto because both sides
are lines. The equality dim_k H^1(X, omega_X) = 1 that the proof reads off it is
finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one

[Stacks, Tag 0BS5] (not registered here: this is not the whole statement of the tag): the i = 0
half of the identification H^i(X, omega^bullet) = H^(-i)(X, O_X)^dual in the proof, at the
canonical dualizing sheaf and proved rather than supplied: clause (4) of Tag 0BS2 in degree zero,
read k-linearly, against the canonical injection of H^1(X, omega_X) into Hom_D(O_X[0],
omega^bullet); the Cohen-Macaulay identification omega^bullet = omega[1] of Tag 0BS3 is not used
-/
def cohomologyOverFieldOneDualizingSheafLinearEquiv (S : CohenMacaulayCurveSituation.{u}) :
    cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1 ≃ₗ[S.k]
      (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 0 →ₗ[S.k] S.k) :=
  letI := Scheme.Modules.linearOverBase S.f
  letI : Functor.Linear S.k (globalSectionsOver S.f) := globalSectionsOver_linear_linearOverBase S.f
  haveI : FiniteDimensional S.k
      (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 1) :=
    finiteDimensional_cohomologyOverField_one_dualizingSheaf S
  haveI : FiniteDimensional S.k ((derivedStructureSheaf S.X).obj ⟶
      (Stacks.Duality.dualizingComplexOverField S.f).obj) :=
    FiniteDimensional.of_finrank_pos (by
      rw [finrank_hom_unit_dualizingComplex_eq_one S]; omega)
  ((exists_injective_firstCohomology_to_hom_dualizingComplex S).choose.linearEquivOfInjective
      (exists_injective_firstCohomology_to_hom_dualizingComplex S).choose_spec (by
        rw [finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one S,
          finrank_hom_unit_dualizingComplex_eq_one S])).trans
    ((Stacks.Duality.dualityLinearEquivZero S.f (derivedStructureSheaf S.X)).trans
      (Stacks.Duality.derivedCohomologyOverFieldDualLinearEquiv S.f
        (Stacks.Ample.unitModule S.X) 0 0 rfl))

/-! ### Lemma 53.5.1 of Section 0B5B at the canonical dualizing sheaf -/

/-- **`dim_k H⁰(X, ω_X) = dim_k H¹(X, 𝒪_X)`** in Situation [Stacks, Tag 0B5D]: the duality at
`i = 1` reads `H⁰(X, ω_X)` as the `k`-linear dual of `H¹(X, 𝒪_X)`, and a `k`-vector space and
its dual have the same dimension. -/
theorem finrank_cohomologyOverField_zero_dualizingSheaf_eq_finrank_unit_one
    (S : CohenMacaulayCurveSituation.{u}) :
    Module.finrank S.k
        (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) 0) =
      Module.finrank S.k
        (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) 1) := by
  rw [(cohomologyOverFieldZeroDualizingSheafLinearEquiv S).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- **Lemma 53.5.1 of Section [Stacks, Tag 0B5B] at the canonical dualizing sheaf:**
`χ(X, 𝒪_X) = -χ(X, ω_X)` in Situation [Stacks, Tag 0B5D], for
`ω_X = H^{-1}(f^×(𝒪_{Spec k}))`.

Both Euler characteristics are written as the alternating sums of dimensions that define
`AlgebraicGeometry.eulerCharacteristic`; see the module documentation for why. Both collapse to
`h⁰ - h¹` because `X` is one-dimensional, so [Stacks, Tag 02UZ] kills cohomology above degree
one. The duality gives `dim_k H⁰(X, ω_X) = dim_k H¹(X, 𝒪_X)`, and `dim_k H¹(X, ω_X) = 1` and
`dim_k H⁰(X, 𝒪_X) = 1` in Situation [Stacks, Tag 0B5D], so
`χ(X, ω_X) = dim_k H¹(X, 𝒪_X) - 1 = -χ(X, 𝒪_X)`.

[Stacks, Tag 0B5B] (not registered here: this is not the whole statement of the tag): Lemma 53.5.1
in the Cohen-Macaulay case, chi(X, O_X) = - chi(X, omega_X), at the canonical dualizing sheaf
omega_X = H^(-1)(f^x(O_Spec k)) of Tag 0BS2 and with nothing left to supply: the duality H^i(X,
omega^bullet) = Hom_k(H^(-i)(X, O_X), k) in the two degrees is proved here from clause (4) and
clause (5) of Tag 0BS2, both of which are proved, and what is proved on top of it is the collapse
of both Euler characteristics to h^0 - h^1 by Tag 02UZ and the passage from the duality to the
equality through H^0(X, O_X) = k of Situation 0B5D. Both Euler characteristics are written as the
alternating sums of dimensions that define AlgebraicGeometry.eulerCharacteristic, which is what
lets the statement avoid the coherence of omega_X of clause (2) of Tag 0BS2

[Stacks, Tag 0BS5] (not registered here: this is not the whole statement of the tag): the
Cohen-Macaulay conclusion chi(X, O_X) = - chi(X, omega_X) at the canonical dualizing sheaf, with
the identification H^i(X, omega^bullet) = H^(-i)(X, O_X)^dual of the proof proved rather than
supplied, from clauses (4) and (5) of Tag 0BS2; Tag 0BS3 is not used
-/
theorem finsum_alternating_finrank_unit_eq_neg_dualizingSheaf
    (S : CohenMacaulayCurveSituation.{u}) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank S.k
          (cohomologyOverField S.k S.f (SheafOfModules.unit S.X.ringCatSheaf) n) : ℤ)) =
      -(∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank S.k
        (cohomologyOverField S.k S.f (Stacks.Duality.dualizingSheafOverField S.f) n) : ℤ)) := by
  have hvan : ∀ (M : S.X.Modules) (m : ℕ), 2 ≤ m →
      IsZero (cohomologyOverField S.k S.f M m) := fun M m hm =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le S.k S.f M (d := 1)
      (le_of_eq S.dimension_one) (by omega)
  rw [finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero S.k S.f
      (Stacks.Duality.dualizingSheafOverField S.f) (hvan _),
    finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero S.k S.f
      (SheafOfModules.unit S.X.ringCatSheaf) (hvan _),
    finrank_cohomologyOverField_unit_zero_eq_one S.f,
    finrank_cohomologyOverField_one_dualizingSheafOverField_eq_one S,
    finrank_cohomologyOverField_zero_dualizingSheaf_eq_finrank_unit_one S]
  push_cast
  ring

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
