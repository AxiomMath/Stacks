module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DerivedSectionsAmplitude
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulGeneration.TruncationCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverFieldDuality
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.DerivedUpperBound
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing complex of a curve has no cohomology below degree `-1`

Let `f : X ⟶ Spec k` be a proper morphism to the spectrum of a field with `X` of topological
Krull dimension at most one — the hypotheses of Situation [Stacks, Tag 0B5D] — and let

  `ω_X^• = f^×(𝒪_{Spec k})`

be the dualizing complex `Stacks.Duality.dualizingComplexOverField f` of [Stacks, Tag 0BS2].
Then `H^j(ω_X^•) = 0` for every `j ≤ -2`; equivalently `ω_X^•` lies in `D^{≥ -1}`.

## Main definitions

* `Stacks.Duality.truncLEQuasiCoherent`: the canonical truncation `τ^{≤ a}` on `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.Duality.isZero_homology_dualizingComplexOverField_of_le_neg_two`: `H^j(ω_X^•) = 0`
  for `j ≤ -2`.
* `Stacks.Duality.isGE_dualizingComplexOverField`: the same, packaged as `ω_X^• ∈ D^{≥ -1}`.
* `Stacks.Duality.isZero_homology_dualizingComplexOverField_of_dim_le` and
  `Stacks.Duality.isGE_dualizingComplexOverField_of_dim_le`: for `X` of dimension at most `d`,
  `H^j(ω_X^•) = 0` for `j ≤ -d-1`, that is `ω_X^• ∈ D^{≥ -d}`.
* `Stacks.Duality.truncLEι_dualizingComplexOverField_eq_zero`: the canonical map
  `τ^{≤ -2}(ω_X^•) ⟶ ω_X^•` is the zero morphism.
* In the namespace `AlgebraicGeometry.CohenMacaulayCurveSituation`,
  `isZero_homology_dualizingComplexOverField_of_le_neg_two` and
  `isGE_dualizingComplexOverField`: the same in Situation [Stacks, Tag 0B5D].

## Implementation notes

The class hypotheses of `DerivedCategory.prop_homologyFunctor_truncLE_obj` must be supplied at the
`X.Modules` spelling of `SheafOfModules.isQuasicoherent X.ringCatSheaf`: at
`SheafOfModules X.ringCatSheaf` instance search looks for a `HasDerivedCategory` instance that
does not exist.

Everything is at the locally small `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, where
`Stacks.Duality.dualizingComplexOverField` lives.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.Duality

/-! ### `D_QCoh(𝒪_X)` is stable under truncation from above -/

/-- **The cohomology sheaves of a canonical truncation from above are quasi-coherent** when those
of the object are. -/
theorem isQuasicoherent_homology_truncLE_obj {X : Scheme.{u}}
    (K : DerivedCategory X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent)
    (a i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE a).obj K)).IsQuasicoherent := by
  let P : ObjectProperty X.Modules := SheafOfModules.isQuasicoherent X.ringCatSheaf
  let : P.IsClosedUnderIsomorphisms :=
    inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderIsomorphisms
  let : P.ContainsZero :=
    inferInstanceAs (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero
  exact DerivedCategory.prop_homologyFunctor_truncLE_obj P K hK a i

/-- **`D_QCoh(𝒪_X)` is stable under the canonical truncations from above**: the truncation
`τ^{≤ a}K` of an object with quasi-coherent cohomology again has quasi-coherent cohomology. -/
def truncLEQuasiCoherent {X : Scheme.{u}} (K : quasiCoherentDerivedCategory X) (a : ℤ) :
    quasiCoherentDerivedCategory X :=
  ⟨(DerivedCategory.TStructure.t.truncLE a).obj K.obj,
    fun i => isQuasicoherent_homology_truncLE_obj K.obj K.property a i⟩

/-! ### The truncation below degree `-dim(X)` maps to zero -/

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

/-- **`H^0(X, τ^{≤ a}K) = 0`** for `K` in `D_QCoh(𝒪_X)` and `a ≤ -d-1`, on a proper `X` of
dimension at most `d`. -/
theorem isZero_derivedCohomologyOverField_truncLE {d : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a : ℤ) (ha : a ≤ -(d : ℤ) - 1)
    (K : quasiCoherentDerivedCategory X) :
    IsZero (derivedCohomologyOverField f (truncLEQuasiCoherent K a).obj 0) :=
  AlgebraicGeometry.isZero_derivedCohomology_of_isLE_of_topologicalKrullDim_le k f hdim _
    (fun j => isQuasicoherent_homology_truncLE_obj K.obj K.property a j) a
    (DerivedCategory.TStructure.t.isLE_truncLE_obj K.obj a a le_rfl) 0 (by omega)

/-- **`H^0(X, τ^{≤ -2}K) = 0`** for `K` in `D_QCoh(𝒪_X)`, on a proper `X` of dimension at most
one. -/
theorem isZero_derivedCohomologyOverField_truncLE_neg_two
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (K : quasiCoherentDerivedCategory X) :
    IsZero (derivedCohomologyOverField f (truncLEQuasiCoherent K (-2)).obj 0) :=
  isZero_derivedCohomologyOverField_truncLE f (d := 1) (by exact_mod_cast hdim) (-2)
    (by norm_num) K

/-- **The canonical map `τ^{≤ a}(ω_X^•) ⟶ ω_X^•` is zero** for every `a ≤ -d-1`, on a proper `X`
of dimension at most `d` over a field. -/
theorem truncLEι_dualizingComplexOverField_eq_zero_of_dim_le {d : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (a : ℤ) (ha : a ≤ -(d : ℤ) - 1) :
    (DerivedCategory.TStructure.t.truncLEι a).app (dualizingComplexOverField f).obj = 0 := by
  exact (dualityAddEquivZero f (truncLEQuasiCoherent (dualizingComplexOverField f) a)).injective
    (((isZero_derivedCohomologyOverField_truncLE f hdim a ha _).eq_of_src _ _).trans (map_zero
      (dualityAddEquivZero f (truncLEQuasiCoherent (dualizingComplexOverField f) a))).symm)

/-- **The canonical map `τ^{≤ -2}(ω_X^•) ⟶ ω_X^•` is zero** on a proper `X` of dimension at most
one. -/
theorem truncLEι_dualizingComplexOverField_eq_zero
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    (DerivedCategory.TStructure.t.truncLEι (-2)).app (dualizingComplexOverField f).obj = 0 :=
  truncLEι_dualizingComplexOverField_eq_zero_of_dim_le f (d := 1) (by exact_mod_cast hdim) (-2)
    (by norm_num)

/-! ### The vanishing -/

/-- **An isomorphism which is the zero morphism has zero target.** -/
theorem isZero_of_isIso_of_eq_zero {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B : C} (φ : A ⟶ B) (hiso : IsIso φ) (hφ : φ = 0) : IsZero B :=
  let := hiso
  IsZero.of_epi_eq_zero φ hφ

/-- **The dualizing complex of a proper `X` of dimension at most `d` over a field has no
cohomology below degree `-d`.** For `f : X ⟶ Spec k` proper with `X` of topological Krull
dimension at most `d`,

  `H^j(f^×(𝒪_{Spec k})) = 0`  for every `j ≤ -d-1`. -/
theorem isZero_homology_dualizingComplexOverField_of_dim_le {d : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (j : ℤ) (hj : j ≤ -(d : ℤ) - 1) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj
      (dualizingComplexOverField f).obj) :=
  isZero_of_isIso_of_eq_zero
    ((DerivedCategory.homologyFunctor X.Modules j).map
      ((DerivedCategory.TStructure.t.truncLEι (-(d : ℤ) - 1)).app
        (dualizingComplexOverField f).obj))
    (Stacks.DerivedTruncation.isIso_homologyMap_truncLEι
      (dualizingComplexOverField f).obj (-(d : ℤ) - 1) j hj)
    (by rw [truncLEι_dualizingComplexOverField_eq_zero_of_dim_le f hdim _ le_rfl,
      Functor.map_zero])

/-- **The dualizing complex of a proper `X` of dimension at most `d` over a field lies in
`D^{≥ -d}`.** Over a field this is the lower half of part (1) of [Stacks, Tag 0AWN] at the
canonical dualizing complex `ω_X^• = f^×(𝒪_{Spec k})`. -/
theorem isGE_dualizingComplexOverField_of_dim_le {d : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    (dualizingComplexOverField f).obj.IsGE (-(d : ℤ)) :=
  (DerivedCategory.isGE_iff (dualizingComplexOverField f).obj (-(d : ℤ))).2 fun j hj =>
    isZero_homology_dualizingComplexOverField_of_dim_le f hdim j (by omega)

/-- **The dualizing complex of a proper curve has no cohomology below degree `-1`.** For
`f : X ⟶ Spec k` proper with `X` of topological Krull dimension at most one,

  `H^j(f^×(𝒪_{Spec k})) = 0`  for every `j ≤ -2`.

This is clause (1) of [Stacks, Tag 0BS2] in the degrees at most `-2`, at the canonical dualizing
complex `f^×(𝒪_{Spec k})`.

[Stacks, Tag 0BS2] (not registered here: this is not the whole statement of the tag): clause (1)
in the degrees at most -2, at the canonical dualizing complex f^×(𝒪_{Spec k}), with no
dualizing-complex hypothesis
-/
theorem isZero_homology_dualizingComplexOverField_of_le_neg_two
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) (j : ℤ) (hj : j ≤ -2) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj
      (dualizingComplexOverField f).obj) :=
  isZero_homology_dualizingComplexOverField_of_dim_le f (d := 1) (by exact_mod_cast hdim) j
    (by push_cast; omega)

/-- **The dualizing complex of a proper curve lies in `D^{≥ -1}`.** -/
theorem isGE_dualizingComplexOverField
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    (dualizingComplexOverField f).obj.IsGE (-1) :=
  (DerivedCategory.isGE_iff (dualizingComplexOverField f).obj (-1)).2 fun j hj =>
    isZero_homology_dualizingComplexOverField_of_le_neg_two f hdim j (by omega)

end Stacks.Duality

namespace AlgebraicGeometry.CohenMacaulayCurveSituation

/-- **The dualizing complex of Situation [Stacks, Tag 0B5D] has no cohomology below degree
`-1`.** -/
theorem isZero_homology_dualizingComplexOverField_of_le_neg_two
    (S : CohenMacaulayCurveSituation.{u}) (j : ℤ) (hj : j ≤ -2) :
    IsZero ((DerivedCategory.homologyFunctor S.X.Modules j).obj
      (Stacks.Duality.dualizingComplexOverField S.f).obj) :=
  Stacks.Duality.isZero_homology_dualizingComplexOverField_of_le_neg_two S.f
    (le_of_eq S.dimension_one) j hj

/-- **The dualizing complex of Situation [Stacks, Tag 0B5D] lies in `D^{≥ -1}`.** -/
theorem isGE_dualizingComplexOverField (S : CohenMacaulayCurveSituation.{u}) :
    (Stacks.Duality.dualizingComplexOverField S.f).obj.IsGE (-1) :=
  Stacks.Duality.isGE_dualizingComplexOverField S.f (le_of_eq S.dimension_one)

end AlgebraicGeometry.CohenMacaulayCurveSituation

end
