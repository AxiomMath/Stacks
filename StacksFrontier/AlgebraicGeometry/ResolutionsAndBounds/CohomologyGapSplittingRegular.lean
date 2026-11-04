module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Field.ULift
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.RingTheory.KrullDimension.Field
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.CohomologyGapSplitting
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.RegularExtVanishing.Basic

/-!
# The cohomology-gap splitting on a regular scheme, and its dimension-zero case

[Stacks, Tag 0FZ4] says: let `X` be a regular Noetherian scheme of dimension `d < ∞`, let
`K ∈ D^b_{Coh}(𝒪_X)` and `a ∈ ℤ`; if `H^i(K) = 0` for `a < i < a + d`, then
`K = τ^{≤ a} K ⊕ τ^{≥ a + d} K`.

The source's proof begins with `τ^{≤ a} K = τ^{≤ a + d - 1} K`, which holds for `d ≥ 1` but not
for `d = 0`, and the statement itself fails at `d = 0`: on the spectrum of a field, a regular
Noetherian scheme of dimension `0`, the structure sheaf placed in degree `a` satisfies the empty
gap condition, but both `τ^{≤ a}` and `τ^{≥ a}` keep its degree-`a` cohomology, so the claimed sum
would have `𝒪_X ⊕ 𝒪_X` where the complex has `𝒪_X`. This file proves that failure, and proves
the corrected statement: under exactly the source's hypotheses,
`K ≅ τ^{≤ a + d - 1} K ⊕ τ^{≥ a + d} K` for every `d`, and `K ≅ τ^{≤ a} K ⊕ τ^{≥ a + d} K` for
`0 < d`. The connecting morphism of the truncation triangle vanishes by [Stacks, Tag 0FZ3] (2),
`AlgebraicGeometry.separatedCohomologyHomVanishing`.

## Main results

* `AlgebraicGeometry.exists_iso_biprod_truncations_of_isRegular`: [Stacks, Tag 0FZ4], corrected
  at `d = 0`.

* `AlgebraicGeometry.not_nonempty_iso_biprod_self_of_iso_unit`: on a nonempty scheme a module
  isomorphic to `𝒪_X` is not isomorphic to its own direct square.
* `AlgebraicGeometry.not_nonempty_iso_biprod_truncLE_truncGE_singleFunctor_unit`: the structure
  sheaf in degree `a` is not `τ^{≤ a} ⊕ τ^{≥ a}` of itself.
* `AlgebraicGeometry.not_forall_nonempty_iso_biprod_truncLE_truncGE_of_dim_zero`: the statement
  of Tag 0FZ4 at `d = 0` is false.

## Implementation notes

The structure sheaf is handled through a module `M : X.Modules` given with an isomorphism to
`SheafOfModules.unit X.ringCatSheaf`, rather than through `SheafOfModules.unit` itself: the
latter has type `SheafOfModules X.ringCatSheaf`, at which the biproduct and t-structure
instances of `X.Modules` are not found.

`HasDerivedCategory.standard` is made a local instance at high priority, so that every derived
category here, in the counterexample as in the corrected statement, is the one
`AlgebraicGeometry.exists_iso_biprod_truncations` is stated in; the imports also provide other
`HasDerivedCategory` instances on `X.Modules`.

## References

* [Stacks Project, Tag 0FZ4](https://stacks.math.columbia.edu/tag/0FZ4)
* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- On a nonempty scheme a module isomorphic to the structure sheaf is not isomorphic to its own
direct square: on global sections such an isomorphism would be a linear isomorphism
`R ≃ R × R` over the nonzero ring `R = Γ(X, X)`, and the two sides have ranks `1` and `2`. -/
theorem not_nonempty_iso_biprod_self_of_iso_unit (X : Scheme.{u}) [Nonempty X] (M : X.Modules)
    (hM : Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf)) : ¬ Nonempty (M ≅ M ⊞ M) := by
  rintro ⟨e⟩
  obtain ⟨u⟩ := hM
  let F : X.Modules ⥤ ModuleCat (X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))) :=
    SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))
  have : F.Additive :=
    inferInstanceAs (SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  let R := X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  have : Nontrivial Γ(X, ⊤) := Scheme.component_nontrivial X ⊤
  have : Nontrivial R := inferInstanceAs (Nontrivial Γ(X, ⊤))
  have : StrongRankCondition R := inferInstanceAs (StrongRankCondition Γ(X, ⊤))
  let l := (F.mapIso u.symm ≪≫ F.mapIso e ≪≫ F.mapBiprod _ _ ≪≫
    biprod.mapIso (F.mapIso u) (F.mapIso u) ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  have h := l.finrank_eq
  change Module.finrank R R = Module.finrank R (R × R) at h
  rw [Module.finrank_prod, Module.finrank_self] at h
  omega

/-- On a nonempty scheme, the structure sheaf placed in degree `a` is not the direct sum of its
truncations `τ^{≤ a}` and `τ^{≥ a}`: both truncations keep the degree-`a` cohomology, so the sum
would have `𝒪_X ⊕ 𝒪_X` in degree `a` where the complex has `𝒪_X`. -/
theorem not_nonempty_iso_biprod_truncLE_truncGE_singleFunctor_unit (X : Scheme.{u})
    [Nonempty X] (M : X.Modules) (hM : Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf))
    (a : ℤ) :
    ¬ Nonempty ((DerivedCategory.singleFunctor X.Modules a).obj M ≅
      (DerivedCategory.TStructure.t.truncLE a).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj M) ⊞
      (DerivedCategory.TStructure.t.truncGE a).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj M)) := by
  rintro ⟨e⟩
  have hLE : IsIso ((DerivedCategory.homologyFunctor X.Modules a).map
      ((DerivedCategory.TStructure.t.truncLEι a).app
        ((DerivedCategory.singleFunctor X.Modules a).obj M))) := by
    change IsIso ((DerivedCategory.homologyFunctor X.Modules a).map
      ((DerivedCategory.TStructure.t.truncLTι (a + 1)).app _))
    exact DerivedCategory.isIso_homologyMap_truncLTι_app (a + 1) a (by omega) _
  have hGE : IsIso ((DerivedCategory.homologyFunctor X.Modules a).map
      ((DerivedCategory.TStructure.t.truncGEπ a).app
        ((DerivedCategory.singleFunctor X.Modules a).obj M))) :=
    DerivedCategory.isIso_homologyMap_truncGEπ_app a a le_rfl _
  have : PreservesBinaryBiproducts (DerivedCategory.homologyFunctor X.Modules a) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let u : (DerivedCategory.homologyFunctor X.Modules a).obj
      ((DerivedCategory.singleFunctor X.Modules a).obj M) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules a).app _ ≪≫ hM.some
  exact not_nonempty_iso_biprod_self_of_iso_unit X _ ⟨u⟩
    ⟨(DerivedCategory.homologyFunctor X.Modules a).mapIso e ≪≫
      (DerivedCategory.homologyFunctor X.Modules a).mapBiprod _ _ ≪≫
      biprod.mapIso (@asIso _ _ _ _ _ hLE) (@asIso _ _ _ _ _ hGE).symm⟩

/-- **[Stacks, Tag 0FZ4] is false as stated when `d = 0`.** The spectrum of a field is a
regular Noetherian scheme of dimension `0`, the structure sheaf placed in any degree `a` is a
bounded complex with coherent cohomology, and the gap condition `a < i < a + 0` is empty; yet
the complex is not `τ^{≤ a} K ⊕ τ^{≥ a + 0} K`
(`not_nonempty_iso_biprod_truncLE_truncGE_singleFunctor_unit`). The source's proof uses
`τ^{≤ a} K = τ^{≤ a + d - 1} K`, which is where `d ≥ 1` is needed. -/
theorem not_forall_nonempty_iso_biprod_truncLE_truncGE_of_dim_zero :
    ¬ ∀ (X : Scheme.{u}) [IsNoetherian X], IsRegular X →
      topologicalKrullDim X = ((0 : ℕ) : WithBot ℕ∞) →
      ∀ K : DerivedCategory X.Modules, DerivedCategory.TStructure.t.bounded K →
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent) →
      ∀ a : ℤ, (∀ i : ℤ, a < i → i < a + ((0 : ℕ) : ℤ) →
        IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) →
      Nonempty (K ≅ (DerivedCategory.TStructure.t.truncLE a).obj K ⊞
        (DerivedCategory.TStructure.t.truncGE (a + ((0 : ℕ) : ℤ))).obj K) := by
  intro h
  let k : Type u := ULift.{u} (ZMod 2)
  let X : Scheme.{u} := Spec (CommRingCat.of k)
  have hX : IsRegular X := (isRegular_spec_iff k).2 inferInstance
  have hd : topologicalKrullDim X = ((0 : ℕ) : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum k) = _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    rfl
  have : Nonempty X := inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨M, ⟨u⟩⟩ : ∃ M : X.Modules, Nonempty (M ≅ SheafOfModules.unit X.ringCatSheaf) :=
    ⟨_, ⟨Iso.refl _⟩⟩
  have hbdd : DerivedCategory.TStructure.t.bounded
      ((DerivedCategory.singleFunctor X.Modules 0).obj M) :=
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩
  have hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)).IsCoherent := by
    intro i
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
        (DerivedCategory.isZero_of_isGE ((DerivedCategory.singleFunctor X.Modules 0).obj M)
          0 i hi)
    · exact AlgebraicGeometry.isCoherent_of_moduleIso
        (u.symm ≪≫ ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app _).symm)
        (Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit X)
    · exact Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_isZero
        (DerivedCategory.isZero_of_isLE ((DerivedCategory.singleFunctor X.Modules 0).obj M)
          0 i hi)
  obtain ⟨e⟩ := h X hX hd _ hbdd hcoh 0 (fun i h₁ h₂ => by omega)
  exact not_nonempty_iso_biprod_truncLE_truncGE_singleFunctor_unit X M ⟨u⟩ 0 ⟨e⟩

/-- Let `X` be a regular Noetherian scheme of dimension `d < ∞`, let `K ∈ D^b_{Coh}(𝒪_X)` and
`a ∈ ℤ` with `H^i(K) = 0` for `a < i < a + d`. Then `K ≅ τ^{≤ a + d - 1} K ⊕ τ^{≥ a + d} K`, and
when `d ≥ 1` (where `τ^{≤ a + d - 1} K = τ^{≤ a} K`) `K ≅ τ^{≤ a} K ⊕ τ^{≥ a + d} K`, the
source's form. At `d = 0` the source's form is false
(`not_forall_nonempty_iso_biprod_truncLE_truncGE_of_dim_zero`), so the first conjunct is the
statement for every `d` and the second is the source's conclusion wherever it holds. The
connecting morphism of the truncation triangle vanishes by [Stacks, Tag 0FZ3] part (2). -/
@[stacks 0FZ4 "corrected statement, under exactly the source's hypotheses: the source's form
  `K = τ^{≤ a} K ⊕ τ^{≥ a + d} K` is false at `d = 0`
  (`not_forall_nonempty_iso_biprod_truncLE_truncGE_of_dim_zero`), so it is concluded for
  `0 < d`, together with the form `K = τ^{≤ a + d - 1} K ⊕ τ^{≥ a + d} K`, which holds for every
  `d` and agrees with the source's for `0 < d`"]
theorem exists_iso_biprod_truncations_of_isRegular (X : Scheme.{u}) [IsNoetherian X]
    (hX : IsRegular X) (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞))
    (K : DerivedCategory X.Modules)
    (hKbdd : DerivedCategory.TStructure.t.bounded K)
    (hKcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsCoherent)
    (a : ℤ)
    (hgap : ∀ i : ℤ, a < i → i < a + (d : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj K)) :
    Nonempty (K ≅ (DerivedCategory.TStructure.t.truncLE (a + (d : ℤ) - 1)).obj K ⊞
        (DerivedCategory.TStructure.t.truncGE (a + (d : ℤ))).obj K) ∧
      (0 < d → Nonempty (K ≅ (DerivedCategory.TStructure.t.truncLE a).obj K ⊞
        (DerivedCategory.TStructure.t.truncGE (a + (d : ℤ))).obj K)) :=
  ⟨exists_iso_biprod_truncLE_truncGE X hX d hd (separatedCohomologyHomVanishing X d) K hKbdd
      hKcoh a hgap,
    fun hd0 => exists_iso_biprod_truncations X hX d hd hd0 K hKbdd hKcoh a hgap⟩

end AlgebraicGeometry
