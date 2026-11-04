module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsPseudoCoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsClauseThree
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualBoundedAboveOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualLocalTorAmplitude
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessCriterionGeneral

/-!
# An invertible object of the derived category of a ringed site is perfect

Let `(C, O)` be a ringed site and let `M` be an invertible object of `D(O)`. Then `M` is
perfect. This is the step of the source's proof of Stacks 0FPY which reads "then `N` is a left
dual for `M` in the monoidal category `D(O)` and we conclude that `M` is perfect by Lemma 0FPV",
proved here for an invertible `M` along the lines of the proof of Stacks 0FPV:

* locally on `C`, `M` is concentrated in degrees `≤ b` for some `b`
  (`AlgebraicGeometry.RingedSite.exists_presieve_isLE`);
* on such a slice `C/W`, the restriction `M|_W` is again invertible
  (`AlgebraicGeometry.RingedSite.InvertibleDerived.restrictTensorIsoUnit`), hence pseudo-coherent
  (`AlgebraicGeometry.RingedSite.InvertibleDerived.isPseudoCoherentFrom_of_isLE`, the descending
  induction of the source) and locally of finite Tor dimension
  (`AlgebraicGeometry.RingedSite.locallyHasFiniteTorDimension_of_exactPairing_of_isLE`), so it is
  perfect on `C/W` by Stacks 08G8
  (`isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension_general` in the namespace
  `Stacks.SheafOfModules.DerivedTensorProduct`);
* perfectness descends along the covering
  (`AlgebraicGeometry.RingedSite.isPerfect_of_locally_general`).

Everything is stated with the derived categories of the modules on `C` and on its slices given by
`HasDerivedCategory.standard`; the transport to an arbitrary model of `D(O)` is
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjectsTFAE`.

Nothing below is a clause of a tag, so no `@[stacks …]` attribute is attached.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.isPerfect_of_isInvertibleObject_standard`.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable {X : RingedSite.{u, u, u}} [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- An object of `D(O)` which is `n`-pseudo-coherent for every `n` is pseudo-coherent: a single
complex representing it is `n`-pseudo-coherent for every `n` at once
(`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_iso_general`). -/
theorem isPseudoCoherent_of_forall_isPseudoCoherentFrom (Y : RingedSite.{u, u, u})
    [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{u}]
    [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (E : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Y.O)
    (h : ∀ n, Y.IsPseudoCoherentFrom E n) : Y.IsPseudoCoherent E := by
  obtain ⟨P, _, ⟨e⟩⟩ := h 0
  exact ⟨P, fun n => RingedSite.isPseudoCoherentComplexFrom_of_iso_general Y E n (h n) P e, ⟨e⟩⟩

/-! ### The tensor data of a diagonal ringed site

The derived tensor product of Stacks 06YU and the perfectness criterion of Stacks 08G8 read the
additivity of `⊗_O` in each variable and the existence of total tensor complexes as instance
arguments, on a ringed site, its slices and its iterated slices. All three hold on every ringed
site `RingedSite.{u, u, u}`; they are recorded here once, for an arbitrary such site, so that
instance search finds them on the slices without unfolding the slice construction. -/

/-- The tensor product of `O`-modules is additive in the first variable. -/
local instance invPerfSheafTensorAdditive (Y : RingedSite.{u, u, u}) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_additive _

/-- The tensor product of `O`-modules is additive in the second variable. -/
local instance invPerfSheafTensorObjAdditive (Y : RingedSite.{u, u, u})
    (A : RingedSite.Modules.{u, u, u} Y) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj A).Additive :=
  Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive _ A

/-- Total tensor complexes of complexes of `O`-modules exist. -/
local instance invPerfHasMapBifunctor (Y : RingedSite.{u, u, u})
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} Y) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor _ K L

/-- **An invertible object of `D(O)` concentrated in degrees `≤ b` is perfect**, the derived
categories being the standard ones. It is pseudo-coherent
(`AlgebraicGeometry.RingedSite.InvertibleDerived.isPseudoCoherentFrom_of_isLE`) and locally of
finite Tor dimension
(`AlgebraicGeometry.RingedSite.locallyHasFiniteTorDimension_of_exactPairing_of_isLE`), so
Stacks 08G8 applies. -/
theorem isPerfect_of_tensorIsoUnit_of_isLE (Y : RingedSite.{u, u, u})
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules Y.O)
    (e₁ : letI := derivedMonoidal Y.O; M ⊗ N ≅ 𝟙_ _)
    (e₂ : letI := derivedMonoidal Y.O; N ⊗ M ≅ 𝟙_ _) (b : ℤ) (hb : M.IsLE b) :
    Y.IsPerfect M := by
  let := derivedMonoidal Y.O
  obtain ⟨N₂, ⟨p₂⟩⟩ := exists_exactPairing_of_isInvertibleObject Y M ⟨⟨N, e₁, e₂⟩⟩
  have hpc : Y.IsPseudoCoherent M :=
    isPseudoCoherent_of_forall_isPseudoCoherentFrom Y M (isPseudoCoherentFrom_of_isLE M N e₁ b hb)
  let T : ∀ V : Y.C, Stacks.SheafOfModules.DerivedTensorProduct (Y.over V) :=
    fun V => Stacks.SheafOfModules.canonicalDerivedTensorProduct (Y.over V)
  exact open Stacks.SheafOfModules in
    DerivedTensorProduct.isPerfect_of_isPseudoCoherent_of_locallyHasFiniteTorDimension_general
      T M hpc (RingedSite.locallyHasFiniteTorDimension_of_exactPairing_of_isLE Y M N₂ p₂ b hb T)

/-- **An invertible object of `D(O)` is perfect**, the derived categories being the standard
ones. Locally `M` is concentrated in degrees `≤ b` for some `b`
(`AlgebraicGeometry.RingedSite.exists_presieve_isLE`); on such a slice its restriction is again
invertible (`AlgebraicGeometry.RingedSite.InvertibleDerived.restrictTensorIsoUnit`), hence
perfect by `isPerfect_of_tensorIsoUnit_of_isLE`; and perfectness is local
(`AlgebraicGeometry.RingedSite.isPerfect_of_locally_general`). -/
theorem isPerfect_of_isInvertibleObject_standard
    (M : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (hM : IsInvertibleObject X M) : X.IsPerfect M := by
  let := derivedMonoidal X.O
  obtain ⟨H⟩ := hM
  obtain ⟨N₁, ⟨p₁⟩⟩ := exists_exactPairing_of_isInvertibleObject X M ⟨H⟩
  refine RingedSite.isPerfect_of_locally_general X M fun U => ?_
  obtain ⟨S, hS, hdata⟩ := RingedSite.exists_presieve_isLE X U M N₁ p₁
  refine ⟨S, hS, fun {W} f hf => ?_⟩
  obtain ⟨b, hb⟩ := hdata f hf
  exact isPerfect_of_tensorIsoUnit_of_isLE (X.over W) ((ovF X W).mapDerivedCategory.obj M)
    ((ovF X W).mapDerivedCategory.obj H.inv) (restrictTensorIsoUnit W M H.inv H.isoLeft)
    (restrictTensorIsoUnit W H.inv M H.isoRight) b hb

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
