module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Higher direct images along an affine morphism of algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝓕` be a quasi-coherent `𝒪_X`-module. Then `R^n f_* 𝓕 = 0` for `n > 0`;
equivalently, `𝓕` is right acyclic for `f_*`.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_smallBaseChangeModulePushforward_of_isAffineHom`:
  the vanishing for the direct image `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`
  along small-chart base change of a representable affine morphism.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_isAffineHom`: the vanishing for
  the direct image `AlgebraicGeometry.Space.modulePushforward`.
* `AlgebraicGeometry.Space.rightAcyclic_modulePushforward_of_isQuasicoherentOnSite`: the same
  statement read as right acyclicity, that is, `f_*𝓕 ⟶ Rf_*𝓕` is an isomorphism.

## Implementation notes

For a representable `f`, `AlgebraicGeometry.Space.modulePushforwardChartIso` identifies
`AlgebraicGeometry.Space.modulePushforward` with the site pushforward
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`. The higher direct images of the
latter vanish by the covering criterion
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve` applied
to the covering families of affine charts, whose base changes along `f` are affine charts, where
the cohomology of a quasi-coherent module vanishes in positive degrees.

The structure sheaf of an algebraic space has two spellings, the reduced
`AlgebraicGeometry.Space.smallEtaleRingSheaf` and the projection
`AlgebraicGeometry.RingedSite.ringSheaf` of `AlgebraicGeometry.Space.smallEtaleRingedSite`,
which instance search does not identify; enough injectives and additivity are registered at both.

## References

* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03WF](https://stacks.math.columbia.edu/tag/03WF)
* [Stacks Project, Tag 04CF](https://stacks.math.columbia.edu/tag/04CF)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

open Stacks.Cohomology.ModuleDirectImageOnACover

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

/-- Naturally isomorphic additive functors have isomorphic right derived functors. -/
private def rightDerivedIsoOfNatIso {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] [HasInjectiveResolutions C] {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### The homological instances on the modules of an algebraic space -/

/-- The `𝒪_F`-modules at the universe of the structure rings have enough injectives. -/
local instance enoughInjectives_modules_instance (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : EnoughInjectives (Modules.{u, u} B S hS F hF) :=
  enoughInjectives_modules B S hS F hF

/-- The sheaves of modules over `AlgebraicGeometry.Space.smallEtaleRingSheaf` have enough
injectives. -/
local instance enoughInjectives_sheafOfModules_smallEtaleRingSheaf
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    EnoughInjectives (SheafOfModules.{u} (smallEtaleRingSheaf B S hS F hF)) :=
  enoughInjectives_modules B S hS F hF

/-! ### The vanishing for the concrete direct image -/

/-- The direct image of modules along small-chart base change is additive. -/
local instance additive_smallBaseChangeModulePushforward (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    (smallBaseChangeModulePushforward.{u, u} B S hS f hf).Additive :=
  inferInstanceAs (SheafOfModules.pushforward (smallBaseChangeSharp B S hS f hf)).Additive

/-- The direct image of modules along small-chart base change is additive, with the source and
target categories spelled as `AlgebraicGeometry.Space.Modules`. -/
local instance additive_smallBaseChangeModulePushforward_modules (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) :
    @Functor.Additive (Modules.{u, u} B S hS X.1 X.2) (Modules.{u, u} B S hS Y.1 Y.2) _ _
      Abelian.toPreadditive Abelian.toPreadditive
      (smallBaseChangeModulePushforward.{u, u} B S hS f hf) :=
  additive_smallBaseChangeModulePushforward B S hS f hf

/-- Let `f : X ⟶ Y` be a representable affine morphism of algebraic spaces over `S` and let `𝓕`
be a quasi-coherent `𝒪_X`-module. Then `R^p f_* 𝓕 = 0` for `p > 0`, for the direct image along
small-chart base change and the structure map `AlgebraicGeometry.Space.smallBaseChangeSharp`. -/
theorem isZero_rightDerived_smallBaseChangeModulePushforward_of_isAffineHom (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (haff : IsAffineHom B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (p : ℕ) (hp : 0 < p) :
    IsZero (((smallBaseChangeModulePushforward.{u, u} B S hS f hf).rightDerived p).obj F) := by
  refine isZero_rightDerived_pushforward_of_presieve.{u, u + 1, u, u + 1, u, u}
    (smallBaseChange B S hS f hf) (smallEtaleRingSheaf B S hS X.1 X.2)
    (smallEtaleRingSheaf B S hS Y.1 Y.2) (smallBaseChangeSharp B S hS f hf) p F (fun V ↦ ?_)
  obtain ⟨I, Ui, g, hcov, haffchart⟩ := hasEnoughObjects_isAffineChart B S hS Y.1 V
  exact ⟨Presieve.ofArrows Ui g, hcov, fun _ _ ⟨i⟩ ↦
    isZero_rightDerived_evaluation_of_isAffineChart B S hS X.1 X.2 F hF
      ((smallBaseChange B S hS f hf).obj (Ui i))
      (isAffine_smallBaseChange_obj B S hS f hf haff (Ui i) (haffchart i)) p hp⟩

/-! ### Stacks 073H -/

/-- Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, and let `𝓕` be a quasi-coherent `𝒪_X`-module. Then the higher direct images
`R^p f_* 𝓕` vanish for `p > 0`, the direct image being
`AlgebraicGeometry.Space.modulePushforward`. -/
@[stacks 073H]
theorem isZero_rightDerived_modulePushforward_isAffineHom (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (p : ℕ) (hp : 0 < p) :
    IsZero (((modulePushforward B S hS f).rightDerived p).obj F) := by
  have hrep := relativelyRepresentable_of_isAffineHom B S hS f haff
  exact (isZero_rightDerived_smallBaseChangeModulePushforward_of_isAffineHom B S hS f hrep haff
    F hF p hp).of_iso ((rightDerivedIsoOfNatIso (modulePushforwardChartIso B S hS f hrep) p).app F)

/-- A quasi-coherent module is right acyclic for the direct image along an affine morphism of
algebraic spaces, that is, the canonical map `f_*𝓕 ⟶ Rf_*𝓕` is an isomorphism. -/
theorem rightAcyclic_modulePushforward_of_isQuasicoherentOnSite (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) : (modulePushforward B S hS f).rightAcyclic F :=
  (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat (modulePushforward B S hS f) F).2
    (isZero_rightDerived_modulePushforward_isAffineHom B S hS f haff F hF)

end AlgebraicGeometry.Space

end
