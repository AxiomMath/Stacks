module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackExistence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedDirectImageAndRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived pullback along a cocontinuous morphism of ringed sites

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by the functor `u : D ⥤ C`,
and suppose that `u` is also *cocontinuous*. Then the direct image of sheaves of modules
`f_* : Mod(O_C) ⥤ Mod(O_D)` — restriction of sections along `u` followed by restriction of
scalars along `f^♯` — is exact, so the derived direct image `Rf_*` is the functor that `f_*`
induces on derived categories, and the derived adjunction `Lf^* ⊣ Rf_*` of Tag 07A6 becomes an
adjunction `Lf^* ⊣ f_*` with `f_*` read on derived categories.

If moreover `u` is fully faithful and `f^♯ : O_D ⟶ u_* O_C` is invertible — the situation of a
full subsite `D ⊆ C` whose structure sheaf is the restriction of that of `C` — the unit
`K ⟶ f_* Lf^* K` of that adjunction is an isomorphism: `Lf^*` is fully faithful. The source of
this is the underived statement `M ≅ f_* f^* M` (Stacks 00XT on sheaves of modules,
`SheafOfModules.isIso_unit_of_isIso_coefficient`), and the passage to derived categories goes
through K-flat complexes with flat terms, on which `Lf^*` is computed by `f^*` (Tag 06YY).

## Main results

* `Stacks.Cohomology.FullyFaithfulSubsite.preservesFiniteColimits_pushforwardTopos` and
  `preservesFiniteLimits_pushforwardTopos`: the direct image along a cocontinuous morphism of
  ringed sites is exact.
* `Stacks.Cohomology.FullyFaithfulSubsite.derivedPushforwardIso`:
  `Rf_* ≅ f_*` on derived categories.
* `Stacks.Cohomology.FullyFaithfulSubsite.derivedPullbackAdjunction`: `Lf^* ⊣ f_*`.
* `Stacks.Cohomology.FullyFaithfulSubsite.isIso_unit_pullbackPushforwardAdjunctionTopos`: for
  `u` fully faithful and `f^♯` invertible, the unit `M ⟶ f_* f^* M` is an isomorphism.
* `Stacks.Cohomology.FullyFaithfulSubsite.isIso_derivedPullbackAdjunction_unit`: under the same
  hypotheses, the unit `K ⟶ f_* Lf^* K` is an isomorphism.

## Implementation notes

All derived categories here are the standard models, as in the development of Tag 06YY and
Tag 07A6 that this file builds on. `Lf^*` is stated in the binder context of
`Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPullback`, whose
`HasLeftDerivedFunctor` instance argument is a `Prop` class discharged for every morphism of
ringed sites by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`.

## References

* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 00XT](https://stacks.math.columbia.edu/tag/00XT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

namespace Stacks.Cohomology.FullyFaithfulSubsite

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- The inverse image of sheaves of modules along a morphism of ringed sites is additive, being
a left adjoint; instantiated at the universes of a morphism of ringed sites. -/
local instance additive_pullbackTopos {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    f.toRingedToposSiteHom.pullbackTopos.Additive :=
  Adjunction.left_adjoint_additive
    (RingedToposSiteHom.pullbackPushforwardAdjunctionTopos f.toRingedToposSiteHom)

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Exactness of the direct image -/

/-- The direct image of sheaves of modules along a morphism of ringed sites preserves finite
limits, being a right adjoint. -/
@[sga "4 IV 13.6" "special case"]
instance preservesFiniteLimits_pushforwardTopos :
    PreservesFiniteLimits f.toRingedToposSiteHom.pushforwardTopos :=
  letI := f.toRingedToposSiteHom.isContinuous
  SheafOfModules.preservesFiniteLimits_pushforward _

/-- The direct image of sheaves of modules along a morphism of ringed sites whose functor is
cocontinuous preserves finite colimits: restriction of sections along a continuous and
cocontinuous functor commutes with sheafification. -/
instance preservesFiniteColimits_pushforwardTopos [f.u.IsCocontinuous Y.J X.J] :
    PreservesFiniteColimits f.toRingedToposSiteHom.pushforwardTopos :=
  letI := f.toRingedToposSiteHom.isContinuous
  letI : f.toRingedToposSiteHom.u.IsCocontinuous Y.ringedTopos.J X.ringedTopos.J := ‹_›
  (SheafOfModules.exactFunctor_pushforward_of_isCocontinuous f.toRingedToposSiteHom.u
    f.toRingedToposSiteHom.fSharpRing).2

/-! ### The derived direct image -/

section Derived

variable [f.u.IsCocontinuous Y.J X.J]

/-- **The derived direct image along a cocontinuous morphism of ringed sites is the direct image
read on derived categories.** The direct image is exact, so the functor it induces on derived
categories is a right derived functor of degreewise direct image, and right derived functors are
unique. -/
def derivedPushforwardIso :
    derivedPushforward.{u} f.toRingedToposSiteHom ≅
      f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory :=
  letI : f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.IsRightDerivedFunctor
      f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts _ _
      f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategoryFactorsh
  Functor.rightDerivedUnique _ _ (derivedPushforwardUnit.{u} f.toRingedToposSiteHom)
    f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (ComplexShape.up ℤ))

/-- The comparison `f_* ⟶ Rf_*` from degreewise direct image is invertible at every complex, the
direct image being exact. -/
instance isIso_derivedPushforwardUnit :
    IsIso (derivedPushforwardUnit.{u} f.toRingedToposSiteHom) :=
  Stacks.Cohomology.Localization.isIso_of_isRightDerivedFunctor_of_exact
    f.toRingedToposSiteHom.pushforwardTopos _ _

variable [(pullbackOnHomotopy f.toRingedToposSiteHom).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

/-- **`Lf^* ⊣ f_*` on derived categories**, for a morphism of ringed sites whose functor is
cocontinuous: the derived adjunction of Tag 07A6 composed with `derivedPushforwardIso`. -/
def derivedPullbackAdjunction :
    derivedPullback.{u} f.toRingedToposSiteHom ⊣
      f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory :=
  (derivedAdjunction f.toRingedToposSiteHom f.isMorphismOfSites_toRingedToposSiteHom).ofNatIsoRight
    (derivedPushforwardIso f)

/-! ### The unit, for a fully faithful functor and an invertible structure map -/

section FullyFaithful

variable [f.u.Full] [f.u.Faithful] [IsIso f.fsharp]

/-- The structure map read on sheaves of not necessarily commutative rings is invertible as
soon as the structure map itself is: it is its image under forgetting commutativity. -/
instance isIso_fSharpRing : IsIso f.toRingedToposSiteHom.fSharpRing :=
  inferInstanceAs (IsIso ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).map f.fsharp))

/-- **`M ≅ f_* f^* M`.** For a morphism of ringed sites whose functor is continuous,
cocontinuous and fully faithful, and whose structure map is invertible, the unit of the
pullback--pushforward adjunction of sheaves of modules is an isomorphism (Stacks 00XT on
sheaves of modules). -/
instance isIso_unit_pullbackPushforwardAdjunctionTopos :
    IsIso f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit :=
  letI := f.toRingedToposSiteHom.isContinuous
  letI : f.toRingedToposSiteHom.u.IsCocontinuous Y.ringedTopos.J X.ringedTopos.J := ‹_›
  letI : f.toRingedToposSiteHom.u.Full := ‹f.u.Full›
  letI : f.toRingedToposSiteHom.u.Faithful := ‹f.u.Faithful›
  haveI : IsIso f.toRingedToposSiteHom.fSharpRing := isIso_fSharpRing f
  SheafOfModules.isIso_unit_of_isIso_coefficient.{u, u, u, u, u, u} f.toRingedToposSiteHom.u
    Y.ringedTopos.J X.ringedTopos.J (Stacks.SheafOfModules.Tensor.ringSheaf X.ringedTopos.O)
    f.toRingedToposSiteHom.fSharpRing
    f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos

/-- The unit of the derived adjunction `Lf^* ⊣ Rf_*` of Tag 07A6 is invertible at a K-flat
complex with flat terms: there `Lf^*` is computed by `f^*` (Tag 06YY), `Rf_*` by `f_*`, and the
underived unit is invertible. -/
theorem isIso_derivedAdjunction_unit_app_of_isKFlat
    (M : HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (hM : IsKFlat (Y := Y.ringedTopos) M) :
    IsIso ((derivedAdjunction f.toRingedToposSiteHom
      f.isMorphismOfSites_toRingedToposSiteHom).unit.app (DerivedCategory.Qh.obj M)) := by
  have hfac := derivedPullbackPushforwardAdjunctionOfKFlat_unit_fac f.toRingedToposSiteHom
    f.isMorphismOfSites_toRingedToposSiteHom
    (fun h ↦ pullbackInvertsQuasiIso_isKFlat f.toRingedToposSiteHom h) M
  have hcomp : IsIso ((derivedPullbackComparison f.toRingedToposSiteHom).app M) := by
    obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
    exact isIso_derivedPullbackComparison_app_kFlat f.toRingedToposSiteHom
      f.isMorphismOfSites_toRingedToposSiteHom N hM.1 hM.2
  have hunit :
      IsIso ((homotopyPullbackPushforwardAdjunction f.toRingedToposSiteHom).unit.app M) := by
    obtain ⟨N, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
    have : ∀ n : ℤ, IsIso (((Adjunction.mapHomologicalComplexAdjunction
        f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
        (ComplexShape.up ℤ)).unit.app N).f n) := fun n ↦
      inferInstanceAs (IsIso
        (f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app (N.X n)))
    have : IsIso ((Adjunction.mapHomologicalComplexAdjunction
        f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
        (ComplexShape.up ℤ)).unit.app N) := HomologicalComplex.Hom.isIso_of_components _
    exact inferInstanceAs (IsIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((Adjunction.mapHomologicalComplexAdjunction
        f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
        (ComplexShape.up ℤ)).unit.app N)))
  have : IsIso ((derivedAdjunction f.toRingedToposSiteHom
      f.isMorphismOfSites_toRingedToposSiteHom).unit.app (DerivedCategory.Qh.obj M) ≫
      (derivedPushforward f.toRingedToposSiteHom).map
        ((derivedPullbackComparison f.toRingedToposSiteHom).app M)) := by
    rw [show derivedAdjunction f.toRingedToposSiteHom f.isMorphismOfSites_toRingedToposSiteHom =
      derivedPullbackPushforwardAdjunctionOfKFlat f.toRingedToposSiteHom
        f.isMorphismOfSites_toRingedToposSiteHom
        (fun h ↦ pullbackInvertsQuasiIso_isKFlat f.toRingedToposSiteHom h) from rfl, hfac]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((derivedPushforward f.toRingedToposSiteHom).map
      ((derivedPullbackComparison f.toRingedToposSiteHom).app M))

/-- **The unit of the derived adjunction `Lf^* ⊣ Rf_*` is an isomorphism**, for a morphism of
ringed sites whose functor is continuous, cocontinuous and fully faithful and whose structure
map is invertible. Every object of `D(O_D)` is isomorphic to a K-flat complex with flat terms
(Tag 06YS), and there `isIso_derivedAdjunction_unit_app_of_isKFlat` applies. -/
instance isIso_derivedAdjunction_unit :
    IsIso (derivedAdjunction f.toRingedToposSiteHom
      f.isMorphismOfSites_toRingedToposSiteHom).unit := by
  refine (NatTrans.isIso_iff_isIso_app _).2 fun K ↦ ?_
  obtain ⟨M, hM, s, hs⟩ := hasResolutions_isKFlat (Y := Y.ringedTopos)
    (DerivedCategory.Qh.objPreimage K)
  have : IsIso (DerivedCategory.Qh.map s) := by
    rw [DerivedCategory.isIso_Qh_map_iff]
    exact hs
  have := isIso_derivedAdjunction_unit_app_of_isKFlat f M hM
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Qh.objObjPreimageIso K),
    ← NatTrans.isIso_app_iff_of_iso _ (asIso (DerivedCategory.Qh.map s))]
  exact this

/-- **The unit `K ⟶ f_* Lf^* K` is an isomorphism**, for a morphism of ringed sites whose
functor is continuous, cocontinuous and fully faithful and whose structure map is invertible:
`Lf^*` is fully faithful. -/
instance isIso_derivedPullbackAdjunction_unit :
    IsIso (derivedPullbackAdjunction f).unit := by
  rw [derivedPullbackAdjunction, Adjunction.ofNatIsoRight_unit]
  infer_instance

end FullyFaithful

end Derived

end Stacks.Cohomology.FullyFaithfulSubsite

end
