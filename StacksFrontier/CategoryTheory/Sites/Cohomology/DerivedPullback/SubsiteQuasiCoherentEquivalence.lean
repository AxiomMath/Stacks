module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GeneratedByGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.FullyFaithfulSubsiteSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonBaseChangeAcyclic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonCartesianCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonGluing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.ChaoticComparisonLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentInverseImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentRestrictScalars
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.TildePullback
public import StacksFrontier.CategoryTheory.Triangulated.AdjunctionRestrictedEquivalence
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Restriction to a full subsite on the subcategories of Stacks 0GZS

Let `f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites given by a functor `u : D ⥤ C` which
is fully faithful and cocontinuous, with invertible structure map `f^♯ : O_D ≅ u⁻¹O_C`: the
situation of a full subsite `D ⊆ C` carrying the restricted structure sheaf. For a ringed site
write `QC` for the full subcategory of its derived category of modules consisting of the objects
`K` whose derived pushforward `Rε_*K` to the chaotic site is cartesian, the subcategory appearing
in Stacks 0GZS (`IsCartesianPushforwardOn`). This file proves that, under two hypotheses on `C`,
the derived pullback `Lf^*` and the direct image `f_*` restrict to mutually inverse equivalences
`QC(D) ≌ QC(C)` (`equivalence`).

The hypotheses are:

* `hunit`: for every object `x` of `C`, the unit of `ε^* ⊣ Rε_*` on the slice `C/x` is invertible
  at the derived base changes `Lp^*P` from the terminal object `id_x`. This is the conclusion of
  `isIso_derivedEpsilonAdjunction_unit_app_Lpullback_of_baseChange` in the namespace
  `Stacks.ModulesOnACategory.ChaoticComparison`.
* `hcov`: every object `x` of `C` has a `DescentCover`: a family `x_i ⟶ x` generating a covering
  sieve, each `x_i` mapping to an object in the image of `u`, along which the cartesian condition
  descends.

## The argument

The adjunction `Lf^* ⊣ f_*` of
`Stacks.Cohomology.FullyFaithfulSubsite.smallDerivedPullbackAdjunction` has invertible unit, so by
the argument of Stacks 09J1 (`Stacks.Triangulated.restrictedEquivalence`) it suffices to show three
things.

* `f_*` maps `QC(C)` into `QC(D)` (`isCartesianPushforwardOn_pushforward`): `Rε_*(f_*L)` is the
  inverse image of `Rε_*L` along `u` with scalars restricted along `f^♯`, and both operations
  preserve cartesian objects.
* `f_*` has zero kernel on `QC(C)` (`isZero_of_isCartesianPushforwardOn_of_isZero_pushforward`):
  if `f_*L = 0` then `RΓ(u y, L) = 0` for all `y`, hence `RΓ(z, L) = 0` for every `z` mapping to
  some `u y`, and these `z` cover `C`.
* `Lf^*` maps `QC(D)` into `QC(C)` (`isCartesianPushforwardOn_smallDerivedPullback`). Over the
  slice `C/u y`, the restriction of `Lf^*K` is the derived pullback along the localized morphism of
  the restriction `K|_y` (Stacks 04J0), and `K|_y` is the sheafified base change of `RΓ(y, K)` from
  the terminal object of `D/y` (Stacks 0H0R); its derived pullback is again a sheafified base
  change (`Stacks.ModulesOnACategory.TildePullback.derivedPullbackTildeIsoOfIsIso`), which lies in
  the 0GZS subcategory of the slice by `hunit`. So the comparison maps of `Rε_*(Lf^*K)` are
  invertible along all arrows over the image of `u`; descent along the covers gives them along the
  arrows of the covers, and the 0GZS condition glues from a covering family on each slice
  (`isCartesianPushforward_of_comparison_of_exists_mem_sieve`).

## Implementation notes

The derived pullback of Tag 06YY, the derived localization square and the tilde computation are
stated in the standard models of the derived categories of sheaves of modules, while `Rε_*` and the
0GZS subcategory are stated in the locally small models of Tag 079Q. The two models have the same
objects; isomorphisms are transported with `mapDerivedCategoryTargetModelIso`, which compares the
derived functor of an exact functor into the two models of its target, together with
`Stacks.Injectives.mapDerivedCategoryModelIso` for the source.

## References

* [Stacks Project, Tag 0GZS](https://stacks.math.columbia.edu/tag/0GZS)
* [Stacks Project, Tag 0H0R](https://stacks.math.columbia.edu/tag/0H0R)
* [Stacks Project, Tag 04J0](https://stacks.math.columbia.edu/tag/04J0)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence
open Stacks.ModulesOnACategory.ChaoticComparison
open Stacks.ModulesOnACategory.MorphismsOverAnObject
open Stacks.Sites.OverModules (overRingPresheaf)
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange (baseChangeDataOfComm)
open Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent (dInverseImage)
open Stacks.ModulesOnACategory.TerminalMorphismOfSites (morphismOfSites)
open Stacks.Cohomology.FullyFaithfulSubsite
open ZeroObject

namespace Stacks.Cohomology.SubsiteQuasiCoherentEquivalence

universe t u w₁ w₂ u₁ v₁ u₂ v₂

/-! ### Changing the model of the target of an exact functor -/

section ModelChange

open Stacks.Injectives (grothendieckModelEquiv hasDerivedCategory_of_isGrothendieckAbelian)

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] (hA : HasDerivedCategory.{w₁} A)
  (B : Type u₂) [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The derived functor of an exact functor does not depend on the model of the target
derived category.** For an exact functor `F : A ⥤ B` into a Grothendieck abelian category, the
functor `F` induces from a fixed model of `D(A)` into the locally small model of `D(B)` of
Tag 079Q is the one it induces into the standard model of `D(B)`, followed by the comparison
equivalence `Stacks.Injectives.grothendieckModelEquiv`. Both lift `F` on cochain complexes along
the localization functor of `D(A)`, the comparison carrying the one localization functor of
`D(B)` to the other on the nose. -/
def mapDerivedCategoryTargetModelIso :
    @Functor.mapDerivedCategory A _ _ hA B _ _
        (hasDerivedCategory_of_isGrothendieckAbelian.{w₂} B) F _ _ _ ≅
      @Functor.mapDerivedCategory A _ _ hA B _ _ (HasDerivedCategory.standard B) F _ _ _ ⋙
        (grothendieckModelEquiv.{w₂} B).functor :=
  letI : Localization.Lifting (@DerivedCategory.Q A _ _ hA)
      (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
      (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        @DerivedCategory.Q B _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w₂} B))
      (@Functor.mapDerivedCategory A _ _ hA B _ _ (HasDerivedCategory.standard B) F _ _ _ ⋙
        (grothendieckModelEquiv.{w₂} B).functor) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (@Functor.mapDerivedCategoryFactors A _ _ hA B _ _ (HasDerivedCategory.standard B)
          F _ _ _) _ ≪≫ Functor.associator _ _ _⟩
  Localization.liftNatIso (@DerivedCategory.Q A _ _ hA)
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      @DerivedCategory.Q B _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w₂} B))
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      @DerivedCategory.Q B _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w₂} B)) _ _
    (Iso.refl _)

end ModelChange

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive
attribute [local instance 1500] HasDerivedCategory.standard
attribute [local instance 2000]
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory
attribute [local instance 2000]
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

/-- **The subcategory of Stacks 0GZS of a ringed site.** The objects `K` of `D(O)` whose
derived pushforward `Rε_*K` to the chaotic site is cartesian, that is
`RΓ(V, K) ⊗^L_{O(V)} O(U) ⟶ RΓ(U, K)` is invertible for every `U ⟶ V`. This is
`Stacks.ModulesOnACategory.ChaoticComparison.IsCartesianPushforward` at the canonical base-change
datum of the commutative structure sheaf, with modules in the universe of the site. -/
abbrev IsCartesianPushforwardOn (Z : RingedSite.{u, u, u})
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ObjectProperty (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) :=
  IsCartesianPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
    (baseChangeDataOfComm.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj
      Stacks.TerminalBaseChange.CommSections.mul_comm)

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The derived functor of an exact functor kills an object exactly when the functor kills each
of its cohomology objects. -/
private theorem isZero_mapDerivedCategory_obj_iff_homology {A : Type u₁} [Category.{v₁} A]
    [Abelian A] [HasDerivedCategory.{w₁} A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
    [HasDerivedCategory.{w₂} B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (K : DerivedCategory A) :
    IsZero (F.mapDerivedCategory.obj K) ↔
      ∀ n : ℤ, IsZero (F.obj ((DerivedCategory.homologyFunctor A n).obj K)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  exact forall_congr' fun n ↦ ((F.mapDerivedCategoryHomologyIso n).app K).isZero_iff

/-- If the direct image `f_* L` along a cocontinuous morphism of ringed sites vanishes, then the
derived sections `RΓ(u y, L)` vanish for every object `y` of the target: by
`derivedEpsilonPushforwardInverseImageIso` they are, up to restriction of scalars along `f^♯`, the
derived sections `RΓ(y, f_* L)`, and vanishing is read off the cohomology modules. -/
theorem isZero_rGamma_of_isZero_pushforward [f.u.IsCocontinuous Y.J X.J]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsZero (f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.obj L)) (y : Y.C) :
    IsZero ((RGamma.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op (f.u.obj y))).obj
      ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L)) := by
  have := (derivedEpsilonAdjunction.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).right_adjoint_additive
  have h1 : IsZero ((fSharpRestrictScalars f).mapDerivedCategory.obj
      ((dInverseImage.{u, u, u, u, u} f.u (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).obj
        ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L))) :=
    ((derivedEpsilonPushforward.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_isZero hL).of_iso
      ((derivedEpsilonPushforwardInverseImageIso f).app L).symm
  have h2 : IsZero ((dInverseImage.{u, u, u, u, u} f.u
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj).obj
        ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L)) :=
    (DerivedCategory.isZero_iff_forall_isZero_homology _).2 fun n ↦ _root_.isZero_of_faithful
      (PresheafOfModules.restrictScalars.{u} f.toRingedToposSiteHom.fSharpPresheaf)
      ((isZero_mapDerivedCategory_obj_iff_homology _ _).1 h1 n)
  refine (isZero_mapDerivedCategory_obj_iff_homology
    (PresheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
      (op (f.u.obj y))) _).2 fun n ↦ ?_
  exact ((PresheafOfModules.evaluation.{u} _ (op y)).map_isZero
    ((isZero_mapDerivedCategory_obj_iff_homology
      (PresheafOfModules.pushforward₀.{u} f.u (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) _).1
      h2 n))

/-- **The direct image has zero kernel on the 0GZS subcategory.** Suppose every object of the
source has a covering sieve whose members all map to objects in the image of `u`. If `L` lies in
the 0GZS subcategory and `f_* L = 0`, then `L = 0`. Indeed `RΓ(u y, L) = 0` for every `y`, so by
the cartesian condition `RΓ(z, L) = 0` for every `z` mapping to some `u y`; hence the zero map
`Rε_*L ⟶ 0` is invertible on derived sections over the members of a covering sieve of every
object, so it becomes invertible after sheafification, and `L = ε^*Rε_*L = 0`. -/
theorem isZero_of_isZero_pushforward [f.u.IsCocontinuous Y.J X.J]
    (hcov : ∀ x : X.C, ∃ S : Sieve x, S ∈ X.J x ∧
      ∀ ⦃z : X.C⦄ (a : z ⟶ x), S a → ∃ y : Y.C, Nonempty (z ⟶ f.u.obj y))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsCartesianPushforwardOn X L)
    (h : IsZero (f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.obj L)) :
    IsZero L := by
  set bc := baseChangeDataOfComm.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
    Stacks.TerminalBaseChange.CommSections.mul_comm
  set N := (derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L
  have hz : ∀ z : X.C, (∃ y : Y.C, Nonempty (z ⟶ f.u.obj y)) →
      IsZero ((RGamma.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op z)).obj N) := by
    rintro z ⟨y, ⟨b⟩⟩
    have h1 := isZero_rGamma_of_isZero_pushforward f L h y
    have := hL b.op
    have := (bc.baseChangeAdj b.op).isLeftAdjoint
    exact ((bc.baseChange b.op).map_isZero h1).of_iso (asIso (comparison.{u} bc b.op N)).symm
  have hc : IsIso ((epsilonPullback.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategory.map (0 : N ⟶ 0)) := by
    refine isIso_epsilonPullback_map_of_exists_mem_sieve.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (0 : N ⟶ 0)
      fun V ↦ ?_
    obtain ⟨S, hS, hSz⟩ := hcov V
    exact ⟨S, hS, fun Z a ha ↦ (hz Z (hSz a ha)).isIso
      ((RGamma.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op Z)).map_isZero
        (isZero_zero _)) _⟩
  have h0 : IsZero ((epsilonPullback.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategory.obj N) :=
    (((epsilonPullback.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategory.map_isZero
      (isZero_zero _))).of_iso
      (asIso ((epsilonPullback.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).mapDerivedCategory.map (0 : N ⟶ 0)))
  exact h0.of_iso (asIso ((derivedEpsilonAdjunction.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).counit.app L)).symm

section ModelObj

open Stacks.Injectives (grothendieckModelEquiv hasDerivedCategory_of_isGrothendieckAbelian
  mapDerivedCategoryModelIso)

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The derived functor of an exact functor between Grothendieck abelian categories, read on
the locally small models of Tag 079Q at an object, is its standard-model derived functor at the
same object followed by the comparison equivalence of the target. -/
def mapDerivedCategoryShrinkObjIso
    (E : @DerivedCategory A _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w₁} A)) :
    (@Functor.mapDerivedCategory A _ _ (hasDerivedCategory_of_isGrothendieckAbelian.{w₁} A) B _ _
        (hasDerivedCategory_of_isGrothendieckAbelian.{w₂} B) F _ _ _).obj E ≅
      (grothendieckModelEquiv.{w₂} B).functor.obj
        ((@Functor.mapDerivedCategory A _ _ (HasDerivedCategory.standard A) B _ _
          (HasDerivedCategory.standard B) F _ _ _).obj E) :=
  (@mapDerivedCategoryModelIso.{w₁} A _ _ _ B _ _
    (hasDerivedCategory_of_isGrothendieckAbelian.{w₂} B) F _ _ _).symm.app E ≪≫
    (mapDerivedCategoryTargetModelIso (HasDerivedCategory.standard A) B F).app E

end ModelObj

attribute [local instance] derivedEpsilonPushforwardCommShift in
/-- The 0GZS subcategory is a triangulated subcategory: it is the preimage under the
triangulated functor `Rε_*` of the triangulated subcategory `QC(O)` (Stacks 0GYW). -/
instance isTriangulated_isCartesianPushforwardOn (Z : RingedSite.{u, u, u})
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (IsCartesianPushforwardOn Z).IsTriangulated :=
  haveI := derivedEpsilonPushforward_isTriangulated.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)
  inferInstanceAs (ObjectProperty.inverseImage (IsQC.{u} (baseChangeDataOfComm.{u, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj
      Stacks.TerminalBaseChange.CommSections.mul_comm))
      (derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).IsTriangulated

/-- The 0GZS subcategory is closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_isCartesianPushforwardOn (Z : RingedSite.{u, u, u})
    [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (IsCartesianPushforwardOn Z).IsClosedUnderIsomorphisms :=
  inferInstanceAs (ObjectProperty.inverseImage (IsQC.{u} (baseChangeDataOfComm.{u, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj
      Stacks.TerminalBaseChange.CommSections.mul_comm))
      (derivedEpsilonPushforward.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))).IsClosedUnderIsomorphisms

/-- The structure map of a morphism of ringed sites, read on presheaves of rings, is invertible
when the structure map is. -/
instance isIso_fSharpPresheaf [IsIso f.fsharp] :
    IsIso f.toRingedToposSiteHom.fSharpPresheaf := by
  haveI : IsIso ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).map f.fsharp) :=
    inferInstance
  exact inferInstanceAs (IsIso ((sheafToPresheaf _ _).map
    ((sheafCompose Y.J (forget₂ CommRingCat.{u} RingCat.{u})).map f.fsharp)))

/-- **The direct image along a cocontinuous morphism of ringed sites with invertible structure
map preserves the 0GZS subcategory.** `Rε_*(f_* L)` is the inverse image of `Rε_*L` along `u`
with scalars restricted along `f^♯` (`derivedEpsilonPushforwardInverseImageIso`); the inverse image
of a cartesian object is cartesian (Stacks 0GZ1), and so is its restriction of scalars along an
isomorphism of presheaves of rings. -/
theorem isCartesianPushforwardOn_pushforward [f.u.IsCocontinuous Y.J X.J] [IsIso f.fsharp]
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsCartesianPushforwardOn X L) :
    IsCartesianPushforwardOn Y
      (f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.obj L) := by
  refine (isQC_isClosedUnderIsomorphisms.{u} _).of_iso
    ((derivedEpsilonPushforwardInverseImageIso f).app L).symm
    ((Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isQC_restrictScalars_iff.{u}
      f.toRingedToposSiteHom.fSharpPresheaf _
      (baseChangeDataOfComm.{u, u, u, u} (f.u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (fun V x y ↦ mul_comm (G := (X.O.obj.obj (f.u.op.obj V) : Type u)) x y)) _).2 ?_)
  exact Stacks.ModulesOnACategory.PullbackPreservesQuasiCoherent.isQC_dInverseImage f.u
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj _ _ _ hL

section Slice

/-- The canonical base-change datum of the restriction `O_x` of the structure sheaf of a ringed
site to the slice over an object `x`. -/
abbrev baseChangeDataOver (Z : RingedSite.{u, u, u}) (x : Z.C) :
    BaseChangeData.{u} (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj x) :=
  baseChangeDataOfComm.{u, u, u, u} (overRingPresheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj x)
    (comm_overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj x
      Stacks.TerminalBaseChange.CommSections.mul_comm)

/-- The derived pullback `Lp^* : D(O(x)) ⥤ D(O_x)` along the morphism of chaotic sites
`(C/x, O_x) ⟶ (pt, O_x(t))` given by a terminal object `t` of the slice `C/x`. -/
abbrev slicePullback (Z : RingedSite.{u, u, u}) (x : Z.C) {t : Over x} (ht : IsTerminal t) :=
  (morphismOfSites.{u} (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj x)
    (comm_overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj x
      Stacks.TerminalBaseChange.CommSections.mul_comm)
    ht).Lpullback

variable (Z : RingedSite.{u, u, u}) [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The comparison map of `Rε_{x*}(L|_x)` along an arrow of the slice `C/x` is invertible exactly
when the comparison map of `Rε_*L` along the underlying arrow of `C` is. -/
theorem isIso_comparison_restriction_iff (x : Z.C)
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    {A B : (Over x)ᵒᵖ} (a : B ⟶ A) :
    IsIso (comparison.{u} (baseChangeDataOver Z x) a
        ((sliceDerivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x).obj
          ((sheafRestriction.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x).mapDerivedCategory.obj L))) ↔
      IsIso (comparison.{u} (baseChangeDataOfComm.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj
          Stacks.TerminalBaseChange.CommSections.mul_comm) ((Over.forget x).op.map a)
        ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).obj L)) := by
  refine (Stacks.ModulesOnACategory.QuasiCoherentRestrictScalars.isIso_comparison_iff_of_iso _ a
    ((derivedRestrictionPushforwardIso.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x).app L)).symm.trans ?_
  dsimp only [Functor.comp_obj]
  rw [← comparison_derivedRestriction.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj x
    (baseChangeDataOfComm.{u, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj
      Stacks.TerminalBaseChange.CommSections.mul_comm) _ _ a]
  simp only [isIso_comp_left_iff, isIso_comp_right_iff]

omit [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The invertibility of the `ε`-unit of the slice `C/x` at the derived base changes from the
terminal object `id_x` passes to the terminal object `Over.mk g` for any `g = id_x`. -/
theorem isIso_unit_slicePullback_of_eq_id (x : Z.C)
    (hunit : ∀ P, IsIso ((derivedEpsilonAdjunction.{u} (overRingSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x)).unit.app
      ((slicePullback Z x (Over.mkIdTerminal (X := x))).obj P)))
    {g : x ⟶ x} (hg : g = 𝟙 x) (ht : IsTerminal (Over.mk g)) (P) :
    IsIso ((derivedEpsilonAdjunction.{u} (overRingSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x)).unit.app
      ((slicePullback Z x ht).obj P)) := by
  subst hg
  obtain rfl : ht = Over.mkIdTerminal := Subsingleton.elim _ _
  exact hunit P

omit [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- If the `ε`-unit of the slice `C/x` is invertible at the derived base change `Lp^*P` from a
terminal object, then the sheafification `ε^*Lp^*P` lies in the 0GZS subcategory of the slice: its
derived pushforward is `Lp^*P`, which is cartesian (Stacks 0H0R). -/
theorem isCartesianPushforward_epsilonPullback_slicePullback (x : Z.C) {t : Over x}
    (ht : IsTerminal t) (P)
    (hP : IsIso ((derivedEpsilonAdjunction.{u} (overRingSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x)).unit.app
      ((slicePullback Z x ht).obj P))) :
    IsCartesianPushforward.{u} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x)
      (baseChangeDataOver Z x)
      ((epsilonPullback.{u} (overRingSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x)).mapDerivedCategory.obj
        ((slicePullback Z x ht).obj P)) :=
  (isQC_isClosedUnderIsomorphisms.{u} _).of_iso
    (asIso ((derivedEpsilonAdjunction.{u} (overRingSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) x)).unit.app
      ((slicePullback Z x ht).obj P)))
    (main_Lpullback_isQC.{u} _ (morphismOfSites.{u} (overRingPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj x)
      (comm_overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj x
        Stacks.TerminalBaseChange.CommSections.mul_comm)
      ht) P)

end Slice

section Local

open Stacks.Injectives (grothendieckModelEquiv)

attribute [local instance] AlgebraicGeometry.RingedSite.derivedPullbackHasLeftDerived

variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The restriction of an object of the 0GZS subcategory to a slice is a sheafified base
change.** For `K` in the 0GZS subcategory and an object `y`, the restriction `K|_y` to the slice
`C/y`, whose terminal object is `id_y`, is `ε^*(Lp^*RΓ(y, K))`: the counit of `Lp^* ⊣ RΓ(id_y, -)`
is invertible at the cartesian object `Rε_*(K|_y)` (Stacks 0H0R), and `ε^*Rε_* = id`. -/
def restrictionTildeIso (K : DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : IsCartesianPushforwardOn Y K) (y : Y.C) :
    (sheafRestriction.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y).mapDerivedCategory.obj K ≅
      (epsilonPullback.{u} (overRingSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y)).mapDerivedCategory.obj
        ((slicePullback Y y (Over.mkIdTerminal (X := y))).obj
          ((RGamma.{u} (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y)
            (op (Over.mk (𝟙 y)))).obj
            ((derivedEpsilonPushforward.{u} (overRingSheaf
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y)).obj
              ((sheafRestriction.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y).mapDerivedCategory.obj K)))) :=
  haveI := main_counit_isIso.{u} (baseChangeDataOver Y y)
    (morphismOfSites.{u} (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y)
      (comm_overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y
        Stacks.TerminalBaseChange.CommSections.mul_comm)
      (Over.mkIdTerminal (X := y))) _
    ((isCartesianPushforward_iff_forall_restriction.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
      Stacks.TerminalBaseChange.CommSections.mul_comm K).1 hK y)
  (asIso ((derivedEpsilonAdjunction.{u} (overRingSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y)).counit.app _)).symm ≪≫
    (epsilonPullback.{u} (overRingSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y)).mapDerivedCategory.mapIso
      (asIso ((morphismOfSites.{u} (overRingPresheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y)
        (comm_overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y
          Stacks.TerminalBaseChange.CommSections.mul_comm)
        (Over.mkIdTerminal (X := y))).adj.counit.app _)).symm

open Stacks.ModulesOnACategory.TildePullback
  (tilde structureMapAt derivedPullbackTildeIsoOfIsIso)

/-- `restrictionTildeIso` read in the standard model of the derived category of sheaves of
modules on the slice, in which the derived pullback of Tag 06YY and the tilde functor
`Stacks.ModulesOnACategory.TildePullback.tilde` are stated. -/
def restrictionTildeStdIso (K : DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : IsCartesianPushforwardOn Y K) (y : Y.C) :
    (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (sheafRestriction.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y) _ _ _).obj K ≅
      (tilde (Z := Y.over y) (Over.mkIdTerminal (X := y))).obj
          ((RGamma.{u} (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y)
            (op (Over.mk (𝟙 y)))).obj
            ((derivedEpsilonPushforward.{u} (overRingSheaf
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y)).obj
              ((sheafRestriction.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y).mapDerivedCategory.obj K))) :=
  (grothendieckModelEquiv.{u} (SheafOfModules.{u} (overRingSheaf
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y))
    ).fullyFaithfulFunctor.preimageIso
    ((mapDerivedCategoryShrinkObjIso (sheafRestriction.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y) K).symm ≪≫
      restrictionTildeIso K hK y ≪≫
      (mapDerivedCategoryTargetModelIso
        (Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory.{u, u, u, u}
          (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y)) _
        (epsilonPullback.{u} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y))).app _)

/-- The image `u(id_y) = Over.mk (u.map (𝟙 y))` of the terminal object of the slice over `y`
is terminal in the slice over `u y`. -/
def localizedTerminal (y : Y.C) : IsTerminal ((f.localized y).u.obj (Over.mk (𝟙 y))) :=
  Over.mkIdTerminal.ofIso (Over.isoMk (Iso.refl _) (by simp [Over.post]))

/-- The localization of a morphism of ringed sites with invertible structure map has invertible
structure map. -/
instance isIso_localized_fsharp [IsIso f.fsharp] (y : Y.C) : IsIso (f.localized y).fsharp :=
  inferInstanceAs (IsIso ((Y.J.overPullback CommRingCat.{u} y).map f.fsharp))

/-- The structure map of the localized morphism at the terminal object `id_y` is invertible
when that of the morphism is. -/
instance isIso_structureMapAt_localized [IsIso f.fsharp] (y : Y.C) :
    IsIso (structureMapAt (f.localized y) (Over.mk (𝟙 y))) :=
  inferInstanceAs (IsIso ((f.localized y).toRingedToposSiteHom.fSharpPresheaf.app _))

variable [IsIso f.fsharp]

/-- **The derived pullback of an object of the 0GZS subcategory, restricted to the slice over
`u y`, is a sheafified base change** (standard model). Restriction to `C/u y` of `Lf^*K` is
`L(f_y)^*(K|_y)` by the derived localization square of Stacks 04J0; `K|_y` is the sheafified base
change of `RΓ(y, K)` by `restrictionTildeStdIso`; and the derived pullback of a sheafified base
change from a terminal object is the sheafified base change of the scalar extension
(`Stacks.ModulesOnACategory.TildePullback.derivedPullbackTildeIsoOfIsIso`), which is a restriction
of scalars since the structure map is invertible. -/
def restrictionDerivedPullbackStdIso (K : DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : IsCartesianPushforwardOn Y K) (y : Y.C) :
    (@Functor.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
        (HasDerivedCategory.standard _) (sheafRestriction.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj y)) _ _ _).obj
        ((@DerivedPullbackPushforwardAdjunction.derivedPullback _ _ _ _ _ _ f.toRingedToposSiteHom
          (_) (_) (RingedSite.derivedPullbackHasLeftDerived f)).obj
          ((grothendieckModelEquiv.{u}
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inverse.obj K)) ≅
      (tilde (Z := X.over (f.u.obj y)) (localizedTerminal f y)).obj
        ((ModuleCat.restrictScalars.{u}
          (inv (structureMapAt (f.localized y) (Over.mk (𝟙 y)))).hom).mapDerivedCategory.obj
          ((RGamma.{u} (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y)
            (op (Over.mk (𝟙 y)))).obj
            ((derivedEpsilonPushforward.{u} (overRingSheaf
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y)).obj
              ((sheafRestriction.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y).mapDerivedCategory.obj K)))) :=
  (f.nonempty_derivedPullbackLocalizedIso_of_noFiniteLimits y K).some.symm ≪≫
    (@DerivedPullbackPushforwardAdjunction.derivedPullback _ _ _ _ _ _
      (f.localized y).toRingedToposSiteHom (_) (_)
      (RingedSite.derivedPullbackHasLeftDerived (f.localized y))).mapIso
        (restrictionTildeStdIso K hK y) ≪≫
    (derivedPullbackTildeIsoOfIsIso (f.localized y) (Over.mkIdTerminal (X := y))
      (localizedTerminal f y)).app _

variable [f.u.IsCocontinuous Y.J X.J]

/-- `restrictionDerivedPullbackStdIso` read in the locally small models of Tag 079Q, in which
`Rε_*` and the 0GZS subcategory are stated. -/
def restrictionSmallDerivedPullbackIso (K : DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : IsCartesianPushforwardOn Y K) (y : Y.C) :
    (sheafRestriction.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (f.u.obj y)).mapDerivedCategory.obj
        ((smallDerivedPullback f).obj K) ≅
      (epsilonPullback.{u} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.u.obj y))).mapDerivedCategory.obj
        ((slicePullback X (f.u.obj y) (localizedTerminal f y)).obj
          ((ModuleCat.restrictScalars.{u}
            (inv (structureMapAt (f.localized y) (Over.mk (𝟙 y)))).hom).mapDerivedCategory.obj
            ((RGamma.{u} (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj y)
              (op (Over.mk (𝟙 y)))).obj
              ((derivedEpsilonPushforward.{u} (overRingSheaf
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y)).obj
                ((sheafRestriction.{u}
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) y).mapDerivedCategory.obj K))))) :=
  mapDerivedCategoryShrinkObjIso (sheafRestriction.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (f.u.obj y)) _ ≪≫
    (grothendieckModelEquiv.{u} (SheafOfModules.{u} (overRingSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj y)))
      ).functor.mapIso (restrictionDerivedPullbackStdIso f K hK y) ≪≫
    ((mapDerivedCategoryTargetModelIso
        (Stacks.ModulesOnACategory.QuasiCoherentEquivalence.derivedPresheafCategory.{u, u, u, u}
          (overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (f.u.obj y))) _
        (epsilonPullback.{u} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (f.u.obj y)))).app _).symm

omit [f.u.IsCocontinuous Y.J X.J] in
/-- **The derived pullback of an object of the 0GZS subcategory lies in the 0GZS subcategory
over every object of the image of `u`.** Suppose the `ε`-unit of every slice of the source is
invertible at the derived base changes from its terminal object (`hunit`). For `K` in the 0GZS
subcategory of the target and an object `y`, the restriction of `Lf^*K` to the slice over `u y` is
a sheafified base change from the terminal object (`restrictionSmallDerivedPullbackIso`), hence
lies in the 0GZS subcategory of that slice. -/
theorem isCartesianPushforward_restriction_smallDerivedPullback
    (hunit : ∀ (x : X.C) (P), IsIso ((derivedEpsilonAdjunction.{u}
      (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) x)).unit.app
        ((slicePullback X x (Over.mkIdTerminal (X := x))).obj P)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : IsCartesianPushforwardOn Y K) (y : Y.C) :
    IsCartesianPushforward.{u} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (f.u.obj y))
      (baseChangeDataOver X (f.u.obj y))
      ((sheafRestriction.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (f.u.obj y)).mapDerivedCategory.obj
        ((smallDerivedPullback f).obj K)) :=
  (isQC_isClosedUnderIsomorphisms.{u} _).of_iso
    ((derivedEpsilonPushforward.{u} (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (f.u.obj y))).mapIso
      (restrictionSmallDerivedPullbackIso f K hK y).symm)
    (isCartesianPushforward_epsilonPullback_slicePullback X (f.u.obj y) _ _
      (isIso_unit_slicePullback_of_eq_id X (f.u.obj y) (hunit (f.u.obj y))
        (g := f.u.map (𝟙 y)) (f.u.map_id y) (localizedTerminal f y) _))

omit [f.u.IsCocontinuous Y.J X.J] in
/-- Under `hunit`, for `K` in the 0GZS subcategory of the target, the comparison map of
`Rε_*(Lf^*K)` along every arrow `z ⟶ z'` whose target maps to some `u y` is invertible. -/
theorem isIso_comparison_smallDerivedPullback_of_hom
    (hunit : ∀ (x : X.C) (P), IsIso ((derivedEpsilonAdjunction.{u}
      (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) x)).unit.app
        ((slicePullback X x (Over.mkIdTerminal (X := x))).obj P)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : IsCartesianPushforwardOn Y K) {y : Y.C} {z z' : X.C} (a : z ⟶ z')
    (c : z' ⟶ f.u.obj y) :
    IsIso (comparison.{u} (baseChangeDataOfComm.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
      Stacks.TerminalBaseChange.CommSections.mul_comm) a.op
      ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        ((smallDerivedPullback f).obj K))) :=
  (isIso_comparison_restriction_iff X (f.u.obj y) _
    (Over.homMk a : Over.mk (a ≫ c) ⟶ Over.mk c).op).1
    (isCartesianPushforward_restriction_smallDerivedPullback f hunit K hK y _)

end Local

/-- **A descent cover of an object `x` of the source.** A family of arrows `π i : obj i ⟶ x`
generating a covering sieve, each `obj i` mapping to an object in the image of `u`, along which
the cartesian condition descends: if `Rε_*L` has invertible comparison maps along every arrow
whose target maps to some `obj i`, then it has invertible comparison maps along each `π i`. For
the big affine étale site of an algebraic stack and the affine étale site of a representing
algebraic space, the descent property is étale descent through the small étale site of `x`. -/
structure DescentCover (x : X.C) where
  /-- The index type of the family. -/
  ι : Type t
  /-- The sources of the arrows of the family. -/
  obj : ι → X.C
  /-- The arrows of the family. -/
  π : ∀ i, obj i ⟶ x
  /-- The family generates a covering sieve of `x`. -/
  mem_sieve : Sieve.ofArrows obj π ∈ X.J x
  /-- Each source of the family maps to an object in the image of `u`. -/
  exists_hom (i : ι) : ∃ y : Y.C, Nonempty (obj i ⟶ f.u.obj y)
  /-- The cartesian condition descends along the family. -/
  isIso_comparison (L : DerivedCategory (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : ∀ ⦃z z' : X.C⦄ (a : z ⟶ z') (i : ι), Nonempty (z' ⟶ obj i) →
      IsIso (comparison.{u} (baseChangeDataOfComm.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
        Stacks.TerminalBaseChange.CommSections.mul_comm) a.op
        ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L)))
    (i : ι) :
    IsIso (comparison.{u} (baseChangeDataOfComm.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj
        Stacks.TerminalBaseChange.CommSections.mul_comm) (π i).op
      ((derivedEpsilonPushforward.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj L))

section Main

attribute [local instance] AlgebraicGeometry.RingedSite.derivedPullbackHasLeftDerived

variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [f.u.IsCocontinuous Y.J X.J] [f.u.Full] [f.u.Faithful] [IsIso f.fsharp]
  (hunit : ∀ (x : X.C) (P), IsIso ((derivedEpsilonAdjunction.{u}
      (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) x)).unit.app
        ((slicePullback X x (Over.mkIdTerminal (X := x))).obj P)))
  (hcov : ∀ x : X.C, Nonempty (DescentCover.{t} f x))

omit [f.u.IsCocontinuous Y.J X.J] [f.u.Full] [f.u.Faithful] in
include hunit hcov in
/-- **`Lf^*` carries the 0GZS subcategory of the target into that of the source.** The 0GZS
condition is local over the objects of the source
(`isCartesianPushforward_iff_forall_restriction`). Over an object `x` choose a descent cover
`π i : x_i ⟶ x`. The comparison maps of `Rε_*(Lf^*K)` along arrows over the image of `u` are
invertible (`isIso_comparison_smallDerivedPullback_of_hom`), so those along arrows over the `x_i`
are, and by descent so are those along the `π i`; the 0GZS condition on the slice over `x` then
glues from the covering family (`isCartesianPushforward_of_comparison_of_exists_mem_sieve`), the
`ε`-unit being invertible at derived base changes from the terminal object by `hunit`. -/
theorem isCartesianPushforwardOn_smallDerivedPullback
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : IsCartesianPushforwardOn Y K) :
    IsCartesianPushforwardOn X ((smallDerivedPullback f).obj K) := by
  refine (isCartesianPushforward_iff_forall_restriction.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    Stacks.TerminalBaseChange.CommSections.mul_comm _).2 fun x ↦ ?_
  obtain ⟨D⟩ := hcov x
  have hloc : ∀ {i} {z z' : X.C} (a : z ⟶ z') (b : z' ⟶ D.obj i), _ := fun {i} {_ _} a b ↦
    isIso_comparison_smallDerivedPullback_of_hom f hunit K hK a
      (b ≫ (D.exists_hom i).choose_spec.some)
  have hπ := D.isIso_comparison ((smallDerivedPullback f).obj K) fun z z' a i ⟨b⟩ ↦ hloc a b
  intro U V a
  refine isCartesianPushforward_of_comparison_of_exists_mem_sieve.{u}
    (overRingSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) x)
    (comm_overRingPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj x
      Stacks.TerminalBaseChange.CommSections.mul_comm)
    (Over.mkIdTerminal (X := x)) _ (fun i ↦ Over.mk (D.π i)) (fun i ↦ ?_) (fun V ↦ ?_)
    (hunit x _) a
  · refine (isIso_comparison_restriction_iff X x _ _).2 ?_
    have h : (Over.mkIdTerminal.from (Over.mk (D.π i))).left = D.π i := by
      simp
    show IsIso (comparison.{u} _ (Over.mkIdTerminal.from (Over.mk (D.π i))).left.op _)
    rw [h]
    exact hπ i
  · refine ⟨(Sieve.overEquiv V).symm (Sieve.pullback V.hom (Sieve.ofArrows D.obj D.π)),
      GrothendieckTopology.overEquiv_symm_mem_over _ _ _ (X.J.pullback_stable _ D.mem_sieve),
      fun Y' a ha ↦ ?_⟩
    rw [Sieve.overEquiv_symm_iff, Sieve.pullback_apply, Sieve.mem_ofArrows_iff] at ha
    obtain ⟨i, h, hh⟩ := ha
    refine ⟨i, Over.homMk h (by simp [← hh]), ?_⟩
    exact (isIso_comparison_restriction_iff X x _ _).2 (hloc h (𝟙 _))

omit [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Y.C, HasSheafify (Y.J.over U) AddCommGrpCat.{u}]
  [∀ U : Y.C, (Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [f.u.Full] [f.u.Faithful] [IsIso f.fsharp] in
include hcov in
/-- The direct image has zero kernel on the 0GZS subcategory when every object has a descent
cover. -/
theorem isZero_of_isCartesianPushforwardOn_of_isZero_pushforward
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsCartesianPushforwardOn X L)
    (h : IsZero (f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.obj L)) :
    IsZero L := by
  refine isZero_of_isZero_pushforward f (fun x ↦ ?_) L hL h
  obtain ⟨D⟩ := hcov x
  refine ⟨_, D.mem_sieve, fun z a ha ↦ ?_⟩
  obtain ⟨i, b, -⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 ha
  obtain ⟨y, ⟨c⟩⟩ := D.exists_hom i
  exact ⟨y, ⟨b ≫ c⟩⟩

/-- **Restriction to a full subsite is an equivalence on the 0GZS subcategories.** Let
`f : (C, O_C) ⟶ (D, O_D)` be a morphism of ringed sites whose functor `u : D ⥤ C` is fully
faithful and cocontinuous and whose structure map is invertible. Suppose the `ε`-unit of every
slice of `C` is invertible at the derived base changes from its terminal object (`hunit`) and
every object of `C` has a descent cover (`hcov`). Then `Lf^*` and `f_*` restrict to mutually
inverse equivalences between the full subcategories of `D(O_D)` and `D(O_C)` of the objects `K`
with `Rε_*K` cartesian.

The adjunction `Lf^* ⊣ f_*` has invertible unit (`isIso_smallDerivedPullbackAdjunction_unit`),
`f_*` is triangulated, `Lf^*` and `f_*` preserve the two subcategories
(`isCartesianPushforwardOn_smallDerivedPullback`, `isCartesianPushforwardOn_pushforward`), and
`f_*` has zero kernel on the subcategory of `D(O_C)`
(`isZero_of_isCartesianPushforwardOn_of_isZero_pushforward`), which is the argument of
Stacks 09J1 (`Stacks.Triangulated.restrictedEquivalence`). -/
def equivalence :
    (IsCartesianPushforwardOn Y).FullSubcategory ≌ (IsCartesianPushforwardOn X).FullSubcategory :=
  Stacks.Triangulated.restrictedEquivalence (smallDerivedPullbackAdjunction f)
    (IsCartesianPushforwardOn Y) (IsCartesianPushforwardOn X)
    (isCartesianPushforwardOn_smallDerivedPullback f hunit hcov)
    (isCartesianPushforwardOn_pushforward f)
    (isZero_of_isCartesianPushforwardOn_of_isZero_pushforward f hcov)

/-- The functor of `equivalence` is the restriction of the derived pullback `Lf^*`. -/
theorem equivalence_functor_obj_obj (K : (IsCartesianPushforwardOn Y).FullSubcategory) :
    ((equivalence f hunit hcov).functor.obj K).obj = (smallDerivedPullback f).obj K.obj :=
  rfl

/-- The inverse of `equivalence` is the restriction of the direct image `f_*`. -/
theorem equivalence_inverse_obj_obj (L : (IsCartesianPushforwardOn X).FullSubcategory) :
    ((equivalence f hunit hcov).inverse.obj L).obj =
      f.toRingedToposSiteHom.pushforwardTopos.mapDerivedCategory.obj L.obj :=
  rfl

end Main

end Stacks.Cohomology.SubsiteQuasiCoherentEquivalence
