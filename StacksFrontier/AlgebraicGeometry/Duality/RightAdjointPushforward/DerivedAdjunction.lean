module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.DerivedAdjunction
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution

/-!
# The derived sheaf-Hom adjunction

Let `f : Y ⟶ X` be a morphism of schemes. Restriction of scalars from modules over `f₊ 𝒪_Y` to
modules over `𝒪_X` has the sheaf-Hom functor `ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` as right adjoint. This
file shows that their unbounded derived functors are again adjoint.

## Main definitions

* `AlgebraicGeometry.pushforwardRingCatSheaf` is the sheaf of rings `f₊ 𝒪_Y` on `X`.

## Main results

* `AlgebraicGeometry.derivedRestriction_adj_derivedSheafHom` says that the derived sheaf-Hom
  functor is right adjoint to derived restriction of scalars.

## Implementation notes

The ordinary sheaf-Hom functor and its adjunction are supplied as data; this is the interface
furnished by Stacks, Tag 0BUZ. Both derived functors are characterized by their universal
properties, so the assertion is independent of choices of models and retains the canonical
comparison maps to the underived functors.

**That data is no longer hypothetical.** It is constructed: the sheaf-Hom functor is
`RingedSpaceModuleAdjunction.homSheaf`, its adjunction with restriction of scalars is
`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction` (Tag 0BUZ), the right derived
functor exists by the K-injective resolutions of Tag 079P, and restriction of scalars is exact,
so `CategoryTheory.Functor.mapDerivedCategory` is its derived extension. Tag 0BV0 with nothing
assumed beyond the morphism `f` is therefore
`AlgebraicGeometry.derivedRestriction_adj_derivedHomSheaf`, in the module
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ConstructedDerivedAdjunction`,
which carries the tag with no caveat. The theorem below is the reduction those constructions are
fed into, and it is kept in the general form because the conclusion then depends on no choice of
model for either derived functor.

The existence of enough K-injective resolutions, which is what makes the right derived functor
pointwise, comes from `Stacks.Injectives.functorialKInjectiveResolution`.

## References

* [Stacks Project, Tag 0BV0](https://stacks.math.columbia.edu/tag/0BV0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Functor
open Stacks.DerivedFunctor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- Restriction of scalars between sheaves of modules preserves finite limits: it does so after
composing with the faithful forgetful functor to sheaves, which reflects them. -/
noncomputable instance restrictionPreservesFiniteLimits {C : Type*}
    [Category C] {J : GrothendieckTopology C} {R R' : Sheaf J RingCat} (α : R ⟶ R') :
    Limits.PreservesFiniteLimits (SheafOfModules.restrictScalars α) := by
  have h : Limits.PreservesFiniteLimits
      (SheafOfModules.restrictScalars α ⋙ SheafOfModules.toSheaf R) := by
    change Limits.PreservesFiniteLimits (SheafOfModules.toSheaf R')
    infer_instance
  exact Limits.preservesFiniteLimits_of_reflects_of_preserves
    (SheafOfModules.restrictScalars α) (SheafOfModules.toSheaf R)

/-- A functor sends a composite equal to the identity to a composite equal to the identity. -/
private theorem map_comp_eq_id {C D : Type*} [Category C] [Category D] (Q : C ⥤ D)
    {X Y : C} {f : X ⟶ Y} {g : Y ⟶ X} (h : f ≫ g = 𝟙 X) : Q.map f ≫ Q.map g = 𝟙 _ := by
  rw [← Q.map_comp, h, Q.map_id]

/-- An adjunction of additive functors between abelian categories induces an adjunction between
the induced functors on homotopy categories of complexes. -/
private noncomputable def homotopyAdjunction {A B : Type*}
    [Category A] [Category B] [Abelian A] [Abelian B]
    (G : B ⥤ A) (F : A ⥤ B) [G.Additive] [F.Additive] (adj : G ⊣ F) (c : ComplexShape ℤ) :
    G.mapHomotopyCategory c ⊣ F.mapHomotopyCategory c where
  unit := CategoryTheory.Quotient.natTransLift _
    (whiskerRight (adj.mapHomologicalComplex c).unit (HomotopyCategory.quotient B c))
  counit := CategoryTheory.Quotient.natTransLift _
    (whiskerRight (adj.mapHomologicalComplex c).counit (HomotopyCategory.quotient A c))
  left_triangle_components := by
    rintro ⟨X⟩
    exact map_comp_eq_id (HomotopyCategory.quotient A c)
      ((adj.mapHomologicalComplex c).left_triangle_components X)
  right_triangle_components := by
    rintro ⟨Y⟩
    exact map_comp_eq_id (HomotopyCategory.quotient B c)
      ((adj.mapHomologicalComplex c).right_triangle_components Y)

/-- The direct image `f₊ 𝒪_Y` of the structure sheaf, regarded as a sheaf of rings
on the target of `f`. -/
public noncomputable abbrev pushforwardRingCatSheaf {X Y : Scheme.{u}} (f : Y ⟶ X) :=
  ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf

/-- **Stacks 0BV0.** For a morphism `f : Y ⟶ X`, the derived internal-Hom
functor `Rℰom_{𝒪_X}(f₊ 𝒪_Y, -)` is right adjoint to the functor from
`D(f₊ 𝒪_Y)` to `D(𝒪_X)` induced by restriction of scalars.

This is the general form: the underived internal Hom, its adjunction with restriction of
scalars, and a derived extension of each are taken as data. All of that data is constructed, and
the unconditional form of the tag is
`AlgebraicGeometry.derivedRestriction_adj_derivedHomSheaf`.

This general form takes its functors as data, so it is not registered under [stacks 0BV0]; it is
superseded by `AlgebraicGeometry.derivedRestriction_adj_derivedHomSheaf`. -/
public theorem derivedRestriction_adj_derivedSheafHom
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (sheafHom : SheafOfModules.{u} X.ringCatSheaf ⥤
      SheafOfModules.{u} (pushforwardRingCatSheaf f)) [sheafHom.Additive]
    (underivedAdjunction :
      SheafOfModules.restrictScalars f.toRingCatSheafHom ⊣ sheafHom)
    (derivedSheafHom : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)))
    (derivedSheafHomComparison :
      sheafHom.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
        DerivedCategory.Qh ⋙ derivedSheafHom)
    [derivedSheafHom.IsRightDerivedFunctor derivedSheafHomComparison
      (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf)
        (ComplexShape.up ℤ))]
    (derivedRestriction :
      DerivedCategory (SheafOfModules.{u} (pushforwardRingCatSheaf f)) ⥤
        DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (derivedRestrictionComparison :
      letI : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
        SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
      DerivedCategory.Qh ⋙ derivedRestriction ⟶
        (SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [derivedRestriction.IsLeftDerivedFunctor derivedRestrictionComparison
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (pushforwardRingCatSheaf f)) (ComplexShape.up ℤ))] :
    Nonempty (derivedRestriction ⊣ derivedSheafHom) := by
  let : (SheafOfModules.restrictScalars f.toRingCatSheafHom).Additive :=
    SheafOfModules.instAdditiveRestrictScalars f.toRingCatSheafHom
  let G := SheafOfModules.restrictScalars f.toRingCatSheafHom
  let : G.IsLeftAdjoint := underivedAdjunction.isLeftAdjoint
  let : Limits.PreservesFiniteLimits G :=
    restrictionPreservesFiniteLimits f.toRingCatSheafHom
  let : Limits.PreservesFiniteColimits G := inferInstance
  let : G.PreservesHomology := inferInstance
  have hG : (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)).IsInvertedBy
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) := by
    rw [MorphismProperty.IsInvertedBy.iff_of_iso _
      (G.mapDerivedCategoryFactorsh).symm]
    exact MorphismProperty.IsInvertedBy.of_comp _ DerivedCategory.Qh
      (Localization.inverts _ _ ) _
  have : IsIso derivedRestrictionComparison :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _ hG
  have : (derivedRestriction ⋙ derivedSheafHom).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh derivedRestriction derivedSheafHom).inv ≫
        whiskerRight derivedRestrictionComparison derivedSheafHom)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
    apply (Functor.isLeftDerivedFunctor_iff_of_inverts _ _
      (MorphismProperty.IsInvertedBy.of_comp _ _ hG _)).2
    infer_instance
  have hK : ∀ K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ,
      ∃ (I : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
        (q : K ⟶ I), I.IsKInjective ∧ QuasiIso q := by
    intro K
    let R := Stacks.Injectives.functorialKInjectiveResolution
      (SheafOfModules.{u} X.ringCatSheaf)
    exact ⟨R.functor.obj K, R.inclusion.app K, R.isKInjective K, R.quasiIso K⟩
  let F := sheafHom.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  have : F.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    (F.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} hK).1
  have hterminal : ∀ Y : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf),
      Nonempty (Σ t : CostructuredArrow DerivedCategory.Qh Y, Limits.IsTerminal t) := by
    intro Y
    let K := (DerivedCategory.Qh.objPreimage Y).as
    obtain ⟨I, q, hI, hq⟩ := hK K
    have : I.IsKInjective := hI
    have hq' : HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)
        ((HomotopyCategory.quotient _ _).map q) := by
      rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    have : IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map q)) :=
      Localization.inverts _ _ _ hq'
    let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) ≅ Y :=
      (asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map q))).symm ≪≫
        DerivedCategory.Qh.objObjPreimageIso Y
    exact ⟨⟨CostructuredArrow.mk e.hom,
      terminalCostructuredArrowOfBijective DerivedCategory.Qh Y _ e
        (fun Z => CochainComplex.IsKInjective.Qh_map_bijective Z I)⟩⟩
  have hpres : derivedRestriction.PreservesPointwiseLeftKanExtension
      F DerivedCategory.Qh := fun Y => by
    obtain ⟨t, ht⟩ := (hterminal Y).some
    let : Limits.PreservesColimit
        (CostructuredArrow.proj DerivedCategory.Qh Y ⋙ F) derivedRestriction :=
      preservesColimitOfTerminal ht _ _
    infer_instance
  let : derivedRestriction.PreservesPointwiseLeftKanExtension
      F DerivedCategory.Qh := hpres
  let : HasPointwiseLeftKanExtension DerivedCategory.Qh F :=
    F.hasPointwiseLeftKanExtension_of_hasPointwiseRightDerivedFunctor
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  let : derivedRestriction.PreservesLeftKanExtension F DerivedCategory.Qh := inferInstance
  let : derivedSheafHom.IsLeftKanExtension derivedSheafHomComparison :=
    Functor.IsRightDerivedFunctor.isLeftKanExtension _ _
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
  have : (derivedSheafHom ⋙ derivedRestriction).IsRightDerivedFunctor
      (whiskerRight derivedSheafHomComparison derivedRestriction ≫
        (Functor.associator DerivedCategory.Qh derivedSheafHom derivedRestriction).hom)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    ⟨Functor.PreservesLeftKanExtension.preserves derivedSheafHom
      derivedSheafHomComparison⟩
  exact ⟨(homotopyAdjunction _ _ underivedAdjunction (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    derivedRestrictionComparison derivedSheafHomComparison⟩

end AlgebraicGeometry
