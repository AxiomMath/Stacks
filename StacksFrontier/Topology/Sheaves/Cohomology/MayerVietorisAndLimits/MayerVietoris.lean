module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.Topology.Sheaves.MayerVietoris
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.UnboundedTriangle
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# The unbounded Mayer--Vietoris triangle of a cover by two opens

Let `O` be a sheaf of rings on a topological space `X` which is the union of two open
subspaces `U` and `V`. Stacks 08BV is the distinguished triangle, functorial in the object
`E` of the unbounded derived category of `O`-modules,

`E ⟶ Rj_{U*}(E|_U) ⊕ Rj_{V*}(E|_V) ⟶ Rj_{(U∩V)*}(E|_{U∩V}) ⟶ E⟦1⟧`.

The proof is the dévissage of the source. Over injective sheaves of modules the sequence of
underived functors

`0 ⟶ id ⟶ j_{U*}j_U^* ⊕ j_{V*}j_V^* ⟶ j_{(U∩V)*}j_{U∩V}^* ⟶ 0`

is short exact: this is checked on sections over an arbitrary open, where it is the sheaf
condition for the cover of that open by its intersections with `U` and with `V`, together
with surjectivity of restriction of an injective sheaf of modules to a smaller open (Stacks
01EA). Evaluating the three functors on a functorial K-injective resolution (Stacks 079P)
computes each of the three right derived functors, so the short exact sequence of complexes
of injectives gives the distinguished triangle in the derived category, naturally in the
complex; and every object of the derived category is represented by such a complex.

## Main definitions

* `Stacks.Cohomology.MayerVietoris.resolutionCoverMiddleIso`: the derived functor of the
  underived biproduct of the two restrictions is the biproduct of the two derived functors.

## Main results

* `Stacks.Cohomology.MayerVietoris.exists_distinguished_triangle_of_cover`: the functorial
  distinguished Mayer--Vietoris triangle associated to a cover by two opens.

## Implementation notes

The ringed space is presented by a topological space and a sheaf of possibly noncommutative
rings, which harmlessly generalises the source. Rather than choosing models for the three
derived functors, the statement applies to arbitrary functors equipped with their
`IsRightDerivedFunctor` structures; the equations in the conclusion characterise the
restriction maps and the two difference maps through the supplied derived-functor comparison
maps, so the triangle's canonical maps, its Mayer--Vietoris sign and its naturality in `E` are
all retained rather than merely asserted to exist.

`DerivedCategory.Qh` is a localisation of the homotopy category at the quasi-isomorphisms, but
the corresponding instance is not found by typeclass inference at the elaboration of
`Functor.IsRightDerivedFunctor`, so it is supplied explicitly as `qhIsLocalization`.

The sheaf-level short exact sequence, the homotopy-category layer and the distinguished
triangle of a sequence exact on injectives all come from
`StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.UnboundedTriangle` and the
`RestrictionCoverShortExact` file it imports; what is added here is the naturality of the
comparison for the middle term, `resolutionCoverMiddleIso`, and the theorem that consumes it.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules
open Stacks.Cohomology.RestrictionCover

universe u

namespace Stacks.Cohomology.MayerVietoris

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

omit O in
/-- Sheaves of modules on a ringed space form a Grothendieck abelian category at the universe
of the space. The universe has to be pinned: typeclass inference cannot determine it from the
goals in which it is used below. -/
private local instance sheafOfModulesIsGrothendieckAbelian
    {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) :=
  inferInstance

/-! ### Universal-property bridges -/

private abbrev W : MorphismProperty
    (HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)

omit O in
/-- `DerivedCategory.Qh` is a localisation of the homotopy category at the quasi-isomorphisms.
Typeclass inference does not find this when elaborating `Functor.IsRightDerivedFunctor`, so it
is named and supplied explicitly below. -/
private noncomputable local instance qhIsLocalization
    {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} :
    (DerivedCategory.Qh (C := SheafOfModules.{u} O)).IsLocalization (W (O := O)) :=
  inferInstance

/-- The component of a derived-functor comparison map at the image of a complex, with its type
written in the form the complex-level comparison map needs. Carrying the identification
`(F.mapHomotopyCategory c).obj (Q₀ K) = Q₀ ((F.mapHomologicalComplex c).obj K)` in the result
type of a declaration, instead of rewriting through it, is what keeps the goals in
`complexDerivedUnit_fac` type-correct. -/
private noncomputable def complexUnitApp
    (F : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O) [F.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ homotopyLocalization O).obj K ⟶
      (homotopyLocalization O ⋙ RF).obj K :=
  α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)

/-- Reassociation of a composite of four morphisms, in the one shape needed below. Stating it
as a lemma lets the step be taken as a term: the composites involved are type-correct only at
the default transparency level, so `rw`/`simp only [Category.assoc]` cannot perform it. -/
private lemma assoc_reassoc {C : Type*} [Category C] {A B D E F : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ F) :
    a ≫ (b ≫ c) ≫ d = (a ≫ b) ≫ c ≫ d := by
  simp

/-! ### Biproduct bookkeeping

The biproducts below occur with their summands written through functor compositions, so the
`simp` set for `biprod` does not match them: the three lemmas of this section state the
bookkeeping steps for an abstract binary biproduct, where it does match, and the use sites
discharge the identification by a definitional-equality check in `exact`. -/

omit O in
/-- Two maps into a binary biproduct agree as soon as both of their components do. -/
private lemma comp_lift_eq_comp_lift {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D X₁ X₂ : C} [HasBinaryBiproduct X₁ X₂]
    (m : A ⟶ B) (n : A ⟶ D) (u : B ⟶ X₁) (v : B ⟶ X₂) (x : D ⟶ X₁) (y : D ⟶ X₂)
    (h₁ : m ≫ u = n ≫ x) (h₂ : m ≫ v = n ≫ y) :
    m ≫ biprod.lift u v = n ≫ biprod.lift x y := by
  apply biprod.hom_ext <;> simp [h₁, h₂]

omit O in
/-- Componentwise naturality of `biprod.lift` against `biprod.map`. -/
private lemma comp_lift_eq_lift_comp_map {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B X₁ X₂ Y₁ Y₂ : C} [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ Y₂]
    (m : A ⟶ B) (u : B ⟶ Y₁) (v : B ⟶ Y₂) (x : A ⟶ X₁) (y : A ⟶ X₂)
    (h : X₁ ⟶ Y₁) (k : X₂ ⟶ Y₂)
    (h₁ : m ≫ u = x ≫ h) (h₂ : m ≫ v = y ≫ k) :
    m ≫ biprod.lift u v = biprod.lift x y ≫ biprod.map h k := by
  apply biprod.hom_ext <;> simp [h₁, h₂]

omit O in
/-- The difference of the two projections of a binary biproduct, as a `biprod.desc`. -/
private lemma sub_eq_desc {C : Type*} [Category C] [Preadditive C] {X₁ X₂ B : C}
    [HasBinaryBiproduct X₁ X₂] (c : X₁ ⟶ B) (d : X₂ ⟶ B) :
    biprod.fst ≫ c - biprod.snd ≫ d = biprod.desc c (-d) := by
  rw [biprod.desc_eq, Preadditive.comp_neg, sub_eq_add_neg]

omit O in
/-- Assembling a map out of a binary biproduct from its two components, the second with a
sign. -/
private lemma lift_desc_eq_sub_comp {C : Type*} [Category C] [Preadditive C]
    {A B E M₁ M₂ X₁ X₂ : C} [HasBinaryBiproduct X₁ X₂]
    (p₁ : A ⟶ M₁) (p₂ : A ⟶ M₂) (u₁ : M₁ ⟶ X₁) (u₂ : M₂ ⟶ X₂)
    (c₁ : X₁ ⟶ E) (c₂ : X₂ ⟶ E) (t₁ : M₁ ⟶ B) (t₂ : M₂ ⟶ B) (z : A ⟶ B) (e : B ⟶ E)
    (h₁ : u₁ ≫ c₁ = t₁ ≫ e) (h₂ : u₂ ≫ c₂ = -(t₂ ≫ e))
    (h : p₁ ≫ t₁ - p₂ ≫ t₂ = z) :
    biprod.lift (p₁ ≫ u₁) (p₂ ≫ u₂) ≫ biprod.desc c₁ c₂ = z ≫ e := by
  rw [biprod.lift_desc, Category.assoc, Category.assoc, h₁, h₂, Preadditive.comp_neg,
    ← Category.assoc, ← Category.assoc, ← sub_eq_add_neg, ← Preadditive.sub_comp, h]

private lemma restrictionCoverFst_sub_snd (U V : Opens X) :
    restrictionCoverFst O U V ≫ restrictPushTransition O (U ⊓ V) U inf_le_left -
        restrictionCoverSnd O U V ≫ restrictPushTransition O (U ⊓ V) V inf_le_right =
      restrictionCoverSecond O U V :=
  NatTrans.ext <| funext fun M => sub_eq_desc
    ((restrictPushTransition O (U ⊓ V) U inf_le_left).app M)
    ((restrictPushTransition O (U ⊓ V) V inf_le_right).app M)

private lemma restrictionCoverFst_sub_snd_mapped (U V : Opens X)
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) :
    ((restrictionCoverFst O U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I ≫
        ((restrictPushTransition O (U ⊓ V) U inf_le_left).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I -
      ((restrictionCoverSnd O U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I ≫
        ((restrictPushTransition O (U ⊓ V) V inf_le_right).mapHomologicalComplex
          (ComplexShape.up ℤ)).app I =
    ((restrictionCoverSecond O U V).mapHomologicalComplex (ComplexShape.up ℤ)).app I := by
  ext n : 1
  exact NatTrans.congr_app (restrictionCoverFst_sub_snd O U V) (I.X n)

section CoverMiddle

variable (U V : Opens X)
  (RU RV : DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O))
  (eU : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
    (restrictPush O U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ RU)
  (eV : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
    (restrictPush O V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ RV)

private lemma coverMiddleIsoApp_hom
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (coverMiddleComponentIso O U V RU RV eU eV K).hom =
      biprod.lift
        (DerivedCategory.Q.map (((restrictionCoverFst O U V).mapHomologicalComplex
          (ComplexShape.up ℤ)).app
            ((Stacks.Injectives.kInjectiveResolutionFunctor
              (SheafOfModules.{u} O)).obj K)) ≫ eU.hom.app K)
        (DerivedCategory.Q.map (((restrictionCoverSnd O U V).mapHomologicalComplex
          (ComplexShape.up ℤ)).app
            ((Stacks.Injectives.kInjectiveResolutionFunctor
              (SheafOfModules.{u} O)).obj K)) ≫ eV.hom.app K) := by
  change biprod.lift
      (DerivedCategory.Q.map (((restrictionCoverFst O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)))
      (DerivedCategory.Q.map (((restrictionCoverSnd O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K))) ≫
    biprod.map (eU.hom.app K) (eV.hom.app K) = _
  apply biprod.hom_ext <;> simp

/-- Naturality of a single component of the comparison map: a projection of the degreewise
biproduct followed by that summand's resolution isomorphism. Both components of
`coverMiddleComponentIso` are instances of this, which keeps either one inside the default
heartbeat budget. -/
private lemma coverMiddleComponent_naturality
    (W' : Opens X)
    (RW : DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O))
    (p : restrictionCoverMiddle O U V ⟶ restrictPush O W')
    (e : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      (restrictPush O W').mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RW)
    {K L : CochainComplex (SheafOfModules.{u} O) ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map (((restrictionCoverMiddle O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
        ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).map f)) ≫
      DerivedCategory.Q.map ((p.mapHomologicalComplex (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj L)) ≫
        e.hom.app L =
      DerivedCategory.Q.map ((p.mapHomologicalComplex (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫
        (e.hom.app K ≫ RW.map (DerivedCategory.Q.map f)) := by
  rw [← Category.assoc, ← Functor.map_comp,
    (p.mapHomologicalComplex (ComplexShape.up ℤ)).naturality
      ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).map f),
    Functor.map_comp, Category.assoc]
  exact congrArg (fun t => DerivedCategory.Q.map
    ((p.mapHomologicalComplex (ComplexShape.up ℤ)).app
      ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫ t)
    (e.hom.naturality f)

private lemma coverMiddleIsoApp_naturality
    {K L : CochainComplex (SheafOfModules.{u} O) ℤ} (f : K ⟶ L) :
    (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      (restrictionCoverMiddle O U V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).map f ≫ (coverMiddleComponentIso O U V RU RV eU eV L).hom =
      (coverMiddleComponentIso O U V RU RV eU eV K).hom ≫
        (DerivedCategory.Q ⋙ derivedCoverMiddle O RU RV).map f := by
  rw [coverMiddleIsoApp_hom, coverMiddleIsoApp_hom]
  exact comp_lift_eq_lift_comp_map _ _ _ _ _ _ _
    ((coverMiddleComponent_naturality O U V U RU (restrictionCoverFst O U V) eU f).trans
      (Category.assoc _ _ _).symm)
    ((coverMiddleComponent_naturality O U V V RV (restrictionCoverSnd O U V) eV f).trans
      (Category.assoc _ _ _).symm)

/-- The derived functor of the underived biproduct of the two restrictions is the biproduct of
the two derived functors. -/
private noncomputable def resolutionCoverMiddleIso :
    Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      (restrictionCoverMiddle O U V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ≅ DerivedCategory.Q ⋙ derivedCoverMiddle O RU RV :=
  NatIso.ofComponents (coverMiddleComponentIso O U V RU RV eU eV)
    (fun f => coverMiddleIsoApp_naturality O U V RU RV eU eV f)

/-- The first map of the Mayer--Vietoris sequence is compatible with the comparison
isomorphisms: the restriction maps to the two opens assemble into the map to the biproduct.
Stated separately from the main theorem so that it gets its own heartbeat budget. -/
private lemma coverFirst_resolution_fac
    (rU : CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)) ⟶ RU)
    (rV : CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)) ⟶ RV)
    (eF : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      (CategoryTheory.Functor.id (SheafOfModules.{u} O)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)))
    (K : CochainComplex (SheafOfModules.{u} O) ℤ)
    (hU : eF.hom.app K ≫ rU.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((jStarAdjunction U O).unit.mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) ≫ eU.hom.app K)
    (hV : eF.hom.app K ≫ rV.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((jStarAdjunction V O).unit.mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) ≫ eV.hom.app K) :
    eF.hom.app K ≫ biprod.lift (rU.app (DerivedCategory.Q.obj K))
        (rV.app (DerivedCategory.Q.obj K)) =
      DerivedCategory.Q.map (((restrictionCoverFirst O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) ≫
        biprod.lift
          (DerivedCategory.Q.map (((restrictionCoverFst O U V).mapHomologicalComplex
            (ComplexShape.up ℤ)).app
              ((Stacks.Injectives.kInjectiveResolutionFunctor
                (SheafOfModules.{u} O)).obj K)) ≫ eU.hom.app K)
          (DerivedCategory.Q.map (((restrictionCoverSnd O U V).mapHomologicalComplex
            (ComplexShape.up ℤ)).app
              ((Stacks.Injectives.kInjectiveResolutionFunctor
                (SheafOfModules.{u} O)).obj K)) ≫ eV.hom.app K) := by
  have hqU : DerivedCategory.Q.map (((restrictionCoverFirst O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫
      DerivedCategory.Q.map (((restrictionCoverFst O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) =
      DerivedCategory.Q.map (((jStarAdjunction U O).unit.mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) := by
    rw [← Functor.map_comp]
    congr 1
    ext n : 1
    exact biprod.lift_fst _ _
  have hqV : DerivedCategory.Q.map (((restrictionCoverFirst O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫
      DerivedCategory.Q.map (((restrictionCoverSnd O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) =
      DerivedCategory.Q.map (((jStarAdjunction V O).unit.mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) := by
    rw [← Functor.map_comp]
    congr 1
    ext n : 1
    exact biprod.lift_snd _ _
  exact comp_lift_eq_comp_lift _ _ _ _ _ _
    (hU.trans ((congrArg (fun t => t ≫ eU.hom.app K) hqU.symm).trans (Category.assoc _ _ _)))
    (hV.trans ((congrArg (fun t => t ≫ eV.hom.app K) hqV.symm).trans (Category.assoc _ _ _)))

/-- The second map of the Mayer--Vietoris sequence is compatible with the comparison
isomorphisms: the difference of the two transition maps is the map out of the biproduct.
Stated separately from the main theorem so that it gets its own heartbeat budget. -/
private lemma coverSecond_resolution_fac
    (RUV : DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O))
    (eH : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      (restrictPush O (U ⊓ V)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RUV)
    (dU : RU ⟶ RUV) (dV : RV ⟶ RUV)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ)
    (hdu : eU.hom.app K ≫ dU.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((restrictPushTransition O (U ⊓ V) U
        inf_le_left).mapHomologicalComplex (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) ≫ eH.hom.app K)
    (hdv : eV.hom.app K ≫ dV.app (DerivedCategory.Q.obj K) =
      -(DerivedCategory.Q.map (((restrictPushTransition O (U ⊓ V) V
        inf_le_right).mapHomologicalComplex (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) ≫ eH.hom.app K)) :
    biprod.lift
        (DerivedCategory.Q.map (((restrictionCoverFst O U V).mapHomologicalComplex
          (ComplexShape.up ℤ)).app
            ((Stacks.Injectives.kInjectiveResolutionFunctor
              (SheafOfModules.{u} O)).obj K)) ≫ eU.hom.app K)
        (DerivedCategory.Q.map (((restrictionCoverSnd O U V).mapHomologicalComplex
          (ComplexShape.up ℤ)).app
            ((Stacks.Injectives.kInjectiveResolutionFunctor
              (SheafOfModules.{u} O)).obj K)) ≫ eV.hom.app K) ≫
      biprod.desc (dU.app (DerivedCategory.Q.obj K)) (dV.app (DerivedCategory.Q.obj K)) =
    DerivedCategory.Q.map (((restrictionCoverSecond O U V).mapHomologicalComplex
      (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor
          (SheafOfModules.{u} O)).obj K)) ≫ eH.hom.app K := by
  have hsub : DerivedCategory.Q.map (((restrictionCoverFst O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫
      DerivedCategory.Q.map (((restrictPushTransition O (U ⊓ V) U
        inf_le_left).mapHomologicalComplex (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) -
      DerivedCategory.Q.map (((restrictionCoverSnd O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫
      DerivedCategory.Q.map (((restrictPushTransition O (U ⊓ V) V
        inf_le_right).mapHomologicalComplex (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) =
      DerivedCategory.Q.map (((restrictionCoverSecond O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_sub,
      restrictionCoverFst_sub_snd_mapped]
  exact lift_desc_eq_sub_comp _ _ _ _ _ _ _ _ _ _ hdu hdv hsub

end CoverMiddle

/-- The restriction map of a right derived functor of `restrictPush O W'` is compatible with the
unit of the adjunction `jStarAdjunction W' O`, after passing to the derived category. -/
private lemma unit_restriction_fac (W' : Opens X)
    (RW : DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O))
    (aW : homotopyToDerived O W' ⟶ DerivedCategory.Qh ⋙ RW)
    [RW.IsRightDerivedFunctor aW (W (O := O))] :
    Functor.whiskerRight (homotopyIdentityIso O).hom DerivedCategory.Qh ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedRestrictionMap O (homotopyToDerived O W')
          RW aW (homotopyRestriction O W')) =
      Functor.whiskerRight ((jStarAdjunction W' O).unit.mapHomotopyCategory
        (ComplexShape.up ℤ)) DerivedCategory.Qh ≫ aW := by
  rw [← derivedRestrictionMap_fac O (homotopyToDerived O W') RW aW (homotopyRestriction O W')]
  dsimp [homotopyRestriction]
  simp [← Category.assoc, ← Functor.whiskerRight_comp]

/-- **Stacks 08BV.** A two-open cover gives a distinguished Mayer--Vietoris triangle, naturally
in every object of the unbounded derived category of modules. -/
@[stacks 08BV]
theorem exists_distinguished_triangle_of_cover
    (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (RU RV RUV : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyToDerived O U ⟶ DerivedCategory.Qh ⋙ RU)
    (aV : homotopyToDerived O V ⟶ DerivedCategory.Qh ⋙ RV)
    (aUV : homotopyToDerived O (U ⊓ V) ⟶ DerivedCategory.Qh ⋙ RUV)
    [RU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [RV.IsRightDerivedFunctor aV
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [RUV.IsRightDerivedFunctor aUV
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    ∃ (qU : homotopyToDerived O U ⟶ homotopyToDerived O (U ⊓ V))
      (qV : homotopyToDerived O V ⟶ homotopyToDerived O (U ⊓ V))
      (rU : (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)) :
        DerivedCategory (SheafOfModules.{u} O) ⥤
          DerivedCategory (SheafOfModules.{u} O)) ⟶ RU)
      (rV : (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)) :
        DerivedCategory (SheafOfModules.{u} O) ⥤
          DerivedCategory (SheafOfModules.{u} O)) ⟶ RV)
      (dU : RU ⟶ RUV) (dV : RV ⟶ RUV)
      (δ : RUV ⟶ (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)) :
          DerivedCategory (SheafOfModules.{u} O) ⥤
            DerivedCategory (SheafOfModules.{u} O)) ⋙
        shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)),
      homotopyRestriction O U ≫ qU = homotopyRestriction O (U ⊓ V) ∧
      homotopyRestriction O V ≫ qV = homotopyRestriction O (U ⊓ V) ∧
      homotopyRestriction O U ≫ aU = Functor.whiskerLeft DerivedCategory.Qh rU ∧
      homotopyRestriction O V ≫ aV = Functor.whiskerLeft DerivedCategory.Qh rV ∧
      qU ≫ aUV = aU ≫ Functor.whiskerLeft DerivedCategory.Qh dU ∧
      -(qV ≫ aUV) = aV ≫ Functor.whiskerLeft DerivedCategory.Qh dV ∧
      ∀ E, Triangle.mk (biprod.lift (rU.app E) (rV.app E))
        (biprod.desc (dU.app E) (dV.app E)) (δ.app E) ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O)) := by
  let T := U ⊓ V
  let qU := homotopyRestrictPushTransition O T U inf_le_left
  let qV := homotopyRestrictPushTransition O T V inf_le_right
  let rU := derivedRestrictionMap O (homotopyToDerived O U) RU aU
    (homotopyRestriction O U)
  let rV := derivedRestrictionMap O (homotopyToDerived O V) RV aV
    (homotopyRestriction O V)
  let dU := derivedRestrictionTransition O (homotopyToDerived O U)
    (homotopyToDerived O T) RU RUV aU aUV qU
  let dV := -derivedRestrictionTransition O (homotopyToDerived O V)
    (homotopyToDerived O T) RV RUV aV aUV qV
  have hdV : -(qV ≫ aUV) = aV ≫ Functor.whiskerLeft DerivedCategory.Qh dV := by
    ext K
    have h := NatTrans.congr_app (derivedRestrictionTransition_fac O
      (homotopyToDerived O V) (homotopyToDerived O T) RV RUV aV aUV qV) K
    simpa [dV, Preadditive.comp_neg] using congrArg Neg.neg h
  let aId := Functor.whiskerRight (homotopyIdentityIso O).hom DerivedCategory.Qh
  let _ : (Functor.id (DerivedCategory (SheafOfModules.{u} O))).IsRightDerivedFunctor
      aId (W (O := O)) :=
    Functor.isRightDerivedFunctor_of_inverts (W (O := O)) (Functor.id _)
      (Functor.isoWhiskerRight (homotopyIdentityIso O).symm DerivedCategory.Qh)
  let eF := resolutionDerivedIso O (Functor.id _) (Functor.id _) aId
  let eU := resolutionDerivedIso O (restrictPush O U) RU aU
  let eV := resolutionDerivedIso O (restrictPush O V) RV aV
  let eH := resolutionDerivedIso O (restrictPush O T) RUV aUV
  let eG := resolutionCoverMiddleIso O U V RU RV eU eV
  let rf : Functor.id (DerivedCategory (SheafOfModules.{u} O)) ⟶
      derivedCoverMiddle O RU RV :=
    { app := fun E => biprod.lift (rU.app E) (rV.app E)
      naturality := fun K L k => by
        apply biprod.hom_ext <;>
          simp [derivedCoverMiddle, ← rU.naturality, ← rV.naturality] }
  let rg : derivedCoverMiddle O RU RV ⟶ RUV :=
    { app := fun E => biprod.desc (dU.app E) (dV.app E)
      naturality := fun K L k => by
        apply biprod.hom_ext' <;>
          simp [derivedCoverMiddle, dU.naturality, dV.naturality] }
  have hU := unit_restriction_fac O U RU aU
  have hV := unit_restriction_fac O V RV aV
  have hf (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
      eF.hom.app K ≫ rf.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((restrictionCoverFirst O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) ≫ eG.hom.app K := by
    rw [show eG.hom.app K = _ from coverMiddleIsoApp_hom O U V RU RV eU eV K]
    exact coverFirst_resolution_fac O U V RU RV eU eV rU rV eF K
      (resolutionDerivedIso_fac O
        (F := Functor.id _) (G := restrictPush O U) (RF := Functor.id _) (RG := RU)
        aId aU (jStarAdjunction U O).unit rU hU K)
      (resolutionDerivedIso_fac O
        (F := Functor.id _) (G := restrictPush O V) (RF := Functor.id _) (RG := RV)
        aId aV (jStarAdjunction V O).unit rV hV K)
  have hg (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
      eG.hom.app K ≫ rg.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (((restrictionCoverSecond O U V).mapHomologicalComplex
        (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K)) ≫ eH.hom.app K := by
    have hdu := resolutionDerivedIso_fac O aU aUV
      (restrictPushTransition O T U inf_le_left) dU
      (derivedRestrictionTransition_fac O (homotopyToDerived O U)
        (homotopyToDerived O T) RU RUV aU aUV qU).symm K
    have hdv := resolutionDerivedIso_fac O aV aUV
      (restrictPushTransition O T V inf_le_right)
      (derivedRestrictionTransition O (homotopyToDerived O V)
        (homotopyToDerived O T) RV RUV aV aUV qV)
      (derivedRestrictionTransition_fac O (homotopyToDerived O V)
        (homotopyToDerived O T) RV RUV aV aUV qV).symm K
    have hdv' : eV.hom.app K ≫ dV.app (DerivedCategory.Q.obj K) =
        -(DerivedCategory.Q.map (((restrictPushTransition O T V
          inf_le_right).mapHomologicalComplex (ComplexShape.up ℤ)).app
            ((Stacks.Injectives.kInjectiveResolutionFunctor
              (SheafOfModules.{u} O)).obj K)) ≫ eH.hom.app K) := by
      simpa [dV, Preadditive.comp_neg] using congrArg Neg.neg hdv
    rw [show eG.hom.app K = _ from coverMiddleIsoApp_hom O U V RU RV eU eV K]
    exact coverSecond_resolution_fac O U V RU RV eU eV RUV eH dU dV K hdu hdv'
  let d := derivedTriangleOfShortExactOnInjectives O (Functor.id _)
    (restrictionCoverMiddle O U V) (restrictPush O T)
    (restrictionCoverFirst O U V) (restrictionCoverSecond O U V)
    (restrictionCoverFirst_comp_second O U V)
    (restrictionCoverShortExact_object O U V hUV)
    (Functor.id _) (derivedCoverMiddle O RU RV) RUV eF eG eH rf rg hf hg
  let δ := d.val
  refine ⟨qU, qV, rU, rV, dU, dV, δ, ?_⟩
  exact ⟨homotopyRestriction_transition O T U inf_le_left,
    homotopyRestriction_transition O T V inf_le_right,
    derivedRestrictionMap_fac O (homotopyToDerived O U) RU aU
      (homotopyRestriction O U),
    derivedRestrictionMap_fac O (homotopyToDerived O V) RV aV
      (homotopyRestriction O V),
    derivedRestrictionTransition_fac O (homotopyToDerived O U)
      (homotopyToDerived O T) RU RUV aU aUV qU,
    hdV,
    d.property⟩

end Stacks.Cohomology.MayerVietoris

end
