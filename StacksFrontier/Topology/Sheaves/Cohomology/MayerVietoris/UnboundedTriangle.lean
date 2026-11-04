module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GrothendieckAbelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExistsKInjectiveResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverShortExact
import StacksCore.Tactic.StacksAttribute

/-!
# The unbounded Mayer--Vietoris triangle for a cover by two opens

Let `X` be a topological space, `O` a sheaf of rings on `X`, and `X = U ∪ V` a cover by two
opens.  This file produces, functorially in an object of the unbounded derived category
`D(O)`, the distinguished triangle

`E ⟶ Rj_{U,*}E|_U ⊕ Rj_{V,*}E|_V ⟶ Rj_{U∩V,*}E|_{U∩V} ⟶ E[1]`.

## Main definitions

* `Stacks.Cohomology.RestrictionCover.homotopyToDerived`: the functor on homotopy categories
  whose right derived functor is `Rj_{U,*}(-)|_U`.
* `Stacks.Cohomology.RestrictionCover.homotopyRestriction`: the canonical restriction map
  before deriving.
* `Stacks.Cohomology.RestrictionCover.resolutionDerivedIso`: a chosen right derived functor,
  evaluated on a complex, is computed by the functorial K-injective resolution.
* `Stacks.Cohomology.RestrictionCover.derivedCoverMiddle`: the pointwise biproduct of two
  endofunctors of the derived category, the middle term of the triangle.

## Main results

* `Stacks.Cohomology.RestrictionCover.derivedTriangleOfShortExactOnInjectives`: the connecting
  map and the distinguished triangle, for any short exact sequence of additive endofunctors of
  `Mod(O)` which is short exact at every injective object.

The Mayer--Vietoris theorem itself is **not** in this file yet; see the section "What remains"
below for the one missing ingredient and the measurement that identifies it.

## Implementation notes

The sheaf-level input is
`StacksFrontier.Topology.Sheaves.Cohomology.MayerVietoris.RestrictionCoverShortExact`:
the Mayer--Vietoris short complex of endofunctors of `Mod(O)` is short exact at every
*injective* sheaf of modules.
Since `restrictPush` is only left exact, this is the exactness that is available, and it is
exactly the hypothesis the K-injective route consumes: a K-injective resolution chosen
functorially (Tag 079P) has injective terms, so applying the three functors to it degreewise
gives a short exact sequence of cochain complexes, hence a distinguished triangle in `D(O)`,
which is then transported to the chosen right derived functors.

Rather than fixing models for the derived functors, the statement quantifies over arbitrary
functors equipped with their `IsRightDerivedFunctor` data, and characterizes the maps of the
triangle by their composites with the supplied comparison maps.

Three elaboration points are worth recording because the obvious spellings
fail.

* `IsRightDerivedFunctor`'s localization functor `L` is implicit and recovered from the unit
  `α : F ⟶ L ⋙ RF`.  With `RF` the identity functor and `α = 𝟙 Qh` the constraint
  `L ⋙ 𝟭 =?= Qh` needs structure eta, so the instance argument `[L.IsLocalization W]` is
  searched while `L` is still a metavariable and the search fails.  Writing
  `(L := DerivedCategory.Qh)` out fixes it.
* `IsGrothendieckAbelian (SheafOfModules O)` must be in scope — not merely derivable — before
  the `DerivedCategory.Qh.IsLocalization` instance can be found at all: without the
  `GrothendieckAbelian` import the search does not fail fast but runs out of heartbeats inside
  `isDefEq`.
* `DerivedCategory.Q.obj K` and `DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)`
  are only *definitionally* equal, so composites that mix them are not type-correct at
  `instances` transparency and `rw`/`simp` cannot act on them.  Every such square below is
  therefore closed in term mode, by `calc` steps that are `Category.assoc`, `congrArg`, or a
  named naturality hypothesis.  This is the same technique, and for the same reason, as in
  the `j_!` companion of Stacks Tag 08BU, in
  `StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.MayerVietorisTriangle`.

The morphism property is written out as
`HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)` at every occurrence
rather than abbreviated, so that a single spelling reaches every instance.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open ExtensionByZeroModules

universe u

namespace Stacks.Cohomology.RestrictionCover

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-! ### The homotopy-category layer -/

/-- Applying restriction and pushforward degreewise, then passing to the derived category. -/
public abbrev homotopyToDerived (U : Opens X) :
    HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} O) :=
  (restrictPush O U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Applying the identity functor degreewise is canonically isomorphic to the identity on the
homotopy category. -/
public def homotopyIdentityIso :
    (CategoryTheory.Functor.id (SheafOfModules.{u} O)).mapHomotopyCategory
        (ComplexShape.up ℤ) ≅
      CategoryTheory.Functor.id
        (HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  CategoryTheory.Quotient.natIsoLift _
    (Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
      (HomotopyCategory.quotient (SheafOfModules.{u} O) (ComplexShape.up ℤ)))

/-- The canonical map from a complex to restriction followed by pushforward, after passage
to the homotopy and derived categories. -/
public def homotopyRestriction (U : Opens X) :
    DerivedCategory.Qh (C := SheafOfModules.{u} O) ⟶ homotopyToDerived O U :=
  Functor.whiskerRight (homotopyIdentityIso O).inv DerivedCategory.Qh ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (jStarAdjunction U O).unit (ComplexShape.up ℤ))
      DerivedCategory.Qh

/-- The transition map between two opens, on the homotopy category. -/
public def homotopyRestrictPushTransition (T U : Opens X) (hTU : T ≤ U) :
    homotopyToDerived O U ⟶ homotopyToDerived O T :=
  Functor.whiskerRight
    (NatTrans.mapHomotopyCategory (restrictPushTransition O T U hTU)
      (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- The restriction maps are compatible with the transition maps. -/
public lemma homotopyRestriction_transition (T U : Opens X) (hTU : T ≤ U) :
    homotopyRestriction O U ≫ homotopyRestrictPushTransition O T U hTU =
      homotopyRestriction O T := by
  dsimp [homotopyRestriction, homotopyRestrictPushTransition]
  rw [Category.assoc, ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp,
    restrictPushTransition_unit]

/-! ### The identity functor as a right derived functor -/

/-- The identity functor on `D(O)` is the right derived functor of `Qh` along the identity.
The localization functor `L` is written out: it is implicit in `IsRightDerivedFunctor` and
recovered from the unit, and `L ⋙ 𝟭 =?= Qh` leaves it a metavariable when the instance
argument `[L.IsLocalization _]` is searched. -/
public instance identityRightDerivedUnit :
    (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O))).IsRightDerivedFunctor
      (L := DerivedCategory.Qh)
      (𝟙 (DerivedCategory.Qh (C := SheafOfModules.{u} O)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ (Iso.refl _)

/-! ### Descending maps into a chosen right derived functor -/

/-- Descend a map from the localization functor into a chosen right-derived functor. -/
public def derivedRestrictionMap
    (F : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (R : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (a : F ⟶ DerivedCategory.Qh ⋙ R)
    (s : DerivedCategory.Qh (C := SheafOfModules.{u} O) ⟶ F) :
    (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O))) ⟶ R :=
  Functor.rightDerivedDesc
    (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)))
    (L := DerivedCategory.Qh)
    (𝟙 (DerivedCategory.Qh (C := SheafOfModules.{u} O)))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) R (s ≫ a)

/-- The comparison map just defined is characterized by its composite with the derived unit. -/
public lemma derivedRestrictionMap_fac
    (F : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (R : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (a : F ⟶ DerivedCategory.Qh ⋙ R)
    (s : DerivedCategory.Qh (C := SheafOfModules.{u} O) ⟶ F) :
    s ≫ a = Functor.whiskerLeft DerivedCategory.Qh
      (derivedRestrictionMap O F R a s) := by
  simpa [derivedRestrictionMap] using
    (Functor.rightDerived_fac
      (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)))
      (L := DerivedCategory.Qh)
      (𝟙 (DerivedCategory.Qh (C := SheafOfModules.{u} O)))
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
      R (s ≫ a)).symm

/-- The map of right derived functors induced by a map of the underlying functors. -/
public def derivedRestrictionTransition
    (F G : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (RF RG : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aF : F ⟶ DerivedCategory.Qh ⋙ RF)
    (aG : G ⟶ DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor aF
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor aG
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (q : F ⟶ G) : RF ⟶ RG :=
  RF.rightDerivedNatTrans RG aF aG
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) q

/-- The induced map is characterized by its composite with the two derived units. -/
public lemma derivedRestrictionTransition_fac
    (F G : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (RF RG : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aF : F ⟶ DerivedCategory.Qh ⋙ RF)
    (aG : G ⟶ DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor aF
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor aG
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (q : F ⟶ G) :
    q ≫ aG = aF ≫ Functor.whiskerLeft DerivedCategory.Qh
      (derivedRestrictionTransition O F G RF RG aF aG q) := by
  simp [derivedRestrictionTransition]

/-! ### K-injective resolutions -/

/-- Every cochain complex in a Grothendieck abelian category admits a quasi-isomorphism into a
K-injective complex (Tag 079P, forgetting functoriality). -/
public alias exists_quasiIso_kInjective := Stacks.Cohomology.moduleExistsKInjectiveResolution

/-- The unit of a right derived functor is invertible at a K-injective complex. -/
public lemma derivedUnit_isIso_of_isKInjective
    (F : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (R : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (a : F ⟶ DerivedCategory.Qh ⋙ R)
    [R.IsRightDerivedFunctor a
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    IsIso (a.app ((HomotopyCategory.quotient _ _).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    F (exists_quasiIso_kInjective (SheafOfModules.{u} O))).2
    DerivedCategory.Qh R a I inferInstance

/-! ### Comparison with the functorial K-injective resolution -/

/-- The composite of the quotient to the homotopy category with the localization `Qh`.  This is
`DerivedCategory.Q` up to the canonical isomorphism `DerivedCategory.quotientCompQhIso`, but it
is the spelling in which the derived unit of a functor on the homotopy category is stated. -/
public abbrev homotopyLocalization : CochainComplex (SheafOfModules.{u} O) ℤ ⥤
    DerivedCategory (SheafOfModules.{u} O) :=
  HomotopyCategory.quotient (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The derived unit of `F`, read on cochain complexes rather than on the homotopy category. -/
public def complexDerivedUnitHomotopy
    (F : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O) [F.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ homotopyLocalization O ⟶
      homotopyLocalization O ⋙ RF where
  app K := α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)
  naturality _ _ f := α.naturality ((HomotopyCategory.quotient _ _).map f)

/-- The derived unit of `F`, transported to the localization `DerivedCategory.Q`. -/
public def complexDerivedUnit
    (F : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O) [F.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RF :=
  Functor.whiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).inv ≫
    complexDerivedUnitHomotopy O F RF α ≫
    Functor.whiskerRight
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).hom RF

/-- The three factors of `complexDerivedUnit`, spelled out.  Stating this once is what lets the
compatibility lemmas below be proved in term mode: the composite mixes `DerivedCategory.Q.obj K`
with `DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)`, which are definitionally
but not syntactically equal. -/
public lemma complexDerivedUnit_app
    (F : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O) [F.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (complexDerivedUnit O F RF α).app K =
      (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).inv.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        α.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
          RF.map ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).hom.app K) :=
  rfl

/-- A natural transformation of additive functors, applied degreewise and then pushed to the
homotopy category, is the quotient of its degreewise application. -/
public lemma mapHomotopyCategory_app_quotient_obj
    {F G : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K) :=
  rfl

/-- A purely formal diagram chase, stated in an abstract category.  Two of the composites it
relates live in `DerivedCategory` and mix the two definitionally-equal spellings of the
localization of a complex, where `rw` and `simp` cannot act; stated abstractly there is no such
obstruction, and the single `exact` that applies it checks the identification at default
transparency. -/
public lemma comp_square_chase {D : Type*} [Category D]
    {P P' Q₁ Q₂ R₁ R₂ S T : D}
    (p : P ⟶ Q₁) (a : Q₁ ⟶ R₁) (f : R₁ ⟶ S) (g : S ⟶ T)
    (g' : R₁ ⟶ R₂) (f' : R₂ ⟶ T) (m : Q₁ ⟶ Q₂) (b : Q₂ ⟶ R₂)
    (n : P ⟶ P') (p' : P' ⟶ Q₂)
    (hn : f ≫ g = g' ≫ f') (hh : a ≫ g' = m ≫ b) (hi : n ≫ p' = p ≫ m) :
    (p ≫ a ≫ f) ≫ g = n ≫ p' ≫ b ≫ f' := by
  simp only [Category.assoc, hn, reassoc_of% hh, reassoc_of% hi]

/-- The derived units are compatible with a map of the underlying functors. -/
public lemma complexDerivedUnit_fac
    {F G : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O}
    [F.Additive] [G.Additive]
    {RF RG : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O)}
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    (τ : F ⟶ G) (r : RF ⟶ RG)
    (h : α ≫ Functor.whiskerLeft DerivedCategory.Qh r =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ β) :
    complexDerivedUnit O F RF α ≫ Functor.whiskerLeft DerivedCategory.Q r =
      Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ))
        DerivedCategory.Q ≫ complexDerivedUnit O G RG β := by
  refine NatTrans.ext (funext fun K => ?_)
  exact comp_square_chase _ _ _ _ _ _ _ _ _ _
    (r.naturality ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).hom.app K))
    (congr_app h ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).inv.naturality
      ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K))

/-- Cancelling two isomorphisms across a commuting square, stated abstractly for the same
reason as `comp_square_chase`. -/
public lemma inv_comp_comm {D : Type*} [Category D] {A B C E : D}
    (b : A ⟶ B) [IsIso b] (y : B ⟶ E) (x : A ⟶ C) (z : C ⟶ E) [IsIso z]
    (h : b ≫ y = x ≫ z) : inv b ≫ x = y ≫ inv z := by
  refine (IsIso.inv_comp_eq b).2 ?_
  rw [← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The second formal chase: transporting a square across one inverted leg. -/
public lemma comp_inv_chase {D : Type*} [Category D] {A A' B B' C C' : D}
    (a : A ⟶ B) (ib : B ⟶ C) (rC : C ⟶ C') (rB : B ⟶ B') (ib' : B' ⟶ C')
    (n : A ⟶ A') (a' : A' ⟶ B')
    (h1 : ib ≫ rC = rB ≫ ib') (h2 : a ≫ rB = n ≫ a') :
    (a ≫ ib) ≫ rC = n ≫ a' ≫ ib' := by
  rw [Category.assoc, h1, ← Category.assoc, h2, Category.assoc]

/-- The derived unit of `F` is invertible on a K-injective complex, read at the level of
cochain complexes. -/
public lemma complexDerivedUnit_app_isIso_of_isKInjective
    (F : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O) [F.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (I : CochainComplex (SheafOfModules.{u} O) ℤ) [I.IsKInjective] :
    IsIso ((complexDerivedUnit O F RF α).app I) := by
  have hα := derivedUnit_isIso_of_isKInjective O
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) RF α I
  rw [complexDerivedUnit_app]
  exact IsIso.comp_isIso'
    ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).symm.app _).isIso_hom
    (IsIso.comp_isIso' hα
      (RF.mapIso ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)).app I)).isIso_hom)

/-- A chosen right derived functor is computed by the functorial K-injective resolution:
applying `F` degreewise to the resolution and localizing agrees with `RF`. -/
public def resolutionDerivedIso
    (F : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O) [F.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RF := by
  have ha : ∀ K, IsIso ((Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O))
      (complexDerivedUnit O F RF α)).app K) := fun K =>
    complexDerivedUnit_app_isIso_of_isKInjective O F RF α _
  have hb : ∀ K, IsIso ((Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u} O))
      (DerivedCategory.Q ⋙ RF)).app K) := fun K =>
    RF.map_isIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u} O)).app K))
  have : IsIso (Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O))
      (complexDerivedUnit O F RF α)) := NatIso.isIso_of_isIso_app _
  have : IsIso (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u} O))
      (DerivedCategory.Q ⋙ RF)) := NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft
      (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O))
      (complexDerivedUnit O F RF α)) ≪≫
    (asIso (Functor.whiskerRight
      (Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u} O))
      (DerivedCategory.Q ⋙ RF))).symm

/-- The two legs of `resolutionDerivedIso`, spelled out. -/
public lemma resolutionDerivedIso_hom_app
    (F : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O) [F.Additive]
    (RF : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (resolutionDerivedIso O F RF α).hom.app K =
      (complexDerivedUnit O F RF α).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K) ≫
        inv (RF.map (DerivedCategory.Q.map
          ((Stacks.Injectives.kInjectiveResolutionInclusion
            (SheafOfModules.{u} O)).app K))) := by
  simp [resolutionDerivedIso, NatIso.isIso_inv_app]

/-- The comparison isomorphisms are compatible with a map of the underlying functors. -/
public lemma resolutionDerivedIso_fac
    {F G : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O}
    [F.Additive] [G.Additive]
    {RF RG : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O)}
    (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    (β : G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RG)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [RG.IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (τ : F ⟶ G) (r : RF ⟶ RG)
    (h : α ≫ Functor.whiskerLeft DerivedCategory.Qh r =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
        DerivedCategory.Qh ≫ β)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (resolutionDerivedIso O F RF α).hom.app K ≫ r.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫
        (resolutionDerivedIso O G RG β).hom.app K := by
  rw [resolutionDerivedIso_hom_app, resolutionDerivedIso_hom_app]
  exact comp_inv_chase _ _ _ _ _ _ _
    (inv_comp_comm _ _ _ _ (r.naturality (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion (SheafOfModules.{u} O)).app K))))
    (congr_app (complexDerivedUnit_fac O α β τ r h)
      ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K))

/-! ### The distinguished triangle of a sequence exact on injectives -/

/-- Given three additive endofunctors of `Mod(O)`, maps `f : F ⟶ G`, `g : G ⟶ H` composing to
zero whose short complex is short exact at every injective object, and chosen right derived
functors identified on K-injective resolutions by `eF`, `eG`, `eH`, there is a connecting map
making the triangle of the derived maps distinguished at every object. -/
public def derivedTriangleOfShortExactOnInjectives
    (F G H : SheafOfModules.{u} O ⥤ SheafOfModules.{u} O)
    [F.Additive] [G.Additive] [H.Additive]
    (f : F ⟶ G) (g : G ⟶ H) (hfg : f ≫ g = 0)
    (hS : ∀ (I : SheafOfModules.{u} O) [Injective I],
      (ShortComplex.mk (f.app I) (g.app I) (NatTrans.congr_app hfg I)).ShortExact)
    (RF RG RH : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (eF : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RF)
    (eG : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RG)
    (eH : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RH)
    (rf : RF ⟶ RG) (rg : RG ⟶ RH)
    (hf : ∀ K, eF.hom.app K ≫ rf.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫
          eG.hom.app K)
    (hg : ∀ K, eG.hom.app K ≫ rg.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app
        ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K)) ≫
          eH.hom.app K) :
    {δ : RH ⟶ RF ⋙ shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ) //
      ∀ K, Triangle.mk (rf.app K) (rg.app K) (δ.app K) ∈
        distTriang (DerivedCategory (SheafOfModules.{u} O))} := by
  have hz (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
      (NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app K ≫
        (NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app K = 0 := by
    ext n : 1
    exact NatTrans.congr_app hfg (K.X n)
  have hs (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
      (ShortComplex.mk
        ((NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K))
        ((NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).app
          ((Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O)).obj K))
        (hz _)).ShortExact := by
    rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
    exact fun _ => hS _
  let d : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      H.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
        F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ) :=
    { app := fun K => DerivedCategory.triangleOfSESδ (hs K)
      naturality := fun K L k =>
        (DerivedCategory.triangleOfSESδ_naturality (hs K) (hs L)
          { τ₁ := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor
                (SheafOfModules.{u} O)).map k)
            τ₂ := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor
                (SheafOfModules.{u} O)).map k)
            τ₃ := (H.mapHomologicalComplex (ComplexShape.up ℤ)).map
              ((Stacks.Injectives.kInjectiveResolutionFunctor
                (SheafOfModules.{u} O)).map k)
            comm₁₂ := (NatTrans.mapHomologicalComplex f (ComplexShape.up ℤ)).naturality
              ((Stacks.Injectives.kInjectiveResolutionFunctor
                (SheafOfModules.{u} O)).map k)
            comm₂₃ := (NatTrans.mapHomologicalComplex g (ComplexShape.up ℤ)).naturality
              ((Stacks.Injectives.kInjectiveResolutionFunctor
                (SheafOfModules.{u} O)).map k) }).symm }
  let b : DerivedCategory.Q ⋙ RH ⟶
      DerivedCategory.Q ⋙ (RF ⋙
        shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)) :=
    eH.inv ≫ d ≫ Functor.whiskerRight eF.hom
      (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ))
  let E := (Functor.whiskeringLeft (CochainComplex (SheafOfModules.{u} O) ℤ)
    (DerivedCategory (SheafOfModules.{u} O))
    (DerivedCategory (SheafOfModules.{u} O))).obj DerivedCategory.Q
  have : E.Full := Localization.full_whiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) _
  let δ : RH ⟶ RF ⋙ shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ) :=
    E.preimage b
  have hd (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
      δ.app (DerivedCategory.Q.obj K) = b.app K :=
    NatTrans.congr_app (E.map_preimage b) K
  have hdist (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
      Triangle.mk (rf.app (DerivedCategory.Q.obj K)) (rg.app (DerivedCategory.Q.obj K))
        (δ.app (DerivedCategory.Q.obj K)) ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O)) := by
    apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished (hs K)) _
    apply Iso.symm
    refine Triangle.isoMk _ _ (eF.app K) (eG.app K) (eH.app K) ?_ ?_ ?_
    · exact (hf K).symm
    · exact (hg K).symm
    · dsimp [DerivedCategory.triangleOfSES]
      rw [hd]
      dsimp [b, d]
      simp only [Iso.hom_inv_id_app_assoc]
  refine ⟨δ, fun K => ?_⟩
  exact isomorphic_distinguished _ (hdist (DerivedCategory.Q.objPreimage K)) _
    (Triangle.isoMk _ _ (RF.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (RG.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (RH.mapIso (DerivedCategory.Q.objObjPreimageIso K))
      (rf.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm
      (rg.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm
      (δ.naturality (DerivedCategory.Q.objObjPreimageIso K).hom).symm).symm

/-! ### The middle term as a biproduct -/

/-- First projection out of the middle term. -/
public def restrictionCoverFst (U V : Opens X) :
    restrictionCoverMiddle O U V ⟶ restrictPush O U where
  app _ := biprod.fst
  naturality _ _ _ := by simp [restrictionCoverMiddle]

/-- Second projection out of the middle term. -/
public def restrictionCoverSnd (U V : Opens X) :
    restrictionCoverMiddle O U V ⟶ restrictPush O V where
  app _ := biprod.snd
  naturality _ _ _ := by simp [restrictionCoverMiddle]

/-- First inclusion into the middle term. -/
public def restrictionCoverInl (U V : Opens X) :
    restrictPush O U ⟶ restrictionCoverMiddle O U V where
  app _ := biprod.inl
  naturality _ _ _ := by simp [restrictionCoverMiddle]

/-- Second inclusion into the middle term. -/
public def restrictionCoverInr (U V : Opens X) :
    restrictPush O V ⟶ restrictionCoverMiddle O U V where
  app _ := biprod.inr
  naturality _ _ _ := by simp [restrictionCoverMiddle]

/-- Applying the middle term degreewise to a cochain complex gives a binary bicone on the two
degreewise restriction-pushforwards. -/
public def restrictionCoverBicone (U V : Opens X)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    BinaryBicone (((restrictPush O U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      (((restrictPush O V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) where
  pt := ((restrictionCoverMiddle O U V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  fst := (NatTrans.mapHomologicalComplex (restrictionCoverFst O U V)
    (ComplexShape.up ℤ)).app K
  snd := (NatTrans.mapHomologicalComplex (restrictionCoverSnd O U V)
    (ComplexShape.up ℤ)).app K
  inl := (NatTrans.mapHomologicalComplex (restrictionCoverInl O U V)
    (ComplexShape.up ℤ)).app K
  inr := (NatTrans.mapHomologicalComplex (restrictionCoverInr O U V)
    (ComplexShape.up ℤ)).app K
  inl_fst := by ext n : 1; exact biprod.inl_fst
  inl_snd := by ext n : 1; exact biprod.inl_snd
  inr_fst := by ext n : 1; exact biprod.inr_fst
  inr_snd := by ext n : 1; exact biprod.inr_snd

/-- That bicone is a biproduct. -/
public def restrictionCoverBiconeIsBilimit (U V : Opens X)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (restrictionCoverBicone O U V K).IsBilimit := by
  apply isBinaryBilimitOfTotal
  ext n : 1
  exact biprod.total (X := (restrictPush O U).obj (K.X n))
    (Y := (restrictPush O V).obj (K.X n))

/-- The pointwise biproduct of two endofunctors of the derived category. -/
public def derivedCoverMiddle
    (RU RV : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O)) :
    DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O) where
  obj E := RU.obj E ⊞ RV.obj E
  map f := biprod.map (RU.map f) (RV.map f)
  map_id _ := by apply biprod.hom_ext <;> simp
  map_comp _ _ := by apply biprod.hom_ext <;> simp [Functor.map_comp]

/-- The action of `derivedCoverMiddle` on morphisms, in the spelling its own definition uses. -/
public lemma derivedCoverMiddle_map
    (RU RV : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    {E E' : DerivedCategory (SheafOfModules.{u} O)} (f : E ⟶ E') :
    (derivedCoverMiddle O RU RV).map f =
      biprod.map (RU.map f) (RV.map f) := rfl

/-- The third formal chase: a square of the form `Φ(m) ≫ Φ(p) ≫ e` where the square lives in
the source category and the naturality in the target.  Hoisted out because the concrete
instance mixes `CochainComplex C ℤ` with `HomologicalComplex C (ComplexShape.up ℤ)`, and the
`change` that pins the spelling in place is what a heartbeat budget would otherwise pay for. -/
public lemma functor_map_square_chase {D E : Type*} [Category D] [Category E]
    (Φ : D ⥤ E) {A B A' B' : D} {W W' : E}
    (m : A ⟶ B) (pL : B ⟶ B') (pK : A ⟶ A') (n : A' ⟶ B')
    (eL : Φ.obj B' ⟶ W') (eK : Φ.obj A' ⟶ W) (w : W ⟶ W')
    (hsq : m ≫ pL = pK ≫ n) (hnat : Φ.map n ≫ eL = eK ≫ w) :
    Φ.map m ≫ Φ.map pL ≫ eL = Φ.map pK ≫ eK ≫ w := by
  rw [← Category.assoc, ← Φ.map_comp, hsq, Φ.map_comp, Category.assoc, hnat]

/-- `biprod.lift` followed by `biprod.map`.  Stated abstractly: in the concrete goals the
`HasBinaryBiproduct` instance inside `biprod.lift` and the one `biprod.hom_ext` synthesizes are
different terms, so `biprod.lift_fst` does not fire there at all.  Keeping every biproduct step
inside lemmas like this one means the instances are synthesized once, uniformly. -/
public lemma biprod_lift_comp_map {D : Type*} [Category D] [HasZeroMorphisms D]
    {A B₁ B₂ C₁ C₂ : D} [HasBinaryBiproduct B₁ B₂] [HasBinaryBiproduct C₁ C₂]
    (f : A ⟶ B₁) (g : A ⟶ B₂) (h : B₁ ⟶ C₁) (i : B₂ ⟶ C₂) :
    biprod.lift f g ≫ biprod.map h i = biprod.lift (f ≫ h) (g ≫ i) := by
  apply biprod.hom_ext <;> simp

/-- Pre-composition into a `biprod.lift`. -/
public lemma comp_biprod_lift {D : Type*} [Category D] [HasZeroMorphisms D]
    {A A' B₁ B₂ : D} [HasBinaryBiproduct B₁ B₂]
    (x : A' ⟶ A) (f : A ⟶ B₁) (g : A ⟶ B₂) :
    x ≫ biprod.lift f g = biprod.lift (x ≫ f) (x ≫ g) := by
  apply biprod.hom_ext <;> simp

/-- Congruence for `biprod.lift`, so that a goal between two lifts splits without introducing a
second `biprod.fst` whose instance may differ. -/
public lemma biprod_lift_congr {D : Type*} [Category D] [HasZeroMorphisms D]
    {A B₁ B₂ : D} [HasBinaryBiproduct B₁ B₂] {f f' : A ⟶ B₁} {g g' : A ⟶ B₂}
    (hf : f = f') (hg : g = g') : biprod.lift f g = biprod.lift f' g' := by
  rw [hf, hg]

/-- `DerivedCategory.Q` preserves binary biproducts.  Seated here as an instance rather than
supplied by a `letI` inside the definition below: a `letI`-bound instance in a definition body
leaves a `let` in the term, which stops `simp` from unfolding that definition at all, so the
projection lemmas for the resulting isomorphism never fire. -/
public instance derivedQPreservesBinaryBiproducts :
    PreservesBinaryBiproducts (DerivedCategory.Q (C := SheafOfModules.{u} O)) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts _

/-- The comparison isomorphism for the middle term, at one complex. -/
public def coverMiddleComponentIso (U V : Opens X)
    (RU RV : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (eU : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      (restrictPush O U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RU)
    (eV : Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      (restrictPush O V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ RV)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (Stacks.Injectives.kInjectiveResolutionFunctor (SheafOfModules.{u} O) ⋙
      (restrictionCoverMiddle O U V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).obj K ≅
      (DerivedCategory.Q ⋙ derivedCoverMiddle O RU RV).obj K :=
  biprod.uniqueUpToIso _ _
      (isBinaryBilimitOfPreserves DerivedCategory.Q
        (restrictionCoverBiconeIsBilimit O U V
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u} O)).obj K))) ≪≫
    biprod.mapIso (eU.app K) (eV.app K)

/-! ### What remains

`resolutionCoverMiddleIso`, the comparison isomorphism
`R ⋙ (restrictionCoverMiddle O U V).mapHomologicalComplex ⋙ Q ≅ Q ⋙ derivedCoverMiddle O RU RV`,
is not built here, and neither is the Mayer--Vietoris theorem that consumes it.  The component
isomorphism `coverMiddleComponentIso` above exists; what is missing is its naturality in the
complex.  The obstruction: the `HasBinaryBiproduct` instance that `biprod.hom_ext`
synthesizes for the target `(derivedCoverMiddle O RU RV).obj (Q.obj L)` is a different term from
the one carried by the `biprod.lift` in `coverMiddleComponentIso`, so in those goals
`biprod.lift_fst` does not fire at all, `rw [Iso.trans_hom]` reports that `(?α ≪≫ ?β).hom` does
not occur in a target that displays exactly that, and the defeq between the two spellings of the
comparison runs past 200000 heartbeats inside `isDefEq`.  The abstract lemmas
`biprod_lift_comp_map`, `comp_biprod_lift` and `biprod_lift_congr` above are uniform in their
instances and are the intended ingredients; what is still needed is a functor-level
identification of `Q ⋙ derivedCoverMiddle O RU RV` as the biproduct of `Q ⋙ RU` and `Q ⋙ RV`,
from which naturality follows without any pointwise `biprod` matching.
-/

/-- The first map of the Mayer--Vietoris complex, followed by the first projection. -/
public lemma restrictionCoverFirst_fst (U V : Opens X) :
    restrictionCoverFirst O U V ≫ restrictionCoverFst O U V =
      (jStarAdjunction U O).unit :=
  NatTrans.ext (funext fun _ => biprod.lift_fst _ _)

/-- The first map of the Mayer--Vietoris complex, followed by the second projection. -/
public lemma restrictionCoverFirst_snd (U V : Opens X) :
    restrictionCoverFirst O U V ≫ restrictionCoverSnd O U V =
      (jStarAdjunction V O).unit :=
  NatTrans.ext (funext fun _ => biprod.lift_snd _ _)

end Stacks.Cohomology.RestrictionCover
