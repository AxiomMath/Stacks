module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDevissage
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# The comparison functor of Stacks 06VT on an arbitrary affine scheme

`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence` states that the comparison
functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of [Stacks, Tag 06VT] is an equivalence for
`X = Spec R`. The dévissage of [Stacks, Tag 09T6] needs it for an arbitrary *affine* scheme,
which is isomorphic to a spectrum but not equal to one, so the statement has to be transported
along an isomorphism of schemes.

The transport is formal. An isomorphism `e : X ≅ Y` induces an equivalence
`Mod(𝒪_X) ≌ Mod(𝒪_Y)` by restriction along `e.inv` and `e.hom`; this carries quasi-coherent
modules to quasi-coherent modules in both directions, hence restricts to an equivalence
`QCoh(𝒪_X) ≌ QCoh(𝒪_Y)`, and it induces an equivalence of the unbounded derived categories which
again restricts to `D_QCoh(𝒪_X) ≌ D_QCoh(𝒪_Y)`. The two comparison functors sit in a commuting
square with these equivalences, so one is an equivalence exactly when the other is.

## Main definitions

* `Stacks.DerivedQCoh.liftObjectPropertyEquivalence` — an equivalence of categories preserving a
  pair of object properties restricts to their full subcategories.
* `Stacks.DerivedQCoh.modulesRestrictAlong` — restriction of modules along a morphism of schemes
  in the `AlgebraicGeometry.SheafOfModules` spelling.
* `Stacks.DerivedQCoh.modulesRestrictionEquivalence` — the equivalence of module categories
  attached to an isomorphism of schemes.

## Main results

* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_schemeIso` — the comparison
  functor of [Stacks, Tag 06VT] is an equivalence at `X` as soon as it is at an isomorphic
  scheme.
* `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_isAffine` — **the
  comparison functor of [Stacks, Tag 06VT] is an equivalence on every affine scheme.**

## Implementation notes

The derived categories are the locally small ones; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/SupportedDevissage.lean`. This is forced here, the
affine input `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence` being available at
that model only.

Everything is spelled over `AlgebraicGeometry.SheafOfModules X.ringCatSheaf` rather than
`AlgebraicGeometry.Scheme.Modules X`, which is why `Stacks.DerivedQCoh.modulesRestrictAlong`
exists: the two spellings of the category of `𝒪_X`-modules are definitionally equal but carry
separately declared `Category` and `Preadditive` instances, so an exactness instance proved for
one is not *found* for the other, and the comparison functor of [Stacks, Tag 06VT] is stated in
the first. This is the device of `Stacks.DerivedQCoh.modulesPushforward`.

## References

* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.AlgebraicGeometry.QuasicoherentDerived

universe v u

namespace Stacks.DerivedQCoh

attribute [local instance] preservesFiniteLimits_restrictFunctor

/-! ### Restricting an equivalence to full subcategories -/

/-- **An equivalence preserving a pair of object properties restricts to their full
subcategories.** If `e : A ≌ B` carries the objects with `P` into those with `Q` and `e.inverse`
carries `Q` into `P`, the two restrictions form an equivalence
`P.FullSubcategory ≌ Q.FullSubcategory`, with unit and counit those of `e`. -/
def liftObjectPropertyEquivalence {A : Type u} [Category.{v} A] {B : Type u} [Category.{v} B]
    (e : A ≌ B) (P : ObjectProperty A) (Q : ObjectProperty B)
    (hF : ∀ X, P X → Q (e.functor.obj X)) (hG : ∀ Y, Q Y → P (e.inverse.obj Y)) :
    P.FullSubcategory ≌ Q.FullSubcategory :=
  CategoryTheory.Equivalence.mk (Q.lift (P.ι ⋙ e.functor) fun X => hF X.obj X.property)
    (P.lift (Q.ι ⋙ e.inverse) fun Y => hG Y.obj Y.property)
    (Functor.fullyFaithfulCancelRight P.ι (Functor.isoWhiskerLeft P.ι e.unitIso))
    (Functor.fullyFaithfulCancelRight Q.ι (Functor.isoWhiskerLeft Q.ι e.counitIso))

/-! ### Restriction of modules along a morphism of schemes -/

/-- Restriction of modules along a morphism of schemes, with domain and codomain spelled
`SheafOfModules.{u} X.ringCatSheaf` rather than `AlgebraicGeometry.Scheme.Modules X`; see the
implementation notes of this file. -/
def modulesRestrictAlong {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} X.ringCatSheaf :=
  Scheme.Modules.restrictFunctor f

/-- `Stacks.DerivedQCoh.modulesRestrictAlong` is additive. -/
instance modulesRestrictAlong_additive {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (modulesRestrictAlong f).Additive :=
  inferInstanceAs ((Scheme.Modules.restrictFunctor f).Additive)

/-- `Stacks.DerivedQCoh.modulesRestrictAlong` is left exact along an open immersion. -/
instance modulesRestrictAlong_preservesFiniteLimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteLimits (modulesRestrictAlong f) :=
  preservesFiniteLimits_restrictFunctor f

/-- `Stacks.DerivedQCoh.modulesRestrictAlong` is right exact along an open immersion. -/
instance modulesRestrictAlong_preservesFiniteColimits {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] : PreservesFiniteColimits (modulesRestrictAlong f) :=
  inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor f))

/-- **Restriction along an isomorphism of schemes is an equivalence of module categories.**
Restriction along `e.inv` and along `e.hom` are mutually inverse, the comparisons being the
compatibilities of restriction with composition and with the identity. -/
def modulesRestrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    SheafOfModules.{u} X.ringCatSheaf ≌ SheafOfModules.{u} Y.ringCatSheaf :=
  CategoryTheory.Equivalence.mk (modulesRestrictAlong e.inv) (modulesRestrictAlong e.hom)
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.hom e.inv)
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫ Scheme.Modules.restrictFunctorId)

/-! ### Transport of the comparison equivalence -/

/-- An exact functor carries objects of `D_P` into `D_Q` if it carries `P` into `Q`. -/
private theorem derivedCategoryB_obj_mapDerivedCategory
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : ObjectProperty C) (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms]
    (h : ∀ X, P X → Q (F.obj X)) (K : DerivedCategory C)
    (hK : DerivedCategoryB.derivedCategoryB P K) :
    DerivedCategoryB.derivedCategoryB Q (F.mapDerivedCategory.obj K) := fun n =>
  Q.prop_of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F n).app K).symm
    (h _ (hK n))

/-- **The comparison functor of [Stacks, Tag 06VT] is an equivalence at `X` as soon as it is at
an isomorphic scheme.** An isomorphism `e : X ≅ Y` induces equivalences
`QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` and `D_QCoh(𝒪_X) ≌ D_QCoh(𝒪_Y)` compatible with the two comparison
functors; a functor whose composite with an equivalence is an equivalence is one. -/
theorem derivedQuasicoherentComparison_isEquivalence_of_schemeIso {X Y : Scheme.{u}} (e : X ≅ Y)
    [(derivedQuasicoherentComparison.{u} Y).IsEquivalence] :
    (derivedQuasicoherentComparison.{u} X).IsEquivalence := by
  let E := modulesRestrictionEquivalence e
  have hEf : E.functor.Additive := modulesRestrictAlong_additive e.inv
  have hEi : E.inverse.Additive := modulesRestrictAlong_additive e.hom
  have hEfl : PreservesFiniteLimits E.functor :=
    modulesRestrictAlong_preservesFiniteLimits e.inv
  have hEfc : PreservesFiniteColimits E.functor :=
    modulesRestrictAlong_preservesFiniteColimits e.inv
  have hEil : PreservesFiniteLimits E.inverse :=
    modulesRestrictAlong_preservesFiniteLimits e.hom
  have hEic : PreservesFiniteColimits E.inverse :=
    modulesRestrictAlong_preservesFiniteColimits e.hom
  have hq : ∀ {A B : Scheme.{u}} (f : A ⟶ B) [IsOpenImmersion f]
      (M : SheafOfModules.{u} B.ringCatSheaf), SheafOfModules.isQuasicoherent B.ringCatSheaf M →
      SheafOfModules.isQuasicoherent A.ringCatSheaf ((modulesRestrictAlong f).obj M) :=
    fun f _ M hM => by
      have : M.IsQuasicoherent := hM
      exact Scheme.Modules.isQuasicoherent_restrictFunctor f M
  have hF := hq e.inv
  have hG := hq e.hom
  let Eq := liftObjectPropertyEquivalence E (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf) hF hG
  have hEqf : Eq.functor.Additive := Functor.additive_of_preserves_binary_products _
  let ED := Stacks.DerivedQCoh.Equivalence.mapDerivedCategory E
  have hDF := derivedCategoryB_obj_mapDerivedCategory E.functor _ _ hF
  have hDG := derivedCategoryB_obj_mapDerivedCategory E.inverse _ _ hG
  let EDq := liftObjectPropertyEquivalence ED
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent X.ringCatSheaf))
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)) hDF hDG
  let e0 : Eq.functor ⋙ (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι ≅
      (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ⋙ E.functor := Iso.refl _
  let e1 : Eq.functor.mapDerivedCategory ⋙ derivedQuasicoherentComparison.{u} Y ≅
      derivedQuasicoherentComparison.{u} X ⋙ EDq.functor :=
    Functor.fullyFaithfulCancelRight
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι
      (Functor.isoWhiskerLeft Eq.functor.mapDerivedCategory
          (derivedQuasicoherentComparisonCompι.{u} Y) ≪≫
        (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso Eq.functor
          (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι).symm ≪≫
        Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso _ _ e0 ≪≫
        Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
          (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι E.functor ≪≫
        Functor.isoWhiskerRight (derivedQuasicoherentComparisonCompι.{u} X).symm
          E.functor.mapDerivedCategory)
  have : Eq.functor.mapDerivedCategory.IsEquivalence :=
    (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory Eq).isEquivalence_functor
  have : (derivedQuasicoherentComparison.{u} X ⋙ EDq.functor).IsEquivalence :=
    Functor.isEquivalence_of_iso e1
  exact Functor.isEquivalence_of_comp_right (derivedQuasicoherentComparison.{u} X) EDq.functor

/-- **The comparison functor of [Stacks, Tag 06VT] is an equivalence on every affine scheme.**
An affine scheme is isomorphic to `Spec Γ(X, ⊤)` by `AlgebraicGeometry.Scheme.isoSpec`, where the
assertion is `Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence`, and
`Stacks.DerivedQCoh.derivedQuasicoherentComparison_isEquivalence_of_schemeIso` transports it.

This is the base case of the dévissage of [Stacks, Tag 09T6], where the affine open `U ⊆ X` is
not literally a spectrum. -/
theorem derivedQuasicoherentComparison_isEquivalence_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    (derivedQuasicoherentComparison.{u} X).IsEquivalence :=
  have := derivedQuasicoherentComparison_isEquivalence (Γ(X, ⊤))
  derivedQuasicoherentComparison_isEquivalence_of_schemeIso X.isoSpec

end Stacks.DerivedQCoh

end
