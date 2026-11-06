module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftCartesian
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.UniverseLiftSite

/-!
# The Comparison Lemma for sheaves of modules above the universe of the rings

Let `v : C ⥤ X.C` exhibit `(C, J)` as a dense subsite of the site of a ringed site `X` whose
structure rings lie in a universe `r`. The Comparison Lemma for sheaves of modules
(`Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`) is stated for modules whose sections
lie in the universe of the structure rings. This file extends it to modules with sections in any
universe `max r z`: raising the universe of the structure rings to `max r z`, on `X` and on the
subsite, changes the categories of modules only through restriction of scalars along
`ULift.ringEquiv`, and at the raised universe the Comparison Lemma applies.

## Main definitions

* `AlgebraicGeometry.RingedSite.uliftRing`: a ringed site with its structure rings raised to a
  larger universe, on the same site.
* `Stacks.UniverseLift.uliftRingTransport`: the ring transport over the identity of the site
  from a presheaf of commutative rings to its universe lift.
* `Stacks.UniverseLift.moduleRestrictionEquivalenceULift`: restriction of sheaves of modules to a
  dense subsite, as an equivalence, at a module universe above that of the structure rings.

## Main results

* `Stacks.UniverseLift.RingTransport.isUniversalArrow_functor_obj_map_iff_of_refl`: over the
  identity of the site, a restriction map of the transport is a base change exactly when the
  corresponding restriction map of the presheaf is.
* `Stacks.UniverseLift.isCartesianPresheaf_moduleRestrictionEquivalenceULift_iff`: the image of a
  sheaf of modules under that equivalence is cartesian exactly when its restriction maps along
  the arrows of the subsite are base changes.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.ModulesOnACategory.ChaoticComparison (IsCartesianPresheaf)

universe m z u v r u₁ v₁ r₁ r₂

namespace AlgebraicGeometry.RingedSite

/-- **A ringed site with its structure rings raised to the universe `max r z`**: the same site,
with structure sheaf `U ↦ ULift (O_X(U))`. -/
noncomputable abbrev uliftRing (X : RingedSite.{u, v, r}) : RingedSite.{u, v, max r z} where
  C := X.C
  J := X.J
  O := ⟨X.O.obj ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{r, z},
    Stacks.UniverseLift.isSheaf_comp_commRingCatULift _ X.O.property⟩

end AlgebraicGeometry.RingedSite

namespace Stacks.UniverseLift

variable {C : Type u} [Category.{v} C]

/-- The ring transport over the identity of `C` from a presheaf of commutative rings `P` to its
universe lift `U ↦ ULift (P(U))`: the ring isomorphisms are `ULift.ringEquiv`. -/
noncomputable def uliftRingTransport (P : Cᵒᵖ ⥤ CommRingCat.{r}) :
    RingTransport (CategoryTheory.Equivalence.refl : C ≌ C) (P ⋙ forget₂ CommRingCat RingCat)
      ((P ⋙ AlgebraicGeometry.SheafOfModules.commRingCatULift.{r, z}) ⋙
        forget₂ CommRingCat RingCat) where
  iso _ := ULift.ringEquiv
  naturality _ _ := rfl

namespace RingTransport

/-- **Along a ring transport over the identity, each restriction map of a transport is a base
change exactly when the corresponding restriction map of the presheaf is.** Over
`Equivalence.refl` the transport changes no section and no restriction map, only the rings
through which the sections are read. -/
theorem isUniversalArrow_functor_obj_map_iff_of_refl
    {R₁ : Cᵒᵖ ⥤ RingCat.{r₁}} {R₂ : Cᵒᵖ ⥤ RingCat.{r₂}}
    (T : RingTransport (CategoryTheory.Equivalence.refl : C ≌ C) R₁ R₂)
    (M : PresheafOfModules.{m} R₁)
    {U V : Cᵒᵖ} (a : V ⟶ U) :
    (ModuleCat.restrictScalars.{m} (R₂.map a).hom).IsUniversalArrow
        ((T.functor.obj M).map a) ↔
      (ModuleCat.restrictScalars.{m} (R₁.map a).hom).IsUniversalArrow (M.map a) := by
  refine ⟨fun h => ?_, T.isUniversalArrow_functor_obj_map M a⟩
  have h' := T.symm.isUniversalArrow_functor_obj_map (T.functor.obj M) a h
  let i := (T.unitIso.app M).symm
  exact h'.of_iso ((PresheafOfModules.evaluation R₁ V).mapIso i)
    ((PresheafOfModules.evaluation R₁ U).mapIso i) (i.hom.naturality a)

end RingTransport

section Comparison

open Stacks.DenseSubsiteModules _root_.AlgebraicGeometry.RingedSite

variable (X : _root_.AlgebraicGeometry.RingedSite.{u, v, r}) {C₀ : Type u₁} [Category.{v₁} C₀]
  (J₀ : GrothendieckTopology C₀) (ι : C₀ ⥤ X.C) [ι.IsDenseSubsite J₀ X.J]
  [(ι.sheafPushforwardContinuous AddCommGrpCat.{max r z} J₀ X.J).IsEquivalence]

/-- **The Comparison Lemma for sheaves of modules with sections above the universe of the
structure rings.** If `ι : C₀ ⥤ X.C` exhibits `(C₀, J₀)` as a dense subsite of the site of `X`
and the Comparison Lemma holds for sheaves of abelian groups with sections in `max r z`, then
sheaves of `O_X`-modules with sections in `max r z` are equivalent to sheaves of modules over the
restriction of `O_X` to the subsite.

It is the Comparison Lemma `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` at the
structure rings raised to `max r z`, conjugated by the ring transports
`Stacks.UniverseLift.uliftRingTransport` on `X` and on the subsite, so on sections and on
restriction maps it is restriction along `ι`. -/
noncomputable def moduleRestrictionEquivalenceULift :
    SheafOfModules.{max r z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
      SheafOfModules.{max r z}
        (ringRestriction J₀ X.J ι (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ((uliftRingTransport.{z} X.O.obj).sheafEquivalence
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (R' := (Stacks.SheafOfModules.Tensor.ringSheaf (uliftRing.{z} X).O))).trans
    ((moduleRestrictionEquivalence.{max r z} J₀ X.J ι
        (Stacks.SheafOfModules.Tensor.ringSheaf (uliftRing.{z} X).O)).trans
      ((uliftRingTransport.{z} (ι.op ⋙ X.O.obj)).sheafEquivalence
        (R := ringRestriction J₀ X.J ι (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (R' := ringRestriction J₀ X.J ι
          (Stacks.SheafOfModules.Tensor.ringSheaf (uliftRing.{z} X).O))).symm)

/-- The functor of `Stacks.UniverseLift.moduleRestrictionEquivalenceULift` is additive. -/
instance moduleRestrictionEquivalenceULift_functor_additive :
    (moduleRestrictionEquivalenceULift.{z} X J₀ ι).functor.Additive where
  map_add := rfl

/-- **The image of a sheaf of modules under the Comparison Lemma is cartesian exactly when the
restriction maps of the sheaf along the arrows of the subsite are base changes.** -/
theorem isCartesianPresheaf_moduleRestrictionEquivalenceULift_iff
    (G : SheafOfModules.{max r z} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsCartesianPresheaf ((moduleRestrictionEquivalenceULift.{z} X J₀ ι).functor.obj G).val ↔
      ∀ ⦃U V : C₀ᵒᵖ⦄ (a : V ⟶ U),
        (ModuleCat.restrictScalars.{max r z}
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map (ι.op.map a)).hom).IsUniversalArrow
            (G.val.map (ι.op.map a)) := by
  refine ((uliftRingTransport.{z} (ι.op ⋙ X.O.obj)).symm.isCartesianPresheaf_functor_obj_iff
    _).trans ?_
  refine forall_congr' fun U => forall_congr' fun V => forall_congr' fun a => ?_
  exact (uliftRingTransport.{z} X.O.obj).isUniversalArrow_functor_obj_map_iff_of_refl G.val
    (ι.op.map a)

end Comparison

end Stacks.UniverseLift

end
