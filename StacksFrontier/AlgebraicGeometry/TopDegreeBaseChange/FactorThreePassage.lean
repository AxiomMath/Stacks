module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayCompositeOpenSubschemeJoin
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Factor (3)'s passage: the join read in degree `d`, through the `ψ` side's left inverse

`LerayCompositeOpenSubschemeJoin.lean` joins the two bricks of factor (3) of the 2b(B) match of
[Stacks, Tag 0EX3] (c) at the level of **transformations**, leaving the open-subscheme Leray
comparison of [Stacks, Tag 0D5W] on one side and
`Stacks.EdgeCompat.preimageSectionsModelComparison` on the other. The `ψ` side reads that Leray
comparison only through the **left inverse** of its degree-`d` cohomology that
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` hands in as a
hypothesis, and it hands it in at `Hᵈ` of the **bare** component. In the join the same comparison
sits under **two** restriction-of-scalars layers — `ModuleCat.restrictScalars` along
`AlgebraicGeometry.Scheme.Opens.topIso` at `p⁻¹V`, and
`Stacks.EdgeCompat.preimageRestrictScalars p V`. This file performs that passage.

## Main results

* `…TopDegreeBaseChange.homologyFunctor_map_derivedPreimageSectionsCompModel_comp_eq`: the
  degree-`d` cohomology of the join's right-hand side — the relative Leray comparison inverted,
  `preimageSectionsModelComparison p V` whiskered, and `…openSubschemeLerayComparisonLE` under the
  scalars — followed by the left inverse conjugated through the two layers, is the degree-`d`
  cohomology of the join's left-hand prefix: the comparison of the two models of `RΓ((p ∘ i)⁻¹V,
  -)` and `…openSubschemeSectionsComparisonLE` under the scalars.

  **Nothing is assumed** of `i`, of `p`, of `V`, of `U`, of the object or of the degree — no
  affineness, no acyclicity, no boundedness and no quasi-coherence. The one hypothesis is the left
  inverse itself, in the shape the `ψ` side supplies it.

## Implementation notes

*The conjugation is one lemma applied twice.* `StacksDraft.DerivedCategoryHomology`
`.map_homologyFunctor_map` moves `Hᵈ` past a restriction of scalars read on derived categories;
`mapDerivedCategoryHomologyIso` is built by `CategoryTheory.Localization.liftNatIso` and has no
component formula, so its naturality is all that is used, and the statement therefore carries
**four** of its components. The private `comp_conj_id_of_map` packages "a morphism conjugated by
an iso pair has the conjugated inverse as a right inverse" at variables of abstract categories,
and the two layers are two applications of it: the inner at the `topIso` scalars, whose output is
the `hv` of the outer at `preimageRestrictScalars`.

*The only inverse taken is the Leray one*, unconditional by
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`. It is handed in as a **left**
inverse of a plain morphism, the form
`…AffineComparison.cohomologyIsoPushforward_inv_eq_lerayComparison` uses; that it is also a right
inverse is derived inside the proof from that unconditional invertibility and costs no hypothesis.
Neither model comparison, neither `rightDerivedDesc` and neither open-subscheme crossing is
inverted.

*One duplicate recorded, nothing retired, the dedup phase being closed.* The private
`comp_eq_id_of_comp_id` below — a left inverse of an isomorphism is a right inverse — is the same
three-line statement as the private `comp_eq_id_of_comp_id` of
`FactorOnePrefixTransport.lean`. Being `private` there it is unusable from this module; this is a
further instance of the pattern that ledger records.

*The `γ⁺`-side spelling is written second.* The side the inputs live at — the join's right-hand
side, where `derivedPreimageSectionsCompIso` and `preimageSectionsModelComparison` are — is
written first, so the one definitional crossing the statement makes is paid once.

*No `@[stacks …]` attribute is placed.* Conclusion (c) of [Stacks, Tag 0EX3] is proved elsewhere,
as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap` (`BaseChangeTopDegreeConclusion.lean`),
by a route that does not use this file, and [Stacks, Tag 0D5W] carries its own where it is proved.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction (opensMap)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.Cohomology.DerivedSectionsLeray (lerayComparison isIso_lerayComparison
  derivedPreimageSections derivedSectionsOverOpen derivedPreimageSectionsCompModel
  derivedPreimageSectionsCompIso)
open Stacks.EdgeCompat (preimageRestrictScalars preimageSectionsModelComparison)
open StacksDraft.DerivedCategoryHomology

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-! ### Cancellations, at variables -/

/-- **A left inverse of an isomorphism is a right inverse.** At variables of an abstract category.
The invertibility is an explicit argument and not an instance: the morphism it is asked of is the
cohomology of a component of the Leray comparison, and instance search at that spelling does
not find it. -/
private theorem comp_eq_id_of_comp_id {C : Type*} [Category* C] {q r : C} (w : q ⟶ r)
    (hi : IsIso w) {lInv : r ⟶ q} (h : lInv ≫ w = 𝟙 r) : w ≫ lInv = 𝟙 q := by
  have := hi
  rw [← IsIso.inv_eq_of_inv_hom_id h, IsIso.hom_inv_id]

/-- **A morphism conjugated by an iso pair inherits the conjugated right inverse.** From a functor
`G`, a right inverse `v ≫ v' = 𝟙` upstairs, two iso pairs `a, a'` and `b, b'` identifying `G`'s
image with two objects downstairs, and the identification `G.map v = a' ≫ W ≫ b` of `G` of `v`
with the conjugate of `W`, the composite `b ≫ G.map v' ≫ a'` is a right inverse of `W`.

At variables of abstract categories, where every reassociation is free. This is the whole content
of moving a left inverse across one restriction-of-scalars layer; the two layers of factor (3) are
two applications of it. -/
private theorem comp_conj_id_of_map {D E : Type*} [Category* D] [Category* E] (G : D ⥤ E)
    {X₁ X₂ : D} {v : X₁ ⟶ X₂} {v' : X₂ ⟶ X₁} (hv : v ≫ v' = 𝟙 X₁)
    {P Q : E} {a : P ⟶ G.obj X₁} {a' : G.obj X₁ ⟶ P} (ha : a ≫ a' = 𝟙 P)
    {b : Q ⟶ G.obj X₂} {b' : G.obj X₂ ⟶ Q} (hb : b ≫ b' = 𝟙 Q) (hb' : b' ≫ b = 𝟙 (G.obj X₂))
    {W : P ⟶ Q} (hW : G.map v = a' ≫ W ≫ b) :
    W ≫ b ≫ G.map v' ≫ a' = 𝟙 P := by
  have hWe : W = a ≫ G.map v ≫ b' := by
    rw [hW]
    simp only [Category.assoc]
    rw [← Category.assoc a a', ha, Category.id_comp, hb, Category.comp_id]
  rw [hWe]
  simp only [Category.assoc]
  rw [← Category.assoc b' b, hb', Category.id_comp, ← Category.assoc (G.map v), ← G.map_comp,
    hv, G.map_id, Category.id_comp, ha]

/-- **A right inverse of the cohomology of `φ`, conjugated through an exact functor `F` by the
naturality of `mapDerivedCategoryHomologyIso F d`, is one of the cohomology of `F φ`.** -/
private theorem comp_homologyIso_conj_id {C D : Type*} [Category* C] [Category* D] [Abelian C]
    [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (d : ℤ) {K L : DerivedCategory C}
    {φ : K ⟶ L} {ψ : (DerivedCategory.homologyFunctor C d).obj L ⟶
      (DerivedCategory.homologyFunctor C d).obj K}
    (hψ : (DerivedCategory.homologyFunctor C d).map φ ≫ ψ = 𝟙 _) :
    (DerivedCategory.homologyFunctor D d).map (F.mapDerivedCategory.map φ) ≫
      (mapDerivedCategoryHomologyIso F d).hom.app L ≫ F.map ψ ≫
        (mapDerivedCategoryHomologyIso F d).inv.app K = 𝟙 _ :=
  comp_conj_id_of_map F hψ ((mapDerivedCategoryHomologyIso F d).hom_inv_id_app _)
    ((mapDerivedCategoryHomologyIso F d).hom_inv_id_app _)
    ((mapDerivedCategoryHomologyIso F d).inv_hom_id_app _) (map_homologyFunctor_map F d φ)

/-- **An equation of composites read under a functor, with the left-hand side's inner functor
application split**: from `m ≫ G.map (y ≫ z) = u ≫ v ≫ t` one gets the five factors read under
`H`, with `G.map (y ≫ z)` split into `G.map y` and `G.map z`.

At variables of abstract categories, where the application meets the concrete morphisms in
argument position only. The split is stated here rather than performed by `simp only` at the
hypothesis: on a goal of this shape `simp only [Functor.map_comp]` leaves the hypothesis
**unchanged and reports no error**. -/
private theorem map3_eq_map3_of_mapComp {C D E : Type*} [Category* C] [Category* D]
    [Category* E] (H : D ⥤ E) (G : C ⥤ D)
    {A₀ B₁ B₂ : D} {A₁ A₂ A₃ : C}
    {m : A₀ ⟶ G.obj A₁} {y : A₁ ⟶ A₂} {z : A₂ ⟶ A₃}
    {u : A₀ ⟶ B₁} {v : B₁ ⟶ B₂} {t : B₂ ⟶ G.obj A₃}
    (h : m ≫ G.map (y ≫ z) = u ≫ v ≫ t) :
    H.map m ≫ H.map (G.map y) ≫ H.map (G.map z) = H.map u ≫ H.map v ≫ H.map t := by
  simp only [← H.map_comp, ← G.map_comp]
  rw [h]

/-- **A three-factor composite solved for a two-factor prefix against a right inverse.** From
`A₁ ≫ A₂ ≫ W = l₁ ≫ l₂ ≫ l₃` and `W ≫ Ψ = 𝟙`, the composite `l₁ ≫ l₂ ≫ l₃ ≫ Ψ` is `A₁ ≫ A₂`.
At variables of an abstract category. -/
private theorem eq_of_comp_eq_three {C : Type*} [Category* C] {T R₁ R₂ P₁ P Q : C}
    {A₁ : T ⟶ P₁} {A₂ : P₁ ⟶ P} {W : P ⟶ Q}
    {l₁ : T ⟶ R₁} {l₂ : R₁ ⟶ R₂} {l₃ : R₂ ⟶ Q}
    (hm : A₁ ≫ A₂ ≫ W = l₁ ≫ l₂ ≫ l₃) {Ψ : Q ⟶ P} (hΨ : W ≫ Ψ = 𝟙 P) :
    l₁ ≫ l₂ ≫ l₃ ≫ Ψ = A₁ ≫ A₂ := by
  rw [← reassoc_of% hm, hΨ, Category.comp_id]

/-! ### The passage -/

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (p : X ⟶ Y) (V : Y.Opens) {U : Z.Opens}
  (e : U ≤ i ⁻¹ᵁ (p ⁻¹ᵁ V))

/-- **Factor (3) of the 2b(B) match of [Stacks, Tag 0EX3] (c), read in degree `d` and transposed
through the `ψ` side's left inverse.** For morphisms of schemes `i : Z ⟶ X` and `p : X ⟶ Y`, an
open `V ⊆ Y`, an open `U ≤ i⁻¹(p⁻¹V)` of `Z`, an object `K` of `D(𝒪_Z)`, a degree `d` and a left
inverse `lInv` of the degree-`d` cohomology of the Leray comparison of [Stacks, Tag 0D5W] for
`AlgebraicGeometry.Scheme.Hom.resLE i (p⁻¹V) U e` over the whole of the open subscheme `p⁻¹V`,

> the degree-`d` cohomology of `…DerivedSectionsLeray.derivedPreimageSectionsCompIso` **inverted**,
> of `Stacks.EdgeCompat.preimageSectionsModelComparison p V` at `Ri_*K`, and of
> `…TopDegreeBaseChange.openSubschemeLerayComparisonLE` under the restriction of scalars along
> `p^♯`, followed by `lInv` conjugated through the restriction of scalars along
> `AlgebraicGeometry.Scheme.Opens.topIso` and then through
> `Stacks.EdgeCompat.preimageRestrictScalars p V`

is

> the degree-`d` cohomology of `…DerivedSectionsLeray.derivedPreimageSectionsCompModel` and of
> `…TopDegreeBaseChange.openSubschemeSectionsComparisonLE` under the same restriction of scalars.

This is `…TopDegreeBaseChange.lerayCompositeModel_comp_openSubschemeSectionsComparisonLE_eq` read
in degree `d`, with the Leray comparison's cohomology cancelled against `lInv`. The conjugation is
the naturality of `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso` at each of
the two layers — that transformation has no component formula, so its naturality is all that is
used — which is why four of its components appear.

**Nothing is assumed** of `i`, of `p`, of `V`, of `U`, of `K` or of `d`: no affineness, no
acyclicity, no boundedness and no quasi-coherence. The Leray comparison is invertible
unconditionally by `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`, so `lInv` being
a **left** inverse — the form `Stacks.Cohomology.AffineComparison`
`.cohomologyIsoPushforward_inv_eq_lerayComparison` hands it in — suffices. -/
theorem homologyFunctor_map_derivedPreimageSectionsCompModel_comp_eq (d : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u}
            ((structureSheafRing (p ⁻¹ᵁ V : Scheme).toRingedSpace).obj.obj (op ⊤))) d).obj
        ((derivedPushforward (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⋙
            derivedSectionsOverOpen (p ⁻¹ᵁ V : Scheme).toRingedSpace ⊤).obj
          ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K)) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u}
            ((structureSheafRing (p ⁻¹ᵁ V : Scheme).toRingedSpace).obj.obj (op ⊤))) d).obj
        ((derivedPreimageSections (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⊤).obj
          ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K))}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
            (ModuleCat.{u}
              ((structureSheafRing (p ⁻¹ᵁ V : Scheme).toRingedSpace).obj.obj (op ⊤))) d).map
          ((lerayComparison (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⊤).app
            ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K)) = 𝟙 _) :
    (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
          ((derivedPreimageSectionsCompIso i.toLRSHom.toShHom p.toLRSHom.toShHom V).inv.app K) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
            ((preimageSectionsModelComparison p.toLRSHom.toShHom V).app
              ((derivedPushforward i.toLRSHom.toShHom).obj K)) ≫
          (DerivedCategory.homologyFunctor
                (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
              ((preimageRestrictScalars p.toLRSHom.toShHom V).mapDerivedCategory.map
                ((openSubschemeLerayComparisonLE i (p ⁻¹ᵁ V) e).app K)) ≫
            (mapDerivedCategoryHomologyIso
                (preimageRestrictScalars p.toLRSHom.toShHom V) d).hom.app
                ((ModuleCat.restrictScalars
                    (Scheme.Opens.topIso (p ⁻¹ᵁ V)).inv.hom).mapDerivedCategory.obj
                  ((derivedPushforward (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⋙
                      derivedSectionsOverOpen (p ⁻¹ᵁ V : Scheme).toRingedSpace ⊤).obj
                    ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K))) ≫
              (preimageRestrictScalars p.toLRSHom.toShHom V).map
                  ((mapDerivedCategoryHomologyIso
                      (ModuleCat.restrictScalars
                        (Scheme.Opens.topIso (p ⁻¹ᵁ V)).inv.hom) d).hom.app
                      ((derivedPushforward (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⋙
                          derivedSectionsOverOpen (p ⁻¹ᵁ V : Scheme).toRingedSpace ⊤).obj
                        ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K)) ≫
                    (ModuleCat.restrictScalars
                        (Scheme.Opens.topIso (p ⁻¹ᵁ V)).inv.hom).map lInv ≫
                      (mapDerivedCategoryHomologyIso
                        (ModuleCat.restrictScalars
                          (Scheme.Opens.topIso (p ⁻¹ᵁ V)).inv.hom) d).inv.app
                        ((derivedPreimageSections
                            (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⊤).obj
                          ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K))) ≫
                (mapDerivedCategoryHomologyIso
                  (preimageRestrictScalars p.toLRSHom.toShHom V) d).inv.app
                  ((ModuleCat.restrictScalars
                      (Scheme.Opens.topIso (p ⁻¹ᵁ V)).inv.hom).mapDerivedCategory.obj
                    ((derivedPreimageSections
                        (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⊤).obj
                      ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K))) =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
          ((derivedPreimageSectionsCompModel
            i.toLRSHom.toShHom p.toLRSHom.toShHom V).app K) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d).map
            ((preimageRestrictScalars p.toLRSHom.toShHom V).mapDerivedCategory.map
              ((openSubschemeSectionsComparisonLE i (p ⁻¹ᵁ V) e).app K)) := by
  have hc : (derivedPreimageSectionsCompModel
          i.toLRSHom.toShHom p.toLRSHom.toShHom V).app K ≫
        (preimageRestrictScalars p.toLRSHom.toShHom V).mapDerivedCategory.map
          ((openSubschemeSectionsComparisonLE i (p ⁻¹ᵁ V) e).app K ≫
            (ModuleCat.restrictScalars
                (Scheme.Opens.topIso (p ⁻¹ᵁ V)).inv.hom).mapDerivedCategory.map
              ((lerayComparison (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⊤).app
                ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K))) =
      (derivedPreimageSectionsCompIso i.toLRSHom.toShHom p.toLRSHom.toShHom V).inv.app K ≫
        (preimageSectionsModelComparison p.toLRSHom.toShHom V).app
            ((derivedPushforward i.toLRSHom.toShHom).obj K) ≫
          (preimageRestrictScalars p.toLRSHom.toShHom V).mapDerivedCategory.map
            ((openSubschemeLerayComparisonLE i (p ⁻¹ᵁ V) e).app K) :=
    NatTrans.congr_app
      (lerayCompositeModel_comp_openSubschemeSectionsComparisonLE_eq i p V e) K
  have hiso : IsIso ((lerayComparison (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⊤).app
      ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K)) := by
    have := isIso_lerayComparison (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom
      (⊤ : Opens (p ⁻¹ᵁ V : Scheme))
    infer_instance
  have hwl := comp_eq_id_of_comp_id ((DerivedCategory.homologyFunctor
      (ModuleCat.{u}
        ((structureSheafRing (p ⁻¹ᵁ V : Scheme).toRingedSpace).obj.obj (op ⊤))) d).map
        ((lerayComparison (i.resLE (p ⁻¹ᵁ V) U e).toLRSHom.toShHom ⊤).app
          ((openSubschemeRestrictionOf Z U).mapDerivedCategory.obj K)))
    (by have := hiso; infer_instance) hl
  have hinner := comp_homologyIso_conj_id
    (ModuleCat.restrictScalars (Scheme.Opens.topIso (p ⁻¹ᵁ V)).inv.hom) d hwl
  have houter := comp_homologyIso_conj_id
    (preimageRestrictScalars p.toLRSHom.toShHom V) d hinner
  exact eq_of_comp_eq_three
    (map3_eq_map3_of_mapComp
      (DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((structureSheafRing Y.toRingedSpace).obj.obj (op V))) d)
      (preimageRestrictScalars p.toLRSHom.toShHom V).mapDerivedCategory hc)
    houter

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
