module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FactorOneCollapseMirror
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.LerayOpenSubschemeCrossingInvertible
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Factor (1)'s match transported to the `γ⁺` side's reading at `(f, V)`

`FactorOneCollapseMirror.lean` matches factor (1) of [Stacks, Tag 089W] against the `γ⁺` side's
prefix **at the pair `((f ∣_ V), ⊤)`** — the open subscheme `f⁻¹V` read as a scheme in its own
right and the whole of the open subscheme `V`. The tail of conclusion (c) of [Stacks, Tag 0EX3]
reads the `γ⁺` side at `(f, V)` on `X` instead, in
`…TopDegreeBaseChange.prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison`. The
passage between the two readings is the derived crossing
`…TopDegreeBaseChange.openSubschemeSectionsComparison f V`, invertible with no hypothesis by
`…TopDegreeBaseChange.isIso_openSubschemeSectionsComparison`. This file writes the equation that
transports the match across it.

Nothing about the crossing's invertibility is used: the transport is an equation, and the only
inverse it takes is the Leray one, which
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` supplies unconditionally. The one
piece of machinery is `…openSubschemeSectionsComparison_comp_lerayComparison_eq`, which says that
the two crossings — out of `RΓ(f⁻¹V, -)` and out of the Leray comparison's target — differ by the
two Leray comparisons, and `StacksDraft.DerivedCategoryHomology.map_homologyFunctor_map`, which
crosses `Hⁿ` past the restriction of scalars that the open-subscheme reading carries. That
transformation has **no component formula**, so its naturality is all that is used.

## Main results

* `…TopDegreeBaseChange.homologyFunctor_map_openSubschemeSectionsComparison_eq`: **the crossing
  transport, at an arbitrary object of `D(𝒪_X)`.** The degree-`n` cohomology of the crossing out
  of `RΓ(f⁻¹V, -)` is the degree-`n` cohomology of the Leray comparison of [Stacks, Tag 0D5W],
  then of the crossing out of its target, then the restriction of scalars crossed past `Hⁿ` and
  applied to a left inverse of the Leray comparison for `f ∣_ V` over `⊤`.
* `…TopDegreeBaseChange.homologyFunctor_map_openSubschemeSectionsComparison_single_eq`: the same
  with the object a **single complex** `M[0]`, so that the Leray left inverse is asked for at
  `((openSubschemeRestriction f V).obj M)[0]` — which is the object factor (1)'s match asks for
  it at. The passage between the two is the naturality of the Leray comparison at
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`.
* `…TopDegreeBaseChange.prefix_transport_eq_openSubschemeSectionsComparison_comp`: **factor (1)'s
  match transported.** The `γ⁺` prefix at `((f ∣_ V), ⊤)`, read under the restriction of scalars
  along `AlgebraicGeometry.Scheme.Opens.topIso` and transported along the two open-subscheme
  crossings, is the crossing out of `RΓ(f⁻¹V, -)`, the restriction of scalars crossed past `Hⁿ`,
  and the restriction of scalars applied to everything factor (1)'s match leaves after the Leray
  left inverse.

The hypotheses are exactly those of
`…TopDegreeBaseChange.prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv`: Grothendieck's
pointwise homology-preservation hypothesis `hpl` at the pair `((f ∣_ V)_*, Γ(V, ⊤, -))`, and a
left inverse of the degree-`n` cohomology of the Leray comparison. **Nothing is assumed of `f`,
of `V`, of `M` or of `n`** — no affineness, no quasi-compactness, no quasi-separatedness, no
boundedness and no quasi-coherence.

*No `@[stacks …]` attribute is placed.* [Stacks, Tag 089W], [Stacks, Tag 01XK] and
[Stacks, Tag 0D5W] carry theirs where they are proved, and conclusion (c) of [Stacks, Tag 0EX3] is
proved elsewhere, as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap`
(`BaseChangeTopDegreeConclusion.lean`), by a route that does not use this file.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.EdgeCompat
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison)
open StacksDraft.DerivedCategoryHomology

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Cancellations, at variables -/

/-- **A left inverse of an isomorphism is a right inverse.** At variables of an abstract category.
The invertibility is an explicit argument and not an instance: the morphism it is asked of is the
cohomology of a component of the Leray comparison, and instance search at that spelling is
unreliable. -/
private theorem comp_eq_id_of_comp_id {C : Type*} [Category* C] {p q : C} (w : p ⟶ q)
    (hi : IsIso w) {lInv : q ⟶ p} (h : lInv ≫ w = 𝟙 q) : w ≫ lInv = 𝟙 p := by
  have := hi
  rw [← IsIso.inv_eq_of_inv_hom_id h, IsIso.hom_inv_id]

/-- **The two factors of an equation of composites, read under a functor.** At variables of
abstract categories, where the application meets the concrete morphisms in argument position
only. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {A B B' T : C} {x : A ⟶ B} {y : B ⟶ T} {z : A ⟶ B'} {w : B' ⟶ T} (h : x ≫ y = z ≫ w) :
    H.map x ≫ H.map y = H.map z ≫ H.map w := by
  rw [← H.map_comp, ← H.map_comp, h]

/-- **A left inverse carried across a naturality square and a functor.** From `A ≫ W = l ≫ o`,
a naturality square `a ≫ W' = W ≫ b`, a transformation `W' ≫ ι₂ = ι₁ ≫ G.map w` of `W'` into
`G`'s image, an inverse pair `ι₁ ≫ ι₁' = 𝟙` and a right inverse `w ≫ lInv = 𝟙`, the composite
`l ≫ o ≫ b ≫ ι₂ ≫ G.map lInv ≫ ι₁'` is `A ≫ a`. At variables of abstract categories, where
every reassociation is free. -/
private theorem eq_of_comp_eq_of_nat {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {T R P P' Q Q' : D} {p q : C} {A : T ⟶ P} {W : P ⟶ Q} {l : T ⟶ R} {o : R ⟶ Q}
    (hm : A ≫ W = l ≫ o)
    {a : P ⟶ P'} {b : Q ⟶ Q'} {W' : P' ⟶ Q'} (hn : a ≫ W' = W ≫ b)
    {ι₁ : P' ⟶ G.obj p} {ι₁' : G.obj p ⟶ P'} (h1 : ι₁ ≫ ι₁' = 𝟙 P')
    {ι₂ : Q' ⟶ G.obj q} {w : p ⟶ q} (hnat : W' ≫ ι₂ = ι₁ ≫ G.map w)
    {lInv : q ⟶ p} (hw : w ≫ lInv = 𝟙 p) :
    l ≫ o ≫ b ≫ ι₂ ≫ G.map lInv ≫ ι₁' = A ≫ a := by
  have h2 : G.map w ≫ G.map lInv = 𝟙 (G.obj p) := by rw [← G.map_comp, hw, G.map_id]
  have key : l ≫ o ≫ b ≫ ι₂ ≫ G.map lInv ≫ ι₁' =
      A ≫ (W ≫ b) ≫ ι₂ ≫ G.map lInv ≫ ι₁' := by
    rw [← Category.assoc l, ← hm]
    simp only [Category.assoc]
  rw [key, ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc W' ι₂, hnat]
  simp only [Category.assoc]
  rw [← Category.assoc (G.map w), h2, Category.id_comp, h1, Category.comp_id]

/-- **The same with no naturality square**, the degenerate case where the two readings sit at one
object. At variables of abstract categories. -/
private theorem eq_of_comp_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {T R P Q : D} {p q : C} {A : T ⟶ P} {W : P ⟶ Q} {l : T ⟶ R} {o : R ⟶ Q}
    (hm : A ≫ W = l ≫ o)
    {ι₁ : P ⟶ G.obj p} {ι₁' : G.obj p ⟶ P} (h1 : ι₁ ≫ ι₁' = 𝟙 P)
    {ι₂ : Q ⟶ G.obj q} {w : p ⟶ q} (hnat : W ≫ ι₂ = ι₁ ≫ G.map w)
    {lInv : q ⟶ p} (hw : w ≫ lInv = 𝟙 p) :
    l ≫ o ≫ ι₂ ≫ G.map lInv ≫ ι₁' = A := by
  simpa using eq_of_comp_eq_of_nat G hm (a := 𝟙 _) (b := 𝟙 _) (by simp) h1 hnat hw

/-- **A hoisted prefix substituted for a left inverse followed by the rest.** From
`l ≫ o ≫ b ≫ ι₂ ≫ G.map lInv ≫ ι₁' = A ≫ a`, an inverse pair `ι₁' ≫ ι₁ = 𝟙` and a
factorisation `pre = lInv ≫ Rest`, the composite `l ≫ o ≫ b ≫ ι₂ ≫ G.map pre` is
`A ≫ a ≫ ι₁ ≫ G.map Rest`. At variables of abstract categories. -/
private theorem comp_map_eq_of_transport {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {T R R' Q' P P' : D} {p q t : C}
    {l : T ⟶ R} {o : R ⟶ R'} {b : R' ⟶ Q'} {ι₂ : Q' ⟶ G.obj q}
    {lInv : q ⟶ p} {Rest : p ⟶ t} {pre : q ⟶ t} (hpre : pre = lInv ≫ Rest)
    {A : T ⟶ P} {a : P ⟶ P'} {ι₁ : P' ⟶ G.obj p} {ι₁' : G.obj p ⟶ P'}
    (h1 : ι₁' ≫ ι₁ = 𝟙 (G.obj p))
    (ht : l ≫ o ≫ b ≫ ι₂ ≫ G.map lInv ≫ ι₁' = A ≫ a) :
    l ≫ o ≫ b ≫ ι₂ ≫ G.map pre = A ≫ a ≫ ι₁ ≫ G.map Rest :=
  calc l ≫ o ≫ b ≫ ι₂ ≫ G.map pre
      = l ≫ o ≫ b ≫ ι₂ ≫ G.map lInv ≫ (ι₁' ≫ ι₁) ≫ G.map Rest := by
        rw [h1, Category.id_comp, hpre, G.map_comp]
    _ = (l ≫ o ≫ b ≫ ι₂ ≫ G.map lInv ≫ ι₁') ≫ ι₁ ≫ G.map Rest := by
        simp only [Category.assoc]
    _ = (A ≫ a) ≫ ι₁ ≫ G.map Rest := by rw [ht]
    _ = A ≫ a ≫ ι₁ ≫ G.map Rest := by simp only [Category.assoc]

/-! ### The crossing transport -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)

/-- **The crossing square in degree `n`.** `Hⁿ` of the two sides of
`…openSubschemeSectionsComparison_comp_lerayComparison_eq` at `K`, the restriction of scalars
carried by `mapDerivedCategory`. -/
private theorem homologyFunctor_map_sectionsComparison_comp_eq (n : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))) :
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
        ((openSubschemeSectionsComparison f V).app K) ≫
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
        ((ModuleCat.restrictScalars
            (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
          ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
            ((openSubschemeRestriction f V).mapDerivedCategory.obj K))) =
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
        ((lerayComparison f.toLRSHom.toShHom V).app K) ≫
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
        ((openSubschemeLerayComparison f V).app K) := by
  have hc := NatTrans.congr_app (openSubschemeSectionsComparison_comp_lerayComparison_eq f V) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hc
  exact map_comp_eq_map_comp _ hc


/-- **The degree-`n` cohomology of the open-subscheme crossing of `RΓ(f⁻¹V, -)`, read off the
Leray comparisons.** For a morphism of schemes `f : X ⟶ S`, an open `V ⊆ S`, an object `K` of
`D(𝒪_X)` and a degree `n`,

> `Hⁿ(…openSubschemeSectionsComparison f V at K)`

is the degree-`n` cohomology of the Leray comparison of [Stacks, Tag 0D5W] for `f` over `V`, then
of `…openSubschemeLerayComparison f V`, then
`StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso` at the restriction of scalars
along `AlgebraicGeometry.Scheme.Opens.topIso`, then that restriction of scalars applied to a left
inverse of the degree-`n` cohomology of the Leray comparison for `f ∣_ V` over `⊤`, then the
comparison inverted.

This is `…openSubschemeSectionsComparison_comp_lerayComparison_eq` read in degree `n`, with the
restriction of scalars crossed past `Hⁿ` by the naturality of
`mapDerivedCategoryHomologyIso` — that transformation is built by
`CategoryTheory.Localization.liftNatIso` and has no component formula, so its naturality is all
that is used. The left inverse is taken as a left inverse of a **plain** morphism, in the form
`…prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` hands it in; that it is also a right
inverse is not an extra hypothesis but
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`, which is unconditional.

**Nothing is assumed** of `f`, of `V`, of `K` or of `n`. -/
theorem homologyFunctor_map_openSubschemeSectionsComparison_eq (n : ℤ)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) n).obj
        ((derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
            derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤).obj
          ((openSubschemeRestriction f V).mapDerivedCategory.obj K)) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) n).obj
        ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).obj
          ((openSubschemeRestriction f V).mapDerivedCategory.obj K))}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
            (ModuleCat.{u}
              ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) n).map
          ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
            ((openSubschemeRestriction f V).mapDerivedCategory.obj K)) = 𝟙 _) :
    (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
          ((lerayComparison f.toLRSHom.toShHom V).app K) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
            ((openSubschemeLerayComparison f V).app K) ≫
          (mapDerivedCategoryHomologyIso
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).hom.app
              ((derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
                  derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤).obj
                ((openSubschemeRestriction f V).mapDerivedCategory.obj K)) ≫
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map lInv ≫
              (mapDerivedCategoryHomologyIso
                (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).inv.app
                ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).obj
                  ((openSubschemeRestriction f V).mapDerivedCategory.obj K)) =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
          ((openSubschemeSectionsComparison f V).app K) := by
  have hm := homologyFunctor_map_sectionsComparison_comp_eq f V n K
  have hnat := (mapDerivedCategoryHomologyIso
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).hom.naturality
    ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
      ((openSubschemeRestriction f V).mapDerivedCategory.obj K))
  simp only [Functor.comp_map] at hnat
  have hw := comp_eq_id_of_comp_id ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) n).map
        ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
          ((openSubschemeRestriction f V).mapDerivedCategory.obj K)))
    (by have := isIso_lerayComparison (f ∣_ V).toLRSHom.toShHom (⊤ : Opens (V : Scheme))
        infer_instance) hl
  exact eq_of_comp_eq (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) hm
    ((mapDerivedCategoryHomologyIso
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).hom_inv_id_app _)
    hnat hw

/-- **The crossing transport at a single complex.** The same as
`homologyFunctor_map_openSubschemeSectionsComparison_eq` with `K` the single complex of a module
`M` on `X`, and the Leray left inverse asked for at
`((openSubschemeRestriction f V).obj M)[0]` instead of at
`(openSubschemeRestriction f V).mapDerivedCategory.obj (M[0])`. The two objects are related by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, and the passage is that isomorphism's
naturality under the Leray comparison; the extra factor it leaves appears on both sides.

This is the object `…prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` asks for its own
Leray left inverse at, which is what makes the two composable. **Nothing is assumed** of `f`, of
`V`, of `M` or of `n`. -/
theorem homologyFunctor_map_openSubschemeSectionsComparison_single_eq (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) n).obj
        ((derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
            derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u}
              (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
            ((openSubschemeRestriction f V).obj M))) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) n).obj
        ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u}
              (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
            ((openSubschemeRestriction f V).obj M)))}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
            (ModuleCat.{u}
              ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) n).map
          ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u}
                (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
              ((openSubschemeRestriction f V).obj M))) = 𝟙 _) :
    (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
          ((lerayComparison f.toLRSHom.toShHom V).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
            ((openSubschemeLerayComparison f V).app
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) ≫
          (DerivedCategory.homologyFunctor
                (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
              ((ModuleCat.restrictScalars
                  (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
                ((derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
                    derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤).map
                  (((openSubschemeRestriction f V).mapDerivedCategorySingleFunctor
                    0).hom.app M))) ≫
            (mapDerivedCategoryHomologyIso
                (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).hom.app
                ((derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
                    derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤).obj
                  ((DerivedCategory.singleFunctor
                    (SheafOfModules.{u}
                      (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
                    ((openSubschemeRestriction f V).obj M))) ≫
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map lInv ≫
                (mapDerivedCategoryHomologyIso
                  (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).inv.app
                  ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).obj
                    ((DerivedCategory.singleFunctor
                      (SheafOfModules.{u}
                        (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
                      ((openSubschemeRestriction f V).obj M))) =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
          ((openSubschemeSectionsComparison f V).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n).map
            ((ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
              ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).map
                (((openSubschemeRestriction f V).mapDerivedCategorySingleFunctor
                  0).hom.app M))) := by
  have hm := homologyFunctor_map_sectionsComparison_comp_eq f V n
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)
  have hn := map_comp_eq_map_comp
    ((ModuleCat.restrictScalars
      (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory ⋙
        DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) n)
    ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).naturality
      (((openSubschemeRestriction f V).mapDerivedCategorySingleFunctor 0).hom.app M))
  simp only [Functor.comp_map] at hn
  have hnat := (mapDerivedCategoryHomologyIso
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).hom.naturality
    ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u}
          (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
        ((openSubschemeRestriction f V).obj M)))
  simp only [Functor.comp_map] at hnat
  have hw := comp_eq_id_of_comp_id ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) n).map
        ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u}
              (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
            ((openSubschemeRestriction f V).obj M))))
    (by have := isIso_lerayComparison (f ∣_ V).toLRSHom.toShHom (⊤ : Opens (V : Scheme))
        infer_instance) hl
  exact eq_of_comp_eq_of_nat (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) hm hn
    ((mapDerivedCategoryHomologyIso
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) n).hom_inv_id_app _)
    hnat hw

/-! ### Factor (1)'s match transported -/

/-- **Factor (1) of [Stacks, Tag 089W] matched against the `γ⁺` side's prefix read at `(f, V)`.**
For a morphism of schemes `f : X ⟶ S`, an open `V ⊆ S`, a module `M` on `X` and a degree `n`, the
composite

> the degree-`n` cohomology of the Leray comparison of [Stacks, Tag 0D5W] for `f` over `V`, then
> of `…openSubschemeLerayComparison f V`, then of the restriction of scalars applied to
> `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, then
> `StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso`, then the restriction of
> scalars along `AlgebraicGeometry.Scheme.Opens.topIso` applied to the `γ⁺` prefix at
> `((f ∣_ V), ⊤)`

is

> the degree-`n` cohomology of `…openSubschemeSectionsComparison f V` — the crossing of the two
> readings of `RΓ(f⁻¹V, -)` — then of the restriction of scalars applied to
> `mapDerivedCategorySingleFunctor`, then `mapDerivedCategoryHomologyIso`, then the restriction of
> scalars applied to everything
> `…prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` leaves after its Leray left inverse:
> the degree-`n` cohomology of `Stacks.EdgeCompat.preimageSectionsModelComparison (f ∣_ V) ⊤`, the
> edge morphism of the restriction of scalars along `(f ∣_ V)^♯`, **factor (1)** of
> [Stacks, Tag 089W], **factor (5)**, Grothendieck's comparison of [Stacks, Tag 01XK] at the pair
> `((f ∣_ V)_*, Γ(V, ⊤, -))` inverted, and `Γ(V, ⊤, -)` of the comparison of the two indexings.

So factor (1)'s match, which
`…prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv` makes at `((f ∣_ V), ⊤)`, is carried to
the reading at `(f, V)` on `X` that
`…prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison` and the tail of
conclusion (c) of [Stacks, Tag 0EX3] use. The crossing is taken in the **forward** direction on
both sides, so `…isIso_openSubschemeSectionsComparison` is not used and no inverse of either
open-subscheme crossing is written down; the only inverse is the Leray one, which
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` supplies unconditionally.

The two hypotheses are its inputs' own and nothing more: `hpl` is Grothendieck's pointwise
homology-preservation hypothesis at the pair `((f ∣_ V)_*, Γ(V, ⊤, -))`, and `hl` is a left
inverse of the degree-`n` cohomology of the Leray comparison for `f ∣_ V` over `⊤`. **Nothing is
assumed** of `f`, of `V`, of `M` or of `n`. -/
theorem prefix_transport_eq_openSubschemeSectionsComparison_comp (n : ℕ)
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (hpl : ∀ Z : SheafOfModules.{u} (structureSheafRing X.toRingedSpace),
      (sectionsOverOpen (V : Scheme).toRingedSpace ⊤).PreservesLeftHomologyOf
        ((((modulePushforward (f ∣_ V).toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
            (injectiveResolution ((openSubschemeRestriction f V).obj Z)).cocomplex).sc n))
    {lInv : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))
          (n : ℤ)).obj
        ((derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
            derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u}
              (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
            ((openSubschemeRestriction f V).obj M))) ⟶
      (DerivedCategory.homologyFunctor
          (ModuleCat.{u} ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))
          (n : ℤ)).obj
        ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u}
              (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
            ((openSubschemeRestriction f V).obj M)))}
    (hl : lInv ≫ (DerivedCategory.homologyFunctor
            (ModuleCat.{u}
              ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤))) (n : ℤ)).map
          ((lerayComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u}
                (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
              ((openSubschemeRestriction f V).obj M))) = 𝟙 _) :
    (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) (n : ℤ)).map
          ((lerayComparison f.toLRSHom.toShHom V).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) (n : ℤ)).map
            ((openSubschemeLerayComparison f V).app
              ((DerivedCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) ≫
          (DerivedCategory.homologyFunctor
                (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))
                (n : ℤ)).map
              ((ModuleCat.restrictScalars
                  (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
                ((derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
                    derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤).map
                  (((openSubschemeRestriction f V).mapDerivedCategorySingleFunctor
                    0).hom.app M))) ≫
            (mapDerivedCategoryHomologyIso
                (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) (n : ℤ)).hom.app
                ((derivedPushforward (f ∣_ V).toLRSHom.toShHom ⋙
                    derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤).obj
                  ((DerivedCategory.singleFunctor
                    (SheafOfModules.{u}
                      (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
                    ((openSubschemeRestriction f V).obj M))) ≫
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
                ((derivedHomologyComparison (sectionsOverOpen (V : Scheme).toRingedSpace ⊤)
                      (derivedSectionsOverOpen (V : Scheme).toRingedSpace ⊤)
                      (derivedSectionsOverOpenUnit (V : Scheme).toRingedSpace ⊤)
                      (exists_quasiIso_isKInjective (V : Scheme).toRingedSpace) (n : ℤ)).app
                    ((derivedPushforward (f ∣_ V).toLRSHom.toShHom).obj
                      ((DerivedCategory.singleFunctor
                        (SheafOfModules.{u}
                          (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
                        ((openSubschemeRestriction f V).obj M))) ≫
                  (sectionsOverOpen (V : Scheme).toRingedSpace ⊤).map
                    (homologyFunctorDerivedPushforwardIso (f ∣_ V)
                      ((openSubschemeRestriction f V).obj M) (n : ℤ)).hom) =
      (DerivedCategory.homologyFunctor
            (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V))) (n : ℤ)).map
          ((openSubschemeSectionsComparison f V).app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj M)) ≫
        (DerivedCategory.homologyFunctor
              (ModuleCat.{u} ((structureSheafRing S.toRingedSpace).obj.obj (op V)))
              (n : ℤ)).map
            ((ModuleCat.restrictScalars
                (Scheme.Opens.topIso V).inv.hom).mapDerivedCategory.map
              ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).map
                (((openSubschemeRestriction f V).mapDerivedCategorySingleFunctor
                  0).hom.app M))) ≫
          (mapDerivedCategoryHomologyIso
              (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) (n : ℤ)).hom.app
              ((derivedPreimageSections (f ∣_ V).toLRSHom.toShHom ⊤).obj
                ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u}
                    (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
                  ((openSubschemeRestriction f V).obj M))) ≫
            (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom).map
              ((DerivedCategory.homologyFunctor
                    (ModuleCat.{u}
                      ((structureSheafRing (V : Scheme).toRingedSpace).obj.obj (op ⊤)))
                    (n : ℤ)).map
                  ((preimageSectionsModelComparison (f ∣_ V).toLRSHom.toShHom ⊤).app
                    ((DerivedCategory.singleFunctor
                      (SheafOfModules.{u}
                        (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
                      ((openSubschemeRestriction f V).obj M))) ≫
                (derivedHomologyComparison
                      (preimageRestrictScalars (f ∣_ V).toLRSHom.toShHom ⊤)
                      (preimageRestrictScalars (f ∣_ V).toLRSHom.toShHom ⊤).mapDerivedCategory
                      (preimageRestrictScalars (f ∣_ V).toLRSHom.toShHom
                        ⊤).mapDerivedCategoryFactorsh.inv
                      (exists_quasiIso_isKInjective_preimageSectionsRing
                        (f ∣_ V).toLRSHom.toShHom ⊤) (n : ℤ)).app
                    ((derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                        ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤)).obj
                      ((DerivedCategory.singleFunctor
                        (SheafOfModules.{u}
                          (structureSheafRing (f ⁻¹ᵁ V : Scheme).toRingedSpace)) 0).obj
                        ((openSubschemeRestriction f V).obj M))) ≫
                  (preimageRestrictScalars (f ∣_ V).toLRSHom.toShHom ⊤).map
                      ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
                        (sectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                          ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤))
                        (derivedSectionsOverOpen (f ⁻¹ᵁ V : Scheme).toRingedSpace
                          ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤))
                        (derivedSectionsOverOpenUnit (f ⁻¹ᵁ V : Scheme).toRingedSpace
                          ((opensMap (f ∣_ V).toLRSHom.toShHom).obj ⊤))
                        (exists_quasiIso_isKInjective
                          (f ⁻¹ᵁ V : Scheme).toRingedSpace) n).hom.app
                        ((openSubschemeRestriction f V).obj M)) ≫
                    (Stacks.Cohomology.AffineComparison.restrictScalarsRightDerivedIso (f ∣_ V)
                        ((openSubschemeRestriction f V).obj M) n).hom ≫
                      (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso
                          (openSubschemeRestriction f V)
                          (modulePushforward (f ∣_ V).toLRSHom.toShHom)
                          (sectionsOverOpen (V : Scheme).toRingedSpace ⊤) n hpl).inv.app M ≫
                        (sectionsOverOpen (V : Scheme).toRingedSpace ⊤).map
                          ((Stacks.DerivedIndexing.rightDerivedIso
                            (modulePushforward (f ∣_ V).toLRSHom.toShHom) n).hom.app
                            ((openSubschemeRestriction f V).obj M))) := by
  have := hpl M
  exact comp_map_eq_of_transport (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom)
    (prefix_eq_factorOneFive_comp_rightDerivedCompNatIso_inv (f ∣_ V) n
      (openSubschemeRestriction f V) hpl M hl)
    ((mapDerivedCategoryHomologyIso
      (ModuleCat.restrictScalars (Scheme.Opens.topIso V).inv.hom) (n : ℤ)).inv_hom_id_app _)
    (homologyFunctor_map_openSubschemeSectionsComparison_single_eq f V (n : ℤ) M hl)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
