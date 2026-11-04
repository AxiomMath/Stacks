module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectInduction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentIso
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentHomDescentTriangle
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectArrowIso

/-!
# Relative descent situations with isomorphic fixed stages

Let `D` be a relative descent situation in the sense of Stacks 0DI6, with inverse system `Sᵢ`,
limit `S` and flat morphism of finite presentation `X₀ ⟶ S₀`. Replacing `X₀` by a scheme `Y`
isomorphic to it over `S₀` gives a second situation `D.withX₀ Y` with the same inverse system;
its stages `Y ×_{S₀} Sᵢ` and its limit `Y ×_{S₀} S` are isomorphic over `Sᵢ` and over `S` to
those of `D`. This file shows that both halves of Stacks 0DI8 — the descent of derived morphism
sets of `AlgebraicGeometry.RelativeDescentSituation.HomDescent` and the essential surjectivity
of `AlgebraicGeometry.RelativeDescentSituation.PerfectEssentiallySurjectiveCanonical` — are
unchanged by this replacement, and specialises this to two cases for quasi-compact opens of
`X₀`: the restriction to `⊤`, and a restriction of a restriction.

## Main definitions

* `AlgebraicGeometry.RelativeDescentSituation.withX₀`: the situation with `X₀` replaced by `Y`.
* `AlgebraicGeometry.RelativeDescentSituation.withX₀StageIso` and `withX₀LimitIso`: the
  isomorphisms of the stages and of the limits induced by an isomorphism `Y ≅ X₀` over `S₀`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_iso_over_iff`: relative perfectness of
  Stacks 0DI0 is invariant under an isomorphism of the source over a fixed base.
* `AlgebraicGeometry.RelativeDescentSituation.homDescent_withX₀_iff` and
  `perfectEssentiallySurjectiveCanonical_withX₀_iff`: both halves of Stacks 0DI8 transport along
  an isomorphism of the fixed stage.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_top_iff` and
  `perfectEssentiallySurjectiveCanonical_restrict_top_iff`: the situation restricted to
  `⊤ ⊆ X₀` and the situation itself.
* `AlgebraicGeometry.RelativeDescentSituation.restrictHomDescent_restrict_iff` and
  `restrictPerfectEssentiallySurjective_restrict_iff`: for quasi-compact opens `U₀ ≤ W₀` of
  `X₀`, the restriction of `D.restrict W₀` to the preimage of `U₀` and `D.restrict U₀`.

## References

* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DI7](https://stacks.math.columbia.edu/tag/0DI7)
* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Relative perfectness is invariant under an isomorphism of the source over the base.** For
morphisms `f : X ⟶ S` and `f' : X' ⟶ S`, flat and locally of finite presentation, and an
isomorphism `ρ : X' ≅ X` with `ρ ≫ f = f'`, the derived pullback along `ρ` of an object of
`D(𝒪_X)` is `S`-perfect exactly when the object is, at the canonical certificate families. -/
theorem isPerfectRelativeTo_iso_over_iff {X X' S : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [Flat f'] [LocallyOfFinitePresentation f']
    [CompactSpace X'.carrier] (ρ : X' ≅ X) (hρ : ρ.hom ≫ f = f')
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    f'.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedPullback ρ.hom.toLRSHom.toShHom).obj E) ↔
      f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E :=
  isPerfectRelativeTo_arrowIso_iff f' f
    (Arrow.isoMk (Scheme.forgetToRingedSpace.mapIso ρ) (Iso.refl _) (by
      simp only [Arrow.mk_hom, Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
      rw [← Scheme.forgetToRingedSpace.map_comp, hρ])) E

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

variable {X X' S T T' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S) (a : X' ≅ X) (ha : a.hom ≫ f = f')

/-- An isomorphism `X' ≅ X` over `S` induces an isomorphism `X' ×_S T ≅ X ×_S T` over `T`. -/
def pullbackLeftIso (g : T ⟶ S) : pullback f' g ≅ pullback f g where
  hom := pullback.lift (pullback.fst f' g ≫ a.hom) (pullback.snd f' g)
    (by rw [Category.assoc, ha, pullback.condition])
  inv := pullback.lift (pullback.fst f g ≫ a.inv) (pullback.snd f g)
    (by rw [Category.assoc, ← ha, Iso.inv_hom_id_assoc, pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.lift_snd,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- `pullbackLeftIso` followed by the first projection is the first projection followed by `a`. -/
@[reassoc]
theorem pullbackLeftIso_hom_fst (g : T ⟶ S) :
    (pullbackLeftIso f f' a ha g).hom ≫ pullback.fst f g = pullback.fst f' g ≫ a.hom :=
  pullback.lift_fst _ _ _

/-- `pullbackLeftIso` commutes with the second projections to `T`. -/
@[reassoc]
theorem pullbackLeftIso_hom_snd (g : T ⟶ S) :
    (pullbackLeftIso f f' a ha g).hom ≫ pullback.snd f g = pullback.snd f' g :=
  pullback.lift_snd _ _ _

/-- The isomorphisms `pullbackLeftIso` commute with the maps of pullbacks induced by a map of
the second factors. -/
theorem lift_comp_pullbackLeftIso (g : T ⟶ S) (g' : T' ⟶ S) (m : T' ⟶ T)
    (w' : pullback.fst f' g' ≫ f' = (pullback.snd f' g' ≫ m) ≫ g)
    (w : pullback.fst f g' ≫ f = (pullback.snd f g' ≫ m) ≫ g) :
    pullback.lift (pullback.fst f' g') (pullback.snd f' g' ≫ m) w' ≫
        (pullbackLeftIso f f' a ha g).hom =
      (pullbackLeftIso f f' a ha g').hom ≫
        pullback.lift (pullback.fst f g') (pullback.snd f g' ≫ m) w := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackLeftIso_hom_fst, pullback.lift_fst,
      pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullbackLeftIso_hom_snd, pullbackLeftIso_hom_snd_assoc,
      pullback.lift_snd]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.RelativeDescentSituation

/-! ### Transfer of a descent statement along a bijection of systems -/

/-- **A descent statement transfers along an isomorphism of systems with their cocones.** Given
two directed systems of sets `A`, `B` with maps `cA`, `cB` to vertices `Ainf`, `Binf`, and
bijections `F` at every stage and `Finf` at the vertex commuting with the transition and
comparison maps, every element of `Ainf` comes from a stage and the stages separate eventually
exactly when the same holds for `B`. -/
theorem descent_transfer {ι : Type*} (r : ι → ι → Prop) {A B : ι → Type*} {Ainf Binf : Type*}
    (tA : ∀ {i j}, r i j → A i → A j) (cA : ∀ i, A i → Ainf)
    (tB : ∀ {i j}, r i j → B i → B j) (cB : ∀ i, B i → Binf)
    (F : ∀ i, A i → B i) (Finf : Ainf → Binf) (hF : ∀ i, Function.Bijective (F i))
    (hFinf : Function.Bijective Finf)
    (ht : ∀ {i j} (h : r i j) (x : A i), tB h (F i x) = F j (tA h x))
    (hc : ∀ i (x : A i), cB i (F i x) = Finf (cA i x)) :
    ((∀ y, ∃ i x, cA i x = y) ∧
        ∀ i (x x' : A i), cA i x = cA i x' → ∃ j, ∃ h : r i j, tA h x = tA h x') ↔
      ((∀ y, ∃ i x, cB i x = y) ∧
        ∀ i (x x' : B i), cB i x = cB i x' → ∃ j, ∃ h : r i j, tB h x = tB h x') := by
  constructor
  · rintro ⟨hs, hi⟩
    refine ⟨fun y => ?_, fun i b b' hb => ?_⟩
    · obtain ⟨x0, rfl⟩ := hFinf.surjective y
      obtain ⟨i, x, rfl⟩ := hs x0
      exact ⟨i, F i x, hc i x⟩
    · obtain ⟨a, rfl⟩ := (hF i).surjective b
      obtain ⟨a', rfl⟩ := (hF i).surjective b'
      obtain ⟨j, h, hj⟩ := hi i a a' (hFinf.injective (by rw [← hc, ← hc, hb]))
      exact ⟨j, h, by rw [ht, ht, hj]⟩
  · rintro ⟨hs, hi⟩
    refine ⟨fun y => ?_, fun i a a' ha => ?_⟩
    · obtain ⟨i, b, hb⟩ := hs (Finf y)
      obtain ⟨a, rfl⟩ := (hF i).surjective b
      exact ⟨i, a, hFinf.injective (by rw [← hc, hb])⟩
    · obtain ⟨j, h, hj⟩ := hi i (F i a) (F i a') (by rw [hc, hc, ha])
      exact ⟨j, h, (hF j).injective (by rw [← ht, ← ht, hj])⟩

/-- Precomposition with an isomorphism is a bijection of morphism sets. -/
theorem bijective_precomp_iso {C : Type*} [Category* C] {X X' Y : C} (e : X' ≅ X) :
    Function.Bijective (fun φ : X ⟶ Y => e.hom ≫ φ) :=
  ⟨fun a b h => by simpa using congrArg (e.inv ≫ ·) h, fun ψ => ⟨e.inv ≫ ψ, by simp⟩⟩

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

/-! ### Invariance of the descent of derived morphism sets under isomorphisms of objects -/

/-- **The conclusion of Stacks 0DI7 is invariant under an isomorphism of its first argument.**
Precomposition with the derived pullback of the isomorphism is a bijection at every stage and at
the limit, compatible with the transition and comparison maps. -/
theorem homDescent_of_iso_left
    {K₀ K₀' L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace))}
    (e : K₀ ≅ K₀') (hd : D.HomDescent K₀ L₀) : D.HomDescent K₀' L₀ :=
  (descent_transfer (fun i j : D.LaterIndex => i.1 ≤ j.1)
    (fun h => D.homTransition K₀ L₀ h) (D.homComparison K₀ L₀)
    (fun h => D.homTransition K₀' L₀ h) (D.homComparison K₀' L₀)
    (fun i φ => (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).map e.inv ≫ φ)
    (fun φ => (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).map e.inv ≫ φ)
    (fun i => bijective_precomp_iso
      ((derivedPullback (D.toFixedStage i).toLRSHom.toShHom).mapIso e.symm))
    (bijective_precomp_iso ((derivedPullback D.limitToFixedStage.toLRSHom.toShHom).mapIso e.symm))
    (fun _ φ => Stacks.DerivedPullback.schemeFactorHom_map_comp _ _ _ _ _ _ _ e.inv φ)
    (fun _ φ => Stacks.DerivedPullback.schemeFactorHom_map_comp _ _ _ _ _ _ _ e.inv φ)).1 hd

/-! ### Replacing the fixed stage by an isomorphic scheme -/

/-- **The relative descent situation with `X₀` replaced by `Y`**, a scheme flat and of finite
presentation over `S₀`; the inverse system, its limit and its fixed index are those of `D`. -/
abbrev withX₀ (Y : Over (D.descent.system.obj (op D.descent.base))) (hflat : Flat Y.hom)
    (hfp : FinitePresentation Y.hom) : RelativeDescentSituation.{u, u} I :=
  ⟨D.descent, Y, hflat, hfp⟩

variable (Y : Over (D.descent.system.obj (op D.descent.base))) (hflat : Flat Y.hom)
  (hfp : FinitePresentation Y.hom) (α : Y ≅ D.X₀)

/-- The isomorphism `Y ×_{S₀} Sᵢ ≅ X₀ ×_{S₀} Sᵢ` of the stages induced by `α`, over `Sᵢ`. -/
def withX₀StageIso (i : D.LaterIndex) : (D.withX₀ Y hflat hfp).schemeAt i ≅ D.schemeAt i :=
  Scheme.pullbackLeftIso D.X₀.hom Y.hom ((Over.forget _).mapIso α) (Over.w α.hom) (D.baseMap i)

/-- The isomorphism `Y ×_{S₀} S ≅ X₀ ×_{S₀} S` of the limits induced by `α`, over `S`. -/
def withX₀LimitIso : (D.withX₀ Y hflat hfp).limitScheme ≅ D.limitScheme :=
  Scheme.pullbackLeftIso D.X₀.hom Y.hom ((Over.forget _).mapIso α) (Over.w α.hom)
    (D.descent.limitCone.π.app (op D.descent.base))

/-- `withX₀StageIso` intertwines the projections of the stages to `Y` and to `X₀` via `α`. -/
theorem withX₀StageIso_hom_comp_toFixedStage (i : D.LaterIndex) :
    (D.withX₀StageIso Y hflat hfp α i).hom ≫ D.toFixedStage i =
      (D.withX₀ Y hflat hfp).toFixedStage i ≫ α.hom.left :=
  Scheme.pullbackLeftIso_hom_fst _ _ _ _ _

/-- `withX₀StageIso` is an isomorphism over `Sᵢ`. -/
theorem withX₀StageIso_hom_comp_structureMapAt (i : D.LaterIndex) :
    (D.withX₀StageIso Y hflat hfp α i).hom ≫ D.structureMapAt i =
      (D.withX₀ Y hflat hfp).structureMapAt i :=
  Scheme.pullbackLeftIso_hom_snd _ _ _ _ _

/-- `withX₀LimitIso` intertwines the projections of the limits to `Y` and to `X₀` via `α`. -/
theorem withX₀LimitIso_hom_comp_limitToFixedStage :
    (D.withX₀LimitIso Y hflat hfp α).hom ≫ D.limitToFixedStage =
      (D.withX₀ Y hflat hfp).limitToFixedStage ≫ α.hom.left :=
  Scheme.pullbackLeftIso_hom_fst _ _ _ _ _

/-- `withX₀LimitIso` is an isomorphism over `S`. -/
theorem withX₀LimitIso_hom_comp_structureMapLimit :
    (D.withX₀LimitIso Y hflat hfp α).hom ≫ D.structureMapLimit =
      (D.withX₀ Y hflat hfp).structureMapLimit :=
  Scheme.pullbackLeftIso_hom_snd _ _ _ _ _

/-- The isomorphisms `withX₀StageIso` commute with the transition maps of the stages. -/
theorem transition_comp_withX₀StageIso {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    (D.withX₀ Y hflat hfp).transition h ≫ (D.withX₀StageIso Y hflat hfp α i).hom =
      (D.withX₀StageIso Y hflat hfp α j).hom ≫ D.transition h :=
  Scheme.lift_comp_pullbackLeftIso _ _ _ _ _ _ _ _ _

/-- The isomorphisms `withX₀StageIso` and `withX₀LimitIso` commute with the projections from the
limit to the stages. -/
theorem projection_comp_withX₀StageIso (i : D.LaterIndex) :
    (D.withX₀ Y hflat hfp).projection i ≫ (D.withX₀StageIso Y hflat hfp α i).hom =
      (D.withX₀LimitIso Y hflat hfp α).hom ≫ D.projection i :=
  Scheme.lift_comp_pullbackLeftIso _ _ _ _ _ _ _ _ _

variable (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- The bijection of derived morphism sets at a stage induced by `α`. -/
def withX₀HomStage (i : D.LaterIndex)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L) :
    (derivedPullback ((D.withX₀ Y hflat hfp).toFixedStage i).toLRSHom.toShHom).obj
        ((derivedPullback α.hom.left.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback ((D.withX₀ Y hflat hfp).toFixedStage i).toLRSHom.toShHom).obj
        ((derivedPullback α.hom.left.toLRSHom.toShHom).obj L) :=
  Stacks.DerivedPullback.schemeFactorSquareHom (D.withX₀StageIso Y hflat hfp α i).hom
    (D.toFixedStage i) ((D.withX₀ Y hflat hfp).toFixedStage i) α.hom.left
    (D.withX₀StageIso_hom_comp_toFixedStage Y hflat hfp α i) K L φ

/-- The bijection of derived morphism sets at the limit induced by `α`. -/
def withX₀HomLimit
    (φ : (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj K ⟶
      (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj L) :
    (derivedPullback (D.withX₀ Y hflat hfp).limitToFixedStage.toLRSHom.toShHom).obj
        ((derivedPullback α.hom.left.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback (D.withX₀ Y hflat hfp).limitToFixedStage.toLRSHom.toShHom).obj
        ((derivedPullback α.hom.left.toLRSHom.toShHom).obj L) :=
  Stacks.DerivedPullback.schemeFactorSquareHom (D.withX₀LimitIso Y hflat hfp α).hom
    D.limitToFixedStage (D.withX₀ Y hflat hfp).limitToFixedStage α.hom.left
    (D.withX₀LimitIso_hom_comp_limitToFixedStage Y hflat hfp α) K L φ

/-- The map `withX₀HomStage` of derived morphism sets at a stage is bijective. -/
theorem bijective_withX₀HomStage (i : D.LaterIndex) :
    Function.Bijective (D.withX₀HomStage Y hflat hfp α K L i) :=
  Stacks.DerivedPullback.bijective_schemeFactorSquareHom _ _ _ _
    (D.withX₀StageIso_hom_comp_toFixedStage Y hflat hfp α i) (D.withX₀StageIso Y hflat hfp α i).inv
    (D.withX₀StageIso Y hflat hfp α i).hom_inv_id (D.withX₀StageIso Y hflat hfp α i).inv_hom_id K L

/-- The map `withX₀HomLimit` of derived morphism sets at the limit is bijective. -/
theorem bijective_withX₀HomLimit :
    Function.Bijective (D.withX₀HomLimit Y hflat hfp α K L) :=
  Stacks.DerivedPullback.bijective_schemeFactorSquareHom _ _ _ _
    (D.withX₀LimitIso_hom_comp_limitToFixedStage Y hflat hfp α) (D.withX₀LimitIso Y hflat hfp α).inv
    (D.withX₀LimitIso Y hflat hfp α).hom_inv_id (D.withX₀LimitIso Y hflat hfp α).inv_hom_id K L

/-- The bijections `withX₀HomStage` commute with the transition maps of derived morphism sets. -/
theorem homTransition_withX₀HomStage {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L) :
    (D.withX₀ Y hflat hfp).homTransition _ _ h (D.withX₀HomStage Y hflat hfp α K L i φ) =
      D.withX₀HomStage Y hflat hfp α K L j (D.homTransition K L h φ) :=
  Stacks.DerivedPullback.schemeFactorHom_schemeFactorSquareHom _ _ _ _
    ((D.withX₀ Y hflat hfp).transition h) (D.transition h) _ _ _ _
    (D.withX₀StageIso_hom_comp_toFixedStage Y hflat hfp α j)
    ((D.withX₀ Y hflat hfp).transition_comp_toFixedStage h) (D.transition_comp_toFixedStage h)
    (D.transition_comp_withX₀StageIso Y hflat hfp α h) K L φ

/-- The bijections `withX₀HomStage` and `withX₀HomLimit` commute with the comparison maps from
the stages to the limit. -/
theorem homComparison_withX₀HomStage (i : D.LaterIndex)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L) :
    (D.withX₀ Y hflat hfp).homComparison _ _ i (D.withX₀HomStage Y hflat hfp α K L i φ) =
      D.withX₀HomLimit Y hflat hfp α K L (D.homComparison K L i φ) :=
  Stacks.DerivedPullback.schemeFactorHom_schemeFactorSquareHom _ _ _ _
    ((D.withX₀ Y hflat hfp).projection i) (D.projection i) _ _ _ _
    (D.withX₀LimitIso_hom_comp_limitToFixedStage Y hflat hfp α)
    ((D.withX₀ Y hflat hfp).projection_comp_toFixedStage i) (D.projection_comp_toFixedStage i)
    (D.projection_comp_withX₀StageIso Y hflat hfp α i) K L φ

/-- **Stacks 0DI7 transports along an isomorphism of the fixed stage.** For `α : Y ≅ X₀` over
`S₀`, the derived morphism sets of the derived pullbacks along `α` of `K` and `L` descend in the
situation `D.withX₀ Y` exactly when those of `K` and `L` descend in `D`. -/
theorem homDescent_withX₀_iff :
    (D.withX₀ Y hflat hfp).HomDescent ((derivedPullback α.hom.left.toLRSHom.toShHom).obj K)
        ((derivedPullback α.hom.left.toLRSHom.toShHom).obj L) ↔ D.HomDescent K L :=
  (descent_transfer (fun i j : D.LaterIndex => i.1 ≤ j.1)
    (fun h => D.homTransition K L h) (D.homComparison K L)
    (fun h => (D.withX₀ Y hflat hfp).homTransition _ _ h)
    ((D.withX₀ Y hflat hfp).homComparison _ _)
    (D.withX₀HomStage Y hflat hfp α K L) (D.withX₀HomLimit Y hflat hfp α K L)
    (D.bijective_withX₀HomStage Y hflat hfp α K L) (D.bijective_withX₀HomLimit Y hflat hfp α K L)
    (D.homTransition_withX₀HomStage Y hflat hfp α K L)
    (D.homComparison_withX₀HomStage Y hflat hfp α K L)).symm

/-! ### Quasi-compactness of the stages and of the limit -/

/-- Every stage `Xᵢ` of a relative descent situation is quasi-compact. -/
theorem compactSpace_schemeAt (i : D.LaterIndex) : CompactSpace (D.schemeAt i) := by
  have : QuasiCompact D.X₀.hom := D.finitePresentation.quasiCompact
  have : CompactSpace (D.descent.system.obj (op i.1)) := D.descent.quasiCompact i.1
  exact QuasiCompact.compactSpace_of_compactSpace (D.structureMapAt i)

/-- The limit `X` of a relative descent situation is quasi-compact. -/
theorem compactSpace_limitScheme : CompactSpace D.limitScheme := by
  have : Nonempty I := ⟨D.descent.base⟩
  have : IsFiltered I := isFiltered_of_directed_le_nonempty I
  have : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.descent.system.map f) :=
    fun f => D.descent.transition_affine f
  have : ∀ i : Iᵒᵖ, CompactSpace (D.descent.system.obj i) :=
    fun i => D.descent.quasiCompact i.unop
  have : CompactSpace D.descent.limitCone.pt :=
    Scheme.compactSpace_of_isLimit D.descent.system D.descent.limitCone D.descent.isLimit
  have : QuasiCompact D.X₀.hom := D.finitePresentation.quasiCompact
  exact QuasiCompact.compactSpace_of_compactSpace D.structureMapLimit

/-! ### Essential surjectivity along an isomorphism of the fixed stage -/

/-- For `α : Y ≅ X₀` over `S₀`, if the essential-surjectivity half of Stacks 0DI8 holds for `D`,
then it holds for `D.withX₀ Y`. -/
theorem perfectEssentiallySurjectiveCanonical_withX₀_of (α : Y ≅ D.X₀)
    (hD : D.PerfectEssentiallySurjectiveCanonical) :
    (D.withX₀ Y hflat hfp).PerfectEssentiallySurjectiveCanonical := by
  have := D.flat
  have := D.finitePresentation.locallyOfFinitePresentation
  have := hfp.locallyOfFinitePresentation
  have := D.compactSpace_limitScheme
  intro E' hE'
  let ρ := D.withX₀LimitIso Y hflat hfp α
  have hE : D.structureMapLimit.IsPerfectRelativeTo D.canonicalLimitCertificates
      ((derivedPullback ρ.inv.toLRSHom.toShHom).obj E') :=
    (Scheme.Hom.isPerfectRelativeTo_iso_over_iff (D.withX₀ Y hflat hfp).structureMapLimit
      D.structureMapLimit ρ.symm (by
        rw [Iso.symm_hom, Iso.inv_comp_eq,
          D.withX₀LimitIso_hom_comp_structureMapLimit Y hflat hfp α]) E').2 hE'
  obtain ⟨i, Ei, hEi, ⟨e⟩⟩ := hD _ hE
  have := (D.withX₀ Y hflat hfp).compactSpace_schemeAt i
  let ρi := D.withX₀StageIso Y hflat hfp α i
  refine ⟨i, (derivedPullback ρi.hom.toLRSHom.toShHom).obj Ei,
    (Scheme.Hom.isPerfectRelativeTo_iso_over_iff (D.structureMapAt i)
      ((D.withX₀ Y hflat hfp).structureMapAt i) ρi
      (D.withX₀StageIso_hom_comp_structureMapAt Y hflat hfp α i) Ei).2 hEi, ⟨?_⟩⟩
  exact (Stacks.DerivedPullback.schemeFactorSquareIso ρ.hom (D.projection i)
      ((D.withX₀ Y hflat hfp).projection i) ρi.hom
      (D.projection_comp_withX₀StageIso Y hflat hfp α i).symm).app Ei ≪≫
    (derivedPullback ρ.hom.toLRSHom.toShHom).mapIso e ≪≫
    (Stacks.Cohomology.TorAmplitude.derivedPullbackHomCompInvIso
      (Scheme.forgetToRingedSpace.mapIso ρ.symm)).app E'

/-- **The essential-surjectivity half of Stacks 0DI8 transports along an isomorphism of the fixed
stage.** For `α : Y ≅ X₀` over `S₀`, it holds for `D.withX₀ Y` exactly when it holds for `D`. -/
theorem perfectEssentiallySurjectiveCanonical_withX₀_iff (α : Y ≅ D.X₀) :
    (D.withX₀ Y hflat hfp).PerfectEssentiallySurjectiveCanonical ↔
      D.PerfectEssentiallySurjectiveCanonical :=
  ⟨fun h => (D.withX₀ Y hflat hfp).perfectEssentiallySurjectiveCanonical_withX₀_of D.X₀ D.flat
      D.finitePresentation α.symm h,
    D.perfectEssentiallySurjectiveCanonical_withX₀_of Y hflat hfp α⟩

/-! ### Restrictions to `⊤` and restrictions of restrictions -/

/-- `⊤ ⊆ X₀`, as a scheme over `S₀`, is isomorphic to `X₀`. -/
def restrictTopOverIso (hT : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left)) :
    (D.restrict ⊤ hT).X₀ ≅ D.X₀ :=
  Over.isoMk D.X₀.left.topIso (by simp [restrict])

/-- **Stacks 0DI7 for the restriction to `⊤ ⊆ X₀` is Stacks 0DI7 for the situation itself.** -/
theorem restrictHomDescent_top_iff (hT : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left)) :
    D.RestrictHomDescent K L ⊤ hT ↔ D.HomDescent K L :=
  D.homDescent_withX₀_iff (D.restrict ⊤ hT).X₀ (D.restrict ⊤ hT).flat
    (D.restrict ⊤ hT).finitePresentation (D.restrictTopOverIso hT) K L

/-- **The essential-surjectivity half of Stacks 0DI8 for the restriction to `⊤ ⊆ X₀` is that for
the situation itself.** -/
theorem perfectEssentiallySurjectiveCanonical_restrict_top_iff
    (hT : IsCompact ((⊤ : D.X₀.left.Opens) : Set D.X₀.left)) :
    D.RestrictPerfectEssentiallySurjective ⊤ hT ↔ D.PerfectEssentiallySurjectiveCanonical :=
  D.perfectEssentiallySurjectiveCanonical_withX₀_iff (D.restrict ⊤ hT).X₀ (D.restrict ⊤ hT).flat
    (D.restrict ⊤ hT).finitePresentation (D.restrictTopOverIso hT)

section Nested

variable {U₀ W₀ : D.X₀.left.Opens} (hU₀ : IsCompact (U₀ : Set D.X₀.left))
  (hW₀ : IsCompact (W₀ : Set D.X₀.left))
  (hA : IsCompact ((W₀.ι ⁻¹ᵁ U₀ : (W₀ : Scheme.{u}).Opens) : Set W₀.toScheme))

/-- For opens `U₀ ≤ W₀`, the preimage of `U₀` in `W₀` and `U₀` have the same image in `X₀`. -/
theorem range_preimage_ι_comp_ι (hUW : U₀ ≤ W₀) :
    Set.range ((W₀.ι ⁻¹ᵁ U₀).ι ≫ W₀.ι).base = Set.range U₀.ι.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
    Scheme.Opens.range_ι, Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range,
    Scheme.Opens.range_ι]
  exact Set.inter_eq_left.2 hUW

/-- For quasi-compact opens `U₀ ≤ W₀` of `X₀`, the preimage of `U₀` in `W₀` is isomorphic to `U₀`
over `X₀`. -/
def preimageιIso (hUW : U₀ ≤ W₀) : ((W₀.ι ⁻¹ᵁ U₀ : (W₀ : Scheme.{u}).Opens) : Scheme.{u}) ≅ U₀ :=
  IsOpenImmersion.isoOfRangeEq ((W₀.ι ⁻¹ᵁ U₀).ι ≫ W₀.ι) U₀.ι (D.range_preimage_ι_comp_ι hUW)

/-- `preimageιIso` is an isomorphism over `X₀`. -/
theorem preimageιIso_hom_ι (hUW : U₀ ≤ W₀) :
    (D.preimageιIso hUW).hom ≫ U₀.ι = (W₀.ι ⁻¹ᵁ U₀).ι ≫ W₀.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The restriction of `D.restrict W₀` to the preimage of `U₀`, as a scheme over `S₀`, is
isomorphic to the restriction of `D` to `U₀`. -/
def restrictRestrictOverIso (hUW : U₀ ≤ W₀) :
    ((D.restrict W₀ hW₀).restrict (W₀.ι ⁻¹ᵁ U₀) hA).X₀ ≅ (D.restrict U₀ hU₀).X₀ :=
  Over.isoMk (D.preimageιIso hUW) (by
    simp only [restrict, Over.mk_left, Over.mk_hom]
    rw [← Category.assoc, D.preimageιIso_hom_ι hUW, Category.assoc])

/-- **Stacks 0DI7 for a restriction of a restriction.** For quasi-compact opens `U₀ ≤ W₀` of
`X₀`, the conclusion for `D.restrict W₀` restricted to the preimage of `U₀` holds exactly when it
holds for `D` restricted to `U₀`. -/
theorem restrictHomDescent_restrict_iff (hUW : U₀ ≤ W₀) :
    (D.restrict W₀ hW₀).RestrictHomDescent ((derivedPullback W₀.ι.toLRSHom.toShHom).obj K)
        ((derivedPullback W₀.ι.toLRSHom.toShHom).obj L) (W₀.ι ⁻¹ᵁ U₀) hA ↔
      D.RestrictHomDescent K L U₀ hU₀ := by
  let e : ∀ M : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)),
      (derivedPullback (D.preimageιIso hUW).hom.toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj M) ≅
        (derivedPullback (W₀.ι ⁻¹ᵁ U₀).ι.toLRSHom.toShHom).obj
          ((derivedPullback W₀.ι.toLRSHom.toShHom).obj M) := fun M =>
    (Stacks.DerivedPullback.schemeFactorIso (D.preimageιIso hUW).hom U₀.ι
        ((W₀.ι ⁻¹ᵁ U₀).ι ≫ W₀.ι) (D.preimageιIso_hom_ι hUW)).app M ≪≫
      (Stacks.DerivedPullback.schemeFactorIso (W₀.ι ⁻¹ᵁ U₀).ι W₀.ι
        ((W₀.ι ⁻¹ᵁ U₀).ι ≫ W₀.ι) rfl).symm.app M
  let R := ((D.restrict W₀ hW₀).restrict (W₀.ι ⁻¹ᵁ U₀) hA)
  have key := (D.restrict U₀ hU₀).homDescent_withX₀_iff R.X₀ R.flat R.finitePresentation
    (D.restrictRestrictOverIso hU₀ hW₀ hA hUW)
    ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K)
    ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L)
  have step : ∀ {K₁ K₂ L₁ L₂ : DerivedCategory
      (SheafOfModules.{u} (structureSheafRing R.X₀.left.toRingedSpace))},
      (K₁ ≅ K₂) → (L₁ ≅ L₂) → R.HomDescent K₁ L₁ → R.HomDescent K₂ L₂ :=
    fun eK eL h => R.homDescent_of_iso_left eK (R.homDescent_of_iso _ eL h)
  exact Iff.trans ⟨step (e K).symm (e L).symm, step (e K) (e L)⟩ key

/-- **The essential-surjectivity half of Stacks 0DI8 for a restriction of a restriction.** For
quasi-compact opens `U₀ ≤ W₀` of `X₀`, it holds for `D.restrict W₀` restricted to the preimage of
`U₀` exactly when it holds for `D` restricted to `U₀`. -/
theorem restrictPerfectEssentiallySurjective_restrict_iff (hUW : U₀ ≤ W₀) :
    (D.restrict W₀ hW₀).RestrictPerfectEssentiallySurjective (W₀.ι ⁻¹ᵁ U₀) hA ↔
      D.RestrictPerfectEssentiallySurjective U₀ hU₀ :=
  (D.restrict U₀ hU₀).perfectEssentiallySurjectiveCanonical_withX₀_iff
    ((D.restrict W₀ hW₀).restrict (W₀.ι ⁻¹ᵁ U₀) hA).X₀
    ((D.restrict W₀ hW₀).restrict (W₀.ι ⁻¹ᵁ U₀) hA).flat
    ((D.restrict W₀ hW₀).restrict (W₀.ι ⁻¹ᵁ U₀) hA).finitePresentation
    (D.restrictRestrictOverIso hU₀ hW₀ hA hUW)

end Nested

end AlgebraicGeometry.RelativeDescentSituation

end
