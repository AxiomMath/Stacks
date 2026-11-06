module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCover

/-!
# Base change and flat descent of finite étale Galois covers

The torsor condition of `AlgebraicGeometry.FiniteEtaleGaloisCover`, that the comparison map
`G × Y ⟶ Y ×_X Y` be an isomorphism, is compatible with base change: along a cartesian square
whose top map is equivariant, the comparison map of the top cover is the base change of the
comparison map of the bottom one. It therefore passes to every base change, and it descends
along a flat, surjective and quasi-compact base change.

## Main definitions

* `AlgebraicGeometry.FiniteEtaleGaloisCover.baseChange`: the base change of a finite étale Galois
  cover, given that its total space stays connected.

## Main results

* `AlgebraicGeometry.GaloisCoverLimits.galoisCoverComparison_isPullback`: the comparison maps
  of an equivariant cartesian square form a cartesian square.
* `AlgebraicGeometry.GaloisCoverLimits.isIso_galoisCoverComparison_of_isPullback` and
  `AlgebraicGeometry.GaloisCoverLimits.isIso_galoisCoverComparison_of_isPullback_of_flat`:
  ascent and flat descent of the torsor condition.

## References

* [Stacks Project, Section 03SF](https://stacks.math.columbia.edu/tag/03SF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- The comparison map lies over the first projection by the codiagonal. -/
lemma galoisCoverComparison_fst {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) :
    Stacks.Descent.galoisCoverComparison f a ≫ pullback.fst f f =
      Limits.Sigma.desc (fun _ : G ↦ 𝟙 X) := by
  ext σ
  simp only [Stacks.Descent.galoisCoverComparison, Sigma.ι_desc_assoc, pullback.lift_fst,
    Limits.Sigma.ι_desc]

/-- The comparison map lies over the base by the codiagonal followed by the structure map. -/
lemma galoisCoverComparison_fst_comp {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) :
    Stacks.Descent.galoisCoverComparison f a ≫ pullback.fst f f ≫ f =
      Limits.Sigma.desc (fun _ : G ↦ f) := by
  rw [← Category.assoc, galoisCoverComparison_fst]
  ext σ
  simp only [Sigma.ι_desc_assoc, Category.id_comp, Limits.Sigma.ι_desc]

/-- The comparison map of a cover with an action, as a morphism of schemes over the base. -/
def galoisCoverComparisonOver {G : Type v} [Group G] [Finite G] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (a : Gᵐᵒᵖ →* Aut (Over.mk f)) :
    Over.mk (Limits.Sigma.desc (fun _ : G ↦ f)) ⟶ Over.mk (pullback.fst f f ≫ f) :=
  Over.homMk (Stacks.Descent.galoisCoverComparison f a) (galoisCoverComparison_fst_comp f a)

namespace GaloisCoverLimits

variable {W V T S : Scheme.{u}} {p : W ⟶ V} {h : W ⟶ T} {f : V ⟶ S} {q : T ⟶ S}

/-- In a cartesian square `W = V ×_S T`, the self-product `W ×_T W` is the base change of the
self-product `V ×_S V` along `W ⟶ V`. -/
theorem isPullback_pullbackMap_self (H : IsPullback p h f q) :
    IsPullback (pullback.fst h h) (pullback.map h h f f p p q H.w.symm H.w.symm) p
      (pullback.fst f f) := by
  let r := pullback.map h h f f p p q H.w.symm H.w.symm
  have hrs : r ≫ pullback.snd f f = pullback.snd h h ≫ p := pullback.lift_snd _ _ _
  have hrf : r ≫ pullback.fst f f = pullback.fst h h ≫ p := pullback.lift_fst _ _ _
  have ho : IsPullback (r ≫ pullback.snd f f) (pullback.fst h h) f (p ≫ f) := by
    rw [hrs, H.w]
    exact (IsPullback.of_hasPullback h h).flip.paste_horiz H
  exact (ho.of_right hrf (IsPullback.of_hasPullback f f).flip).flip

/-- In a cartesian square `W = V ×_S T` whose top map intertwines an endomorphism `b` of `W`
over `T` with an endomorphism `a` of `V` over `S`, the graph of `b` is the base change of the
graph of `a`. -/
theorem isPullback_lift_id_lift (H : IsPullback p h f q) (a : V ⟶ V) (ha : a ≫ f = f)
    (b : W ⟶ W) (hb : b ≫ h = h) (hab : b ≫ p = p ≫ a) :
    IsPullback (pullback.lift (𝟙 W) b (by rw [Category.id_comp, hb])) p
      (pullback.map h h f f p p q H.w.symm H.w.symm)
      (pullback.lift (𝟙 V) a (by rw [Category.id_comp, ha])) := by
  let r := pullback.map h h f f p p q H.w.symm H.w.symm
  let ga := pullback.lift (𝟙 V) a (by rw [Category.id_comp, ha])
  let gb := pullback.lift (𝟙 W) b (by rw [Category.id_comp, hb])
  have hw : gb ≫ r = p ≫ ga := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp,
        Category.assoc, pullback.lift_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc,
        pullback.lift_snd, hab]
  have ho : IsPullback (gb ≫ pullback.fst h h) p p (ga ≫ pullback.fst f f) := by
    rw [pullback.lift_fst, pullback.lift_fst]
    exact IsPullback.id_horiz p
  exact ho.of_right hw (isPullback_pullbackMap_self H)

/-- **The comparison maps of an equivariant cartesian square form a cartesian square.** If
`W = V ×_S T` and the top map `W ⟶ V` intertwines the actions, then `G × W ⟶ W ×_T W` is the
base change of `G × V ⟶ V ×_S V` along `W ×_T W ⟶ V ×_S V`. -/
theorem galoisCoverComparison_isPullback {G : Type v} [Group G] [Finite G]
    (H : IsPullback p h f q)
    (a : Gᵐᵒᵖ →* Aut (Over.mk f)) (b : Gᵐᵒᵖ →* Aut (Over.mk h))
    (hab : ∀ g, (b g).asIso.hom.left ≫ p = p ≫ (a g).asIso.hom.left) :
    IsPullback (Stacks.Descent.galoisCoverComparison h b)
      (Sigma.desc fun i : G ↦ p ≫ Sigma.ι (fun _ : G ↦ V) i)
      (pullback.map h h f f p p q H.w.symm H.w.symm)
      (Stacks.Descent.galoisCoverComparison f a) := by
  have hu : IsUniversalColimit (Cofan.mk _ (Sigma.ι fun _ : G ↦ V)) :=
    FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _)
  exact hu.isPullback_of_isColimit_left
    (fun g ↦ pullback.lift (𝟙 V) (a (.op g)).asIso.hom.left
      ((Category.id_comp _).trans (Over.w (a (.op g)).asIso.hom).symm))
    (Stacks.Descent.galoisCoverComparison f a)
    (pullback.map h h f f p p q H.w.symm H.w.symm)
    (fun g ↦ pullback.lift (𝟙 W) (b (.op g)).asIso.hom.left
      ((Category.id_comp _).trans (Over.w (b (.op g)).asIso.hom).symm))
    (fun _ ↦ p)
    (fun g ↦ isPullback_lift_id_lift H _ (Over.w (a (.op g)).asIso.hom) _
      (Over.w (b (.op g)).asIso.hom)
      (hab (.op g)))
    (coproductIsCoproduct _) (fun g ↦ by
      show Sigma.ι _ g ≫ Stacks.Descent.galoisCoverComparison f a = _
      exact Sigma.ι_desc _ g)

/-- **The torsor condition passes to base changes.** -/
theorem isIso_galoisCoverComparison_of_isPullback {G : Type v} [Group G] [Finite G]
    (H : IsPullback p h f q)
    (a : Gᵐᵒᵖ →* Aut (Over.mk f)) (b : Gᵐᵒᵖ →* Aut (Over.mk h))
    (hab : ∀ g, (b g).asIso.hom.left ≫ p = p ≫ (a g).asIso.hom.left)
    [IsIso (Stacks.Descent.galoisCoverComparison f a)] :
    IsIso (Stacks.Descent.galoisCoverComparison h b) :=
  MorphismProperty.of_isPullback (P := MorphismProperty.isomorphisms Scheme.{u})
    (galoisCoverComparison_isPullback H a b hab).flip
    (inferInstanceAs (IsIso (Stacks.Descent.galoisCoverComparison f a)))

/-- **The torsor condition descends along a flat, surjective, quasi-compact base change.** -/
theorem isIso_galoisCoverComparison_of_isPullback_of_flat {G : Type v} [Group G] [Finite G]
    [Flat q] [Surjective q] [QuasiCompact q]
    (H : IsPullback p h f q)
    (a : Gᵐᵒᵖ →* Aut (Over.mk f)) (b : Gᵐᵒᵖ →* Aut (Over.mk h))
    (hab : ∀ g, (b g).asIso.hom.left ≫ p = p ≫ (a g).asIso.hom.left)
    [IsIso (Stacks.Descent.galoisCoverComparison h b)] :
    IsIso (Stacks.Descent.galoisCoverComparison f a) := by
  let r := pullback.map h h f f p p q H.w.symm H.w.symm
  have step : ∀ {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange], P q → P r :=
    fun hq ↦ MorphismProperty.of_isPullback (isPullback_pullbackMap_self H)
      (MorphismProperty.of_isPullback H.flip hq)
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (galoisCoverComparison_isPullback H a b hab)
    (show (Surjective r ∧ Flat r) ∧ QuasiCompact r from
      ⟨⟨step (P := @Surjective) ‹_›, step (P := @Flat) ‹_›⟩, step (P := @QuasiCompact) ‹_›⟩)
    (inferInstanceAs (IsIso (Stacks.Descent.galoisCoverComparison h b)))

/-- **The torsor condition is the base change of the bottom one.** In a cartesian square
`W = V ×_S T` whose top map is equivariant, the comparison map `G × W ⟶ W ×_T W` is an
isomorphism exactly when the base change along `T ⟶ S` of the comparison map
`G × V ⟶ V ×_S V`, as a morphism of schemes over `S`, is. -/
theorem isIso_galoisCoverComparison_iff_isIso_pullback_map {G : Type v} [Group G] [Finite G]
    (H : IsPullback p h f q)
    (a : Gᵐᵒᵖ →* Aut (Over.mk f)) (b : Gᵐᵒᵖ →* Aut (Over.mk h))
    (hab : ∀ g, (b g).asIso.hom.left ≫ p = p ≫ (a g).asIso.hom.left) :
    IsIso (Stacks.Descent.galoisCoverComparison h b) ↔
      IsIso ((Over.pullback q).map (galoisCoverComparisonOver f a)).left := by
  let r := pullback.map h h f f p p q H.w.symm H.w.symm
  let ς : (∐ fun _ : G ↦ W) ⟶ ∐ fun _ : G ↦ V :=
    Sigma.desc fun i : G ↦ p ≫ Sigma.ι (fun _ : G ↦ V) i
  have S2 := galoisCoverComparison_isPullback H a b hab
  have Hbig : IsPullback (pullback.fst h h ≫ h) r q (pullback.fst f f ≫ f) :=
    (isPullback_pullbackMap_self H).paste_horiz H.flip
  have HA : IsPullback (Limits.Sigma.desc fun _ : G ↦ h) ς q
      (Limits.Sigma.desc fun _ : G ↦ f) := by
    simpa only [galoisCoverComparison_fst_comp] using S2.paste_horiz Hbig
  let α := HA.flip.isoPullback
  let β := Hbig.flip.isoPullback
  let M := ((Over.pullback q).map (galoisCoverComparisonOver f a)).left
  have hM₁ : M ≫ pullback.fst (pullback.fst f f ≫ f) q =
      pullback.fst (Limits.Sigma.desc fun _ : G ↦ f) q ≫ Stacks.Descent.galoisCoverComparison f a :=
    pullback.lift_fst _ _ _
  have hM₂ : M ≫ pullback.snd (pullback.fst f f ≫ f) q =
      pullback.snd (Limits.Sigma.desc fun _ : G ↦ f) q :=
    pullback.lift_snd _ _ _
  have key : α.hom ≫ M = Stacks.Descent.galoisCoverComparison h b ≫ β.hom := by
    apply pullback.hom_ext
    · dsimp only [Over.mk_hom]
      rw [Category.assoc, hM₁, ← Category.assoc, HA.flip.isoPullback_hom_fst, Category.assoc,
        Hbig.flip.isoPullback_hom_fst]
      exact S2.w.symm
    · dsimp only [Over.mk_hom]
      rw [Category.assoc, hM₂, HA.flip.isoPullback_hom_snd, Category.assoc,
        Hbig.flip.isoPullback_hom_snd, galoisCoverComparison_fst_comp]
  have hc : Stacks.Descent.galoisCoverComparison h b = α.hom ≫ M ≫ β.inv := by
    rw [← Category.assoc, key, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  show _ ↔ IsIso M
  rw [hc, isIso_comp_left_iff, isIso_comp_right_iff]

/-- An equivariant cartesian square of finite étale covers yields an equivariant isomorphism
from the base change. -/
theorem exists_equivariant_iso_of_isPullback {S T : Scheme.{u}} (q : T ⟶ S)
    (A : FiniteEtaleOver S) (B : FiniteEtaleOver T) (n : B.left ⟶ A.left)
    (hn : IsPullback n B.hom A.hom q) {ι : Type*} (α : ι → (A ⟶ A)) (β : ι → (B ⟶ B))
    (hact : ∀ g, (β g).left ≫ n = n ≫ (α g).left) :
    ∃ e : (finiteEtaleBaseChange q).obj A ≅ B,
      ∀ g, (finiteEtaleBaseChange q).map (α g) ≫ e.hom = e.hom ≫ β g := by
  let i : pullback A.hom q ≅ B.left := (IsPullback.of_hasPullback A.hom q).isoIsPullback _ _ hn
  have hi₁ : i.hom ≫ n = pullback.fst A.hom q :=
    (IsPullback.of_hasPullback A.hom q).isoIsPullback_hom_fst _ _ hn
  have hi₂ : i.hom ≫ B.hom = pullback.snd A.hom q :=
    (IsPullback.of_hasPullback A.hom q).isoIsPullback_hom_snd _ _ hn
  refine ⟨MorphismProperty.Over.isoMk i hi₂, fun g ↦ ?_⟩
  apply MorphismProperty.Over.Hom.ext
  let M : pullback A.hom q ⟶ pullback A.hom q := ((finiteEtaleBaseChange q).map (α g)).left
  have hM₁ : M ≫ pullback.fst A.hom q = pullback.fst A.hom q ≫ (α g).left :=
    finiteEtaleBaseChange_map_left_fst q (α g)
  have hM₂ : M ≫ pullback.snd A.hom q = pullback.snd A.hom q :=
    MorphismProperty.Over.w ((finiteEtaleBaseChange q).map (α g))
  show M ≫ i.hom = i.hom ≫ (β g).left
  apply hn.hom_ext
  · rw [Category.assoc, hi₁, hM₁, Category.assoc, hact, ← Category.assoc, hi₁]
  · rw [Category.assoc, hi₂, hM₂, Category.assoc, MorphismProperty.Over.w (β g), hi₂]

/-- An equivariant isomorphism from the base change of a finite étale cover yields an
equivariant cartesian square. -/
theorem exists_equivariant_isPullback_of_iso {S T : Scheme.{u}} (q : T ⟶ S)
    (A : FiniteEtaleOver S) (B : FiniteEtaleOver T) (e : (finiteEtaleBaseChange q).obj A ≅ B)
    {ι : Type*} (α : ι → (A ⟶ A)) (β : ι → (B ⟶ B))
    (he : ∀ g, (finiteEtaleBaseChange q).map (α g) ≫ e.hom = e.hom ≫ β g) :
    ∃ n : B.left ⟶ A.left, IsPullback n B.hom A.hom q ∧
      ∀ g, (β g).left ≫ n = n ≫ (α g).left := by
  let φ : B.left ⟶ pullback A.hom q := e.inv.left
  let φ' : pullback A.hom q ⟶ B.left := e.hom.left
  let i : B.left ≅ pullback A.hom q :=
    { hom := φ
      inv := φ'
      hom_inv_id := congrArg (fun m ↦ m.left) e.inv_hom_id
      inv_hom_id := congrArg (fun m ↦ m.left) e.hom_inv_id }
  have hi₂ : i.hom ≫ pullback.snd A.hom q = B.hom := MorphismProperty.Over.w e.inv
  refine ⟨i.hom ≫ pullback.fst A.hom q, IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, pullback.condition, ← Category.assoc, hi₂]⟩ i rfl hi₂, fun g ↦ ?_⟩
  have he' : e.inv ≫ (finiteEtaleBaseChange q).map (α g) = β g ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← he g, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  let M : pullback A.hom q ⟶ pullback A.hom q := ((finiteEtaleBaseChange q).map (α g)).left
  have hM₁ : M ≫ pullback.fst A.hom q = pullback.fst A.hom q ≫ (α g).left :=
    finiteEtaleBaseChange_map_left_fst q (α g)
  have hl : φ ≫ M = (β g).left ≫ φ := congrArg (fun m ↦ m.left) he'
  show (β g).left ≫ φ ≫ pullback.fst A.hom q = (φ ≫ pullback.fst A.hom q) ≫ (α g).left
  rw [← Category.assoc, ← hl, Category.assoc, hM₁, Category.assoc]

end GaloisCoverLimits

/-- **The base change of a finite étale Galois cover.** Along `q : T ⟶ S`, a finite étale Galois
cover of `S` with group `G` whose base change has connected total space gives a finite étale
Galois cover of `T` with group `G`, acting through base change. -/
def FiniteEtaleGaloisCover.baseChange {S T : Scheme.{u}} (q : T ⟶ S) {G : Type v} [Group G]
    [Finite G] (Z : FiniteEtaleGaloisCover S G)
    (hconn : ConnectedSpace ((finiteEtaleBaseChange q).obj Z.obj).left) :
    FiniteEtaleGaloisCover T G where
  obj := (finiteEtaleBaseChange q).obj Z.obj
  connected := hconn
  action := ((finiteEtaleBaseChange q).mapAut Z.obj).comp Z.action
  comparisonIsIso :=
    GaloisCoverLimits.isIso_galoisCoverComparison_of_isPullback
      (IsPullback.of_hasPullback Z.obj.hom q)
      (((MorphismProperty.Over.forget finiteEtale ⊤ S).mapAut Z.obj).comp Z.action) _
      fun g ↦ finiteEtaleBaseChange_map_left_fst q (Z.action g).asIso.hom

/-- The underlying cover of the base change of a Galois cover is the base change. -/
theorem FiniteEtaleGaloisCover.baseChange_obj {S T : Scheme.{u}} (q : T ⟶ S) {G : Type v}
    [Group G] [Finite G] (Z : FiniteEtaleGaloisCover S G)
    (hconn : ConnectedSpace ((finiteEtaleBaseChange q).obj Z.obj).left) :
    (Z.baseChange q hconn).obj = (finiteEtaleBaseChange q).obj Z.obj :=
  rfl

/-- The projection from the base change of a Galois cover is equivariant. -/
theorem FiniteEtaleGaloisCover.baseChange_action_fst {S T : Scheme.{u}} (q : T ⟶ S) {G : Type v}
    [Group G] [Finite G] (Z : FiniteEtaleGaloisCover S G)
    (hconn : ConnectedSpace ((finiteEtaleBaseChange q).obj Z.obj).left) (g : Gᵐᵒᵖ) :
    ((Z.baseChange q hconn).action g).asIso.hom.left ≫ pullback.fst Z.obj.hom q =
      pullback.fst Z.obj.hom q ≫ (Z.action g).asIso.hom.left :=
  finiteEtaleBaseChange_map_left_fst q (Z.action g).asIso.hom

end AlgebraicGeometry

end
