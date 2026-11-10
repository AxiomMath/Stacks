module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentFunctor
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Full faithfulness of étale descent

Let `f : X ⟶ S` be a morphism of schemes. Pulling back along `f` gives the canonical functor
`AlgebraicGeometry.etaleDescentFunctor f` from schemes étale over `S` to descent data relative
to `f` whose underlying `X`-scheme is étale. This file proves that the functor is faithful when
`f` is surjective, and fully faithful when `f` is submersive and every étale base change of `f`
is submersive.

## Main results

* `AlgebraicGeometry.etaleDescentFunctor_faithful` is faithfulness for a surjective morphism.
* `AlgebraicGeometry.etaleDescentFunctor_fullyFaithful_of_submersive_baseChange` is full
  faithfulness under the submersiveness hypotheses.
* `AlgebraicGeometry.etaleDescentFunctor_fullyFaithful_of_universallyClosed`,
  `AlgebraicGeometry.etaleDescentFunctor_fullyFaithful_of_universallyOpen` and
  `AlgebraicGeometry.etaleDescentFunctor_fullyFaithful_of_quasiCompact_of_flat` are the three
  standard cases: they discharge the submersiveness hypotheses from surjectivity together with
  universal closedness, universal openness, or quasi-compactness and flatness.

Three facts about étale morphisms are also proved:

* `AlgebraicGeometry.isOpenImmersion_of_section_of_etale`: a section of an étale morphism is an
  open immersion.
* `AlgebraicGeometry.eq_of_comp_eq_of_surjective_of_etale`: two morphisms into the source of an
  étale morphism that agree after composing with it and after precomposing with a surjection
  are equal.
* `AlgebraicGeometry.isIso_of_etale_of_isPullback_id`: an étale morphism admitting a section
  after a surjective base change is an isomorphism.

## Implementation notes

Submersiveness is `Topology.IsQuotientMap` on the underlying map, and the base change of `f`
along `g : U ⟶ S` is `CategoryTheory.Limits.pullback.snd f g`.

## References

* [Stacks Project, Tag 0BTJ](https://stacks.math.columbia.edu/tag/0BTJ)
* [Stacks Project, Tag 0BTK](https://stacks.math.columbia.edu/tag/0BTK)
* [Stacks Project, Tag 0BTL](https://stacks.math.columbia.edu/tag/0BTL)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-- A section of an étale morphism is an open immersion. -/
@[ega "IV 17.9.3"]
theorem isOpenImmersion_of_section_of_etale {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p] (s : Y ⟶ X)
    (hs : s ≫ p = 𝟙 Y) : IsOpenImmersion s := by
  have : Etale (s ≫ p) := hs ▸ inferInstance
  have : Etale s := Etale.of_comp s p
  have : IsSplitMono s := ⟨⟨p, hs⟩⟩
  exact IsOpenImmersion.of_flat_of_mono s

/-- Two morphisms into the source of an étale morphism `p` that become equal after composing
with `p` and after precomposing with a surjective morphism are equal. -/
theorem eq_of_comp_eq_of_surjective_of_etale {T Y Z W : Scheme.{u}} (p : T ⟶ Y) [Etale p]
    (q : Z ⟶ W) [Surjective q] (a b : W ⟶ T) (w : a ≫ p = b ≫ p) (h : q ≫ a = q ≫ b) :
    a = b := by
  let d := pullback.diagonal p
  have : IsOpenImmersion d :=
    isOpenImmersion_of_section_of_etale (pullback.fst p p) d (by simp [d])
  let c := pullback.lift a b w
  have hc : q ≫ c = (q ≫ a) ≫ d := by
    apply pullback.hom_ext
    · simp only [c, d, Category.assoc, pullback.lift_fst, pullback.diagonal_fst,
        Category.comp_id]
    · simp only [c, d, Category.assoc, pullback.lift_snd, pullback.diagonal_snd,
        Category.comp_id]
      exact h.symm
  have hrange : Set.range c ⊆ Set.range d := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := q.surjective x
    exact ⟨a (q z), congrArg (fun k : Z ⟶ pullback p p => k z) hc.symm⟩
  have h₁ := IsOpenImmersion.lift_fac d c hrange =≫ pullback.fst p p
  have h₂ := IsOpenImmersion.lift_fac d c hrange =≫ pullback.snd p p
  simp only [c, d, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
    Category.comp_id, pullback.lift_fst, pullback.lift_snd] at h₁ h₂
  exact h₁.symm.trans h₂

/-- An étale morphism which, after base change along a surjective morphism, admits a section
splitting the base change square, is an isomorphism. -/
theorem isIso_of_etale_of_isPullback_id {X Y Z : Scheme.{u}} (p : X ⟶ Y) [Etale p] (q : Z ⟶ Y)
    [Surjective q] (s : Z ⟶ X) (h : IsPullback s (𝟙 Z) p q) : IsIso p := by
  have : Mono p := ⟨by
    intro T a b w
    let v := pullback.fst (a ≫ p) q
    apply eq_of_comp_eq_of_surjective_of_etale p v a b w
    have ha : (v ≫ a) ≫ p = pullback.snd (a ≫ p) q ≫ q := by
      simpa [v, Category.assoc] using (pullback.condition (f := a ≫ p) (g := q))
    have hb : (v ≫ b) ≫ p = pullback.snd (a ≫ p) q ≫ q := by
      simpa only [Category.assoc, ← w] using ha
    have h₁ := h.lift_fst (v ≫ a) (pullback.snd (a ≫ p) q) ha
    have h₂ := h.lift_fst (v ≫ b) (pullback.snd (a ≫ p) q) hb
    have he : h.lift (v ≫ a) (pullback.snd (a ≫ p) q) ha =
        h.lift (v ≫ b) (pullback.snd (a ≫ p) q) hb := by
      simpa using (h.lift_snd (v ≫ a) (pullback.snd (a ≫ p) q) ha).trans
        (h.lift_snd (v ≫ b) (pullback.snd (a ≫ p) q) hb).symm
    exact h₁.symm.trans ((congrArg (fun k => k ≫ s) he).trans h₂)⟩
  have : IsOpenImmersion p := IsOpenImmersion.of_flat_of_mono p
  refine (isIso_iff_isOpenImmersion_and_surjective p).mpr ⟨inferInstance, ⟨fun y => ?_⟩⟩
  obtain ⟨z, rfl⟩ := q.surjective y
  exact ⟨s z, congrArg (fun k : Z ⟶ Y => k z) (by simpa using h.w)⟩

variable {X S : Scheme.{u}}

/-- Pullback to a surjective scheme detects equality of morphisms
between étale schemes over the base. -/
@[stacks 0BTJ]
theorem etaleDescentFunctor_faithful (f : X ⟶ S) [Surjective f] :
    (etaleDescentFunctor f).Faithful where
  map_injective {U V} {a b} h := by
    have hpb : (Over.pullback f).map ((Scheme.Etale.forget S).map a) =
        (Over.pullback f).map ((Scheme.Etale.forget S).map b) := by
      have h1 := congrArg (fun k => k.hom) h
      dsimp [etaleDescentFunctor] at h1
      have h2 := congrArg (fun φ => φ.hom ()) h1
      dsimp [DescentData.canonicalFunctor] at h2
      have key := fun c : (Scheme.Etale.forget S).obj U ⟶ (Scheme.Etale.forget S).obj V =>
        (DescentData.pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)).map
          ((DescentData.trivialFunctor S).map c)
      have hA := key ((Scheme.Etale.forget S).map a)
      rw [h2, ← key ((Scheme.Etale.forget S).map b)] at hA
      exact (cancel_epi _).1 hA
    have hcomp := congrArg
      (fun k : (Over.pullback f).obj ((Scheme.Etale.forget S).obj U) ⟶
          (Over.pullback f).obj ((Scheme.Etale.forget S).obj V) =>
        k.left ≫ pullback.fst ((Scheme.Etale.forget S).obj V).hom f) hpb
    simp only [Over.pullback_map_left, pullback.lift_fst] at hcomp
    have : Surjective (pullback.fst V.hom f) := inferInstance
    have hleft : ((Scheme.Etale.forget S).map a).left =
        ((Scheme.Etale.forget S).map b).left :=
      eq_of_comp_eq_of_surjective_of_etale V.hom (pullback.fst U.hom f) _ _
        (((Scheme.Etale.forget S).map a).w.trans ((Scheme.Etale.forget S).map b).w.symm) hcomp
    exact (Scheme.Etale.forget S).map_injective (Over.OverMorphism.ext hleft)

/-- Conjugating a product of morphisms in `Over S` by the identification of a binary product
with a fibre product gives the corresponding map of fibre products. -/
theorem prodLeftIsoPullback_inv_prodMap_left {A B C D : Over S} (a : A ⟶ C) (b : B ⟶ D) :
    (Over.prodLeftIsoPullback A B).inv ≫ (prod.map a b).left ≫
        (Over.prodLeftIsoPullback C D).hom =
      pullback.map A.hom B.hom C.hom D.hom a.left b.left (𝟙 S) (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst, pullback.lift_fst]
    rw [← Over.comp_left, prod.map_fst, Over.comp_left]
    simp
  · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd, pullback.lift_snd]
    rw [← Over.comp_left, prod.map_snd, Over.comp_left]
    simp

namespace DescentData

/-- Compatibility of a morphism of descent data with the gluing isomorphisms, read on the
fibre products of schemes rather than on binary products in `Over S`. -/
theorem hom_comm_gluingPullbackIso (f : X ⟶ S)
    {D E : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ f)} (φ : D ⟶ E) :
    pullback.map ((D.obj ()).hom ≫ f) f ((E.obj ()).hom ≫ f) f (φ.hom ()).left (𝟙 X) (𝟙 S)
          (by simp) (by simp) ≫ (E.gluingPullbackIso () ()).hom =
      (D.gluingPullbackIso () ()).hom ≫
        pullback.map f ((D.obj ()).hom ≫ f) f ((E.obj ()).hom ≫ f) (𝟙 X) (φ.hom ()).left (𝟙 S)
          (by simp) (by simp) := by
  let A := (Over.map f).obj (D.obj ())
  let B := Over.mk f
  let C := (Over.map f).obj (E.obj ())
  have h := congrArg
    (fun e : A ⨯ B ⟶ B ⨯ C =>
      (Over.prodLeftIsoPullback A B).inv ≫ e.left ≫ (Over.prodLeftIsoPullback B C).hom)
    (φ.comm () ())
  have hs := prodLeftIsoPullback_inv_prodMap_left ((Over.map f).map (φ.hom ())) (𝟙 B)
  have ht := prodLeftIsoPullback_inv_prodMap_left (𝟙 B) ((Over.map f).map (φ.hom ()))
  have hs' :
      pullback.map ((D.obj ()).hom ≫ f) f ((E.obj ()).hom ≫ f) f (φ.hom ()).left (𝟙 X) (𝟙 S)
          (by simp) (by simp) =
      (Over.prodLeftIsoPullback A B).inv ≫
        (prod.map ((Over.map f).map (φ.hom ())) (𝟙 B)).left ≫
          (Over.prodLeftIsoPullback C B).hom := by
    simpa [A, B, C] using hs.symm
  have ht' :
      pullback.map f ((D.obj ()).hom ≫ f) f ((E.obj ()).hom ≫ f) (𝟙 X) (φ.hom ()).left (𝟙 S)
          (by simp) (by simp) =
      (Over.prodLeftIsoPullback B A).inv ≫
        (prod.map (𝟙 B) ((Over.map f).map (φ.hom ()))).left ≫
          (Over.prodLeftIsoPullback B C).hom := by
    simpa [A, B, C] using ht.symm
  rw [hs', ht']
  simpa [gluingPullbackIso, A, B, C] using h

/-- The second projection of the target of the gluing isomorphism, followed by the structure
morphism, is the first projection of its source. -/
theorem gluingPullbackIso_hom_snd_structureMap (f : X ⟶ S)
    (D : DescentData (S := S) (X := fun _ : Unit ↦ X) (fun _ ↦ f)) :
    (D.gluingPullbackIso () ()).hom ≫ pullback.snd f ((D.obj ()).hom ≫ f) ≫ (D.obj ()).hom =
      pullback.snd ((D.obj ()).hom ≫ f) f := by
  simp only [gluingPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.forget_map,
    Category.assoc]
  have he := congrArg Over.Hom.left (D.gluing_hom_snd_structureMap () ())
  simp only [Over.comp_left] at he
  have hp := Over.prodLeftIsoPullback_hom_snd (Over.mk f) ((Over.map f).obj (D.obj ()))
  change ((Over.mk f).prodLeftIsoPullback ((Over.map f).obj (D.obj ()))).hom ≫
    pullback.snd f ((D.obj ()).hom ≫ f) = Over.Hom.left prod.snd at hp
  rw [reassoc_of% hp]
  change (((Over.map f).obj (D.obj ())).prodLeftIsoPullback (Over.mk f)).inv ≫
    Over.Hom.left (Over.Hom.left (D.gluing () ()).hom) ≫
      Over.Hom.left prod.snd ≫ Over.Hom.left (structureMap f (D.obj ())) = _
  rw [he]
  exact Over.prodLeftIsoPullback_inv_snd _ _

/-- On the canonical descent datum of an `S`-scheme, the gluing isomorphism exchanges the two
projections, read in the coordinates supplied by the pullback functor. -/
theorem canonical_gluingPullbackIso_hom_snd_fst (f : X ⟶ S)
    (P : PullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)) (U : Over S) :
    let D := (trivialFunctor S).obj U
    ((P.functor.obj D).gluingPullbackIso () ()).hom ≫
        pullback.snd f (((P.functor.obj D).obj ()).hom ≫ f) ≫
          (P.objIso D).hom.left ≫ pullback.fst U.hom f =
      pullback.fst (((P.functor.obj D).obj ()).hom ≫ f) f ≫
        (P.objIso D).hom.left ≫ pullback.fst U.hom f := by
  dsimp only
  let D := (trivialFunctor S).obj U
  have htriv :
      (D.gluingPullbackIso () ()).hom ≫ pullback.snd (𝟙 S) ((D.obj ()).hom ≫ 𝟙 S) =
        pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S) := by
    simp only [gluingPullbackIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Over.forget_map, Category.assoc]
    have hp := Over.prodLeftIsoPullback_hom_snd (Over.mk (𝟙 S))
      ((Over.map (𝟙 S)).obj (D.obj ()))
    change (((Over.mk (𝟙 S)).prodLeftIsoPullback ((Over.map (𝟙 S)).obj (D.obj ()))).hom ≫
        pullback.snd (𝟙 S) ((D.obj ()).hom ≫ 𝟙 S) = Over.Hom.left prod.snd) at hp
    rw [hp]
    have hb : Over.Hom.left (Over.Hom.left (D.gluing () ()).hom) ≫ Over.Hom.left prod.snd =
        Over.Hom.left prod.fst := by
      have hcat :
          (D.gluing () ()).hom.left ≫
              (prod.snd : Over.mk (𝟙 S) ⨯ ((Over.map (𝟙 S)).obj (D.obj ())) ⟶
                (Over.map (𝟙 S)).obj (D.obj ())) =
            (prod.fst : ((Over.map (𝟙 S)).obj (D.obj ())) ⨯ Over.mk (𝟙 S) ⟶
              (Over.map (𝟙 S)).obj (D.obj ())) := by
        simp [D, trivialFunctor]
      simpa only [Over.comp_left] using congrArg Over.Hom.left hcat
    rw [hb]
    have hi := Over.prodLeftIsoPullback_inv_fst ((Over.map (𝟙 S)).obj (D.obj ()))
      (Over.mk (𝟙 S))
    change (((Over.map (𝟙 S)).obj (D.obj ())).prodLeftIsoPullback (Over.mk (𝟙 S))).inv ≫
        Over.Hom.left prod.fst = pullback.fst ((D.obj ()).hom ≫ 𝟙 S) (𝟙 S) at hi
    exact hi
  have h := congrArg (fun k => k ≫ pullback.snd (𝟙 S) ((D.obj ()).hom ≫ 𝟙 S)) (P.gluing D)
  simp only [Category.assoc, P.targetMap_snd] at h
  rw [htriv] at h
  rw [P.sourceMap_fst D] at h
  simpa [D, trivialFunctor, gluingPullbackIso] using h

end DescentData

/-- Étale descent is fully faithful when the morphism and all its
étale base changes are submersive. -/
@[stacks 0BTK, sga "1 IX 3.4" "fully faithful"]
theorem etaleDescentFunctor_fullyFaithful_of_submersive_baseChange (f : X ⟶ S)
    (hf : Topology.IsQuotientMap f)
    (hbase : ∀ {U : Scheme.{u}} (g : U ⟶ S), Etale g →
      Topology.IsQuotientMap (pullback.snd f g)) :
    Nonempty (etaleDescentFunctor f).FullyFaithful := by
  classical
  let F := etaleDescentFunctor f
  have : Surjective f := ⟨hf.surjective⟩
  have : F.Faithful := etaleDescentFunctor_faithful f
  let : F.Full := ⟨by
    intro U V m
    let G := Scheme.Etale.forget S
    let T := DescentData.trivialFunctor S
    let P := DescentData.pullbackFunctor (𝟙 S) f (𝟙 S) f (by simp)
    let D := T.obj (G.obj U)
    let E := T.obj (G.obj V)
    let α := m.hom
    change (P.functor.obj D) ⟶ (P.functor.obj E) at α
    let U₁ := G.obj U
    let U₂ := G.obj V
    let g₁ := U₁.hom
    let g₂ := U₂.hom
    let aOver : (Over.pullback f).obj U₁ ⟶ (Over.pullback f).obj U₂ :=
      (P.objIso D).inv ≫ α.hom () ≫ (P.objIso E).hom
    have haOver : aOver.left ≫ pullback.snd g₂ f = pullback.snd g₁ f := by
      simpa [aOver] using aOver.w
    let B := pullback g₁ g₂
    let pB := pullback.fst g₁ g₂
    let gB := pB ≫ g₁
    let V₁ := pullback g₁ f
    let gamma : V₁ ⟶ B := pullback.lift (pullback.fst g₁ f)
      (aOver.left ≫ pullback.fst g₂ f)
      (by simp only [pullback.condition, ← haOver, Category.assoc])
    have hgammaFst : gamma ≫ pB = pullback.fst g₁ f := pullback.lift_fst _ _ _
    let Vtot := pullback gB f
    let qB := pullback.fst gB f
    let r : V₁ ⟶ Vtot := pullback.lift gamma (pullback.snd g₁ f) (by
      dsimp only [gB]
      rw [← Category.assoc, hgammaFst, pullback.condition])
    let eAssoc := pullbackRightPullbackFstIso g₁ f pB
    let pV : Vtot ⟶ V₁ := eAssoc.inv ≫ pullback.snd pB (pullback.fst g₁ f)
    have hrFst : r ≫ qB = gamma := pullback.lift_fst _ _ _
    have hrSnd : r ≫ pullback.snd gB f = pullback.snd g₁ f := pullback.lift_snd _ _ _
    have hpVFst : pV ≫ pullback.fst g₁ f = qB ≫ pB := by
      dsimp [pV, eAssoc, qB]
      rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]
    have hpVSnd : pV ≫ pullback.snd g₁ f = pullback.snd gB f := by
      dsimp [pV, eAssoc]
      rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
    have hr : r ≫ pV = 𝟙 V₁ := by
      apply pullback.hom_ext
      · simp [hpVFst, reassoc_of% hrFst, hgammaFst]
      · simp [hpVSnd, hrSnd]
    have : Etale g₁ := U.2
    have : Etale g₂ := V.2
    have hEtaleB : Etale gB := Etale.etale_comp pB g₁
    have hqB : Topology.IsQuotientMap qB := by
      have heq : (fun z : Vtot => pullback.snd f gB ((pullbackSymmetry f gB).inv z)) = qB :=
        funext fun z => congrArg (fun k : Vtot ⟶ B => k z) (pullbackSymmetry_inv_comp_snd f gB)
      exact heq ▸ (hbase gB hEtaleB).comp (pullbackSymmetry f gB).inv.homeomorph.isQuotientMap
    have : Etale pV := by
      dsimp only [pV]
      infer_instance
    have hrOpen : IsOpenImmersion r := isOpenImmersion_of_section_of_etale pV r hr
    have hcompat := DescentData.hom_comm_gluingPullbackIso f α
    have hDcoord := DescentData.canonical_gluingPullbackIso_hom_snd_fst f P U₁
    have hEcoord :
        ((P.functor.obj E).gluingPullbackIso () ()).hom ≫
            pullback.snd f (((P.functor.obj E).obj ()).hom ≫ f) ≫
              (P.objIso E).hom.left ≫ pullback.fst g₂ f =
          pullback.fst (((P.functor.obj E).obj ()).hom ≫ f) f ≫
            (P.objIso E).hom.left ≫ pullback.fst g₂ f :=
      DescentData.canonical_gluingPullbackIso_hom_snd_fst f P U₂
    have hcompatCoord :
        pullback.fst (((P.functor.obj D).obj ()).hom ≫ f) f ≫
            (α.hom ()).left ≫ (P.objIso E).hom.left ≫ pullback.fst g₂ f =
          ((P.functor.obj D).gluingPullbackIso () ()).hom ≫
            pullback.snd f (((P.functor.obj D).obj ()).hom ≫ f) ≫
              (α.hom ()).left ≫ (P.objIso E).hom.left ≫ pullback.fst g₂ f := by
      have h := congrArg
        (fun k => k ≫ pullback.snd f (((P.functor.obj E).obj ()).hom ≫ f) ≫
          (P.objIso E).hom.left ≫ pullback.fst g₂ f) hcompat
      simp only [Category.assoc] at h
      rw [hEcoord] at h
      dsimp only [pullback.map] at h
      simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc] using h
    have hinv : ∀ {T₀ : Scheme.{u}} (x y : T₀ ⟶ V₁),
        x ≫ pullback.fst g₁ f = y ≫ pullback.fst g₁ f →
        x ≫ aOver.left ≫ pullback.fst g₂ f = y ≫ aOver.left ≫ pullback.fst g₂ f := by
      intro T₀ x y hxy
      let e := (P.objIso D)
      let d := ((P.functor.obj D).obj ()).hom
      have heh : e.hom.left ≫ pullback.snd g₁ f = d := e.hom.w
      have hei : e.inv.left ≫ d = pullback.snd g₁ f := e.inv.w
      let k : T₀ ⟶ pullback (d ≫ f) f :=
        pullback.lift (x ≫ e.inv.left) (y ≫ pullback.snd g₁ f) (by
          rw [Category.assoc, ← Category.assoc e.inv.left, hei, ← pullback.condition,
            ← Category.assoc, hxy, Category.assoc, pullback.condition, ← Category.assoc])
      let l := k ≫ ((P.functor.obj D).gluingPullbackIso () ()).hom ≫ pullback.snd f (d ≫ f)
      have hl : l ≫ e.hom.left = y := by
        apply pullback.hom_ext
        · change k ≫ ((P.functor.obj D).gluingPullbackIso () ()).hom ≫
              pullback.snd f (d ≫ f) ≫ e.hom.left ≫ pullback.fst g₁ f =
            y ≫ pullback.fst g₁ f
          rw [hDcoord]
          change k ≫ pullback.fst (d ≫ f) f ≫ e.hom.left ≫ pullback.fst g₁ f = _
          have hk : k ≫ pullback.fst (d ≫ f) f = x ≫ e.inv.left := pullback.lift_fst _ _ _
          rw [reassoc_of% hk]
          rw [← Category.assoc e.inv.left, ← Over.comp_left, Iso.inv_hom_id, Over.id_left,
            Category.id_comp]
          exact hxy
        · change k ≫ ((P.functor.obj D).gluingPullbackIso () ()).hom ≫
              pullback.snd f (d ≫ f) ≫ e.hom.left ≫ pullback.snd g₁ f =
            y ≫ pullback.snd g₁ f
          rw [heh, DescentData.gluingPullbackIso_hom_snd_structureMap]
          exact pullback.lift_snd _ _ _
      have hle : l = y ≫ e.inv.left := by
        rw [← hl]
        simp [Category.assoc, ← Over.comp_left]
      have hc' := congrArg (fun t => k ≫ t) hcompatCoord
      change (k ≫ pullback.fst (d ≫ f) f) ≫ (α.hom ()).left ≫
          (P.objIso E).hom.left ≫ pullback.fst g₂ f =
        l ≫ (α.hom ()).left ≫ (P.objIso E).hom.left ≫ pullback.fst g₂ f at hc'
      rw [hle] at hc'
      simpa [k, aOver, e, Category.assoc, pullback.lift_fst_assoc] using hc'
    let v := pullback.fst gamma qB
    let z := pullback.snd gamma qB
    let b := z ≫ pV
    have hvb : v ≫ pullback.fst g₁ f = b ≫ pullback.fst g₁ f := by
      rw [show b ≫ pullback.fst g₁ f = z ≫ qB ≫ pB by
        dsimp [b]; rw [Category.assoc, hpVFst]]
      rw [← Category.assoc, ← pullback.condition, Category.assoc, hgammaFst]
    have hv : v ≫ gamma = z ≫ qB := pullback.condition
    have hb : b ≫ r = z := by
      apply pullback.hom_ext
      · change b ≫ r ≫ qB = z ≫ qB
        rw [hrFst]
        apply pullback.hom_ext
        · have hv' : v ≫ pullback.fst g₁ f = z ≫ qB ≫ pB := by
            simpa only [Category.assoc, hgammaFst] using congrArg (fun k => k ≫ pB) hv
          change b ≫ gamma ≫ pB = z ≫ qB ≫ pB
          rw [hgammaFst]
          exact hvb.symm.trans hv'
        · have he := congrArg (fun k => k ≫ pullback.snd g₁ g₂) hv
          simp only [gamma, Category.assoc, pullback.lift_snd] at he ⊢
          exact (hinv v b hvb).symm.trans he
      · change b ≫ r ≫ pullback.snd gB f = z ≫ pullback.snd gB f
        rw [hrSnd]
        dsimp [b]
        rw [Category.assoc, hpVSnd]
    have hsaturated : ∀ x y : Vtot, qB x = qB y →
        (x ∈ (r.opensRange : Set Vtot) ↔ y ∈ (r.opensRange : Set Vtot)) := by
      suffices H : ∀ x y : Vtot, qB x = qB y →
          x ∈ (r.opensRange : Set Vtot) → y ∈ (r.opensRange : Set Vtot) from
        fun x y h => ⟨H x y h, H y x h.symm⟩
      intro x y hxy hx
      obtain ⟨t, rfl⟩ := hx
      have he : gamma t = qB y := by
        rw [← hrFst]
        exact hxy
      obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback t y he
      exact ⟨b w, (congrArg (fun k => k w) hb).trans hw₂⟩
    obtain ⟨O₀, hO₀open, hO₀⟩ :=
      Stacks.Etale.exists_isOpen_preimage_eq_of_isQuotientMap hqB
        ((Stacks.Etale.preimage_pullback_fst_eq_preimage_pullback_snd_iff qB
          (r.opensRange : Set Vtot)).mpr hsaturated) r.opensRange.2
    let O : B.Opens := ⟨O₀, hO₀open⟩
    have hO : qB ⁻¹ᵁ O = r.opensRange := TopologicalSpace.Opens.ext hO₀
    have hgammaRange : Set.range gamma ⊆ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      have ht : r t ∈ qB ⁻¹' O₀ := by
        rw [hO₀]
        exact ⟨t, rfl⟩
      have hgt : qB (r t) = gamma t := by
        simpa using congrArg (fun k : V₁ ⟶ B => k t) hrFst
      exact hgt ▸ ht
    let s := IsOpenImmersion.lift O.ι gamma hgammaRange
    have hs : s ≫ O.ι = gamma := IsOpenImmersion.lift_fac _ _ _
    have hgraph : IsPullback s r O.ι qB :=
      IsOpenImmersion.isPullback s r O.ι qB (hrFst.trans hs.symm) (by simpa using hO)
    have hV : IsPullback qB pV pB (pullback.fst g₁ f) := by
      apply IsPullback.of_bot (v₂₁ := pullback.snd g₁ f) (v₂₂ := g₁)
      · rw [hpVSnd]
        exact IsPullback.of_hasPullback gB f
      · exact hpVFst.symm
      · exact IsPullback.of_hasPullback g₁ f
    let p := O.ι ≫ pB
    have : Etale p := by
      dsimp [p, pB]
      infer_instance
    have hsection : IsPullback s (𝟙 V₁) p (pullback.fst g₁ f) := by
      simpa only [hr] using hgraph.paste_vert hV
    have : IsIso p := isIso_of_etale_of_isPullback_id p (pullback.fst g₁ f) s hsection
    let a := inv p ≫ O.ι ≫ pullback.snd g₁ g₂
    have ha : a ≫ g₂ = g₁ := by
      dsimp [a]
      rw [Category.assoc, Category.assoc, ← pullback.condition, ← Category.assoc O.ι]
      change inv p ≫ p ≫ g₁ = g₁
      simp
    have hs' : pullback.fst g₁ f ≫ inv p = s := by
      rw [← cancel_mono p]
      simpa using hsection.w.symm
    have ha' : pullback.fst g₁ f ≫ a = aOver.left ≫ pullback.fst g₂ f := by
      dsimp [a]
      rw [← Category.assoc, ← Category.assoc, hs', hs]
      exact pullback.lift_snd _ _ _
    let aS : U₁ ⟶ U₂ := Over.homMk a ha
    have haS : (Over.pullback f).map aS = aOver := by
      apply Over.OverMorphism.ext
      apply pullback.hom_ext
      · simpa [aS, pullback.lift_fst] using ha'
      · simpa [aS, pullback.lift_snd] using haOver.symm
    let aEt : U ⟶ V := G.preimage aS
    refine ⟨aEt, ?_⟩
    apply ObjectProperty.hom_ext
    apply DescentData.hom_ext
    intro i
    cases i
    have hm := P.map (T.map aS)
    change (P.objIso D).hom ≫ (Over.pullback f).map aS =
      (P.functor.map (T.map aS)).hom () ≫ (P.objIso E).hom at hm
    rw [haS] at hm
    have hm' : (P.functor.map (T.map aS)).hom () = α.hom () := by
      rw [← cancel_mono (P.objIso E).hom, ← hm]
      simp [aOver]
    change (P.functor.map (T.map (G.map aEt))).hom () = α.hom ()
    simpa [aEt] using hm'⟩
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

/-- Étale descent along a
surjective universally closed morphism is fully faithful. -/
@[stacks 0BTL "universally_closed", sga "1 IX 6.9" "fully faithful half"]
theorem etaleDescentFunctor_fullyFaithful_of_universallyClosed (f : X ⟶ S) [Surjective f]
    [UniversallyClosed f] : Nonempty (etaleDescentFunctor f).FullyFaithful :=
  etaleDescentFunctor_fullyFaithful_of_submersive_baseChange f
    (f.isClosedMap.isQuotientMap f.continuous f.surjective)
    fun g _ => (pullback.snd f g).isClosedMap.isQuotientMap (pullback.snd f g).continuous
      (pullback.snd f g).surjective

/-- Étale descent along a
surjective universally open morphism is fully faithful. -/
@[stacks 0BTL "universally_open"]
theorem etaleDescentFunctor_fullyFaithful_of_universallyOpen (f : X ⟶ S) [Surjective f]
    [UniversallyOpen f] : Nonempty (etaleDescentFunctor f).FullyFaithful :=
  etaleDescentFunctor_fullyFaithful_of_submersive_baseChange f
    (f.isOpenMap.isQuotientMap f.continuous f.surjective)
    fun g _ => (pullback.snd f g).isOpenMap.isQuotientMap (pullback.snd f g).continuous
      (pullback.snd f g).surjective

/-- Étale descent along a
surjective quasi-compact flat morphism is fully faithful. -/
@[stacks 0BTL "quasi_compact_flat"]
theorem etaleDescentFunctor_fullyFaithful_of_quasiCompact_of_flat (f : X ⟶ S) [Surjective f]
    [QuasiCompact f] [Flat f] : Nonempty (etaleDescentFunctor f).FullyFaithful :=
  etaleDescentFunctor_fullyFaithful_of_submersive_baseChange f (Flat.isQuotientMap_of_surjective f)
    fun g _ => Flat.isQuotientMap_of_surjective (pullback.snd f g)

end AlgebraicGeometry

end
