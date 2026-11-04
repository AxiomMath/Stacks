module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffinePullbackPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSource
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts

/-!
# Affine source of a representable affine morphism (Stacks 0AKP, part (1)): the refined forms

The set-theoretic condition of Stacks 0AIS on an fppf sheaf passes from the target of a
relatively representable morphism of fppf sheaves to its source.

## Main results

* `satisfiesSetTheoreticCondition_of_relativelyRepresentable`: if `f : X ⟶ Y` is relatively
  representable and `Y` satisfies the set-theoretic condition, then so does `X`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

/-- Given a pullback square `a, t` of `f` along `p'`, and a pullback `V` of `f` along
`q' ≫ pullback.fst p' p' ≫ p'`, the induced map from `V` to the kernel pair of `a` exhibits `V`
as the pullback of that kernel pair along `q'`. -/
private theorem isPullback_lift_kernelPair_of_isPullback {C : Type*} [Category C]
    {X Y T U R V : C} {f : X ⟶ Y} {p' : U ⟶ Y} {a : T ⟶ X} {t : T ⟶ U}
    (hpb : IsPullback a t f p') [HasPullback p' p'] [HasPullback a a]
    (q' : R ⟶ pullback p' p') {vX : V ⟶ X} {vR : V ⟶ R}
    (hV : IsPullback vX vR f (q' ≫ pullback.fst p' p' ≫ p')) :
    IsPullback
      (pullback.lift (hpb.lift vX (vR ≫ q' ≫ pullback.fst p' p') (by simp [hV.w]))
        (hpb.lift vX (vR ≫ q' ≫ pullback.snd p' p') (by simp [hV.w, pullback.condition]))
        (by rw [hpb.lift_fst, hpb.lift_fst]))
      vR
      (pullback.lift (pullback.fst a a ≫ t) (pullback.snd a a ≫ t)
        (by simp only [Category.assoc, ← hpb.w, pullback.condition_assoc]))
      q' := by
  refine IsPullback.mk' (pullback.hom_ext (by simp) (by simp)) ?_ ?_
  · intro Z φ ψ hφ hψ
    refine hV.hom_ext ?_ hψ
    simpa using congrArg (· ≫ pullback.fst a a ≫ a) hφ
  · intro Z cK cR hc
    have hc₁ := congrArg (· ≫ pullback.fst p' p') hc
    have hc₂ := congrArg (· ≫ pullback.snd p' p') hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at hc₁ hc₂
    have hx : (cK ≫ pullback.fst a a ≫ a) ≫ f = cR ≫ q' ≫ pullback.fst p' p' ≫ p' := by
      simp only [Category.assoc, hpb.w, ← reassoc_of% hc₁]
    refine ⟨hV.lift _ cR hx, pullback.hom_ext (hpb.hom_ext ?_ ?_) (hpb.hom_ext ?_ ?_), by simp⟩
    · simp
    · simpa using hc₁.symm
    · simp [pullback.condition]
    · simpa using hc₂.symm

/-- A base change of an epimorphism of fppf sheaves, read off a cartesian square, is an
epimorphism. -/
private theorem epi_of_isPullback {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P X Y Z : FppfSheaf B S hS} {f' : P ⟶ X} {g' : P ⟶ Y} {g : X ⟶ Z} {f : Y ⟶ Z}
    (sq : IsPullback f' g' g f) (hg : Epi g) : Epi g' := by
  have := Sheaf.epi_pullback_snd g f hg
  rw [← sq.isoPullback_hom_snd]
  infer_instance

/-- The set-theoretic condition of **Stacks 0AIS** passes to the source of a *relatively
representable* morphism of fppf sheaves: a representable surjection onto the target, and a
representable surjection onto its kernel pair, base change to the same data over the source.

Only relative representability is used; no property of the represented base changes — in
particular no affineness — enters, which is why the hypothesis is
`CategoryTheory.Functor.relativelyRepresentable` rather than a relative morphism property. -/
theorem satisfiesSetTheoreticCondition_of_relativelyRepresentable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : Functor.relativelyRepresentable
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f)
    (hY : SatisfiesSetTheoreticCondition B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS X := by
  let J := BigFppfOver.topology B S hS
  let G := Sheaf.sheafifiedYoneda J
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  obtain ⟨U, R, hU, hR, hUrep, hRrep, p, hp, q, hq⟩ := hY
  let F := sheafToPresheaf J (Type (u + 1))
  let eU : hU ≅ G.obj U :=
    (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
      (Classical.choice hUrep ≪≫ (F.mapIso (eG.app U)).symm)
  let eR : hR ≅ G.obj R :=
    (Functor.FullyFaithful.ofFullyFaithful F).preimageIso
      (Classical.choice hRrep ≪≫ (F.mapIso (eG.app R)).symm)
  let p' : G.obj U ⟶ Y := eU.inv ≫ p
  let q' : G.obj R ⟶ pullback p' p' :=
    eR.inv ≫ q ≫ pullback.map p p p' p' eU.hom eU.hom (𝟙 Y)
      (by simp [p']) (by simp [p'])
  have hp' : Epi p' := by
    dsimp [p']
    infer_instance
  have hq' : Epi q' := by
    dsimp [q']
    infer_instance
  let hrep : Functor.relativelyRepresentable G f := hf
  have hpb := hrep.isPullback p'
  have hsq := isPullback_lift_kernelPair_of_isPullback hpb q'
    (hrep.isPullback (q' ≫ pullback.fst p' p' ≫ p'))
  exact ⟨_, _, _, _, ⟨F.mapIso (eG.app (hrep.pullback p'))⟩,
    ⟨F.mapIso (eG.app (hrep.pullback (q' ≫ pullback.fst p' p' ≫ p')))⟩, _,
    epi_of_isPullback hpb.flip hp', _, epi_of_isPullback hsq.flip hq'⟩

end AlgebraicGeometry.FormalSpace

end
