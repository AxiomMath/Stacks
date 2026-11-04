module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.PointsSheaf

/-!
# Fibre products of spectra over `T'`

The spectrum of a pushout of small algebras over `T'` is a fibre product in the big fppf site
(`AlgebraicGeometry.Stack.GroupoidLift.isPullback_specOverMap_of_isPushout`). This is the geometric
input of the descent of an object along `Spec C' ⟶ T'` from a lift of the descent arrow with an
exact cocycle: the double and triple overlaps of the covering are `Spec (C' ⊗ C')` and
`Spec (C' ⊗ C' ⊗ C')`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.isPullback_specOverMap_of_isPushout`.
-/

@[expose] public section

open CategoryTheory Opposite Limits
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- **The spectrum of a pushout is a fibre product over `T'`.** -/
theorem isPullback_specOverMap_of_isPushout {N N₁ N₂ N₃ : SmallAlg (ringOf B S hS T') B.cutoff}
    (f₁ : N ⟶ N₁) (f₂ : N ⟶ N₂) (i₁ : N₁ ⟶ N₃) (i₂ : N₂ ⟶ N₃)
    (hpush : IsPushout (CommRingCat.ofHom (f₁.hom.hom : N.obj →+* N₁.obj))
      (CommRingCat.ofHom (f₂.hom.hom : N.obj →+* N₂.obj))
      (CommRingCat.ofHom (i₁.hom.hom : N₁.obj →+* N₃.obj))
      (CommRingCat.ofHom (i₂.hom.hom : N₂.obj →+* N₃.obj))) :
    IsPullback (specOverMap i₁) (specOverMap i₂) (specOverMap f₁) (specOverMap f₂) := by
  have hpb := isPullback_SpecMap_of_isPushout _ _ _ _ hpush
  have hw : specOverMap i₁ ≫ specOverMap f₁ = specOverMap i₂ ≫ specOverMap f₂ :=
    BigFppfOver.map_toScheme_injective B S hS (by
      simp only [Functor.map_comp, toScheme_map_specOverMap]
      exact hpb.w)
  let lift : ∀ s : PullbackCone (specOverMap f₁) (specOverMap f₂), s.pt ⟶ specOver N₃ := fun s =>
    let q₁ : (BigFppfOver.toScheme B S hS).obj s.pt ⟶ Spec (CommRingCat.of N₁.obj) :=
      (BigFppfOver.toScheme B S hS).map s.fst
    let q₂ : (BigFppfOver.toScheme B S hS).obj s.pt ⟶ Spec (CommRingCat.of N₂.obj) :=
      (BigFppfOver.toScheme B S hS).map s.snd
    have hp' : q₁ ≫ Spec.map (CommRingCat.ofHom (f₁.hom.hom : N.obj →+* N₁.obj)) =
        q₂ ≫ Spec.map (CommRingCat.ofHom (f₂.hom.hom : N.obj →+* N₂.obj)) := by
      have h := congrArg (fun k ↦ (BigFppfOver.toScheme B S hS).map k) s.condition
      simp only [Functor.map_comp, toScheme_map_specOverMap] at h
      exact h
    have hw₁ : q₁ ≫ specToBase N₁ ≫ B.inclusion.map T'.hom = B.inclusion.map s.pt.hom := by
      have h := congrArg (fun k ↦ B.inclusion.map k) (Over.w s.fst)
      simp only [Functor.map_comp] at h
      exact h
    have hbase : hpb.lift _ _ hp' ≫ specToBase N₃ ≫ B.inclusion.map T'.hom =
        B.inclusion.map s.pt.hom := by
      calc hpb.lift _ _ hp' ≫ specToBase N₃ ≫ B.inclusion.map T'.hom
          = hpb.lift _ _ hp' ≫ (Spec.map (CommRingCat.ofHom (i₁.hom.hom : N₁.obj →+* N₃.obj)) ≫
              specToBase N₁) ≫ B.inclusion.map T'.hom := by rw [specMap_comp_specToBase]
        _ = (hpb.lift _ _ hp' ≫ Spec.map (CommRingCat.ofHom
              (i₁.hom.hom : N₁.obj →+* N₃.obj))) ≫ specToBase N₁ ≫ B.inclusion.map T'.hom := by
            simp only [Category.assoc]
        _ = B.inclusion.map s.pt.hom := by rwa [hpb.lift_fst]
    BigFppfOver.homMk B S hS (contains_spec N₃) _ (hpb.lift _ _ hp') hbase
  have fac₁ : ∀ s, lift s ≫ specOverMap i₁ = s.fst := fun s => by
    apply BigFppfOver.map_toScheme_injective B S hS
    dsimp only
    rw [Functor.map_comp, toScheme_map_specOverMap]
    exact hpb.lift_fst _ _ _
  have fac₂ : ∀ s, lift s ≫ specOverMap i₂ = s.snd := fun s => by
    apply BigFppfOver.map_toScheme_injective B S hS
    dsimp only
    rw [Functor.map_comp, toScheme_map_specOverMap]
    exact hpb.lift_snd _ _ _
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ hw)
    (PullbackCone.IsLimit.mk hw lift fac₁ fac₂ (fun s m h₁ h₂ => ?_))
  apply BigFppfOver.map_toScheme_injective B S hS
  dsimp only
  apply hpb.hom_ext
  · have e := congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) (h₁.trans (fac₁ s).symm)
    simp only [Functor.map_comp, toScheme_map_specOverMap] at e
    exact e
  · have e := congrArg (fun k => (BigFppfOver.toScheme B S hS).map k) (h₂.trans (fac₂ s).symm)
    simp only [Functor.map_comp, toScheme_map_specOverMap] at e
    exact e

end AlgebraicGeometry.Stack.GroupoidLift

end
