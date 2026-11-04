module

public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.RelationSize

/-!
# The chapter's convention along a monomorphic comparison of inverse systems

Let `t : E ⟶ D` be a morphism of cofiltered inverse systems of presheaves on the big fppf site of
`S`, where `D` has affine transition morphisms and satisfies the chapter's standing convention of
Section 70.2 (tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`. If for every
transition `j ⟶ i` the comparison `E_j ⟶ E_i ×_{D_i} D_j` is a monomorphism, then `E` satisfies the
convention too: for an affine test object `Z` with a point `Z ⟶ E_i`, the base changes
`Z ×_{E_i} E_k` embed into the base changes `Z ×_{D_i} D_k` along the composite point
`Z ⟶ E_i ⟶ D_i`, compatibly in `k`, so the limit of the underlying schemes of the former has a
monomorphism to the limit of the latter, which lies in the site, and so lies in the site itself
(`AlgebraicGeometry.BigFppfSite.contains_of_mono`).

This applies to systems of closed subspaces of base changes of `D`, such as the fibre squares
`U_i ×_{Y_i} U_i` of the image systems of Stacks 0CP9.

## Main results

* `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits.of_mono_lift`.

## References

* [Stacks Project, Tag 07SD](https://stacks.math.columbia.edu/tag/07SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The chapter's convention passes along a monomorphic comparison.** Let `t : E ⟶ D` be a
morphism of cofiltered inverse systems of presheaves, `D` with affine transition morphisms and
satisfying the convention of Section 70.2. If every comparison `E_j ⟶ E_i ×_{D_i} D_j`, for
`f : j ⟶ i`, is a monomorphism, then `E` satisfies the convention. -/
theorem SiteContainsBaseChangeLimits.of_mono_lift {I : Type u} [Category.{u} I] [IsCofiltered I]
    {D E : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hD : SiteContainsBaseChangeLimits B S hS D)
    (hDaff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (t : E ⟶ D)
    (hmono : ∀ {j i : I} (f : j ⟶ i),
      Mono (pullback.lift (E.map f) (t.app j) (t.naturality f) :
        E.obj j ⟶ pullback (t.app i) (D.map f))) :
    SiteContainsBaseChangeLimits B S hS E := by
  intro i Z g W eW c hc
  -- the base changes of the stages of `D` along `Z ⟶ E_i ⟶ D_i`, lifted to the affine site
  let gD := g ≫ t.app i
  let F := BigAffineFppf.inclusion B S hS ⋙ yoneda
  let ED := (Over.post (X := i) D ⋙ Over.pullback gD) ⋙
    Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))
  have hess : ∀ k : Over i, F.essImage (ED.obj k) := fun k => by
    obtain ⟨A, _, _, hpb⟩ := hDaff k.hom Z gD
    exact ⟨A, ⟨hpb.isoPullback⟩⟩
  let WD := Functor.essImage.liftFunctor ED F hess
  let eWD : WD ⋙ F ≅ ED := Functor.essImage.liftFunctorCompIso ED F hess
  have hLD : BigFppfOver.LimitInSite (WD ⋙ BigAffineFppf.inclusion B S hS) := hD i Z gD WD eWD
  -- the comparison of the two diagrams of base changes, in presheaves
  let α : ∀ k : Over i, pullback (E.map k.hom) g ⟶ pullback (D.map k.hom) gD := fun k =>
    pullback.map _ _ _ _ (t.app k.left) (𝟙 _) (t.app i) (t.naturality k.hom) (by simp [gD])
  have hα : ∀ k : Over i, Mono (α k) := by
    intro k
    refine ⟨fun {T} a b h => ?_⟩
    have h₁ := congrArg (· ≫ pullback.fst _ _) h
    have h₂ := congrArg (· ≫ pullback.snd _ _) h
    simp only [Category.assoc, α, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at h₁ h₂
    have _ := hmono k.hom
    have hfst : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _ := by
      refine (cancel_mono (pullback.lift (E.map k.hom) (t.app k.left) (t.naturality k.hom))).1 ?_
      refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.lift_fst]
        rw [pullback.condition, ← Category.assoc, h₂, Category.assoc, ← pullback.condition]
      · simpa only [Category.assoc, pullback.lift_snd] using h₁
    exact pullback.hom_ext hfst h₂
  have hnat : ∀ {k k' : Over i} (φ : k ⟶ k'),
      (pullback.lift (pullback.fst (E.map k.hom) g ≫ E.map φ.left) (pullback.snd _ _)
          (by rw [Category.assoc, ← E.map_comp, Over.w φ, pullback.condition]) :
          pullback (E.map k.hom) g ⟶ pullback (E.map k'.hom) g) ≫ α k' =
        α k ≫ (pullback.lift (pullback.fst (D.map k.hom) gD ≫ D.map φ.left) (pullback.snd _ _)
          (by rw [Category.assoc, ← D.map_comp, Over.w φ, pullback.condition]) :
          pullback (D.map k.hom) gD ⟶ pullback (D.map k'.hom) gD) := by
    intro k k' φ
    apply pullback.hom_ext
    · simp only [α, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [NatTrans.naturality]
    · simp only [α, pullback.map, Category.assoc, pullback.lift_snd, Category.comp_id]
  let αN : (Over.post (X := i) E ⋙ Over.pullback g) ⋙
      Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z)) ⟶ ED :=
    { app := α
      naturality _ _ φ := hnat φ }
  -- the comparison in the affine site
  have hF : F.FullyFaithful := .comp (.ofFullyFaithful _) Yoneda.fullyFaithful
  let βN : W ⟶ WD := (hF.whiskeringRight (Over i)).preimage (eW.hom ≫ αN ≫ eWD.inv)
  have hFβ : ∀ k : Over i, F.map (βN.app k) = eW.hom.app k ≫ α k ≫ eWD.inv.app k := fun k =>
    NatTrans.congr_app ((hF.whiskeringRight (Over i)).map_preimage (eW.hom ≫ αN ≫ eWD.inv)) k
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  have hβmono : ∀ k : Over i, Mono ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (βN.app k))) := by
    intro k
    have : Mono (yoneda.map ((BigAffineFppf.inclusion B S hS).map (βN.app k))) := by
      change Mono (F.map (βN.app k))
      rw [hFβ]
      have h₁ : Mono (eWD.inv.app k) := inferInstanceAs (Mono (eWD.app k).inv)
      have h₂ : Mono (eW.hom.app k) := inferInstanceAs (Mono (eW.app k).hom)
      exact @mono_comp _ _ _ _ _ _ h₂ _ (@mono_comp _ _ _ _ _ (α k) (hα k) _ h₁)
    have : Mono ((BigAffineFppf.inclusion B S hS).map (βN.app k)) :=
      (yoneda (C := BigFppfOver B S hS)).mono_of_mono_map this
    infer_instance
  -- the limit of the schemes of the base changes of `D`, inside the site
  have hWDaff : ∀ k, IsAffine ((underlyingDiagram (WD ⋙ BigAffineFppf.inclusion B S hS)).obj k) :=
    fun k => (WD.obj k).property
  have := CofilteredLimit.hasLimit_of_isAffine
    (underlyingDiagram (WD ⋙ BigAffineFppf.inclusion B S hS))
  have hLc : B.Contains (limit (underlyingDiagram (WD ⋙ BigAffineFppf.inclusion B S hS))) :=
    hLD _ (limit.isLimit _)
  -- the induced morphism of limits is a monomorphism
  let β' : underlyingDiagram (W ⋙ BigAffineFppf.inclusion B S hS) ⟶
      underlyingDiagram (WD ⋙ BigAffineFppf.inclusion B S hS) :=
    Functor.whiskerRight (Functor.whiskerRight βN (BigAffineFppf.inclusion B S hS))
      (BigFppfOver.toScheme B S hS)
  let m := limit.lift _ ((Cone.postcompose β').obj c)
  have hm : Mono m := by
    refine ⟨fun {T} x y hxy => hc.hom_ext fun k => ?_⟩
    have := hβmono k
    refine (cancel_mono ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (βN.app k)))).1 ?_
    simpa [m, β'] using congrArg (· ≫ limit.π _ k) hxy
  exact B.contains_of_mono m hLc

end AlgebraicGeometry.Space

end
