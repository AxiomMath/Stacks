module

public import StacksFrontier.AlgebraicGeometry.Descent.DischargedEtaleDescent

/-!
# An open subspace whose chart preimage is quasi-affine over an affine base is a scheme

Let `G` be a sheaf on the big fppf site with a morphism `π : G ⟶ yoneda a`, let `q : c ⟶ a` be a
surjective étale morphism of the site, and let `g : yoneda U ⟶ G`, `ρ : yoneda U ⟶ yoneda c`
present `yoneda U` as `G ×_a c`. Let `W` be a set of points of `G` whose open subspace pulls back,
cartesianly, to an open `i : b ⟶ U` of the chart. If `b ⟶ c` is a quasi-affine morphism of
schemes, then the open subspace of `G` cut out by `W` is representable.

The argument is the one of
`AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom`, whose third
step derives quasi-affineness of `b ⟶ c` from separatedness and quasi-finiteness (Stacks 02LR);
here quasi-affineness is the hypothesis. The square obtained by pasting exhibits `yoneda b` as the
base change of the open subspace over `yoneda a` along the surjective étale `q`, so the open
subspace is quasi-affine, hence representable, over `yoneda a` by effective descent of
quasi-affine morphisms along surjective étale morphisms
(`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`).

## Main results

* `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom_chart`: the
  statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An open subspace whose preimage in a surjective étale chart is quasi-affine over the chart
of the base is representable.** For a sheaf `G` over `yoneda a`, a surjective étale `q : c ⟶ a`,
a chart `g : yoneda U ⟶ G` presenting `yoneda U` as `G ×_a c`, and a set `W` of points of `G`
whose open subspace pulls back to the open `i : b ⟶ U`, quasi-affineness of the morphism of
schemes `b ⟶ c` makes the open subspace representable. -/
theorem isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom_chart
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {a c : BigFppfOver B S hS} (π : G ⟶ yoneda.obj a) (q : c ⟶ a)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ G} {ρ : yoneda.obj U ⟶ yoneda.obj c}
    (sqg : IsPullback g ρ π (yoneda.map q))
    {W : Set (points B S hS G)} {b : BigFppfOver B S hS} {i : b ⟶ U}
    {k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G W).toFunctor}
    (hsqb : IsPullback k (yoneda.map i) (openSubspaceOfPoints B S hS G W).ι g)
    (hQA : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map (i ≫ yoneda.preimage ρ))) :
    (openSubspaceOfPoints B S hS G W).toFunctor.IsRepresentable := by
  have _hqari := isQuasiAffineHom_respectsIso.{u}
  set ρ₀ : U ⟶ c := yoneda.preimage ρ
  have hρmap : yoneda.map ρ₀ = ρ := Functor.map_preimage _ _
  have hQAp : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map i ≫ ρ) := by
    rw [← hρmap, ← Functor.map_comp]
    exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (i ≫ ρ₀)).2 hQA
  have sqF : IsPullback k (yoneda.map i ≫ ρ)
      ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q) := hsqb.paste_vert sqg
  have hpb := IsPullback.of_hasPullback
    ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q)
  have hV : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.snd ((openSubspaceOfPoints B S hS G W).ι ≫ π) (yoneda.map q)) := by
    rw [← hpb.isoIsPullback_hom_snd _ _ sqF]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hQAp
  exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _
    (presheaf_of_surjectiveEtaleChart
      (isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom B S hS)
      (isSheaf_openSubspaceOfPoints B S hS hG W)
      (BigFppfOver.isSheaf_yoneda_obj B S hS a)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe) hV).rep

end AlgebraicGeometry.Space

end
