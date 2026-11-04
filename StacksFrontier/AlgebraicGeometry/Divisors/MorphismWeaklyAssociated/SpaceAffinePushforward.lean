module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Weakly associated points of an affine direct image on algebraic spaces

Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over a scheme `S` of a big fppf site
`B` and let `F` be a quasi-coherent `𝒪_X`-module. Stacks 0CU2 asserts the inclusion
`WeakAss(f_*F) ⊆ |f|(WeakAss(F))`. We prove it for an arbitrary target, granted the same
inclusion for an affine morphism whose target is the algebraic space of an affine scheme of the
site.

## Main definitions

* `AlgebraicGeometry.Space.SchemeTargetAffinePushforwardWeaklyAssociatedImage` is Stacks 0CU2
  restricted to a target represented by an affine scheme of the site.

## Main results

* `AlgebraicGeometry.Space.affinePushforwardWeaklyAssociatedImage` is **Stacks 0CU2** for an
  arbitrary target, granted that restriction.

## References

* [Stacks Project, Tag 0CU2](https://stacks.math.columbia.edu/tag/0CU2)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
* [Stacks Project, Tag 05EX](https://stacks.math.columbia.edu/tag/05EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CU2 for a target represented by an affine scheme of the site**, as a proposition:
for every affine morphism `g : X ⟶ V` of algebraic spaces whose target is the algebraic space
of an affine scheme `V` of the big fppf site, and every quasi-coherent `𝒪_X`-module `H`, each
weakly associated point of `g_*H` is the image of a weakly associated point of `H`. -/
def SchemeTargetAffinePushforwardWeaklyAssociatedImage : Prop :=
  ∀ (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS} (g : X ⟶ schemeSpace V),
    IsAffine ((BigFppfOver.toScheme B S hS).obj V) → IsAffineHom B S hS g.hom →
      ∀ H : Modules.{u, u} B S hS X.1 X.2, H.IsQuasicoherentOnSite →
        weaklyAssociatedPoints B S hS (schemeSpace V)
            ((modulePushforward B S hS g).obj H) ⊆
          pointsMap B S hS X.1 g.hom '' weaklyAssociatedPoints B S hS X H

/-- Let `f : X ⟶ Y` be an affine morphism of algebraic spaces over `S` and let `F` be a
quasi-coherent `𝒪_X`-module. Granted the hypothesis `h`, the same inclusion for a target
represented by an affine scheme of the site, every weakly associated point of `f_*F` is the
image of a weakly associated point of `F`. -/
@[stacks 0CU2 "the reduction to a target represented by an affine scheme of the site, which is \
the hypothesis h; that case needs the comparison of the Zariski and small-étale modules of a \
represented algebraic space, absent here"]
theorem affinePushforwardWeaklyAssociatedImage
    (h : SchemeTargetAffinePushforwardWeaklyAssociatedImage B S hS) :
    AffinePushforwardWeaklyAssociatedImage B S hS := by
  intro X Y f hf F hF y hy
  obtain ⟨V, b, hV, hb, v, hv⟩ := exists_affine_etale_chart_at_point B S hS Y.1 Y.2 y
  let c : schemeSpace V ⟶ Y := ObjectProperty.homMk b
  have hc : IsEtale B S hS c.hom := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hb
  have hwV : IsWeaklyAssociatedPoint B S hS (schemeSpace V)
      ((etaleModulePullback B S hS c hc).obj ((modulePushforward B S hS f).obj F)) v :=
    (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS c hc _ v).2 (hv ▸ hy)
  let X' := AlgebraicSpaces.fiberProduct B S hS c f
  let f' : X' ⟶ schemeSpace V := ObjectProperty.homMk (pullback.fst c.hom f.hom)
  let i : X' ⟶ X := ObjectProperty.homMk (pullback.snd c.hom f.hom)
  have sq : IsPullback i f' f c := (AlgebraicSpaces.isPullback_fiberProduct B S hS c f).flip
  have hiEt : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i c f sq.flip hc
  have hf' : IsAffineHom B S hS f'.hom :=
    isAffineHom_of_isPullback ((IsPullback.of_hasPullback c.hom f.hom).flip) hf
  have hwX' : IsWeaklyAssociatedPoint B S hS (schemeSpace V)
      ((modulePushforward B S hS f').obj ((etaleModulePullback B S hS i hiEt).obj F)) v :=
    (isWeaklyAssociatedPoint_congr B S hS
      ((modulePushforwardEtaleBaseChangeIso B S hS i f' f c sq hc).app F) v).2 hwV
  obtain ⟨x, hx, hxv⟩ := h V f' hV hf' _
    (isQuasicoherentOnSite_etaleModulePullback B S hS i hiEt F hF) hwX'
  refine ⟨pointsMap B S hS X'.1 i.hom x,
    (isWeaklyAssociatedPoint_etaleModulePullback_iff B S hS i hiEt F x).1 hx, ?_⟩
  rwa [← pointsMap_comp_apply,
    show i.hom ≫ f.hom = f'.hom ≫ c.hom from congrArg (fun k => k.hom) sq.w,
    pointsMap_comp_apply, hxv]

/-- The general statement of Stacks 0CU2 implies its case of a target represented by an affine
scheme of the site. -/
theorem schemeTargetAffinePushforwardWeaklyAssociatedImage_of_affine
    (h : AffinePushforwardWeaklyAssociatedImage B S hS) :
    SchemeTargetAffinePushforwardWeaklyAssociatedImage B S hS :=
  fun _ _ g _ hg H hH ↦ h g hg H hH

end AlgebraicGeometry.Space

end
