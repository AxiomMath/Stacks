module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# An equality of kernel ideal sheaves is local on an open cover of the target

Let `g₁ : Y₁ ⟶ X` and `g₂ : Y₂ ⟶ X` be quasi-compact morphisms of schemes, and let `X` be covered
by the ranges of a family of open immersions `iV k : V k ⟶ X`. This file proves that

`g₁.ker = g₂.ker`

as soon as the two morphisms pulled back to each `V k` have the same kernel. It then packages the
consequence for closed immersions: two closed immersions into `X` with the same kernel are
isomorphic over `X`.

This is the `ker`-level analogue of the affine-local transfer principle
`Stacks.AlgebraicGeometry.Tag07ZGMorphism.of_forall_chart`, which transfers a *morphism
property* that is Zariski-local at the target. A kernel ideal sheaf is not a morphism property,
so that principle does not apply to it; what replaces `IsZariskiLocalAtTarget` here is Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.ext_of_iSup_eq_top`, an equality of ideal sheaves being
tested on a family of *affine* opens covering `X`.

## Main definitions

* `Stacks.AlgebraicGeometry.KerChart.isoOfKerEq`: **two closed immersions with the same kernel are
  isomorphic over their common target.**

## Main results

* `Stacks.AlgebraicGeometry.KerChart.ideal_ker_eq_of_isPullback`: if the two morphisms restricted
  to an open `V` have the same kernel, their kernel ideal sheaves agree on every affine open of
  `X` coming from an affine open of `V`.
* `Stacks.AlgebraicGeometry.KerChart.ker_eq_of_forall_chart`: **the reduction to an open cover.**
* `Stacks.AlgebraicGeometry.KerChart.isoOfKerEq_hom_comp`: the isomorphism is one over the target.

## The route

Mathlib's `AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion` computes the
kernel ideal sheaf of a restricted morphism on an affine open `T` of `V`: it is the ideal sheaf of
the unrestricted morphism at the affine open `iV ''ᵁ T` of `X`, pulled back along the isomorphism
`Γ(X, iV ''ᵁ T) ≅ Γ(V, T)` that the open immersion gives. The two ideals of `X` are therefore
compared through one and the same ring isomorphism, and an ideal is recovered from its contraction
along a surjection by `Ideal.map_comap_of_surjective`.

The affine opens `iV ''ᵁ T`, as `k` ranges over the cover and `T` over the affine opens of `V k`,
do cover `X`: the affine opens of each `V k` cover it (`AlgebraicGeometry.iSup_affineOpens_eq_top`),
images under an open immersion commute with suprema (`…Scheme.Hom.image_iSup`), and the image of
`⊤` is the range. So `ext_of_iSup_eq_top` applies at the index type `Σ k, (V k).affineOpens`.

For the closed-immersion packaging nothing has to be built: Mathlib's
`AlgebraicGeometry.IsClosedImmersion.lift` is the comparison morphism and
`…IsClosedImmersion.isIso_lift` says it is an isomorphism when the kernels agree.

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)

## Not done here

No Stacks tag is claimed: nothing here is a statement of the Stacks project, only a locality
principle used in the proof of Tag 0801.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.AlgebraicGeometry.KerChart

universe u

/-! ### The comparison on one open of the cover -/

/-- **The kernel ideal sheaves agree on the affine opens coming from one open of the cover.** Both
sides are computed by `AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion` as the
contraction, along one and the same ring isomorphism, of the kernel of the restricted morphism. -/
public theorem ideal_ker_eq_of_isPullback {X Y₁ Y₂ V W₁ W₂ : Scheme.{u}}
    (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X) [QuasiCompact g₁] [QuasiCompact g₂]
    (iV : V ⟶ X) [IsOpenImmersion iV]
    (f₁ : W₁ ⟶ V) (iW₁ : W₁ ⟶ Y₁) (H₁ : IsPullback f₁ iW₁ iV g₁)
    (f₂ : W₂ ⟶ V) (iW₂ : W₂ ⟶ Y₂) (H₂ : IsPullback f₂ iW₂ iV g₂)
    (hker : f₁.ker = f₂.ker) (T : V.affineOpens) :
    g₁.ker.ideal ⟨iV ''ᵁ T.1, T.2.image_of_isOpenImmersion iV⟩ =
      g₂.ker.ideal ⟨iV ''ᵁ T.1, T.2.image_of_isOpenImmersion iV⟩ := by
  have e₁ := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g₁ f₁ iW₁ iV H₁ T
  have e₂ := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion g₂ f₂ iW₂ iV H₂ T
  exact Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (iV.appIso T.1).inv).2 (by rw [← e₁, ← e₂, hker])

/-! ### The reduction to an open cover -/

/-- **An equality of kernel ideal sheaves reduces to an open cover of the target.** If `X` is
covered by the ranges of a family of open immersions and the two morphisms pulled back to each
member of the family have the same kernel, then the two morphisms have the same kernel. -/
public theorem ker_eq_of_forall_chart {X Y₁ Y₂ : Scheme.{u}} (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X)
    [QuasiCompact g₁] [QuasiCompact g₂] {ι : Type*} {V W₁ W₂ : ι → Scheme.{u}}
    (iV : (k : ι) → V k ⟶ X) [∀ k, IsOpenImmersion (iV k)]
    (f₁ : (k : ι) → W₁ k ⟶ V k) (iW₁ : (k : ι) → W₁ k ⟶ Y₁)
    (H₁ : ∀ k, IsPullback (f₁ k) (iW₁ k) (iV k) g₁)
    (f₂ : (k : ι) → W₂ k ⟶ V k) (iW₂ : (k : ι) → W₂ k ⟶ Y₂)
    (H₂ : ∀ k, IsPullback (f₂ k) (iW₂ k) (iV k) g₂)
    (hcov : (⨆ k, (iV k).opensRange) = ⊤)
    (hker : ∀ k, (f₁ k).ker = (f₂ k).ker) :
    g₁.ker = g₂.ker := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun p : (k : ι) × (V k).affineOpens =>
      ⟨iV p.1 ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion (iV p.1)⟩) ?_ ?_
  · refine top_le_iff.1 ?_
    rw [← hcov]
    refine iSup_le fun k => ?_
    rw [← Scheme.Hom.image_top_eq_opensRange, ← AlgebraicGeometry.iSup_affineOpens_eq_top (V k),
      Scheme.Hom.image_iSup]
    exact iSup_le fun T => le_iSup_of_le ⟨k, T⟩ le_rfl
  · rintro ⟨k, T⟩
    exact ideal_ker_eq_of_isPullback g₁ g₂ (iV k) (f₁ k) (iW₁ k) (H₁ k) (f₂ k) (iW₂ k) (H₂ k)
      (hker k) T

/-! ### Closed immersions with the same kernel -/

/-- **Two closed immersions into the same scheme with the same kernel are isomorphic over it.**
This is `AlgebraicGeometry.IsClosedImmersion.isIso_lift`, packaged as an isomorphism; it is what
turns an equality of kernel ideal sheaves into an identification of closed subschemes. -/
public def isoOfKerEq {X Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (h : i₁.ker = i₂.ker) : Z₂ ≅ Z₁ :=
  @asIso _ _ _ _ _ (IsClosedImmersion.isIso_lift i₁ i₂ h)

/-- The identification of two closed immersions with the same kernel is one over their common
target. -/
@[reassoc]
public theorem isoOfKerEq_hom_comp {X Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (h : i₁.ker = i₂.ker) :
    (isoOfKerEq i₁ i₂ h).hom ≫ i₁ = i₂ :=
  IsClosedImmersion.lift_fac i₁ i₂ h.le

/-! ### Transporting an equality of kernels along an isomorphism of the ambient scheme -/

/-- Equal kernels of two closed immersions stay equal after composing with an isomorphism. -/
private theorem ker_comp_eq_of_ker_eq {X Y Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (e : X ≅ Y) (h : i₁.ker = i₂.ker) :
    (i₁ ≫ e.hom).ker = (i₂ ≫ e.hom).ker := by
  rw [← Scheme.Hom.ker_comp_of_isIso (isoOfKerEq i₁ i₂ h).hom (i₁ ≫ e.hom),
    ← Category.assoc, isoOfKerEq_hom_comp i₁ i₂ h]

/-- **An equality of kernel ideal sheaves of two closed immersions is unchanged by an
isomorphism of the ambient scheme.** The two kernels live on `X` on the left and on `Y` on the
right, so this is not a transport of one ideal sheaf to another: it is the statement that both
sides say the same thing about the two closed subschemes, because for a closed immersion the
kernel determines the subscheme over the target, by `…isoOfKerEq`, and composing an
identification over `X` with `e` gives one over `Y`.

This is what lets a statement proved at one grading of a ring be used at another with the same
carriers: `Stacks.GradedRegrading.projIso` identifies the two projective spectra, and
`Stacks.ClosedSubschemeProjQuotient.ker_eq_ker_ambientHom` is available only at a
`Submodule`-valued grading while the charts of a relative `Proj` are graded by `AddSubgroup`. -/
public theorem ker_eq_iff_ker_comp_eq {X Y Z₁ Z₂ : Scheme.{u}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] (e : X ≅ Y) :
    i₁.ker = i₂.ker ↔ (i₁ ≫ e.hom).ker = (i₂ ≫ e.hom).ker := by
  exact ⟨ker_comp_eq_of_ker_eq i₁ i₂ e, fun h => by simpa using ker_comp_eq_of_ker_eq _ _ e.symm h⟩

end Stacks.AlgebraicGeometry.KerChart

end
