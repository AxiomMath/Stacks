/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorPresheafBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotSubfunctorAffineLocal

/-!
# Base change of a subfunctor of the Quot presheaf

Let `F/X/B` be a Quot situation (Stacks 09TR), `p : B' ⟶ B` a morphism of algebraic spaces and
`F'/X'/B'` the base-changed situation of Stacks 08IT
(`AlgebraicGeometry.Space.QuotSituation.canonicalBaseChanged`). The Quot presheaf of `F'/X'/B'`
is `Quot_{F/X/B} ×_B B'`
(`AlgebraicGeometry.Space.QuotSituation.isPullback_canonicalBaseChangedQuotSitePresheaf`). For
a subfunctor `Q ⊆ Quot_{F/X/B}`, its preimage `Q ×_B B'` in the Quot presheaf of `F'/X'/B'` is
again cartesian over `p`.

Together with `AlgebraicGeometry.Space.QuotSituation.isProperAlgebraicSpaceOver_of_isAffine`
it follows that `Q` is an algebraic space proper over `B` as soon as it is a sheaf and, for every
affine scheme `W` with a morphism to `B`, the subfunctor `Q ×_B W` of the Quot presheaf of the
base change to `W` is represented by a scheme proper over `W`.

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.baseChangeSubfunctor`: `Q ×_B B'`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.isPullback_baseChangeSubfunctor`: the square of
  subfunctors over `p` is cartesian.
* `AlgebraicGeometry.Space.QuotSituation.exists_isPullback_of_represented`: a representation of
  `Q ×_B W` gives a cartesian square over `h_W ⟶ B` for any model of `Q`.
* `AlgebraicGeometry.Space.QuotSituation.isProperAlgebraicSpaceOver_of_represented`: the
  reduction to affine bases, in terms of the base-changed subfunctors.

## References

* [Stacks Project, Tag 08IT](https://stacks.math.columbia.edu/tag/08IT)
* [Stacks Project, Tag 083R](https://stacks.math.columbia.edu/tag/083R)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : QuotSituation B S hS)
  {Y' : AlgebraicSpaces B S hS} (p : Y' ⟶ D.Y) (Q : Subfunctor D.quotSitePresheaf)

/-- **`Q ×_B B'`**: the subfunctor of the Quot presheaf of the base-changed situation `F'/X'/B'`
of the quotients which, read as quotients of `F/X/B`, lie in `Q`. -/
abbrev baseChangeSubfunctor : Subfunctor (D.canonicalBaseChanged p).quotSitePresheaf :=
  Q.preimage (D.canonicalBaseChangedQuotSitePresheafHom p)

/-- The comparison morphism `Q ×_B B' ⟶ Q`. -/
def baseChangeSubfunctorHom : (D.baseChangeSubfunctor p Q).toFunctor ⟶ Q.toFunctor :=
  Subfunctor.lift ((D.baseChangeSubfunctor p Q).ι ≫ D.canonicalBaseChangedQuotSitePresheafHom p)
    (by rintro T _ ⟨x, rfl⟩; exact x.2)

/-- **`Q ×_B B'` is the fibre product of `Q ⟶ B` and `p : B' ⟶ B`.** -/
theorem isPullback_baseChangeSubfunctor :
    IsPullback (D.baseChangeSubfunctorHom p Q)
      ((D.baseChangeSubfunctor p Q).ι ≫ (D.canonicalBaseChanged p).quotSitePresheafToBase)
      (Q.ι ≫ D.quotSitePresheafToBase) (Functor.whiskerRight p.hom uliftFunctor.{u + 1, u}) := by
  refine IsPullback.of_forall_isPullback_app fun T ↦ ?_
  have hbig := (D.isPullback_canonicalBaseChangedQuotSitePresheaf p).map
    ((evaluation (BigFppfOver B S hS)ᵒᵖ (Type (u + 1))).obj T)
  rw [Types.isPullback_iff] at hbig ⊢
  obtain ⟨hw, hinj, hsurj⟩ := hbig
  refine ⟨?_, ?_, ?_⟩
  · ext ⟨x, hx⟩
    exact ConcreteCategory.congr_hom hw x
  · rintro ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ ⟨e₁, e₂⟩
    exact Subtype.ext (hinj y₁ y₂ ⟨congrArg Subtype.val e₁, e₂⟩)
  · rintro ⟨x, hx⟩ b hxb
    obtain ⟨y, hy₁, hy₂⟩ := hsurj x b hxb
    refine ⟨⟨y, ?_⟩, Subtype.ext hy₁, hy₂⟩
    change (D.canonicalBaseChangedQuotSitePresheafHom p).app T y ∈ Q.obj T
    rwa [show (D.canonicalBaseChangedQuotSitePresheafHom p).app T y = x from hy₁]

/-- **A representation of `Q ×_B W` is a cartesian square over `h_W ⟶ B` for every model of
`Q`.** If `Q ×_B W` is identified, over `W`, with the universe lift of the presheaf represented
by an object `Z` with a morphism `q : Z ⟶ W`, then for every model `M` of `Q` the square formed
by `h_Z ⟶ M`, `h_q`, `M ⟶ B` and `ξ : h_W ⟶ B` is cartesian. -/
theorem exists_isPullback_of_represented (M : D.SubfunctorModel Q) {W : BigFppfOver B S hS}
    (ξ : yoneda.obj W ⟶ D.Y.obj) {Z : BigFppfOver B S hS} (q : Z ⟶ W)
    (e : yoneda.obj Z ⋙ uliftFunctor.{u + 1, u} ≅
      (D.baseChangeSubfunctor (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ) Q).toFunctor)
    (he : e.hom ≫ (D.baseChangeSubfunctor (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)
        Q).ι ≫ (D.canonicalBaseChanged
          (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)).quotSitePresheafToBase =
      Functor.whiskerRight (yoneda.map q) uliftFunctor.{u + 1, u}) :
    ∃ s : yoneda.obj Z ⟶ M.presheaf, IsPullback s (yoneda.map q) M.toBase ξ := by
  let p : schemeSpace W ⟶ D.Y := ObjectProperty.homMk ξ
  let FF := (Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight
    (BigFppfOver B S hS)ᵒᵖ
  have : ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1, u}).Full := FF.full
  have : ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1, u}).Faithful := FF.faithful
  let s : yoneda.obj Z ⟶ M.presheaf :=
    FF.preimage (e.hom ≫ D.baseChangeSubfunctorHom p Q ≫ M.iso.inv)
  have hs : Functor.whiskerRight s uliftFunctor.{u + 1, u} =
      e.hom ≫ D.baseChangeSubfunctorHom p Q ≫ M.iso.inv := FF.map_preimage _
  have H : IsPullback (Functor.whiskerRight s uliftFunctor.{u + 1, u})
      (Functor.whiskerRight (yoneda.map q) uliftFunctor.{u + 1, u})
      (Functor.whiskerRight M.toBase uliftFunctor.{u + 1, u})
      (Functor.whiskerRight ξ uliftFunctor.{u + 1, u}) := by
    refine (D.isPullback_baseChangeSubfunctor p Q).of_iso e.symm M.iso.symm
      (by exact Iso.refl (yoneda.obj W ⋙ uliftFunctor.{u + 1, u})) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [hs]
    · rw [← he]
      exact (Category.comp_id _).trans (e.inv_hom_id_assoc _).symm
    · simp [M.whiskerRight_toBase]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  refine ⟨s, IsPullback.of_map ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u)
    (Type (u + 1))).obj uliftFunctor.{u + 1, u}) (FF.map_injective ?_) H⟩
  rw [Functor.map_comp, Functor.map_comp]
  exact H.w

/-- **Properness of a subfunctor of the Quot presheaf, checked on affine bases.** A
subfunctor `Q` of the Quot presheaf which is an fppf sheaf is an algebraic space proper over `B`
as soon as, for every object `W` of the site with affine underlying scheme and every morphism
`ξ : h_W ⟶ B`, the subfunctor `Q ×_B W` of the Quot presheaf of the base change of `F/X/B` to
`W` is represented, over `W`, by an object `Z` whose morphism `Z ⟶ W` is proper. -/
theorem isProperAlgebraicSpaceOver_of_represented
    (hQ : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Q.toFunctor)
    (h : ∀ (W : BigFppfOver B S hS) (ξ : yoneda.obj W ⟶ D.Y.obj),
      IsAffine ((BigFppfOver.toScheme B S hS).obj W) →
        ∃ (Z : BigFppfOver B S hS) (q : Z ⟶ W)
          (e : yoneda.obj Z ⋙ uliftFunctor.{u + 1, u} ≅
            (D.baseChangeSubfunctor (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)
              Q).toFunctor),
          e.hom ≫ (D.baseChangeSubfunctor (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)
              Q).ι ≫ (D.canonicalBaseChanged
                (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)).quotSitePresheafToBase =
            Functor.whiskerRight (yoneda.map q) uliftFunctor.{u + 1, u} ∧
          _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q)) :
    D.IsProperAlgebraicSpaceOver Q := by
  let M := SubfunctorModel.canonical Q
  refine D.isProperAlgebraicSpaceOver_of_isAffine Q hQ M fun W ξ hW ↦ ?_
  obtain ⟨Z, q, e, he, hq⟩ := h W ξ hW
  obtain ⟨s, hs⟩ := D.exists_isPullback_of_represented Q M ξ q e he
  exact ⟨Z, s, q, hs, hq⟩

end AlgebraicGeometry.Space.QuotSituation

end
