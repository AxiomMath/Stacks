module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Unramified

/-!
# Smooth representable transformations are formally smooth (Stacks 04AL)

A smooth representable transformation of set-valued functors on the big fppf site over a
scheme has a lift in every affine square-zero infinitesimal lifting problem.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.formallySmooth_of_smooth`: **Stacks 04AL, part (1)**, a smooth
  representable transformation is formally smooth.

## Implementation notes

The property `CategoryTheory.MorphismProperty.presheaf` bundles representability of the
transformation with the requirement that every represented base change have the indicated
property, here smoothness of the underlying morphism of schemes in the big fppf slice.

Representability turns the lifting problem into one about a scheme. By
`AlgebraicGeometry.Space.exists_representing_scheme_lift_equiv` the base change of `a` along
the point `y` is represented by an object `P` of the slice with a projection `p : P ⟶ T'`, and
lifts `z` of the square correspond to sections of `p` extending the given map `t : T ⟶ P`. So
the statement to prove is that `p` admits such a section, which is an infinitesimal lifting
problem for the scheme morphism underlying `p`.

That scheme morphism is smooth by the second clause of the hypothesis, hence formally smooth
by Tag 02H6 (`Stacks.Smooth.formallySmoothScheme_of_smooth`, the implication of
`Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth` that does not need
finite presentation). Its filler lives in `Scheme`; it is transported back into the slice by
the fullness and faithfulness of `AlgebraicGeometry.BigFppfSite.inclusion` — the preimage
morphism is over `S` because composing it with `p` gives the identity — and the
correspondence of `exists_representing_scheme_lift_equiv` carries it back to a lift of the
original square.

The scheme-level lifting property is written out as `Stacks.Smooth.FormallySmoothScheme`,
since inside `AlgebraicGeometry.Space` the bare name `FormallySmooth` resolves to the
space-level Tag 049S predicate and not to the scheme-level Tag 02H0 one. The scheme-level
property quantifies over *all* affine first-order thickenings, so in particular over those
coming from the site, which is the direction needed here.

## References

* [Stacks Project, Tag 02H0](https://stacks.math.columbia.edu/tag/02H0)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 049S](https://stacks.math.columbia.edu/tag/049S)
* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04AL, part (1).** A smooth representable transformation on the big fppf site is
formally smooth. -/
@[stacks 04AL "part (1)"]
public theorem formallySmooth_of_smooth
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G)
    (ha : (MorphismProperty.inverseImage
      (@Smooth.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    FormallySmooth a := by
  intro T T' hT hT' i hi x y hxy
  obtain ⟨P, p, q, hPB, t, htp, hqx, e, he⟩ :=
    exists_representing_scheme_lift_equiv B S hS a ha.1 T T' i x y hxy
  have hpFormal : Stacks.Smooth.FormallySmoothScheme
      ((BigFppfOver.toScheme B S hS).map p) :=
    @Stacks.Smooth.formallySmoothScheme_of_smooth _ _ _
      (ha.2 (g := yonedaEquiv.symm y) (fst := q) (snd := p) hPB)
  set f : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj P :=
    (BigFppfOver.toScheme B S hS).map t with hf
  have hcomm : f ≫ (BigFppfOver.toScheme B S hS).map p =
      (BigFppfOver.toScheme B S hS).map i ≫ (BigFppfOver.toScheme B S hS).map (𝟙 T') := by
    rw [hf, ← Functor.map_comp, htp, ← Functor.map_comp, Category.comp_id]
  have hi' : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map i) := hi
  obtain ⟨h, hhp, hhi⟩ := hpFormal hT hT' ((BigFppfOver.toScheme B S hS).map i) hi' f
    ((BigFppfOver.toScheme B S hS).map (𝟙 T')) hcomm
  set hB : (BigFppfOver.forget B S hS).obj T' ⟶ (BigFppfOver.forget B S hS).obj P :=
    B.inclusion.preimage h with hhB
  have hBp : hB ≫ (BigFppfOver.forget B S hS).map p = 𝟙 _ := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, hhB, B.inclusion.map_preimage]
    simpa using hhp
  have hOver : hB ≫ P.hom = T'.hom := by
    conv_lhs => rw [← p.w, ← Category.assoc]
    change (hB ≫ (BigFppfOver.forget B S hS).map p) ≫ T'.hom = _
    rw [hBp]
    simp
  set s : T' ⟶ P := Over.homMk hB hOver
  have hs_map : (BigFppfOver.toScheme B S hS).map s = h := by
    change B.inclusion.map hB = h
    rw [hhB]
    exact B.inclusion.map_preimage h
  have hsp : s ≫ p = 𝟙 T' :=
    (BigFppfOver.forget B S hS).map_injective hBp
  have hit : i ≫ s = t := by
    apply (BigFppfOver.forget B S hS).map_injective
    apply B.inclusion.map_injective
    rw [Functor.map_comp]
    change (BigFppfOver.toScheme B S hS).map i ≫
      (BigFppfOver.toScheme B S hS).map s = f
    simpa only [hs_map] using hhi
  exact ⟨(e.symm ⟨s, hsp, hit⟩).val, (e.symm ⟨s, hsp, hit⟩).property⟩

end AlgebraicGeometry.Space

end
