module

public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit

/-!
# Two quasi-compact opens of a limit of schemes descend to one and the same level

[Stacks, Tag 01Z4] (1), which is Mathlib's `AlgebraicGeometry.exists_preimage_eq`, says that a
quasi-compact open of the vertex of a limit cone over a cofiltered system of schemes with affine
transition morphisms is the preimage of an open of *some* level. A Mayer--Vietoris argument needs
**two** opens at *one* level: the splitting of a section over `U ⊓ V` into sections over `U` and
over `V` has to be carried out upstairs, where both opens are available.

This file supplies that: descend each open separately and then pull both back to a common level,
which the cofilteredness of the index provides.

## Main results

* `AlgebraicGeometry.exists_preimage_eq_pair` — **two quasi-compact opens of the limit are the
  preimages of two opens of a single level.**

## Implementation notes

The statement is at an index `I : Type v` which is a nonempty directed preorder and schemes
`Scheme.{max u v}`, the shape the étale-cohomology developments of [Stacks, Tag 09YQ] use, so it
cannot invoke Mathlib's `AlgebraicGeometry.exists_preimage_eq` directly — that is stated for an
index category whose object *and* morphism universes are the scheme universe. What it invokes is
`AlgebraicGeometry.exists_preimage_eq_of_initiallySmall`, the same statement with the index
universes freed; its two hypotheses `CategoryTheory.LocallySmall` and
`CategoryTheory.InitiallySmall` hold because `Iᵒᵖ` and its hom types are `v`-small and
`v ≤ max u v`.

The opens produced at the level are **not** claimed to be quasi-compact. The Mayer--Vietoris
splitting at the level, `Stacks.EtaleCohomology.OpensAcyclicity.sectionsDifference_of_injective`,
holds for an arbitrary pair of opens of the level, injectivity of the sheaf there doing all the
work.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

/-- **Two quasi-compact opens of a limit of schemes are the preimages of two opens of one and the
same level.** Let `I` be a nonempty directed preorder, `D : Iᵒᵖ ⥤ Scheme` an inverse system with
affine transition morphisms, `c` a limit cone with vertex `X`, and let `U`, `V` be quasi-compact
opens of `X`. Then there are a level `k` and opens `U'`, `V'` of `X_k` with
`c.π.app k ⁻¹ᵁ U' = U` and `c.π.app k ⁻¹ᵁ V' = V`.

Each open descends on its own by [Stacks, Tag 01Z4] (1), in the index-universe-free form
`AlgebraicGeometry.exists_preimage_eq_of_initiallySmall`; the two levels are then joined by
cofilteredness of `Iᵒᵖ` and the opens pulled back along the two transition morphisms, the cone
identity turning the preimage along the longer composite back into the preimage along the shorter
one. -/
public theorem exists_preimage_eq_pair {I : Type v} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : Iᵒᵖ ⥤ Scheme.{max u v}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (U V : (c.pt).Opens) (hU : IsCompact (U : Set c.pt)) (hV : IsCompact (V : Set c.pt)) :
    ∃ (k : Iᵒᵖ) (U' V' : (D.obj k).Opens),
      c.π.app k ⁻¹ᵁ U' = U ∧ c.π.app k ⁻¹ᵁ V' = V := by
  have : InitiallySmall.{max u v} Iᵒᵖ :=
    initiallySmall_of_small_of_locallySmall.{max u v} Iᵒᵖ
  obtain ⟨i, U', -, hU'⟩ := exists_preimage_eq_of_initiallySmall D c hc U hU
  obtain ⟨j, V', -, hV'⟩ := exists_preimage_eq_of_initiallySmall D c hc V hV
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  refine ⟨k, D.map a ⁻¹ᵁ U', D.map b ⁻¹ᵁ V', ?_, ?_⟩
  · rwa [← Scheme.Hom.comp_preimage, c.w a]
  · rwa [← Scheme.Hom.comp_preimage, c.w b]

end AlgebraicGeometry

end
