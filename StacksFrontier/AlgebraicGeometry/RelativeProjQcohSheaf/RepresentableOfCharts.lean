module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleGluesProof
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleSmall

/-!
# Tag 01NV from the charts of Tag 01NU

Let `S` be a scheme and `𝒜` a graded `𝒪_S`-algebra (Situation 01NN), and fix an integer `d`.
[Stacks, Tag 01NV] says that the functor `F_d` of Section 01NS is representable by a scheme over
`S`, and the source proves it in four steps:

1. `F_d` is a sheaf on the big Zariski site;
2. `F_d` has a family of subfunctors which are representable by schemes, the charts;
3. those subfunctors cover `F_d`;
4. a Zariski sheaf covered by representable open subfunctors is representable.

Step (4) is Mathlib's [Stacks, Tag 01JJ]. Steps (2) and (3) together are [Stacks, Tag 01NU] in
the form the charts want. Step (1) is `...RelativeProjQcohSheaf.Fd.isSheaf_functor` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/QuadrupleGluesProof.lean`. This file
deduces Tag 01NV from the charts alone, for an arbitrary graded algebra and integer `d`; the
charts themselves are constructed, for Situation 01NN and `d ≥ 1`, in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/AffineOpenCharts.lean`.

## Main results

* `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts'`: **Tag 01NV with step
  (1) discharged**, from the charts of Tag 01NU.
* `...RelativeProjQcohSheaf.Fd.isRepresentable_functor_of_charts'`: the same in the bare form
  `(Fd.functor 𝒜 d).IsRepresentable`.
* `...RelativeProjQcohSheaf.Fd.exists_amalgamation_opens`: **a compatible family of classes on a
  covering of a test scheme by opens has an amalgamation**, with no hypothesis. This is
  `...RelativeProjQcohSheaf.Fd.exists_amalgamation_opens_of_quadrupleGlues` fed
  `quadrupleGlues_proof`.

## Implementation notes

`Fd.isSheaf_functor` lives downstream of `...RelativeProjQcohSheaf.SmallModel` and
`...RelativeProjQcohSheaf.QuadrupleSmall`, which state the forms of Tag 01NV with the sheaf
property as a hypothesis `hsheaf`, so the forms without it are stated here.

## References

* [Stacks Project, Tag 01NV](https://stacks.math.columbia.edu/tag/01NV)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open AlgebraicGeometry Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

variable {S : Scheme.{u}}
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)) (d : ℤ)

/-! ### The amalgamation of classes along a covering by opens, unconditionally -/

/-- **A compatible family of classes of `F_d` on a covering of a test scheme by opens has an
amalgamation**, with no hypothesis: the morphism to `S` is glued rather than assumed, and so is
the quadruple over it. This is
`...RelativeProjQcohSheaf.Fd.exists_amalgamation_opens_of_quadrupleGlues` with its hypothesis
`hglue` supplied by `...RelativeProjQcohSheaf.quadrupleGlues_proof`. -/
theorem Fd.exists_amalgamation_opens
    (T : Scheme.{u}) (ι : Type u) (W : ι → T.Opens) (hW : ∀ x : T, ∃ a, x ∈ W a)
    (ξ : ∀ a, Fd A d (W a).toScheme)
    (hcompat : ∀ a b, Fd.pullback (T.homOfLE (inf_le_left : W a ⊓ W b ≤ W a)) (ξ a) =
      Fd.pullback (T.homOfLE (inf_le_right : W a ⊓ W b ≤ W b)) (ξ b)) :
    ∃ t : Fd A d T, ∀ a, Fd.pullback (W a).ι t = ξ a :=
  Fd.exists_amalgamation_opens_of_quadrupleGlues (quadrupleGlues_proof A d) T ι W hW ξ hcompat

/-! ### Tag 01NV from the charts -/

/-- **Stacks Project, Tag 01NV, with step (1) of the source proof discharged.** The functor `F_d`
of Section 41.21 (Tag 01NS) is representable by a scheme over `S`: there are a scheme `Y`, a
morphism `p : Y ⟶ S` and a representation of `F_d` by `Y` under which the morphism `T ⟶ Y`
representing a class `ξ ∈ F_d(T)`, composed with `p`, is the morphism `T ⟶ S` recorded by `ξ`.

This is `...RelativeProjQcohSheaf.Fd.exists_representableBy_functor_of_charts` with its
hypothesis `hsheaf` — the Zariski sheaf property of `F_d`, the source's step (1) — supplied by
the theorem `...RelativeProjQcohSheaf.Fd.isSheaf_functor`; the charts `c`, `hc`, `hcover` are
steps (2) and (3). -/
theorem Fd.exists_representableBy_functor_of_charts'
    {ι : Type u} {X : ι → Scheme.{u}}
    (c : (i : ι) → yoneda.obj (X i) ⟶ Fd.smallPresheaf A d)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ S) (e : (Fd.functor A d).RepresentableBy Y),
      ∀ (T : Scheme.{u}) (ξ : Fd A d T), e.homEquiv.symm ξ ≫ p = ξ.1 :=
  Fd.exists_representableBy_functor_of_charts A d (Fd.isSheaf_functor A d) c hc hcover

/-- **Stacks Project, Tag 01NV, in the bare form, with step (1) of the source proof discharged.**
This is `Fd.exists_representableBy_functor_of_charts'` forgetting the structure morphism to
`S`. -/
theorem Fd.isRepresentable_functor_of_charts'
    {ι : Type u} {X : ι → Scheme.{u}}
    (c : (i : ι) → yoneda.obj (X i) ⟶ Fd.smallPresheaf A d)
    (hc : ∀ i, IsOpenImmersion.presheaf (c i))
    (hcover : Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc c)) :
    (Fd.functor A d).IsRepresentable :=
  Fd.isRepresentable_functor_of_charts A d (Fd.isSheaf_functor A d) c hc hcover

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
