module

public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedDualizingTransitivity

/-!
# The cocycle condition for the canonical comparisons of the local models

In Situation [Stacks, Tag 0AU4] let `X` be of finite type over `S` and let
`𝒰 : X = ⋃_{i = 1, …, n} U_i` be a finite covering of `X` by opens separated and of finite type
over `S`. The discussion preceding Definition [Stacks, Tag 0AUA] extracts three things from such
a covering: the local models `ω_i^• = p_i^!ω_S^•`, the canonical comparisons
`φ_{ij} : ω_i^•|_{U_i ∩ U_j} → ω_j^•|_{U_i ∩ U_j}`, and — item (3), which is
[Stacks, Tag 0AU6] — the cocycle condition

`φ_{ik}|_{U_i ∩ U_j ∩ U_k} = φ_{jk}|_{U_i ∩ U_j ∩ U_k} ∘ φ_{ij}|_{U_i ∩ U_j ∩ U_k}`

in `D(𝒪_{U_i ∩ U_j ∩ U_k})`. This file defines `φ` and proves that identity.

Everything is read in the upper-shriek formalism `Stacks.Duality.UpperShriek` of
`StacksFrontier/AlgebraicGeometry/Duality/NormalizedDualizingTransitivity.lean`, where restriction
to an open is `(W → U)^!` — legitimate by [Stacks, Tag 0AU0] — and the comparison of
[Stacks, Tag 0ATX] is the `factorIso` field. The source's own justification of item (3) is "we
use that the upper shriek functors form a pseudo functor by Lemma [Stacks, Tag 0ATY]", and that
coherence is the `factorIso_assoc` field; it is used exactly once below.

## Main definitions

All in the namespace `Stacks.Duality.UpperShriek`.

* `localModelRestrict` — `ω_U^•|_W = (W → U)^!(U → S)^!ω_S^•` for `W ≤ U`.
* `localModelRestrictIso` — the comparison `ω_W^• ≅ ω_U^•|_W` of [Stacks, Tag 0ATX].
* `localCompare` — the canonical `φ : ω_U^•|_W ≅ ω_{U'}^•|_W` for `W ≤ U` and `W ≤ U'`, which
  on `W = U_i ∩ U_j` is the `φ_{ij}` of the source.
* `overlapCompareRestrict` — `φ_{ij}` restricted from `U_i ∩ U_j` to a smaller open, conjugated
  by the comparisons of [Stacks, Tag 0ATX] on both sides. This is what
  `φ_{ij}|_{U_i ∩ U_j ∩ U_k}` means.

## Main results

* `Stacks.Duality.UpperShriek.factorIso_homOfLE_localModel` — the one application of the
  coherence [Stacks, Tag 0ATY]: the comparison for a composite of two open inclusions, read at a
  local model, is built from the three comparisons `ω_W^• ≅ ω_U^•|_W`.
* `Stacks.Duality.UpperShriek.restrictCompare_localCompare` — restricting `φ` from `W` to
  `W' ≤ W` gives the `φ` built directly on `W'`. This is the substantive step: it is what makes
  the three restrictions in [Stacks, Tag 0AU6] comparable at all.
* `Stacks.Duality.UpperShriek.localCompare_trans` — three local models over one open satisfy
  `φ_{13} = φ_{23} ∘ φ_{12}`, since each `φ` factors through `ω_W^•`.
* `Stacks.Duality.UpperShriek.overlapCompareRestrict_cocycle` — **[Stacks, Tag 0AU6]**, the
  cocycle condition in the form the source states it, on the triple overlap of three members of
  a covering.

## Implementation notes

*Where the content is.* With `φ` defined as the composite `ω_U^•|_W ≅ ω_W^• ≅ ω_{U'}^•|_W` —
which is how the source defines it, through the identification
`(U_i ∩ U_j → U_i)^! ∘ p_i^! = p_{ij}^! = (U_i ∩ U_j → U_j)^! ∘ p_j^!` of [Stacks, Tag 0ATX] —
the cocycle identity *over a fixed open* is a cancellation, `localCompare_trans`. The source's
statement is not that: its three `φ` are defined on the three different double overlaps and then
restricted to the triple overlap, so the identity only becomes meaningful once one knows that
restricting a `φ` gives a `φ`. That is `restrictCompare_localCompare`, and it is exactly one
application of the pseudofunctor coherence [Stacks, Tag 0ATY]. Both halves are proved here and
`overlapCompareRestrict_cocycle` is their composite.

*How the restriction is taken.* `Stacks.Duality.UpperShriek.restrictCompare`, introduced
with [Stacks, Tag 0AUB], conjugates an isomorphism `m^!ω ≅ n^!L` along `r : W' → W` by the
comparisons for `r ≫ m` and `r ≫ n`. A `φ` on `W` has precisely that shape, with
`m : W → U_i` and `n : W → U_j` the two open inclusions, so no new notion of restriction is
introduced.

*What is carried.* Only the upper-shriek formalism itself: `f^!` ([Stacks, Tag 0A9Y]), its
composition comparison ([Stacks, Tag 0ATX]) and the coherence ([Stacks, Tag 0ATY]) are the
fields of the parameter `Stacks.Duality.UpperShriek`, as in [Stacks, Tag 0AUB] and
[Stacks, Tag 0AUC]. Nothing else is assumed: the covering is an arbitrary
`Stacks.Duality.SeparatedCovering`, and no dualizing-ness of `ω_S^•` is needed, just as item (3)
of the source needs none.

*Relation to `Normalized.compat`.* The docstring of `Stacks.Duality.Normalized` explains that
its compatibility condition is the source's `φ_{ij} = α_j|_{U_i ∩ U_j} ∘ α_i^{-1}|_{U_i ∩ U_j}`
rewritten using the factorization of `φ_{ij}` through `ω_{U_i ∩ U_j}^•`. `localCompare` is that
`φ_{ij}`, so this file supplies the object that explanation refers to.

## References

* [Stacks Project, Tag 0AU6](https://stacks.math.columbia.edu/tag/0AU6)
* [Stacks Project, Tag 0AU4](https://stacks.math.columbia.edu/tag/0AU4)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v v' w

namespace Stacks.Duality

namespace UpperShriek

variable {𝒟 : Scheme.{u} → Type v} [∀ X : Scheme.{u}, Category.{v'} (𝒟 X)] (A : UpperShriek 𝒟)
  {X S : Scheme.{u}} {p : X ⟶ S} (hp : IsFiniteTypeOverNoetherian p) (ωS : 𝒟 S)

/-! ### The local models and their canonical comparisons -/

/-- The restriction `ω_U^•|_W` of the local model of [Stacks, Tag 0AUA] to a smaller open,
read as `(W → U)^!(U → S)^!ω_S^•`. By [Stacks, Tag 0AU0] this is derived restriction. -/
abbrev localModelRestrict {W U : X.Opens} (h : W ≤ U) (hU : IsShriekable (U.ι ≫ p)) :
    𝒟 W.toScheme :=
  (A.shriek (X.homOfLE h) (hp.isShriekable_homOfLE h)).obj (A.localModel hU ωS)

/-- The canonical comparison `ω_W^• ≅ ω_U^•|_W` for `W ≤ U`: the comparison of
[Stacks, Tag 0ATX] for the factorization `W → U → S` of the structure morphism of `W`. -/
def localModelRestrictIso {W U : X.Opens} (h : W ≤ U) (hU : IsShriekable (U.ι ≫ p))
    (hW : IsShriekable (W.ι ≫ p)) :
    A.localModel hW ωS ≅ A.localModelRestrict hp ωS h hU :=
  (A.factorIso (show X.homOfLE h ≫ U.ι ≫ p = W.ι ≫ p by rw [← Category.assoc, X.homOfLE_ι])
    (hp.isShriekable_homOfLE h) hU hW).app ωS

/-- **The canonical comparison `φ` of [Stacks, Tag 0AUA], item (2).** For an open `W` contained
in two members `U`, `U'` of the covering, the isomorphism `ω_U^•|_W ≅ ω_{U'}^•|_W` obtained from
the identification `(W → U)^! ∘ (U → S)^! = (W → S)^! = (W → U')^! ∘ (U' → S)^!` of
[Stacks, Tag 0ATX]: it is the composite `ω_U^•|_W ≅ ω_W^• ≅ ω_{U'}^•|_W`.

Taking `W = U_i ⊓ U_j`, `U = U_i` and `U' = U_j` gives the `φ_{ij}` of the source. -/
def localCompare {W U U' : X.Opens} (h : W ≤ U) (h' : W ≤ U')
    (hU : IsShriekable (U.ι ≫ p)) (hU' : IsShriekable (U'.ι ≫ p))
    (hW : IsShriekable (W.ι ≫ p)) :
    A.localModelRestrict hp ωS h hU ≅ A.localModelRestrict hp ωS h' hU' :=
  (A.localModelRestrictIso hp ωS h hU hW).symm ≪≫ A.localModelRestrictIso hp ωS h' hU' hW

/-! ### The comparisons restrict to one another -/

/-- **The coherence [Stacks, Tag 0ATY], read on a composite of two open inclusions.** For
`W' ≤ W ≤ U` the comparison of [Stacks, Tag 0ATX] attached to the factorization
`W' → W → U`, evaluated at the local model `ω_U^•`, is the composite of the three comparisons
`ω_{W'}^• ≅ ω_U^•|_{W'}`, `ω_{W'}^• ≅ ω_W^•|_{W'}` and `ω_W^• ≅ ω_U^•|_W`.

This is the only use of `Stacks.Duality.UpperShriek.factorIso_assoc` in the file; everything
else is cancellation. -/
theorem factorIso_homOfLE_localModel {W' W U : X.Opens} (hr : W' ≤ W) (h : W ≤ U)
    (hU : IsShriekable (U.ι ≫ p)) (hW : IsShriekable (W.ι ≫ p))
    (hW' : IsShriekable (W'.ι ≫ p)) :
    (A.factorIso (X.homOfLE_homOfLE hr h) (hp.isShriekable_homOfLE hr)
          (hp.isShriekable_homOfLE h) (hp.isShriekable_homOfLE (hr.trans h))).app
        (A.localModel hU ωS) =
      (A.localModelRestrictIso hp ωS (hr.trans h) hU hW').symm ≪≫
        A.localModelRestrictIso hp ωS hr hW hW' ≪≫
          (A.shriek (X.homOfLE hr) (hp.isShriekable_homOfLE hr)).mapIso
            (A.localModelRestrictIso hp ωS h hU hW) := by
  have e : ∀ {V V' : X.Opens} (h : V ≤ V'), X.homOfLE h ≫ V'.ι ≫ p = V.ι ≫ p := fun h => by
    rw [← Category.assoc, X.homOfLE_ι]
  have key := A.factorIso_assoc (X.homOfLE_homOfLE hr h) (e h) (e (hr.trans h)) (e hr)
    (hp.isShriekable_homOfLE hr) (hp.isShriekable_homOfLE h) hU
    (hp.isShriekable_homOfLE (hr.trans h)) hW hW' ωS
  refine Iso.ext ?_
  simp only [localModelRestrictIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.app_inv]
  rw [key]
  simp

/-- **Restricting `φ` gives `φ`.** For `W' ≤ W` and `W ≤ U`, `W ≤ U'`, conjugating the
comparison `φ : ω_U^•|_W ≅ ω_{U'}^•|_W` along `W' → W` by the comparisons of
[Stacks, Tag 0ATX] produces the comparison built directly on `W'`.

This is what gives the restrictions `φ_{ij}|_{U_i ∩ U_j ∩ U_k}` of [Stacks, Tag 0AU6] a common
description, and it is one application of `Stacks.Duality.UpperShriek.factorIso_homOfLE_localModel`
on each side. -/
theorem restrictCompare_localCompare {W' W U U' : X.Opens} (hr : W' ≤ W) (h : W ≤ U)
    (h' : W ≤ U') (hU : IsShriekable (U.ι ≫ p)) (hU' : IsShriekable (U'.ι ≫ p))
    (hW : IsShriekable (W.ι ≫ p)) (hW' : IsShriekable (W'.ι ≫ p)) :
    A.restrictCompare (X.homOfLE_homOfLE hr h) (X.homOfLE_homOfLE hr h')
        (hp.isShriekable_homOfLE hr) (hp.isShriekable_homOfLE h)
        (hp.isShriekable_homOfLE h') (hp.isShriekable_homOfLE (hr.trans h))
        (hp.isShriekable_homOfLE (hr.trans h'))
        (A.localCompare hp ωS h h' hU hU' hW) =
      A.localCompare hp ωS (hr.trans h) (hr.trans h') hU hU' hW' := by
  rw [restrictCompare, A.factorIso_homOfLE_localModel hp ωS hr h hU hW hW',
    A.factorIso_homOfLE_localModel hp ωS hr h' hU' hW hW']
  refine Iso.ext ?_
  simp [localCompare]

/-- **The cocycle condition over a fixed open.** For three members `U`, `U'`, `U''` of the
covering all containing `W`, the comparisons of `Stacks.Duality.UpperShriek.localCompare`
satisfy `φ_{U U''} = φ_{U' U''} ∘ φ_{U U'}`.

Each `φ` factors through `ω_W^•` by construction, so this is a cancellation. The content of
[Stacks, Tag 0AU6] is not here but in
`Stacks.Duality.UpperShriek.restrictCompare_localCompare`, which identifies the restrictions of
the three `φ` of the source with the three comparisons appearing below. -/
theorem localCompare_trans {W U U' U'' : X.Opens} (h : W ≤ U) (h' : W ≤ U') (h'' : W ≤ U'')
    (hU : IsShriekable (U.ι ≫ p)) (hU' : IsShriekable (U'.ι ≫ p))
    (hU'' : IsShriekable (U''.ι ≫ p)) (hW : IsShriekable (W.ι ≫ p)) :
    A.localCompare hp ωS h h'' hU hU'' hW =
      A.localCompare hp ωS h h' hU hU' hW ≪≫ A.localCompare hp ωS h' h'' hU' hU'' hW :=
  Iso.ext (by simp [localCompare])

/-! ### The cocycle condition on a triple overlap -/

variable {ι : Type w}

/-- `φ_{ij}` restricted from the overlap `U_i ⊓ U_j` to a smaller open `W`, conjugated by the
comparisons of [Stacks, Tag 0ATX] on both sides. For `W = U_i ⊓ U_j ⊓ U_k` this is the
`φ_{ij}|_{U_i ∩ U_j ∩ U_k}` of [Stacks, Tag 0AU6]. -/
def overlapCompareRestrict (𝒰 : SeparatedCovering p ι) (i j : ι) (W : X.Opens)
    (hW : W ≤ 𝒰.U i ⊓ 𝒰.U j) :
    A.localModelRestrict hp ωS (hW.trans inf_le_left) (𝒰.shriekable i) ≅
      A.localModelRestrict hp ωS (hW.trans inf_le_right) (𝒰.shriekable j) :=
  A.restrictCompare (X.homOfLE_homOfLE hW inf_le_left) (X.homOfLE_homOfLE hW inf_le_right)
    (hp.isShriekable_homOfLE hW) (hp.isShriekable_homOfLE inf_le_left)
    (hp.isShriekable_homOfLE inf_le_right) (hp.isShriekable_homOfLE (hW.trans inf_le_left))
    (hp.isShriekable_homOfLE (hW.trans inf_le_right))
    (A.localCompare hp ωS inf_le_left inf_le_right (𝒰.shriekable i) (𝒰.shriekable j)
      (hp.isShriekable_le inf_le_left (𝒰.shriekable i)))

/-- The restriction of `φ_{ij}` to `W` is the comparison built directly on `W`, by
`Stacks.Duality.UpperShriek.restrictCompare_localCompare`. -/
theorem overlapCompareRestrict_eq (𝒰 : SeparatedCovering p ι) (i j : ι) (W : X.Opens)
    (hW : W ≤ 𝒰.U i ⊓ 𝒰.U j) (hWp : IsShriekable (W.ι ≫ p)) :
    A.overlapCompareRestrict hp ωS 𝒰 i j W hW =
      A.localCompare hp ωS (hW.trans inf_le_left) (hW.trans inf_le_right)
        (𝒰.shriekable i) (𝒰.shriekable j) hWp :=
  A.restrictCompare_localCompare hp ωS hW inf_le_left inf_le_right (𝒰.shriekable i)
    (𝒰.shriekable j) (hp.isShriekable_le inf_le_left (𝒰.shriekable i)) hWp

/-- **Stacks Project, Tag 0AU6.** In Situation [Stacks, Tag 0AU4] let `X` be of finite type over
`S` and let `𝒰 : X = ⋃ U_i` be a finite covering of `X` by opens separated and of finite type
over `S`. Let `ω_i^•` be the local models and `φ_{ij} : ω_i^•|_{U_i ∩ U_j} ≅ ω_j^•|_{U_i ∩ U_j}`
the canonical comparisons of the discussion preceding Definition [Stacks, Tag 0AUA]. Then for
all `i, j, k`

`φ_{ik}|_{U_i ∩ U_j ∩ U_k} = φ_{jk}|_{U_i ∩ U_j ∩ U_k} ∘ φ_{ij}|_{U_i ∩ U_j ∩ U_k}`

in `D(𝒪_{U_i ∩ U_j ∩ U_k})`. Composition is written left to right, so the right hand side
below reads `φ_{ij}` followed by `φ_{jk}`.

The restrictions are `Stacks.Duality.UpperShriek.overlapCompareRestrict`, i.e. the conjugation
of `Stacks.Duality.UpperShriek.restrictCompare`; the proof identifies all three with
comparisons built directly on the triple overlap
(`Stacks.Duality.UpperShriek.overlapCompareRestrict_eq`, which is the coherence
[Stacks, Tag 0ATY]) and then cancels
(`Stacks.Duality.UpperShriek.localCompare_trans`). -/
@[stacks 0AU6 "item (3) of the discussion before Definition 0AUA: the cocycle condition \
phi_ik = phi_jk after phi_ij for the canonical comparisons of the local models, restricted to \
the triple overlap U_i cap U_j cap U_k. RESTRICTED only in that the upper-shriek formalism of \
Stacks 0A9Y/0ATX/0ATY is the parameter UpperShriek, as in 0AUB and 0AUC; the \
coherence 0ATY, which the source cites for item (3), is its factorIso_assoc field"]
theorem overlapCompareRestrict_cocycle (𝒰 : SeparatedCovering p ι) (i j k : ι) :
    A.overlapCompareRestrict hp ωS 𝒰 i k (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) =
      A.overlapCompareRestrict hp ωS 𝒰 i j (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k) inf_le_left ≪≫
        A.overlapCompareRestrict hp ωS 𝒰 j k (𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k)
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right) := by
  have hWp : IsShriekable ((𝒰.U i ⊓ 𝒰.U j ⊓ 𝒰.U k).ι ≫ p) :=
    hp.isShriekable_le (inf_le_left.trans inf_le_left) (𝒰.shriekable i)
  rw [A.overlapCompareRestrict_eq hp ωS 𝒰 i k _ _ hWp,
    A.overlapCompareRestrict_eq hp ωS 𝒰 i j _ _ hWp,
    A.overlapCompareRestrict_eq hp ωS 𝒰 j k _ _ hWp]
  exact A.localCompare_trans hp ωS _ _ _ (𝒰.shriekable i) (𝒰.shriekable j) (𝒰.shriekable k) hWp

end UpperShriek

end Stacks.Duality

end
