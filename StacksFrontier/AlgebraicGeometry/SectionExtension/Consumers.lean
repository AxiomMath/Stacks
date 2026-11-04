module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Basic
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffinePullback.Basic

/-!
# What the surjectivity half of Stacks Tag 01PW discharges in the ample cluster

`StacksFrontier/AlgebraicGeometry/SectionExtension/Basic.lean` isolates the surjectivity half of
Stacks Tag 01PW as `Stacks.SectionExtension.IsSectionRatio` and proves from it that every basic
open of an affine `X_s` is itself an `X_u`. That last statement is exactly
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing`, the single premise the general case of Stacks
Tag 0B3E and the content of Stacks Tag 01VN stand on in this repository. This file makes the
identification and carries the premise through to those three statements, so that the whole
cluster rests on one named declaration about section extension and nothing else.

## Main results

* `Stacks.SectionExtension.basicOpenIsPow_of_isSectionRatio`:
  `Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow` from `Stacks.SectionExtension.IsSectionRatio`.
  The two statements are the same proposition; this is the sole reason
  `Stacks.SectionExtension.Basic` writes the conclusion out instead of importing it. This is the
  form with **no affineness hypothesis** on `X_s`, which part (2) of Stacks Tag 0892 needs and
  which Stacks Tag 01PW itself has.
* `Stacks.SectionExtension.basicOpenIsPowNonvanishing_of_isSectionRatio`: the
  affineness-restricted form, `Stacks.AmplePullback.BasicOpenIsPowNonvanishing`, which follows by
  discarding a hypothesis.
* `Stacks.SectionExtension.isAmple_modulePullback_of_isSectionRatio`: **Stacks Tag 0B3E in the
  shape of its statement**, on the section-extension premise for the one module at hand.
* `Stacks.SectionExtension.amplePullbackGap_of_isSectionRatio` and
  `Stacks.SectionExtension.isRelativelyAmple_of_hasRelativeTwistImmersion`:
  `Stacks.RelativeVeryAmple.AmplePullbackGap` and the content of Stacks Tag 01VN, on the premise
  taken for every scheme and every *ample* invertible module — which is how those two statements
  quantify. The ampleness hypothesis is kept on the premise rather than dropped, because
  `Stacks.SectionExtension.IsSectionRatio` is Stacks Tag 01PW part (2) and that part needs `X`
  quasi-compact and quasi-separated: ampleness supplies quasi-compactness outright and
  quasi-separatedness by Stacks Tag 01PY, so stating the premise only for ample modules keeps it
  a consequence of the source lemma rather than a strengthening of it.

## No Stacks attribute is attached

Every result below is conditional on `Stacks.SectionExtension.IsSectionRatio`, which is not
proved. A tag on a conditional statement would claim its label is done, so none is attached here;
the labels at stake are 01PW (assumed), 0B3E and 01VN (both reduced to it, their attributes
already sitting on `Stacks.AmplePullback` and `Stacks.Tag01VN` declarations carrying the same
premise).

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Ample

universe u

namespace Stacks.SectionExtension

/-! ### The premise of the ample cluster -/

section Premise

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- **`Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow` from the surjectivity half of Stacks Tag
01PW.** The two propositions are literally the same; `Stacks.SectionExtension.Basic` states the
conclusion in its own words only so that it need not import `Stacks.AmpleQuasiAffinePullback`.

This is the **hypothesis-free** form — no affineness of `X_s` — which is what part (2) of Stacks
Tag 0892 needs, the open it shrinks inside being a quasi-affine preimage `f⁻¹(S_t)` rather than an
affine one. It closes three statements at once: the general case of Stacks Tag 0B3E, clause (3) of
Stacks Tag 01Q3, and part (2) of Stacks Tag 0892. -/
theorem basicOpenIsPow_of_isSectionRatio (h : IsSectionRatio X L) :
    Stacks.AmpleQuasiAffinePullback.BasicOpenIsPow X L :=
  fun n hn s g => exists_powNonvanishingOpen_eq_basicOpen X L h n hn s g

/-- **`Stacks.AmplePullback.BasicOpenIsPowNonvanishing` from the surjectivity half of Stacks Tag
01PW**, by discarding the affineness hypothesis that the hypothesis-free form above does not
need. -/
theorem basicOpenIsPowNonvanishing_of_isSectionRatio (h : IsSectionRatio X L) :
    Stacks.AmplePullback.BasicOpenIsPowNonvanishing X L :=
  Stacks.AmpleQuasiAffinePullback.basicOpenIsPowNonvanishing X L
    (basicOpenIsPow_of_isSectionRatio X L h)

end Premise

/-! ### Stacks Tag 0B3E and Stacks Tag 01VN -/

section Pullback

variable {X' X : Scheme.{u}} (i : X' ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **Stacks Tag 0B3E in the shape of its statement**, on the surjectivity half of Stacks
Tag 01PW for `L` alone. The four unconditional reductions are
`Stacks.AmplePullback.isAmple_modulePullback`'s; all this does is discharge its premise. -/
theorem isAmple_modulePullback_of_isSectionRatio (hL : IsAmple X L)
    (hi : (QuasiCompact i ∧ IsImmersion i) ∨ (CompactSpace X' ∧ IsImmersion i) ∨
      (QuasiCompact i ∧ Topology.IsEmbedding i) ∨
      (CompactSpace X' ∧ Topology.IsEmbedding i))
    (h : IsSectionRatio X L) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) :=
  Stacks.AmplePullback.isAmple_modulePullback i L hL hi
    (basicOpenIsPowNonvanishing_of_isSectionRatio X L h)

end Pullback

/-- **`Stacks.RelativeVeryAmple.AmplePullbackGap` on the surjectivity half of Stacks Tag 01PW.**
The gap quantifies over every scheme and every invertible module, so the premise is taken in that
generality. -/
theorem amplePullbackGap_of_isSectionRatio
    (h : ∀ (B : Scheme.{u}) (N : B.Modules) (_ : IsInvertibleModule B N),
      IsAmple B N → IsSectionRatio B N) :
    Stacks.RelativeVeryAmple.AmplePullbackGap.{u} :=
  Stacks.AmplePullback.amplePullbackGap_of_basicOpenIsPowNonvanishing fun B N _ hN =>
    basicOpenIsPowNonvanishing_of_isSectionRatio B N (h B N inferInstance hN)

/-- **The content of Stacks Tag 01VN on the surjectivity half of Stacks Tag 01PW**: relative
ampleness is inherited by an immersion over the base. -/
theorem isRelativelyAmple_of_hasRelativeTwistImmersion
    (h : ∀ (B : Scheme.{u}) (N : B.Modules) (_ : IsInvertibleModule B N),
      IsAmple B N → IsSectionRatio B N)
    {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) [IsInvertibleModule Y M]
    (hf : QuasiCompact f) (hr : Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f M) :
    Stacks.RelativeAmple.IsRelativelyAmple f M :=
  Stacks.AmplePullback.isRelativelyAmple_of_hasRelativeTwistImmersion
    (fun B N _ hN => basicOpenIsPowNonvanishing_of_isSectionRatio B N (h B N inferInstance hN))
    f M hf hr

end Stacks.SectionExtension

end
