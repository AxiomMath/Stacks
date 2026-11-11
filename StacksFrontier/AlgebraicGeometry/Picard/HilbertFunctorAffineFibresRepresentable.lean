module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineFibres
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorAffineRepresentableUnconditional
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenCoverRepresentable

/-!
# Representability of the Hilbert functor when points of a fibre lie in an affine open

Let `X ⟶ S` be a separated morphism of schemes and let `d` be a natural number such that any
`d` points of a fibre of `X ⟶ S` lie in an affine open of `X`. Then the degree-`d` Hilbert functor
of `X` over `S` is representable by a scheme. The same holds without separatedness if any `d + 1`
points of a fibre lie in an affine open. Both strengthen the hypothesis of Stacks Proposition
0B9A, which is false as printed, and this file assembles their proof:

* over an affine base, the gluing criterion of Stacks 01JJ is applied to the subfunctors
  `Stacks.Hilbert.supportedIn X d U` of families supported in an affine open `U ⊆ X`, which are
  open, cover the field-valued points by the hypothesis, and are represented by the Hilbert
  scheme of `U`, which exists by Stacks 0B99;
* over a general base, the criterion is applied to the subfunctors `Stacks.Hilbert.overOpen X d V`
  of families over bases mapping into an affine open `V ⊆ S`, represented by the Hilbert scheme of
  `X ×_S V` over `V` from the affine case. This is the reduction the source omits.

As an application, the degree-`d` Hilbert scheme of a projective scheme over an affine base, in
particular over a field, exists.

## Main results

* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_affineFibres_of_isAffine` — the case
  of an affine base.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_forall_affineOpens` — the reduction to
  an affine base.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_affineFibres` — representability for
  separated `X ⟶ S` and every `d`.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_affineFibres_succ` — representability
  without separatedness, when any `d + 1` points of a fibre lie in an affine open, as in the
  footnote to the source's proof.
* `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism` — the Hilbert
  scheme of points of a projective scheme over an affine base.

## Implementation notes

*Why separatedness, or a `(d + 1)`-st point, is assumed.* The source states 0B9A for an arbitrary
morphism `X ⟶ S`. That statement is false: for the affine line `X` with a doubled origin over
`S = 𝔸¹` and `d = 1`, the hypothesis holds trivially, but the functor is not representable. Over
each thickening `Spec k[t]/(t^n)` of the origin, the inclusion into one copy of `𝔸¹` gives a point
of the functor, as the section it induces has a one-point, hence closed, image; these are
compatible, so a representing scheme would have a point over `Spec k[[t]]` restricting to them. The
only candidate is the section of `X_{k[[t]]} ⟶ Spec k[[t]]` induced by `k[t] ⟶ k[[t]]`, whose image
is not closed: its closure contains the other origin. The source's proof breaks at the
identification `F_U = Hilb^d_{U/S}`, whose footnote argues from an affine open containing `d + 1`
points of a fibre. The identification `Stacks.Hilbert.supportedInIso` holds whenever the families
in `U` are closed in `X_T` (`Stacks.Hilbert.ClosedInAmbient`): for separated `X ⟶ S`, and, by the
footnote's argument `Stacks.Hilbert.isClosed_range_of_affineFibres_succ`, when any `d + 1` points
of a fibre lie in an affine open. Every application listed in Stacks 0B9B is separated.

Neither theorem here carries the `@[stacks 0B9A]` attribute, since each assumes more than the
corrected statement of the tag: the tag is registered on
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_isSeparated`
in `StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean`, which assumes
the source's `d`-tuple hypothesis for every `d` and separatedness at `d = 1` alone, as recorded in
`errata.md`.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 0B9B](https://stacks.math.columbia.edu/tag/0B9B)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Hilbert

variable {S : Scheme.{u}}

/-- **The reduction of Stacks 0B9A to an affine base** ("Details omitted" in the source). If for
every affine open `V ⊆ S` the degree-`d` Hilbert functor of `X ×_S V` over `V` is representable,
then so is the degree-`d` Hilbert functor of `X` over `S`: the subfunctors of families over bases
mapping into an affine open `V` are open, cover the field-valued points, and are represented by
the Hilbert schemes of the `X ×_S V`. -/
theorem exists_representsHilbertFunctorOfRank_of_forall_affineOpens (X : Over S) (d : ℕ)
    (h : ∀ V : S.affineOpens,
      Nonempty (Σ H : Over V.1.toScheme, RepresentsHilbertFunctorOfRank (baseRestrict X V.1) H d)) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  refine exists_representsHilbertFunctorOfRank_of_isOpenHilbertSubfunctor X d
    (fun V : S.affineOpens => overOpen X d V.1)
    (fun V => isOpenHilbertSubfunctor_overOpen X d V.1) (fun V => ?_) (fun k _ g Z => ?_)
  · obtain ⟨⟨H, hH⟩⟩ := h V
    exact ⟨(Over.map V.1.ι).obj H, ⟨overOpenRepresentableBy hH.representableBy⟩⟩
  · refine exists_mem_overOpen_of_specField X d (fun V : S.affineOpens => V.1) (fun s => ?_) k g Z
    obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
    exact ⟨⟨V, hV⟩, hsV⟩

/-- **Stacks 0B9A over an affine base, from closedness of families in opens.** Let `X ⟶ S` be a
morphism to an affine scheme such that any `d` points of a fibre lie in an affine open of `X`,
and such that degree-`d` families in every open of `X` are closed in `X ×_S T`. Then the
degree-`d` Hilbert functor of `X` is representable: the subfunctors of families supported in the
affine opens of `X` are open, cover the field-valued points, and are the Hilbert functors of
those affine opens, which are representable by Stacks 0B99. -/
theorem exists_representsHilbertFunctorOfRank_of_affineFibres_of_closedInAmbient [IsAffine S]
    (X : Over S) (d : ℕ) (hc : ∀ U : X.left.Opens, ClosedInAmbient X d U)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  refine exists_representsHilbertFunctorOfRank_of_isOpenHilbertSubfunctor X d
    (fun U : X.left.affineOpens => supportedIn X d U.1)
    (fun U => isOpenHilbertSubfunctor_supportedIn X d U.1) (fun U => ?_) (fun k _ g Z => ?_)
  · have : IsAffine (restrictOver X U.1).left := U.2
    have := hc U.1
    obtain ⟨⟨H, h⟩⟩ := exists_representsHilbertFunctorOfRank_of_isAffine_of_isAffine
      (restrictOver X U.1) d
    exact ⟨H, ⟨supportedInRepresentableBy h.representableBy⟩⟩
  · obtain ⟨U, hU, hZ⟩ := exists_isAffineOpen_mem_supportedIn_of_specField X d hX k g Z
    exact ⟨⟨U, hU⟩, hZ⟩

/-- **Stacks 0B9A over an affine base.** Let `X ⟶ S` be a separated morphism to an affine
scheme such that any `d` points of a fibre lie in an affine open of `X`. Then the degree-`d`
Hilbert functor of `X` is representable. -/
theorem exists_representsHilbertFunctorOfRank_of_affineFibres_of_isAffine [IsAffine S]
    (X : Over S) [IsSeparated X.hom] (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) :=
  exists_representsHilbertFunctorOfRank_of_affineFibres_of_closedInAmbient X d
    (fun _ => inferInstance) hX

/-- **The Hilbert functor of points of a separated morphism is representable.** Let `X ⟶ S` be
a separated morphism of schemes and let `d` be a natural number such that for every `s ∈ S` and
all points `x₁, …, x_d` of the fibre `X_s` there is an affine open of `X` containing them. Then
the degree-`d` Hilbert functor of `X` over `S` is representable by a scheme.

The subfunctors of families over bases mapping into an affine open `V ⊆ S` are open, cover the
field-valued points, and are represented by the Hilbert scheme of `X ×_S V` over `V`, which
exists by the affine case since the hypothesis passes to `X ×_S V ⟶ V`.

Stacks Tag 0B9A states this without separatedness, and is false so stated. Let `X` be the
affine line with a doubled origin over `𝔸¹` and `d = 1`; the hypothesis holds. Over each
`Spec k[t]/(t^n)` the inclusion into one copy of `𝔸¹` is a point of the Hilbert functor, these
are compatible, and compatible maps from all `Spec k[t]/(t^n)` to a scheme come from a map from
`Spec k[[t]]`; but the only candidate section of `X_{k[[t]]} ⟶ Spec k[[t]]` has non-closed
image, so the functor is not representable. The source's footnote, which proves `F_U = Hilb^d_U`
without separatedness, uses an affine open containing `d + 1` points of a fibre: the `d` points of
`Z_t` and one more point of the closure of `Z`. The corrected statement of the tag, which needs
separatedness at `d = 1` alone, is
`nonempty_representsHilbertFunctorOfRank_of_exists_isAffineOpen_forall_mem_of_isSeparated`. -/
theorem exists_representsHilbertFunctorOfRank_of_affineFibres (X : Over S) [IsSeparated X.hom]
    (d : ℕ)
    (hX : ∀ (s : S) (x : Fin d → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  refine exists_representsHilbertFunctorOfRank_of_forall_affineOpens X d fun V => ?_
  have : IsAffine V.1.toScheme := V.2
  have : IsSeparated (baseRestrict X V.1).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X.hom V.1.ι))
  exact exists_representsHilbertFunctorOfRank_of_affineFibres_of_isAffine
    (baseRestrict X V.1) d (baseRestrict_affineFibres X d hX V.1)

/-- **Representability of the Hilbert functor of points, in the form of the footnote to the
proof of Stacks Tag 0B9A.** Let `X ⟶ S` be a morphism of schemes and let `d` be a natural
number such that for every `s ∈ S` and all points `x₀, …, x_d` of the fibre `X_s` there is an
affine open of `X` containing them. Then the degree-`d` Hilbert functor of `X` over `S` is
representable by a scheme.

No separatedness is assumed; the hypothesis asks for `d + 1` points of a fibre, which is what
the source's footnote uses to show that a family in an open `U ⊆ X` is closed in `X_T`
(`Stacks.Hilbert.isClosed_range_of_affineFibres_succ`). With `d` points instead of `d + 1` the
statement is false, by the affine line with a doubled origin over `𝔸¹` and `d = 1`, as recorded
on `Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_affineFibres`. -/
theorem exists_representsHilbertFunctorOfRank_of_affineFibres_succ (X : Over S) (d : ℕ)
    (hX : ∀ (s : S) (x : Fin (d + 1) → X.left), (∀ i, X.hom (x i) = s) →
      ∃ U : X.left.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  refine exists_representsHilbertFunctorOfRank_of_forall_affineOpens X d fun V => ?_
  have : IsAffine V.1.toScheme := V.2
  have hV := baseRestrict_affineFibres X (d + 1) hX V.1
  exact exists_representsHilbertFunctorOfRank_of_affineFibres_of_closedInAmbient
    (baseRestrict X V.1) d (closedInAmbient_of_affineFibres_succ _ d hV)
    (affineFibres_of_affineFibres_succ _ d hV)

/-- **The Hilbert scheme of points of a projective scheme over an affine base exists**, in
particular over a field: for `X` projective over an affine scheme `S` and any `d`, the degree-`d`
Hilbert functor of `X` is representable. Any finitely many points of `X` lie in an affine open,
and a projective morphism is separated, so
`Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_affineFibres` applies. For `X` over a
field `k` the representing scheme is the scheme `S^d(X) = Hilb^d_{X/k}` of the source's Section
0FH9 hint. -/
theorem exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism [IsAffine S] (X : Over S)
    (hX : IsProjectiveMorphism X.hom) (d : ℕ) :
    Nonempty (Σ H : Over S, RepresentsHilbertFunctorOfRank X H d) := by
  have : IsProper X.hom := isProper_of_isProjectiveMorphism X.hom hX
  exact exists_representsHilbertFunctorOfRank_of_affineFibres X d
    (affineFibres_of_isProjectiveMorphism X hX d)

/-- The degree-`d` Hilbert functor of a projective scheme over an affine base is representable,
in the sense of `CategoryTheory.Functor.IsRepresentable`; its representing object is
`Stacks.Hilbert.hilbertScheme X d`. -/
theorem isRepresentable_hilbertFunctorOfRank_of_isProjectiveMorphism [IsAffine S] (X : Over S)
    (hX : IsProjectiveMorphism X.hom) (d : ℕ) : (hilbertFunctorOfRank X d).IsRepresentable := by
  obtain ⟨⟨H, h⟩⟩ := exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism X hX d
  exact h.representableBy.isRepresentable

end Stacks.Hilbert

end
