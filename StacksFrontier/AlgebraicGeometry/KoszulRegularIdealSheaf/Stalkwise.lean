module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.KoszulRegularIdealSheaf.Affine
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence

/-!
# The sheaf-exactness and stalkwise forms of Koszul-regularity agree

Koszul-regularity of a family of sections of the structure sheaf, Stacks tag 063D part (2), has
two renderings, and the development carries both.

* The **sheaf-exactness** form asks that the Koszul complex of the family be exact in every
  positive degree *as a complex of sheaves*: every Koszul cycle over an open is locally a Koszul
  boundary.  That is
  `Stacks.AlgebraicGeometry.KoszulRegularIdealSheaf.IsKoszulRegularSequenceOn`.
* The **stalkwise** form asks that the ring-level Koszul homology of the *germs* of the family
  vanish in every positive degree.  That is
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulSequenceExactOn` with `P = (0 < ·)`, and the
  ideal-sheaf condition built from it is
  `Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularIdealSheaf`.

Over an affine open the two are the same condition, and this file proves it, once, so that nothing
downstream needs a third rendering or a private shortcut past one of the two.  Both are equal to
Koszul-regularity of the family in the ring of sections: on the sheaf side by
`KoszulRegularIdealSheaf.isKoszulRegularSequenceOn_iff_isKoszulRegular`, which tests the sheaf
condition on the basic opens — where the ring of sections is a localization — and on the stalk side
by `AlgebraicGeometry.forall_isKoszulRegular_germFamily_iff`, which is flat base change for Koszul
homology in one direction and the locality of Koszul-regularity on the spectrum in the other.  The
affine criterion of Stacks tag 063G for an ideal sheaf then needs only that the affine opens form a
basis, so that a witness open of the stalkwise condition may be shrunk to an affine one.

## Main results

* `KoszulRegularIdealSheaf.isKoszulRegularSequenceOn_iff_isKoszulSequenceExactOn`: over an affine
  open the two forms of **Stacks tag 063D part (2)** for a family of sections agree.
* `RegularIdealSheaf.isKoszulRegularIdealSheaf_iff_affine`: **Stacks tag 063G** for the stalkwise
  form, which is the shape a hypothesis of Stacks tag 063J part (2) is consumed in.

## Implementation notes

The comparison of the two sequence conditions is stated only over an *affine* open, which is where
it is true by the two results it is assembled from; the sheaf condition on a general open is not a
pointwise condition, so no such statement is available there without a covering argument that the
ideal-sheaf definitions already perform.

`AlgebraicGeometry.forall_isKoszulRegular_germFamily_iff` lives with the fpqc-descent material for
regular immersions, which is where it was first needed, and is the only input of this file that is
not local to `Stacks.AlgebraicGeometry.KoszulRegularIdealSheaf` or
`Stacks.AlgebraicGeometry.RegularIdealSheaf`; the import exists for it alone.

## References

* [Stacks Project, Definition 31.20.1 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 31.20.4 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Definition 31.21.1 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.QuasiRegular
open Stacks.RingedSpace

universe u

namespace Stacks.AlgebraicGeometry

namespace KoszulRegularIdealSheaf

/-- Over an affine open, positive-degree Koszul exactness of the germs is Koszul-regularity in the
ring of sections. -/
private theorem isKoszulSequenceExactOn_iff_isKoszulRegular (X : Scheme.{u}) {U : X.Opens}
    (hU : IsAffineOpen U) {r : ℕ} (f : Fin r → Γ(X, U)) :
    RegularIdealSheaf.IsKoszulSequenceExactOn X.toRingedSpace U f (0 < ·) ↔
      Koszul.IsKoszulRegular f :=
  (RegularIdealSheaf.isKoszulSequenceExactOn_iff_forall_germ_isKoszulRegular
    X.toRingedSpace U f).trans (forall_isKoszulRegular_germFamily_iff X hU f)

/-- **Over an affine open the two forms of Stacks tag 063D part (2) for a family of sections
agree.** Local exactness of the sheaf Koszul complex of `f` in positive degrees is the vanishing
of the Koszul homology of the germs of `f` at every point of the open, in positive degrees.

Both are Koszul-regularity of `f` in `Γ(X, U)`: the sheaf condition because it may be tested on
the basic opens of `U`, whose rings of sections are the localizations of `Γ(X, U)`, and the
stalkwise condition because each stalk over `U` is the localization of `Γ(X, U)` at the prime of
the corresponding point. -/
theorem isKoszulRegularSequenceOn_iff_isKoszulSequenceExactOn (X : Scheme.{u}) {U : X.Opens}
    (hU : IsAffineOpen U) {r : ℕ} (f : Fin r → Γ(X, U)) :
    IsKoszulRegularSequenceOn X.toRingedSpace U f ↔
      RegularIdealSheaf.IsKoszulSequenceExactOn X.toRingedSpace U f (0 < ·) :=
  (isKoszulRegularSequenceOn_iff_isKoszulRegular X U f hU).trans
    (isKoszulSequenceExactOn_iff_isKoszulRegular X hU f).symm

end KoszulRegularIdealSheaf

namespace RegularIdealSheaf

/-- **Stacks Project, Tag 063G (`koszul_regular`).** A sheaf of ideals on a scheme is
Koszul-regular if and only if, around each point of the support of its quotient, it is generated
on an affine open by a sequence which is Koszul-regular in the ring of sections of that open. -/
@[stacks 063G "koszul_regular"]
theorem isKoszulRegularIdealSheaf_iff_affine (X : Scheme.{u})
    (J : (structureSheafModule X.toRingedSpace).Submodule) :
    IsKoszulRegularIdealSheaf X.toRingedSpace J ↔
      ∀ x : X, x ∈ idealQuotientSupport X.toRingedSpace J →
        ∃ (U : X.affineOpens) (_hx : x ∈ (U : Set X)) (r : ℕ) (f : Fin r → Γ(X, U.1)),
          IsGeneratedByOn X.toRingedSpace J U.1 f ∧ Koszul.IsKoszulRegular f := by
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · obtain ⟨U₀, hxU₀, r, f, hreg, hgen⟩ := h x hx
    obtain ⟨V, hV, hxV, hVU₀⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxU₀
    refine ⟨⟨V, hV⟩, hxV, r, fun i => X.presheaf.map (homOfLE hVU₀).op (f i),
      RegularIdealSheaf.isGeneratedByOn_of_le U₀ f hgen V hVU₀, ?_⟩
    exact (KoszulRegularIdealSheaf.isKoszulSequenceExactOn_iff_isKoszulRegular X hV _).mp
      (hreg.of_le V hVU₀)
  · obtain ⟨U, hxU, r, f, hgen, hf⟩ := h x hx
    exact ⟨U.1, hxU, r, f,
      (KoszulRegularIdealSheaf.isKoszulSequenceExactOn_iff_isKoszulRegular X U.2 f).mpr hf,
      hgen⟩

end RegularIdealSheaf

end Stacks.AlgebraicGeometry

end
