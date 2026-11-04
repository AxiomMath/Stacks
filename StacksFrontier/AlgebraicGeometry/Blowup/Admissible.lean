module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Admissible blowups

Let `X` be a scheme and `U ⊆ X` an open subscheme. A morphism `X' ⟶ X` is a *`U`-admissible
blowup* when there is a closed immersion `Z ⟶ X` of finite presentation whose image is disjoint
from `U`, such that `X'` is isomorphic to the blowup of `X` in `Z` compatibly with the morphisms
to `X`.

The centre `Z` is recorded here as the quasi-coherent sheaf of ideals cutting it out, Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData`: a closed immersion into `X` is the same thing as such
an ideal sheaf, with `Z` recovered as `AlgebraicGeometry.Scheme.IdealSheafData.subscheme` and
`Z ⟶ X` as `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`, so the quantifier over closed
immersions `Z ⟶ X` becomes a quantifier over ideal sheaves. The blowup of `X` in `Z` is then
`Stacks.Blowup.blowUp I`, with structure morphism `Stacks.Blowup.blowUpToBase I`.

"Disjoint from `U`" is disjointness of `U` from the support of `I`, which is exactly the image of
`Z ⟶ X` by `AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`.

## Main definitions

* `Stacks.Blowup.IsAdmissibleBlowup` is the predicate of being a `U`-admissible blowup.

## Main results

* `Stacks.Blowup.isAdmissibleBlowup_blowUpToBase` recognizes the blowup in a finitely presented
  centre disjoint from `U` as `U`-admissible.
* `Stacks.Blowup.IsAdmissibleBlowup.isSeparated`: a `U`-admissible blowup is separated.
* `Stacks.Blowup.IsAdmissibleBlowup.isProper_of_fg`: a `U`-admissible blowup is proper once its
  centre is of finite type.

## Implementation notes

The predicate is an `abbrev` with its existential witness exposed, rather than a structure or an
opaque `def`: Stacks tags 080L, 080Y, 080B, 080I and 0815 all quantify over admissible blowups
and have to produce or consume the centre directly. This follows
`AlgebraicGeometry.FinitePresentation`, the conjunctive predicate of tag 01TP that appears inside
it, which is an `abbrev` for the same reason.

Projectivity is *not* part of the definition. Stacks notes after the definition that a
`U`-admissible blowup is projective, via tag 02NS and the finite-type criterion of tag 01TV; that
is a consequence of the definition, not part of it. Tag 02NS part (2) IS formalized, as
`AlgebraicGeometry.isRelativelyAmple_twist_reesSituation` in
`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/TwistAmple.lean`, carrying a
`Stacks.RelativeProj.Situation.TwistTransition 1` hypothesis; it is the projectivity statement
that is not placed, for the reason given at the end of
`StacksFrontier/AlgebraicGeometry/Blowup/Proper.lean`. What is recorded here instead is the
properness statement that file does supply, which takes finite type of the centre as a hypothesis
rather than deriving it from finite presentation of `I.subschemeι` — the route from tag 01TV is
not formalized here.

## References

* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Blowup

variable {X X' : Scheme.{u}}

/-- A morphism `f : X' ⟶ X` is a **`U`-admissible blowup** if there is a quasi-coherent sheaf of
ideals `I` on `X` whose closed subscheme is of finite presentation over `X` and supported away
from `U`, together with an isomorphism of `X'` with the blowup of `X` in `I` carrying the blowup
morphism to `f`. -/
@[stacks 080K]
abbrev IsAdmissibleBlowup (U : X.Opens) (f : X' ⟶ X) : Prop :=
  ∃ I : X.IdealSheafData,
    FinitePresentation I.subschemeι ∧
      Disjoint (U : Set X) (I.support : Set X) ∧
        ∃ e : X' ≅ blowUp I, e.hom ≫ blowUpToBase I = f

variable {U : X.Opens} {f : X' ⟶ X}

/-- The blowup of `X` in a finitely presented centre disjoint from `U` is a `U`-admissible
blowup. -/
theorem isAdmissibleBlowup_blowUpToBase {I : X.IdealSheafData}
    (hfp : FinitePresentation I.subschemeι)
    (hdisj : Disjoint (U : Set X) (I.support : Set X)) :
    IsAdmissibleBlowup U (blowUpToBase I) :=
  ⟨I, hfp, hdisj, Iso.refl _, Category.id_comp _⟩

namespace IsAdmissibleBlowup

/-- A `U`-admissible blowup is separated, with no hypothesis on the centre. -/
theorem isSeparated (h : IsAdmissibleBlowup U f) : IsSeparated f := by
  obtain ⟨I, -, -, e, he⟩ := h
  rw [← he]
  infer_instance

/-- A `U`-admissible blowup is proper as soon as the centre exhibiting it is of finite type. -/
theorem isProper_of_fg {I : X.IdealSheafData} (e : X' ≅ blowUp I)
    (he : e.hom ≫ blowUpToBase I = f) (hfg : ∀ V : X.affineOpens, (I.ideal V).FG) :
    IsProper f := by
  have : IsProper (blowUpToBase I) := isProper_blowUpToBase I hfg
  rw [← he]
  infer_instance

end IsAdmissibleBlowup

end Stacks.Blowup

end
