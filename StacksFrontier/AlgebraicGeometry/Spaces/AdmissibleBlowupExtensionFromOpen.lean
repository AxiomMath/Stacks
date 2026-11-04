module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceExtension

/-!
# Extending an admissible blowup from a quasi-compact open subspace

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S` and
let `U, V ⊆ X` be quasi-compact open subspaces.  Tag 086D asserts that every `U ∩ V`-admissible
blowup `b : V' ⟶ V` is the restriction to `V` of a `U`-admissible blowup `X' ⟶ X`.

The source's proof has three steps: the centre of `b` is extended to `X`, away from `U`, by
Tag 0853; the blowup of `X` in the extended centre is formed; and its restriction to `V` is the
blowup of `V` in the restricted centre.  All three are proved in this development, and this file
assembles them.

* The extension of the centre is
  `AlgebraicGeometry.Space.exists_closedSubspace_extension_disjoint`, which works with finitely
  presented closed subspaces rather than with finite type quasi-coherent ideals, and is proved
  by the induction principle of Tag 08GP rather than by Noetherian approximation.
* The blowup in a finitely presented closed subspace exists by
  `AlgebraicGeometry.Space.exists_isBlowupAlong_of_isFinitePresentation` (Tags 085Q and 085U).
* The restriction clause is
  `AlgebraicGeometry.Space.IsBlowupAlong.exists_restrictionToOpen`.

## Main results

* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isPullback'`: **Tag 086D**.

## References

* [Stacks Project, Tag 086D](https://stacks.math.columbia.edu/tag/086D)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 086D.**  Let `X` be a quasi-compact and quasi-separated algebraic space over `S`,
let `U, V ⊆ X` be quasi-compact open subspaces and let `b : V' ⟶ V` be a `U ∩ V`-admissible
blowup.  Then there is a `U`-admissible blowup `f : X' ⟶ X` whose restriction to `V` is `V'`,
the restriction being recorded as a cartesian square.

The extension of the centre is
`AlgebraicGeometry.Space.exists_closedSubspace_extension_disjoint`: the centre `W ⊆ V` of `b`,
together with the empty closed subspace on `U`, extends to a finitely presented `Z ⊆ X` whose
points avoid those of `U` and with `Z ∩ V = W`, by the induction principle of Stacks 08GP.  The
blowup of `X` in `Z` exists by
`AlgebraicGeometry.Space.exists_isBlowupAlong_of_isFinitePresentation`, it is `U`-admissible,
and by `AlgebraicGeometry.Space.IsBlowupAlong.exists_restrictionToOpen` its restriction to `V`
is the blowup of `V` in `Z ∩ V = W`, hence isomorphic over `V` to `V'`. -/
@[stacks 086D]
theorem exists_isAdmissibleBlowup_isPullback'
    (hZ : B.Contains (⊤_ Scheme.{u})) {X V' : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U V : OpenSubspaces B S hS X.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hVqc : IsQuasiCompactSpace B S hS V.1.toFunctor)
    (b : V' ⟶ openSubspace B S hS X V)
    (hb : IsAdmissibleBlowup B S hS (openSubspaceRestrict B S hS X V U) b) :
    ∃ (X' : AlgebraicSpaces B S hS) (f : X' ⟶ X), IsAdmissibleBlowup B S hS U f ∧
      ∃ e : V' ⟶ X', IsPullback b e (openSubspaceι B S hS X V) f := by
  obtain ⟨W, hWfp, hWdisj, hWb⟩ := hb
  obtain ⟨Z, hZc, hZfp, hZdisj, hZW⟩ := exists_closedSubspace_extension_disjoint hZ hXqc hXqs
    U.1 V.1 U.2 V.2 hUqc hVqc W.1 W.2 hWfp hWdisj
  obtain ⟨X', f, hf⟩ := exists_isBlowupAlong_of_isFinitePresentation ⟨Z, hZc⟩ hZfp
  obtain ⟨P, p, q, hsq, hp⟩ := hf.exists_restrictionToOpen V ⟨Z, hZc⟩
  have hWeq : closedSubspaceRestrict B S hS X V ⟨Z, hZc⟩ = W := Subtype.ext hZW
  rw [← hWeq] at hWb
  obtain ⟨e, he⟩ := hWb.exists_iso hp
  refine ⟨X', f, ⟨⟨Z, hZc⟩, hZfp, hZdisj, hf⟩, e.hom ≫ q, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ (e ≪≫ hsq.isoPullback) ?_ ?_
  · rw [← he, Category.assoc, Category.assoc, hsq.w]
  · rw [Iso.trans_hom, Category.assoc, hsq.isoPullback_hom_fst, he]
  · rw [Iso.trans_hom, Category.assoc, hsq.isoPullback_hom_snd]

end AlgebraicGeometry.Space

end
