module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementFibreDegreeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.DiagonalComplementObj
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologicalDimensionGeneralBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FreeActionQuotientQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactDiagonalQuasiAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport

/-!
# The choices (4) and (5) of Stacks 072C

Let `Y` be a quasi-compact, quasi-separated algebraic space over an arbitrary base scheme `S`,
as in the source. The choices (1)–(3) of [Stacks, Tag 072C] — an affine scheme `U`, a surjective
étale morphism `f : U ⟶ Y`, and an integer bounding the degrees of the fibres of `f` — are
`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers'`.
This file makes the remaining two choices: for every `p` an affine scheme `V_p` with a
surjective étale morphism `V_p ⟶ U_p` onto the quotient `U_p = W_p/S_{p+1}` of [Stacks,
Tag 0726], and an integer bounding the degrees of *its* fibres.

Both choices are the same statement again, applied to `U_p` in place of `Y`; what has to be
supplied is that `U_p` is a quasi-compact and quasi-separated algebraic space. That `U_p` is an
algebraic space is [Stacks, Tag 071S], with which
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotient` is formed.
Quasi-compactness passes from `W_p` to `U_p` along the chart `h_{W_p} ⟶ U_p` by
`AlgebraicGeometry.Space.isQuasiCompactSpace_actionQuotient_of_compactSpace`, applied to the
quotient sheaf of a representing object of `W_p` that `U_p` is by
`AlgebraicGeometry.Space.SpacesEtale.diagonalComplementQuotientIsoActionQuotient`, and for `W_p`
itself it is
`AlgebraicGeometry.Space.SpacesEtale.compactSpace_of_iso_underlying_diagonalComplement`.
Quasi-separatedness is got from *separatedness* of `U_p`, which is
`AlgebraicGeometry.Space.SpacesEtale.isAbsolutelySeparated_diagonalComplementQuotient`,
followed by [Stacks, Tag 02X3]. These are the source's two clauses: "since `X` is
quasi-separated the schemes `W_p` are quasi-compact, hence `U_p` is quasi-compact; since `U` is
separated, the schemes `W_p` are separated, hence `U_p` is separated by (the absolute version
of) Spaces, Lemma 65.14.5".

**Why the base is arbitrary.** Neither clause mentions `S`: quasi-compactness of `W_p` comes
from quasi-compactness of `Y` and of the chart, and separatedness of `W_p` from separatedness
of the affine chart, both absolute. Taking the quasi-separatedness of `U_p` through
`AlgebraicGeometry.Space.SpacesEtale.isAbsolutelyQuasiSeparated_diagonalComplementQuotient`
instead would need the *base* to be quasi-separated, because that route reads
quasi-separatedness of the scheme representing `W_p` off the structure morphism to the terminal
object of the site, whose underlying scheme is `S`. The separated route avoids `S` entirely.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isQuasiCompactSpace_diagonalComplementQuotient` and
  `AlgebraicGeometry.Space.SpacesEtale.isAbsolutelyQuasiSeparated_diagonalComplementQuotient`:
  the quotient `U_p` is quasi-compact, and is quasi-separated over a quasi-separated base.
* `AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_diagonalComplementQuotient`:
  **the choices (1)–(5) of [Stacks, Tag 072C]**, the last two for every `p` at once.
* `AlgebraicGeometry.Space.exists_bound_affine_etale_surjective_cover_diagonalComplementQuotient`:
  the same, together with an integer dominating `d_p + p` on the columns that can be nonzero;
  bookkeeping, not the tag, whose vanishing is
  `AlgebraicGeometry.Space.isZero_sheafH_of_boundsFibreDegrees_of_diagonalComplementQuotient`.

## Implementation notes

The chart `U` of choices (1)–(2) is affine, hence separated, so `f : U ⟶ Y` is a separated
morphism by `AlgebraicGeometry.Space.isSeparated_of_isEtale_of_scheme_isSeparated`; this is the
hypothesis `hsep` under which `W_p` is formed, and it is produced inside the statement rather
than assumed. The chart is moreover representable as an object of the site, so that `W_p` is
representable too and `U_p` is the quotient of an object of the big fppf site by a free action
of a finite abstract group; the quasi-compactness and separatedness of `U_p` are read off that
quotient.

Quasi-compactness of the morphism `f`, needed for quasi-compactness of `W_p`, is
[Stacks, Tag 073B] part (1): `U` is quasi-compact and `Y` is quasi-separated.

The maximum `max(d_p + p)` is taken over a finite range because `W_p` has no points once
`p + 1` exceeds the fibre bound `d` of choice (3), which is
`AlgebraicGeometry.Space.SpacesEtale.exists_forall_isEmpty_points_diagonalComplement`; the
integers `d_p` are exposed by `AlgebraicGeometry.Space.BoundsFibreDegrees`, the named bound
whose existential `AlgebraicGeometry.Space.HasUniversallyBoundedFibers` is.

**What is not proved here.** The *conclusion* of [Stacks, Tag 072C] — that the cohomology of
every quasi-coherent module vanishes in degrees `≥ max(d_p + p)` — is not here but in
`StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.QuasiSeparatedVanishing`, as
`AlgebraicGeometry.Space.isZero_sheafH_of_boundsFibreDegrees_of_diagonalComplementQuotient`, which takes the five choices as
hypotheses and is likewise stated over an arbitrary base scheme. What this file supplies is
that those hypotheses can always be met.

## References

* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
* [Stacks Project, Tag 073B](https://stacks.math.columbia.edu/tag/073B)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 02X3](https://stacks.math.columbia.edu/tag/02X3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

namespace SpacesEtale

variable (W : BigFppfOver B S hS) (c : yoneda.obj W ⟶ X.obj) (hc : IsEtale B S hS c)
    (hsep : IsSeparated B S hS c) (n : ℕ)

/-- **The quotient `U_p = W_p/S_{p+1}` is quasi-compact.** The scheme representing `W_p` is
quasi-compact, and `h_{W_p} ⟶ U_p` is a surjective étale chart. -/
theorem isQuasiCompactSpace_diagonalComplementQuotient
    (hXqc : IsQuasiCompactSpace B S hS X.obj) (hcqc : IsQuasiCompact B S hS c) :
    IsQuasiCompactSpace B S hS
      (diagonalComplementQuotient B S hS X (chartObj B S hS X W c hc) (n + 1) hsep).obj := by
  obtain ⟨V, ⟨e⟩⟩ := exists_siteObj_iso_underlying_diagonalComplement B S hS X
    (chartObj B S hS X W c hc) (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj W))) n hsep
  exact IsQuasiCompactSpace.of_iso B S hS
    (isQuasiCompactSpace_actionQuotient_of_compactSpace (Equiv.Perm (Fin (n + 1))) B S hS V _
      (actsFreelyOnNonemptyPoints_diagonalComplementSchemeAut B S hS X
        (chartObj B S hS X W c hc) (n + 1) hsep V e)
      (compactSpace_of_iso_underlying_diagonalComplement B S hS X W c hc hsep (n + 1) V e
        hXqc hcqc))
    (diagonalComplementQuotientIsoActionQuotient B S hS X (chartObj B S hS X W c hc) (n + 1)
      hsep V e).symm

/-- **The quotient `U_p = W_p/S_{p+1}` is quasi-separated.** The scheme representing `W_p` is
quasi-separated, being the complement of the diagonals in a self-product of a quasi-separated
chart over a quasi-separated base, and `h_{W_p} ⟶ U_p` is a surjective étale chart whose kernel
pair has a quasi-compact projection. The quasi-separatedness is the absolute notion of
[Stacks, Tag 03BS] part (3), which is the form the source's reference to Spaces, Lemma 65.14.5
delivers.

This route asks the base `S` to be quasi-separated, because quasi-separatedness of the scheme
representing `W_p` is read off the structure morphism to the terminal object of the site, whose
underlying scheme is `S`. The choices (4)–(5) below therefore do not use it: they take
quasi-separatedness of `U_p` from its *separatedness*, which needs nothing of `S`. -/
theorem isAbsolutelyQuasiSeparated_diagonalComplementQuotient (hSqs : QuasiSeparatedSpace S)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.obj)
    (hWqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj W)) :
    IsAbsolutelyQuasiSeparated B S hS hZ
      (diagonalComplementQuotient B S hS X (chartObj B S hS X W c hc) (n + 1) hsep).obj := by
  obtain ⟨V, ⟨e⟩⟩ := exists_siteObj_iso_underlying_diagonalComplement B S hS X
    (chartObj B S hS X W c hc) (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj W))) n hsep
  exact isAbsolutelyQuasiSeparated_of_iso B S hS hZ
    (diagonalComplementQuotient B S hS X (chartObj B S hS X W c hc) (n + 1) hsep).2
    (diagonalComplementQuotientIsoActionQuotient B S hS X (chartObj B S hS X W c hc) (n + 1)
      hsep V e)
    (isAbsolutelyQuasiSeparated_actionQuotient_of_quasiSeparatedSpace
      (Equiv.Perm (Fin (n + 1))) B S hS V _
      (actsFreelyOnNonemptyPoints_diagonalComplementSchemeAut B S hS X
        (chartObj B S hS X W c hc) (n + 1) hsep V e) hZ
      (quasiSeparatedSpace_toScheme_obj B S hS hZ hSqs V
        (isAbsolutelyQuasiSeparated_of_iso B S hS hZ (isAlgebraicSpace_yoneda B S hS V) e
          (isAbsolutelyQuasiSeparated_underlying_diagonalComplement B S hS hZ X
            (chartObj B S hS X W c hc) hXqs
            (isAbsolutelyQuasiSeparated_yoneda_obj B S hS hZ W hWqs) (n + 1) hsep))))

end SpacesEtale

/-! ### The five choices of Stacks 072C -/

section Choices

variable (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)

include hY in
/-- **The choices (1)–(5) of Stacks 072C.** On a quasi-compact, quasi-separated algebraic space
`Y` over an arbitrary base scheme `S` one may choose an affine scheme `U`, a surjective étale
morphism `f : U ⟶ Y` and a universal bound on the degrees of its fibres — and then, for *every*
`p`, an affine scheme `V_p`, a surjective étale morphism `V_p ⟶ U_p` onto the quotient
`U_p = W_p/S_{p+1}` of [Stacks, Tag 0726], and a universal bound on the degrees of *its*
fibres.

The separatedness of `f`, under which `W_p` and `U_p` are formed, is produced here rather than
assumed. The source restricts `p` to `0 ≤ p ≤ d`; the restriction is dropped, which is
stronger.

Choices (1)–(3) are
`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers'`, and
(4)–(5) are that same statement applied to `U_p`, which is quasi-compact by
`AlgebraicGeometry.Space.SpacesEtale.isQuasiCompactSpace_diagonalComplementQuotient` and
quasi-separated because it is *separated*, by
`AlgebraicGeometry.Space.SpacesEtale.isAbsolutelySeparated_diagonalComplementQuotient` and
[Stacks, Tag 02X3]. Separatedness of `U_p` is what the source itself records — "since `U` is
separated, the schemes `W_p` are separated, hence `U_p` is separated" — and it needs nothing of
the base, which is why the base here is an arbitrary scheme. -/
@[stacks 072C "parts (4)-(5), together with parts (1)-(3) restated, for Y a quasi-compact and \
quasi-separated algebraic space over an arbitrary base scheme S: an affine scheme V_p, a \
surjective etale morphism V_p -> U_p onto the quotient U_p = W_p/S_{p+1} of Tag 0726, and an \
integer bounding the degrees of its fibres, for every p -- the source's range 0 <= p <= d \
being dropped, which is stronger. The integer max(d_p + p) is formed at \
AlgebraicGeometry.Space.exists_bound_affine_etale_surjective_cover_diagonalComplementQuotient; \
the vanishing these choices feed is \
AlgebraicGeometry.Space.isZero_sheafH_of_boundsFibreDegrees_of_diagonalComplementQuotient"]
theorem exists_affine_etale_surjective_cover_diagonalComplementQuotient
    (hqc : IsQuasiCompactSpace B S hS Y)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y)
        (het : IsEtale B S hS g) (hsep : IsSeparated B S hS g),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        HasUniversallyBoundedFibers B S hS U g ∧
        ∀ p : ℕ, ∃ (V : BigFppfOver B S hS)
            (f : yoneda.obj V ⟶ (SpacesEtale.diagonalComplementQuotient B S hS
              ⟨Y, hY⟩ (SpacesEtale.chartObj B S hS ⟨Y, hY⟩ U g het)
              (p + 1) hsep).obj),
          IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
            (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)).presheaf f ∧
            IsEtale B S hS f ∧
            HasUniversallyBoundedFibers B S hS V f := by
  obtain ⟨U, g, hU, hsurj, het, hbd⟩ :=
    exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers'.{u} B S hS hZ Y hY hqc hqs
  have hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hsep : IsSeparated B S hS g :=
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS Y hY U inferInstance g het
  have hcqc : IsQuasiCompact B S hS g :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hY hqs
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS U hU) g
  have hUsep : IsAbsolutelySeparated B S hS hZ
      (SpacesEtale.underlying B S hS ⟨Y, hY⟩
        (SpacesEtale.chartObj B S hS ⟨Y, hY⟩ U g het)).obj :=
    isAbsolutelySeparated_of_isAffineSpace B S hS hZ (isAffineSpace_yoneda B S hS U hU)
  refine ⟨U, g, het, hsep, hU, hsurj, hbd, fun p => ?_⟩
  exact exists_affine_etale_surjective_cover_hasUniversallyBoundedFibers'.{u} B S hS hZ _
    (SpacesEtale.diagonalComplementQuotient B S hS ⟨Y, hY⟩
      (SpacesEtale.chartObj B S hS ⟨Y, hY⟩ U g het) (p + 1) hsep).2
    (SpacesEtale.isQuasiCompactSpace_diagonalComplementQuotient B S hS
      ⟨Y, hY⟩ U g het hsep p hqc hcqc)
    (isQuasiSeparatedOver_of_isSeparatedOver B (⊤_ Scheme.{u}) hZ _
      (SpacesEtale.isAbsolutelySeparated_diagonalComplementQuotient B S hS hZ ⟨Y, hY⟩
        (SpacesEtale.chartObj B S hS ⟨Y, hY⟩ U g het) p hsep
        (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj U))) hUsep))

include hY in
/-- **An integer dominating `d_p + p`, beside the five choices.** On a quasi-compact and
quasi-separated algebraic space there are choices (1)–(5) as in [Stacks, Tag 072C] together with
a single integer `N` dominating `d_p + p` for every `p` whose column can be nonzero: the `d`
produced here is the threshold above which `W_q` has no points, got from the fibre bound of
choice (3), the domination is asserted for the `p` with `p + 1 ≤ d`, and `N` is the maximum of
`d_p + p` over those.

This is bookkeeping for the tag, not the tag: its `d` is the emptiness threshold rather than the
fibre bound of choice (3), and it states no vanishing.  [Stacks, Tag 072C] itself — the vanishing
`H^q(X, ℱ) = 0` for `q ≥ max (d_p + p)` from any choices (1)–(5) — is
`AlgebraicGeometry.Space.isZero_sheafH_of_boundsFibreDegrees_of_diagonalComplementQuotient`, and
the choices exist by
`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_diagonalComplementQuotient`. -/
theorem exists_bound_affine_etale_surjective_cover_diagonalComplementQuotient
    (hqc : IsQuasiCompactSpace B S hS Y)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y) :
    ∃ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ Y)
        (het : IsEtale B S hS g) (hsep : IsSeparated B S hS g)
        (d : ℕ) (N : ℤ),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf g ∧
        HasUniversallyBoundedFibers B S hS U g ∧
        (∀ q : ℕ, d < q → IsEmpty (points B S hS
          (SpacesEtale.underlying B S hS ⟨Y, hY⟩
            (SpacesEtale.diagonalComplement B S hS ⟨Y, hY⟩
              (SpacesEtale.chartObj B S hS ⟨Y, hY⟩ U g het) q hsep)).obj)) ∧
        ∀ p : ℕ, ∃ (V : BigFppfOver B S hS)
            (f : yoneda.obj V ⟶ (SpacesEtale.diagonalComplementQuotient B S hS
              ⟨Y, hY⟩ (SpacesEtale.chartObj B S hS ⟨Y, hY⟩ U g het)
              (p + 1) hsep).obj) (dp : ℤ),
          IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
            (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
              (BigFppfOver.toScheme B S hS)).presheaf f ∧
            IsEtale B S hS f ∧
            BoundsFibreDegrees B S hS V f dp ∧
            (p + 1 ≤ d → dp + p ≤ N) := by
  classical
  obtain ⟨U, g, het, hsep, hU, hsurj, hbd, hall⟩ :=
    exists_affine_etale_surjective_cover_diagonalComplementQuotient.{u} B S hS hZ Y hY hqc hqs
  obtain ⟨d, hd⟩ := SpacesEtale.exists_forall_isEmpty_points_diagonalComplement
    B S hS ⟨Y, hY⟩ U g het hsep hbd
  choose V f hV hfsurj hfet hfbd using hall
  choose dp hdp using hfbd
  refine ⟨U, g, het, hsep, d,
    (((Finset.range (d + 1)).sup fun p => (dp p + p).toNat : ℕ) : ℤ),
    hU, hsurj, hbd, hd, fun p => ?_⟩
  refine ⟨V p, f p, dp p, hV p, hfsurj p, hfet p, hdp p, fun hple => ?_⟩
  have hmem : p ∈ Finset.range (d + 1) := Finset.mem_range.2 (by omega)
  have hsup : (dp p + p).toNat ≤
      (Finset.range (d + 1)).sup fun q => (dp q + q).toNat :=
    Finset.le_sup (f := fun q => (dp q + q).toNat) hmem
  exact (Int.self_le_toNat (dp p + p)).trans (Int.ofNat_le.2 hsup)

end Choices

end AlgebraicGeometry.Space

end
