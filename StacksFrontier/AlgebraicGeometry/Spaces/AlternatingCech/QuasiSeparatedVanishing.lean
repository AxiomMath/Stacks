module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.AffineSerreFromCech
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.BoundedRowVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.ColumnVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuotientSeparatedAbsolute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleQuasicoherentCechVanishing

/-!
# Higher vanishing on a quasi-compact quasi-separated algebraic space

Let `S` be a scheme and let `X` be a quasi-compact and quasi-separated algebraic space over `S`.
Choose, as in [Stacks, Tag 072C]:

1. an affine scheme `U`;
2. a surjective étale morphism `f : U ⟶ X`;
3. an integer `d` bounding the degrees of the fibres of `f`;
4. for each `p` with `0 ≤ p ≤ d` an affine scheme `V_p` and a surjective étale morphism
   `V_p ⟶ U_p` onto the quotient `U_p = W_{p+1}/S_{p+1}` of the complement of the diagonals in
   the `(p+1)`-fold self-product of `U` over `X`;
5. an integer `d_p` bounding the degrees of the fibres of `V_p ⟶ U_p`.

Then `H^q(X, ℱ) = 0` for every quasi-coherent `𝒪_X`-module `ℱ` and every `q ≥ max (d_p + p)`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_boundsFibreDegrees`:
  **[Stacks, Tag 072B] with the source's explicit bound**, on a separated algebraic space with an
  affine surjective étale chart whose fibre degrees are bounded by `d`: the cohomology of
  quasi-coherent coefficients vanishes in every degree `n ≥ d`.
* `AlgebraicGeometry.Space.SpacesEtale.isZero_zExt_koszulComplex_X_of_chart_over_quotient`: the
  column `p` of the `E₁`-page of [Stacks, Tag 0728] vanishes in the degrees `q ≥ d_p`, which is
  the source's application of Tag 072B to `U_p`.
* `AlgebraicGeometry.Space.isZero_sheafH_of_data_072C`: **[Stacks, Tag 072C]**, the vanishing
  `H^q(X, ℱ) = 0` for `q ≥ max (d_p + p)`.
* `AlgebraicGeometry.Space.exists_forall_isZero_sheafH_of_isQuasiCompactSpace_072C`:
  **[Stacks, Tag 072C] end to end** — the five choices and the vanishing they give, combined
  into the statement that a quasi-compact quasi-separated algebraic space over an arbitrary
  base scheme has a single degree beyond which quasi-coherent cohomology vanishes.

## Implementation notes

**The two levels of the recursion.** The outer level is the alternating Čech spectral sequence of
[Stacks, Tag 0728] for the chart `f : U ⟶ X`, whose convergence at explicit column bounds is
`AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_zExt_column_bounds`.  Its column `p` is
`Ext` out of the sign twist of `W_{p+1}` on the spaces-étale site of `U_p`, hence — the twist
being locally free of rank one, `W_{p+1}` being a torsor over `U_p` — the cohomology of `U_p`
with coefficients twisted by the sign character; those coefficients are again quasi-coherent, by
[Stacks, Tag 072A].  The inner level is Tag 072B for the chart `V_p ⟶ U_p`, and it is the *same*
spectral sequence: `U_p` is separated, by
`AlgebraicGeometry.Space.SpacesEtale.isAbsolutelySeparated_diagonalComplementQuotient`, so the
quotients formed from `V_p` over `U_p` are affine and the inner columns vanish in *every*
positive degree.  Taking the inner column bounds all equal to one turns the convergence step into
the vanishing above `d_p`, which is the source's "`H^q(U_p, 𝒢) = 0` for `q ≥ d_p`".

**Why the inner level needs no hypothesis on `X`.** The affineness of the quotients formed from
`V_p` over `U_p` is [Stacks, Tag 03BM] applied to `W'_{p'+1} ⊆ V_p^{p'+1}_{U_p}`, and the
affineness of that self-product is [Stacks, Tag 08GB] part (4), which asks the *base* to be
separated.  The base is `U_p`, not `X`; `X` itself is only quasi-separated, and that is exactly
the gap between Tag 072B and Tag 072C.

**The form of the bounds.**  Both fibre-degree bounds are taken in the degree form of
[Stacks, Tag 03JL], `AlgebraicGeometry.Space.BoundsFibreDegrees`, which is what the source's
proof uses: what it needs is the emptiness of `W_m` above the bound, and that follows from the
degree bound and not from a bound on the cardinality of the topological fibres — over
`X = Spec k` with `U = Spec k'` for a separable quadratic extension the map `|U| → |X|` is a
bijection while `W_1` is nonempty.  The passage is
`AlgebraicGeometry.Space.SpacesEtale.isEmpty_points_diagonalComplement_of_boundsFibreDegrees`.

**Separatedness of the charts is not a hypothesis.**  The source does not assume `f : U ⟶ X` or
`V_p ⟶ U_p` separated, and neither does anything below: an étale morphism from an affine scheme
to an algebraic space is separated, by [Stacks, Tag 03FZ].  The choices (4)–(5) are therefore
stated for an arbitrary object representing `W_{p+1}` and an arbitrary proof that `f` is
separated, both of which are artifacts of the way `U_p` is presented here rather than data of the
source.

## References

* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 072A](https://stacks.math.columbia.edu/tag/072A)
* [Stacks Project, Tag 072B](https://stacks.math.columbia.edu/tag/072B)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 08GB](https://stacks.math.columbia.edu/tag/08GB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

namespace SpacesEtale

/-- **[Stacks, Tag 072B] with the source's explicit bound.**  Let `Y` be a separated algebraic
space over `S` carrying a surjective étale morphism `g : V ⟶ Y` from an affine scheme whose fibre
degrees are bounded by `d`.  Then the cohomology of `Y` with quasi-coherent coefficients vanishes
in every degree `n ≥ d`.

Separatedness of `Y` makes every quotient `V_{p} = W_{p+1}/S_{p+1}` affine, so the column `p` of
the `E₁`-page of [Stacks, Tag 0728] vanishes in *every* positive degree; the convergence step
`AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_zExt_column_bounds` with all the column
bounds equal to one then gives the vanishing above `max_{p < d} (1 + p) = d`. -/
theorem isZero_sheafH_of_boundsFibreDegrees (hSerre : AffineSerreVanishing B S hS)
    (Y : AlgebraicSpaces B S hS) (hYsep : IsAbsolutelySeparated B S hS hZ Y.obj)
    (V : BigFppfOver B S hS) (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : yoneda.obj V ⟶ Y.obj) (hg : IsEtale B S hS g) (hgsurj : IsSurjective B S hS g)
    (d : ℕ) (hgbd : BoundsFibreDegrees B S hS V g (d : ℤ))
    (F : Sheaf (topology B S hS Y) AddCommGrpCat.{u + 1})
    (hF : IsQuasicoherentAbelian B S hS Y F) (n : ℕ) (hn : d ≤ n) :
    IsZero (AddCommGrpCat.of (Sheaf.H F n)) := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
  have hgsep : IsSeparated B S hS g :=
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS Y.obj Y.2 V inferInstance g hg
  refine isZero_sheafH_of_zExt_column_bounds B S hS Y V g hg hgsurj hgsep d
    (isEmpty_points_diagonalComplement_of_boundsFibreDegrees B S hS Y V g hg hgsep d hgbd)
    (fun _ => 1) F ?_ n (fun p hp => by omega)
  intro p q hpd hq
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
  exact isZero_zExt_koszulComplex_X_of_isAffineSpace_quotient B S hS Y
    (chartObj B S hS Y V g hg) hgsep hSerre p
    (isAffineSpace_diagonalComplementQuotient B S hS hZ Y (chartObj B S hS Y V g hg) p hgsep
      (isAffineSpace_yoneda B S hS V hVaff) hYsep) F hF q (by omega)

/-- `AlgebraicGeometry.Space.SpacesEtale.isZero_sheafH_of_boundsFibreDegrees` read at the `Ext`
universe of the character-twist comparison.  The two cohomology groups lie in `AddCommGrpCat` at
two different universes, so the comparison is
`Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv` rather than an isomorphism of the
category. -/
theorem subsingleton_sheafH_of_boundsFibreDegrees (hSerre : AffineSerreVanishing B S hS)
    (Y : AlgebraicSpaces B S hS) (hYsep : IsAbsolutelySeparated B S hS hZ Y.obj)
    (V : BigFppfOver B S hS) (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : yoneda.obj V ⟶ Y.obj) (hg : IsEtale B S hS g) (hgsurj : IsSurjective B S hS g)
    (d : ℕ) (hgbd : BoundsFibreDegrees B S hS V g (d : ℤ))
    (F : Sheaf (topology B S hS Y) AddCommGrpCat.{u + 1})
    (hF : IsQuasicoherentAbelian B S hS Y F) (n : ℕ) (hn : d ≤ n) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F n) :=
  subsingleton_of_addEquiv Stacks.Cohomology.SimplicialComponent.extChgUnivAddEquiv
    (AddCommGrpCat.subsingleton_of_isZero
      (isZero_sheafH_of_boundsFibreDegrees B S hS hZ hSerre Y hYsep V hVaff g hg hgsurj d hgbd
        F hF n hn))

/-- **The column `p` of the `E₁`-page of [Stacks, Tag 0728] vanishes above `d_p`.**  Let `U` be a
representable object of the spaces-étale site of `X` whose underlying algebraic space is
separated and whose structure morphism is separated, and let `g : V ⟶ U_p` be a surjective étale
morphism from an affine scheme onto the quotient `U_p = W_{p+1}/S_{p+1}` whose fibre degrees are
bounded by `d_p`.  Then the column `p` vanishes in every degree `q ≥ d_p`.

This is the source's application of [Stacks, Tag 072B] to `U_p`: the column is the cohomology of
`U_p` with coefficients twisted by the sign character, those coefficients are quasi-coherent by
[Stacks, Tag 072A], and `U_p` is separated. -/
theorem isZero_zExt_koszulComplex_X_of_chart_over_quotient (hSerre : AffineSerreVanishing B S hS)
    (X : AlgebraicSpaces B S hS) (U : SpacesEtale B S hS X)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (hUrep : (underlying B S hS X U).obj.IsRepresentable)
    (hUsep : IsAbsolutelySeparated B S hS hZ (underlying B S hS X U).obj)
    (p : ℕ) (V : BigFppfOver B S hS) (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (g : yoneda.obj V ⟶ (diagonalComplementQuotient B S hS X U (p + 1) hsep).obj)
    (hg : IsEtale B S hS g) (hgsurj : IsSurjective B S hS g)
    (dp : ℕ) (hgbd : BoundsFibreDegrees B S hS V g (dp : ℤ))
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1})
    (hF : IsQuasicoherentAbelian B S hS X F) (q : ℕ) (hq : dp ≤ q) :
    IsZero (AddCommGrpCat.of
      (Abelian.zExt ((koszulComplex B S hS X U).X p) F (q : ℤ))) :=
  isZero_zExt_koszulComplex_X_of_subsingleton_sheafH B S hS X U hsep p q F
    (subsingleton_sheafH_of_boundsFibreDegrees B S hS hZ hSerre
      (diagonalComplementQuotient B S hS X U (p + 1) hsep)
      (isAbsolutelySeparated_diagonalComplementQuotient B S hS hZ X U p hsep hUrep hUsep)
      V hVaff g hg hgsurj dp hgbd _
      (isQuasicoherentAbelian_diagonalComplementTwistedRestriction B S hS X U hsep p F hF) q hq)

end SpacesEtale

/-- **The vanishing of [Stacks, Tag 072C] from the choices (1)–(5).**  Let `S` be a scheme and
let `X` be a quasi-compact and quasi-separated
algebraic space over `S`.  Choose an affine scheme `U`, a surjective étale morphism `f : U ⟶ X`
and an integer `d` bounding the degrees of the fibres of `f`; for each `p` with `0 ≤ p ≤ d`
choose an affine scheme `V_p`, a surjective étale morphism `V_p ⟶ U_p` onto the quotient
`U_p = W_{p+1}/S_{p+1}` of [Stacks, Tag 0726], and an integer `d_p` bounding the degrees of its
fibres.  Then

`H^q(X, ℱ) = 0`

for every quasi-coherent `𝒪_X`-module `ℱ` and every `q` at least `max (d_p + p)`.

The bound is the source's, formed as the supremum of `d_p + p` over `0 ≤ p ≤ d`.  The vanishing is
read on the spaces-étale site of `X`, as the sheaf cohomology of the underlying abelian sheaf of
`ℱ`; the cohomological descent that identifies that with the derived functors of global sections
on modules is [Stacks, Tag 03FD].

The one input of the recursion that the recursion cannot supply is the positive-degree vanishing
on an *affine* algebraic space — the clause of [Stacks, Tag 03DW] in positive degrees,
`AlgebraicGeometry.Space.SpacesEtale.AffineSerreVanishing`.  It is supplied here by
`AlgebraicGeometry.Space.SpacesEtale.affineSerreVanishing_of_isZero_cechCohomology`, the
Čech-to-derived criterion of [Stacks, Tag 03F9] on the cofinal affine objects of the small étale
site, whose Čech hypothesis is
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_comparisonCoefficients_forall`. -/
@[stacks 072C "the conclusion: for X a quasi-compact and quasi-separated algebraic space over a \
scheme S, given the choices (1)-(5) -- an affine U with a surjective etale U -> X, an integer d \
bounding its fibre degrees, and for each p <= d an affine V_p with a surjective etale \
V_p -> U_p = W_{p+1}/S_{p+1} and an integer d_p bounding its fibre degrees -- the cohomology \
H^q(X, F) vanishes for every quasi-coherent module F and every q at least the source's \
max(d_p + p) over 0 <= p <= d. The cohomology is the sheaf cohomology of the underlying abelian \
sheaf of F on the spaces-etale site of X"]
theorem isZero_sheafH_of_data_072C
    (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.obj)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : yoneda.obj U ⟶ X.obj) (hf : IsEtale B S hS f) (hfsurj : IsSurjective B S hS f)
    (d : ℕ) (hd : BoundsFibreDegrees B S hS U f (d : ℤ)) (dp : ℕ → ℕ)
    (hdata : ∀ (hsep : IsSeparated B S hS f) (p : ℕ), p ≤ d →
      ∃ (V : BigFppfOver B S hS)
        (g : yoneda.obj V ⟶ (SpacesEtale.diagonalComplementQuotient B S hS X
          (SpacesEtale.chartObj B S hS X U f hf) (p + 1) hsep).obj),
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
          IsEtale B S hS g ∧ IsSurjective B S hS g ∧
          BoundsFibreDegrees B S hS V g (dp p : ℤ))
    (M : SheafOfModules.{u + 1} (SpacesEtale.spacesEtaleRing B S hS X))
    (hM : M.IsQuasicoherentOnSite)
    (n : ℕ) (hn : (Finset.range (d + 1)).sup (fun p => dp p + p) ≤ n) :
    IsZero (AddCommGrpCat.of (Sheaf.H
      ((SheafOfModules.toSheaf.{u + 1} (SpacesEtale.spacesEtaleRing B S hS X)).obj M) n)) := by
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hSerre : SpacesEtale.AffineSerreVanishing B S hS :=
    SpacesEtale.affineSerreVanishing_of_isZero_cechCohomology B S hS
      (SmallEtale.isZero_cechCohomology_comparisonCoefficients_forall B S hS)
  have hsep : IsSeparated B S hS f :=
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS X.obj X.2 U inferInstance f hf
  have hUsep : IsAbsolutelySeparated B S hS hZ
      (SpacesEtale.underlying B S hS X (SpacesEtale.chartObj B S hS X U f hf)).obj :=
    isAbsolutelySeparated_of_isAffineSpace B S hS hZ
      (isAffineSpace_yoneda B S hS U hU)
  have hF : SpacesEtale.IsQuasicoherentAbelian B S hS X
      ((SheafOfModules.toSheaf.{u + 1} (SpacesEtale.spacesEtaleRing B S hS X)).obj M) :=
    ⟨M, hM, ⟨Iso.refl _⟩⟩
  refine SpacesEtale.isZero_sheafH_of_zExt_column_bounds B S hS X U f hf hfsurj hsep d
    (SpacesEtale.isEmpty_points_diagonalComplement_of_boundsFibreDegrees B S hS X U f hf hsep d hd)
    dp _ ?_ n fun p hpd => le_trans ?_ hn
  · intro p q hpd hq
    obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    obtain ⟨V, g, hVaff, hg, hgsurj, hgbd⟩ := hdata hsep p (by omega)
    exact SpacesEtale.isZero_zExt_koszulComplex_X_of_chart_over_quotient B S hS hZ hSerre X
      (SpacesEtale.chartObj B S hS X U f hf) hsep
      (Functor.IsRepresentable.mk' (Iso.refl (yoneda.obj U))) hUsep p V hVaff g hg hgsurj
      (dp p) hgbd _ hF q (by omega)
  · exact Finset.le_sup (f := fun p => dp p + p) (Finset.mem_range.2 (by omega))

/-- **[Stacks, Tag 072C], end to end.**  Let `S` be a scheme and let `X` be a quasi-compact and
quasi-separated algebraic space over `S`.  Then there is a single degree `N` beyond which the
cohomology of `X` with quasi-coherent coefficients vanishes:

`H^q(X, ℱ) = 0` for every quasi-coherent `𝒪_X`-module `ℱ` and every `q ≥ N`.

The base is an arbitrary scheme, as in the source.  This is the five choices of the tag,
`AlgebraicGeometry.Space.exists_affine_etale_surjective_cover_diagonalComplementQuotient`, fed
into the vanishing they give,
`AlgebraicGeometry.Space.isZero_sheafH_of_data_072C`, with `N` the source's `max (d_p + p)`
over `0 ≤ p ≤ d`; the two fibre bounds are produced as integers by
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers` and enlarged to natural numbers by
`AlgebraicGeometry.Space.BoundsFibreDegrees.mono`.  The uniformity in `ℱ` — one degree for all
quasi-coherent coefficients at once — is what the tag asserts and is what makes the Euler
characteristic of a coherent module a finite alternating sum. -/
@[stacks 072C "the tag end to end, over an arbitrary base scheme S: for X a quasi-compact and \
quasi-separated algebraic space over S there is a single degree N beyond which the sheaf \
cohomology on the spaces-etale site of X of the underlying abelian sheaf of every \
quasi-coherent module vanishes. N is constructed in the proof as the source's max(d_p + p) for \
the choices (1)-(5) made there; the statement quantifies N existentially, and the \
identification of N with that maximum is stated at \
AlgebraicGeometry.Space.isZero_sheafH_of_data_072C"]
theorem exists_forall_isZero_sheafH_of_isQuasiCompactSpace_072C
    (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.obj)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.obj) :
    ∃ N : ℕ, ∀ (M : SheafOfModules.{u + 1} (SpacesEtale.spacesEtaleRing B S hS X)),
      M.IsQuasicoherentOnSite → ∀ n : ℕ, N ≤ n →
        IsZero (AddCommGrpCat.of (Sheaf.H
          ((SheafOfModules.toSheaf.{u + 1} (SpacesEtale.spacesEtaleRing B S hS X)).obj M) n)) := by
  classical
  obtain ⟨U, f, hf, hsep, hU, hsurj, hbd, hall⟩ :=
    exists_affine_etale_surjective_cover_diagonalComplementQuotient B S hS hZ X.obj X.2 hqc hqs
  obtain ⟨dz, hdz⟩ := hbd
  choose V g hVaff hgsurj hget hgbd using hall
  choose dpz hdpz using hgbd
  refine ⟨(Finset.range (dz.toNat + 1)).sup fun p => (dpz p).toNat + p,
    fun M hM n hn => ?_⟩
  refine isZero_sheafH_of_data_072C B S hS hZ X hqc hqs U hU f hf
    (isSurjective_of_presheafSurjective B S hS f hsurj) dz.toNat
    (BoundsFibreDegrees.mono hdz (Int.self_le_toNat dz)) (fun p => (dpz p).toNat) ?_ M hM n hn
  intro hsep' p _
  exact ⟨V p, g p, hVaff p, hget p,
    isSurjective_of_presheafSurjective B S hS (g p) (hgsurj p),
    BoundsFibreDegrees.mono (hdpz p) (Int.self_le_toNat (dpz p))⟩

end AlgebraicGeometry.Space

end
