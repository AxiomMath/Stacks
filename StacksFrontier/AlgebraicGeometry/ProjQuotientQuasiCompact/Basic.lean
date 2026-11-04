module

public import StacksFrontier.AlgebraicGeometry.ProjQuotientFiniteCover.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A closed subscheme of a quasi-compact `Proj` is the `Proj` of a quotient

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a graded ring generated in degree one over `𝒮 0`, with `Proj 𝒮`
quasi-compact, and let `i : Z ⟶ Proj 𝒮` be a closed immersion. Then `Z` is isomorphic over
`Proj 𝒮` to `Proj (𝒮 / I(Z))`, for `I(Z)` the homogeneous ideal of equations of `Z` of
[Stacks, Tag 0BXK].

This is the absolute case of [Stacks, Tag 0801] over an affine base, and the hypothesis it is
proved under here is the source's own: Tag 0801 assumes that the structure morphism
`p : Proj_S(𝒜) ⟶ S` be quasi-compact, which over an affine base says exactly that `Proj 𝒮` is
a quasi-compact scheme. No Noetherian hypothesis is used.

## Main results

* `Stacks.ProjQuotientQuasiCompact.exists_finite_degreeOne_cover`: a quasi-compact `Proj 𝒮` over
  a graded ring generated in degree one admits a *finite* family of degree-one elements whose
  standard opens cover it.
* `Stacks.ProjQuotientQuasiCompact.saturationIdentification_of_compactSpace`: the identification
  `Z ≅ Proj (𝒮 / I(Z))` over `Proj 𝒮`, and
  `Stacks.ProjQuotientQuasiCompact.ker_eq_ker_ambientHom_of_compactSpace`, the equality of ideal
  sheaves behind it.
* `Stacks.ProjQuotientQuasiCompact.projQuotientIso`: the isomorphism itself, and
  `Stacks.ProjQuotientQuasiCompact.projQuotientIso_hom_comp_ambientHom`: that it is an
  isomorphism *over* `Proj 𝒮`, so an equality of closed subschemes rather than an abstract
  isomorphism.
* `Stacks.ProjQuotientQuasiCompact.projQuotientPresentation`: all five clauses of
  `Stacks.ClosedSubschemeProjQuotient.ProjQuotientPresentation` together.

## Implementation notes

Everything downstream of the finite cover is already proved without a Noetherian hypothesis, in
`Stacks.ProjQuotientFiniteCover`, which takes the finite degree-one family as a hypothesis. The
only work here is to produce that family from quasi-compactness instead of from finite
generation of the irrelevant ideal: the standard opens of *all* degree-one elements cover
`Proj 𝒮` when `𝒮` is generated in degree one
(`Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top`, which needs no
finiteness), and a compact space admits a finite subcover of any open cover.

That is a strictly weaker hypothesis than the Noetherian one it replaces, and a faithful one:
`Stacks.ClosedSubschemeProjQuotient.projQuotientIso` uses `[IsNoetherianRing S]` only through
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_mem_idealOfClosedSubscheme`, whose own
use of it is `Ideal.fg_of_isNoetherianRing` on the irrelevant ideal — finiteness and nothing
else. Quasi-compactness of `Proj 𝒮` does not follow from generation in degree one
(`𝒮 1` need not be a finite module), so it is a genuine hypothesis, and it is the one the source
carries.

The isomorphism is a `def`, so the finite cover it is built from has to be *chosen* rather than
merely to exist; `degreeOneCover` names that choice and `degreeOneCover_spec` its covering
property, so that the isomorphism and its compatibility with the two morphisms to `Proj 𝒮` are
built from the same cover and the second is literally about the first.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 03GL](https://stacks.math.columbia.edu/tag/03GL)

## No Stacks tag attribute is attached in this file

Stacks Tag 0801 is about the relative `Proj_S(𝒜)` of a quasi-coherent graded `𝒪_S`-algebra over
an arbitrary base scheme, under the single hypothesis that the structure morphism be
quasi-compact. What is proved here is its absolute case, over an affine base, and with one
further hypothesis on the graded ring — that it be generated in degree one. That is a special
case of the tag, so no `@[stacks 0801]` attribute is attached to anything here: the tag's
existing attachments stay where they are, on
`Stacks.ClosedSubschemeProjQuotient.projQuotientIso` and
`Stacks.ClosedSubschemeProjQuotient.projQuotientIso_hom_comp_ambientHom`.

What this file does remove is the Noetherian hypothesis, which the source does not have. The
hypothesis that remains beyond the source's own, generation in degree one, is what the chart
machinery is stated for: a standard open `D₊(f)` of a degree-one `f` serves as a trivialising
chart of the twisting sheaves, which needs the twists invertible. Over an arbitrary graded ring
the twists `𝒪(n)` are invertible only after passing to multiples of a common degree of a
covering family. That machinery is available and unconditional —
`AlgebraicGeometry.Proj.exists_common_degree_finite_basicOpen_cover` produces such a covering
family from quasi-compactness alone,
`Stacks.AlgebraicGeometry.CommonDegreeTwist.isInvertible_restrict_twistingSheaf_mul_degree`
inverts the divisible twists on it, and
`Stacks.AlgebraicGeometry.CommonDegreeTwist.isIso_restrict_twistMultiplication_mul_degree`
is Tag 01MW (3), the multiplication isomorphism the source's proof cites — so removing this last
hypothesis is a matter of restating the chart comparison with the numerator in a degree
divisible by that common degree, exactly as the source's proof does. It is not done here.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ClosedSubschemeProjQuotient

universe u

namespace Stacks.ProjQuotientQuasiCompact

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (𝒮 : ℕ → Submodule R S)
  [GradedAlgebra 𝒮]

/-- **A quasi-compact `Proj` of a graded ring generated in degree one has a finite degree-one
chart cover.** The standard opens of all degree-one elements cover `Proj 𝒮`, and compactness
extracts a finite subfamily.

This is the hypothesis that
`Stacks.ProjQuotientFiniteCover.exists_pow_mul_mem_idealOfClosedSubscheme_of_cover` asks for, and
the only thing `[IsNoetherianRing S]` is used to produce in
`AlgebraicGeometry.ProjectiveSpectrum.Proj.exists_pow_mul_mem_idealOfClosedSubscheme`. -/
theorem exists_finite_degreeOne_cover [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) :
    ∃ t : Finset (𝒮 1),
      ⨆ j : {x : 𝒮 1 // x ∈ t}, Proj.basicOpen 𝒮 ((j : 𝒮 1) : S) = ⊤ := by
  obtain ⟨t, ht⟩ := CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _
    ((TopologicalSpace.Opens.isCompactElement_iff (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)).2
      isCompact_univ) _
    (Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top 𝒮 hgen).ge
  exact ⟨t, top_le_iff.mp (ht.trans_eq iSup_subtype')⟩

/-- The chosen finite family of degree-one elements whose standard opens cover a quasi-compact
`Proj 𝒮`. -/
def degreeOneCover [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) : Finset (𝒮 1) :=
  (exists_finite_degreeOne_cover 𝒮 hgen).choose

/-- The chosen finite family does cover `Proj 𝒮`. -/
theorem degreeOneCover_spec [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤) :
    ⨆ j : {x : 𝒮 1 // x ∈ degreeOneCover 𝒮 hgen},
      Proj.basicOpen 𝒮 ((j : 𝒮 1) : S) = ⊤ :=
  (exists_finite_degreeOne_cover 𝒮 hgen).choose_spec

/-- **A closed subscheme of a quasi-compact `Proj 𝒮` is the `Proj` of the quotient by its ideal
of equations**, for a graded ring generated in degree one. No Noetherian hypothesis is used.

This is `Stacks.ClosedSubschemeProjQuotient.saturationIdentification` with `[IsNoetherianRing S]`
traded for quasi-compactness of `Proj 𝒮`, which is Tag 0801's own hypothesis read over an affine
base. -/
theorem saturationIdentification_of_compactSpace [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    SaturationIdentification 𝒮 i :=
  Stacks.ProjQuotientFiniteCover.saturationIdentification_of_cover 𝒮 hgen
    (fun j : {x : 𝒮 1 // x ∈ degreeOneCover 𝒮 hgen} => ((j : 𝒮 1) : S))
    (fun j => (j : 𝒮 1).2) (degreeOneCover_spec 𝒮 hgen) i

/-- `Z` and `Proj (𝒮 / I(Z))` cut out the same ideal sheaf of `Proj 𝒮`. -/
theorem ker_eq_ker_ambientHom_of_compactSpace [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    i.ker = (ambientHom 𝒮 i).ker :=
  Stacks.ProjQuotientFiniteCover.ker_eq_ker_ambientHom_of_cover 𝒮 hgen
    (fun j : {x : 𝒮 1 // x ∈ degreeOneCover 𝒮 hgen} => ((j : 𝒮 1) : S))
    (fun j => (j : 𝒮 1).2) (degreeOneCover_spec 𝒮 hgen) i

/-- **The isomorphism `Z ≅ Proj (𝒮 / I(Z))`** for a quasi-compact `Proj 𝒮` over a graded ring
generated in degree one. It is the lift of `i` through the closed immersion
`Stacks.ClosedSubschemeProjQuotient.ambientHom`, which is invertible because the two closed
subschemes have the same ideal sheaf. -/
@[ega "II 2.9.2" "more general"]
def projQuotientIso [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    Z ≅ projQuotient 𝒮 i :=
  Stacks.ProjQuotientFiniteCover.projQuotientIso_of_cover 𝒮 hgen
    (fun j : {x : 𝒮 1 // x ∈ degreeOneCover 𝒮 hgen} => ((j : 𝒮 1) : S))
    (fun j => (j : 𝒮 1).2) (degreeOneCover_spec 𝒮 hgen) i

/-- **The isomorphism is canonical**: it is compatible with the two morphisms to `Proj 𝒮`, so it
is an equality of closed subschemes of `Proj 𝒮` and not merely an abstract isomorphism. -/
@[simp]
theorem projQuotientIso_hom_comp_ambientHom [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    (projQuotientIso 𝒮 hgen i).hom ≫ ambientHom 𝒮 i = i :=
  Stacks.ProjQuotientFiniteCover.projQuotientIso_of_cover_hom_comp_ambientHom 𝒮 hgen
    (fun j : {x : 𝒮 1 // x ∈ degreeOneCover 𝒮 hgen} => ((j : 𝒮 1) : S))
    (fun j => (j : 𝒮 1).2) (degreeOneCover_spec 𝒮 hgen) i

/-- **Every clause of the presentation of a closed subscheme of `Proj 𝒮` as a `Proj`**, for a
quasi-compact `Proj 𝒮` over a graded ring generated in degree one. -/
def projQuotientPresentation [CompactSpace (AlgebraicGeometry.Proj 𝒮)]
    (hgen : Algebra.adjoin (𝒮 0) ((𝒮 1 : Set S)) = ⊤)
    {Z : Scheme.{u}} (i : Z ⟶ Proj 𝒮) [IsClosedImmersion i] :
    ProjQuotientPresentation 𝒮 i where
  quotient_epi := surjective_quotientMk 𝒮 i
  quotient_kernel := quotientMk_coe_eq_zero_iff 𝒮 i
  isClosedImmersion_ambient := isClosedImmersion_ambientHom 𝒮 i
  iso := projQuotientIso 𝒮 hgen i
  iso_over_ambient := projQuotientIso_hom_comp_ambientHom 𝒮 hgen i

end Stacks.ProjQuotientQuasiCompact

end
