module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.MorphismToProjAwayLift
public import StacksFrontier.AlgebraicGeometry.MorphismsIntoProj

/-!
# The chart morphism into a standard open of `Proj`

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, let `f ∈ 𝒜 d` with `d > 0`, and let `X` be a scheme
with an open `U`. The projective standard open `D₊(f) ⊆ Proj 𝒜` is affine, with ring of sections
the degree-zero localization `A_{(f)}`
(`AlgebraicGeometry.Proj.basicOpenIsoSpec`), so a morphism `U ⟶ D₊(f)` is the same thing as a
ring map `A_{(f)} →+* Γ(X, U)`. This file turns such a ring map — presented as the degreewise
family `Stacks.MorphismToProj.HomogeneousRatios` of the sibling file — into the morphism, and
records its effect on sections.

This is step 1 of the proof of [Stacks, Tag 01N8] with its module-theoretic input abstracted
away. There `U` is the nonvanishing locus `Y_{ψ(f)}` of the section `ψ(f)` of the invertible
sheaf `L`, and the family of ratios is `a ↦ ψ(a) / ψ(f) ^ n`, well defined because a nonvanishing
section trivializes an invertible sheaf ([Stacks, Tag 01CY]). Nothing about `L` is needed to build
the morphism once that family is in hand, which is why the two halves are separated.

## Main definitions

* `Stacks.MorphismToProj.HomogeneousRatios.toSpecAway`: the morphism `U ⟶ Spec A_{(f)}`, namely
  `U ⟶ Spec Γ(X, U)` followed by `Spec` of the ring map.
* `Stacks.MorphismToProj.HomogeneousRatios.chart`: **the chart morphism `U ⟶ D₊(f)`.**
* `Stacks.MorphismToProj.HomogeneousRatios.chartToProj`: the same morphism read into `Proj 𝒜`,
  through the open immersion `AlgebraicGeometry.Proj.awayι`.

## Main results

* `Stacks.MorphismToProj.HomogeneousRatios.chart_ι`: the chart morphism followed by the inclusion
  of `D₊(f)` is `chartToProj`, so it does factor through the standard open. This is the clause
  of [Stacks, Tag 01N8] that pins down *which* morphism has been built.
* `Stacks.MorphismToProj.HomogeneousRatios.toDegreeOpen`: the chart morphism read into the
  degree `d` open `U_d`, which is the target the pair of [Stacks, Tag 01N8] is indexed by, with
  `Stacks.MorphismToProj.HomogeneousRatios.toProj_toDegreeOpen` identifying the two readings.
* `Stacks.MorphismToProj.HomogeneousRatios.preimage_basicOpen_toDegreeOpen`: **clause (a) of
  [Stacks, Tag 01N8] on a single chart**, in the spelling the uniqueness half consumes.
* `Stacks.MorphismToProj.HomogeneousRatios.toSpecAway_appTop`: the effect of `toSpecAway` on
  global sections is the ring map, up to the canonical isomorphisms. With
  `Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext` this is what identifies a competing morphism
  with this one.
* `Stacks.MorphismToProj.HomogeneousRatios.chartToProj_base_mem`: every point of the image of
  `chartToProj` lies in `D₊(f)`.
* `Stacks.MorphismToProj.HomogeneousRatios.homOfLE_toSpecAway`: **two charts whose ring maps are
  compatible with restriction agree on the smaller open.** This is the input the gluing step of
  [Stacks, Tag 01N8] consumes.

## Implementation notes

**Why the target is `Spec A_{(f)}` and not `D₊(f)` from the start.** The identification of `D₊(f)`
with `Spec A_{(f)}` needs `f` homogeneous of positive degree, and it is Mathlib's
`AlgebraicGeometry.Proj.basicOpenIsoSpec`; its inverse composed with the inclusion of the standard
open is exactly `AlgebraicGeometry.Proj.awayι`. Factoring the construction through
`Spec A_{(f)}` therefore lets `chart_ι` be a definitional unfolding rather than a computation, and
it is the shape in which Mathlib's own `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` is
built.

**No hypothesis relating `U` to `f` is needed here.** In the source, `U` is the nonvanishing locus
of `ψ(f)` and the equality `φ ⁻¹ᵁ D₊(f) = Y_{ψ(f)}` is part of the conclusion. That equality is a
statement about the *glued* morphism on all of `Y`, not about one chart; on a single chart there is
nothing to say, because the chart morphism lands in `D₊(f)` by construction
(`chartToProj_base_mem`). Accordingly this file assumes nothing about `U`, and the sheaf-theoretic
hypotheses enter only when the family of ratios is produced.

**The degreewise form of the compatibility square.** Where this file is consumed, the square of
[Stacks, Tag 01N8] is to be stated degreewise — one equation for each `n` and each homogeneous
`x` of Veronese degree `n` — rather than as a single equality of graded ring maps. The two are the
same statement: a graded ring map is its family of components, so equality of two such maps
unfolds definitionally to equality in every degree, and the source itself writes the square
degreewise in its uniqueness argument. No reformulation is being asserted.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Stacks.MorphismToProj.HomogeneousRatios

universe u w

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {d : ℕ} {f : A} {hf : f ∈ 𝒜 d}
  {X : Scheme.{u}} {U : X.Opens} (R : HomogeneousRatios 𝒜 hf ↥Γ(X, U)) (hd : 0 < d)

/-- The morphism `U ⟶ Spec A_{(f)}` attached to a family of homogeneous ratios: the canonical
morphism `U ⟶ Spec Γ(X, U)` followed by `Spec` of the induced ring map. -/
def toSpecAway : U.toScheme ⟶ Spec (CommRingCat.of (Away 𝒜 f)) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (R.lift hd))

/-- **The chart morphism `U ⟶ D₊(f)`** attached to a family of homogeneous ratios, through the
identification of the standard open `D₊(f)` with `Spec A_{(f)}`. -/
def chart : U.toScheme ⟶ (Proj.basicOpen 𝒜 f).toScheme :=
  R.toSpecAway hd ≫ (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv

/-- The chart morphism read as a morphism into `Proj 𝒜`. -/
def chartToProj : U.toScheme ⟶ Proj 𝒜 :=
  R.toSpecAway hd ≫ Proj.awayι 𝒜 f hf hd

/-- **The chart morphism factors the morphism into `Proj 𝒜` through `D₊(f)`.** -/
@[reassoc] theorem chart_ι : R.chart hd ≫ (Proj.basicOpen 𝒜 f).ι = R.chartToProj hd := by
  rw [chart, chartToProj, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]

/-- Every point of the image of the morphism into `Proj 𝒜` lies in the standard open `D₊(f)`. -/
theorem chartToProj_base_mem (x : U.toScheme) :
    (R.chartToProj hd).base x ∈ Proj.basicOpen 𝒜 f := by
  rw [← R.chart_ι hd]
  exact ((R.chart hd).base x).2

/-- **The effect of the chart morphism on global sections is the given ring map.** Composed with
the canonical isomorphism `Γ(Spec A_{(f)}, ⊤) ≅ A_{(f)}` and with the identification of
`Γ(U.toScheme, ⊤)` with `Γ(X, U)`, the map `Scheme.Hom.appTop` of `toSpecAway` is `lift`. -/
theorem toSpecAway_appTop :
    (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜 f))).inv ≫ (R.toSpecAway hd).appTop
      = CommRingCat.ofHom (R.lift hd) ≫ U.topIso.inv := by
  rw [toSpecAway, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop,
    Scheme.ΓSpecIso_naturality_assoc, Iso.inv_hom_id_assoc]

/-! ### Alignment with the uniqueness half -/

/-- **The chart morphism read as a morphism into `U_d`.** The standard open `D₊(f)` of a
homogeneous `f` of degree `d` lies in the degree `d` open `U_d`, so the chart morphism factors
through `U_d`. This is the target the pair of Stacks Tag 01N8 is indexed by. -/
def toDegreeOpen :
    U.toScheme ⟶ (AlgebraicGeometry.Proj.degreeOpen 𝒜 d).toScheme :=
  R.chart hd ≫ (AlgebraicGeometry.Proj 𝒜).homOfLE
    (Stacks.AlgebraicGeometry.MorphismsIntoProj.basicOpen_le_degreeOpen 𝒜 ⟨f, hf⟩)

/-- Reading the chart morphism into `U_d` and then into `Proj 𝒜` gives back the morphism into
`Proj 𝒜`. -/
theorem toProj_toDegreeOpen :
    Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜 (R.toDegreeOpen hd)
      = R.chartToProj hd := by
  rw [Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj, toDegreeOpen, Category.assoc,
    Scheme.homOfLE_ι, R.chart_ι hd]

/-- **Clause (a) of Stacks Tag 01N8 on a single chart.** The preimage of `D₊(f)` under the chart
morphism is all of `U`, in the exact spelling
`Stacks.AlgebraicGeometry.ProjSectionsUnique.eq_of_appLE_eq_on_away` consumes. For the glued
morphism this preimage is the nonvanishing open `Y_{ψ(f)}`, which on the chart — where `U` *is*
that nonvanishing open — is this statement. -/
theorem preimage_basicOpen_toDegreeOpen :
    Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜 (R.toDegreeOpen hd)
        ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f = ⊤ := by
  rw [R.toProj_toDegreeOpen hd, eq_top_iff]
  exact fun x _ => R.chartToProj_base_mem hd x

/-! ### Compatibility with restriction -/

/-- **Charts built from ring maps compatible with restriction agree on the smaller open.** If `U'`
is an open inside `U` and the ring map of `R'` is the ring map of `R` followed by restriction of
sections, then the morphism of `R'` is the morphism of `R` restricted along the inclusion.

This is the compatibility that lets the charts of [Stacks, Tag 01N8] be glued: for two elements
`f, f'` of `S_d` the two charts, restricted to the overlap `Y_{ψ(f)} ⊓ Y_{ψ(f')}`, are built from
restrictions of the ratio families, so this reduces their agreement there to an identity of ring
maps out of `A_{(f)}` — which `Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext` checks on the
fractions `a / f ^ n` alone. The whole proof is
`AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map`, the naturality of `U ⟶ Spec Γ(X, U)`
in `U`. -/
theorem homOfLE_toSpecAway {U' : X.Opens} (h : U' ≤ U)
    (R' : HomogeneousRatios 𝒜 hf ↥Γ(X, U'))
    (hlift : R'.lift hd
      = (CommRingCat.Hom.hom (X.presheaf.map (homOfLE h).op)).comp (R.lift hd)) :
    X.homOfLE h ≫ R.toSpecAway hd = R'.toSpecAway hd := by
  rw [toSpecAway, toSpecAway, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map U' U h, Category.assoc, ← Spec.map_comp,
    hlift, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom]

end Stacks.MorphismToProj.HomogeneousRatios

end
