module

public import StacksFrontier.AlgebraicGeometry.MorphismsIntoProj
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.RelativeDegreeOne
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenCover
public import StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison

/-!
# Lemma 01O1 over the degree-`d` locus, with no generation hypothesis

[Stacks, Tag 01O1] attaches to a quadruple `(f : T → S, d, ℒ, ψ)` the `S`-morphism
`r = r_{d, ℒ, ψ} : T ⟶ Proj_S(𝒜)` and an isomorphism of `ℤ`-graded `𝒪_T`-algebras
`θ : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) → ⨁_{n ∈ ℤ} ℒ^{⊗ n}` characterised by a commuting triangle.
`StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison` constructs the comparison
of sources that the `θ`-assertion needs out of the recognition theorem, but only for a graded
algebra **generated in degree one over every affine open of the base** — because that is the
hypothesis under which the recognition theorem's two inputs, invertibility of the multiplications
`𝒪(nd) ⊗ 𝒪(md) ⟶ 𝒪((n+m)d)` and invertibility of the degree-zero piece, were available.

That hypothesis is not where the lemma lives. The source's own statement is about the morphism
`r_{d, ℒ, ψ}`, which lands in the degree-`d` locus `U_d` of Equation 27.12.0.1, and *there* both
inputs hold for an arbitrary quasi-coherent graded algebra. **This file replaces the generation
hypothesis by the honest one: that `r` lands in the relative `U_d`.**

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.laurentComparisonOfDegreeOpen`: **the
  comparison `c : r^*(⨁_n 𝒪(nd)) ≅ ⨁_n ℒ^{⊗ n}`, for a morphism `r` landing in the relative
  `U_d` and with no hypothesis on `𝒜` beyond Situation 01NN.**

## Main results

* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.existsUnique_theta_of_degreeOpen`:
  **Lemma 01O1's `θ`-assertion — existence, the commuting triangle and uniqueness — at the tag's
  own source, over the degree-`d` locus.** No generation hypothesis.
* `...RelativeVeroneseTwists.isIso_mulSheaf_pullbackTwistVeronese_of_mem_degreeOpen`: **the
  multiplications of `r^*(⨁_n 𝒪(nd))` are isomorphisms** whenever `r` lands in the relative `U_d`.
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.isInvertible_twistVeronese_piece_zero` and
  `isInvertible_pullbackTwistVeronese_piece_zero`: **`𝒪(0)` and its pullback are invertible**, with
  no hypothesis at all.
* `Stacks.AlgebraicGeometry.RelativeVeroneseTwists.mem_degreeOpen_of_isGeneratedInDegreeOne`:
  **the new hypothesis follows from the old one**, so the statements here subsume those of
  `...RelativeLaurentComparison` for every positive `d`.
* `Stacks.AlgebraicGeometry.TwistMapsInvertible.isIso_pullback_mulSheaf_of_mem_degreeOpen`: the
  relative statement the whole file turns on — **for a morphism `g` into a relative homogeneous
  spectrum whose image lies in the relative `U_d`, the pullback along `g` of a `d`-divisible
  multiplication of a graded algebra carrying Tag 01NR's chart identifications is an
  isomorphism.**

## The route

Everything rests on two *unconditional* absolute facts about `U_d ⊆ Proj 𝒮` of a graded ring,
both already in the repository and both consequences of
`Stacks.AlgebraicGeometry.ProjDegreeOpenSections.degreeOpen_le_ratioLocus` — which needs only
divisibility, never generation:

* `Stacks.AlgebraicGeometry.MorphismsIntoProj.isIso_restrict_twistMultiplicationMap_degreeOpen`:
  the multiplication `𝒪(dn) ⊗ 𝒪(dm) ⟶ 𝒪(d(n+m))` restricts to an isomorphism on `U_d`, in
  every integer bidegree;
* `Stacks.AlgebraicGeometry.ProjDegreeOpenSections.isGoodOpen_degreeOpen`, of which the above is
  the multiplication half.

The relative statement is these, chart by chart. `restrict_chart_mulSheaf_eq` of
`StacksFrontier.AlgebraicGeometry.TwistMapsInvertible.Multiplication` identifies the restriction of
the glued multiplication to a chart with the absolute multiplication map conjugated by the chart
identifications, so restricting one step further — to the absolute `U_d` inside the chart — lands
exactly on the absolute fact. The charts of the base cover, so the inverse images
`g^{-1}(π^{-1}(U))` cover `T`; over each of them `g` factors through
`U_d(Γ(U, 𝒜)) ⟶ Proj Γ(U, 𝒜) ⟶ Proj_S(𝒜)` because its image lies in
`π^{-1}(U) ⊓ U_d`, which is the range of that composite
(`...RelativeProj.RelativeProjData.opensRange_ι_comp_chart`); and `IsIso` of a morphism of
`𝒪_T`-modules is local on `T` (`...AffineBaseChange.isIso_of_isIso_restrict`).

Degree zero is separate and needs no locus at all: `𝒪(0)` is the structure sheaf on every chart,
which is `exists_mem_restrict_isoUnit_twistingSheaf` at `d = 0`, where the ratio locus is
everything (`...ProjShared.ratioLocus_zero`). That is why the degree-zero invertibility below
carries no hypothesis whatever.

## What is still carried

The degree-one datum `α : r^*𝒪(d) ≅ ℒ` and the commutativity of the triangle for the given
degreewise family `v`. These are one package, not two: `α` is `θ`'s own degree-one component, and
the triangle in degree one *is* the statement that `α` is the one the quadruple determines.
Discharging them *at the tag's own source* needs the identification of the universal quadruple of
a representation of the functor `F_d` of Section 01NS with the glued twists — `ℒ_univ` with
`𝒪(d)|_{U_d}` and `ψ_univ` with `...RelativeProjTwists.TwistData.ψ` — which this repository does
not have: over a general base the representation
`...RelativeProjQcohSheaf.Fd.degreeOpenEquiv` is `Equiv.ofBijective` of `Fd.homDegreeOpen`, so
its inverse is `Function.surjInv` of a surjectivity proof that amalgamates chart-wise data
through the bare existential `Fd.exists_amalgamation_opens`, and no declaration names the
resulting `ℒ` or `ψ`.

**The triangle is not carried everywhere, though.** Over an *affine* base the representation of
`F_d` is honest computable data —
`...RelativeProjQcohSheaf.Fd.representableByDegreeOpen`, whose bijections
`...RelativeProjQcohSheaf.Quadruple.fdEquiv` have `...AffineTripleSections.fdOfHom` for their
inverse — and there the whole `θ`-assertion is proved with nothing carried, as
`...RelativeProjQcohSheaf.Quadruple.existsUnique_theta_of_isAffine` of
`StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaAffineRepresentable`: existence, the
commutativity of the triangle in every integer degree against the pullback of the universal
quadruple's own `ψ`, uniqueness, and the over-`S` identity for the associated morphism. What that
statement does *not* do is present `θ` on the tag's own source `r^*(⨁_n 𝒪(nd))`: its source is
the Laurent algebra of the pullback of the universal invertible module, which is where the
identification above would be needed.

## References

* [Stacks Project, Tag 01O1](https://stacks.math.columbia.edu/tag/01O1)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

open AlgebraicGeometry Stacks.RingedSpace
open Stacks.AlgebraicGeometry.ProjDegreeOpenSections
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists

universe u

namespace Stacks.AlgebraicGeometry.TwistMapsInvertible

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S}
  {algebra : RelativeProjTwists.SchemeGradedAlgebra (relativeProj A).scheme}

/-- Every point of the relative homogeneous spectrum lies over some affine open of the base. -/
private theorem exists_mem_toBase_preimage_affineOpens (x : (relativeProj A).scheme) :
    ∃ U : S.affineOpens, x ∈ (relativeProj A).toBase ⁻¹ᵁ (U.1 : S.Opens) :=
  TopologicalSpace.Opens.mem_iSup.mp
    ((RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)).ge
      (TopologicalSpace.Opens.mem_top x))

/-- **The degree-zero piece of a graded algebra carrying Tag 01NR's chart identifications is an
invertible module**, with no hypothesis on the algebra.

This is `...TwistMapsInvertible.isInvertibleModule_piece` with the trivialization of the twists
on a chart taken at `d = 0` rather than at degree-one generation: on the chart the degree-zero
piece is the absolute `𝒪(0)`, and `exists_mem_restrict_isoUnit_twistingSheaf` trivializes it near
every point once the point lies in `ProjShared.ratioLocus _ 0`, which is everything. The index is
taken as an arbitrary integer with a proof that it vanishes, so that the statement applies to
`0 * d` without a rewrite under a dependent motive. -/
theorem isInvertibleModule_piece_eq_zero (D : RelativeProjTwists.ChartData A algebra) {k : ℤ}
    (hk : k = 0) :
    Stacks.Ample.IsInvertibleModule (relativeProj A).scheme (algebra.piece k) := by
  subst hk
  refine isInvertibleModule_of_forall_exists_isoUnit_openImmersion (algebra.piece 0) fun x => ?_
  obtain ⟨U, hxU⟩ := exists_mem_toBase_preimage_affineOpens (A := A) x
  have := D.chart_isOpenImmersion U.1 U.2
  have hrange : x ∈ ((relativeProj A).chart U.1 U.2).opensRange := by
    rw [← Scheme.Hom.image_top_eq_opensRange, D.chart_range U.1 U.2]
    exact hxU
  obtain ⟨y, hy⟩ := hrange
  obtain ⟨V, hyV, ⟨eV⟩⟩ := exists_mem_restrict_isoUnit_twistingSheaf (A.grading U.1)
    (d := 0) (n := 0) (c := 0) (by simp) (x := y)
    (by rw [Stacks.AlgebraicGeometry.ProjShared.ratioLocus_zero]; trivial)
  refine ⟨V.toScheme, V.ι ≫ (relativeProj A).chart U.1 U.2, inferInstance,
    ⟨⟨y, hyV⟩, hy⟩, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorComp V.ι ((relativeProj A).chart U.1 U.2)).app
      (algebra.piece 0) ≪≫
    (Scheme.Modules.restrictFunctor V.ι).mapIso (D.chartIso U.1 U.2 0) ≪≫ eV

/-- Transport `IsIso` of a functor image along an equality of morphisms. -/
private theorem isIso_map_of_eq {C₁ C₂ : Type*} [Category C₁] [Category C₂] (F : C₁ ⥤ C₂)
    {X Y : C₁} {f g : X ⟶ Y} (h : f = g) (hg : IsIso (F.map g)) : IsIso (F.map f) := h ▸ hg

/-- A functor image of `e.hom ≫ b` is an isomorphism as soon as the image of `b` is. -/
private theorem isIso_map_iso_hom_comp {C₁ C₂ : Type*} [Category C₁] [Category C₂] (F : C₁ ⥤ C₂)
    {X Y Z : C₁} (e : X ≅ Y) (b : Y ⟶ Z) (hb : IsIso (F.map b)) : IsIso (F.map (e.hom ≫ b)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' (Iso.isIso_hom (F.mapIso e)) hb

/-- A functor image of `b ≫ e.hom` is an isomorphism as soon as the image of `b` is. -/
private theorem isIso_map_comp_iso_hom {C₁ C₂ : Type*} [Category C₁] [Category C₂] (F : C₁ ⥤ C₂)
    {X Y Z : C₁} (b : X ⟶ Y) (e : Y ≅ Z) (hb : IsIso (F.map b)) : IsIso (F.map (b ≫ e.hom)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' hb (Iso.isIso_hom (F.mapIso e))

/-- A functor image of `b ≫ e.inv` is an isomorphism as soon as the image of `b` is. -/
private theorem isIso_map_comp_iso_inv {C₁ C₂ : Type*} [Category C₁] [Category C₂] (F : C₁ ⥤ C₂)
    {X Y Z : C₁} (b : X ⟶ Y) (e : Z ≅ Y) (hb : IsIso (F.map b)) : IsIso (F.map (b ≫ e.inv)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' hb (Iso.isIso_inv (F.mapIso e))

/-- **One chart of the degree-`d` locus.** Restricting the `d`-divisible multiplication of a
graded algebra on a relative homogeneous spectrum first to the chart of an affine open `U` of the
base and then to the absolute degree-`d` open of `Proj Γ(U, 𝒜)` gives an isomorphism, with no
hypothesis on the algebra.

`restrict_chart_mulSheaf_eq` presents the restriction to the chart as the absolute multiplication
map conjugated by the chart identifications; restricting further to the absolute `U_d` leaves the
two conjugating isomorphisms isomorphisms and turns the middle factor into
`...MorphismsIntoProj.isIso_restrict_twistMultiplicationMap_degreeOpen`, which is unconditional
because `U_d` lies in the ratio locus of `d`. -/
theorem isIso_restrict_chart_degreeOpen_mulSheaf (D : RelativeProjTwists.ChartData A algebra)
    (hD : RelativeProjTwists.IsGradedChartIso D) (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ)
    (n m : ℤ) :
    letI := D.chart_isOpenImmersion U hU
    IsIso ((Scheme.Modules.restrictFunctor
          (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι).map
      ((Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU)).map
        (SheafOfModules.GradedAlgebra.mulSheaf algebra ((d : ℤ) * n) ((d : ℤ) * m)))) := by
  have := D.chart_isOpenImmersion U hU
  have hG := (Iso.inv_comp_eq _).mp
    (restrict_chart_mulSheaf_eq D hD U hU ((d : ℤ) * n) ((d : ℤ) * m))
  refine isIso_map_of_eq _ hG ?_
  refine isIso_map_iso_hom_comp _ _ _ ?_
  refine isIso_map_iso_hom_comp _ _ _ ?_
  exact isIso_map_comp_iso_inv _ _ _
    (MorphismsIntoProj.isIso_restrict_twistMultiplicationMap_degreeOpen (A.grading U) d n m)

/-- The same, read along the single open immersion
`U_d(Γ(U, 𝒜)) ⟶ Proj Γ(U, 𝒜) ⟶ Proj_S(𝒜)` and in the pullback vocabulary, which is the
shape the covering argument consumes. -/
theorem isIso_pullback_chart_degreeOpen_mulSheaf (D : RelativeProjTwists.ChartData A algebra)
    (hD : RelativeProjTwists.IsGradedChartIso D) (U : S.Opens) (hU : IsAffineOpen U) (d : ℕ)
    (n m : ℤ) :
    letI := D.chart_isOpenImmersion U hU
    IsIso ((Scheme.Modules.pullback
          ((AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι ≫
            (relativeProj A).chart U hU)).map
      (SheafOfModules.GradedAlgebra.mulSheaf algebra ((d : ℤ) * n) ((d : ℤ) * m))) := by
  have := D.chart_isOpenImmersion U hU
  have nat : Scheme.Modules.restrictFunctor ((relativeProj A).chart U hU) ⋙
      Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι ≅
      Scheme.Modules.pullback ((AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι ≫
        (relativeProj A).chart U hU) :=
    (Scheme.Modules.restrictFunctorComp
        (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).ι
        ((relativeProj A).chart U hU)).symm ≪≫
      Scheme.Modules.restrictFunctorIsoPullback _
  exact (NatIso.isIso_map_iff nat
    (SheafOfModules.GradedAlgebra.mulSheaf algebra ((d : ℤ) * n) ((d : ℤ) * m))).mp
    (isIso_restrict_chart_degreeOpen_mulSheaf D hD U hU d n m)

/-- **The multiplications of a `d`-divisible graded algebra on a relative homogeneous spectrum
become isomorphisms after pullback along any morphism whose image lies in the relative `U_d`** —
for an arbitrary quasi-coherent graded algebra carrying Tag 01NR's chart identifications.

Invertibility of a morphism of `𝒪_T`-modules is local on `T`; the inverse images of the charts of
the base cover `T`; and over each of them the morphism factors through the absolute degree-`d`
open of that chart, because its image lies in the part of the relative `U_d` lying over `U`, which
is the range of `U_d(Γ(U, 𝒜)) ⟶ Proj Γ(U, 𝒜) ⟶ Proj_S(𝒜)` by
`...RelativeProj.RelativeProjData.opensRange_ι_comp_chart`. The degrees are given as arbitrary
integers with proofs that they are the intended multiples of `d`, so that a caller spelling them
`n * d` needs no rewrite. -/
theorem isIso_pullback_mulSheaf_of_mem_degreeOpen (D : RelativeProjTwists.ChartData A algebra)
    (hD : RelativeProjTwists.IsGradedChartIso D) (d : ℕ) {T : Scheme.{u}}
    (g : T ⟶ (relativeProj A).scheme)
    (hg : ∀ t : T, g.base t ∈ (relativeProj A).degreeOpen d) {i j : ℤ} (n m : ℤ)
    (hi : i = (d : ℤ) * n) (hj : j = (d : ℤ) * m) :
    IsIso ((Scheme.Modules.pullback g).map
      (SheafOfModules.GradedAlgebra.mulSheaf algebra i j)) := by
  subst hi
  subst hj
  have hcov : IsOpenCover
      (fun U : S.affineOpens => g ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ (U.1 : S.Opens))) := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    refine top_le_iff.mp fun t _ => ?_
    obtain ⟨U, hU⟩ := exists_mem_toBase_preimage_affineOpens (A := A) (g.base t)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩
  refine AffineBaseChange.isIso_of_isIso_restrict _ _ hcov ?_
  intro U
  have := D.chart_isOpenImmersion U.1 U.2
  set W := g ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ (U.1 : S.Opens))
  set c := (AlgebraicGeometry.Proj.degreeOpen (A.grading U.1) d).ι ≫ (relativeProj A).chart U.1 U.2
  have hrange : Set.range (W.ι ≫ g).base ⊆ Set.range c.base := by
    rintro z ⟨x, rfl⟩
    have hz : (W.ι ≫ g).base x ∈
        (relativeProj A).toBase ⁻¹ᵁ (U.1 : S.Opens) ⊓ (relativeProj A).degreeOpen d :=
      ⟨x.2, hg _⟩
    rwa [← (relativeProj A).opensRange_ι_comp_chart U.1 U.2 d] at hz
  refine (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback W.ι) _).mpr ?_
  have hfac := AlgebraicGeometry.IsOpenImmersion.lift_fac c (W.ι ≫ g) hrange
  refine (NatIso.isIso_map_iff
    (Scheme.Modules.pullbackComp W.ι g ≪≫ eqToIso (congrArg Scheme.Modules.pullback hfac.symm) ≪≫
      (Scheme.Modules.pullbackComp _ c).symm)
    (SheafOfModules.GradedAlgebra.mulSheaf algebra ((d : ℤ) * n) ((d : ℤ) * m))).mpr ?_
  have := isIso_pullback_chart_degreeOpen_mulSheaf D hD U.1 U.2 d n m
  exact Functor.map_isIso (Scheme.Modules.pullback _) _

end Stacks.AlgebraicGeometry.TwistMapsInvertible

namespace Stacks.AlgebraicGeometry.RelativeVeroneseTwists

open Stacks.AlgebraicGeometry.GradedVeronese
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.TwistMapsInvertible

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} (D : RelativeProjTwists.TwistData A)
  (d : ℕ) {T : Scheme.{u}} (g : T ⟶ (relativeProj A).scheme)

/-- **The multiplications of `r^*(⨁_{n ∈ ℤ} 𝒪(nd))` are isomorphisms** for any morphism
`r : T ⟶ Proj_S(𝒜)` whose image lies in the relative degree-`d` locus, with no hypothesis on
`𝒜` beyond Situation 01NN.

This is `...RelativeVeroneseTwists.isIso_mulSheaf_pullbackTwistVeronese` with the generation
hypothesis traded for the locus: the Veronese multiplication is the algebra's own in the degrees
`(nd, md)` up to one `eqToHom` (`...GradedVeronese.veronese_mulSheaf`), its pullback is an
isomorphism by `...TwistMapsInvertible.isIso_pullback_mulSheaf_of_mem_degreeOpen`, and the
multiplication of a pulled-back graded algebra is that pullback conjugated by the comparison of
[Stacks, Tag 01CD]. -/
theorem isIso_mulSheaf_pullbackTwistVeronese_of_mem_degreeOpen
    (hg : ∀ t : T, g.base t ∈ (relativeProj A).degreeOpen d) (n m : ℤ) :
    IsIso (SheafOfModules.GradedAlgebra.mulSheaf
      (pullbackTwistVeronese D (d : ℤ) g) n m) := by
  refine Stacks.RingedSpace.isIso_mulSheaf_pullbackGradedAlgebra_of_isIso_map
    (ringedSpaceHom g) (twistVeronese D (d : ℤ)) n m ?_
  refine isIso_map_of_eq _ (veronese_mulSheaf D.algebra (d : ℤ) n m) ?_
  exact isIso_map_comp_iso_hom _ _
    (eqToIso (congrArg D.algebra.piece
      (by ring : n * (d : ℤ) + m * (d : ℤ) = (n + m) * (d : ℤ))))
    (isIso_pullback_mulSheaf_of_mem_degreeOpen D.chartData D.isGradedChartIso d g hg n m
      (mul_comm n (d : ℤ)) (mul_comm m (d : ℤ)))

/-- **The degree-zero piece of the `d`-divisible glued twists is invertible**, with no hypothesis:
it is `𝒪(0)`, whichever `d` the regrading uses. -/
theorem isInvertible_twistVeronese_piece_zero (e : ℤ) :
    Stacks.SheafOfModules.IsInvertible (relativeProj A).scheme.toRingedSpace.presheaf
      (isSheafStruct (relativeProj A).scheme) ((twistVeronese D e).piece 0) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    (relativeProj A).scheme.presheaf (relativeProj A).scheme.ringCatSheaf.2
    (D.algebra.piece (0 * e))).mpr
    (isInvertibleModule_piece_eq_zero D.chartData (zero_mul e))

/-- **The degree-zero piece of `r^*(⨁_n 𝒪(nd))` is invertible**, with no hypothesis: the pullback
of an invertible module is invertible, by [Stacks, Tag 0B8L]. This is the second of the two inputs
the recognition theorem asks for, and the reason no invertibility hypothesis survives below. -/
theorem isInvertible_pullbackTwistVeronese_piece_zero (e : ℤ) :
    Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      ((pullbackTwistVeronese D e g).piece 0) := by
  have := isInvertible_twistVeronese_piece_zero D e
  exact Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj (ringedSpaceHom g)
    ((twistVeronese D e).piece 0)

/-- **The comparison `c` of [Stacks, Tag 01O1] over the degree-`d` locus**: an isomorphism

`r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of `ℤ`-graded `𝒪_T`-algebras, for a morphism `r : T ⟶ Proj_S(𝒜)` whose image lies in
the relative degree-`d` locus and an invertible `𝒪_T`-module `ℒ` identified with `r^*𝒪(d)` by `α`.

This is `...RelativeVeroneseTwists.laurentComparison` with the degree-one generation hypothesis
removed. The recognition theorem `...GradedLaurentRecognition.gradedIso` is applied to the tag's
own source exactly as there; what has changed is that both of its inputs are now proved on the
locus the lemma lives over, by `isIso_mulSheaf_pullbackTwistVeronese_of_mem_degreeOpen` and
`isInvertible_pullbackTwistVeronese_piece_zero`. -/
def laurentComparisonOfDegreeOpen
    (hg : ∀ t : T, g.base t ∈ (relativeProj A).degreeOpen d)
    {Lc : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) Lc]
    (α : (pullbackTwistVeronese D (d : ℤ) g).piece 1 ≅ Lc) :
    pullbackTwistVeronese D (d : ℤ) g ≅ laurent Lc :=
  Stacks.AlgebraicGeometry.GradedLaurentRecognition.gradedIso
    (pullbackTwistVeronese D (d : ℤ) g) Lc α
    (isIso_mulSheaf_pullbackTwistVeronese_of_mem_degreeOpen D d g hg)
    (isInvertible_pullbackTwistVeronese_piece_zero D g (d : ℤ))

variable {S' : Scheme.{u}} {f : T ⟶ S'}
  {B : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S'.toRingedSpace)} {e : ℤ}

/-- **The new hypothesis is implied by the old one.** If `𝒜` is generated in degree one over
every affine open of the base then, for every positive `d`, the relative degree-`d` locus is the
whole of `Proj_S(𝒜)`, so every morphism into it lands there. Hence the statements of this file
subsume those of `StacksFrontier.AlgebraicGeometry.TwistTensor.RelativeLaurentComparison` for every
positive `d`.

`...ProjRepresentsF1.degreeOpen_one_eq_top` is `U_1 = Proj_S(𝒜)` under that hypothesis, and
`...RelativeProj.RelativeProjData.degreeOpen_le_of_dvd` puts `U_1 ⊆ U_d`. -/
theorem mem_degreeOpen_of_isGeneratedInDegreeOne
    (hgen : ProjRepresentsF1.IsGeneratedInDegreeOne A) {k : ℕ} (hk : 0 < k)
    {T' : Scheme.{u}} (h : T' ⟶ (relativeProj A).scheme) (t : T') :
    h.base t ∈ (relativeProj A).degreeOpen k := by
  have hle : (⊤ : (relativeProj A).scheme.Opens) ≤ (relativeProj A).degreeOpen k :=
    (ProjRepresentsF1.degreeOpen_one_eq_top A (relativeProj A) hgen).ge.trans
      ((relativeProj A).degreeOpen_le_of_dvd (one_dvd k) hk)
  exact hle (TopologicalSpace.Opens.mem_top _)

/-- **Stacks Project, Tag 01O1.** *The comparison `θ`, the commutativity of its characterising
triangle and its uniqueness, at the tag's own source, over the degree-`d` locus the lemma lives
over.*

Let `(f : T → S', e, ℒ, ψ)` be a quadruple, let `r : T ⟶ Proj_S(𝒜)` be a morphism whose image
lies in the relative degree-`d` locus — for the tag, `r_{d, ℒ, ψ}` — let
`v_n : f^*ℬ_{ne} ⟶ r^*𝒪(nd)` be the second leg of the tag's triangle and let `α : r^*𝒪(d) ≅ ℒ` be
the degree-one datum. If the triangle commutes for the comparison
`laurentComparisonOfDegreeOpen` built out of `α`, there is an isomorphism

`θ' : r^*(⨁_{n ∈ ℤ} 𝒪_{Proj_S(𝒜)}(nd)) ≅ ⨁_{n ∈ ℤ} ℒ^{⊗ n}`

of sheaves of `ℤ`-graded `𝒪_T`-algebras solving the triangle, and it is the unique homomorphism of
graded algebras that does.

This is `...RelativeVeroneseTwists.existsUnique_theta_of_degreeOneIso` with the degree-one
generation hypothesis replaced by the locus, which by
`mem_degreeOpen_of_isGeneratedInDegreeOne` is a weaker demand for every positive `d`. What is
still carried is the degree-one datum `α` together with the commutativity of the triangle for
`v`; see the module docstring for why those are one package and what identification would
discharge them. -/
theorem existsUnique_theta_of_degreeOpen
    (hg : ∀ t : T, g.base t ∈ (relativeProj A).degreeOpen d) (P : Quadruple f B e)
    (v : ∀ n : ℤ, (pullbackFunctor (ringedSpaceHom f)).obj (B.piece (n * e)) ⟶
      (pullbackTwistVeronese D (d : ℤ) g).piece n)
    (α : (pullbackTwistVeronese D (d : ℤ) g).piece 1 ≅ P.L)
    (hv : ∀ n : ℤ, v n ≫ (laurentComparisonOfDegreeOpen D d g hg α).hom.app n =
      P.twisting.app n) :
    ∃ θ' : pullbackTwistVeronese D (d : ℤ) g ≅ laurent P.L,
      (∀ n : ℤ, v n ≫ θ'.hom.app n = P.twisting.app n) ∧
        ∃! Θ : pullbackTwistVeronese D (d : ℤ) g ⟶ laurent P.L,
          ∀ n : ℤ, v n ≫ Θ.app n = P.twisting.app n :=
  ⟨laurentComparisonOfDegreeOpen D d g hg α, hv,
    Quadruple.existsUnique_theta P (pullbackTwistVeronese D (d : ℤ) g) v hv⟩

end Stacks.AlgebraicGeometry.RelativeVeroneseTwists

end
