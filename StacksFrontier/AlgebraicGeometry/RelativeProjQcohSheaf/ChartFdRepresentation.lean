module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineFdRepresentable
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransport
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenCover
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictDegreeOpen

/-!
# One chart of residue (i) of Tag 01NY: `F_d` of the restricted algebra and the relative `U_d`

Let `S` be a scheme, `A` a quasi-coherent graded `𝒪_S`-algebra (Situation 01NN), `U` an affine
open of `S` and `d ≥ 1`. [Stacks, Tag 01NU] is proved for an affine base
(`...RelativeProjQcohSheaf.Fd.representableByDegreeOpen`), so it applies to the restriction
`A|_U` of `A` to `U` (`...RelativeProjBridge.SheafGradedAlgebra.restrict`): the functor `F_d` of
Section 01NS for `A|_U` is represented by the absolute degree-`d` open of the graded ring of
*global* sections of `A|_U`. This file carries that representation over to the open of a
**relative** homogeneous spectrum `X` of `A` that the chart of `U` cuts out, namely
`U_d ⊓ f⁻¹(U)` where `f : X ⟶ S` is the structure morphism — one chart of residue (i).

Two identifications do it, and both are now available. The grading identification
`...SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RestrictDegreeOpen` replaces the degree-`d`
open of `Γ(⊤, A|_U)` by the degree-`d` open of `Γ(U, A)`, which is where the chart of `U` starts;
and `...RelativeProj.RelativeProjData.degreeOpenChartIso` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenCover` identifies that with
`U_d ⊓ f⁻¹(U)` compatibly with the two inclusions into `X`.

The naturality in the test scheme is carried along: it is
`...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass_pullback`, the naturality clause of
Tag 01NU, and both identifications are postcompositions and so commute with precomposition.

## Main definitions

* `...RelativeProjQcohSheaf.Fd.chartEquiv`: **`F_d` for `A|_U` is represented by the absolute
  degree-`d` open of `Γ(U, A)`** — Tag 01NU for the restricted algebra, read at the grading the
  chart of `U` uses.
* `...RelativeProjQcohSheaf.Fd.chartRelativeEquiv`: **`F_d` for `A|_U` is represented by the open
  `U_d ⊓ f⁻¹(U)` of a relative homogeneous spectrum of `A`.**
* `...RelativeProjQcohSheaf.Fd.chartHom`: the morphism into the relative homogeneous spectrum
  that a point of `F_d(T)` for `A|_U` defines, and `Fd.chartHom_eq_comp`, which factors it
  through the chart of `U`.

## Main results

* `...RelativeProjQcohSheaf.Fd.chartEquiv_pullback`, `...Fd.chartRelativeEquiv_pullback` and
  `...Fd.chartHom_pullback`: **all three are natural in the test scheme.**

## What this is not: the descent is not done here

This is residue (i) **over one chart**, and it is not residue (i). Gluing the chart-wise
morphisms into a single morphism out of a test scheme `W` needs them to agree on the overlaps
`W ⊓ f⁻¹(U) ⊓ f⁻¹(V)` of two charts, and that is **not** naturality in the test scheme: it is a
compatibility of the classifying morphism with a change of *chart*, i.e. with the transition
morphisms of Tag 01NO. Precisely, for affine opens `Z ≤ U` of the base what is owed is

`(the morphism of `Z`) ≫ projInclusionMap A Z U = (the morphism of `U`) restricted to `f⁻¹(Z)`,

an equality of morphisms into `AlgebraicGeometry.Proj (A.grading U)`.

**That equality is proved for the classifying morphism of [Stacks, Tag 01N8].** It used to be
recorded here that the ingredient was in the tree —
`Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projInclusionMap`,
the functoriality of the Tag 01NK morphism `r_{L, ψ}` along `...RelativeProj.projInclusionMap` —
but that the classifying morphism of a quadruple is
`...ProjTripleClassifying.classifyingHom`, defined by the `∃!` of [Stacks, Tag 01N8] and not as
that `r_{L, ψ}`, with no lemma identifying the two.
`...ProjChartGradedClassifying.classifyingHom_eq_glued` of
`StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedClassifying` is that lemma, and
`...ProjChartGradedClassifying.toProj_classifyingHom_comp_projInclusionMap` is the change of
chart it unlocks: for affine opens `Z ≤ V` of the base, the Tag 01N8 morphism of a datum for the
graded ring `𝒜(Z)`, followed by the Tag 01NO transition, is the Tag 01N8 morphism of that datum
composed with the restriction `𝒜(V) → 𝒜(Z)`.

**The grading mismatch is bridged, and the change of chart now applies to `Fd.chartEquiv`.** The
change of chart is stated for the graded rings `𝒜(Z)`, `𝒜(V)` of homogeneous sections, while
`Fd.chartEquiv` reaches them through the graded ring of *global* sections of `A|_U` and the
comparison `...SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme`. That mismatch is removed by
`...RelativeProjQcohSheaf.Fd.toProj_chartEquiv_mk` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassifyingTransport`, which identifies
the chart-wise morphism of `Fd.chartEquiv`, read into `Proj 𝒜(U)`, with the Tag 01N8 classifying
morphism of `𝒜(U)` itself, and `...Fd.toProj_chartEquiv_comp_projInclusionMap` of that file is the
change of chart for `Fd.chartEquiv` that follows.

**What is still owed.** That change of chart carries one hypothesis: that the Veronese families of
the two chart-wise quadruples are related by `...ProjChartGradedClassifying.comapVeronese` along
the restriction `𝒜(U) → 𝒜(Z)`. The restriction of quadruples needed to discharge it is in the tree,
as `...RelativeProjQcohSheaf.Fd.chartClass` of that same file: the chart-wise class of a quadruple
for `A` over an open of the base, `...Fd.baseChangeDownQ` of [Stacks, Tag 01NT] followed by
`...Fd.pullbackRestrictEquiv` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AlgebraTransport`. Neither chart class is
obtained from the other there — both come from *one* quadruple for `A` on `S` by a single base
change along the inclusion of its own affine open — and that is forced: a map from quadruples for
`A|_U` to quadruples for `A|_Z` would need
`(A.restrict U.ι).restrict (S.homOfLE h) = A.restrict Z.ι`, which fails by `rfl`, the two
differing by `Set.image_comp` on the image opens.

The identification of `...RelativeProjQcohSheaf.veroneseSections` of a chart-wise class with
`comapVeronese` of the one over a larger open used to be recorded here as not done, on the ground
that by `...Fd.chartClass_mk` the computation starts at a transport along
`...RelativeProjQcohSheaf.unitalHomInverse` of
`...SituationRestrict.restrictPullbackUnitalHom`, an adjoint transpose of the unit of the
restriction adjunction. That ground was wrong: the route reads the transported `ψ` on the
restriction-adjunction *unit image* of a section, where only the forward maps occur, and the
computation is `...RelativeProjQcohSheaf.veroneseSections_chartTwisting` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassVeronese`. With the two transports
of `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartClassComap` the identification is
`...RelativeProjQcohSheaf.heq_comapVeronese_chartTwisting`, so
`AlgebraicGeometry.Scheme.existsUnique_hom_of_opens_cover` now *does* have an unconditional
compatibility hypothesis to be given.

Residue (i) for a general base nevertheless stays open, and nothing below claims otherwise: the
`equiv` field of `...RelativeProjQcohSheaf.ProjDegreeRepresentation` is a **bijection**
`F_d(W) ≃ Mor(W, U_d)`, and what the chart agreement gives is the compatibility hypothesis its
forward map needs — injective, once glued, by
`...ZariskiSeparated.Fd.eq_of_pullback_eq_of_cover`. The inverse needs a compatible family of
chart-wise classes to be amalgamated into a class in `F_d(W)`, i.e. the Zariski sheaf property of
`F_d`; that is **no longer missing** — it is the theorem
`...RelativeProjQcohSheaf.Fd.isSheaf_functor`, and the amalgamation in the shape the descent
wants is `...RelativeProjQcohSheaf.Fd.exists_amalgamation_opens` of
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/RepresentableOfCharts.lean`, with no
hypothesis.

The **forward** map of the bijection over a general base is assembled out of this, in
`StacksFrontier/AlgebraicGeometry/RelativeProjQcohSheaf/ChartGlue.lean`, as
`...RelativeProjQcohSheaf.Fd.existsUnique_hom_degreeOpen`, together with its naturality in the
test scheme: the chart agreement is extended from a *nested* pair `Z ≤ U` to two arbitrary affine
opens of the base by `...RelativeProjQcohSheaf.Fd.chartHom_eq_of_chartClassInv_eq`, and the
inverse of `...RelativeProjQcohSheaf.Fd.chartClass` is
`...RelativeProjQcohSheaf.Fd.chartClassInv`. What is still missing is the **inverse** of the
bijection — whose obstruction is not the amalgamation but the *converse* of the chart agreement,
that two chart-wise classes with the same morphism into `X` have the same image under
`Fd.chartClassInv` — which is **proved**, as
`...RelativeProjQcohSheaf.Fd.chartClassInv_eq_of_chartHom_eq` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartConverse`, but carrying the clause that
the two chart-wise classes record the same morphism to `S`, which is implied by its conclusion
and whose discharge needs `Fd.chartHom ≫ P.toBase = ξ.1 ≫ U.ι` at a *chart* — and `equiv_scale`,
whose chart-wise Veronese computation is `...RelativeProjQcohSheaf.Fd.chartHom_scale` of
`StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.ChartScale` and which still needs
`Fd.chartClassInv` to commute with `...RelativeProjQcohSheaf.Fd.scale`.

## References

* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NT](https://stacks.math.columbia.edu/tag/01NT)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

/-! ### Postcomposition with an isomorphism of schemes -/

/-- Postcomposition with an isomorphism of schemes, as a bijection on the morphisms out of a test
scheme. -/
def homEquivOfSchemeIso {X Y : Scheme.{u}} (e : X ≅ Y) (T : Scheme.{u}) : (T ⟶ X) ≃ (T ⟶ Y) where
  toFun φ := φ ≫ e.hom
  invFun φ := φ ≫ e.inv
  left_inv φ := by simp
  right_inv φ := by simp

/-- `homEquivOfSchemeIso e T` sends a morphism `φ : T ⟶ X` to `φ ≫ e.hom`. -/
@[simp] theorem homEquivOfSchemeIso_apply {X Y : Scheme.{u}} (e : X ≅ Y) (T : Scheme.{u})
    (φ : T ⟶ X) : homEquivOfSchemeIso e T φ = φ ≫ e.hom := rfl

/-- Postcomposition with an isomorphism is natural in the test scheme. -/
theorem homEquivOfSchemeIso_comp {X Y : Scheme.{u}} (e : X ≅ Y) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (φ : T ⟶ X) :
    homEquivOfSchemeIso e T' (g ≫ φ) = g ≫ homEquivOfSchemeIso e T φ :=
  (Category.assoc g φ e.hom).symm

/-! ### `F_d` of the restricted algebra, at the chart's grading -/

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U : S.Opens) (hU : IsAffineOpen U)
  {k : ℕ}

/-- **[Stacks, Tag 01NU] for the restriction of `A` to an affine open `U` of the base, read at
the graded ring of sections of `A` over `U`.** The set `F_d(T)` of strict equivalence classes of
quadruples of Section 01NS for the algebra `A|_U` on the affine scheme `U` is in bijection with
the morphisms `T ⟶ U_d` into the absolute degree-`d` open
`AlgebraicGeometry.Proj.degreeOpen (A.grading U) d` of Equation 27.12.0.1 — the open of the
scheme the chart of `U` maps out of.

This is `...RelativeProjQcohSheaf.Quadruple.fdEquiv` for `A|_U`, whose target is the degree-`d`
open of the graded ring of *global* sections of `A|_U`, composed with the grading identification
`...SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme`. The quasi-coherence `Tag 01NU` asks of
the homogeneous pieces is not a hypothesis here: it is the field
`...RelativeProjBridge.SheafGradedAlgebra.isQuasicoherent` of the restricted algebra, which
`...SheafGradedAlgebra.restrict` supplies from
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`. -/
def Fd.chartEquiv (hk : 0 < k) (T : Scheme.{u}) :
    Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T
      ≃ (T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).toScheme) :=
  haveI : IsAffine U.toScheme := hU
  (Quadruple.fdEquiv (B := A.restrict U.ι) (T := T) hk
      (fun n => (A.restrict U.ι).isQuasicoherent n)).trans
    (SheafGradedAlgebra.restrictDegreeOpenHomEquiv A U k T)

/-- **The chart-wise representation is natural in the test scheme.** This is
`...RelativeProjQcohSheaf.Quadruple.classifyingHomOfClass_pullback`, the naturality clause of
Tag 01NU, read through a postcomposition. -/
theorem Fd.chartEquiv_pullback (hk : 0 < k) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartEquiv A U hU hk T' (Fd.pullback g ξ) = g ≫ Fd.chartEquiv A U hU hk T ξ := by
  have : IsAffine U.toScheme := hU
  have hnat := Quadruple.classifyingHomOfClass_pullback (B := A.restrict U.ι) hk
    (fun n => (A.restrict U.ι).isQuasicoherent n) g ξ
  have hstep : SheafGradedAlgebra.restrictDegreeOpenHomEquiv A U k T'
        (Quadruple.classifyingHomOfClass hk (fun n => (A.restrict U.ι).isQuasicoherent n)
          (Fd.pullback g ξ).2)
      = SheafGradedAlgebra.restrictDegreeOpenHomEquiv A U k T'
        (g ≫ Quadruple.classifyingHomOfClass hk
          (fun n => (A.restrict U.ι).isQuasicoherent n) ξ.2) := by
    rw [hnat]
  exact hstep.trans (SheafGradedAlgebra.restrictDegreeOpenHomEquiv_comp A U k g _)

/-! ### `F_d` of the restricted algebra and the relative degree-`d` open -/

variable (P : RelativeProjData A)

/-- **One chart of residue (i) of Tag 01NY**: for an affine open `U` of the base the set
`F_d(T)` of strict equivalence classes of quadruples for `A|_U` is in bijection with the
morphisms of `T` into the open `U_d ⊓ f⁻¹(U)` of a relative homogeneous spectrum `X` of `A`,
where `f : X ⟶ S` is the structure morphism and `U_d` is the relative degree-`d` open
`...RelativeProj.RelativeProjData.degreeOpen`.

`Fd.chartEquiv` lands in the absolute degree-`d` open of `Γ(U, A)`, and
`...RelativeProjData.degreeOpenChartIso` identifies that with `U_d ⊓ f⁻¹(U)`.

**No descent is claimed.** This is one chart; the morphisms attached to two different affine
opens of the base are not compared here, and cannot be with what the tree has — see the section
"What this is not" of this file's module documentation. -/
def Fd.chartRelativeEquiv (hU : IsAffineOpen U) (hk : 0 < k) (T : Scheme.{u}) :
    Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T
      ≃ (T ⟶ (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen k).toScheme) :=
  (Fd.chartEquiv A U hU hk T).trans
    (homEquivOfSchemeIso (P.degreeOpenChartIso U hU k) T)

/-- The chart-wise representation by the open `U_d ⊓ f⁻¹(U)` is natural in the test scheme. -/
theorem Fd.chartRelativeEquiv_pullback (hU : IsAffineOpen U) (hk : 0 < k)
    {T T' : Scheme.{u}} (g : T' ⟶ T) (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartRelativeEquiv A U P hU hk T' (Fd.pullback g ξ)
      = g ≫ Fd.chartRelativeEquiv A U P hU hk T ξ := by
  show homEquivOfSchemeIso (P.degreeOpenChartIso U hU k) T'
      (Fd.chartEquiv A U hU hk T' (Fd.pullback g ξ)) = _
  rw [Fd.chartEquiv_pullback A U hU hk g ξ]
  exact homEquivOfSchemeIso_comp (P.degreeOpenChartIso U hU k) g _

/-! ### The morphism into the relative homogeneous spectrum -/

/-- The morphism `T ⟶ X` into a relative homogeneous spectrum of `A` that a point of `F_d(T)`
for `A|_U` defines: the chart-wise morphism of `Fd.chartRelativeEquiv` followed by the inclusion
of `U_d ⊓ f⁻¹(U)`. -/
def Fd.chartHom (hU : IsAffineOpen U) (hk : 0 < k) (T : Scheme.{u})
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) : T ⟶ P.scheme :=
  Fd.chartRelativeEquiv A U P hU hk T ξ ≫ (P.toBase ⁻¹ᵁ U ⊓ P.degreeOpen k).ι

/-- **The morphism attached to a point of `F_d(T)` for `A|_U` factors through the chart of `U`**:
it is the absolute classifying morphism of `Fd.chartEquiv` followed by the inclusion of the
absolute degree-`d` open and then the chart `Proj Γ(U, A) ⟶ X`. This is
`...RelativeProjData.degreeOpenChartIso_hom_fac`. -/
theorem Fd.chartHom_eq_comp (hU : IsAffineOpen U) (hk : 0 < k) (T : Scheme.{u})
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartHom A U P hU hk T ξ
      = Fd.chartEquiv A U hU hk T ξ
          ≫ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) k).ι ≫ P.chart U hU := by
  rw [Fd.chartHom, Fd.chartRelativeEquiv, ← P.degreeOpenChartIso_hom_fac U hU k]
  simp [Fd.chartEquiv, homEquivOfSchemeIso]

/-- The morphism attached to a point of `F_d(T)` for `A|_U` is natural in the test scheme. -/
theorem Fd.chartHom_pullback (hU : IsAffineOpen U) (hk : 0 < k) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (ξ : Fd (situationAlgebra (A.restrict U.ι)) (k : ℤ) T) :
    Fd.chartHom A U P hU hk T' (Fd.pullback g ξ) = g ≫ Fd.chartHom A U P hU hk T ξ := by
  rw [Fd.chartHom, Fd.chartHom, Fd.chartRelativeEquiv_pullback A U P hU hk g ξ, Category.assoc]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
