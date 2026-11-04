module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.AffineQuadrupleBijection
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.DegreeOpenCover

/-!
# Tag 01NU over an affine base, at the relative `U_d`

Let `S` be an **affine** scheme, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous
pieces (Situation 01NN), `d ≥ 1`, and let `X` be a relative homogeneous spectrum of `𝒜` — a
`Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData`, hence in particular `Proj_S(𝒜)` of
Lemma 01NQ. [Stacks, Tag 01NU] is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.fdEquiv`, stated about the absolute
degree-`d` open `U_d ⊆ Proj Γ(S, 𝒜)` of Equation 27.12.0.1. This file moves it to the degree-`d`
open `RelativeProjData.degreeOpen` of `X`.

Over an affine base the move needs no glueing: `⊤` is an affine open of `S`, its chart
`Proj Γ(S, 𝒜) ⟶ X` has range `f⁻¹(⊤) = ⊤`, and so the chart carries the absolute degree-`d`
open isomorphically onto the relative one.

## Main results

* `...RelativeProj.RelativeProjData.degreeOpenAffineIso`: over an affine base the relative
  degree-`d` open of any relative homogeneous spectrum **is** the absolute degree-`d` open
  `⋃_{g ∈ Γ(S, 𝒜)_d} D₊(g)` of `Proj Γ(S, 𝒜)`, compatibly with the inclusion into `X`
  (`degreeOpenAffineIso_hom_fac`). This is `RelativeProjData.degreeOpenChartIso` at `U = ⊤`,
  where `f⁻¹(⊤) ⊓ U_d` is `U_d`.
* `...RelativeProjQcohSheaf.Quadruple.fdEquivDegreeOpen`: **the `equiv` field of
  `...RelativeProjQcohSheaf.ProjDegreeRepresentation` over an affine base**, i.e. the bijection
  `F_d(T) ≃ Mor(T, U_d)` of [Stacks, Tag 01NU] with `U_d` the degree-`d` open of the relative
  `Proj` itself. No quasi-compactness of `T` is needed.

## References

* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
* [Stacks Project, Tag 01NY](https://stacks.math.columbia.edu/tag/01NY)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwistGlue

universe u

namespace Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (P : RelativeProjData A) [IsAffine S]

/-- **Over an affine base the relative degree-`d` open is the absolute one.** For `S` affine and
`𝒜` with quasi-coherent homogeneous pieces, the degree-`d` open
`...RelativeProj.RelativeProjData.degreeOpen` of a relative homogeneous spectrum `X` of `𝒜` is
isomorphic to the absolute degree-`d` open `⋃_{g ∈ Γ(S, 𝒜)_d} D₊(g)` of `Proj Γ(S, 𝒜)` of
Equation 27.12.0.1, compatibly with the two inclusions into `X`
(`degreeOpenAffineIso_hom_fac`).

This is `RelativeProjData.degreeOpenChartIso` at the affine open `U = ⊤`, whose target
`f⁻¹(⊤) ⊓ U_d` is `U_d`: the two open immersions into `X` — the inclusion of the absolute
degree-`d` open followed by the chart of `⊤`, and the inclusion of the relative `U_d` — have the
same range by `RelativeProjData.opensRange_ι_comp_chart`. -/
def degreeOpenAffineIso (d : ℕ) :
    (AlgebraicGeometry.Proj.degreeOpen (A.grading (⊤ : S.Opens)) d).toScheme ≅
      (P.degreeOpen d).toScheme :=
  AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq
    ((AlgebraicGeometry.Proj.degreeOpen (A.grading (⊤ : S.Opens)) d).ι ≫
      P.chart ⊤ (isAffineOpen_top S))
    (P.degreeOpen d).ι
    (by
      have h := P.opensRange_ι_comp_chart ⊤ (isAffineOpen_top S) d
      rw [Scheme.Hom.preimage_top, top_inf_eq,
        ← Scheme.Opens.opensRange_ι (P.degreeOpen d)] at h
      exact congrArg (fun V : P.scheme.Opens => (V : Set P.scheme)) h)

/-- The comparison of the relative degree-`d` open with the absolute one over an affine base is
compatible with the two inclusions into the relative `Proj`: composed with the inclusion of the
relative `U_d` it is the inclusion of the absolute degree-`d` open followed by the chart of
`⊤`. -/
theorem degreeOpenAffineIso_hom_fac (d : ℕ) :
    (P.degreeOpenAffineIso d).hom ≫ (P.degreeOpen d).ι =
      (AlgebraicGeometry.Proj.degreeOpen (A.grading (⊤ : S.Opens)) d).ι ≫
        P.chart ⊤ (isAffineOpen_top S) :=
  AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

open Stacks.AlgebraicGeometry.RelativeProj

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S}

/-- **Tag 01NU at the degree-`d` open of the relative `Proj`, over an affine
base.** Let `S` be affine, `𝒜` a graded `𝒪_S`-algebra with quasi-coherent homogeneous pieces
(Situation 01NN), `d ≥ 1`, `T` a test scheme, and let `X` be a relative homogeneous spectrum of
`𝒜` — in particular `Proj_S(𝒜)` of Lemma 01NQ. The set `F_d(T)` of strict equivalence classes of
quadruples of Section 01NS over `T` is in bijection with the morphisms `T ⟶ U_d`, where `U_d` is
the degree-`d` open `...RelativeProj.RelativeProjData.degreeOpen` of `X`.

This is `...RelativeProjQcohSheaf.Quadruple.fdEquiv` — the same bijection for the *absolute*
degree-`d` open of `Proj Γ(S, 𝒜)` — carried along
`...RelativeProj.RelativeProjData.degreeOpenAffineIso`. It is the `equiv` field of
`...RelativeProjQcohSheaf.ProjDegreeRepresentation` over an affine base, and no quasi-compactness
of `T` is used. -/
def Quadruple.fdEquivDegreeOpen [IsAffine S] (P : RelativeProjData A) {d : ℕ} (hd : 0 < d)
    (hqc : ∀ n : ℤ, ((situationAlgebra A).piece n).IsQuasicoherent) (T : Scheme.{u}) :
    Fd (situationAlgebra A) (d : ℤ) T ≃ (T ⟶ (P.degreeOpen d).toScheme) :=
  (Quadruple.fdEquiv (T := T) (B := A) hd hqc).trans
    (Iso.homCongr (Iso.refl T) (P.degreeOpenAffineIso d))

/-- The bijection of `Quadruple.fdEquivDegreeOpen` is the classifying morphism of [Stacks, Tag
01NU] followed by the chart of `⊤`. -/
theorem Quadruple.fdEquivDegreeOpen_apply [IsAffine S] (P : RelativeProjData A) {d : ℕ}
    (hd : 0 < d) (hqc : ∀ n : ℤ, ((situationAlgebra A).piece n).IsQuasicoherent) (T : Scheme.{u})
    (ξ : Fd (situationAlgebra A) (d : ℤ) T) :
    Quadruple.fdEquivDegreeOpen P hd hqc T ξ =
      Quadruple.classifyingHomOfClass hd hqc ξ.2 ≫ (P.degreeOpenAffineIso d).hom :=
  rfl

/-- `Quadruple.fdEquivDegreeOpen` with the degree an integer, which is the type the `equiv` field
of `...RelativeProjQcohSheaf.ProjDegreeRepresentation` is stated at. -/
def Quadruple.fdEquivDegreeOpen' [IsAffine S] (P : RelativeProjData A) {d : ℤ} (hd : 0 < d)
    (hqc : ∀ n : ℤ, ((situationAlgebra A).piece n).IsQuasicoherent) (T : Scheme.{u}) :
    Fd (situationAlgebra A) d T ≃ (T ⟶ (P.degreeOpen d.toNat).toScheme) :=
  Int.toNat_of_nonneg hd.le ▸ Quadruple.fdEquivDegreeOpen P (d := d.toNat) (by omega) hqc T

/-- For `S` affine and `𝒜` with quasi-coherent homogeneous pieces, a
`...RelativeProjQcohSheaf.ProjDegreeRepresentation` whose `equiv` field is the bijection
`Quadruple.fdEquivDegreeOpen'`, from its naturality in the test scheme and its compatibility with
the transitions `F_d → F_{a d}`. -/
def ProjDegreeRepresentation.ofAffine [IsAffine S] (P : RelativeProjData A)
    (hqc : ∀ n : ℤ, ((situationAlgebra A).piece n).IsQuasicoherent)
    (hpullback : ∀ (d : ℤ) (hd : 0 < d) (W W' : Scheme.{u}) (_hW : CompactSpace W)
      (_hW' : CompactSpace W') (h : W' ⟶ W) (ξ : Fd (situationAlgebra A) d W),
      Quadruple.fdEquivDegreeOpen' P hd hqc W' (Fd.pullback h ξ)
        = h ≫ Quadruple.fdEquivDegreeOpen' P hd hqc W ξ)
    (hscale : ∀ (d a : ℤ) (hd : 0 < d) (ha : 0 < a) (W : Scheme.{u}) (_hW : CompactSpace W)
      (ξ : Fd (situationAlgebra A) d W),
      Quadruple.fdEquivDegreeOpen' P (mul_pos ha hd) hqc W (Fd.scale ha ξ)
        = Quadruple.fdEquivDegreeOpen' P hd hqc W ξ ≫ P.scheme.homOfLE
            (P.degreeOpen_toNat_le_of_dvd hd (mul_pos ha hd) ⟨a, mul_comm a d⟩)) :
    ProjDegreeRepresentation A P where
  equiv _d hd W _ := Quadruple.fdEquivDegreeOpen' P hd hqc W
  equiv_pullback := hpullback
  equiv_scale := hscale

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf

end
