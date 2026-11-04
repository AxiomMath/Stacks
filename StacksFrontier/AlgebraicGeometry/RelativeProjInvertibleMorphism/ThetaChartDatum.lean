module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ChartCoverGlue
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeIntTheta
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.GlobalMorphism
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistGlue
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.Pullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartIntPullbackMul

/-!
# The chart datum of the relative `θ` of Stacks Tag 01O9

Let `(S, 𝒜, f : X ⟶ S, ℒ, ψ)` be the data of [Stacks, Tag 01O8] and let
`r = r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` be the morphism of [Stacks, Tag 01O9]
(`…GradedPowerMap.globalMorphism`). This file sets up the two legs out of the piece
`O_V = U(ψ) ∩ f^{-1}(V)` of `U(ψ)` over an affine open `V` of the base, over which the degreewise
family

`θ_n : r^*(⨁_{d ∈ ℤ} 𝒪_{Proj_S(𝒜)}(d))_n ⟶ ℒ^{⊗ n}|_{U(ψ)}`

is to be glued from [Stacks, Tag 01NK]'s `θ` for the induced datum `…GradedPowerMap.affineDatum V`.

## Why the pieces of `U(ψ)` and not the charts of `Proj_S(𝒜)`

For the pushforward form `𝒪_{Proj_S(𝒜)}(n) ⟶ r_*(ℒ^{⊗ n}|_{U(ψ)})` over the charts of
[Stacks, Tag 01NQ], the target's sections over a chart image are the sections of `ℒ^{⊗ n}` over
`r^{-1}` of that image, which is `O_V` because `r` is a morphism over `S`
(`…GradedPowerMap.globalMorphism_comp_toBase`); that is the route `…GradedPowerMap.theta` takes.
The legs here work on the pieces of `U(ψ)` instead and do not use it.

`θ` itself has no such obligation. An inverse image restricts along an open immersion of its
**source** by pseudofunctoriality alone, and `…GradedPowerMap.ι_globalMorphism` factors
`O_V ↪ U(ψ) ≫ r` through the chart over `V`. So the cover is the one `r` was itself glued over —
the preimages of the affine opens of the base — and no inverse image of an open of `Proj_S(𝒜)`
is taken. This is the shape in which [Stacks, Tag 07ZG] performs the same construction for a
homomorphism of graded algebras (`…Tag07ZGTwist.relativeTwistChart`), and the two gluings share
the cover rung `…RelativeProjChartGlue.existsUnique_hom_of_nested_affineOpens`.

## Main definitions

* `…GradedPowerMap.pieceIso`: the identification of `O_V` with the covering open of the induced
  datum over `V`, `…GradedPowerMap.toBaseIso` followed by the inverse of
  `…GradedPowerMap.datumIso`.
* `…GradedPowerMap.pieceLeg`, `…GradedPowerMap.pieceTargetLeg`: the legs `O_V ⟶ Proj 𝒜(V)` and
  `O_V ⟶ f^{-1}(V)` — `pieceIso` followed by [Stacks, Tag 01NK]'s morphism for the induced datum,
  and by the inclusion of that datum's covering open.
* `…GradedPowerMap.chartSourceLegIso`, `…GradedPowerMap.chartTargetLegIso`: the identifications of
  the source and the target of `θ` over the piece with inverse images along those two legs; and
  `chartSourceIso`, `chartTargetIso`, the same with the leg split into its two steps, which is the
  shape the chart datum consumes.
* `…GradedPowerMap.thetaChart`: **the chart datum** — [Stacks, Tag 01NK]'s `θ` for the induced
  datum, conjugated by those two identifications.
* `…GradedPowerMap.IsNestedThetaChart`: the one remaining obligation, the nested compatibility of
  the chart data; its docstring names the three parts it is to be assembled from and which of them
  are proved.

## Main results

* `…GradedPowerMap.pieceLeg_comp_chart`: **the leg followed by the chart of [Stacks, Tag 01NQ] is
  the inclusion of the piece followed by `r`.** This is `…GradedPowerMap.ι_globalMorphism` read as
  a factorisation, and it is what lets the source of `θ` be computed over the piece.
* `…GradedPowerMap.pieceIso_comp_ι` and `…GradedPowerMap.pieceTargetLeg_comp_ι`: the
  identification of `O_V` carries the inclusion of the covering open of the induced datum into
  `f^{-1}(V)` and then into `X` to the inclusion of `O_V` into `U(ψ)` and then into `X`. This is
  what lets the target of `θ` be computed over the piece.
* `…GradedPowerMap.existsUnique_relTheta`: **the degreewise component of the relative `θ` exists
  and is unique**, granted `IsNestedThetaChart`. The cover rung is
  `…RelativeProjChartGlue.existsUnique_hom_of_preimage_nested`.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedTheta (twistM)
open Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild (theta laurentRestrict)
open Stacks.AlgebraicGeometry.ProjChartIntPullbackMul (intPullIso)
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjFromSections
open Stacks.AlgebraicGeometry.Tag07ZGTwist (relativeTwist chartTwistIso)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace GradedPowerMap

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {T : Scheme.{u}} {f : T ⟶ S}
  (P : GradedPowerMap A f) (rp : RelativeProjData A)

/-! ### The piece of `U(ψ)` over an affine open of the base -/

/-- **The piece of `U(ψ)` over an affine open `V` of the base, identified with the covering open
of the induced datum there.** `…GradedPowerMap.toBaseIso` reads the piece as the open `U(ψ_V)` of
`X` and `…GradedPowerMap.datumIso` reads the covering open of the induced datum as that same open,
so the composite is an identification of the two subschemes. -/
public def pieceIso (V : S.Opens) (hV : IsAffineOpen V) :
    (P.toBase ⁻¹ᵁ V).toScheme ≅ ((P.affineDatum V).coveringOpen).toScheme :=
  P.toBaseIso V hV ≪≫ (P.datumIso V).symm

/-- **The identification of the piece respects the two inclusions into `X`.** -/
public theorem pieceIso_comp_ι (V : S.Opens) (hV : IsAffineOpen V) :
    (P.pieceIso V hV).hom ≫ ((P.affineDatum V).coveringOpen).ι ≫ (f ⁻¹ᵁ V).ι
      = (P.toBase ⁻¹ᵁ V).ι ≫ P.coveringOpen.ι := by
  rw [pieceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← P.datumIso_hom_ι V,
    Iso.inv_hom_id_assoc, P.toBaseIso_hom_ι V hV]

/-- **The leg out of the piece**: the identification of the piece with the covering open of the
induced datum over `V`, followed by [Stacks, Tag 01NK]'s morphism `r_{ℒ|_{f^{-1}V}, ψ_V}` for that
datum. -/
public def pieceLeg (V : S.Opens) (hV : IsAffineOpen V) :
    (P.toBase ⁻¹ᵁ V).toScheme ⟶ AlgebraicGeometry.Proj (A.grading V) :=
  (P.pieceIso V hV).hom ≫ (P.affineDatum V).glued

/-- **The leg followed by the chart of [Stacks, Tag 01NQ] is the inclusion of the piece followed
by `r_{ℒ,ψ}`.** This is `…GradedPowerMap.ι_globalMorphism` read as a factorisation of the
composite through the chart over `V`; it is what computes the source of `θ` over the piece. -/
public theorem pieceLeg_comp_chart (V : S.affineOpens) :
    P.pieceLeg (V.1 : S.Opens) V.2 ≫ rp.chart (V.1 : S.Opens) V.2
      = (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι ≫ P.globalMorphism rp := by
  rw [P.ι_globalMorphism rp V]
  simp only [pieceLeg, pieceIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rfl

/-- **The leg out of the piece into `f^{-1}(V)`**: the identification of the piece with the
covering open of the induced datum over `V`, followed by that covering open's inclusion. -/
public def pieceTargetLeg (V : S.Opens) (hV : IsAffineOpen V) :
    (P.toBase ⁻¹ᵁ V).toScheme ⟶ (f ⁻¹ᵁ V).toScheme :=
  (P.pieceIso V hV).hom ≫ ((P.affineDatum V).coveringOpen).ι

/-- **The leg into `f^{-1}(V)` followed by its inclusion is the inclusion of the piece followed by
that of `U(ψ)`.** This is `…GradedPowerMap.pieceIso_comp_ι` reassociated; it is what computes the
target of `θ` over the piece. -/
public theorem pieceTargetLeg_comp_ι (V : S.Opens) (hV : IsAffineOpen V) :
    P.pieceTargetLeg V hV ≫ (f ⁻¹ᵁ V).ι = (P.toBase ⁻¹ᵁ V).ι ≫ P.coveringOpen.ι :=
  (Category.assoc _ _ _).trans (P.pieceIso_comp_ι V hV)

/-! ### The source and the target of `θ` over a piece -/

/-- **The source of `θ` over the piece, identified with the inverse image along the leg of the
absolute twist on `Proj 𝒜(V)`.** The inverse image along the inclusion of the piece of the inverse
image along `r_{ℒ,ψ}` is the inverse image along the composite, which
`…GradedPowerMap.pieceLeg_comp_chart` factors through the chart over `V`; the inverse image along
the chart of the relative twist is the absolute twist, by [Stacks, Tag 01NR]'s chart
identification `…Tag07ZGTwist.chartTwistIso`. -/
public def chartSourceLegIso (V : S.affineOpens) (n : ℤ) :
    (Scheme.Modules.pullback (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).obj
        ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj (relativeTwist A n))
      ≅ (Scheme.Modules.pullback (P.pieceLeg (V.1 : S.Opens) V.2)).obj
          (twistM (A.grading (V.1 : S.Opens)) n) :=
  (Scheme.Modules.pullbackComp (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι
        (P.globalMorphism (relativeProj A))).app (relativeTwist A n)
    ≪≫ (Scheme.Modules.pullbackCongr
          (P.pieceLeg_comp_chart (relativeProj A) V)).symm.app (relativeTwist A n)
    ≪≫ (Scheme.Modules.pullbackComp (P.pieceLeg (V.1 : S.Opens) V.2)
          ((relativeProj A).chart (V.1 : S.Opens) V.2)).symm.app (relativeTwist A n)
    ≪≫ (Scheme.Modules.pullback (P.pieceLeg (V.1 : S.Opens) V.2)).mapIso
          (chartTwistIso A n V)

/-- **The underlying morphism of the four-fold composite of identifications that the source of the
chart datum is presented by**, at the level of variables.

Taking it at the concrete inverse images is a chain of delta steps the kernel cannot afford,
although the composite and the resulting morphism both elaborate — the same obstruction
`…Tag07ZGTwist.natIso_trans₄_hom` is written against for [Stacks, Tag 07ZG]. The chain is
therefore taken once, here, with the functors and the natural isomorphisms as variables, and each
concrete instance is a substitution. -/
public theorem natIso_four_hom {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    (F : ℰ ⥤ 𝒟) (H : 𝒞 ⥤ ℰ) {P₁ P₂ P₃ : 𝒞 ⥤ 𝒟}
    (a : P₁ ≅ P₂) (b : P₃ ≅ P₂) (c : H ⋙ F ≅ P₃) (M : 𝒞) {Tw : ℰ} (e : H.obj M ≅ Tw) :
    (a.app M ≪≫ b.symm.app M ≪≫ c.symm.app M ≪≫ F.mapIso e).hom
      = a.hom.app M ≫ b.inv.app M ≫ c.inv.app M ≫ F.map e.hom :=
  rfl

/-- **The underlying morphism of the five-fold composite of identifications that the target of the
chart datum is presented by**, at the level of variables, for the same reason as
`…GradedPowerMap.natIso_four_hom`. -/
public theorem natIso_five_hom {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    (F : ℰ ⥤ 𝒟) (H : 𝒞 ⥤ ℰ) {P₁ P₂ P₃ : 𝒞 ⥤ 𝒟} {X : 𝒟}
    (a : P₁ ≅ P₂) (b : P₃ ≅ P₂) (c : H ⋙ F ≅ P₃) (N : 𝒞) (e₁ : X ≅ P₁.obj N)
    {Tw : ℰ} (e₂ : H.obj N ≅ Tw) :
    (e₁ ≪≫ a.app N ≪≫ b.symm.app N ≪≫ c.symm.app N ≪≫ F.mapIso e₂).hom
      = e₁.hom ≫ a.hom.app N ≫ b.inv.app N ≫ c.inv.app N ≫ F.map e₂.hom :=
  rfl

/-- `…GradedPowerMap.chartSourceLegIso` read as the four-factor composite its nested compatibility
is stated against: the pseudofunctoriality factor of the inclusion of the piece and of `r_{ℒ,ψ}`,
the congruence of the two readings of that composite, the pseudofunctoriality factor of the leg
and the chart, and the inverse image along the leg of [Stacks, Tag 01NR]'s chart identification. -/
public theorem chartSourceLegIso_hom (V : S.affineOpens) (n : ℤ) :
    (P.chartSourceLegIso V n).hom
      = (Scheme.Modules.pullbackComp (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι
            (P.globalMorphism (relativeProj A))).hom.app (relativeTwist A n)
        ≫ ((Scheme.Modules.pullbackCongr
              (P.pieceLeg_comp_chart (relativeProj A) V)).inv.app (relativeTwist A n)
          ≫ (Scheme.Modules.pullbackComp (P.pieceLeg (V.1 : S.Opens) V.2)
                ((relativeProj A).chart (V.1 : S.Opens) V.2)).inv.app (relativeTwist A n)
          ≫ (Scheme.Modules.pullback (P.pieceLeg (V.1 : S.Opens) V.2)).map
                (chartTwistIso A n V).hom) :=
  natIso_four_hom (Scheme.Modules.pullback (P.pieceLeg (V.1 : S.Opens) V.2))
    (Scheme.Modules.pullback ((relativeProj A).chart (V.1 : S.Opens) V.2))
    (Scheme.Modules.pullbackComp (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι
      (P.globalMorphism (relativeProj A)))
    (Scheme.Modules.pullbackCongr (P.pieceLeg_comp_chart (relativeProj A) V))
    (Scheme.Modules.pullbackComp (P.pieceLeg (V.1 : S.Opens) V.2)
      ((relativeProj A).chart (V.1 : S.Opens) V.2))
    (relativeTwist A n) (chartTwistIso A n V)

/-- **The source of `θ` over the piece, identified with the inverse image of the absolute twist
along the two steps of the leg.** This is `…GradedPowerMap.chartSourceLegIso` followed by the
pseudofunctoriality factor splitting the leg into the identification of the piece and
[Stacks, Tag 01NK]'s morphism, which is the shape the chart datum consumes. -/
public def chartSourceIso (V : S.affineOpens) (n : ℤ) :
    (Scheme.Modules.pullback (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).obj
        ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj (relativeTwist A n))
      ≅ (Scheme.Modules.pullback ((P.pieceIso (V.1 : S.Opens) V.2).hom)).obj
          ((Scheme.Modules.pullback (P.affineDatum (V.1 : S.Opens)).glued).obj
            (twistM (A.grading (V.1 : S.Opens)) n)) :=
  P.chartSourceLegIso V n
    ≪≫ (Scheme.Modules.pullbackComp ((P.pieceIso (V.1 : S.Opens) V.2).hom)
          (P.affineDatum (V.1 : S.Opens)).glued).symm.app
          (twistM (A.grading (V.1 : S.Opens)) n)

/-- **The target of `θ` over the piece, identified with the inverse image along the leg into
`f^{-1}(V)` of the tensor powers of `ℒ|_{f^{-1}(V)}`.**
`…GradedPowerMap.pieceTargetLeg_comp_ι` identifies the two routes from the piece into `X`, and
`…ProjChartIntPullbackMul.intPullIso` — [Stacks, Tag 01CU]'s own comparison of the integer tensor
powers under pullback — identifies the powers of `ℒ|_{f^{-1}(V)}` with the restrictions of the
powers of `ℒ`. -/
public def chartTargetLegIso (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (Scheme.Modules.pullback (P.toBase ⁻¹ᵁ V).ι).obj
        ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι)
      ≅ (Scheme.Modules.pullback (P.pieceTargetLeg V hV)).obj
          (tensorPowerModule (f ⁻¹ᵁ V).toScheme
            ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n) :=
  (Scheme.Modules.pullback (P.toBase ⁻¹ᵁ V).ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).app
        (tensorPowerModule T P.L n))
    ≪≫ (Scheme.Modules.pullbackComp (P.toBase ⁻¹ᵁ V).ι P.coveringOpen.ι).app
          (tensorPowerModule T P.L n)
    ≪≫ (Scheme.Modules.pullbackCongr
          (P.pieceTargetLeg_comp_ι V hV)).symm.app (tensorPowerModule T P.L n)
    ≪≫ (Scheme.Modules.pullbackComp (P.pieceTargetLeg V hV) (f ⁻¹ᵁ V).ι).symm.app
          (tensorPowerModule T P.L n)
    ≪≫ (Scheme.Modules.pullback (P.pieceTargetLeg V hV)).mapIso
          (intPullIso (f ⁻¹ᵁ V).ι P.L n)

/-- `…GradedPowerMap.chartTargetLegIso` read as the five-factor composite its nested compatibility
is to be stated against. -/
public theorem chartTargetLegIso_hom (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (P.chartTargetLegIso V hV n).hom
      = (Scheme.Modules.pullback (P.toBase ⁻¹ᵁ V).ι).map
            ((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).hom.app
              (tensorPowerModule T P.L n))
        ≫ (Scheme.Modules.pullbackComp (P.toBase ⁻¹ᵁ V).ι P.coveringOpen.ι).hom.app
              (tensorPowerModule T P.L n)
          ≫ (Scheme.Modules.pullbackCongr
                (P.pieceTargetLeg_comp_ι V hV)).inv.app (tensorPowerModule T P.L n)
          ≫ (Scheme.Modules.pullbackComp (P.pieceTargetLeg V hV) (f ⁻¹ᵁ V).ι).inv.app
                (tensorPowerModule T P.L n)
          ≫ (Scheme.Modules.pullback (P.pieceTargetLeg V hV)).map
                (intPullIso (f ⁻¹ᵁ V).ι P.L n).hom :=
  natIso_five_hom (Scheme.Modules.pullback (P.pieceTargetLeg V hV))
    (Scheme.Modules.pullback (f ⁻¹ᵁ V).ι)
    (Scheme.Modules.pullbackComp (P.toBase ⁻¹ᵁ V).ι P.coveringOpen.ι)
    (Scheme.Modules.pullbackCongr (P.pieceTargetLeg_comp_ι V hV))
    (Scheme.Modules.pullbackComp (P.pieceTargetLeg V hV) (f ⁻¹ᵁ V).ι)
    (tensorPowerModule T P.L n)
    ((Scheme.Modules.pullback (P.toBase ⁻¹ᵁ V).ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).app
        (tensorPowerModule T P.L n)))
    (intPullIso (f ⁻¹ᵁ V).ι P.L n)

/-- **The target of `θ` over the piece, identified with the inverse image of [Stacks, Tag 01NK]'s
target for the induced datum along the identification of the piece.** This is
`…GradedPowerMap.chartTargetLegIso` followed by the pseudofunctoriality factor splitting the leg
into the identification of the piece and the inclusion of the covering open of the induced datum,
which is the shape the chart datum consumes. -/
public def chartTargetIso (V : S.Opens) (hV : IsAffineOpen V) (n : ℤ) :
    (Scheme.Modules.pullback (P.toBase ⁻¹ᵁ V).ι).obj
        ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι)
      ≅ (Scheme.Modules.pullback ((P.pieceIso V hV).hom)).obj
          ((P.affineDatum V).laurentPiece n) :=
  P.chartTargetLegIso V hV n
    ≪≫ (Scheme.Modules.pullbackComp ((P.pieceIso V hV).hom)
          ((P.affineDatum V).coveringOpen).ι).symm.app
          (tensorPowerModule (f ⁻¹ᵁ V).toScheme
            ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n)
    ≪≫ (Scheme.Modules.pullback ((P.pieceIso V hV).hom)).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback
            ((P.affineDatum V).coveringOpen).ι).app
            (tensorPowerModule (f ⁻¹ᵁ V).toScheme
              ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj P.L) n)).symm

/-! ### The chart datum -/

/-- **The chart datum of the relative `θ` over an affine open `V` of the base**: [Stacks, Tag
01NK]'s `θ` for the induced datum `…GradedPowerMap.affineDatum V`, pulled back along the
identification of the piece and conjugated by `…GradedPowerMap.chartSourceIso` and
`…GradedPowerMap.chartTargetIso`.

This is the local datum the degreewise family of the relative `θ` is glued from, in the shape
`Stacks.AlgebraicGeometry.ModuleHomGlue.ofPullback` and
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq` consume it — the same shape
[Stacks, Tag 07ZG]'s `…Tag07ZGTwist.relativeTwistChart` takes. -/
public def thetaChart (V : S.affineOpens) (n : ℤ) :
    (Scheme.Modules.pullback (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).obj
        ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj (relativeTwist A n))
      ⟶ (Scheme.Modules.pullback (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).obj
          ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι) :=
  (P.chartSourceIso V n).hom
    ≫ (Scheme.Modules.pullback ((P.pieceIso (V.1 : S.Opens) V.2).hom)).map
        ((theta (A.grading (V.1 : S.Opens)) (P.affineDatum (V.1 : S.Opens))).app n)
    ≫ (P.chartTargetIso (V.1 : S.Opens) V.2 n).inv

/-! ### The nested compatibility, and the degreewise family it glues to -/

/-- **The nested compatibility of the chart data of the relative `θ`**, in exactly the shape
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq` consumes it: for affine opens
`Z ≤ V` of the base, the chart datum over `V`, pulled back along the inclusion of the piece over
`Z` into the piece over `V`, is the chart datum over `Z`.

This is the one remaining obligation of the gluing of the relative `θ`. It is to be assembled by
`…Tag07ZGTwist.nested_of_comp_target`, which asks for three things, and **the first is proved**:

* the nested compatibility of the **source** identifications, with [Stacks, Tag 01MY]'s comparison
  map for the restriction `𝒜(V) → 𝒜(Z)` as the tail —
  `…GradedPowerMap.chartSourceLegIso_hom_nested` in
  `StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaChartNested`;
* the same for the **target** identifications. The two legs it is taken along are identified by
  `…GradedPowerMap.pieceTargetLeg_comp_homOfLE`, but the tail is not a chart identification of a
  relative twist as it is for [Stacks, Tag 07ZG]: it is [Stacks, Tag 01CU]'s own comparison of the
  integer tensor powers under pullback, `…ProjChartIntPullbackMul.intPullIso`, composed with the
  identification `…ProjChartRatioPullbackLocalMul.restrictCompIso` of the two readings of
  `ℒ|_{f^{-1}(Z)}`, and the cocycle law for that composite is not proved;
* the **splice**, which is the nested compatibility of [Stacks, Tag 01NK]'s `θ` itself in both of
  its variables — the graded ring `𝒜(V)` shrinking to `𝒜(Z)` and the scheme `f^{-1}(V)` shrinking
  to `f^{-1}(Z)`. Both halves of that are proved at the level of sections over a standard open,
  `…ProjChartGradedThetaSheafRingFunctoriality.pushTheta_comap_app_basicOpen` and
  `…GradedPowerMap.pushTheta_nestedDatum`; what is not proved is the passage from those to an
  identity of **morphisms**, which the sections of an inverse image along a morphism that is not
  an open immersion cannot supply directly. It has to go through the adjoint transpose
  (`…Tag07ZGTwist.transpose_injective`) and then the basis of standard opens of `Proj 𝒜(V)`
  (`…ProjShared.exists_basicOpen_homogeneous_le`), which is the relative counterpart of
  `…ProjChartGradedThetaBuild.nested_localApp_eq` and does not exist. -/
public def IsNestedThetaChart (n : ℤ) : Prop :=
  ∀ (Z V : S.affineOpens) (h : (Z.1 : S.Opens) ≤ (V.1 : S.Opens)),
    (Scheme.Modules.pullbackCongr
          (P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h))).inv.app
        ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj (relativeTwist A n))
      ≫ (Scheme.Modules.pullbackComp
            (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
            (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).inv.app
          ((Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj (relativeTwist A n))
      ≫ (Scheme.Modules.pullback
            (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))).map (P.thetaChart V n)
      ≫ (Scheme.Modules.pullbackComp
            (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
            (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).hom.app
          ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι)
      ≫ (Scheme.Modules.pullbackCongr
            (P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h))).hom.app
          ((tensorPowerModule T P.L n).restrict P.coveringOpen.ι)
      = P.thetaChart Z n

/-- **The chart data agree wherever two pieces of `U(ψ)` see the same open**, granted their nested
compatibility. The arbitrary pair is reduced to the nested one by
`…RelativeProjChartGlue.localApp_eq_of_nested_affineOpens`, and the nested pair is read on
sections by `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_ofPullback_eq`. -/
public theorem localApp_thetaChart_eq (n : ℤ) (hnest : P.IsNestedThetaChart n)
    (V Z : S.affineOpens) (h : (Z.1 : S.Opens) ≤ (V.1 : S.Opens))
    {W₁ : (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).toScheme.Opens}
    {W₂ : (P.toBase ⁻¹ᵁ (Z.1 : S.Opens)).toScheme.Opens}
    {U : P.coveringOpen.toScheme.Opens}
    (h₁ : (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι ''ᵁ W₁ = U)
    (h₂ : (P.toBase ⁻¹ᵁ (Z.1 : S.Opens)).ι ''ᵁ W₂ = U) :
    localApp (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι
        (ofPullback (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι (P.thetaChart V n)) h₁
      = localApp (P.toBase ⁻¹ᵁ (Z.1 : S.Opens)).ι
          (ofPullback (P.toBase ⁻¹ᵁ (Z.1 : S.Opens)).ι (P.thetaChart Z n)) h₂ :=
  localApp_ofPullback_eq (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι
    (P.coveringOpen.toScheme.homOfLE (P.toBase.preimage_mono h))
    (P.coveringOpen.toScheme.homOfLE_ι (P.toBase.preimage_mono h))
    (P.thetaChart V n) (P.thetaChart Z n) (hnest Z V h) h₁ h₂

/-- **The degreewise component of the relative `θ` exists and is unique**, granted the nested
compatibility of the chart data. There is exactly one morphism

`θ_n : r_{ℒ,ψ}^*(𝒪_{Proj_S(𝒜)}(n)) ⟶ ℒ^{⊗ n}|_{U(ψ)}`

whose inverse image along the inclusion of the piece of `U(ψ)` over each affine open of the base
is the chart datum `…GradedPowerMap.thetaChart` there — that is, [Stacks, Tag 01NK]'s `θ` for the
induced datum, read through the two identifications over the piece.

The cover rung is `…RelativeProjChartGlue.existsUnique_hom_of_preimage_nested` and the glueing is
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`; nothing is assumed of
`𝒜`, of `ℒ` or of `ψ` beyond the data of [Stacks, Tag 01O8]. -/
public theorem existsUnique_relTheta (n : ℤ) (hnest : P.IsNestedThetaChart n) :
    ∃! φ : (Scheme.Modules.pullback (P.globalMorphism (relativeProj A))).obj (relativeTwist A n)
        ⟶ (tensorPowerModule T P.L n).restrict P.coveringOpen.ι,
      ∀ V : S.affineOpens,
        (Scheme.Modules.restrictFunctor (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι).map φ
          = ofPullback (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι (P.thetaChart V n) :=
  RelativeProjChartGlue.existsUnique_hom_of_preimage_nested P.toBase
    (fun V : S.affineOpens =>
      ofPullback (P.toBase ⁻¹ᵁ (V.1 : S.Opens)).ι (P.thetaChart V n))
    (fun V Z h _ _ _ h₁ h₂ => P.localApp_thetaChart_eq n hnest V Z h h₁ h₂)

end GradedPowerMap

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
