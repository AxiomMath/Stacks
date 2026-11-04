module

public import StacksFrontier.AlgebraicGeometry.ProjDegreeOneTriv.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjDegreeOne.Chart
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono

/-!
# The degree-one twist on a relative projective spectrum is generated in degree one

Tag 01NR's twist datum of a graded algebra `𝒜` on a scheme `S` carries, in every nonnegative
degree, a map `ψ n : 𝒜_n ⟶ π_*𝒪(n)` on the base. Its transpose under `π^* ⊣ π_*` is a map
`π^*𝒜_n ⟶ 𝒪(n)` on the relative `Proj`. This file proves that in degree one that transpose is
an **epimorphism**, whenever `𝒜` is generated in degree one.

This is the clause `Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Pair.degreeOneSurjective` for
the universal pair, and — at `𝒜 = Sym(ℰ)` — the surjectivity of the tautological map of a
projective bundle that `Stacks.Divisors.BundleSplittingDatum` asks for. The library had both
ends of the argument and no bridge between them.

## The argument

Epimorphy is local (`Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections`), so it is
enough to lift a section near every point. Near a point of the relative `Proj`:

* the point lies in a projective-spectrum chart over an affine open `U` of the base;
* on that chart the graded ring is `Γ(U, 𝒜)`, generated in degree one, so the point lies in the
  standard open of some degree-one element `a₁`
  (`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne`);
* on that standard open `𝒪(1)` is free on the degree-one section attached to `a₁`
  (`Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection`);
* the chart identification of the twist datum carries that section to the restriction of
  `ψ₁(a₁)` — this is the field `ψ_chart`, carried down from the top open of the chart by
  `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.mapSection_res`;
* and `ψ₁(a₁)` is the value of the transpose at the pulled-back section `a₁`, which is the
  triangle identity of the adjunction.

So every section is, locally, a function multiple of something in the image.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.psiTranspose`: the transpose
  `π^*𝒜_n ⟶ 𝒪(n)` of the homogeneous-section map of a twist datum. At `𝒜 = Sym(ℰ)` and the
  canonical twist datum this is `Stacks.ProjectiveBundleSplitting.tautologicalTwistMap`, on the
  nose.
* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.unitSection`: a section pulled back along a
  morphism of schemes, named so that it can be carried around as a short term.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.epi_psiTranspose`: **the transpose is an
  epimorphism in degree one** when the algebra is generated in degree one.
* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.exists_local_lift`: its local content, which
  is the statement a consumer wanting an explicit local preimage should use.
* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.mapSection_degreeOneSection`: the chart
  identification carries the degree-one trivializing section to the restriction of `ψ₁`.
* `Stacks.AlgebraicGeometry.RelativeProjDegreeOne.app_homEquiv_symm`: the transpose evaluated at
  a pulled-back section is the value of `ψ`.

## Implementation notes

**Every lemma is applied with its arguments explicit, and this is not style.** Three of the
steps below leave Lean a unification problem between two spellings of one section of a twist —
`degreeOneSection`, which is a restriction of `degreeSection`, against the restriction written
out — and solving it by unification rather than by supplying the argument exhausts the default
heartbeat budget. The same is true of the unit of the pullback–pushforward adjunction, which is
why `unitSection` exists: `set u := …` on the written-out unit times out while abstracting it
out of the goal, and the named form costs nothing.

**The transport along `ChartData.chart_range` is discharged once.** `ψ_chart` states its
conclusion in the sections over the chart's image, transported along the equality of that image
with `π⁻¹U`; `map_eqRec` says that restricting a transported section is restricting the section,
because the two inclusions prove one proposition. Nothing else in the file meets the equality.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MS](https://stacks.math.columbia.edu/tag/01MS)
* [Stacks Project, Tag 0AYP](https://stacks.math.columbia.edu/tag/0AYP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.ProjTwistSections

namespace Stacks.AlgebraicGeometry.RelativeProjDegreeOne

universe u

/-- Restricting a section transported along an equality of opens is restricting the section
itself: the two inclusions are proofs of one proposition, so the restriction maps agree. -/
public theorem map_eqRec {X : Scheme.{u}} {M : X.Modules} {W₁ W₂ : X.Opens} (e : W₁ = W₂)
    (x : Γ(M, W₂)) {V : X.Opens} (h₁ : V ≤ W₁) (h₂ : V ≤ W₂) :
    M.val.map (homOfLE h₁).op (e ▸ x : Γ(M, W₁)) = M.val.map (homOfLE h₂).op x := by
  subst e
  rfl

/-- **A section pulled back along a morphism of schemes**: the value at it of the unit of
`pullback ⊣ pushforward`, over the inverse image of the open it lives on.

Named so that the degree-one generation argument can carry it around as a short term: written
out, the unit of the adjunction is large enough that `set` spends its whole heartbeat budget
abstracting it out of a goal. -/
public def unitSection {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (x : Γ(M, U)) : Γ((Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U)) x

/-- **The transpose of a morphism into a direct image, read on sections.** Over an open `U` of
the target the transpose of `ψ` sends the value of the unit of `pullback ⊣ pushforward` at a
section to the value of `ψ` at it. This is the triangle identity of the adjunction evaluated at
one section, and it is the only property of the transpose the degree-one generation argument
uses. -/
public theorem app_homEquiv_symm {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (ψ : M ⟶ (Scheme.Modules.pushforward f).obj N) (U : Y.Opens) (x : Γ(M, U)) :
    ((((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N).symm ψ).val.app
        (op (f ⁻¹ᵁ U)))
        (unitSection f M U x) =
      (ψ.val.app (op U)) x :=
  congrArg (fun θ : M ⟶ (Scheme.Modules.pushforward f).obj N => (θ.val.app (op U)) x)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M N).apply_symm_apply ψ)

variable {S : Scheme.{u}} {A : SheafGradedAlgebra.{u} S}

/-- **The transpose of the homogeneous-section map of a twist datum.** -/
public def psiTranspose (D : TwistData A) (n : ℕ) :
    (Scheme.Modules.pullback (relativeProj A).toBase).obj (A.piece (n : ℤ)) ⟶
      D.algebra.piece (n : ℤ) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (relativeProj A).toBase).homEquiv _ _).symm
    (D.ψ n)

/-- **The chart comparison carries the degree-one trivializing section to the restriction of
the homogeneous-section map.** Over an open `V` of the chart contained in the standard open of
the image of a degree-one local section `a₁`, the trivializing section of `𝒪(1)` attached to
that image corresponds, under the chart identification of the twist datum, to the restriction of
`ψ₁(a₁)`.

This is the field `RelativeProjTwists.TwistData.ψ_chart` — which is stated at the top open of
the chart only — carried down to `V` by `mapSection_res`, with the transport along
`ChartData.chart_range` absorbed by `map_eqRec`. -/
public theorem mapSection_degreeOneSection (D : TwistData A) (U : S.Opens) (hU : IsAffineOpen U)
    [IsOpenImmersion ((relativeProj A).chart U hU)]
    (a₁ : A.sectionPieces U 1) (V : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (hV : V ≤ AlgebraicGeometry.Proj.basicOpen (A.grading U)
      (DirectSum.of (A.sectionPieces U) 1 a₁ : A.sectionRing U))
    (h₂ : (relativeProj A).chart U hU ''ᵁ V ≤ (relativeProj A).toBase ⁻¹ᵁ U) :
    D.chartData.mapSection U hU ((1 : ℕ) : ℤ) V
        (Stacks.AlgebraicGeometry.ProjDegreeOneTriv.degreeOneSection (A.grading U)
          (A.of_mem_grading U a₁) hV) =
      (D.algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE h₂).op
        ((D.ψ 1).val.app (op U) a₁) := by
  refine Eq.trans ?_ (map_eqRec (D.chartData.chart_range U hU)
    ((D.ψ 1).val.app (op U) a₁)
    (Scheme.Hom.image_mono ((relativeProj A).chart U hU) (le_top : V ≤ ⊤)) h₂)
  refine Eq.trans ?_ (congrArg
    (fun w => (D.algebra.piece ((1 : ℕ) : ℤ)).val.map
      (homOfLE (Scheme.Hom.image_mono ((relativeProj A).chart U hU) (le_top : V ≤ ⊤))).op w)
    (D.ψ_chart U hU 1 a₁))
  exact (mapSection_res D.chartData U hU ((1 : ℕ) : ℤ) (le_top : V ≤ ⊤)
    (degreeSection (A.grading U) 1
      ⟨DirectSum.of (A.sectionPieces U) 1 a₁, A.of_mem_grading U a₁⟩)).symm

/-- A morphism of sheaves of modules on a scheme commutes with restriction followed by the
action of a function on the smaller open. -/
public theorem app_smul_map {X : Scheme.{u}} {P M : X.Modules} (φ : P ⟶ M)
    {V₁ V₂ : X.Opens} (h : V₂ ≤ V₁) (u : Γ(P, V₁)) (ρ : Γ(X, V₂)) :
    (φ.val.app (op V₂)) ((P.smul ρ).hom ((P.val.map (homOfLE h).op) u)) =
      (M.smul ρ).hom ((M.val.map (homOfLE h).op) ((φ.val.app (op V₁)) u)) :=
  ((φ.val.app (op V₂)).hom.map_smul ρ _).trans
    (congrArg (fun w => (M.smul ρ).hom w)
      (PresheafOfModules.naturality_apply φ.val (homOfLE h).op u))

/-- **Every section of the degree-one twist is, near every point, in the image of the transpose
of the homogeneous-section map.** This is the local form of degree-one generation on a relative
projective spectrum, and it is the whole content of `epi_psiTranspose`.

The open produced is the image of `D₊(a₁) ⊓ chart⁻¹ W` in a projective-spectrum chart over an
affine open of the base, for a degree-one local section `a₁` whose image is nonzero at the
point; such an `a₁` exists because the algebra is generated in degree one. -/
public theorem exists_local_lift (D : TwistData A)
    (hgen : Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne A)
    (W : (relativeProj A).scheme.Opens) (t : Γ(D.algebra.piece ((1 : ℕ) : ℤ), W))
    (y : (relativeProj A).scheme) (hy : y ∈ W) :
    ∃ (V : (relativeProj A).scheme.Opens) (hVW : V ≤ W) (_ : y ∈ V)
      (s : Γ((Scheme.Modules.pullback (relativeProj A).toBase).obj (A.piece ((1 : ℕ) : ℤ)), V)),
      (psiTranspose D 1).val.app (op V) s =
        (D.algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE hVW).op t := by
  obtain ⟨U, hU, hpU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
      (X := S) (x := (relativeProj A).toBase.base y) (U := ⊤) trivial
  let := D.chartData.chart_isOpenImmersion U hU
  have hyU : y ∈ (relativeProj A).toBase ⁻¹ᵁ U := hpU
  rw [← D.chartData.chart_range U hU] at hyU
  obtain ⟨z, -, hz⟩ := hyU
  obtain ⟨g, hgz⟩ := Stacks.AlgebraicGeometry.ProjDegreeOneTriv.exists_mem_basicOpen_degreeOne
    (A.grading U) (hgen U hU) z
  obtain ⟨a₁, ha₁⟩ := (A.mem_grading_iff U (g : A.sectionRing U)).mp g.2
  have hgeq : g = ⟨DirectSum.of (A.sectionPieces U) 1 a₁, A.of_mem_grading U a₁⟩ :=
    Subtype.ext ha₁.symm
  subst hgeq
  set V' : (AlgebraicGeometry.Proj (A.grading U)).Opens :=
    ((relativeProj A).chart U hU ⁻¹ᵁ W) ⊓
      AlgebraicGeometry.Proj.basicOpen (A.grading U)
        (DirectSum.of (A.sectionPieces U) 1 a₁ : A.sectionRing U) with hV'
  have hzV' : z ∈ V' := ⟨show ((relativeProj A).chart U hU).base z ∈ W from hz ▸ hy, hgz⟩
  have hle : (relativeProj A).chart U hU ''ᵁ V' ≤ W := by
    rintro _ ⟨w, hw, rfl⟩; exact hw.1
  have h₂ : (relativeProj A).chart U hU ''ᵁ V' ≤ (relativeProj A).toBase ⁻¹ᵁ U := by
    rw [← D.chartData.chart_range U hU]
    exact Scheme.Hom.image_mono _ le_top
  refine ⟨(relativeProj A).chart U hU ''ᵁ V', hle, ⟨z, hzV', hz⟩, ?_⟩
  obtain ⟨b, hb⟩ := mapSection_surjective D.chartData U hU ((1 : ℕ) : ℤ) V'
    ((D.algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE hle).op t)
  obtain ⟨r, hr⟩ := (Stacks.AlgebraicGeometry.ProjDegreeOneTriv.bijective_smul_degreeOneSection
    (A.grading U) (A.of_mem_grading U a₁) (W := V') (fun _ hx => hx.2)).2 b
  have key := mapSection_degreeOneSection D U hU a₁ V' (fun _ hx => hx.2) h₂
  refine ⟨(((Scheme.Modules.pullback (relativeProj A).toBase).obj
        (A.piece ((1 : ℕ) : ℤ))).smul ((((relativeProj A).chart U hU).appIso V').inv r)).hom
      (((Scheme.Modules.pullback (relativeProj A).toBase).obj
          (A.piece ((1 : ℕ) : ℤ))).val.map (homOfLE h₂).op
        (unitSection (relativeProj A).toBase (A.piece ((1 : ℕ) : ℤ)) U a₁)), ?_⟩
  refine ((app_smul_map (psiTranspose D 1) h₂
    (unitSection (relativeProj A).toBase (A.piece ((1 : ℕ) : ℤ)) U a₁)
    ((((relativeProj A).chart U hU).appIso V').inv r)).trans ?_).trans hb
  refine Eq.trans ?_ (congrArg (D.chartData.mapSection U hU ((1 : ℕ) : ℤ) V') hr)
  refine Eq.trans ?_ (mapSection_smul D.chartData U hU ((1 : ℕ) : ℤ) V' r
    (Stacks.AlgebraicGeometry.ProjDegreeOneTriv.degreeOneSection (A.grading U)
      (A.of_mem_grading U a₁) (W := V') (fun _ hx => hx.2))).symm
  exact congrArg (fun w => ((show (relativeProj A).scheme.Modules from
        D.algebra.piece ((1 : ℕ) : ℤ)).smul
      ((((relativeProj A).chart U hU).appIso V').inv r)).hom w)
    ((congrArg (fun w => (D.algebra.piece ((1 : ℕ) : ℤ)).val.map (homOfLE h₂).op w)
      (app_homEquiv_symm (relativeProj A).toBase (D.ψ 1) U a₁)).trans key.symm)

/-- **The degree-one twist on a relative projective spectrum is generated by the degree-one
sections of the base algebra**, whenever that algebra is generated in degree one: the transpose
of the degree-one homogeneous-section map of any twist datum is an epimorphism. -/
public theorem epi_psiTranspose (D : TwistData A)
    (hgen : Stacks.AlgebraicGeometry.ProjRepresentsF1.IsGeneratedInDegreeOne A) :
    Epi (psiTranspose D 1) :=
  Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections (psiTranspose D 1)
    (exists_local_lift D hgen)

end Stacks.AlgebraicGeometry.RelativeProjDegreeOne

end
