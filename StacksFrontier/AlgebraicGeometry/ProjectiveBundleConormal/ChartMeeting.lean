module

public import StacksFrontier.AlgebraicGeometry.PartTwo.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartReduction
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.PullbackSourceSection

/-!
# The two halves of Tag 0B3V clause 3 meet on the tautological chart

The chart computation of [Stacks, Tag 0B3V] clause 3 has a source half
(`Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde_inv_unit_toOpen`, applied through
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_unit`)
and a target half (`restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`).
**They cannot meet over `π⁻¹W`** — the source half produces a section of `ℐ(σ)` only over an open
on which `𝒪(-1)` is trivial, and `𝒪(-1)` has no nonzero section over `π⁻¹W` — so the target half
has to be taken over `Stacks.ProjectiveBundleConormal.tautologicalChart`, which is not the open
`Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTilde` is built from.

This file supplies the target identification *at the tautological chart*, the reduction of the
clause to an equation against it, the bridge between the two spellings of a conormal generator,
and the transport data that the target generator formula asks for at that chart.

## Main definitions

* `Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTildeTaut`: **the target of the
  clause's map, restricted to a chart, taken over the tautological chart.** It has the same type
  as `Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTilde`, the tautological chart
  having the same preimage `W` under `σ`
  (`Stacks.ProjectiveBundleConormal.preimage_tautologicalChart`).
* `Stacks.ProjectiveBundleConormal.chartIdealSection`: **the section `x` of the ideal sheaf of the
  affine chart named by a section `y` of `ℐ(σ)` over the tautological chart** — the argument `x`
  of `Stacks.Conormal.restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap` at
  `V := tautologicalChart E W t`, written out.

## Main results

* `Stacks.Conormal.conormalSheafIsoPullbackSelf_inv_pullbackSection`: **the bridge between the two
  spellings of a conormal generator.** The section of `𝒞_i` that
  `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` names by the pullback of a section `y` of
  `ℐ_i` is the restriction of the conormal generator of [Stacks, Tag 01R3] at `y`.
* `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq_taut`: **the clause
  follows from one equation on a chart, against the tautological-chart target.** This is
  `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq'` with
  `restrictConormalTargetIsoTilde` replaced by the identification that *can* be fed.
* `Stacks.ProjectiveBundleConormal.isoSpec_comp_zeroSection_comp_tautologicalChartLift_eq` and
  `Stacks.ProjectiveBundleConormal.chartIdealSection_eq`: the arguments `L`, `hL` and `hxy` of
  that generator formula at the tautological chart.
* `Stacks.ProjectiveBundleConormal.chartIdealSection_app_ι`: **the image of
  `chartIdealSection` in the structure sheaf**, assembled from the `_comp_ι` pin of each of its
  factors. This is the side of `hxκ` the source half contributes.
* `Stacks.ProjectiveBundleConormal.val_app_ι_image_top_of_val_app`: **the match between the two
  readings of a chart**, `W` and `W.ι ''ᵁ ⊤`, at which the source generator formula and the
  source half of the clause are respectively stated.

## Implementation notes

Nothing is rewritten: see the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatio` for why no `rw` occurs on
this layer.

`AlgebraicGeometry.morphismRestrict` of `σ` along the tautological chart has `σ ⁻¹ᵁ` of that chart
for its source, an open only *equal* to `W`, so the morphism `L` of the generator formula is
`AlgebraicGeometry.Scheme.isoOfEq` followed by `σ ∣_` the chart rather than `σ ∣_` the chart
itself; that is the reason the formula being fed carries `L` as a variable at all.

## What is not done here, and how clause (b) is closed

**No `@[stacks 0B3V]` attribute is attached in this file.** Clause (b) **is** discharged, in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartAssembly`: the hypothesis `h` of
`Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq_taut` is
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_restrict_eq_taut` there, and the clause
itself is `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap`, which carries the tag. The
rest of this section records the inputs that assembly consumes.

Three of them are statements of `ChartAssembly`: the normalisation of
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections` on a section
(`specModuleIsoSections_hom_apply`), without which the section of `ker(q)` that the source
generator formula produces at `k` cannot be recognised and the chart coordinate cannot be `k`; its
consequence `Stacks.ProjectiveBundleConormal.map_ι_image_top_specModuleChartKerIso_inv`; and the
hypothesis `hy'` of the target generator formula
(`Stacks.ProjectiveBundleConormal.idealSheafIsoOfIsoSource_inv_restrictIdealSheafIso'_app_ι`).

Two things stand between that hypothesis and a proof: the
ratio identity across `Stacks.ProjectiveBundleConormal.chartMap`, and the fact that the section
`w₀` the source half returns is not pinned.

**The second of those is closed by the pinned existential.**
`exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned` returns `w₀` together with
the value `1` of its pairing against the degree-one section of the frame, which — with
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_smul_left_eq_mul` — makes the image of `y` in
`𝒪_{𝐏(ℰ)}` the *ratio itself* rather than the ratio times an unknown unit. Getting there needs
the pairing to be evaluated on a named pair; that evaluation is
`Stacks.ProjectiveBundleConormal.sectionMulNegOne_eq_negOneMulIso`, and the two crossings it rests
on (`tensorObjIso_eq_tensorIso`, `sheafifyUnitIso_eq_unitIso`) are each `CategoryTheory.Iso.ext`
followed by `rfl` — **the `Iso` structures are not definitionally equal and neither are their
`inv` fields, but their `hom` fields are**, which is the whole of the comparison between
the monoidal tensor product of sheaves of modules and the tensor product sheaf of
[Stacks, Tag 01CA] on this layer.

**The four inputs between `h` and a proof**, listed in the order a proof meets them.

1. **The ratio identity across `chartMap`.** It is
   `Stacks.ProjectiveBundleConormal.appLE_chartMap_eq_awayToSection_of_res_eq_smul`, carried on
   into `Sym_{Γ(X,W)}(ker p)` by
   `Stacks.ProjectiveBundleConormal.exists_appLE_splitChartMap_comp_chartMap_eq_ι`, both in
   `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartRatioSplit`. The general form is
   stated at an *opaque* morphism into `Proj` with the open as a variable, which keeps the
   chart layer out of the statement and makes the transport a cheap application.
2. **`hpair`.** The pinned statement asks that `q s` and
   `w` pair to `1` downstairs. For general chart data, with the frame `eL` and the
   trivialisation `τ` of `𝓛|_W` unrelated, the pairing is only a unit, so the cover
   `Stacks.ProjectiveBundleConormal.exists_affine_open_chartData` is strengthened to produce the
   trivialisation that the frame induces: it returns `τ`
   together with the equation `τ = Stacks.ProjectiveBundleConormal.chartTrivialisation …`, the
   trivialisation `Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop` builds out of the
   spanning section `q s`, and the two reductions below carry that equation into their hypotheses,
   so a chart computation may assume it.

   **Strengthening the cover is necessary but not sufficient**: two section formulas are
   additionally needed. **Both are proved**, in
   `StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTrivialisationPairing`, and so is
   `hpair` itself
   (`Stacks.ProjectiveBundleConormal.tensorPairing_chartTrivialisation_eq_unitSection`).
   * the value of the trivialisation on the unit section,
     `(restrictIsoUnitOfSpanEqTop L U hU t ht).inv (1) = t` up to
     `AlgebraicGeometry.Scheme.Opens.ι_image_top`, is
     `Stacks.ProjectiveBundleConormal.restrictIsoUnitOfSpanEqTop_inv_val_app_one`. **The chain is
     definitional on
     sections apart from two steps.** `Stacks.AlgebraicGeometry.TwistMapsInvertible`
     `.restrictIsoUnitOfOverIsoUnit` on a section is a `rfl`,
     `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` is the *identity* on sections in both
     directions (`rfl`), `AlgebraicGeometry.Scheme.Modules.overEquiv` re-indexes the
     open (`rfl`), and `Stacks.SheafOfModules.isoUnitOver` is `c ↦ c · a` (`rfl`,
     `Stacks.SheafOfModules.isoUnitOver_inv_val_app`). The only two non-`rfl` steps are
     `one_smul` and the unit comparison,
     `Stacks.AlgebraicGeometry.IdealPowerHomColimit.restrictUnitIso_inv_val_app_one`. One point
     has to be worked around: the generation hypothesis of `isoUnitOver` cannot be named
     in the scheme spelling — `HSMul` fails to synthesise — so it is bound existentially with
     proof `⟨_, rfl⟩`.
   * that the trivialisation of the inverse twist a trivialisation of `𝓛` induces is its
     pairing inverse, `pairing(τ⁻¹ 1, (restrictInverseTwistIso Q.L W τ)⁻¹ 1) = 1`, is
     `Stacks.ProjectiveBundleConormal.sectionMulNegOne_restrictInverseTwistIso_inv_one`: the
     five-fold composite read on a product section, four of whose factors already have their
     formula and whose fifth is the left unitor
     (`Stacks.ProjectiveBundleConormal.leftUnitor_inv_tensorSectionsAt`). The crossing from
     `Stacks.SheafOfModules.Invertible.sectionMulNegOne` to
     `Stacks.SheafOfModules.tensorPairing` against
     `Stacks.ProjBundleInverseBaseChange.negOneMulPairingIso'` is
     `Stacks.ProjectiveBundleConormal.tensorPairing_negOneMulPairingIso'`, and it needs
     `Stacks.SheafOfModules.tensorPairing` read at an **opaque** trivialisation: with the
     composite written out the same `rfl` is a deterministic timeout at `whnf`.

   So `hpair` is `1` on the nose for the chart data the cover returns.
3. **The image of `Stacks.ProjectiveBundleConormal.chartIdealSection` in `𝒪`.**
   It is `Stacks.ProjectiveBundleConormal.chartIdealSection_app_ι`: the image of `y` in
   `𝒪_{𝐏(ℰ)}`, restricted to the self-preimage of the chart, read on the chart as an open
   subscheme and pulled back along
   `Stacks.ProjectiveBundleConormal.tautologicalChartLift`. Every factor contributes exactly its
   `_comp_ι` pin, as the docstring of `chartIdealSection` describes.
4. **The assembly mismatch on opens.**
   `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_unit_toOpen` reduces `h` to one equation per
   generator `k`, whose two sides are
   `Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde_inv_unit_toOpen` followed by
   the source half and `restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`;
   the source generator formula produces its product section over `W.ι ''ᵁ ⊤` and the source half
   consumes one over `W`, and
   `Stacks.ProjectiveBundleConormal.val_app_ι_image_top_of_val_app` matches the two along
   `AlgebraicGeometry.Scheme.Opens.ι_image_top`. What is left at that point is the commutation of
   `Stacks.SheafOfModules.tensorSectionsAt` with the one restriction map, which is
   `Stacks.AlgebraicGeometry.GradedAlgebraTwist.tensorSectionsAt_naturality`.

**The coordinate computation `hxκ`.** The target generator formula
`Stacks.ProjectiveBundleConormal.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`
asks which element `κ` of the augmentation ideal of `Sym_A(ker p)` the section `y` of `ℐ(σ)`
produced by the source half cuts out on the chart. Its three ingredients are all
available. The image of `y` in `𝒪_{𝐏(ℰ)}` is
`Stacks.SheafOfModules.Invertible.sectionMulNegOne` of `v(π^*κ)` with `w₀`
(`exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_unit`),
and on the target side
`Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso_hom_comp_idealSheafι` normalises
`Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso` against the inclusion of the ideal
sheaf into the structure sheaf, so the element of the augmentation ideal that cuts out a given
section of the ideal sheaf of the zero section *can* be read off. The middle step — the ratio of
that image against the degree-one section of the frame, transported across
`Stacks.ProjectiveBundleConormal.chartMap` — is
`Stacks.ProjectiveBundleConormal.exists_appLE_splitChartMap_comp_chartMap_eq_ι`.

**So `hxκ` is an assembly with no missing input**: every lemma it needs exists and is
reachable, `hpair` through
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartTrivialisationPairing`. In the order
a proof meets them:

* `Stacks.Conormal.Locality.idealSheaf_section_injective` reduces the equation between sections of
  the ideal sheaf of `hW.isoSpec.hom ≫ zeroSection …` to an equation in
  `Γ(𝒪_{Spec Sym_A(ker p)}, ⊤)`.
* the source side of that equation is
  `Stacks.ProjectiveBundleConormal.chartIdealSection_app_ι` preceded by
  `Stacks.AlgebraicGeometry.ConormalSourceTransport.idealSheafIsoOfIsoSource_hom_comp_ι`, which
  moves the source transport past the inclusion;
  `Stacks.ProjectiveBundleConormal.tautologicalChartLift_comp_ι` is what turns the resulting
  `(tautologicalChartLift)^♯` into `(splitChartMap ≫ chartMap)^♯`, the spelling the ratio lemma is
  stated at.
* the image of `y` itself is the second conjunct of
  `exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_unit`, turned into the ratio by
  `Stacks.ProjectiveBundleConormal.kernelTautologicalMap_res_unitSection`,
  `sectionMulNegOne_smul_left_eq_mul` and the pairing value `1` that
  `exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned` now returns — whose
  hypothesis `hpair` is
  `Stacks.ProjectiveBundleConormal.tensorPairing_chartTrivialisation_eq_unitSection`.
* the target side is `zeroSectionIdealSheafIso_hom_comp_idealSheafι` read on
  `AlgebraicGeometry.tilde.toOpen (augIdealModule …) ⊤ κ`; `AlgebraicGeometry.tilde.tildeSelf` is
  `Iso.refl` and `AlgebraicGeometry.tilde.toOpen_map_app` carries the inclusion of the
  augmentation ideal through, so that side is
  `AlgebraicGeometry.tilde.toOpen (ModuleCat.of _ _) ⊤ (κ : Sym_A(ker p))`. The ratio lemma
  states its value as `(AlgebraicGeometry.Scheme.ΓSpecIso …).inv`, and the identification of that
  with `AlgebraicGeometry.StructureSheaf.toOpen … ⊤` is a `rfl` — `AlgebraicGeometry.Scheme`
  `.ΓSpecIso_inv` and `AlgebraicGeometry.toOpen_eq` both hold by `rfl`, as the implementation notes
  of `StacksFrontier.RingTheory.LocalCohomology.HigherDegree.OrderedCechModuleComparison` record.
  The module-level `AlgebraicGeometry.tilde.toOpen` at `M = R` agrees with
  `(AlgebraicGeometry.Scheme.ΓSpecIso R).inv` **by `rfl`**, so the two sides of the
  equation already speak one vocabulary and no bridge is owed.

A second point concerns `w₀`.
`Stacks.ProjectiveBundleConormal.exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app`
hands back `w₀` and `hw` but does not pin `w₀`: it determines `σ^*w₀`, hence `w₀` only modulo `I`,
so with that `w₀` the element `κ` has to be *derived* from `y` rather than chosen — in particular
`hxκ` is not true with `κ` taken to be `ι k`.
`exists_pullbackSection_inverseTwistBaseChangeIso_inv_val_app_pinned` is that existential
strengthened to hand back the pairing of `w₀` against the degree-one section of the frame, and the
value is `1`; with it the image of `y` in `𝒪_{𝐏(ℰ)}` is the ratio on the nose, so `κ := ι k` is
the right choice once the ratio is computed.

**The target generator formula *can* be read at `α := hW.isoSpec`.** The coercion
`Spec Γ(X, W) ≡ Spec (CommRingCat.of ↥Γ(X, W))` is no obstruction to feeding
`Stacks.ProjectiveBundleConormal.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`
with `A := ↥Γ(X, W)` and `α := hW.isoSpec`. **Applying** the formula at that `α`,
with every remaining argument left as a binder so that the kernel checks the whole remaining
telescope — hypotheses and conclusion — with `α := hW.isoSpec` substituted, checks in under a
second; so does the same application made through a wrapper declared at
`↑W ≅ Spec (CommRingCat.of ↥Γ(X, W))`. The coercion is therefore not the obstruction, and no such
wrapper is needed.

What does end in a `(kernel) deterministic timeout` is *restating* the formula at that `α`:
the kernel then has to compare the restatement against the instantiated original, and it is that
defeq comparison, not the coercion, which exceeds the budget. It is the same mechanism recorded in
the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineZeroSection`, where each leg of an
isomorphism and the type of their composite are separately cheap and only the comparison of that
composite against a proof term's type is not. **A consumer should apply this formula and use its
conclusion, never restate it.**

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.Conormal

/-- **The bridge between the two spellings of a conormal generator.** For an immersion
`i : Z ⟶ Y`, an open `O` of `Y` and a section `y` of `ℐ_i` over `O`, the section of `𝒞_i` over an
open `U ≤ i ⁻¹ᵁ O` that `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` names by
`AlgebraicGeometry.Scheme.Modules.pullbackSection` of `y` is the restriction to `U` of the
conormal generator of [Stacks, Tag 01R3] at `y`,
`Stacks.Immersion.canonicalConormalQuotientMap`.

The source half of [Stacks, Tag 0B3V] clause 3 produces its value in the first spelling
(`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_val_app_tensorSectionsAt`) and the target
half consumes it in the second
(`Stacks.Conormal.restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap`), so this is
what lets them be compared at all.

`Stacks.Immersion.conormalSheafIsoPullbackSelf_hom_canonicalConormalQuotientMap` is the same
statement over `i ⁻¹ᵁ O` and in the forward direction; turning it around is
`CategoryTheory.Iso.hom_inv_id` read on a section, and moving the restriction map past the
comparison is naturality. The inclusion of opens is a variable because morphisms of
`TopologicalSpace.Opens` are unique. -/
theorem conormalSheafIsoPullbackSelf_inv_pullbackSection {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsImmersion i] (O : Y.Opens) (U : Z.Opens) (hU : U ≤ i ⁻¹ᵁ O) (ν : U ⟶ i ⁻¹ᵁ O)
    (y : (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom).val.obj (op O)) :
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv.val.app (op U)
        (Scheme.Modules.pullbackSection i
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom) O U hU y) =
      (Stacks.Conormal.conormalSheaf i).val.map ν.op
        ((Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op O) y) := by
  have hgen : (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv.val.app
        (op (i ⁻¹ᵁ O))
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).val.app (op O) y) =
      (Stacks.Immersion.canonicalConormalQuotientMap i).val.app (op O) y :=
    (congrArg (fun z : ((Scheme.Modules.pullback i).obj
          (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).val.obj (op (i ⁻¹ᵁ O)) =>
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv.val.app (op (i ⁻¹ᵁ O)) z)
      (Stacks.Immersion.conormalSheafIsoPullbackSelf_hom_canonicalConormalQuotientMap
        i O y).symm).trans
      (Stacks.SheafOfModules.inv_val_app_hom_val_app
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i) (op (i ⁻¹ᵁ O)) _)
  refine Eq.trans (congrArg (fun z : ((Scheme.Modules.pullback i).obj
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).val.obj (op U) =>
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv.val.app (op U) z)
    (PresheafOfModules.congr_map_apply
      (M := ((Scheme.Modules.pullback i).obj
        (Stacks.ClosedImmersion.idealSheaf i.toLRSHom.toShHom)).val)
      (f := (homOfLE hU).op) (g := ν.op) (Subsingleton.elim _ _) _)) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply
    (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv.val ν.op _) ?_
  exact congrArg (fun z : (Stacks.Conormal.conormalSheaf i).val.obj (op (i ⁻¹ᵁ O)) =>
    (Stacks.Conormal.conormalSheaf i).val.map ν.op z) hgen

end Stacks.Conormal

namespace Stacks.ProjectiveBundleConormal

attribute [local instance] monoidalSheafTensor

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]
  (Q : Stacks.Divisors.InvertibleQuotient X E)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  [IsImmersion σ]

include hσ e hqe in
/-- **The target of the conormal map of [Stacks, Tag 0B3V] clause 3, restricted to a chart, taken
over the tautological chart.** Over an affine open `W` carrying a frame for `𝓛` and a section `t`
of `ℰ` at which the chart's linear form takes the value `1`, the conormal sheaf of `σ` restricted
to `W` is the pullback along `W ≅ Spec Γ(X, W)` of `(ker p)^~`.

This is `Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTilde` with the ambient open
`π⁻¹W` replaced by `Stacks.ProjectiveBundleConormal.tautologicalChart E W t`, whose preimage
under `σ` is also `W` (`Stacks.ProjectiveBundleConormal.preimage_tautologicalChart`), so that the
two have the same type. **The replacement is what makes clause 3's chart computation possible at
all**: the generator formula
`Stacks.ProjectiveBundleConormal.restrictConormalIsoOfOpenFactor_trans_zeroSection_hom_unit_toOpen`
names its conormal generator by a section of `ℐ(σ)` over the ambient open, and the source half
produces one only over a chart trivialising `𝒪(-1)` — of which `π⁻¹W` is not one.

The factorization is
`Stacks.ProjectiveBundleConormal.isoSpec_comp_zeroSection_comp_tautologicalChartLift_comp_ι` and
the open immersion is `Stacks.ProjectiveBundleConormal.tautologicalChartLift`. -/
def restrictConormalTargetIsoTildeTaut {W : X.Opens} (hW : IsAffineOpen W)
    (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W)) (t : Γ(E, W))
    (ht : chartLinearForm Q W eL t = 1) :
    (Scheme.Modules.restrictFunctor W.ι).obj (Stacks.Conormal.conormalSheaf σ) ≅
      (Scheme.Modules.pullback hW.isoSpec.hom).obj (tilde (chartKerModule Q W eL)) :=
  Stacks.Conormal.restrictConormalIsoOfOpenFactor σ (tautologicalChart E W t)
      (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm hW.isoSpec
      (zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))
      (tautologicalChartLift E Q hW eL t ht)
      (isoSpec_comp_zeroSection_comp_tautologicalChartLift_comp_ι E Q hσ e hqe hW eL t ht) ≪≫
    (Scheme.Modules.pullback hW.isoSpec.hom).mapIso
      ((Stacks.CartierConormal.conormalSheafIsoPullbackSelf
            (zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))).symm ≪≫
        conormalZeroSectionIso Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL)))

include hσ e hqe in
/-- **The isomorphism assertion of [Stacks, Tag 0B3V] clause 3 follows from one equation on a
chart, stated against the tautological-chart target identification.**

This is `Stacks.ProjectiveBundleConormal.isIso_conormalCanonicalMap_of_restrict_eq'` with
`Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTilde` replaced by
`Stacks.ProjectiveBundleConormal.restrictConormalTargetIsoTildeTaut`. Both are isomorphisms
between the same two objects, so the right-hand side is invertible either way and the content of
the hypothesis is entirely that it *is* the clause's map; the point of the replacement is that the
tautological-chart identification has a generator formula a consumer can feed, and the `π⁻¹W` one
does not. See the "What is not done" of
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.ChartConormalTarget`. -/
theorem isIso_conormalCanonicalMap_of_restrict_eq_taut
    (h : ∀ (W : X.Opens) (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
      (t : Γ(E, W)) (ht : chartLinearForm Q W eL t = 1)
      (τ : (Scheme.Modules.restrictFunctor W.ι).obj Q.L ≅ 𝟙_ (↑W : Scheme.{u}).Modules),
      τ = chartTrivialisation Q hW eL t ht →
      (restrictConormalSourceIsoTilde Q W eL hW τ).inv ≫
          (Scheme.Modules.restrictFunctor W.ι).map (conormalCanonicalMap E Q hσ e hqe) =
        (restrictConormalTargetIsoTildeTaut E Q hσ e hqe hW eL t ht).inv) :
    IsIso (conormalCanonicalMap E Q hσ e hqe) := by
  refine isIso_conormalCanonicalMap_of_forall_exists_isIso_restrict E Q hσ e hqe fun x => ?_
  obtain ⟨W, hxW, hW, eL, t, ht, τ, hτ⟩ := exists_affine_open_chartData Q x
  refine ⟨W, hxW, Eq.mp (congrArg (fun φ => IsIso φ)
    ((Iso.inv_comp_eq (restrictConormalSourceIsoTilde Q W eL hW τ)).mp
      (h W hW eL t ht τ hτ)).symm) inferInstance⟩

/-! ### Matching the two readings of a chart along `ι_image_top` -/

/-- **A morphism of modules read over `W.ι ''ᵁ ⊤` from its reading over `W`.** The two opens are
equal (`AlgebraicGeometry.Scheme.Opens.ι_image_top`) but not the same term, and the two halves of
clause 3's chart computation are stated at different ones of them: the source generator formula
`Stacks.ProjectiveBundleConormal.restrictConormalSourceIsoTilde_inv_unit_toOpen` produces its
product section over `W.ι ''ᵁ ⊤`, because that is what the sections of a restricted module over
`⊤` are, while the source half
`Stacks.ProjectiveBundleConormal.exists_conormalCanonicalMap_val_app_tensorSectionsAt_chart_unit`
consumes a section over `W`. **This is the match.** Given the value of `φ` at the restriction of
`x` to `W`, it returns the value of `φ` at `x` itself.

It is naturality of `φ` along the inclusion `W.ι ''ᵁ ⊤ ⟶ W` together with the fact that the two
restrictions between the two opens undo one another — `Stacks.Tag08S2Locality.map_map` and
`Stacks.Tag08S2Locality.map_self`, homs of a poset agreeing by proof irrelevance. The value over
`W` is a variable `y` named by `h` rather than the term itself, so that a consumer instantiates it
from the formula it holds instead of unfolding; this is the same discipline as
`Stacks.ProjectiveBundleConormal.surjective_smul_restrictIsoUnit`.

`Stacks.ProjectiveBundleConormal.val_map_ι_image_top_injective` is the companion statement for an
equation already read at `W`; this one is what turns a formula at `W` into a formula at
`W.ι ''ᵁ ⊤`, which is the direction
`Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_unit_toOpen` needs, its generators living over
`⊤`. -/
theorem val_app_ι_image_top_of_val_app {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens)
    (x : Γ(M, W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens))) (y : Γ(N, W))
    (h : φ.val.app (op W) (M.val.map (homOfLE W.ι_image_top.ge).op x) = y) :
    φ.val.app (op (W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens))) x =
      N.val.map (homOfLE W.ι_image_top.le).op y := by
  refine Eq.trans ?_ (congrArg
    (fun z : Γ(N, W) => N.val.map (homOfLE W.ι_image_top.le).op z) h)
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply φ.val
    (homOfLE W.ι_image_top.le).op _)
  refine congrArg (fun z : Γ(M, W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens)) =>
    φ.val.app (op (W.ι ''ᵁ (⊤ : (↑W : Scheme.{u}).Opens))) z) ?_
  exact ((Stacks.Tag08S2Locality.map_map M (homOfLE W.ι_image_top.le)
      (homOfLE W.ι_image_top.ge) x).trans
    (Stacks.Tag08S2Locality.map_self M _ x)).symm

/-! ### The target generator formula at the tautological chart -/

section TautTarget

/-- Equal morphisms of sheaves of modules agree on every section. -/
private theorem val_app_congr_hom {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} {φ ψ : M ⟶ N} (h : φ = ψ) (U : Cᵒᵖ)
    (x : M.val.obj U) : φ.val.app U x = ψ.val.app U x :=
  congrArg (fun k : M ⟶ N => k.val.app U x) h

open SymmetricAlgebra

variable {W : X.Opens} (hW : IsAffineOpen W) (eL : Γ(Q.L, W) ≃ₗ[Γ(X, W)] Γ(X, W))
  (t : Γ(E, W)) (ht : chartLinearForm Q W eL t = 1)

omit [IsImmersion σ] in
include hσ e hqe in
/-- **The affine chart of the frame, composed into the tautological chart, is `σ` restricted** —
up to the identification of `W` with `σ ⁻¹ᵁ` of the tautological chart.

This is the hypothesis `hL` of
`Stacks.Conormal.restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap` at
`V := tautologicalChart E W t`. The transport `AlgebraicGeometry.Scheme.isoOfEq` is unavoidable:
`AlgebraicGeometry.morphismRestrict` of `σ` along the chart has `σ ⁻¹ᵁ` of the chart for its
source, and that open is only *equal* to `W`, which is why the statement being fed carries `L` as
a variable. It is `CategoryTheory.cancel_mono` of the inclusion of the chart and nothing else. -/
theorem isoSpec_comp_zeroSection_comp_tautologicalChartLift_eq :
    (hW.isoSpec.hom ≫ zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL))) ≫
        tautologicalChartLift E Q hW eL t ht =
      (Scheme.isoOfEq X
            (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm).hom ≫
        σ ∣_ tautologicalChart E W t := by
  refine (cancel_mono (tautologicalChart E W t).ι).mp ?_
  refine Eq.trans ((Category.assoc _ _ _).trans
    (isoSpec_comp_zeroSection_comp_tautologicalChartLift_comp_ι E Q hσ e hqe hW eL t ht)) ?_
  refine Eq.trans (congrArg (fun m => m ≫ σ)
    (Scheme.isoOfEq_hom_ι X
      (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm).symm) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact (congrArg (fun m => (Scheme.isoOfEq X
      (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm).hom ≫ m)
    (morphismRestrict_ι σ (tautologicalChart E W t))).symm

include hσ e hqe in
/-- **The section of the ideal sheaf of the affine chart named by a section of `ℐ(σ)` over the
tautological chart.** This is the section `x` that
`Stacks.Conormal.restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap` produces at
`V := tautologicalChart E W t`, written out: restrict `y` to the self-preimage of the chart,
transport it along `Stacks.Conormal.Restriction.restrictIdealSheafIso'` and the source transport
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource`, cancel the open
immersion of the chart off the target with
`Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq`, and normalise the resulting open to
`⊤` by `Stacks.ProjectiveBundleConormal.top_eq_preimage_tautologicalChartLift_preimage_ι`.

Its image in `𝒪_{𝐏(ℰ)}` is that of `y`, every factor being pinned by a `_comp_ι` lemma; naming it
is what lets the one remaining hypothesis of clause 3's chart computation — `hxκ` — be *stated*
about a section of the ideal sheaf of the affine chart. -/
def chartIdealSection
    (y : (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.obj
      (op (tautologicalChart E W t))) :
    (Stacks.ClosedImmersion.idealSheaf
        (hW.isoSpec.hom ≫
          zeroSection Γ(X, W)
            (LinearMap.ker (chartLinearForm Q W eL))).toLRSHom.toShHom).val.obj (op ⊤) :=
  (Stacks.ClosedImmersion.idealSheaf
      (hW.isoSpec.hom ≫
        zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL))).toLRSHom.toShHom).val.map
    (eqToHom (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht)).op
    ((Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq
          (hW.isoSpec.hom ≫ zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))
          (tautologicalChartLift E Q hW eL t ht)
          ((Scheme.isoOfEq X
                (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm).hom ≫
            σ ∣_ tautologicalChart E W t)
          (isoSpec_comp_zeroSection_comp_tautologicalChartLift_eq
            E Q hσ e hqe hW eL t ht)).val.app
      (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
      ((Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
            (Scheme.isoOfEq X
              (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm)
            (σ ∣_ tautologicalChart E W t)).inv.val.app
        (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
        ((Stacks.Conormal.Restriction.restrictIdealSheafIso' σ
              (tautologicalChart E W t)).hom.val.app
          (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
          ((Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.map
            (homOfLE ((tautologicalChart E W t).ι.image_preimage_le
              (tautologicalChart E W t))).op y))))

omit [IsImmersion σ] in
include hσ e hqe in
/-- **`Stacks.ProjectiveBundleConormal.chartIdealSection` read as the hypothesis `hxy` of
`Stacks.Conormal.restrictConormalIsoOfOpenFactor_hom_canonicalConormalQuotientMap`.** It is the
definition of `chartIdealSection`, so this is `rfl`; it is a declaration of its own because the
heartbeat budget is per declaration and the consumer below must not be asked to perform this
delta-step inside a larger term. -/
theorem chartIdealSection_eq
    (y : (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.obj
      (op (tautologicalChart E W t))) :
    (Stacks.ClosedImmersion.idealSheaf
          (hW.isoSpec.hom ≫
            zeroSection Γ(X, W)
              (LinearMap.ker (chartLinearForm Q W eL))).toLRSHom.toShHom).val.map
        (eqToHom (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht)).op
        ((Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq
              (hW.isoSpec.hom ≫ zeroSection Γ(X, W) (LinearMap.ker (chartLinearForm Q W eL)))
              (tautologicalChartLift E Q hW eL t ht)
              ((Scheme.isoOfEq X
                    (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm).hom ≫
                σ ∣_ tautologicalChart E W t)
              (isoSpec_comp_zeroSection_comp_tautologicalChartLift_eq
                E Q hσ e hqe hW eL t ht)).val.app
          (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
          ((Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource
                (Scheme.isoOfEq X
                  (preimage_tautologicalChart E Q hσ e hqe hW eL t ht).symm)
                (σ ∣_ tautologicalChart E W t)).inv.val.app
            (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
            ((Stacks.Conormal.Restriction.restrictIdealSheafIso' σ
                  (tautologicalChart E W t)).hom.val.app
              (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
              ((Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.map
                (homOfLE ((tautologicalChart E W t).ι.image_preimage_le
                  (tautologicalChart E W t))).op y)))) =
      chartIdealSection E Q hσ e hqe hW eL t ht y :=
  rfl

omit [IsImmersion σ] in
include hσ e hqe in
/-- **The image of `Stacks.ProjectiveBundleConormal.chartIdealSection` in the structure sheaf.**
The section of the ideal sheaf of the affine chart that a section `y` of `ℐ(σ)` over the
tautological chart names has for its image in `𝒪_{Spec Sym_A(ker p)}` the image of `y` in
`𝒪_{𝐏(ℰ)}`, restricted to the self-preimage of the chart, read on the chart as an open subscheme
and pulled back along `Stacks.ProjectiveBundleConormal.tautologicalChartLift`.

**This is what the remaining hypothesis `hxκ` of clause 3's chart computation is compared
against.** `Stacks.Conormal.Locality.idealSheaf_section_injective` reduces an equation between
sections of that ideal sheaf to an equation between their images in
`Γ(𝒪, ⊤) = Sym_A(ker p)`, and the target side of that equation is read off by
`Stacks.ProjectiveBundleConormal.zeroSectionIdealSheafIso_hom_comp_idealSheafι`; this is the
source side. Its docstring on `chartIdealSection` recorded that every factor is pinned by a
`_comp_ι` lemma — here they are composed.

Each factor contributes one step and nothing else. The transport to `⊤` is naturality of the
inclusion (`PresheafOfModules.naturality_apply`); the cancellation of the open immersion of the
chart is `Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq_comp_ι`, read on a section
with the direct image stripped by
`Stacks.Conormal.OpenFactorizations.modulePushforward_map_val_app`; the source transport is
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource_inv_comp_ι`; and the
restriction isomorphism together with the restriction of `y` is
`Stacks.Tag01R3PartTwo.image_restrictIso'`. Composites are split on sections by
`AlgebraicGeometry.SheafOfModules.comp_val_app_apply`, which is `rfl`.

The inclusion is written at the `CategoryTheory.Limits.kernel.ι` spelling of the pinning lemmas
rather than at `Stacks.ClosedImmersion.idealSheafι`; the two are the same morphism and the choice
avoids a definitional crossing inside this declaration. -/
theorem chartIdealSection_app_ι
    (y : (Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom).val.obj
      (op (tautologicalChart E W t))) :
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (structureSheafHom
            (hW.isoSpec.hom ≫
              zeroSection Γ(X, W)
                (LinearMap.ker (chartLinearForm Q W eL))).toLRSHom.toShHom))).val.app (op ⊤)
        (chartIdealSection E Q hσ e hqe hW eL t ht y) =
      (Stacks.IdealSheafRestrict.unitModule
            (Spec (symRing Γ(X, W) ↥(LinearMap.ker (chartLinearForm Q W eL))))).val.map
          (eqToHom (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht)).op
        ((SheafOfModules.unitToPushforwardObjUnit
              (structureSheafHom
                (tautologicalChartLift E Q hW eL t ht).toLRSHom.toShHom)).val.app
            (op ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t))
          (((tautologicalChart E W t).ι.appIso
                ((tautologicalChart E W t).ι ⁻¹ᵁ tautologicalChart E W t)).hom
            (((bundle E).scheme.presheaf.map
                  (homOfLE ((tautologicalChart E W t).ι.image_preimage_le
                    (tautologicalChart E W t))).op).hom
              ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
                    (structureSheafHom σ.toLRSHom.toShHom))).val.app
                  (op (tautologicalChart E W t)) y)))) := by
  have hc := chartIdealSection_eq E Q hσ e hqe hW eL t ht y
  refine Eq.trans (congrArg _ hc.symm) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply _ _ _) ?_
  refine congrArg ((Stacks.IdealSheafRestrict.unitModule _).val.map
    (eqToHom (top_eq_preimage_tautologicalChartLift_preimage_ι E Q hW eL t ht)).op) ?_
  refine Eq.trans (Stacks.Conormal.OpenFactorizations.modulePushforward_map_val_app _ _ _ _).symm ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _).symm ?_
  refine Eq.trans (val_app_congr_hom
    (Stacks.Conormal.OpenFactorizations.idealRestrictHomOfCompEq_comp_ι _ _ _ _) _ _) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _) ?_
  refine congrArg ((SheafOfModules.unitToPushforwardObjUnit _).val.app _) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply _ _ _ _).symm ?_
  refine Eq.trans (val_app_congr_hom
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoOfIsoSource_inv_comp_ι _ _)
    _ _) ?_
  exact Stacks.Tag01R3PartTwo.image_restrictIso' _ _ _ _ _

end TautTarget

end Stacks.ProjectiveBundleConormal

end
