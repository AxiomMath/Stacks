module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedRingFunctoriality
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTriplePullback

/-!
# The classifying morphism of Stacks Tag 01N8 is a chart, and is functorial in the graded ring

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `d ≥ 1`, `Y` a scheme, `L` an invertible `𝒪_Y`-module
and `ψ : A^{(d)} ⟶ Γ_*(Y, L)` a graded map whose degree-`d` values generate `L`.
[Stacks, Tag 01N8] attaches to `(d, L, ψ)` a unique pair `(φ, α)`, and
`Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom` is its morphism `φ : Y ⟶ U_d`,
*chosen* from the `∃!`. This file gives that choice a formula:

`φ` restricted to `Y_{ψ(f)}` is the dehomogenisation chart of `f`,

for every homogeneous `f` of degree `d` — in other words `φ` is
`Stacks.AlgebraicGeometry.ProjChartCocycle.glued`, the witness the existence half of the tag
builds. That identification is what this file is for: the charts have a functoriality in the
graded ring that the `∃!`-witness cannot be given, and with the identification it transfers.

The functoriality is then proved. For a degree-preserving homomorphism `φ : A → B` of graded
rings, a graded map `ψ : B^{(d)} ⟶ Γ_*(Y, L)` pulls back to `χ = ψ ∘ φ : A^{(d)} ⟶ Γ_*(Y, L)` for
the *same* scheme and the *same* module, and

`r_ψ ≫ Proj(φ) = r_χ`

as morphisms `Y ⟶ Proj 𝒜`, where `r_ψ`, `r_χ` are the morphisms [Stacks, Tag 01N8] classifies.
The generation hypothesis needed is the one for `χ`, which is strictly stronger than the one for
`ψ` — the degree-`d` values of `χ` are the values of `ψ` at the images `φ(A_d) ⊆ B_d` only — and
`iSup_nonvanishingOpen_psiSection_comapVeronese` records the implication.

The case the development consumes is `φ` the restriction `𝒜(V) → 𝒜(Z)` of homogeneous sections of
a quasi-coherent graded algebra along an inclusion `Z ≤ V` of affine opens of a base, where
`Proj(φ)` is the transition morphism `Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap` of
[Stacks, Tag 01NO]. That is `toProj_classifyingHom_comp_projInclusionMap`, the **change of chart**
for the classifying morphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedClassifying.comapVeronese`: **the graded map
  `χ = ψ ∘ φ : A^{(d)} ⟶ Γ_*(Y, L)`**, degreewise, in the spelling [Stacks, Tag 01N8] consumes.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedClassifying.isCompatible_glued` and
  `classifyingHom_eq_glued`: **the morphism `Stacks.AlgebraicGeometry.ProjTripleClassifying`
  `.classifyingHom` chosen from the `∃!` of [Stacks, Tag 01N8] is the glued chart morphism
  `Stacks.AlgebraicGeometry.ProjChartCocycle.glued`.**
* `Stacks.AlgebraicGeometry.ProjChartGradedClassifying.ι_classifyingHom`: **the classifying
  morphism restricts on `Y_{ψ(f)}` to the dehomogenisation chart of `f`**, for every homogeneous
  `f` of degree `d`.
* `Stacks.AlgebraicGeometry.ProjChartGradedClassifying.lift_comapVeronese`: **the
  dehomogenisation ring map is functorial in the graded ring**: the ring map
  `A_{(f)} ⟶ Γ(V, 𝒪_Y)` of `χ` at `f` is `HomogeneousLocalization.Away.map φ f` followed by the
  ring map `B_{(φ f)} ⟶ Γ(V, 𝒪_Y)` of `ψ` at `φ f`; and
  `chartToProj_comapVeronese`, hence so is the chart.
* `Stacks.AlgebraicGeometry.ProjChartGradedClassifying.comapVeronese_pullbackSections`: **the
  two functorialities commute** — pulling back along a morphism of test schemes and along a
  homomorphism of graded rings.
* `Stacks.AlgebraicGeometry.ProjChartGradedClassifying.toProj_classifyingHom_comp_projMap`:
  **the classifying morphism of [Stacks, Tag 01N8] is functorial in the graded ring.**
* `Stacks.AlgebraicGeometry.ProjChartGradedClassifying`
  `.toProj_classifyingHom_comp_projInclusionMap`: **the change of chart** — the same for the
  transition morphism of [Stacks, Tag 01NO] attached to an inclusion of affine opens of a base.

## Implementation notes

**Why the identification with the glued morphism has to be proved and not read off.**
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair` is an `∃!`; its existence
half exhibits the pair `(glued, alphaGlued ≪≫ unitorPow L)` and its uniqueness half says there is
no other compatible pair, but the statement exports neither, so a consumer of `classifyingHom`
has no formula for it. `isCompatible_glued` states exactly the compatibility that proof
establishes, and `classifyingHom_eq_glued` is then the uniqueness half.

**The chart-level functoriality is the same identity as for a full graded map.** The sibling
`Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.lift_comp_awayMap` proves it for
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`, i.e. for a graded map defined in
every degree; `lift_comapVeronese` below is the same statement for
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`, a graded map defined on the
Veronese subring only, which is the datum [Stacks, Tag 01N8] and the quadruples of Section 01NS
produce. The two spellings share the ring map — both lift a
`Stacks.MorphismToProj.HomogeneousRatios` — so the proofs are the same computation on the
fractions `a / f ^ n`, where both sides are the ratio `ψ(φ a) / ψ(φ f ^ n)` and the only
discrepancy is that the left side presents the denominator as `ψ(φ (f ^ n))` and the right as
`ψ((φ f) ^ n)`.

**`Proj.map` is universe-monomorphic**, so as in the sibling the two graded rings and the two
types of homogeneous pieces are all taken in one universe in the sections about `φ`. The section
about the glued morphism has no such constraint.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal Graded
open AlgebraicGeometry.Proj (degreeOpen)
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.MorphismToProjUniversal
open Stacks.AlgebraicGeometry.ProjChartCocycle
open Stacks.AlgebraicGeometry.ProjChartCocycleMatch
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjTripleClassifying
open Stacks.AlgebraicGeometry.RelativeProj (projInclusionMap)
open Stacks.AlgebraicGeometry.RelativeProjBridge (SheafGradedAlgebra)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedClassifying

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The classifying morphism is the glued chart morphism -/

section Glued

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L]

/-- **The covering family of [Stacks, Tag 01N8] lies under the trivializing sections.** The
nonvanishing open of `ψ(f)`, read in `L`, is the nonvanishing open of the degree-one value of `ψ`
at `f`, read in `L ^⊗ 1`; this is that equality as the inequality the gluing of the charts takes
as data. -/
theorem le_nonvanishingOpen_psiSection (ψ : VeroneseSections 𝒜 d L) (g : 𝒜 d) :
    nonvanishingOpen Y L (psiSection 𝒜 ψ g)
      ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1) :=
  (nonvanishingOpen_psiSection 𝒜 ψ g).le

/-- **The pair the existence half of [Stacks, Tag 01N8] builds is compatible with `ψ`.** The
morphism is `Stacks.AlgebraicGeometry.ProjChartCocycle.glued`, the charts of `ψ` over the
nonvanishing opens of its degree-`d` values glued together, and the isomorphism is
`Stacks.AlgebraicGeometry.ProjChartCocycleMatch.alphaGlued`, the per-chart trivializations glued
together and read in `L` through the left unitor.

The degree-one clause is the normalisation `α(m f) = ψ(f)` of `α`
(`...ProjChartCocycleMatch.alphaGlued_hom_app_top`). The degree-`n` clause is clause (b) of the
tag on a single chart (`...VeroneseSections.resTop_eq_lift_smul`) together with the
identification of `φ^♯` on the fraction `a / f ^ n` with the chart's own ring map
(`...ProjChartGluing.appLE_awayToSection`), which applies because over an open contained in
`Y_{ψ(f)}` the glued morphism *is* the chart of `f`.

This is the content of the existence half of
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair`, which proves it inside the
`∃!` and so does not export it. -/
theorem isCompatible_glued (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) :
    IsCompatible 𝒜 ψ
      ⟨glued 𝒜 ψ hd (le_nonvanishingOpen_psiSection 𝒜 ψ) hgen,
        alphaGlued 𝒜 ψ hd (le_nonvanishingOpen_psiSection 𝒜 ψ) hgen ≪≫ unitorPow L⟩ := by
  set hWle := le_nonvanishingOpen_psiSection 𝒜 ψ with hWdef
  refine ⟨fun x => ?_, fun f V hV n y hy a hay => ?_⟩
  · rw [twistCast_hom_app_psiPullbackHom 𝒜 _ x (by simpa using x.2), Iso.trans_hom,
      Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
      alphaGlued_hom_app_top 𝒜 ψ hd hWle hgen ⟨(x : A), by simpa using x.2⟩]
    exact congrArg _ (ψ.toFun_eq_pow (by simpa using x.2) 1 x (pow_one _).symm).symm
  · have hVle : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow f.2 1) :=
      hV.trans (preimage_basicOpen_glued 𝒜 ψ hd hWle hgen f).le
    have hVW : V ≤ nonvanishingOpen Y L (psiSection 𝒜 ψ f) :=
      hVle.trans (nonvanishingOpen_psiSection 𝒜 ψ f).ge
    have hPhi : V.ι ≫ toProj 𝒜 (glued 𝒜 ψ hd hWle hgen)
        = (ψ.homogeneousRatios f.2 hVle).chartToProj hd := by
      rw [← Y.homOfLE_ι hVW, Category.assoc,
        ι_comp_toProj 𝒜 ψ hd hWle (ι_glued 𝒜 ψ hd hWle hgen) f,
        homOfLE_chartToProj 𝒜 ψ f.2 hd (hWle f) hVW]
    rw [ProjChartGluing.appLE_awayToSection (ψ.homogeneousRatios f.2 hVle) hd hPhi hV]
    exact ψ.resTop_eq_lift_smul f.2 hVle hd n y hy a hay

/-- **The morphism of [Stacks, Tag 01N8] chosen from the `∃!` is the glued chart morphism.**
`isCompatible_glued` exhibits a compatible pair whose first component is
`Stacks.AlgebraicGeometry.ProjChartCocycle.glued`, and by the uniqueness half of the tag that
first component is the classifying morphism. -/
theorem classifyingHom_eq_glued (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) :
    classifyingHom 𝒜 hd ψ hgen = glued 𝒜 ψ hd (le_nonvanishingOpen_psiSection 𝒜 ψ) hgen :=
  (eq_classifyingHom_of_isCompatible 𝒜 hd ψ hgen _ (isCompatible_glued 𝒜 hd ψ hgen)).symm

/-- **The classifying morphism of [Stacks, Tag 01N8] restricts on `Y_{ψ(f)}` to the
dehomogenisation chart of `f`**, for every homogeneous `f` of degree `d`. This is the formula for
the `∃!`-witness that `classifyingHom_eq_glued` unlocks, and it is what makes the morphism
comparable with anything built from charts. -/
theorem ι_classifyingHom (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) (g : 𝒜 d) :
    (nonvanishingOpen Y L (psiSection 𝒜 ψ g)).ι ≫ classifyingHom 𝒜 hd ψ hgen
      = ψ.toDegreeOpen g.2 (le_nonvanishingOpen_psiSection 𝒜 ψ g) hd := by
  rw [classifyingHom_eq_glued 𝒜 hd ψ hgen]
  exact ι_glued 𝒜 ψ hd (le_nonvanishingOpen_psiSection 𝒜 ψ) hgen g

/-- The classifying morphism read into `Proj 𝒜`, restricted to `Y_{ψ(f)}`, is the
dehomogenisation chart of `f` read into `Proj 𝒜`. -/
theorem ι_toProj_classifyingHom (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) (g : 𝒜 d) :
    (nonvanishingOpen Y L (psiSection 𝒜 ψ g)).ι ≫ toProj 𝒜 (classifyingHom 𝒜 hd ψ hgen)
      = (ψ.homogeneousRatios g.2 (le_nonvanishingOpen_psiSection 𝒜 ψ g)).chartToProj hd := by
  rw [toProj, ← Category.assoc, ι_classifyingHom 𝒜 hd ψ hgen g,
    VeroneseSections.toDegreeOpen, ← toProj]
  exact HomogeneousRatios.toProj_toDegreeOpen _ hd

/-- **On any open inside `Y_{ψ(f)}` the classifying morphism of [Stacks, Tag 01N8], read into
`Proj 𝒜`, is the dehomogenisation chart of `f`.** `ι_toProj_classifyingHom` is the case of the
nonvanishing open itself; the general case follows because the charts restrict
(`...MorphismToProjUniversal.homOfLE_chartToProj`).

The open is given together with its two inclusion proofs, one into the nonvanishing open read in
`L` and one into the nonvanishing open read in `L ^⊗ 1`, rather than deriving the second from the
first: the second is what indexes the chart, and naming it keeps the statement applicable at an
open presented through a different but equal spelling of the nonvanishing locus. -/
theorem homOfLE_toProj_classifyingHom (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 ψ f) = ⊤) (g : 𝒜 d) {V : Y.Opens}
    (hVW : V ≤ nonvanishingOpen Y L (psiSection 𝒜 ψ g))
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1)) :
    V.ι ≫ toProj 𝒜 (classifyingHom 𝒜 hd ψ hgen)
      = (ψ.homogeneousRatios g.2 hV).chartToProj hd := by
  rw [← Y.homOfLE_ι hVW, Category.assoc, ι_toProj_classifyingHom 𝒜 hd ψ hgen g]
  exact homOfLE_chartToProj 𝒜 ψ g.2 hd (le_nonvanishingOpen_psiSection 𝒜 ψ g) hVW

end Glued

/-! ### The graded map pulled back along a homomorphism of graded rings -/

section Comap

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
  {Y : Scheme.{u}} {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L] {d : ℕ}
  (ψ : VeroneseSections ℬ d L)

/-- **The graded map `χ = ψ ∘ φ : A^{(d)} → Γ_*(Y, L)`**, for a degree-preserving homomorphism
`φ : A → B` of graded rings and a graded map `ψ : B^{(d)} → Γ_*(Y, L)`. In degree `n` it is the
degree-`nd` component `𝒜 (nd) →+ ℬ (nd)` of `φ` followed by the degree-`n` component of `ψ`;
multiplicativity across degrees is that of `ψ` applied to the images, `φ` being
multiplicative. -/
def comapVeronese : VeroneseSections 𝒜 d L where
  toFun n := (ψ.toFun n).comp (φ.gradedAddHom (n * d))
  map_mul n m a b ab hab := by
    refine ψ.map_mul n m (φ.gradedAddHom (n * d) a) (φ.gradedAddHom (m * d) b)
      (φ.gradedAddHom ((n + m) * d) ab) ?_
    change φ (ab : A) = φ (a : A) * φ (b : A)
    rw [hab, map_mul]

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- The value of `χ` on a homogeneous element is the value of `ψ` on its image. -/
theorem comapVeronese_toFun (n : ℕ) (a : 𝒜 (n * d)) :
    (comapVeronese φ ψ).toFun n a = ψ.toFun n ⟨φ (a : A), map_mem φ a.2⟩ := rfl

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **The trivializing sections of `χ` are those of `ψ` at the images.** The `n`-th power of the
trivializing section of `χ` at `f` is that of `ψ` at `φ f`: the first is `ψ(φ (f ^ n))` and the
second `ψ((φ f) ^ n)`, and `φ` is multiplicative. -/
theorem comapVeronese_pow {f : A} (hf : f ∈ 𝒜 d) (n : ℕ) :
    (comapVeronese φ ψ).pow hf n = ψ.pow (map_mem φ hf) n := by
  rw [VeroneseSections.pow, comapVeronese_toFun]
  exact ψ.toFun_eq_pow (map_mem φ hf) n _ (map_pow φ f n)

omit [Stacks.Ample.IsInvertibleModule Y L] in
/-- **The global section `χ(f)` of `L` is the global section `ψ(φ f)`.** -/
theorem psiSection_comapVeronese (f : 𝒜 d) :
    psiSection 𝒜 (comapVeronese φ ψ) f = psiSection ℬ ψ ⟨φ (f : A), map_mem φ f.2⟩ :=
  congrArg _ (comapVeronese_pow φ ψ f.2 1)

/-- **The generation hypothesis for `χ` implies the one for `ψ`.** The nonvanishing opens of the
degree-`d` values of `χ` are among those of the degree-`d` values of `ψ`, namely the ones indexed
by the images `φ(A_d) ⊆ B_d`, so the second family covers `Y` as soon as the first does. The
converse fails: `φ` need not be surjective. -/
theorem iSup_nonvanishingOpen_psiSection_comapVeronese
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 (comapVeronese φ ψ) f) = ⊤) :
    ⨆ g : ℬ d, nonvanishingOpen Y L (psiSection ℬ ψ g) = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← hgen]
  refine iSup_le fun f => le_iSup_of_le ⟨φ (f : A), map_mem φ f.2⟩ (le_of_eq ?_)
  rw [psiSection_comapVeronese φ ψ f]

/-- **Pulling back along a morphism of test schemes and pulling back along a homomorphism of
graded rings commute.** The two functorialities act on different arguments of a value `ψ(a)`, so
the identity holds degreewise on the nose: both sides send a homogeneous `a` of degree `nd` to
the pullback along `h` of `ψ(φ a)`. -/
theorem comapVeronese_pullbackSections {Y' : Scheme.{u}} (h : Y' ⟶ Y) :
    comapVeronese φ (ProjTriplePullback.pullbackSections ℬ ψ h)
      = ProjTriplePullback.pullbackSections 𝒜 (comapVeronese φ ψ) h := rfl

/-! ### The chart of a homogeneous element is functorial in the graded ring -/

section Chart

variable (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) {V : Y.Opens}
  (hV : V ≤ nonvanishingOpen Y (natTensorPow L 1) ((comapVeronese φ ψ).pow hf 1))
  (hV' : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow (map_mem φ hf) 1))

include hd hV hV'

/-- **The dehomogenisation ring map is functorial in the graded ring.** The ring map
`A_{(f)} ⟶ Γ(V, 𝒪_Y)` attached to `χ = ψ ∘ φ` and a homogeneous `f ∈ A_d` is
`HomogeneousLocalization.Away.map φ f`, which sends `a / f ^ n` to `φ a / (φ f) ^ n`, followed by
the ring map `B_{(φ f)} ⟶ Γ(V, 𝒪_Y)` attached to `ψ` and `φ f`.

Checked on the fractions `a / f ^ n`, which are all of `A_{(f)}`. Both sides are the ratio
`ψ(φ a) / ψ(φ f ^ n)`; the left side reads the denominator as `ψ(φ (f ^ n))` and the right as
`ψ((φ f) ^ n)`, and `...ProjChartCocycle.ratioOf_psi_congr` identifies the two. -/
theorem lift_comapVeronese :
    ((comapVeronese φ ψ).homogeneousRatios hf hV).lift hd
      = (((ψ.homogeneousRatios (map_mem φ hf) hV').lift hd)).comp
          (HomogeneousLocalization.Away.map φ f) := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun n x hx => ?_
  have hxm : x ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using hx
  have hmem : φ x ∈ ℬ (n • d) := map_mem φ hx
  have hfn : (f : A) ^ n ∈ 𝒜 (n * d) := HomogeneousRatios.pow_mem hf n
  have hpn : (φ f : B) ^ n ∈ ℬ (n * d) := HomogeneousRatios.pow_mem (map_mem φ hf) n
  rw [HomogeneousRatios.lift_mk _ hd n x hx ⟨x, hxm⟩ rfl]
  change _ = ((ψ.homogeneousRatios (map_mem φ hf) hV').lift hd)
    (HomogeneousLocalization.Away.map φ f (HomogeneousLocalization.Away.mk 𝒜 hf n x hx))
  rw [HomogeneousLocalization.Away.map_mk,
    HomogeneousRatios.lift_mk _ hd n (φ x) hmem ⟨φ x, map_mem φ hxm⟩ rfl]
  exact ratioOf_psi_congr ψ (map_mem φ hfn) (map_mem φ hxm) hpn (map_mem φ hxm)
    ((comapVeronese φ ψ).le_nonvanishingOpen hf hV n)
    (ψ.le_nonvanishingOpen (map_mem φ hf) hV' n) rfl (map_pow φ f n) rfl

variable (hφ : irrelevant ℬ ≤ (irrelevant 𝒜).map φ)

include hφ

/-- **The chart of a homogeneous element is functorial in the graded ring.** The chart
`V ⟶ Proj 𝒜` of `f` for `χ = ψ ∘ φ` is the chart `V ⟶ Proj ℬ` of `φ f` for `ψ` followed by
`AlgebraicGeometry.Proj.map φ`.

The two dehomogenisation ring maps differ by `HomogeneousLocalization.Away.map φ f`
(`lift_comapVeronese`), and Mathlib's `AlgebraicGeometry.Proj.awayι_comp_map` is exactly the
square saying that `Spec` of that ring map commutes with `Proj.map φ` and the two standard affine
charts. -/
theorem chartToProj_comapVeronese :
    ((comapVeronese φ ψ).homogeneousRatios hf hV).chartToProj hd
      = (ψ.homogeneousRatios (map_mem φ hf) hV').chartToProj hd
          ≫ AlgebraicGeometry.Proj.map φ hφ := by
  unfold HomogeneousRatios.chartToProj HomogeneousRatios.toSpecAway
  rw [lift_comapVeronese φ ψ hd hf hV hV', CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [AlgebraicGeometry.Proj.awayι_comp_map]

end Chart

/-! ### The classifying morphism is functorial in the graded ring -/

/-- **The classifying morphism of [Stacks, Tag 01N8] is functorial in the graded ring.** For a
degree-preserving homomorphism `φ : A → B` of graded rings and a graded map
`ψ : B^{(d)} → Γ_*(Y, L)` whose values at the images `φ(A_d)` already generate `L`, the morphism
`Y ⟶ Proj ℬ` that [Stacks, Tag 01N8] attaches to `ψ`, followed by
`AlgebraicGeometry.Proj.map φ`, is the morphism `Y ⟶ Proj 𝒜` it attaches to `χ = ψ ∘ φ`.

Both sides are morphisms out of `Y`, which the nonvanishing opens `Y_{χ(f)} = Y_{ψ(φ f)}`,
`f ∈ A_d`, cover by the generation hypothesis. On `Y_{χ(f)}` each restricts to a
dehomogenisation chart of `f` — by `ι_toProj_classifyingHom` on both sides, the right one at the
index `φ f` — and the two charts are identified by `chartToProj_comapVeronese`. -/
theorem ι_toProj_classifyingHom_comp_projMap
    (hφ : irrelevant ℬ ≤ (irrelevant 𝒜).map φ) (hd : 0 < d)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 (comapVeronese φ ψ) f) = ⊤)
    (f : 𝒜 d) :
    (nonvanishingOpen Y L (psiSection 𝒜 (comapVeronese φ ψ) f)).ι
        ≫ toProj ℬ (classifyingHom ℬ hd ψ
            (iSup_nonvanishingOpen_psiSection_comapVeronese φ ψ hgen))
          ≫ AlgebraicGeometry.Proj.map φ hφ
      = (nonvanishingOpen Y L (psiSection 𝒜 (comapVeronese φ ψ) f)).ι
          ≫ toProj 𝒜 (classifyingHom 𝒜 hd (comapVeronese φ ψ) hgen) := by
  have hVψ : nonvanishingOpen Y L (psiSection 𝒜 (comapVeronese φ ψ) f)
      ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow (map_mem φ f.2) 1) := by
    rw [← comapVeronese_pow φ ψ f.2 1]
    exact le_nonvanishingOpen_psiSection 𝒜 (comapVeronese φ ψ) f
  have hVW : nonvanishingOpen Y L (psiSection 𝒜 (comapVeronese φ ψ) f)
      ≤ nonvanishingOpen Y L (psiSection ℬ ψ ⟨φ (f : A), map_mem φ f.2⟩) :=
    le_of_eq (congrArg _ (psiSection_comapVeronese φ ψ f))
  rw [← Category.assoc,
    homOfLE_toProj_classifyingHom ℬ hd ψ
      (iSup_nonvanishingOpen_psiSection_comapVeronese φ ψ hgen)
      ⟨φ (f : A), map_mem φ f.2⟩ hVW hVψ,
    ← chartToProj_comapVeronese φ ψ hd f.2
      (le_nonvanishingOpen_psiSection 𝒜 (comapVeronese φ ψ) f) hVψ hφ]
  exact (ι_toProj_classifyingHom 𝒜 hd (comapVeronese φ ψ) hgen f).symm

/-- **The classifying morphism of [Stacks, Tag 01N8] is functorial in the graded ring**, as an
equality of morphisms out of `Y`. The nonvanishing opens `Y_{χ(f)}`, `f ∈ A_d`, cover `Y` by the
generation hypothesis, and `ι_toProj_classifyingHom_comp_projMap` is the identity on each. -/
theorem toProj_classifyingHom_comp_projMap (hφ : irrelevant ℬ ≤ (irrelevant 𝒜).map φ) (hd : 0 < d)
    (hgen : ⨆ f : 𝒜 d, nonvanishingOpen Y L (psiSection 𝒜 (comapVeronese φ ψ) f) = ⊤) :
    toProj ℬ (classifyingHom ℬ hd ψ
          (iSup_nonvanishingOpen_psiSection_comapVeronese φ ψ hgen))
        ≫ AlgebraicGeometry.Proj.map φ hφ
      = toProj 𝒜 (classifyingHom 𝒜 hd (comapVeronese φ ψ) hgen) :=
  Scheme.Cover.hom_ext (opensCover 𝒜 hgen) _ _ fun f =>
    ι_toProj_classifyingHom_comp_projMap φ ψ hφ hd hgen f

end Comap

/-! ### The change of chart -/

section Base

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) {Z V : S.Opens} (h : Z ≤ V)
  (hZ : IsAffineOpen Z) (hV : IsAffineOpen V)
  {Y : Scheme.{u}} {L : Y.Modules} [Stacks.Ample.IsInvertibleModule Y L] {d : ℕ}
  (ψ : VeroneseSections (A.grading Z) d L)

/-- **The change of chart for the classifying morphism of [Stacks, Tag 01N8].** For affine opens
`Z ⊆ V` of a scheme `S` carrying a quasi-coherent graded algebra `𝒜`, let `ψ` be a Tag 01N8 datum
of weight `d` for the graded ring `𝒜(Z)` of homogeneous sections over `Z`, and
`χ = ψ ∘ (𝒜(V) → 𝒜(Z))` the induced datum for `𝒜(V)`, whose degree-`d` values are assumed to
generate. Then the morphism `Y ⟶ Proj 𝒜(Z)` that the tag attaches to `ψ`, followed by the
transition morphism `Proj 𝒜(Z) ⟶ Proj 𝒜(V)` of [Stacks, Tag 01NO], is the morphism
`Y ⟶ Proj 𝒜(V)` the tag attaches to `χ`.

This is `toProj_classifyingHom_comp_projMap` together with
`Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_eq_map_of_le_opens`, which says that the
transition morphism of an arbitrary inclusion of affine opens is `AlgebraicGeometry.Proj.map` of
the restriction homomorphism. -/
theorem toProj_classifyingHom_comp_projInclusionMap (hd : 0 < d)
    (hgen : ⨆ f : A.grading V d,
      nonvanishingOpen Y L (psiSection (A.grading V) (comapVeronese (A.res h) ψ) f) = ⊤) :
    toProj (A.grading Z) (classifyingHom (A.grading Z) hd ψ
          (iSup_nonvanishingOpen_psiSection_comapVeronese (A.res h) ψ hgen))
        ≫ projInclusionMap A Z V h hZ hV
      = toProj (A.grading V)
          (classifyingHom (A.grading V) hd (comapVeronese (A.res h) ψ) hgen) := by
  have hres : irrelevant (A.grading Z) ≤ (irrelevant (A.grading V)).map (A.res h) :=
    RelativeProjGeneral.irrelevant_le_map_res_of_le_opens A.toGradedAlgebra
      (U := ⟨Z, hZ⟩) (V := ⟨V, hV⟩) h
  have hmap : projInclusionMap A Z V h hZ hV = AlgebraicGeometry.Proj.map (A.res h) hres :=
    RelativeProjGeneral.transition_eq_map_of_le_opens A.toGradedAlgebra
      (U := ⟨Z, hZ⟩) (V := ⟨V, hV⟩) h _
  rw [hmap]
  exact toProj_classifyingHom_comp_projMap (A.res h) ψ hres hd hgen

end Base

end Stacks.AlgebraicGeometry.ProjChartGradedClassifying

end
