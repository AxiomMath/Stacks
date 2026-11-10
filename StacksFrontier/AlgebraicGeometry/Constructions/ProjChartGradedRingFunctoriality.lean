module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartFullGradedGluing
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Assembled

/-!
# The morphism `r_{L, ψ} : U(ψ) ⟶ Proj 𝒜` is functorial in the graded ring

Let `T` be a scheme, `L` an invertible `𝒪_T`-module, and let `φ : A → B` be a degree-preserving
homomorphism of graded rings, `φ : 𝒜 →+*ᵍ ℬ`. A graded map `ψ : B → Γ_*(T, L)` in the degreewise
spelling `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections` pulls back along `φ` to a
graded map `χ = ψ ∘ φ : A → Γ_*(T, L)` for the *same* scheme and the *same* invertible module.
This file proves that the morphism of [Stacks, Tag 01NK] is compatible with that pullback:

`(U(χ) ↪ U(ψ)) ≫ r_{L, ψ} ≫ Proj(φ) = r_{L, χ}`,

where `Proj(φ) : Proj ℬ ⟶ Proj 𝒜` is Mathlib's `AlgebraicGeometry.Proj.map`.

The sibling file `ProjChartGradedPullback.lean` proves the compatibility in the other variable —
the scheme and the module move, the graded ring is fixed. The two together are what a comparison
of the Tag 01NK morphisms attached to two nested affine opens of a base needs, which is the
agreement hypothesis that
`Stacks.AlgebraicGeometry.RelativeProjFromSections.glued` takes as data.

**The inclusion of the open sets is strict in general, and the statement says so.** `U(ψ)` is the
union of the nonvanishing opens `T_{ψ(b)}` over the homogeneous `b ∈ B` of positive degree, and
`U(χ)` the union over the homogeneous `a ∈ A`; since `φ` need not be surjective, the second union
runs over fewer sections and `U(χ) ⊆ U(ψ)` can be proper. At a *single* element there is no loss:
`nonvanishingOpenAt_comap` below is `rfl`, the two opens being the nonvanishing open of one and
the same section `ψ(φ a)`. So the inclusion `coveringOpen_le` is the only inequality in the file,
and the generation condition that `glued` carries as data is the one for `χ`, not a consequence of
the one for `ψ`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.comap`: **the graded map
  `χ = ψ ∘ φ`**, degreewise.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.coveringOpen_le`:
  **`U(χ) ≤ U(ψ)`.**
* `Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.lift_comp_awayMap`: **the
  dehomogenisation ring map is functorial in the graded ring.** The ring map
  `A_{(f)} ⟶ Γ(V, 𝒪_T)` of `χ` at `f` is `HomogeneousLocalization.Away.map φ f` followed by the
  ring map `B_{(φ f)} ⟶ Γ(V, 𝒪_T)` of `ψ` at `φ f`.
* `Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.chartToProj_comp_projMap`: **the
  chart of a homogeneous element is functorial in the graded ring.**
* `Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projMap`:
  **`r_{L, ψ}` is functorial in the graded ring**, which is the statement above.
* `Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality.homOfLE_glued_comp_projInclusionMap`:
  the same for the morphism of projective spectra induced by restriction of homogeneous sections
  along an inclusion of affine opens of a base,
  `Stacks.AlgebraicGeometry.RelativeProj.projInclusionMap`.

## Implementation notes

The whole content is one identity of ring maps out of `A_{(f)}`, namely `lift_comp_awayMap`, which
`Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext` checks on the fractions `a / f ^ n`. There both
sides are the ratio `ψ(φ a) / ψ(φ f ^ n)` of two global sections of `L ^⊗ (n e)`; the only
discrepancy is that the left side presents the denominator as `ψ(φ (f ^ n))` and the right side as
`ψ((φ f) ^ n)`, which `GradedSections.ratioOf_congr` reconciles. The geometric step is then
Mathlib's `AlgebraicGeometry.Proj.awayι_comp_map`, the square relating `Proj.map φ` to the two
standard affine charts.

**`Proj.map` is universe-monomorphic.** Mathlib's `AlgebraicGeometry.Proj.map` lives in a section
where the carriers of the two graded rings and the two types of homogeneous pieces are all in one
universe, so `σ` and `τ` are taken in `Type u` here rather than in a separate universe as
`GradedSections` permits; applying it with the pieces in a different universe does not fail with
an error but loops. The graded rings of sections of a quasi-coherent graded algebra over affine
opens of a scheme `S : Scheme.{u}` are in `Type u`, so nothing is narrowed for the intended
consumer.

**Where the `≤` proofs are named.** `GradedSections.chartToProj` takes the open `V` implicitly,
through the proof that the denominator does not vanish on it, so the two spellings of one open —
the nonvanishing open of `χ(f)` and that of `ψ(φ f)` — have to be given as the *declared* type of
a named inclusion rather than left to `le_rfl`; otherwise the term carries the wrong `V` and the
rewriting that follows is reported as not type-correct at `implicit` transparency.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry HomogeneousLocalization HomogeneousIdeal Graded
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.RelativeProj (projInclusionMap)
open Stacks.AlgebraicGeometry.RelativeProjBridge (SheafGradedAlgebra)
open Stacks.MorphismToProj (HomogeneousRatios)

universe u

namespace Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### The graded map pulled back along a homomorphism of graded rings -/

section Comap

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections ℬ L)

/-- **The graded map `χ = ψ ∘ φ : A → Γ_*(T, L)`**, for a degree-preserving homomorphism of graded
rings `φ : A → B` and a graded map `ψ : B → Γ_*(T, L)`. In degree `n` it is the degree-`n`
component `𝒜 n →+ ℬ n` of `φ` followed by the degree-`n` component of `ψ`; multiplicativity across
degrees is that of `ψ` applied to the images, `φ` being multiplicative. -/
def comap : GradedSections 𝒜 L where
  toFun n := (ψ.toFun n).comp (φ.gradedAddHom n)
  map_mul n m a b ab hab := by
    refine ψ.map_mul n m (φ.gradedAddHom n a) (φ.gradedAddHom m b) (φ.gradedAddHom (n + m) ab) ?_
    change φ (ab : A) = φ (a : A) * φ (b : A)
    rw [hab, map_mul]

omit [Stacks.Ample.IsInvertibleModule T L] in
/-- The value of `χ` on a homogeneous element is the value of `ψ` on its image. -/
theorem comap_toFun (n : ℕ) (a : 𝒜 n) :
    (comap φ ψ).toFun n a = ψ.toFun n ⟨φ (a : A), map_mem φ a.2⟩ := rfl

/-- **At a single homogeneous element the two nonvanishing opens are one and the same**:
`T_{χ(a)} = T_{ψ(φ a)}`, both being the nonvanishing open of the section `ψ(φ a)` of `L ^⊗ n`. -/
theorem nonvanishingOpenAt_comap (n : ℕ) (a : 𝒜 n) :
    (comap φ ψ).nonvanishingOpenAt n a = ψ.nonvanishingOpenAt n (φ.gradedAddHom n a) := rfl

/-- **`U(χ) ≤ U(ψ)`.** Each member `T_{χ(a)}` of the family whose union is `U(χ)` is the member
`T_{ψ(φ a)}` of the family whose union is `U(ψ)`. The inclusion is proper in general: the second
family is indexed by all homogeneous elements of `B` of positive degree, the first only by the
images of those of `A`. -/
theorem coveringOpen_le : (comap φ ψ).coveringOpen ≤ ψ.coveringOpen :=
  iSup_le fun p => ψ.nonvanishingOpenAt_le_coveringOpen p.1 (φ.gradedAddHom (p.1 + 1) p.2)

end Comap

/-! ### The chart of a homogeneous element -/

section Chart

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
  (hφ : ℬ₊ ≤ 𝒜₊.map φ)
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections ℬ L) {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
  (hV : V ≤ nonvanishingOpen T (natTensorPow L e) ((comap φ ψ).toFun e ⟨f, hf⟩))
  (hV' : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨φ f, map_mem φ hf⟩))

include hV hV'

/-- **The dehomogenisation ring map is functorial in the graded ring.** The ring map
`A_{(f)} ⟶ Γ(V, 𝒪_T)` attached to `χ = ψ ∘ φ` and a homogeneous `f ∈ A_e` is
`HomogeneousLocalization.Away.map φ f`, which sends `a / f ^ n` to `φ a / (φ f) ^ n`, followed by
the ring map `B_{(φ f)} ⟶ Γ(V, 𝒪_T)` attached to `ψ` and `φ f`.

Checked on the fractions `a / f ^ n`, which are all of `A_{(f)}`. Both sides are the ratio
`ψ(φ a) / ψ(φ f ^ n)`; the left side reads the denominator as `ψ(φ (f ^ n))` and the right as
`ψ((φ f) ^ n)`, and `GradedSections.ratioOf_congr` identifies the two. -/
theorem lift_comp_awayMap :
    ((comap φ ψ).homogeneousRatios hf hV).lift he
      = ((ψ.homogeneousRatios (map_mem φ hf) hV').lift he).comp
          (HomogeneousLocalization.Away.map φ f) := by
  refine Stacks.ProjGlobalSectionsAppTop.away_ringHom_ext 𝒜 hf fun n x hx => ?_
  have hxm : x ∈ 𝒜 (n * e) := by simpa [smul_eq_mul] using hx
  have hfn : (f : A) ^ n ∈ 𝒜 (n * e) := HomogeneousRatios.pow_mem hf n
  have hpn : φ f ^ n ∈ ℬ (n * e) := HomogeneousRatios.pow_mem (map_mem φ hf) n
  have hmem : φ x ∈ ℬ (n • e) := map_mem φ hx
  rw [(comap φ ψ).lift_mk hf hV he n x hx ⟨x, hxm⟩ rfl]
  change _ = (ψ.homogeneousRatios (map_mem φ hf) hV').lift he
    (HomogeneousLocalization.Away.map φ f (HomogeneousLocalization.Away.mk 𝒜 hf n x hx))
  rw [HomogeneousLocalization.Away.map_mk,
    ψ.lift_mk (map_mem φ hf) hV' he n (φ x) hmem ⟨φ x, map_mem φ hxm⟩ rfl]
  exact ψ.ratioOf_congr (map_mem φ hfn) (map_mem φ hxm) hpn (map_mem φ hxm)
    ((comap φ ψ).le_nonvanishingOpen_pow hf hV n)
    (ψ.le_nonvanishingOpen_pow (map_mem φ hf) hV' n) rfl (map_pow φ f n) rfl

include hφ

/-- **The chart of a homogeneous element is functorial in the graded ring.** The chart
`V ⟶ Proj 𝒜` of `f` for `χ = ψ ∘ φ` is the chart `V ⟶ Proj ℬ` of `φ f` for `ψ` followed by
`AlgebraicGeometry.Proj.map φ`.

The two dehomogenisation ring maps differ by `HomogeneousLocalization.Away.map φ f`
(`lift_comp_awayMap`), and Mathlib's `AlgebraicGeometry.Proj.awayι_comp_map` is exactly the square
saying that `Spec` of that ring map commutes with `Proj.map φ` and the two standard affine
charts. -/
theorem chartToProj_comp_projMap :
    (comap φ ψ).chartToProj hf hV he
      = ψ.chartToProj (map_mem φ hf) hV' he ≫ AlgebraicGeometry.Proj.map φ hφ := by
  unfold GradedSections.chartToProj HomogeneousRatios.chartToProj HomogeneousRatios.toSpecAway
  rw [lift_comp_awayMap φ ψ hf he hV hV', CommRingCat.ofHom_comp, Spec.map_comp]
  simp only [Category.assoc]
  rw [AlgebraicGeometry.Proj.awayι_comp_map]

end Chart

/-! ### The morphism `r_{L, ψ}` is functorial in the graded ring -/

section Glued

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
  (hφ : ℬ₊ ≤ 𝒜₊.map φ)
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections ℬ L)

include hφ

/-- **The morphism `r_{L, ψ}` of [Stacks, Tag 01NK] is functorial in the graded ring.** For a
degree-preserving homomorphism `φ : A → B` of graded rings and a graded map `ψ : B → Γ_*(T, L)`,
the inclusion `U(ψ ∘ φ) ⟶ U(ψ)` followed by `r_{L, ψ}` and by `AlgebraicGeometry.Proj.map φ` is
`r_{L, ψ ∘ φ}`.

Both sides are morphisms out of `U(ψ ∘ φ)`, so it is enough to compare them on each member
`T_{(ψ ∘ φ)(f)}` of its cover (`GradedSections.eq_glued_of_homOfLE_eq`). There the left side
factors through `T_{ψ(φ f)}` — the *same* open — where `r_{L, ψ}` is the chart of `φ f`
(`GradedSections.homOfLE_glued_of_pos`), and the two charts are identified by
`chartToProj_comp_projMap`. -/
theorem homOfLE_glued_comp_projMap :
    T.homOfLE (coveringOpen_le φ ψ) ≫ ψ.glued ≫ AlgebraicGeometry.Proj.map φ hφ
      = (comap φ ψ).glued := by
  refine (comap φ ψ).eq_glued_of_homOfLE_eq fun e f hf he => ?_
  have hVψ : nonvanishingOpen T (natTensorPow L e) ((comap φ ψ).toFun e ⟨f, hf⟩)
      ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨φ f, map_mem φ hf⟩) := le_rfl
  have key : T.homOfLE ((comap φ ψ).nonvanishingOpenAt_le_coveringOpen_of_pos hf he)
        ≫ T.homOfLE (coveringOpen_le φ ψ) ≫ ψ.glued
      = ψ.chartToProj (map_mem φ hf) hVψ he := by
    rw [← Category.assoc, T.homOfLE_homOfLE]
    exact ψ.homOfLE_glued_of_pos (map_mem φ hf) he
  refine Eq.trans ?_ (chartToProj_comp_projMap φ hφ ψ hf he le_rfl hVψ).symm
  rw [← key]
  simp only [Category.assoc]

end Glued

/-! ### Restriction of homogeneous sections along an inclusion of affine opens -/

section Base

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) {Z V : S.Opens} (h : Z ≤ V)
  (hZ : IsAffineOpen Z) (hV : IsAffineOpen V)
  {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections (A.grading Z) L)

/-- **The Tag 01NK morphism is compatible with restriction of the base.** For affine opens
`Z ⊆ V` of a scheme `S` carrying a quasi-coherent graded algebra `𝒜`, let `ψ` be a Tag 01NK datum
for the graded ring `𝒜(Z)` of homogeneous sections over `Z`, and `χ = ψ ∘ (𝒜(V) → 𝒜(Z))` the
induced datum for `𝒜(V)`. Then the inclusion `U(χ) ⟶ U(ψ)` followed by `r_{L, ψ}` and by the
morphism of projective spectra `Proj 𝒜(Z) ⟶ Proj 𝒜(V)` of [Stacks, Tag 01NO] is `r_{L, χ}`.

This is `homOfLE_glued_comp_projMap` together with
`Stacks.AlgebraicGeometry.RelativeProjGeneral.transition_eq_map_of_le_opens`, which says that the
transition morphism of an arbitrary inclusion of affine opens is `AlgebraicGeometry.Proj.map` of
the restriction homomorphism. -/
theorem homOfLE_glued_comp_projInclusionMap :
    T.homOfLE (coveringOpen_le (A.res h) ψ) ≫ ψ.glued ≫ projInclusionMap A Z V h hZ hV
      = (comap (A.res h) ψ).glued := by
  have hres : irrelevant (A.grading Z) ≤ (irrelevant (A.grading V)).map (A.res h) :=
    RelativeProjGeneral.irrelevant_le_map_res_of_le_opens A.toGradedAlgebra
      (U := ⟨Z, hZ⟩) (V := ⟨V, hV⟩) h
  have hmap : projInclusionMap A Z V h hZ hV = AlgebraicGeometry.Proj.map (A.res h) hres :=
    RelativeProjGeneral.transition_eq_map_of_le_opens A.toGradedAlgebra
      (U := ⟨Z, hZ⟩) (V := ⟨V, hV⟩) h _
  rw [hmap]
  exact homOfLE_glued_comp_projMap (A.res h) hres ψ

end Base

end Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality

end
