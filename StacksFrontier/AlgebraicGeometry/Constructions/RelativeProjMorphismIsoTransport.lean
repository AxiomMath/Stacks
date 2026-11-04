module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTransport
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedVeronese
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeProjMorphismBaseRestriction

/-!
# `r_{L, ψ}` is unchanged by transport along an isomorphism of invertible modules

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a datum of graded sections
(`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`), the input of
[Stacks, Tag 01NK]. An isomorphism `β : L ≅ L'` of invertible modules transports `ψ` to a datum
`β ∘ ψ` for `L'` — that is
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.congrModule` — and leaves the open
`U(ψ)` where it was. This file proves that it leaves the *morphism* of Tag 01NK where it was too,
and draws the consequence for the relative morphism `r_{ℒ, ψ}` of [Stacks, Tag 01O9].

The point of doing so is the glueing step of Tag 01O9. The source builds `r_{ℒ, ψ}` over each
affine open `V` of the base and glues; the consistency of two such prescriptions along a nested
pair `Z ≤ V` of affine opens is
`Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart`, which asks the invertible
module over `Z` to be the inverse image of the one over `V` **on the nose**. On the overlap
`V_i ∩ V_j` of two affine opens of the base that cannot be arranged: an affine open `Z` of the
overlap receives two inverse images, one from each side, and they are isomorphic rather than
equal. `resLE_relativeChart_of_iso` is the same consistency with the module over `Z` freed to be
any invertible module isomorphic to the inverse image, which is the shape the overlap comparison
can use.

## The route

The morphism of Tag 01NK is glued from the charts `T_{ψ(f)} ⟶ D₊(f) ⊆ Proj A`, and a chart is
built from the family of ratios `a / f ^ n ↦ ψ(a) / ψ(f ^ n)`. A ratio of two sections of one
invertible module is unchanged by an isomorphism of that module —
`Stacks.AlgebraicGeometry.ProjChartGradedVeronese.ratioOf_iso` — so the families of ratios of `ψ`
and of `β ∘ ψ` are literally the same family (`homogeneousRatios_congrModule`), hence so are the
charts, hence so are the glued morphisms. The only bookkeeping is that the two glued morphisms
have the two opens `U(β ∘ ψ)` and `U(ψ)` for source, and those are equal rather than identical, so
every statement below is an equality after composing with the inclusion of the one in the other.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homogeneousRatios_congrModule` and
  `…chartToProj_congrModule`: the family of ratios, and the chart of a homogeneous element, are
  unchanged by the transport.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homOfLE_glued_of_le`: `r_{L, ψ}`
  restricts to the chart of `f` on *any* open on which `ψ(f)` does not vanish, not only on
  `T_{ψ(f)}`.
* `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homOfLE_glued_congrModule`:
  **the morphism `r_{L, ψ}` of [Stacks, Tag 01NK] is unchanged by the transport.**
* `Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport.coveringOpen_comap_congrModule` and
  `…coveringOpen_comap_le_preimage_of_iso`: the open `U(χ ∘ φ)` is unchanged by the transport, so
  it lies in `j^{-1}(U(ψ))` already when the values of `χ ∘ φ` are those of `ψ` pulled back along
  `j` *up to* an isomorphism of the module of `χ` with the inverse image.
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.homOfLE_relativeChart_congrModule`: the same
  for the relative morphism of clause (3) of [Stacks, Tag 01O9].
* `Stacks.AlgebraicGeometry.RelativeProjFromSections.resLE_relativeChart_of_iso`:
  **the consistency of the clause (3) prescriptions of [Stacks, Tag 01O9] along a nested pair of
  affine opens of the base, with the module over the smaller one only isomorphic to the inverse
  image.**

## Implementation notes

The hypothesis of `resLE_relativeChart_of_iso` is stated with the isomorphism `β : M ≅ j^*L`
pointing *at* the inverse image and applied to the values of `χ ∘ res`, rather than with
`β : j^*L ≅ M` applied to the pulled-back values of `ψ`. The two are interchangeable, but the
first makes the transported datum `congrModule β χ` have exactly the values the hypothesis names,
so the hypothesis of `resLE_relativeChart` holds for it by `rfl`; with the other orientation it
holds only after cancelling `β` against `β⁻¹` on global sections of tensor powers.

`homogeneousRatios_congrModule` is an equality of structures, and the private `ext` lemma it uses
is available because `Stacks.MorphismToProj.HomogeneousRatios` carries one datum field and three
propositions.

## The tag

The whole statement of [Stacks, Tag 01O9] is
`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.tag01O9`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (ratioOf_iso)
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartFullGraded

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace GradedSections

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- Two families of homogeneous ratios with the same values are equal: the remaining fields are
propositions. -/
private theorem homogeneousRatios_ext {d : ℕ} {g : A} {hg : g ∈ 𝒜 d} {P : Type*} [CommRing P]
    (R R' : HomogeneousRatios 𝒜 hg P) (h : R.toFun = R'.toFun) : R = R' := by
  obtain ⟨t, h1, h2, h3⟩ := R
  obtain ⟨t', h1', h2', h3'⟩ := R'
  simp only at h
  subst h
  rfl

section Congr

variable {T : Scheme.{u}} {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  [Stacks.Ample.IsInvertibleModule T L'] (β : L ≅ L') (ψ : GradedSections 𝒜 L)

/-- **The family of homogeneous ratios is unchanged by transport along an isomorphism of
invertible modules.** -/
theorem homogeneousRatios_congrModule {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
    (hV' : V ≤ nonvanishingOpen T (natTensorPow L' e) ((congrModule β ψ).toFun e ⟨f, hf⟩)) :
    (congrModule β ψ).homogeneousRatios hf hV' = ψ.homogeneousRatios hf hV := by
  refine homogeneousRatios_ext _ _ (funext fun n => AddMonoidHom.ext fun a => ?_)
  rw [homogeneousRatios_toFun, homogeneousRatios_toFun]
  exact ratioOf_iso L L' (natTensorPowCongr β (n * e)) _ _
    (ψ.le_nonvanishingOpen_pow hf hV n) ((congrModule β ψ).le_nonvanishingOpen_pow hf hV' n)

/-- **The chart of a homogeneous element is unchanged by transport along an isomorphism of
invertible modules.** -/
theorem chartToProj_congrModule {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
    (hV' : V ≤ nonvanishingOpen T (natTensorPow L' e) ((congrModule β ψ).toFun e ⟨f, hf⟩)) :
    (congrModule β ψ).chartToProj hf hV' he = ψ.chartToProj hf hV he :=
  congrArg (fun R : HomogeneousRatios 𝒜 hf ↥Γ(T, V) => R.chartToProj he)
    (homogeneousRatios_congrModule β ψ hf hV hV')

end Congr

section Restrict

variable {T : Scheme.{u}} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections 𝒜 L)

/-- **`r_{L, ψ}` restricts to the chart of `f` on *any* open on which `ψ(f)` does not vanish**,
not only on `T_{ψ(f)}` itself. This is `homOfLE_glued_of_pos` followed by
`homOfLE_chartToProj`. -/
theorem homOfLE_glued_of_le {e : ℕ} {f : A} (hf : f ∈ 𝒜 e) (he : 0 < e) {V : T.Opens}
    (hV : V ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩))
    (hVU : V ≤ ψ.coveringOpen) :
    T.homOfLE hVU ≫ ψ.glued = ψ.chartToProj hf hV he := by
  rw [show T.homOfLE hVU
        = T.homOfLE hV ≫ T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he) from
      (T.homOfLE_homOfLE hV (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos hf he)).symm,
    Category.assoc, ψ.homOfLE_glued_of_pos hf he,
    ψ.homOfLE_chartToProj hf (le_refl _) he hV]

end Restrict

section GluedCongr

variable {T : Scheme.{u}} {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  [Stacks.Ample.IsInvertibleModule T L'] (β : L ≅ L') (ψ : GradedSections 𝒜 L)

/-- **The morphism `r_{L, ψ}` of [Stacks, Tag 01NK] is unchanged by transport of the datum along
an isomorphism `β : L ≅ L'` of invertible modules.** The two morphisms have the two opens
`U(β ∘ ψ)` and `U(ψ)` for source, and those are equal (`coveringOpen_congrModule`), so the
statement is an equality after composing with the inclusion of the one in the other. -/
theorem homOfLE_glued_congrModule :
    T.homOfLE (le_of_eq (coveringOpen_congrModule β ψ)) ≫ ψ.glued = (congrModule β ψ).glued := by
  refine (congrModule β ψ).eq_glued_of_homOfLE_eq fun e f hf he => ?_
  have hV : nonvanishingOpen T (natTensorPow L' e) ((congrModule β ψ).toFun e ⟨f, hf⟩)
      ≤ nonvanishingOpen T (natTensorPow L e) (ψ.toFun e ⟨f, hf⟩) :=
    le_of_eq (nonvanishingOpenAt_congrModule β ψ e ⟨f, hf⟩)
  rw [← Category.assoc, T.homOfLE_homOfLE _ _]
  exact (ψ.homOfLE_glued_of_le hf he hV _).trans
    (chartToProj_congrModule β ψ hf he hV (le_refl _)).symm

end GluedCongr

end GradedSections

end Stacks.AlgebraicGeometry.ProjChartFullGraded

/-! ### Transport across `comap`, and the open `U(χ ∘ res)` -/

namespace Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections
  (congrModule nonvanishingOpenAt_congrModule)
open Stacks.AlgebraicGeometry.ProjChartGradedPullback (coveringOpen_le_preimage)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {M : T'.Modules}
  [Stacks.Ample.IsInvertibleModule T' M] (β : M ≅ (Scheme.Modules.pullback j).obj L)
  (χ : GradedSections ℬ M)

/-- **Transport along an isomorphism of invertible modules does not move `U(χ ∘ φ)`.** Restricting
the arguments of a datum along a graded ring map and transporting its module along an isomorphism
are independent operations, and the second leaves every nonvanishing open where it was. -/
theorem coveringOpen_comap_congrModule :
    (comap φ (congrModule β χ)).coveringOpen = (comap φ χ).coveringOpen :=
  iSup_congr fun p =>
    nonvanishingOpenAt_congrModule β χ (p.1 + 1) (φ.gradedAddHom (p.1 + 1) p.2)

/-- **`U(χ ∘ φ)` lies in `j^{-1}(U(ψ))` when the values of `χ ∘ φ` are those of `ψ` pulled back
along `j` *up to an isomorphism* `β` of the module of `χ` with the literal inverse image.** This is
`Stacks.AlgebraicGeometry.ProjChartGradedPullback.coveringOpen_le_preimage` for the transported
datum, whose `U` is the same open by `coveringOpen_comap_congrModule`. -/
theorem coveringOpen_comap_le_preimage_of_iso
    (hχ : ∀ (n : ℕ) (a : 𝒜 n),
      (Stacks.AmplePullbackPart1.natTensorPowCongr β n).hom.app ⊤ ((comap φ χ).toFun n a)
        = pullSection j L n (ψ.toFun n a)) :
    (comap φ χ).coveringOpen ≤ j ⁻¹ᵁ ψ.coveringOpen :=
  (le_of_eq (coveringOpen_comap_congrModule φ j β χ).symm).trans
    (coveringOpen_le_preimage j L ψ (comap φ (congrModule β χ)) hχ)

end Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport

/-! ### The relative morphism, and clause (3) consistency up to an isomorphism -/

namespace Stacks.AlgebraicGeometry.RelativeProjFromSections

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections
  (congrModule coveringOpen_congrModule homOfLE_glued_congrModule)
open Stacks.AlgebraicGeometry.ProjChartGradedIsoTransport (coveringOpen_comap_congrModule
  coveringOpen_comap_le_preimage_of_iso)
open Stacks.AlgebraicGeometry.ProjChartGradedPullback (coveringOpen_le_preimage)
open Stacks.AlgebraicGeometry.ProjChartGradedRingFunctoriality (comap coveringOpen_le)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

section IsoTransport

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (rp : RelativeProjData A)
  (V : S.Opens) (hV : IsAffineOpen V)
  {T : Scheme.{u}} {L L' : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  [Stacks.Ample.IsInvertibleModule T L']

/-- **The relative morphism of clause (3) is unchanged by transport of its datum along an
isomorphism of invertible modules**, the two sources being the one open `U(ψ)`. -/
theorem homOfLE_relativeChart_congrModule (β : L ≅ L') (ψ : GradedSections (A.grading V) L) :
    T.homOfLE (le_of_eq (coveringOpen_congrModule β ψ)) ≫ relativeChart rp V hV ψ
      = relativeChart rp V hV (congrModule β ψ) := by
  unfold relativeChart
  rw [← Category.assoc, homOfLE_glued_congrModule]

end IsoTransport

section BaseRestrictionIso

variable {S : Scheme.{u}} {A : SheafGradedAlgebra S} (rp : RelativeProjData A)
  {Z V : S.Opens} (h : Z ≤ V) (hZ : IsAffineOpen Z) (hV : IsAffineOpen V)
  {T T' : Scheme.{u}} (j : T' ⟶ T) {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : GradedSections (A.grading V) L) {M : T'.Modules}
  [Stacks.Ample.IsInvertibleModule T' M] (β : M ≅ (Scheme.Modules.pullback j).obj L)
  (χ : GradedSections (A.grading Z) M)
  (hχ : ∀ (n : ℕ) (a : A.grading V n),
    (Stacks.AmplePullbackPart1.natTensorPowCongr β n).hom.app ⊤ ((comap (A.res h) χ).toFun n a)
      = pullSection j L n (ψ.toFun n a))

include hχ

/-- **Stacks Project, Tag 01O9: the morphism of clause (3) commutes with restriction of the base
to a smaller affine open, the module over the smaller one being only *isomorphic* to the inverse
image.**

Let `Z ⊆ V` be affine opens of `S`, let `ψ` be a Tag 01NK datum for the graded ring `𝒜(V)` on a
scheme `T` with invertible module `L`, let `j : T' ⟶ T` be a morphism of schemes, and let `χ` be a
Tag 01NK datum for `𝒜(Z)` on `T'` with an invertible module `M` carrying an isomorphism
`β : M ≅ j^*L`, under which the values of `χ` on the image of `𝒜(V) → 𝒜(Z)` are the values of `ψ`
pulled back along `j`. Then

`(U(χ ∘ res) ⟶ U(χ)) ≫ r_{M, χ} ≫ i_Z  =  (j : U(χ ∘ res) ⟶ U(ψ)) ≫ r_{L, ψ} ≫ i_V`,

where `i_V` and `i_Z` are the charts of `Proj_S(𝒜)` of Tag 01NQ.

This is `resLE_relativeChart` with the module over `Z` freed from being the inverse image on the
nose: `β` transports `χ` to a datum for `j^*L` by
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.congrModule`, and the transport moves
neither the opens (`coveringOpen_congrModule`) nor the morphism
(`homOfLE_glued_congrModule`). -/
theorem resLE_relativeChart_of_iso :
    T'.homOfLE (coveringOpen_le (A.res h) χ) ≫ relativeChart rp Z hZ χ
      = j.resLE ψ.coveringOpen (comap (A.res h) χ).coveringOpen
          (coveringOpen_comap_le_preimage_of_iso (A.res h) j ψ β χ hχ)
        ≫ relativeChart rp V hV ψ := by
  have hcov := coveringOpen_comap_congrModule (A.res h) j β χ
  have key := resLE_relativeChart rp h hZ hV j ψ (congrModule β χ) hχ
  have e1 : T'.homOfLE (coveringOpen_le (A.res h) χ) ≫ relativeChart rp Z hZ χ
      = T'.homOfLE (le_of_eq hcov.symm)
          ≫ (T'.homOfLE (coveringOpen_le (A.res h) (congrModule β χ))
              ≫ relativeChart rp Z hZ (congrModule β χ)) := by
    rw [← homOfLE_relativeChart_congrModule rp Z hZ β χ, ← Category.assoc, ← Category.assoc,
      T'.homOfLE_homOfLE, T'.homOfLE_homOfLE]
  have e2 : T'.homOfLE (le_of_eq hcov.symm)
        ≫ (j.resLE ψ.coveringOpen (comap (A.res h) (congrModule β χ)).coveringOpen
              (coveringOpen_le_preimage j L ψ (comap (A.res h) (congrModule β χ)) hχ)
            ≫ relativeChart rp V hV ψ)
      = j.resLE ψ.coveringOpen (comap (A.res h) χ).coveringOpen
            (coveringOpen_comap_le_preimage_of_iso (A.res h) j ψ β χ hχ)
          ≫ relativeChart rp V hV ψ := by
    rw [← Category.assoc, Scheme.Hom.map_resLE]
  exact (e1.trans (congrArg (fun k => T'.homOfLE (le_of_eq hcov.symm) ≫ k) key)).trans e2

end BaseRestrictionIso

end Stacks.AlgebraicGeometry.RelativeProjFromSections

end
