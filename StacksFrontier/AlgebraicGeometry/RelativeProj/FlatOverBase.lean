module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Flat
public import StacksFrontier.RingTheory.HomogeneousLocalization.AwayFlatOverBase
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness of `Proj` over a base ring smaller than its degree-zero part

Let `𝒜` be a nonnegatively graded ring and let `b : R ⟶ 𝒜 0` be a ring map from a base ring `R`.
The composite `Proj 𝒜 ⟶ Spec (𝒜 0) ⟶ Spec R` is flat as soon as every standard affine chart of
`Proj 𝒜` is flat over `R`, which is again a statement about the degree-zero localizations
`HomogeneousLocalization.Away 𝒜 (g i)` — this time as algebras over `R` rather than over `𝒜 0`.

For a relative `Proj` this gives flatness of the structure morphism from flatness of the charts
over the rings of sections of the base, with no assumption that the degree-zero identifications
`Data.base U : Γ(S, U) ⟶ 𝒜 U 0` are isomorphisms: the degree-zero part `𝒜₀` may be an arbitrary
quasi-coherent `𝒪_S`-algebra, as in [Stacks, Tag 0D4C].

## Main results

* `AlgebraicGeometry.Proj.flat_toSpecZero_comp_of_flat_away`: `Proj 𝒜 ⟶ Spec R` is flat when each
  standard chart is flat over `R`.
* `AlgebraicGeometry.Proj.irrelevant_le_span_homogeneous` and
  `AlgebraicGeometry.Proj.iSup_basicOpen_homogeneous_eq_top`: the homogeneous elements of positive
  degree span the irrelevant ideal, so their standard opens cover `Proj 𝒜`.
* `Stacks.RelativeProj.Data.flat_toBase_of_flat_away'`: the structure morphism of a relative
  `Proj` is flat when each standard chart of each local `Proj` is flat over the ring of sections
  of the base. No invertibility of the degree-zero identifications is assumed.

## Implementation notes

Flatness of a chart over `R` is stated as `RingHom.Flat` of the composite ring map
`R → 𝒜 0 → Away 𝒜 (g i)` rather than as `Module.Flat R (Away 𝒜 (g i))`: there is no canonical
`R`-module structure on the degree-zero localization in the instance graph, since it depends on
`b`, and `RingHom.Flat` is exactly the predicate the morphism-property API for
`AlgebraicGeometry.Flat` produces for `Spec` of a ring map.

## References

* [Stacks Project, Tag 0D4C](https://stacks.math.columbia.edu/tag/0D4C)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Flatness over `R` of the charts `D₊(g i)` of a cover gives flatness of `Proj 𝒜 ⟶ Spec R`. -/
private theorem flat_toSpecZero_comp_of_iSup_basicOpen_eq_top {R : CommRingCat.{u}}
    (b : R ⟶ CommRingCat.of (𝒜 0)) {ι : Type*} (g : ι → A) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hg : ∀ i, g i ∈ 𝒜 (m i))
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (g i)) = ⊤)
    (hflat : ∀ i, RingHom.Flat
      ((fromZeroRingHom 𝒜 (Submonoid.powers (g i))).comp b.hom)) :
    Flat (Proj.toSpecZero 𝒜 ≫ Spec.map b) := by
  have hsrc : IsZariskiLocalAtSource @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat)
  have := hsrc.toRespects
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Flat) _
    (hcover)]
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Flat)
    (Proj.basicOpenIsoSpec 𝒜 (g i) (hg i) (hm i)).inv, ← Category.assoc, ← Category.assoc,
    ← Proj.awayι, Proj.awayι_toSpecZero, ← Spec.map_comp,
    HasRingHomProperty.Spec_iff (P := @Flat)]
  exact hflat i

/-- **`Proj 𝒜` is flat over `Spec R` as soon as all of its standard affine charts are.**

Here `b : R ⟶ 𝒜 0` is an arbitrary map from the base ring to the degree-zero part, and flatness
of the chart over `D₊(g i)` is flatness of the ring map `R → 𝒜 0 → Away 𝒜 (g i)`. -/
theorem flat_toSpecZero_comp_of_flat_away {R : CommRingCat.{u}}
    (b : R ⟶ CommRingCat.of (𝒜 0)) {ι : Type*} (g : ι → A) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hg : ∀ i, g i ∈ 𝒜 (m i))
    (hadj : Algebra.adjoin (𝒜 0) (Set.range g) = ⊤)
    (hflat : ∀ i, RingHom.Flat
      ((fromZeroRingHom 𝒜 (Submonoid.powers (g i))).comp b.hom)) :
    Flat (Proj.toSpecZero 𝒜 ≫ Spec.map b) := by
  exact flat_toSpecZero_comp_of_iSup_basicOpen_eq_top 𝒜 b g m hm hg
    (Proj.iSup_basicOpen_eq_top' 𝒜 g (fun i ↦ ⟨_, hg i⟩) hadj) hflat

/-- The same criterion with the covering hypothesis in the form `AlgebraicGeometry.Proj` uses for
its affine open covers: the homogeneous elements `g i` of positive degree span the irrelevant
ideal. -/
theorem flat_toSpecZero_comp_of_flat_away' {R : CommRingCat.{u}}
    (b : R ⟶ CommRingCat.of (𝒜 0)) {ι : Type*} (g : ι → A) (m : ι → ℕ)
    (hm : ∀ i, 0 < m i) (hg : ∀ i, g i ∈ 𝒜 (m i))
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span (Set.range g))
    (hflat : ∀ i, RingHom.Flat
      ((fromZeroRingHom 𝒜 (Submonoid.powers (g i))).comp b.hom)) :
    Flat (Proj.toSpecZero 𝒜 ≫ Spec.map b) := by
  exact flat_toSpecZero_comp_of_iSup_basicOpen_eq_top 𝒜 b g m hm hg
    (Proj.iSup_basicOpen_eq_top 𝒜 g hspan) hflat

/-- **The homogeneous elements of positive degree span the irrelevant ideal.** -/
theorem irrelevant_le_span_homogeneous :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range fun i : Σ m : ℕ+, 𝒜 (m : ℕ) ↦ (i.2 : A)) := by
  classical
  intro z hz
  rw [← DirectSum.sum_support_decompose 𝒜 z]
  refine Ideal.sum_mem _ fun c hc ↦ if hc0 : c = 0 then ?_ else
    Ideal.subset_span ⟨⟨⟨c, Nat.pos_iff_ne_zero.mpr hc0⟩, _⟩, rfl⟩
  convert! Ideal.zero_mem _
  subst hc0
  exact hz

/-- **The standard opens at the homogeneous elements of positive degree cover `Proj 𝒜`.** -/
@[ega "II 3.1.6" "special case"]
theorem iSup_basicOpen_homogeneous_eq_top :
    (⨆ i : Σ m : ℕ+, 𝒜 (m : ℕ), Proj.basicOpen 𝒜 (i.2 : A)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top 𝒜 _ (irrelevant_le_span_homogeneous 𝒜)

/-- **`Proj 𝒜` is flat over `Spec R` as soon as every standard affine chart at a homogeneous
element of positive degree is.** No covering hypothesis is needed. -/
theorem flat_toSpecZero_comp_of_flat_away_forall {R : CommRingCat.{u}}
    (b : R ⟶ CommRingCat.of (𝒜 0))
    (hflat : ∀ (m : ℕ+) (f : 𝒜 (m : ℕ)), RingHom.Flat
      ((fromZeroRingHom 𝒜 (Submonoid.powers (f : A))).comp b.hom)) :
    Flat (Proj.toSpecZero 𝒜 ≫ Spec.map b) :=
  flat_toSpecZero_comp_of_flat_away' 𝒜 b (ι := Σ i : ℕ+, 𝒜 (i : ℕ))
    (fun i ↦ (i.2 : A)) (fun i ↦ (i.1 : ℕ)) (fun i ↦ i.1.2) (fun i ↦ i.2.2)
    (irrelevant_le_span_homogeneous 𝒜) fun i ↦ hflat i.1 i.2

end AlgebraicGeometry.Proj

namespace Stacks.RelativeProj.Data

variable {S : Scheme.{u}} {A σ : S.affineOpens → Type u} [∀ U, CommRing (A U)]
  [∀ U, SetLike (σ U) (A U)] [∀ U, AddSubgroupClass (σ U) (A U)]
  {𝒜 : ∀ U, ℕ → σ U} [∀ U, GradedRing (𝒜 U)] (d : Data 𝒜)

/-- **The structure morphism of a relative `Proj` is flat as soon as all the standard affine
charts of all the local `Proj`s are flat over the ring of sections of the base.** Unlike
`Stacks.RelativeProj.Data.flat_toBase_of_flat_away`, this does not assume that the degree-zero
identifications `Data.base U` are isomorphisms. -/
theorem flat_toBase_of_flat_away' {ι : S.affineOpens → Type*} (g : ∀ U, ι U → A U)
    (m : ∀ U, ι U → ℕ) (hm : ∀ U i, 0 < m U i) (hg : ∀ U i, g U i ∈ 𝒜 U (m U i))
    (hadj : ∀ U, Algebra.adjoin (𝒜 U 0) (Set.range (g U)) = ⊤)
    (hflat : ∀ (U : S.affineOpens) (i : ι U), RingHom.Flat
      ((fromZeroRingHom (𝒜 U) (Submonoid.powers (g U i))).comp (d.base U).hom)) :
    Flat d.toBase := by
  have hloc : IsZariskiLocalAtTarget @Flat :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat)
  have := hloc.toRespects
  refine d.prop_toBase @Flat fun U ↦ ?_
  rw [chartToOpen, ← Category.assoc,
    MorphismProperty.cancel_right_of_respectsIso (P := @Flat) _ (isAffineOpen U).isoSpec.inv]
  exact Proj.flat_toSpecZero_comp_of_flat_away (𝒜 U) (d.base U) (g U) (m U) (hm U) (hg U)
    (hadj U) (hflat U)

end Stacks.RelativeProj.Data

end
