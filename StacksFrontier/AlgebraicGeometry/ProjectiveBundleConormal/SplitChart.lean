module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.AffineZeroSection
public import StacksFrontier.RingTheory.SymmetricAlgebra.SplitAway

/-!
# The standard chart of a projective bundle at a split degree-one element, as a scheme

Let `A` be a commutative ring, `M` an `A`-module, `p : M →ₗ[A] A` a linear form and `s : M` an
element with `p s = 1`, so that `p` is a split surjection and `M = K ⊕ A·s` for
`K = LinearMap.ker p`. `SymmetricAlgebra.splitAwayEquiv` identifies the degree-zero homogeneous
localization of `Sym_A(M)` away from the degree-one element `ι s` with `Sym_A(K)`. This file
carries that identification across `Spec`:

  **`𝐀(K) = Spec (Sym_A K)` is the standard open `D₊(ι s)` of `𝐏(M) = Proj (Sym_A M)`.**

That is `Stacks.ProjectiveBundleConormal.splitChartMap`, an open immersion with image exactly
`D₊(ι s)`; in this chart the section of `𝐏(M)` cut out by `p` is the **zero section** of the
affine bundle.

## Main definitions

* `Stacks.ProjectiveBundleConormal.splitChartRingIso`: the chart identification of
  `SymmetricAlgebra.splitAwayEquiv` read in `CommRingCat`.
* `Stacks.ProjectiveBundleConormal.splitChartMap`: **the chart** `Spec (Sym_A K) ⟶ Proj (Sym_A M)`.
* `Stacks.ProjectiveBundleConormal.splitChartOrigin`: the `A`-point of the chart at which every
  affine coordinate vanishes, as a ring map `(Sym_A M)_{(ι s)} ⟶ A`.
* `Stacks.ProjectiveBundleConormal.liftSplitChart`: a morphism into `Proj(Sym_A M)` landing in
  `D₊(ι s)`, read as a morphism into the affine bundle.

## Main results

* `Stacks.ProjectiveBundleConormal.isOpenImmersion_splitChartMap` and
  `Stacks.ProjectiveBundleConormal.opensRange_splitChartMap`: **the chart is an open immersion
  onto `D₊(ι s)`**.
* `Stacks.ProjectiveBundleConormal.splitChartMap_comp_toSpecZero`: the chart lies over the base,
  i.e. the composite with `AlgebraicGeometry.Proj.toSpecZero` is a `Spec.map`.
* `Stacks.ProjectiveBundleConormal.liftSplitChart_comp_splitChartMap`: that reading is a
  factorization of the given morphism through the chart.
* `Stacks.ProjectiveBundleConormal.eq_of_comp_splitChartMap_eq`: **a point of the affine bundle
  is determined by its image in `Proj`**, the chart being a monomorphism;
  `Stacks.ProjectiveBundleConormal.liftSplitChart_unique` is the same fact stated for the
  factorization.
* `Stacks.ProjectiveBundleConormal.zeroSection_comp_splitChartMap`: **the zero section read in
  `Proj`.** Composing the chart with `Stacks.ProjectiveBundleConormal.zeroSection` is
  `Spec.map` of `splitChartOrigin` followed by `AlgebraicGeometry.Proj.awayι`.
* `Stacks.ProjectiveBundleConormal.splitChartOrigin_mk`: **the normalisation.**
  `splitChartOrigin` sends the class of `a / (ι s)^n` to `SymmetricAlgebra.lift p a`.
* `Stacks.ProjectiveBundleConormal.splitChartOrigin_mk_ι`: every affine coordinate `ι k / ι s`
  of the chart vanishes at the origin.

## Implementation notes

The chart of `Proj 𝒜` at a homogeneous element of positive degree is
`AlgebraicGeometry.Proj.awayι`, an open immersion by instance with
`AlgebraicGeometry.Proj.opensRange_awayι` identifying its image as
`AlgebraicGeometry.Proj.basicOpen`; under the splitting its ring is `Sym_A(K)`, by
`SymmetricAlgebra.splitAwayEquiv`.

**The degree is presented as the literal `1`.** `AlgebraicGeometry.Proj.awayι` asks for
`f ∈ 𝒜 m` together with `0 < m`, so the membership is taken in the form
`SymmetricAlgebra.ι_mem_grading_one` and not in the `n • 1` shape that
`HomogeneousLocalization.Away.mk` wants; the two are interchanged by
`SymmetricAlgebra.mem_grading_nsmul` where a fraction has to be written down.

The value of `splitChartOrigin` is computed on a class `a / (ι s)^n`, by
`SymmetricAlgebra.algebraMapInv_comp_splitAwayEquiv`; every element of the chart ring is such a
class (`HomogeneousLocalization.Away.mk_surjective`), so this determines the map.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
* [Stacks Project, Tag 01OA](https://stacks.math.columbia.edu/tag/01OA)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization SymmetricAlgebra

universe u

namespace Stacks.ProjectiveBundleConormal

variable {A : Type u} [CommRing A] {M : Type u} [AddCommGroup M] [Module A M]
  (p : M →ₗ[A] A) (s : M) (hps : p s = 1)

/-! ### The chart ring -/

/-- The chart identification `(Sym_A M)_{(ι s)} ≅ Sym_A(K)` of
`SymmetricAlgebra.splitAwayEquiv`, read as an isomorphism of `CommRingCat`. -/
def splitChartRingIso :
    CommRingCat.of (Away (grading A M) (ι A M s)) ≅ symRing A (LinearMap.ker p) where
  hom := CommRingCat.ofHom (splitAwayEquiv p s hps).toRingHom
  inv := CommRingCat.ofHom (splitAwayEquiv p s hps).symm.toRingHom
  hom_inv_id := CommRingCat.hom_ext (RingHom.ext fun x =>
    (splitAwayEquiv p s hps).symm_apply_apply x)
  inv_hom_id := CommRingCat.hom_ext (RingHom.ext fun x =>
    (splitAwayEquiv p s hps).apply_symm_apply x)

/-! ### The chart as an open immersion into `Proj` -/

/-- **The standard chart of `𝐏(M) = Proj(Sym_A M)` at the split degree-one element `s`.** It is
the affine bundle `𝐀(K) = Spec (Sym_A K)` on `K = ker p`, embedded as the standard open
`D₊(ι s)`. -/
def splitChartMap : Spec (symRing A (LinearMap.ker p)) ⟶ Proj (grading A M) :=
  Spec.map (splitChartRingIso p s hps).hom ≫
    Proj.awayι (grading A M) (ι A M s) (ι_mem_grading_one s) Nat.one_pos

/-- The chart is an open immersion: `AlgebraicGeometry.Proj.awayι` is one, and the chart
identification is an isomorphism. -/
instance isOpenImmersion_splitChartMap : IsOpenImmersion (splitChartMap p s hps) := by
  rw [splitChartMap]
  infer_instance

/-- **The chart covers exactly `D₊(ι s)`.** -/
theorem opensRange_splitChartMap :
    (splitChartMap p s hps).opensRange = Proj.basicOpen (grading A M) (ι A M s) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans
    (Proj.opensRange_awayι (grading A M) (ι A M s) (ι_mem_grading_one s) Nat.one_pos)

/-- **The chart lies over the base**: composing with `AlgebraicGeometry.Proj.toSpecZero` is the
spectrum of a ring map out of the degree-zero part. -/
theorem splitChartMap_comp_toSpecZero :
    splitChartMap p s hps ≫ Proj.toSpecZero (grading A M) =
      Spec.map (CommRingCat.ofHom
          (fromZeroRingHom (grading A M) (Submonoid.powers (ι A M s))) ≫
        (splitChartRingIso p s hps).hom) := by
  rw [splitChartMap, Category.assoc,
    Proj.awayι_toSpecZero (grading A M) (ι A M s) (ι_mem_grading_one s) Nat.one_pos,
    ← Spec.map_comp]

/-! ### Factoring a morphism that lands in the chart -/

/-- **A morphism into `Proj(Sym_A M)` landing in `D₊(ι s)` is a morphism into the affine bundle**
`Spec (Sym_A K)`: its factorization through the chart. -/
def liftSplitChart {Y : Scheme.{u}} (g : Y ⟶ Proj (grading A M))
    (hg : g ⁻¹ᵁ Proj.basicOpen (grading A M) (ι A M s) = ⊤) :
    Y ⟶ Spec (symRing A (LinearMap.ker p)) :=
  IsOpenImmersion.lift (f := splitChartMap p s hps) (g := g) (by
    rintro _ ⟨y, rfl⟩
    have hy : y ∈ g ⁻¹ᵁ Proj.basicOpen (grading A M) (ι A M s) := by rw [hg]; trivial
    exact (opensRange_splitChartMap p s hps).ge hy)

/-- `Stacks.ProjectiveBundleConormal.liftSplitChart` followed by the chart is the given
morphism. -/
@[simp] theorem liftSplitChart_comp_splitChartMap {Y : Scheme.{u}} (g : Y ⟶ Proj (grading A M))
    (hg : g ⁻¹ᵁ Proj.basicOpen (grading A M) (ι A M s) = ⊤) :
    liftSplitChart p s hps g hg ≫ splitChartMap p s hps = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The factorization is the only one**, the chart being an open immersion. -/
theorem liftSplitChart_unique {Y : Scheme.{u}} (g : Y ⟶ Proj (grading A M))
    (hg : g ⁻¹ᵁ Proj.basicOpen (grading A M) (ι A M s) = ⊤)
    (l : Y ⟶ Spec (symRing A (LinearMap.ker p)))
    (hl : l ≫ splitChartMap p s hps = g) :
    l = liftSplitChart p s hps g hg :=
  IsOpenImmersion.lift_uniq _ _ _ l hl

/-- **Two points of the affine bundle agreeing in `Proj` are equal.** The chart being an open
immersion, hence a monomorphism, a morphism to `Spec (Sym_A K)` is determined by its composite
with the chart. -/
theorem eq_of_comp_splitChartMap_eq {Y : Scheme.{u}}
    {l₁ l₂ : Y ⟶ Spec (symRing A (LinearMap.ker p))}
    (h : l₁ ≫ splitChartMap p s hps = l₂ ≫ splitChartMap p s hps) :
    l₁ = l₂ :=
  (cancel_mono (splitChartMap p s hps)).mp h

/-! ### The origin of the chart -/

/-- **The `A`-point of the chart at which every affine coordinate vanishes**, as a ring map
`(Sym_A M)_{(ι s)} ⟶ A`: the chart identification followed by the augmentation of `Sym_A(K)`.
Its spectrum is the zero section of the affine bundle, read in the chart. -/
def splitChartOrigin : CommRingCat.of (Away (grading A M) (ι A M s)) ⟶ CommRingCat.of A :=
  (splitChartRingIso p s hps).hom ≫ augRingHom A (LinearMap.ker p)

/-- **The normalisation of the origin**: it sends the class of `a / (ι s)^n`, for `a` homogeneous
of degree `n`, to `SymmetricAlgebra.lift p a`. -/
theorem splitChartOrigin_mk (n : ℕ) (a : SymmetricAlgebra A M) (ha : a ∈ grading A M (n • 1)) :
    (splitChartOrigin p s hps).hom
        (Away.mk (grading A M) (ι_mem_grading_one s) n a ha) =
      SymmetricAlgebra.lift p a :=
  algebraMapInv_comp_splitAwayEquiv p s hps n a ha

/-- **Every affine coordinate of the chart vanishes at the origin**: the class `ι k / ι s`, for
`k ∈ K`, goes to `0`. -/
theorem splitChartOrigin_mk_ι (k : LinearMap.ker p) :
    (splitChartOrigin p s hps).hom
        (Away.mk (grading A M) (ι_mem_grading_one s) 1 (ι A M (k : M))
          (ι_mem_grading_smul _)) = 0 := by
  rw [splitChartOrigin_mk, SymmetricAlgebra.lift_ι_apply]
  exact k.2

/-- **The zero section read in `Proj`.** The zero section of the affine bundle `𝐀(K)`, followed by
the chart, is the `A`-point `Stacks.ProjectiveBundleConormal.splitChartOrigin` of the standard
open `D₊(ι s)`. -/
theorem zeroSection_comp_splitChartMap :
    zeroSection A (LinearMap.ker p) ≫ splitChartMap p s hps =
      Spec.map (splitChartOrigin p s hps) ≫
        Proj.awayι (grading A M) (ι A M s) (ι_mem_grading_one s) Nat.one_pos := by
  rw [splitChartMap, splitChartOrigin, Spec.map_comp, Category.assoc]

end Stacks.ProjectiveBundleConormal

end
