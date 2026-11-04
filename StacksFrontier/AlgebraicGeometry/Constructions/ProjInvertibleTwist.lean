module

public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.AlgebraicGeometry.Blowup.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeScaling
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualBijective
public import StacksFrontier.AlgebraicGeometry.SegreGlue.Overlap

/-!
# Twisting a graded ring by an invertible module does not change `Proj`

Let `R` be a commutative ring, let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded `R`-algebra and let `ℒ` be an
invertible `R`-module. Tensoring the homogeneous pieces with the tensor powers of `ℒ` gives
another graded `R`-algebra `B = ⨁_{d ≥ 0} 𝒜 d ⊗_R ℒ^{⊗ d}`, and the two have canonically
isomorphic homogeneous spectra over `Spec R`.

The tensor powers and their coherent multiplications are packaged as a family
`𝓛 : ℕ → Submodule R T` of `R`-submodules of an `R`-algebra `T` with `𝓛 0 = R`, with
`𝓛 i * 𝓛 j = 𝓛 (i + j)`, and with the multiplication map `𝓛 i ⊗_R 𝓛 j → T` injective: then
`𝓛 d` is the `d`-th tensor power of `ℒ = 𝓛 1` and every coherence isomorphism is multiplication
in `T`. The twisted algebra is presented by a family of `R`-linear isomorphisms
`𝒜 d ⊗_R 𝓛 d ≅ ℬ d` carrying products of pure tensors to products.

The isomorphism of homogeneous spectra is proved for `ℒ = 𝓛 1` **invertible**, which is the
hypothesis of [Stacks, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC); no global generator
is assumed. For a degree-one element `ℓ` that generates `𝓛 1` the comparison `x ↦ x ⊗ ℓ ^ d` is
an isomorphism of graded rings and induces an isomorphism of homogeneous spectra directly; in
general the isomorphism is glued from the morphisms that the individual degree-one elements
induce on their own domains of definition.

Tag 02NC is stated over an arbitrary base scheme `S`, for a quasi-coherent graded `𝒪_S`-algebra `𝒜`
and an invertible `𝒪_S`-module `ℒ`. This file treats the **absolute** case: `R` a commutative ring,
`𝒜` a graded `R`-algebra, `ℒ` an invertible `R`-module, and `Proj` the absolute homogeneous
spectrum. Clause (1) of the tag, the comparison maps on the twisting sheaves, is proved here for a
twisting module with a global generator, as `Stacks.GradedRing.InvertibleTwist.isIso_twistMap`.

**How the general case goes.** Nothing in the formula `x ↦ x ⊗ ℓ ^ d` requires `ℓ` to generate:
it is a homomorphism of graded rings `ψ_ℓ : 𝒜 →+*ᵍ ℬ` for *every* `ℓ ∈ 𝓛 1`
(`Stacks.GradedRing.InvertibleTwist.twistHomOf`), inducing a morphism to `Proj 𝒜` on the open
`U(ψ_ℓ) ⊆ Proj ℬ` of `Stacks.AlgebraicGeometry.ProjShared.mapDomain`. Three facts assemble those
into one isomorphism. *Compatibility*: for `a` and `b` of the same degree,
`ψ_ℓ a * ψ_{ℓ'} b = ψ_{ℓ'} a * ψ_ℓ b`
(`Stacks.GradedRing.InvertibleTwist.twistHomOf_mul_comm`), which is exactly
`Stacks.AlgebraicGeometry.SegreGlue.CrossComm` and makes the chart morphisms agree on overlaps.
*Covering*: invertibility of `𝓛 1` gives a finite family of pairs `(μ, m)` of a functional and
an element with `∑ μ m = 1` (`Stacks.GradedRing.exists_finset_dual_sum_eq_one`), and for
`r = μ m` multiplication by `r ^ d` carries `𝓛 d` into `R · m ^ d`
(`Stacks.GradedRing.IsTensorPowerFamily.exists_smul_pow_eq`) — so `r ^ d • y = ψ_m x` for
`y ∈ ℬ d`, and a point omitting a positive-degree `y` omits some `ψ_m x`. *Invertibility*: over
the standard open of `r • a` the map `𝒜_{(r • a)} → ℬ_{(ψ_m (r • a))}` of degree-zero
localizations is bijective, surjectively because of the same trivialization and injectively
because the `d`-th power of `μ` recovers `r ^ d`
(`Stacks.GradedRing.IsTensorPowerFamily.dualPow`); those opens cover `Proj 𝒜`, and being an
isomorphism is local at the target.

The symmetry `μ x • y = μ y • x` that makes a single functional trivialize the whole family comes
for free from the setting: multiplication realizes `𝓛 1 ⊗_R 𝓛 1` inside the *commutative* ring
`T` injectively, so the tensor square is symmetric
(`Stacks.GradedRing.IsTensorPowerFamily.tmul_comm_one`).

## Main definitions

* `Stacks.GradedRing.IsTensorPowerFamily`: the family `𝓛` is the family of tensor powers of the
  invertible module `𝓛 1`; `Stacks.GradedRing.invertible_of_bijective_toSpanSingleton` records
  that a module with a generator is invertible, which is the hypothesis of the tag on `ℒ`.
* `Stacks.GradedRing.IsTensorPowerFamily.dualPow`: the `d`-th tensor power of a functional on
  `𝓛 1`, a functional on `𝓛 d`, with
  `Stacks.GradedRing.IsTensorPowerFamily.smul_pow_eq_dualPow_smul`: it computes the coordinate
  of a section of `𝓛 d` in the basis `ℓ ^ d` that
  `Stacks.GradedRing.IsTensorPowerFamily.exists_smul_pow_eq` only asserts to exist.
* `Stacks.GradedRing.InvertibleTwist`: `ℬ` is the twist of `𝒜` by `𝓛`, that is, `ℬ d` is
  `𝒜 d ⊗_R 𝓛 d` compatibly with the products and the units.
* `Stacks.GradedRing.InvertibleTwist.pieceEquiv`: for a generator `ℓ` of `𝓛 1`, the induced
  isomorphism `𝒜 d ≅ ℬ d` of homogeneous pieces, `x ↦ x ⊗ ℓ ^ d`, and
  `Stacks.GradedRing.InvertibleTwist.pieceMap`: the same formula for an arbitrary `ℓ ∈ 𝓛 1`,
  where it is a linear map but need not be bijective.
* `Stacks.GradedRing.InvertibleTwist.twistHom`: the resulting isomorphism `𝒜 →+*ᵍ ℬ` of graded
  rings, with inverse `Stacks.GradedRing.InvertibleTwist.twistHomInv`, and
  `Stacks.GradedRing.InvertibleTwist.twistHomOf`: the homomorphism of graded rings attached to an
  arbitrary `ℓ ∈ 𝓛 1`, with no generation hypothesis.
* `Stacks.GradedRing.InvertibleTwist.chartFamily`: the charts `D₊(ψ_ℓ f)` covering `Proj ℬ`, and
  `Stacks.GradedRing.InvertibleTwist.projTwistGlued`: the morphism `Proj ℬ ⟶ Proj 𝒜` glued from
  the chart morphisms.
* `Stacks.GradedRing.InvertibleTwist.projTwistIsoGeneral`: **the canonical isomorphism
  `Proj ℬ ≅ Proj 𝒜` for an invertible twisting module**, and
  `Stacks.GradedRing.InvertibleTwist.projTwistIso`: the same for a twisting module with a global
  generator, where it is `Proj` of an isomorphism of graded rings.

## Main results

* `Stacks.GradedRing.InvertibleTwist.isIso_projTwistGlued`: the glued morphism is an isomorphism.
* `Stacks.GradedRing.InvertibleTwist.ι_comp_projTwistGlued`: on the domain of definition of the
  comparison attached to *any* degree-one element the glued isomorphism is that comparison; this
  is what makes it canonical.
* `Stacks.GradedRing.InvertibleTwist.projTwistGlued_toSpecZero`: the isomorphism is one over the
  base, that is, it commutes with the two structure morphisms to `Spec` of the degree-zero parts.
* `Stacks.GradedRing.InvertibleTwist.bijective_awayMap_twistHomOf`: the map of degree-zero
  homogeneous localizations is bijective over the standard open of `(μ ℓ) • a`.
* `Stacks.GradedRing.InvertibleTwist.iSup_basicOpen_twistHomOf_eq_top`: the charts cover.
* `Stacks.GradedRing.InvertibleTwist.isIso_twistMap`: every comparison map on the `n`-th twisting
  sheaf is an isomorphism, for a twisting module with a global generator. This is clause (1) of
  Tag 02NC in the trivialized case.
* `Stacks.GradedRing.InvertibleTwist.projTwist_eq_of_generators`: the morphism of homogeneous
  spectra is the same for any two generators of `𝓛 1`.
* `Stacks.GradedRing.InvertibleTwist.twistHom_eq_twistHomOf`: in the generated case the
  unconditional comparison is the comparison of `twistHom`.
* `Stacks.GradedRing.InvertibleTwist.twistHomOf_mul_comm`: the symmetry identity of two
  degree-one elements.
* `Stacks.GradedRing.bijective_toSpanSingleton_of_surjective`: for an invertible module, an
  element that generates it already satisfies the bijectivity hypothesis above.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 07ZE](https://stacks.math.columbia.edu/tag/07ZE)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory AlgebraicGeometry DirectSum Graded HomogeneousIdeal
open scoped TensorProduct

namespace Stacks.GradedRing

variable {R A B T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing T]
  [Algebra R A] [Algebra R B] [Algebra R T]

/-! ### Rank-one modules with a chosen generator -/

/-- A module with a generator `g` for which scalar multiplication by `g` is bijective is free of
rank one, hence invertible. -/
theorem invertible_of_bijective_toSpanSingleton {M : Type u} [AddCommGroup M] [Module R M]
    {g : M} (hg : Function.Bijective (LinearMap.toSpanSingleton R M g)) :
    Module.Invertible R M :=
  Module.Invertible.congr (LinearEquiv.ofBijective _ hg)

/-- **Two generators of a rank-one module differ by a unit of the base ring.** -/
theorem exists_unit_smul_of_bijective_toSpanSingleton {M : Type u} [AddCommGroup M] [Module R M]
    {g g' : M} (hg : Function.Bijective (LinearMap.toSpanSingleton R M g))
    (hg' : Function.Bijective (LinearMap.toSpanSingleton R M g')) :
    ∃ u : Rˣ, g' = (u : R) • g := by
  obtain ⟨u, hu⟩ := hg.surjective g'
  obtain ⟨v, hv⟩ := hg'.surjective g
  have hu' : u • g = g' := hu
  have h1 : v * u = 1 := hg.injective <| by
    show (v * u) • g = (1 : R) • g
    rw [mul_smul, hu', one_smul]
    exact hv
  exact ⟨⟨u, v, (mul_comm u v).trans h1, h1⟩, hu'.symm⟩

/-! ### Families of tensor powers of an invertible module -/

/-- A family `𝓛 : ℕ → Submodule R T` of `R`-submodules of an `R`-algebra `T` **is the family of
tensor powers** of its degree-one member: the degree-zero member is `R`, the product of the
degree-`i` and the degree-`j` member is the degree-`(i + j)` member, and the multiplication map
`𝓛 i ⊗_R 𝓛 j → T` is injective, so that it realizes `𝓛 i ⊗_R 𝓛 j ≅ 𝓛 (i + j)`. -/
structure IsTensorPowerFamily (𝓛 : ℕ → Submodule R T) : Prop where
  /-- The structure map of `T` is injective, so that `𝓛 0 = R` is a copy of `R`. -/
  algebraMap_injective : Function.Injective (algebraMap R T)
  /-- The degree-zero member is the image of `R`. -/
  degree_zero : 𝓛 0 = 1
  /-- The members multiply additively in the degree. -/
  mul_eq (i j : ℕ) : 𝓛 i * 𝓛 j = 𝓛 (i + j)
  /-- Multiplication realizes the tensor product of two members. -/
  mulMap_injective (i j : ℕ) : Function.Injective (Submodule.mulMap (𝓛 i) (𝓛 j))

namespace IsTensorPowerFamily

variable {𝓛 : ℕ → Submodule R T} (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ : T}

include h𝓛

/-- The unit of `T` lies in the degree-zero member of the family. -/
theorem one_mem_zero : (1 : T) ∈ 𝓛 0 := by
  rw [h𝓛.degree_zero]
  exact Submodule.mem_one.mpr ⟨1, map_one _⟩

/-- Powers of a degree-one element have the corresponding degree. -/
theorem pow_mem (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) : ℓ ^ d ∈ 𝓛 d := by
  induction d with
  | zero => simpa using h𝓛.one_mem_zero
  | succ d ih =>
      rw [pow_succ, ← h𝓛.mul_eq d 1]
      exact Submodule.mul_mem_mul ih hℓ

/-- Multiplication is injective from the tensor product onto the product submodule. -/
theorem mulMap'_injective (i j : ℕ) :
    Function.Injective (Submodule.mulMap' (𝓛 i) (𝓛 j)) :=
  fun _ _ hxy ↦ h𝓛.mulMap_injective i j (congrArg Subtype.val hxy)

/-- **Multiplication realizes the tensor product of two members of the family**: the induced map
`𝓛 i ⊗_R 𝓛 j → 𝓛 (i + j)` is an isomorphism of `R`-modules. -/
def mulEquiv (i j : ℕ) : (𝓛 i) ⊗[R] (𝓛 j) ≃ₗ[R] (𝓛 (i + j)) :=
  (LinearEquiv.ofBijective (Submodule.mulMap' (𝓛 i) (𝓛 j))
    ⟨h𝓛.mulMap'_injective i j, Submodule.mulMap'_surjective _ _⟩).trans
      (LinearEquiv.ofEq _ _ (h𝓛.mul_eq i j))

/-- The isomorphism `mulEquiv` sends a pure tensor `x ⊗ y` to the product `x * y`. -/
theorem coe_mulEquiv_tmul (i j : ℕ) (x : 𝓛 i) (y : 𝓛 j) :
    (h𝓛.mulEquiv i j (x ⊗ₜ[R] y) : T) = (x : T) * y := rfl

/-- The degree-zero member of the family is free of rank one on the unit. -/
private theorem bijective_toSpanSingleton_zero_aux :
    Function.Bijective (LinearMap.toSpanSingleton R (𝓛 0) ⟨1, h𝓛.one_mem_zero⟩) := by
  have hval : ∀ r : R,
      ((LinearMap.toSpanSingleton R (𝓛 0) ⟨1, h𝓛.one_mem_zero⟩) r : T) = algebraMap R T r := by
    intro r
    show r • (1 : T) = algebraMap R T r
    rw [Algebra.smul_def, mul_one]
  refine ⟨fun r s hrs => h𝓛.algebraMap_injective ?_, fun x => ?_⟩
  · rw [← hval r, ← hval s, hrs]
  · have hx : (x : T) ∈ (1 : Submodule R T) := by rw [← h𝓛.degree_zero]; exact x.2
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hx
    exact ⟨r, Subtype.ext ((hval r).trans hr)⟩

/-- **A generator in degree one generates every degree.** If `ℓ` generates `𝓛 1` then `𝓛 d` is
free of rank one on `ℓ ^ d`. -/
theorem exists_linearEquiv_pow (hℓ : ℓ ∈ 𝓛 1)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩)) (d : ℕ) :
    ∃ e : R ≃ₗ[R] (𝓛 d), (e 1 : T) = ℓ ^ d := by
  have he1 : ((LinearEquiv.ofBijective _ hgen) (1 : R) : T) = ℓ :=
    congrArg Subtype.val (LinearMap.toSpanSingleton_apply_one _ _ _)
  induction d with
  | zero =>
      refine ⟨LinearEquiv.ofBijective _ h𝓛.bijective_toSpanSingleton_zero_aux, ?_⟩
      exact (congrArg Subtype.val (LinearMap.toSpanSingleton_apply_one _ _ _)).trans
        (pow_zero ℓ).symm
  | succ d ih =>
      obtain ⟨ed, hed⟩ := ih
      refine ⟨(TensorProduct.lid R R).symm.trans
        ((TensorProduct.congr ed (LinearEquiv.ofBijective _ hgen)).trans (h𝓛.mulEquiv d 1)), ?_⟩
      rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, TensorProduct.lid_symm_apply,
        TensorProduct.congr_tmul, h𝓛.coe_mulEquiv_tmul, hed, he1, pow_succ]

/-- **Scalar multiplication by `ℓ ^ d` is a bijection `R → 𝓛 d`** when `ℓ` generates `𝓛 1`. -/
theorem bijective_toSpanSingleton_pow (hℓ : ℓ ∈ 𝓛 1)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩)) (d : ℕ) :
    Function.Bijective (LinearMap.toSpanSingleton R (𝓛 d) ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩) := by
  obtain ⟨e, he⟩ := h𝓛.exists_linearEquiv_pow hℓ hgen d
  have hfun : ∀ r : R,
      (LinearMap.toSpanSingleton R (𝓛 d) ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩) r = e r := by
    intro r
    have h2 : e r = r • e 1 := by rw [← map_smul]; congr 1; simp
    rw [show (LinearMap.toSpanSingleton R (𝓛 d) ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩) r =
      r • (⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ : 𝓛 d) from rfl, h2]
    congr 1
    exact Subtype.ext he.symm
  have hcoe : (LinearMap.toSpanSingleton R (𝓛 d) ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ :
      R → (𝓛 d)) = (e : R → (𝓛 d)) := funext hfun
  rw [hcoe]
  exact e.bijective

end IsTensorPowerFamily

/-! ### The twisted graded ring -/

/-- **`ℬ` is the twist of `𝒜` by the family `𝓛` of tensor powers of an invertible module**: the
degree-`d` piece of `ℬ` is `𝒜 d ⊗_R 𝓛 d`, the product of two pure tensors is the pure tensor of
the two products, and the unit is the pure tensor of the two units.

This is the graded algebra `ℬ = ⨁_d 𝒜_d ⊗ ℒ^{⊗ d}` of the setting of Tag 02NB, written at the
level of graded rings. -/
structure InvertibleTwist (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (𝓛 : ℕ → Submodule R T)
    (ℬ : ℕ → Submodule R B) [GradedAlgebra ℬ] where
  /-- The degree-`d` piece of `ℬ` is `𝒜 d ⊗_R 𝓛 d`. -/
  piece (d : ℕ) : (𝒜 d) ⊗[R] (𝓛 d) ≃ₗ[R] (ℬ d)
  /-- The comparison carries a product of pure tensors to the product. -/
  piece_mul (i j : ℕ) (x : 𝒜 i) (y : 𝒜 j) (l : 𝓛 i) (m : 𝓛 j)
      (hlm : (l : T) * m ∈ 𝓛 (i + j)) :
    (piece (i + j) (⟨(x : A) * y, SetLike.mul_mem_graded x.2 y.2⟩ ⊗ₜ[R] ⟨(l : T) * m, hlm⟩) : B) =
      (piece i (x ⊗ₜ[R] l) : B) * (piece j (y ⊗ₜ[R] m) : B)
  /-- The comparison carries the pure tensor of the units to the unit. -/
  piece_one (h0 : (1 : T) ∈ 𝓛 0) :
    (piece 0 (⟨1, SetLike.one_mem_graded 𝒜⟩ ⊗ₜ[R] ⟨1, h0⟩) : B) = 1

namespace InvertibleTwist

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {𝓛 : ℕ → Submodule R T}
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ] (tw : InvertibleTwist 𝒜 𝓛 ℬ)
  (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ : T} {hℓ : ℓ ∈ 𝓛 1}
  (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩))

/-- Multiplicativity of `x ↦ x ⊗ ℓ ^ d` on pieces, for any `ℓ ∈ 𝓛 1`. -/
private theorem piece_pow_mul (i j : ℕ) (x : 𝒜 i) (y : 𝒜 j) :
    (tw.piece (i + j) (⟨(x : A) * y, SetLike.mul_mem_graded x.2 y.2⟩ ⊗ₜ[R]
        ⟨ℓ ^ (i + j), h𝓛.pow_mem hℓ (i + j)⟩) : B) =
      (tw.piece i (x ⊗ₜ[R] ⟨ℓ ^ i, h𝓛.pow_mem hℓ i⟩) : B) *
        (tw.piece j (y ⊗ₜ[R] ⟨ℓ ^ j, h𝓛.pow_mem hℓ j⟩) : B) := by
  have hlm : (ℓ ^ i) * (ℓ ^ j) ∈ 𝓛 (i + j) := by
    rw [← pow_add]; exact h𝓛.pow_mem hℓ (i + j)
  have hpow : (⟨ℓ ^ (i + j), h𝓛.pow_mem hℓ (i + j)⟩ : 𝓛 (i + j)) = ⟨(ℓ ^ i) * (ℓ ^ j), hlm⟩ :=
    Subtype.ext (pow_add ℓ i j)
  rw [hpow]
  exact tw.piece_mul i j x y ⟨ℓ ^ i, h𝓛.pow_mem hℓ i⟩ ⟨ℓ ^ j, h𝓛.pow_mem hℓ j⟩ hlm

/-- Unitality of `x ↦ x ⊗ ℓ ^ d` on pieces, for any `ℓ ∈ 𝓛 1`. -/
private theorem piece_pow_zero :
    (tw.piece 0 (⟨1, SetLike.one_mem_graded 𝒜⟩ ⊗ₜ[R] ⟨ℓ ^ 0, h𝓛.pow_mem hℓ 0⟩) : B) = 1 := by
  have h0 : (⟨ℓ ^ 0, h𝓛.pow_mem hℓ 0⟩ : 𝓛 0) = ⟨1, h𝓛.one_mem_zero⟩ := Subtype.ext (pow_zero ℓ)
  rw [h0]
  exact tw.piece_one h𝓛.one_mem_zero

include tw h𝓛 hgen

/-- **The comparison of homogeneous pieces attached to a generator `ℓ` of `𝓛 1`**: the
isomorphism `𝒜 d ≅ ℬ d` given by `x ↦ x ⊗ ℓ ^ d`. -/
def pieceEquiv (d : ℕ) : (𝒜 d) ≃ₗ[R] (ℬ d) :=
  ((TensorProduct.rid R (𝒜 d)).symm.trans (TensorProduct.congr (LinearEquiv.refl R (𝒜 d))
    (LinearEquiv.ofBijective _ (h𝓛.bijective_toSpanSingleton_pow hℓ hgen d)))).trans (tw.piece d)

/-- The comparison of pieces sends `x ∈ 𝒜 d` to the piece of `ℬ d` given by `x ⊗ ℓ ^ d`. -/
theorem pieceEquiv_apply (d : ℕ) (x : 𝒜 d) :
    tw.pieceEquiv h𝓛 hgen d x = tw.piece d (x ⊗ₜ[R] ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩) := by
  have h1 : (LinearEquiv.ofBijective _
      (h𝓛.bijective_toSpanSingleton_pow hℓ hgen d) (1 : R) : 𝓛 d) =
      ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ := LinearMap.toSpanSingleton_apply_one _ _ _
  rw [pieceEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    TensorProduct.rid_symm_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply, h1]

/-- The comparison of pieces is multiplicative. -/
theorem pieceEquiv_gMul (i j : ℕ) (x : 𝒜 i) (y : 𝒜 j) :
    (tw.pieceEquiv h𝓛 hgen (i + j) ⟨(x : A) * y, SetLike.mul_mem_graded x.2 y.2⟩ : B) =
      (tw.pieceEquiv h𝓛 hgen i x : B) * (tw.pieceEquiv h𝓛 hgen j y : B) := by
  rw [tw.pieceEquiv_apply h𝓛 hgen, tw.pieceEquiv_apply h𝓛 hgen, tw.pieceEquiv_apply h𝓛 hgen]
  exact tw.piece_pow_mul h𝓛 (hℓ := hℓ) i j x y

/-- The comparison of pieces is unital. -/
theorem pieceEquiv_one :
    (tw.pieceEquiv h𝓛 hgen 0 ⟨1, SetLike.one_mem_graded 𝒜⟩ : B) = 1 := by
  rw [tw.pieceEquiv_apply h𝓛 hgen]
  exact tw.piece_pow_zero h𝓛 (hℓ := hℓ)

/-! ### The comparison homomorphism of graded rings -/

/-- The comparison of pieces as an additive map to `B`. -/
def twistFamily (d : ℕ) : (𝒜 d) →+ B :=
  ((ℬ d).subtype.comp (tw.pieceEquiv h𝓛 hgen d).toLinearMap).toAddMonoidHom

/-- `twistFamily d` is the comparison of pieces in degree `d`, viewed in `B`. -/
theorem twistFamily_apply (d : ℕ) (x : 𝒜 d) :
    tw.twistFamily h𝓛 hgen d x = (tw.pieceEquiv h𝓛 hgen d x : B) := rfl

/-- The ring homomorphism `⨁ d, 𝒜 d →+* B` which is the comparison of pieces in each degree. -/
def twistAux : (⨁ d, (𝒜 d)) →+* B :=
  DirectSum.toSemiring (tw.twistFamily h𝓛 hgen)
    (tw.pieceEquiv_one h𝓛 hgen)
    fun {i j} x y ↦ tw.pieceEquiv_gMul h𝓛 hgen i j x y

/-- On the degree-`d` summand, `twistAux` is the comparison of pieces in degree `d`. -/
theorem twistAux_of (d : ℕ) (x : 𝒜 d) :
    tw.twistAux h𝓛 hgen (DirectSum.of _ d x) = (tw.pieceEquiv h𝓛 hgen d x : B) :=
  DirectSum.toSemiring_of (tw.twistFamily h𝓛 hgen) _ _ d x

/-- **The comparison homomorphism of graded rings `𝒜 →+*ᵍ ℬ` attached to a generator `ℓ` of
`𝓛 1`**: on the degree-`d` piece it is `x ↦ x ⊗ ℓ ^ d`. -/
def twistHom : 𝒜 →+*ᵍ ℬ where
  toRingHom := (tw.twistAux h𝓛 hgen).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom
  map_mem {i x} hx := by
    change tw.twistAux h𝓛 hgen (DirectSum.decompose 𝒜 x) ∈ ℬ i
    rw [DirectSum.decompose_of_mem 𝒜 hx, tw.twistAux_of h𝓛 hgen]
    exact (tw.pieceEquiv h𝓛 hgen i ⟨x, hx⟩).2

/-- On a homogeneous element of degree `d`, `twistHom` is the comparison of pieces in degree
`d`. -/
theorem twistHom_coe (d : ℕ) (x : 𝒜 d) :
    tw.twistHom h𝓛 hgen (x : A) = (tw.pieceEquiv h𝓛 hgen d x : B) := by
  show tw.twistAux h𝓛 hgen (DirectSum.decompose 𝒜 (x : A)) = _
  rw [DirectSum.decompose_of_mem 𝒜 x.2, tw.twistAux_of h𝓛 hgen]

/-- `twistHom` sends an element `a ∈ 𝒜 i` to the piece of `ℬ i` given by `a ⊗ ℓ ^ i`. -/
theorem twistHom_apply_of_mem {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    tw.twistHom h𝓛 hgen a = (tw.piece i (⟨a, ha⟩ ⊗ₜ[R] ⟨ℓ ^ i, h𝓛.pow_mem hℓ i⟩) : B) := by
  have h := tw.twistHom_coe h𝓛 hgen i ⟨a, ha⟩
  rwa [tw.pieceEquiv_apply h𝓛 hgen i ⟨a, ha⟩] at h

/-- The degree-`d` component of `twistHom` is the comparison of pieces `pieceEquiv d`. -/
theorem gradedAddHom_twistHom (d : ℕ) (x : 𝒜 d) :
    GradedRingHom.gradedAddHom (tw.twistHom h𝓛 hgen) d x = tw.pieceEquiv h𝓛 hgen d x :=
  Subtype.ext (tw.twistHom_coe h𝓛 hgen d x)

/-- **The comparison homomorphism is bijective in every degree.** -/
theorem bijective_gradedAddHom_twistHom (d : ℕ) :
    Function.Bijective (GradedRingHom.gradedAddHom (tw.twistHom h𝓛 hgen) d) := by
  have h : (GradedRingHom.gradedAddHom (tw.twistHom h𝓛 hgen) d : (𝒜 d) → (ℬ d)) =
      (tw.pieceEquiv h𝓛 hgen d : (𝒜 d) → (ℬ d)) :=
    funext (tw.gradedAddHom_twistHom h𝓛 hgen d)
  rw [h]
  exact (tw.pieceEquiv h𝓛 hgen d).bijective

/-- **The comparison homomorphism is surjective**, since it is surjective in every degree. -/
theorem surjective_twistHom : Function.Surjective (tw.twistHom h𝓛 hgen) := by
  classical
  intro b
  refine ⟨∑ d ∈ (DirectSum.decompose ℬ b).support,
    (((tw.pieceEquiv h𝓛 hgen d).symm (DirectSum.decompose ℬ b d) : A)), ?_⟩
  rw [map_sum]
  conv_rhs => rw [← DirectSum.sum_support_decompose ℬ b]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [tw.twistHom_coe h𝓛 hgen d, LinearEquiv.apply_symm_apply]

/-- The side condition of `AlgebraicGeometry.Proj.map` for the comparison homomorphism. -/
theorem irrelevant_le_map_twistHom : ℬ₊ ≤ 𝒜₊.map (tw.twistHom h𝓛 hgen) :=
  AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ (tw.surjective_twistHom h𝓛 hgen)

/-! ### The inverse comparison -/

/-- The inverse comparison of pieces as an additive map to `A`. -/
def twistFamilyInv (d : ℕ) : (ℬ d) →+ A :=
  ((𝒜 d).subtype.comp (tw.pieceEquiv h𝓛 hgen d).symm.toLinearMap).toAddMonoidHom

/-- The ring homomorphism `⨁ d, ℬ d →+* A` which is the inverse comparison in each degree. -/
def twistAuxInv : (⨁ d, (ℬ d)) →+* A :=
  DirectSum.toSemiring (tw.twistFamilyInv h𝓛 hgen)
    (by
      change ((tw.pieceEquiv h𝓛 hgen 0).symm ⟨1, SetLike.one_mem_graded ℬ⟩ : A) = 1
      have h : (tw.pieceEquiv h𝓛 hgen 0) ⟨1, SetLike.one_mem_graded 𝒜⟩ =
          ⟨1, SetLike.one_mem_graded ℬ⟩ := Subtype.ext (tw.pieceEquiv_one h𝓛 hgen)
      rw [← h, LinearEquiv.symm_apply_apply])
    fun {i j} y z ↦ by
      change ((tw.pieceEquiv h𝓛 hgen (i + j)).symm
        ⟨(y : B) * z, SetLike.mul_mem_graded y.2 z.2⟩ : A) = _
      have key : (tw.pieceEquiv h𝓛 hgen (i + j))
          ⟨(((tw.pieceEquiv h𝓛 hgen i).symm y : 𝒜 i) : A) *
            (((tw.pieceEquiv h𝓛 hgen j).symm z : 𝒜 j) : A),
            SetLike.mul_mem_graded ((tw.pieceEquiv h𝓛 hgen i).symm y).2
              ((tw.pieceEquiv h𝓛 hgen j).symm z).2⟩ =
          ⟨(y : B) * z, SetLike.mul_mem_graded y.2 z.2⟩ := by
        refine Subtype.ext ?_
        rw [tw.pieceEquiv_gMul h𝓛 hgen i j, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply]
      rw [← key, LinearEquiv.symm_apply_apply]
      rfl

/-- On the degree-`d` summand, `twistAuxInv` is the inverse of the comparison of pieces in degree
`d`. -/
theorem twistAuxInv_of (d : ℕ) (y : ℬ d) :
    tw.twistAuxInv h𝓛 hgen (DirectSum.of _ d y) =
      ((tw.pieceEquiv h𝓛 hgen d).symm y : A) :=
  DirectSum.toSemiring_of (tw.twistFamilyInv h𝓛 hgen) _ _ d y

/-- **The inverse comparison homomorphism of graded rings `ℬ →+*ᵍ 𝒜`.** -/
def twistHomInv : ℬ →+*ᵍ 𝒜 where
  toRingHom := (tw.twistAuxInv h𝓛 hgen).comp (DirectSum.decomposeRingEquiv ℬ).toRingHom
  map_mem {i y} hy := by
    change tw.twistAuxInv h𝓛 hgen (DirectSum.decompose ℬ y) ∈ 𝒜 i
    rw [DirectSum.decompose_of_mem ℬ hy, tw.twistAuxInv_of h𝓛 hgen]
    exact ((tw.pieceEquiv h𝓛 hgen i).symm ⟨y, hy⟩).2

/-- On a homogeneous element of degree `d`, `twistHomInv` is the inverse of the comparison of
pieces in degree `d`. -/
theorem twistHomInv_coe (d : ℕ) (y : ℬ d) :
    tw.twistHomInv h𝓛 hgen (y : B) = ((tw.pieceEquiv h𝓛 hgen d).symm y : A) := by
  show tw.twistAuxInv h𝓛 hgen (DirectSum.decompose ℬ (y : B)) = _
  rw [DirectSum.decompose_of_mem ℬ y.2, tw.twistAuxInv_of h𝓛 hgen]

/-- `twistHomInv` is a left inverse of `twistHom`. -/
theorem twistHomInv_comp_twistHom :
    (tw.twistHomInv h𝓛 hgen).comp (tw.twistHom h𝓛 hgen) = GradedRingHom.id 𝒜 := by
  refine gradedRingHom_ext 𝒜 fun i a ha ↦ ?_
  have h1 : tw.twistHom h𝓛 hgen a = ((tw.pieceEquiv h𝓛 hgen i ⟨a, ha⟩ : ℬ i) : B) :=
    tw.twistHom_coe h𝓛 hgen i ⟨a, ha⟩
  rw [GradedRingHom.comp_apply, GradedRingHom.id_apply, h1,
    tw.twistHomInv_coe h𝓛 hgen i, LinearEquiv.symm_apply_apply]

/-- `twistHomInv` is a right inverse of `twistHom`. -/
theorem twistHom_comp_twistHomInv :
    (tw.twistHom h𝓛 hgen).comp (tw.twistHomInv h𝓛 hgen) = GradedRingHom.id ℬ := by
  refine gradedRingHom_ext ℬ fun i b hb ↦ ?_
  have h1 : tw.twistHomInv h𝓛 hgen b =
      (((tw.pieceEquiv h𝓛 hgen i).symm ⟨b, hb⟩ : 𝒜 i) : A) :=
    tw.twistHomInv_coe h𝓛 hgen i ⟨b, hb⟩
  rw [GradedRingHom.comp_apply, GradedRingHom.id_apply, h1,
    tw.twistHom_coe h𝓛 hgen i, LinearEquiv.apply_symm_apply]

/-- The inverse comparison homomorphism `twistHomInv` is surjective. -/
theorem surjective_twistHomInv : Function.Surjective (tw.twistHomInv h𝓛 hgen) := fun a ↦
  ⟨tw.twistHom h𝓛 hgen a, by
    have h := GradedRingHom.congr_fun (tw.twistHomInv_comp_twistHom h𝓛 hgen) a
    rwa [GradedRingHom.comp_apply, GradedRingHom.id_apply] at h⟩

/-- The side condition of `AlgebraicGeometry.Proj.map` for the inverse comparison. -/
theorem irrelevant_le_map_twistHomInv : 𝒜₊ ≤ ℬ₊.map (tw.twistHomInv h𝓛 hgen) :=
  AlgebraicGeometry.Proj.irrelevant_le_map_of_surjective _ (tw.surjective_twistHomInv h𝓛 hgen)

/-! ### The isomorphism of homogeneous spectra -/

/-- **The morphism of homogeneous spectra `Proj ℬ ⟶ Proj 𝒜` induced by the comparison.** -/
def projTwist : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜 :=
  AlgebraicGeometry.Proj.map _ (tw.irrelevant_le_map_twistHom h𝓛 hgen)

/-- **The isomorphism `Proj ℬ ≅ Proj 𝒜` for a twisting module with a global generator**: the
source's step 1, "this is the identity map when `ℒ ≅ 𝒪_S`". -/
def projTwistIso : AlgebraicGeometry.Proj ℬ ≅ AlgebraicGeometry.Proj 𝒜 where
  hom := tw.projTwist h𝓛 hgen
  inv := AlgebraicGeometry.Proj.map _ (tw.irrelevant_le_map_twistHomInv h𝓛 hgen)
  hom_inv_id := by
    refine Eq.trans (AlgebraicGeometry.Proj.map_comp (tw.twistHomInv h𝓛 hgen)
      (tw.twistHom h𝓛 hgen) (tw.irrelevant_le_map_twistHomInv h𝓛 hgen)
      (tw.irrelevant_le_map_twistHom h𝓛 hgen)).symm ?_
    exact (AlgebraicGeometry.Proj.map_congr (tw.twistHom_comp_twistHomInv h𝓛 hgen) _
      (by simp)).trans AlgebraicGeometry.Proj.map_id
  inv_hom_id := by
    refine Eq.trans (AlgebraicGeometry.Proj.map_comp (tw.twistHom h𝓛 hgen)
      (tw.twistHomInv h𝓛 hgen) (tw.irrelevant_le_map_twistHom h𝓛 hgen)
      (tw.irrelevant_le_map_twistHomInv h𝓛 hgen)).symm ?_
    exact (AlgebraicGeometry.Proj.map_congr (tw.twistHomInv_comp_twistHom h𝓛 hgen) _
      (by simp)).trans AlgebraicGeometry.Proj.map_id

/-- The forward morphism of `projTwistIso` is `projTwist`. -/
theorem projTwistIso_hom : (tw.projTwistIso h𝓛 hgen).hom = tw.projTwist h𝓛 hgen := rfl

/-- **The isomorphism is one over the base**: it commutes with the two structure morphisms to
`Spec` of the degree-zero parts. This is the triangle of Tag 02NC, in the trivialized case. -/
theorem projTwistIso_hom_toSpecZero :
    (tw.projTwistIso h𝓛 hgen).hom ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜 =
      AlgebraicGeometry.Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom (tw.twistHom h𝓛 hgen).gradedZeroRingHom) :=
  AlgebraicGeometry.Proj.map_toSpecZero _ _

/-- **Clause (1) of Tag 02NC**: the comparison map on the `n`-th twisting sheaf is an
isomorphism, for every `n : ℤ`. Under the global generator `ℓ` the pullback of the `n`-th power
of the twisting module is trivial, so this is the comparison
`g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` of the tag. -/
theorem isIso_twistMap (n : ℤ) :
    IsIso ((Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData 𝒜 ℬ
      (tw.twistHom h𝓛 hgen)).twistMap n) :=
  Stacks.AlgebraicGeometry.RelativeProjChain.isIso_projMapData_twistMap_of_eventually_bijective
    𝒜 ℬ _ (Filter.Eventually.of_forall (tw.bijective_gradedAddHom_twistHom h𝓛 hgen)) n

/-- **The comparison maps of clause (1) live on all of `Proj ℬ`.** The comparison maps of
`Stacks.GradedRing.InvertibleTwist.isIso_twistMap` are maps of sheaves on the domain of
definition `U(ψ) ⊆ Proj ℬ` of the comparison homomorphism; that open is the whole of `Proj ℬ`,
because the comparison homomorphism is surjective. -/
theorem mapDomain_twistHom_eq_top :
    Stacks.AlgebraicGeometry.ProjShared.mapDomain 𝒜 ℬ (tw.twistHom h𝓛 hgen) = ⊤ :=
  Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_surjective 𝒜 ℬ _
    (tw.surjective_twistHom h𝓛 hgen)

/-! ### Independence of the generator -/

/-- **The morphism of homogeneous spectra does not depend on the chosen generator.** Two
generators of `𝓛 1` differ by a unit `u` of `R`, so the two comparison homomorphisms differ by
rescaling the degree-`d` piece of `ℬ` by `u ^ d`, which induces the identity on `Proj ℬ`. -/
theorem projTwist_eq_of_generators {ℓ' : T} {hℓ' : ℓ' ∈ 𝓛 1}
    (hgen' : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ', hℓ'⟩)) :
    tw.projTwist h𝓛 hgen' = tw.projTwist h𝓛 hgen := by
  obtain ⟨u, hu⟩ := exists_unit_smul_of_bijective_toSpanSingleton hgen hgen'
  have hu' : ℓ' = (u : R) • ℓ := congrArg Subtype.val hu
  have hw : (algebraMap R B (u : R)) ∈ ℬ 0 := SetLike.algebraMap_mem_graded ℬ _
  have hw' : (algebraMap R B ((u⁻¹ : Rˣ) : R)) ∈ ℬ 0 := SetLike.algebraMap_mem_graded ℬ _
  have hww' : algebraMap R B (u : R) * algebraMap R B ((u⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, u.mul_inv, map_one]
  show AlgebraicGeometry.Proj.map _ (tw.irrelevant_le_map_twistHom h𝓛 hgen') =
    AlgebraicGeometry.Proj.map _ (tw.irrelevant_le_map_twistHom h𝓛 hgen)
  refine Proj_map_eq_of_target_degreeScale 𝒜 hw hw' hww' _ _
    (tw.irrelevant_le_map_twistHom h𝓛 hgen)
    (tw.irrelevant_le_map_twistHom h𝓛 hgen') fun i a ha ↦ ?_
  have hpow : (⟨ℓ' ^ i, h𝓛.pow_mem hℓ' i⟩ : 𝓛 i) =
      ((u : R) ^ i) • (⟨ℓ ^ i, h𝓛.pow_mem hℓ i⟩ : 𝓛 i) := by
    refine Subtype.ext ?_
    show ℓ' ^ i = ((u : R) ^ i) • ℓ ^ i
    rw [hu', smul_pow]
  rw [tw.twistHom_apply_of_mem h𝓛 hgen' ha, tw.twistHom_apply_of_mem h𝓛 hgen ha, hpow,
    TensorProduct.tmul_smul, map_smul, Submodule.coe_smul, ← map_pow, Algebra.smul_def]

end InvertibleTwist

/-! ### The comparison attached to an arbitrary degree-one element

Nothing in the formula `x ↦ x ⊗ ℓ ^ d` requires `ℓ` to generate `𝓛 1`: the comparison
homomorphism of graded rings `𝒜 →+*ᵍ ℬ` exists for *every* `ℓ ∈ 𝓛 1`, and is bijective exactly
when `ℓ` is a generator. This section records the unconditional homomorphism, identifies it with
`Stacks.GradedRing.InvertibleTwist.twistHom` in the generated case, and proves the symmetry
identity that two degree-one elements satisfy. -/

namespace InvertibleTwist

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {𝓛 : ℕ → Submodule R T}
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ] (tw : InvertibleTwist 𝒜 𝓛 ℬ)
  (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ ℓ' : T}

section Unconditional

include h𝓛

/-- **The comparison of homogeneous pieces attached to an arbitrary element `ℓ` of `𝓛 1`**: the
`R`-linear map `𝒜 d → ℬ d` given by `x ↦ x ⊗ ℓ ^ d`.
`Stacks.GradedRing.InvertibleTwist.pieceEquiv` is this map in the case that `ℓ` generates
`𝓛 1`, where it is moreover bijective. -/
def pieceMap (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) : (𝒜 d) →ₗ[R] (ℬ d) :=
  (tw.piece d).toLinearMap ∘ₗ (TensorProduct.mk R (𝒜 d) (𝓛 d)).flip
    ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩

/-- The comparison of pieces sends `x ∈ 𝒜 d` to the piece of `ℬ d` given by `x ⊗ ℓ ^ d`. -/
theorem pieceMap_apply (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) (x : 𝒜 d) :
    tw.pieceMap h𝓛 hℓ d x = tw.piece d (x ⊗ₜ[R] ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩) :=
  rfl

/-- The unconditional comparison of pieces is multiplicative. -/
theorem pieceMap_gMul (hℓ : ℓ ∈ 𝓛 1) (i j : ℕ) (x : 𝒜 i) (y : 𝒜 j) :
    (tw.pieceMap h𝓛 hℓ (i + j) ⟨(x : A) * y, SetLike.mul_mem_graded x.2 y.2⟩ : B) =
      (tw.pieceMap h𝓛 hℓ i x : B) * (tw.pieceMap h𝓛 hℓ j y : B) := by
  rw [tw.pieceMap_apply h𝓛 hℓ, tw.pieceMap_apply h𝓛 hℓ, tw.pieceMap_apply h𝓛 hℓ]
  exact tw.piece_pow_mul h𝓛 (hℓ := hℓ) i j x y

/-- The unconditional comparison of pieces is unital. -/
theorem pieceMap_one (hℓ : ℓ ∈ 𝓛 1) :
    (tw.pieceMap h𝓛 hℓ 0 ⟨1, SetLike.one_mem_graded 𝒜⟩ : B) = 1 := by
  rw [tw.pieceMap_apply h𝓛 hℓ]
  exact tw.piece_pow_zero h𝓛 (hℓ := hℓ)

/-- The unconditional comparison of pieces as an additive map to `B`. -/
def twistFamilyOf (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) : (𝒜 d) →+ B :=
  ((ℬ d).subtype.comp (tw.pieceMap h𝓛 hℓ d)).toAddMonoidHom

/-- The ring homomorphism `⨁ d, 𝒜 d →+* B` which is the unconditional comparison in each
degree. -/
def twistAuxOf (hℓ : ℓ ∈ 𝓛 1) : (⨁ d, (𝒜 d)) →+* B :=
  DirectSum.toSemiring (tw.twistFamilyOf h𝓛 hℓ)
    (tw.pieceMap_one h𝓛 hℓ)
    fun {i j} x y ↦ tw.pieceMap_gMul h𝓛 hℓ i j x y

/-- On the degree-`d` summand, `twistAuxOf` is the comparison of pieces `pieceMap d`. -/
theorem twistAuxOf_of (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) (x : 𝒜 d) :
    tw.twistAuxOf h𝓛 hℓ (DirectSum.of _ d x) = (tw.pieceMap h𝓛 hℓ d x : B) :=
  DirectSum.toSemiring_of (tw.twistFamilyOf h𝓛 hℓ) _ _ d x

/-- **The comparison homomorphism of graded rings `𝒜 →+*ᵍ ℬ` attached to an arbitrary element
`ℓ` of `𝓛 1`**: on the degree-`d` piece it is `x ↦ x ⊗ ℓ ^ d`. This is the homomorphism Tag 02NC
glues over a family of degree-one elements spanning `𝓛 1`; no generation hypothesis is needed to
form it. -/
def twistHomOf (hℓ : ℓ ∈ 𝓛 1) : 𝒜 →+*ᵍ ℬ where
  toRingHom := (tw.twistAuxOf h𝓛 hℓ).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom
  map_mem {i x} hx := by
    change tw.twistAuxOf h𝓛 hℓ (DirectSum.decompose 𝒜 x) ∈ ℬ i
    rw [DirectSum.decompose_of_mem 𝒜 hx, tw.twistAuxOf_of h𝓛 hℓ]
    exact (tw.pieceMap h𝓛 hℓ i ⟨x, hx⟩).2

/-- On a homogeneous element of degree `d`, `twistHomOf` is the comparison of pieces
`pieceMap d`. -/
theorem twistHomOf_coe (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) (x : 𝒜 d) :
    tw.twistHomOf h𝓛 hℓ (x : A) = (tw.pieceMap h𝓛 hℓ d x : B) := by
  show tw.twistAuxOf h𝓛 hℓ (DirectSum.decompose 𝒜 (x : A)) = _
  rw [DirectSum.decompose_of_mem 𝒜 x.2, tw.twistAuxOf_of h𝓛 hℓ]

/-- `twistHomOf` sends an element `a ∈ 𝒜 i` to the piece of `ℬ i` given by `a ⊗ ℓ ^ i`. -/
theorem twistHomOf_apply_of_mem (hℓ : ℓ ∈ 𝓛 1) {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    tw.twistHomOf h𝓛 hℓ a = (tw.piece i (⟨a, ha⟩ ⊗ₜ[R] ⟨ℓ ^ i, h𝓛.pow_mem hℓ i⟩) : B) := by
  have h := tw.twistHomOf_coe h𝓛 hℓ i ⟨a, ha⟩
  rwa [tw.pieceMap_apply h𝓛 hℓ i ⟨a, ha⟩] at h

/-- **The generated case of the unconditional comparison is the comparison of
`Stacks.GradedRing.InvertibleTwist.twistHom`.** -/
theorem twistHom_eq_twistHomOf {hℓ : ℓ ∈ 𝓛 1}
    (hgen : Function.Bijective (LinearMap.toSpanSingleton R (𝓛 1) ⟨ℓ, hℓ⟩)) :
    tw.twistHom h𝓛 hgen = tw.twistHomOf h𝓛 hℓ :=
  gradedRingHom_ext 𝒜 fun i a ha ↦ by
    rw [tw.twistHom_apply_of_mem h𝓛 hgen ha, tw.twistHomOf_apply_of_mem h𝓛 hℓ ha]

/-- **The symmetry identity of two degree-one elements.** For `a` and `b` homogeneous of the
*same* degree, the two mixed products of their images under the comparisons attached to `ℓ` and
to `ℓ'` agree, both being the image of `a * b` tensored with `ℓ ^ i * ℓ' ^ i`. -/
theorem twistHomOf_mul_comm (hℓ : ℓ ∈ 𝓛 1) (hℓ' : ℓ' ∈ 𝓛 1) {i : ℕ} {a b : A}
    (ha : a ∈ 𝒜 i) (hb : b ∈ 𝒜 i) :
    tw.twistHomOf h𝓛 hℓ a * tw.twistHomOf h𝓛 hℓ' b =
      tw.twistHomOf h𝓛 hℓ' a * tw.twistHomOf h𝓛 hℓ b := by
  have hm : (ℓ ^ i) * (ℓ' ^ i) ∈ 𝓛 (i + i) := by
    rw [← h𝓛.mul_eq i i]
    exact Submodule.mul_mem_mul (h𝓛.pow_mem hℓ i) (h𝓛.pow_mem hℓ' i)
  have hm' : (ℓ' ^ i) * (ℓ ^ i) ∈ 𝓛 (i + i) := by
    rw [← h𝓛.mul_eq i i]
    exact Submodule.mul_mem_mul (h𝓛.pow_mem hℓ' i) (h𝓛.pow_mem hℓ i)
  have hswap : (⟨(ℓ ^ i) * (ℓ' ^ i), hm⟩ : 𝓛 (i + i)) = ⟨(ℓ' ^ i) * (ℓ ^ i), hm'⟩ :=
    Subtype.ext (mul_comm _ _)
  have e1 := tw.piece_mul i i ⟨a, ha⟩ ⟨b, hb⟩ ⟨ℓ ^ i, h𝓛.pow_mem hℓ i⟩
    ⟨ℓ' ^ i, h𝓛.pow_mem hℓ' i⟩ hm
  have e2 := tw.piece_mul i i ⟨a, ha⟩ ⟨b, hb⟩ ⟨ℓ' ^ i, h𝓛.pow_mem hℓ' i⟩
    ⟨ℓ ^ i, h𝓛.pow_mem hℓ i⟩ hm'
  rw [tw.twistHomOf_apply_of_mem h𝓛 hℓ ha, tw.twistHomOf_apply_of_mem h𝓛 hℓ' hb,
    tw.twistHomOf_apply_of_mem h𝓛 hℓ' ha, tw.twistHomOf_apply_of_mem h𝓛 hℓ hb, ← e1, ← e2,
    hswap]

end Unconditional

end InvertibleTwist

/-- **A generator of an invertible module satisfies the bijectivity hypothesis.** For `M`
invertible, a surjection onto `M` from an invertible module — here `R` itself — is automatically
bijective. -/
theorem bijective_toSpanSingleton_of_surjective {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Invertible R M] {g : M}
    (hg : Function.Surjective (LinearMap.toSpanSingleton R M g)) :
    Function.Bijective (LinearMap.toSpanSingleton R M g) :=
  Module.Invertible.bijective_of_surjective hg

/-! ### Trivializing data for an invertible module -/

/-- **An invertible module carries a finite family of pairs `(μ, m)` of a functional and an
element whose values `μ m` sum to one.** The contraction `M^* ⊗_R M → R` is bijective for an
invertible module, so `1` is a finite sum of pure tensors' contractions; the resulting elements
`μ m` generate the unit ideal, and each pair trivializes `M` over the corresponding standard
open. -/
theorem exists_finset_dual_sum_eq_one (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Invertible R M] :
    ∃ s : Finset ((Module.Dual R M) × M), ∑ p ∈ s, p.1 p.2 = 1 := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := R) (M := M)).surjective 1
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset t
  refine ⟨s, ?_⟩
  rw [← ht, hs, map_sum]
  exact Finset.sum_congr rfl fun p _ => contractLeft_apply p.1 p.2

/-- If the values `μ m` over a finite family sum to one, one of them is outside any proper ideal
of an `R`-algebra. -/
private theorem exists_notMem_of_sum_eq_one {M C : Type u} [AddCommGroup M] [Module R M]
    [CommRing C] [Algebra R C] {s : Finset ((Module.Dual R M) × M)} (hs : ∑ p ∈ s, p.1 p.2 = 1)
    {P : Ideal C} (hP : P ≠ ⊤) : ∃ p ∈ s, algebraMap R C (p.1 p.2) ∉ P := by
  by_contra hcon
  refine hP ((Ideal.eq_top_iff_one _).mpr ?_)
  rw [← map_one (algebraMap R C), ← hs, map_sum]
  exact Ideal.sum_mem _ fun p hp => not_not.mp fun hp2 => hcon ⟨p, hp, hp2⟩

namespace IsTensorPowerFamily

variable {𝓛 : ℕ → Submodule R T} (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ : T}

include h𝓛

/-- **The tensor square of the degree-one member of the family is symmetric.** Multiplication
realizes `𝓛 1 ⊗_R 𝓛 1` inside the commutative ring `T`, and is injective, so a pure tensor is
unchanged by exchanging its two factors. -/
theorem tmul_comm_one (x y : 𝓛 1) : x ⊗ₜ[R] y = y ⊗ₜ[R] x := by
  refine h𝓛.mulMap_injective 1 1 ?_
  rw [Submodule.mulMap_tmul, Submodule.mulMap_tmul, mul_comm]

/-- **A functional on `𝓛 1` satisfies `μ x • y = μ y • x`.** This is the symmetry of the tensor
square read through `μ ⊗ id`, and it is what makes a single functional trivialize the whole
family: the submodule `R • x` absorbs `μ x • 𝓛 1`. -/
theorem smul_comm_of_dual (μ : (𝓛 1) →ₗ[R] R) (x y : 𝓛 1) : μ x • y = μ y • x := by
  have key : ∀ a b : 𝓛 1,
      (TensorProduct.lid R (𝓛 1)) (TensorProduct.map μ LinearMap.id (a ⊗ₜ[R] b)) = μ a • b :=
    fun a b => by simp
  rw [← key x y, h𝓛.tmul_comm_one x y, key y x]

/-- **The degree-zero member of the family is free of rank one on the unit.** -/
theorem bijective_toSpanSingleton_zero :
    Function.Bijective (LinearMap.toSpanSingleton R (𝓛 0) ⟨1, h𝓛.one_mem_zero⟩) :=
  h𝓛.bijective_toSpanSingleton_zero_aux

/-- The degree-zero member of the family, identified with the base ring. -/
def zeroEquiv : (𝓛 0) ≃ₗ[R] R :=
  (LinearEquiv.ofBijective _ h𝓛.bijective_toSpanSingleton_zero).symm

/-- The identification of `𝓛 0` with the base ring sends `1` to `1`. -/
theorem zeroEquiv_one : h𝓛.zeroEquiv ⟨1, h𝓛.one_mem_zero⟩ = 1 := by
  have h : (LinearEquiv.ofBijective _ h𝓛.bijective_toSpanSingleton_zero) (1 : R) =
      (⟨1, h𝓛.one_mem_zero⟩ : 𝓛 0) := LinearMap.toSpanSingleton_apply_one _ _ _
  rw [zeroEquiv, LinearEquiv.symm_apply_eq, h]

omit h𝓛 in
/-- **The `d`-th tensor power of a functional on `𝓛 1`**, a functional on `𝓛 d`: the degree-zero
member is the base ring, and the degree-`(d + 1)` member is `𝓛 d ⊗_R 𝓛 1`. -/
def dualPow : (h : IsTensorPowerFamily 𝓛) → ((𝓛 1) →ₗ[R] R) → (d : ℕ) → ((𝓛 d) →ₗ[R] R)
  | h, _, 0 => h.zeroEquiv.toLinearMap
  | h, μ, d + 1 => (TensorProduct.rid R R).toLinearMap ∘ₗ
      TensorProduct.map (dualPow h μ d) μ ∘ₗ (h.mulEquiv d 1).symm.toLinearMap

/-- The zeroth power of a functional is the identification `zeroEquiv` of `𝓛 0` with `R`. -/
theorem dualPow_zero (μ : (𝓛 1) →ₗ[R] R) : dualPow h𝓛 μ 0 = h𝓛.zeroEquiv.toLinearMap := rfl

/-- The `(d + 1)`-th power of `μ` is `dualPow μ d ⊗ μ` on `𝓛 d ⊗_R 𝓛 1 ≅ 𝓛 (d + 1)`. -/
theorem dualPow_succ (μ : (𝓛 1) →ₗ[R] R) (d : ℕ) :
    dualPow h𝓛 μ (d + 1) = (TensorProduct.rid R R).toLinearMap ∘ₗ
      TensorProduct.map (dualPow h𝓛 μ d) μ ∘ₗ (h𝓛.mulEquiv d 1).symm.toLinearMap := rfl

/-- The `(d + 1)`-th power of `μ` sends the product of `x ∈ 𝓛 d` and `y ∈ 𝓛 1` to
`dualPow μ d x * μ y`. -/
theorem dualPow_succ_apply (μ : (𝓛 1) →ₗ[R] R) {d : ℕ} (x : 𝓛 d) (y : 𝓛 1) :
    dualPow h𝓛 μ (d + 1) (h𝓛.mulEquiv d 1 (x ⊗ₜ[R] y)) = dualPow h𝓛 μ d x * μ y := by
  rw [h𝓛.dualPow_succ]
  simp [mul_comm]

/-- The `d`-th power of a functional evaluated on the `d`-th power of a degree-one element is the
`d`-th power of its value. -/
theorem dualPow_pow (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) :
    dualPow h𝓛 μ d ⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ = (μ ⟨ℓ, hℓ⟩) ^ d := by
  induction d with
  | zero =>
      have h0 : (⟨ℓ ^ 0, h𝓛.pow_mem hℓ 0⟩ : 𝓛 0) = ⟨1, h𝓛.one_mem_zero⟩ :=
        Subtype.ext (pow_zero ℓ)
      rw [h0, pow_zero, h𝓛.dualPow_zero]
      exact h𝓛.zeroEquiv_one
  | succ d ih =>
      have hmul : h𝓛.mulEquiv d 1 ((⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ : 𝓛 d) ⊗ₜ[R] ⟨ℓ, hℓ⟩) =
          ⟨ℓ ^ (d + 1), h𝓛.pow_mem hℓ (d + 1)⟩ :=
        Subtype.ext (by rw [h𝓛.coe_mulEquiv_tmul]; exact (pow_succ ℓ d).symm)
      rw [← hmul, h𝓛.dualPow_succ_apply μ, ih, pow_succ]

/-- **A functional trivializes the family away from its value on a degree-one element.** For
`r = μ ℓ`, multiplication by `r ^ d` carries `𝓛 d` into the `R`-span of `ℓ ^ d`; after inverting
`r` the element `ℓ ^ d` therefore generates. -/
theorem exists_smul_pow_eq (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) :
    ∀ (d : ℕ) (m : T), m ∈ 𝓛 d → ∃ c : R, (μ ⟨ℓ, hℓ⟩) ^ d • m = c • ℓ ^ d := by
  intro d
  induction d with
  | zero =>
      intro m hm
      rw [h𝓛.degree_zero] at hm
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp hm
      refine ⟨c, ?_⟩
      rw [pow_zero, one_smul, pow_zero, Algebra.smul_def, mul_one, ← hc]
  | succ d ih =>
      intro m hm
      rw [← h𝓛.mul_eq d 1] at hm
      refine Submodule.mul_induction_on hm ?_ ?_
      · intro u hu v hv
        obtain ⟨c, hc⟩ := ih u hu
        have hv' : (μ ⟨ℓ, hℓ⟩) • v = (μ ⟨v, hv⟩) • ℓ :=
          congrArg Subtype.val (h𝓛.smul_comm_of_dual μ ⟨ℓ, hℓ⟩ ⟨v, hv⟩)
        refine ⟨c * μ ⟨v, hv⟩, ?_⟩
        rw [pow_succ, ← smul_mul_smul_comm, hc, hv', smul_mul_smul_comm, pow_succ]
      · intro x y hx hy
        obtain ⟨c, hc⟩ := hx
        obtain ⟨c', hc'⟩ := hy
        exact ⟨c + c', by rw [smul_add, hc, hc', add_smul]⟩

/-- **The trivializing scalar of `Stacks.GradedRing.IsTensorPowerFamily.exists_smul_pow_eq` is
the `d`-th power of the functional.** For `m ∈ 𝓛 d`, multiplication by `(μ ℓ) ^ d` carries `m` to
the multiple of `ℓ ^ d` by `dualPow μ d m`: so after inverting `μ ℓ` the coordinate of `m` in
the basis `ℓ ^ d` is computed by the `d`-th tensor power of `μ`, and not merely known to exist.
For `d = 1` this is `Stacks.GradedRing.IsTensorPowerFamily.smul_comm_of_dual`. -/
theorem smul_pow_eq_dualPow_smul (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) :
    ∀ (d : ℕ) (m : 𝓛 d), (μ ⟨ℓ, hℓ⟩) ^ d • (m : T) = (dualPow h𝓛 μ d m) • ℓ ^ d := by
  intro d
  induction d with
  | zero =>
      intro m
      have h : (h𝓛.zeroEquiv m) • (1 : T) = (m : T) :=
        congrArg Subtype.val ((LinearEquiv.ofBijective _
          h𝓛.bijective_toSpanSingleton_zero).apply_symm_apply m)
      rw [pow_zero, one_smul, pow_zero, h𝓛.dualPow_zero]
      exact h.symm
  | succ d ih =>
      intro m
      obtain ⟨x, hx⟩ := (h𝓛.mulEquiv d 1).surjective m
      subst hx
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul u v =>
          have hv : (μ ⟨ℓ, hℓ⟩) • (v : T) = (μ v) • ℓ :=
            congrArg Subtype.val (h𝓛.smul_comm_of_dual μ ⟨ℓ, hℓ⟩ v)
          rw [h𝓛.coe_mulEquiv_tmul, pow_succ, ← smul_mul_smul_comm, ih u, hv, smul_mul_smul_comm,
            h𝓛.dualPow_succ_apply μ u v, ← pow_succ]
      | add x y hx hy =>
          rw [map_add, Submodule.coe_add, smul_add, hx, hy, map_add, add_smul]

end IsTensorPowerFamily

/-! ### The comparison is bijective up to the trivializing scalar -/

namespace InvertibleTwist

variable {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {𝓛 : ℕ → Submodule R T}
  {ℬ : ℕ → Submodule R B} [GradedAlgebra ℬ] (tw : InvertibleTwist 𝒜 𝓛 ℬ)
  (h𝓛 : IsTensorPowerFamily 𝓛) {ℓ ℓ' : T}

section Trivialization

include tw h𝓛

/-- The unconditional comparison is `R`-linear on homogeneous elements. -/
theorem twistHomOf_smul_of_mem (hℓ : ℓ ∈ 𝓛 1) (c : R) {i : ℕ} {a : A} (ha : a ∈ 𝒜 i) :
    tw.twistHomOf h𝓛 hℓ (c • a) = c • tw.twistHomOf h𝓛 hℓ a := by
  have h1 : tw.pieceMap h𝓛 hℓ i ⟨c • a, Submodule.smul_mem _ c ha⟩ =
      c • tw.pieceMap h𝓛 hℓ i ⟨a, ha⟩ := by
    rw [← map_smul]
    rfl
  rw [tw.twistHomOf_coe h𝓛 hℓ i ⟨c • a, Submodule.smul_mem _ c ha⟩,
    tw.twistHomOf_coe h𝓛 hℓ i ⟨a, ha⟩, h1, Submodule.coe_smul]

/-- The unconditional comparison agrees with the two structure maps in degree zero, so it does
not depend on `ℓ` there. -/
theorem twistHomOf_algebraMap (hℓ : ℓ ∈ 𝓛 1) (c : R) :
    tw.twistHomOf h𝓛 hℓ (algebraMap R A c) = algebraMap R B c := by
  rw [Algebra.algebraMap_eq_smul_one (A := A) c,
    tw.twistHomOf_smul_of_mem h𝓛 hℓ c (SetLike.one_mem_graded 𝒜), map_one, Algebra.smul_def,
    mul_one]

/-- **The comparison of pieces attached to `ℓ` is surjective after multiplication by
`(μ ℓ) ^ d`**, for any functional `μ` on `𝓛 1`: the trivialization
`Stacks.GradedRing.IsTensorPowerFamily.exists_smul_pow_eq` turns the second factor of a pure
tensor into a multiple of `ℓ ^ d`. -/
theorem exists_pieceMap_eq_smul (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) (y : ℬ d) :
    ∃ x : 𝒜 d, (μ ⟨ℓ, hℓ⟩) ^ d • y = tw.pieceMap h𝓛 hℓ d x := by
  obtain ⟨z, rfl⟩ := (tw.piece d).surjective y
  induction z with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
      obtain ⟨c, hc⟩ := h𝓛.exists_smul_pow_eq μ hℓ d (m : T) m.2
      refine ⟨c • a, ?_⟩
      have h3 : ((μ ⟨ℓ, hℓ⟩) ^ d • m) = c • (⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ : 𝓛 d) := Subtype.ext hc
      have h4 : (μ ⟨ℓ, hℓ⟩) ^ d • (a ⊗ₜ[R] m) =
          c • (a ⊗ₜ[R] (⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ : 𝓛 d)) := by
        rw [← TensorProduct.tmul_smul, h3, TensorProduct.tmul_smul]
      rw [← map_smul, h4]
      simp only [tw.pieceMap_apply h𝓛 hℓ d, TensorProduct.smul_tmul']
  | add z w hz hw =>
      obtain ⟨x, hx⟩ := hz
      obtain ⟨x', hx'⟩ := hw
      exact ⟨x + x', by rw [map_add, smul_add, hx, hx', map_add]⟩

/-- **The comparison of pieces attached to `ℓ` is injective after multiplication by
`(μ ℓ) ^ d`**: the `d`-th power of the functional, applied to the second factor, recovers
`(μ ℓ) ^ d` times the first. -/
theorem smul_pow_eq_zero_of_pieceMap_eq_zero (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) (d : ℕ)
    {x : 𝒜 d} (hx : tw.pieceMap h𝓛 hℓ d x = 0) : (μ ⟨ℓ, hℓ⟩) ^ d • x = 0 := by
  have h0 : (x ⊗ₜ[R] (⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ : 𝓛 d)) = 0 := by
    rw [tw.pieceMap_apply h𝓛 hℓ d] at hx
    exact (tw.piece d).map_eq_zero_iff.mp hx
  have hG : (TensorProduct.rid R (𝒜 d)) (TensorProduct.map LinearMap.id
      (IsTensorPowerFamily.dualPow h𝓛 μ d)
      (x ⊗ₜ[R] (⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ : 𝓛 d))) = 0 := by
    rw [h0, map_zero, map_zero]
  rw [TensorProduct.map_tmul, LinearMap.id_apply, h𝓛.dualPow_pow μ hℓ d,
    TensorProduct.rid_tmul] at hG
  exact hG

/-- **The comparison homomorphism attached to `ℓ` is surjective on the degree-`d` piece after
multiplication by `(μ ℓ) ^ d`.** -/
theorem exists_mem_twistHomOf_eq_smul (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) (d : ℕ) {y : B}
    (hy : y ∈ ℬ d) :
    ∃ x : A, x ∈ 𝒜 d ∧ (μ ⟨ℓ, hℓ⟩) ^ d • y = tw.twistHomOf h𝓛 hℓ x := by
  obtain ⟨x, hx⟩ := tw.exists_pieceMap_eq_smul h𝓛 μ hℓ d ⟨y, hy⟩
  refine ⟨(x : A), x.2, ?_⟩
  rw [tw.twistHomOf_coe h𝓛 hℓ d x, ← hx, Submodule.coe_smul]

/-- **The comparison homomorphism attached to `ℓ` is injective on the degree-`d` piece after
multiplication by `(μ ℓ) ^ d`.** -/
theorem smul_pow_eq_zero_of_twistHomOf_eq_zero (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) {d : ℕ}
    {z : A} (hz : z ∈ 𝒜 d) (h : tw.twistHomOf h𝓛 hℓ z = 0) : (μ ⟨ℓ, hℓ⟩) ^ d • z = 0 := by
  have h1 : tw.pieceMap h𝓛 hℓ d ⟨z, hz⟩ = 0 := by
    refine Subtype.ext ?_
    rw [← tw.twistHomOf_coe h𝓛 hℓ d ⟨z, hz⟩]
    exact h
  simpa using congrArg Subtype.val (tw.smul_pow_eq_zero_of_pieceMap_eq_zero h𝓛 μ hℓ d h1)

end Trivialization

/-! ### The chart cover of `Proj ℬ` -/

section Cover

open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.SegreGlue

attribute [local instance] ProjectiveSpectrum.isPrime

include tw h𝓛

/-- **The comparisons attached to two degree-one elements cross-commute**, which is the overlap
compatibility of `Stacks.AlgebraicGeometry.SegreGlue.homOfLE_mapAwayHom_comm`. -/
theorem crossComm_twistHomOf (hℓ : ℓ ∈ 𝓛 1) (hℓ' : ℓ' ∈ 𝓛 1) :
    CrossComm 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) (tw.twistHomOf h𝓛 hℓ') :=
  fun _ _ _ ha hb => tw.twistHomOf_mul_comm h𝓛 hℓ hℓ' ha hb

/-- **The standard opens `D₊(ψ_ℓ f)` cover `Proj ℬ`**, as `ℓ` ranges over `𝓛 1` and `f` over the
homogeneous elements of `𝒜` of positive degree. -/
theorem iSup_basicOpen_twistHomOf_eq_top [Module.Invertible R (𝓛 1)] :
    (⨆ p : (𝓛 1) × MapIndex 𝒜, Proj.basicOpen ℬ (tw.twistHomOf h𝓛 p.1.2 p.2.2.1)) = ⊤ := by
  obtain ⟨s, hs⟩ := exists_finset_dual_sum_eq_one (R := R) (𝓛 1)
  refine top_le_iff.mp fun q _ => ?_
  obtain ⟨n, b, hn, hb, hbq⟩ := exists_homogeneous_pos_notMem ℬ q
  obtain ⟨p, -, hpq⟩ := exists_notMem_of_sum_eq_one (C := B) hs
    (q : ProjectiveSpectrum ℬ).isPrime.ne_top
  obtain ⟨x, hx, hxb⟩ := tw.exists_mem_twistHomOf_eq_smul h𝓛 p.1 p.2.2 n hb
  have hne : tw.twistHomOf h𝓛 p.2.2 x ∉
      (q : ProjectiveSpectrum ℬ).asHomogeneousIdeal.toIdeal := by
    rw [← hxb, Algebra.smul_def, map_pow]
    refine fun hmem => ?_
    rcases (q : ProjectiveSpectrum ℬ).isPrime.mem_or_mem hmem with h | h
    · exact hpq ((q : ProjectiveSpectrum ℬ).isPrime.mem_of_pow_mem n h)
    · exact hbq h
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨(p.2, ⟨n, x, hn, hx⟩), ?_⟩
  exact (Proj.mem_basicOpen ℬ _ q).mpr hne

/-- Every chart lies in the domain of definition of its own comparison. -/
theorem basicOpen_le_mapDomain_twistHomOf (hℓ : ℓ ∈ 𝓛 1) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    Proj.basicOpen ℬ (tw.twistHomOf h𝓛 hℓ f) ≤ mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) :=
  basicOpen_le_mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) hd hf

/-- **A point of one chart which lies in another chart lies in the mixed chart.** If a point
omits `ψ_ℓ f` and `ψ_{ℓ'} g` then it omits `ψ_ℓ g`. -/
theorem notMem_twistHomOf_of_notMem (hℓ : ℓ ∈ 𝓛 1) (hℓ' : ℓ' ∈ 𝓛 1) {d e : ℕ} (hd : 0 < d)
    {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (q : AlgebraicGeometry.Proj ℬ)
    (hqf : tw.twistHomOf h𝓛 hℓ f ∉ q.asHomogeneousIdeal)
    (hqg : tw.twistHomOf h𝓛 hℓ' g ∉ q.asHomogeneousIdeal) :
    tw.twistHomOf h𝓛 hℓ g ∉ q.asHomogeneousIdeal := by
  intro hmem
  have hgd : tw.twistHomOf h𝓛 hℓ (g ^ d) ∈ q.asHomogeneousIdeal.toIdeal := by
    rw [map_pow]
    exact Ideal.pow_mem_of_mem _ hmem d hd
  have hfe : f ^ e ∈ 𝒜 (e * d) := by
    simpa [smul_eq_mul] using SetLike.pow_mem_graded (A := 𝒜) e hf
  have hgd' : g ^ d ∈ 𝒜 (e * d) := by
    simpa [smul_eq_mul, Nat.mul_comm] using SetLike.pow_mem_graded (A := 𝒜) d hg
  have hRHS : tw.twistHomOf h𝓛 hℓ' (f ^ e) * tw.twistHomOf h𝓛 hℓ (g ^ d) ∈
      q.asHomogeneousIdeal.toIdeal := Ideal.mul_mem_left _ _ hgd
  rw [← tw.twistHomOf_mul_comm h𝓛 hℓ hℓ' hfe hgd'] at hRHS
  rcases q.isPrime.mem_or_mem hRHS with h | h
  · rw [map_pow] at h
    exact hqf (q.isPrime.mem_of_pow_mem e h)
  · rw [map_pow] at h
    exact hqg (q.isPrime.mem_of_pow_mem d h)

/-- The opens form of `Stacks.GradedRing.InvertibleTwist.notMem_twistHomOf_of_notMem`. -/
theorem inf_basicOpen_le_basicOpen_twistHomOf (hℓ : ℓ ∈ 𝓛 1) (hℓ' : ℓ' ∈ 𝓛 1) {d e : ℕ}
    (hd : 0 < d) {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) :
    Proj.basicOpen ℬ (tw.twistHomOf h𝓛 hℓ f) ⊓ Proj.basicOpen ℬ (tw.twistHomOf h𝓛 hℓ' g) ≤
      Proj.basicOpen ℬ (tw.twistHomOf h𝓛 hℓ g) := fun z hz =>
  (Proj.mem_basicOpen ℬ _ z).mpr (tw.notMem_twistHomOf_of_notMem h𝓛 hℓ hℓ' hd hf hg z
    ((Proj.mem_basicOpen ℬ _ z).mp hz.1) ((Proj.mem_basicOpen ℬ _ z).mp hz.2))

/-- The family of charts covering `Proj ℬ`: `D₊(ψ_ℓ f)` for a degree-one `ℓ` of the family and a
homogeneous `f` of `𝒜` of positive degree. -/
abbrev chartFamily : ((𝓛 1) × MapIndex 𝒜) → (AlgebraicGeometry.Proj ℬ).Opens :=
  fun p => Proj.basicOpen ℬ (tw.twistHomOf h𝓛 p.1.2 p.2.2.1)

/-- The chart indexed by `(ℓ, f)` is the basic open set `D₊(ψ_ℓ f)` of `Proj ℬ`. -/
theorem chartFamily_apply (p : (𝓛 1) × MapIndex 𝒜) :
    tw.chartFamily h𝓛 p = Proj.basicOpen ℬ (tw.twistHomOf h𝓛 p.1.2 p.2.2.1) := rfl

/-- For an invertible module `𝓛 1`, the charts `chartFamily` cover `Proj ℬ`. -/
theorem iSup_chartFamily_eq_top [Module.Invertible R (𝓛 1)] :
    (⨆ p, tw.chartFamily h𝓛 p) = ⊤ :=
  tw.iSup_basicOpen_twistHomOf_eq_top h𝓛

/-- **The overlap step.** The local morphisms attached to two charts agree on the overlap of
those charts, even though they come from two different comparison homomorphisms. -/
theorem mapAwayHom_twistHomOf_compat (p q : (𝓛 1) × MapIndex 𝒜) :
    (AlgebraicGeometry.Proj ℬ).homOfLE
        (inf_le_left : tw.chartFamily h𝓛 p ⊓ tw.chartFamily h𝓛 q ≤ _) ≫
        mapAwayHom 𝒜 ℬ (tw.twistHomOf h𝓛 p.1.2) p.2.2.2.1 p.2.2.2.2 =
      (AlgebraicGeometry.Proj ℬ).homOfLE
        (inf_le_right : tw.chartFamily h𝓛 p ⊓ tw.chartFamily h𝓛 q ≤ _) ≫
        mapAwayHom 𝒜 ℬ (tw.twistHomOf h𝓛 q.1.2) q.2.2.2.1 q.2.2.2.2 := by
  have hW1 : tw.chartFamily h𝓛 p ⊓ tw.chartFamily h𝓛 q ≤
      Proj.basicOpen ℬ (tw.twistHomOf h𝓛 p.1.2 q.2.2.1) :=
    tw.inf_basicOpen_le_basicOpen_twistHomOf h𝓛 p.1.2 q.1.2 p.2.2.2.1 p.2.2.2.2 q.2.2.2.2
  have hW2 : tw.chartFamily h𝓛 p ⊓ tw.chartFamily h𝓛 q ≤
      Proj.basicOpen ℬ (tw.twistHomOf h𝓛 q.1.2 p.2.2.1) :=
    le_trans (le_of_eq (inf_comm _ _)) (tw.inf_basicOpen_le_basicOpen_twistHomOf h𝓛 q.1.2 p.1.2
      q.2.2.2.1 q.2.2.2.2 p.2.2.2.2)
  have hx : p.2.2.1 * q.2.2.1 ∈ 𝒜 (p.2.1 + q.2.1) :=
    SetLike.mul_mem_graded p.2.2.2.2 q.2.2.2.2
  have hk : 0 < p.2.1 + q.2.1 := Nat.lt_of_lt_of_le p.2.2.2.1 (Nat.le_add_right _ _)
  have hWx : tw.chartFamily h𝓛 p ⊓ tw.chartFamily h𝓛 q ≤
      Proj.basicOpen ℬ (tw.twistHomOf h𝓛 p.1.2 (p.2.2.1 * q.2.2.1)) := by
    rw [map_mul, Proj.basicOpen_mul]
    exact le_inf inf_le_left hW1
  have hWx' : tw.chartFamily h𝓛 p ⊓ tw.chartFamily h𝓛 q ≤
      Proj.basicOpen ℬ (tw.twistHomOf h𝓛 q.1.2 (p.2.2.1 * q.2.2.1)) := by
    rw [map_mul, Proj.basicOpen_mul]
    exact le_inf hW2 inf_le_right
  have hWxx : tw.chartFamily h𝓛 p ⊓ tw.chartFamily h𝓛 q ≤
      Proj.basicOpen ℬ (tw.twistHomOf h𝓛 p.1.2 (p.2.2.1 * q.2.2.1) *
        tw.twistHomOf h𝓛 q.1.2 (p.2.2.1 * q.2.2.1)) := by
    rw [Proj.basicOpen_mul]
    exact le_inf hWx hWx'
  rw [homOfLE_mapAwayHom 𝒜 ℬ (tw.twistHomOf h𝓛 p.1.2) p.2.2.2.1 hk p.2.2.2.2 q.2.2.2.2 hx rfl
      hWx inf_le_left,
    homOfLE_mapAwayHom 𝒜 ℬ (tw.twistHomOf h𝓛 q.1.2) q.2.2.2.1 hk q.2.2.2.2 p.2.2.2.2 hx
      (mul_comm _ _) hWx' inf_le_right]
  exact homOfLE_mapAwayHom_comm 𝒜 ℬ (tw.twistHomOf h𝓛 p.1.2) (tw.twistHomOf h𝓛 q.1.2)
    (tw.crossComm_twistHomOf h𝓛 p.1.2 q.1.2) hk hx rfl hWxx hWx hWx'

end Cover

/-! ### The glued comparison morphism -/

section Glue

open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.SegreGlue

variable [Module.Invertible R (𝓛 1)]

include tw h𝓛

/-- **The comparison morphism `Proj ℬ ⟶ Proj 𝒜` of Tag 02NC for an invertible twisting
module.** The local morphisms attached to the charts `D₊(ψ_ℓ f)`, glued over the chart cover of
`Proj ℬ`. No global generator of `𝓛 1` is assumed. -/
def projTwistGlued : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜 :=
  (Scheme.topIso _).inv ≫
    ((AlgebraicGeometry.Proj ℬ).isoOfEq (tw.iSup_chartFamily_eq_top h𝓛).symm).hom ≫
    (Scheme.Opens.iSupOpenCover (tw.chartFamily h𝓛)).glueMorphisms
      (fun p => mapAwayHom 𝒜 ℬ (tw.twistHomOf h𝓛 p.1.2) p.2.2.2.1 p.2.2.2.2)
      (fun p q => by
        dsimp only [Scheme.Opens.iSupOpenCover]
        rw [← cancel_epi (AlgebraicGeometry.isPullback_opens_inf_le
            (le_iSup (tw.chartFamily h𝓛) p) (le_iSup (tw.chartFamily h𝓛) q)).isoPullback.hom,
          ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_fst,
          ← Category.assoc, CategoryTheory.IsPullback.isoPullback_hom_snd]
        exact tw.mapAwayHom_twistHomOf_compat h𝓛 p q)

/-- **The glued morphism on a chart** is the morphism of affine schemes attached to the map
`𝒜_{(f)} → ℬ_{(ψ_ℓ f)}` of degree-zero homogeneous localizations. -/
@[reassoc]
theorem ι_projTwistGlued (p : (𝓛 1) × MapIndex 𝒜) :
    (tw.chartFamily h𝓛 p).ι ≫ tw.projTwistGlued h𝓛 =
      mapAwayHom 𝒜 ℬ (tw.twistHomOf h𝓛 p.1.2) p.2.2.2.1 p.2.2.2.2 := by
  have h0 : (Scheme.topIso (AlgebraicGeometry.Proj ℬ)).inv ≫
      ((AlgebraicGeometry.Proj ℬ).isoOfEq (tw.iSup_chartFamily_eq_top h𝓛).symm).hom ≫
        (⨆ p, tw.chartFamily h𝓛 p).ι = 𝟙 (AlgebraicGeometry.Proj ℬ) := by
    rw [Scheme.isoOfEq_hom_ι]
    simp
  have h1 : (tw.chartFamily h𝓛 p).ι ≫ (Scheme.topIso (AlgebraicGeometry.Proj ℬ)).inv ≫
      ((AlgebraicGeometry.Proj ℬ).isoOfEq (tw.iSup_chartFamily_eq_top h𝓛).symm).hom =
      (AlgebraicGeometry.Proj ℬ).homOfLE (le_iSup (tw.chartFamily h𝓛) p) := by
    rw [← cancel_mono (Scheme.Opens.ι _), Scheme.homOfLE_ι, Category.assoc, Category.assoc, h0,
      Category.comp_id]
  rw [projTwistGlued, reassoc_of% h1]
  exact (Scheme.Opens.iSupOpenCover (tw.chartFamily h𝓛)).ι_glueMorphisms _ _ p

/-- **The isomorphism is canonical: on the domain of definition of the comparison attached to
*any* degree-one element `ℓ` it is that comparison.** So the glued morphism really is the gluing
of the morphisms `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` of the `ψ_ℓ`, and no
trivialization is preferred. -/
theorem ι_comp_projTwistGlued (hℓ : ℓ ∈ 𝓛 1) :
    (mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).ι ≫ tw.projTwistGlued h𝓛 =
      mapHom 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) := by
  refine mapDomain_hom_ext 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) _ _ fun d hd f hf => ?_
  rw [homOfLE_mapHom 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) hd hf, ← Category.assoc, Scheme.homOfLE_ι]
  exact tw.ι_projTwistGlued h𝓛 (⟨ℓ, hℓ⟩, ⟨d, f, hd, hf⟩)

/-! ### The glued comparison is an isomorphism -/

omit [Module.Invertible R ↥(𝓛 1)] in
/-- **Replacing one degree-one element by another costs a scalar.** For `r = μ ℓ`, the element
`r ^ d • ψ_{ℓ'} a` is an `R`-multiple of `ψ_ℓ a`. -/
theorem smul_pow_twistHomOf_eq (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) (hℓ' : ℓ' ∈ 𝓛 1) {d : ℕ}
    {a : A} (ha : a ∈ 𝒜 d) :
    ∃ c : R, (μ ⟨ℓ, hℓ⟩) ^ d • tw.twistHomOf h𝓛 hℓ' a = c • tw.twistHomOf h𝓛 hℓ a := by
  obtain ⟨c, hc⟩ := h𝓛.exists_smul_pow_eq μ hℓ d (ℓ' ^ d) (h𝓛.pow_mem hℓ' d)
  refine ⟨c, ?_⟩
  have h1 : (μ ⟨ℓ, hℓ⟩) ^ d • (⟨ℓ' ^ d, h𝓛.pow_mem hℓ' d⟩ : 𝓛 d) =
      c • (⟨ℓ ^ d, h𝓛.pow_mem hℓ d⟩ : 𝓛 d) := Subtype.ext hc
  rw [tw.twistHomOf_apply_of_mem h𝓛 hℓ' ha, tw.twistHomOf_apply_of_mem h𝓛 hℓ ha,
    ← Submodule.coe_smul, ← Submodule.coe_smul, ← map_smul, ← map_smul,
    ← TensorProduct.tmul_smul, h1, TensorProduct.tmul_smul]

omit [Module.Invertible R ↥(𝓛 1)] in
/-- **Away from the vanishing of `μ ℓ` only the comparison attached to `ℓ` matters.** A point
omitting `ψ_{ℓ'} ((μ ℓ) • a)` omits `ψ_ℓ ((μ ℓ) • a)`, for any other degree-one element `ℓ'`. -/
theorem notMem_twistHomOf_smul_of_notMem (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) (hℓ' : ℓ' ∈ 𝓛 1)
    {d : ℕ} {a : A} (ha : a ∈ 𝒜 d) (z : AlgebraicGeometry.Proj ℬ)
    (hz : tw.twistHomOf h𝓛 hℓ' ((μ ⟨ℓ, hℓ⟩) • a) ∉ z.asHomogeneousIdeal) :
    tw.twistHomOf h𝓛 hℓ ((μ ⟨ℓ, hℓ⟩) • a) ∉ z.asHomogeneousIdeal := by
  rw [tw.twistHomOf_smul_of_mem h𝓛 hℓ' (μ ⟨ℓ, hℓ⟩) ha, Algebra.smul_def] at hz
  have hr0 : algebraMap R B (μ ⟨ℓ, hℓ⟩) ∉ z.asHomogeneousIdeal := fun hm =>
    hz (Ideal.mul_mem_right _ _ hm)
  have ha' : tw.twistHomOf h𝓛 hℓ' a ∉ z.asHomogeneousIdeal := fun hm =>
    hz (Ideal.mul_mem_left _ _ hm)
  obtain ⟨c, hc⟩ := tw.smul_pow_twistHomOf_eq h𝓛 μ hℓ hℓ' ha
  have hprod : algebraMap R B c * tw.twistHomOf h𝓛 hℓ a ∉ z.asHomogeneousIdeal := by
    have heq : (algebraMap R B (μ ⟨ℓ, hℓ⟩)) ^ d * tw.twistHomOf h𝓛 hℓ' a =
        algebraMap R B c * tw.twistHomOf h𝓛 hℓ a := by
      rw [← map_pow, ← Algebra.smul_def, ← Algebra.smul_def, hc]
    rw [← heq]
    intro hm
    rcases z.isPrime.mem_or_mem hm with h | h
    · exact hr0 (z.isPrime.mem_of_pow_mem d h)
    · exact ha' h
  rw [tw.twistHomOf_smul_of_mem h𝓛 hℓ (μ ⟨ℓ, hℓ⟩) ha, Algebra.smul_def]
  intro hm
  rcases z.isPrime.mem_or_mem hm with h | h
  · exact hr0 h
  · exact hprod (Ideal.mul_mem_left _ _ h)

/-- The inverse image of a standard open under the glued morphism, computed at a point lying in
the domain of definition of one of the comparisons. -/
theorem mem_preimage_basicOpen_iff (hℓ : ℓ ∈ 𝓛 1) (z : AlgebraicGeometry.Proj ℬ)
    (hz : z ∈ mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)) {k : ℕ} (hk : 0 < k) {f : A}
    (hf : f ∈ 𝒜 k) :
    z ∈ tw.projTwistGlued h𝓛 ⁻¹ᵁ Proj.basicOpen 𝒜 f ↔
      z ∈ Proj.basicOpen ℬ (tw.twistHomOf h𝓛 hℓ f) := by
  have key : ∀ U : (AlgebraicGeometry.Proj 𝒜).Opens,
      (z ∈ tw.projTwistGlued h𝓛 ⁻¹ᵁ U) ↔
        ((⟨z, hz⟩ : (mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).toScheme) ∈
          ((mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ)).ι ≫ tw.projTwistGlued h𝓛) ⁻¹ᵁ U) :=
    fun _ => Iff.rfl
  rw [key (Proj.basicOpen 𝒜 f), tw.ι_comp_projTwistGlued h𝓛 hℓ,
    mapHom_preimage_basicOpen 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) f k hf hk]
  exact Iff.rfl

/-- **The inverse image of the standard open of `(μ ℓ) • a` under the glued morphism** is the
standard open of its image under the comparison attached to `ℓ`. -/
theorem preimage_basicOpen_smul (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) {d : ℕ} (hd : 0 < d)
    {a : A} (ha : a ∈ 𝒜 d) :
    tw.projTwistGlued h𝓛 ⁻¹ᵁ Proj.basicOpen 𝒜 ((μ ⟨ℓ, hℓ⟩) • a) =
      Proj.basicOpen ℬ (tw.twistHomOf h𝓛 hℓ ((μ ⟨ℓ, hℓ⟩) • a)) := by
  have hs : (μ ⟨ℓ, hℓ⟩) • a ∈ 𝒜 d := Submodule.smul_mem _ _ ha
  refine le_antisymm (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (show z ∈ ⨆ p, tw.chartFamily h𝓛 p by rw [tw.iSup_chartFamily_eq_top h𝓛]; trivial)
    have hzd : z ∈ mapDomain 𝒜 ℬ (tw.twistHomOf h𝓛 p.1.2) :=
      basicOpen_le_mapDomain 𝒜 ℬ _ p.2.2.2.1 p.2.2.2.2 hp
    have h1 : z ∈ Proj.basicOpen ℬ (tw.twistHomOf h𝓛 p.1.2 ((μ ⟨ℓ, hℓ⟩) • a)) :=
      (tw.mem_preimage_basicOpen_iff h𝓛 p.1.2 z hzd hd hs).mp hz
    exact (Proj.mem_basicOpen ℬ _ z).mpr
      (tw.notMem_twistHomOf_smul_of_notMem h𝓛 μ hℓ p.1.2 ha z
        ((Proj.mem_basicOpen ℬ _ z).mp h1))
  · exact (tw.mem_preimage_basicOpen_iff h𝓛 hℓ z
      (basicOpen_le_mapDomain 𝒜 ℬ _ hd hs hz) hd hs).mpr hz

omit [Module.Invertible R ↥(𝓛 1)] in
/-- **The map of degree-zero homogeneous localizations attached to `ℓ` at `(μ ℓ) • a` is
bijective.** -/
theorem bijective_awayMap_twistHomOf (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) {d : ℕ}
    {a : A} (ha : a ∈ 𝒜 d) :
    Function.Bijective
      (HomogeneousLocalization.Away.map (tw.twistHomOf h𝓛 hℓ) ((μ ⟨ℓ, hℓ⟩) • a)) := by
  have hs : (μ ⟨ℓ, hℓ⟩) • a ∈ 𝒜 d := Submodule.smul_mem _ _ ha
  have hψs : tw.twistHomOf h𝓛 hℓ ((μ ⟨ℓ, hℓ⟩) • a) =
      algebraMap R B (μ ⟨ℓ, hℓ⟩) * tw.twistHomOf h𝓛 hℓ a := by
    rw [tw.twistHomOf_smul_of_mem h𝓛 hℓ (μ ⟨ℓ, hℓ⟩) ha, Algebra.smul_def]
  constructor
  · refine (injective_iff_map_eq_zero _).mpr fun u hu => ?_
    obtain ⟨n, z, hz, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs u
    rw [HomogeneousLocalization.Away.map_mk _ _ hs n z hz] at hu
    have hval := congrArg HomogeneousLocalization.val hu
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at hval
    obtain ⟨m, hm⟩ := hval
    obtain ⟨N, hN⟩ := m.2
    rw [← hN] at hm
    have hNz : (((μ ⟨ℓ, hℓ⟩) • a) ^ N * z) ∈ 𝒜 (N * d + n * d) := by
      simpa [smul_eq_mul] using SetLike.mul_mem_graded (A := 𝒜)
        (SetLike.pow_mem_graded N hs) hz
    have hzero : tw.twistHomOf h𝓛 hℓ (((μ ⟨ℓ, hℓ⟩) • a) ^ N * z) = 0 := by
      rw [map_mul, map_pow]
      simpa [mul_comm] using hm
    have hkey := tw.smul_pow_eq_zero_of_twistHomOf_eq_zero h𝓛 μ hℓ hNz hzero
    refine HomogeneousLocalization.val_injective _ ?_
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_zero,
      Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
    refine ⟨⟨((μ ⟨ℓ, hℓ⟩) • a) ^ (N * d + n * d + N), ⟨N * d + n * d + N, rfl⟩⟩, ?_⟩
    have hexp : ((μ ⟨ℓ, hℓ⟩) • a) ^ (N * d + n * d + N) * z =
        a ^ (N * d + n * d) *
          ((μ ⟨ℓ, hℓ⟩) ^ (N * d + n * d) • (((μ ⟨ℓ, hℓ⟩) • a) ^ N * z)) := by
      simp only [Algebra.smul_def, map_pow, pow_add, map_mul]
      ring
    show ((μ ⟨ℓ, hℓ⟩) • a) ^ (N * d + n * d + N) * z = 0
    rw [hexp, hkey, mul_zero]
  · intro w
    obtain ⟨n, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective ℬ
      ((tw.twistHomOf h𝓛 hℓ).map_mem hs) w
    obtain ⟨x, hx, hxy⟩ := tw.exists_mem_twistHomOf_eq_smul h𝓛 μ hℓ (n • d) hy
    have hxa : x * a ^ (n * d) ∈ 𝒜 ((n + n * d) • d) := by
      have h1 : a ^ (n * d) ∈ 𝒜 (n * d * d) := by
        simpa [smul_eq_mul] using SetLike.pow_mem_graded (A := 𝒜) (n * d) ha
      have h2 : x ∈ 𝒜 (n * d) := by simpa [smul_eq_mul] using hx
      have := SetLike.mul_mem_graded (A := 𝒜) h2 h1
      simpa [smul_eq_mul, Nat.add_mul, Nat.mul_assoc] using this
    refine ⟨HomogeneousLocalization.Away.mk 𝒜 hs (n + n * d) (x * a ^ (n * d)) hxa, ?_⟩
    rw [HomogeneousLocalization.Away.map_mk _ _ hs (n + n * d) _ hxa]
    refine HomogeneousLocalization.val_injective _ ?_
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk_iff]
    refine Localization.r_of_eq ?_
    have hx' : algebraMap R B (μ ⟨ℓ, hℓ⟩) ^ (n * d) * y = tw.twistHomOf h𝓛 hℓ x := by
      rw [← map_pow, ← Algebra.smul_def]
      simpa [smul_eq_mul] using hxy
    show (tw.twistHomOf h𝓛 hℓ ((μ ⟨ℓ, hℓ⟩) • a)) ^ n *
        tw.twistHomOf h𝓛 hℓ (x * a ^ (n * d)) =
      (tw.twistHomOf h𝓛 hℓ ((μ ⟨ℓ, hℓ⟩) • a)) ^ (n + n * d) * y
    rw [map_mul, map_pow, hψs, ← hx']
    ring

/-- **The glued morphism over the standard open of `(μ ℓ) • a`** is `Spec` of the map of
degree-zero homogeneous localizations attached to `ℓ`, up to the canonical isomorphisms. -/
theorem morphismRestrict_projTwistGlued_eq (μ : (𝓛 1) →ₗ[R] R) (hℓ : ℓ ∈ 𝓛 1) {d : ℕ}
    (hd : 0 < d) {a : A} (ha : a ∈ 𝒜 d) :
    tw.projTwistGlued h𝓛 ∣_ Proj.basicOpen 𝒜 ((μ ⟨ℓ, hℓ⟩) • a) =
      ((AlgebraicGeometry.Proj ℬ).isoOfEq
          (tw.preimage_basicOpen_smul h𝓛 μ hℓ hd ha)).hom ≫
        (Proj.basicOpenIsoSpec ℬ (tw.twistHomOf h𝓛 hℓ ((μ ⟨ℓ, hℓ⟩) • a))
          ((tw.twistHomOf h𝓛 hℓ).map_mem (Submodule.smul_mem _ _ ha)) hd).hom ≫
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map (tw.twistHomOf h𝓛 hℓ) ((μ ⟨ℓ, hℓ⟩) • a))) ≫
        (Proj.basicOpenIsoSpec 𝒜 ((μ ⟨ℓ, hℓ⟩) • a) (Submodule.smul_mem _ _ ha) hd).inv := by
  have hs : (μ ⟨ℓ, hℓ⟩) • a ∈ 𝒜 d := Submodule.smul_mem _ _ ha
  have hma : mapAwayHom 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) hd hs =
      Proj.basicOpenToSpec ℬ (tw.twistHomOf h𝓛 hℓ ((μ ⟨ℓ, hℓ⟩) • a)) ≫
        Spec.map (CommRingCat.ofHom
          (HomogeneousLocalization.Away.map (tw.twistHomOf h𝓛 hℓ) ((μ ⟨ℓ, hℓ⟩) • a))) ≫
        Proj.awayι 𝒜 ((μ ⟨ℓ, hℓ⟩) • a) hs hd := rfl
  rw [← cancel_mono (Proj.basicOpen 𝒜 ((μ ⟨ℓ, hℓ⟩) • a)).ι, morphismRestrict_ι]
  simp only [Category.assoc]
  rw [show (Proj.basicOpenIsoSpec 𝒜 ((μ ⟨ℓ, hℓ⟩) • a) hs hd).inv ≫
      (Proj.basicOpen 𝒜 ((μ ⟨ℓ, hℓ⟩) • a)).ι =
      Proj.awayι 𝒜 ((μ ⟨ℓ, hℓ⟩) • a) hs hd from rfl,
    Proj.basicOpenIsoSpec_hom, ← hma,
    ← tw.ι_projTwistGlued h𝓛 (⟨ℓ, hℓ⟩, ⟨d, (μ ⟨ℓ, hℓ⟩) • a, hd, hs⟩),
    ← Category.assoc, Scheme.isoOfEq_hom_ι]

/-- **The glued comparison morphism is an isomorphism.** -/
theorem isIso_projTwistGlued : IsIso (tw.projTwistGlued h𝓛) := by
  obtain ⟨s, hs⟩ := exists_finset_dual_sum_eq_one (R := R) (𝓛 1)
  show MorphismProperty.isomorphisms Scheme (tw.projTwistGlued h𝓛)
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme) fun x => ?_
  obtain ⟨d, a, hd, ha, hax⟩ := exists_homogeneous_pos_notMem 𝒜 x
  obtain ⟨p, -, hpx⟩ := exists_notMem_of_sum_eq_one (C := A) hs
    (x : ProjectiveSpectrum 𝒜).isPrime.ne_top
  refine ⟨Proj.basicOpen 𝒜 ((p.1 p.2) • a), ?_, ?_⟩
  · refine (Proj.mem_basicOpen 𝒜 _ x).mpr ?_
    rw [Algebra.smul_def]
    exact fun hm => ((x : ProjectiveSpectrum 𝒜).isPrime.mem_or_mem hm).elim hpx hax
  · have : IsIso (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (tw.twistHomOf h𝓛 p.2.2) ((p.1 p.2) • a))) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      exact tw.bijective_awayMap_twistHomOf h𝓛 p.1 p.2.2 ha
    rw [MorphismProperty.isomorphisms.iff,
      tw.morphismRestrict_projTwistGlued_eq h𝓛 p.1 p.2.2 hd ha]
    infer_instance

/-- **The canonical isomorphism `Proj ℬ ≅ Proj 𝒜` of Tag 02NC**, for a graded ring `𝒜` and a
twist `ℬ` of it by a family of tensor powers of an **invertible** module: no global generator of
`𝓛 1` is assumed. -/
def projTwistIsoGeneral : AlgebraicGeometry.Proj ℬ ≅ AlgebraicGeometry.Proj 𝒜 :=
  haveI : IsIso (tw.projTwistGlued h𝓛) := tw.isIso_projTwistGlued h𝓛
  asIso (tw.projTwistGlued h𝓛)

/-- The forward morphism of `projTwistIsoGeneral` is `projTwistGlued`. -/
theorem projTwistIsoGeneral_hom :
    (tw.projTwistIsoGeneral h𝓛).hom = tw.projTwistGlued h𝓛 := rfl

/-! ### The isomorphism is one over the base -/

/-- Two morphisms out of `Proj ℬ` agreeing on every chart are equal. -/
theorem chart_hom_ext {Y : Scheme.{u}} (φ χ : AlgebraicGeometry.Proj ℬ ⟶ Y)
    (H : ∀ p, (tw.chartFamily h𝓛 p).ι ≫ φ = (tw.chartFamily h𝓛 p).ι ≫ χ) : φ = χ :=
  ((AlgebraicGeometry.Proj ℬ).openCoverOfIsOpenCover (tw.chartFamily h𝓛)
    (tw.iSup_chartFamily_eq_top h𝓛)).hom_ext φ χ H

omit [Module.Invertible R ↥(𝓛 1)] in
/-- The degree-zero part of the comparison commutes with the two maps from the degree-zero part
into a degree-zero homogeneous localization. -/
theorem awayMap_comp_fromZeroRingHom (hℓ : ℓ ∈ 𝓛 1) (f : A) :
    (HomogeneousLocalization.Away.map (tw.twistHomOf h𝓛 hℓ) f).comp
        (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f)) =
      (HomogeneousLocalization.fromZeroRingHom ℬ
          (Submonoid.powers (tw.twistHomOf h𝓛 hℓ f))).comp
        (tw.twistHomOf h𝓛 hℓ).gradedZeroRingHom := by
  ext c
  simp only [RingHom.comp_apply]
  have hL : HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers f) c =
      HomogeneousLocalization.mk ⟨0, c, 1, Submonoid.one_mem _⟩ := rfl
  have hR : HomogeneousLocalization.fromZeroRingHom ℬ
        (Submonoid.powers (tw.twistHomOf h𝓛 hℓ f)) ((tw.twistHomOf h𝓛 hℓ).gradedZeroRingHom c) =
      HomogeneousLocalization.mk ⟨0, (tw.twistHomOf h𝓛 hℓ).gradedZeroRingHom c, 1,
        Submonoid.one_mem _⟩ := rfl
  rw [hL, hR]
  simp [HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk]

omit [Module.Invertible R ↥(𝓛 1)] in
/-- The chart-level triangle over the base. -/
theorem mapAwayHom_toSpecZero (hℓ : ℓ ∈ 𝓛 1) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    mapAwayHom 𝒜 ℬ (tw.twistHomOf h𝓛 hℓ) hd hf ≫ Proj.toSpecZero 𝒜 =
      (Proj.basicOpen ℬ (tw.twistHomOf h𝓛 hℓ f)).ι ≫ Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom (tw.twistHomOf h𝓛 hℓ).gradedZeroRingHom) := by
  have hψf : tw.twistHomOf h𝓛 hℓ f ∈ ℬ d := (tw.twistHomOf h𝓛 hℓ).map_mem hf
  have hι : (Proj.basicOpen ℬ (tw.twistHomOf h𝓛 hℓ f)).ι =
      Proj.basicOpenToSpec ℬ (tw.twistHomOf h𝓛 hℓ f) ≫
        Proj.awayι ℬ (tw.twistHomOf h𝓛 hℓ f) hψf hd := by
    rw [Proj.awayι, ← Proj.basicOpenIsoSpec_hom ℬ _ hψf hd, Iso.hom_inv_id_assoc]
  rw [mapAwayHom, hι]
  simp only [Category.assoc]
  rw [Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    tw.awayMap_comp_fromZeroRingHom h𝓛 hℓ f]

/-- **The isomorphism is one over the base**: it commutes with the two structure morphisms to
`Spec` of the degree-zero parts. This is the triangle of Tag 02NC. -/
theorem projTwistGlued_toSpecZero (hℓ : ℓ ∈ 𝓛 1) :
    tw.projTwistGlued h𝓛 ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫
        Spec.map (CommRingCat.ofHom (tw.twistHomOf h𝓛 hℓ).gradedZeroRingHom) := by
  refine tw.chart_hom_ext h𝓛 _ _ fun p => ?_
  rw [← Category.assoc, tw.ι_projTwistGlued h𝓛 p,
    tw.mapAwayHom_toSpecZero h𝓛 p.1.2 p.2.2.2.1 p.2.2.2.2]
  have hzero : (tw.twistHomOf h𝓛 p.1.2).gradedZeroRingHom =
      (tw.twistHomOf h𝓛 hℓ).gradedZeroRingHom := by
    ext c
    have h0 : ((c : A)) ∈ 𝒜 0 := c.2
    show tw.twistHomOf h𝓛 p.1.2 (c : A) = tw.twistHomOf h𝓛 hℓ (c : A)
    rw [tw.twistHomOf_apply_of_mem h𝓛 p.1.2 h0, tw.twistHomOf_apply_of_mem h𝓛 hℓ h0]
    simp only [pow_zero]
  rw [hzero]

end Glue

end InvertibleTwist

end Stacks.GradedRing

end
