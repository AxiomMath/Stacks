module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.TangencyLocus

/-!
# The cotangent space of a projective space at a rational point

Let `V` be a vector space over a field `k` and let `x` be a point of `𝐏(V) = Proj (Sym_k V)`
whose space `W_x` of degree-one forms vanishing at it is a hyperplane, that is, the kernel of a
linear functional on `V`. For a degree-one form `v₀` not vanishing at `x` the affine coordinates
`w / v₀`, for `w` in `W_x`, are germs at `x` lying in the maximal ideal, and they identify `W_x`
with the cotangent space `𝔪_x / 𝔪_x²`.

The identification depends on the chart only up to `𝔪_x²`: if `v₀` and `v₁` both fail to vanish
at `x` and take the same value there, then `w / v₁ - w / v₀` lies in `𝔪_x²`. This is what makes
the cotangent space well defined as the chart varies.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.localRing`: the local ring of `𝐏(V)` at a point,
  as a degree-zero homogeneous localization of `Sym_k V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartGerm`: the affine coordinate `v / v₀` as an
  element of that local ring.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.cotangentMk`: the cotangent vector attached to a
  degree-one form vanishing at the point.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartGerm_sub_chartGerm_mem_maximalIdeal_sq`: the
  chart independence just described.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_sub_chartGerm_mem_maximalIdeal_sq` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.eq_zero_of_chartGerm_mem_maximalIdeal_sq`: the
  affine coordinates exhaust the cotangent space, and only the zero form has its coordinate in
  `𝔪_x²`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.cotangentEquiv` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.stalkCotangentEquiv`: the resulting `k`-linear
  identification of `W_x` with `𝔪_x / 𝔪_x²`, for the local ring and for the stalk of the
  structure sheaf.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.stalkCotangentEquivOfIsClosed`: the same at a
  closed point over an algebraically closed field.

## Implementation notes

The local ring is `HomogeneousLocalization.AtPrime` of the homogeneous prime of the point, which
is Mathlib's model of the stalk: `AlgebraicGeometry.Proj.stalkIso` is that identification, so no
comparison between a chart ring and the stalk is needed, and the comparison between `𝔪 / 𝔪²` for
an affine ring and for its localization at `𝔪` — which Mathlib does not have — is never
required.

Surjectivity of `W_x → 𝔪_x / 𝔪_x²` is an induction over the symmetric powers: a homogeneous
coordinate of degree `d` is its value at `x` times `v₀ ^ d` modulo the prime of `x`, so every
fraction is a scalar plus an affine coordinate modulo `𝔪_x²`. Injectivity is a first-order
expansion: a functional `μ` on `V` gives a `k`-algebra map from `Sym_k V` to the dual numbers
over the residue field of the affine cone, carrying a form `w` to `μ w` in the nilpotent
direction; it kills `𝔪_x²`, so an affine coordinate lying there has `μ w = 0` for every `μ`.

The hypothesis that `W_x` is a hyperplane is not removable. At the generic point `x` of a smooth
conic in `𝐏²` no linear form vanishes on the conic, so `W_x` is zero, while the local ring is a
discrete valuation ring and `𝔪_x / 𝔪_x²` is one-dimensional. Over an algebraically closed field
with `V` finite-dimensional the hypothesis holds exactly at the closed points, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_pointSubmodule_eq_ker_of_isClosed`; over an
arbitrary field it holds at every `k`-rational point, by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_dual_pointSubmodule_eq_ker`.
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open Stacks.AlgebraicGeometry.ProjShared

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v w

attribute [local instance] ProjectiveSpectrum.isPrime

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-! ### The ground field inside a homogeneous localization -/

/-- The ground field inside a homogeneous localization of the symmetric algebra of `V`, a scalar
`c` going to the fraction `c / 1`. -/
public def groundFieldHom (S : Submonoid (SymmetricAlgebra k V)) :
    k →+* HomogeneousLocalization (fun n => SymPow.symmetricPower n k V) S :=
  (HomogeneousLocalization.fromZeroRingHom _ S).comp (algebraMap k (SymPow.symmetricPower 0 k V))

/-- A scalar of the ground field is the fraction `c / 1`. -/
@[simp]
public theorem val_groundFieldHom (S : Submonoid (SymmetricAlgebra k V)) (c : k) :
    (groundFieldHom k V S c).val =
      Localization.mk (algebraMap k (SymmetricAlgebra k V) c) 1 := by
  simp only [groundFieldHom, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.fromZeroRingHom]
  rfl

/-- Scaling by the ground field is multiplication by the corresponding fraction `c / 1`. -/
public theorem smul_eq_groundFieldHom_mul (S : Submonoid (SymmetricAlgebra k V)) (c : k)
    (ξ : HomogeneousLocalization (fun n => SymPow.symmetricPower n k V) S) :
    c • ξ = groundFieldHom k V S c * ξ := by
  obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective ξ
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul, val_groundFieldHom,
    HomogeneousLocalization.val_mk, Localization.smul_mk, Localization.mk_mul, one_mul,
    Algebra.smul_def]

/-- The ground field acts on a homogeneous localization of the symmetric algebra of `V` through
the degree-zero part, a scalar `c` acting as the fraction `c / 1`. -/
public instance algebraHomogeneousLocalization (S : Submonoid (SymmetricAlgebra k V)) :
    Algebra k (HomogeneousLocalization (fun n => SymPow.symmetricPower n k V) S) where
  algebraMap := groundFieldHom k V S
  smul c ξ := c • ξ
  commutes' _ _ := mul_comm _ _
  smul_def' := smul_eq_groundFieldHom_mul k V S

-- The generic scalar action on a homogeneous localization is definitionally the one above, but
-- is found first by instance search; deprioritising it keeps the `k`-action on the cotangent
-- spaces below syntactically the algebra action, so the scalar-tower instances apply.
attribute [local instance 0] HomogeneousLocalization.instSMul

/-- A scalar of the ground field is the fraction `c / 1` in a homogeneous localization. -/
@[simp]
public theorem val_algebraMap_homogeneousLocalization (S : Submonoid (SymmetricAlgebra k V))
    (c : k) :
    (algebraMap k (HomogeneousLocalization (fun n => SymPow.symmetricPower n k V) S) c).val =
      Localization.mk (algebraMap k (SymmetricAlgebra k V) c) 1 :=
  val_groundFieldHom k V S c

/-! ### The local ring at a point and its residue map -/

variable {k V}

/-- The homogeneous prime cutting out a point of `𝐏(V)` is a prime ideal of `Sym_k V`. -/
public instance isPrime_asHomogeneousIdeal (x : projectiveSpaceOfModule k V) :
    x.asHomogeneousIdeal.toIdeal.IsPrime :=
  x.isPrime

/-- The local ring of `𝐏(V)` at a point: the degree-zero part of the homogeneous localization of
`Sym_k V` at the homogeneous prime of the point. Mathlib's `AlgebraicGeometry.Proj.stalkIso`
identifies it with the stalk of the structure sheaf there. -/
public abbrev localRing (x : projectiveSpaceOfModule k V) : Type (max u v) :=
  HomogeneousLocalization.AtPrime (fun n => SymPow.symmetricPower n k V)
    x.asHomogeneousIdeal.toIdeal

/-- The residue field of the affine cone over `𝐏(V)` at the generic point of the cone over a
point `x`: the fraction field of `Sym_k V` modulo the homogeneous prime of `x`. -/
public abbrev coneResidueField (x : projectiveSpaceOfModule k V) : Type (max u v) :=
  FractionRing (SymmetricAlgebra k V ⧸ x.asHomogeneousIdeal.toIdeal)

/-- The homogeneous coordinate ring maps to the residue field of the cone at a point, as a
`k`-algebra map. -/
public def toConeResidueFieldₐ (x : projectiveSpaceOfModule k V) :
    SymmetricAlgebra k V →ₐ[k] coneResidueField x :=
  (IsScalarTower.toAlgHom k (SymmetricAlgebra k V ⧸ x.asHomogeneousIdeal.toIdeal)
      (coneResidueField x)).comp (Ideal.Quotient.mkₐ k x.asHomogeneousIdeal.toIdeal)

/-- The homogeneous coordinate ring maps to the residue field of the cone at a point, with kernel
the homogeneous prime of that point. -/
public def toConeResidueField (x : projectiveSpaceOfModule k V) :
    SymmetricAlgebra k V →+* coneResidueField x :=
  (toConeResidueFieldₐ x).toRingHom

/-- The `k`-algebra map to the residue field of the cone agrees with the ring map
`toConeResidueField`. -/
@[simp]
public theorem toConeResidueFieldₐ_apply (x : projectiveSpaceOfModule k V)
    (z : SymmetricAlgebra k V) : toConeResidueFieldₐ x z = toConeResidueField x z :=
  rfl

/-- A homogeneous coordinate dies in the residue field of the cone exactly when it lies in the
homogeneous prime of the point. -/
public theorem toConeResidueField_eq_zero_iff (x : projectiveSpaceOfModule k V)
    (z : SymmetricAlgebra k V) :
    toConeResidueField x z = 0 ↔ z ∈ x.asHomogeneousIdeal.toIdeal := by
  change algebraMap (SymmetricAlgebra k V ⧸ x.asHomogeneousIdeal.toIdeal) (coneResidueField x)
      (Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal z) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

/-- Every element outside the homogeneous prime of a point becomes a unit in the residue field of
the cone there. -/
public theorem isUnit_toConeResidueField (x : projectiveSpaceOfModule k V)
    {s : SymmetricAlgebra k V} (hs : s ∉ x.asHomogeneousIdeal.toIdeal) :
    IsUnit (toConeResidueField x s) :=
  isUnit_iff_ne_zero.mpr fun h => hs ((toConeResidueField_eq_zero_iff x _).mp h)

/-- **Extending a map on homogeneous coordinates to the local ring at a point.** If every
homogeneous coordinate not vanishing at `x` becomes invertible in a ring `T`, then a ring map
`Sym_k V → T` extends to the local ring of `𝐏(V)` at `x`. -/
public def fractionLift {T : Type w} [CommRing T] (x : projectiveSpaceOfModule k V)
    (g : SymmetricAlgebra k V →+* T)
    (hg : ∀ s : x.asHomogeneousIdeal.toIdeal.primeCompl, IsUnit (g s)) :
    localRing x →+* T :=
  (IsLocalization.lift (M := x.asHomogeneousIdeal.toIdeal.primeCompl)
      (S := Localization x.asHomogeneousIdeal.toIdeal.primeCompl) hg).comp
    (algebraMap (localRing x) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))

/-- The extension to the local ring clears denominators: its value at a fraction, times the image
of the denominator, is the image of the numerator. -/
public theorem fractionLift_mk_mul {T : Type w} [CommRing T] (x : projectiveSpaceOfModule k V)
    (g : SymmetricAlgebra k V →+* T)
    (hg : ∀ s : x.asHomogeneousIdeal.toIdeal.primeCompl, IsUnit (g s))
    (y : HomogeneousLocalization.NumDenSameDeg (fun n => SymPow.symmetricPower n k V)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    fractionLift x g hg (HomogeneousLocalization.mk y) * g (y.den : _) = g (y.num : _) := by
  have hval : (HomogeneousLocalization.mk y :
        localRing x).val * algebraMap (SymmetricAlgebra k V) _ (y.den : _) =
      algebraMap (SymmetricAlgebra k V) _ (y.num : _) := by
    rw [HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  change IsLocalization.lift (M := x.asHomogeneousIdeal.toIdeal.primeCompl)
      (S := Localization x.asHomogeneousIdeal.toIdeal.primeCompl) hg
      (HomogeneousLocalization.mk y : localRing x).val * _ = _
  rw [← IsLocalization.lift_eq (M := x.asHomogeneousIdeal.toIdeal.primeCompl)
    (S := Localization x.asHomogeneousIdeal.toIdeal.primeCompl) hg (y.den : _),
    ← _root_.map_mul, hval, IsLocalization.lift_eq]

/-- The local ring at a point maps to the residue field of the cone there, a fraction of
homogeneous coordinates going to the corresponding fraction. -/
public def residueHom (x : projectiveSpaceOfModule k V) :
    localRing x →+* coneResidueField x :=
  fractionLift x (toConeResidueField x) fun s => isUnit_toConeResidueField x s.2

/-- The residue map clears denominators: the value at a fraction, times the image of the
denominator, is the image of the numerator. -/
public theorem residueHom_mk_mul (x : projectiveSpaceOfModule k V)
    (y : HomogeneousLocalization.NumDenSameDeg (fun n => SymPow.symmetricPower n k V)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    residueHom x (HomogeneousLocalization.mk y) * toConeResidueField x (y.den : _) =
      toConeResidueField x (y.num : _) :=
  fractionLift_mk_mul x _ _ y

/-- A fraction whose numerator lies in the homogeneous prime of `x` has residue zero. -/
private theorem residueHom_mk_eq_zero_of_num_mem (x : projectiveSpaceOfModule k V)
    {y : HomogeneousLocalization.NumDenSameDeg (fun n => SymPow.symmetricPower n k V)
      x.asHomogeneousIdeal.toIdeal.primeCompl}
    (hy : (y.num : SymmetricAlgebra k V) ∈ x.asHomogeneousIdeal.toIdeal) :
    residueHom x (HomogeneousLocalization.mk y) = 0 := by
  have h := residueHom_mk_mul x y
  rw [(toConeResidueField_eq_zero_iff x _).mpr hy] at h
  exact (mul_eq_zero.mp h).resolve_right (isUnit_toConeResidueField x y.den_mem).ne_zero

/-- The maximal ideal of the local ring at a point is the kernel of the residue map. -/
public theorem maximalIdeal_eq_ker_residueHom (x : projectiveSpaceOfModule k V) :
    maximalIdeal (localRing x) = RingHom.ker (residueHom x) := by
  refine le_antisymm (fun ξ hξ => ?_) fun ξ hξ => ?_
  · obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective ξ
    by_contra hne
    refine (mem_maximalIdeal _).mp hξ ?_
    have hnum : (y.num : SymmetricAlgebra k V) ∉ x.asHomogeneousIdeal.toIdeal := by
      intro hmem
      exact hne (RingHom.mem_ker.mpr (residueHom_mk_eq_zero_of_num_mem x hmem))
    refine IsUnit.of_mul_eq_one (HomogeneousLocalization.mk ⟨y.deg, y.den, y.num, hnum⟩) ?_
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one, Localization.mk_mul,
      mul_comm (y.num : SymmetricAlgebra k V)]
    exact Localization.mk_self
      (⟨(y.den : SymmetricAlgebra k V), y.den_mem⟩ *
        ⟨(y.num : SymmetricAlgebra k V), hnum⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)
  · exact (mem_maximalIdeal _).mpr fun hunit =>
      (hunit.map (residueHom x)).ne_zero (RingHom.mem_ker.mp hξ)

/-! ### Affine coordinates as germs at a point -/

variable {x : projectiveSpaceOfModule k V}

/-- A degree-one form not vanishing at `x` is invertible in the local ring at `x`. -/
public theorem ι_mem_primeCompl {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) :
    SymmetricAlgebra.ι k V v₀ ∈ x.asHomogeneousIdeal.toIdeal.primeCompl :=
  fun h => hv₀ ((mem_pointSubmodule_iff k V x v₀).mpr h)

/-- **The affine coordinate `v / v₀` as a germ at `x`.** For a degree-one form `v₀` not vanishing
at `x` this is the linear map sending a degree-one form `v` to the ratio `v / v₀`, an element of
the local ring of `𝐏(V)` at `x`. -/
public def chartGerm (x : projectiveSpaceOfModule k V) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) : V →ₗ[k] localRing x where
  toFun v := HomogeneousLocalization.mk
    ⟨1, ⟨SymmetricAlgebra.ι k V v, ι_mem_symmetricPower_one k V v⟩,
      ⟨SymmetricAlgebra.ι k V v₀, ι_mem_symmetricPower_one k V v₀⟩, ι_mem_primeCompl hv₀⟩
  map_add' v w := by
    apply HomogeneousLocalization.val_injective
    simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_mk,
      Localization.add_mk_self, map_add]
  map_smul' c v := by
    apply HomogeneousLocalization.val_injective
    simp only [RingHom.id_apply, Algebra.smul_def, HomogeneousLocalization.val_mul,
      val_algebraMap_homogeneousLocalization, HomogeneousLocalization.val_mk,
      Localization.mk_mul, one_mul, map_smul]

/-- The germ of the affine coordinate `v / v₀` is the fraction `ι v / ι v₀`. -/
@[simp]
public theorem val_chartGerm {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) (v : V) :
    (chartGerm x hv₀ v).val =
      Localization.mk (SymmetricAlgebra.ι k V v)
        ⟨SymmetricAlgebra.ι k V v₀, ι_mem_primeCompl hv₀⟩ :=
  HomogeneousLocalization.val_mk _

/-- The affine coordinate of the chart vector itself is `1`. -/
@[simp]
public theorem chartGerm_self {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) :
    chartGerm x hv₀ v₀ = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [val_chartGerm, HomogeneousLocalization.val_one]
  exact Localization.mk_self ⟨SymmetricAlgebra.ι k V v₀, ι_mem_primeCompl hv₀⟩

/-- **The transition rule between two affine charts.** The coordinate `v / v₀` times the
coordinate `v₀ / v₁` is the coordinate `v / v₁`. -/
public theorem chartGerm_mul_chartGerm {v₀ v₁ : V} (hv₀ : v₀ ∉ pointSubmodule k V x)
    (hv₁ : v₁ ∉ pointSubmodule k V x) (v : V) :
    chartGerm x hv₀ v * chartGerm x hv₁ v₀ = chartGerm x hv₁ v := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_chartGerm, val_chartGerm, val_chartGerm,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

/-- The germ of a degree-one form vanishing at `x` lies in the maximal ideal. -/
public theorem chartGerm_mem_maximalIdeal {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) {w : V}
    (hw : w ∈ pointSubmodule k V x) :
    chartGerm x hv₀ w ∈ maximalIdeal (localRing x) := by
  rw [maximalIdeal_eq_ker_residueHom, RingHom.mem_ker]
  exact residueHom_mk_eq_zero_of_num_mem x ((mem_pointSubmodule_iff k V x w).mp hw)

/-- **Chart independence of the cotangent class.** If two degree-one forms `v₀` and `v₁` do not
vanish at `x` and take the same value there, then for a degree-one form `w` vanishing at `x` the
two affine coordinates `w / v₁` and `w / v₀` differ by an element of `𝔪_x²`. -/
public theorem chartGerm_sub_chartGerm_mem_maximalIdeal_sq {v₀ v₁ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (hv₁ : v₁ ∉ pointSubmodule k V x)
    (hsub : v₀ - v₁ ∈ pointSubmodule k V x) {w : V} (hw : w ∈ pointSubmodule k V x) :
    chartGerm x hv₁ w - chartGerm x hv₀ w ∈ maximalIdeal (localRing x) ^ 2 := by
  have key : chartGerm x hv₁ w - chartGerm x hv₀ w =
      chartGerm x hv₀ w * chartGerm x hv₁ (v₀ - v₁) := by
    rw [map_sub, mul_sub, chartGerm_mul_chartGerm, chartGerm_self, mul_one]
  rw [key, sq]
  exact Ideal.mul_mem_mul (chartGerm_mem_maximalIdeal hv₀ hw)
    (chartGerm_mem_maximalIdeal hv₁ hsub)

/-! ### Evaluation at a rational point -/

/-- A fraction of homogeneous coordinates lies in the maximal ideal exactly when its numerator
vanishes at the point. -/
public theorem mk_mem_maximalIdeal_iff (x : projectiveSpaceOfModule k V)
    (y : HomogeneousLocalization.NumDenSameDeg (fun n => SymPow.symmetricPower n k V)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    HomogeneousLocalization.mk y ∈ maximalIdeal (localRing x) ↔
      (y.num : SymmetricAlgebra k V) ∈ x.asHomogeneousIdeal.toIdeal := by
  rw [maximalIdeal_eq_ker_residueHom, RingHom.mem_ker]
  refine ⟨fun hz => ?_, residueHom_mk_eq_zero_of_num_mem x⟩
  rw [← toConeResidueField_eq_zero_iff x (y.num : _), ← residueHom_mk_mul x y, hz, zero_mul]

variable {f : Module.Dual k V}

/-- Evaluation of the homogeneous coordinate ring at a linear functional on `V`: the `k`-algebra
map sending a degree-one form `v` to its value `f v`. -/
public def evalDual (f : Module.Dual k V) : SymmetricAlgebra k V →ₐ[k] k :=
  SymmetricAlgebra.lift f

/-- Evaluation at `f` sends the degree-one form `v` to its value `f v`. -/
@[simp]
public theorem evalDual_ι (v : V) : evalDual f (SymmetricAlgebra.ι k V v) = f v :=
  SymmetricAlgebra.lift_ι_apply f v

/-- A degree-one form taking a nonzero value at a rational point does not vanish there. -/
public theorem notMem_pointSubmodule_of_apply_ne_zero
    (hfx : pointSubmodule k V x = LinearMap.ker f) {v : V} (hv : f v ≠ 0) :
    v ∉ pointSubmodule k V x := fun h => hv (LinearMap.mem_ker.mp (hfx ▸ h))

/-- A degree-one form not vanishing at a rational point takes a nonzero value there. -/
private theorem apply_ne_zero_of_notMem_pointSubmodule
    (hfx : pointSubmodule k V x = LinearMap.ker f) {v : V} (hv : v ∉ pointSubmodule k V x) :
    f v ≠ 0 := fun h => hv (hfx ▸ LinearMap.mem_ker.mpr h)

/-- Subtracting from `u` the multiple of `v` with the same value gives a form vanishing at a
rational point. -/
private theorem sub_smul_mem_pointSubmodule (hfx : pointSubmodule k V x = LinearMap.ker f)
    {u v : V} {c : k} (h : f u = c * f v) : u - c • v ∈ pointSubmodule k V x := by
  rw [hfx, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, ← h, sub_self]

/-- A nonzero scalar multiple lies in an ideal of the symmetric algebra only if the element does. -/
private theorem mem_of_smul_mem {I : Ideal (SymmetricAlgebra k V)} {c : k} (hc : c ≠ 0)
    {z : SymmetricAlgebra k V} (h : c • z ∈ I) : z ∈ I := by
  simpa [smul_smul, hc] using I.smul_of_tower_mem c⁻¹ h

/-- **A homogeneous coordinate is its value at the point times a power of the chart vector,
modulo the homogeneous prime of the point.** -/
public theorem sub_evalDual_smul_pow_mem (hfx : pointSubmodule k V x = LinearMap.ker f)
    {v₀ : V} (hv₀ : f v₀ = 1) {d : ℕ} {z : SymmetricAlgebra k V}
    (hz : z ∈ SymPow.symmetricPower d k V) :
    z - evalDual f z • SymmetricAlgebra.ι k V v₀ ^ d ∈ x.asHomogeneousIdeal.toIdeal := by
  have hshift : ∀ u : V, SymmetricAlgebra.ι k V u - f u • SymmetricAlgebra.ι k V v₀ ∈
      x.asHomogeneousIdeal.toIdeal := by
    intro u
    simpa using (mem_pointSubmodule_iff k V x _).mp
      (sub_smul_mem_pointSubmodule hfx (by rw [hv₀, mul_one]))
  induction hz using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    simp [Algebra.smul_def]
  | add a b i ha hb iha ihb =>
    have h := Ideal.add_mem x.asHomogeneousIdeal.toIdeal iha ihb
    rw [_root_.map_add, add_smul]
    convert h using 1
    ring
  | mem_mul m hm i z hz ih =>
    obtain ⟨u, rfl⟩ := hm
    have key : SymmetricAlgebra.ι k V u * z -
        evalDual f (SymmetricAlgebra.ι k V u * z) • SymmetricAlgebra.ι k V v₀ ^ (i + 1) =
        SymmetricAlgebra.ι k V u * (z - evalDual f z • SymmetricAlgebra.ι k V v₀ ^ i) +
          (evalDual f z) • ((SymmetricAlgebra.ι k V u - f u • SymmetricAlgebra.ι k V v₀) *
            SymmetricAlgebra.ι k V v₀ ^ i) := by
      rw [_root_.map_mul, evalDual_ι]
      simp only [Algebra.smul_def, _root_.map_mul, pow_succ]
      ring
    rw [Nat.succ_eq_add_one, key]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (hshift u))


/-- A homogeneous coordinate `z` of degree `d` vanishes at a rational point exactly when its
value there is zero. -/
public theorem evalDual_eq_zero_iff (hfx : pointSubmodule k V x = LinearMap.ker f)
    {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) (hf1 : f v₀ = 1) {d : ℕ}
    {z : SymmetricAlgebra k V} (hz : z ∈ SymPow.symmetricPower d k V) :
    evalDual f z = 0 ↔ z ∈ x.asHomogeneousIdeal.toIdeal := by
  have hmem := sub_evalDual_smul_pow_mem hfx hf1 hz
  refine ⟨fun h => by simpa [h] using hmem, fun h => ?_⟩
  by_contra hne
  have hpow := mem_of_smul_mem (I := x.asHomogeneousIdeal.toIdeal) hne
    (by simpa using Ideal.sub_mem _ h hmem)
  exact ι_mem_primeCompl hv₀ ((isPrime_asHomogeneousIdeal x).mem_of_pow_mem d hpow)

/-! ### Affine coordinates of homogeneous fractions -/

/-- The germ at `x` of the fraction `z / v₀ ^ d`, for `z` a homogeneous coordinate of degree `d`
and `v₀` a degree-one form not vanishing at `x`. -/
public def chartFraction {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) {d : ℕ}
    {z : SymmetricAlgebra k V} (hz : z ∈ SymPow.symmetricPower d k V) : localRing x :=
  HomogeneousLocalization.mk ⟨d, ⟨z, hz⟩,
    ⟨SymmetricAlgebra.ι k V v₀ ^ d, by
      simpa using SetLike.pow_mem_graded d (ι_mem_symmetricPower_one k V v₀)⟩,
    pow_mem (ι_mem_primeCompl hv₀) d⟩

/-- The germ `chartFraction hv₀ hz` is represented by the fraction `z / v₀ ^ d` in the
localization. -/
@[simp]
public theorem val_chartFraction {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) {d : ℕ}
    {z : SymmetricAlgebra k V} (hz : z ∈ SymPow.symmetricPower d k V) :
    (chartFraction hv₀ hz).val =
      Localization.mk z ⟨SymmetricAlgebra.ι k V v₀ ^ d, pow_mem (ι_mem_primeCompl hv₀) d⟩ :=
  HomogeneousLocalization.val_mk _

/-- The fraction attached to a sum of homogeneous coordinates of one degree is the sum of the
fractions. -/
public theorem chartFraction_add {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) {d : ℕ}
    {a b : SymmetricAlgebra k V} (ha : a ∈ SymPow.symmetricPower d k V)
    (hb : b ∈ SymPow.symmetricPower d k V) (hab : a + b ∈ SymPow.symmetricPower d k V) :
    chartFraction hv₀ hab = chartFraction hv₀ ha + chartFraction hv₀ hb := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_add, val_chartFraction, val_chartFraction, val_chartFraction,
    Localization.add_mk_self]

/-- The fraction attached to a scalar in degree zero is that scalar. -/
public theorem chartFraction_algebraMap {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) (r : k)
    (hr : algebraMap k (SymmetricAlgebra k V) r ∈ SymPow.symmetricPower 0 k V) :
    chartFraction hv₀ hr = algebraMap k (localRing x) r := by
  apply HomogeneousLocalization.val_injective
  rw [val_chartFraction, val_algebraMap_homogeneousLocalization, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp⟩

/-- Multiplying a homogeneous coordinate by a degree-one form multiplies its fraction by the
corresponding affine coordinate. -/
public theorem chartFraction_ι_mul {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) {d : ℕ}
    {z : SymmetricAlgebra k V} (hz : z ∈ SymPow.symmetricPower d k V) (u : V)
    (huz : SymmetricAlgebra.ι k V u * z ∈ SymPow.symmetricPower (d + 1) k V) :
    chartFraction hv₀ huz = chartGerm x hv₀ u * chartFraction hv₀ hz := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_chartFraction, val_chartGerm, val_chartFraction,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by push_cast; ring⟩

/-- **The affine coordinates generate the cotangent space.** Modulo `𝔪_x²`, the germ at a
rational point `x` of a homogeneous fraction with denominator a power of the chart vector is a
scalar plus the affine coordinate of a degree-one form vanishing at `x`. -/
public theorem exists_chartFraction_sub_mem_maximalIdeal_sq
    (hfx : pointSubmodule k V x = LinearMap.ker f) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (hf1 : f v₀ = 1) {d : ℕ}
    {z : SymmetricAlgebra k V} (hz : z ∈ SymPow.symmetricPower d k V) :
    ∃ (c : k) (w : V), w ∈ pointSubmodule k V x ∧
      chartFraction hv₀ hz - algebraMap k (localRing x) c - chartGerm x hv₀ w
        ∈ maximalIdeal (localRing x) ^ 2 := by
  induction hz using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    have hgoal : ∀ hr : algebraMap k (SymmetricAlgebra k V) r ∈ SymPow.symmetricPower 0 k V,
        chartFraction hv₀ hr - algebraMap k (localRing x) r - chartGerm x hv₀ 0 ∈
          maximalIdeal (localRing x) ^ 2 := by
      intro hr
      rw [chartFraction_algebraMap, _root_.map_zero, sub_zero, sub_self]
      exact zero_mem _
    exact ⟨r, 0, zero_mem _, hgoal _⟩
  | add a b i ha hb iha ihb =>
    obtain ⟨c₁, w₁, hw₁, h₁⟩ := iha
    obtain ⟨c₂, w₂, hw₂, h₂⟩ := ihb
    refine ⟨c₁ + c₂, w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_⟩
    have hsum := Ideal.add_mem (maximalIdeal (localRing x) ^ 2) h₁ h₂
    rw [chartFraction_add hv₀ ha hb, _root_.map_add, _root_.map_add]
    convert hsum using 1
    ring
  | mem_mul mm hmm i z hz ih =>
    obtain ⟨u, rfl⟩ := hmm
    obtain ⟨c, w, hw, hρ⟩ := ih
    have hu' : u - f u • v₀ ∈ pointSubmodule k V x :=
      sub_smul_mem_pointSubmodule hfx (by rw [hf1, mul_one])
    have hEu : chartGerm x hv₀ u =
        algebraMap k (localRing x) (f u) + chartGerm x hv₀ (u - f u • v₀) := by
      rw [map_sub, LinearMap.map_smul, chartGerm_self, Algebra.smul_def, mul_one]
      ring
    have hgoal : ∀ huz : SymmetricAlgebra.ι k V u * z ∈ SymPow.symmetricPower (i + 1) k V,
        chartFraction hv₀ huz - algebraMap k (localRing x) (f u * c) -
            chartGerm x hv₀ (f u • w + c • (u - f u • v₀)) ∈
          maximalIdeal (localRing x) ^ 2 := by
      intro huz
      have hid : chartFraction hv₀ huz - algebraMap k (localRing x) (f u * c) -
          chartGerm x hv₀ (f u • w + c • (u - f u • v₀)) =
            chartGerm x hv₀ (u - f u • v₀) * chartGerm x hv₀ w +
              chartGerm x hv₀ u *
                (chartFraction hv₀ hz - algebraMap k (localRing x) c -
                  chartGerm x hv₀ w) := by
        rw [chartFraction_ι_mul hv₀ hz u, hEu, _root_.map_add, LinearMap.map_smul,
          LinearMap.map_smul, _root_.map_mul, Algebra.smul_def, Algebra.smul_def]
        ring
      rw [hid]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hρ)
      rw [sq]
      exact Ideal.mul_mem_mul (chartGerm_mem_maximalIdeal hv₀ hu')
        (chartGerm_mem_maximalIdeal hv₀ hw)
    refine ⟨f u * c, f u • w + c • (u - f u • v₀),
      Submodule.add_mem _ (Submodule.smul_mem _ _ hw) (Submodule.smul_mem _ _ hu'), ?_⟩
    exact hgoal _

/-- A fraction with denominator a power of the chart vector lies in the maximal ideal exactly
when its numerator vanishes at the point. -/
public theorem chartFraction_mem_maximalIdeal_iff {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x)
    {d : ℕ} {z : SymmetricAlgebra k V} (hz : z ∈ SymPow.symmetricPower d k V) :
    chartFraction hv₀ hz ∈ maximalIdeal (localRing x) ↔ z ∈ x.asHomogeneousIdeal.toIdeal :=
  mk_mem_maximalIdeal_iff x _

/-- An extension to the local ring agrees with the original map on the ground field. -/
public theorem fractionLift_algebraMap {T : Type w} [CommRing T]
    (x : projectiveSpaceOfModule k V) (g : SymmetricAlgebra k V →+* T)
    (hg : ∀ s : x.asHomogeneousIdeal.toIdeal.primeCompl, IsUnit (g s)) (c : k) :
    fractionLift x g hg (algebraMap k (localRing x) c) =
      g (algebraMap k (SymmetricAlgebra k V) c) := by
  change IsLocalization.lift (M := x.asHomogeneousIdeal.toIdeal.primeCompl)
      (S := Localization x.asHomogeneousIdeal.toIdeal.primeCompl) hg
      (algebraMap k (localRing x) c).val = _
  rw [val_algebraMap_homogeneousLocalization, Localization.mk_one_eq_algebraMap,
    IsLocalization.lift_eq]

/-! ### Injectivity: first-order expansion in the dual numbers -/

/-- The first-order expansion of a degree-one form at `x` in the chart `v₀` along a functional
`μ`: the value of the form at `x`, plus `μ` of it times the chart vector as a nilpotent. -/
public def dualNumberLiftMap (x : projectiveSpaceOfModule k V) (v₀ : V) (μ : Module.Dual k V) :
    V →ₗ[k] DualNumber (coneResidueField x) where
  toFun v := TrivSqZeroExt.inl (toConeResidueFieldₐ x (SymmetricAlgebra.ι k V v)) +
    TrivSqZeroExt.inr (μ v • toConeResidueFieldₐ x (SymmetricAlgebra.ι k V v₀))
  map_add' v w := by
    simp only [map_add, add_smul, TrivSqZeroExt.inl_add, TrivSqZeroExt.inr_add]
    abel
  map_smul' c v := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [mul_smul]

/-- The `k`-algebra map recording the value at `x` together with the first-order term along a
functional `μ`, read in the chart `v₀`. -/
public def dualNumberLift (x : projectiveSpaceOfModule k V) (v₀ : V) (μ : Module.Dual k V) :
    SymmetricAlgebra k V →ₐ[k] DualNumber (coneResidueField x) :=
  SymmetricAlgebra.lift (dualNumberLiftMap x v₀ μ)

/-- The value part of the first-order expansion is the residue map. -/
@[simp]
public theorem fst_dualNumberLift (x : projectiveSpaceOfModule k V) (v₀ : V)
    (μ : Module.Dual k V) (z : SymmetricAlgebra k V) :
    (dualNumberLift x v₀ μ z).fst = toConeResidueField x z := by
  have hcomp : (TrivSqZeroExt.fstHom k (coneResidueField x) (coneResidueField x)).comp
      (dualNumberLift x v₀ μ) = toConeResidueFieldₐ x := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [dualNumberLift, dualNumberLiftMap, SymmetricAlgebra.lift_ι_apply]
  exact DFunLike.congr_fun hcomp z

/-- The first-order expansion of a degree-one form. -/
@[simp]
public theorem dualNumberLift_ι (x : projectiveSpaceOfModule k V) (v₀ : V)
    (μ : Module.Dual k V) (v : V) :
    dualNumberLift x v₀ μ (SymmetricAlgebra.ι k V v) = dualNumberLiftMap x v₀ μ v :=
  SymmetricAlgebra.lift_ι_apply _ v

/-- A homogeneous coordinate not vanishing at `x` has invertible first-order expansion. -/
public theorem isUnit_dualNumberLift (x : projectiveSpaceOfModule k V) (v₀ : V)
    (μ : Module.Dual k V) {s : SymmetricAlgebra k V}
    (hs : s ∉ x.asHomogeneousIdeal.toIdeal) : IsUnit (dualNumberLift x v₀ μ s) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr <| by
    rw [fst_dualNumberLift]
    exact isUnit_toConeResidueField x hs

/-- The first-order expansion, extended to the local ring at `x`. -/
public def dualNumberHom (x : projectiveSpaceOfModule k V) (v₀ : V) (μ : Module.Dual k V) :
    localRing x →+* DualNumber (coneResidueField x) :=
  fractionLift x (dualNumberLift x v₀ μ).toRingHom fun s => isUnit_dualNumberLift x v₀ μ s.2

/-- The first-order expansion clears denominators on the local ring. -/
public theorem dualNumberHom_mk_mul (x : projectiveSpaceOfModule k V) (v₀ : V)
    (μ : Module.Dual k V)
    (y : HomogeneousLocalization.NumDenSameDeg (fun n => SymPow.symmetricPower n k V)
      x.asHomogeneousIdeal.toIdeal.primeCompl) :
    dualNumberHom x v₀ μ (HomogeneousLocalization.mk y) *
        dualNumberLift x v₀ μ (y.den : _) = dualNumberLift x v₀ μ (y.num : _) :=
  fractionLift_mk_mul x _ _ y

/-- An element of the maximal ideal has vanishing value part. -/
public theorem fst_dualNumberHom_eq_zero (x : projectiveSpaceOfModule k V) (v₀ : V)
    (μ : Module.Dual k V) {ξ : localRing x} (hξ : ξ ∈ maximalIdeal (localRing x)) :
    (dualNumberHom x v₀ μ ξ).fst = 0 := by
  obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective ξ
  have hfst := congrArg TrivSqZeroExt.fst (dualNumberHom_mk_mul x v₀ μ y)
  rw [TrivSqZeroExt.fst_mul, fst_dualNumberLift, fst_dualNumberLift,
    (toConeResidueField_eq_zero_iff x _).mpr ((mk_mem_maximalIdeal_iff x y).mp hξ)] at hfst
  exact (mul_eq_zero.mp hfst).resolve_right
    fun hd => (isUnit_toConeResidueField x y.den_mem).ne_zero hd

/-- The square of the maximal ideal dies under the first-order expansion. -/
public theorem maximalIdeal_sq_le_ker_dualNumberHom (x : projectiveSpaceOfModule k V) (v₀ : V)
    (μ : Module.Dual k V) :
    maximalIdeal (localRing x) ^ 2 ≤ RingHom.ker (dualNumberHom x v₀ μ) := by
  rw [sq]
  refine Ideal.mul_le.mpr fun a ha b hb => ?_
  have hfa := fst_dualNumberHom_eq_zero x v₀ μ ha
  have hfb := fst_dualNumberHom_eq_zero x v₀ μ hb
  rw [RingHom.mem_ker, _root_.map_mul]
  refine TrivSqZeroExt.ext ?_ ?_
  · simp [TrivSqZeroExt.fst_mul, hfa]
  · simp [TrivSqZeroExt.snd_mul, hfa, hfb]

/-- **Injectivity of the chart description of the cotangent space.** A degree-one form whose
affine coordinate at `x` lies in `𝔪_x²` is zero. -/
public theorem eq_zero_of_chartGerm_mem_maximalIdeal_sq {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) {w : V}
    (h : chartGerm x hv₀ w ∈ maximalIdeal (localRing x) ^ 2) : w = 0 := by
  by_contra hne
  obtain ⟨μ, hμ⟩ := Module.Projective.exists_dual_eq_one k hne
  have hzero : dualNumberHom x v₀ μ (chartGerm x hv₀ w) = 0 :=
    RingHom.mem_ker.mp (maximalIdeal_sq_le_ker_dualNumberHom x v₀ μ h)
  have hmul : dualNumberHom x v₀ μ (chartGerm x hv₀ w) *
      dualNumberLift x v₀ μ (SymmetricAlgebra.ι k V v₀) =
      dualNumberLift x v₀ μ (SymmetricAlgebra.ι k V w) :=
    dualNumberHom_mk_mul x v₀ μ ⟨1, ⟨SymmetricAlgebra.ι k V w, ι_mem_symmetricPower_one k V w⟩,
      ⟨SymmetricAlgebra.ι k V v₀, ι_mem_symmetricPower_one k V v₀⟩, ι_mem_primeCompl hv₀⟩
  rw [hzero, zero_mul] at hmul
  have hsnd := congrArg TrivSqZeroExt.snd hmul
  simp only [dualNumberLift_ι, dualNumberLiftMap, LinearMap.coe_mk, AddHom.coe_mk,
    TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr,
    TrivSqZeroExt.snd_zero, zero_add, hμ, one_smul, toConeResidueFieldₐ_apply] at hsnd
  exact (isUnit_toConeResidueField x (ι_mem_primeCompl hv₀)).ne_zero hsnd.symm

/-! ### Surjectivity of the chart description -/

/-- The residue map sends a scalar to that scalar. -/
@[simp]
public theorem toConeResidueField_algebraMap (x : projectiveSpaceOfModule k V) (c : k) :
    toConeResidueField x (algebraMap k (SymmetricAlgebra k V) c) =
      algebraMap k (coneResidueField x) c :=
  (toConeResidueFieldₐ x).commutes c

/-- The residue map of the local ring sends a scalar to that scalar. -/
@[simp]
public theorem residueHom_algebraMap (x : projectiveSpaceOfModule k V) (c : k) :
    residueHom x (algebraMap k (localRing x) c) = algebraMap k (coneResidueField x) c :=
  (fractionLift_algebraMap x _ _ c).trans (toConeResidueField_algebraMap x c)

/-- A scalar lies in the maximal ideal of the local ring only if it is zero. -/
@[simp]
public theorem algebraMap_mem_maximalIdeal_iff (x : projectiveSpaceOfModule k V) (c : k) :
    algebraMap k (localRing x) c ∈ maximalIdeal (localRing x) ↔ c = 0 := by
  rw [maximalIdeal_eq_ker_residueHom, RingHom.mem_ker, residueHom_algebraMap]
  exact map_eq_zero_iff _ (algebraMap k (coneResidueField x)).injective

/-- **Inverting the value of a homogeneous coordinate.** For `s` of degree `d` not vanishing at
a rational point `x`, the fraction `v₀ ^ d / s` differs from the inverse of the value of `s` at
`x` by an element of `𝔪_x`. -/
public theorem mk_pow_sub_algebraMap_mem_maximalIdeal
    (hfx : pointSubmodule k V x = LinearMap.ker f) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (hf1 : f v₀ = 1) {d : ℕ}
    {s : SymmetricAlgebra k V} (hs : s ∈ SymPow.symmetricPower d k V)
    (hsP : s ∈ x.asHomogeneousIdeal.toIdeal.primeCompl)
    (htd : SymmetricAlgebra.ι k V v₀ ^ d ∈ SymPow.symmetricPower d k V) :
    HomogeneousLocalization.mk
        (⟨d, ⟨SymmetricAlgebra.ι k V v₀ ^ d, htd⟩, ⟨s, hs⟩, hsP⟩ :
          HomogeneousLocalization.NumDenSameDeg (fun n => SymPow.symmetricPower n k V)
            x.asHomogeneousIdeal.toIdeal.primeCompl) -
        algebraMap k (localRing x) (evalDual f s)⁻¹ ∈ maximalIdeal (localRing x) := by
  have hev : evalDual f s ≠ 0 := fun h => hsP ((evalDual_eq_zero_iff hfx hv₀ hf1 hs).mp h)
  have hden : toConeResidueField x s ≠ 0 :=
    fun hd => (isUnit_toConeResidueField x hsP).ne_zero hd
  have hP : (evalDual f s)⁻¹ • s - SymmetricAlgebra.ι k V v₀ ^ d ∈
      x.asHomogeneousIdeal.toIdeal :=
    mem_of_smul_mem hev (by
      simpa [smul_sub, smul_smul, hev] using sub_evalDual_smul_pow_mem hfx hf1 hs)
  have h2 : toConeResidueField x ((evalDual f s)⁻¹ • s) =
      toConeResidueField x (SymmetricAlgebra.ι k V v₀ ^ d) := by
    rw [← sub_eq_zero, ← map_sub]
    exact (toConeResidueField_eq_zero_iff x _).mpr hP
  rw [maximalIdeal_eq_ker_residueHom, RingHom.mem_ker, map_sub, sub_eq_zero,
    residueHom_algebraMap]
  refine mul_right_cancel₀ hden ?_
  rw [residueHom_mk_mul x, ← toConeResidueField_algebraMap, ← _root_.map_mul,
    ← Algebra.smul_def, h2]

/-- **Surjectivity of the chart description of the cotangent space.** At a rational point, every
element of the maximal ideal agrees modulo `𝔪_x²` with the affine coordinate of a degree-one
form vanishing at the point. -/
public theorem exists_sub_chartGerm_mem_maximalIdeal_sq
    (hfx : pointSubmodule k V x = LinearMap.ker f) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (hf1 : f v₀ = 1) {ξ : localRing x}
    (hξ : ξ ∈ maximalIdeal (localRing x)) :
    ∃ w ∈ pointSubmodule k V x,
      ξ - chartGerm x hv₀ w ∈ maximalIdeal (localRing x) ^ 2 := by
  obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective ξ
  have htd : SymmetricAlgebra.ι k V v₀ ^ y.deg ∈ SymPow.symmetricPower y.deg k V := by
    simpa using SetLike.pow_mem_graded y.deg (ι_mem_symmetricPower_one k V v₀)
  have ha : chartFraction hv₀ y.num.2 ∈ maximalIdeal (localRing x) :=
    (chartFraction_mem_maximalIdeal_iff hv₀ y.num.2).mpr ((mk_mem_maximalIdeal_iff x y).mp hξ)
  have hbc : HomogeneousLocalization.mk
      (⟨y.deg, ⟨SymmetricAlgebra.ι k V v₀ ^ y.deg, htd⟩, y.den, y.den_mem⟩ :
        HomogeneousLocalization.NumDenSameDeg (fun n => SymPow.symmetricPower n k V)
          x.asHomogeneousIdeal.toIdeal.primeCompl) -
      algebraMap k (localRing x) (evalDual f (y.den : SymmetricAlgebra k V))⁻¹ ∈
        maximalIdeal (localRing x) :=
    mk_pow_sub_algebraMap_mem_maximalIdeal hfx hv₀ hf1 y.den.2 y.den_mem htd
  have hab : (HomogeneousLocalization.mk y : localRing x) = chartFraction hv₀ y.num.2 *
      HomogeneousLocalization.mk
        ⟨y.deg, ⟨SymmetricAlgebra.ι k V v₀ ^ y.deg, htd⟩, y.den, y.den_mem⟩ := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, val_chartFraction, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists]
    exact ⟨1, by push_cast; ring⟩
  obtain ⟨c₂, w₂, hw₂, hind⟩ :=
    exists_chartFraction_sub_mem_maximalIdeal_sq hfx hv₀ hf1 y.num.2
  have hc₂ : c₂ = 0 := by
    refine (algebraMap_mem_maximalIdeal_iff x c₂).mp ?_
    have hmem := Ideal.sub_mem _ (Ideal.sub_mem _ ha (Ideal.pow_le_self two_ne_zero hind))
      (chartGerm_mem_maximalIdeal hv₀ hw₂)
    have heq : chartFraction hv₀ y.num.2 -
        (chartFraction hv₀ y.num.2 - algebraMap k (localRing x) c₂ - chartGerm x hv₀ w₂) -
        chartGerm x hv₀ w₂ = algebraMap k (localRing x) c₂ := by ring
    rwa [heq] at hmem
  rw [hc₂, _root_.map_zero, sub_zero] at hind
  set c : k := (evalDual f (y.den : SymmetricAlgebra k V))⁻¹
  refine ⟨c • w₂, Submodule.smul_mem _ _ hw₂, ?_⟩
  have hsplit : (HomogeneousLocalization.mk y : localRing x) - chartGerm x hv₀ (c • w₂) =
      chartFraction hv₀ y.num.2 *
        (HomogeneousLocalization.mk
            (⟨y.deg, ⟨SymmetricAlgebra.ι k V v₀ ^ y.deg, htd⟩, y.den, y.den_mem⟩ :
              HomogeneousLocalization.NumDenSameDeg (fun n => SymPow.symmetricPower n k V)
                x.asHomogeneousIdeal.toIdeal.primeCompl) -
          algebraMap k (localRing x) c) +
        algebraMap k (localRing x) c *
          (chartFraction hv₀ y.num.2 - chartGerm x hv₀ w₂) := by
    rw [LinearMap.map_smul, Algebra.smul_def, hab]
    ring
  rw [hsplit]
  refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hind)
  rw [sq]
  exact Ideal.mul_mem_mul ha hbc

/-! ### The cotangent space at a rational point -/

/-- **The cotangent vector of a degree-one form vanishing at `x`**, read in the chart `v₀`: the
class of the affine coordinate `w / v₀` in `𝔪_x / 𝔪_x²`. -/
public def cotangentMk (x : projectiveSpaceOfModule k V) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) :
    ↥(pointSubmodule k V x) →ₗ[k] CotangentSpace (localRing x) :=
  (Ideal.toCotangent (maximalIdeal (localRing x))).restrictScalars k ∘ₗ
    LinearMap.codRestrict ((maximalIdeal (localRing x)).restrictScalars k)
      ((chartGerm x hv₀).comp (pointSubmodule k V x).subtype)
      fun w => chartGerm_mem_maximalIdeal hv₀ w.2

/-- The cotangent vector of `w` is the class in `𝔪_x / 𝔪_x²` of its chart germ
`chartGerm x hv₀ w`. -/
@[simp]
public theorem cotangentMk_apply (x : projectiveSpaceOfModule k V) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (w : ↥(pointSubmodule k V x)) :
    cotangentMk x hv₀ w =
      Ideal.toCotangent _ ⟨chartGerm x hv₀ (w : V), chartGerm_mem_maximalIdeal hv₀ w.2⟩ :=
  rfl

/-- The cotangent vector of `w` is the class of `ξ` as soon as `ξ` and `chartGerm x hv₀ w`
differ by an element of `𝔪_x²`. -/
private theorem cotangentMk_eq_toCotangent {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x)
    (w : ↥(pointSubmodule k V x)) (ξ : maximalIdeal (localRing x))
    (h : (ξ : localRing x) - chartGerm x hv₀ w ∈ maximalIdeal (localRing x) ^ 2) :
    cotangentMk x hv₀ w = Ideal.toCotangent _ ξ := by
  rw [cotangentMk_apply, eq_comm, ← sub_eq_zero, ← map_sub, Ideal.toCotangent_eq_zero]
  simpa using h

/-- A functional cutting out the hyperplane of a rational point can be normalised to take the
value one at any chart vector. -/
public theorem exists_ker_eq_and_apply_eq_one
    (hx : ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) :
    ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g ∧ g v₀ = 1 := by
  obtain ⟨g, hgx⟩ := hx
  have hgv := apply_ne_zero_of_notMem_pointSubmodule hgx hv₀
  exact ⟨(g v₀)⁻¹ • g, hgx.trans (LinearMap.ker_smul g _ (inv_ne_zero hgv)).symm,
    by simp [inv_mul_cancel₀ hgv]⟩

/-- **Every cotangent vector at a rational point is the class of an affine coordinate**, with no
normalisation imposed on the defining functional. -/
public theorem exists_sub_chartGerm_mem_sq
    (hx : ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) {ξ : localRing x}
    (hξ : ξ ∈ maximalIdeal (localRing x)) :
    ∃ w ∈ pointSubmodule k V x,
      ξ - chartGerm x hv₀ w ∈ maximalIdeal (localRing x) ^ 2 := by
  obtain ⟨g, hgx, hg1⟩ := exists_ker_eq_and_apply_eq_one hx hv₀
  exact exists_sub_chartGerm_mem_maximalIdeal_sq hgx hv₀ hg1 hξ

/-- **The affine coordinates give a bijection between the degree-one forms vanishing at a
rational point and the cotangent space there.** -/
public theorem bijective_cotangentMk
    (hx : ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) : Function.Bijective (cotangentMk x hv₀) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker, cotangentMk_apply, Ideal.toCotangent_eq_zero] at ha
    exact Subtype.ext (eq_zero_of_chartGerm_mem_maximalIdeal_sq hv₀ ha)
  · intro ζ
    obtain ⟨ξ, rfl⟩ := Ideal.toCotangent_surjective _ ζ
    obtain ⟨w, hw, hd⟩ := exists_sub_chartGerm_mem_sq hx hv₀ ξ.2
    exact ⟨⟨w, hw⟩, cotangentMk_eq_toCotangent hv₀ _ _ hd⟩

/-- **The cotangent space of `𝐏(V)` at a rational point is the hyperplane `W_x` of degree-one
forms vanishing there**, a form `w` corresponding to the class of the affine coordinate
`w / v₀`. The chart vector `v₀` only shifts the identification by `𝔪_x²`, by
`chartGerm_sub_chartGerm_mem_maximalIdeal_sq`. -/
public def cotangentEquiv (hx : ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g)
    {v₀ : V} (hv₀ : v₀ ∉ pointSubmodule k V x) :
    ↥(pointSubmodule k V x) ≃ₗ[k] CotangentSpace (localRing x) :=
  LinearEquiv.ofBijective (cotangentMk x hv₀) (bijective_cotangentMk hx hv₀)

/-- The identification `cotangentEquiv hx hv₀` sends `w` to its cotangent vector
`cotangentMk x hv₀ w`. -/
@[simp]
public theorem cotangentEquiv_apply
    (hx : ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (w : ↥(pointSubmodule k V x)) :
    cotangentEquiv hx hv₀ w = cotangentMk x hv₀ w :=
  rfl

/-! ### Transport to the stalk of the structure sheaf -/

/-- A `k`-algebra isomorphism of local rings carries the maximal ideal into the maximal ideal. -/
public theorem maximalIdeal_le_comap_of_algEquiv {R S : Type w} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S) :
    maximalIdeal R ≤ Ideal.comap e.toAlgHom (maximalIdeal S) := by
  intro a ha
  rw [Ideal.mem_comap, mem_maximalIdeal]
  intro hu
  exact (mem_maximalIdeal a).mp ha (by simpa using hu.map (e.symm : S →+* R))

/-- **A `k`-algebra isomorphism of local rings identifies their cotangent spaces.** -/
public def cotangentSpaceCongr {R S : Type w} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [Algebra k R] [Algebra k S] (e : R ≃ₐ[k] S) :
    CotangentSpace R ≃ₗ[k] CotangentSpace S :=
  LinearEquiv.ofLinearMap
    (Ideal.mapCotangent _ _ e.toAlgHom (maximalIdeal_le_comap_of_algEquiv e))
    (Ideal.mapCotangent _ _ e.symm.toAlgHom (maximalIdeal_le_comap_of_algEquiv e.symm))
    (by
      refine LinearMap.ext fun ζ => ?_
      obtain ⟨ξ, rfl⟩ := Ideal.toCotangent_surjective _ ζ
      rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent,
        LinearMap.id_apply]
      congr 1
      exact Subtype.ext (e.apply_symm_apply _))
    (by
      refine LinearMap.ext fun ζ => ?_
      obtain ⟨ξ, rfl⟩ := Ideal.toCotangent_surjective _ ζ
      rw [LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent,
        LinearMap.id_apply]
      congr 1
      exact Subtype.ext (e.symm_apply_apply _))

/-- The stalk of the structure sheaf of `𝐏(V)` at a point, identified with the local ring there
by Mathlib's `AlgebraicGeometry.Proj.stalkIso`. -/
public def stalkRingEquiv (x : projectiveSpaceOfModule k V) :
    (projectiveSpaceOfModule k V).presheaf.stalk x ≃+* localRing x :=
  (Proj.stalkIso (fun n => SymPow.symmetricPower n k V) x).commRingCatIsoToRingEquiv

/-- The ground field acts on the stalk of `𝐏(V)` at a point through the identification of the
stalk with the local ring there. -/
public instance algebraStalk (x : projectiveSpaceOfModule k V) :
    Algebra k ((projectiveSpaceOfModule k V).presheaf.stalk x) :=
  (((stalkRingEquiv x).symm : localRing x →+* _).comp (algebraMap k (localRing x))).toAlgebra

/-- The identification of the stalk with the local ring is a `k`-algebra isomorphism. -/
public def stalkAlgEquiv (x : projectiveSpaceOfModule k V) :
    (projectiveSpaceOfModule k V).presheaf.stalk x ≃ₐ[k] localRing x :=
  AlgEquiv.ofRingEquiv (f := stalkRingEquiv x) fun _ => (stalkRingEquiv x).apply_symm_apply _

/-- **The cotangent space of a projective space at a rational point.** For a point `x` of `𝐏(V)`
whose degree-one forms `W_x` form a hyperplane — equivalently, a rational point — the cotangent
space `𝔪_x / 𝔪_x²` of the stalk at `x` is `W_x`, a form `w` going to the class of the affine
coordinate `w / v₀` for any degree-one form `v₀` not vanishing at `x`. -/
public def stalkCotangentEquiv
    (hx : ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) :
    ↥(pointSubmodule k V x) ≃ₗ[k]
      CotangentSpace ((projectiveSpaceOfModule k V).presheaf.stalk x) :=
  (cotangentEquiv hx hv₀).trans (cotangentSpaceCongr (stalkAlgEquiv x).symm)

/-- Over an algebraically closed field the degree-one forms vanishing at a closed point of
`𝐏(V)` are the kernel of a linear functional, so such a point is rational. -/
public theorem exists_pointSubmodule_eq_ker_of_isClosed [IsAlgClosed k] [Module.Finite k V]
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V))) :
    ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g := by
  obtain ⟨g, hg, rfl⟩ := exists_eq_linearFunctionalPoint k V x hx
  exact ⟨g, pointSubmodule_linearFunctionalPoint k V g hg⟩

/-- **The cotangent space of a projective space at a closed point.** Over an algebraically closed
field the cotangent space of `𝐏(V)` at a closed point `x` is the hyperplane `W_x` of degree-one
forms vanishing at `x`. -/
public def stalkCotangentEquivOfIsClosed [IsAlgClosed k] [Module.Finite k V]
    (hx : IsClosed ({x} : Set (projectiveSpaceOfModule k V))) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) :
    ↥(pointSubmodule k V x) ≃ₗ[k]
      CotangentSpace ((projectiveSpaceOfModule k V).presheaf.stalk x) :=
  stalkCotangentEquiv (exists_pointSubmodule_eq_ker_of_isClosed hx) hv₀

/-! ### Independence of the chart, on the cotangent space -/

/-- **The cotangent vector of a degree-one form does not depend on the chart.** Two degree-one
forms not vanishing at `x` and agreeing there give literally the same map `W_x → 𝔪_x / 𝔪_x²`,
so the identification of the cotangent space is canonical even though it is computed in a
chart. -/
public theorem cotangentMk_indep {v₀ v₁ : V} (hv₀ : v₀ ∉ pointSubmodule k V x)
    (hv₁ : v₁ ∉ pointSubmodule k V x) (hsub : v₀ - v₁ ∈ pointSubmodule k V x) :
    cotangentMk x hv₀ = cotangentMk x hv₁ := by
  refine LinearMap.ext fun w => ?_
  rw [cotangentMk_apply x hv₁]
  exact cotangentMk_eq_toCotangent hv₀ w _
    (chartGerm_sub_chartGerm_mem_maximalIdeal_sq hv₀ hv₁ hsub w.2)

/-- The identification of the cotangent space does not depend on the chart. -/
public theorem cotangentEquiv_indep
    (hx : ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g) {v₀ v₁ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (hv₁ : v₁ ∉ pointSubmodule k V x)
    (hsub : v₀ - v₁ ∈ pointSubmodule k V x) (w : ↥(pointSubmodule k V x)) :
    cotangentEquiv hx hv₀ w = cotangentEquiv hx hv₁ w := by
  rw [cotangentEquiv_apply, cotangentEquiv_apply, cotangentMk_indep hv₀ hv₁ hsub]

/-- **Any chart at `x` can be normalised against a given one**, and the cotangent vectors then
agree on the nose. Two degree-one forms not vanishing at `x` need not agree at `x`, so
`cotangentMk_indep` does not apply to them directly; rescaling one of them by the ratio of
their values repairs that, which is what makes a conormal submodule defined in one chart
computable in any other. -/
public theorem exists_smul_cotangentMk_eq
    (hx : ∃ g : Module.Dual k V, pointSubmodule k V x = LinearMap.ker g) {v₀ v₁ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (hv₁ : v₁ ∉ pointSubmodule k V x) :
    ∃ (c : k) (hc : c • v₁ ∉ pointSubmodule k V x), cotangentMk x hv₀ = cotangentMk x hc := by
  obtain ⟨g, hgx⟩ := hx
  have hg0 := apply_ne_zero_of_notMem_pointSubmodule hgx hv₀
  have hg1 := apply_ne_zero_of_notMem_pointSubmodule hgx hv₁
  have hsub : v₀ - (g v₀ / g v₁) • v₁ ∈ pointSubmodule k V x :=
    sub_smul_mem_pointSubmodule hgx (div_mul_cancel₀ _ hg1).symm
  have hmem : (g v₀ / g v₁) • v₁ ∉ pointSubmodule k V x := fun h => by
    simpa using hv₀ (by simpa using Submodule.add_mem _ hsub h)
  exact ⟨g v₀ / g v₁, hmem, cotangentMk_indep hv₀ hmem hsub⟩

/-! ### The cotangent map of a linear projection -/

/-- **The projection away from `W` on hyperplanes.** The degree-one forms on `W` vanishing at
the image of a point `z` of the domain of the projection are exactly those vanishing at `z`,
that is, `W ⊓ W_z` read inside `W`. -/
public theorem pointSubmodule_projection (W : Submodule k V)
    (z : (mapDomain (fun n => SymPow.symmetricPower n k ↥W)
      (fun n => SymPow.symmetricPower n k V)
      (SymPow.gradedSymAlgMap W.subtype)).toScheme) :
    pointSubmodule k ↥W (projection k V W z) =
      (pointSubmodule k V z.val).comap W.subtype := by
  ext w
  rw [Submodule.mem_comap, mem_pointSubmodule_iff,
    mem_projection_iff k V W z Nat.one_pos (ι_mem_symmetricPower_one k ↥W w), SymPow.symAlgMap_ι]
  exact (mem_pointSubmodule_iff k V z.val (w : V)).symm

/-- **The cotangent map of a linear projection hits the affine coordinates of `W ⊓ W_x`.**
Let `ψ` carry the local ring of `𝐏(W)` at the image point to the local ring of `𝐏(V)` at `x`,
taking affine coordinates to affine coordinates — which is what the stalk map of the projection
away from `W` does. Then the ideal generated by the image of the maximal ideal contains the
affine coordinate of every degree-one form that vanishes at `x` and lies in `W`.

This is the inclusion used to deduce unramifiedness; the reverse inclusion, which would need
that the affine coordinates generate the maximal ideal of `𝐏(W)` at the image point, is not
asserted. -/
public theorem span_chartGerm_inf_le_map_maximalIdeal {W : Submodule k V}
    {y : projectiveSpaceOfModule k ↥W}
    (hy : pointSubmodule k ↥W y = (pointSubmodule k V x).comap W.subtype)
    {w₀ : ↥W} (hw₀ : w₀ ∉ pointSubmodule k ↥W y) {v₀ : V}
    (hv₀ : v₀ ∉ pointSubmodule k V x) (ψ : localRing y →+* localRing x)
    (hψ : ∀ w : ↥W, ψ (chartGerm y hw₀ w) = chartGerm x hv₀ (w : V)) :
    Ideal.span (chartGerm x hv₀ '' (↑(W ⊓ pointSubmodule k V x) : Set V)) ≤
      (maximalIdeal (localRing y)).map ψ := by
  rw [Ideal.span_le]
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_inf] at hv
  have hmem : (⟨v, hv.1⟩ : ↥W) ∈ pointSubmodule k ↥W y := by
    rw [hy, Submodule.mem_comap]
    exact hv.2
  have hmap := Ideal.mem_map_of_mem ψ (chartGerm_mem_maximalIdeal hw₀ hmem)
  rwa [hψ ⟨v, hv.1⟩] at hmap

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
