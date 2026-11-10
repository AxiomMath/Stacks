module

public import StacksFrontier.AlgebraicGeometry.ModuleChartLocality.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationColimit

/-!
# The chart comparison of a degreewise base change of graded modules is invertible

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings and `f : M → N` a
`ψ`-semilinear map of graded modules preserving the gradings. Suppose that `ψ` and `f` are base
changes **degreewise** along `𝒜₀ ⟶ ℬ₀`: every homogeneous piece of `ℬ` is `ℬ₀ ⊗_{𝒜₀} 𝒜ₙ`, and
every homogeneous piece of `N` is `ℬ₀ ⊗_{𝒜₀} Mᵢ`. Then for every homogeneous `a` the coefficient
extension of the algebraic chart comparison

`ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎ ⟶ N₍ψ a₎`

is an isomorphism. This is the module companion of
`Stacks.Proj.awayTensorLift_bijective`, and it is the algebraic input of the base change of the
sheaf attached to a graded module.

The proof is the direct-limit presentation of the degree-zero localization, as for the ring. Every
element of the source is the image, under
`Stacks.AlgebraicGeometry.ModuleChartLocality.stageMap`, of an element of `ℬ₀ ⊗_{𝒜₀} M_{k d}` for
a single `k`: a coefficient `x / (ψ a) ^ j` is a sum of `b • ψ y` by the degreewise base change of
the ring, and `ψ y / (ψ a) ^ j` can be moved across the tensor sign. On that stage the comparison
is the degreewise identification `ℬ₀ ⊗_{𝒜₀} M_{k d} ≅ N_{k d}` followed by `n ↦ n / (ψ a) ^ k`,
so surjectivity is the identification on a numerator and injectivity is that an element killed by a
power of `ψ a` already dies at a later stage.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleChartLocality.TargetPiece`: a homogeneous piece of `N`, as a
  module over `𝒜₀` through `𝒜₀ ⟶ ℬ₀`.
* `Stacks.AlgebraicGeometry.ModuleChartLocality.modulePieceMap`: the degree-`i` component of `f`, as
  a map of `𝒜₀`-modules.

## Main results

* `Stacks.AlgebraicGeometry.ModuleChartLocality.isIso_moduleDegreeZeroExtension`: **the coefficient
  extension of the chart comparison is an isomorphism** for a degreewise base change.

## References

* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory HomogeneousLocalization TensorProduct
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.ModuleChartLocality

attribute [local instance] instVAddNatIntModuleChart

/-! ### One graded module -/

section OneModule

variable {A M : Type u} {μ : Type u} [CommRing A] [AddCommGroup M] [Module A M]
  {𝒜 : ℕ → AddSubgroup A} [GradedRing 𝒜] [SetLike μ M] [AddSubgroupClass μ M]
  {𝒨 : ℤ → μ} [DirectSum.Decomposition 𝒨] [SetLike.GradedSMul 𝒜 𝒨]

/-- A homogeneous element times a homogeneous element of the module is homogeneous of the degree
given by any equal sum of degrees. -/
private theorem smul_mem_piece_of_add_eq {R P ρ π : Type u} [CommRing R] [AddCommGroup P]
    [Module R P] [SetLike ρ R] [AddSubgroupClass ρ R] [SetLike π P] {ℛ : ℕ → ρ} {𝒬 : ℤ → π}
    [SetLike.GradedSMul ℛ 𝒬] {e : ℕ} {k n : ℤ} (h : (e : ℤ) + k = n) {y : R} (hy : y ∈ ℛ e)
    {x : P} (hx : x ∈ 𝒬 k) : y • x ∈ 𝒬 n := by
  subst h
  exact SetLike.GradedSMul.smul_mem hy hx

omit [GradedRing 𝒜] [AddSubgroupClass μ M] [DirectSum.Decomposition 𝒨] in
/-- The degree-zero part of the ring preserves every homogeneous piece of the module. -/
public theorem zero_smul_mem_piece {i : ℤ} (r : ↥(𝒜 0)) {x : M} (hx : x ∈ 𝒨 i) :
    (r : A) • x ∈ 𝒨 i :=
  smul_mem_piece_of_add_eq (by simp) r.2 hx

/-- A homogeneous piece of a graded module is a module over the degree-zero part of the ring. -/
public instance modulePieceModule (i : ℤ) : Module ↥(𝒜 0) ↥(𝒨 i) where
  smul r x := ⟨(r : A) • (x : M), zero_smul_mem_piece r x.2⟩
  one_smul x := Subtype.ext (by
    change ((1 : ↥(𝒜 0)) : A) • (x : M) = x
    rw [SetLike.GradeZero.coe_one, one_smul])
  mul_smul r s x := Subtype.ext (by
    change ((r * s : ↥(𝒜 0)) : A) • (x : M) = (r : A) • (s : A) • (x : M)
    rw [SetLike.GradeZero.coe_mul, mul_smul])
  smul_zero r := Subtype.ext (smul_zero (r : A))
  smul_add r x y := Subtype.ext (smul_add (r : A) (x : M) y)
  add_smul r s x := Subtype.ext (by
    change ((r + s : ↥(𝒜 0)) : A) • (x : M) = (r : A) • (x : M) + (s : A) • (x : M)
    rw [AddMemClass.coe_add, add_smul])
  zero_smul x := Subtype.ext (by
    change ((0 : ↥(𝒜 0)) : A) • (x : M) = 0
    rw [ZeroMemClass.coe_zero, zero_smul])

omit [DirectSum.Decomposition 𝒨] in
@[simp] public theorem coe_modulePiece_smul {i : ℤ} (r : ↥(𝒜 0)) (x : ↥(𝒨 i)) :
    ((r • x : ↥(𝒨 i)) : M) = (r : A) • (x : M) := rfl

variable {d : ℕ} {a : A} (ha : a ∈ 𝒜 d)

omit [AddSubgroupClass μ M] [DirectSum.Decomposition 𝒨] in
include ha in
/-- Multiplying a numerator of degree `k d` by `a ^ (l - k)` gives one of degree `l d`. -/
public theorem pow_smul_mem_piece {k l : ℕ} (h : k ≤ l) {x : M} (hx : x ∈ 𝒨 ((k * d : ℕ) : ℤ)) :
    a ^ (l - k) • x ∈ 𝒨 ((l * d : ℕ) : ℤ) :=
  smul_mem_piece_of_add_eq
    (by rw [smul_eq_mul, ← Nat.cast_add, ← Nat.add_mul, Nat.sub_add_cancel h])
    (SetLike.pow_mem_graded (l - k) ha) hx

/-- Multiplication by `a ^ (l - k)`, from the numerators of degree `k d` to those of degree
`l d`, as a map of modules over the degree-zero part. -/
public def mulPowModPiece (k l : ℕ) (h : k ≤ l) :
    ↥(𝒨 ((k * d : ℕ) : ℤ)) →ₗ[↥(𝒜 0)] ↥(𝒨 ((l * d : ℕ) : ℤ)) where
  toFun x := ⟨a ^ (l - k) • (x : M), pow_smul_mem_piece ha h x.2⟩
  map_add' x y := Subtype.ext (smul_add _ (x : M) y)
  map_smul' r x := Subtype.ext (by
    change a ^ (l - k) • (r : A) • (x : M) = (r : A) • a ^ (l - k) • (x : M)
    exact smul_comm _ _ _)

omit [DirectSum.Decomposition 𝒨] in
@[simp] public theorem coe_mulPowModPiece (k l : ℕ) (h : k ≤ l) (x : ↥(𝒨 ((k * d : ℕ) : ℤ))) :
    (mulPowModPiece ha k l h x : M) = a ^ (l - k) • (x : M) := rfl

/-- **Enlarging the denominator does not change the fraction.** -/
public theorem fractionHom_mulPowModPiece (k l : ℕ) (h : k ≤ l) (x : ↥(𝒨 ((k * d : ℕ) : ℤ))) :
    Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha l (mulPowModPiece ha k l h x) =
      Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k x := by
  refine Subtype.ext ?_
  change LocalizedModule.mk (S := Submonoid.powers a) (a ^ (l - k) • (x : M)) ⟨a ^ l, ⟨l, rfl⟩⟩ =
    LocalizedModule.mk (S := Submonoid.powers a) (x : M) ⟨a ^ k, ⟨k, rfl⟩⟩
  refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
  simp only [Submonoid.smul_def, one_smul]
  change a ^ k • a ^ (l - k) • (x : M) = a ^ l • (x : M)
  rw [← mul_smul, ← pow_add, Nat.add_sub_cancel' h]

end OneModule

/-! ### Two graded modules -/

section TwoModules

variable {A B M N : Type u} {μ ν : Type u} [CommRing A] [CommRing B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
  {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν}
  [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul 𝒜 𝒨] [SetLike.GradedSMul ℬ 𝒩]

/-- A homogeneous piece of the target module, to be read as a module over the degree-zero part of
the source ring through `𝒜₀ ⟶ ℬ₀`. It is a type synonym for `𝒩 i` carrying the graded ring `ℬ`,
so that this module structure, which depends on `ℬ`, can be found by instance search. -/
public def TargetPiece (_ℬ : ℕ → AddSubgroup B) (𝒩 : ℤ → ν) (i : ℤ) : Type u :=
  ↥(𝒩 i)

namespace TargetPiece

variable (i : ℤ)

/-- An element of the target piece is an element of the homogeneous piece. -/
public def toPiece {i : ℤ} (x : TargetPiece ℬ 𝒩 i) : ↥(𝒩 i) := x

/-- An element of the homogeneous piece is an element of the target piece. -/
public def ofPiece {i : ℤ} (x : ↥(𝒩 i)) : TargetPiece ℬ 𝒩 i := x

omit [AddCommGroup N] [Module B N] [GradedRing ℬ] [AddSubgroupClass ν N] [DirectSum.Decomposition 𝒩]
  [SetLike.GradedSMul ℬ 𝒩] in
@[simp] public theorem toPiece_ofPiece {i : ℤ} (x : ↥(𝒩 i)) : toPiece (ofPiece (ℬ := ℬ) x) = x :=
  rfl

public instance : AddCommGroup (TargetPiece ℬ 𝒩 i) := inferInstanceAs (AddCommGroup ↥(𝒩 i))

public instance : Module ↥(ℬ 0) (TargetPiece ℬ 𝒩 i) :=
  inferInstanceAs (Module ↥(ℬ 0) ↥(𝒩 i))

variable [Algebra ↥(𝒜 0) ↥(ℬ 0)]

public instance : Module ↥(𝒜 0) (TargetPiece ℬ 𝒩 i) :=
  Module.compHom _ (algebraMap ↥(𝒜 0) ↥(ℬ 0))

public instance : IsScalarTower ↥(𝒜 0) ↥(ℬ 0) (TargetPiece ℬ 𝒩 i) :=
  ⟨fun x y z => by
    rw [Algebra.smul_def x y]
    exact mul_smul (algebraMap ↥(𝒜 0) ↥(ℬ 0) x) y z⟩

end TargetPiece

variable (ψ : 𝒜 →+*ᵍ ℬ) (f : M →ₛₗ[ψ.toRingHom] N) (hf : ∀ (i : ℤ) {m : M}, m ∈ 𝒨 i → f m ∈ 𝒩 i)
  [Algebra ↥(𝒜 0) ↥(ℬ 0)] (halg : ∀ r : ↥(𝒜 0), (algebraMap ↥(𝒜 0) ↥(ℬ 0) r : B) = ψ (r : A))

/-- **The degree-`i` component of `f`**, as a map of modules over the degree-zero part of the
source ring. -/
public def modulePieceMap (i : ℤ) : ↥(𝒨 i) →ₗ[↥(𝒜 0)] TargetPiece ℬ 𝒩 i where
  toFun x := TargetPiece.ofPiece ⟨f x, hf i x.2⟩
  map_add' x y := Subtype.ext (map_add f (x : M) y)
  map_smul' r x := Subtype.ext (by
    change f ((r : A) • (x : M)) = ((algebraMap ↥(𝒜 0) ↥(ℬ 0) r : ↥(ℬ 0)) : B) • f (x : M)
    rw [map_smulₛₗ, halg]
    rfl)

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
public theorem coe_modulePieceMap (i : ℤ) (x : ↥(𝒨 i)) :
    ((modulePieceMap ψ f hf halg i x).toPiece : N) = f x := rfl

/-! ### One chart -/

section Chart

/-- The degree-zero localization acts on the localized module through the ordinary localization;
this is the module structure the degree-zero part `GradedModuleDegreeZeroLocalization` is a
submodule for. -/
local instance awayModule' {R P : Type u} {ρ : Type u} [CommRing R] [AddCommGroup P] [Module R P]
    [SetLike ρ R] [AddSubgroupClass ρ R] (ℛ : ℕ → ρ) [GradedRing ℛ] (a : R) :
    Module (Away ℛ a) (LocalizedModule.Away (R := R) a P) :=
  Module.compHom _ (algebraMap (Away ℛ a) (Localization.Away a))

variable (𝒨) in
/-- The coefficient-extended source of the chart comparison, `ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎`. -/
public abbrev ExtSrc (a : A) : ModuleCat (Away ℬ (ψ a)) :=
  (ModuleCat.extendScalars (Away.map ψ a)).obj
    (ModuleCat.of (Away 𝒜 a) (GradedModuleDegreeZeroLocalization 𝒜 𝒨 a))

/-- A pure tensor of the coefficient-extended source. -/
public abbrev extTmul (a : A) (q : Away ℬ (ψ a))
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) : ExtSrc 𝒨 ψ a :=
  q ⊗ₜ[Away 𝒜 a, Away.map ψ a] z

omit [Algebra ↥(𝒜 0) ↥(ℬ 0)] in
/-- Scalars of the chart ring of `𝒜` move across the tensor sign through `Away.map ψ a`. -/
public theorem extTmul_smul (a : A) (q : Away ℬ (ψ a)) (p : Away 𝒜 a)
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    extTmul ψ a q (p • z) = extTmul ψ a (q * Away.map ψ a p) z := by
  have h := ((ModuleCat.extendRestrictScalarsAdj (Away.map ψ a)).unit.app
    (ModuleCat.of (Away 𝒜 a) (GradedModuleDegreeZeroLocalization 𝒜 𝒨 a))).hom.map_smul p z
  change extTmul ψ a 1 (p • z) = Away.map ψ a p • extTmul ψ a 1 z at h
  have h2 := congrArg (fun w => q • w) h
  change extTmul ψ a (q * 1) (p • z) = extTmul ψ a (q * (Away.map ψ a p * 1)) z at h2
  rwa [mul_one, mul_one] at h2

omit [Algebra ↥(𝒜 0) ↥(ℬ 0)] in
/-- The chart ring of `ℬ` acts on the left factor. -/
public theorem smul_extTmul (a : A) (q q' : Away ℬ (ψ a))
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    q • extTmul ψ a q' z = extTmul ψ a (q * q') z :=
  rfl

omit [Algebra ↥(𝒜 0) ↥(ℬ 0)] in
public theorem extTmul_add_right (a : A) (q : Away ℬ (ψ a))
    (z z' : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    extTmul ψ a q (z + z') = extTmul ψ a q z + extTmul ψ a q z' :=
  TensorProduct.tmul_add _ _ _

omit [Algebra ↥(𝒜 0) ↥(ℬ 0)] in
public theorem extTmul_add_left (a : A) (q q' : Away ℬ (ψ a))
    (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    extTmul ψ a (q + q') z = extTmul ψ a q z + extTmul ψ a q' z :=
  TensorProduct.add_tmul _ _ _

omit [Algebra ↥(𝒜 0) ↥(ℬ 0)] in
public theorem extTmul_zero_left (a : A) (z : GradedModuleDegreeZeroLocalization 𝒜 𝒨 a) :
    extTmul ψ a 0 z = 0 :=
  TensorProduct.zero_tmul _ _

omit [Algebra ↥(𝒜 0) ↥(ℬ 0)] in
public theorem extTmul_zero_right (a : A) (q : Away ℬ (ψ a)) :
    extTmul (𝒨 := 𝒨) ψ a q 0 = 0 :=
  TensorProduct.tmul_zero _ _

variable {d : ℕ} {a : A} (ha : a ∈ 𝒜 d)

/-- A degree-zero scalar of the ring acts on a fraction through its numerator. -/
public theorem fractionHom_zero_smul {R P : Type u} [CommRing R] [AddCommGroup P] [Module R P]
    {ℛ : ℕ → AddSubgroup R} [GradedRing ℛ] {π : Type u} [SetLike π P] [AddSubgroupClass π P]
    {𝒬 : ℤ → π}
    [DirectSum.Decomposition 𝒬] [SetLike.GradedSMul ℛ 𝒬] {e : ℕ} {c : R} (hc : c ∈ ℛ e) (k : ℕ)
    (r : ↥(ℛ 0)) (x : ↥(𝒬 ((k * e : ℕ) : ℤ))) :
    Stacks.SheafOfModules.fractionHom ℛ 𝒬 hc k (r • x) =
      fromZeroRingHom ℛ (Submonoid.powers c) r • Stacks.SheafOfModules.fractionHom ℛ 𝒬 hc k x := by
  refine Subtype.ext ?_
  change LocalizedModule.mk (S := Submonoid.powers c) ((r : R) • (x : P)) ⟨c ^ k, ⟨k, rfl⟩⟩ =
    (Localization.mk (r : R) 1 : Localization.Away c) •
      LocalizedModule.mk (S := Submonoid.powers c) (x : P) ⟨c ^ k, ⟨k, rfl⟩⟩
  rw [LocalizedModule.mk_smul_mk, one_mul]

/-- A homogeneous fraction of the ring acts on a fraction of the module by multiplying numerators
and denominators. -/
public theorem awayMk_smul_fractionHom (j k : ℕ) (y : A) (hy : y ∈ 𝒜 (j • d))
    (x : ↥(𝒨 ((k * d : ℕ) : ℤ))) (hyx : y • (x : M) ∈ 𝒨 (((j + k) * d : ℕ) : ℤ)) :
    Away.mk 𝒜 ha j y hy • Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k x =
      Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha (j + k) ⟨y • (x : M), hyx⟩ := by
  refine Subtype.ext ?_
  change (Localization.mk y ⟨a ^ j, ⟨j, rfl⟩⟩ : Localization.Away a) •
      LocalizedModule.mk (S := Submonoid.powers a) (x : M) ⟨a ^ k, ⟨k, rfl⟩⟩ =
    LocalizedModule.mk (S := Submonoid.powers a) (y • (x : M)) ⟨a ^ (j + k), ⟨j + k, rfl⟩⟩
  rw [LocalizedModule.mk_smul_mk]
  exact congrArg (LocalizedModule.mk (y • (x : M))) (Subtype.ext (pow_add a j k).symm)

omit [GradedRing 𝒜] [AddSubgroupClass μ M] [DirectSum.Decomposition 𝒨] in
/-- A homogeneous element of degree `j d` of the ring times a numerator of degree `k d` is a
numerator of degree `(j + k) d`. -/
public theorem smul_mem_piece_add {j k : ℕ} {y : A} (hy : y ∈ 𝒜 (j • d)) {x : M}
    (hx : x ∈ 𝒨 ((k * d : ℕ) : ℤ)) : y • x ∈ 𝒨 (((j + k) * d : ℕ) : ℤ) :=
  smul_mem_piece_of_add_eq (by rw [smul_eq_mul, ← Nat.cast_add, Nat.add_mul]) hy hx

include halg in
/-- An element of `𝒜₀` maps to `ℬ₍ψ a₎` the same way through `ℬ₀` and through `𝒜₍a₎`. -/
public theorem fromZero_algebraMap (r : ↥(𝒜 0)) :
    fromZeroRingHom ℬ (Submonoid.powers (ψ a)) (algebraMap ↥(𝒜 0) ↥(ℬ 0) r) =
      Away.map ψ a (fromZeroRingHom 𝒜 (Submonoid.powers a) r) := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [Stacks.AlgebraicGeometry.TwistChartLocality.val_awayLocMap 𝒜 ℬ ψ a]
  change Localization.mk ((algebraMap ↥(𝒜 0) ↥(ℬ 0) r : ↥(ℬ 0)) : B) 1 =
    Stacks.AlgebraicGeometry.TwistChartLocality.awayLocMap 𝒜 ℬ ψ a (Localization.mk (r : A) 1)
  rw [Stacks.AlgebraicGeometry.TwistChartLocality.awayLocMap_mk 𝒜 ℬ ψ a (r : A) 1
    (by rw [Submonoid.coe_one, map_one]; exact Submonoid.one_mem _)]
  exact congrArg₂ (fun (t : B) (q : Submonoid.powers (ψ a)) => Localization.mk t q) (halg r)
    (Subtype.ext (map_one ψ).symm)

/-- **The stage-`k` map** `ℬ₀ ⊗_{𝒜₀} M_{k d} ⟶ ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎`, `b ⊗ x ↦ b ⊗ x / a ^ k`. -/
public def stageMap (k : ℕ) :
    ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ)) →+ ExtSrc 𝒨 ψ a :=
  TensorProduct.liftAddHom
    { toFun := fun b =>
        { toFun := fun x => extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b)
            (Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k x)
          map_zero' := by rw [map_zero, extTmul_zero_right]
          map_add' := fun x y => by rw [map_add, extTmul_add_right] }
      map_zero' := by
        ext x
        change extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) 0) _ = 0
        rw [map_zero, extTmul_zero_left]
      map_add' := fun b b' => by
        ext x
        change extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) (b + b')) _ =
          extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b) _ +
            extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b') _
        rw [map_add, extTmul_add_left] }
    (fun r b x => by
      change extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) (r • b))
          (Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k x) =
        extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b)
          (Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k (r • x))
      rw [fractionHom_zero_smul, extTmul_smul, Algebra.smul_def, map_mul,
        fromZero_algebraMap ψ halg, mul_comm])

public theorem stageMap_tmul (k : ℕ) (b : ↥(ℬ 0)) (x : ↥(𝒨 ((k * d : ℕ) : ℤ))) :
    stageMap ψ halg ha k (b ⊗ₜ x) =
      extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b)
        (Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k x) :=
  TensorProduct.liftAddHom_tmul _ _ _ _

/-- The stage maps are linear over `ℬ₀`, acting on the chart ring through `ℬ₀ ⟶ ℬ₍ψ a₎`. -/
public theorem stageMap_smul (k : ℕ) (b : ↥(ℬ 0)) (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ))) :
    stageMap ψ halg ha k (b • u) =
      fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b • stageMap ψ halg ha k u := by
  induction u using TensorProduct.inductionOn with
  | tmul b' x =>
      rw [TensorProduct.smul_tmul', stageMap_tmul, stageMap_tmul, smul_eq_mul, map_mul,
        smul_extTmul]
  | add u v hu hv => rw [smul_add, map_add, map_add, hu, hv, smul_add]

/-- The stage maps are compatible with the transition maps of the system. -/
public theorem stageMap_mulPow (k l : ℕ) (h : k ≤ l)
    (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ))) :
    stageMap ψ halg ha l (LinearMap.lTensor ↥(ℬ 0) (mulPowModPiece ha k l h) u) =
      stageMap ψ halg ha k u := by
  induction u using TensorProduct.inductionOn with
  | tmul b x =>
    rw [LinearMap.lTensor_tmul, stageMap_tmul, stageMap_tmul, fractionHom_mulPowModPiece]
  | add u v hu hv => rw [map_add, map_add, map_add, hu, hv]

/-- Two elements in the image of stage maps have their sum in the image of a stage map. -/
public theorem exists_stageMap_add {w₁ w₂ : ExtSrc 𝒨 ψ a}
    (h₁ : ∃ (k : ℕ) (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ))), stageMap ψ halg ha k u = w₁)
    (h₂ : ∃ (k : ℕ) (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ))), stageMap ψ halg ha k u = w₂) :
    ∃ (k : ℕ) (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ))),
      stageMap ψ halg ha k u = w₁ + w₂ := by
  obtain ⟨k₁, u₁, rfl⟩ := h₁
  obtain ⟨k₂, u₂, rfl⟩ := h₂
  refine ⟨max k₁ k₂,
    LinearMap.lTensor ↥(ℬ 0) (mulPowModPiece ha k₁ _ (le_max_left k₁ k₂)) u₁ +
      LinearMap.lTensor ↥(ℬ 0) (mulPowModPiece ha k₂ _ (le_max_right k₁ k₂)) u₂, ?_⟩
  rw [map_add, stageMap_mulPow, stageMap_mulPow]

/-! ### Fractions of the chart rings -/

omit [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul ℬ 𝒩] in
public theorem awayMk_zero' {j : ℕ} {e : ℕ} {c : B} (hc : c ∈ ℬ e) (h0 : (0 : B) ∈ ℬ (j • e)) :
    Away.mk ℬ hc j 0 h0 = 0 := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

omit [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul ℬ 𝒩] in
public theorem awayMk_add' {j : ℕ} {e : ℕ} {c : B} (hc : c ∈ ℬ e) (x y : B)
    (hx : x ∈ ℬ (j • e)) (hy : y ∈ ℬ (j • e)) (hxy : x + y ∈ ℬ (j • e)) :
    Away.mk ℬ hc j (x + y) hxy = Away.mk ℬ hc j x hx + Away.mk ℬ hc j y hy := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_add, Away.val_mk, Away.val_mk, Away.val_mk,
    Localization.add_mk_self]

omit [DirectSum.Decomposition 𝒩] [SetLike.GradedSMul ℬ 𝒩] in
public theorem awayMk_zero_mul' {j : ℕ} {e : ℕ} {c : B} (hc : c ∈ ℬ e) (b : ↥(ℬ 0)) (x : B)
    (hx : x ∈ ℬ (j • e)) (hbx : (b : B) * x ∈ ℬ (j • e)) :
    Away.mk ℬ hc j ((b : B) * x) hbx =
      fromZeroRingHom ℬ (Submonoid.powers c) b * Away.mk ℬ hc j x hx := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk]
  change _ = Localization.mk (b : B) 1 * _
  rw [Localization.mk_mul, one_mul]

omit [Algebra ↥(𝒜 0) ↥(ℬ 0)] in
/-- The chart comparison on a fraction. -/
public theorem moduleDegreeZeroMap_fractionHom (k : ℕ) (x : ↥(𝒨 ((k * d : ℕ) : ℤ))) :
    moduleDegreeZeroMap ψ f hf a (Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k x) =
      Stacks.SheafOfModules.fractionHom ℬ 𝒩 (ψ.map_mem ha) k ⟨f x, hf _ x.2⟩ := by
  refine Subtype.ext ?_
  change moduleAwayMap ψ f a (LocalizedModule.mk (S := Submonoid.powers a) (x : M)
      ⟨a ^ k, ⟨k, rfl⟩⟩) = LocalizedModule.mk (S := Submonoid.powers (ψ a)) (f x)
      ⟨ψ a ^ k, ⟨k, rfl⟩⟩
  rw [moduleAwayMap_mk]
  exact congrArg (LocalizedModule.mk (f x)) (Subtype.ext (map_pow ψ a k))

variable (hfM : ∀ i : ℤ, IsBaseChange ↥(ℬ 0) (modulePieceMap ψ f hf halg i))

/-- **The chart comparison on a stage**: it is the degreewise identification
`ℬ₀ ⊗_{𝒜₀} M_{k d} ≅ N_{k d}` followed by `n ↦ n / (ψ a) ^ k`. -/
public theorem moduleDegreeZeroExtension_stageMap (k : ℕ)
    (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ))) :
    moduleDegreeZeroExtension ψ f hf a (stageMap ψ halg ha k u) =
      Stacks.SheafOfModules.fractionHom ℬ 𝒩 (ψ.map_mem ha) k
        ((hfM ((k * d : ℕ) : ℤ)).equiv u).toPiece := by
  induction u using TensorProduct.inductionOn with
  | tmul b x =>
      rw [stageMap_tmul]
      have h1 : extTmul ψ a (fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b)
            (Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k x) =
          fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b •
            extTmul ψ a 1 (Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k x) := by
        rw [smul_extTmul, mul_one]
      rw [h1]
      refine ((moduleDegreeZeroExtension ψ f hf a).hom.map_smul _ _).trans ?_
      refine (congrArg (fun z => fromZeroRingHom ℬ (Submonoid.powers (ψ a)) b • z)
        ((moduleDegreeZeroExtension_tmul ψ f hf a _).trans
          (moduleDegreeZeroMap_fractionHom ψ f hf ha k x))).trans ?_
      rw [IsBaseChange.equiv_tmul]
      exact (fractionHom_zero_smul (ψ.map_mem ha) k b ⟨f x, hf _ x.2⟩).symm
  | add u v hu hv =>
      rw [map_add, map_add, hu, hv, LinearEquiv.map_add]
      exact (map_add _ _ _).symm

omit [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] in
include hfM in
/-- The degreewise identifications are compatible with multiplying a numerator by a power of
`a`. -/
public theorem equiv_lTensor_mulPowModPiece (k l : ℕ) (h : k ≤ l)
    (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ))) :
    ((hfM ((l * d : ℕ) : ℤ)).equiv
        (LinearMap.lTensor ↥(ℬ 0) (mulPowModPiece ha k l h) u)).toPiece =
      mulPowModPiece (ψ.map_mem ha) k l h ((hfM ((k * d : ℕ) : ℤ)).equiv u).toPiece := by
  induction u using TensorProduct.inductionOn with
  | tmul b x =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, IsBaseChange.equiv_tmul]
      refine Subtype.ext ?_
      change (b : B) • f (a ^ (l - k) • (x : M)) = ψ a ^ (l - k) • ((b : B) • f (x : M))
      rw [map_smulₛₗ, GradedRingHom.coe_toRingHom, map_pow]
      exact smul_comm _ _ _
  | add u v hu hv =>
      rw [map_add, LinearEquiv.map_add, LinearEquiv.map_add]
      exact (congrArg₂ (· + ·) hu hv).trans
        (map_add (mulPowModPiece (ψ.map_mem ha) k l h) _ _).symm

omit hfM in
/-- **Every element of `ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎` comes from a single stage.** A coefficient
`x / (ψ a) ^ j` is, by the degreewise base change of the ring, a sum of `b • ψ y / (ψ a) ^ j`, and
`ψ y / (ψ a) ^ j` moves across the tensor sign into the module factor. -/
public theorem exists_stageMap
    (hfA : ∀ n : ℕ, IsBaseChange ↥(ℬ 0) (Stacks.Proj.pieceMap ψ halg n))
    (w : ExtSrc 𝒨 ψ a) :
    ∃ (k : ℕ) (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((k * d : ℕ) : ℤ))), stageMap ψ halg ha k u = w := by
  induction w using TensorProduct.inductionOn with
  | add w₁ w₂ h₁ h₂ => exact exists_stageMap_add ψ halg ha h₁ h₂
  | tmul q z =>
      obtain ⟨j, x, hx, rfl⟩ := Away.mk_surjective ℬ (ψ.map_mem ha) q
      obtain ⟨k, m, hm, hz⟩ :=
        Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree 𝒜 𝒨 ha z
      have hz' : z = Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k ⟨m, hm⟩ := Subtype.ext hz
      subst hz'
      have key : ∀ t : ↥(gradePieceSubmodule ℬ (j • d)),
          ∃ (l : ℕ) (u : ↥(ℬ 0) ⊗[↥(𝒜 0)] ↥(𝒨 ((l * d : ℕ) : ℤ))),
            stageMap ψ halg ha l u =
              extTmul ψ a (Away.mk ℬ (ψ.map_mem ha) j t (Stacks.Proj.mem_of_gradePiece ℬ t))
                (Stacks.SheafOfModules.fractionHom 𝒜 𝒨 ha k ⟨m, hm⟩) := by
        intro t
        induction t using (hfA (j • d)).inductionOn with
        | tmul y => ?_
        | smul b t ih => ?_
        | add t₁ t₂ h₁ h₂ => ?_
        · refine ⟨j + k, (1 : ↥(ℬ 0)) ⊗ₜ ⟨(y : A) • m,
            smul_mem_piece_add (Stacks.Proj.mem_of_gradePiece 𝒜 y) hm⟩, ?_⟩
          rw [stageMap_tmul, map_one]
          have h1 : Away.mk ℬ (ψ.map_mem ha) j (Stacks.Proj.pieceMap ψ halg (j • d) y : B)
                (Stacks.Proj.mem_of_gradePiece ℬ _) =
              Away.map ψ a (Away.mk 𝒜 ha j (y : A) (Stacks.Proj.mem_of_gradePiece 𝒜 y)) :=
            (Away.map_mk ψ a ha j (y : A) _).symm
          rw [h1, ← one_mul (Away.map ψ a _), ← extTmul_smul,
            awayMk_smul_fractionHom ha j k (y : A) _ ⟨m, hm⟩]
        · obtain ⟨l, u, hu⟩ := ih
          refine ⟨l, b • u, ?_⟩
          rw [stageMap_smul, hu, smul_extTmul]
          refine congrArg (fun q => extTmul ψ a q _) ?_
          exact (awayMk_zero_mul' (ψ.map_mem ha) b (t : B) _ _).symm
        · obtain ⟨l, u, hu⟩ := exists_stageMap_add ψ halg ha h₁ h₂
          refine ⟨l, u, hu.trans ?_⟩
          rw [← extTmul_add_left]
          refine congrArg (fun q => extTmul ψ a q _) ?_
          exact (awayMk_add' (ψ.map_mem ha) _ _ _ _ _).symm
      exact key ⟨x, hx⟩

include hfM ha in
/-- **The coefficient extension of the chart comparison of a degreewise base change is an
isomorphism**: `ℬ₍ψ a₎ ⊗_{𝒜₍a₎} M₍a₎ ≅ N₍ψ a₎`.

Every element of the source comes from a single stage `ℬ₀ ⊗_{𝒜₀} M_{k d}`
(`Stacks.AlgebraicGeometry.ModuleChartLocality.exists_stageMap`), and on that stage the comparison
is the degreewise identification followed by `n ↦ n / (ψ a) ^ k`
(`Stacks.AlgebraicGeometry.ModuleChartLocality.moduleDegreeZeroExtension_stageMap`). Surjectivity
is the identification on a numerator; injectivity is that an element killed by a power of `ψ a`
already dies at a later stage. -/
public theorem isIso_moduleDegreeZeroExtension
    (hfA : ∀ n : ℕ, IsBaseChange ↥(ℬ 0) (Stacks.Proj.pieceMap ψ halg n)) :
    IsIso (moduleDegreeZeroExtension ψ f hf a) := by
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (moduleDegreeZeroExtension ψ f hf a).hom).mpr
      fun w hw => ?_
    obtain ⟨k, u, rfl⟩ := exists_stageMap ψ halg ha hfA w
    rw [moduleDegreeZeroExtension_stageMap ψ f hf halg ha hfM] at hw
    have hw' : LocalizedModule.mk (S := Submonoid.powers (ψ a))
        ((((hfM ((k * d : ℕ) : ℤ)).equiv u).toPiece : ↥(𝒩 _)) : N) ⟨ψ a ^ k, ⟨k, rfl⟩⟩ =
          LocalizedModule.mk 0 1 :=
      (congrArg Subtype.val hw).trans (LocalizedModule.zero_mk _).symm
    obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp hw'
    obtain ⟨j, hj⟩ := c.2
    have hc' : ψ a ^ j • ((((hfM ((k * d : ℕ) : ℤ)).equiv u).toPiece : ↥(𝒩 _)) : N) = 0 := by
      simpa only [Submonoid.smul_def, one_smul, smul_zero, ← hj] using hc
    have h0 : ((hfM (((k + j) * d : ℕ) : ℤ)).equiv
        (LinearMap.lTensor ↥(ℬ 0) (mulPowModPiece ha k (k + j) (Nat.le_add_right k j)) u)) = 0 := by
      have h2 := equiv_lTensor_mulPowModPiece ψ f hf halg ha hfM k (k + j)
        (Nat.le_add_right k j) u
      refine (congrArg TargetPiece.ofPiece h2).trans ?_
      refine congrArg TargetPiece.ofPiece (Subtype.ext ?_)
      change ψ a ^ (k + j - k) • _ = 0
      rw [Nat.add_sub_cancel_left]
      exact hc'
    have hu0 := (LinearEquiv.map_eq_zero_iff _).mp h0
    rw [← stageMap_mulPow ψ halg ha k (k + j) (Nat.le_add_right k j) u, hu0, map_zero]
  · intro z
    obtain ⟨k, n, hn, hz⟩ :=
      Stacks.SheafOfModules.degreeZeroLocalization_exists_fraction_of_degree ℬ 𝒩
        (ψ.map_mem ha) z
    refine ⟨stageMap ψ halg ha k ((hfM ((k * d : ℕ) : ℤ)).equiv.symm
      (TargetPiece.ofPiece ⟨n, hn⟩)), ?_⟩
    rw [moduleDegreeZeroExtension_stageMap ψ f hf halg ha hfM, LinearEquiv.apply_symm_apply]
    exact Subtype.ext hz.symm

end Chart

end TwoModules

end Stacks.AlgebraicGeometry.ModuleChartLocality

end
