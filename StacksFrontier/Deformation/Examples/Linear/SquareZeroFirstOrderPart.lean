module

public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.RingTheory.Flat.SquareZeroBaseChange

/-!
# The first-order part of an element killed by a square-zero base change

Let `k` be a commutative ring and let `A` be a *square-zero thickening* of `k`: a `k`-algebra
with a retraction `A → k` whose kernel `I` satisfies `I ^ 2 = 0`. Let `M` be a flat `A`-module
exhibiting a `k`-module `N` as its extension of scalars along the retraction, that is
`f : M →ₗ[A] N` with `IsBaseChange k f`. Then the kernel of `f` is canonically `I ⊗[k] N`, and
the resulting `k`-linear map

`firstOrderPart : {z : M // f z = 0} → I ⊗[k] N`

is the *first-order part* of an element of the kernel: an element of the kernel is `i • m` for
`i ∈ I`, and its first-order part is `i ⊗ f m`, which does not depend on the choice of `m`
because two choices differ by an element of `I • M` and `I ^ 2 = 0`.

The point of the construction is that the target `I ⊗[k] N` is built from the retraction and
from the special fibre `N` alone: it does not mention `M`. A discrepancy in `M` which is known
only to vanish in `N` therefore becomes an element of a module independent of `M`, and the
comparison of the first-order parts computed in two different `M`'s is
`firstOrderPart_map` — a morphism over a morphism of thickenings carries one to the other.
That single statement is what makes the first-order class of a deformation independent of the
chosen lift, invariant under isomorphism of deformations, and natural in the thickening.

Everything here is `StacksFrontier.RingTheory.Flat.SquareZeroBaseChange` plus the observation that
`A` acts on `I` through `k`, which turns the `A`-module `I ⊗[A] N` of that file into the
`k`-module `I ⊗[k] N`.

## Main definitions

* `SquareZeroRetraction.idealTensorEquivBase`: for a `k`-module `N` on which `A` acts through
  the retraction, `I ⊗[k] N` and `I ⊗[A] N` are the same module.
* `SquareZeroRetraction.kerEquiv`: the kernel of a flat base change along the retraction,
  identified with `I ⊗[k] N`.
* `SquareZeroRetraction.firstOrderPart`: the first-order part of an element of that kernel.

## Main results

* `SquareZeroRetraction.mul_mem_ker_eq_algebraMap_mul` and
  `SquareZeroRetraction.isScalarTower_ker`: `A` acts on a square-zero ideal through `k`.
* `SquareZeroRetraction.coe_kerEquiv_tmul`: the identification sends `i ⊗ f m` to `i • m`.
* `SquareZeroRetraction.firstOrderPart_smul`: the first-order part of `i • m` is `i ⊗ f m`.
* `SquareZeroRetraction.firstOrderPart_map`: a semilinear map over a morphism of square-zero
  thickenings carries first-order parts to first-order parts.

## Implementation notes

The retraction is not carried as an `AlgHom A k`: it is `algebraMap A k` for an `Algebra A k`
instance, and the retraction property is the hypothesis
`∀ r, algebraMap A k (algebraMap k A r) = r`. That is the shape in which
`StacksFrontier.RingTheory.Flat.SquareZeroBaseChange` states its hypotheses, and it keeps every
statement below free of `letI` prefixes: with `Algebra k A`, `Algebra A k`, `Module A N` and
`IsScalarTower A k N` as instance binders, all the module structures appearing in the types —
including the `k`-module structure on `I`, on `I ⊗[A] N` and on the kernel of `f` — are found
by instance search.

The `A`-action on a square-zero ideal factoring through `k` is `IsScalarTower A k ↥I`, which is
not an instance (it is false without the square-zero hypothesis) and is therefore produced by
`SquareZeroRetraction.isScalarTower_ker` and introduced with `haveI` where needed. It does not
appear in the type of any declaration below.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open TensorProduct

namespace SquareZeroRetraction

universe w u u₂ v t t₂

/-! ### A square-zero ideal is a module over the quotient -/

section Retraction

variable {k : Type w} [CommRing k] {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]

/-- A `k`-algebra with a retraction onto `k` has surjective structure map. -/
theorem surjective_algebraMap (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r) :
    Function.Surjective (algebraMap A k) :=
  fun r => ⟨algebraMap k A r, hret r⟩

/-- Multiplication by an element of a square-zero ideal factors through the retraction: the
difference between a scalar and the lift of its image is in the ideal, and annihilates it. -/
theorem mul_mem_ker_eq_algebraMap_mul
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (a : A) {i : A} (hi : i ∈ RingHom.ker (algebraMap A k)) :
    a * i = algebraMap k A (algebraMap A k a) * i := by
  have hmem : a - algebraMap k A (algebraMap A k a) ∈ RingHom.ker (algebraMap A k) := by
    simp [RingHom.mem_ker, hret]
  have hz := Ideal.mul_mem_mul hmem hi
  rwa [hsq, Ideal.mem_bot, sub_mul, sub_eq_zero] at hz

/-- The action of `A` on a square-zero ideal of a retraction onto `k` is the action of `k`. -/
theorem isScalarTower_ker (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥) :
    IsScalarTower A k ↥(RingHom.ker (algebraMap A k)) := by
  refine IsScalarTower.of_algebraMap_smul fun a i => Subtype.ext ?_
  rw [Submodule.coe_smul_of_tower, Submodule.coe_smul, Algebra.smul_def, Algebra.smul_def]
  exact (mul_mem_ker_eq_algebraMap_mul hret hsq a i.2).symm

variable (N : Type v) [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower A k N]

/-- Tensoring a square-zero ideal of a retraction onto `k` with a `k`-module over `k` or over
`A` gives the same module: both scalar actions on the ideal and on the module factor through the
retraction, so scalars move freely across both tensor products. -/
noncomputable def idealTensorEquivBase
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥) :
    ↥(RingHom.ker (algebraMap A k)) ⊗[k] N ≃ₗ[k]
      ↥(RingHom.ker (algebraMap A k)) ⊗[A] N := by
  haveI := isScalarTower_ker hret hsq
  haveI : TensorProduct.CompatibleSMul A k ↥(RingHom.ker (algebraMap A k)) N :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective _ _ (surjective_algebraMap hret)
  haveI : TensorProduct.CompatibleSMul k A ↥(RingHom.ker (algebraMap A k)) N := by
    refine ⟨fun a i n => ?_⟩
    rw [← IsScalarTower.algebraMap_smul k a i, ← IsScalarTower.algebraMap_smul k a n]
    exact TensorProduct.smul_tmul _ _ _
  exact TensorProduct.equivOfCompatibleSMul A k k _ N

/-- The comparison of the two tensor products is the identity on generators. -/
@[simp]
theorem idealTensorEquivBase_tmul
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (i : ↥(RingHom.ker (algebraMap A k))) (n : N) :
    idealTensorEquivBase N hret hsq (i ⊗ₜ[k] n) = i ⊗ₜ[A] n := rfl

end Retraction

/-! ### The kernel of a flat base change along the retraction -/

section Kernel

variable {k : Type w} [CommRing k] {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {M : Type t} [AddCommGroup M] [Module A M]
  {N : Type v} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower A k N]
  {f : M →ₗ[A] N}

/-- A base change along a retraction onto `k` is surjective. -/
theorem surjective_of_isBaseChange (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hf : IsBaseChange k f) : Function.Surjective f :=
  hf.surjective_of_surjective_algebraMap (surjective_algebraMap hret)

omit [Algebra k A] in
/-- A multiple of an element of `M` by an element of the square-zero ideal lies in the kernel:
the scalar acts on the special fibre through the retraction, which kills it. -/
theorem apply_smul_eq_zero (i : ↥(RingHom.ker (algebraMap A k))) (m : M) :
    f ((i : A) • m) = 0 := by
  rw [map_smul, ← IsScalarTower.algebraMap_smul k (i : A) (f m),
    RingHom.mem_ker.mp i.2, zero_smul]

variable [Module k M] [IsScalarTower k A M] [Module.Flat A M]

/-- The kernel of a flat base change along a square-zero retraction onto `k`, identified with
`I ⊗[k] N` for `I` the kernel of the retraction: a module built from the retraction and the
special fibre alone. -/
noncomputable def kerEquiv (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hf : IsBaseChange k f) :
    ↥(RingHom.ker (algebraMap A k)) ⊗[k] N ≃ₗ[k] ↥(LinearMap.ker f) :=
  (idealTensorEquivBase N hret hsq).trans
    ((hf.idealTensorEquivKer (surjective_algebraMap hret) hsq).restrictScalars k)

/-- The identification of the kernel with `I ⊗[k] N` sends `i ⊗ f m` to `i • m`. This is the
characterisation used at every call site: it holds for *every* preimage `m` of the second
factor, which is why the first-order part of an element of the kernel is well defined. -/
theorem coe_kerEquiv_tmul (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hf : IsBaseChange k f) (i : ↥(RingHom.ker (algebraMap A k))) (m : M) :
    ((kerEquiv hret hsq hf (i ⊗ₜ[k] f m) : ↥(LinearMap.ker f)) : M) = (i : A) • m :=
  hf.coe_idealTensorEquivKer_tmul (surjective_algebraMap hret) hsq i m

/-- The first-order part of an element of the kernel of a flat base change along a square-zero
retraction onto `k`: the element of `I ⊗[k] N` corresponding to it. -/
noncomputable def firstOrderPart (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hf : IsBaseChange k f) {z : M} (hz : f z = 0) :
    ↥(RingHom.ker (algebraMap A k)) ⊗[k] N :=
  (kerEquiv hret hsq hf).symm ⟨z, hz⟩

/-- The first-order part is characterised by the identification of the kernel. -/
theorem kerEquiv_firstOrderPart (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hf : IsBaseChange k f) {z : M} (hz : f z = 0) :
    ((kerEquiv hret hsq hf (firstOrderPart hret hsq hf hz) :
      ↥(LinearMap.ker f)) : M) = z :=
  congrArg (fun y : ↥(LinearMap.ker f) => (y : M))
    ((kerEquiv hret hsq hf).apply_symm_apply ⟨z, hz⟩)

/-- An element of `I ⊗[k] N` is the first-order part of the element of the kernel it names. -/
theorem firstOrderPart_eq_of_coe_kerEquiv_eq
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hf : IsBaseChange k f) {z : M} (hz : f z = 0)
    (ζ : ↥(RingHom.ker (algebraMap A k)) ⊗[k] N)
    (hζ : ((kerEquiv hret hsq hf ζ : ↥(LinearMap.ker f)) : M) = z) :
    firstOrderPart hret hsq hf hz = ζ :=
  (kerEquiv hret hsq hf).injective <| Subtype.ext <|
    (kerEquiv_firstOrderPart hret hsq hf hz).trans hζ.symm

/-- The first-order part of `i • m` is `i ⊗ f m`. -/
theorem firstOrderPart_smul (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hf : IsBaseChange k f) (i : ↥(RingHom.ker (algebraMap A k))) (m : M) :
    firstOrderPart hret hsq hf (apply_smul_eq_zero (f := f) i m) = i ⊗ₜ[k] f m :=
  firstOrderPart_eq_of_coe_kerEquiv_eq hret hsq hf _ _
    (coe_kerEquiv_tmul hret hsq hf i m)

/-- The first-order part is additive. -/
theorem firstOrderPart_add (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hf : IsBaseChange k f) {z z' : M} (hz : f z = 0) (hz' : f z' = 0) :
    firstOrderPart hret hsq hf (show f (z + z') = 0 by rw [map_add, hz, hz', add_zero]) =
      firstOrderPart hret hsq hf hz + firstOrderPart hret hsq hf hz' := by
  apply firstOrderPart_eq_of_coe_kerEquiv_eq
  rw [map_add, Submodule.coe_add, kerEquiv_firstOrderPart, kerEquiv_firstOrderPart]

end Kernel

/-! ### Comparison along a morphism of square-zero thickenings -/

section Transport

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {B : Type u₂} [CommRing B] [Algebra k B] [Algebra B k]

/-- The restriction to the square-zero ideals of a `k`-algebra map of thickenings compatible
with the two retractions onto `k`. -/
def kerMap (φ : A →ₐ[k] B) (hφ : ∀ a : A, algebraMap B k (φ a) = algebraMap A k a) :
    ↥(RingHom.ker (algebraMap A k)) →ₗ[k] ↥(RingHom.ker (algebraMap B k)) where
  toFun i := ⟨φ (i : A), by rw [RingHom.mem_ker, hφ, RingHom.mem_ker.mp i.2]⟩
  map_add' i j := Subtype.ext (map_add φ (i : A) (j : A))
  map_smul' r i := Subtype.ext (map_smul φ r (i : A))

/-- The restriction of a map of thickenings to the square-zero ideals is the map itself. -/
@[simp]
theorem coe_kerMap (φ : A →ₐ[k] B) (hφ : ∀ a : A, algebraMap B k (φ a) = algebraMap A k a)
    (i : ↥(RingHom.ker (algebraMap A k))) : (kerMap φ hφ i : B) = φ (i : A) := rfl

variable {M : Type t} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Flat A M]
  {M' : Type t₂} [AddCommGroup M'] [Module B M'] [Module k M'] [IsScalarTower k B M']
    [Module.Flat B M']
  {N : Type v} [AddCommGroup N] [Module k N]
  [Module A N] [IsScalarTower A k N] [Module B N] [IsScalarTower B k N]
  {f : M →ₗ[A] N} {f' : M' →ₗ[B] N}

/-- A map of thickenings carries the identification of the kernel with `I ⊗[k] N` over the
corresponding identification: for the same special fibre `N`, the diagram of the two kernels
and the two receptacles commutes.

This is the one computation behind every invariance property of a first-order class. -/
theorem coe_kerEquiv_map
    (hretA : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsqA : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hretB : ∀ r : k, algebraMap B k (algebraMap k B r) = r)
    (hsqB : RingHom.ker (algebraMap B k) * RingHom.ker (algebraMap B k) = ⊥)
    (hf : IsBaseChange k f) (hf' : IsBaseChange k f')
    (φ : A →ₐ[k] B) (hφ : ∀ a : A, algebraMap B k (φ a) = algebraMap A k a)
    (g : M →+ M') (hg : ∀ (a : A) (x : M), g (a • x) = φ a • g x)
    (hcomm : ∀ x : M, f' (g x) = f x)
    (t : ↥(RingHom.ker (algebraMap A k)) ⊗[k] N) :
    ((kerEquiv hretB hsqB hf' (LinearMap.rTensor N (kerMap φ hφ) t) :
        ↥(LinearMap.ker f')) : M') =
      g ((kerEquiv hretA hsqA hf t : ↥(LinearMap.ker f)) : M) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul i n =>
      obtain ⟨m, rfl⟩ := surjective_of_isBaseChange hretA hf n
      rw [coe_kerEquiv_tmul hretA hsqA hf i m, hg, LinearMap.rTensor_tmul, ← hcomm m,
        coe_kerEquiv_tmul hretB hsqB hf' (kerMap φ hφ i) (g m), coe_kerMap]
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]

/-- **A first-order part is carried along a morphism of square-zero thickenings.** If `g` is
semilinear over a `k`-algebra map `φ : A → B` of thickenings and compatible with the two
comparisons to the common special fibre `N`, then the first-order part of `g z` is the image of
the first-order part of `z` under `φ ⊗ N`.

Taking `B = A` and `φ` the identity, this says the first-order part is unchanged by an
isomorphism of the ambient modules over the special fibre; taking `g` the identity of a common
module, that it does not depend on how the kernel element is written. -/
theorem firstOrderPart_map
    (hretA : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsqA : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hretB : ∀ r : k, algebraMap B k (algebraMap k B r) = r)
    (hsqB : RingHom.ker (algebraMap B k) * RingHom.ker (algebraMap B k) = ⊥)
    (hf : IsBaseChange k f) (hf' : IsBaseChange k f')
    (φ : A →ₐ[k] B) (hφ : ∀ a : A, algebraMap B k (φ a) = algebraMap A k a)
    (g : M →+ M') (hg : ∀ (a : A) (x : M), g (a • x) = φ a • g x)
    (hcomm : ∀ x : M, f' (g x) = f x)
    {z : M} (hz : f z = 0) :
    firstOrderPart hretB hsqB hf' (show f' (g z) = 0 by rw [hcomm, hz]) =
      LinearMap.rTensor N (kerMap φ hφ) (firstOrderPart hretA hsqA hf hz) := by
  apply firstOrderPart_eq_of_coe_kerEquiv_eq
  rw [coe_kerEquiv_map hretA hsqA hretB hsqB hf hf' φ hφ g hg hcomm,
    kerEquiv_firstOrderPart]

end Transport

end SquareZeroRetraction

end
