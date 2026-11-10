module

public import StacksFrontier.Deformation.Examples.Linear.GradedJacobianFirstOrderClass

/-!
# The first-order class of a graded deformation is independent of the chosen lifts

Let `P` be a graded `k`-algebra with a weighted-homogeneous presentation

`k[X_i] ⟶ P`,  `X_i ↦ x_i ∈ 𝒜 (d i)`,  relations `F_j` of degree `e j`,

let `A` be a square-zero thickening of `k` with square-zero ideal `I`, identified with a
`k`-module `V`, and let `Q` be a deformation of `P` over `A`. Choosing homogeneous lifts `y_i` of
the generators `x_i` produces the first-order class of the lifted presentation, an element of
`W ⊗[k] V` for `W` the cokernel of the graded Jacobian; that construction is
`StacksFrontier.Deformation.Examples.Linear.GradedJacobianFirstOrderClass`. This file proves that
the class does not depend on the lifts.

The mechanism is the first-order Taylor expansion. Two families of lifts of the same generators
differ by elements `z_i = y'_i - y_i` of the kernel of the reduction, and that kernel is `I · Q`,
so all pairwise products `z_i z_{i'}` vanish. Hence

`F_j(y') = F_j(y) + ∑_i z_i · ∂F_j/∂X_i (y)`,

and taking first-order parts in degree `e j` turns the correction term into the `j`-th component
of the graded Jacobian applied to the first-order parts of the `z_i`. That lies in the image of
the Jacobian, so it dies in the cokernel `W`: the two classes agree.

Three inputs are needed and are provided here. The first is that the kernel of the reduction is
closed under multiplication into zero, which is
`StacksFrontier.RingTheory.Flat.SquareZeroBaseChange` read through the square-zero hypothesis. The
second is a multiplication law for first-order parts across degrees: multiplying an element of
the kernel by a homogeneous element of the deformation multiplies its first-order part, in the
second factor of `I ⊗[k] 𝒜 d`, by the reduction of that element. The third is the degree
bookkeeping on the side of the deformation: `∂F_j/∂X_i` is weighted homogeneous of degree
`e j - d i` with *truncated* subtraction, and the degenerate case `e j < d i` has to be split off
again for the grading of the deformation, exactly as
`Algebra.WeightedHomogeneousPresentation.mul_pderivVal_mem` does it for the grading of the
special fibre.

## Main definitions

* `GradedDeformation.mulRightPiece`: multiplication by a fixed element of a graded algebra, as a
  map between prescribed graded pieces.
* `GradedDeformation.pderivValPiece`: multiplication by the value at the chosen generators of a
  partial derivative of a relation, as such a map. Collecting these over the generators is the
  graded Jacobian.
* `GradedDeformation.kerElement`: the element of the deformation named by an element of
  `I ⊗[k] 𝒜 d`, through the identification of the kernel of the degreewise reduction.
* `GradedDeformation.liftDifferenceFirstOrderPart`: the first-order part of the difference of two
  lifts of a chosen generator.

## Main results

* `MvPolynomial.mul_aeval_pderiv_mem`: a homogeneous element of the weight of a variable
  multiplies the value of the corresponding partial derivative into the degree of the
  polynomial. This is the statement of which
  `Algebra.WeightedHomogeneousPresentation.mul_pderivVal_mem` is the special case for the chosen
  generators, and it is applied here to the grading of the deformation.
* `GradedDeformation.mul_eq_zero_of_reduction_eq_zero`: two elements killed by the reduction have
  vanishing product.
* `GradedDeformation.aeval_eq_aeval_add_sum_mul_aeval_pderiv`: the first-order Taylor expansion
  of a polynomial along a change of lifts.
* `GradedDeformation.kerElement_lTensor_mulRightPiece`: the multiplication law for first-order
  parts across degrees.
* `GradedDeformation.relationFirstOrderPart_eq_add_sum`: the first-order part of a relation at
  one family of lifts differs from the one at another by the graded Jacobian of the differences.
* `GradedDeformation.sum_relationComponent_tmul_jacobian_eq_zero` and
  `GradedDeformation.sum_relationComponent_lTensor_pderivValPiece_eq_zero`: the graded Jacobian
  vanishes in its own cokernel, for an arbitrary element of `I ⊗[k] 𝒜 (d i)` and not only for a
  pure tensor.
* `GradedDeformation.firstOrderClass_eq_of_reduction_eq`: **the first-order class of a lifted
  presentation does not depend on the chosen lifts.**

## Implementation notes

The thickening is carried as instance binders — `Algebra k A`, `Algebra A k`, `Module A P`,
`IsScalarTower A k P` — with the retraction and square-zero conditions as explicit hypotheses. Every
module structure appearing in a statement is then found by instance search and no statement carries
a `letI` prefix.

The hypothesis that the kernel of the *global* reduction `Q → P` is `I · Q` is taken as a base
change condition on an arbitrary `A`-linear map agreeing with the reduction, rather than on a
named linear-map spelling of the reduction. A caller holding a deformation holds a base change
condition for whichever linear map its own structure produces, and supplying the agreement is
then `fun _ ↦ rfl`; naming a spelling here would force that caller to compare two maps that are
equal only by function extensionality.

`GradedDeformation.kerElement` exists so that the characterisation of a first-order part is an
equation in `Q` rather than one between elements of a kernel submodule of a graded piece. The
bridges `GradedDeformation.relationFirstOrderPart_eq_of_kerElement_eq` and
`GradedDeformation.kerElement_firstOrderPart` are the only places where the two layers of
subtype coercion are crossed, and they are term-mode proofs for that reason: a `change` or a
`rw` crossing them has to unfold definitions that it may not unfold.

`GradedDeformation.mulRightPiece` takes the degree compatibility as the membership hypothesis
`∀ x ∈ 𝒜 d, x * p ∈ 𝒜 n` rather than deriving it from an equation `d + d' = n`. At the call site
the source degree is a variable degree, the target degree a relation degree, and the two are
related only by a truncated subtraction, so no such equation is available.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

universe w u v t t₂ x y

/-! ### Multiplying the value of a partial derivative into the degree of the polynomial -/

namespace MvPolynomial

variable {R : Type*} {S : Type*} {ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Multiplying the value of `∂φ/∂X_i` at homogeneous elements by a homogeneous element of the
weight of `X_i` lands in the degree of `φ`: the partial derivative is weighted homogeneous of
degree `n - d i`, and vanishes when that truncated subtraction is lossy.

`Algebra.WeightedHomogeneousPresentation.mul_pderivVal_mem` is this statement for the relations
of a presentation evaluated at the chosen generators. The same statement is needed for the same
polynomials evaluated at lifts of those generators in a deformation, where the grading is the
grading of the deformation, which is why it is stated for an arbitrary graded monoid of
submodules. -/
theorem mul_aeval_pderiv_mem (𝒞 : ℕ → Submodule R S) [SetLike.GradedMonoid 𝒞]
    (x : ι → S) (d : ι → ℕ) (hx : ∀ i, x i ∈ 𝒞 (d i)) {φ : MvPolynomial ι R} {n : ℕ}
    (hφ : φ.IsWeightedHomogeneous d n) (i : ι) {p : S} (hp : p ∈ 𝒞 (d i)) :
    p * aeval x (pderiv i φ) ∈ 𝒞 n := by
  rcases le_or_gt (d i) n with hle | hlt
  · have hd : (pderiv i φ).IsWeightedHomogeneous d (n - d i) :=
      hφ.pderiv (Nat.sub_add_cancel hle)
    have hprod := SetLike.mul_mem_graded hp
      (aeval_mem_of_isWeightedHomogeneous 𝒞 x d hx hd)
    rwa [Nat.add_sub_cancel' hle] at hprod
  · rw [hφ.pderiv_eq_zero_of_lt hlt, map_zero, mul_zero]
    exact zero_mem _

end MvPolynomial

namespace GradedDeformation

/-! ### Multiplication between graded pieces -/

section MulPiece

variable {k : Type w} [CommRing k] {P : Type v} [CommRing P] [Algebra k P]
  {𝒜 : ℕ → Submodule k P}

/-- Multiplication by a fixed element of a graded algebra, as a map from the degree-`d` piece to
the degree-`n` piece, given that it carries the first into the second. -/
def mulRightPiece {d n : ℕ} (p : P) (hp : ∀ x ∈ 𝒜 d, x * p ∈ 𝒜 n) :
    ↥(𝒜 d) →ₗ[k] ↥(𝒜 n) :=
  (LinearMap.mulRight k p).restrict fun x hx ↦ by
    rw [LinearMap.mulRight_apply]
    exact hp x hx

/-- Multiplication between graded pieces is multiplication. -/
@[simp]
theorem coe_mulRightPiece {d n : ℕ} (p : P) (hp : ∀ x ∈ 𝒜 d, x * p ∈ 𝒜 n) (y : ↥(𝒜 d)) :
    (mulRightPiece p hp y : P) = (y : P) * p := by
  rw [mulRightPiece, LinearMap.coe_restrict_apply, LinearMap.mulRight_apply]

end MulPiece

/-! ### The kernel of the reduction is closed under multiplication into zero -/

section Kernel

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {Q : Type t} [CommRing Q] [Algebra A Q]
  {red : Q →+* P}

/-- **The product of two elements killed by the reduction vanishes.** The kernel of a base change
along the retraction is the square-zero ideal times the module, so each factor is a sum of
multiples of elements of that ideal, and the product of two such multiples carries the square of
the ideal. -/
theorem mul_eq_zero_of_reduction_eq_zero
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    {redₗ : Q →ₗ[A] P} (hredₗ : ∀ q : Q, redₗ q = red q) (hbcQ : IsBaseChange k redₗ)
    {z z' : Q} (hz : red z = 0) (hz' : red z' = 0) : z * z' = 0 := by
  have hker := hbcQ.ker_eq_ker_algebraMap_smul_top
    (SquareZeroRetraction.surjective_algebraMap hret)
  have hmem : ∀ w : Q, red w = 0 → w ∈ RingHom.ker (algebraMap A k) • (⊤ : Submodule A Q) :=
    fun w hw ↦ by rw [← hker, LinearMap.mem_ker, hredₗ]; exact hw
  refine Submodule.smul_induction_on (hmem z hz) ?_ fun w w' hw hw' ↦ ?_
  · intro a ha q _
    refine Submodule.smul_induction_on (hmem z' hz') ?_ fun w w' hw hw' ↦ ?_
    · intro b hb q' _
      have hab : a * b = 0 := by
        have hprod := Ideal.mul_mem_mul ha hb
        rwa [hsq, Ideal.mem_bot] at hprod
      rw [smul_mul_assoc, mul_smul_comm, smul_smul, hab, zero_smul]
    · rw [mul_add, hw, hw', add_zero]
  · rw [add_mul, hw, hw', add_zero]

end Kernel

/-! ### The first-order Taylor expansion along a change of lifts -/

section Taylor

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q]
  {red : Q →+* P} {ι : Type x} [Fintype ι]

/-- **First-order Taylor expansion along a change of lifts.** Two families of elements of a
deformation whose differences are killed by the reduction have vanishing pairwise products of
those differences, so the value of a polynomial at the second family is its value at the first
plus the corresponding combination of the values of the partial derivatives. -/
theorem aeval_eq_aeval_add_sum_mul_aeval_pderiv
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    {redₗ : Q →ₗ[A] P} (hredₗ : ∀ q : Q, redₗ q = red q) (hbcQ : IsBaseChange k redₗ)
    {yl yl' : ι → Q} (hdiff : ∀ i, red (yl' i - yl i) = 0) (F : MvPolynomial ι k) :
    aeval yl' F = aeval yl F + ∑ i, (yl' i - yl i) * aeval yl (pderiv i F) := by
  have hz : ∀ i i', (yl' i - yl i) * (yl' i' - yl i') = 0 := fun i i' ↦
    mul_eq_zero_of_reduction_eq_zero hret hsq hredₗ hbcQ (hdiff i) (hdiff i')
  have hsum : yl + (fun i ↦ yl' i - yl i) = yl' := by
    funext i
    simp
  have hexp := MvPolynomial.aeval_add_of_mul_eq_zero (R := k) yl (fun i ↦ yl' i - yl i) hz F
  rwa [hsum] at hexp

end Taylor

/-! ### The element of a deformation named by an element of `I ⊗[k] 𝒜 d` -/

section KerElement

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {𝒜 : ℕ → Submodule k P}
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q} [∀ d, Module.Flat A ↥(𝒬 d)]
  {red : Q →+* P}
  {hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q}
  {hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d}

omit [Algebra k A] [Algebra k Q] [IsScalarTower k A Q] [∀ d, Module.Flat A ↥(𝒬 d)] in
/-- An element of a graded piece killed by the reduction is killed by the degreewise
reduction. -/
theorem gradedPiece_eq_zero {d : ℕ} {z : ↥(𝒬 d)} (hz : red (z : Q) = 0) :
    gradedPiece red hsmul hmem d z = 0 := by
  apply Subtype.ext
  simpa using hz

/-- The element of the deformation which an element of `I ⊗[k] 𝒜 d` names, through the
identification of the kernel of the degreewise reduction with `I ⊗[k] 𝒜 d`. It is additive,
which is what lets a first-order part be computed from a decomposition of the element it is the
first-order part of. -/
noncomputable def kerElement
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d)) (d : ℕ) :
    ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 d) →+ Q where
  toFun ζ := (((SquareZeroRetraction.kerEquiv hret hsq (hbc d) ζ :
    ↥(LinearMap.ker (gradedPiece red hsmul hmem d))) : ↥(𝒬 d)) : Q)
  map_zero' := by simp
  map_add' ζ ζ' := by simp

/-- The element named by the first-order part of an element of the kernel is that element. -/
theorem kerElement_firstOrderPart
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d)) {d : ℕ} {z : ↥(𝒬 d)}
    (hz : red (z : Q) = 0) :
    kerElement hret hsq hbc d
        (SquareZeroRetraction.firstOrderPart hret hsq (hbc d) (gradedPiece_eq_zero hz)) =
      (z : Q) :=
  congrArg (fun y : ↥(𝒬 d) ↦ (y : Q))
    (SquareZeroRetraction.kerEquiv_firstOrderPart hret hsq (hbc d) (gradedPiece_eq_zero hz))

/-- **The multiplication law for the element named by an element of `I ⊗[k] 𝒜 d`.** Multiplying
the named element by a homogeneous element `q` of the deformation is, on `I ⊗[k] 𝒜 d`,
multiplication of the second factor by the reduction of `q`.

This is the statement that carries a first-order part across degrees, and it is what turns the
correction term of the Taylor expansion of a relation into a component of the graded
Jacobian. -/
theorem kerElement_lTensor_mulRightPiece
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d)) {d n : ℕ} {q : Q} {p : P}
    (hp : red q = p) (hmulP : ∀ y ∈ 𝒜 d, y * p ∈ 𝒜 n) (hmulQ : ∀ y ∈ 𝒬 d, y * q ∈ 𝒬 n)
    (ζ : ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 d)) :
    kerElement hret hsq hbc n
        (LinearMap.lTensor ↥(RingHom.ker (algebraMap A k)) (mulRightPiece p hmulP) ζ) =
      kerElement hret hsq hbc d ζ * q := by
  induction ζ using TensorProduct.inductionOn with
  | tmul a y =>
      obtain ⟨m, rfl⟩ := SquareZeroRetraction.surjective_of_isBaseChange hret (hbc d) y
      have hmy : (m : Q) * q ∈ 𝒬 n := hmulQ (m : Q) m.2
      have hval : mulRightPiece p hmulP (gradedPiece red hsmul hmem d m) =
          gradedPiece red hsmul hmem n ⟨(m : Q) * q, hmy⟩ := by
        apply Subtype.ext
        rw [coe_mulRightPiece, coe_gradedPiece, coe_gradedPiece, map_mul, hp]
      have hK : ∀ (e : ℕ) (m : ↥(𝒬 e)), kerElement hret hsq hbc e
          (a ⊗ₜ[k] gradedPiece red hsmul hmem e m) = (a : A) • (m : Q) := fun e m ↦
        (congrArg (fun w : ↥(𝒬 e) ↦ (w : Q))
          (SquareZeroRetraction.coe_kerEquiv_tmul hret hsq (hbc e) a m)).trans
            (Submodule.coe_smul _ _)
      rw [LinearMap.lTensor_tmul, hval, hK, hK, smul_mul_assoc]
  | add ζ ζ' h h' => simp only [map_add, h, h', add_mul]

end KerElement

/-! ### The degree bookkeeping on the side of the deformation -/

section Degrees

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q} [GradedAlgebra 𝒬]
  {red : Q →+* P}
  {hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q}
  {ι : Type x} {σ : Type y}
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ) {yl : ι → Q}

omit [Algebra A k] [Module A P] [IsScalarTower A k P] [GradedAlgebra 𝒜] in
/-- **The `𝒬`-side of the truncated-subtraction case split.** The value of `∂F_j/∂X_i` at lifted
generators multiplies the degree-`d i` piece of the deformation into its degree-`e j` piece: the
partial derivative is weighted homogeneous of degree `e j - d i`, and vanishes when that
truncated subtraction is lossy.

`Algebra.WeightedHomogeneousPresentation.mul_pderivVal_mem` is the same statement for the grading
of the special fibre, which is not the grading needed here. -/
theorem mul_aeval_pderiv_relation_mem (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (j : σ) (i : ι)
    {w : Q} (hw : w ∈ 𝒬 (pres.varDegree i)) :
    w * aeval yl (pderiv i (pres.relation j)) ∈ 𝒬 (pres.relDegree j) := by
  have hgm := gradedMonoid_restrictScalars (k := k) 𝒬
  exact MvPolynomial.mul_aeval_pderiv_mem (fun d ↦ (𝒬 d).restrictScalars k) yl
    pres.varDegree hyd (pres.relation_isWeightedHomogeneous j) i hw

omit [Module A P] [IsScalarTower A k P] [GradedAlgebra 𝒜] in
include hsmul in
/-- The reduction of the value of `∂F_j/∂X_i` at lifted generators is its value at the chosen
generators themselves. -/
theorem reduction_aeval_pderiv_relation
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hy : ∀ i, red (yl i) = pres.val i) (j : σ) (i : ι) :
    red (aeval yl (pderiv i (pres.relation j))) = pres.pderivVal j i := by
  have hval : (fun i ↦ red (yl i)) = pres.val := funext hy
  exact (comp_aeval_apply (f := yl) (mapAlgHom red hsmul hret)
      (pderiv i (pres.relation j))).trans
    (congrArg (fun g : ι → P ↦ aeval g (pderiv i (pres.relation j))) hval)

omit [Algebra A k] [Module A P] [IsScalarTower A k P] [GradedAlgebra 𝒬] in
/-- Multiplication by the value of `∂F_j/∂X_i` at the chosen generators, as a map from the
degree-`d i` piece of the special fibre to its degree-`e j` piece. Collecting these over the
generators is the `j`-th component of the graded Jacobian. -/
noncomputable def pderivValPiece (j : σ) (i : ι) :
    ↥(𝒜 (pres.varDegree i)) →ₗ[k] ↥(𝒜 (pres.relDegree j)) :=
  mulRightPiece (pres.pderivVal j i) fun _ hw ↦ pres.mul_pderivVal_mem j i hw

omit [Algebra A k] [Module A P] [IsScalarTower A k P] [GradedAlgebra 𝒬] in
/-- Multiplication by the value of a partial derivative is multiplication. -/
@[simp]
theorem coe_pderivValPiece (j : σ) (i : ι) (y : ↥(𝒜 (pres.varDegree i))) :
    (pderivValPiece pres j i y : P) = (y : P) * pres.pderivVal j i :=
  coe_mulRightPiece _ _ y

end Degrees

/-! ### The first-order part of a relation under a change of lifts -/

section Relation

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q} [GradedAlgebra 𝒬] [∀ d, Module.Flat A ↥(𝒬 d)]
  {red : Q →+* P}
  {hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q}
  {hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d}
  {ι : Type x} {σ : Type y}
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ) {yl yl' : ι → Q}

omit [GradedAlgebra 𝒜] [Algebra k Q] in
/-- The difference of two lifts of a chosen generator is killed by the reduction. -/
theorem reduction_liftDifference_eq_zero (hy : ∀ i, red (yl i) = pres.val i)
    (hy' : ∀ i, red (yl' i) = pres.val i) (i : ι) : red (yl' i - yl i) = 0 := by
  rw [map_sub, hy, hy', sub_self]

/-- The first-order part of the difference of two lifts of a chosen generator, an element of
`I ⊗[k] 𝒜 (d i)`. Perturbing the lifts by these differences is what could change the first-order
class, and the graded Jacobian is exactly the change. -/
noncomputable def liftDifferenceFirstOrderPart
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i)
    (hyd' : ∀ i, yl' i ∈ 𝒬 (pres.varDegree i)) (hy' : ∀ i, red (yl' i) = pres.val i) (i : ι) :
    ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.varDegree i)) :=
  SquareZeroRetraction.firstOrderPart hret hsq (hbc (pres.varDegree i))
    (gradedPiece_eq_zero (z := ⟨yl' i - yl i, sub_mem (hyd' i) (hyd i)⟩)
      (reduction_liftDifference_eq_zero pres hy hy' i))

omit [GradedAlgebra 𝒜] [GradedAlgebra 𝒬] in
/-- The element named by the first-order part of the difference of two lifts is that
difference. -/
theorem kerElement_liftDifferenceFirstOrderPart
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i)
    (hyd' : ∀ i, yl' i ∈ 𝒬 (pres.varDegree i)) (hy' : ∀ i, red (yl' i) = pres.val i) (i : ι) :
    kerElement hret hsq hbc (pres.varDegree i)
        (liftDifferenceFirstOrderPart pres hret hsq hbc hyd hy hyd' hy' i) = yl' i - yl i :=
  kerElement_firstOrderPart hret hsq hbc
    (z := ⟨yl' i - yl i, sub_mem (hyd' i) (hyd i)⟩)
    (reduction_liftDifference_eq_zero pres hy hy' i)

omit [GradedAlgebra 𝒜] in
/-- An element of `I ⊗[k] 𝒜 (e j)` naming the value of a relation at the lifts *is* the
first-order part of that value. This is
`SquareZeroRetraction.firstOrderPart_eq_of_coe_kerEquiv_eq` with its characterisation restated as
an equation in `Q`. -/
theorem relationFirstOrderPart_eq_of_kerElement_eq
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i) (j : σ)
    (ζ : ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.relDegree j)))
    (hζ : kerElement hret hsq hbc (pres.relDegree j) ζ = aeval yl (pres.relation j)) :
    relationFirstOrderPart pres hret hsq hbc hyd hy j = ζ :=
  SquareZeroRetraction.firstOrderPart_eq_of_coe_kerEquiv_eq hret hsq (hbc (pres.relDegree j))
    (gradedPiece_aeval_relation pres hret hyd hy j) ζ (Subtype.ext hζ)

omit [GradedAlgebra 𝒜] in
/-- The element named by the first-order part of a relation is the value of that relation at the
lifts. -/
theorem kerElement_relationFirstOrderPart
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i) (j : σ) :
    kerElement hret hsq hbc (pres.relDegree j)
        (relationFirstOrderPart pres hret hsq hbc hyd hy j) = aeval yl (pres.relation j) :=
  kerElement_firstOrderPart hret hsq hbc
    (z := ⟨aeval yl (pres.relation j), aeval_relation_mem pres hyd j⟩)
    (congrArg (fun y : ↥(𝒜 (pres.relDegree j)) ↦ (y : P))
      (gradedPiece_aeval_relation (hsmul := hsmul) (hmem := hmem) pres hret hyd hy j))

/-- The multiplication law of `GradedDeformation.kerElement_lTensor_mulRightPiece`, for
multiplication by the value of a partial derivative of a relation. -/
theorem kerElement_lTensor_pderivValPiece
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i) (j : σ) (i : ι)
    (ζ : ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.varDegree i))) :
    kerElement hret hsq hbc (pres.relDegree j)
        (LinearMap.lTensor ↥(RingHom.ker (algebraMap A k)) (pderivValPiece pres j i) ζ) =
      kerElement hret hsq hbc (pres.varDegree i) ζ *
        aeval yl (pderiv i (pres.relation j)) :=
  kerElement_lTensor_mulRightPiece hret hsq hbc
    (reduction_aeval_pderiv_relation (hsmul := hsmul) pres hret hy j i)
    (fun _ hw ↦ pres.mul_pderivVal_mem j i hw)
    (fun _ hw ↦ mul_aeval_pderiv_relation_mem pres hyd j i hw) ζ

variable [Fintype ι]

/-- **The `𝒬`-side of the graded-Jacobian identity.** The first-order part of a relation at one
family of homogeneous lifts of the chosen generators differs from its first-order part at another
such family by the `j`-th component of the graded Jacobian applied to the first-order parts of
the differences of the lifts.

This is `Algebra.WeightedHomogeneousPresentation.aeval_val_add_relation_eq_jacobian` for the
deformation rather than for the special fibre: the Taylor expansion is taken in `Q`, and the
correction term is read in `I ⊗[k] 𝒜 (e j)` through the multiplication law for first-order
parts. -/
theorem relationFirstOrderPart_eq_add_sum
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    {redₗ : Q →ₗ[A] P} (hredₗ : ∀ q : Q, redₗ q = red q) (hbcQ : IsBaseChange k redₗ)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i)
    (hyd' : ∀ i, yl' i ∈ 𝒬 (pres.varDegree i)) (hy' : ∀ i, red (yl' i) = pres.val i) (j : σ) :
    relationFirstOrderPart (yl := yl') pres hret hsq hbc hyd' hy' j =
      relationFirstOrderPart (yl := yl) pres hret hsq hbc hyd hy j +
        ∑ i, LinearMap.lTensor ↥(RingHom.ker (algebraMap A k)) (pderivValPiece pres j i)
          (liftDifferenceFirstOrderPart pres hret hsq hbc hyd hy hyd' hy' i) := by
  have hterm : ∀ i : ι, kerElement hret hsq hbc (pres.relDegree j)
      (LinearMap.lTensor ↥(RingHom.ker (algebraMap A k)) (pderivValPiece pres j i)
        (liftDifferenceFirstOrderPart pres hret hsq hbc hyd hy hyd' hy' i)) =
      (yl' i - yl i) * aeval yl (pderiv i (pres.relation j)) := fun i ↦ by
    rw [kerElement_lTensor_pderivValPiece pres hret hsq hbc hyd hy j i,
      kerElement_liftDifferenceFirstOrderPart pres hret hsq hbc hyd hy hyd' hy' i]
  apply relationFirstOrderPart_eq_of_kerElement_eq
  rw [map_add, map_sum, kerElement_relationFirstOrderPart pres hret hsq hbc hyd hy j]
  simp only [hterm]
  exact (aeval_eq_aeval_add_sum_mul_aeval_pderiv hret hsq hredₗ hbcQ
    (reduction_liftDifference_eq_zero pres hy hy') (pres.relation j)).symm

end Relation

/-! ### The graded Jacobian vanishes in its own cokernel -/

section Cokernel

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {V : Type t₂} [AddCommGroup V] [Module k V]
  {ι : Type x} [Fintype ι] {σ : Type y} [Fintype σ] [DecidableEq σ]
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ)

/-- **The graded Jacobian dies in its own cokernel.** The collected comparison with `W ⊗[k] V` of
the components of the graded Jacobian of any element vanishes: passing to the cokernel of the
Jacobian is exactly what kills it. -/
theorem sum_relationComponent_tmul_jacobian_eq_zero
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (a : ↥(RingHom.ker (algebraMap A k))) (y : ∀ i, ↥(𝒜 (pres.varDegree i))) :
    ∑ j, relationComponent pres eV j (a ⊗ₜ[k] pres.jacobian y j) = 0 := by
  calc ∑ j, relationComponent pres eV j (a ⊗ₜ[k] pres.jacobian y j)
      = ∑ j, (LinearMap.range pres.jacobian).mkQ
          (LinearMap.single k (fun j ↦ ↥(𝒜 (pres.relDegree j))) j (pres.jacobian y j)) ⊗ₜ[k]
            eV a :=
        Finset.sum_congr rfl fun j _ ↦ relationComponent_tmul pres eV j a _
    _ = (LinearMap.range pres.jacobian).mkQ (pres.jacobian y) ⊗ₜ[k] eV a := by
        rw [← TensorProduct.sum_tmul, ← map_sum]
        exact congrArg (fun z ↦ (LinearMap.range pres.jacobian).mkQ z ⊗ₜ[k] eV a)
          (Finset.univ_sum_single (pres.jacobian y))
    _ = 0 := by
        rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ y),
          TensorProduct.zero_tmul]

/-- **The first-order variation of the relations dies in the cokernel of the Jacobian.** For a
fixed generator, the collected comparison with `W ⊗[k] V` of the multiples of the values of the
partial derivatives `∂F_j/∂X_i` vanishes, for *every* element of `I ⊗[k] 𝒜 (d i)` and not only
for a pure tensor: a pure tensor gives the Jacobian of a single-coordinate family, and the
general case follows because the comparison is additive. -/
theorem sum_relationComponent_lTensor_pderivValPiece_eq_zero
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V) (i : ι)
    (ζ : ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.varDegree i))) :
    ∑ j, relationComponent pres eV j
      (LinearMap.lTensor ↥(RingHom.ker (algebraMap A k)) (pderivValPiece pres j i) ζ) = 0 := by
  classical
  induction ζ using TensorProduct.inductionOn with
  | tmul a y =>
      have hj : ∀ j : σ, pderivValPiece pres j i y = pres.jacobian (Pi.single i y) j := by
        intro j
        apply Subtype.ext
        rw [coe_pderivValPiece, Algebra.WeightedHomogeneousPresentation.jacobian_apply_coe,
          Finset.sum_eq_single_of_mem i (Finset.mem_univ i), Pi.single_eq_same]
        intro n _ hn
        rw [Pi.single_eq_of_ne hn, ZeroMemClass.coe_zero, zero_mul]
      calc ∑ j, relationComponent pres eV j
            (LinearMap.lTensor ↥(RingHom.ker (algebraMap A k)) (pderivValPiece pres j i)
              (a ⊗ₜ[k] y))
          = ∑ j, relationComponent pres eV j (a ⊗ₜ[k] pres.jacobian (Pi.single i y) j) :=
            Finset.sum_congr rfl fun j _ ↦ by rw [LinearMap.lTensor_tmul, hj j]
        _ = 0 := sum_relationComponent_tmul_jacobian_eq_zero pres eV a (Pi.single i y)
  | add ζ ζ' h h' => simp only [map_add, Finset.sum_add_distrib, h, h', add_zero]

end Cokernel

/-! ### Independence of the lifts -/

section Independence

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q} [GradedAlgebra 𝒬] [∀ d, Module.Flat A ↥(𝒬 d)]
  {V : Type t₂} [AddCommGroup V] [Module k V]
  {red : Q →+* P}
  {hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q}
  {hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d}
  {ι : Type x} [Fintype ι] {σ : Type y} [Fintype σ] [DecidableEq σ]
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ) {yl yl' : ι → Q}

/-- The first-order class is the collected comparison of the first-order parts of the
relations. -/
theorem firstOrderClass_eq_sum
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i) :
    firstOrderClass pres hret hsq hbc eV hyd hy =
      ∑ j, relationComponent pres eV j
        (relationFirstOrderPart pres hret hsq hbc hyd hy j) := rfl

/-- **The first-order class of a lifted presentation does not depend on the chosen lifts.** Two
families of homogeneous lifts of the chosen generators, of the prescribed degrees and with the
prescribed reductions, give the same element of `W ⊗[k] V`.

The two differ by the graded Jacobian applied to the first-order parts of the differences of the
lifts, by the Taylor expansion of each relation, and that correction lies in the image of the
Jacobian, hence vanishes in the cokernel `W`. This is what the cokernel was taken for: it makes
the first-order class an invariant of the deformation rather than of a choice of lifts of a
presentation of its special fibre. -/
theorem firstOrderClass_eq_of_reduction_eq
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    {redₗ : Q →ₗ[A] P} (hredₗ : ∀ q : Q, redₗ q = red q) (hbcQ : IsBaseChange k redₗ)
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i)
    (hyd' : ∀ i, yl' i ∈ 𝒬 (pres.varDegree i)) (hy' : ∀ i, red (yl' i) = pres.val i) :
    firstOrderClass (yl := yl') pres hret hsq hbc eV hyd' hy' =
      firstOrderClass (yl := yl) pres hret hsq hbc eV hyd hy := by
  have hkey : ∀ j : σ, relationComponent pres eV j
      (relationFirstOrderPart (yl := yl') pres hret hsq hbc hyd' hy' j) =
      relationComponent pres eV j
          (relationFirstOrderPart (yl := yl) pres hret hsq hbc hyd hy j) +
        ∑ i, relationComponent pres eV j
          (LinearMap.lTensor ↥(RingHom.ker (algebraMap A k)) (pderivValPiece pres j i)
            (liftDifferenceFirstOrderPart pres hret hsq hbc hyd hy hyd' hy' i)) := fun j ↦ by
    rw [relationFirstOrderPart_eq_add_sum pres hret hsq hbc hredₗ hbcQ hyd hy hyd' hy' j,
      map_add, map_sum]
  have hzero : ∑ j : σ, ∑ i : ι, relationComponent pres eV j
      (LinearMap.lTensor ↥(RingHom.ker (algebraMap A k)) (pderivValPiece pres j i)
        (liftDifferenceFirstOrderPart pres hret hsq hbc hyd hy hyd' hy' i)) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun i _ ↦
      sum_relationComponent_lTensor_pderivValPiece_eq_zero pres eV i _
  rw [firstOrderClass_eq_sum pres hret hsq hbc eV hyd' hy',
    firstOrderClass_eq_sum pres hret hsq hbc eV hyd hy,
    Finset.sum_congr rfl fun j _ ↦ hkey j, Finset.sum_add_distrib, hzero, add_zero]

end Independence

end GradedDeformation

end
