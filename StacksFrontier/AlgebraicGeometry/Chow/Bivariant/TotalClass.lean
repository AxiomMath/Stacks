module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.IdentityRule
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InverseIsoGysin
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassKGroup
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing

/-!
# The ring of total Chow cohomology classes

Let `Y` be locally of finite type over the base of chapter 42 of the Stacks Project. A *total
Chow cohomology class* of `Y` is a family `c = (c_0, c_1, c_2, …)` with `c_p ∈ A^p(Y)`, the
Chow cohomology of [Stacks, Tag 0B7E] at the Gysin system of the first Chern class of an
invertible module; that is, an element of the product `∏_{p ≥ 0} A^p(Y)`
(`Stacks.Chow.chowCohomologySeries`). This file makes these classes into a ring, with the
Cauchy product

  `(c d)_p = ∑_{i + j = p} c_i d_j`

of the products `A^i(Y) × A^j(Y) ⟶ A^{i+j}(Y)` of [Stacks, Tag 0B75], and the class
`1 ∈ A^0(Y)` as unit.

The ring axioms are not proved on the bivariant classes themselves but on their operations. On
a test scheme `g : T ⟶ Y` every `c_p` acts as an operation `A_k(T) ⟶ A_{k-p}(T)`
(`Stacks.Chow.BivariantClass.idRule`), so `c` acts as a graded cap family on the Chow groups of
`T` (`Stacks.Chow.TotalChowClass.op`). A class is determined by these operations, the operation
of a sum is the sum, the operation of the product is the convolution of the operations
(`Stacks.Chow.TotalChowClass.op_mul`, from `Stacks.Chow.BivariantClass.idRule_mulId`) and the
operation of `1` is the identity (`Stacks.Chow.TotalChowClass.op_one`). So every identity of the
ring of graded cap families `StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing`
holds for total classes, and the operation on each test scheme is a ring homomorphism
(`Stacks.Chow.TotalChowClass.opRingHom`). The ring is not claimed to be commutative.

A total class whose degree-`0` component is `1` is a unit
(`Stacks.Chow.TotalChowClass.isUnit_of_apply_zero`); its inverse is given by the recursion
`d_m = 1_m - ∑_{j < m} c_{m-j} d_j`, which on every test scheme is the recursion of
`Stacks.Chow.gradedRightInv`.

## Main definitions

* `Stacks.Chow.bivariantClassDegreeCongr` — a bivariant class of degree `p` read in an equal
  degree `p'`.
* `Stacks.Chow.bivariantIdentityClassOfInvertible` — the class `1 ∈ A^0(Y)`.
* `Stacks.Chow.TotalChowClass` — the total Chow cohomology classes of `Y`.
* `Stacks.Chow.TotalChowClass.op` — the operation of a total class on a test scheme.
* `Stacks.Chow.TotalChowClass.instRing` — the ring of total classes.
* `Stacks.Chow.TotalChowClass.opRingHom` — the operation as a ring homomorphism.

## Main results

* `Stacks.Chow.identityCapRule_gysinNaturality` — the identity commutes with Gysin maps.
* `Stacks.Chow.TotalChowClass.ext_op` — a total class is determined by its operations.
* `Stacks.Chow.TotalChowClass.op_mul`, `Stacks.Chow.TotalChowClass.op_one`.
* `Stacks.Chow.TotalChowClass.isUnit_of_apply_zero` — a total class `1 + c_1 + c_2 + ⋯` is a
  unit.

## References

* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow

/-! ### Transport of a bivariant class along an equality of degrees -/

section Degree

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
  [LocallyOfFiniteType f] (hf : f ≫ sY = sX)

/-- A bivariant class of degree `p` is one of degree `p'` whenever `p = p'`, as an additive
equivalence. The degrees `i + j` of a product and `p` of a component of a total class are equal
integers and not the same term. -/
def bivariantClassDegreeCongr {p p' : ℤ} (h : p = p') :
    BivariantClass C G sX sY f hf p ≃+ BivariantClass C G sX sY f hf p' := by
  subst h
  exact AddEquiv.refl _

/-- The transport of a class along an equality of degrees caps the way the class does. -/
theorem bivariantClassDegreeCongr_cap {p p' : ℤ} (h : p = p')
    (c : BivariantClass C G sX sY f hf p) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (bivariantClassDegreeCongr C G sX sY f hf h c).cap g k α ≍ c.cap g k α := by
  subst h
  rfl

end Degree

/-! ### The operation of a class is additive in the class -/

section IdRule

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX]

/-- The operation of the transport of a class along an equality of degrees is the operation of
the class. -/
theorem BivariantClass.idRule_bivariantClassDegreeCongr {p p' : ℤ} (h : p = p')
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    (bivariantClassDegreeCongr C G sX sX (𝟙 X) (Category.id_comp sX) h c).idRule C sX G g k α ≍
      c.idRule C sX G g k α := by
  subst h
  rfl

/-- The operation on a test scheme `g : T ⟶ X` in degree `k`, as an additive map in the class. -/
def BivariantClass.idRuleHom {p : ℤ} {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g]
    (k : ℤ) :
    BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p →+
      (chowGroup C (g ≫ sX) k →+ chowGroup C (g ≫ sX) (k - p)) where
  toFun c := c.idRule C sX G g k
  map_zero' := by
    ext α
    simp [BivariantClass.idRule_apply]
  map_add' c d := by
    ext α
    simp [BivariantClass.idRule_apply]

/-- The additive map `Stacks.Chow.BivariantClass.idRuleHom` evaluates to the operation. -/
theorem BivariantClass.idRuleHom_apply {p : ℤ} {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    BivariantClass.idRuleHom C G sX g k c = c.idRule C sX G g k :=
  rfl

variable {p : ℤ} {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
  (α : chowGroup C (g ≫ sX) k)

/-- The operation of the zero class is zero. -/
@[simp]
theorem BivariantClass.idRule_zero :
    (0 : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p).idRule C sX G g k α = 0 := by
  rw [← BivariantClass.idRuleHom_apply, map_zero, AddMonoidHom.zero_apply]

/-- The operation of a sum of classes is the sum of the operations. -/
@[simp]
theorem BivariantClass.idRule_add (c d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    (c + d).idRule C sX G g k α = c.idRule C sX G g k α + d.idRule C sX G g k α := by
  rw [← BivariantClass.idRuleHom_apply, map_add, AddMonoidHom.add_apply]
  rfl

/-- The operation of the negative of a class is the negative of the operation. -/
@[simp]
theorem BivariantClass.idRule_neg (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    (-c).idRule C sX G g k α = -c.idRule C sX G g k α := by
  rw [← BivariantClass.idRuleHom_apply, map_neg, AddMonoidHom.neg_apply]
  rfl

/-- The operation of a difference of classes is the difference of the operations. -/
@[simp]
theorem BivariantClass.idRule_sub (c d : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    (c - d).idRule C sX G g k α = c.idRule C sX G g k α - d.idRule C sX G g k α := by
  rw [← BivariantClass.idRuleHom_apply, map_sub, AddMonoidHom.sub_apply]
  rfl

/-- The operation of a natural multiple of a class is that multiple of the operation. -/
@[simp]
theorem BivariantClass.idRule_nsmul (n : ℕ)
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    (n • c).idRule C sX G g k α = n • c.idRule C sX G g k α := by
  rw [← BivariantClass.idRuleHom_apply, map_nsmul, AddMonoidHom.nsmul_apply]
  rfl

/-- The operation of an integer multiple of a class is that multiple of the operation. -/
@[simp]
theorem BivariantClass.idRule_zsmul (n : ℤ)
    (c : BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    (n • c).idRule C sX G g k α = n • c.idRule C sX G g k α := by
  rw [← BivariantClass.idRuleHom_apply, map_zsmul, AddMonoidHom.zsmul_apply]
  rfl

/-- The operation of a finite sum of classes is the sum of the operations. -/
theorem BivariantClass.idRule_sum {ι : Type*} (s : Finset ι)
    (c : ι → BivariantClass C G sX sX (𝟙 X) (Category.id_comp sX) p) :
    (∑ i ∈ s, c i).idRule C sX G g k α = ∑ i ∈ s, (c i).idRule C sX G g k α := by
  rw [← BivariantClass.idRuleHom_apply, map_sum, AddMonoidHom.finsetSum_apply]
  rfl

end IdRule

/-! ### The class `1 ∈ A^0(Y)` -/

section One

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- The identity cap rule returns its argument, read in degree `k - 0`. -/
theorem identityCapRule_heq {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sY) k) : identityCapRule C sY g k α ≍ α := by
  rw [identityCapRule_apply]
  exact chowGroup_cast_heq (g ≫ sY) (sub_zero k).symm α

/-- **Stacks 0B76 (3) for the identity, read on the test schemes.** The identity cap rule
commutes with the Gysin maps of every Gysin system: the two sides differ only by transports of
the degree. -/
theorem identityCapRule_gysinNaturality (G : GysinSystem C) :
    IdentityCapRule.GysinNaturality C sY 0 (identityCapRule C sY) G := by
  intro T g _ N _ s k α
  have key : ∀ (k' : ℤ) (_ : k = k') (β : chowGroup C (g ≫ sY) (k' + 1)), β ≍ α →
      G.onChow (g ≫ sY) N s k' β ≍ G.onChow (g ≫ sY) N s k α := by
    rintro k' rfl β hβ
    cases hβ
    rfl
  rw [identityCapRule_apply C sY g (k + 1) α]
  refine eq_of_heq ((identityCapRule_heq C sY _ k _).trans
    (key (k - 0) (sub_zero k).symm _ ?_).symm)
  exact (chowGroup_cast_heq (g ≫ sY) (by omega : k + 1 - 0 = k - 0 + 1) _).trans
    (chowGroup_cast_heq (g ≫ sY) (sub_zero (k + 1)).symm α)

/-- **The class `1 ∈ A^0(Y)`** at the Gysin system of the first Chern class of an invertible
module: the bivariant class of degree `0` for `𝟙 Y` acting as the identity on every test
scheme. -/
def bivariantIdentityClassOfInvertible :
    BivariantClass C (gysinSystemOfInvertible C) sY sY (𝟙 Y) (Category.id_comp sY) 0 :=
  bivariantIdentityClass C sY (gysinSystemOfInvertible C)
    (IdentityCapRule.transportGysinNaturality C sY 0 (identityCapRule C sY)
      (gysinSystemOfInvertible C) (identityCapRule_gysinNaturality C sY _)
      (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C))

/-- The operation of `1` on a test scheme is the identity, read in degree `k - 0`. -/
theorem idRule_bivariantIdentityClassOfInvertible {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (bivariantIdentityClassOfInvertible C sY).idRule C sY (gysinSystemOfInvertible C) g k α =
      identityCapRule C sY g k α :=
  bivariantIdentityClass_cap_pushforward C sY (gysinSystemOfInvertible C)
    (IdentityCapRule.transportGysinNaturality C sY 0 (identityCapRule C sY)
      (gysinSystemOfInvertible C) (identityCapRule_gysinNaturality C sY _)
      (GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C)) g k α

/-- The operation of `1` on a test scheme returns its argument. -/
theorem idRule_bivariantIdentityClassOfInvertible_heq {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (bivariantIdentityClassOfInvertible C sY).idRule C sY (gysinSystemOfInvertible C) g k α ≍
      α := by
  rw [idRule_bivariantIdentityClassOfInvertible]
  exact identityCapRule_heq C sY g k α

end One


/-! ### Total Chow cohomology classes -/

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]

/-- **The total Chow cohomology classes of `Y`.** Families `(c_0, c_1, c_2, …)` with
`c_p ∈ A^p(Y)`, the Chow cohomology of Stacks 0B7E at the Gysin system of the first Chern class
of an invertible module: the product `∏_{p ≥ 0} A^p(Y)`, with no condition on the support. -/
def TotalChowClass : Type (u + 1) :=
  chowCohomologySeries C (gysinSystemOfInvertible C) sY

namespace TotalChowClass

/-- Total classes are added componentwise. -/
instance : AddCommGroup (TotalChowClass C sY) :=
  inferInstanceAs (AddCommGroup (chowCohomologySeries C (gysinSystemOfInvertible C) sY))

variable {C sY}

/-- Two total classes with the same components are equal. -/
@[ext]
theorem ext {c d : TotalChowClass C sY} (h : ∀ p : ℕ, c p = d p) : c = d :=
  funext h

/-- The components of `0` are zero. -/
@[simp]
theorem zero_apply (p : ℕ) : (0 : TotalChowClass C sY) p = 0 :=
  rfl

/-- Total classes are added componentwise. -/
@[simp]
theorem add_apply (c d : TotalChowClass C sY) (p : ℕ) : (c + d) p = c p + d p :=
  rfl

/-- Total classes are negated componentwise. -/
@[simp]
theorem neg_apply (c : TotalChowClass C sY) (p : ℕ) : (-c) p = -c p :=
  rfl

/-- Total classes are subtracted componentwise. -/
@[simp]
theorem sub_apply (c d : TotalChowClass C sY) (p : ℕ) : (c - d) p = c p - d p :=
  rfl

/-- The components of a finite sum of total classes. -/
@[simp]
theorem sum_apply {ι : Type*} (s : Finset ι) (c : ι → TotalChowClass C sY) (p : ℕ) :
    (∑ i ∈ s, c i) p = ∑ i ∈ s, c i p :=
  Finset.sum_apply p s c

/-! #### The operation on the test schemes -/

/-- **The operation of a total class on a test scheme.** For `c = (c_p)_p` and a test scheme
`g : T ⟶ Y`, the graded cap family on the Chow groups of `T` whose index-`p` component in degree
`k` is the operation `A_k(T) ⟶ A_{k-p}(T)` of `c_p`. -/
def op (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] :
    GradedCapFamily (fun k ↦ chowGroup C (g ≫ sY) k) :=
  fun k p ↦ (c p).idRule C sY (gysinSystemOfInvertible C) g k

/-- The components of the operation of a total class are the operations of its components. -/
theorem op_apply (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (k : ℤ) (p : ℕ) (α : chowGroup C (g ≫ sY) k) :
    c.op g k p α = (c p).idRule C sY (gysinSystemOfInvertible C) g k α :=
  rfl

/-- **A total class is determined by its operations on the test schemes.** -/
theorem ext_op {c d : TotalChowClass C sY}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g], c.op g = d.op g) : c = d := by
  refine ext fun p ↦ ?_
  refine BivariantClass.eq_of_idRule_eq C sY _ (c p) (d p) fun g _ k α ↦ ?_
  exact DFunLike.congr_fun (congrFun (congrFun (h g) k) p) α

/-- The operation on a test scheme, as an additive map in the total class. -/
def opHom {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] :
    TotalChowClass C sY →+ GradedCapFamily (fun k ↦ chowGroup C (g ≫ sY) k) where
  toFun c := c.op g
  map_zero' := by
    funext k p
    refine AddMonoidHom.ext fun α ↦ ?_
    simp [op_apply]
  map_add' c d := by
    funext k p
    refine AddMonoidHom.ext fun α ↦ ?_
    simp [op_apply]

/-- The additive map `Stacks.Chow.TotalChowClass.opHom` evaluates to the operation. -/
theorem opHom_apply {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (c : TotalChowClass C sY) : opHom g c = c.op g :=
  rfl

/-- The operation of `0` is zero. -/
@[simp]
theorem op_zero {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] :
    (0 : TotalChowClass C sY).op g = 0 :=
  map_zero (opHom g)

/-- The operation of a sum is the sum of the operations. -/
@[simp]
theorem op_add (c d : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (c + d).op g = c.op g + d.op g :=
  map_add (opHom g) c d

/-- The operation of a negative is the negative of the operation. -/
@[simp]
theorem op_neg (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] :
    (-c).op g = -c.op g :=
  map_neg (opHom g) c

/-- The operation of a difference is the difference of the operations. -/
@[simp]
theorem op_sub (c d : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (c - d).op g = c.op g - d.op g :=
  map_sub (opHom g) c d

/-! #### The unit -/

/-- **The unit total class**: the class `1 ∈ A^0(Y)` in degree `0`, and zero in every positive
degree. -/
instance : One (TotalChowClass C sY) where
  one p := if h : p = 0 then
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY)
        (show (0 : ℤ) = (p : ℤ) by simp [h]) (bivariantIdentityClassOfInvertible C sY)
    else 0

/-- The degree-`0` component of `1` is the class `1 ∈ A^0(Y)`. -/
theorem one_apply_zero :
    (1 : TotalChowClass C sY) 0 =
      bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) (by simp)
        (bivariantIdentityClassOfInvertible C sY) :=
  dite_eq_left rfl

/-- The components of `1` in positive degrees vanish. -/
theorem one_apply_of_ne {p : ℕ} (hp : p ≠ 0) : (1 : TotalChowClass C sY) p = 0 :=
  dite_eq_right hp

/-- **The operation of `1` is the identity.** -/
theorem op_one {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] :
    (1 : TotalChowClass C sY).op g = 1 := by
  funext k p
  refine AddMonoidHom.ext fun α ↦ ?_
  rcases eq_or_ne p 0 with rfl | hp
  · rw [op_apply, one_apply_zero, gradedCap_one_apply_zero]
    exact eq_of_heq (((BivariantClass.idRule_bivariantClassDegreeCongr C _ sY _ _ g k α).trans
      (idRule_bivariantIdentityClassOfInvertible_heq C sY g k α)).trans
        (gradedDegreeCast_heq _ α).symm)
  · rw [op_apply, one_apply_of_ne hp, gradedCap_one_of_ne hp, BivariantClass.idRule_zero]
    rfl

/-! #### The product -/

/-- The `j`-th summand `c_{m-j} d_j ∈ A^m(Y)` of the degree-`m` component of a product, and zero
for `j > m`. -/
def mulTerm (c d : TotalChowClass C sY) (m j : ℕ) :
    BivariantClass C (gysinSystemOfInvertible C) sY sY (𝟙 Y) (Category.id_comp sY) (m : ℤ) :=
  if h : j ≤ m then
    bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY)
      (show ((m - j : ℕ) : ℤ) + (j : ℤ) = m by omega) ((c (m - j)).mulId C sY (d j))
  else 0

/-- **The product of total classes**, the Cauchy product `(c d)_m = ∑_{i + j = m} c_i d_j` of
the products `A^i(Y) × A^j(Y) ⟶ A^{i+j}(Y)` of Stacks 0B75. -/
instance : Mul (TotalChowClass C sY) where
  mul c d m := ∑ j ∈ range (m + 1), mulTerm c d m j

/-- The degree-`m` component of a product. -/
theorem mul_apply (c d : TotalChowClass C sY) (m : ℕ) :
    (c * d) m = ∑ j ∈ range (m + 1), mulTerm c d m j :=
  rfl

/-- The operation of a product class, read in an equal degree, is the composite of the
operations of the factors, up to the transport of degrees. -/
private theorem idRule_degreeCongr_mulId {p q r : ℤ} (h : p + q = r)
    (c : BivariantClass C (gysinSystemOfInvertible C) sY sY (𝟙 Y) (Category.id_comp sY) p)
    (d : BivariantClass C (gysinSystemOfInvertible C) sY sY (𝟙 Y) (Category.id_comp sY) q)
    {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sY) k) :
    (bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY) h
      (c.mulId C sY d)).idRule C sY (gysinSystemOfInvertible C) g k α ≍
      c.idRule C sY (gysinSystemOfInvertible C) g (k - q)
        (d.idRule C sY (gysinSystemOfInvertible C) g k α) :=
  (BivariantClass.idRule_bivariantClassDegreeCongr C _ sY _ _ g k α).trans
    (BivariantClass.idRule_mulId C sY _ _ g k α)

/-- **The operation of a product is the convolution of the operations.** -/
theorem op_mul (c d : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (c * d).op g = c.op g * d.op g := by
  funext k m
  refine AddMonoidHom.ext fun α ↦ ?_
  rw [op_apply, mul_apply, BivariantClass.idRule_sum, gradedCap_mul_apply]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [convolveTerm_of_le _ _ _ hjm, capTo_def, mulTerm, dite_eq_left hjm]
  exact eq_of_heq ((idRule_degreeCongr_mulId _ _ _ g k α).trans
    (gradedDegreeCast_heq _ _).symm)


/-! #### The ring -/

/-- **The ring of total Chow cohomology classes**, with the Cauchy product of Stacks 0B75 and
the unit `1 ∈ A^0(Y)`. Each ring axiom is the corresponding identity of the operations on the
test schemes, in the ring of graded cap families, by `Stacks.Chow.TotalChowClass.ext_op`. -/
instance instRing : Ring (TotalChowClass C sY) where
  __ := (inferInstance : AddCommGroup (TotalChowClass C sY))
  mul_assoc a b c := ext_op fun g _ ↦ by simp only [op_mul, mul_assoc]
  one_mul a := ext_op fun g _ ↦ by rw [op_mul, op_one, one_mul]
  mul_one a := ext_op fun g _ ↦ by rw [op_mul, op_one, mul_one]
  zero_mul a := ext_op fun g _ ↦ by rw [op_mul, op_zero, zero_mul]
  mul_zero a := ext_op fun g _ ↦ by rw [op_mul, op_zero, mul_zero]
  left_distrib a b c := ext_op fun g _ ↦ by simp only [op_mul, op_add, mul_add]
  right_distrib a b c := ext_op fun g _ ↦ by simp only [op_mul, op_add, add_mul]

/-- **The operation on a test scheme is a ring homomorphism** from the total classes of `Y` to the
graded cap families on the Chow groups of the test scheme. -/
def opRingHom {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] :
    TotalChowClass C sY →+* GradedCapFamily (fun k ↦ chowGroup C (g ≫ sY) k) where
  toFun c := c.op g
  map_one' := op_one g
  map_mul' c d := op_mul c d g
  map_zero' := op_zero g
  map_add' c d := op_add c d g

/-- The ring homomorphism `Stacks.Chow.TotalChowClass.opRingHom` evaluates to the operation. -/
theorem opRingHom_apply {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g]
    (c : TotalChowClass C sY) : opRingHom g c = c.op g :=
  rfl

/-! #### Units -/

/-- The components of the right inverse of a total class, by recursion on the degree:
`d_m = 1_m - ∑_{j < m} c_{m-j} d_j`. -/
def rightInvAux (c : TotalChowClass C sY) (m : ℕ) :
    BivariantClass C (gysinSystemOfInvertible C) sY sY (𝟙 Y) (Category.id_comp sY) (m : ℤ) :=
  (1 : TotalChowClass C sY) m -
    ∑ j : Fin m, bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY)
      (show ((m - (j : ℕ) : ℕ) : ℤ) + ((j : ℕ) : ℤ) = m by have := j.isLt; omega)
      ((c (m - j)).mulId C sY (rightInvAux c j))
termination_by m
decreasing_by exact j.isLt

/-- The right inverse of a total class whose degree-`0` component is `1`. -/
def rightInv (c : TotalChowClass C sY) : TotalChowClass C sY :=
  rightInvAux c

/-- The recursion defining the right inverse. -/
theorem rightInv_apply (c : TotalChowClass C sY) (m : ℕ) :
    rightInv c m = (1 : TotalChowClass C sY) m -
      ∑ j : Fin m, bivariantClassDegreeCongr C _ sY sY (𝟙 Y) (Category.id_comp sY)
        (show ((m - (j : ℕ) : ℕ) : ℤ) + ((j : ℕ) : ℤ) = m by have := j.isLt; omega)
        ((c (m - j)).mulId C sY (rightInv c j)) := by
  rw [rightInv, rightInvAux]

/-- The operation of the right inverse is the right inverse of the operation, the two being
given by the same recursion. -/
theorem op_rightInv (c : TotalChowClass C sY) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] : (rightInv c).op g = gradedRightInv (c.op g) := by
  funext k m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    refine AddMonoidHom.ext fun α ↦ ?_
    rw [op_apply, rightInv_apply, gradedRightInv_apply, BivariantClass.idRule_sub,
      AddMonoidHom.sub_apply, BivariantClass.idRule_sum, AddMonoidHom.finsetSum_apply, ← op_apply,
      op_one]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    refine eq_of_heq ((idRule_degreeCongr_mulId _ _ _ g k α).trans ?_)
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← ih j j.isLt]
    exact (gradedDegreeCast_heq _ _).symm

/-- **A total class whose operations have identity index-`0` component is a unit.** -/
theorem isUnit_of_op_apply_zero {c : TotalChowClass C sY}
    (hc : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] (k : ℤ),
      c.op g k 0 = (1 : GradedCapFamily (fun k ↦ chowGroup C (g ≫ sY) k)) k 0) :
    IsUnit c := by
  have h1 : c * rightInv c = 1 := ext_op fun g _ ↦ by
    rw [op_mul, op_rightInv, op_one, mul_gradedRightInv (hc g)]
  have h2 : rightInv c * rightInv (rightInv c) = 1 := ext_op fun g _ ↦ by
    simp only [op_mul, op_rightInv, op_one]
    exact mul_gradedRightInv (gradedRightInv_zero _)
  rw [← left_inv_eq_right_inv h1 h2] at h2
  exact isUnit_iff_exists.2 ⟨rightInv c, h1, h2⟩

/-- **A total class `1 + c_1 + c_2 + ⋯` is a unit**: a total class whose degree-`0` component is
the class `1 ∈ A^0(Y)` is invertible in the ring of total classes. -/
theorem isUnit_of_apply_zero {c : TotalChowClass C sY} (hc : c 0 = (1 : TotalChowClass C sY) 0) :
    IsUnit c :=
  isUnit_of_op_apply_zero fun g _ k ↦ by
    rw [← op_one g]
    refine AddMonoidHom.ext fun α ↦ ?_
    rw [op_apply, op_apply, hc]

/-- The operation of the inverse of a unit is the inverse of its operation. -/
theorem op_inv (c : (TotalChowClass C sY)ˣ) {T : Scheme.{u}} (g : T ⟶ Y)
    [LocallyOfFiniteType g] :
    (↑c⁻¹ : TotalChowClass C sY).op g = ↑(Units.map (opRingHom (C := C) g).toMonoidHom c)⁻¹ :=
  rfl

end TotalChowClass

end Stacks.Chow

end
