module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.TotalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ChowCohomology
public import Mathlib.Algebra.DirectSum.Ring

/-!
# The Chow cohomology algebra `A^*(X)` (Stacks 0B7E)

Let `(S, δ)` be as in Situation 02QL and let `X` be locally of finite type over `S`. The *Chow
cohomology* of `X` is the graded `ℤ`-algebra `A^*(X)` whose degree `p` component is
`A^p(X) = A^p(X ⟶ X)`, the group of bivariant classes of degree `p` (Stacks 0B76) for the
identity of `X`. The product of `a ∈ A^p(X)` and `b ∈ A^q(X)` is the composite
`a ∘ b ∈ A^{p+q}(X ⟶ X)` of Stacks 0B75, and the unit is the class `1 ∈ A^0(X)` acting as the
identity on the Chow groups of every scheme over `X`.

## Main definitions

* `Stacks.Chow.ChowCohomologyGroup` — the degree `p` component `A^p(X) = A^p(X ⟶ X)`, as the
  group of bivariant classes `Stacks.Chow.BivariantChowClass` of Stacks 0B76 for `𝟙 X`.
* `Stacks.Chow.ChowCohomologyGroup.comp` — the composition `A^p(X) × A^q(X) ⟶ A^{p+q}(X)` of
  Stacks 0B75, and `Stacks.Chow.ChowCohomologyGroup.one`, the class `1 ∈ A^0(X)`.
* `Stacks.Chow.ChowCohomologyGroup.instGRing` — the graded ring structure on the family
  `p ↦ A^p(X)`.
* `Stacks.Chow.ChowCohomology` — the graded `ℤ`-algebra `A^*(X) = ⊕_p A^p(X)`.
* `Stacks.Chow.ChowCohomologyGroup.addEquivChowCohomologyComponent`,
  `Stacks.Chow.ChowCohomology.addEquivChowCohomology` — the identifications with
  `Stacks.Chow.chowCohomologyComponent` and `Stacks.Chow.chowCohomology` at the Gysin system
  `Stacks.Chow.gysinSystemOfInvertible` of the first Chern class.

## Main results

* `Stacks.Chow.ChowCohomologyGroup.ext_op` — a class is determined by its operations on the Chow
  groups of the schemes over `X`.
* `Stacks.Chow.ChowCohomologyGroup.op_comp`, `Stacks.Chow.ChowCohomologyGroup.op_one` — the
  operation of a composite is the composite of the operations, and `1` acts as the identity.
* `Stacks.Chow.ChowCohomology.of_mul_of` — the product of homogeneous elements of `A^*(X)` is
  their composite.

## References

* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Sums in two Chow groups of equal degrees are heterogeneously equal when the summands are. -/
theorem chowGroup_add_heq (C : ChowSituation.{u}) {A : Scheme.{u}} {s : A ⟶ C.S}
    [LocallyOfFiniteType s] {k l : ℤ} (h : k = l) {x y : chowGroup C s k}
    {x' y' : chowGroup C s l} (hx : x ≍ x') (hy : y ≍ y') : x + y ≍ x' + y' := by
  subst h
  cases hx
  cases hy
  rfl

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- The group `A^p(X) = A^p(X ⟶ X)` of bivariant classes of degree `p` (Stacks 0B76) for the
identity morphism of `X`. -/
@[stacks 0B7E "the degree p component A^p(X) = A^p(X → X) of the Chow cohomology: the bivariant \
classes of degree p of Stacks 0B76 for id_X"]
abbrev ChowCohomologyGroup (p : ℤ) : Type (u + 1) :=
  BivariantChowClass C sX sX (𝟙 X) (Category.id_comp sX) p

namespace ChowCohomologyGroup

variable {C sX}

/-- The operation of a class on the schemes over `X`: for `c ∈ A^p(X)` and `g : T ⟶ X`
locally of finite type, the map `A_k(T) ⟶ A_{k-p}(T)` obtained by capping with `c` into the Chow
group of `X ×_X T` and pushing forward along the isomorphism `X ×_X T ⟶ T`. -/
def op {p : ℤ} (c : ChowCohomologyGroup C sX p) : IdentityCapRule C sX p :=
  (BivariantChowClass.equivBivariantClass c).idRule C sX (gysinSystemOfInvertible C)

/-- A class of `A^p(X)` is determined by its operations. -/
theorem ext_op {p : ℤ} {c d : ChowCohomologyGroup C sX p}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sX) k), c.op g k α = d.op g k α) : c = d :=
  BivariantChowClass.equivBivariantClass.injective
    (BivariantClass.eq_of_idRule_eq C sX (gysinSystemOfInvertible C) _ _ h)

/-- Two classes of equal degrees with heterogeneously equal operations are the same element of
the graded monoid `Σ p, A^p(X)`. -/
theorem gradedMonoid_ext {p q : ℤ} (c : ChowCohomologyGroup C sX p)
    (d : ChowCohomologyGroup C sX q) (hpq : p = q)
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
      (α : chowGroup C (g ≫ sX) k), c.op g k α ≍ d.op g k α) :
    GradedMonoid.mk (A := ChowCohomologyGroup C sX) p c = GradedMonoid.mk q d := by
  subst hpq
  exact congrArg (GradedMonoid.mk p) (ext_op fun g _ k α ↦ eq_of_heq (h g k α))

/-- The operation of a sum is the sum of the operations. -/
@[simp]
theorem op_add {p : ℤ} (c d : ChowCohomologyGroup C sX p) {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    (c + d).op g k α = c.op g k α + d.op g k α := by
  have hcd : BivariantChowClass.equivBivariantClass (c + d) =
      BivariantChowClass.equivBivariantClass c + BivariantChowClass.equivBivariantClass d :=
    map_add BivariantChowClass.addEquivBivariantClass c d
  simp only [op, hcd, BivariantClass.idRule_add]

/-- The operation of the zero class is zero. -/
@[simp]
theorem op_zero {p : ℤ} {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) : (0 : ChowCohomologyGroup C sX p).op g k α = 0 := by
  have h0 : BivariantChowClass.equivBivariantClass (0 : ChowCohomologyGroup C sX p) = 0 :=
    map_zero BivariantChowClass.addEquivBivariantClass
  simp only [op, h0, BivariantClass.idRule_zero]

/-- The composition `A^p(X) × A^q(X) ⟶ A^{p+q}(X)` of Stacks 0B75: the composite `c ∘ d` of
bivariant classes for `𝟙 X` and `𝟙 X`, a class for `𝟙 X ≫ 𝟙 X = 𝟙 X`. -/
def comp {p q : ℤ} (c : ChowCohomologyGroup C sX p) (d : ChowCohomologyGroup C sX q) :
    ChowCohomologyGroup C sX (p + q) :=
  BivariantChowClass.equivBivariantClass.symm
    ((BivariantChowClass.equivBivariantClass c).mulId C sX
      (BivariantChowClass.equivBivariantClass d))

/-- The class `1 ∈ A^0(X)`: the bivariant class of degree `0` for `𝟙 X` acting as the identity
on the Chow groups of every scheme over `X`. -/
def one : ChowCohomologyGroup C sX 0 :=
  BivariantChowClass.equivBivariantClass.symm (bivariantIdentityClassOfInvertible C sX)

/-- The operation of a composite is the composite of the operations: for `c ∈ A^p(X)` and
`d ∈ A^q(X)`, `(c ∘ d) ∩ α = c ∩ (d ∩ α)` on every scheme over `X`. -/
theorem op_comp {p q : ℤ} (c : ChowCohomologyGroup C sX p) (d : ChowCohomologyGroup C sX q)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    (c.comp d).op g k α ≍ c.op g (k - q) (d.op g k α) :=
  BivariantClass.idRule_mulId C sX (BivariantChowClass.equivBivariantClass c)
    (BivariantChowClass.equivBivariantClass d) g k α

/-- The class `1` acts as the identity. -/
theorem op_one {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) : (one : ChowCohomologyGroup C sX 0).op g k α ≍ α :=
  idRule_bivariantIdentityClassOfInvertible_heq C sX g k α

/-- `1 ∘ c = c` in the graded monoid `Σ p, A^p(X)`. -/
theorem one_comp {p : ℤ} (c : ChowCohomologyGroup C sX p) :
    GradedMonoid.mk (A := ChowCohomologyGroup C sX) (0 + p) (one.comp c) = GradedMonoid.mk p c :=
  gradedMonoid_ext _ _ (zero_add p) fun g _ k α ↦ (op_comp one c g k α).trans (op_one g _ _)

/-- `c ∘ 1 = c` in the graded monoid `Σ p, A^p(X)`. -/
theorem comp_one {p : ℤ} (c : ChowCohomologyGroup C sX p) :
    GradedMonoid.mk (A := ChowCohomologyGroup C sX) (p + 0) (c.comp one) = GradedMonoid.mk p c :=
  gradedMonoid_ext _ _ (add_zero p) fun g _ k α ↦ (op_comp c one g k α).trans
    (IdentityCapRule.heq_congr C sX c.op rfl (sub_zero k) (op_one g k α))

/-- Composition is associative, in the graded monoid `Σ p, A^p(X)`. -/
theorem comp_assoc {p q r : ℤ} (a : ChowCohomologyGroup C sX p) (b : ChowCohomologyGroup C sX q)
    (c : ChowCohomologyGroup C sX r) :
    GradedMonoid.mk (A := ChowCohomologyGroup C sX) (p + q + r) ((a.comp b).comp c) =
      GradedMonoid.mk (p + (q + r)) (a.comp (b.comp c)) :=
  gradedMonoid_ext _ _ (add_assoc p q r) fun g _ k α ↦
    ((op_comp (a.comp b) c g k α).trans (op_comp a b g (k - r) (c.op g k α))).trans
      ((op_comp a (b.comp c) g k α).trans
        (IdentityCapRule.heq_congr C sX a.op rfl (by ring) (op_comp b c g k α))).symm

/-- To compute the operation of a composite, it suffices to identify the iterated operation. -/
private theorem op_comp_eq {p q : ℤ} (c : ChowCohomologyGroup C sX p)
    (d : ChowCohomologyGroup C sX q) {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sX) k) {x : chowGroup C (g ≫ sX) (k - (p + q))}
    (h : c.op g (k - q) (d.op g k α) ≍ x) : (c.comp d).op g k α = x :=
  eq_of_heq ((op_comp c d g k α).trans h)

/-- Composition is additive in its second argument. -/
theorem comp_add {p q : ℤ} (a : ChowCohomologyGroup C sX p) (b c : ChowCohomologyGroup C sX q) :
    a.comp (b + c) = a.comp b + a.comp c :=
  ext_op fun g _ k α ↦ by
    rw [op_add]
    refine op_comp_eq _ _ g k α ?_
    rw [op_add, map_add]
    exact chowGroup_add_heq C (by ring) (op_comp a b g k α).symm (op_comp a c g k α).symm

/-- Composition is additive in its first argument. -/
theorem add_comp {p q : ℤ} (a b : ChowCohomologyGroup C sX p) (c : ChowCohomologyGroup C sX q) :
    (a + b).comp c = a.comp c + b.comp c :=
  ext_op fun g _ k α ↦ by
    rw [op_add]
    refine op_comp_eq _ _ g k α ?_
    rw [op_add]
    exact chowGroup_add_heq C (by ring) (op_comp a c g k α).symm (op_comp b c g k α).symm

/-- The composite with the zero class is zero. -/
theorem comp_zero {p q : ℤ} (a : ChowCohomologyGroup C sX p) :
    a.comp (0 : ChowCohomologyGroup C sX q) = 0 :=
  ext_op fun g _ k α ↦ by
    rw [op_zero]
    refine op_comp_eq _ _ g k α ?_
    rw [op_zero, map_zero]
    exact chowGroup_zero_heq C _ (by ring)

/-- The composite of the zero class with any class is zero. -/
theorem zero_comp {p q : ℤ} (c : ChowCohomologyGroup C sX q) :
    (0 : ChowCohomologyGroup C sX p).comp c = 0 :=
  ext_op fun g _ k α ↦ by
    rw [op_zero]
    refine op_comp_eq _ _ g k α ?_
    rw [op_zero]
    exact chowGroup_zero_heq C _ (by ring)

/-- The graded unit of `p ↦ A^p(X)` is the class `1 ∈ A^0(X)`. -/
instance : GradedMonoid.GOne (ChowCohomologyGroup C sX) where
  one := one

/-- The graded multiplication `A^p(X) × A^q(X) ⟶ A^{p+q}(X)` is the composition of bivariant
classes. -/
instance : GradedMonoid.GMul (ChowCohomologyGroup C sX) where
  mul c d := c.comp d

/-- The family `p ↦ A^p(X)` is a graded ring: the product `A^p(X) × A^q(X) ⟶ A^{p+q}(X)` is the
composition of bivariant classes of Stacks 0B75, which is associative and bilinear, with unit the
class `1 ∈ A^0(X)`. -/
@[stacks 0B7E "the graded Z-algebra structure on A^*(X): the product of the degree p and q \
components is the composition A^p(X → X) × A^q(X → X) → A^{p+q}(X → X) of Stacks 0B75, \
associative and bilinear, with unit 1 ∈ A^0(X)"]
instance instGRing : DirectSum.GRing (ChowCohomologyGroup C sX) where
  one_mul := fun ⟨_, c⟩ ↦ one_comp c
  mul_one := fun ⟨_, c⟩ ↦ comp_one c
  mul_assoc := fun ⟨_, a⟩ ⟨_, b⟩ ⟨_, c⟩ ↦ comp_assoc a b c
  mul_zero := comp_zero
  zero_mul := zero_comp
  mul_add := comp_add
  add_mul := add_comp
  natCast n := n • one
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n
  intCast n := n • one
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

/-- The graded multiplication of `p ↦ A^p(X)` is the composition of Stacks 0B75. -/
@[simp]
theorem gMul_eq_comp {p q : ℤ} (c : ChowCohomologyGroup C sX p) (d : ChowCohomologyGroup C sX q) :
    GradedMonoid.GMul.mul c d = c.comp d :=
  rfl

/-- The graded unit of `p ↦ A^p(X)` is the class `1 ∈ A^0(X)`. -/
@[simp]
theorem gOne_eq_one : (GradedMonoid.GOne.one : ChowCohomologyGroup C sX 0) = one :=
  rfl

/-- `A^p(X)` is the group `Stacks.Chow.chowCohomologyComponent` at the Gysin system of the first
Chern class, the cap operations corresponding identically. -/
def addEquivChowCohomologyComponent (p : ℤ) :
    ChowCohomologyGroup C sX p ≃+ chowCohomologyComponent C (gysinSystemOfInvertible C) sX p :=
  BivariantChowClass.addEquivBivariantClass

/-- Under `addEquivChowCohomologyComponent`, the composition is
`Stacks.Chow.BivariantClass.mulId`. -/
theorem addEquivChowCohomologyComponent_comp {p q : ℤ} (c : ChowCohomologyGroup C sX p)
    (d : ChowCohomologyGroup C sX q) :
    addEquivChowCohomologyComponent (p + q) (c.comp d) =
      (addEquivChowCohomologyComponent p c).mulId C sX (addEquivChowCohomologyComponent q d) :=
  rfl

/-- Under `addEquivChowCohomologyComponent`, the class `1` is
`Stacks.Chow.bivariantIdentityClassOfInvertible`. -/
theorem addEquivChowCohomologyComponent_one :
    addEquivChowCohomologyComponent 0 (one : ChowCohomologyGroup C sX 0) =
      bivariantIdentityClassOfInvertible C sX :=
  rfl

end ChowCohomologyGroup

/-- The *Chow cohomology* `A^*(X)` of `X`: the graded `ℤ`-algebra `⊕_{p ∈ ℤ} A^p(X)` whose degree
`p` component is `A^p(X ⟶ X)`, with the multiplication of
`Stacks.Chow.ChowCohomologyGroup.instGRing`, composition of bivariant classes. -/
@[stacks 0B7E "the Chow cohomology A^*(X): the graded Z-algebra ⊕_p A^p(X → X), with \
multiplication the composition of bivariant classes"]
abbrev ChowCohomology : Type (u + 1) :=
  DirectSum ℤ (ChowCohomologyGroup C sX)

namespace ChowCohomology

variable {C sX}

/-- The product of homogeneous elements of `A^*(X)` is their composite: for `a ∈ A^p(X)` and
`b ∈ A^q(X)`, `a · b = a ∘ b ∈ A^{p+q}(X)`. -/
theorem of_mul_of {p q : ℤ} (a : ChowCohomologyGroup C sX p) (b : ChowCohomologyGroup C sX q) :
    DirectSum.of (ChowCohomologyGroup C sX) p a * DirectSum.of _ q b =
      DirectSum.of _ (p + q) (a.comp b) :=
  DirectSum.of_mul_of a b

/-- The unit of `A^*(X)` is the class `1 ∈ A^0(X)`. -/
theorem one_def :
    (1 : ChowCohomology C sX) = DirectSum.of (ChowCohomologyGroup C sX) 0 ChowCohomologyGroup.one :=
  rfl

/-- `A^*(X)` is the graded group `Stacks.Chow.chowCohomology` at the Gysin system of the first
Chern class, componentwise by `Stacks.Chow.ChowCohomologyGroup.addEquivChowCohomologyComponent`. -/
def addEquivChowCohomology :
    ChowCohomology C sX ≃+ chowCohomology C (gysinSystemOfInvertible C) sX :=
  DFinsupp.mapRange.addEquiv fun p ↦ ChowCohomologyGroup.addEquivChowCohomologyComponent p

/-- On homogeneous elements, `addEquivChowCohomology` is
`Stacks.Chow.ChowCohomologyGroup.addEquivChowCohomologyComponent`. -/
theorem addEquivChowCohomology_of {p : ℤ} (a : ChowCohomologyGroup C sX p) :
    addEquivChowCohomology (DirectSum.of _ p a) =
      DirectSum.of _ p (ChowCohomologyGroup.addEquivChowCohomologyComponent p a) := by
  change DFinsupp.mapRange (fun p ↦ ⇑(ChowCohomologyGroup.addEquivChowCohomologyComponent p))
    (fun p ↦ map_zero _) (DFinsupp.single p a) = DFinsupp.single p _
  exact DFinsupp.mapRange_single

end ChowCohomology

end Stacks.Chow

end
