module

public import Mathlib.Algebra.DirectSum.Ring
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProductUnit

/-!
# The ring of even-degree de Rham cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex. The cup product of Section 50.4 makes

`⨁_{i ≥ 0} H^{2i}_{dR}`

a commutative ring, graded by `i ↦ H^{2i}_{dR}`: it is associative and graded commutative
(Tag 0FM3), the sign `(-1)^{(2i)(2j)}` being `1`, and the class `1 ∈ H^0_{dR}` is a two-sided unit.
This is the ring `A(X)` of the proofs of Lemmas 0FW9 and 0FWB in the Stacks project.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.evenDeRhamCohomology`: the graded piece `H^{2i}_{dR}`.
* `AlgebraicGeometry.SheafOfModules.evenDeRhamRing`: `⨁_{i ≥ 0} H^{2i}_{dR}`, a commutative ring.
* `AlgebraicGeometry.SheafOfModules.evenDeRhamRingHom`: the ring homomorphism induced by a family
  of additive maps `H^m_{dR} ⟶ H^m_{dR}'` compatible with the unit and the cup product.

## Implementation notes

The product of `H^{2i}` and `H^{2j}` lands in degree `2i + 2j`, which is equal but not
definitionally equal to `2(i + j)`; it is transported by
`AlgebraicGeometry.SheafOfModules.reindexDeRhamCohomology`, and the laws of the graded monoid are
equalities of elements of the sigma type, reduced to equalities of transports.

## References

* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
* [Stacks Project, Tag 0FWB](https://stacks.math.columbia.edu/tag/0FWB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### Transport and the cup product -/

/-- Transporting along an equality of degrees sends zero to zero. -/
theorem reindexDeRhamCohomology_zero {m n : ℤ} (h : m = n) :
    reindexDeRhamCohomology B D h 0 = 0 := by
  subst h
  rfl

/-- The cup product with a transported first factor is the transported cup product. -/
theorem deRhamCohomologyCup_reindex_left {m m' : ℤ} (h : m = m') (n : ℤ)
    (x : deRhamCohomology B D m) (y : deRhamCohomology B D n) :
    deRhamCohomologyCup B D m' n (reindexDeRhamCohomology B D h x) y =
      reindexDeRhamCohomology B D (by rw [h]) (deRhamCohomologyCup B D m n x y) := by
  subst h
  rfl

/-- The cup product with a transported second factor is the transported cup product. -/
theorem deRhamCohomologyCup_reindex_right (m : ℤ) {n n' : ℤ} (h : n = n')
    (x : deRhamCohomology B D m) (y : deRhamCohomology B D n) :
    deRhamCohomologyCup B D m n' x (reindexDeRhamCohomology B D h y) =
      reindexDeRhamCohomology B D (by rw [h]) (deRhamCohomologyCup B D m n x y) := by
  subst h
  rfl

/-- The cup product vanishes when its first factor does. -/
theorem deRhamCohomologyCup_zero_left (m n : ℤ) (y : deRhamCohomology B D n) :
    deRhamCohomologyCup B D m n 0 y = 0 := by
  simpa using deRhamCohomologyCup_add_left B D m n 0 0 y

/-- The cup product vanishes when its second factor does. -/
theorem deRhamCohomologyCup_zero_right (m n : ℤ) (x : deRhamCohomology B D m) :
    deRhamCohomologyCup B D m n x 0 = 0 := by
  simpa using deRhamCohomologyCup_add_right B D m n x 0 0

/-! ### The graded ring -/

/-- **The graded piece `H^{2i}_{dR}`** of the even-degree de Rham cohomology ring. -/
abbrev evenDeRhamCohomology (i : ℕ) : Type u :=
  deRhamCohomology B D ((2 * i : ℕ) : ℤ)

/-- The degree `2i + 2j` of a cup product of even-degree classes is `2(i + j)`. -/
theorem two_mul_add_cast (i j : ℕ) :
    ((2 * i : ℕ) : ℤ) + ((2 * j : ℕ) : ℤ) = ((2 * (i + j) : ℕ) : ℤ) := by
  push_cast
  ring

/-- **The product of `H^{2i}_{dR}` and `H^{2j}_{dR}`**: the cup product, read in degree
`2(i + j)`. -/
def evenDeRhamMul {i j : ℕ} (a : evenDeRhamCohomology B D i) (b : evenDeRhamCohomology B D j) :
    evenDeRhamCohomology B D (i + j) :=
  reindexDeRhamCohomology B D (two_mul_add_cast i j) (deRhamCohomologyCup B D _ _ a b)

/-- The unit of the graded family `i ↦ H^{2i}_{dR}` is the class `1 ∈ H^0_{dR}`. -/
instance evenDeRhamGOne : GradedMonoid.GOne (evenDeRhamCohomology B D) where
  one := (deRhamOneClass B D : deRhamCohomology B D ((2 * 0 : ℕ) : ℤ))

/-- The graded multiplication `H^{2i}_{dR} × H^{2j}_{dR} → H^{2(i + j)}_{dR}` is
`evenDeRhamMul`. -/
instance evenDeRhamGMul : GradedMonoid.GMul (evenDeRhamCohomology B D) where
  mul a b := evenDeRhamMul B D a b

/-- Two elements of the sigma type over the even-degree pieces are equal as soon as one is the
transport of the other. -/
theorem evenDeRham_mk_eq {i j : ℕ} (h : i = j) (x : evenDeRhamCohomology B D i)
    (y : evenDeRhamCohomology B D j)
    (hxy : reindexDeRhamCohomology B D (by rw [h]) x = y) :
    (GradedMonoid.mk i x : GradedMonoid (evenDeRhamCohomology B D)) = GradedMonoid.mk j y := by
  subst h
  subst hxy
  rfl

/-- The class `1 ∈ H^0_{dR}` is a left unit for the graded product. -/
theorem evenDeRham_one_mul (a : GradedMonoid (evenDeRhamCohomology B D)) : 1 * a = a := by
  obtain ⟨i, a⟩ := a
  change GradedMonoid.mk (0 + i) (evenDeRhamMul B D (deRhamOneClass B D :
    evenDeRhamCohomology B D 0) a) = GradedMonoid.mk i a
  refine evenDeRham_mk_eq B D (zero_add i) _ _ ?_
  rw [evenDeRhamMul, reindexDeRhamCohomology_reindexDeRhamCohomology]
  exact deRhamCohomologyCup_one_left B D _ a

/-- The class `1 ∈ H^0_{dR}` is a right unit for the graded product. -/
theorem evenDeRham_mul_one (a : GradedMonoid (evenDeRhamCohomology B D)) : a * 1 = a := by
  obtain ⟨i, a⟩ := a
  change GradedMonoid.mk (i + 0) (evenDeRhamMul B D a (deRhamOneClass B D :
    evenDeRhamCohomology B D 0)) = GradedMonoid.mk i a
  refine evenDeRham_mk_eq B D (add_zero i) _ _ ?_
  rw [evenDeRhamMul, reindexDeRhamCohomology_reindexDeRhamCohomology]
  exact deRhamCohomologyCup_one_right B D _ a

/-- The graded product of even-degree classes is associative. -/
theorem evenDeRham_mul_assoc (a b c : GradedMonoid (evenDeRhamCohomology B D)) :
    a * b * c = a * (b * c) := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  obtain ⟨k, c⟩ := c
  change GradedMonoid.mk (i + j + k) (evenDeRhamMul B D (evenDeRhamMul B D a b) c) =
    GradedMonoid.mk (i + (j + k)) (evenDeRhamMul B D a (evenDeRhamMul B D b c))
  refine evenDeRham_mk_eq B D (add_assoc i j k) _ _ ?_
  simp only [evenDeRhamMul]
  rw [deRhamCohomologyCup_reindex_left, deRhamCohomologyCup_reindex_right,
    ← deRhamCohomologyCup_assoc]
  simp only [reindexDeRhamCohomology_reindexDeRhamCohomology]

/-- The graded product of even-degree classes is commutative. -/
theorem evenDeRham_mul_comm (a b : GradedMonoid (evenDeRhamCohomology B D)) : a * b = b * a := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  change GradedMonoid.mk (i + j) (evenDeRhamMul B D a b) =
    GradedMonoid.mk (j + i) (evenDeRhamMul B D b a)
  refine evenDeRham_mk_eq B D (add_comm i j) _ _ ?_
  simp only [evenDeRhamMul]
  have heven : Even (((2 * i : ℕ) : ℤ) * ((2 * j : ℕ) : ℤ)) :=
    ⟨((2 * i * j : ℕ) : ℤ), by push_cast; ring⟩
  rw [deRhamCohomologyCup_comm, Int.negOnePow_even _ heven, Units.val_one, one_smul]
  simp only [reindexDeRhamCohomology_reindexDeRhamCohomology]

/-- The even-degree pieces `i ↦ H^{2i}_{dR}` form a graded commutative ring under the cup
product. -/
instance evenDeRhamGCommRing : DirectSum.GCommRing (evenDeRhamCohomology B D) where
  one_mul := evenDeRham_one_mul B D
  mul_one := evenDeRham_mul_one B D
  mul_assoc := evenDeRham_mul_assoc B D
  mul_comm := evenDeRham_mul_comm B D
  mul_zero a := by
    dsimp only [GradedMonoid.GMul.mul, evenDeRhamMul]
    rw [deRhamCohomologyCup_zero_right, reindexDeRhamCohomology_zero]
  zero_mul b := by
    dsimp only [GradedMonoid.GMul.mul, evenDeRhamMul]
    rw [deRhamCohomologyCup_zero_left, reindexDeRhamCohomology_zero]
  mul_add a b c := by
    dsimp only [GradedMonoid.GMul.mul, evenDeRhamMul]
    rw [deRhamCohomologyCup_add_right, reindexDeRhamCohomology_add]
  add_mul a b c := by
    dsimp only [GradedMonoid.GMul.mul, evenDeRhamMul]
    rw [deRhamCohomologyCup_add_left, reindexDeRhamCohomology_add]
  natCast n := n • (GradedMonoid.GOne.one : evenDeRhamCohomology B D 0)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n
  intCast n := n • (GradedMonoid.GOne.one : evenDeRhamCohomology B D 0)
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

/-- **The ring of even-degree de Rham cohomology** `⨁_{i ≥ 0} H^{2i}_{dR}`, with the cup
product. -/
abbrev evenDeRhamRing : Type u :=
  DirectSum ℕ (evenDeRhamCohomology B D)

/-- **The grading** `A^i = H^{2i}_{dR}` of the even-degree ring, as additive subgroups. -/
def evenDeRhamGrade (i : ℕ) : AddSubgroup (evenDeRhamRing B D) :=
  (DirectSum.of (evenDeRhamCohomology B D) i).range

/-- **The grading is a direct sum decomposition**, `⨁_i A^i = A`. -/
theorem isInternal_evenDeRhamGrade : DirectSum.IsInternal (evenDeRhamGrade B D) := by
  classical
  let f : ∀ i, evenDeRhamCohomology B D i →+ evenDeRhamGrade B D i := fun i =>
    (DirectSum.of (evenDeRhamCohomology B D) i).rangeRestrict
  have hf : Function.Bijective (DirectSum.map f) :=
    ⟨(DirectSum.map_injective f).2 fun i _ _ hab =>
        DirectSum.of_injective i (congrArg Subtype.val hab),
      (DirectSum.map_surjective f).2 fun i =>
        (DirectSum.of (evenDeRhamCohomology B D) i).rangeRestrict_surjective⟩
  have hcomp : (DirectSum.coeAddMonoidHom (evenDeRhamGrade B D)).comp (DirectSum.map f) =
      AddMonoidHom.id _ := by
    refine DirectSum.addHom_ext fun i a => ?_
    rw [AddMonoidHom.comp_apply, DirectSum.map_of, DirectSum.coeAddMonoidHom_of]
    rfl
  have hb : Function.Bijective ((DirectSum.coeAddMonoidHom (evenDeRhamGrade B D)) ∘
      (DirectSum.map f)) := by
    rw [← AddMonoidHom.coe_comp, hcomp]
    exact Function.bijective_id
  exact (Function.Bijective.of_comp_iff _ hf).1 hb

/-- The unit lies in degree zero. -/
theorem one_mem_evenDeRhamGrade : (1 : evenDeRhamRing B D) ∈ evenDeRhamGrade B D 0 :=
  ⟨GradedMonoid.GOne.one, rfl⟩

/-- Multiplication adds degrees. -/
theorem mul_mem_evenDeRhamGrade (i j : ℕ) {a b : evenDeRhamRing B D}
    (ha : a ∈ evenDeRhamGrade B D i) (hb : b ∈ evenDeRhamGrade B D j) :
    a * b ∈ evenDeRhamGrade B D (i + j) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨GradedMonoid.GMul.mul x y, (DirectSum.of_mul_of x y).symm⟩

/-- Transporting along an equality of degrees commutes with the action of the global sections of
the base ring sheaf. -/
theorem reindexDeRhamCohomology_smul {m n : ℤ} (h : m = n)
    (r : (underlyingRingSheaf A).obj.obj (op ⊤)) (x : deRhamCohomology B D m) :
    reindexDeRhamCohomology B D h (r • x) = r • reindexDeRhamCohomology B D h x := by
  subst h
  rfl

/-- **The structure map of the even-degree ring as an algebra over the global sections of the
base ring sheaf**: `r ↦ r · 1 ∈ H^0_{dR}`. The cup product is bilinear over these sections. -/
def evenDeRhamAlgebraMap :
    (underlyingRingSheaf A).obj.obj (op ⊤) →+* evenDeRhamRing B D where
  toFun r := DirectSum.of (evenDeRhamCohomology B D) 0
    (r • (deRhamOneClass B D : evenDeRhamCohomology B D 0))
  map_one' := by
    rw [one_smul]
    rfl
  map_mul' r s := by
    rw [DirectSum.of_mul_of]
    refine congrArg (DirectSum.of (evenDeRhamCohomology B D) 0) ?_
    change (r * s) • (deRhamOneClass B D : evenDeRhamCohomology B D 0) =
      reindexDeRhamCohomology B D (two_mul_add_cast 0 0)
        (deRhamCohomologyCup B D _ _ (r • (deRhamOneClass B D : evenDeRhamCohomology B D 0))
          (s • (deRhamOneClass B D : evenDeRhamCohomology B D 0)))
    rw [deRhamCohomologyCup_smul_left, deRhamCohomologyCup_smul_right,
      reindexDeRhamCohomology_smul, reindexDeRhamCohomology_smul, mul_smul]
    exact congrArg (fun t => r • s • t)
      (deRhamCohomologyCup_one_left B D 0 (deRhamOneClass B D)).symm
  map_zero' := by
    rw [zero_smul, map_zero]
  map_add' r s := by
    rw [add_smul, map_add]

/-- The structure map lands in degree zero. -/
theorem evenDeRhamAlgebraMap_mem_grade_zero (r : (underlyingRingSheaf A).obj.obj (op ⊤)) :
    evenDeRhamAlgebraMap B D r ∈ evenDeRhamGrade B D 0 :=
  ⟨_, rfl⟩

/-! ### Ring homomorphisms -/

variable {X' : RingedSpace.{u, u}} {A' : TopCat.Sheaf CommRingCat.{u} X'.carrier}
  {φ' : A' ⟶ X'.sheaf}
  (B' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X'.carrier) (moduleOfDifferentials.{u, u, u} φ'))
  (D' : DeRhamDifferential B')

/-- A family of additive maps of de Rham cohomology commutes with transport along equalities of
degrees. -/
theorem reindexDeRhamCohomology_apply
    (P : ∀ m : ℤ, deRhamCohomology B D m →+ deRhamCohomology B' D' m) {m n : ℤ} (h : m = n)
    (x : deRhamCohomology B D m) :
    P n (reindexDeRhamCohomology B D h x) = reindexDeRhamCohomology B' D' h (P m x) := by
  subst h
  rfl

/-- **The ring homomorphism of even-degree de Rham cohomology** induced by a family of additive
maps `H^m_{dR} ⟶ H^m_{dR}'` which preserves the unit and the cup product. -/
def evenDeRhamRingHom (P : ∀ m : ℤ, deRhamCohomology B D m →+ deRhamCohomology B' D' m)
    (hone : P 0 (deRhamOneClass B D) = deRhamOneClass B' D')
    (hmul : ∀ (m n : ℤ) (x : deRhamCohomology B D m) (y : deRhamCohomology B D n),
      P (m + n) (deRhamCohomologyCup B D m n x y) =
        deRhamCohomologyCup B' D' m n (P m x) (P n y)) :
    evenDeRhamRing B D →+* evenDeRhamRing B' D' :=
  DirectSum.toSemiring (fun i => (DirectSum.of (evenDeRhamCohomology B' D') i).comp
      (P ((2 * i : ℕ) : ℤ)))
    (congrArg (DirectSum.of (evenDeRhamCohomology B' D') 0) hone)
    (fun {i j} a b => by
      rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
        DirectSum.of_mul_of]
      refine congrArg (DirectSum.of (evenDeRhamCohomology B' D') (i + j)) ?_
      change P _ (reindexDeRhamCohomology B D (two_mul_add_cast i j)
          (deRhamCohomologyCup B D _ _ a b)) =
        reindexDeRhamCohomology B' D' (two_mul_add_cast i j)
          (deRhamCohomologyCup B' D' _ _ (P _ a) (P _ b))
      rw [reindexDeRhamCohomology_apply, hmul])

/-- On the graded piece `H^{2i}_{dR}`, `evenDeRhamRingHom` is the map `P (2i)`. -/
@[simp]
theorem evenDeRhamRingHom_of (P : ∀ m : ℤ, deRhamCohomology B D m →+ deRhamCohomology B' D' m)
    (hone hmul) (i : ℕ) (a : evenDeRhamCohomology B D i) :
    evenDeRhamRingHom B D B' D' P hone hmul (DirectSum.of _ i a) =
      DirectSum.of (evenDeRhamCohomology B' D') i (P _ a) :=
  DirectSum.toSemiring_of _ _ _ i a

/-- An even-degree ring homomorphism preserves the grading. -/
theorem evenDeRhamRingHom_mem_grade
    (P : ∀ m : ℤ, deRhamCohomology B D m →+ deRhamCohomology B' D' m) (hone hmul) (i : ℕ)
    {a : evenDeRhamRing B D} (ha : a ∈ evenDeRhamGrade B D i) :
    evenDeRhamRingHom B D B' D' P hone hmul a ∈ evenDeRhamGrade B' D' i := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨P _ x, (evenDeRhamRingHom_of B D B' D' P hone hmul i x).symm⟩

end AlgebraicGeometry.SheafOfModules
