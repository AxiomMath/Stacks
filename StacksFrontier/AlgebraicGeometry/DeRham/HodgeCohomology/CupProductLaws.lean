module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CanonicalCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalPairingLaws
import StacksCore.Tactic.StacksAttribute

/-!
# Associativity and graded commutativity of the cup product on Hodge cohomology

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` (for a
morphism of schemes `p : X ⟶ S`, `A = p^{-1}𝒪_S`) and let `Ω^p` be the exterior powers of its
sheaf of relative differentials. Section 50.5 of the source (Tag 0FM4) defines the Hodge
cohomology `H^n_{Hodge}(X/S) = ⨁_{p + q = n} H^q(X, Ω^p)` and the cup product

`∪ : H^i_{Hodge}(X/S) × H^j_{Hodge}(X/S) ⟶ H^{i + j}_{Hodge}(X/S)`

combining the wedge product of forms with the cup product of Cohomology, Section 0FKU. We
construct that cup product and show, as in Tag 0FM5, that it is associative and graded
commutative.

The grading is the total degree `p + q` of `H^q(X, Ω^p)`, and the sign of graded commutativity
is that of the total degrees. The cup product of pure bidegrees carries the Koszul sign
`(-1)^{qp'}` of reading `H^q(X, Ω^p)` as the degree-`p + q` cohomology of `Ω^p[-p]`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.hodgeCohomologyCupProduct`: the cup product of Cohomology,
  Section 0FKU on the groups `H^q(X, Ω^p)`, as a
  `AlgebraicGeometry.SheafOfModules.HodgeCohomologyCupProduct`.
* `AlgebraicGeometry.SheafOfModules.hodgeTotalCupProduct`: the cup product on `H^*_{Hodge}(X/S)`,
  the biadditive extension to the direct sums of the cup product of pure bidegrees.

## Main results

* `AlgebraicGeometry.SheafOfModules.hodgeTotalCupProduct_assoc`: the cup product on
  `H^*_{Hodge}(X/S)` is associative.
* `AlgebraicGeometry.SheafOfModules.hodgeTotalCupProduct_comm`: the cup product on
  `H^*_{Hodge}(X/S)` is graded commutative, `x ∪ y = (-1)^{nm} y ∪ x` for `x` of total degree `n`
  and `y` of total degree `m`.

## References

* [Stacks Project, Tag 0FM5](https://stacks.math.columbia.edu/tag/0FM5)
* [Stacks Project, Tag 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape Opposite
open TopologicalSpace
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.Cohomology.DerivedGlobalCupProduct (cohomologyModule)
open scoped TensorProduct DirectSum Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-- Reading a class of `H^n(moduleDerived Ω^p[0])` in an equal degree `n'` is reindexing the
corresponding Hodge cohomology class. -/
theorem hodgeComponentIso_eqToHom {p : ℕ} {n n' : ℤ} (h : n = n')
    (y : cohomologyModule (moduleDerived (singleNat (deRhamTerm B p))) n) :
    ofHodgeComponentBase B ((hodgeComponentIso B p n').hom.hom
        ((eqToHom (congrArg (cohomologyModule (moduleDerived (singleNat (deRhamTerm B p)))) h)).hom
          y)) =
      reindexHodgeDeg B h (ofHodgeComponentBase B ((hodgeComponentIso B p n).hom.hom y)) := by
  subst h
  rfl

/-- A Hodge cohomology class through `hodgeComponentIso` and back. -/
theorem hodgeComponentIso_inv_hom_apply {p : ℕ} {n : ℤ}
    (y : cohomologyModule (moduleDerived (singleNat (deRhamTerm B p))) n) :
    (hodgeComponentIso B p n).inv.hom (toHodgeComponentBase B
      (ofHodgeComponentBase B ((hodgeComponentIso B p n).hom.hom y))) = y :=
  ModuleCat.inv_hom_apply _ y

section Monoidal

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory

/-- The cup product of Cohomology, Section 0FKU on the groups `H^q(X, Ω^p)` is associative
whenever the multiplications of forms are, as in Cohomology, Lemma 0FP4. -/
theorem hodgeComponentCup_assoc {p p' p'' r s s' t : ℕ} (hs : s = s')
    (m₁ : FormsMultiplication B p p' r) (m₂ : FormsMultiplication B r p'' s)
    (m₃ : FormsMultiplication B p' p'' t) (m₄ : FormsMultiplication B p t s')
    (h : IsAssociativeTriple B m₁ m₂ m₃ m₄) (q q' q'' : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q')
    (θ : hodgeCohomologyComponent B p'' q'') :
    reindexHodge B hs (add_assoc q q' q'')
        (hodgeComponentCup B m₂ (q + q') q'' (hodgeComponentCup B m₁ q q' ξ ζ) θ) =
      hodgeComponentCup B m₄ q (q' + q'') ξ (hodgeComponentCup B m₃ q' q'' ζ θ) := by
  subst hs
  have hcx := multiplicationInt_assoc (singleMultiplication m₁) (singleMultiplication m₂)
    (singleMultiplication m₃) (singleMultiplication m₄)
    (singleMultiplication_assoc_value m₁ m₂ m₃ m₄ (isAssociativeTriple_tmul B h))
  have he := canonicalPairingModule_assoc _ _ _ _ hcx q q' q''
    ((hodgeComponentIso B p q).inv.hom (toHodgeComponentBase B ξ))
    ((hodgeComponentIso B p' q').inv.hom (toHodgeComponentBase B ζ))
    ((hodgeComponentIso B p'' q'').inv.hom (toHodgeComponentBase B θ))
  rw [Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast] at he
  simp only [hodgeComponentCup, reindexHodge, reindexHodgeForm_rfl, hodgeComponentIso_inv_hom_apply]
  rw [← hodgeComponentIso_eqToHom, he]

end Monoidal

section Symmetric

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexSymmetricCategory

/-- The cup product of Cohomology, Section 0FKU on the groups `H^q(X, Ω^p)`: transposing the
multiplication of forms transposes the pairing, with the sign `(-1)^{qq'}`, as in Cohomology,
Lemma 0FP5. -/
theorem hodgeComponentCup_comm
    {p p' r r' : ℕ} (hr : r' = r) (m : FormsMultiplication B p p' r)
    (m' : FormsMultiplication B p' p r') (k : ℤ) (h : IsScaledTranspose B m m' k) (q q' : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeComponentCup B m q q' ξ ζ =
      (k * ((q * q').negOnePow : ℤ)) • reindexHodge B hr (add_comm q' q)
        (hodgeComponentCup B m' q' q ζ ξ) := by
  subst hr
  have hcx := multiplicationInt_braiding (singleMultiplication m)
    (singleMultiplication (k • m'))
    (singleMultiplication_comm_value m (k • m') (isScaledTranspose_tmul B h))
  have he := canonicalPairingModule_comm _ _ hcx q q'
    ((hodgeComponentIso B p q).inv.hom (toHodgeComponentBase B ξ))
    ((hodgeComponentIso B p' q').inv.hom (toHodgeComponentBase B ζ))
  rw [singleMultiplication_zsmul, canonicalPairingModule_zsmul,
    Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast] at he
  simp only [hodgeComponentCup, reindexHodge, reindexHodgeForm_rfl]
  rw [he, ← hodgeComponentIso_eqToHom, ModuleCat.hom_zsmul, LinearMap.smul_apply, map_zsmul,
    map_zsmul, map_zsmul, smul_smul, mul_comm]
  rfl

end Symmetric

/-- The cup product of Cohomology, Section 0FKU on the groups `H^q(X, Ω^p)`, with its
bilinearity, associativity and graded commutativity. -/
def hodgeCohomologyCupProduct : HodgeCohomologyCupProduct B where
  cup m q q' := hodgeComponentCup B m q q'
  cup_add_left m q q' := hodgeComponentCup_add_left B m q q'
  cup_add_right m q q' := hodgeComponentCup_add_right B m q q'
  cup_smul_left m q q' := hodgeComponentCup_smul_left B m q q'
  cup_smul_right m q q' := hodgeComponentCup_smul_right B m q q'
  cup_assoc hs m₁ m₂ m₃ m₄ h q q' q'' ξ ζ θ :=
    hodgeComponentCup_assoc B hs m₁ m₂ m₃ m₄ h q q' q'' ξ ζ θ
  cup_comm hr m m' k h q q' ξ ζ := hodgeComponentCup_comm B hr m m' k h q q' ξ ζ

/-- The cup product on Hodge cohomology in pure bidegrees

`∪ : H^q(X, Ω^p) × H^{q'}(X, Ω^{p'}) ⟶ H^{q + q'}(X, Ω^{p + p'})`

of Section 50.5: the cup product of Cohomology, Section 0FKU along the wedge product of
Tag 0FM2, with the Koszul sign `(-1)^{qp'}` (`AlgebraicGeometry.SheafOfModules.hodgeCupProduct`),
for the constructed cup product `hodgeCohomologyCupProduct`. -/
abbrev hodgeCohomologyCup (p p' : ℕ) (q q' : ℤ) (ξ : hodgeCohomologyComponent B p q)
    (ζ : hodgeCohomologyComponent B p' q') : hodgeCohomologyComponent B (p + p') (q + q') :=
  hodgeCupProduct B (hodgeCohomologyCupProduct B) p p' q q' ξ ζ

/-! ### Transport along equalities of degrees -/

/-- Reindexing a Hodge cohomology class does not change it up to heterogeneous equality. -/
theorem reindexHodge_heq {p p' : ℕ} {q q' : ℤ} (hp : p = p') (hq : q = q')
    (x : hodgeCohomologyComponent B p q) : HEq (reindexHodge B hp hq x) x := by
  subst hp hq; rfl

/-- Reindexing the cohomological degree does not change a class up to heterogeneous equality. -/
theorem reindexHodgeDeg_heq {p : ℕ} {q q' : ℤ} (hq : q = q')
    (x : hodgeCohomologyComponent B p q) : HEq (reindexHodgeDeg B hq x) x := by
  subst hq; rfl

/-- Reindexing the cohomological degree is additive. -/
theorem reindexHodgeDeg_add {p : ℕ} {q q' : ℤ} (hq : q = q')
    (x y : hodgeCohomologyComponent B p q) :
    reindexHodgeDeg B hq (x + y) = reindexHodgeDeg B hq x + reindexHodgeDeg B hq y := by
  subst hq; rfl

/-- Reindexing the cohomological degree commutes with integer multiples. -/
theorem reindexHodgeDeg_zsmul {p : ℕ} {q q' : ℤ} (hq : q = q') (k : ℤ)
    (x : hodgeCohomologyComponent B p q) :
    reindexHodgeDeg B hq (k • x) = k • reindexHodgeDeg B hq x := by
  subst hq; rfl

/-- Integer multiples of heterogeneously equal Hodge classes are heterogeneously equal. -/
theorem zsmul_hodge_heq {p p' : ℕ} {q q' : ℤ} (hp : p = p') (hq : q = q') (k : ℤ)
    {x : hodgeCohomologyComponent B p q} {y : hodgeCohomologyComponent B p' q'}
    (h : HEq x y) : HEq (k • x) (k • y) := by
  subst hp hq; cases h; rfl

/-- The index set of the summands of `H^n_{Hodge}`: the bidegrees `(p, q)` with `p + q = n`. -/
abbrev HodgeBidegree (n : ℕ) := {i : ℕ × ℕ // i.1 + i.2 = n}

/-- A total Hodge cohomology class read in another, equal, total degree. -/
noncomputable def reindexHodgeTotal {n n' : ℕ} (h : n = n') :
    hodgeCohomology B n →+ hodgeCohomology B n' := by
  subst h
  exact AddMonoidHom.id _

/-- Reindexing the total degree on a class of pure bidegree. -/
theorem reindexHodgeTotal_of {n n' : ℕ} (h : n = n') (i : HodgeBidegree n)
    (x : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ)) :
    reindexHodgeTotal B h (DirectSum.of (fun i : HodgeBidegree n =>
        (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) i x) =
      DirectSum.of (fun i : HodgeBidegree n' =>
        (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) ⟨i.1, i.2.trans h⟩ x := by
  subst h; rfl

/-- Two summand inclusions agree on heterogeneously equal classes in equal bidegrees. -/
theorem hodgeOf_congr {n : ℕ} {i j : HodgeBidegree n} (h : i.1 = j.1)
    {x : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ)}
    {y : hodgeCohomologyComponent B j.1.1 (j.1.2 : ℤ)} (hxy : HEq x y) :
    DirectSum.of (fun i : HodgeBidegree n =>
        (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) i x =
      DirectSum.of (fun i : HodgeBidegree n =>
        (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) j y := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  subst h
  cases hxy
  rfl

/-! ### The cup product of pure bidegrees as a biadditive map -/

/-- The cup product of pure bidegrees is additive in its first variable. -/
theorem hodgeCupProduct_add_left (p p' : ℕ) (q q' : ℤ)
    (ξ ξ' : hodgeCohomologyComponent B p q) (ζ : hodgeCohomologyComponent B p' q') :
    hodgeCohomologyCup B p p' q q' (ξ + ξ') ζ =
      hodgeCohomologyCup B p p' q q' ξ ζ + hodgeCohomologyCup B p p' q q' ξ' ζ := by
  simp only [hodgeCohomologyCup, hodgeCupProduct, (hodgeCohomologyCupProduct B).cup_add_left,
    smul_add]

/-- The cup product of pure bidegrees is additive in its second variable. -/
theorem hodgeCupProduct_add_right (p p' : ℕ) (q q' : ℤ)
    (ξ : hodgeCohomologyComponent B p q) (ζ ζ' : hodgeCohomologyComponent B p' q') :
    hodgeCohomologyCup B p p' q q' ξ (ζ + ζ') =
      hodgeCohomologyCup B p p' q q' ξ ζ + hodgeCohomologyCup B p p' q q' ξ ζ' := by
  simp only [hodgeCohomologyCup, hodgeCupProduct, (hodgeCohomologyCupProduct B).cup_add_right,
    smul_add]

/-- The cup product of pure bidegrees respects equalities of cohomological degrees. -/
theorem hodgeCupProduct_heq {p p' : ℕ} {q₁ q₂ q₁' q₂' : ℤ} (hq : q₁ = q₂) (hq' : q₁' = q₂')
    {ξ₁ : hodgeCohomologyComponent B p q₁} {ξ₂ : hodgeCohomologyComponent B p q₂}
    {ζ₁ : hodgeCohomologyComponent B p' q₁'} {ζ₂ : hodgeCohomologyComponent B p' q₂'}
    (hξ : HEq ξ₁ ξ₂) (hζ : HEq ζ₁ ζ₂) :
    HEq (hodgeCohomologyCup B p p' q₁ q₁' ξ₁ ζ₁) (hodgeCohomologyCup B p p' q₂ q₂' ξ₂ ζ₂) := by
  subst hq hq'; cases hξ; cases hζ; rfl

/-- The summand of the total cup product at a pair of bidegrees. -/
noncomputable def hodgeCupSummand {n m : ℕ} (i : HodgeBidegree n) (j : HodgeBidegree m) :
    (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u) →+
      (hodgeCohomologyComponent B j.1.1 (j.1.2 : ℤ) : Type u) →+ hodgeCohomology B (n + m) :=
  AddMonoidHom.mk' (fun ξ => AddMonoidHom.mk' (fun ζ =>
      DirectSum.of (fun k : HodgeBidegree (n + m) =>
          (hodgeCohomologyComponent B k.1.1 (k.1.2 : ℤ) : Type u))
        ⟨(i.1.1 + j.1.1, i.1.2 + j.1.2), by have := i.2; have := j.2; dsimp only; omega⟩
        (reindexHodgeDeg B (Nat.cast_add i.1.2 j.1.2).symm
          (hodgeCohomologyCup B i.1.1 j.1.1 (i.1.2 : ℤ) (j.1.2 : ℤ) ξ ζ)))
      (fun ζ ζ' => by
        rw [hodgeCupProduct_add_right, reindexHodgeDeg_add, map_add]))
    (fun ξ ξ' => by
      ext ζ
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [hodgeCupProduct_add_left, reindexHodgeDeg_add, map_add])

/-- The cup product on Hodge cohomology

`∪ : H^n_{Hodge}(X/S) × H^m_{Hodge}(X/S) ⟶ H^{n + m}_{Hodge}(X/S)`,

the biadditive extension of the cup product of pure bidegrees. -/
noncomputable def hodgeTotalCupProduct (n m : ℕ) :
    hodgeCohomology B n →+ hodgeCohomology B m →+ hodgeCohomology B (n + m) :=
  DirectSum.toAddMonoid fun i =>
    (DirectSum.toAddMonoid fun j => (hodgeCupSummand B i j).flip).flip

/-- On classes of pure bidegree the total cup product is the cup product of pure bidegrees:
`ξ ∪ ξ' ∈ H^{q + q'}(X, Ω^{p + p'})` for `ξ ∈ H^q(X, Ω^p)` and `ξ' ∈ H^{q'}(X, Ω^{p'})`. -/
theorem hodgeTotalCupProduct_of {n m : ℕ} (i : HodgeBidegree n) (j : HodgeBidegree m)
    (ξ : hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ))
    (ζ : hodgeCohomologyComponent B j.1.1 (j.1.2 : ℤ)) :
    hodgeTotalCupProduct B n m
        (DirectSum.of (fun i : HodgeBidegree n =>
          (hodgeCohomologyComponent B i.1.1 (i.1.2 : ℤ) : Type u)) i ξ)
        (DirectSum.of (fun j : HodgeBidegree m =>
          (hodgeCohomologyComponent B j.1.1 (j.1.2 : ℤ) : Type u)) j ζ) =
      DirectSum.of (fun k : HodgeBidegree (n + m) =>
          (hodgeCohomologyComponent B k.1.1 (k.1.2 : ℤ) : Type u))
        ⟨(i.1.1 + j.1.1, i.1.2 + j.1.2), by have := i.2; have := j.2; dsimp only; omega⟩
        (reindexHodgeDeg B (Nat.cast_add i.1.2 j.1.2).symm
          (hodgeCohomologyCup B i.1.1 j.1.1 (i.1.2 : ℤ) (j.1.2 : ℤ) ξ ζ)) := by
  simp only [hodgeTotalCupProduct, DirectSum.toAddMonoid_of, AddMonoidHom.flip_apply]
  rfl

/-- The cup product on `H^*_{Hodge}(X/S)` is associative: `(x ∪ y) ∪ z = x ∪ (y ∪ z)` for `x`,
`y`, `z` of total degrees `n`, `m`, `l`, the two sides read in the same group
`H^{n + m + l}_{Hodge}(X/S)`. -/
@[stacks 0FM5 "the cup product on H^*_Hodge(X/S) = ⨁_{p+q=n} H^q(X, Ω^p) is associative; the cup \
product is constructed (hodgeCohomologyCupProduct: the 0FKU pairing of the ringed space \
(X, A) along the wedge product), nothing assumed"]
theorem hodgeTotalCupProduct_assoc (n m l : ℕ) (x : hodgeCohomology B n)
    (y : hodgeCohomology B m) (z : hodgeCohomology B l) :
    reindexHodgeTotal B (add_assoc n m l)
        (hodgeTotalCupProduct B (n + m) l (hodgeTotalCupProduct B n m x y) z) =
      hodgeTotalCupProduct B n (m + l) x (hodgeTotalCupProduct B m l y z) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx']
  | of i ξ =>
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp [hy, hy']
  | of j ζ =>
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z z' hz hz' => simp [hz, hz']
  | of k θ =>
  rw [hodgeTotalCupProduct_of, hodgeTotalCupProduct_of, hodgeTotalCupProduct_of,
    hodgeTotalCupProduct_of, reindexHodgeTotal_of]
  refine hodgeOf_congr B (Prod.ext (add_assoc _ _ _) (add_assoc _ _ _)) ?_
  refine (reindexHodgeDeg_heq B _ _).trans (HEq.trans ?_ (reindexHodgeDeg_heq B _ _).symm)
  refine (hodgeCupProduct_heq B (Nat.cast_add i.1.2 j.1.2) rfl
    (reindexHodgeDeg_heq B _ _) HEq.rfl).trans (HEq.trans ?_
      (hodgeCupProduct_heq B rfl (Nat.cast_add j.1.2 k.1.2) HEq.rfl
        (reindexHodgeDeg_heq B _ _)).symm)
  exact (reindexHodge_heq B _ _ _).symm.trans
    (heq_of_eq (hodgeCupProduct_assoc B (hodgeCohomologyCupProduct B) _ _ _ _ _ _ ξ ζ θ))

/-- The cup product on `H^*_{Hodge}(X/S)` is graded commutative: `x ∪ y = (-1)^{nm} y ∪ x` for
`x` of degree `n` and `y` of degree `m`. -/
@[stacks 0FM5 "the cup product on H^*_Hodge(X/S) is graded commutative, x ∪ y = (-1)^(nm) y ∪ x \
for x, y of total degrees n, m; the cup product is constructed (hodgeCohomologyCupProduct), \
nothing assumed"]
theorem hodgeTotalCupProduct_comm (n m : ℕ) (x : hodgeCohomology B n)
    (y : hodgeCohomology B m) :
    hodgeTotalCupProduct B n m x y =
      ((((n : ℤ) * m).negOnePow : ℤ)) •
        reindexHodgeTotal B (add_comm m n) (hodgeTotalCupProduct B m n y x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x x' hx hx' => simp [hx, hx', smul_add]
  | of i ξ =>
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y y' hy hy' => simp [hy, hy', smul_add]
  | of j ζ =>
  rw [hodgeTotalCupProduct_of, hodgeTotalCupProduct_of, reindexHodgeTotal_of, ← map_zsmul]
  refine hodgeOf_congr B (Prod.ext (add_comm _ _) (add_comm _ _)) ?_
  have hs : ((((i.1.1 : ℤ) + (i.1.2 : ℤ)) * ((j.1.1 : ℤ) + (j.1.2 : ℤ))).negOnePow : ℤ) =
      ((((n : ℤ) * m).negOnePow : ℤ)) := by
    rw [show ((i.1.1 : ℤ) + (i.1.2 : ℤ)) = n by exact_mod_cast i.2,
      show ((j.1.1 : ℤ) + (j.1.2 : ℤ)) = m by exact_mod_cast j.2]
  refine (reindexHodgeDeg_heq B _ _).trans ?_
  rw [hodgeCohomologyCup, hodgeCupProduct_comm B (hodgeCohomologyCupProduct B), hs]
  refine (zsmul_hodge_heq B (Nat.add_comm _ _) (add_comm _ _) _
    (reindexHodge_heq B _ _ _)).trans ?_
  exact zsmul_hodge_heq B rfl (Nat.cast_add _ _).symm _ (reindexHodgeDeg_heq B _ _).symm

end AlgebraicGeometry.SheafOfModules

end
