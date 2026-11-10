module

public import Mathlib.Algebra.Module.Torsion.Free
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.ExplicitDividedPower.Formula
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic
public import StacksFrontier.RingTheory.DividedPowers.Ring

/-!
# Divided powers on a second-order thickening

Let `(A, I, γ)` be a divided power ring, let `M` and `N` be `A`-modules and let
`q : M →ₗ[A] M →ₗ[A] N` be a bilinear map.  The second-order extension `A ⊕ M ⊕ N`, with
multiplication `(a, m, n) (a', m', n') = (a a', a m' + a' m, a n' + a' n + q m m' + q m' m)`,
carries divided powers on the ideal `I ⊕ M ⊕ N`, given by the explicit formula

`δ_n (a, m, n') = (γ_n a, γ_{n-1} a · m, γ_{n-1} a · n' + γ_{n-2} a · q m m)`.

The unary axioms and the scalar rule for that formula are checked directly.  The three
remaining axioms — additivity, the product rule and the composition rule — are each an identity
between two expressions in one or two elements of the ideal, and are obtained here by transport
from a single universal example: the second-order extension of the divided power polynomial ring
on two variables over `(ℤ, (0))`, whose ideal carries divided powers because that ring is
torsion free.  Any pair of elements of the ideal of any second-order extension is the image of
the two universal variables under a map of second-order extensions compatible with the formula,
so an identity in the universal example is an identity everywhere.

## Main results

* `Crystalline.exists_dividedPowers_secondOrderExtension` constructs the divided powers on the
  ideal of a second-order extension and records that the structure map is a divided power
  morphism.

## Implementation notes

The extension is presented invariantly: an additive equivalence with `A × (M × N)` is required
to identify its multiplication, its structure map and its distinguished ideal.  This lets the
result apply to any chosen implementation of the extension while retaining all three coordinate
formulas of the source.

The universal second-order extension is a structure wrapping the product carrier, so that it
carries the second-order ring structure rather than the componentwise product one.

## References

* [Stacks Project, Tag 07HI](https://stacks.math.columbia.edu/tag/07HI)
-/

@[expose] public section

namespace Crystalline

universe u v w x

noncomputable section

/-- The divided power ring `(ℤ, (0), triv)`, the base of the universal second-order extension. -/
private noncomputable def universalBaseDP : DividedPowerRing :=
  .of ℤ ⊥ (dividedPowersBot ℤ)

/-- The divided power polynomial ring on two variables over `(ℤ, (0))`.  Its two variables are the
universal pair of elements of a divided power ideal. -/
private abbrev universalBase :=
  DividedPowers.dividedPowerPolynomialDividedPowerRing universalBaseDP (Fin 2)

/-- The divided power polynomial ring on two variables is torsion free, being free as a module over
`ℤ`. -/
private instance universalBase_isTorsionFree :
    Module.IsTorsionFree ℤ universalBase := by
  change Module.IsTorsionFree ℤ (DividedPowerAlgebra ℤ (Fin 2 →₀ ℤ))
  exact (DividedPowers.dividedPowerPolynomialMonomialBasis universalBaseDP (Fin 2)).isTorsionFree

/-- The universal module: a free module of rank two over the universal base. -/
private abbrev universalModule := universalBase × universalBase

/-- The universal second tensor power of the universal module. -/
private abbrev universalModuleSquare := TensorProduct universalBase universalModule universalModule

/-- The universal target of a symmetric bilinear map out of the universal module: two free summands
for the values on the basis vectors and one for the tensor square. -/
private abbrev universalCokernelModule :=
  universalBase × (universalBase × universalModuleSquare)

/-- The universal module is torsion free. -/
private theorem universalModule_torsionFree :
    Module.IsTorsionFree ℤ universalModule := Module.IsTorsionFree.trans universalBase

/-- The universal tensor square is torsion free. -/
private theorem universalModuleSquare_torsionFree :
    Module.IsTorsionFree ℤ universalModuleSquare := Module.IsTorsionFree.trans universalBase

/-- The universal target is torsion free. -/
private theorem universalCokernelModule_torsionFree :
    Module.IsTorsionFree ℤ universalCokernelModule := Module.IsTorsionFree.trans universalBase

/-- The carrier of the universal second-order extension. -/
private abbrev universalSecondOrderCarrier :=
  universalBase × (universalModule × universalCokernelModule)

/-- The carrier of the universal second-order extension is torsion free. -/
private theorem universalSecondOrderCarrier_torsionFree :
    Module.IsTorsionFree ℤ universalSecondOrderCarrier := Module.IsTorsionFree.trans universalBase

/-- The universal symmetric bilinear map: it records a pair of elements of the universal module as
their tensor product in the last summand of the universal target. -/
private def universalQ :
    universalModule →ₗ[universalBase] universalModule →ₗ[universalBase]
      universalCokernelModule :=
  LinearMap.mk₂ universalBase
    (fun m m' => (0, (0, TensorProduct.mk universalBase universalModule universalModule m m')))
    (by
      intro m₁ m₂ m'
      change (0, (0, (m₁ + m₂) ⊗ₜ[universalBase] m')) =
        (0, (0, m₁ ⊗ₜ[universalBase] m')) + (0, (0, m₂ ⊗ₜ[universalBase] m'))
      simp [TensorProduct.add_tmul])
    (by
      intro a m m'
      change (0, (0, (a • m) ⊗ₜ[universalBase] m')) =
        a • (0, (0, m ⊗ₜ[universalBase] m'))
      simp [TensorProduct.smul_tmul'])
    (by
      intro m m₁ m₂
      change (0, (0, m ⊗ₜ[universalBase] (m₁ + m₂))) =
        (0, (0, m ⊗ₜ[universalBase] m₁)) + (0, (0, m ⊗ₜ[universalBase] m₂))
      simp [TensorProduct.tmul_add])
    (by
      intro a m m'
      change (0, (0, m ⊗ₜ[universalBase] (a • m'))) =
        a • (0, (0, m ⊗ₜ[universalBase] m'))
      simp [TensorProduct.tmul_smul])

/-- The universal second-order extension, as a type: the carrier wrapped in a structure, so that it
carries the second-order ring structure rather than the componentwise product one. -/
private structure UniversalSecondOrderRing where
  coords : universalSecondOrderCarrier

/-- The universal second-order extension is its carrier. -/
private def UniversalSecondOrderRing.equiv :
    UniversalSecondOrderRing ≃ universalSecondOrderCarrier where
  toFun := UniversalSecondOrderRing.coords
  invFun := UniversalSecondOrderRing.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

/-- The additive group of the universal second-order extension, transported from its carrier. -/
private instance : AddCommGroup UniversalSecondOrderRing :=
  Equiv.addCommGroup UniversalSecondOrderRing.equiv

/-- The universal second-order extension is additively its carrier. -/
private def UniversalSecondOrderRing.addEquiv :
    UniversalSecondOrderRing ≃+ universalSecondOrderCarrier where
  toEquiv := UniversalSecondOrderRing.equiv
  map_add' := by intro x y; rfl

/-- The second-order multiplication on the carrier, the bilinear map contributing the symmetrized
correction in the last coordinate. -/
private def universalSecondOrderMul (x y : universalSecondOrderCarrier) :
    universalSecondOrderCarrier :=
  ((x.1 * y.1),
    (x.1 • y.2.1 + y.1 • x.2.1,
      x.1 • y.2.2 + y.1 • x.2.2 + universalQ x.2.1 y.2.1 + universalQ y.2.1 x.2.1))

/-- Multiplication on the universal second-order extension. -/
private instance : Mul UniversalSecondOrderRing :=
  ⟨fun x y => ⟨universalSecondOrderMul x.coords y.coords⟩⟩

/-- The unit of the universal second-order extension. -/
private instance : One UniversalSecondOrderRing := ⟨⟨(1, (0, 0))⟩⟩

/-- The multiplicative monoid of the universal second-order extension. -/
private instance : Monoid UniversalSecondOrderRing where
  mul_assoc x y z := by
    apply UniversalSecondOrderRing.equiv.injective
    change universalSecondOrderMul (universalSecondOrderMul x.coords y.coords) z.coords =
      universalSecondOrderMul x.coords (universalSecondOrderMul y.coords z.coords)
    ext <;> (try simp [universalSecondOrderMul, universalQ, TensorProduct.smul_tmul',
      TensorProduct.tmul_smul, TensorProduct.tmul_add])
    all_goals try module
    all_goals try ring
  one_mul x := by
    apply UniversalSecondOrderRing.equiv.injective
    change universalSecondOrderMul (1, (0, 0)) x.coords = x.coords
    ext <;> simp [universalSecondOrderMul, universalQ]
  mul_one x := by
    apply UniversalSecondOrderRing.equiv.injective
    change universalSecondOrderMul x.coords (1, (0, 0)) = x.coords
    ext <;> simp [universalSecondOrderMul, universalQ]

/-- The natural number cast into the universal second-order extension. -/
private instance : NatCast UniversalSecondOrderRing :=
  ⟨fun n => n • (1 : UniversalSecondOrderRing)⟩

/-- The semiring structure of the universal second-order extension. -/
private instance : Semiring UniversalSecondOrderRing where
  zero_mul x := by
    apply UniversalSecondOrderRing.equiv.injective
    change universalSecondOrderMul (0, (0, 0)) x.coords = 0
    ext <;> simp [universalSecondOrderMul, universalQ]
  mul_zero x := by
    apply UniversalSecondOrderRing.equiv.injective
    change universalSecondOrderMul x.coords (0, (0, 0)) = 0
    ext <;> simp [universalSecondOrderMul, universalQ]
  left_distrib x y z := by
    apply UniversalSecondOrderRing.equiv.injective
    change universalSecondOrderMul x.coords (y.coords + z.coords) =
      universalSecondOrderMul x.coords y.coords + universalSecondOrderMul x.coords z.coords
    ext <;> (try simp [universalSecondOrderMul, universalQ, TensorProduct.tmul_add])
    all_goals try module
    all_goals try ring
  right_distrib x y z := by
    apply UniversalSecondOrderRing.equiv.injective
    change universalSecondOrderMul (x.coords + y.coords) z.coords =
      universalSecondOrderMul x.coords z.coords + universalSecondOrderMul y.coords z.coords
    ext <;> (try simp [universalSecondOrderMul, universalQ, TensorProduct.tmul_add])
    all_goals try module
    all_goals try ring
  natCast_zero := by simp [NatCast.natCast]
  natCast_succ n := by
    change (n + 1) • (1 : UniversalSecondOrderRing) = n • (1 : UniversalSecondOrderRing) + 1
    exact succ_nsmul 1 n

/-- The integer cast into the universal second-order extension. -/
private instance : IntCast UniversalSecondOrderRing := ⟨fun n => n • (1 : UniversalSecondOrderRing)⟩

/-- The ring structure of the universal second-order extension. -/
private instance : Ring UniversalSecondOrderRing where
  neg_add_cancel x := by
    apply UniversalSecondOrderRing.equiv.injective
    simp
  intCast_negSucc n := by
    change Int.negSucc n • (1 : UniversalSecondOrderRing) =
      -((n + 1) • (1 : UniversalSecondOrderRing))
    simp

/-- The universal second-order extension is commutative, because the correction term of its
multiplication is symmetrized. -/
private instance : CommRing UniversalSecondOrderRing where
  mul_comm x y := by
    apply UniversalSecondOrderRing.equiv.injective
    change universalSecondOrderMul x.coords y.coords = universalSecondOrderMul y.coords x.coords
    ext <;> (try simp [universalSecondOrderMul, universalQ, mul_comm]) <;>
      try module

/-- The structure map of the universal second-order extension, placing a scalar in the first
coordinate. -/
private def universalSecondOrderBaseMap : universalBase →+* UniversalSecondOrderRing where
  toFun a := ⟨(a, (0, 0))⟩
  map_one' := rfl
  map_mul' a b := by
    apply UniversalSecondOrderRing.equiv.injective
    change (a * b, (0, 0)) = universalSecondOrderMul (a, (0, 0)) (b, (0, 0))
    simp [universalSecondOrderMul, universalQ]
  map_zero' := rfl
  map_add' a b := by
    apply UniversalSecondOrderRing.addEquiv.injective
    rw [map_add]
    simp [UniversalSecondOrderRing.addEquiv, UniversalSecondOrderRing.equiv]

/-- The universal second-order extension as an algebra over the universal base. -/
private instance : Algebra universalBase UniversalSecondOrderRing :=
  universalSecondOrderBaseMap.toAlgebra

/-- The projection of the universal second-order extension onto the universal base. -/
private def universalSecondOrderProjection : UniversalSecondOrderRing →+* universalBase where
  toFun b := b.coords.1
  map_one' := rfl
  map_mul' a b := rfl
  map_zero' := rfl
  map_add' a b := by
    have h := UniversalSecondOrderRing.addEquiv.map_add a b
    exact congrArg Prod.fst h

/-- The distinguished ideal of the universal second-order extension: the elements whose first
coordinate lies in the divided power ideal of the universal base. -/
private def universalSecondOrderIdeal : Ideal UniversalSecondOrderRing :=
  Ideal.comap universalSecondOrderProjection universalBase.ideal

/-- Membership in the distinguished ideal is a condition on the first coordinate alone. -/
private lemma universalSecondOrderIdeal_mem_iff (b : UniversalSecondOrderRing) :
    b ∈ universalSecondOrderIdeal ↔ b.coords.1 ∈ universalBase.ideal := Iff.rfl

/-- The universal second-order extension is torsion free. -/
private theorem universalSecondOrderRing_torsionFree :
    Module.IsTorsionFree ℤ UniversalSecondOrderRing := by
  refine ⟨?_⟩
  intro r hr x y h
  apply UniversalSecondOrderRing.equiv.injective
  change r • x = r • y at h
  have h' := congrArg UniversalSecondOrderRing.addEquiv h
  simp only [map_zsmul] at h'
  change r • x.coords = r • y.coords at h'
  change x.coords = y.coords
  exact (universalSecondOrderCarrier_torsionFree.isSMulRegular hr) h'

/-- The structure map of the universal second-order extension in coordinates. -/
private lemma universalSecondOrder_halgebra (a : universalBase) :
    UniversalSecondOrderRing.addEquiv (algebraMap universalBase UniversalSecondOrderRing a) =
      (a, (0, 0)) := by
  rfl

/-- The multiplication of the universal second-order extension in coordinates. -/
private lemma universalSecondOrder_hmul (b b' : UniversalSecondOrderRing) :
    UniversalSecondOrderRing.addEquiv (b * b') =
      ((UniversalSecondOrderRing.addEquiv b).1 *
          (UniversalSecondOrderRing.addEquiv b').1,
        ((UniversalSecondOrderRing.addEquiv b).1 •
            (UniversalSecondOrderRing.addEquiv b').2.1 +
          (UniversalSecondOrderRing.addEquiv b').1 •
            (UniversalSecondOrderRing.addEquiv b).2.1,
          (UniversalSecondOrderRing.addEquiv b).1 •
              (UniversalSecondOrderRing.addEquiv b').2.2 +
            (UniversalSecondOrderRing.addEquiv b').1 •
              (UniversalSecondOrderRing.addEquiv b).2.2 +
            universalQ (UniversalSecondOrderRing.addEquiv b).2.1
              (UniversalSecondOrderRing.addEquiv b').2.1 +
            universalQ (UniversalSecondOrderRing.addEquiv b').2.1
              (UniversalSecondOrderRing.addEquiv b).2.1)) := by
  rfl

/-- The distinguished ideal of the universal second-order extension carries divided powers given by
the explicit second-order formula, by the torsion-free case. -/
private theorem universalSecondOrder_exists_dividedPowers :
    ∃ δ : DividedPowers universalSecondOrderIdeal,
      ∀ (n : ℕ) (b : UniversalSecondOrderRing), 2 ≤ n →
        b ∈ universalSecondOrderIdeal →
        δ.dpow n b = UniversalSecondOrderRing.addEquiv.symm
          (universalBase.dividedPowers.dpow n b.coords.1,
            (universalBase.dividedPowers.dpow (n - 1) b.coords.1 • b.coords.2.1,
              universalBase.dividedPowers.dpow (n - 1) b.coords.1 • b.coords.2.2 +
                universalBase.dividedPowers.dpow (n - 2) b.coords.1 •
                  universalQ b.coords.2.1 b.coords.2.1)) := by
  let : Module.IsTorsionFree ℤ UniversalSecondOrderRing :=
    universalSecondOrderRing_torsionFree
  exact exists_dividedPowers_secondOrderExtension_torsionFree
    universalBase.ideal universalBase.dividedPowers universalQ
    UniversalSecondOrderRing.addEquiv universalSecondOrder_halgebra
    universalSecondOrder_hmul universalSecondOrderIdeal universalSecondOrderIdeal_mem_iff

/-- The divided powers of the universal second-order extension. -/
private noncomputable def universalSecondOrderDividedPowers :
    DividedPowers universalSecondOrderIdeal :=
  Classical.choose universalSecondOrder_exists_dividedPowers

/-- The divided powers of the universal second-order extension are given in degrees at least two by
the explicit second-order formula. -/
private lemma universalSecondOrderDividedPowers_formula
    {n : ℕ} (hn : 2 ≤ n) {b : UniversalSecondOrderRing}
    (hb : b ∈ universalSecondOrderIdeal) :
    universalSecondOrderDividedPowers.dpow n b =
      UniversalSecondOrderRing.addEquiv.symm
        (universalBase.dividedPowers.dpow n b.coords.1,
          (universalBase.dividedPowers.dpow (n - 1) b.coords.1 • b.coords.2.1,
            universalBase.dividedPowers.dpow (n - 1) b.coords.1 • b.coords.2.2 +
              universalBase.dividedPowers.dpow (n - 2) b.coords.1 •
                universalQ b.coords.2.1 b.coords.2.1)) :=
  Classical.choose_spec universalSecondOrder_exists_dividedPowers n b hn hb

/-- The integer cast into any ring is a divided power morphism out of the trivial divided powers on
the zero ideal. -/
private lemma intCast_isDPMorphism
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I) :
    DividedPowers.IsDPMorphism (dividedPowersBot ℤ) γ (Int.castRingHom A) := by
  refine ⟨?_, ?_⟩
  · simp [(bot_le : (⊥ : Ideal A) ≤ I)]
  · intro n a ha
    have ha0 : a = 0 := Ideal.mem_bot.mp ha
    subst a
    by_cases hn : n = 0
    · subst n
      simp [dividedPowersBot, γ.dpow_zero I.zero_mem]
    · simp [dividedPowersBot, γ.dpow_eval_zero hn, hn]

/-- Any two elements of a divided power ideal are the images of the two universal variables under a
divided power morphism out of the universal base. -/
private theorem exists_universalBaseDPMorphism
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {a a' : A} (ha : a ∈ I) (ha' : a' ∈ I) :
    ∃ f : DividedPowers.DPMorphism universalBase.dividedPowers γ,
      f (DividedPowers.dividedPowerPolynomialVariable ℤ (0 : Fin 2)) = a ∧
      f (DividedPowers.dividedPowerPolynomialVariable ℤ (1 : Fin 2)) = a' := by
  let C : DividedPowerRing := .of A I γ
  let f₀ : DividedPowers.DPMorphism (dividedPowersBot ℤ) γ :=
    DividedPowers.DPMorphism.mk' (intCast_isDPMorphism I γ)
  let k : Fin 2 → I := fun i => if i = 0 then ⟨a, ha⟩ else ⟨a', ha'⟩
  obtain ⟨f, hf, _⟩ :=
    DividedPowers.existsUnique_dPMorphism_from_dividedPowerPolynomial
      universalBaseDP (Fin 2) C f₀ k
  refine ⟨f, ?_, ?_⟩
  · have h := hf.2 (0 : Fin 2)
    change f (DividedPowers.dividedPowerPolynomialVariable ℤ (0 : Fin 2)) = a at h
    exact h
  · have h := hf.2 (1 : Fin 2)
    change f (DividedPowers.dividedPowerPolynomialVariable ℤ (1 : Fin 2)) = a' at h
    exact h

/-- Each of the two variables lies in the divided power ideal of the universal base. -/
private lemma universalBase_variable_mem (i : Fin 2) :
    DividedPowers.dividedPowerPolynomialVariable ℤ i ∈ universalBase.ideal := by
  change DividedPowers.dividedPowerPolynomialVariable ℤ i ∈
    DividedPowers.dividedPowerPolynomialIdeal (⊥ : Ideal ℤ) (Fin 2)
  apply Ideal.mem_sup_right
  change DividedPowers.dividedPowerPolynomialAugmentation ℤ (Fin 2)
    (DividedPowers.dividedPowerPolynomialVariable ℤ i) = 0
  simp [DividedPowers.dividedPowerPolynomialAugmentation,
    DividedPowers.dividedPowerPolynomialVariable,
    DividedPowerAlgebra.lift_apply_dp, DividedPowers.dpow_eval_zero]

/-- The map out of the universal module determined by a ring homomorphism from the universal base
and the images of the two basis vectors. -/
private def universalModuleMap
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M] (z z' : M) :
    universalModule →+ M where
  toFun m := f m.1 • z + f m.2 • z'
  map_zero' := by simp
  map_add' m m' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel

/-- The map out of the universal module is semilinear over the chosen ring homomorphism. -/
private lemma universalModuleMap_smul
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M] (z z' : M)
    (a : universalBase) (m : universalModule) :
    universalModuleMap f z z' (a • m) = f a • universalModuleMap f z z' m := by
  simp [universalModuleMap, smul_add, mul_smul]

/-- The map out of the universal module sends the first basis vector to the first chosen value. -/
private lemma universalModuleMap_fst
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M] (z z' : M) :
    universalModuleMap f z z' (1, 0) = z := by
  simp [universalModuleMap]

/-- The map out of the universal module sends the second basis vector to the second chosen
value. -/
private lemma universalModuleMap_snd
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M] (z z' : M) :
    universalModuleMap f z z' (0, 1) = z' := by
  simp [universalModuleMap]

/-- The map out of the universal tensor square induced by a bilinear map and the images of the two
basis vectors. -/
private def universalTensorMap
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) :
    universalModuleSquare →+ N := by
  letI : Module universalBase M := Module.compHom M f
  letI : Module universalBase N := Module.compHom N f
  let φ : universalModule →ₗ[universalBase] M :=
    { universalModuleMap f z z' with
      map_smul' := fun a m => universalModuleMap_smul f z z' a m }
  let β : universalModule →ₗ[universalBase] universalModule →ₗ[universalBase] N :=
    LinearMap.mk₂ universalBase (fun m m' => q (φ m) (φ m'))
      (by intro m₁ m₂ m'; simp)
      (by
        intro a m m'
        rw [map_smul]
        change q (f a • φ m) (φ m') = f a • q (φ m) (φ m')
        simp)
      (by intro m m₁ m₂; simp)
      (by
        intro a m m'
        rw [map_smul]
        change q (φ m) (f a • φ m') = f a • q (φ m) (φ m')
        simp)
  exact (TensorProduct.lift β).toAddMonoidHom

/-- The map out of the universal tensor square on a pure tensor. -/
private lemma universalTensorMap_tmul
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (m m' : universalModule) :
    universalTensorMap f q z z' (m ⊗ₜ[universalBase] m') =
      q (universalModuleMap f z z' m) (universalModuleMap f z z' m') := by
  simp [universalTensorMap]

/-- The map out of the universal tensor square is semilinear over the chosen ring homomorphism. -/
private lemma universalTensorMap_smul
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M)
    (a : universalBase) (t : universalModuleSquare) :
    universalTensorMap f q z z' (a • t) = f a • universalTensorMap f q z z' t := by
  induction t using TensorProduct.inductionOn with
  | tmul m m' =>
      rw [TensorProduct.smul_tmul', universalTensorMap_tmul,
        universalTensorMap_tmul, universalModuleMap_smul]
      simp
  | add t₁ t₂ ht₁ ht₂ =>
      simp [smul_add, map_add, ht₁, ht₂]

/-- The map out of the universal target determined by a ring homomorphism, a bilinear map, and the
images of the generators of the three summands. -/
private def universalCokernelModuleMap
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N) :
    universalCokernelModule →+ N where
  toFun t := f t.1 • w + f t.2.1 • w' +
    universalTensorMap f q z z' t.2.2
  map_zero' := by simp
  map_add' t t' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul]
    abel

/-- The map out of the universal target is semilinear over the chosen ring homomorphism. -/
private lemma universalCokernelModuleMap_smul
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N)
    (a : universalBase) (t : universalCokernelModule) :
    universalCokernelModuleMap f q z z' w w' (a • t) =
      f a • universalCokernelModuleMap f q z z' w w' t := by
  simp [universalCokernelModuleMap, universalTensorMap_smul,
    smul_add, mul_smul]

/-- The map out of the universal target carries the universal bilinear map to the chosen one. -/
private lemma universalCokernelModuleMap_q
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N)
    (m m' : universalModule) :
    universalCokernelModuleMap f q z z' w w' (universalQ m m') =
      q (universalModuleMap f z z' m) (universalModuleMap f z z' m') := by
  simp [universalCokernelModuleMap, universalQ, universalTensorMap_tmul]

/-- The map out of the universal target sends the generator of the first summand to the first
chosen value. -/
private lemma universalCokernelModuleMap_fst
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N) :
    universalCokernelModuleMap f q z z' w w' (1, (0, 0)) = w := by
  simp [universalCokernelModuleMap]

/-- The map out of the universal target sends the generator of the second summand to the second
chosen value. -/
private lemma universalCokernelModuleMap_snd
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N) :
    universalCokernelModuleMap f q z z' w w' (0, (1, 0)) = w' := by
  simp [universalCokernelModuleMap]

/-- The coordinates of the unit of the universal second-order extension. -/
private lemma universalSecondOrder_coords_one :
    (1 : UniversalSecondOrderRing).coords = (1, (0, 0)) := rfl

/-- The coordinates of the zero of the universal second-order extension. -/
private lemma universalSecondOrder_coords_zero :
    (0 : UniversalSecondOrderRing).coords = (0, (0, 0)) := rfl

/-- Addition in the universal second-order extension is coordinatewise. -/
private lemma universalSecondOrder_coords_add (t t' : UniversalSecondOrderRing) :
    (t + t').coords = t.coords + t'.coords := by
  have h := UniversalSecondOrderRing.addEquiv.map_add t t'
  change (t + t').coords = t.coords + t'.coords at h
  exact h

/-- The first universal element of the distinguished ideal: the first variable, the first basis
vector, and the generator of the first summand of the universal target. -/
private def universalFirstElement : UniversalSecondOrderRing :=
  ⟨(DividedPowers.dividedPowerPolynomialVariable ℤ (0 : Fin 2),
    ((1, 0), (1, (0, 0))))⟩

/-- The second universal element of the distinguished ideal: the second variable, the second basis
vector, and the generator of the second summand of the universal target. -/
private def universalSecondElement : UniversalSecondOrderRing :=
  ⟨(DividedPowers.dividedPowerPolynomialVariable ℤ (1 : Fin 2),
    ((0, 1), (0, (1, 0))))⟩

/-- The first universal element lies in the distinguished ideal. -/
private lemma universalFirstElement_mem :
    universalFirstElement ∈ universalSecondOrderIdeal :=
  universalBase_variable_mem 0

/-- The second universal element lies in the distinguished ideal. -/
private lemma universalSecondElement_mem :
    universalSecondElement ∈ universalSecondOrderIdeal :=
  universalBase_variable_mem 1

/-- The map from the universal second-order extension to an arbitrary second-order extension
determined by a ring homomorphism of the bases and the images of the generators. -/
private def universalSecondOrderMap
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1))) :
    UniversalSecondOrderRing →+* B where
  toFun t := e.symm
    (f t.coords.1,
      (universalModuleMap f z z' t.coords.2.1,
        universalCokernelModuleMap f q z z' w w' t.coords.2.2))
  map_one' := by
    apply e.injective
    have h1 : e (1 : B) = (1, (0, 0)) := by simpa using halgebra (1 : A)
    simp [universalSecondOrder_coords_one, universalModuleMap,
      universalCokernelModuleMap, h1]
  map_mul' t t' := by
    apply e.injective
    rw [hmul]
    simp only [e.apply_symm_apply]
    change
      (f (universalSecondOrderMul t.coords t'.coords).1,
        (universalModuleMap f z z' (universalSecondOrderMul t.coords t'.coords).2.1,
          universalCokernelModuleMap f q z z' w w'
            (universalSecondOrderMul t.coords t'.coords).2.2)) = _
    ext <;> simp [universalSecondOrderMul, universalModuleMap_smul,
      universalCokernelModuleMap_smul, universalCokernelModuleMap_q,
      map_add, map_mul]
  map_zero' := by
    apply e.injective
    simp [universalSecondOrder_coords_zero, universalModuleMap,
      universalCokernelModuleMap]
  map_add' t t' := by
    apply e.injective
    simp [universalSecondOrder_coords_add, map_add]

/-- The comparison map in coordinates. -/
private lemma universalSecondOrderMap_coords
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (t : UniversalSecondOrderRing) :
    e (universalSecondOrderMap f q z z' w w' e halgebra hmul t) =
      (f t.coords.1,
        (universalModuleMap f z z' t.coords.2.1,
          universalCokernelModuleMap f q z z' w w' t.coords.2.2)) :=
  e.apply_symm_apply _

/-- The comparison map carries the distinguished ideal of the universal second-order extension into
the distinguished ideal of the target. -/
private lemma universalSecondOrderMap_mem
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    (f : DividedPowers.DPMorphism universalBase.dividedPowers γ)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {t : UniversalSecondOrderRing} (ht : t ∈ universalSecondOrderIdeal) :
    universalSecondOrderMap f.toRingHom q z z' w w' e halgebra hmul t ∈ J := by
  apply (hJ _).2
  rw [universalSecondOrderMap_coords]
  exact f.ideal_comp (Ideal.mem_map_of_mem f.toRingHom
    ((universalSecondOrderIdeal_mem_iff t).1 ht))

/-- The comparison map sends the first universal element to the first chosen element. -/
private lemma universalSecondOrderMap_first
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (b b' : B)
    (hvar : f (DividedPowers.dividedPowerPolynomialVariable ℤ (0 : Fin 2)) =
      (e b).1) :
    universalSecondOrderMap f q (e b).2.1 (e b').2.1
      (e b).2.2 (e b').2.2 e halgebra hmul universalFirstElement = b := by
  apply e.injective
  rw [universalSecondOrderMap_coords]
  exact Prod.ext hvar (Prod.ext (universalModuleMap_fst ..) (universalCokernelModuleMap_fst ..))

/-- The comparison map sends the second universal element to the second chosen element. -/
private lemma universalSecondOrderMap_second
    {A : Type u} [CommRing A] (f : universalBase →+* A)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (b b' : B)
    (hvar : f (DividedPowers.dividedPowerPolynomialVariable ℤ (1 : Fin 2)) =
      (e b').1) :
    universalSecondOrderMap f q (e b).2.1 (e b').2.1
      (e b).2.2 (e b').2.2 e halgebra hmul universalSecondElement = b' := by
  apply e.injective
  rw [universalSecondOrderMap_coords]
  exact Prod.ext hvar (Prod.ext (universalModuleMap_snd ..) (universalCokernelModuleMap_snd ..))

/-- The comparison map commutes with the second-order divided power operation in degrees at least
two. -/
private lemma universalSecondOrderMap_dpow
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    (f : DividedPowers.DPMorphism universalBase.dividedPowers γ)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {n : ℕ} (hn : 2 ≤ n) {t : UniversalSecondOrderRing}
    (ht : t ∈ universalSecondOrderIdeal) :
    universalSecondOrderMap f.toRingHom q z z' w w' e halgebra hmul
      (universalSecondOrderDividedPowers.dpow n t) =
      secondOrderExtensionDpow I γ q e J n
        (universalSecondOrderMap f.toRingHom q z z' w w' e halgebra hmul t) := by
  let F := universalSecondOrderMap f.toRingHom q z z' w w' e halgebra hmul
  have hFt : F t ∈ J :=
    universalSecondOrderMap_mem I γ f q z z' w w' e halgebra hmul J hJ ht
  apply e.injective
  rw [secondOrderExtensionDpow_formula I γ q e J hn hFt,
    universalSecondOrderDividedPowers_formula hn ht]
  simp only [e.apply_symm_apply]
  rw [universalSecondOrderMap_coords, universalSecondOrderMap_coords]
  have ha : t.coords.1 ∈ universalBase.ideal :=
    (universalSecondOrderIdeal_mem_iff t).1 ht
  have hdp (k : ℕ) :
      f (universalBase.dividedPowers.dpow k t.coords.1) =
        γ.dpow k (f t.coords.1) :=
    (f.dpow_comp t.coords.1 ha).symm
  simp [UniversalSecondOrderRing.addEquiv, UniversalSecondOrderRing.equiv,
    hdp, universalModuleMap_smul,
    universalCokernelModuleMap_smul, universalCokernelModuleMap_q,
    map_add]

/-- The comparison map commutes with the second-order divided power operation in every degree. -/
private lemma universalSecondOrderMap_dpow_all
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    (f : DividedPowers.DPMorphism universalBase.dividedPowers γ)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) (z z' : M) (w w' : N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    (n : ℕ) {t : UniversalSecondOrderRing}
    (ht : t ∈ universalSecondOrderIdeal) :
    universalSecondOrderMap f.toRingHom q z z' w w' e halgebra hmul
      (universalSecondOrderDividedPowers.dpow n t) =
      secondOrderExtensionDpow I γ q e J n
        (universalSecondOrderMap f.toRingHom q z z' w w' e halgebra hmul t) := by
  let F := universalSecondOrderMap f.toRingHom q z z' w w' e halgebra hmul
  have hFt : F t ∈ J :=
    universalSecondOrderMap_mem I γ f q z z' w w' e halgebra hmul J hJ ht
  by_cases h0 : n = 0
  · subst n
    rw [universalSecondOrderDividedPowers.dpow_zero ht, map_one,
      secondOrderExtensionDpow_zero I γ q e halgebra J hJ hFt]
  · by_cases h1 : n = 1
    · subst n
      rw [universalSecondOrderDividedPowers.dpow_one ht,
        secondOrderExtensionDpow_one I γ q e J hFt]
    · exact universalSecondOrderMap_dpow I γ f q z z' w w' e
        halgebra hmul J hJ (by omega) ht

/-- Any two elements of the distinguished ideal of a second-order extension are the images of the
two universal elements under a comparison map compatible with the second-order divided power
operation. -/
private theorem exists_universalSecondOrderMap_pair
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {b b' : B} (hb : b ∈ J) (hb' : b' ∈ J) :
    ∃ F : UniversalSecondOrderRing →+* B,
      F universalFirstElement = b ∧ F universalSecondElement = b' ∧
      (∀ {t : UniversalSecondOrderRing}, t ∈ universalSecondOrderIdeal → F t ∈ J) ∧
      (∀ (n : ℕ) {t : UniversalSecondOrderRing},
        t ∈ universalSecondOrderIdeal →
          F (universalSecondOrderDividedPowers.dpow n t) =
            secondOrderExtensionDpow I γ q e J n (F t)) := by
  obtain ⟨f, hf₀, hf₁⟩ := exists_universalBaseDPMorphism I γ
    ((hJ b).1 hb) ((hJ b').1 hb')
  let F := universalSecondOrderMap f.toRingHom q (e b).2.1 (e b').2.1
    (e b).2.2 (e b').2.2 e halgebra hmul
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · exact universalSecondOrderMap_first f.toRingHom q e halgebra hmul b b' hf₀
  · exact universalSecondOrderMap_second f.toRingHom q e halgebra hmul b b' hf₁
  · intro t ht
    exact universalSecondOrderMap_mem I γ f q (e b).2.1 (e b').2.1
      (e b).2.2 (e b').2.2 e halgebra hmul J hJ ht
  · intro n t ht
    exact universalSecondOrderMap_dpow_all I γ f q (e b).2.1 (e b').2.1
      (e b).2.2 (e b').2.2 e halgebra hmul J hJ n ht

/-- Additivity of the second-order divided power operation, transported from the universal second-
order extension. -/
private lemma secondOrderExtensionDpow_add
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {n : ℕ} {b b' : B} (hb : b ∈ J) (hb' : b' ∈ J) :
    secondOrderExtensionDpow I γ q e J n (b + b') =
      (Finset.antidiagonal n).sum fun k =>
        secondOrderExtensionDpow I γ q e J k.1 b *
          secondOrderExtensionDpow I γ q e J k.2 b' := by
  obtain ⟨F, hF₀, hF₁, _, hnat⟩ :=
    exists_universalSecondOrderMap_pair I γ q e halgebra hmul J hJ hb hb'
  let u := universalFirstElement
  let v := universalSecondElement
  have hu : u ∈ universalSecondOrderIdeal := universalFirstElement_mem
  have hv : v ∈ universalSecondOrderIdeal := universalSecondElement_mem
  calc
    secondOrderExtensionDpow I γ q e J n (b + b') =
        F (universalSecondOrderDividedPowers.dpow n (u + v)) := by
      rw [hnat n (universalSecondOrderIdeal.add_mem hu hv), map_add, hF₀, hF₁]
    _ = F ((Finset.antidiagonal n).sum fun k =>
        universalSecondOrderDividedPowers.dpow k.1 u *
          universalSecondOrderDividedPowers.dpow k.2 v) := by
      rw [universalSecondOrderDividedPowers.dpow_add hu hv]
    _ = (Finset.antidiagonal n).sum fun k =>
        F (universalSecondOrderDividedPowers.dpow k.1 u) *
          F (universalSecondOrderDividedPowers.dpow k.2 v) := by
      simp [map_sum, map_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hnat k.1 hu, hnat k.2 hv, hF₀, hF₁]

/-- The product rule for the second-order divided power operation, transported from the universal
second-order extension. -/
private lemma secondOrderExtensionDpow_mul_dpow
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {m n : ℕ} {b : B} (hb : b ∈ J) :
    secondOrderExtensionDpow I γ q e J m b *
        secondOrderExtensionDpow I γ q e J n b =
      (Nat.choose (m + n) m : B) *
        secondOrderExtensionDpow I γ q e J (m + n) b := by
  obtain ⟨F, hF₀, _, _, hnat⟩ :=
    exists_universalSecondOrderMap_pair I γ q e halgebra hmul J hJ hb hb
  let u := universalFirstElement
  have hu : u ∈ universalSecondOrderIdeal := universalFirstElement_mem
  calc
    secondOrderExtensionDpow I γ q e J m b *
        secondOrderExtensionDpow I γ q e J n b =
        F (universalSecondOrderDividedPowers.dpow m u) *
          F (universalSecondOrderDividedPowers.dpow n u) := by
      rw [hnat m hu, hnat n hu, hF₀]
    _ = F (universalSecondOrderDividedPowers.dpow m u *
          universalSecondOrderDividedPowers.dpow n u) := by rw [map_mul]
    _ = F ((Nat.choose (m + n) m : UniversalSecondOrderRing) *
          universalSecondOrderDividedPowers.dpow (m + n) u) := by
      rw [universalSecondOrderDividedPowers.mul_dpow hu]
    _ = _ := by
      rw [map_mul, map_natCast, hnat (m + n) hu, hF₀]

/-- The composition rule for the second-order divided power operation, transported from the
universal second-order extension. -/
private lemma secondOrderExtensionDpow_comp
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I)
    {m n : ℕ} (hn : n ≠ 0) {b : B} (hb : b ∈ J) :
    secondOrderExtensionDpow I γ q e J m
        (secondOrderExtensionDpow I γ q e J n b) =
      (Nat.uniformBell m n : B) *
        secondOrderExtensionDpow I γ q e J (m * n) b := by
  obtain ⟨F, hF₀, _, _, hnat⟩ :=
    exists_universalSecondOrderMap_pair I γ q e halgebra hmul J hJ hb hb
  let u := universalFirstElement
  have hu : u ∈ universalSecondOrderIdeal := universalFirstElement_mem
  calc
    secondOrderExtensionDpow I γ q e J m
        (secondOrderExtensionDpow I γ q e J n b) =
        F (universalSecondOrderDividedPowers.dpow m
          (universalSecondOrderDividedPowers.dpow n u)) := by
      rw [hnat m (universalSecondOrderDividedPowers.dpow_mem hn hu), hnat n hu, hF₀]
    _ = F ((Nat.uniformBell m n : UniversalSecondOrderRing) *
          universalSecondOrderDividedPowers.dpow (m * n) u) := by
      rw [universalSecondOrderDividedPowers.dpow_comp hn hu]
    _ = _ := by
      rw [map_mul, map_natCast, hnat (m * n) hu, hF₀]

/-- The ideal of a second-order extension has divided powers given by the explicit
second-order formula, and the scalar inclusion is a divided-power morphism. -/
@[stacks 07HI, stacks 07HH "the first-order case, at N = 0 and q = 0"]
public theorem exists_dividedPowers_secondOrderExtension
    {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I)
    {M : Type v} [AddCommGroup M] [Module A M]
    {N : Type w} [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N)
    {B : Type x} [CommRing B] [Algebra A B]
    (e : B ≃+ A × (M × N))
    (halgebra : ∀ a : A, e (algebraMap A B a) = (a, (0, 0)))
    (hmul : ∀ b b' : B,
      e (b * b') =
        ((e b).1 * (e b').1,
          ((e b).1 • (e b').2.1 + (e b').1 • (e b).2.1,
            (e b).1 • (e b').2.2 + (e b').1 • (e b).2.2 +
              q (e b).2.1 (e b').2.1 + q (e b').2.1 (e b).2.1)))
    (J : Ideal B) (hJ : ∀ b : B, b ∈ J ↔ (e b).1 ∈ I) :
    ∃ δ : DividedPowers J,
      (∀ (n : ℕ) (b : B), 2 ≤ n → b ∈ J →
        δ.dpow n b = e.symm
          (γ.dpow n (e b).1,
            (γ.dpow (n - 1) (e b).1 • (e b).2.1,
              γ.dpow (n - 1) (e b).1 • (e b).2.2 +
                γ.dpow (n - 2) (e b).1 • q (e b).2.1 (e b).2.1))) ∧
      DividedPowers.IsDPMorphism γ δ (algebraMap A B) := by
  let δ : DividedPowers J := {
    dpow := secondOrderExtensionDpow I γ q e J
    dpow_null := by
      intro n b hb
      exact secondOrderExtensionDpow_null I γ q e J hb
    dpow_zero := by
      intro b hb
      exact secondOrderExtensionDpow_zero I γ q e halgebra J hJ hb
    dpow_one := by
      intro b hb
      exact secondOrderExtensionDpow_one I γ q e J hb
    dpow_mem := by
      intro n b hn hb
      exact secondOrderExtensionDpow_mem I γ q e J hJ hn hb
    dpow_add := by
      intro n b b' hb hb'
      exact secondOrderExtensionDpow_add I γ q e halgebra hmul J hJ hb hb'
    dpow_mul := by
      intro n a b hb
      by_cases hn0 : n = 0
      · subst n
        have hab : a * b ∈ J := J.mul_mem_left a hb
        rw [secondOrderExtensionDpow_zero I γ q e halgebra J hJ hab,
          secondOrderExtensionDpow_zero I γ q e halgebra J hJ hb]
        simp
      · by_cases hn1 : n = 1
        · subst n
          have hab : a * b ∈ J := J.mul_mem_left a hb
          rw [secondOrderExtensionDpow_one I γ q e J hab,
            secondOrderExtensionDpow_one I γ q e J hb]
          simp
        · exact secondOrderExtensionDpow_mul I γ q e halgebra hmul J hJ
            (by omega) a hb
    mul_dpow := by
      intro m n b hb
      exact secondOrderExtensionDpow_mul_dpow I γ q e halgebra hmul J hJ hb
    dpow_comp := by
      intro m n b hn hb
      exact secondOrderExtensionDpow_comp I γ q e halgebra hmul J hJ hn hb
  }
  refine ⟨δ, ?_, ?_⟩
  · intro n b hn hb
    exact secondOrderExtensionDpow_formula I γ q e J hn hb
  · refine ⟨?_, ?_⟩
    · apply Ideal.map_le_iff_le_comap.mpr
      intro a ha
      exact (hJ _).2 (by simpa only [halgebra] using ha)
    · intro n a ha
      have hma : algebraMap A B a ∈ J :=
        (hJ _).2 (by simpa only [halgebra] using ha)
      by_cases hn0 : n = 0
      · subst n
        change secondOrderExtensionDpow I γ q e J 0 (algebraMap A B a) =
          algebraMap A B (γ.dpow 0 a)
        rw [secondOrderExtensionDpow_zero I γ q e halgebra J hJ hma,
          γ.dpow_zero ha, map_one]
      · by_cases hn1 : n = 1
        · subst n
          change secondOrderExtensionDpow I γ q e J 1 (algebraMap A B a) =
            algebraMap A B (γ.dpow 1 a)
          rw [secondOrderExtensionDpow_one I γ q e J hma, γ.dpow_one ha]
        · change secondOrderExtensionDpow I γ q e J n (algebraMap A B a) =
            algebraMap A B (γ.dpow n a)
          apply e.injective
          rw [secondOrderExtensionDpow_formula I γ q e J (by omega) hma,
            e.apply_symm_apply, halgebra, halgebra]
          simp [map_zero]

end

end Crystalline

end
