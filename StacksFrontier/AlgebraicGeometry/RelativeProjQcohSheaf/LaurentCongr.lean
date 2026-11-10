module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

/-!
# Transporting the Laurent algebra along an isomorphism of invertible modules

Let `T` be a scheme, let `L` and `L'` be invertible `𝒪_T`-modules and let `e : L ≅ L'` be an
isomorphism. This file constructs the comparison `L^{⊗ n} ≅ L'^{⊗ n}` for every integer `n`,
between the tensor powers of Tag 01CU in the spelling the Laurent algebra `⨁_{n ∈ ℤ} L^{⊗ n}` of
Section 01NS is graded by, together with its successor law, and proves that it is compatible with
the multiplication of the Laurent algebra in every integral bidegree.

## Main definitions

* `CongrCmp`: the type of a comparison in a single degree, `L^{⊗ n} ≅ L'^{⊗ n}`.
* `congrClimb`, `congrSucc` and `congrPred`: the splitting of the top tensor factor and the two
  steps, raising and lowering the degree by one.
* `congrIso`: the comparison `L^{⊗ n} ≅ L'^{⊗ n}` for every integer `n`.
* `MulCompat`: the multiplicativity square in one bidegree.

## Main results

* `congrSucc_congrPred` and `congrPred_congrSucc`: the two steps are mutually inverse.
* `congrIso_zero`, `congrIso_succ` and `congrIso_pred`: the degree-zero value and the successor law
  in every integral degree.
* `congrIso_succIso`: the successor law read as a commuting square against the successor comparison
  of Tag 01CU.
* `congrIso_one` and `congrIso_oneIso`: the value in degree one, and its compatibility with the
  identification `L^{⊗ 1} = L` of Tag 01CU.
* `congrIso_reindex` and `congrIso_reindex_inv`: compatibility with reindexing along an equality of
  exponents.
* `mulCompat_zero` and `mulCompat_one`: the square in the bidegrees `(n, 0)` and `(n, 1)`, for
  every integer `n`.
* `mulCompat_succ` and `mulCompat_of_succ`: the inductive step, upwards and downwards.
* `congrIso_mul`: the comparison is multiplicative in every integral bidegree.

## Implementation notes

`congrIso` is defined by structural recursion on `ℤ`: the nonnegative half by the successor step
`congrSucc`, the negative half by the cancellation step `congrPred`, since tensoring on the right
by `L'` is fully faithful.

`Stacks.SheafOfModules.TensorPower.tensorPowerCongr` is another isomorphism `L^{⊗ n} ≅ L'^{⊗ n}`
induced by `e`. It satisfies no successor law, and the two are only known to agree in degrees `0`
and `1`.

The degree-zero pieces `(laurent L).piece 0`, `(laurent L').piece 0` and `𝟙_` are equal by
definition but not syntactically, so an identity morphism at one of them is invisible to a `rw`
whose pattern names another. `congrIso_one` crosses between them by definitional unfolding, and
`mulCompat_zero` is derived from `mulCompat_one` so that no such identity morphism is written.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01NU](https://stacks.math.columbia.edu/tag/01NU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T : Scheme.{u}}
  {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- A comparison in a single degree: an isomorphism `L^{⊗ n} ≅ L'^{⊗ n}` between the degree-`n`
pieces of the Laurent algebras of `L` and of `L'`.

The isomorphism `_e` does not occur in the body; it is an argument because it determines the
implicit modules `L` and `L'`. -/
abbrev CongrCmp (_e : L ≅ L') (n : ℤ) : Type u :=
  (laurent L).piece n ≅ (laurent L').piece n

variable (e : L ≅ L')

/-- Splitting off the top factor and exchanging it: `L^{⊗ (n+1)} ≅ L^{⊗ n} ⊗ L'`, the successor
comparison of Tag 01CU read backwards followed by `e` in the second factor. -/
def congrClimb (n : ℤ) :
    (laurent L).piece (n + 1) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
            (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').obj
        ((laurent L).piece n) :=
  (succIso L n).symm ≪≫ MonoidalCategory.whiskerLeftIso ((laurent L).piece n) e

/-- Raising the degree by one: split the extra factor off by `congrClimb`, apply the comparison at
`n` in the first factor, and reassemble by the successor comparison on the `L'` side. -/
def congrSucc (n : ℤ) (φ : CongrCmp e n) : CongrCmp e (n + 1) :=
  congrClimb e n ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
          (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').mapIso φ ≪≫
    succIso L' n

/-- Lowering the degree by one: the comparison at `n` whose tensor product with `L'` is, by Tag
01CU, the given comparison at `n + 1`. It exists and is unique because tensoring on the right by
`L'` is an equivalence, hence fully faithful. -/
def congrPred (n : ℤ) (ψ : CongrCmp e (n + 1)) : CongrCmp e n :=
  haveI : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
        (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _
  ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
        (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').preimageIso
    ((congrClimb e n).symm ≪≫ ψ ≪≫ (succIso L' n).symm)

/-- Tensoring the lowering step by `L'` gives back
`(congrClimb e n).symm ≪≫ ψ ≪≫ (succIso L' n).symm`. -/
theorem mapIso_congrPred (n : ℤ) (ψ : CongrCmp e (n + 1)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
          (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').mapIso
        (congrPred e n ψ) =
      (congrClimb e n).symm ≪≫ ψ ≪≫ (succIso L' n).symm :=
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
        (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _
  Iso.ext (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
      (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').map_preimage _)

/-- Lowering and then raising the degree is the identity. -/
@[simp] theorem congrSucc_congrPred (n : ℤ) (ψ : CongrCmp e (n + 1)) :
    congrSucc e n (congrPred e n ψ) = ψ := by
  simp only [congrSucc, mapIso_congrPred]
  exact iso_conj_left _ _ _

/-- Whiskering on the right by an invertible module reflects equality of morphisms. -/
private theorem eq_of_whiskerRight_eq
    {M X Y : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M]
    {f g : X ⟶ Y} (h : f ▷ M = g ▷ M) : f = g := by
  have : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
        (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj M).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _
  exact this.faithful.map_injective ((tensorRight_map (X := T) f M).trans
    (h.trans (tensorRight_map (X := T) g M).symm))

/-- Raising and then lowering the degree is the identity. -/
@[simp] theorem congrPred_congrSucc (n : ℤ) (φ : CongrCmp e n) :
    congrPred e n (congrSucc e n φ) = φ := by
  refine Iso.ext (eq_of_whiskerRight_eq (M := L') ?_)
  rw [← tensorRight_map (X := T), ← tensorRight_map (X := T)]
  refine (congrArg Iso.hom (mapIso_congrPred e n (congrSucc e n φ))).trans ?_
  simp only [congrSucc]
  exact congrArg Iso.hom (iso_conj_right _ _ _)

/-- The comparison in degree `0`: both sides are the structure sheaf, and the comparison is the
identity. -/
def congrZero : CongrCmp e 0 :=
  Iso.refl _

/-- The comparison in the nonnegative degrees, by recursion. -/
def congrIsoNat : (j : ℕ) → CongrCmp e (j : ℤ)
  | 0 => congrZero e
  | j + 1 => congrSucc e (j : ℤ) (congrIsoNat j)

/-- The comparison in the negative degrees, by recursion downwards from degree `0`. -/
def congrIsoNeg : (j : ℕ) → CongrCmp e (Int.negSucc j)
  | 0 => congrPred e (Int.negSucc 0) (congrZero e)
  | j + 1 => congrPred e (Int.negSucc (j + 1)) (congrIsoNeg j)

/-- The comparison `L^{⊗ n} ≅ L'^{⊗ n}` of the integral tensor powers of Tag 01CU induced by an
isomorphism `e : L ≅ L'`, for every integer `n`, in the spelling the Laurent algebra of Section
01NS is graded by. -/
def congrIso : (n : ℤ) → CongrCmp e n
  | Int.ofNat j => congrIsoNat e j
  | Int.negSucc j => congrIsoNeg e j

/-- The comparison in a nonnegative degree is given by `congrIsoNat`. -/
@[simp] theorem congrIso_ofNat (j : ℕ) : congrIso e (j : ℤ) = congrIsoNat e j := rfl

/-- The comparison in a negative degree is given by `congrIsoNeg`. -/
@[simp] theorem congrIso_negSucc (j : ℕ) :
    congrIso e (Int.negSucc j) = congrIsoNeg e j := rfl

/-- In degree `0` the comparison is the identity. -/
theorem congrIso_zero : congrIso e 0 = Iso.refl _ := rfl

/-- The successor law: the comparison at `n + 1` is the comparison at `n` raised by `congrSucc`. -/
theorem congrIso_succ (n : ℤ) : congrIso e (n + 1) = congrSucc e n (congrIso e n) := by
  match n with
  | Int.ofNat j => rfl
  | Int.negSucc 0 => exact (congrSucc_congrPred e (Int.negSucc 0) (congrZero e)).symm
  | Int.negSucc (j + 1) =>
      exact (congrSucc_congrPred e (Int.negSucc (j + 1)) (congrIsoNeg e j)).symm

/-- The predecessor law: the comparison at `n` is the comparison at `n + 1` lowered by `congrPred`.
-/
theorem congrIso_pred (n : ℤ) : congrIso e n = congrPred e n (congrIso e (n + 1)) := by
  rw [congrIso_succ, congrPred_congrSucc]

/-! ### The successor law as a commuting square, and degree one -/

/-- The comparison is compatible with the successor comparison of Tag 01CU. -/
theorem congrIso_succIso (n : ℤ) :
    (succIso L n).hom ≫ (congrIso e (n + 1)).hom =
      ((laurent L).piece n ◁ e.hom) ≫ ((congrIso e n).hom ▷ L') ≫ (succIso L' n).hom := by
  rw [congrIso_succ]
  change (succIso L n).hom ≫
      (((succIso L n).inv ≫ ((laurent L).piece n ◁ e.hom)) ≫
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
                (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L').map
            (congrIso e n).hom ≫ (succIso L' n).hom)) = _
  refine Eq.trans ?_ (congrArg
    (fun z => ((laurent L).piece n ◁ e.hom) ≫ z ≫ (succIso L' n).hom)
    (bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T)
      (congrIso e n).hom L').symm).symm
  simp only [Category.assoc]
  exact Iso.hom_inv_id_assoc (succIso L n) _

/-- In degree one the comparison is `e` whiskered by the unit object. -/
theorem congrIso_one :
    (congrIso e 1).hom =
      𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) ◁ e.hom := by
  have hsucc : (succIso L 0).hom ≫ (congrIso e (0 + 1)).hom = (congrIso e 1).hom :=
    Category.id_comp _
  have hw : (congrIso e 0).hom ▷ L' = 𝟙 ((laurent L).piece 0 ⊗ L') :=
    MonoidalCategory.id_whiskerRight _ L'
  have hb : 𝟙 ((laurent L).piece 0 ⊗ L') ≫ (succIso L' 0).hom = (succIso L' 0).hom :=
    Category.id_comp _
  have hc : ((laurent L).piece 0 ◁ e.hom) ≫ (succIso L' 0).hom =
      𝟙_ (SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) ◁ e.hom :=
    Category.comp_id _
  have h := congrIso_succIso e 0
  rw [hsucc] at h
  refine h.trans (Eq.trans (congrArg (fun z => ((laurent L).piece 0 ◁ e.hom) ≫ z)
    (Eq.trans (congrArg (fun w => w ≫ (succIso L' 0).hom) hw) hb)) hc)

/-- The comparison is compatible with the identification `L^{⊗ 1} = L` of Tag 01CU. -/
theorem congrIso_oneIso :
    (oneIsoL L).hom ≫ e.hom = (congrIso e 1).hom ≫ (oneIsoL L').hom := by
  rw [congrIso_one, oneIsoL_eq_leftUnitor, oneIsoL_eq_leftUnitor]
  exact (MonoidalCategory.leftUnitor_naturality e.hom).symm

/-- The comparison is compatible with reindexing along an equality of exponents. -/
theorem congrIso_reindex {n m : ℤ} (h : n = m) :
    (reindexIso L h).hom ≫ (congrIso e m).hom =
      (congrIso e n).hom ≫ (reindexIso L' h).hom := by
  subst h
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

/-- The comparison is compatible with reindexing, read backwards. -/
theorem congrIso_reindex_inv {n m : ℤ} (h : n = m) :
    (reindexIso L h).inv ≫ (congrIso e n).hom =
      (congrIso e m).hom ≫ (reindexIso L' h).inv := by
  subst h
  change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

/-! ### Multiplicativity of the comparison -/

/-- The multiplicativity square of the comparison in bidegree `(n, m)`: multiplying in the Laurent
algebra of `L` and then comparing in degree `n + m` agrees with comparing in degrees `n` and `m`
and then multiplying in the Laurent algebra of `L'`. -/
abbrev MulCompat (n m : ℤ) : Prop :=
  (mulIso L n m).hom ≫ (congrIso e (n + m)).hom =
    ((congrIso e n).hom ⊗ₘ (congrIso e m).hom) ≫ (mulIso L' n m).hom

/-- Multiplicativity in bidegree `(n, 1)`, for every integer `n`. -/
theorem mulCompat_one (n : ℤ) : MulCompat e n 1 := by
  change (mulIso L n 1).hom ≫ _ = _
  rw [mulIso_one_right, mulIso_one_right, Category.assoc, congrIso_succIso,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, congrIso_oneIso]
  simp only [tensorHom_def', Category.assoc, MonoidalCategory.whiskerLeft_comp]
  rw [whisker_exchange_assoc (congrIso e n).hom (oneIsoL L').hom]

/-- The isomorphism `L'^{⊗ (n + m)} ⊗ L^{⊗ 1} ≅ L'^{⊗ (n + (m + 1))}`: the comparison in degree one
on the second factor, followed by multiplication by the first power on the `L'` side and
reindexing. -/
def mulTail (n m : ℤ) :
    (laurent L').piece (n + m) ⊗ (laurent L).piece 1 ≅
      (laurent L').piece (n + (m + 1)) :=
  MonoidalCategory.whiskerLeftIso _ (congrIso e 1) ≪≫
    (mulIso L' (n + m) 1 ≪≫ (reindexIso L' (Int.add_assoc n m 1).symm).symm)

/-- The isomorphism `(L^{⊗ n} ⊗ L^{⊗ m}) ⊗ L^{⊗ 1} ≅ L^{⊗ n} ⊗ L^{⊗ (m + 1)}`: the associator
followed by multiplication in bidegree `(m, 1)` on the second factor. -/
def mulHead (n m : ℤ) :
    ((laurent L).piece n ⊗ (laurent L).piece m) ⊗ (laurent L).piece 1 ≅
      (laurent L).piece n ⊗ (laurent L).piece (m + 1) :=
  α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1) ≪≫
    MonoidalCategory.whiskerLeftIso ((laurent L).piece n) (mulIso L m 1)

/-- The forward morphism of `mulHead` is the associator followed by multiplication in bidegree
`(m, 1)` on the second factor. -/
theorem mulHead_hom (n m : ℤ) :
    (mulHead (L := L) n m).hom =
      (α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1)).hom ≫
        ((laurent L).piece n ◁ (mulIso L m 1).hom) :=
  rfl

/-- The left-hand side of the bidegree-`(n, m + 1)` multiplicativity square, precomposed with
`mulHead`, is the left-hand side of the bidegree-`(n, m)` square whiskered by `L^{⊗ 1}`, followed
by `mulTail`. -/
theorem mulCompat_lhs (n m : ℤ) :
    (α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1)).hom ≫
        ((laurent L).piece n ◁ (mulIso L m 1).hom) ≫
          ((mulIso L n (m + 1)).hom ≫ (congrIso e (n + (m + 1))).hom) =
      (((mulIso L n m).hom ≫ (congrIso e (n + m)).hom) ▷ (laurent L).piece 1) ≫
        (mulTail e n m).hom := by
  rw [← Category.assoc, ← Category.assoc, mulIso_assoc_one]
  simp only [Category.assoc]
  rw [congrIso_reindex_inv, reassoc_of% (mulCompat_one e (n + m))]
  simp only [mulTail, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.whiskerLeftIso_hom,
    Category.assoc, tensorHom_def, MonoidalCategory.comp_whiskerRight]

/-- The right-hand side of the bidegree-`(n, m + 1)` multiplicativity square, precomposed with
`mulHead`, is the right-hand side of the bidegree-`(n, m)` square whiskered by `L^{⊗ 1}`, followed
by `mulTail`. -/
theorem mulCompat_rhs (n m : ℤ) :
    (α_ ((laurent L).piece n) ((laurent L).piece m) ((laurent L).piece 1)).hom ≫
        ((laurent L).piece n ◁ (mulIso L m 1).hom) ≫
          (((congrIso e n).hom ⊗ₘ (congrIso e (m + 1)).hom) ≫
            (mulIso L' n (m + 1)).hom) =
      ((((congrIso e n).hom ⊗ₘ (congrIso e m).hom) ≫ (mulIso L' n m).hom) ▷
          (laurent L).piece 1) ≫
        (mulTail e n m).hom := by
  rw [tensorHom_def' (congrIso e n).hom (congrIso e (m + 1)).hom]
  simp only [Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, mulCompat_one e m]
  simp only [mulTail, Iso.trans_hom, Iso.symm_hom, MonoidalCategory.whiskerLeftIso_hom,
    MonoidalCategory.comp_whiskerRight, Category.assoc]
  exact monoidalStep (congrIso e n).hom (congrIso e m).hom (congrIso e 1).hom
    (mulIso L' m 1).hom (mulIso L' n m).hom (mulIso L' n (m + 1)).hom
    (mulIso L' (n + m) 1).hom (reindexIso L' (Int.add_assoc n m 1).symm).inv
    (mulIso_assoc_one L' n m)

/-- Multiplicativity in bidegree `(n, m)` implies multiplicativity in bidegree `(n, m + 1)`. -/
theorem mulCompat_succ {n m : ℤ} (h : MulCompat e n m) : MulCompat e n (m + 1) := by
  refine (Iso.cancel_iso_hom_left (mulHead (L := L) n m) _ _).mp ?_
  rw [mulHead_hom]
  simp only [Category.assoc]
  rw [mulCompat_lhs, mulCompat_rhs, h]

/-- Multiplicativity in bidegree `(n, m + 1)` implies multiplicativity in bidegree `(n, m)`. -/
theorem mulCompat_of_succ {n m : ℤ} (h : MulCompat e n (m + 1)) : MulCompat e n m := by
  have h2 := congrArg (fun z => (mulHead (L := L) n m).hom ≫ z) h
  rw [mulHead_hom] at h2
  simp only [Category.assoc] at h2
  rw [mulCompat_lhs, mulCompat_rhs] at h2
  have h4 := (Iso.cancel_iso_hom_right _ _ (mulTail e n m)).mp h2
  have : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T)
      ((laurent L).piece 1) :=
    Stacks.SheafOfModules.TensorPower.isInvertible_tensorPower T.toRingedSpace.presheaf
      (isSheafStruct T) L 1
  exact eq_of_whiskerRight_eq (M := (laurent L).piece 1) h4

/-- Multiplicativity in bidegree `(n, 0)`, for every integer `n`. -/
theorem mulCompat_zero (n : ℤ) : MulCompat e n 0 :=
  mulCompat_of_succ e (mulCompat_one e n)

/-- The comparison `congrIso e` induced by an isomorphism `e : L ≅ L'` is multiplicative in every
integral bidegree: it intertwines the multiplication of Tag 01CU on the integral tensor powers of
`L` with the one on those of `L'`. -/
theorem congrIso_mul (n m : ℤ) : MulCompat e n m := by
  induction m using Int.induction_on with
  | zero => exact mulCompat_zero e n
  | succ i ih => exact mulCompat_succ e ih
  | pred i ih =>
      refine mulCompat_of_succ e (n := n) (m := -(i : ℤ) - 1) ?_
      rwa [sub_add_cancel]

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

end
