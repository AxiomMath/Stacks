module

public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.BraidingSelf
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.IntPowerSystem
public import StacksFrontier.AlgebraicGeometry.Ample.AmpleCriteria
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced

/-!
# The coherent multiplication of the tensor powers of an invertible sheaf of modules

Let `O` be a sheaf of commutative rings on a site and `L` an invertible sheaf of `O`-modules, with
integer tensor powers `L^{⊗ n}`. This file supplies the **canonical multiplication isomorphisms**

  `L^{⊗ n} ⊗_O L^{⊗ m} ≅ L^{⊗ (n + m)}`,

for arbitrary integers `n` and `m`, normalized so that multiplication by `L^{⊗ 1}` is the defining
successor comparison, and **compatible with the unit, associativity and symmetry constraints of the
tensor product sheaf**, as asserted in Tag 01CU.

## Main definitions

* `Stacks.SheafOfModules.Invertible.SheafLocalizedMonoidal`: sheaves of modules with the monoidal
  structure obtained by localizing the monoidal structure on presheaves of modules along
  sheafification.
* `Stacks.SheafOfModules.Invertible.TensorPowerCoherence`: coherent multiplication data on the
  integer tensor powers of `L` — invertibility of every tensor power, the multiplication
  isomorphisms, the two unit laws, the normalization in degree `(n, 1)`, naturality of the
  successor comparison, and the associativity and commutativity constraints.
* `Stacks.SheafOfModules.Invertible.tensorPowerCoherence`: a choice of such data.

## Main results

* `Stacks.SheafOfModules.Invertible.powSuccIso_natural`: the successor comparison of the integer
  iterates of an autoequivalence is natural.
* `Stacks.SheafOfModules.Invertible.tensorPowerCoherence_exists`: **the coherent multiplication
  data exist.**

## Implementation notes

The conditions are verified in the symmetric monoidal structure
`Stacks.SheafOfModules.sheafTensorSymmetric`, whose structure maps are the unit, associativity and
symmetry constraints of the tensor product sheaf themselves. Invertibility is
`AlgebraicGeometry.SheafOfModules.IsInvertible` of Tag 01CS, written with `_root_` because inside
this namespace the bare name resolves to `Stacks.SheafOfModules.IsInvertible`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Localization
universe v u w
namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheaves of modules, carrying the monoidal structure obtained by localizing the monoidal
structure on presheaves of modules along sheafification. -/
abbrev SheafLocalizedMonoidal :=
  LocalizedMonoidal (Stacks.SheafOfModules.sheafifyFunctor O hO)
    (Stacks.SheafOfModules.localIso (J := J) O) (Stacks.SheafOfModules.sheafifyUnitIso O hO)

noncomputable example : Category (SheafLocalizedMonoidal O hO) := inferInstance
noncomputable example : MonoidalCategory (SheafLocalizedMonoidal O hO) := inferInstance
noncomputable example : SymmetricCategory (SheafLocalizedMonoidal O hO) := inferInstance

/-! ### Naturality of the successor comparison -/

private theorem powNatSuccIso_natural
    {A : Type u} [Category.{v} A] (e : A ≌ A) (n : ℕ) {M N : A} (f : M ⟶ N) :
    e.functor.map ((e.powNat n).functor.map f) ≫ (powNatSuccIso e n N).hom =
      (powNatSuccIso e n M).hom ≫ (e.powNat (n + 1)).functor.map f := by
  revert M N f
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro M N f
      cases n with
      | zero =>
          change e.functor.map f ≫ 𝟙 _ = 𝟙 _ ≫ e.functor.map f
          simp
      | succ n =>
          cases n with
          | zero =>
              change e.functor.map (e.functor.map f) ≫ 𝟙 _ =
                𝟙 _ ≫ e.functor.map (e.functor.map f)
              simp
          | succ k =>
              change e.functor.map ((e.powNat (k + 1)).functor.map (e.functor.map f)) ≫
                  (powNatSuccIso e (k + 1) (e.functor.obj N)).hom =
                (powNatSuccIso e (k + 1) (e.functor.obj M)).hom ≫
                  (e.powNat (k + 2)).functor.map (e.functor.map f)
              exact ih (k + 1) (by omega) (M := e.functor.obj M) (N := e.functor.obj N)
                (f := e.functor.map f)

private theorem powNatInverseSuccIso_natural
    {A : Type u} [Category.{v} A] (e : A ≌ A) (n : ℕ) {M N : A} (f : M ⟶ N) :
    e.functor.map ((e.symm.powNat (n + 1)).functor.map f) ≫
        (powNatInverseSuccIso e n N).hom =
      (powNatInverseSuccIso e n M).hom ≫ (e.symm.powNat n).functor.map f := by
  revert M N f
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro M N f
      cases n with
      | zero =>
          change (e.inverse ⋙ e.functor).map f ≫ e.counitIso.hom.app N =
            e.counitIso.hom.app M ≫ f
          exact e.counitIso.hom.naturality f
      | succ n =>
          cases n with
          | zero =>
              change e.functor.map (e.inverse.map (e.inverse.map f)) ≫
                  e.counitIso.hom.app (e.inverse.obj N) =
                e.counitIso.hom.app (e.inverse.obj M) ≫ e.inverse.map f
              exact e.counitIso.hom.naturality (e.inverse.map f)
          | succ k =>
              change e.functor.map ((e.symm.powNat (k + 2)).functor.map (e.inverse.map f)) ≫
                  (powNatInverseSuccIso e (k + 1) (e.inverse.obj N)).hom =
                (powNatInverseSuccIso e (k + 1) (e.inverse.obj M)).hom ≫
                  (e.symm.powNat (k + 1)).functor.map (e.inverse.map f)
              exact ih (k + 1) (by omega) (M := e.inverse.obj M) (N := e.inverse.obj N)
                (f := e.inverse.map f)

/-- The successor comparison for the integer iterates of an autoequivalence is natural in the
object the iterates are applied to. -/
theorem powSuccIso_natural
    {A : Type u} [Category.{v} A] (e : A ≌ A) (n : ℤ) {M N : A} (f : M ⟶ N) :
    e.functor.map ((e ^ n).functor.map f) ≫ (powSuccIso e n N).hom =
      (powSuccIso e n M).hom ≫ (e ^ (n + 1)).functor.map f := by
  cases n with
  | ofNat k => exact powNatSuccIso_natural e k f
  | negSucc k =>
      cases k with
      | zero =>
          change (e.inverse ⋙ e.functor).map f ≫ e.counitIso.hom.app N =
            e.counitIso.hom.app M ≫ f
          exact e.counitIso.hom.naturality f
      | succ k => exact powNatInverseSuccIso_natural e (k + 1) f

/-! ### The coherent multiplication data -/

/-- The reindexing isomorphism `tensorPower O hO L n ≅ tensorPower O hO L m` along an equality
`n = m` of exponents is the isomorphism `eqToIso` induced by that equality. -/
theorem tensorPowerReindex_eq_eqToIso
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] {n m : ℤ} (h : n = m) :
    tensorPowerReindex O hO L h = eqToIso (congrArg (tensorPower O hO L) h) := by
  cases h
  rfl

/-- **Coherent multiplication data on the integer tensor powers of `L`.** Multiplication of the
integer tensor powers of `L` adds the exponents, is normalized in degree `(n, 1)` by the defining
successor comparison, and respects the unit, associativity and symmetry constraints of the tensor
product sheaf. -/
structure TensorPowerCoherence
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] where
  /-- Every integer tensor power is again invertible. -/
  isInvertible (n : ℤ) :
    _root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO (tensorPower O hO L n)
  /-- Multiplication of tensor powers adds their exponents. -/
  mulIso (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ (O) (forget₂ CommRingCat RingCat) (hO)⟩).obj
          ((tensorPower O hO L n))).obj ((tensorPower O hO L m))) ≅
      tensorPower O hO L (n + m)
  /-- Left multiplication by the zeroth power is the left unit constraint. -/
  mul_zero_left (n : ℤ) :
    mulIso 0 n ≪≫ tensorPowerReindex O hO L (Int.zero_add n) =
      tensorProductLeftUnitor O hO (tensorPower O hO L n)
  /-- Right multiplication by the zeroth power is the right unit constraint. -/
  mul_zero_right (n : ℤ) :
    mulIso n 0 ≪≫ tensorPowerReindex O hO L (Int.add_zero n) =
      tensorProductRightUnitor O hO (tensorPower O hO L n)
  /-- Multiplication by the first power is one more iteration of right tensoring, after identifying
  the first power with `L`. -/
  mul_one_right (n : ℤ) :
    mulIso n 1 =
      tensorProductIso O hO (Iso.refl _) (tensorPowerOneIso O hO L) ≪≫
        tensorPowerSuccIso O hO L n
  /-- The successor comparison is natural in the sheaf the iterated autoequivalence acts on. -/
  pow_succ_natural (n : ℤ)
      {M N : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)} (f
        : M ⟶ N) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).map ((tensorPowerEquivalence O hO L n).functor.map f) ≫
        (powSuccIso ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
            L).asEquivalence n N).hom =
      (powSuccIso ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
          ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
            L).asEquivalence n M).hom ≫
        (tensorPowerEquivalence O hO L (n + 1)).functor.map f
  /-- Multiplication respects the associativity constraint of the tensor product sheaf. -/
  mul_assoc (n m k : ℤ) :
    tensorProductIso O hO (mulIso n m) (Iso.refl _) ≪≫ mulIso (n + m) k =
      tensorProductAssociator O hO
          (tensorPower O hO L n) (tensorPower O hO L m) (tensorPower O hO L k) ≪≫
        tensorProductIso O hO (Iso.refl _) (mulIso m k) ≪≫
        mulIso n (m + k) ≪≫
        tensorPowerReindex O hO L (Int.add_assoc n m k).symm
  /-- Multiplication respects the symmetry constraint of the tensor product sheaf. -/
  mul_comm (n m : ℤ) :
    mulIso n m =
      tensorProductBraiding O hO (tensorPower O hO L n) (tensorPower O hO L m) ≪≫
      mulIso m n ≪≫
      tensorPowerReindex O hO L (Int.add_comm m n)

/-- **Existence of a coherent multiplication on the tensor powers.** The integer tensor powers of
an invertible sheaf of modules `L` carry coherent multiplication data
`Stacks.SheafOfModules.Invertible.TensorPowerCoherence O hO L`. -/
@[stacks 01CU "canonical multiplication and coherence"]
theorem tensorPowerCoherence_exists
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    Nonempty (TensorPowerCoherence O hO L) := by
  let := sheafTensorMonoidal O hO
  let := sheafTensorSymmetric O hO
  let : (MonoidalCategory.tensorRight L).Full := by
    change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj L).Full
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence.fullyFaithfulFunctor.full
  let : (MonoidalCategory.tensorRight L).Faithful := by
    change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).Faithful
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        L).asEquivalence.fullyFaithfulFunctor.faithful
  let P := tensorPower O hO L
  let p : ∀ n : ℤ, P n ⊗ L ≅ P (n + 1) := tensorPowerSuccIso O hO L
  let μ := Stacks.Monoidal.IntPower.mul P L p (Iso.refl _)
  have h0 (n : ℤ) :
      (Stacks.Monoidal.IntPower.mulAt P L p (Iso.refl _) n 0 n (Int.add_zero n)).hom =
        (ρ_ (P n)).hom := by
    refine (Stacks.Monoidal.IntPower.mulAt_zero_hom P L p (Iso.refl _) n).trans ?_
    change P n ◁ 𝟙 (SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO)) ≫
      (ρ_ (P n)).hom = (ρ_ (P n)).hom
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have hl (n : ℤ) : Stacks.Monoidal.IntPower.mulAt P L p (Iso.refl _) 0 n n (Int.zero_add n) =
      whiskerRightIso (Iso.refl _) (P n) ≪≫ λ_ (P n) := by
    simp only [whiskerRightIso_refl, Iso.refl_trans]
    apply Stacks.Monoidal.IntPower.eq_leftUnitor_of_assoc
    have ha := Stacks.Monoidal.IntPower.mulAt_assoc P L p (Iso.refl _) n 0 0 0 n n
      (Int.add_zero 0) (Int.zero_add n) (Int.zero_add n)
    rw [h0 0] at ha
    exact ha
  refine ⟨{
    isInvertible := tensorPower_isInvertible O hO L
    mulIso := μ
    mul_zero_left := by
      intro n
      rw [tensorPowerReindex_eq_eqToIso]
      change Stacks.Monoidal.IntPower.mulAt P L p (Iso.refl _) 0 n n (Int.zero_add n) = λ_ (P n)
      simpa only [whiskerRightIso_refl, Iso.refl_trans] using hl n
    mul_zero_right := by
      intro n
      rw [tensorPowerReindex_eq_eqToIso]
      change Stacks.Monoidal.IntPower.mulAt P L p (Iso.refl _) n 0 n (Int.add_zero n) = ρ_ (P n)
      exact Iso.ext (h0 n)
    mul_one_right := by
      intro n
      have h := Stacks.Monoidal.IntPower.mulAt_step P L p (Iso.refl _) n 0 n (Int.add_zero n)
      rw [h0 n] at h
      change (ρ_ (P n)).hom ▷ L ≫ (p n).hom =
        (α_ (P n) (𝟙_ _) L).hom ≫ P n ◁ 𝟙 _ ≫
          (Stacks.Monoidal.IntPower.mulAt P L p (Iso.refl _) n 1 (n + 1) rfl).hom at h
      simp only [whiskerLeft_id, Stacks.Monoidal.IntPower.mulAt, Iso.trans_hom,
        eqToIso_refl, Iso.refl_hom, Category.comp_id] at h
      apply Iso.ext
      change (μ n 1).hom = P n ◁ (λ_ L).hom ≫ (p n).hom
      apply (cancel_epi (α_ (P n) (𝟙_ _) L).hom).mp
      calc
        _ = (ρ_ (P n)).hom ▷ L ≫ (p n).hom := h.symm
        _ = _ := by
          simpa only [Category.assoc] using
            (congrArg (fun f => f ≫ (p n).hom) (triangle (P n) L)).symm
    pow_succ_natural := by
      intro n M N f
      exact powSuccIso_natural ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
        ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
          L).asEquivalence n f
    mul_assoc := by
      intro n m k
      rw [tensorPowerReindex_eq_eqToIso]
      apply Iso.ext
      change (μ n m).hom ▷ P k ≫ (μ (n + m) k).hom =
        (α_ (P n) (P m) (P k)).hom ≫ P n ◁ (μ m k).hom ≫
          (μ n (m + k)).hom ≫ (eqToIso (congrArg P (Int.add_assoc n m k).symm)).hom
      have ha := Stacks.Monoidal.IntPower.mulAt_assoc P L p (Iso.refl _) k n m (n + m) (m + k)
        ((n + m) + k) rfl rfl rfl
      simpa only [Stacks.Monoidal.IntPower.mulAt, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
        Category.comp_id, Category.assoc] using ha
    mul_comm := ?_ }⟩
  let : _root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO (P 1) :=
    tensorPower_isInvertible O hO L 1
  let : (MonoidalCategory.tensorRight (P 1)).Faithful := by
    change ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (P 1)).Faithful
    exact ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp _ O (forget₂ CommRingCat RingCat) hO⟩).flip.obj
        (P 1)).asEquivalence.fullyFaithfulFunctor.faithful
  have hb : (β_ (P 1) (P 1)) = Iso.refl _ := tensorProductBraiding_self O hO (P 1)
  intro n m
  rw [tensorPowerReindex_eq_eqToIso]
  apply Iso.ext
  change (μ n m).hom = (β_ (P n) (P m)).hom ≫ (μ m n).hom ≫
    (eqToIso (congrArg P (Int.add_comm m n))).hom
  have hc := Stacks.Monoidal.IntPower.mulAt_comm P L p (Iso.refl _) hl hb n m (n + m) rfl
  simpa only [Stacks.Monoidal.IntPower.mulAt, Iso.trans_hom, eqToIso_refl, Iso.refl_hom,
    Category.comp_id, Category.assoc] using hc

/-- A choice of coherent multiplication data on the integer tensor powers. -/
noncomputable def tensorPowerCoherence
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [_root_.AlgebraicGeometry.SheafOfModules.IsInvertible O hO L] :
    TensorPowerCoherence O hO L :=
  Classical.choice (tensorPowerCoherence_exists O hO L)

end Stacks.SheafOfModules.Invertible

end
