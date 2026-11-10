module

public import StacksFrontier.AlgebraicGeometry.Constructions.CoherentMulSections
public import StacksFrontier.AlgebraicGeometry.TensorPowerDivision.Integer
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalRightUnitorCompare
public import StacksFrontier.AlgebraicGeometry.TensorPowerAssoc.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.TwistRemarkAlgebra

/-!
# The comparison of the iterated tensor powers with Tag 01CU's powers is multiplicative

On a ringed site, an invertible module `𝓛` has two families of powers: the iterated tensor powers
`L ^⊗ m` (`Stacks.TensorPowers.natTensorPow`, for the monoidal structure obtained by localizing at
the sheafification) and the integer powers `𝓛^{⊗ n}` of Stacks Tag 01CU
(`Stacks.SheafOfModules.Invertible.tensorPower`, for `Stacks.SheafOfModules.monoidalCategory`).
The two monoidal structures share their tensor product and associator and differ in their unitors.
This file shows that the comparison `tensorPowerCompare : L ^⊗ m ≅ 𝓛^{⊗ m}` carries the addition
of the iterated powers to Tag 01CU's multiplication `powMulIso`, and builds from it the
isomorphism `twistPowBeta : L ^⊗ e ≅ 𝓛^{⊗ n} ⊙ k` for `e = n + k`, which the obvious
identification `M(n) = Γ_*(X, 𝓛, 𝓕 ⊗ 𝓛^{⊗ n})` of Stacks Tag 01QK uses for a negative `n`.

## Main definitions

* `Stacks.SheafOfModules.Invertible.powMulIso`: Tag 01CU's `𝓛^{⊗ n} ⊗ 𝓛^{⊗ m} ≅ 𝓛^{⊗ (n + m)}`.
* `Stacks.SheafOfModules.Invertible.twistPowCompare`: `𝓛^{⊗ n} ⊙ m ⟶ 𝓛^{⊗ (n + m)}`.
* `Stacks.SheafOfModules.Invertible.twistPowBeta`: `L ^⊗ e ≅ 𝓛^{⊗ n} ⊙ k`.

## Main results

* `Stacks.SheafOfModules.Invertible.tensorPowerCompare_powAdd`: the comparison is multiplicative.
* `Stacks.SheafOfModules.Invertible.powMulIso_assoc`: Tag 01CU's multiplication is associative.
* `Stacks.SheafOfModules.Invertible.eqToHom_twistPowCompare`: compatibility with adding copies of
  `𝓛`.
* `Stacks.SheafOfModules.Invertible.smulRight_twistPowCompare`: multiplying by a global section
  through the comparison is Tag 01CU's multiplication.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorSheafification (structureSheaf structureRingPresheaf)
open Stacks.TensorPowers (natTensorPow)
open AlgebraicGeometry.SheafOfModules (IsInvertible unitIso)
open Stacks.GradedSections (powSections powAdd)

universe v u w

namespace Stacks.SheafOfModules.Invertible

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The two localized monoidal structures have the same right unitor up to the comparison of
their units**, on an arbitrary site. -/
theorem rightUnitor_sheafOfModulesMonoidal_hom'
    (M : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (@MonoidalCategoryStruct.rightUnitor _ _
      (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪).toMonoidalCategoryStruct M).hom
      = M ◁ (unitIso 𝒪 h𝒪).inv ≫ (ρ_ M).hom := by
  have key : ∀ {A B D : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (a : A ⟶ B)
      (i : B ⟶ B) (_ : i = 𝟙 B) (r : B ⟶ D), a ≫ r = a ≫ i ≫ r := by
    intro A B D a i hi r
    rw [hi, Category.id_comp]
  refine key (M ◁ (unitIso 𝒪 h𝒪).inv) (M ◁ 𝟙 _) ?_ _
  exact MonoidalCategory.whiskerLeft_id M _

variable (L : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The comparison of the two localized monoidal structures carries the multiplication of the
iterated tensor powers to itself.** -/
theorem natTensorPowUnitShift_powAdd (a : ℕ) : ∀ b : ℕ,
    ((natTensorPowUnitShift 𝒪 h𝒪 L a).hom ⊗ₘ (natTensorPowUnitShift 𝒪 h𝒪 L b).hom) ≫
        @powAdd _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L a b =
      powAdd L a b ≫ (natTensorPowUnitShift 𝒪 h𝒪 L (a + b)).hom
  | 0 => by
      change ((natTensorPowUnitShift 𝒪 h𝒪 L a).hom ⊗ₘ (unitIso 𝒪 h𝒪).hom) ≫
          (@MonoidalCategoryStruct.rightUnitor _ _
            (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪).toMonoidalCategoryStruct _).hom =
        (ρ_ _).hom ≫ (natTensorPowUnitShift 𝒪 h𝒪 L a).hom
      rw [rightUnitor_sheafOfModulesMonoidal_hom', tensorHom_def, Category.assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id,
        MonoidalCategory.whiskerLeft_id, Category.id_comp]
      exact rightUnitor_naturality _
  | b + 1 => by
      change ((natTensorPowUnitShift 𝒪 h𝒪 L a).hom ⊗ₘ
          ((natTensorPowUnitShift 𝒪 h𝒪 L b).hom ▷ L)) ≫
          ((α_ _ _ _).inv ≫
            (@powAdd _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L a b ▷ L)) =
        ((α_ _ _ _).inv ≫ (powAdd L a b ▷ L)) ≫
          ((natTensorPowUnitShift 𝒪 h𝒪 L (a + b)).hom ▷ L)
      have key : ((natTensorPowUnitShift 𝒪 h𝒪 L a).hom ⊗ₘ
          ((natTensorPowUnitShift 𝒪 h𝒪 L b).hom ▷ L)) ≫ (α_ _ _ _).inv =
          (α_ _ _ _).inv ≫ (((natTensorPowUnitShift 𝒪 h𝒪 L a).hom ⊗ₘ
            (natTensorPowUnitShift 𝒪 h𝒪 L b).hom) ▷ L) := by
        rw [← tensorHom_id ((natTensorPowUnitShift 𝒪 h𝒪 L b).hom) L, associator_inv_naturality,
          tensorHom_id]
      refine ((reassoc_of% key) _).trans ?_
      refine (congrArg (fun φ => (α_ _ _ _).inv ≫ φ)
        (MonoidalCategory.comp_whiskerRight _ _ L).symm).trans ?_
      refine (congrArg (fun φ => (α_ _ _ _).inv ≫ φ ▷ L)
        (natTensorPowUnitShift_powAdd a b)).trans ?_
      exact (congrArg (fun φ => (α_ _ _ _).inv ≫ φ)
        (MonoidalCategory.comp_whiskerRight _ _ L)).trans (Category.assoc _ _ _).symm

variable [IsInvertible 𝒪 h𝒪 L]

/-- **The coherent multiplication of Tag 01CU's powers**, typed with the tensor product of
`Stacks.SheafInternalHom.monoidalCategory`, the structure the iterated powers are read in. It is
`Stacks.SheafOfModules.TensorPower.monoidalMulIso`; the two localized structures have the same
tensor product. -/
def powMulIso (n m : ℤ) :
    tensorPower 𝒪 h𝒪 L n ⊗ tensorPower 𝒪 h𝒪 L m ≅ tensorPower 𝒪 h𝒪 L (n + m) := by
  exact Stacks.SheafOfModules.TensorPower.monoidalMulIso 𝒪 h𝒪 L n m

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The comparison with Tag 01CU's powers is multiplicative**: it carries the multiplication of
the iterated tensor powers to the coherent multiplication of the integer powers. -/
theorem tensorPowerCompare_powAdd (a b : ℕ) :
    ((tensorPowerCompare 𝒪 h𝒪 L a).hom ⊗ₘ (tensorPowerCompare 𝒪 h𝒪 L b).hom) ≫
        (powMulIso 𝒪 h𝒪 L a b).hom =
      powAdd L a b ≫ (tensorPowerCompare 𝒪 h𝒪 L (a + b)).hom := by
  have h1 := natTensorPowCompare_mul 𝒪 h𝒪 L a b
  rw [tensorPowerMulIso_hom,
    @Stacks.GradedSections.powAddIso_hom _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪)] at h1
  have h2 : ((natTensorPowCompare 𝒪 h𝒪 L a).hom ⊗ₘ (natTensorPowCompare 𝒪 h𝒪 L b).hom) ≫
      (powMulIso 𝒪 h𝒪 L a b).hom =
      @powAdd _ _ (Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪) L a b ≫
        (natTensorPowCompare 𝒪 h𝒪 L (a + b)).hom := h1
  change (((natTensorPowUnitShift 𝒪 h𝒪 L a).hom ≫ (natTensorPowCompare 𝒪 h𝒪 L a).hom) ⊗ₘ
      ((natTensorPowUnitShift 𝒪 h𝒪 L b).hom ≫ (natTensorPowCompare 𝒪 h𝒪 L b).hom)) ≫
        (powMulIso 𝒪 h𝒪 L a b).hom =
      powAdd L a b ≫ (natTensorPowUnitShift 𝒪 h𝒪 L (a + b)).hom ≫
        (natTensorPowCompare 𝒪 h𝒪 L (a + b)).hom
  rw [← tensorHom_comp_tensorHom, Category.assoc, h2]
  exact ((reassoc_of% (natTensorPowUnitShift_powAdd 𝒪 h𝒪 L a b)) _).trans
    (Category.assoc _ _ _).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- `tensorPowerCompare_powAdd`, read from right to left, with the degree of the target written as
the natural number `a + b`. -/
theorem powAdd_tensorPowerCompare (a b : ℕ) :
    powAdd L a b ≫ (tensorPowerCompare 𝒪 h𝒪 L (a + b)).hom =
      ((tensorPowerCompare 𝒪 h𝒪 L a).hom ⊗ₘ (tensorPowerCompare 𝒪 h𝒪 L b).hom) ≫
        (powMulIso 𝒪 h𝒪 L a b).hom ≫
          eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (Nat.cast_add a b).symm) := by
  rw [show eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (Nat.cast_add a b).symm) =
    𝟙 (tensorPower 𝒪 h𝒪 L ((a : ℤ) + (b : ℤ))) from eqToHom_refl _ _, Category.comp_id]
  exact (tensorPowerCompare_powAdd 𝒪 h𝒪 L a b).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Reindexing commutes with the multiplication, in the first factor. -/
theorem eqToHom_whiskerRight_powMulIso {a a' : ℤ} (h : a = a') (b : ℤ) :
    eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) h) ▷ tensorPower 𝒪 h𝒪 L b ≫
        (powMulIso 𝒪 h𝒪 L a' b).hom =
      (powMulIso 𝒪 h𝒪 L a b).hom ≫
        eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (congrArg (· + b) h)) := by
  subst h
  simp

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Reindexing commutes with the multiplication, in the second factor. -/
theorem whiskerLeft_eqToHom_powMulIso (a : ℤ) {b b' : ℤ} (h : b = b') :
    tensorPower 𝒪 h𝒪 L a ◁ eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) h) ≫
        (powMulIso 𝒪 h𝒪 L a b').hom =
      (powMulIso 𝒪 h𝒪 L a b).hom ≫
        eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (congrArg (a + ·) h)) := by
  subst h
  simp

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Associativity of the multiplication**, at the spelling of `powMulIso`. -/
theorem powMulIso_assoc (a b c : ℤ) :
    (α_ (tensorPower 𝒪 h𝒪 L a) (tensorPower 𝒪 h𝒪 L b) (tensorPower 𝒪 h𝒪 L c)).hom ≫
        tensorPower 𝒪 h𝒪 L a ◁ (powMulIso 𝒪 h𝒪 L b c).hom ≫
          (powMulIso 𝒪 h𝒪 L a (b + c)).hom =
      (powMulIso 𝒪 h𝒪 L a b).hom ▷ tensorPower 𝒪 h𝒪 L c ≫
        (powMulIso 𝒪 h𝒪 L (a + b) c).hom ≫
          eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (Int.add_assoc a b c)) := by
  have := Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor 𝒪 h𝒪 L
  have h := Stacks.SheafOfModules.TensorPower.monoidalMulIso_assoc 𝒪 h𝒪 L a b c
  have hr : (Stacks.SheafOfModules.TensorPower.tensorPowerReindex 𝒪 h𝒪 L
      (Int.add_assoc a b c).symm).hom =
      eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (Int.add_assoc a b c).symm) := by
    generalize Int.add_assoc a b c = e
    generalize a + b + c = x at e
    subst e
    rfl
  rw [hr] at h
  have h' : (powMulIso 𝒪 h𝒪 L a b).hom ▷ tensorPower 𝒪 h𝒪 L c ≫
        (powMulIso 𝒪 h𝒪 L (a + b) c).hom =
      (α_ (tensorPower 𝒪 h𝒪 L a) (tensorPower 𝒪 h𝒪 L b) (tensorPower 𝒪 h𝒪 L c)).hom ≫
        tensorPower 𝒪 h𝒪 L a ◁ (powMulIso 𝒪 h𝒪 L b c).hom ≫
          (powMulIso 𝒪 h𝒪 L a (b + c)).hom ≫
            eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (Int.add_assoc a b c).symm) := h
  rw [reassoc_of% h']
  simp

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [IsInvertible 𝒪 h𝒪 L] in
private theorem whiskerRight_tensorHom_whiskerRight
    {A B D E X Y : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
    (f : A ⟶ B) (g : B ⟶ D) (h : X ⟶ Y) (k : D ⟶ E) :
    f ▷ X ≫ (g ⊗ₘ h) ≫ k ▷ Y = (f ≫ g ≫ k) ⊗ₘ h := by
  rw [tensorHom_def, tensorHom_def, MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight, Category.assoc, Category.assoc,
    MonoidalCategory.whisker_exchange]
  simp only [Category.assoc]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [IsInvertible 𝒪 h𝒪 L] in
private theorem whiskerRight_comp_tensorHom'
    {A B D X Y : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
    (f : A ⟶ B) (g : B ⟶ D) (h : X ⟶ Y) :
    f ▷ X ≫ (g ⊗ₘ h) = (f ≫ g) ⊗ₘ h := by
  rw [tensorHom_def, tensorHom_def, MonoidalCategory.comp_whiskerRight, Category.assoc]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [IsInvertible 𝒪 h𝒪 L] in
private theorem tensorHom_comp_whiskerRight'
    {A B D X Y : _root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
    (f : A ⟶ B) (g : B ⟶ D) (h : X ⟶ Y) :
    (f ≫ g) ⊗ₘ h = (f ⊗ₘ h) ≫ g ▷ Y := by
  rw [tensorHom_def', tensorHom_def', MonoidalCategory.comp_whiskerRight, Category.assoc]

/-! ### The identification `𝓛^{⊗ e} ≅ 𝓛^{⊗ n} ⊙ k` against the comparison -/

section Shift

open Stacks.TwistedSections (twistPow twistPowMap twistPowTensorIso)

variable (n : ℤ)

/-- **`𝓛^{⊗ n} ⊙ m ⟶ 𝓛^{⊗ (n + m)}`**: the grouped form, the comparison of the iterated power
`𝓛^{⊗ m}` with Tag 01CU's, and Tag 01CU's multiplication. -/
def twistPowCompare (m : ℕ) :
    twistPow (tensorPower 𝒪 h𝒪 L n) L m ⟶ tensorPower 𝒪 h𝒪 L (n + m) :=
  (twistPowTensorIso (tensorPower 𝒪 h𝒪 L n) L m).hom ≫
    tensorPower 𝒪 h𝒪 L n ◁ (tensorPowerCompare 𝒪 h𝒪 L m).hom ≫ (powMulIso 𝒪 h𝒪 L n m).hom

/-- **`𝓛^{⊗ e} ≅ 𝓛^{⊗ n} ⊙ k`**, for `e = n + k`. -/
def twistPowBeta (e k : ℕ) (he : (e : ℤ) = n + k) :
    natTensorPow L e ≅ twistPow (tensorPower 𝒪 h𝒪 L n) L k :=
  tensorPowerCompare 𝒪 h𝒪 L e ≪≫ eqToIso (congrArg (tensorPower 𝒪 h𝒪 L) he) ≪≫
    (powMulIso 𝒪 h𝒪 L n k).symm ≪≫
    whiskerLeftIso (tensorPower 𝒪 h𝒪 L n) (tensorPowerCompare 𝒪 h𝒪 L k).symm ≪≫
    (twistPowTensorIso (tensorPower 𝒪 h𝒪 L n) L k).symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The inverse of `twistPowBeta`, followed by the comparison `𝓛^{⊗ e} ⟶ tensorPower e`, is
`twistPowCompare` followed by the identification `tensorPower (n + k) = tensorPower e`. -/
theorem twistPowBeta_inv (e k : ℕ) (he : (e : ℤ) = n + k) :
    (twistPowBeta 𝒪 h𝒪 L n e k he).inv ≫ (tensorPowerCompare 𝒪 h𝒪 L e).hom =
      twistPowCompare 𝒪 h𝒪 L n k ≫ eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) he.symm) := by
  simp [twistPowBeta, twistPowCompare]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The comparison is compatible with adding `j` further copies of `𝓛`.** -/
theorem eqToHom_twistPowCompare (e k j : ℕ) (he : (e : ℤ) = n + k) :
    eqToHom (Stacks.SectionRingProjTheta.twistPow_twistPow (tensorPower 𝒪 h𝒪 L n) L k j) ≫
        twistPowCompare 𝒪 h𝒪 L n (k + j) =
      twistPowMap L (twistPowBeta 𝒪 h𝒪 L n e k he).inv j ≫
        eqToHom (Stacks.SectionRingProjTheta.twistPow_natTensorPow L e j) ≫
          (tensorPowerCompare 𝒪 h𝒪 L (e + j)).hom ≫
            eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (by push_cast; omega)) := by
  have hα : (α_ (tensorPower 𝒪 h𝒪 L n) (natTensorPow L k) (natTensorPow L j)).hom ≫
      tensorPower 𝒪 h𝒪 L n ◁ ((tensorPowerCompare 𝒪 h𝒪 L k).hom ⊗ₘ
        (tensorPowerCompare 𝒪 h𝒪 L j).hom) =
      ((tensorPower 𝒪 h𝒪 L n ◁ (tensorPowerCompare 𝒪 h𝒪 L k).hom) ⊗ₘ
        (tensorPowerCompare 𝒪 h𝒪 L j).hom) ≫
        (α_ (tensorPower 𝒪 h𝒪 L n) (tensorPower 𝒪 h𝒪 L k) (tensorPower 𝒪 h𝒪 L j)).hom := by
    rw [← MonoidalCategory.id_tensorHom (tensorPower 𝒪 h𝒪 L n)
        ((tensorPowerCompare 𝒪 h𝒪 L k).hom ⊗ₘ (tensorPowerCompare 𝒪 h𝒪 L j).hom),
      ← associator_naturality, MonoidalCategory.id_tensorHom]
  conv_lhs =>
    rw [twistPowCompare, Stacks.SectionRingProjTheta.eqToHom_twistPow_twistPow_hom_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, powAdd_tensorPowerCompare,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      Category.assoc, whiskerLeft_eqToHom_powMulIso, reassoc_of% hα,
      reassoc_of% powMulIso_assoc, reassoc_of% whiskerRight_tensorHom_whiskerRight]
  conv_rhs =>
    rw [← Stacks.SectionRingProjTheta.twistPowTensorIso_hom_powAdd L e j, Category.assoc,
      reassoc_of% (Stacks.TwistedSections.twistPowTensorIso_hom_naturality L
        (twistPowBeta 𝒪 h𝒪 L n e k he).inv j),
      reassoc_of% powAdd_tensorPowerCompare, reassoc_of% whiskerRight_comp_tensorHom',
      twistPowBeta_inv, tensorHom_comp_whiskerRight', Category.assoc,
      reassoc_of% (eqToHom_whiskerRight_powMulIso 𝒪 h𝒪 L he.symm _)]
  simp only [twistPowCompare, eqToHom_trans]

end Shift

/-! ### Multiplication by a global section on the right, read on the left -/

section Mul

open Stacks.TwistedSections (twistPow twistPowTensorIso)

attribute [local instance] Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
private theorem braiding_monoidalMulIso_aux (a b : ℤ) :
    (β_ (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L a)
        (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L b)).hom ≫
        (Stacks.SheafOfModules.TensorPower.monoidalMulIso 𝒪 h𝒪 L b a).hom =
      (Stacks.SheafOfModules.TensorPower.monoidalMulIso 𝒪 h𝒪 L a b).hom ≫
        (Stacks.SheafOfModules.TensorPower.tensorPowerReindex 𝒪 h𝒪 L (Int.add_comm a b)).hom := by
  have hb := tensorObjIso_braiding 𝒪 h𝒪 (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L a)
    (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L b)
  have hc := congrArg Iso.hom
    (Stacks.SheafOfModules.TensorPower.coherentMulIso_comm 𝒪 h𝒪 L a b)
  have hcomp : (Stacks.SheafOfModules.TensorPower.tensorPowerReindex 𝒪 h𝒪 L
      (Int.add_comm b a)).hom ≫ (Stacks.SheafOfModules.TensorPower.tensorPowerReindex 𝒪 h𝒪 L
        (Int.add_comm a b)).hom = 𝟙 _ := by
    generalize Int.add_comm b a = e₁
    generalize Int.add_comm a b = e₂
    revert e₁ e₂
    generalize a + b = x
    rintro rfl e₂
    rfl
  have e1 := ((reassoc_of% hb)
    (Stacks.SheafOfModules.TensorPower.coherentMulIso 𝒪 h𝒪 L b a).hom).symm
  have e2 : (tensorProductBraiding 𝒪 h𝒪 (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L a)
        (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L b)).hom ≫
        (Stacks.SheafOfModules.TensorPower.coherentMulIso 𝒪 h𝒪 L b a).hom =
      (Stacks.SheafOfModules.TensorPower.coherentMulIso 𝒪 h𝒪 L a b).hom ≫
        (Stacks.SheafOfModules.TensorPower.tensorPowerReindex 𝒪 h𝒪 L (Int.add_comm a b)).hom :=
    (congrArg (fun x => _ ≫ x) (Category.comp_id _).symm).trans
      ((congrArg (fun x => _ ≫ _ ≫ x) hcomp.symm).trans
        ((congrArg (fun x => _ ≫ x) (Category.assoc _ _ _).symm).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hc.symm))))
  exact e1.trans ((congrArg (fun x => (tensorObjIso 𝒪 h𝒪 _ _).hom ≫ x) e2).trans
    (Category.assoc _ _ _).symm)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The multiplication of Tag 01CU's powers is commutative**, at the spelling of `powMulIso`:
the braiding followed by the multiplication in the other order is the multiplication. -/
theorem braiding_powMulIso (a b : ℤ) :
    (β_ (tensorPower 𝒪 h𝒪 L a) (tensorPower 𝒪 h𝒪 L b)).hom ≫ (powMulIso 𝒪 h𝒪 L b a).hom =
      (powMulIso 𝒪 h𝒪 L a b).hom ≫
        eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (Int.add_comm a b)) := by
  have hr : (Stacks.SheafOfModules.TensorPower.tensorPowerReindex 𝒪 h𝒪 L
      (Int.add_comm a b)).hom =
      eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (Int.add_comm a b)) := by
    generalize Int.add_comm a b = e
    generalize b + a = x at e
    subst e
    rfl
  exact (braiding_monoidalMulIso_aux 𝒪 h𝒪 L a b).trans (congrArg (_ ≫ ·) hr)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Multiplication by a global section on the right, read through `twistPowCompare`, is
multiplication by it on the left**: for `σ` a global section of `𝓛^{⊗ m}`, multiplying a section
of `𝓛^{⊗ n}` by `σ` in `𝓛^{⊗ n} ⊙ m` and comparing is multiplying by the comparison of `σ` in
Tag 01CU's powers. -/
theorem smulRight_twistPowCompare (n : ℤ) (m : ℕ)
    (σ : 𝟙_ (_root_.SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ natTensorPow L m) :
    (ρ_ (tensorPower 𝒪 h𝒪 L n)).inv ≫ tensorPower 𝒪 h𝒪 L n ◁ σ ≫
        (twistPowTensorIso (tensorPower 𝒪 h𝒪 L n) L m).inv ≫ twistPowCompare 𝒪 h𝒪 L n m =
      (λ_ (tensorPower 𝒪 h𝒪 L n)).inv ≫
        (σ ≫ (tensorPowerCompare 𝒪 h𝒪 L m).hom) ▷ tensorPower 𝒪 h𝒪 L n ≫
          (powMulIso 𝒪 h𝒪 L m n).hom ≫
            eqToHom (congrArg (tensorPower 𝒪 h𝒪 L) (Int.add_comm (m : ℤ) n)) := by
  rw [← braiding_powMulIso, twistPowCompare, Iso.inv_hom_id_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc, BraidedCategory.braiding_naturality_left_assoc,
    ← leftUnitor_inv_braiding_assoc]

end Mul

end Stacks.SheafOfModules.Invertible

end
