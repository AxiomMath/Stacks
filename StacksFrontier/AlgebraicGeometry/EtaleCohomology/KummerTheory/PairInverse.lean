module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairGroup
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairPicardTorsion

/-!
# The inverse of a pair

A pair on a scheme is an invertible sheaf together with a trivialization of its `n`-th tensor
power, and `AlgebraicGeometry.tensorPair` is the tensor product of two pairs. This file builds
the inverse of a pair: its invertible sheaf is the inverse tensor power `L^{⊗ -1}` of Tag 01CU,
and its trivialization is the one forced by requiring the tensor product with the original pair
to be the unit pair.

## Main definitions

* `AlgebraicGeometry.inverseSheafTensorIso` is `L^{⊗ -1} ⊗ L ≅ 𝒪`, the successor comparison of
  Tag 01CU at the exponent `-1`.
* `AlgebraicGeometry.tensorTrivSolve` is the trivialization of the first factor of a tensor
  product solved out of a trivialization of the whole and one of the second factor. The solution
  exists because a trivialization of the second factor turns the tensor product into its first
  factor, by the right unit constraint.
* `AlgebraicGeometry.inversePair` is **the inverse of a pair.**

## Main results

* `AlgebraicGeometry.tensorTriv_tensorTrivSolve`: **the solved trivialization does solve the
  equation** — tensoring it with the given trivialization of the second factor returns the given
  trivialization of the tensor product. Its content is
  `AlgebraicGeometry.tensorHom_rightUnitor_solve`.
* `AlgebraicGeometry.pairIsoTensorPairInverse`: **the tensor product of a pair with its inverse
  is the unit pair**, up to isomorphism of pairs.

## Implementation notes

The inverse pair is not built by inverting the trivialization of `P`: the invertible sheaf of
the inverse pair is `L^{⊗ -1}`, whose `n`-th tensor power is not presented by the development as
the inverse of the `n`-th tensor power of `L`. What is available is
`AlgebraicGeometry.inverseSheafTensorIso`, and the trivialization is obtained from it by solving
the equation that defines the tensor product of trivializations, which is
`AlgebraicGeometry.tensorTrivSolve`. The compatibility of the resulting pair with the unit pair
is then true by construction.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso tensorPowerReindex)

universe u v w

namespace AlgebraicGeometry

attribute [local instance] ringedSiteModulesMonoidal ringedSiteModulesSymmetric
  isInvertible_tensorObj isInvertible_unitRingedSite isInvertible_tensorUnitRingedSite
  isInvertible_schemeRingedSite

/-! ### Solving for the trivialization of one factor -/

/-- **A trivialization of a tensor product with a trivialized second factor determines one of
the first factor.** Tensoring with the given trivialization of the second factor and cancelling
the resulting unit factor is an isomorphism onto the first factor, so the equation defining the
tensor product of trivializations can be solved: that is the content of `hw`. -/
theorem tensorHom_rightUnitor_solve {D : Type w} [Category.{v} D] [MonoidalCategory D]
    {A B : D} (a : B ⟶ 𝟙_ D) (w : A ⊗ B ≅ A) (hw : w.hom = (𝟙 A ⊗ₘ a) ≫ (ρ_ A).hom)
    (d : A ⊗ B ⟶ 𝟙_ D) :
    ((w.inv ≫ d) ⊗ₘ a) ≫ (ρ_ (𝟙_ D)).hom = d := by
  rw [tensorHom_whiskerLeft_rightUnitor, ← Category.assoc, ← MonoidalCategory.id_tensorHom,
    ← hw, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **The trivialization of the first factor of a tensor product**, solved out of a
trivialization `γ` of the `n`-th tensor power of the product and a trivialization `α` of the
`n`-th tensor power of the second factor. -/
def tensorTrivSolve (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (K L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 K]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (α : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (γ : tpow X (tensorSheafOfModules X K L) n ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    tpow X K n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (tensorIsoOfModules X (Iso.refl (tpow X K n)) α ≪≫ ρ_ (tpow X K n)).symm ≪≫
    (tpowTensorIso X K L n).symm ≪≫ γ

/-- **The solved trivialization solves the equation**: tensoring it with the given
trivialization of the second factor returns the given trivialization of the tensor product. -/
theorem tensorTriv_tensorTrivSolve (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (K L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 K]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (n : ℕ)
    (α : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (γ : tpow X (tensorSheafOfModules X K L) n ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    tensorTriv X K L n (tensorTrivSolve X K L n α γ) α = γ := by
  apply Iso.ext
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (tpowTensorIso X K L n).hom ≫ z)
    (tensorHom_rightUnitor_solve α.hom
      (tensorIsoOfModules X (Iso.refl (tpow X K n)) α ≪≫ ρ_ (tpow X K n)) rfl
      ((tpowTensorIso X K L n).inv ≫ γ.hom))) ?_
  exact (tpowTensorIso X K L n).hom_inv_id_assoc γ.hom

/-! ### The inverse of a pair -/

/-- **`L^{⊗ -1} ⊗ L ≅ 𝒪`**: the successor comparison of Tag 01CU at the exponent `-1`, whose
target is the zeroth tensor power, that is the structure sheaf. -/
def inverseSheafTensorIso (S : Scheme.{u}) (L : SheafOfModules.{u} (ringSheaf S))
    [IsInvertible S.presheaf (ringSheafCond S) L] :
    tensorSheafOfModules (schemeRingedSite S)
        (tensorPower S.presheaf (ringSheafCond S) L (-1)) L ≅
      SheafOfModules.unit (ringSheaf S) :=
  tensorPowerSuccIso S.presheaf (ringSheafCond S) L (-1) ≪≫
    tensorPowerReindex S.presheaf (ringSheafCond S) L (neg_add_cancel (1 : ℤ))

/-- **The inverse of a pair**: the inverse tensor power of its invertible sheaf, with the
trivialization solved so that the tensor product with the original pair carries the canonical
trivialization of the structure sheaf. -/
def inversePair (S : Scheme.{u}) (n : ℕ) (P : TrivializedPower S n) : TrivializedPower S n :=
  letI := P.invertible
  letI := isInvertible_tensorPower S P.sheaf (-1)
  letI : IsInvertible S.presheaf (ringSheafCond S)
      (tensorSheafOfModules (schemeRingedSite S)
        (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf S.presheaf (ringSheafCond S)
      (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf
  letI : IsInvertible (schemeRingedSite S).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite S).O).2
      (tensorSheafOfModules (schemeRingedSite S)
        (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf S.presheaf (ringSheafCond S)
      (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf
  { sheaf := tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)
    invertible := isInvertible_tensorPower S P.sheaf (-1)
    trivialization :=
      tensorTrivSolve (schemeRingedSite S)
        (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf n P.trivialization
        (powerMap (schemeRingedSite S) (inverseSheafTensorIso S P.sheaf) n ≪≫
          structureSheafTensorPowerIso S n) }

/-- The invertible sheaf of the inverse of a pair is the inverse tensor power of its invertible
sheaf. -/
theorem inversePair_sheaf (S : Scheme.{u}) (n : ℕ) (P : TrivializedPower S n) :
    letI := P.invertible
    (inversePair S n P).sheaf =
      tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1) := rfl

/-- **The tensor product of the inverse of a pair with the pair is the unit pair**, up to
isomorphism of pairs: the isomorphism of invertible sheaves is
`AlgebraicGeometry.inverseSheafTensorIso`, and the compatibility with the trivializations holds
because the trivialization of the inverse pair was solved to make it hold. -/
def pairIsoTensorPairInverse {S : Scheme.{u}} {n : ℕ} (P : TrivializedPower S n) :
    PairIso (tensorPair S n (inversePair S n P) P) (unitPair S n 1) := by
  letI := P.invertible
  letI := isInvertible_tensorPower S P.sheaf (-1)
  letI : IsInvertible S.presheaf (ringSheafCond S)
      (tensorSheafOfModules (schemeRingedSite S)
        (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf S.presheaf (ringSheafCond S)
      (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf
  letI : IsInvertible (schemeRingedSite S).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (schemeRingedSite S).O).2
      (tensorSheafOfModules (schemeRingedSite S)
        (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf S.presheaf (ringSheafCond S)
      (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf
  refine { sheafIso := inverseSheafTensorIso S P.sheaf, compatible := ?_ }
  refine Eq.trans (congrArg (fun z => z ≪≫ (unitPair S n 1).trivialization)
    (tensorPowerMap_eq_powerMap S (inverseSheafTensorIso S P.sheaf) n)) ?_
  refine Eq.trans (congrArg
    (fun z => powerMap (schemeRingedSite S) (inverseSheafTensorIso S P.sheaf) n ≪≫ z)
    (unitPair_one_trivialization S n)) ?_
  exact (tensorTriv_tensorTrivSolve (schemeRingedSite S)
    (tensorPower S.presheaf (ringSheafCond S) P.sheaf (-1)) P.sheaf n P.trivialization
    (powerMap (schemeRingedSite S) (inverseSheafTensorIso S P.sheaf) n ≪≫
      structureSheafTensorPowerIso S n)).symm

/-- **Every isomorphism class of pairs has an inverse for the tensor product.** -/
theorem exists_tensorPairClass_eq_unitPair (S : Scheme.{u}) (n : ℕ) (x : PairClasses S n) :
    ∃ y : PairClasses S n,
      tensorPairClass S n y x = pairClass (unitPair S n 1) := by
  refine Quotient.inductionOn x fun P => ?_
  exact ⟨pairClass (inversePair S n P), (pairClass_eq_iff _ _).2 ⟨pairIsoTensorPairInverse P⟩⟩

end AlgebraicGeometry

end
