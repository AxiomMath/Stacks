module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairGroup

/-!
# The tensor product of pairs is commutative

A pair on a scheme is an invertible sheaf together with a trivialization of its `n`-th tensor
power, and `AlgebraicGeometry.tensorPair` is the tensor product of two pairs. This file proves
that the tensor product of two pairs is commutative up to isomorphism of pairs, the symmetry
constraint of the invertible sheaves being the isomorphism that realizes it.

## Main results

* `AlgebraicGeometry.tensorMu_braiding_swap`: **the middle-four interchange of a symmetric
  monoidal category is compatible with the braiding**, which is
  `CategoryTheory.SymmetricCategory.tensorμ_braid_swap` with the two pairs of arguments allowed
  to differ.
* `AlgebraicGeometry.tpowTensorIso_braiding`: **the tensor-power comparison is compatible with
  the braiding.** Proved by induction out of `AlgebraicGeometry.tensorMu_braiding_step`.
* `AlgebraicGeometry.tensorTriv_braiding`: **the trivialization of a tensor product of pairs is
  carried to the one of the pairs in the other order by the braiding.**
* `AlgebraicGeometry.pairIsoTensorPairComm`: **the tensor product of two pairs is commutative up
  to isomorphism of pairs**, and `AlgebraicGeometry.tensorPairClass_comm` is the resulting
  commutativity on isomorphism classes.

## Implementation notes

The monoidal coherences are isolated as statements of an abstract symmetric monoidal category
and applied to sheaves of modules by `exact`, exactly as the two unit laws of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.PairGroup` are: no object of the
abstract statements carries a projection of a ringed site, so `rw` and `simp` work on them.

The isomorphism of invertible sheaves realizing the commutativity is written as
`Stacks.SheafOfModules.Invertible.tensorProductBraiding` rather than `β_`, because the pair
built by `AlgebraicGeometry.tensorPair` carries its sheaf as a tensor product sheaf of the
Picard development; the two are the same morphism by
`Stacks.Cohomology.Torsors.Generators.braiding_eq`, but only the first spelling lets instance
resolution see the monoidal structure without being asked to invert
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O)`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules (schemeRingedSite)
open Stacks.Cohomology.Torsors.Generators
open Stacks.SheafOfModules (IsInvertible)
open Stacks.SheafOfModules.Invertible (tensorPower tensorProductBraiding)

universe u v w

namespace AlgebraicGeometry

attribute [local instance] ringedSiteModulesMonoidal ringedSiteModulesSymmetric
  isInvertible_tensorObj isInvertible_unitRingedSite isInvertible_tensorUnitRingedSite
  isInvertible_schemeRingedSite

/-! ### The monoidal coherences behind the commutativity -/

/-- The braiding of the unit object with itself is the identity: both unit constraints agree on
the unit object, and the braiding is the one composed with the inverse of the other. -/
theorem braidingUnit_hom {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] :
    (β_ (𝟙_ D) (𝟙_ D)).hom = 𝟙 ((𝟙_ D) ⊗ (𝟙_ D)) := by
  rw [braiding_tensorUnit_left, MonoidalCategory.unitors_equal, Iso.hom_inv_id]

/-- **The middle-four interchange is compatible with the braiding.** This is
`CategoryTheory.SymmetricCategory.tensorμ_braid_swap`, which states the case of two repeated
arguments, for four arbitrary objects; the symmetry is needed and the braiding alone does not
suffice, because the two inverse braidings of the two sides have to be identified. -/
theorem tensorMu_braiding_swap {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] (A B L M : D) :
    tensorμ A B L M ≫ (β_ (A ⊗ L) (B ⊗ M)).hom =
      ((β_ A B).hom ⊗ₘ (β_ L M).hom) ≫ tensorμ B A M L := by
  simp [tensorμ, SymmetricCategory.braiding_swap_eq_inv_braiding L B,
    MonoidalCategory.tensorHom_def]

/-- **The inductive step of the compatibility of the tensor-power comparison with the
braiding**, isolated as an identity of a symmetric monoidal category. Both sides are read after
the leading inverse successor comparison has been cancelled; the hypothesis `ih` is the
compatibility at the previous exponent. -/
theorem tensorMu_braiding_step {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] {V V' A B L M A' B' : D}
    (pg : V ⟶ V') (T : V ⟶ A ⊗ B) (T' : V' ⟶ B ⊗ A)
    (sl : A ⊗ L ⟶ A') (sm : B ⊗ M ⟶ B')
    (ih : pg ≫ T' = T ≫ (β_ A B).hom) :
    (pg ⊗ₘ (β_ L M).hom) ≫ (T' ⊗ₘ 𝟙 (M ⊗ L)) ≫ tensorμ B A M L ≫ (sm ⊗ₘ sl) =
      (T ⊗ₘ 𝟙 (L ⊗ M)) ≫ tensorμ A B L M ≫ (sl ⊗ₘ sm) ≫ (β_ A' B').hom := by
  have h1 : (pg ⊗ₘ (β_ L M).hom) ≫ (T' ⊗ₘ 𝟙 (M ⊗ L)) =
      (T ⊗ₘ 𝟙 (L ⊗ M)) ≫ ((β_ A B).hom ⊗ₘ (β_ L M).hom) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, ih]
  rw [reassoc_of% h1, ← reassoc_of% tensorMu_braiding_swap,
    ← BraidedCategory.braiding_naturality]

/-- The base case of the compatibility of the tensor-power comparison with the braiding: at the
zero exponent the comparison is an inverse unit constraint and the braiding is the identity. -/
theorem rightUnitor_inv_braiding_unit {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] :
    (ρ_ (𝟙_ D)).inv = (ρ_ (𝟙_ D)).inv ≫ (β_ (𝟙_ D) (𝟙_ D)).hom := by
  rw [braidingUnit_hom, Category.comp_id]

/-- **Two morphisms to the unit object, tensored in either order and followed by the right unit
constraint, are exchanged by the braiding.** -/
theorem braiding_tensorHom_rightUnitor {D : Type w} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] {A B : D} (a : A ⟶ 𝟙_ D) (b : B ⟶ 𝟙_ D) :
    (β_ A B).hom ≫ (b ⊗ₘ a) ≫ (ρ_ (𝟙_ D)).hom = (a ⊗ₘ b) ≫ (ρ_ (𝟙_ D)).hom := by
  rw [← Category.assoc, ← BraidedCategory.braiding_naturality, braidingUnit_hom,
    Category.comp_id]

/-! ### The tensor-power comparison and the braiding -/

/-- **The tensor-power comparison is compatible with the braiding**: comparing the `n`-th power
of `L ⊗ M` with `L^{⊗ n} ⊗ M^{⊗ n}` and then exchanging the two factors is the same as taking
the `n`-th power of the symmetry constraint of `L ⊗ M` first. -/
theorem tpowTensorIso_braiding (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ) :
    (powerMap X (β_ L M) n).hom ≫ (tpowTensorIso X M L n).hom =
      (tpowTensorIso X L M n).hom ≫ (β_ (tpow X L n) (tpow X M n)).hom := by
  induction n with
  | zero =>
    exact (Category.id_comp _).trans rightUnitor_inv_braiding_unit
  | succ k ih =>
    simp only [powerMap_succ_tensorIsoOfModules, tpowTensorIso_succ, Iso.trans_hom, Iso.symm_hom,
      Iso.refl_hom, tensorIsoOfModules_hom, tensorInterchangeIso_hom, ← tensorObj_eq,
      Category.assoc, Iso.hom_inv_id_assoc]
    exact (tpowSuccIso X (L ⊗ M) k).inv ≫=
      (tensorMu_braiding_step (powerMap X (β_ L M) k).hom (tpowTensorIso X L M k).hom
        (tpowTensorIso X M L k).hom (tpowSuccIso X L k).hom (tpowSuccIso X M k).hom ih)

/-- **The trivialization of a tensor product of pairs is compatible with the braiding**: the
`n`-th power of the symmetry constraint carries the trivialization of the tensor product in one
order to the one in the other order. -/
theorem tensorTriv_braiding (X : RingedSite.{u, u, u})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify X.J AddCommGrpCat.{u}]
    (L M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (n : ℕ)
    (al : tpow X L n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (bl : tpow X M n ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    powerMap X (β_ L M) n ≪≫ tensorTriv X M L n bl al = tensorTriv X L M n al bl := by
  apply Iso.ext
  change (powerMap X (β_ L M) n).hom ≫
      (((tpowTensorIso X M L n).hom ≫ (bl.hom ⊗ₘ al.hom)) ≫
        (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom) =
    ((tpowTensorIso X L M n).hom ≫ (al.hom ⊗ₘ bl.hom)) ≫
      (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom
  refine Eq.trans (congrArg (fun z => (powerMap X (β_ L M) n).hom ≫ z)
    (Category.assoc _ _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun z => z ≫ (bl.hom ⊗ₘ al.hom) ≫
      (ρ_ (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom)
    (tpowTensorIso_braiding X L M n)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun z => (tpowTensorIso X L M n).hom ≫ z)
    (braiding_tensorHom_rightUnitor al.hom bl.hom)) ?_
  exact (Category.assoc _ _ _).symm

/-! ### The tensor product of pairs is commutative -/

/-- **The tensor product of two pairs is commutative up to isomorphism of pairs**: the
isomorphism of invertible sheaves is the symmetry constraint, and its compatibility with the
trivializations is `AlgebraicGeometry.tensorTriv_braiding`. -/
def pairIsoTensorPairComm {S : Scheme.{u}} {n : ℕ} (P Q : TrivializedPower S n) :
    PairIso (tensorPair S n P Q) (tensorPair S n Q P) where
  sheafIso := tensorProductBraiding S.presheaf (ringSheafCond S) P.sheaf Q.sheaf
  compatible := by
    let := P.invertible
    let := Q.invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
            (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj P.sheaf).obj Q.sheaf)) :=
      (tensorPair S n P Q).invertible
    let : IsInvertible S.presheaf (ringSheafCond S)
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨S.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ S.presheaf
            (forget₂ CommRingCat RingCat) (ringSheafCond S)⟩).obj Q.sheaf).obj P.sheaf)) :=
      (tensorPair S n Q P).invertible
    refine Eq.trans (congrArg (fun z => z ≪≫ (tensorPair S n Q P).trivialization)
      (tensorPowerMap_eq_powerMap S
        (tensorProductBraiding S.presheaf (ringSheafCond S) P.sheaf Q.sheaf) n)) ?_
    exact tensorTriv_braiding (schemeRingedSite S) P.sheaf Q.sheaf n
      P.trivialization Q.trivialization

/-- **The tensor product of isomorphism classes of pairs is commutative.** -/
theorem tensorPairClass_comm (S : Scheme.{u}) (n : ℕ) (x y : PairClasses S n) :
    tensorPairClass S n x y = tensorPairClass S n y x := by
  refine Quotient.inductionOn₂ x y fun P Q => ?_
  exact (pairClass_eq_iff _ _).2 ⟨pairIsoTensorPairComm P Q⟩

end AlgebraicGeometry

end
