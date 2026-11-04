module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonId

/-!
# The identity law for the comparison of the integral tensor powers

Let `T` be a scheme, `L` an invertible `𝒪_T`-module, and
`pieceIso k L n : k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` the comparison of the integral tensor powers along
a morphism `k : T' ⟶ T`. Pullback along `𝟙_T` is only isomorphic to the identity functor, so
`(𝟙_T)^*L` is isomorphic to `L` but not equal to it. This file proves the identity law: for every
integer `n` the triangle

    (𝟙_T)^*(L^{⊗ n}) ──pieceIso──> ((𝟙_T)^*L)^{⊗ n}
              │                            │
              │ the identity law           │ the degreewise transport of the identity law
              v                            v
            L^{⊗ n} <───────────────── L^{⊗ n}

commutes, where the right-hand vertical is `congrIso` applied to the component `(𝟙_T)^*L ≅ L` of
the identity law for pullback.

## Main definitions

* `isInvertiblePullbackModule`: the pullback of an invertible module along a morphism of schemes
  is invertible.
* `idCmp`: the component `(𝟙_T)^*L ≅ L` of the identity law for pullback.
* `IdCompat`: the identity triangle in degree `n`.

## Main results

* `idCompat_zero`: the triangle commutes in degree `0`.
* `idCompat_lhs`, `idCompat_rhs`: the two sides of the triangle in degree `n + 1`, expressed
  through their degree-`n` counterparts whiskered by `L`.
* `idCompat_succ`, `idCompat_of_succ`: the triangle commutes in degree `n + 1` if and only if it
  commutes in degree `n`.
* `pieceIso_id`: the triangle commutes in every integral degree.

## Implementation notes

In degree `0` the objects `(laurent L).piece 0` and `(laurent ((𝟙_T)^*L)).piece 0` are
definitionally equal but syntactically distinct; the crossing between them is made once, in an
ascribed `have` proved by a term. `ringedSpaceHom (𝟙 T) = 𝟙 T.toRingedSpace` holds by `rfl`, and
the statements below mix the two spellings.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentIdentity

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T : Scheme.{u}}
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The pullback of an invertible module along a morphism of schemes is invertible. -/
instance isInvertiblePullbackModule {T' T : Scheme.{u}} (k : T' ⟶ T)
    (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
    [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) M] :
    Stacks.SheafOfModules.IsInvertible T'.toRingedSpace.presheaf (isSheafStruct T')
      (pullbackModule k M) :=
  Stacks.PullbackMonoidalSheaf.isInvertible_pullbackFunctor_obj (ringedSpaceHom k) M

/-- The component `(𝟙_T)^*L ≅ L` of the identity law for pullback, with its source spelled as
`pullbackModule (𝟙 T) L`. -/
abbrev idCmp : pullbackModule (𝟙 T) L ≅ L :=
  (pullbackIdIso T.toRingedSpace).app L

/-- The identity triangle in degree `n`: the comparison of the integral tensor powers along
`𝟙_T`, followed by the degreewise transport of the identity law, is the identity law in degree
`n`. -/
abbrev IdCompat (n : ℤ) : Prop :=
  (pieceIso (𝟙 T) L n).hom ≫ (congrIso (idCmp L) n).hom =
    (pullbackIdIso T.toRingedSpace).hom.app ((laurent L).piece n)

/-- The identity triangle commutes in degree `0`. -/
theorem idCompat_zero : IdCompat L 0 := by
  have h : (pieceIso (𝟙 T) L 0).hom ≫ (congrIso (idCmp L) 0).hom =
      (pieceIso (𝟙 T) L 0).hom :=
    Category.comp_id _
  refine h.trans ?_
  exact (pullbackUnitComparison_id T.toRingedSpace).symm

/-- The left-hand side of the identity triangle in degree `n + 1`, precomposed with the
successor comparison, expressed through its degree-`n` counterpart whiskered by `L`. -/
theorem idCompat_lhs (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom (𝟙 T))).map (succIso L n).hom ≫
        ((pieceIso (𝟙 T) L (n + 1)).hom ≫ (congrIso (idCmp L) (n + 1)).hom) =
      pullbackTensorComparison (ringedSpaceHom (𝟙 T)) ((laurent L).piece n) L ≫
        ((pullbackModule (𝟙 T) ((laurent L).piece n)) ◁ (idCmp L).hom) ≫
          (((pieceIso (𝟙 T) L n).hom ≫ (congrIso (idCmp L) n).hom) ▷ L) ≫
            (succIso L n).hom := by
  rw [← Category.assoc, pieceIso_succIso]
  simp only [Category.assoc]
  rw [congrIso_succIso, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc (pieceIso (𝟙 T) L n).hom (idCmp L).hom]

/-- The right-hand side of the identity triangle in degree `n + 1`, precomposed with the
successor comparison, expressed through its degree-`n` counterpart whiskered by `L`. -/
theorem idCompat_rhs (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom (𝟙 T))).map (succIso L n).hom ≫
        (pullbackIdIso T.toRingedSpace).hom.app ((laurent L).piece (n + 1)) =
      pullbackTensorComparison (ringedSpaceHom (𝟙 T)) ((laurent L).piece n) L ≫
        ((pullbackModule (𝟙 T) ((laurent L).piece n)) ◁ (idCmp L).hom) ≫
          (((pullbackIdIso T.toRingedSpace).hom.app ((laurent L).piece n)) ▷ L) ≫
            (succIso L n).hom := by
  refine ((pullbackIdIso T.toRingedSpace).hom.naturality (succIso L n).hom).trans ?_
  rw [pullbackTensorComparison_id ((laurent L).piece n) L]
  simp only [Category.assoc, tensorHom_def']
  rfl

/-- The identity triangle commutes in degree `n + 1` if and only if it commutes in degree `n`. -/
private theorem idCompat_succ_iff (n : ℤ) : IdCompat L (n + 1) ↔ IdCompat L n := by
  refine (cancel_epi ((pullbackFunctor (ringedSpaceHom (𝟙 T))).map (succIso L n).hom)).symm.trans ?_
  rw [idCompat_lhs, idCompat_rhs]
  rw [cancel_epi, cancel_epi]
  refine (cancel_mono (succIso L n).hom).trans ?_
  let F := (Stacks.SheafOfModules.Tensor.sheafTensor ⟨T.toRingedSpace.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ T.toRingedSpace.presheaf
      (forget₂ CommRingCat RingCat) (isSheafStruct T)⟩).flip.obj L
  have : F.IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _
  refine ⟨fun h5 => F.map_injective ?_, fun h => congrArg (· ▷ L) h⟩
  exact (bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T)
      ((pieceIso (𝟙 T) L n).hom ≫ (congrIso (idCmp L) n).hom) L).trans
    (h5.trans (bridge_tensorRight T.toRingedSpace.presheaf (isSheafStruct T)
      ((pullbackIdIso T.toRingedSpace).hom.app ((laurent L).piece n)) L).symm)

/-- If the identity triangle commutes in degree `n`, it commutes in degree `n + 1`. -/
theorem idCompat_succ {n : ℤ} (h : IdCompat L n) : IdCompat L (n + 1) :=
  (idCompat_succ_iff L n).2 h

/-- If the identity triangle commutes in degree `n + 1`, it commutes in degree `n`. -/
theorem idCompat_of_succ {n : ℤ} (h : IdCompat L (n + 1)) : IdCompat L n :=
  (idCompat_succ_iff L n).1 h

/-- The identity law for the comparison `pieceIso`: for every integer `n`, the comparison along
`𝟙_T` followed by the degreewise transport of the identity law for pullback is the identity law
in degree `n`. -/
theorem pieceIso_id (n : ℤ) : IdCompat L n := by
  induction n using Int.induction_on with
  | zero => exact idCompat_zero L
  | succ i ih => exact idCompat_succ L ih
  | pred i ih => exact idCompat_of_succ L (n := -(i : ℤ) - 1) (by rwa [sub_add_cancel])

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentIdentity

end
