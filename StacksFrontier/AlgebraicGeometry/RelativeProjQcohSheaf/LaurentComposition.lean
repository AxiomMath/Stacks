module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonComp

/-!
# The composition law for the comparison of the integral tensor powers

Let `k' : T'' ⟶ T'` and `k : T' ⟶ T` be morphisms of schemes and `L` an invertible
`𝒪_T`-module, and let `pieceIso k L n : k^*(L^{⊗ n}) ≅ (k^*L)^{⊗ n}` be the comparison of the
integral tensor powers. This file proves the composition law: for every integer `n` the square

    k'^*k^*(L^{⊗ n}) ──k'^*(pieceIso k)──> k'^*((k^*L)^{⊗ n}) ──pieceIso k'──> (k'^*k^*L)^{⊗ n}
            │                                                                        │
            │ the composition law                        the degreewise transport of it
            v                                                                        v
    (k' ≫ k)^*(L^{⊗ n}) ────────────pieceIso (k' ≫ k)───────────────> ((k' ≫ k)^*L)^{⊗ n}

commutes, where the left-hand vertical is the composition law for pullback and the right-hand
vertical is `congrIso` applied to its component `k'^*k^*L ≅ (k' ≫ k)^*L`.

## Main definitions

* `compCmp`: the component `k'^*k^*M ≅ (k' ≫ k)^*M` of the composition law for pullback.
* `CompCompat`: the composition square in degree `n`.

## Main results

* `compCompat_zero`: the square commutes in degree `0`.
* `compCompat_lhs`, `compCompat_rhs`: the two sides of the square in degree `n + 1`, expressed
  through their degree-`n` counterparts whiskered by `k'^*k^*L`.
* `compCompat_succ`, `compCompat_of_succ`: the square commutes in degree `n + 1` if and only if
  it commutes in degree `n`.
* `pieceIso_comp`: the square commutes in every integral degree.

## Implementation notes

`ringedSpaceHom (k' ≫ k) = ringedSpaceHom k' ≫ ringedSpaceHom k` holds by `rfl`, but the two
spellings are not syntactically equal: `Stacks.PullbackTensorCoherence.pullbackCompIso` is stated
at the second while `pieceIso (k' ≫ k)` produces the first. Each crossing between them is made
inside a lemma proved by a term, never by asking `rw` to match across the two.

## References

* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

open AlgebraicGeometry Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.SheafOfModules.TensorPower

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentPullback
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentIdentity

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {T'' T' T : Scheme.{u}} (k' : T'' ⟶ T') (k : T' ⟶ T)
  (L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace))
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]

/-- The component `k'^*k^*M ≅ (k' ≫ k)^*M` of the composition law for pullback, with its source
spelled as the iterated pullback `pullbackModule k' (pullbackModule k M)`. -/
abbrev compCmp (M : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :
    pullbackModule k' (pullbackModule k M) ≅ pullbackModule (k' ≫ k) M :=
  (pullbackCompIso (ringedSpaceHom k') (ringedSpaceHom k)).app M

/-- The composition square in degree `n`: pulling back the comparison along `k'`, comparing
along `k'`, and transporting along the composition law agrees with the comparison along
`k' ≫ k`. -/
abbrev CompCompat (n : ℤ) : Prop :=
  (compCmp k' k ((laurent L).piece n)).hom ≫ (pieceIso (k' ≫ k) L n).hom =
    (pullbackFunctor (ringedSpaceHom k')).map (pieceIso k L n).hom ≫
      ((pieceIso k' (pullbackModule k L) n).hom ≫ (congrIso (compCmp k' k L) n).hom)

/-- The composition square commutes in degree `0`. -/
theorem compCompat_zero : CompCompat k' k L 0 := by
  have h : (pullbackFunctor (ringedSpaceHom k')).map (pieceIso k L 0).hom ≫
        ((pieceIso k' (pullbackModule k L) 0).hom ≫ (congrIso (compCmp k' k L) 0).hom) =
      (pullbackFunctor (ringedSpaceHom k')).map (pieceIso k L 0).hom ≫
        (pieceIso k' (pullbackModule k L) 0).hom :=
    congrArg (fun z => (pullbackFunctor (ringedSpaceHom k')).map (pieceIso k L 0).hom ≫ z)
      (Category.comp_id _)
  refine Eq.trans ?_ h.symm
  exact pullbackUnitComparison_comp (ringedSpaceHom k') (ringedSpaceHom k)

/-- Naturality of the composition law `compCmp`, with the source functor spelled as an iterated
pullback. -/
theorem compCmp_naturality {M N : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
    (h : M ⟶ N) :
    (pullbackFunctor (ringedSpaceHom k')).map ((pullbackFunctor (ringedSpaceHom k)).map h) ≫
        (compCmp k' k N).hom =
      (compCmp k' k M).hom ≫ (pullbackFunctor (ringedSpaceHom (k' ≫ k))).map h :=
  (pullbackCompIso (ringedSpaceHom k') (ringedSpaceHom k)).hom.naturality h

/-- The tensor comparison of pullback along `k' ≫ k` is compatible with the composition law
`compCmp`. -/
theorem compCmp_tensorComparison
    (A B : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)) :
    (compCmp k' k (A ⊗ B)).hom ≫
        pullbackTensorComparison (ringedSpaceHom (k' ≫ k)) A B =
      (pullbackFunctor (ringedSpaceHom k')).map
          (pullbackTensorComparison (ringedSpaceHom k) A B) ≫
        pullbackTensorComparison (ringedSpaceHom k')
            (pullbackModule k A) (pullbackModule k B) ≫
          ((compCmp k' k A).hom ⊗ₘ (compCmp k' k B).hom) :=
  pullbackTensorComparison_comp (ringedSpaceHom k') (ringedSpaceHom k) A B

/-- The left-hand side of the composition square in degree `n + 1`, precomposed with the
successor comparison, expressed through its degree-`n` counterpart whiskered by `k'^*k^*L`. -/
theorem compCompat_lhs (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom k')).map
          ((pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom) ≫
        ((compCmp k' k ((laurent L).piece (n + 1))).hom ≫
          (pieceIso (k' ≫ k) L (n + 1)).hom) =
      (pullbackFunctor (ringedSpaceHom k')).map
          (pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L) ≫
        pullbackTensorComparison (ringedSpaceHom k')
            (pullbackModule k ((laurent L).piece n)) (pullbackModule k L) ≫
          (((compCmp k' k ((laurent L).piece n)).hom ≫ (pieceIso (k' ≫ k) L n).hom) ▷
            pullbackModule k' (pullbackModule k L)) ≫
            ((laurent (pullbackModule (k' ≫ k) L)).piece n ◁ (compCmp k' k L).hom) ≫
              (succIso (pullbackModule (k' ≫ k) L) n).hom := by
  rw [← Category.assoc, compCmp_naturality]
  simp only [Category.assoc]
  rw [pieceIso_succIso, ← Category.assoc, compCmp_tensorComparison]
  simp only [Category.assoc, tensorHom_def, MonoidalCategory.comp_whiskerRight]
  rw [whisker_exchange_assoc (pieceIso (k' ≫ k) L n).hom (compCmp k' k L).hom]

/-- The right-hand side of the composition square in degree `n + 1`, precomposed with the
successor comparison, expressed through its degree-`n` counterpart whiskered by `k'^*k^*L`. -/
theorem compCompat_rhs (n : ℤ) :
    (pullbackFunctor (ringedSpaceHom k')).map
          ((pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom) ≫
        ((pullbackFunctor (ringedSpaceHom k')).map (pieceIso k L (n + 1)).hom ≫
          ((pieceIso k' (pullbackModule k L) (n + 1)).hom ≫
            (congrIso (compCmp k' k L) (n + 1)).hom)) =
      (pullbackFunctor (ringedSpaceHom k')).map
          (pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L) ≫
        pullbackTensorComparison (ringedSpaceHom k')
            (pullbackModule k ((laurent L).piece n)) (pullbackModule k L) ≫
          (((pullbackFunctor (ringedSpaceHom k')).map (pieceIso k L n).hom ≫
            ((pieceIso k' (pullbackModule k L) n).hom ≫
              (congrIso (compCmp k' k L) n).hom)) ▷
            pullbackModule k' (pullbackModule k L)) ≫
            ((laurent (pullbackModule (k' ≫ k) L)).piece n ◁ (compCmp k' k L).hom) ≫
              (succIso (pullbackModule (k' ≫ k) L) n).hom := by
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, pieceIso_succIso,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (pieceIso_succIso k' (pullbackModule k L) n), congrIso_succIso,
    reassoc_of% (pullbackTensorComparison_naturality_left (ringedSpaceHom k')
      (B := pullbackModule k L) (pieceIso k L n).hom)]
  simp only [Category.assoc, MonoidalCategory.comp_whiskerRight]
  rw [whisker_exchange_assoc (congrIso (compCmp k' k L) n).hom (compCmp k' k L).hom]

/-- The square in degree `n + 1` commutes iff it does after precomposing with the successor
comparison. -/
private theorem compCompat_succ_iff (n : ℤ) :
    CompCompat k' k L (n + 1) ↔
      (pullbackFunctor (ringedSpaceHom k')).map
          ((pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom) ≫
        ((compCmp k' k ((laurent L).piece (n + 1))).hom ≫
          (pieceIso (k' ≫ k) L (n + 1)).hom) =
      (pullbackFunctor (ringedSpaceHom k')).map
          ((pullbackFunctor (ringedSpaceHom k)).map (succIso L n).hom) ≫
        ((pullbackFunctor (ringedSpaceHom k')).map (pieceIso k L (n + 1)).hom ≫
          ((pieceIso k' (pullbackModule k L) (n + 1)).hom ≫
            (congrIso (compCmp k' k L) (n + 1)).hom)) :=
  (Iso.cancel_iso_hom_left
    ((pullbackFunctor (ringedSpaceHom k')).mapIso
      ((pullbackFunctor (ringedSpaceHom k)).mapIso (succIso L n))) _ _).symm

/-- If the composition square commutes in degree `n`, it commutes in degree `n + 1`. -/
theorem compCompat_succ {n : ℤ} (h : CompCompat k' k L n) : CompCompat k' k L (n + 1) :=
  (compCompat_succ_iff k' k L n).mpr (by rw [compCompat_lhs, compCompat_rhs, h])

/-- If the composition square commutes in degree `n + 1`, it commutes in degree `n`. -/
theorem compCompat_of_succ {n : ℤ} (h : CompCompat k' k L (n + 1)) : CompCompat k' k L n := by
  have h2 := (compCompat_succ_iff k' k L n).mp h
  rw [compCompat_lhs, compCompat_rhs] at h2
  have h3 := (Iso.cancel_iso_hom_left
    ((pullbackFunctor (ringedSpaceHom k')).mapIso
      (asIso (pullbackTensorComparison (ringedSpaceHom k) ((laurent L).piece n) L))) _ _).mp h2
  have h4 := (Iso.cancel_iso_hom_left
    (asIso (pullbackTensorComparison (ringedSpaceHom k')
      (pullbackModule k ((laurent L).piece n)) (pullbackModule k L))) _ _).mp h3
  have h5 := (Iso.cancel_iso_hom_right _ _
    (MonoidalCategory.whiskerLeftIso
        ((laurent (pullbackModule (k' ≫ k) L)).piece n) (compCmp k' k L) ≪≫
      succIso (pullbackModule (k' ≫ k) L) n)).mp h4
  let : ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨T''.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        T''.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
        (isSheafStruct T'')⟩).flip.obj
    (pullbackModule k' (pullbackModule k L))).IsEquivalence :=
    Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor _ _ _
  refine ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, u, u}
      ⟨T''.toRingedSpace.presheaf, Presheaf.isSheaf_of_isSheaf_comp _
        T''.toRingedSpace.presheaf (forget₂ CommRingCat RingCat)
        (isSheafStruct T'')⟩).flip.obj
    (pullbackModule k' (pullbackModule k L))).map_injective ?_
  exact (bridge_tensorRight T''.toRingedSpace.presheaf (isSheafStruct T'')
      ((compCmp k' k ((laurent L).piece n)).hom ≫ (pieceIso (k' ≫ k) L n).hom)
      (pullbackModule k' (pullbackModule k L))).trans
    (h5.trans (bridge_tensorRight T''.toRingedSpace.presheaf (isSheafStruct T'')
      ((pullbackFunctor (ringedSpaceHom k')).map (pieceIso k L n).hom ≫
        ((pieceIso k' (pullbackModule k L) n).hom ≫ (congrIso (compCmp k' k L) n).hom))
      (pullbackModule k' (pullbackModule k L))).symm)

/-- The composition law for the comparison `pieceIso`: for every integer `n`, pulling the
comparison back twice agrees with pulling it back along the composite, through the composition
law for pullback and its degreewise transport. -/
theorem pieceIso_comp (n : ℤ) : CompCompat k' k L n := by
  induction n using Int.induction_on with
  | zero => exact compCompat_zero k' k L
  | succ i ih => exact compCompat_succ k' k L ih
  | pred i ih => exact compCompat_of_succ k' k L (n := -(i : ℤ) - 1) (by rwa [sub_add_cancel])

end Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentComposition

end
