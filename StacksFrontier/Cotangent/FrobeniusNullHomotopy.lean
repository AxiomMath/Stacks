module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.StandardResolutionFrobeniusHomotopy

/-!
# The Frobenius endomorphism of the cotangent complex in positive characteristic

Let `p` be a prime, let `A → B` be a ring map with `p = 0` in `A`, and let `F_A` and `F_B` be the
Frobenius endomorphisms. They form a commutative square of ring maps, so they induce an
endomorphism of the cotangent complex `L_{B/A}` — the map of Section 08QL, which here is
`CommAlgCat.squareCotangentComplexMap` applied to `CommAlgCat.frobeniusSquare`. That endomorphism
is homotopic to zero.

## Main definitions

* `CommAlgCat.squareCotangentPush` is the map of base-changed differential modules
  `B ⊗[Pᵢ] Ω[Pᵢ⁄A] → B' ⊗[P'ⱼ] Ω[P'ⱼ⁄A']` induced by a ring map `Pᵢ → P'ⱼ` lying over a
  commutative square of ring maps, in possibly different simplicial degrees.
* `CommAlgCat.cylinderCotangentMap` is its value at a member of the homotopy of Tag 0G5Y.

## Main results

* `CommAlgCat.nonempty_homotopy_squareCotangentComplexMap_frobeniusSquare`: the endomorphism of
  `L_{B/A}` induced by the Frobenius square admits a null homotopy.
* `CommAlgCat.cotangentTermDifferential_pow`: the pure differential of a `p`-th power vanishes
  when `p = 0` in `A`.

## References

* [Stacks Project, Tag 0G5Z](https://stacks.math.columbia.edu/tag/0G5Z)
* [Stacks Project, Tag 0G5Y](https://stacks.math.columbia.edu/tag/0G5Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open scoped ChangeOfRings TensorProduct

universe u v w

/-- The differential of a `p`-th power vanishes when `p = 0` in the ring. -/
public theorem KaehlerDifferential.D_pow_eq_zero {A P : Type*} [CommRing A] [CommRing P]
    [Algebra A P] {p : ℕ} (hP : (p : P) = 0) (x : P) :
    KaehlerDifferential.D A P (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul P p, hP, zero_smul]

namespace CommAlgCat

section Push

variable {A : Type u} [CommRing A] {A' : Type w} [CommRing A']
  {B : CommAlgCat.{max u w v} A} {B' : CommAlgCat.{max u w v} A'}

/-- The `Pᵢ`-linear map `Ω[Pᵢ⁄A] → B' ⊗[P'ⱼ] Ω[P'ⱼ⁄A']`, `ω ↦ 1 ⊗ ω`, attached to a ring map
`u : Pᵢ → P'ⱼ` which carries the base ring along the given square and the augmentation along its
horizontal map. -/
public noncomputable def squareCotangentPushAdjoint (sq : AlgebraSquare.{u, v, w} A A' B B')
    {i j : SimplexCategoryᵒᵖ}
    (u : (standardResolution.{u, max w v} A B).left.obj i →+*
      (standardResolution.{w, max u v} A' B').left.obj j)
    (hbase : ∀ a : A, u (algebraMap A _ a) = algebraMap A' _ (sq.base a))
    (haug : ∀ x, standardResolutionAugmentationHom.{w, max u v} A' B' j (u x) =
      sq.map (standardResolutionAugmentationHom.{u, max w v} A B i x)) :
    ModuleCat.of ((standardResolution.{u, max w v} A B).left.obj i)
        (KaehlerDifferential A ((standardResolution.{u, max w v} A B).left.obj i)) ⟶
      (ModuleCat.restrictScalars
          (standardResolutionAugmentationHom.{u, max w v} A B i)).obj
        ((ModuleCat.restrictScalars sq.map).obj (cotangentTerm.{w, max u v} A' B' j)) := by
  let P := (standardResolution.{u, max w v} A B).left.obj i
  let P' := (standardResolution.{w, max u v} A' B').left.obj j
  let ε := standardResolutionAugmentationHom.{u, max w v} A B i
  let ε' := standardResolutionAugmentationHom.{w, max u v} A' B' j
  letI : Algebra A A' := sq.base.toAlgebra
  letI : Algebra P P' := u.toAlgebra
  letI : Algebra A P' := ((algebraMap A' P').comp sq.base).toAlgebra
  letI : Algebra P' B' := ε'.toAlgebra
  letI : Algebra P B' := (sq.map.comp ε).toAlgebra
  haveI : IsScalarTower P P' B' := IsScalarTower.of_algebraMap_eq fun x => (haug x).symm
  haveI : IsScalarTower A A' P' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower A P P' := IsScalarTower.of_algebraMap_eq fun a => (hbase a).symm
  haveI : SMulCommClass A' P P' :=
    ⟨fun a' x y => by simp only [Algebra.smul_def, mul_left_comm]⟩
  let M := ModuleCat.of P (KaehlerDifferential A P)
  let N := (ModuleCat.restrictScalars sq.map).obj (cotangentTerm.{w, max u v} A' B' j)
  let d : M ⟶ (ModuleCat.restrictScalars ε).obj N :=
    ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars ε).obj N)
      { toFun := fun ω => (1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P' ω)
        map_add' := by
          intro x y
          change (TensorProduct.mk P' B' (KaehlerDifferential A' P') 1)
              (KaehlerDifferential.map A A' P P' (x + y)) = _
          rw [map_add]
          exact (TensorProduct.mk P' B' (KaehlerDifferential A' P') 1).map_add _ _
        map_smul' := by
          intro q x
          change (1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P' (q • x)) =
            sq.map (ε q) • ((1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P' x))
          rw [map_smul, TensorProduct.tmul_smul]
          rfl }
  exact d

/-- The `B`-linear map `B ⊗[Pᵢ] Ω[Pᵢ⁄A] → B' ⊗[P'ⱼ] Ω[P'ⱼ⁄A']` of base-changed differentials, the
target being read over `B` along the horizontal map of the square, induced by a ring map
`u : Pᵢ → P'ⱼ` over that square: the `B`-linear extension of
`CommAlgCat.squareCotangentPushAdjoint`. -/
public noncomputable def squareCotangentPush (sq : AlgebraSquare.{u, v, w} A A' B B')
    {i j : SimplexCategoryᵒᵖ}
    (u : (standardResolution.{u, max w v} A B).left.obj i →+*
      (standardResolution.{w, max u v} A' B').left.obj j)
    (hbase : ∀ a : A, u (algebraMap A _ a) = algebraMap A' _ (sq.base a))
    (haug : ∀ x, standardResolutionAugmentationHom.{w, max u v} A' B' j (u x) =
      sq.map (standardResolutionAugmentationHom.{u, max w v} A B i x)) :
    cotangentTerm.{u, max w v} A B i ⟶
      (ModuleCat.restrictScalars sq.map).obj (cotangentTerm.{w, max u v} A' B' j) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (standardResolutionAugmentationHom.{u, max w v} A B i)
    (squareCotangentPushAdjoint.{u, v, w} sq u hbase haug)

/-- The induced map sends the pure differential `1 ⊗ d x` to `1 ⊗ d (u x)`. -/
@[simp]
public theorem squareCotangentPush_D (sq : AlgebraSquare.{u, v, w} A A' B B')
    {i j : SimplexCategoryᵒᵖ}
    (u : (standardResolution.{u, max w v} A B).left.obj i →+*
      (standardResolution.{w, max u v} A' B').left.obj j)
    (hbase : ∀ a : A, u (algebraMap A _ a) = algebraMap A' _ (sq.base a))
    (haug : ∀ x, standardResolutionAugmentationHom.{w, max u v} A' B' j (u x) =
      sq.map (standardResolutionAugmentationHom.{u, max w v} A B i x))
    (x : (standardResolution.{u, max w v} A B).left.obj i) :
    squareCotangentPush.{u, v, w} sq u hbase haug
        (cotangentTermDifferential.{u, max w v} A B i x) =
      cotangentTermDifferential.{w, max u v} A' B' j (u x) := by
  have key : squareCotangentPush.{u, v, w} sq u hbase haug
        (cotangentTermDifferential.{u, max w v} A B i x) =
      (1 : B) • (squareCotangentPushAdjoint.{u, v, w} sq u hbase haug)
        (KaehlerDifferential.D A ((standardResolution.{u, max w v} A B).left.obj i) x) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (standardResolutionAugmentationHom.{u, max w v} A B i)
      (squareCotangentPushAdjoint.{u, v, w} sq u hbase haug) (1 : B)
      (KaehlerDifferential.D A ((standardResolution.{u, max w v} A B).left.obj i) x)
  rw [key, one_smul]
  let P := (standardResolution.{u, max w v} A B).left.obj i
  let P' := (standardResolution.{w, max u v} A' B').left.obj j
  let ε := standardResolutionAugmentationHom.{u, max w v} A B i
  let ε' := standardResolutionAugmentationHom.{w, max u v} A' B' j
  let _ : Algebra A A' := sq.base.toAlgebra
  let _ : Algebra P P' := u.toAlgebra
  let _ : Algebra A P' := ((algebraMap A' P').comp sq.base).toAlgebra
  let _ : Algebra P' B' := ε'.toAlgebra
  let _ : Algebra P B' := (sq.map.comp ε).toAlgebra
  have : IsScalarTower P P' B' := IsScalarTower.of_algebraMap_eq fun y => (haug y).symm
  have : IsScalarTower A A' P' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A P P' := IsScalarTower.of_algebraMap_eq fun a => (hbase a).symm
  have : SMulCommClass A' P P' := ⟨fun a' y z => by simp only [Algebra.smul_def, mul_left_comm]⟩
  change (1 : B') ⊗ₜ[P'] (KaehlerDifferential.map A A' P P'
    (KaehlerDifferential.D A P x)) = _
  rw [KaehlerDifferential.map_D]
  rfl

end Push

section Characteristic

variable (p : ℕ) {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}

/-- The pure differential of a `p`-th power vanishes when `p = 0` in the base ring. -/
public theorem cotangentTermDifferential_pow (hA : (p : A) = 0) (n : SimplexCategoryᵒᵖ)
    (x : (standardResolution.{u, max u v} A B).left.obj n) :
    cotangentTermDifferential.{u, max u v} A B n (x ^ p) = 0 := by
  rw [← cotangentTermMk_D, KaehlerDifferential.D_pow_eq_zero
    (natCast_eq_zero_of_algebra (p := p) ((standardResolution.{u, max u v} A B).left.obj n) hA) x,
    map_zero]
  rfl

end Characteristic

section Homotopy

variable (p : ℕ) (hp : p.Prime) (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
  (hA : (p : A) = 0)

/-- The cotangent simplicial module, read over `B` along the Frobenius of `B`. -/
public noncomputable abbrev frobeniusCotangentSimplicialModule :
    SimplicialObject (ModuleCat.{max u v} B) :=
  ((SimplicialObject.whiskering _ _).obj
      (ModuleCat.restrictScalars (frobeniusSquare.{u, v} p hp A B hA).map)).obj
    (cotangentSimplicialModule.{u, max u v} A B).object

/-- The map of base-changed differentials attached to a simplex `t` of the interval by the
cylinder of Tag 0G5Y. -/
public noncomputable def cylinderCotangentMap
    (C : FrobeniusHomotopyCylinder.{u, v} p hp A B hA) (n : ℕ) (t : ⦋n⦌ ⟶ ⦋1⦌) :
    cotangentTerm.{u, max u v} A B (op ⦋n⦌) ⟶
      (ModuleCat.restrictScalars (frobeniusSquare.{u, v} p hp A B hA).map).obj
        (cotangentTerm.{u, max u v} A B (op ⦋n⦌)) :=
  squareCotangentPush.{u, v, u} (frobeniusSquare.{u, v} p hp A B hA) (C.map n t)
    (C.map_algebraMap n t) (C.map_augmentation n t)

/-- The value of `CommAlgCat.cylinderCotangentMap` on a pure differential. -/
public theorem cylinderCotangentMap_D (C : FrobeniusHomotopyCylinder.{u, v} p hp A B hA) (n : ℕ)
    (t : ⦋n⦌ ⟶ ⦋1⦌) (x : (standardResolution.{u, max u v} A B).left.obj (op ⦋n⦌)) :
    cylinderCotangentMap p hp A B hA C n t
        (cotangentTermDifferential.{u, max u v} A B (op ⦋n⦌) x) =
      cotangentTermDifferential.{u, max u v} A B (op ⦋n⦌) (C.map n t x) :=
  squareCotangentPush_D.{u, v, u} (frobeniusSquare.{u, v} p hp A B hA) (C.map n t)
    (C.map_algebraMap n t) (C.map_augmentation n t) x

/-- The cylinder maps commute with every simplicial operator. -/
private theorem cylinderCotangentMap_naturality
    (C : FrobeniusHomotopyCylinder.{u, v} p hp A B hA) {n m : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (t : ⦋n⦌ ⟶ ⦋1⦌) :
    cylinderCotangentMap p hp A B hA C n t ≫
        (frobeniusCotangentSimplicialModule.{u, v} p hp A B hA).map f.op =
      (cotangentSimplicialModule.{u, max u v} A B).object.map f.op ≫
        cylinderCotangentMap p hp A B hA C m (f ≫ t) := by
  refine cotangentTerm_hom_ext.{u, max u v} A B (op ⦋n⦌) _ _ fun x => ?_
  change (ModuleCat.restrictScalars (frobeniusSquare.{u, v} p hp A B hA).map).map
        (cotangentMap.{u, max u v} A B f.op)
      (cylinderCotangentMap p hp A B hA C n t
        (cotangentTermDifferential.{u, max u v} A B (op ⦋n⦌) x)) =
    cylinderCotangentMap p hp A B hA C m (f ≫ t)
      (cotangentMap.{u, max u v} A B f.op
        (cotangentTermDifferential.{u, max u v} A B (op ⦋n⦌) x))
  rw [cylinderCotangentMap_D, cotangentMap_D, cylinderCotangentMap_D,
    ← C.map_naturality f t x]
  exact cotangentMap_D.{u, max u v} A B f.op (C.map n t x)

/-- The simplicial homotopy of simplicial `B`-modules from the zero map to the endomorphism of
`L_{B/A}` induced by the Frobenius square: the cylinder of Tag 0G5Y, pushed to base-changed
differentials. -/
private theorem nonempty_homotopy_simplicial
    (C : FrobeniusHomotopyCylinder.{u, v} p hp A B hA) :
    Nonempty (SimplicialObject.Homotopy
      (0 : (cotangentSimplicialModule.{u, max u v} A B).object ⟶
        frobeniusCotangentSimplicialModule.{u, v} p hp A B hA)
      (squareCotangentSimplicialMap.{u, v, u} (frobeniusSquare.{u, v} p hp A B hA))) := by
  refine ⟨Godement.Prep.homotopyOfRel _ _
    (fun n i => cylinderCotangentMap p hp A B hA C n (SimplexCategory.toMk₁ i))
    ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro n
    refine cotangentTerm_hom_ext.{u, max u v} A B (op ⦋n⦌) _ _ fun x => ?_
    rw [toMk₁_zero_eq_const, cylinderCotangentMap_D, C.map_const_one]
    exact (squareCotangentTermMap_D.{u, v, u}
      (frobeniusSquare.{u, v} p hp A B hA) (op ⦋n⦌) x).symm
  · intro n
    refine cotangentTerm_hom_ext.{u, max u v} A B (op ⦋n⦌) _ _ fun x => ?_
    rw [toMk₁_last_eq_const, cylinderCotangentMap_D, C.map_const_zero,
      cotangentTermDifferential_pow p hA]
    rfl
  · intro n j i hji
    have hi : j.castSucc < i.succ := Fin.castSucc_lt_succ_iff.2 hji
    have h := cylinderCotangentMap_naturality p hp A B hA C (SimplexCategory.δ j)
      (SimplexCategory.toMk₁ i.succ)
    rwa [SimplexCategory.δ_comp_toMk₁_of_lt _ _ hi, Fin.pred_succ] at h
  · intro n j i hij
    have h := cylinderCotangentMap_naturality p hp A B hA C (SimplexCategory.δ j)
      (SimplexCategory.toMk₁ i.castSucc)
    rwa [SimplexCategory.δ_comp_toMk₁_of_le _ _ hij, Fin.castPred_castSucc] at h
  · intro n j i hji
    have hi : j.castSucc < i.succ := Fin.castSucc_lt_succ_iff.2 hji
    have h := cylinderCotangentMap_naturality p hp A B hA C (SimplexCategory.σ j)
      (SimplexCategory.toMk₁ i.succ)
    rwa [SimplexCategory.σ_comp_toMk₁_of_lt _ _ hi] at h
  · intro n j i hij
    have h := cylinderCotangentMap_naturality p hp A B hA C (SimplexCategory.σ j)
      (SimplexCategory.toMk₁ i.castSucc)
    rwa [SimplexCategory.σ_comp_toMk₁_of_le _ _ hij] at h

/-- Let `p` be a prime, let `A → B` be a ring map with `p = 0` in `A`, and let `F_A` and `F_B` be
the Frobenius endomorphisms. The endomorphism of the cotangent complex `L_{B/A}` induced by the
commutative square `(F_A, F_B)` — the map of Section 08QL, namely the `complexMap` field of
`CommAlgCat.squareFunctoriality` at `CommAlgCat.frobeniusSquare` — is homotopic to zero.

The target is the cotangent complex read over `B` along `F_B`: the induced map is semilinear over
`F_B`, not `B`-linear. Restriction of scalars leaves the underlying complex of abelian groups and
its differentials unchanged, so a null homotopy of this map is a null homotopy of the endomorphism
`L_{B/A} → L_{B/A}`. -/
@[stacks 0G5Z]
public theorem nonempty_homotopy_squareCotangentComplexMap_frobeniusSquare :
    Nonempty (Homotopy
      (squareCotangentComplexMap.{u, v, u} (frobeniusSquare.{u, v} p hp A B hA)) 0) := by
  obtain ⟨C⟩ := exists_frobeniusHomotopyCylinder.{u, v} p hp A B hA
  obtain ⟨H⟩ := nonempty_homotopy_simplicial.{u, v} p hp A B hA C
  refine ⟨?_⟩
  have h₁ : Homotopy
      ((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).map
        (squareCotangentSimplicialMap.{u, v, u} (frobeniusSquare.{u, v} p hp A B hA))) 0 :=
    H.toChainHomotopy.symm.trans (Homotopy.ofEq (by simp))
  have h₂ : Homotopy
      (squareCotangentMooreMap.{u, v, u} (frobeniusSquare.{u, v} p hp A B hA)) 0 :=
    (h₁.compRight _).trans (Homotopy.ofEq zero_comp)
  have h₃ : Homotopy
      (HomologicalComplex.extendMap
        (squareCotangentMooreMap.{u, v, u} (frobeniusSquare.{u, v} p hp A B hA))
        (ComplexShape.embeddingUpIntLE 0)) 0 :=
    (h₂.extend (ComplexShape.embeddingUpIntLE 0)).trans
      (Homotopy.ofEq (HomologicalComplex.extendMap_zero _ _ _))
  exact (h₃.compRight _).trans (Homotopy.ofEq zero_comp)

end Homotopy

end CommAlgCat

end
