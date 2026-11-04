module

public import StacksFrontier.Homology.DerivedIndexing.BaseChangeDelta
public import StacksFrontier.Homology.DerivedIndexing.CompositeCommShift
public import StacksFrontier.Homology.DerivedIndexing.NatTransCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.NaturalComplementComparison

/-!
# The composition transformation along an exact first factor and the connecting morphisms

Let `P : 𝒜' ⥤ 𝒜` be an exact functor and `Q : 𝒜 ⥤ ℬ` additive, `𝒜'` and `𝒜` with enough
injectives. The canonical transformation `t : R(Q ∘ P) ⟶ RP ⋙ RQ` of [Stacks, Tag 05T2],
followed by `RQ` of the inverse of the canonical isomorphism `P(X)[0] ≅ RP(X[0])` (invertible
because `P` is exact), gives a map

`R(Q ∘ P)(X[0]) ⟶ RQ(P(X)[0])`

for every object `X` of `𝒜'`, natural in `X`. This file shows that it commutes with the
connecting morphisms: on cohomology it is a morphism from the δ-functor `R ⁱ(Q ∘ P)` to the
δ-functor `R ⁱQ ∘ P`. This is the companion of
`Stacks.DerivedIndexing.canonicalδ_comp_derivedPairMap`, which treats maps *into* the right
derived functor of a composite.

## Main definitions

* `Stacks.DerivedIndexing.exactPrecompMap`: the map `R(Q ∘ P)(X[0]) ⟶ RQ(P(X)[0])`.

## Main results

* `Stacks.DerivedIndexing.exactPrecompMap_naturality`: naturality in `X`.
* `Stacks.DerivedIndexing.canonicalδ_comp_exactPrecompMap`: **compatibility with the connecting
  morphisms.**

## References

* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

namespace Stacks.DerivedIndexing

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  Functor.isTriangulated_rightDerivedFunctorPlus

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B] [Abelian A] [Abelian A']
  [Abelian B] [EnoughInjectives A] [EnoughInjectives A'] (P : A' ⥤ A) (Q : A ⥤ B)
  [P.Additive] [Q.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]

/-- The connecting morphism of `derivedDeltaFunctorStructure F` unfolds to `RF` of `singleδPlus`
followed by the shift isomorphism. -/
private theorem derivedDeltaFunctorStructure_δ_eq {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [EnoughInjectives C] (F : C ⥤ D) [F.Additive] {S : ShortComplex C}
    (hS : S.ShortExact) :
    (derivedDeltaFunctorStructure F).δ hS = F.rightDerivedFunctorPlus.map (singleδPlus hS) ≫
      (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) := rfl

/-- For an exact functor the canonical map `P(X)[0] ⟶ RP(X[0])` is an isomorphism. -/
instance isIso_rightDerivedPlusUnitSingle_app_of_exact (X : A') :
    IsIso ((rightDerivedPlusUnitSingle P).app X) :=
  haveI := Stacks.Cohomology.LerayDegreewise.isIso_rightDerivedPlusUnitSingle P
    (Functor.rightAcyclic_of_exact P)
  inferInstance

/-- **The map `R(Q ∘ P)(X[0]) ⟶ RQ(P(X)[0])`** for an exact `P`: the canonical transformation
`R(Q ∘ P) ⟶ RP ⋙ RQ` followed by `RQ` of the inverse of `P(X)[0] ≅ RP(X[0])`. -/
def exactPrecompMap (X : A') :
    (P ⋙ Q).rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A' 0).obj X) ⟶
      Q.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj (P.obj X)) :=
  (rightDerivedPlusCompTrans P Q).app _ ≫
    Q.rightDerivedFunctorPlus.map (inv ((rightDerivedPlusUnitSingle P).app X))

/-- **`exactPrecompMap` is natural.** -/
@[reassoc]
theorem exactPrecompMap_naturality {X Y : A'} (a : X ⟶ Y) :
    (P ⋙ Q).rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A' 0).map a) ≫
        exactPrecompMap P Q Y =
      exactPrecompMap P Q X ≫
        Q.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map (P.map a)) := by
  have ht := (rightDerivedPlusCompTrans P Q).naturality
    ((DerivedCategory.Plus.singleFunctor A' 0).map a)
  have hu := (rightDerivedPlusUnitSingle P).naturality a
  simp only [Functor.comp_map] at ht hu
  have hu' : inv ((rightDerivedPlusUnitSingle P).app X) ≫
      (DerivedCategory.Plus.singleFunctor A 0).map (P.map a) =
        P.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A' 0).map a) ≫
          inv ((rightDerivedPlusUnitSingle P).app Y) := by
    rw [IsIso.inv_comp_eq, ← assoc, ← hu, assoc, IsIso.hom_inv_id, comp_id]
  dsimp only [exactPrecompMap]
  rw [← assoc, ht, assoc, assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, hu']

attribute [local instance] natTransCommShift_rightDerivedPlusCompTrans

/-- **`exactPrecompMap` commutes with the connecting morphisms**: for a short exact sequence `S`
of `𝒜'`, the connecting morphism of `R ⁱ(Q ∘ P)` along `S` followed by the map at `S.X₁` is the
map at `S.X₃` followed by the connecting morphism of `R ⁱQ` along `P(S)`. -/
theorem canonicalδ_comp_exactPrecompMap {S : ShortComplex A'} (hS : S.ShortExact) (q : ℕ) :
    canonicalδ (P ⋙ Q) hS q ≫
        (DerivedCategory.Plus.homologyFunctor B ((q + 1 : ℕ) : ℤ)).map
          (exactPrecompMap P Q S.X₁) =
      (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map (exactPrecompMap P Q S.X₃) ≫
        canonicalδ Q (hS.map_of_exact P) q := by
  have hPS := hS.map_of_exact P
  have hL := singleδPlus_comp_unitSingle P hPS hS (𝟙 _)
  simp only [ShortComplex.id_τ₁, ShortComplex.id_τ₃, CategoryTheory.Functor.map_id, id_comp]
    at hL
  have hL' : inv ((rightDerivedPlusUnitSingle P).app S.X₃) ≫ singleδPlus hPS =
      (derivedDeltaFunctorStructure P).δ hS ≫
        (inv ((rightDerivedPlusUnitSingle P).app S.X₁))⟦(1 : ℤ)⟧' := by
    rw [IsIso.inv_comp_eq, ← assoc, ← hL, assoc, ← CategoryTheory.Functor.map_comp,
      IsIso.hom_inv_id, CategoryTheory.Functor.map_id, comp_id]
  let φ : Triangle.mk
      ((DerivedCategory.Plus.singleFunctor A' 0 ⋙ (P ⋙ Q).rightDerivedFunctorPlus).map S.f)
      ((DerivedCategory.Plus.singleFunctor A' 0 ⋙ (P ⋙ Q).rightDerivedFunctorPlus).map S.g)
      ((derivedDeltaFunctorStructure (P ⋙ Q)).δ hS) ⟶
    Triangle.mk ((DerivedCategory.Plus.singleFunctor A 0 ⋙ Q.rightDerivedFunctorPlus).map
        (S.map P).f)
      ((DerivedCategory.Plus.singleFunctor A 0 ⋙ Q.rightDerivedFunctorPlus).map (S.map P).g)
      ((derivedDeltaFunctorStructure Q).δ hPS) :=
    Triangle.homMk _ _ (exactPrecompMap P Q S.X₁) (exactPrecompMap P Q S.X₂)
      (exactPrecompMap P Q S.X₃)
      (exactPrecompMap_naturality P Q S.f) (exactPrecompMap_naturality P Q S.g) (by
        dsimp only [Triangle.mk_mor₃, exactPrecompMap]
        rw [derivedDeltaFunctorStructure_δ_eq, derivedDeltaFunctorStructure_δ_eq]
        have hcQ := (Q.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.naturality
          (inv ((rightDerivedPlusUnitSingle P).app S.X₁))
        have hts := NatTrans.shift_app_comm (rightDerivedPlusCompTrans P Q) (1 : ℤ)
          ((DerivedCategory.Plus.singleFunctor A' 0).obj S.X₁)
        have hcomp := Functor.commShiftIso_comp_hom_app P.rightDerivedFunctorPlus
          Q.rightDerivedFunctorPlus (1 : ℤ) ((DerivedCategory.Plus.singleFunctor A' 0).obj S.X₁)
        have htn := (rightDerivedPlusCompTrans P Q).naturality (singleδPlus hS)
        simp only [Functor.comp_map, Functor.comp_obj] at hcQ hts hcomp htn
        rw [hcomp] at hts
        have key : Q.rightDerivedFunctorPlus.map (P.rightDerivedFunctorPlus.map (singleδPlus hS)) ≫
            Q.rightDerivedFunctorPlus.map ((P.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
              ((DerivedCategory.Plus.singleFunctor A' 0).obj S.X₁)) ≫
            Q.rightDerivedFunctorPlus.map
              ((inv ((rightDerivedPlusUnitSingle P).app S.X₁))⟦(1 : ℤ)⟧') =
          Q.rightDerivedFunctorPlus.map (inv ((rightDerivedPlusUnitSingle P).app S.X₃)) ≫
            Q.rightDerivedFunctorPlus.map (singleδPlus hPS) := by
          rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
            ← CategoryTheory.Functor.map_comp, ← assoc, ← derivedDeltaFunctorStructure_δ_eq, ← hL']
        rw [CategoryTheory.Functor.map_comp, assoc, reassoc_of% hts,
          ← assoc ((P ⋙ Q).rightDerivedFunctorPlus.map _), htn]
        simp only [assoc]
        rw [← hcQ, reassoc_of% key]
        rfl)
  exact (Functor.homologySequenceδ_naturality _ φ (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl).symm

section NatTrans

variable {A' B : Type*} [Category* A'] [Category* B] [Abelian A'] [Abelian B] [EnoughInjectives A']
  {F₁ F₂ : A' ⥤ B} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂)

/-- **The transformation of right derived functors induced by `τ : F₁ ⟶ F₂` commutes with the
connecting morphisms**: on cohomology of objects placed in degree zero it is a morphism of the
δ-functors `R ⁱF₁ ⟶ R ⁱF₂`. -/
theorem canonicalδ_comp_rightDerivedFunctorPlusNatTrans {S : ShortComplex A'}
    (hS : S.ShortExact) (q : ℕ) :
    canonicalδ F₁ hS q ≫
        (DerivedCategory.Plus.homologyFunctor B ((q + 1 : ℕ) : ℤ)).map
          ((rightDerivedFunctorPlusNatTrans τ).app
            ((DerivedCategory.Plus.singleFunctor A' 0).obj S.X₁)) =
      (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map
          ((rightDerivedFunctorPlusNatTrans τ).app
            ((DerivedCategory.Plus.singleFunctor A' 0).obj S.X₃)) ≫
        canonicalδ F₂ hS q := by
  have := natTransCommShift_rightDerivedFunctorPlusNatTrans τ
  let φ : Triangle.mk
      ((DerivedCategory.Plus.singleFunctor A' 0 ⋙ F₁.rightDerivedFunctorPlus).map S.f)
      ((DerivedCategory.Plus.singleFunctor A' 0 ⋙ F₁.rightDerivedFunctorPlus).map S.g)
      ((derivedDeltaFunctorStructure F₁).δ hS) ⟶
    Triangle.mk ((DerivedCategory.Plus.singleFunctor A' 0 ⋙ F₂.rightDerivedFunctorPlus).map S.f)
      ((DerivedCategory.Plus.singleFunctor A' 0 ⋙ F₂.rightDerivedFunctorPlus).map S.g)
      ((derivedDeltaFunctorStructure F₂).δ hS) :=
    Triangle.homMk _ _ ((rightDerivedFunctorPlusNatTrans τ).app _)
      ((rightDerivedFunctorPlusNatTrans τ).app _) ((rightDerivedFunctorPlusNatTrans τ).app _)
      ((rightDerivedFunctorPlusNatTrans τ).naturality _)
      ((rightDerivedFunctorPlusNatTrans τ).naturality _) (by
        dsimp only [Triangle.mk_mor₃]
        rw [derivedDeltaFunctorStructure_δ_eq, derivedDeltaFunctorStructure_δ_eq, assoc,
          NatTrans.shift_app_comm, ← assoc, ← assoc,
          (rightDerivedFunctorPlusNatTrans τ).naturality])
  exact (Functor.homologySequenceδ_naturality _ φ (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl).symm

end NatTrans

end Stacks.DerivedIndexing

end
