module

public import StacksFrontier.Homology.DerivedIndexing.UnitSingleDelta

/-!
# A comparison of right derived functors through an intermediate functor and the connecting
morphisms

Let `G : 𝒜' ⥤ 𝒜`, `F : 𝒜 ⥤ ℬ` and `K : 𝒜' ⥤ ℬ` be additive functors between abelian categories,
`𝒜` and `𝒜'` with enough injectives, and `Θ : RG ⋙ RF ⟶ RK` a transformation of right derived
functors on bounded below derived categories commuting with the shift. For `φ : M ⟶ G X'` the
composite

`RF(M[0]) ⟶ RF(G(X')[0]) ⟶ RF(RG(X'[0])) ⟶ RK(X'[0])`

induces maps `R ⁱF(M) ⟶ R ⁱK(X')`. For a short exact sequence `S` of `𝒜`, one `S'` of `𝒜'` and
a morphism of short complexes `μ : S ⟶ G(S')`, these maps commute with the connecting morphisms.
In the geometric application `G = g'_*`, `F = f_*`, `K = (f' ∘ g)_*` for a commutative square of
schemes, and the maps are the base change maps of higher direct images.

## Main definitions

* `Stacks.DerivedIndexing.derivedPairMap`: the map `RF(M[0]) ⟶ RK(X'[0])` attached to
  `φ : M ⟶ G X'`.

## Main results

* `Stacks.DerivedIndexing.derivedPairMap_naturality`: naturality in the pair.
* `Stacks.DerivedIndexing.canonicalδ_comp_derivedPairMap`: **compatibility with the connecting
  morphisms.**
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

namespace Stacks.DerivedIndexing

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] Functor.commShiftRightDerivedFunctorPlus
  Functor.natTransCommShiftRightDerivedFunctorPlusUnit
  Functor.isTriangulated_rightDerivedFunctorPlus

variable {A A' B : Type*} [Category* A] [Category* A'] [Category* B] [Abelian A] [Abelian A']
  [Abelian B] [EnoughInjectives A] [EnoughInjectives A'] (G : A' ⥤ A) (F : A ⥤ B) (K : A' ⥤ B)
  [G.Additive] [F.Additive] [K.Additive]
  (Θ : G.rightDerivedFunctorPlus ⋙ F.rightDerivedFunctorPlus ⟶ K.rightDerivedFunctorPlus)

/-- The map `RF(M[0]) ⟶ RK(X'[0])` attached to `φ : M ⟶ G X'`: `RF` of `φ` followed by the
canonical map `G(X')[0] ⟶ RG(X'[0])`, then `Θ`. -/
def derivedPairMap {M : A} {X' : A'} (φ : M ⟶ G.obj X') :
    F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj M) ⟶
      K.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A' 0).obj X') :=
  F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map φ ≫
      (rightDerivedPlusUnitSingle G).app X') ≫
    Θ.app ((DerivedCategory.Plus.singleFunctor A' 0).obj X')

/-- **`derivedPairMap` is natural in the pair.** -/
theorem derivedPairMap_naturality {M N : A} {X' Y' : A'} (φ : M ⟶ G.obj X')
    (ψ : N ⟶ G.obj Y') (a : M ⟶ N) (a' : X' ⟶ Y') (h : a ≫ ψ = φ ≫ G.map a') :
    F.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map a) ≫
        derivedPairMap G F K Θ ψ =
      derivedPairMap G F K Θ φ ≫
        K.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A' 0).map a') := by
  have hu := (rightDerivedPlusUnitSingle G).naturality a'
  have hΘ := Θ.naturality ((DerivedCategory.Plus.singleFunctor A' 0).map a')
  simp only [Functor.comp_map] at hu hΘ
  have e : (DerivedCategory.Plus.singleFunctor A 0).map a ≫
      (DerivedCategory.Plus.singleFunctor A 0).map ψ ≫ (rightDerivedPlusUnitSingle G).app Y' =
      ((DerivedCategory.Plus.singleFunctor A 0).map φ ≫ (rightDerivedPlusUnitSingle G).app X') ≫
        G.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor A' 0).map a') := by
    rw [← Functor.map_comp_assoc, h, Functor.map_comp, assoc, hu, assoc]
  dsimp only [derivedPairMap]
  rw [← Functor.map_comp_assoc, assoc, e, Functor.map_comp, assoc, hΘ]

variable [NatTrans.CommShift Θ ℤ]

/-- The connecting morphism of `derivedDeltaFunctorStructure H` is `RH` of the connecting morphism
of `D⁺` followed by the shift comparison. -/
private theorem derivedDeltaFunctorStructure_δ {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [EnoughInjectives C] (H : C ⥤ D) [H.Additive] {S : ShortComplex C}
    (hS : S.ShortExact) : (derivedDeltaFunctorStructure H).δ hS = H.rightDerivedFunctorPlus.map
      (singleδPlus hS) ≫ (H.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj S.X₁) := rfl

/-- **`derivedPairMap` commutes with the connecting morphisms**: for short exact sequences `S` of
`𝒜` and `S'` of `𝒜'` and `μ : S ⟶ G(S')`, the connecting morphism of `R ⁱF` along `S` followed by
the map attached to `μ.τ₁` is the map attached to `μ.τ₃` followed by the connecting morphism of
`R ⁱK` along `S'`. -/
theorem canonicalδ_comp_derivedPairMap {S : ShortComplex A} (hS : S.ShortExact)
    {S' : ShortComplex A'} (hS' : S'.ShortExact) (μ : S ⟶ S'.map G) (q : ℕ) :
    canonicalδ F hS q ≫
        (DerivedCategory.Plus.homologyFunctor B ((q + 1 : ℕ) : ℤ)).map
          (derivedPairMap G F K Θ μ.τ₁) =
      (DerivedCategory.Plus.homologyFunctor B (q : ℤ)).map (derivedPairMap G F K Θ μ.τ₃) ≫
        canonicalδ K hS' q := by
  have hL := singleδPlus_comp_unitSingle G hS hS' μ
  let φ : Triangle.mk ((DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus).map S.f)
      ((DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus).map S.g)
      ((derivedDeltaFunctorStructure F).δ hS) ⟶
    Triangle.mk ((DerivedCategory.Plus.singleFunctor A' 0 ⋙ K.rightDerivedFunctorPlus).map S'.f)
      ((DerivedCategory.Plus.singleFunctor A' 0 ⋙ K.rightDerivedFunctorPlus).map S'.g)
      ((derivedDeltaFunctorStructure K).δ hS') :=
    Triangle.homMk _ _ (derivedPairMap G F K Θ μ.τ₁) (derivedPairMap G F K Θ μ.τ₂)
      (derivedPairMap G F K Θ μ.τ₃)
      (derivedPairMap_naturality G F K Θ μ.τ₁ μ.τ₂ S.f S'.f μ.comm₁₂.symm)
      (derivedPairMap_naturality G F K Θ μ.τ₂ μ.τ₃ S.g S'.g μ.comm₂₃.symm) (by
        dsimp only [Triangle.mk_mor₃, derivedPairMap]
        rw [derivedDeltaFunctorStructure_δ F hS,
          derivedDeltaFunctorStructure_δ K hS']
        have hcF := (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.naturality
          ((DerivedCategory.Plus.singleFunctor A 0).map μ.τ₁ ≫
            (rightDerivedPlusUnitSingle G).app S'.X₁)
        have hΘs := NatTrans.shift_app_comm Θ (1 : ℤ)
          ((DerivedCategory.Plus.singleFunctor A' 0).obj S'.X₁)
        have hcomp := Functor.commShiftIso_comp_hom_app G.rightDerivedFunctorPlus
          F.rightDerivedFunctorPlus (1 : ℤ) ((DerivedCategory.Plus.singleFunctor A' 0).obj S'.X₁)
        have hΘn := Θ.naturality (singleδPlus hS')
        simp only [Functor.comp_map, Functor.comp_obj] at hcF hΘs hcomp hΘn
        rw [hcomp, assoc] at hΘs
        rw [Functor.map_comp, assoc, ← assoc ((Functor.commShiftIso _ _).hom.app _), ← hcF, assoc,
          ← Functor.map_comp_assoc, hL, Functor.map_comp, assoc,
          derivedDeltaFunctorStructure_δ G hS', Functor.map_comp, assoc,
          Functor.map_comp, assoc, hΘs,
          ← assoc (F.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlus.map _)), hΘn]
        simp only [assoc])
  exact (Functor.homologySequenceδ_naturality _ φ (q : ℤ) ((q + 1 : ℕ) : ℤ) rfl).symm

end Stacks.DerivedIndexing
