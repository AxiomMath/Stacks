module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective.Exactness
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The right derived functor on `D⁺` as an exact functor and as a `δ`-functor

Let `𝒜` be an abelian category with enough injectives, let `F : 𝒜 ⥤ ℬ` be an additive functor,
and let `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` be a right derived functor of `K⁺(F) ⋙ Q⁺_ℬ` along the localization
`Q⁺_𝒜 : K⁺(𝒜) ⥤ D⁺(𝒜)`, with unit `α` and with its commutation with the shift. This file collects
the four ways in which `RF` is exact ([Stacks, Tag 0159]):

1. `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is an exact functor of triangulated categories;
2. the composite `K⁺(𝒜) ⥤ D⁺(𝒜) ⥤ D⁺(ℬ)` is an exact functor;
3. the composite `Comp⁺(𝒜) ⥤ D⁺(𝒜) ⥤ D⁺(ℬ)` is a `δ`-functor;
4. the composite `𝒜 ⥤ D⁺(𝒜) ⥤ D⁺(ℬ)`, `A ↦ RF(A[0])`, is a `δ`-functor.

Part (1) is
`CategoryTheory.Functor.isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus`.
Part (2) follows because `Q⁺_𝒜` is exact. For part (3), the localization functor
`Q⁺ : Comp⁺(𝒜) ⥤ D⁺(𝒜)` carries the `δ`-functor structure
`DerivedCategory.Plus.deltaFunctorStructure` whose connecting morphism
`DerivedCategory.Plus.triangleOfSESδ` is the canonical one `-p ∘ q⁻¹` of [Stacks, Tag 0152]
read in `D⁺(𝒜)`; composing with the exact functor `RF` gives a `δ`-functor
([Stacks, Tag 0151]). For part (4), the functor `A ↦ A[0] : 𝒜 ⥤ D⁺(𝒜)` carries the
`δ`-functor structure `Stacks.DerivedIndexing.singleDeltaFunctorStructure`, and again one
composes with `RF`.

## Main results

* `DerivedCategory.Plus.deltaFunctorStructure`: the `δ`-functor structure on
  `Q⁺ : Comp⁺(𝒜) ⥤ D⁺(𝒜)`.
* `CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus_and_deltaFunctorStructure`:
  [Stacks, Tag 0159], all four parts, for `RF = F.rightDerivedFunctorPlus`.
* `CategoryTheory.Functor.isTriangulated_and_deltaFunctorStructure_of_isRightDerivedFunctor`:
  the same for any right derived functor `RF` with unit `α` and a compatible commutation with
  the shift.

## Implementation notes

`Comp⁺(𝒜)` is Mathlib's `CochainComplex.Plus 𝒜`, the full subcategory of bounded below
complexes. A short exact sequence in it is one in the sense of that category; since the
subcategory is closed under finite limits and colimits, its inclusion into all complexes is
exact and carries such a sequence to a short exact sequence of complexes
(`DerivedCategory.Plus.shortExact_map_ι`), to which Mathlib's `DerivedCategory.triangleOfSESδ`
applies.

`CategoryTheory.Functor.DeltaFunctorStructure.comp` asks for an abelian source category, an
instance `CochainComplex.Plus 𝒜` does not carry, so in part (3) the composite with `RF` is built
by the same argument directly; in part (4) that construction is used as is.

In parts (3) and (4) a `δ`-functor structure is data, and the source means the one induced by
`RF`; the statement therefore asserts the existence of a `δ`-functor structure together with the
equation identifying its connecting morphism with `RF` applied to the canonical connecting
morphism, followed by the commutation of `RF` with the shift.

## References

* [Stacks, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
* [Stacks, Tag 0152](https://stacks.math.columbia.edu/tag/0152)
* [Stacks, Tag 0151](https://stacks.math.columbia.edu/tag/0151)
-/

@[expose] public section

universe w w₁ w₂ v v₁ v₂ u u₁ u₂

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {S : ShortComplex (CochainComplex.Plus C)}

omit [HasDerivedCategory C] in
/-- A short exact sequence of bounded below complexes is a short exact sequence of complexes:
the inclusion of bounded below complexes preserves finite limits and finite colimits. -/
lemma shortExact_map_ι (hS : S.ShortExact) : (S.map (CochainComplex.Plus.ι C)).ShortExact :=
  have : (CochainComplex.plus C).IsClosedUnderFiniteLimits := {}
  have : (CochainComplex.plus C).IsClosedUnderFiniteColimits := {}
  hS.map_of_exact _

/-- The connecting morphism `Q⁺(C^•) ⟶ Q⁺(A^•)⟦1⟧` attached to a short exact sequence
`0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` of bounded below complexes: the canonical connecting morphism
`DerivedCategory.triangleOfSESδ = -p ∘ q⁻¹` of the derived category, read in `D⁺`. -/
noncomputable def triangleOfSESδ (hS : S.ShortExact) :
    Q.obj S.X₃ ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
  ι.preimage (DerivedCategory.triangleOfSESδ (shortExact_map_ι hS) ≫
    (ι.commShiftIso (1 : ℤ)).inv.app (Q.obj S.X₁))

/-- The defining property of `DerivedCategory.Plus.triangleOfSESδ`. -/
lemma ι_map_triangleOfSESδ (hS : S.ShortExact) :
    ι.map (triangleOfSESδ hS) ≫ (ι.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁) =
      DerivedCategory.triangleOfSESδ (shortExact_map_ι hS) :=
  (congrArg (· ≫ (ι.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁)) (ι.map_preimage _)).trans
    ((assoc _ _ _).trans ((congrArg (DerivedCategory.triangleOfSESδ (shortExact_map_ι hS) ≫ ·)
      (Iso.inv_hom_id_app (ι.commShiftIso (1 : ℤ)) (Q.obj S.X₁))).trans (comp_id _)))

/-- The triangle `Q⁺(A^•) ⟶ Q⁺(B^•) ⟶ Q⁺(C^•) ⟶ Q⁺(A^•)⟦1⟧` of a short exact sequence of
bounded below complexes is distinguished. -/
lemma triangleOfSES_distinguished (hS : S.ShortExact) :
    Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS) ∈ distTriang (Plus C) := by
  rw [← ι.map_distinguished_iff]
  refine isomorphic_distinguished _
    (DerivedCategory.triangleOfSES_distinguished (shortExact_map_ι hS)) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · exact (comp_id _).trans (id_comp _).symm
  · exact (comp_id _).trans (id_comp _).symm
  · exact (congrArg (fun w ↦ (ι.map (triangleOfSESδ hS) ≫
          (ι.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁)) ≫ w)
        (CategoryTheory.Functor.map_id (shiftFunctor (DerivedCategory C) (1 : ℤ))
          (DerivedCategory.Q.obj S.X₁.obj))).trans
      ((comp_id _).trans ((ι_map_triangleOfSESδ hS).trans (id_comp _).symm))

/-- The connecting morphism `DerivedCategory.Plus.triangleOfSESδ` is natural in the short exact
sequence of bounded below complexes. -/
lemma triangleOfSESδ_naturality {S₁ S₂ : ShortComplex (CochainComplex.Plus C)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    triangleOfSESδ h₁ ≫ (Q.map φ.τ₁)⟦(1 : ℤ)⟧' = Q.map φ.τ₃ ≫ triangleOfSESδ h₂ := by
  apply ι.map_injective
  rw [Functor.map_comp, Functor.map_comp, ← cancel_mono
    ((ι.commShiftIso (1 : ℤ)).hom.app (Q.obj S₂.X₁)), assoc, assoc,
    Functor.commShiftIso_hom_naturality, ← assoc, ι_map_triangleOfSESδ h₁, ← assoc]
  have h := ι_map_triangleOfSESδ h₂
  rw [assoc, h]
  exact DerivedCategory.triangleOfSESδ_naturality (shortExact_map_ι h₁) (shortExact_map_ι h₂)
    ((CochainComplex.Plus.ι C).mapShortComplex.map φ)

/-- **The `δ`-functor `Comp⁺(𝒜) ⥤ D⁺(𝒜)`** ([Stacks, Tag 0152], bounded below case): the
localization functor `Q⁺` with the connecting morphisms `DerivedCategory.Plus.triangleOfSESδ`. -/
noncomputable def deltaFunctorStructure :
    Functor.DeltaFunctorStructure (CochainComplex.Plus C) (Plus C) Q where
  δ hS := triangleOfSESδ hS
  distinguished hS := triangleOfSES_distinguished hS
  δ_naturality h₁ h₂ φ := triangleOfSESδ_naturality h₁ h₂ φ

end DerivedCategory.Plus

namespace CategoryTheory.Functor

open _root_.DerivedCategory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
  [EnoughInjectives C] (RF : Plus C ⥤ Plus D)
  (α : F.mapHomotopyCategoryPlus ⋙ Plus.Qh ⟶ Plus.Qh ⋙ RF)

/-- The four exactness properties of [Stacks, Tag 0159], for an arbitrary right derived functor.
Let `𝒜` be an abelian category with enough injectives and let
`F : 𝒜 ⥤ ℬ` be an additive functor. Let `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` be a right derived functor of
`K⁺(F) ⋙ Q⁺_ℬ` along the localization `Q⁺_𝒜 : K⁺(𝒜) ⥤ D⁺(𝒜)` at the quasi-isomorphisms, with
unit `α` and a commutation with the shift compatible with `α`. Then

1. `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is an exact functor;
2. `RF` induces an exact functor `Q⁺_𝒜 ⋙ RF : K⁺(𝒜) ⥤ D⁺(ℬ)`;
3. `RF` induces a `δ`-functor `Q⁺ ⋙ RF : Comp⁺(𝒜) ⥤ D⁺(ℬ)`, whose connecting morphism on a
   short exact sequence `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` of bounded below complexes is `RF` of the
   canonical connecting morphism `Q⁺(C^•) ⟶ Q⁺(A^•)⟦1⟧` followed by `RF(Q⁺(A^•)⟦1⟧) ≅
   RF(Q⁺(A^•))⟦1⟧`;
4. `RF` induces a `δ`-functor `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`, whose connecting morphism on a short
   exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜` is `RF` of the connecting morphism
   `C[0] ⟶ A[0]⟦1⟧` followed by the commutation of `RF` with the shift.

The source's `RF` is the case `RF := F.rightDerivedFunctorPlus`,
`α := F.rightDerivedFunctorPlusUnit`, whose existence is [Stacks, Tag 05TI]; that case is
`CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus_and_deltaFunctorStructure`. -/
theorem isTriangulated_and_deltaFunctorStructure_of_isRightDerivedFunctor
    [RF.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso C)]
    [RF.CommShift ℤ] [NatTrans.CommShift α ℤ] :
    RF.IsTriangulated ∧ (Plus.Qh ⋙ RF).IsTriangulated ∧
    (∃ h : (Plus.Q ⋙ RF).DeltaFunctorStructure (CochainComplex.Plus C) (Plus D),
      ∀ {S : ShortComplex (CochainComplex.Plus C)} (hS : S.ShortExact),
        h.δ hS = RF.map (Plus.triangleOfSESδ hS) ≫
          (RF.commShiftIso (1 : ℤ)).hom.app (Plus.Q.obj S.X₁)) ∧
    (∃ h : (Plus.singleFunctor C 0 ⋙ RF).DeltaFunctorStructure C (Plus D),
      ∀ {S : ShortComplex C} (hS : S.ShortExact),
        h.δ hS = RF.map (Stacks.DerivedIndexing.singleδPlus hS) ≫
          (RF.commShiftIso (1 : ℤ)).hom.app ((Plus.singleFunctor C 0).obj S.X₁)) := by
  have := isTriangulated_of_isRightDerivedFunctor_mapHomotopyCategoryPlus F RF α
  refine ⟨this, inferInstance,
    ⟨{ δ hS := RF.map (Plus.triangleOfSESδ hS) ≫ (RF.commShiftIso (1 : ℤ)).hom.app (Plus.Q.obj _)
       distinguished hS := RF.map_distinguished _ (Plus.triangleOfSES_distinguished hS)
       δ_naturality h₁ h₂ φ := by
         have hξ := (RF.commShiftIso (1 : ℤ)).hom.naturality (Plus.Q.map φ.τ₁)
         simp only [Functor.comp_map] at hξ ⊢
         rw [Category.assoc, ← hξ, ← RF.map_comp_assoc, Plus.triangleOfSESδ_naturality h₁ h₂ φ,
           RF.map_comp_assoc] }, ?_⟩,
    ⟨(Stacks.DerivedIndexing.singleDeltaFunctorStructure (C := C)).comp RF, ?_⟩⟩
  · intro S hS
    rfl
  · intro S hS
    rfl

section RightDerivedFunctorPlus

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D] (F : C ⥤ D) [F.Additive]
  [EnoughInjectives C]

attribute [local instance] commShiftRightDerivedFunctorPlus

/-- **Stacks 0159.** Let `𝒜` be an abelian category with enough injectives and let
`F : 𝒜 ⥤ ℬ` be an additive functor, with right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`
(`F.rightDerivedFunctorPlus`, everywhere defined by [Stacks, Tag 05TI]) and its commutation with
the shift induced by the universal property (`commShiftRightDerivedFunctorPlus`). Then

1. `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` is an exact functor;
2. `RF` induces an exact functor `Q⁺_𝒜 ⋙ RF : K⁺(𝒜) ⥤ D⁺(ℬ)`;
3. `RF` induces a `δ`-functor `Q⁺ ⋙ RF : Comp⁺(𝒜) ⥤ D⁺(ℬ)`, whose connecting morphism on a
   short exact sequence `0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0` of bounded below complexes is `RF` of the
   canonical connecting morphism `Q⁺(C^•) ⟶ Q⁺(A^•)⟦1⟧` of [Stacks, Tag 0152] followed by
   `RF(Q⁺(A^•)⟦1⟧) ≅ RF(Q⁺(A^•))⟦1⟧`;
4. `RF` induces a `δ`-functor `A ↦ RF(A[0]) : 𝒜 ⥤ D⁺(ℬ)`, whose connecting morphism on a short
   exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of `𝒜` is `RF` of the connecting morphism
   `C[0] ⟶ A[0]⟦1⟧` followed by the commutation of `RF` with the shift. -/
@[stacks 0159]
theorem isTriangulated_rightDerivedFunctorPlus_and_deltaFunctorStructure :
    F.rightDerivedFunctorPlus.IsTriangulated ∧
    (Plus.Qh ⋙ F.rightDerivedFunctorPlus).IsTriangulated ∧
    (∃ h : (Plus.Q ⋙ F.rightDerivedFunctorPlus).DeltaFunctorStructure (CochainComplex.Plus C)
        (Plus D),
      ∀ {S : ShortComplex (CochainComplex.Plus C)} (hS : S.ShortExact),
        h.δ hS = F.rightDerivedFunctorPlus.map (Plus.triangleOfSESδ hS) ≫
          (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app (Plus.Q.obj S.X₁)) ∧
    (∃ h : (Plus.singleFunctor C 0 ⋙ F.rightDerivedFunctorPlus).DeltaFunctorStructure C (Plus D),
      ∀ {S : ShortComplex C} (hS : S.ShortExact),
        h.δ hS = F.rightDerivedFunctorPlus.map (Stacks.DerivedIndexing.singleδPlus hS) ≫
          (F.rightDerivedFunctorPlus.commShiftIso (1 : ℤ)).hom.app
            ((Plus.singleFunctor C 0).obj S.X₁)) :=
  have := natTransCommShiftRightDerivedFunctorPlusUnit F
  isTriangulated_and_deltaFunctorStructure_of_isRightDerivedFunctor F _
    F.rightDerivedFunctorPlusUnith

end RightDerivedFunctorPlus

end CategoryTheory.Functor
