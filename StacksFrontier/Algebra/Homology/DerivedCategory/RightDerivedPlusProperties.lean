module

public import StacksFrontier.Homology.DerivedIndexing.CoEdgeDelta

/-!
# Properties of the higher right derived functors of a left exact functor

Let `𝒜` be an abelian category with enough injectives and let `F : 𝒜 ⥤ ℬ` be a left exact
functor to an abelian category. With `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` its right derived functor and
`R ⁱ F = H ⁱ ∘ RF ∘ (·[0])` its higher right derived functors, this file collects the four
standard properties of [Stacks, Tag 015B]:

1. a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of bounded below complexes gives a long exact
   sequence `⋯ ⟶ H ⁱ(RF(A)) ⟶ H ⁱ(RF(B)) ⟶ H ⁱ(RF(C)) ⟶ H ⁱ⁺¹(RF(A)) ⟶ ⋯`;
2. `R ⁱ F = 0` for `i < 0` and `R ⁰ F ≅ F`;
3. `R ⁱ F (I) = 0` for `i > 0` and `I` injective;
4. the `R ⁱ F`, with their connecting morphisms, form a universal `δ`-functor.

## Main results

* `CategoryTheory.Functor.exists_δ_exact_homology_rightDerivedFunctorPlus`: part (1), for any
  additive `F`.
* `CategoryTheory.Functor.rightDerivedPlus_properties`: the four parts together.

## References

* [Stacks, Tag 015B](https://stacks.math.columbia.edu/tag/015B)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace CategoryTheory.Functor

open _root_.DerivedCategory

section Triangle

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]

/-- A short exact sequence of bounded below complexes gives a distinguished triangle of
`D⁺(𝒜)`: the triangle `DerivedCategory.triangleOfSES` read in the full subcategory `D⁺(𝒜)`. -/
private lemma exists_distTriang_plusQ (S : ShortComplex (CochainComplex.Plus A))
    (hS : (S.map (CochainComplex.Plus.ι A)).ShortExact) :
    ∃ δ, Triangle.mk (Plus.Q.map S.f) (Plus.Q.map S.g) δ ∈ distTriang (DerivedCategory.Plus A) := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Plus.Q.obj S.X₃ ⟶ (Plus.Q.obj S.X₁)⟦(1 : ℤ)⟧,
      Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app (Plus.Q.obj S.X₁) =
        triangleOfSESδ hS :=
    ⟨Plus.ι.preimage (triangleOfSESδ hS ≫ (Plus.ι.commShiftIso (1 : ℤ)).inv.app
      (Plus.Q.obj S.X₁)), by
        rw [Functor.map_preimage]
        exact (Iso.eq_comp_inv ((Plus.ι.commShiftIso (1 : ℤ)).app (Plus.Q.obj S.X₁))).1 rfl⟩
  refine ⟨δ, ?_⟩
  rw [← Plus.ι.map_distinguished_iff]
  refine isomorphic_distinguished _ (triangleOfSES_distinguished hS) _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change (Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app (Plus.Q.obj S.X₁)) ≫
        (shiftFunctor (DerivedCategory A) (1 : ℤ)).map (𝟙 (Q.obj S.X₁.obj)) =
      𝟙 (Q.obj S.X₃.obj) ≫ triangleOfSESδ hS
    exact (congrArg (fun v ↦ (Plus.ι.map δ ≫ (Plus.ι.commShiftIso (1 : ℤ)).hom.app
          (Plus.Q.obj S.X₁)) ≫ v)
        (CategoryTheory.Functor.map_id (shiftFunctor (DerivedCategory A) (1 : ℤ))
          (Q.obj S.X₁.obj))).trans
      ((Category.comp_id _).trans (hδ.trans (Category.id_comp _).symm))

end Triangle

section LongExact

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive] [EnoughInjectives A]

attribute [local instance] commShiftRightDerivedFunctorPlus isTriangulated_rightDerivedFunctorPlus

/-- **The long exact sequence of `RF`** ([Stacks, Tag 015B] (1)). Let `F : 𝒜 ⥤ ℬ` be an additive
functor between abelian categories, `𝒜` with enough injectives. A short exact sequence
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` of bounded below complexes of `𝒜` gives a long exact sequence
`⋯ ⟶ H ⁱ(RF(K₁)) ⟶ H ⁱ(RF(K₂)) ⟶ H ⁱ(RF(K₃)) ⟶ H ⁱ⁺¹(RF(K₁)) ⟶ ⋯`: there are morphisms
`δ ⁱ : H ⁱ(RF(K₃)) ⟶ H ⁱ⁺¹(RF(K₁))` making it exact at every term. -/
theorem exists_δ_exact_homology_rightDerivedFunctorPlus
    (S : ShortComplex (CochainComplex.Plus A))
    (hS : (S.map (CochainComplex.Plus.ι A)).ShortExact) :
    ∃ δ : ∀ i : ℤ,
        (Plus.homologyFunctor B i).obj (F.rightDerivedFunctorPlus.obj (Plus.Q.obj S.X₃)) ⟶
        (Plus.homologyFunctor B (i + 1)).obj (F.rightDerivedFunctorPlus.obj (Plus.Q.obj S.X₁)),
      ∀ i : ℤ,
        (∃ hz : (Plus.homologyFunctor B i).map (F.rightDerivedFunctorPlus.map (Plus.Q.map S.f)) ≫
            (Plus.homologyFunctor B i).map (F.rightDerivedFunctorPlus.map (Plus.Q.map S.g)) = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
        (∃ hz : (Plus.homologyFunctor B i).map
            (F.rightDerivedFunctorPlus.map (Plus.Q.map S.g)) ≫ δ i = 0,
          (ShortComplex.mk _ _ hz).Exact) ∧
        (∃ hz : δ i ≫ (Plus.homologyFunctor B (i + 1)).map
            (F.rightDerivedFunctorPlus.map (Plus.Q.map S.f)) = 0,
          (ShortComplex.mk _ _ hz).Exact) := by
  obtain ⟨δ, hT⟩ := exists_distTriang_plusQ S hS
  let T := F.rightDerivedFunctorPlus.mapTriangle.obj
    (Triangle.mk (Plus.Q.map S.f) (Plus.Q.map S.g) δ)
  have hT' : T ∈ distTriang _ := F.rightDerivedFunctorPlus.map_distinguished _ hT
  exact ⟨fun i ↦ (Plus.homologyFunctor B 0).homologySequenceδ T i (i + 1) rfl, fun i ↦
    ⟨⟨_, (Plus.homologyFunctor B 0).homologySequence_exact₂ T hT' i⟩,
      ⟨_, (Plus.homologyFunctor B 0).homologySequence_exact₃ T hT' i (i + 1) rfl⟩,
      ⟨_, (Plus.homologyFunctor B 0).homologySequence_exact₁ T hT' i (i + 1) rfl⟩⟩⟩

end LongExact

section Properties

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]

/-- **The higher right derived functors of a left exact functor** ([Stacks, Tag 015B]). Let `𝒜`
be an abelian category with enough injectives and `F : 𝒜 ⥤ ℬ` a left exact functor to an abelian
category, with right derived functor `RF : D⁺(𝒜) ⥤ D⁺(ℬ)` and higher right derived functors
`R ⁱ F = H ⁱ ∘ RF ∘ (·[0])`.
1. A short exact sequence `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` of bounded below complexes of `𝒜` gives a long
   exact sequence `⋯ ⟶ H ⁱ(RF(K₁)) ⟶ H ⁱ(RF(K₂)) ⟶ H ⁱ(RF(K₃)) ⟶ H ⁱ⁺¹(RF(K₁)) ⟶ ⋯`.
2. `R ⁱ F = 0` for `i < 0`, and `R ⁰ F ≅ F`.
3. `R ⁱ F (I) = 0` for `i > 0` and `I` injective.
4. The `R ⁱ F`, `i ≥ 0`, with the connecting morphisms of the distinguished triangles of short
   exact sequences (`Stacks.DerivedIndexing.plusDelta`), form a universal `δ`-functor
   ([Stacks, Tag 010S]).

Part (2) is `Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj` and
`Stacks.RightDerivedPlus.rightDerivedPlusZeroIso` ([Stacks, Tag 05TD]); part (3) is
`CategoryTheory.Functor.isZero_rightDerivedPlus_obj_injective`; part (4) is Grothendieck's
criterion `CategoryTheory.DeltaFunctor.isUniversal_of_effaceable` ([Stacks, Tag 010T]) applied
to the effaceable `δ`-functor `Stacks.DerivedIndexing.plusDelta F`. -/
@[stacks 015B]
theorem rightDerivedPlus_properties :
    (∀ (S : ShortComplex (CochainComplex.Plus A))
        (_ : (S.map (CochainComplex.Plus.ι A)).ShortExact),
      ∃ δ : ∀ i : ℤ,
          (Plus.homologyFunctor B i).obj (F.rightDerivedFunctorPlus.obj (Plus.Q.obj S.X₃)) ⟶
          (Plus.homologyFunctor B (i + 1)).obj (F.rightDerivedFunctorPlus.obj (Plus.Q.obj S.X₁)),
        ∀ i : ℤ,
          (∃ hz : (Plus.homologyFunctor B i).map
                (F.rightDerivedFunctorPlus.map (Plus.Q.map S.f)) ≫
              (Plus.homologyFunctor B i).map (F.rightDerivedFunctorPlus.map (Plus.Q.map S.g)) = 0,
            (ShortComplex.mk _ _ hz).Exact) ∧
          (∃ hz : (Plus.homologyFunctor B i).map
              (F.rightDerivedFunctorPlus.map (Plus.Q.map S.g)) ≫ δ i = 0,
            (ShortComplex.mk _ _ hz).Exact) ∧
          (∃ hz : δ i ≫ (Plus.homologyFunctor B (i + 1)).map
              (F.rightDerivedFunctorPlus.map (Plus.Q.map S.f)) = 0,
            (ShortComplex.mk _ _ hz).Exact)) ∧
      ((∀ i < 0, ∀ X : A, IsZero ((F.rightDerivedPlus i).obj X)) ∧
        Nonempty (F.rightDerivedPlus 0 ≅ F)) ∧
      (∀ i : ℤ, 0 < i → ∀ (I : A), Injective I → IsZero ((F.rightDerivedPlus i).obj I)) ∧
      ((∀ n : ℕ, (Stacks.DerivedIndexing.plusDelta F).functor n = F.rightDerivedPlus n) ∧
        (Stacks.DerivedIndexing.plusDelta F).IsUniversal) :=
  ⟨fun S hS ↦ F.exists_δ_exact_homology_rightDerivedFunctorPlus S hS,
    ⟨fun i hi X ↦ Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj F i hi X,
      ⟨Stacks.RightDerivedPlus.rightDerivedPlusZeroIso F⟩⟩,
    fun i hi I _ ↦ F.isZero_rightDerivedPlus_obj_injective i hi.ne' I,
    ⟨fun _ ↦ rfl, DeltaFunctor.isUniversal_of_effaceable _⟩⟩

end Properties

end CategoryTheory.Functor
