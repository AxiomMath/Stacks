module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KernelColocalization

/-!
# Recognizing the left orthogonal `𝒜` of `D_{𝓟 ∩ 𝓛}(A)` in `D_𝓛(A)`

In the setting of `DerivedCategory.KernelColocalization` — weak Serre classes `𝓟`, `𝓛` of an
abelian category `A`, a triangulated functor `G` out of `D(A)` whose kernel is `D_𝓟(A)`, with a
fully faithful left adjoint `L` preserving `D_𝓛(A)` — every object `K` of `D_𝓛(A)` sits in the
canonical triangle `L G K ⟶ K ⟶ P ⟶` with `P` in `D_{𝓟 ∩ 𝓛}(A)` and `L G K` in the left
orthogonal `𝒜 = interLeftOrthogonal 𝓟 𝓛`.

This file gives a criterion for a triangulated, isomorphism-closed subcategory `Q` of `D(A)` to
be `𝒜`: `Q` must lie in `D_𝓛(A)`, contain every `L G K` for `K` in `D_𝓛(A)`, and meet
`D_{𝓟 ∩ 𝓛}(A)` only in zero objects. The proof is the canonical triangle: for `K` in `Q` or in
`𝒜` its third term lies in `Q`, resp. `𝒜`, by the two-out-of-three property, and in
`D_{𝓟 ∩ 𝓛}(A)`; it is therefore zero, so `K ≅ L G K`.

This is the shape of the proof of **Stacks 0H16**, where `Q` is the image `Q_𝒳` of `QC(𝒳)`.

## Main results

* `DerivedCategory.KernelColocalization.eq_interLeftOrthogonal_of_isZero_of_derivedInter`.

## References

* [Stacks Project, Tag 07BA](https://stacks.math.columbia.edu/tag/07BA)
* [Stacks Project, Tag 0H11](https://stacks.math.columbia.edu/tag/0H11)
* [Stacks Project, Tag 0H16](https://stacks.math.columbia.edu/tag/0H16)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

namespace DerivedCategory.KernelColocalization

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (𝓟 𝓛 : ObjectProperty A)
  [𝓟.IsWeakSerreClass] [𝓛.IsWeakSerreClass]
  {D' : Type*} [Category D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
  {G : DerivedCategory A ⥤ D'} [G.CommShift ℤ] [G.IsTriangulated]
  {Lsh : D' ⥤ DerivedCategory A} (adj : Lsh ⊣ G)

/-- **A triangulated subcategory of `D(A)` is `𝒜` as soon as it lies in `D_𝓛(A)`, contains the
image `L G K` of every object `K` of `D_𝓛(A)`, and meets `D_{𝓟 ∩ 𝓛}(A)` only in zero objects.**

For `K` in `Q` or in `𝒜`, the cone `P` of the counit `L G K ⟶ K` lies in `D_{𝓟 ∩ 𝓛}(A)`
(`derivedInter_obj₃_of_distTriang`) and, by the two-out-of-three property, in `Q`, resp. in `𝒜`;
an object of `𝒜` lying in `D_{𝓟 ∩ 𝓛}(A)` is zero, as is one of `Q` by hypothesis. So the counit
is an isomorphism and `K ≅ L G K`, which lies in both. -/
theorem eq_interLeftOrthogonal_of_isZero_of_derivedInter
    (hG : ∀ K, IsZero (G.obj K) ↔ ∀ n : ℤ, 𝓟 ((homologyFunctor A n).obj K))
    (hunit : IsIso adj.unit)
    (hshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      DerivedCategoryB.derivedCategoryB 𝓛 (Lsh.obj (G.obj K)))
    (Q : ObjectProperty (DerivedCategory A)) [Q.IsClosedUnderIsomorphisms] [Q.IsTriangulated]
    (hQ : Q ≤ DerivedCategoryB.derivedCategoryB 𝓛)
    (hQshriek : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K → Q (Lsh.obj (G.obj K)))
    (hQzero : ∀ K, Q K → derivedInter 𝓟 𝓛 K → IsZero K) :
    Q = interLeftOrthogonal 𝓟 𝓛 := by
  obtain ⟨-, -, hA⟩ := isSaturated_interLeftOrthogonal 𝓟 𝓛
  have tri : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      ∃ (P : DerivedCategory A) (b : K ⟶ P) (c : P ⟶ (Lsh.obj (G.obj K))⟦(1 : ℤ)⟧),
        Triangle.mk (adj.counit.app K) b c ∈ distTriang (DerivedCategory A) ∧
          derivedInter 𝓟 𝓛 P := fun K hK => by
    obtain ⟨P, b, c, hT⟩ := distinguished_cocone_triangle (adj.counit.app K)
    exact ⟨P, b, c, hT,
      derivedInter_obj₃_of_distTriang 𝓟 𝓛 adj hG hunit K hK (hshriek K hK) P b c hT⟩
  have hLG : ∀ K, DerivedCategoryB.derivedCategoryB 𝓛 K →
      interLeftOrthogonal 𝓟 𝓛 (Lsh.obj (G.obj K)) := fun K hK =>
    ⟨leftOrthogonal_obj_counit 𝓟 𝓛 adj hG K, hshriek K hK⟩
  ext K
  refine ⟨fun hK => ?_, fun hK => ?_⟩
  · obtain ⟨P, b, c, hT, hP⟩ := tri K (hQ K hK)
    have hPQ : Q P := Q.ext_of_isTriangulatedClosed₃ _ hT (hQshriek K (hQ K hK)) hK
    have : IsIso (adj.counit.app K) :=
      (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hQzero P hPQ hP)
    exact (interLeftOrthogonal 𝓟 𝓛).prop_of_iso (asIso (adj.counit.app K)) (hLG K (hQ K hK))
  · obtain ⟨P, b, c, hT, hP⟩ := tri K hK.2
    have hPA : interLeftOrthogonal 𝓟 𝓛 P :=
      (interLeftOrthogonal 𝓟 𝓛).ext_of_isTriangulatedClosed₃ _ hT (hLG K hK.2) hK
    have : IsIso (adj.counit.app K) :=
      (Triangle.isZero₃_iff_isIso₁ _ hT).1 ((IsZero.iff_id_eq_zero P).2 (hPA.1 (𝟙 P) hP))
    exact Q.prop_of_iso (asIso (adj.counit.app K)) (hQshriek K hK.2)

end DerivedCategory.KernelColocalization

end
