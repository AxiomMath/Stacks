module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.CohomologyActionTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCoproducts
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleCompact
public import StacksFrontier.CategoryTheory.Triangulated.Generators
public import StacksCore.Tactic.StacksAttribute

/-! # The derived tensor product with a compact bimodule is fully faithful

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. [Stacks, Tag 09R9] says that if

1. `N` defines a compact object of `D(B, d)`, and
2. the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` is an isomorphism for every `k ∈ ℤ`,

then the derived tensor product `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is fully faithful.

The functor has a right adjoint `RHom(N, -)` unconditionally, by [Stacks, Tag 09LT], and a left
adjoint is fully faithful exactly when the unit of the adjunction is invertible
(`CategoryTheory.Adjunction.fullyFaithfulLOfIsIsoUnit`, [Stacks, Tag 07RB]). So everything is a
statement about the unit
$$M \longrightarrow R\!\operatorname{Hom}(N, M \otimes_A^{\mathbf L} N),$$
and the objects `M` at which it is invertible are all of `D(A, d)` by the dévissage of
[Stacks, Tag 0FQE]: that class is closed under direct sums because `RHom(N, -)` commutes with
direct sums, which is hypothesis (1); it satisfies two-out-of-three in a distinguished triangle
because both `- ⊗_A^𝐋 N` and `RHom(N, -)` are exact; and it contains every shift `A[k]` of the
regular module, which is hypothesis (2).

## Main definitions

* `DifferentialGraded.Bimodule.derivedTensorFunctor_fullyFaithful`: **Stacks 09R9**.

## Main results

* `CategoryTheory.ObjectProperty.IsWeakTriangulatedGenerator.isIso_of_bijective_comp`: a weak
  generator detects invertibility — a morphism `b` is invertible as soon as postcomposition with
  `b` is bijective on morphisms out of the translates of a weak generator.
* `CategoryTheory.Adjunction.isIso_unit_app_sigma`,
  `CategoryTheory.Adjunction.isIso_unit_app_of_mem_distTriang`,
  `CategoryTheory.Adjunction.isIso_unit_app_shift_of_bijective_map`: the three dévissage clauses
  for the property "the unit of an adjunction is invertible at this object".
* `DifferentialGraded.Bimodule.isIso_unit_derivedTensorFunctor_adj_derivedHomFunctor`: under the
  two hypotheses of Tag 09R9, the unit of the adjunction of Tag 09LT is invertible.

## Implementation notes

*The three clauses, abstractly.* Write `F ⊣ G` with `F` exact and compatible with the
translation, and let the property in question be `IsIso (adj.unit.app X)`.

* *Direct sums.* A left adjoint preserves all colimits, so if `G` preserves the direct sums
  indexed by `ι` then so does `F ⋙ G`, and the unit at `∐ᵢ Kᵢ` is the direct sum of the units at
  the `Kᵢ` followed by the comparison `∐ᵢ (F ⋙ G) Kᵢ ⟶ (F ⋙ G) (∐ᵢ Kᵢ)`. Both factors are
  invertible.
* *Triangles.* The unit, read on a triangle `Δ`, is a morphism of triangles
  `Δ ⟶ (F ⋙ G).mapTriangle.obj Δ` — the third square is the compatibility of the unit with the
  translation (`CategoryTheory.Adjunction.unit_app_commShiftIso_hom_app`). Both triangles are
  distinguished, so the five lemma for pretriangulated categories gives each of the three
  implications.
* *Translates of a generator.* The unit at `X⟦k⟧` is the translate of the unit at `X` composed
  with an isomorphism, so the property is stable under the translation and only the case of `E`
  itself is at stake. There, postcomposition with `adj.unit.app E` on morphisms `P ⟶ E` is the
  hom-set bijection of the adjunction applied to `F`, so it is bijective exactly when `F` is
  bijective from `P ⟶ E` onto `F P ⟶ F E`; and when `E` is a weak generator, that bijectivity at
  every `P` isomorphic to a translate of `E` forces `adj.unit.app E` to be invertible, by
  completing it to a distinguished triangle and seeing that the third vertex receives only zero
  morphisms from the translates of `E`.

*Why hypothesis (2) is a bijectivity of `- ⊗_A^𝐋 N`.* The regular module represents cohomology
in `D(A, d)`, so hypothesis (2) says exactly that `- ⊗_A^𝐋 N` is bijective from
`Hom_{D(A,d)}(A, A[k])` onto `Hom_{D(B,d)}(N, N[k])`; this is
`DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_iff_shift`. Bijectivity
on `Hom(A, A[k])` for every `k` gives bijectivity on `Hom(A[n], A)` for every `n` by translating
by `n`, which is the form the weak-generator criterion consumes.

*Two pretriangulated structures on `K(A, d)`.* As in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomCoproducts.lean`, the imports bring both
`DifferentialGradedModule.instPretriangulatedHomotopyCategory` — whose distinguished triangles
are the cone triangles — and
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`, whose distinguished triangles
come from admissible short exact sequences. Everything about `D(A, d)` in this chapter is stated
against the primed one, and that is the one given priority below.

## References

* [Stacks Project, Tag 09R9](https://stacks.math.columbia.edu/tag/09R9), the result proved here.
* [Stacks Project, Tag 09LT](https://stacks.math.columbia.edu/tag/09LT) for the adjunction,
  [Tag 07RB](https://stacks.math.columbia.edu/tag/07RB) for the criterion of full faithfulness,
  [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE) for the dévissage,
  [Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ) for weak generators and
  [Tag 014A](https://stacks.math.columbia.edu/tag/014A) for the five lemma in a pretriangulated
  category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace CategoryTheory

universe w v₁ v₂ u₁ u₂

/-- The morphisms between two objects and the morphisms between their translates are in
bijection, the translation being an equivalence of categories. -/
private def shiftHomEquiv {E : Type*} [Category E] [HasShift E ℤ] (n : ℤ) (X Y : E) :
    (X ⟶ Y) ≃ ((X⟦n⟧ : E) ⟶ Y⟦n⟧) where
  toFun f := f⟦n⟧'
  invFun g := (shiftFunctor E n).preimage g
  left_inv _ := (shiftFunctor E n).map_injective (by rw [Functor.map_preimage])
  right_inv g := (shiftFunctor E n).map_preimage g

/-! ### Bijectivity of a functor on a morphism group -/

section BijectiveMap

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] (F : D ⥤ C)

/-- **Bijectivity of `F` on a morphism group is invariant under isomorphisms at both ends.** -/
theorem Functor.bijective_map_of_iso {X Y X' Y' : D} (eX : X ≅ X') (eY : Y ≅ Y')
    (h : Function.Bijective (fun f : X ⟶ Y => F.map f)) :
    Function.Bijective (fun f : X' ⟶ Y' => F.map f) := by
  have hfun : (fun f : X' ⟶ Y' => F.map f) ∘ (Iso.homCongr eX eY) =
      (Iso.homCongr (F.mapIso eX) (F.mapIso eY)) ∘ (fun f : X ⟶ Y => F.map f) := by
    funext f
    simp only [Function.comp_apply, Iso.homCongr_apply, Functor.mapIso_hom, Functor.mapIso_inv,
      Functor.map_comp]
  refine (Equiv.bijective_comp (Iso.homCongr eX eY) (fun f : X' ⟶ Y' => F.map f)).1 ?_
  rw [hfun]
  exact (Equiv.comp_bijective (fun f : X ⟶ Y => F.map f)
    (Iso.homCongr (F.mapIso eX) (F.mapIso eY))).2 h

variable [HasShift C ℤ] [HasShift D ℤ]

/-- **Bijectivity of `F` on a morphism group is inherited by the translates of both ends**, when
`F` commutes with the translation. -/
theorem Functor.bijective_map_shift [F.CommShift ℤ] (n : ℤ) {X Y : D}
    (h : Function.Bijective (fun f : X ⟶ Y => F.map f)) :
    Function.Bijective (fun f : (X⟦n⟧ : D) ⟶ Y⟦n⟧ => F.map f) := by
  have hfun : (fun f : (X⟦n⟧ : D) ⟶ Y⟦n⟧ => F.map f) ∘ (shiftHomEquiv n X Y) =
      ((shiftHomEquiv n (F.obj X) (F.obj Y)).trans
          (Iso.homCongr ((F.commShiftIso n).app X).symm ((F.commShiftIso n).app Y).symm)) ∘
        (fun f : X ⟶ Y => F.map f) := by
    funext f
    change F.map ((shiftFunctor D n).map f) = (F.commShiftIso n).hom.app X ≫
      (shiftFunctor C n).map (F.map f) ≫ (F.commShiftIso n).inv.app Y
    rw [← Category.assoc, ← F.commShiftIso_hom_naturality f n, Category.assoc,
      Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  refine (Equiv.bijective_comp (shiftHomEquiv n X Y)
    (fun f : (X⟦n⟧ : D) ⟶ Y⟦n⟧ => F.map f)).1 ?_
  rw [hfun]
  exact (Equiv.comp_bijective (fun f : X ⟶ Y => F.map f) _).2 h

end BijectiveMap

/-! ### A weak generator detects invertibility -/

section Detection

variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **A weak generator detects invertibility.** Let `E` be a weak generator of a pretriangulated
category `D` and let `b : K ⟶ X` be a morphism such that postcomposition with `b` is bijective
from `P ⟶ K` onto `P ⟶ X` for every object `P` isomorphic to a translate of `E`. Then `b` is an
isomorphism.

Complete `b` to a distinguished triangle `K → X → Z → K[1]`. A morphism `ξ : P ⟶ Z` out of a
translate of `E` is annihilated by `Z ⟶ K[1]`, because the composite `P ⟶ K[1] ⟶ X[1]` vanishes
and postcomposition with `b[1]` is injective on morphisms out of `P` — being, after translating
by `-1`, postcomposition with `b` on morphisms out of `P[-1]`, again a translate of `E`. So `ξ`
factors through `X`, hence through `b`, hence through the zero composite `K ⟶ X ⟶ Z`. Thus `Z`
receives only zero morphisms from the translates of `E`, so it vanishes and `b` is invertible. -/
theorem ObjectProperty.IsWeakTriangulatedGenerator.isIso_of_bijective_comp {E : D}
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) {K X : D} (b : K ⟶ X)
    (h : ∀ ⦃P : D⦄, ((ObjectProperty.singleton E).shiftClosure ℤ) P →
      Function.Bijective (fun f : P ⟶ K => f ≫ b)) :
    IsIso b := by
  obtain ⟨Z, g, k, hT⟩ := distinguished_cocone_triangle b
  have h₁₂ : b ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have h₃₁ : k ≫ b⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have hinj : ∀ ⦃P : D⦄, ((ObjectProperty.singleton E).shiftClosure ℤ) P →
      ∀ ζ : P ⟶ K⟦(1 : ℤ)⟧, ζ ≫ b⟦(1 : ℤ)⟧' = 0 → ζ = 0 := by
    intro P hP ζ hζ
    have e : (P⟦(-1 : ℤ)⟧ : D)⟦(1 : ℤ)⟧ ≅ P :=
      (shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by simp)).app P
    obtain ⟨u, hu⟩ : ∃ u : (P⟦(-1 : ℤ)⟧ : D) ⟶ K, u⟦(1 : ℤ)⟧' = e.hom ≫ ζ :=
      ⟨(shiftFunctor D (1 : ℤ)).preimage _, (shiftFunctor D (1 : ℤ)).map_preimage _⟩
    have hub : u ≫ b = 0 := by
      refine (shiftFunctor D (1 : ℤ)).map_injective ?_
      rw [Functor.map_comp, hu, Category.assoc, hζ, Limits.comp_zero,
        (shiftFunctor D (1 : ℤ)).map_zero]
    have hu0 : u = 0 :=
      (h (((ObjectProperty.singleton E).shiftClosure ℤ).le_shift (-1 : ℤ) _ hP)).1
        (by simpa using hub)
    rw [← cancel_epi e.hom, Limits.comp_zero, ← hu, hu0,
      (shiftFunctor D (1 : ℤ)).map_zero]
  refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 (hE Z fun {P} ξ hP => ?_)
  have hξk : ξ ≫ k = 0 := by
    refine hinj hP _ ?_
    rw [Category.assoc, h₃₁, Limits.comp_zero]
  obtain ⟨η, hη⟩ := Triangle.coyoneda_exact₃ _ hT ξ hξk
  obtain ⟨μ, hμ⟩ := (h hP).2 η
  have hηg : η ≫ g = 0 := by
    rw [← hμ]
    exact (Category.assoc μ b g).trans (by rw [h₁₂, comp_zero])
  exact hη.trans hηg

end Detection

/-! ### The three dévissage clauses for the unit of an adjunction -/

namespace Adjunction

section Sigma

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {F : D ⥤ C} {G : C ⥤ D}

/-- The unit at a coproduct is the coproduct of the units followed by the comparison map. -/
private theorem map_unit_app_comp_sigmaComparison (adj : F ⊣ G) {ι : Type w} (K : ι → D)
    [HasCoproductsOfShape ι D] :
    Limits.Sigma.map (f := fun i => (F ⋙ G).obj (K i)) (g := K)
        (fun i => adj.unit.app (K i)) ≫
      Limits.sigmaComparison (F ⋙ G) K = adj.unit.app (∐ K) := by
  refine Limits.Sigma.hom_ext _ _ fun i => ?_
  rw [Limits.Sigma.ι_map_assoc, Limits.ι_comp_sigmaComparison]
  exact (adj.unit.naturality (Limits.Sigma.ι K i)).symm

/-- **The unit of an adjunction is invertible at a direct sum of objects at which it is
invertible**, as soon as the right adjoint preserves that direct sum.

The unit at `∐ᵢ Kᵢ` is the direct sum of the units at the `Kᵢ` followed by the comparison
morphism `∐ᵢ (F ⋙ G) Kᵢ ⟶ (F ⋙ G) (∐ᵢ Kᵢ)`; the first is invertible by hypothesis and the second
because `F ⋙ G` preserves the direct sum, `F` being a left adjoint. -/
theorem isIso_unit_app_sigma (adj : F ⊣ G) {ι : Type w} (K : ι → D)
    [HasCoproductsOfShape ι D] [PreservesColimitsOfShape (Discrete ι) G]
    (h : ∀ i, IsIso (adj.unit.app (K i))) : IsIso (adj.unit.app (∐ K)) := by
  have : PreservesColimitsOfShape (Discrete ι) F :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  rw [← map_unit_app_comp_sigmaComparison adj K]
  infer_instance

/-- **The unit of an adjunction is invertible at a direct sum of objects at which it is
invertible**, as soon as the right adjoint preserves the direct sum of their images under the left
adjoint.

The unit at `∐ᵢ Kᵢ` is the direct sum of the units at the `Kᵢ` followed by the comparison
morphism `∐ᵢ (F ⋙ G) Kᵢ ⟶ (F ⋙ G) (∐ᵢ Kᵢ)`; the first is invertible by hypothesis and the second
because `F ⋙ G` preserves the direct sum, `F` being a left adjoint. -/
theorem isIso_unit_app_sigma_of_preservesColimit (adj : F ⊣ G) {ι : Type w} (K : ι → D)
    [HasCoproductsOfShape ι D] [PreservesColimit (Discrete.functor fun i => F.obj (K i)) G]
    (h : ∀ i, IsIso (adj.unit.app (K i))) : IsIso (adj.unit.app (∐ K)) := by
  have : PreservesColimitsOfShape (Discrete ι) F :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimit (Discrete.functor (F.obj ∘ K)) G :=
    ‹PreservesColimit (Discrete.functor fun i => F.obj (K i)) G›
  have : PreservesColimit (Discrete.functor K ⋙ F) G :=
    preservesColimit_of_iso_diagram G (Discrete.compNatIsoDiscrete K F).symm
  rw [← map_unit_app_comp_sigmaComparison adj K]
  infer_instance

/-- **Postcomposition with the unit is the left adjoint, read through the hom-set bijection.**
For an adjunction `F ⊣ G`, postcomposition with `adj.unit.app X` is bijective from `P ⟶ X` onto
`P ⟶ G (F X)` exactly when `F` is bijective from `P ⟶ X` onto `F P ⟶ F X`. -/
theorem bijective_comp_unit_app_iff (adj : F ⊣ G) (P X : D) :
    Function.Bijective (fun f : P ⟶ X => f ≫ adj.unit.app X) ↔
      Function.Bijective (fun f : P ⟶ X => F.map f) := by
  have hfun : (fun f : P ⟶ X => f ≫ adj.unit.app X) =
      (adj.homEquiv P (F.obj X)) ∘ (fun f : P ⟶ X => F.map f) := by
    funext f
    change f ≫ adj.unit.app X = adj.unit.app P ≫ G.map (F.map f)
    exact adj.unit.naturality f
  rw [hfun, Equiv.comp_bijective]

end Sigma

section Triangulated

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [HasZeroObject C] [HasZeroObject D] [Preadditive C] [Preadditive D]
  [HasShift C ℤ] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated C] [Pretriangulated D]
  {F : D ⥤ C} {G : C ⥤ D}

/-- **The unit of an adjunction, read on a triangle.** For an adjunction `F ⊣ G` compatible with
the translation, the components of the unit at the three vertices of a triangle `Δ` form a
morphism of triangles `Δ ⟶ (F ⋙ G).mapTriangle.obj Δ`. The first two squares are the naturality
of the unit and the third is its compatibility with the translation. -/
def unitMapTriangle (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ] [adj.CommShift ℤ]
    (Δ : Triangle D) : Δ ⟶ (F ⋙ G).mapTriangle.obj Δ :=
  Triangle.homMk _ _ (adj.unit.app Δ.obj₁) (adj.unit.app Δ.obj₂) (adj.unit.app Δ.obj₃)
    (adj.unit.naturality Δ.mor₁) (adj.unit.naturality Δ.mor₂) (by
      have hnat : Δ.mor₃ ≫ adj.unit.app (Δ.obj₁⟦(1 : ℤ)⟧) =
          adj.unit.app Δ.obj₃ ≫ (F ⋙ G).map Δ.mor₃ := adj.unit.naturality Δ.mor₃
      change Δ.mor₃ ≫ (shiftFunctor D (1 : ℤ)).map (adj.unit.app Δ.obj₁) =
        adj.unit.app Δ.obj₃ ≫ (F ⋙ G).map Δ.mor₃ ≫
          ((F ⋙ G).commShiftIso (1 : ℤ)).hom.app Δ.obj₁
      rw [← Category.assoc, ← hnat, Category.assoc,
        Adjunction.unit_app_commShiftIso_hom_app])

/-- **Two-out-of-three for the invertibility of the unit in a distinguished triangle.** For an
adjunction `F ⊣ G` of exact functors compatible with the translation, if the unit is invertible
at two of the three vertices of a distinguished triangle then it is invertible at the third.

The unit is a morphism from the triangle to its image under `F ⋙ G`
(`CategoryTheory.Adjunction.unitMapTriangle`), and both triangles are distinguished, so this is
the five lemma for pretriangulated categories. -/
theorem isIso_unit_app_of_mem_distTriang (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ]
    [adj.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated] (Δ : Triangle D)
    (hΔ : Δ ∈ distTriang D) :
    (IsIso (adj.unit.app Δ.obj₁) → IsIso (adj.unit.app Δ.obj₂) →
        IsIso (adj.unit.app Δ.obj₃)) ∧
      (IsIso (adj.unit.app Δ.obj₁) → IsIso (adj.unit.app Δ.obj₃) →
        IsIso (adj.unit.app Δ.obj₂)) ∧
      (IsIso (adj.unit.app Δ.obj₂) → IsIso (adj.unit.app Δ.obj₃) →
        IsIso (adj.unit.app Δ.obj₁)) := by
  have hΔ' : (F ⋙ G).mapTriangle.obj Δ ∈ distTriang D := (F ⋙ G).map_distinguished Δ hΔ
  exact ⟨fun h₁ h₂ => isIso₃_of_isIso₁₂ (adj.unitMapTriangle Δ) hΔ hΔ' h₁ h₂,
    fun h₁ h₃ => isIso₂_of_isIso₁₃ (adj.unitMapTriangle Δ) hΔ hΔ' h₁ h₃,
    fun h₂ h₃ => isIso₁_of_isIso₂₃ (adj.unitMapTriangle Δ) hΔ hΔ' h₂ h₃⟩

omit [HasZeroObject C] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- **The unit of an adjunction is invertible at the translates of a weak generator on which the
left adjoint is bijective on morphisms.** Let `F ⊣ G` be an adjunction compatible with the
translation, let `E` be a weak generator of the source of `F`, and suppose `F` is bijective from
`Hom(E, E⟦n⟧)` onto `Hom(F E, F (E⟦n⟧))` for every `n : ℤ`. Then the unit is invertible at every
translate of `E`.

The unit at `E⟦k⟧` is the `k`-th translate of the unit at `E` composed with an isomorphism, so
only the case of `E` itself is at stake. There, postcomposition with the unit on morphisms
`P ⟶ E` is bijective for every `P` isomorphic to a translate of `E`: translating the hypothesis
at `-n` identifies `Hom(E⟦n⟧, E)` with `Hom(E, E⟦-n⟧)` compatibly with `F`. So the
weak-generator criterion
`CategoryTheory.ObjectProperty.IsWeakTriangulatedGenerator.isIso_of_bijective_comp` applies. -/
theorem isIso_unit_app_shift_of_bijective_map (adj : F ⊣ G) [F.CommShift ℤ] [G.CommShift ℤ]
    [adj.CommShift ℤ] {E : D}
    (hE : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator)
    (h : ∀ n : ℤ, Function.Bijective (fun f : E ⟶ E⟦n⟧ => F.map f)) (k : ℤ) :
    IsIso (adj.unit.app (E⟦k⟧)) := by
  have hbase : IsIso (adj.unit.app E) := by
    refine hE.isIso_of_bijective_comp _ fun {P} hP => ?_
    obtain ⟨Y, n, e, hY⟩ := hP
    obtain rfl := (ObjectProperty.singleton_iff _ _).1 hY
    refine (adj.bijective_comp_unit_app_iff P E).2 ?_
    refine F.bijective_map_of_iso e.symm (Iso.refl E) ?_
    exact F.bijective_map_of_iso (Iso.refl _)
      ((shiftFunctorCompIsoId D (-n) n (by simp)).app E)
      (F.bijective_map_shift n (h (-n)))
  rw [← Adjunction.unit_app_shift_commShiftIso_inv_app adj ℤ k E]
  infer_instance

end Triangulated

end Adjunction

end CategoryTheory

/-! ### Tag 09R9 -/

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- **The unit of the adjunction of Tag 09LT is invertible under the hypotheses of
[Stacks, Tag 09R9].** Let `(A, d)` and `(B, d)` be differential graded algebras over a
commutative ring `R` and let `N` be a differential graded `(A, B)`-bimodule whose class in
`D(B, d)` is a compact object, and suppose the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` is
bijective for every `k : ℤ`. Then the unit `M → RHom(N, M ⊗_A^𝐋 N)` of the adjunction of
Tag 09LT is an isomorphism in `D(A, d)` for every object `M`.

This is the dévissage of Tag 0FQE for the property "the unit is invertible here": direct sums are
handled by the compactness hypothesis through
`DifferentialGraded.Bimodule.preservesColimitsOfShape_discrete_derivedHomFunctor`, distinguished
triangles by the exactness of `- ⊗_A^𝐋 N` and of its right adjoint, and the translates of the
regular module by the bijectivity hypothesis through
`DifferentialGraded.Bimodule.bijective_cohomologyEndomorphismComparison_iff_shift` together with
the fact that the class of the regular module generates `D(A, d)`. -/
theorem isIso_unit_derivedTensorFunctor_adj_derivedHomFunctor (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    IsIso (derivedTensorFunctor_adj_derivedHomFunctor N).unit := by
  have : IsCompactObject.{u} ((derivedTensorFunctor N).obj
      ((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))) :=
    isCompactObject_of_iso (derivedTensorRegularIso N) ‹_›
  let adj := derivedTensorFunctor_adj_derivedHomFunctor N
  have : (derivedHomData A B N.rightModule N.leftAction).functor.Additive :=
    adj.right_adjoint_additive
  let _ : (derivedHomData A B N.rightModule N.leftAction).functor.CommShift ℤ :=
    adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : (derivedHomData A B N.rightModule N.leftAction).functor.IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  have key : ∀ M : derivedCategory' A, IsIso (adj.unit.app M) := by
    refine property_of_coproducts_of_two_out_of_three_of_shifts A
      (fun M => IsIso (adj.unit.app M)) (fun {ι} K hK => ?_) (fun Δ hΔ => ?_) (fun k => ?_)
    · have := preservesColimitsOfShape_discrete_derivedHomFunctor N ι
      exact adj.isIso_unit_app_sigma K hK
    · exact adj.isIso_unit_app_of_mem_distTriang Δ hΔ
    · exact adj.isIso_unit_app_shift_of_bijective_map
        (isWeakTriangulatedGenerator_q_regularModule A)
        (fun n => (bijective_cohomologyEndomorphismComparison_iff_shift N n).1 (h2 n)) k
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks 09R9.** Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative
ring `R` and let `N` be a differential graded `(A, B)`-bimodule. Assume

1. the class of `N` in `D(B, d)` is a compact object, and
2. the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` of
   `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is bijective for every
   `k : ℤ`.

Then the derived tensor product `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of Tag 09LS is fully faithful.

Full faithfulness is data — a chosen inverse to the action on morphism groups — so this is a
definition. It is Tag 07RB applied to the adjunction of Tag 09LT, whose unit is invertible by
`DifferentialGraded.Bimodule.isIso_unit_derivedTensorFunctor_adj_derivedHomFunctor`. -/
@[stacks 09R9]
def derivedTensorFunctor_fullyFaithful (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorFunctor N).FullyFaithful :=
  haveI := isIso_unit_derivedTensorFunctor_adj_derivedHomFunctor N h2
  (derivedTensorFunctor_adj_derivedHomFunctor N).fullyFaithfulLOfIsIsoUnit

end DifferentialGraded.Bimodule

end
