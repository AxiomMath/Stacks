module

public import StacksFrontier.Algebra.Homology.SplitConeAnnihilation

/-!
# Transporting the annihilation of the cohomology of a cone along a ladder of quasi-isomorphisms

Let `𝒜` be an abelian category.  For a morphism `α : A ⟶ B` of `D(𝒜)` and `q : ℤ`, say that
**the cones of `α` have cohomology killed by `q`** if for every distinguished triangle
`A ⟶ B ⟶ Z ⟶ A[1]` on `α` and every `j`, `q` annihilates `H^j(Z)`.  This is the conclusion of
[Stacks, Tag 07Q9], read on the derived category of abelian groups after taking sections.

This file records the three facts that move this property around:

* it only depends on the isomorphism class of `α` in the arrow category
  (`ConeHomologyKilled.of_arrowIso`);
* a commutative square of complexes whose vertical maps are quasi-isomorphisms gives an
  isomorphism of arrows in `D(𝒜)` between the images of the two horizontal maps
  (`arrowIsoOfQuasiIso`, `arrowIsoOfQuasiIsoSymm`);
* for a morphism of complexes `φ`, the property for `Q(φ)` is the annihilation of the homology
  of the mapping cone of `φ` (`coneHomologyKilled_Q_map_iff`), and it follows from the
  annihilation of the identity of every cone (`ConeHomologyKilled.of_smul_id_eq_zero`).

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive Pretriangulated

namespace Stacks.ConeLadder

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- **The cones of `α` have cohomology killed by `q`**: in every distinguished triangle
`A ⟶ B ⟶ Z ⟶ A[1]` of `D(𝒜)` on `α`, `q` annihilates every cohomology object of `Z`. -/
def ConeHomologyKilled (q : ℤ) {A B : DerivedCategory 𝒜} (α : A ⟶ B) : Prop :=
  ∀ (Z : DerivedCategory 𝒜) (v : B ⟶ Z) (w : Z ⟶ A⟦(1 : ℤ)⟧),
    Triangle.mk α v w ∈ distTriang (DerivedCategory 𝒜) →
      ∀ j : ℤ, q • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj Z) = 0

omit [HasDerivedCategory 𝒜] in
/-- Annihilation of the identity is invariant under isomorphism. -/
theorem smul_id_eq_zero_of_iso' {X Y : 𝒜} (i : X ≅ Y) (q : ℤ) (h : q • 𝟙 X = 0) :
    q • 𝟙 Y = 0 := by
  rw [show q • 𝟙 Y = i.inv ≫ (q • 𝟙 X) ≫ i.hom by simp, h, zero_comp, comp_zero]

/-- Annihilation of the cohomology of the third object transfers along an isomorphism of
triangles. -/
private theorem smul_id_homology_obj₃_of_iso {q : ℤ} {T T' : Triangle (DerivedCategory 𝒜)}
    (i : T ≅ T') (j : ℤ) (h : q • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T'.obj₃) = 0) :
    q • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T.obj₃) = 0 :=
  smul_id_eq_zero_of_iso' ((DerivedCategory.homologyFunctor 𝒜 j).mapIso
    (Triangle.π₃.mapIso i).symm) q h

/-- **The property depends only on the isomorphism class of the arrow.** -/
theorem ConeHomologyKilled.of_arrowIso {q : ℤ} {A B A' B' : DerivedCategory 𝒜}
    {α : A ⟶ B} {α' : A' ⟶ B'} (φ : Arrow.mk α ≅ Arrow.mk α')
    (h : ConeHomologyKilled q α') : ConeHomologyKilled q α := by
  intro Z v w hZ j
  obtain ⟨Z', v', w', hZ'⟩ := distinguished_cocone_triangle α'
  obtain ⟨i, -⟩ := exists_iso_of_arrow_iso _ _ hZ hZ' φ
  exact smul_id_homology_obj₃_of_iso i j (h Z' v' w' hZ' j)

/-- **Annihilation of the identity of every cone gives annihilation of its cohomology**, the
cohomology functors being additive. -/
theorem ConeHomologyKilled.of_smul_id_eq_zero {q : ℤ} {A B : DerivedCategory 𝒜} (α : A ⟶ B)
    (h : ∀ (Z : DerivedCategory 𝒜) (v : B ⟶ Z) (w : Z ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk α v w ∈ distTriang (DerivedCategory 𝒜) → q • 𝟙 Z = 0) :
    ConeHomologyKilled q α := by
  intro Z v w hZ j
  rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, h Z v w hZ, Functor.map_zero]

/-- **A commutative square of complexes with quasi-isomorphisms as vertical maps** gives an
isomorphism, in the arrow category of `D(𝒜)`, between the images of its two horizontal maps. -/
noncomputable def arrowIsoOfQuasiIso {K₀ L₀ K₁ L₁ : CochainComplex 𝒜 ℤ} (φ₀ : K₀ ⟶ L₀)
    (φ₁ : K₁ ⟶ L₁) (a : K₀ ⟶ K₁) (b : L₀ ⟶ L₁) [QuasiIso a] [QuasiIso b]
    (w : φ₀ ≫ b = a ≫ φ₁) :
    Arrow.mk (DerivedCategory.Q.map φ₀) ≅ Arrow.mk (DerivedCategory.Q.map φ₁) :=
  haveI : IsIso (DerivedCategory.Q.map a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := 𝒜) a).2 inferInstance
  haveI : IsIso (DerivedCategory.Q.map b) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := 𝒜) b).2 inferInstance
  Arrow.isoMk (asIso (DerivedCategory.Q.map a)) (asIso (DerivedCategory.Q.map b)) (by
    simp only [Arrow.mk_hom, asIso_hom, ← Functor.map_comp, w])

/-- The ladder lemma with the quasi-isomorphisms pointing the other way. -/
noncomputable def arrowIsoOfQuasiIsoSymm {K₀ L₀ K₁ L₁ : CochainComplex 𝒜 ℤ} (φ₀ : K₀ ⟶ L₀)
    (φ₁ : K₁ ⟶ L₁) (a : K₁ ⟶ K₀) (b : L₁ ⟶ L₀) [QuasiIso a] [QuasiIso b]
    (w : φ₁ ≫ b = a ≫ φ₀) :
    Arrow.mk (DerivedCategory.Q.map φ₀) ≅ Arrow.mk (DerivedCategory.Q.map φ₁) :=
  (arrowIsoOfQuasiIso φ₁ φ₀ a b w).symm

/-- **For a morphism of complexes, the property is the annihilation of the homology of its
mapping cone.**  The mapping cone triangle is distinguished, and cones are unique up to
isomorphism. -/
theorem coneHomologyKilled_Q_map_iff (q : ℤ) {K L : CochainComplex 𝒜 ℤ} (φ : K ⟶ L) :
    ConeHomologyKilled q (DerivedCategory.Q.map φ) ↔
      ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone φ).homology j) = 0 := by
  have hT := DerivedCategory.mappingCone_triangle_distinguished φ
  constructor
  · intro h j
    exact smul_id_eq_zero_of_iso' ((DerivedCategory.homologyFunctorFactors 𝒜 j).app _) q
      (h _ _ _ hT j)
  · intro h Z v w hZ j
    obtain ⟨i, -⟩ := exists_iso_of_arrow_iso _ _ hZ hT (Iso.refl _)
    exact smul_id_homology_obj₃_of_iso i j
      (smul_id_eq_zero_of_iso' ((DerivedCategory.homologyFunctorFactors 𝒜 j).app _).symm q (h j))

/-- **The zigzag form of the ladder lemma.**  Two morphisms of complexes `φ : A ⟶ B` and
`μ : M ⟶ N` mapping, by quasi-isomorphisms, to a common morphism `Ψ : P ⟶ R` — that is,
`α : A ⟶ P`, `α' : B ⟶ R`, `β : M ⟶ P`, `β' : N ⟶ R` quasi-isomorphisms with
`φ ≫ α' = α ≫ Ψ` and `μ ≫ β' = β ≫ Ψ` — have isomorphic images in the arrow category of
`D(𝒜)`. -/
noncomputable def arrowIsoOfZigzag {A B M N P R : CochainComplex 𝒜 ℤ} (φ : A ⟶ B) (μ : M ⟶ N)
    (Ψ : P ⟶ R) (α : A ⟶ P) (α' : B ⟶ R) (β : M ⟶ P) (β' : N ⟶ R) [QuasiIso α] [QuasiIso α']
    [QuasiIso β] [QuasiIso β'] (wα : φ ≫ α' = α ≫ Ψ) (wβ : μ ≫ β' = β ≫ Ψ) :
    Arrow.mk (DerivedCategory.Q.map φ) ≅ Arrow.mk (DerivedCategory.Q.map μ) :=
  arrowIsoOfQuasiIso φ Ψ α α' wα ≪≫ (arrowIsoOfQuasiIso μ Ψ β β' wβ).symm

/-- **The annihilation of the cohomology of the mapping cone transfers along a zigzag of
quasi-isomorphisms.** -/
theorem smul_id_homology_mappingCone_of_zigzag (q : ℤ) {A B M N P R : CochainComplex 𝒜 ℤ}
    (φ : A ⟶ B) (μ : M ⟶ N) (Ψ : P ⟶ R) (α : A ⟶ P) (α' : B ⟶ R) (β : M ⟶ P) (β' : N ⟶ R)
    [QuasiIso α] [QuasiIso α'] [QuasiIso β] [QuasiIso β'] (wα : φ ≫ α' = α ≫ Ψ)
    (wβ : μ ≫ β' = β ≫ Ψ)
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone μ).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone φ).homology j) = 0 :=
  (coneHomologyKilled_Q_map_iff q φ).1
    (ConeHomologyKilled.of_arrowIso (arrowIsoOfZigzag φ μ Ψ α α' β β' wα wβ)
      ((coneHomologyKilled_Q_map_iff q μ).2 h)) j

end Stacks.ConeLadder
