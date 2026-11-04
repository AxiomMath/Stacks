module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import StacksFrontier.Algebra.Homology.DerivedCategory.ConeHomologyLadder
public import StacksFrontier.Algebra.Homology.Embedding.MapExtend07Q9
public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology

/-!
# Cone cohomology killed by a scalar, along an exact functor

Let `F : C ⥤ D` be an additive functor of abelian categories which preserves homology, and let
`φ : K ⟶ L` be a morphism of `ℕ`-indexed cochain complexes of `C`.  If `q` kills the cohomology
of the mapping cone of the extension of `φ` to `ℤ`, it kills that of `F` applied to `φ`
(`smul_id_homology_mappingCone_map`).  The application is the universe lift
`AddCommGrpCat.uliftFunctor`, which carries the Moore complexes of the cosimplicial modules of
[Stacks, Tag 07LG], at the universe of the crystal, to the Čech complexes of sections at the
universe of crystalline cohomology.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory Category Limits

namespace Stacks.ConeLadder

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology]

omit [Abelian C] in
/-- A scalar killing an object kills every object isomorphic to it. -/
theorem smul_id_eq_zero_of_iso07Q9 {X Y : D} (i : X ≅ Y) (q : ℤ) (h : q • 𝟙 X = 0) :
    q • 𝟙 Y = 0 := by
  have : q • 𝟙 Y = i.inv ≫ (q • 𝟙 X) ≫ i.hom := by simp
  rw [this, h, zero_comp, comp_zero]

/-- The annihilation of the cohomology of a mapping cone is invariant under isomorphisms of
arrows of `ℤ`-indexed complexes. -/
private theorem smul_id_homology_mappingCone_of_arrowIso (q : ℤ) {K L K' L' : CochainComplex D ℤ}
    {φ : K ⟶ L} {φ' : K' ⟶ L'} (i : Arrow.mk φ ≅ Arrow.mk φ')
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone φ').homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone φ).homology j) = 0 := by
  let := HasDerivedCategory.standard D
  exact (coneHomologyKilled_Q_map_iff q φ).1 (ConeHomologyKilled.of_arrowIso
    (DerivedCategory.Q.mapArrow.mapIso i) ((coneHomologyKilled_Q_map_iff q φ').2 h)) j

/-- **An additive homology-preserving functor carries a scalar killing the cohomology of a
mapping cone to one killing the cohomology of the image mapping cone.**  The image of the cone of
`φ` is the cone of the image of `φ` (`CochainComplex.mappingCone.mapHomologicalComplexIso`), and
its cohomology is `F` of the cohomology of the cone. -/
theorem smul_id_homology_mappingCone_functor (q : ℤ) {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone φ).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone ((F.mapHomologicalComplex _).map φ)).homology j) = 0 := by
  refine smul_id_eq_zero_of_iso07Q9
    ((HomologicalComplex.homologyFunctor D _ j).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso φ F)) q ?_
  refine smul_id_eq_zero_of_iso07Q9
    (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso F _ j).symm q ?_
  rw [← F.map_id, ← F.map_zsmul, h j, F.map_zero]

/-- **`smul_id_homology_mappingCone_functor` for a morphism of `ℕ`-indexed complexes extended to
`ℤ`**: if `q` kills the cohomology of the cone of the extension of `φ`, it kills that of the cone
of the extension of `F` applied to `φ`. -/
theorem smul_id_homology_mappingCone_map (q : ℤ) {K L : CochainComplex C ℕ} (φ : K ⟶ L)
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      ((F.mapHomologicalComplex _).map φ) ComplexShape.embeddingUpNat)).homology j) = 0 := by
  have harrow : Arrow.mk (HomologicalComplex.extendMap ((F.mapHomologicalComplex _).map φ)
      ComplexShape.embeddingUpNat) ≅
      Arrow.mk ((F.mapHomologicalComplex _).map
        (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)) :=
    Arrow.isoMk (HomologicalComplex.mapExtendIso F ComplexShape.embeddingUpNat K).symm
      (HomologicalComplex.mapExtendIso F ComplexShape.embeddingUpNat L).symm (by
        dsimp
        rw [Iso.inv_comp_eq, ← assoc, Iso.eq_comp_inv,
          HomologicalComplex.mapExtendIso_hom_naturality])
  exact smul_id_homology_mappingCone_of_arrowIso q harrow
    (smul_id_homology_mappingCone_functor F q _ h) j

/-- **The annihilation of the cohomology of a mapping cone is invariant under isomorphisms of
arrows of `ℕ`-indexed complexes**, read on the extensions to `ℤ`. -/
theorem smul_id_homology_mappingCone_extend_of_arrowIso (q : ℤ) {K L K' L' : CochainComplex D ℕ}
    {φ : K ⟶ L} {φ' : K' ⟶ L'} (i : Arrow.mk φ ≅ Arrow.mk φ')
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap φ' ComplexShape.embeddingUpNat)).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)).homology j) = 0 := by
  exact smul_id_homology_mappingCone_of_arrowIso q
    (((ComplexShape.embeddingUpNat.extendFunctor D).mapArrow).mapIso i) h j

/-- **Transport of the annihilation along an exact functor and an isomorphism of arrows**: if
`φ` is isomorphic, as an arrow, to `F` applied to `ψ`, a scalar killing the cohomology of the cone
of (the extension of) `ψ` kills that of `φ`. -/
theorem smul_id_homology_mappingCone_of_arrowIso_map (q : ℤ) {K L : CochainComplex D ℕ}
    {K₀ L₀ : CochainComplex C ℕ} (φ : K ⟶ L) (ψ : K₀ ⟶ L₀)
    (i : Arrow.mk φ ≅ Arrow.mk ((F.mapHomologicalComplex _).map ψ))
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap ψ ComplexShape.embeddingUpNat)).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone
      (HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat)).homology j) = 0 :=
  smul_id_homology_mappingCone_extend_of_arrowIso q i
    (smul_id_homology_mappingCone_map F q ψ h) j

end Stacks.ConeLadder
