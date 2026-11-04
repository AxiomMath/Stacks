module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.Triangle.DifferentialSequence

/-!
# The distinguished triangle of the cotangent differential sequence

For an injective map `f : B ⟶ C` of commutative `A`-algebras, the degreewise short exact
sequence of simplicial `C`-modules formed by the differentials of the two standard resolutions
and of the base-changed relative resolution yields a distinguished triangle in
`D(ModuleCat C)`. Its middle vertex is the cotangent complex `L_{C/A}` and its first vertex is
the degreewise extension of scalars along `f` of the cotangent simplicial module of `B` over
`A`.

## Main definitions

* `AlgebraicTopology.alternatingFaceMapCochainComplex`: the alternating face map complex of a
  simplicial object, reindexed so that simplicial degree `n` sits in cohomological degree `-n`.
* `CommAlgCat.cotangentDifferentialComplexes`: the short complex of cochain complexes of
  `C`-modules obtained from the differential sequence of `A → B → C`.
* `CommAlgCat.cotangentTriangle`: the resulting distinguished triangle in `D(ModuleCat C)`.

## Main results

* `AlgebraicTopology.shortExact_map_alternatingFaceMapCochainComplex`: a short exact sequence of
  simplicial objects in an abelian category stays short exact after reindexing.
* `CommAlgCat.cotangentDifferentialComplexes_shortExact` and
  `CommAlgCat.cotangentTriangle_distinguished`: the short complex is short exact and the
  associated triangle is distinguished.
* `CommAlgCat.cotangentTriangle_obj₂` identifies the middle vertex with `L_{C/A}`, and
  `CommAlgCat.cotangentDifferentialComplexes_X₁_degreeIso` identifies the first vertex
  degreewise with `C ⊗[B] (Ω[Pₙ⁄A] ⊗[Pₙ] B)`.

## References

* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
* [Stacks Project, Tag 08QS](https://stacks.math.columbia.edu/tag/08QS)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 08SC](https://stacks.math.columbia.edu/tag/08SC)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicTopology Opposite Simplicial
open scoped ChangeOfRings TensorProduct

universe t u v

namespace AlgebraicTopology

/-- The alternating face map complex of a simplicial object in a preadditive category with a
zero object, reindexed so that simplicial degree `n` occurs in cohomological degree `-n`. -/
noncomputable def alternatingFaceMapCochainComplex (C : Type*) [Category* C] [Preadditive C]
    [HasZeroObject C] : SimplicialObject C ⥤ CochainComplex C ℤ :=
  alternatingFaceMapComplex C ⋙ (ComplexShape.embeddingUpIntLE 0).extendFunctor C

/-- The reindexed alternating face map complex functor is additive. -/
instance (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] :
    (alternatingFaceMapCochainComplex C).Additive :=
  inferInstanceAs (Functor.Additive
    (alternatingFaceMapComplex C ⋙ (ComplexShape.embeddingUpIntLE 0).extendFunctor C))

/-- Reindexing and then taking the term in the cohomological degree attached to the simplicial
degree `n` is evaluation in simplicial degree `n`. -/
noncomputable def alternatingFaceMapCochainComplexCompEvalIso (C : Type*) [Category* C]
    [Preadditive C] [HasZeroObject C] (n : ℕ) :
    alternatingFaceMapCochainComplex C ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ)
        ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n) ≅
      (evaluation SimplexCategoryᵒᵖ C).obj (op ⦋n⦌) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctorCompEvalIso C rfl) ≪≫
    NatIso.ofComponents fun _ => Iso.refl _

/-- A short exact sequence of simplicial objects in an abelian category remains short exact
after passing to the reindexed alternating face map complexes. -/
theorem shortExact_map_alternatingFaceMapCochainComplex {C : Type*} [Category* C] [Abelian C]
    {S : ShortComplex (SimplicialObject C)} (hS : S.ShortExact) :
    (S.map (alternatingFaceMapCochainComplex C)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  by_cases hi : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = i
  · obtain ⟨n, rfl⟩ := hi
    rw [← ShortComplex.map_comp]
    exact (ShortComplex.shortExact_iff_of_iso
      (S.mapNatIso (alternatingFaceMapCochainComplexCompEvalIso C n))).2
      (hS.map_of_exact ((evaluation SimplexCategoryᵒᵖ C).obj (op ⦋n⦌)))
  · refine (ShortComplex.Splitting.ofIsZero _ ?_ ?_ ?_).shortExact <;>
      exact HomologicalComplex.isZero_extend_X _ _ i (by tauto)

end AlgebraicTopology

namespace CommAlgCat

/-- The cotangent complex is the reindexed alternating face map complex of the cotangent
simplicial module. -/
theorem cotangentComplex_eq_alternatingFaceMapCochainComplex_obj (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    cotangentComplex A B =
      (alternatingFaceMapCochainComplex (ModuleCat.{max u v} B)).obj
        (cotangentSimplicialModule A B).object :=
  rfl

/-- The short complex of cochain complexes of `C`-modules attached to the differential sequence
of the standard resolutions of `A → B → C`. Its middle term is `L_{C/A}`. -/
noncomputable def cotangentDifferentialComplexes (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    ShortComplex (CochainComplex (ModuleCat.{max u v} C) ℤ) :=
  (standardResolutionDifferentialSequence A f).complex.map
    (alternatingFaceMapCochainComplex (ModuleCat.{max u v} C))

/-- The middle term of the differential short complex is the cotangent complex `L_{C/A}`. -/
theorem cotangentDifferentialComplexes_X₂ (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    (cotangentDifferentialComplexes A f).X₂ = cotangentComplex A C :=
  rfl

/-- In cohomological degree `-n` the first term of the differential short complex is the
extension of scalars along `f` of `Ω[Pₙ⁄A] ⊗[Pₙ] B`. -/
noncomputable def cotangentDifferentialComplexes_X₁_degreeIso (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) (n : ℕ) :
    (cotangentDifferentialComplexes A f).X₁.X (-(n : ℤ)) ≅
      (ModuleCat.extendScalars f.hom.toRingHom).obj (cotangentTerm A B (op ⦋n⦌)) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE 0) (i := n) (by simp)

/-- In cohomological degree `-n` the third term of the differential short complex is the
base-changed relative differentials of the base-changed resolution in simplicial degree `n`. -/
noncomputable def cotangentDifferentialComplexes_X₃_degreeIso (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) (n : ℕ) :
    (cotangentDifferentialComplexes A f).X₃.X (-(n : ℤ)) ≅
      (relativeCotangentSimplicialObject A f).obj (op ⦋n⦌) :=
  HomologicalComplex.extendXIso _ (ComplexShape.embeddingUpIntLE 0) (i := n) (by simp)

/-- For an injective map `f : B ⟶ C` of `A`-algebras, the differential short complex of cochain
complexes of `C`-modules is short exact. -/
@[stacks 08SD "differential_sequence complexes"]
theorem cotangentDifferentialComplexes_shortExact (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) (hf : Function.Injective f.hom) :
    (cotangentDifferentialComplexes A f).ShortExact :=
  shortExact_map_alternatingFaceMapCochainComplex
    (standardResolution_differentials_shortExact A f hf)

/-- The triangle in `D(ModuleCat C)` attached to the differential short exact sequence of the
standard resolutions of `A → B → C`, for `f : B ⟶ C` injective. -/
@[stacks 08SD "differential_sequence triangle"]
noncomputable def cotangentTriangle (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{t} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    Triangle (DerivedCategory (ModuleCat.{max u v} C)) :=
  DerivedCategory.triangleOfSES (cotangentDifferentialComplexes_shortExact A f hf)

/-- The triangle attached to the differential sequence is distinguished. -/
@[stacks 08SD "differential_sequence triangle distinguished"]
theorem cotangentTriangle_distinguished (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{t} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    cotangentTriangle A f hf ∈ distTriang (DerivedCategory (ModuleCat.{max u v} C)) :=
  DerivedCategory.triangleOfSES_distinguished _

/-- The first vertex of the triangle is the reindexed complex of the degreewise extension of
scalars along `f` of the cotangent simplicial module of `B` over `A`. -/
theorem cotangentTriangle_obj₁ (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{t} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    (cotangentTriangle A f hf).obj₁ =
      DerivedCategory.Q.obj ((alternatingFaceMapCochainComplex (ModuleCat.{max u v} C)).obj
        ((cotangentSimplicialModule A B).object ⋙
          ModuleCat.extendScalars f.hom.toRingHom)) :=
  rfl

/-- The middle vertex of the triangle is the cotangent complex `L_{C/A}`. -/
theorem cotangentTriangle_obj₂ (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{t} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    (cotangentTriangle A f hf).obj₂ = DerivedCategory.Q.obj (cotangentComplex A C) :=
  rfl

/-- The third vertex of the triangle is the reindexed complex of the base-changed relative
differentials of the base-changed resolution. -/
theorem cotangentTriangle_obj₃ (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{t} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    (cotangentTriangle A f hf).obj₃ =
      DerivedCategory.Q.obj ((alternatingFaceMapCochainComplex (ModuleCat.{max u v} C)).obj
        (relativeCotangentSimplicialObject A f)) :=
  rfl

/-- The first arrow of the triangle is the image of the first map of the differential
sequence. -/
theorem cotangentTriangle_mor₁ (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{t} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    (cotangentTriangle A f hf).mor₁ =
      DerivedCategory.Q.map
        ((alternatingFaceMapCochainComplex (ModuleCat.{max u v} C)).map
          (differentialSequenceFirstMap A f)) :=
  rfl

/-- The second arrow of the triangle is the image of the second map of the differential
sequence. -/
theorem cotangentTriangle_mor₂ (A : Type u) [CommRing A]
    {B C : CommAlgCat.{max u v} A} [HasDerivedCategory.{t} (ModuleCat.{max u v} C)]
    (f : B ⟶ C) (hf : Function.Injective f.hom) :
    (cotangentTriangle A f hf).mor₂ =
      DerivedCategory.Q.map
        ((alternatingFaceMapCochainComplex (ModuleCat.{max u v} C)).map
          (differentialSequenceSecondMap A f)) :=
  rfl

end CommAlgCat

end
