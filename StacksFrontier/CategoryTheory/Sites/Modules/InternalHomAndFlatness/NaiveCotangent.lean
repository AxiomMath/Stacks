module

public import Mathlib.Algebra.Homology.Double
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.CorepresentingConormalSequence
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraSheaf
public import StacksFrontier.Homology.DoubleHomology

/-!
# The naive cotangent complex of a morphism of sheaves of rings

For a morphism `a : A ⟶ B` of sheaves of commutative rings on a site, take the canonical
polynomial presentation `A[B] ⟶ B` of `B` as a quotient of a polynomial algebra over `A`. Its
conormal sequence, with kernel ideal `I`, gives the two-term naive cotangent complex of sheaves
of `B`-modules

`I/I² ⟶ B ⊗[A[B]] Ω[A[B]/A]`,

placed in degrees `-1` and `0`.

## Main definitions

* `Stacks.SheafOfModules.canonicalConormalSequence` is the conormal sequence of the canonical
  polynomial presentation.
* `Stacks.SheafOfModules.naiveCotangentComplex` is the naive cotangent complex.
* `Stacks.SheafOfModules.presentation` is the polynomial presentation `A[E] ⟶ B` attached to a
  family of generators `α : E ⟶ B`, and
  `Stacks.SheafOfModules.presentationNaiveCotangentComplex` is the complex `NL(α)` built from
  its conormal sequence.
* `Stacks.SheafOfModules.freeAlgebraMap` is the morphism of `A`-algebras `A[E₁] ⟶ A[E₂]`
  induced by a morphism `E₁ ⟶ E₂` of presheaves of sets.
* `Stacks.SheafOfModules.presentationNaiveCotangentComplexMap` is the chain map
  `NL(α₁) ⟶ NL(α₂)` induced by a morphism of presentations.
* `Stacks.SheafOfModules.naiveCotangentComplexComparison` is the canonical comparison map
  `NL(α) ⟶ NL_{B/A}`.

## Main results

* `Stacks.SheafOfModules.naiveCotangentComplex_X_negOne` and
  `Stacks.SheafOfModules.naiveCotangentComplex_X_zero` identify its two terms.
* `Stacks.SheafOfModules.naiveCotangentComplex_isZero_X` says that all other terms vanish.
* `Stacks.SheafOfModules.naiveCotangentComplex_d_negOne_zero` identifies its differential.
* `Stacks.SheafOfModules.presentationNaiveCotangentComplex_id` says that `NL_{B/A}` is
  `NL(id_B)`, the complex of the presentation whose family of generators is the identity.
* `Stacks.SheafOfModules.naiveCotangentComplexComparison_id` says that the comparison map is
  the identity at the canonical presentation, and
  `Stacks.SheafOfModules.naiveCotangentComplexComparison_naturality` that the comparison maps
  are compatible with every morphism of presentations.
* `Stacks.SheafOfModules.presentationNaiveCotangentComplexHomologyZeroIso` identifies the
  degree `0` cohomology sheaf of `NL(α)` with the sheaf of relative differentials
  `Ω_{B/A}`, the same sheaf for every presentation `α`, and
  `Stacks.SheafOfModules.presentationNaiveCotangentComplexHomologyNegOneIso` identifies the
  degree `-1` cohomology sheaf with the kernel of the conormal map.

## Implementation notes

The differential raises degree from `-1` to `0`, so the complex is represented by a
`CochainComplex` indexed by `ℤ`, built with `HomologicalComplex.double`, which makes every other
degree zero. The named term and differential equations let later results use the complex without
unfolding its construction.

## References

* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW)
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical
  polynomial presentation.
* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w z

namespace Stacks.SheafOfModules


variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The conormal sequence for the canonical polynomial presentation of `B` over `A`.
Its first two terms are `I/I²` and `B ⊗[A[B]] Ω[A[B]/A]`. -/
@[stacks 08TV "the canonical map is the left-hand map of this sequence"]
noncomputable abbrev canonicalConormalSequence
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    ShortComplex
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) := by
  have : Presheaf.IsLocallySurjective J
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a).hom :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
      (Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective J A B a)
  exact Stacks.Sites.Conormal.conormalSequence.{v, u, w, z} J A
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)) B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B))
    (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a)

/-- **Stacks 08TW.** The naive cotangent complex of `B` over `A`, with `I/I²` in degree `-1`
and `B ⊗[A[B]] Ω[A[B]/A]` in degree `0`. This two-term complex is the one displayed in
Stacks 08TI, and 08TJ names it for a morphism of sheaves of rings. -/
@[stacks 08TW,
  sga "6 0 4.4" "NL_{B/A} construction"]
noncomputable def naiveCotangentComplex
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    CochainComplex
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.double (canonicalConormalSequence.{v, u, w, z} J A B a).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The conormal sheaf is the degree `-1` term. -/
@[simp] theorem naiveCotangentComplex_X_negOne
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    (naiveCotangentComplex.{v, u, w, z} J A B a).X (-1) =
      (canonicalConormalSequence.{v, u, w, z} J A B a).X₁ := by
  simp [naiveCotangentComplex, HomologicalComplex.double]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The scalar extension of relative differentials is the degree `0` term. -/
@[simp] theorem naiveCotangentComplex_X_zero
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    (naiveCotangentComplex.{v, u, w, z} J A B a).X 0 =
      (canonicalConormalSequence.{v, u, w, z} J A B a).X₂ := by
  simp [naiveCotangentComplex, HomologicalComplex.double]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The naive cotangent complex has no terms outside degrees `-1` and `0`. -/
theorem naiveCotangentComplex_isZero_X
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (i : ℤ)
    (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((naiveCotangentComplex.{v, u, w, z} J A B a).X i) := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  show IsZero
    ((HomologicalComplex.double
      (canonicalConormalSequence.{v, u, w, z} J A B a).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).X i)
  exact HomologicalComplex.isZero_double_X _ _ i hneg hzero

/-- The differential of `double f` from degree `-1` to `0` is `f`, up to the identifications of
the terms. -/
private theorem double_d_negOne_zero {D : Type*} [Category D] [HasZeroMorphisms D]
    [HasZeroObject D] {X Y : D} (f : X ⟶ Y) (hr : (ComplexShape.up ℤ).Rel (-1) 0)
    {K : CochainComplex D ℤ} (hK : K = HomologicalComplex.double f hr)
    (h₀ : K.X (-1) = X) (h₁ : K.X 0 = Y) :
    K.d (-1) 0 = eqToHom h₀ ≫ f ≫ eqToHom h₁.symm := by
  subst hK
  rw [HomologicalComplex.double_d _ _ (by decide)]
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The only nonzero differential is the conormal map. -/
theorem naiveCotangentComplex_d_negOne_zero
    (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) :
    (naiveCotangentComplex.{v, u, w, z} J A B a).d (-1) 0 =
      eqToHom (naiveCotangentComplex_X_negOne J A B a) ≫
        (canonicalConormalSequence.{v, u, w, z} J A B a).f ≫
        eqToHom (naiveCotangentComplex_X_zero J A B a).symm := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact double_d_negOne_zero _ (by decide) rfl (naiveCotangentComplex_X_negOne J A B a)
    (naiveCotangentComplex_X_zero J A B a)

/-! ### Arbitrary polynomial presentations -/

section Presentation

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- The polynomial presentation of `B` over `A` attached to a family of generators
`α : E ⟶ B`: the `A`-algebra morphism `A[E] ⟶ B` sending the variable `[x]` to `α(x)`. -/
noncomputable abbrev presentation (E : Functor Cᵒᵖ (Type w))
    (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E ⟶ B :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc J A B E a α

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The identity family of generators presents `B` by the canonical polynomial presentation. -/
theorem presentation_id :
    presentation J A B a (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _) =
      Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a :=
  (Stacks.Sites.FreeAlgebra.canonicalPresentation_eq_desc J A B a).symm

/-- The underlying morphism of presheaves of rings of the canonical polynomial presentation
`A[B] ⟶ B` is locally surjective. -/
instance canonicalPresentation_isLocallySurjective :
    Presheaf.IsLocallySurjective J
      (Stacks.Sites.FreeAlgebra.canonicalPresentation J A B a).hom :=
  (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    (Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective J A B a)

/-- The presentation of `B` attached to the identity family of generators is locally surjective. -/
instance presentation_id_isLocallySurjective :
    Presheaf.IsLocallySurjective J
      (presentation J A B a (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)).hom := by
  rw [presentation_id]
  exact (Presheaf.isLocallySurjective_iff_whisker_forget J _).mpr
    (Stacks.Sites.FreeAlgebra.canonicalPresentation_isLocallySurjective J A B a)

variable (E : Functor Cᵒᵖ (Type w))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)

/-- The conormal sequence of the presentation `A[E] ⟶ B`. Writing `K` for the kernel of that
morphism, its first two terms are `K/K²` and `B ⊗[A[E]] Ω[A[E]/A]`. -/
noncomputable abbrev presentationConormalSequence
    [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] :
    ShortComplex (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
  Stacks.Sites.Conormal.conormalSequence.{v, u, w, z} J A
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E) B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E)
    (presentation J A B a E α)

/-- The naive cotangent complex `NL(α)` of a polynomial presentation `α : E ⟶ B` of `B` over
`A`, with `K/K²` in degree `-1` and `B ⊗[A[E]] Ω[A[E]/A]` in degree `0`. -/
noncomputable def presentationNaiveCotangentComplex
    [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] :
    CochainComplex
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.double
    (presentationConormalSequence.{v, u, w, z} J A B a E α).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `NL_{B/A}` is `NL(id_B)`: the canonical polynomial presentation is the one whose family of
generators is the identity of `B`. -/
theorem presentationConormalSequence_id :
    presentationConormalSequence.{v, u, w, z} J A B a
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _) =
      canonicalConormalSequence.{v, u, w, z} J A B a :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `NL_{B/A}` is `NL(id_B)` as a complex. -/
theorem presentationNaiveCotangentComplex_id :
    presentationNaiveCotangentComplex.{v, u, w, z} J A B a
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _) =
      naiveCotangentComplex.{v, u, w, z} J A B a :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The conormal sheaf of the presentation is the degree `-1` term of `NL(α)`. -/
@[simp] theorem presentationNaiveCotangentComplex_X_negOne
    [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α).X (-1) =
      (presentationConormalSequence.{v, u, w, z} J A B a E α).X₁ := by
  simp [presentationNaiveCotangentComplex, HomologicalComplex.double]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The scalar extension of relative differentials is the degree `0` term of `NL(α)`. -/
@[simp] theorem presentationNaiveCotangentComplex_X_zero
    [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α).X 0 =
      (presentationConormalSequence.{v, u, w, z} J A B a E α).X₂ := by
  simp [presentationNaiveCotangentComplex, HomologicalComplex.double]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `NL(α)` has no terms outside degrees `-1` and `0`. -/
theorem presentationNaiveCotangentComplex_isZero_X
    [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] (i : ℤ)
    (hneg : i ≠ -1) (hzero : i ≠ 0) :
    IsZero ((presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α).X i) := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  show IsZero
    ((HomologicalComplex.double
      (presentationConormalSequence.{v, u, w, z} J A B a E α).f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).X i)
  exact HomologicalComplex.isZero_double_X _ _ i hneg hzero

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The only nonzero differential of `NL(α)` is the conormal map. -/
theorem presentationNaiveCotangentComplex_d_negOne_zero
    [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α).d (-1) 0 =
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E α) ≫
        (presentationConormalSequence.{v, u, w, z} J A B a E α).f ≫
        eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E α).symm := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact double_d_negOne_zero _ (by decide) rfl
    (presentationNaiveCotangentComplex_X_negOne J A B a E α)
    (presentationNaiveCotangentComplex_X_zero J A B a E α)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `NL(α)` has no differential out of degree `0`. -/
theorem presentationNaiveCotangentComplex_d_zero
    [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom] (k : ℤ) :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α).d 0 k = 0 := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  show (HomologicalComplex.double
    (presentationConormalSequence.{v, u, w, z} J A B a E α).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d 0 k = 0
  exact HomologicalComplex.double_d_eq_zero₀ _ _ 0 k (by decide)

end Presentation

/-! ### Morphisms of presentations -/

section MorphismOfPresentations

variable (A : Sheaf J CommRingCat.{w}) (E₁ E₂ : Functor Cᵒᵖ (Type w)) (h : E₁ ⟶ E₂)

/-- The morphism of `A`-algebras `A[E₁] ⟶ A[E₂]` induced by a morphism `h : E₁ ⟶ E₂` of
presheaves of sets: it is the identity on coefficients and sends the variable `[x]` to the
variable `[h x]`. -/
noncomputable abbrev freeAlgebraMap :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁ ⟶
      Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂ :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc J A
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂) E₁
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₂)
    (h ≫ Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A E₂)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphism `A[E₁] ⟶ A[E₂]` respects the structural morphisms from `A`. -/
theorem freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₁ ≫
        freeAlgebraMap J A E₁ E₂ h =
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₂ :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc J A _ E₁ _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphism `A[E₁] ⟶ A[E₂]` sends the variable `[x]` to the variable `[h x]`. -/
theorem freeAlgebraSheafVariable_comp_freeAlgebraMap :
    Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A E₁ ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{w}).map (freeAlgebraMap J A E₁ E₂ h))
        (forget CommRingCat.{w}) =
      h ≫ Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable J A E₂ :=
  Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc J A _ E₁ _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphism `A[E] ⟶ A[E]` induced by the identity of `E` is the identity. -/
theorem freeAlgebraMap_id :
    freeAlgebraMap J A E₁ E₁ (𝟙 E₁) = 𝟙 (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁) := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A _ E₁ ?_ ?_
  · rw [freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap, Category.comp_id]
  · rw [freeAlgebraSheafVariable_comp_freeAlgebraMap, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.whiskerRight_id', Category.id_comp]
    exact (Category.comp_id _).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The morphism `A[E₁] ⟶ A[E₃]` induced by a composition of morphisms of presheaves of sets is
the composition of the induced morphisms. -/
theorem freeAlgebraMap_comp (E₃ : Functor Cᵒᵖ (Type w)) (k : E₂ ⟶ E₃) :
    freeAlgebraMap J A E₁ E₂ h ≫ freeAlgebraMap J A E₂ E₃ k =
      freeAlgebraMap J A E₁ E₃ (h ≫ k) := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A _ E₁ ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap,
      freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap,
      freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap]
  · rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_freeAlgebraMap, Category.assoc,
      freeAlgebraSheafVariable_comp_freeAlgebraMap, freeAlgebraSheafVariable_comp_freeAlgebraMap,
      Category.assoc]

variable (B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (α₁ : E₁ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  (α₂ : E₂ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- A morphism of presentations, that is a morphism `h : E₁ ⟶ E₂` of families of generators
with `h ≫ α₂ = α₁`, induces a morphism `A[E₁] ⟶ A[E₂]` over `B`. -/
theorem freeAlgebraMap_comp_presentation (hα : h ≫ α₂ = α₁) :
    freeAlgebraMap J A E₁ E₂ h ≫ presentation J A B a E₂ α₂ =
      presentation J A B a E₁ α₁ := by
  refine Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext J A B E₁ ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc]
  · rw [Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_freeAlgebraMap, Category.assoc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc,
      Stacks.Sites.FreeAlgebra.freeAlgebraSheafVariable_comp_desc, hα]

variable [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  (hα : h ≫ α₂ = α₁)

/-- The map `K₁/K₁² ⟶ K₂/K₂²` of conormal sheaves induced by a morphism of presentations. -/
noncomputable abbrev presentationConormalMap :
    (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₁ ⟶
      (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₁ :=
  Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, w, z} J B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
    (freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)

/-- The map `B ⊗[A[E₁]] Ω[A[E₁]/A] ⟶ B ⊗[A[E₂]] Ω[A[E₂]/A]` induced by a morphism of
presentations. -/
noncomputable abbrev presentationTensorMap :
    (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).X₂ ⟶
      (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).X₂ :=
  Stacks.Sites.Conormal.tensorSheafMapOfFac.{v, u, w, z} J A B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₁)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
    (freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)

/-- The square expressing that the maps induced by a morphism of presentations commute with
the differentials of `NL(α₁)` and `NL(α₂)`. -/
theorem presentationConormalMap_comm :
    (presentationConormalMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E₂ α₂).symm) ≫
      (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₂ α₂).d (-1) 0 =
    (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f ≫
      (presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E₂ α₂).symm) := by
  rw [presentationNaiveCotangentComplex_d_negOne_zero]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun t ↦ t ≫ eqToHom
      (presentationNaiveCotangentComplex_X_zero J A B a E₂ α₂).symm)
    (Stacks.Sites.Conormal.conormalSequence_f_naturality.{v, u, w, z} J A B
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₁)
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₂)
      (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
      (freeAlgebraMap J A E₁ E₂ h)
      (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
      (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)).symm

/-- The degree `0` component of the induced maps is killed by every differential out of
degree `0`, since `NL(α₂)` has none. -/
theorem presentationTensorMap_comp_d (k : ℤ) :
    (presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E₂ α₂).symm) ≫
      (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₂ α₂).d 0 k = 0 := by
  rw [presentationNaiveCotangentComplex_d_zero, Limits.comp_zero]

/-- The chain map `NL(α₁) ⟶ NL(α₂)` induced by a morphism of presentations, that is by a
morphism `h : E₁ ⟶ E₂` of families of generators with `h ≫ α₂ = α₁`. -/
noncomputable def presentationNaiveCotangentComplexMap :
    presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₁ α₁ ⟶
      presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₂ α₂ := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (presentationConormalMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E₂ α₂).symm)
    (presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
      eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E₂ α₂).symm)
    (presentationConormalMap_comm.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
    (fun k _ ↦ presentationTensorMap_comp_d.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα k)

/-- In degree `-1` the chain map is the map of conormal sheaves. -/
theorem presentationNaiveCotangentComplexMap_f_negOne :
    (presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα).f (-1) =
      eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E₁ α₁) ≫
        presentationConormalMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        eqToHom (presentationNaiveCotangentComplex_X_negOne J A B a E₂ α₂).symm := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble_f₀
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (presentationConormalMap_comm.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
    (fun k _ ↦ presentationTensorMap_comp_d.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα k)

/-- In degree `0` the chain map is the map on the scalar extensions of the differentials. -/
theorem presentationNaiveCotangentComplexMap_f_zero :
    (presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα).f 0 =
      eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E₁ α₁) ≫
        presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        eqToHom (presentationNaiveCotangentComplex_X_zero J A B a E₂ α₂).symm := by
  have : HasZeroObject
      (_root_.SheafOfModules.{max w u v z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    hasZeroObject_of_hasTerminal_object
  exact HomologicalComplex.mkHomFromDouble_f₁
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide) _ _
    (presentationConormalMap_comm.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
    (fun k _ ↦ presentationTensorMap_comp_d.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα k)

end MorphismOfPresentations

/-! ### The canonical comparison map -/

section Comparison

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (E : Functor Cᵒᵖ (Type w))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]

/-- The canonical comparison chain map `NL(α) ⟶ NL_{B/A}` from the naive cotangent complex of
an arbitrary polynomial presentation `α : E ⟶ B` to the one of the canonical presentation. It
is the map of the morphism of presentations `α : (E, α) ⟶ (B, id)`. -/
@[stacks 08TL "the canonical map"]
noncomputable def naiveCotangentComplexComparison :
    presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α ⟶
      naiveCotangentComplex.{v, u, w, z} J A B a :=
  presentationNaiveCotangentComplexMap.{v, u, w, z} J A E
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) α B a α (𝟙 _) (Category.comp_id α)

end Comparison

/-! ### Extensionality -/

section Ext

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (E₁ E₂ : Functor Cᵒᵖ (Type w))
  (α₁ : E₁ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  (α₂ : E₂ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Two chain maps between the naive cotangent complexes of two polynomial presentations which
agree in degrees `-1` and `0` are equal, the other terms being zero. -/
theorem presentationNaiveCotangentComplex_hom_ext
    {p q : presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₁ α₁ ⟶
      presentationNaiveCotangentComplex.{v, u, w, z} J A B a E₂ α₂}
    (hneg : p.f (-1) = q.f (-1)) (hzero : p.f 0 = q.f 0) : p = q := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases h1 : i = -1
  · subst h1; exact hneg
  by_cases h0 : i = 0
  · subst h0; exact hzero
  exact (presentationNaiveCotangentComplex_isZero_X.{v, u, w, z} J A B a E₁ α₁ i h1 h0).eq_of_src
    (p.f i) (q.f i)

end Ext

/-! ### The comparison map at the canonical presentation -/

section CanonicalComparison

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (E : Functor Cᵒᵖ (Type w))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The identity morphism of a presentation induces the identity on conormal sheaves. -/
theorem presentationConormalMap_id :
    presentationConormalMap.{v, u, w, z} J A E E (𝟙 E) B a α α (Category.id_comp α) = 𝟙 _ := by
  have key : ∀ (ψ : Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E ⟶
        Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E)
      (hψ : ψ ≫ presentation J A B a E α = presentation J A B a E α), ψ = 𝟙 _ →
      Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, w, z} J B
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E)
        (presentation J A B a E α) (presentation J A B a E α) ψ hψ = 𝟙 _ := by
    intro ψ hψ hid
    subst hid
    exact Stacks.Sites.Conormal.conormalSheafMapOfFac_id.{v, u, w, z} J
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E) B (presentation J A B a E α)
  exact key _ _ (freeAlgebraMap_id J A E)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The identity morphism of a presentation induces the identity on the scalar extensions of
the modules of differentials. -/
theorem presentationTensorMap_id :
    presentationTensorMap.{v, u, w, z} J A E E (𝟙 E) B a α α (Category.id_comp α) = 𝟙 _ := by
  have key : ∀ (ψ : Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E ⟶
        Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E)
      (hψ : ψ ≫ presentation J A B a E α = presentation J A B a E α)
      (ha : Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E ≫ ψ =
        Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E), ψ = 𝟙 _ →
      Stacks.Sites.Conormal.tensorSheafMapOfFac.{v, u, w, z} J A B
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E)
        (presentation J A B a E α) (presentation J A B a E α) ψ hψ ha = 𝟙 _ := by
    intro ψ hψ ha hid
    subst hid
    exact Stacks.Sites.Conormal.tensorSheafMapOfFac_id.{v, u, w, z} J A
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E) B
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E)
      (presentation J A B a E α)
  exact key _ _ _ (freeAlgebraMap_id J A E)

/-- The chain map induced by the identity morphism of a presentation is the identity. -/
theorem presentationNaiveCotangentComplexMap_id :
    presentationNaiveCotangentComplexMap.{v, u, w, z} J A E E (𝟙 E) B a α α
      (Category.id_comp α) = 𝟙 _ := by
  refine presentationNaiveCotangentComplex_hom_ext.{v, u, w, z} J A B a E E α α ?_ ?_
  · rw [presentationNaiveCotangentComplexMap_f_negOne, presentationConormalMap_id,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
    exact (HomologicalComplex.id_f _ _).symm
  · rw [presentationNaiveCotangentComplexMap_f_zero, presentationTensorMap_id,
      Category.id_comp, eqToHom_trans, eqToHom_refl]
    exact (HomologicalComplex.id_f _ _).symm

/-- **Stacks 08TY**, normalisation at the canonical presentation. The canonical presentation is
the one whose family of generators is the identity of `B`, and there the comparison map
`NL(α) ⟶ NL_{B/A}` is the identity; so the identification of `NL(α)` with `NL_{B/A}` is the
identity for `α = id_B`. -/
@[stacks 08TY "normalisation: the canonical comparison map is the identity at the canonical
presentation"]
theorem naiveCotangentComplexComparison_id :
    naiveCotangentComplexComparison.{v, u, w, z} J A B a
      (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _) = 𝟙 _ :=
  presentationNaiveCotangentComplexMap_id.{v, u, w, z} J A B a
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) (𝟙 _)

end CanonicalComparison

/-! ### Functoriality of the comparison map -/

section ComparisonFunctoriality

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (E₁ E₂ E₃ : Functor Cᵒᵖ (Type w)) (h : E₁ ⟶ E₂) (k : E₂ ⟶ E₃)
  (α₁ : E₁ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  (α₂ : E₂ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  (α₃ : E₃ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₃ α₃).hom]
  (hα : h ≫ α₂ = α₁) (hβ : k ≫ α₃ = α₂)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hα hβ in
/-- The maps of conormal sheaves of two composable morphisms of presentations compose. -/
@[reassoc]
theorem presentationConormalMap_comp :
    presentationConormalMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        presentationConormalMap.{v, u, w, z} J A E₂ E₃ k B a α₂ α₃ hβ =
      presentationConormalMap.{v, u, w, z} J A E₁ E₃ (h ≫ k) B a α₁ α₃
        (by rw [Category.assoc, hβ, hα]) := by
  have hαβ : (h ≫ k) ≫ α₃ = α₁ := by rw [Category.assoc, hβ, hα]
  have key : ∀ (ψ : Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁ ⟶
        Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₃)
      (hψ : ψ ≫ presentation J A B a E₃ α₃ = presentation J A B a E₁ α₁),
      ψ = freeAlgebraMap J A E₁ E₃ (h ≫ k) →
      Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, w, z} J B
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₃)
        (presentation J A B a E₁ α₁) (presentation J A B a E₃ α₃) ψ hψ =
      presentationConormalMap.{v, u, w, z} J A E₁ E₃ (h ≫ k) B a α₁ α₃ hαβ := by
    intro ψ hψ hid
    subst hid
    rfl
  refine Eq.trans (Stacks.Sites.Conormal.conormalSheafMapOfFac_comp.{v, u, w, z} J B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₃)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂) (presentation J A B a E₃ α₃)
    (freeAlgebraMap J A E₁ E₂ h) (freeAlgebraMap J A E₂ E₃ k)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraMap_comp_presentation J A E₂ E₃ k B a α₂ α₃ hβ)) ?_
  exact key _ _ (freeAlgebraMap_comp J A E₁ E₂ h E₃ k)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
include hα hβ in
/-- The maps on the scalar extensions of the modules of differentials of two composable
morphisms of presentations compose. -/
@[reassoc]
theorem presentationTensorMap_comp :
    presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        presentationTensorMap.{v, u, w, z} J A E₂ E₃ k B a α₂ α₃ hβ =
      presentationTensorMap.{v, u, w, z} J A E₁ E₃ (h ≫ k) B a α₁ α₃
        (by rw [Category.assoc, hβ, hα]) := by
  have hαβ : (h ≫ k) ≫ α₃ = α₁ := by rw [Category.assoc, hβ, hα]
  have key : ∀ (ψ : Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁ ⟶
        Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₃)
      (hψ : ψ ≫ presentation J A B a E₃ α₃ = presentation J A B a E₁ α₁)
      (ha : Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₁ ≫ ψ =
        Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₃),
      ψ = freeAlgebraMap J A E₁ E₃ (h ≫ k) →
      Stacks.Sites.Conormal.tensorSheafMapOfFac.{v, u, w, z} J A B
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₃)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₁)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₃)
        (presentation J A B a E₁ α₁) (presentation J A B a E₃ α₃) ψ hψ ha =
      presentationTensorMap.{v, u, w, z} J A E₁ E₃ (h ≫ k) B a α₁ α₃ hαβ := by
    intro ψ hψ ha hid
    subst hid
    rfl
  refine Eq.trans (Stacks.Sites.Conormal.tensorSheafMapOfFac_comp.{v, u, w, z} J A B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₃)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₁)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₂)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₃)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂) (presentation J A B a E₃ α₃)
    (freeAlgebraMap J A E₁ E₂ h) (freeAlgebraMap J A E₂ E₃ k)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraMap_comp_presentation J A E₂ E₃ k B a α₂ α₃ hβ)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₂ E₃ k)) ?_
  exact key _ _ _ (freeAlgebraMap_comp J A E₁ E₂ h E₃ k)

include hα hβ in
/-- The chain maps of two composable morphisms of presentations compose. -/
theorem presentationNaiveCotangentComplexMap_comp :
    presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₂ E₃ k B a α₂ α₃ hβ =
      presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₃ (h ≫ k) B a α₁ α₃
        (by rw [Category.assoc, hβ, hα]) := by
  refine presentationNaiveCotangentComplex_hom_ext.{v, u, w, z} J A B a E₁ E₃ α₁ α₃ ?_ ?_
  · rw [HomologicalComplex.comp_f, presentationNaiveCotangentComplexMap_f_negOne,
      presentationNaiveCotangentComplexMap_f_negOne,
      presentationNaiveCotangentComplexMap_f_negOne]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [presentationConormalMap_comp_assoc]
  · rw [HomologicalComplex.comp_f, presentationNaiveCotangentComplexMap_f_zero,
      presentationNaiveCotangentComplexMap_f_zero,
      presentationNaiveCotangentComplexMap_f_zero]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [presentationTensorMap_comp_assoc]

include hα in
/-- **Stacks 08TY**, compatibility with functorialities. The comparison maps `NL(α) ⟶ NL_{B/A}`
of two polynomial presentations of `B` over `A` are compatible with every morphism of
presentations between them, so the identification of `NL(α)` with `NL_{B/A}` is canonical. -/
@[stacks 08TY "canonicality: the comparison maps are compatible with every morphism of
presentations"]
theorem naiveCotangentComplexComparison_naturality :
    presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        naiveCotangentComplexComparison.{v, u, w, z} J A B a E₂ α₂ =
      naiveCotangentComplexComparison.{v, u, w, z} J A B a E₁ α₁ := by
  have hcomp := presentationNaiveCotangentComplexMap_comp.{v, u, w, z} J A B a E₁ E₂
    (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) h α₂ α₁ α₂ (𝟙 _) hα (Category.comp_id α₂)
  have key : ∀ (m : E₁ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
      (hm : m ≫ 𝟙 (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) = α₁), m = α₁ →
      presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁
        (Stacks.Sites.FreeAlgebra.underlyingPresheaf J B) m B a α₁ (𝟙 _) hm =
      naiveCotangentComplexComparison.{v, u, w, z} J A B a E₁ α₁ := by
    intro m hm hid
    subst hid
    rfl
  exact hcomp.trans (key _ _ hα)

end ComparisonFunctoriality

/-! ### The cohomology sheaves of `NL(α)` -/

section Cohomology

open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite)

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (E : Functor Cᵒᵖ (Type w))
  (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-- The degree `-1` cohomology sheaf of `NL(α)` is the kernel of the conormal map. -/
noncomputable def presentationNaiveCotangentComplexHomologyNegOneIso :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α).homology (-1) ≅
      kernel (presentationConormalSequence.{v, u, w, z} J A B a E α).f := by
  change (HomologicalComplex.double
    (presentationConormalSequence.{v, u, w, z} J A B a E α).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).homology (-1) ≅ _
  exact HomologicalComplex.doubleHomologyIsoKernel _ _ (by decide)

/-- The degree `0` cohomology sheaf of `NL(α)` is the cokernel of the conormal map. -/
noncomputable def presentationNaiveCotangentComplexHomologyZeroIsoCokernel :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α).homology 0 ≅
      cokernel (presentationConormalSequence.{v, u, w, z} J A B a E α).f := by
  change (HomologicalComplex.double
    (presentationConormalSequence.{v, u, w, z} J A B a E α).f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).homology 0 ≅ _
  exact HomologicalComplex.doubleHomologyIsoCokernel _ _ (by decide)

/-- The conormal sequence of a presentation is exact at its middle term and its right-hand map
is an epimorphism, so its right-hand term is the cokernel of the conormal map. -/
noncomputable def presentationConormalSequenceCokernelIso :
    cokernel (presentationConormalSequence.{v, u, w, z} J A B a E α).f ≅
      (presentationConormalSequence.{v, u, w, z} J A B a E α).X₃ :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _)
    (Stacks.Sites.Conormal.conormalSequence_exact.{v, u, w, z} J A
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E) B
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E)
      (presentation J A B a E α)).gIsCokernel

/-- **Stacks 08TY** in degree `0`. For every polynomial presentation `α : E ⟶ B` of `B` over
`A` the degree `0` cohomology sheaf of `NL(α)` is the sheaf of relative differentials
`Ω_{B/A}`, one and the same sheaf of `B`-modules for all `α`; in particular it agrees with the
degree `0` cohomology sheaf of `NL_{B/A}`, which is the case `α = id_B`. -/
@[stacks 08TY "degree 0 of the canonical isomorphism: H⁰(NL(α)) is Ω_{B/A} for every
presentation"]
noncomputable def presentationNaiveCotangentComplexHomologyZeroIso :
    (presentationNaiveCotangentComplex.{v, u, w, z} J A B a E α).homology 0 ≅
      moduleOfDifferentialsOfSite.{v, u, w, z} A B a :=
  presentationNaiveCotangentComplexHomologyZeroIsoCokernel.{v, u, w, z} J A B a E α ≪≫
    presentationConormalSequenceCokernelIso.{v, u, w, z} J A B a E α ≪≫
    Stacks.Sites.Conormal.imageDifferentialsIso.{v, u, w, z} J A
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E) B
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E)
      (presentation J A B a E α) ≪≫
    eqToIso (congrArg (fun φ ↦ moduleOfDifferentialsOfSite.{v, u, w, z} A B φ)
      (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap_comp_desc J A B E a α))

end Cohomology

/-! ### The comparison map in degree `0` -/

section ComparisonDegreeZero

variable (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (E₁ E₂ : Functor Cᵒᵖ (Type w)) (h : E₁ ⟶ E₂)
  (α₁ : E₁ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  (α₂ : E₂ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom]
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]
  (hα : h ≫ α₂ = α₁)

include hα in
/-- **Stacks 08TY** in degree `0`, for the comparison map. A morphism of polynomial
presentations induces an isomorphism on the degree `0` cohomology sheaves of the two naive
cotangent complexes, these being the cokernels of the two conormal maps: both are `Ω_{B/A}`
and the induced map is the identity there. -/
@[stacks 08TY "degree 0: a morphism of presentations induces an isomorphism on H⁰"]
theorem isIso_cokernel_map_presentationConormalSequence_f :
    IsIso (cokernel.map
      (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f
      (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).f
      (presentationConormalMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      (presentationTensorMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα)
      (Stacks.Sites.Conormal.conormalSequence_f_naturality.{v, u, w, z} J A B
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₁)
        (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₂)
        (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
        (freeAlgebraMap J A E₁ E₂ h)
        (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
        (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h))) :=
  Stacks.Sites.Conormal.isIso_cokernel_map_conormalSequence_f.{v, u, w, z} J A B
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₁)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheaf J A E₂)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₁)
    (Stacks.Sites.FreeAlgebra.freeAlgebraSheafCoefficientMap J A E₂)
    (presentation J A B a E₁ α₁) (presentation J A B a E₂ α₂)
    (freeAlgebraMap J A E₁ E₂ h)
    (freeAlgebraMap_comp_presentation J A E₁ E₂ h B a α₁ α₂ hα)
    (freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap J A E₁ E₂ h)

end ComparisonDegreeZero

end Stacks.SheafOfModules

add_to_stacks 08TJ Stacks.SheafOfModules.naiveCotangentComplex
add_to_stacks 08TI "the displayed two-term complex `I/I² ⟶ Ω_{A[B]/A} ⊗_{A[B]} B`"
  Stacks.SheafOfModules.naiveCotangentComplex
