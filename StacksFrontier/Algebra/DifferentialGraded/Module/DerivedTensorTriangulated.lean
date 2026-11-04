module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFunctor
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorTriangulated
public import StacksFrontier.CategoryTheory.Functor.Derived.OrthogonalResolutions
public import StacksFrontier.CategoryTheory.Localization.LeftDerivedByResolutions
public import StacksFrontier.Homology.PseudoCoherent.BaseChange

/-! # The derived tensor product with a differential graded bimodule is exact

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. The derived tensor product
`- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` of Tag 09LS is the total left derived functor of tensoring with
`N` followed by localization. This file equips it with the two structures that make it a functor
of triangulated categories: a commutation with the translation, and the preservation of
distinguished triangles.

## Main results

* `DifferentialGraded.Bimodule.derivedTensorFunctor_commShift`: `- ⊗_A^𝐋 N` commutes with the
  translation.
* `DifferentialGraded.Bimodule.derivedTensorFunctor_isTriangulated`: `- ⊗_A^𝐋 N` is exact, that
  is, it carries distinguished triangles of `D(A, d)` to distinguished triangles of `D(B, d)`.

Both are instances, so `(derivedTensorFunctor N).mapTriangle` and the statement that a morphism
is a morphism of distinguished triangles become available.

## Implementation notes

*The two clauses are not independent.* `CategoryTheory.Functor.IsTriangulated` takes the
commutation with the translation as an instance argument, since `F.mapTriangle` is built from
it; the exactness statement is therefore *about* the structure that
`derivedTensorFunctor_commShift` provides, and that structure has to be seated as an instance
before exactness can even be stated.

*Route to the commutation.* A total left derived functor commutes with the translation whenever
the functor being derived does, the localization functor does, and the class being inverted is
stable under it. This is `StacksDraft.PseudoCoherence.leftDerivedCommShift`, and
`StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility` says the counit is compatible
with the resulting isomorphisms — which is the hypothesis
`CategoryTheory.Functor.isTriangulated_of_rightExtension` consumes.

*Why the commutation of the underived functor has to be chosen.* Tag 09LR is formalized as
`DifferentialGraded.Bimodule.tensorHomotopyFunctor_isTriangulated'`, which is existentially
quantified over the commutation isomorphisms: it asserts that *some* `CommShift` structure on
`- ⊗_A N : K(A, d) ⥤ K(B, d)` makes that functor exact, the witness being built from the
sign-free comparison `(M ⊗_A N)[k] ≅ M[k] ⊗_A N` of Tag 0FQN but not exported. The two
declarations below select that witness and the exactness statement paired with it, which is
exactly what is needed: the pair, not either half separately, is what the argument consumes.

*Route to exactness.* `CategoryTheory.Functor.isTriangulated_of_rightExtension` needs every
morphism of `D(A, d)` to be, up to isomorphism of arrows, the image of a morphism between
objects of `K(A, d)` at which the counit is invertible, together with a distinguished triangle
on that morphism whose three vertices all have invertible counit. The resolving class taken here
is the left orthogonal `⊥(acyclic)` of the acyclic modules, and the three ingredients are: it
resolves every object of `K(A, d)` (Tag 09KP followed by Tag 09KM, assembled in
`DifferentialGradedModule.exists_quasiIso_leftOrthogonal_acyclic`), so the inclusion of the
left orthogonal is a localized equivalence and the induced functor is essentially surjective on
*arrows*; the counit is invertible at every object of the left orthogonal, because a
quasi-isomorphism between two such objects is already an isomorphism of `K(A, d)`
(`CategoryTheory.ObjectProperty.isIso_of_trW_of_leftOrthogonal`), so the underived functor
inverts it; and the left orthogonal of a triangulated subcategory is a triangulated subcategory,
hence contains the third vertex of a distinguished triangle whose first two vertices it contains.

*No tag.* Tag 09LS asserts the existence of `- ⊗_A^𝐋 N`, and Tag 09LR the exactness of the
underived functor on homotopy categories; the source does not separately state that the derived
functor is exact, so nothing here carries a `stacks` attribute.

## References

* [Stacks Project, Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) names the functor; the
  exactness of the underived functor is [Tag 09LR](https://stacks.math.columbia.edu/tag/09LR),
  the resolutions are [Tag 09KP](https://stacks.math.columbia.edu/tag/09KP) and their
  orthogonality [Tag 09KM](https://stacks.math.columbia.edu/tag/09KM).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- Every object of `K(A, d)` receives a quasi-isomorphism from an object orthogonal on the left
to the acyclic modules.

This is `DifferentialGradedModule.exists_quasiIso_leftOrthogonal_acyclic` read in the homotopy
category, in the shape the resolution machinery of
`CategoryTheory.LeftDerivedByResolutions` consumes. -/
theorem exists_quasiIso_leftOrthogonal_acyclic_homotopy (X : HomotopyCategory A) :
    ∃ (P : HomotopyCategory A) (_ : (acyclic' A).leftOrthogonal P) (s : P ⟶ X),
      quasiIsomorphisms' A s := by
  obtain ⟨P, s, hs, hP⟩ := exists_trW_leftOrthogonal_of_exists_quasiIso_leftOrthogonal A
    (exists_quasiIso_leftOrthogonal_acyclic A) X
  exact ⟨P, hP, s, by rwa [← acyclic_trW_eq_quasiIsomorphisms']⟩

/-- Left orthogonality to the acyclic modules passes to the cone: in a distinguished triangle of
`K(A, d)` whose first two vertices are orthogonal on the left to the acyclic modules, the third
vertex is too.  The left orthogonal of a triangulated subcategory is a triangulated
subcategory. -/
theorem leftOrthogonal_acyclic_obj₃_of_distTriang (T : Triangle (HomotopyCategory A))
    (hT : T ∈ distTriang _) (h₁ : (acyclic' A).leftOrthogonal T.obj₁)
    (h₂ : (acyclic' A).leftOrthogonal T.obj₂) : (acyclic' A).leftOrthogonal T.obj₃ :=
  (acyclic' A).leftOrthogonal.ext_of_isTriangulatedClosed₃ T hT h₁ h₂

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- The commutation with the translation of `- ⊗_A N : K(A, d) ⥤ K(B, d)` for which that functor
is exact, chosen from **Stacks Tag 09LR**
(`DifferentialGraded.Bimodule.tensorHomotopyFunctor_isTriangulated'`). Its components come from
the sign-free comparison `(M ⊗_A N)[k] ≅ M[k] ⊗_A N` of Tag 0FQN. -/
instance tensorHomotopyFunctorCommShift' (N : Bimodule A B) :
    (tensorHomotopyFunctor N).CommShift ℤ :=
  tensorHomotopyCommShift N

/-- **Stacks Tag 09LR** as an instance: tensoring with `N` carries distinguished triangles of
`K(A, d)` to distinguished triangles of `K(B, d)`, with respect to the commutation with the
translation of `DifferentialGraded.Bimodule.tensorHomotopyFunctorCommShift'`. -/
instance isTriangulated_tensorHomotopyFunctor' (N : Bimodule A B) :
    (tensorHomotopyFunctor N).IsTriangulated :=
  letI : NatTrans.CommShift (tensorHomotopyLiftIso N).hom ℤ :=
    Functor.CommShift.ofIso_compatibility (tensorHomotopyLiftIso N) ℤ
  Functor.isTriangulated_of_iso (tensorHomotopyLiftIso N)

/-- Tensoring with `N`, followed by localization, inverts a quasi-isomorphism between two
objects of `K(A, d)` orthogonal on the left to the acyclic modules: such a quasi-isomorphism is
already an isomorphism of `K(A, d)`. -/
theorem isIso_tensorFunctorToDerivedCategory_map_of_leftOrthogonal (N : Bimodule A B)
    {X Y : HomotopyCategory A} (s : X ⟶ Y) (hs : quasiIsomorphisms' A s)
    (hX : (acyclic' A).leftOrthogonal X) (hY : (acyclic' A).leftOrthogonal Y) :
    IsIso ((tensorFunctorToDerivedCategory N).map s) := by
  have : IsIso s := (acyclic' A).isIso_of_trW_of_leftOrthogonal s
    (by rw [acyclic_trW_eq_quasiIsomorphisms']; exact hs) hX hY
  infer_instance

/-- **The comparison `P ⊗_A^𝐋 N → P ⊗_A N` is invertible when `P` is orthogonal on the left to
the acyclic modules.** Those objects resolve every object of `K(A, d)` and tensoring with `N`
inverts the quasi-isomorphisms between them, so they compute the left derived functor. -/
theorem isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal (N : Bimodule A B)
    (X : HomotopyCategory A) (hX : (acyclic' A).leftOrthogonal X) :
    IsIso ((derivedTensorFunctorCounit N).app X) :=
  LeftDerivedByResolutions.isIso_app_of_resolutions (quasiIsomorphisms' A)
    (acyclic' A).leftOrthogonal (exists_quasiIso_leftOrthogonal_acyclic_homotopy A)
    (tensorFunctorToDerivedCategory N)
    (fun s hs hX hY =>
      isIso_tensorFunctorToDerivedCategory_map_of_leftOrthogonal N s hs hX hY)
    (quasiIsomorphisms' A).Q (derivedTensorFunctor N) (derivedTensorFunctorCounit N) X hX

/-- **The derived tensor product commutes with the translation.** `- ⊗_A^𝐋 N` is the total left
derived functor of tensoring with `N` along the localization of `K(A, d)` at the
quasi-isomorphisms; tensoring with `N` and the localization functor both commute with the
translation, and the quasi-isomorphisms are stable under it, so the derived functor does too. -/
@[instance_reducible]
instance derivedTensorFunctor_commShift (N : Bimodule A B) :
    (derivedTensorFunctor N).CommShift ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift (derivedTensorFunctor N)
    (derivedTensorFunctorCounit N) (quasiIsomorphisms' A) ℤ

/-- The comparison `- ⊗_A^𝐋 N → - ⊗_A N` is compatible with the commutation with the translation
of `DifferentialGraded.Bimodule.derivedTensorFunctor_commShift`. This is what makes the
exactness argument below run. -/
instance derivedTensorFunctorCounit_commShift (N : Bimodule A B) :
    NatTrans.CommShift (derivedTensorFunctorCounit N) ℤ :=
  StacksDraft.PseudoCoherence.leftDerivedCommShift_compatibility (derivedTensorFunctor N)
    (derivedTensorFunctorCounit N) (quasiIsomorphisms' A) ℤ

/-- **The derived tensor product is exact**: `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` carries
distinguished triangles to distinguished triangles.

Every morphism of `D(A, d)` is, up to isomorphism of arrows, the image of a morphism between
objects of `K(A, d)` orthogonal on the left to the acyclic modules: those objects resolve every
object, so their inclusion is a localized equivalence and the induced functor is essentially
surjective on arrows. Completing such a morphism to a distinguished triangle of `K(A, d)` leaves
all three vertices in the left orthogonal, the third because the left orthogonal of a
triangulated subcategory is a triangulated subcategory, and the comparison
`- ⊗_A^𝐋 N → - ⊗_A N` is invertible at each of them. That is exactly the input of
`CategoryTheory.Functor.isTriangulated_of_rightExtension`. -/
instance derivedTensorFunctor_isTriangulated (N : Bimodule A B) :
    (derivedTensorFunctor N).IsTriangulated := by
  have : (LeftDerivedByResolutions.inclusionLocalizerMorphism (quasiIsomorphisms' A)
      (acyclic' A).leftOrthogonal).HasLeftResolutions := fun M => by
    obtain ⟨P, hP, s, hs⟩ := exists_quasiIso_leftOrthogonal_acyclic_homotopy A M
    exact ⟨{ X₁ := ⟨P, hP⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (quasiIsomorphisms' A) (acyclic' A).leftOrthogonal
  have := LeftDerivedByResolutions.hasRightCalculusOfFractions_inverseImage_ι
    (quasiIsomorphisms' A) (acyclic' A).leftOrthogonal
  have : ((acyclic' A).leftOrthogonal.ι ⋙ (quasiIsomorphisms' A).Q).IsLocalization
      ((quasiIsomorphisms' A).inverseImage (acyclic' A).leftOrthogonal.ι) :=
    LocalizerMorphism.IsLocalizedEquivalence.isLocalization
      (LeftDerivedByResolutions.inclusionLocalizerMorphism (quasiIsomorphisms' A)
        (acyclic' A).leftOrthogonal) (quasiIsomorphisms' A).Q
  have := Localization.essSurj_mapArrow_of_hasRightCalculusOfFractions
    ((acyclic' A).leftOrthogonal.ι ⋙ (quasiIsomorphisms' A).Q)
    ((quasiIsomorphisms' A).inverseImage (acyclic' A).leftOrthogonal.ι)
  refine Functor.isTriangulated_of_rightExtension (derivedTensorFunctor N)
    (derivedTensorFunctorCounit N) (fun {X Y} g => ?_)
  obtain ⟨a, ⟨ea⟩⟩ := Functor.EssSurj.mem_essImage
    (F := ((acyclic' A).leftOrthogonal.ι ⋙ (quasiIsomorphisms' A).Q).mapArrow) (Arrow.mk g)
  obtain ⟨Z, u, v, hT⟩ := distinguished_cocone_triangle
    ((acyclic' A).leftOrthogonal.ι.map a.hom)
  have h₁ : (acyclic' A).leftOrthogonal
      (Triangle.mk ((acyclic' A).leftOrthogonal.ι.map a.hom) u v).obj₁ := a.left.property
  have h₂ : (acyclic' A).leftOrthogonal
      (Triangle.mk ((acyclic' A).leftOrthogonal.ι.map a.hom) u v).obj₂ := a.right.property
  exact ⟨Triangle.mk ((acyclic' A).leftOrthogonal.ι.map a.hom) u v, hT,
    isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N _ h₁,
    isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N _ h₂,
    isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N _
      (leftOrthogonal_acyclic_obj₃_of_distTriang A _ hT h₁ h₂), ⟨ea⟩⟩

end DifferentialGraded.Bimodule

end
