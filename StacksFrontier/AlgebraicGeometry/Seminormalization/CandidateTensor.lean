module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Seminormalization.CandidateCategory
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleLocalizationQuasiFinite.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.RingColimit
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapPullback

/-!
# Tensor products of seminormalization candidates

Let `A` be a commutative ring and let `B` and `C` be `A`-algebras whose spectrum morphisms to
`Spec A` are universal homeomorphisms inducing isomorphisms on all residue fields.  This file
shows that `B ⊗[A] C` has the same two properties over `A`, which is what produces an upper
bound for a pair of objects of `Algebra.SeminormalizationIndex A`.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_specMap_tensorProduct_includeRight` and
  `AlgebraicGeometry.isIso_residueFieldMap_specMap_tensorProduct_includeRight`: the projection
  `Spec (B ⊗[A] C) ⟶ Spec C` inherits both properties from `Spec B ⟶ Spec A`.
* `AlgebraicGeometry.universalHomeomorphism_specMap_tensorProduct_includeLeft`: the same for
  the other projection, obtained from the commutativity isomorphism of the tensor product.
* `AlgebraicGeometry.universalHomeomorphism_specMap_tensorProduct` and
  `AlgebraicGeometry.isIso_residueFieldMap_specMap_tensorProduct`: `B ⊗[A] C` is again a
  universal homeomorphism over `A` inducing isomorphisms on residue fields.
* `Algebra.FinitePresentation.tensorProduct`: a tensor product of two finitely presented
  algebras is finitely presented.

## Implementation notes

The route is entirely by base change.  `AlgebraicGeometry.pullbackSpecIso` identifies
`Spec (B ⊗[A] C)` with the fibre product of `Spec B` and `Spec C` over `Spec A` in such a way
that the projection induced by `Algebra.TensorProduct.includeRight` becomes
`CategoryTheory.Limits.pullback.snd`.  Universal homeomorphisms are stable under base change
because they are defined through `CategoryTheory.MorphismProperty.universally`; for residue
fields the input is `AlgebraicGeometry.pullback_snd_residueFieldMap_isIso`, which says that at a
point of a fibre product where one projection is residually trivial so is the other.  The left
projection is deduced from the right one rather than proved again, using
`Algebra.TensorProduct.comm`.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUS is used: `A`, `B` and `C` are arbitrary commutative
rings, with no Noetherian, reducedness or finiteness assumption except where finite
presentation is itself the conclusion.

## What is not done

Nothing here is about the indexing category of the seminormalization diagram, and nothing here
mentions a colimit; the filteredness of that category is proved in
`StacksFrontier.AlgebraicGeometry.Seminormalization.IndexFiltered`.  The statement that a
tensor product of candidates is a candidate is proved only for the two conditions appearing in
`Algebra.SeminormalizationIndex`, and is not packaged as a statement about
`AlgebraicGeometry.IsSeminormalizationCandidate`, which is a property of objects of `Over X`
for a scheme `X` rather than of algebras.

## References

* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Algebra.FinitePresentation

/-- A tensor product of two finitely presented algebras over a commutative ring is finitely
presented. -/
theorem tensorProduct (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.FinitePresentation A B]
    [Algebra.FinitePresentation A C] :
    Algebra.FinitePresentation A (B ⊗[A] C) := by
  have : Algebra.FinitePresentation A (C ⊗[A] B) :=
    Algebra.FinitePresentation.trans A C (C ⊗[A] B)
  exact Algebra.FinitePresentation.equiv (Algebra.TensorProduct.comm A C B)

end Algebra.FinitePresentation

namespace AlgebraicGeometry

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- The projection `Spec (B ⊗[A] C) ⟶ Spec C` is the base change of `Spec B ⟶ Spec A`. -/
private lemma pullbackSpecIso_hom_comp_includeRight :
    (pullbackSpecIso A B C).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom) =
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (Spec.map (CommRingCat.ofHom (algebraMap A C))) := by
  simp

/-- The structure morphism of `B ⊗[A] C` over `A` factors through the projection to `Spec C`. -/
private lemma specMap_algebraMap_tensorProduct :
    Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C))) =
      Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  exact (Algebra.TensorProduct.includeRight.commutes a).symm

/-- If `Spec B ⟶ Spec A` is a universal homeomorphism, so is its base change
`Spec (B ⊗[A] C) ⟶ Spec C`. -/
theorem universalHomeomorphism_specMap_tensorProduct_includeRight
    (hB : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom)) := by
  refine ⟨(MorphismProperty.cancel_left_of_respectsIso _ (pullbackSpecIso A B C).hom _).mp ?_⟩
  rw [pullbackSpecIso_hom_comp_includeRight A B C]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback _ _) hB.universally_isHomeomorph

/-- If `Spec B ⟶ Spec A` induces isomorphisms on residue fields, so does its base change
`Spec (B ⊗[A] C) ⟶ Spec C`. -/
theorem isIso_residueFieldMap_specMap_tensorProduct_includeRight
    (hB : ∀ x : Spec (CommRingCat.of B),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap x))
    (x : Spec (CommRingCat.of (B ⊗[A] C))) :
    IsIso (Scheme.Hom.residueFieldMap (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom)) x) := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let g := Spec.map (CommRingCat.ofHom (algebraMap A C))
  let p := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom)
  let e := pullbackSpecIso A B C
  let z : ↑(pullback f g) := e.inv x
  have hz : e.hom z = x := by simp [z]
  have hcomp : IsIso ((e.hom ≫ p).residueFieldMap z) := by
    rw [pullbackSpecIso_hom_comp_includeRight A B C]
    exact pullback_snd_residueFieldMap_isIso f g z (hB _)
  have : IsIso (p.residueFieldMap (e.hom z) ≫ e.hom.residueFieldMap z) := by
    rwa [← Scheme.residueFieldMap_comp]
  rw [← hz]
  exact IsIso.of_isIso_comp_right _ (e.hom.residueFieldMap z)

/-- If `Spec B ⟶ Spec A` is a universal homeomorphism, so is the other projection
`Spec (C ⊗[A] B) ⟶ Spec C`. -/
theorem universalHomeomorphism_specMap_tensorProduct_includeLeft
    (hB : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B)))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := C) (B := B)))) := by
  let ρ : CommRingCat.of (C ⊗[A] B) ≅ CommRingCat.of (B ⊗[A] C) :=
    RingEquiv.toCommRingCatIso (Algebra.TensorProduct.comm A C B).toRingEquiv
  let i : Spec (CommRingCat.of (B ⊗[A] C)) ⟶ Spec (CommRingCat.of (C ⊗[A] B)) := Spec.map ρ.hom
  let p := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom)
  let q := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := C) (B := B)))
  have hcomp : i ≫ q = p := by
    have hr : CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := C) (B := B)) ≫ ρ.hom =
        CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom := by
      apply CommRingCat.hom_ext
      have he : (Algebra.TensorProduct.comm A C B).toAlgHom.comp
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := C) (B := B)) =
          Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C) :=
        Algebra.TensorProduct.comm_comp_includeLeft A C B
      exact congrArg (fun φ : C →ₐ[A] B ⊗[A] C => φ.toRingHom) he
    simpa [i, p, q, Spec.map_comp] using congrArg Spec.map hr
  have hq : q = (asIso i).inv ≫ p := by
    calc
      q = (asIso i).inv ≫ (i ≫ q) := by simp
      _ = (asIso i).inv ≫ p := by rw [hcomp]
  show UniversalHomeomorphism q
  rw [hq]
  exact hasTwoOutOfThreeProperty_universalHomeomorphism.comp_mem _ _
    (universalHomeomorphism_of_isIso _)
    (universalHomeomorphism_specMap_tensorProduct_includeRight A B C hB)

/-- A tensor product of two `A`-algebras whose spectrum morphisms to `Spec A` are universal
homeomorphisms again has universal homeomorphic spectrum morphism to `Spec A`. -/
theorem universalHomeomorphism_specMap_tensorProduct
    (hB : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hC : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C)))) :
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C)))) := by
  rw [specMap_algebraMap_tensorProduct A B C]
  exact hasTwoOutOfThreeProperty_universalHomeomorphism.comp_mem _ _
    (universalHomeomorphism_specMap_tensorProduct_includeRight A B C hB) hC

/-- A tensor product of two `A`-algebras whose spectrum morphisms to `Spec A` induce
isomorphisms on all residue fields again induces isomorphisms on all residue fields. -/
theorem isIso_residueFieldMap_specMap_tensorProduct
    (hB : ∀ x : Spec (CommRingCat.of B),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A B))).residueFieldMap x))
    (hC : ∀ x : Spec (CommRingCat.of C),
      IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A C))).residueFieldMap x))
    (x : Spec (CommRingCat.of (B ⊗[A] C))) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] C)))).residueFieldMap x) := by
  rw [specMap_algebraMap_tensorProduct A B C, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (hC _)
    (isIso_residueFieldMap_specMap_tensorProduct_includeRight A B C hB x)

end AlgebraicGeometry

end
