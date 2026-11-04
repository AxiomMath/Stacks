module

public import Mathlib.Algebra.Category.CommAlgCat.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.RingTheory.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic

/-!
# Seminormalization and absolute weak normalization of a ring

For a commutative ring `A`, its seminormalization is the colimit of the finitely presented
`A`-algebras whose spectra are universal homeomorphisms over `Spec A` and whose maps on
residue fields are isomorphisms. Dropping the condition on residue fields and taking the
colimit instead gives the absolute weak normalization of `A`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.InducesResidueFieldIsomorphisms` says that a morphism of
  schemes induces isomorphisms on all residue fields.
* `Algebra.FinitelyPresentedAlgebraPresentation` is a small collection of explicit
  representatives for the finitely presented algebras over a ring.
* `Algebra.seminormalization` is the seminormalization of a commutative ring, regarded as a
  bundled commutative algebra over that ring.
* `Algebra.AbsoluteWeakNormalizationIndex` is a small category of representatives of the
  finitely presented algebras whose spectrum maps are universal homeomorphisms.
* `Algebra.AbsoluteWeakNormalization` is their colimit.

## Main results

* `Algebra.absoluteWeakNormalizationDiagram_obj_finitePresentation` and
  `Algebra.absoluteWeakNormalizationDiagram_obj_universalHomeomorphism` expose the defining
  properties of the diagram's objects.

Both colimits carry their canonical `A`-algebra structure, whose structure map is
`algebraMap A _`.

## Implementation notes

In the seminormalization, finitely presented algebras are represented by quotients of
finite-variable polynomial rings by finitely generated ideals. This gives an actually small
indexing category without choosing a skeleton; morphisms in the indexing category are all
algebra homomorphisms between the represented algebras.

The absolute weak normalization instead uses that the category of all relevant algebras is
essentially small, because every finitely presented algebra is of finite type and hence has a
representative among quotients of finite-variable polynomial rings. `SmallModel` chooses a
genuinely small equivalent category; its inverse equivalence followed by the inclusion gives
`absoluteWeakNormalizationDiagram`. `AbsoluteWeakNormalization` is an abbreviation for the
carrier of the colimit in `CommAlgCat A`, which exposes the colimit's commutative-ring and
`A`-algebra instances directly to clients.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme morphism induces isomorphisms on residue fields if its canonical residue-field
map at every point is an isomorphism. -/
abbrev InducesResidueFieldIsomorphisms {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x : X, IsIso (f.residueFieldMap x)

end AlgebraicGeometry.Scheme.Hom

noncomputable section

namespace Algebra

/-- A small collection of explicit representatives for finitely presented `A`-algebras. -/
structure FinitelyPresentedAlgebraPresentation (A : Type u) [CommRing A] where
  /-- The finite number of polynomial generators. -/
  generators : ℕ
  /-- The ideal of relations. -/
  relations : Ideal (MvPolynomial (Fin generators) A)
  /-- The relations are finitely generated. -/
  relations_fg : relations.FG

namespace FinitelyPresentedAlgebraPresentation

variable {A : Type u} [CommRing A]

/-- The algebra represented by a finite presentation. -/
def algebra (P : FinitelyPresentedAlgebraPresentation A) : CommAlgCat.{u} A :=
  CommAlgCat.of A (MvPolynomial (Fin P.generators) A ⧸ P.relations)

/-- The algebra represented by a finite presentation is finitely presented. -/
instance (P : FinitelyPresentedAlgebraPresentation A) :
    Algebra.FinitePresentation A P.algebra :=
  Algebra.FinitePresentation.quotient P.relations_fg

/-- Finite presentations form a category whose morphisms are the `A`-algebra maps between the
represented algebras. -/
instance : Category.{u} (FinitelyPresentedAlgebraPresentation A) where
  Hom P Q := P.algebra ⟶ Q.algebra
  id P := 𝟙 P.algebra
  comp f g := f ≫ g
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

/-- The diagram sending a finite presentation to its represented algebra. -/
@[implicit_reducible]
def diagram (A : Type u) [CommRing A] :
    FinitelyPresentedAlgebraPresentation A ⥤ CommAlgCat.{u} A where
  obj P := P.algebra
  map f := f

end FinitelyPresentedAlgebraPresentation

/-- The small category of finite presentations whose spectra are subintegral over `Spec A`. -/
abbrev SeminormalizationIndex (A : Type u) [CommRing A] :=
  ObjectProperty.FullSubcategory (fun P : FinitelyPresentedAlgebraPresentation A ↦
    UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A P.algebra))) ∧
      Scheme.Hom.InducesResidueFieldIsomorphisms
        (Spec.map (CommRingCat.ofHom (algebraMap A P.algebra))))

/-- The diagram of all finite-presentation representatives which are subintegral over `A`. -/
@[implicit_reducible]
def seminormalizationDiagram (A : Type u) [CommRing A] :
    SeminormalizationIndex A ⥤ CommAlgCat.{u} A :=
  ObjectProperty.ι _ ⋙ FinitelyPresentedAlgebraPresentation.diagram A

/-- The seminormalization `Aˢⁿ` is the colimit of the finitely presented `A`-algebras
which induce a universal homeomorphism on spectra and isomorphisms on residue fields. Its
`A`-algebra structure is the canonical map `A → Aˢⁿ`. -/
@[stacks 0EUR "seminormalization_of_a_ring"]
def seminormalization (A : Type u) [CommRing A] : CommAlgCat.{u} A :=
  colimit (seminormalizationDiagram A)

/-- The property defining the algebras used to construct the absolute weak normalization:
finite presentation over the base and a universal homeomorphism on spectra. -/
abbrev absoluteWeakNormalizationObject (A : Type u) [CommRing A] :
    ObjectProperty (CommAlgCat.{u} A) :=
  fun B => Algebra.FinitePresentation A B ∧
    UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)

/-- The relevant finitely presented algebras form an essentially small object property. -/
instance absoluteWeakNormalizationObject_essentiallySmall (A : Type u) [CommRing A] :
    ObjectProperty.EssentiallySmall.{u} (absoluteWeakNormalizationObject A) :=
  ⟨⟨ObjectProperty.ofObj (fun P : FGAlgCatSkeleton A ↦ (P.eval).obj), inferInstance, by
    intro B hB
    have : Algebra.FinitePresentation A B := hB.1
    have : Algebra.FiniteType A B := Algebra.FiniteType.of_finitePresentation
    obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton A (B : Type u)
    exact ⟨(P.eval).obj, ObjectProperty.ofObj_apply _ P, ⟨CommAlgCat.isoMk e⟩⟩⟩⟩

/-- The full category of algebras used in the construction is essentially small. -/
instance absoluteWeakNormalizationIndex_essentiallySmall (A : Type u) [CommRing A] :
    EssentiallySmall.{u} ((absoluteWeakNormalizationObject A).FullSubcategory) := by
  have : LocallySmall.{u} (CommAlgCat.{u} A) := CategoryTheory.locallySmall_self _
  infer_instance

/-- A small category of representatives of finitely presented `A`-algebras whose maps on
spectra are universal homeomorphisms. -/
@[stacks 0EUR "absolute_weak_normalization_of_a_ring"]
abbrev AbsoluteWeakNormalizationIndex (A : Type u) [CommRing A] : Type u :=
  @SmallModel.{u, u, u + 1} ((absoluteWeakNormalizationObject A).FullSubcategory) inferInstance
    (absoluteWeakNormalizationIndex_essentiallySmall A)

/-- The diagram of `A`-algebras represented by `AbsoluteWeakNormalizationIndex A`. -/
@[implicit_reducible]
def absoluteWeakNormalizationDiagram (A : Type u) [CommRing A] :
    AbsoluteWeakNormalizationIndex A ⥤ CommAlgCat.{u} A :=
  (equivSmallModel.{u} ((absoluteWeakNormalizationObject A).FullSubcategory)).inverse ⋙
    ObjectProperty.ι (absoluteWeakNormalizationObject A)

/-- Every algebra in the absolute weak normalization diagram is finitely presented. -/
instance absoluteWeakNormalizationDiagram_obj_finitePresentation (A : Type u) [CommRing A]
    (B : AbsoluteWeakNormalizationIndex A) :
    Algebra.FinitePresentation A ((absoluteWeakNormalizationDiagram A).obj B) :=
  ((equivSmallModel.{u}
    ((absoluteWeakNormalizationObject A).FullSubcategory)).inverse.obj B).property.1

/-- The spectrum map of every algebra in the absolute weak normalization diagram is a
universal homeomorphism. -/
instance absoluteWeakNormalizationDiagram_obj_universalHomeomorphism (A : Type u) [CommRing A]
    (B : AbsoluteWeakNormalizationIndex A) :
    UniversalHomeomorphism (Scheme.Spec.map (CommRingCat.ofHom
      (algebraMap A ((absoluteWeakNormalizationDiagram A).obj B))).op) :=
  ((equivSmallModel.{u}
    ((absoluteWeakNormalizationObject A).FullSubcategory)).inverse.obj B).property.2

/-- The absolute weak normalization `Aᵃʷⁿ` is the colimit of all finitely presented
`A`-algebras whose maps on spectra are universal homeomorphisms. Its inherited `A`-algebra
structure supplies the canonical map `A → Aᵃʷⁿ`. -/
@[stacks 0EUR "absolute_weak_normalization_of_a_ring"]
abbrev AbsoluteWeakNormalization (A : Type u) [CommRing A] : Type u :=
  (colimit (absoluteWeakNormalizationDiagram A) : CommAlgCat.{u} A)

end Algebra

end

end
