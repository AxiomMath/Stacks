module

public import StacksFrontier.AlgebraicGeometry.Seminormalization.Colimit
public import Mathlib.CategoryTheory.Presentable.Finite
import StacksFrontier.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.FinitePresentation

/-!
# The universal property of the seminormalization of a ring, for finite presentations

For a commutative ring `A`, `Algebra.seminormalization A` is the colimit of the diagram of
finitely presented `A`-algebras whose structure morphism on spectra is a universal homeomorphism
inducing isomorphisms on all residue fields.  This file proves that it receives exactly one
`A`-algebra map from every *finitely presented* such algebra.

## Main definitions

* `AlgebraicGeometry.canonicalHomToSeminormalization`: the canonical `A`-algebra map from a
  finitely presented seminormalization candidate to `Algebra.seminormalization A`.
* `AlgebraicGeometry.uniqueHomToSeminormalization`: that map is the only one.
* `AlgebraicGeometry.IsFinitelyPresentedCandidateUnder`: the same two conditions, plus finite
  presentation, as a property of objects of `CategoryTheory.Under (CommRingCat.of A)`.
* `AlgebraicGeometry.seminormalizationUnder` and
  `AlgebraicGeometry.canonicalUnderHomToSeminormalization`: the seminormalization and the
  canonical map, repackaged in `Under (CommRingCat.of A)`.

## Main results

* `AlgebraicGeometry.hom_seminormalization_eq_of_algEquiv`: an `A`-algebra map from a finitely
  presented candidate `C` to `Algebra.seminormalization A` is determined by any presentation of
  `C` as the algebra of an object of `Algebra.SeminormalizationIndex A`: it is the inverse of
  that presentation followed by the colimit inclusion.
* `AlgebraicGeometry.subsingleton_hom_seminormalization`: there is at most one such map.
* `AlgebraicGeometry.subsingleton_underHom_seminormalization`: the same, in
  `Under (CommRingCat.of A)`.

## Implementation notes

Finite presentability in the categorical sense, `CategoryTheory.IsFinitelyPresentable`, is
available for objects of `CategoryTheory.Under (CommRingCat.of A)` and not for objects of
`CommAlgCat A`, so the factorization of a map through a stage of the colimit is obtained in
`Under (CommRingCat.of A)`, through the image of the colimit cocone under
`CommAlgCat.commAlgCatEquivUnder`.  That functor is an equivalence, hence full and faithful, so
the factoring map is transported back to `CommAlgCat A` by `CategoryTheory.Functor.preimage` and
the resulting identity is checked by `CategoryTheory.Functor.map_injective`.  This replaces the
unit-isomorphism conjugation that would otherwise be needed.

Once the factoring map `qA : C ⟶ (seminormalizationDiagram A).obj j` is available, no
filteredness is used: the composite of the chosen presentation with `qA` *is* a morphism of
`Algebra.SeminormalizationIndex A`, because that category is a full subcategory of
`Algebra.FinitelyPresentedAlgebraPresentation A`, whose morphisms are by definition all algebra
maps between the represented algebras, and `Algebra.seminormalizationDiagram` acts as the
identity on morphisms.  Cocone naturality then finishes.  Filteredness of the index,
`AlgebraicGeometry.seminormalizationIndex_isFiltered`, is still needed, but only as the
hypothesis of `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit`.

The `Under (CommRingCat.of A)` repackaging at the end of the file exists because that is the
category in which Tag 0EUJ states its filtered-colimit presentation.  It costs nothing: with
the algebra structure `CommRingCat.Hom.hom.toAlgebra` on `C.right`, the identities
`(commAlgCatEquivUnder (CommRingCat.of A)).functor.obj (CommAlgCat.of A C.right) = C` and
`Spec.map (CommRingCat.ofHom (algebraMap A C.right)) = Spec.map C.hom` both hold by `rfl`, so
no transport along an isomorphism of objects is needed, only the full faithfulness of the
equivalence on morphisms.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUR is used on `A`: it is an arbitrary commutative ring, with
no Noetherian or reducedness assumption.  The extra hypothesis here, relative to Tag 0EUR, is
that the source algebra is finitely presented.

## What is not done

Terminality of `Algebra.seminormalization A` among *all* `A`-algebras with the two candidate
properties is not proved here; only the finitely presented ones are treated.  The passage to an
arbitrary candidate is exactly Tag 0EUJ, the presentation of such an algebra as a filtered
colimit of finitely presented ones, for which no declaration exists in the Lean libraries of
this repository.  See
`StacksFrontier.AlgebraicGeometry.Seminormalization.UniversalPropertyOfInd` for the reduction of
the general statement to that one.

Nothing here is about schemes: the initial object of
`AlgebraicGeometry.SeminormalizationCategory X` is not constructed, not even for `X` affine, and
the instance `CategoryTheory.Limits.HasInitial (AlgebraicGeometry.SeminormalizationCategory X)`
is still unproved after this file.

## References

* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace AlgebraicGeometry

variable (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]

/-- A finitely presented `A`-algebra is a finitely presentable object of
`CategoryTheory.Under (CommRingCat.of A)`. -/
theorem isFinitelyPresentable_mkUnder (hfp : Algebra.FinitePresentation A C) :
    IsFinitelyPresentable.{u}
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj (CommAlgCat.of A C)) :=
  ((CommRingCat.isFinitelyPresentable_under_tfae
      (Under.mk (CommRingCat.ofHom (algebraMap A C)))).out 1 2).mp
    (RingHom.finitePresentation_algebraMap.mpr hfp)

/-- Every `A`-algebra map from a finitely presented algebra `C` to `Algebra.seminormalization A`
is the inverse of a presentation of `C` by an object of `Algebra.SeminormalizationIndex A`,
followed by the inclusion of that object into the colimit.  In particular it does not depend on
the map. -/
theorem hom_seminormalization_eq_of_algEquiv (hfp : Algebra.FinitePresentation A C)
    (P : Algebra.SeminormalizationIndex A) (e : P.obj.algebra ≃ₐ[A] C)
    (f : CommAlgCat.of A C ⟶ Algebra.seminormalization A) :
    f = (CommAlgCat.isoMk e).inv ≫ colimit.ι (Algebra.seminormalizationDiagram A) P := by
  set E := commAlgCatEquivUnder (CommRingCat.of A)
  set D := Algebra.seminormalizationDiagram A
  have : IsFinitelyPresentable.{u} (E.functor.obj (CommAlgCat.of A C)) :=
    isFinitelyPresentable_mkUnder A C hfp
  have hc : IsColimit (E.functor.mapCocone (colimit.cocone D)) :=
    isColimitOfPreserves _ (colimit.isColimit _)
  obtain ⟨j, q, hq⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hc (E.functor.map f)
  let qA : CommAlgCat.of A C ⟶ D.obj j := E.functor.preimage q
  have hqA : qA ≫ colimit.ι D j = f :=
    E.functor.map_injective (by rwa [Functor.map_comp, Functor.map_preimage])
  let g : D.obj P ⟶ D.obj j := (CommAlgCat.isoMk e).hom ≫ qA
  let d : P ⟶ j := ObjectProperty.homMk g
  have hdm : D.map d = g := rfl
  have hig : (CommAlgCat.isoMk e).inv ≫ g = qA := by
    simp only [g, Iso.inv_hom_id_assoc]
  rw [← hqA, ← colimit.w D d, hdm, ← Category.assoc, hig]

/-- **Stacks 0EUR.** There is at most one `A`-algebra map from a finitely presented
seminormalization candidate to `Algebra.seminormalization A`. -/
theorem subsingleton_hom_seminormalization (hfp : Algebra.FinitePresentation A C)
    (huh : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (hres : Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))) :
    Subsingleton (CommAlgCat.of A C ⟶ Algebra.seminormalization A) := by
  obtain ⟨P, e⟩ := exists_seminormalizationIndex_algEquiv A C hfp huh hres
  exact ⟨fun f₁ f₂ => (hom_seminormalization_eq_of_algEquiv A C hfp P e f₁).trans
    (hom_seminormalization_eq_of_algEquiv A C hfp P e f₂).symm⟩

/-- **Stacks 0EUR.** The canonical `A`-algebra map from a finitely presented seminormalization
candidate to `Algebra.seminormalization A`. -/
def canonicalHomToSeminormalization (hfp : Algebra.FinitePresentation A C)
    (huh : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (hres : Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))) :
    CommAlgCat.of A C ⟶ Algebra.seminormalization A :=
  let P := Classical.choice (exists_seminormalizationIndex_algEquiv A C hfp huh hres)
  (CommAlgCat.isoMk P.2).inv ≫ colimit.ι (Algebra.seminormalizationDiagram A) P.1

/-- **Stacks 0EUR.** A finitely presented `A`-algebra whose structure morphism on spectra is a
universal homeomorphism inducing isomorphisms on all residue fields admits exactly one
`A`-algebra map to `Algebra.seminormalization A`. -/
@[instance_reducible]
def uniqueHomToSeminormalization (hfp : Algebra.FinitePresentation A C)
    (huh : UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A C))))
    (hres : Scheme.Hom.InducesResidueFieldIsomorphisms
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))) :
    Unique (CommAlgCat.of A C ⟶ Algebra.seminormalization A) :=
  let := subsingleton_hom_seminormalization A C hfp huh hres
  uniqueOfSubsingleton (canonicalHomToSeminormalization A C hfp huh hres)

section Under

variable {C' : Type u} [Category.{v} C'] {D' : Type u'} [Category.{v'} D']

/-- A full and faithful functor carries a subsingleton hom-set to a subsingleton hom-set. -/
theorem subsingleton_map_of_fullyFaithful (F : C' ⥤ D') [F.Full] [F.Faithful]
    {X Y : C'} [Subsingleton (X ⟶ Y)] : Subsingleton (F.obj X ⟶ F.obj Y) :=
  ⟨fun f g => by
    rw [← F.map_preimage f, ← F.map_preimage g,
      Subsingleton.elim (F.preimage f) (F.preimage g)]⟩

/-- The seminormalization of `A`, as an object of `CategoryTheory.Under (CommRingCat.of A)`. -/
def seminormalizationUnder : Under (CommRingCat.of A) :=
  (commAlgCatEquivUnder (CommRingCat.of A)).functor.obj (Algebra.seminormalization A)

/-- The property, among commutative rings under `A`, of being finitely presented over `A` and
of giving a universal homeomorphism on spectra which induces isomorphisms on all residue
fields.  This is the property whose filtered colimits Tag 0EUJ is about. -/
def IsFinitelyPresentedCandidateUnder : ObjectProperty (Under (CommRingCat.of A)) :=
  fun C => C.hom.hom.FinitePresentation ∧
    UniversalHomeomorphism (Spec.map C.hom) ∧
    Scheme.Hom.InducesResidueFieldIsomorphisms (Spec.map C.hom)

variable {A}

/-- **Stacks 0EUR.** The canonical map from a finitely presented seminormalization candidate
under `A` to the seminormalization of `A`. -/
def canonicalUnderHomToSeminormalization (C : Under (CommRingCat.of A))
    (hC : IsFinitelyPresentedCandidateUnder A C) : C ⟶ seminormalizationUnder A :=
  let : Algebra A C.right := C.hom.hom.toAlgebra
  (commAlgCatEquivUnder (CommRingCat.of A)).functor.map
    (canonicalHomToSeminormalization A C.right
      (RingHom.finitePresentation_algebraMap.mp hC.1) hC.2.1 hC.2.2)

/-- **Stacks 0EUR.** There is at most one map from a finitely presented seminormalization
candidate under `A` to the seminormalization of `A`. -/
theorem subsingleton_underHom_seminormalization (C : Under (CommRingCat.of A))
    (hC : IsFinitelyPresentedCandidateUnder A C) :
    Subsingleton (C ⟶ seminormalizationUnder A) := by
  let _ : Algebra A C.right := C.hom.hom.toAlgebra
  let _ := subsingleton_hom_seminormalization A C.right
    (RingHom.finitePresentation_algebraMap.mp hC.1) hC.2.1 hC.2.2
  exact subsingleton_map_of_fullyFaithful (commAlgCatEquivUnder (CommRingCat.of A)).functor
    (X := CommAlgCat.of A C.right) (Y := Algebra.seminormalization A)

end Under

end AlgebraicGeometry

end
