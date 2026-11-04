module

public import StacksFrontier.AlgebraicGeometry.Seminormalization.UniversalPropertyOfInd
public import Mathlib.AlgebraicGeometry.Group.Affine

/-!
# Initiality of the seminormalization over an affine base, reduced to Tag 0EUJ

Tag 0EUS asks for an initial object of `AlgebraicGeometry.SeminormalizationCategory X`, the
category of universal homeomorphisms onto `X` which induce isomorphisms on all residue fields.
This file settles the case `X = Spec A`, conditionally on Tag 0EUJ: the object
`AlgebraicGeometry.seminormalizationObject A` is initial as soon as the seminormalization of `A`
has the ring-level universal property of Tag 0EUR, and that in turn needs only Tag 0EUJ by
`StacksFrontier.AlgebraicGeometry.Seminormalization.UniversalPropertyOfInd`.

Nothing here assumes anything as an axiom; the hypothesis is explicit on every declaration.

## Main definitions

* `AlgebraicGeometry.isInitial_seminormalizationObject_of_unique`: initiality over `Spec A`,
  given that the seminormalization receives exactly one map from every candidate `A`-algebra.
* `AlgebraicGeometry.isInitial_seminormalizationObject_of_ind`: the same, with Tag 0EUJ in place
  of that hypothesis.

## Main results

* `AlgebraicGeometry.isClosedUnderIsomorphisms_isSeminormalizationCandidate`: being a
  seminormalization candidate over `X` is invariant under isomorphism in `Over X`.  This is
  unconditional and is what lets an abstract candidate be replaced by a spectrum.
* `AlgebraicGeometry.isSeminormalizationCandidate_algSpec_iff`: for an `A`-algebra `B`, the
  object `Spec B` of `Over (Spec A)` is a candidate exactly when the two ring-level conditions
  hold of `Spec.map (CommRingCat.ofHom (algebraMap A B))`.
* `AlgebraicGeometry.subsingleton_overHom_seminormalization`: the transport of uniqueness from
  `A`-algebra maps to morphisms of the seminormalization category.

## Implementation notes

The passage from rings to schemes over `Spec A` is Mathlib's
`AlgebraicGeometry.algSpec (CommRingCat.of A) : (CommAlgCat (CommRingCat.of A))ᵒᵖ ⥤ Over (Spec A)`,
which is full and faithful (`AlgebraicGeometry.algSpec.fullyFaithful`) and whose essential image
is exactly the objects with affine source (`AlgebraicGeometry.essImage_algSpec`).  The three
steps are then:

1. A candidate over an affine base has affine source,
   `AlgebraicGeometry.IsSeminormalizationCandidate.isAffine`, so every object `Y` of the
   seminormalization category of `Spec A` is isomorphic in `Over (Spec A)` to
   `(algSpec _).obj Z` for some `A`-algebra `Z.unop`.
2. The candidate property transfers across that isomorphism, which is the
   `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms` instance proved here from
   `AlgebraicGeometry.IsSeminormalizationCandidate.comp` applied to the inverse isomorphism.
3. `AlgebraicGeometry.seminormalizationObject A` is *already* in the image on the nose:
   `(seminormalizationObject A).obj = (algSpec (CommRingCat.of A)).obj (op (seminormalization A))`
   holds by `rfl`, so the hom-sets are compared with no transport on the source side.

Morphisms of the full subcategory are morphisms of `Over (Spec A)`
(`CategoryTheory.ObjectProperty.fullyFaithfulι`), and the hom-set in
`(CommAlgCat (CommRingCat.of A))ᵒᵖ` is the opposite of an `A`-algebra hom-set, so the uniqueness
statement is carried across by `AlgebraicGeometry.subsingleton_map_of_fullyFaithful` twice and
`Quiver.Hom.unop_inj` once.

The existence and uniqueness halves are stated as two separate `Prop`s rather than one `Unique`
because the isomorphism of step 1 is extracted from an `Exists`, which cannot eliminate into
data.

Everything lives in a single universe `u`, as `AlgebraicGeometry.UniversalHomeomorphism` is
available only for `Scheme.{u}`.

No hypothesis beyond those of Tag 0EUS is used on `A`: it is an arbitrary commutative ring, with
no Noetherian or reducedness assumption.

## What is not done

Tag 0EUJ is not proved; see the corresponding section of
`StacksFrontier.AlgebraicGeometry.Seminormalization.UniversalPropertyOfInd`.  So nothing here is
an unconditional instance of `CategoryTheory.Limits.HasInitial`, not even for an affine scheme.

The arbitrary scheme of Tag 0EUS is *not* treated.  Granting Tag 0EUJ, what remains is the
gluing: a functor on the affine opens of `X` sending `U` to `Spec (seminormalization Γ(X, U))`
whose squares are pullbacks, fed to `AlgebraicGeometry.Scheme.Cover.RelativeGluingData` (Tag
01LH, in Mathlib).  The pullback condition is the statement that seminormalization commutes with
localization away from an element, which by the argument of Tag 0EUS is deduced from part (4) of
that tag — the characterization of when the canonical morphism is an isomorphism, the
seminormality criterion of Tag 0EUR, which nothing in this repository proves — together with
`Stacks.RingTheory.Seminormal.IsSeminormalRing.localizationAway`.  Nothing in this repository
proves that seminormalization commutes with localization, and nothing here supplies it.

## References

* [Stacks Project, Tag 0EUJ](https://stacks.math.columbia.edu/tag/0EUJ)
* [Stacks Project, Tag 0EUR](https://stacks.math.columbia.edu/tag/0EUR)
* [Stacks Project, Tag 0EUS](https://stacks.math.columbia.edu/tag/0EUS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- Being a universal homeomorphism onto `X` which induces isomorphisms on all residue fields is
invariant under isomorphism in `Over X`. -/
instance isClosedUnderIsomorphisms_isSeminormalizationCandidate (X : Scheme.{u}) :
    (IsSeminormalizationCandidate X).IsClosedUnderIsomorphisms where
  of_iso {Y Y'} e hY := by
    have : IsIso e.inv.left := (Over.forget X).map_isIso e.inv
    have h := IsSeminormalizationCandidate.comp hY e.inv.left
      (universalHomeomorphism_of_isIso _) (fun _ => inferInstance)
    rwa [show e.inv.left ≫ Y.hom = Y'.hom from Over.w e.inv] at h

variable (A : Type u) [CommRing A]

/-- The spectrum of an `A`-algebra, as an object of `Over (Spec A)`, is a seminormalization
candidate exactly when its structure morphism is a universal homeomorphism inducing isomorphisms
on all residue fields. -/
theorem isSeminormalizationCandidate_algSpec_iff
    (Z : (CommAlgCat (CommRingCat.of A))ᵒᵖ) :
    IsSeminormalizationCandidate (Spec (CommRingCat.of A))
        ((algSpec (CommRingCat.of A)).obj Z) ↔
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A Z.unop))) ∧
        Scheme.Hom.InducesResidueFieldIsomorphisms
          (Spec.map (CommRingCat.ofHom (algebraMap A Z.unop))) := by
  rw [isSeminormalizationCandidate_iff, algSpec_obj_hom]
  exact Iff.rfl

/-- Uniqueness of the `A`-algebra map to the seminormalization transfers to uniqueness of the
morphism of seminormalization categories out of `seminormalizationObject A`. -/
theorem subsingleton_overHom_seminormalization (Z : (CommAlgCat (CommRingCat.of A))ᵒᵖ)
    (hZ : IsSeminormalizationCandidate (Spec (CommRingCat.of A))
      ((algSpec (CommRingCat.of A)).obj Z))
    (hss : Subsingleton ((Z.unop : CommAlgCat (CommRingCat.of A)) ⟶
      Algebra.seminormalization A)) :
    Subsingleton (seminormalizationObject A ⟶
      (⟨_, hZ⟩ : SeminormalizationCategory (Spec (CommRingCat.of A)))) :=
  have h1 : Subsingleton (op (Algebra.seminormalization A) ⟶ Z) :=
    ⟨fun f g => Quiver.Hom.unop_inj (hss.allEq f.unop g.unop)⟩
  have h2 : Subsingleton ((algSpec (CommRingCat.of A)).obj (op (Algebra.seminormalization A)) ⟶
      (algSpec (CommRingCat.of A)).obj Z) :=
    @subsingleton_map_of_fullyFaithful _ _ _ _ (algSpec (CommRingCat.of A))
      algSpec.fullyFaithful.full algSpec.fullyFaithful.faithful _ _ h1
  ⟨fun _ _ => ObjectProperty.hom_ext
    (P := IsSeminormalizationCandidate (Spec (CommRingCat.of A))) (h2.allEq _ _)⟩

/-- Every seminormalization candidate over `Spec A` is isomorphic to the spectrum of an
`A`-algebra satisfying the two ring-level conditions. -/
private theorem exists_algSpec_iso_seminormalizationCategory
    (Y : SeminormalizationCategory (Spec (CommRingCat.of A))) :
    ∃ (Z : (CommAlgCat (CommRingCat.of A))ᵒᵖ) (_ : (algSpec (CommRingCat.of A)).obj Z ≅ Y.obj)
      (_ : IsSeminormalizationCandidate (Spec (CommRingCat.of A))
        ((algSpec (CommRingCat.of A)).obj Z)),
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A Z.unop))) ∧
        Scheme.Hom.InducesResidueFieldIsomorphisms
          (Spec.map (CommRingCat.ofHom (algebraMap A Z.unop))) := by
  obtain ⟨Z, ⟨e⟩⟩ := essImage_algSpec.mpr (IsSeminormalizationCandidate.isAffine Y.property)
  have hZ := (IsSeminormalizationCandidate (Spec (CommRingCat.of A))).prop_of_iso e.symm
    Y.property
  exact ⟨Z, e, hZ, (isSeminormalizationCandidate_algSpec_iff A Z).mp hZ⟩

variable (h : ∀ (B : Type u) [CommRing B] [Algebra A B],
  UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
  Scheme.Hom.InducesResidueFieldIsomorphisms
    (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
  Unique (CommAlgCat.of A B ⟶ Algebra.seminormalization A))

include h in
/-- **Stacks 0EUS**, conditionally on the ring-level universal property.  There is at most one
morphism from the seminormalization of `A` to any seminormalization candidate over `Spec A`. -/
theorem subsingleton_hom_seminormalizationObject_of_unique
    (Y : SeminormalizationCategory (Spec (CommRingCat.of A))) :
    Subsingleton (seminormalizationObject A ⟶ Y) := by
  obtain ⟨Z, e, hZ, huh, hres⟩ := exists_algSpec_iso_seminormalizationCategory A Y
  have := subsingleton_overHom_seminormalization A Z hZ
    (@Unique.instSubsingleton _ (h Z.unop huh hres))
  exact Equiv.subsingleton ((Iso.refl (seminormalizationObject A)).homCongr
    (ObjectProperty.isoMk (P := IsSeminormalizationCandidate (Spec (CommRingCat.of A)))
      (X := ⟨_, hZ⟩) (Y := Y) e)).symm

include h in
/-- **Stacks 0EUS**, conditionally on the ring-level universal property.  There is at least one
morphism from the seminormalization of `A` to any seminormalization candidate over `Spec A`. -/
theorem nonempty_hom_seminormalizationObject_of_unique
    (Y : SeminormalizationCategory (Spec (CommRingCat.of A))) :
    Nonempty (seminormalizationObject A ⟶ Y) := by
  obtain ⟨Z, e, hZ, huh, hres⟩ := exists_algSpec_iso_seminormalizationCategory A Y
  let _ := h Z.unop huh hres
  exact ⟨ObjectProperty.homMk ((algSpec (CommRingCat.of A)).map
    (Quiver.Hom.op (default : (Z.unop : CommAlgCat (CommRingCat.of A)) ⟶
      Algebra.seminormalization A)) ≫ e.hom)⟩

include h in
/-- **Stacks 0EUS** over an affine base, conditionally on the ring-level universal property of
Tag 0EUR: the seminormalization of `A` is an initial object of the category of universal
homeomorphisms onto `Spec A` which induce isomorphisms on all residue fields. -/
def isInitial_seminormalizationObject_of_unique :
    IsInitial (seminormalizationObject A) :=
  let : ∀ Y : SeminormalizationCategory (Spec (CommRingCat.of A)),
      Unique (seminormalizationObject A ⟶ Y) := fun Y =>
    let := subsingleton_hom_seminormalizationObject_of_unique A h Y
    uniqueOfSubsingleton (nonempty_hom_seminormalizationObject_of_unique A h Y).some
  IsInitial.ofUnique _

/-- **Stacks 0EUS** over an affine base, conditionally on Tag 0EUJ alone: if every `A`-algebra
whose spectrum is a universal homeomorphism over `Spec A` inducing isomorphisms on all residue
fields is a filtered colimit of finitely presented such algebras, then the seminormalization of
`A` is initial among universal homeomorphisms onto `Spec A` inducing isomorphisms on all residue
fields. -/
def isInitial_seminormalizationObject_of_ind
    (hind : ∀ (B : Type u) [CommRing B] [Algebra A B],
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
      Scheme.Hom.InducesResidueFieldIsomorphisms
        (Spec.map (CommRingCat.ofHom (algebraMap A B))) →
      ObjectProperty.ind.{u} (IsFinitelyPresentedCandidateUnder A)
        (Under.mk (CommRingCat.ofHom (algebraMap A B)))) :
    IsInitial (seminormalizationObject A) :=
  isInitial_seminormalizationObject_of_unique A fun B _ _ huh hres =>
    uniqueHomToSeminormalization_of_ind A B (hind B huh hres)

end AlgebraicGeometry

end
