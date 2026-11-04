module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Realizing a derived-category identification with a K-injective complex by a chain map

Let `C` be an abelian category with a derived category, let `L` be a cochain complex and let `I`
be a K-injective one. An isomorphism `Q(L) ≅ Q(I)` in the derived category is then *realized by a
morphism of complexes*: there is a quasi-isomorphism `L ⟶ I` whose image in the derived category
is the given isomorphism.

The localization functor out of the homotopy category is bijective on morphisms into a
K-injective object (`CochainComplex.IsKInjective.Qh_map_bijective`), and the quotient functor
from complexes to the homotopy category is full, so the isomorphism descends to a homotopy class
and then to an honest chain map; it is a quasi-isomorphism because its image under `Q` is an
isomorphism.

## Main definitions

* `CochainComplex.realizeDerivedIso`: a chosen chain map `L ⟶ I` realizing the isomorphism.

## Main results

* `CochainComplex.exists_quasiIso_of_isKInjective_of_iso`: the existence statement.
* `CochainComplex.quasiIso_realizeDerivedIso` and `CochainComplex.Q_map_realizeDerivedIso`: the
  chosen chain map is a quasi-isomorphism and does realize the isomorphism.

## Implementation notes

The hypothesis is on the target. The same argument with
`CochainComplex.IsKProjective.Qh_map_bijective` realizes an isomorphism out of a K-projective
complex; neither form implies the other, and a strictly perfect complex of sheaves of modules is
not K-projective, whereas K-injective resolutions of sheaves of modules always exist.

The statements hold for an arbitrary instance of `HasDerivedCategory C`, not only for
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- **An isomorphism in the derived category whose target is a K-injective complex is realized by
a quasi-isomorphism of complexes.** For `I` K-injective and `e : Q(L) ≅ Q(I)` there is a morphism
of complexes `f : L ⟶ I` with `Q(f) = e.hom`; it is then a quasi-isomorphism, `Q(f)` being an
isomorphism. -/
theorem exists_quasiIso_of_isKInjective_of_iso (L I : CochainComplex C ℤ) [I.IsKInjective]
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj I) :
    ∃ f : L ⟶ I, QuasiIso f ∧ DerivedCategory.Q.map f = e.hom := by
  obtain ⟨β, hβ⟩ := (IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L) I).surjective
    ((DerivedCategory.quotientCompQhIso C).hom.app L ≫ e.hom ≫
      (DerivedCategory.quotientCompQhIso C).inv.app I)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective β
  have h := DerivedCategory.quotientCompQhIso_hom_naturality (C := C) f
  rw [hβ] at h
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] at h
  have hQ : DerivedCategory.Q.map f = e.hom :=
    ((cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app L)).1 h).symm
  refine ⟨f, ?_, hQ⟩
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, hQ]
  infer_instance

/-- **A chosen quasi-isomorphism realizing a derived-category identification with a K-injective
complex**, the morphism of complexes whose existence is
`CochainComplex.exists_quasiIso_of_isKInjective_of_iso`. -/
def realizeDerivedIso (L I : CochainComplex C ℤ) [I.IsKInjective]
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj I) : L ⟶ I :=
  (exists_quasiIso_of_isKInjective_of_iso L I e).choose

/-- The chain map `CochainComplex.realizeDerivedIso L I e` is a quasi-isomorphism. -/
instance quasiIso_realizeDerivedIso (L I : CochainComplex C ℤ) [I.IsKInjective]
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj I) :
    QuasiIso (realizeDerivedIso L I e) :=
  (exists_quasiIso_of_isKInjective_of_iso L I e).choose_spec.1

/-- The image of `CochainComplex.realizeDerivedIso L I e` in the derived category is `e.hom`. -/
theorem Q_map_realizeDerivedIso (L I : CochainComplex C ℤ) [I.IsKInjective]
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj I) :
    DerivedCategory.Q.map (realizeDerivedIso L I e) = e.hom :=
  (exists_quasiIso_of_isKInjective_of_iso L I e).choose_spec.2

end CochainComplex

end
