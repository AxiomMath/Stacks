module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectDirectImageReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeSlice

/-!
# A morphism to an affine algebraic space, read over the spectrum of a ring

Let `Y` be an affine algebraic space over `S`, so `Y ≅ h_T` for an object `T` of the big fppf
site with affine underlying scheme, and let `A = Γ(T, 𝒪_T)`. Then `Spec A` belongs to the site,
`Y ≅ h_{(Spec A, g)}` for the composite `g : Spec A ≅ T ⟶ S`, and by Stacks 04SG every algebraic
space `X` with a morphism `f : X ⟶ Y` is the lower-shriek extension `Λ X_A` of an algebraic space
`X_A` over `Spec A`, with `f` read as the structure morphism of `X_A`.

## Main results

* `AlgebraicGeometry.Space.exists_relocalizeSpec_of_isAffineSpace`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The spectrum of the ring of global functions of an affine object `T` of the big fppf site,
over `S` through `Spec Γ(T, 𝒪_T) ≅ T ⟶ S`. -/
def specGlobalSectionsBase (T : BigFppfOver B S hS) [IsAffine T.left.obj] :
    B.obj (@contains_spec_globalSections_of_isAffine _ _ hS T ‹_›) ⟶ B.obj hS :=
  (ObjectProperty.isoMk _ T.left.obj.isoSpec.symm).hom ≫ T.hom

/-- An affine object of the big fppf site, read over the spectrum of its ring of global
functions: `h_{(Spec Γ(T, 𝒪_T), g)} ≅ h_T`. -/
def specGlobalSectionsIso (T : BigFppfOver B S hS) [IsAffine T.left.obj] :
    schemeSpace (Over.mk (specGlobalSectionsBase T)) ≅ schemeSpace T :=
  (schemeSpaceFunctor B S hS).mapIso
    (Over.isoMk (ObjectProperty.isoMk _ T.left.obj.isoSpec.symm) rfl)

/-- **A morphism to an affine algebraic space is the structure morphism of an algebraic space
over the spectrum of a ring** (Stacks 04SG). For `f : X ⟶ Y` with `Y` affine there are a ring
`A` with `Spec A` in the site, a morphism `g : Spec A ⟶ S`, an isomorphism
`Y ≅ h_{(Spec A, g)}`, an algebraic space `X_A` over `Spec A` and an isomorphism `Λ X_A ≅ X`
under which `f` is the lower-shriek extension of the structure morphism of `X_A`. -/
theorem exists_relocalizeSpec_of_isAffineSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hY : IsAffineSpace B S hS Y.1) :
    ∃ (A : Type u) (_ : CommRing A) (hA : B.Contains (Spec (.of A)))
      (g : B.obj hA ⟶ B.obj hS) (eY : Y ≅ schemeSpace (Over.mk g))
      (XA : AlgebraicSpaces B (Spec (.of A)) hA) (e : relocalizeSpace B hA hS g XA ≅ X),
      e.hom ≫ f ≫ eY.hom =
        relocalizeHom B hA hS g (toFinalHom B hA XA) ≫ relocalizeBaseHom B hA hS g := by
  obtain ⟨T, hT, ⟨i⟩⟩ := hY
  have : IsAffine T.left.obj := hT
  let eY : Y ≅ schemeSpace (Over.mk (specGlobalSectionsBase T)) :=
    ObjectProperty.isoMk _ i ≪≫ (specGlobalSectionsIso T).symm
  obtain ⟨XA, e, he⟩ := exists_relocalizeSpace_iso B
    (@contains_spec_globalSections_of_isAffine _ _ hS T ‹_›) hS (specGlobalSectionsBase T) X
    (f ≫ eY.hom)
  exact ⟨Γ(T.left.obj, ⊤), inferInstance, @contains_spec_globalSections_of_isAffine _ _ hS T ‹_›,
    specGlobalSectionsBase T, eY, XA, e, he⟩

end AlgebraicGeometry.Space

end
