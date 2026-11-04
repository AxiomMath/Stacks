module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraOfImmersionSquareMap
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId

/-!
# The conormal module of an immersion is the inverse image of its kernel ideal sheaf

Let `i : Z ⟶ X` be an immersion of algebraic spaces.  Its conormal module
`AlgebraicGeometry.Space.conormalModuleOfImmersion` (Stacks 04CN) is defined through the closed
factorisation `Z ⟶ X ∖ ∂Z`.  Since the inclusion `X ∖ ∂Z ⟶ X` is an étale monomorphism, the square
formed by the closed factorisation, `i`, the inclusion and `𝟙 Z` is cartesian, and Stacks 09RR in
degree one identifies the conormal module with `i^*Ker(i^♯)`, the degree-one piece of the conormal
algebra of `i` itself.

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleOfImmersionIso`: `𝒞_{Z/X} ≅ i^*Ker(i^♯)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The conormal module of an immersion is `i^*Ker(i^♯)`**: Stacks 09RR in degree one along
the étale inclusion `X ∖ ∂Z ⟶ X`, read at the cartesian square
`AlgebraicGeometry.Space.isPullback_immersionClosedFactorization`. -/
def conormalModuleOfImmersionIso (hX : IsAlgebraicSpace B S hS X₀)
    (hZ : IsAlgebraicSpace B S hS Z₀) (i : Z₀ ⟶ X₀) (hi : IsImmersion B S hS i) :
    conormalModuleOfImmersion B S hS hX hZ i hi ≅
      (conormalAlgebra B S hS
        (ObjectProperty.homMk i : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩)).piece 1 :=
  let i' : (⟨Z₀, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X₀, hX⟩ := ObjectProperty.homMk i
  eqToIso (conormalModuleOfImmersion_eq_conormalAlgebraOfImmersion_piece_one B S hS hX hZ i hi) ≪≫
    (conormalAlgebraEtaleRestrictionPieceIso B S hS (𝟙 _)
      (immersionClosedFactorization B S hS hX hZ i hi) i' (immersionAmbientι B S hS i' hi)
      (isPullback_immersionClosedFactorization B S hS hZ hX i' hi).flip
      (isEtale_immersionAmbientι B S hS i' hi) 1).symm ≪≫
    (modulePullbackIdIso B S hS _).app _

end AlgebraicGeometry.Space

end
