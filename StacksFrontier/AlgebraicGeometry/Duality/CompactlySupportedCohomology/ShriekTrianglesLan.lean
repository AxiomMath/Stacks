module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTriangles
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.Independence
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.IndependenceLan
public import
  StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ProperPushforwardCoherent
public import
  StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemExistence
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.RestrictionHomColimit
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTrianglesData

/-!
# Further results

Results complementing
`StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTriangles`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u₁ u₂ u₃

namespace CategoryTheory.CompactificationData

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]
  {ℳ : Type u₃} [Category.{v} ℳ] [HasShift ℳ ℤ] [HasShift 𝒟 ℤ]

variable [HasZeroObject ℳ] [Preadditive ℳ] [∀ n : ℤ, (shiftFunctor ℳ n).Additive]
  [Pretriangulated ℳ] [HasZeroObject 𝒟] [Preadditive 𝒟]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]

variable [HasZeroObject 𝒞] [Preadditive 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

end CategoryTheory.CompactificationData

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{v} 𝒟]

end CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {U X : Scheme.{u}}

/-- The restriction to `U` of a vertex system of an inverse system of triangles over `X`, when the
restricted system of triangles is constant at `T`, is the constant system at the corresponding
vertex of `T`. -/
private def vertexRestrictIso (j : U ⟶ X) [IsOpenImmersion j] [IsLocallyNoetherian X]
    {TX : ℕᵒᵖ ⥤ Triangle (BoundedCoherentDerived X)} {T : Triangle (BoundedCoherentDerived U)}
    (eR : TX ⋙ (restrictBoundedCoherentLift j).mapTriangle ≅ (Functor.const ℕᵒᵖ).obj T)
    (π : Triangle (BoundedCoherentDerived X) ⥤ BoundedCoherentDerived X)
    (π' : Triangle (BoundedCoherentDerived U) ⥤ BoundedCoherentDerived U)
    (w : π ⋙ restrictBoundedCoherentLift j ≅ (restrictBoundedCoherentLift j).mapTriangle ⋙ π') :
    (TX ⋙ π) ⋙ restrictBoundedCoherentLift j ≅ (Functor.const ℕᵒᵖ).obj (π'.obj T) :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft TX w ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight eR π' ≪≫ Functor.constComp _ _ _

variable {X' Y : Scheme.{u}}

section FTS

variable {S : Scheme.{u}} [IsNoetherian S] {X₁ Y₁ : FTS S}

end FTS

end AlgebraicGeometry

end
