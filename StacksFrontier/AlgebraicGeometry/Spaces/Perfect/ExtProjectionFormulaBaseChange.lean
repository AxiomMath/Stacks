module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ElementaryDistinguishedSquarePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FlatProperSupportRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DualPushforwardBaseChangeHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtCoefficientEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleBaseChange

/-!
# Stacks 0DKL: the complex `L` of Stacks 08JR (B) is compatible with base change

This file assembles the base change of the complex `L` of Stacks 08JR (B).

## Main definitions

* `AlgebraicGeometry.Space.edsEtaleRestrictDerivedPullbackIso`: restricting `L(g')^*E` to the
  preimage of the quasi-compact neighbourhood is pulling back the restriction of `E`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

section Restriction

variable {Uo : Subfunctor X.1} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo V.ι) (g' : X' ⟶ X)
  {Uo' : Subfunctor X'.1}
  (hsq' : IsElementaryDistinguishedSquare B S hS X'.2 Uo' (V.preimage g'.hom).ι)

/-- **Restriction to the preimage neighbourhood commutes with derived pullback**:
`(L(g')^*E)|_{g'⁻¹V} ≅ L(g'|)^*(E|_V)`, both being derived pullbacks along `g'⁻¹V ⟶ X`
(étale restriction is derived pullback along an étale morphism, and derived pullbacks
compose). -/
def edsEtaleRestrictDerivedPullbackIso
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :
    (edsEtaleRestrict B S hS hsq').obj ((smallEtaleDerivedModulePullback B S hS g').obj E) ≅
      (smallEtaleDerivedModulePullback B S hS (edsEtalePreimageHom hsq g' hsq')).obj
        ((edsEtaleRestrict B S hS hsq).obj E) :=
  ((smallEtaleDerivedModulePullbackIsoEtale B S hS _
      (isEtale_edsEtaleHom B S hS hsq')).app _).symm ≪≫
    (smallEtaleDerivedModulePullbackCompIso B S hS (edsEtaleHom B S hS hsq') g').app E ≪≫
    (smallEtaleDerivedModulePullbackCongr B S hS
      (isPullback_edsEtalePreimageHom hsq g' hsq').w.symm).app E ≪≫
    ((smallEtaleDerivedModulePullbackCompIso B S hS (edsEtalePreimageHom hsq g' hsq')
      (edsEtaleHom B S hS hsq)).app E).symm ≪≫
    (smallEtaleDerivedModulePullback B S hS (edsEtalePreimageHom hsq g' hsq')).mapIso
      ((smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_edsEtaleHom B S hS hsq)).app E)

variable {Y Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}

include hsq hsq' in
/-- The preimage neighbourhood is the base change of the neighbourhood along `g : Y' ⟶ Y`. -/
theorem isPullback_edsEtalePreimageHom_comp (sq : IsPullback g' f' f g) :
    IsPullback (edsEtalePreimageHom hsq g' hsq') (edsEtaleHom B S hS hsq' ≫ f')
      (edsEtaleHom B S hS hsq ≫ f) g :=
  (isPullback_edsEtalePreimageHom hsq g' hsq').paste_vert sq

end Restriction

end AlgebraicGeometry.Space

end
