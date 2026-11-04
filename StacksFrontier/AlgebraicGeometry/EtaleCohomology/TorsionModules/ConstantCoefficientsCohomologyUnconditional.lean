module
public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyForget
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Module.ZMod
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Constant étale sheaves of modules and their underlying abelian sheaves

For a commutative ring `Λ` and a scheme `X`, the underlying abelian sheaf of the constant sheaf
of `Λ`-modules on the small étale site of `X` with value `M` is the constant abelian sheaf with
value the underlying abelian group of `M`, naturally in `M`, for coefficients in an arbitrary
universe.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleForgetConstantSheafIsoGeneral`: The natural isomorphism
  between the underlying abelian sheaf of a constant sheaf of `Λ`-modules and the constant
  abelian sheaf on the underlying abelian group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- **The underlying abelian sheaf of a constant sheaf of `Λ`-modules is constant**: `(M̲)_ab` is
the constant abelian sheaf on the underlying abelian group of `M`, naturally in `M`. -/
def etaleModuleForgetConstantSheafIsoGeneral :
    constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ⋙
        _root_.Stacks.EtaleCohomology.etaleModuleForgetAb.{u, r} Λ X ≅
      forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r} ⋙
        constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r} :=
  have := preservesSheafification_forget₂_moduleCat_smallEtale.{u, r} Λ X
  constantCommuteCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r})

/-- The constant sheaf functor from abelian groups to abelian sheaves on the small étale site of
`X` is additive. -/
local instance : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).Additive :=
  (constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}
    (etaleSiteTerminalIsTerminal X)).left_adjoint_additive

/-- The global sections functor on abelian sheaves on the small étale site of `X` is additive. -/
local instance : (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).Additive :=
  Functor.additive_of_preserves_binary_products _

variable {Λ X}

section Colimit

end Colimit

section Span

universe w

end Span

section Prime

end Prime

section Devissage

attribute [local instance] HasDerivedCategory.standard

end Devissage

end Stacks.EtaleCohomology

end
