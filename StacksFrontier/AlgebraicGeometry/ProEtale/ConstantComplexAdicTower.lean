module

public import StacksFrontier.AlgebraicGeometry.ProEtale.CompletedConstantComplexLimit

/-!
# The tower of constant complexes of the adic reductions of a complex of modules

Let `(C, J)` be a site, `Λ` a commutative ring and `I ⊆ Λ` an ideal. For a complex `N` of
`Λ`-modules, the constant complexes `\underline{N/IⁿN}` of sheaves of `Λ`-modules form a tower
indexed by `n`, the transition maps being the reductions `N/Iⁿ⁺¹N → N/IⁿN`. On the small
pro-étale site, read over the constant coefficient ring sheaf, this is
`AlgebraicGeometry.ProEtale.adicQuotientConstantComplexTower`.

## Main definitions

* `Stacks.ModuleSheaf.constantAdicQuotientFunctorTower`: the tower of functors
  `M ↦ \underline{M/IⁿM}` from `Λ`-modules to sheaves of `Λ`-modules.
* `Stacks.ModuleSheaf.constantAdicQuotientComplexTower`: the tower `n ↦ \underline{N/IⁿN}` of
  complexes attached to a complex `N` of `Λ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace Stacks.ModuleSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (Λ : Type w) [CommRing Λ] [UnivLE.{max u v, w}] (I : Ideal Λ)

/-- The tower of functors `M ↦ \underline{M/IⁿM}` from `Λ`-modules to sheaves of `Λ`-modules,
the transition maps being the reductions. -/
def constantAdicQuotientFunctorTower : ℕᵒᵖ ⥤ ModuleCat.{w} Λ ⥤ Sheaf J (ModuleCat.{w} Λ) :=
  (AlgebraicGeometry.ProEtale.adicQuotientModuleFunctor.{w, w} Λ I).flip ⋙
    (Functor.whiskeringRight _ _ _).obj (constantSheaf J (ModuleCat.{w} Λ))

/-- Each functor `M ↦ \underline{M/IⁿM}` of the tower preserves zero morphisms. -/
instance (n : ℕᵒᵖ) : ((constantAdicQuotientFunctorTower J Λ I).obj n).PreservesZeroMorphisms :=
  have : PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} Λ)) :=
    preservesFiniteLimits_constantSheaf J Λ
  have : (constantSheaf J (ModuleCat.{w} Λ)).Additive :=
    Functor.additive_of_preserves_binary_products _
  inferInstanceAs (((AlgebraicGeometry.ProEtale.adicQuotientModuleFunctor.{w, w} Λ I).flip.obj n ⋙
    constantSheaf J (ModuleCat.{w} Λ)).PreservesZeroMorphisms)

/-- The tower `n ↦ \underline{N/IⁿN}` of constant complexes of sheaves of `Λ`-modules attached to
a complex `N` of `Λ`-modules, the transition maps being the reductions. -/
abbrev constantAdicQuotientComplexTower (N : CochainComplex (ModuleCat.{w} Λ) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (Sheaf J (ModuleCat.{w} Λ)) ℤ :=
  (constantAdicQuotientFunctorTower J Λ I).mapHomologicalComplexDiagram _ N

end Stacks.ModuleSheaf

end
