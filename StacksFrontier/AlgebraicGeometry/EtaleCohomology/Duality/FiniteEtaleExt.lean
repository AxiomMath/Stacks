module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.FiniteEtaleAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit

/-!
# `Ext` groups along a finite étale morphism

Let `π : Y ⟶ X` be a finite étale morphism. On sheaves of modules on the small étale sites both
`π^{-1}` and `π_*` are exact, and there are adjunctions `π^{-1} ⊣ π_*` and `π_* ⊣ π^{-1}`
(`Stacks.EtaleCohomology.etaleModuleDirectImageInverseImageAdj`). Each gives isomorphisms of
`Ext` groups (`Stacks.ExtAdjunction.extMap_bijective`):

* `Ext^n_X(A, π_* G) ≅ Ext^n_Y(π^{-1} A, G)`, the degenerate Leray spectral sequence of a finite
  morphism; with `A = Λ_X` it reads `Hⁿ(X, π_* G) ≅ Hⁿ(Y, G)`;
* `Ext^n_X(π_* G, F) ≅ Ext^n_Y(G, π^{-1} F)`, the duality for the finite étale morphism `π`
  (`π^! = π^{-1}`).

The first only needs `π` integral; the second is where finiteness and étaleness enter.

## Main definitions

* `Stacks.EtaleCohomology.extDirectImageAddEquiv`: `Ext^n_X(A, π_* G) ≃+ Ext^n_Y(π^{-1} A, G)`.
* `Stacks.EtaleCohomology.extConstantDirectImageAddEquiv`: `Hⁿ(X, π_* G) ≃+ Hⁿ(Y, G)` in the
  form `Ext^n_X(Λ_X, π_* G) ≃+ Ext^n_Y(Λ_Y, G)`.
* `Stacks.EtaleCohomology.extDirectImageLeftAddEquiv`:
  `Ext^n_X(π_* G, F) ≃+ Ext^n_Y(G, π^{-1} F)` for finite étale `π`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Integral

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (π : Y ⟶ X) [IsIntegralHom π]

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **`Ext^n_X(A, π_* G) ≃+ Ext^n_Y(π^{-1} A, G)`** for an integral morphism `π`. -/
def extDirectImageAddEquiv (A : EtaleModules.{u, 0} Λ X) (G : EtaleModules.{u, 0} Λ Y)
    (n : ℕ) :
    Ext A ((etaleModuleDirectImage.{u, 0} Λ π).obj G) n ≃+
      Ext ((etaleModuleInverseImage.{u, 0} Λ π).obj A) G n :=
  AddEquiv.ofBijective (Stacks.ExtAdjunction.extMap (etaleModuleInverseImageAdj.{u, 0} Λ π) A G n)
    (Stacks.ExtAdjunction.extMap_bijective (etaleModuleInverseImageAdj.{u, 0} Λ π) A G n)

end Integral

section Constant

variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}} (π : Y ⟶ X) [IsIntegralHom π]

/-- **`Hⁿ(X, π_* G) ≃+ Hⁿ(Y, G)`** for an integral morphism `π`, as
`Ext^n_X(Λ_X, π_* G) ≃+ Ext^n_Y(Λ_Y, G)`. -/
def extConstantDirectImageAddEquiv (G : EtaleModules.{u, 0} Λ Y) (n : ℕ) :
    Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} Λ X.smallEtaleTopology)
        ((etaleModuleDirectImage.{u, 0} Λ π).obj G) n ≃+
      Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf.{0} Λ Y.smallEtaleTopology)
        G n :=
  (extDirectImageAddEquiv Λ π _ G n).trans
    (AddEquiv.ofBijective _ (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso
      ((etaleModuleInverseImageConstantIso.{u, 0} Λ π).inv.app
        (ModuleCat.of Λ (ULift.{u + 1} Λ))) (Z := G) n))

end Constant

section FiniteEtale

variable (Λ : Type) [Ring Λ] {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Etale π]

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- **`Ext^n_X(π_* G, F) ≃+ Ext^n_Y(G, π^{-1} F)`** for a finite étale morphism `π`. -/
def extDirectImageLeftAddEquiv (G : EtaleModules.{u, 0} Λ Y) (F : EtaleModules.{u, 0} Λ X)
    (n : ℕ) :
    Ext G ((etaleModuleInverseImage.{u, 0} Λ π).obj F) n ≃+
      Ext ((etaleModuleDirectImage.{u, 0} Λ π).obj G) F n :=
  haveI : (etaleModuleDirectImage.{u, 0} Λ π).Additive := inferInstance
  AddEquiv.ofBijective
    (Stacks.ExtAdjunction.extMap (etaleModuleDirectImageInverseImageAdj.{u, 0} Λ π) G F n)
    (Stacks.ExtAdjunction.extMap_bijective (etaleModuleDirectImageInverseImageAdj.{u, 0} Λ π)
      G F n)

end FiniteEtale

end Stacks.EtaleCohomology

end
