module

public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomOpModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafEffacement
public import StacksFrontier.Homology.CompositeCollapse

/-!
# The abelian internal Hom out of an étale sheaf of `Λ`-modules

Let `Y` be a scheme, `Λ` a ring (not necessarily commutative) and `G` a sheaf of left
`Λ`-modules on `Y_étale`. For an abelian sheaf `F` the internal Hom `ℋom_ℤ(G, F)` is a sheaf of
right `Λ`-modules, i.e. of `Λᵐᵒᵖ`-modules (`Stacks.EtaleCohomology.etaleHomOp`). This file
identifies its global sections with `Hom_ℤ(G, F)` and proves that it is acyclic for global
sections when `F` is an injective abelian sheaf.

## Main definitions

* `Stacks.EtaleCohomology.etaleHomOp`: the functor `F ↦ ℋom_ℤ(G, F)` from abelian sheaves to
  sheaves of `Λᵐᵒᵖ`-modules on `Y_étale`.
* `Stacks.EtaleCohomology.etaleHomOpGlobalSectionsIso`: `Γ(Y, ℋom_ℤ(G, F)) ≅ Hom_ℤ(G, F)`.

## Main results

* `Stacks.EtaleCohomology.isZero_rightDerived_etaleHomOp_of_injective`: for `I` an injective
  abelian sheaf, `Hⁿ(Y, ℋom_ℤ(G, I)) = 0` for `n > 0`.
* `Stacks.EtaleCohomology.rightAcyclic_etaleHomOp_of_injective`: the same, as acyclicity for the
  derived functor of global sections on the bounded below derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MulOpposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] (Y : Scheme.{u})

/-- **`ℋom_ℤ(G, -)`** from abelian sheaves on `Y_étale` to sheaves of `Λᵐᵒᵖ`-modules, for a
sheaf `G` of left `Λ`-modules: `op r` acts on a local morphism by precomposition with `r • -`. -/
abbrev etaleHomOp (G : EtaleModules.{u, 0} Λ Y) :
    Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ EtaleModules.{u, 0} Λᵐᵒᵖ Y :=
  Stacks.AbelianInternalHom.homOpFunctor Y.smallEtaleTopology G

/-- The abelian sheaf underlying `ℋom_ℤ(G, F)` is the abelian internal Hom of `G` into `F`. -/
lemma etaleModuleUnderlyingAbelian_etaleHomOp (G : EtaleModules.{u, 0} Λ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleModuleUnderlyingAbelian Y Λᵐᵒᵖ).obj ((etaleHomOp Λ Y G).obj F) =
      internalHomSheaf Y.smallEtaleTopology
        (Stacks.AbelianInternalHom.toAb Y.smallEtaleTopology G) F := rfl

/-- **`Γ(Y, ℋom_ℤ(G, F)) ≅ Hom_ℤ(G, F)`**, as `Λᵐᵒᵖ`-modules. -/
def etaleHomOpGlobalSectionsIso (G : EtaleModules.{u, 0} Λ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ Y).obj ((etaleHomOp Λ Y G).obj F) ≅
      (letI := Stacks.AbelianInternalHom.sheafHomModule Y.smallEtaleTopology G F;
        ModuleCat.of Λᵐᵒᵖ (Stacks.AbelianInternalHom.toAb Y.smallEtaleTopology G ⟶ F)) :=
  (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λᵐᵒᵖ)
      terminalIsTerminal).app _ ≪≫
    Stacks.AbelianInternalHom.homOpSectionsIso Y.smallEtaleTopology G terminalIsTerminal F

/-- **`Hⁿ(Y, ℋom_ℤ(G, I)) = 0` for `n > 0`**, for an injective abelian sheaf `I` and any sheaf
`G` of `Λ`-modules. -/
theorem isZero_rightDerived_etaleHomOp_of_injective (G : EtaleModules.{u, 0} Λ Y)
    (I : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] (n : ℕ) (hn : 0 < n) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ Y).rightDerived n).obj
      ((etaleHomOp Λ Y G).obj I)) := by
  have : IsGrothendieckAbelian.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Y
  have : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    CategoryTheory.IsGrothendieckAbelian.hasExt _
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hH := Stacks.AbelianInternalHom.subsingleton_H_internalHomSheaf.{u, u + 1, u + 1}
    Y.smallEtaleTopology (Stacks.AbelianInternalHom.toAb Y.smallEtaleTopology G) I m
  let e := (etaleModuleCohomologyIsoFunctorH Λᵐᵒᵖ (m + 1)).app ((etaleHomOp Λ Y G).obj I)
  have : Subsingleton ((etaleModuleUnderlyingAbelian Y Λᵐᵒᵖ ⋙
      Sheaf.functorH.{u + 1, u + 1, u, u + 1} Y.smallEtaleTopology (m + 1)).obj
        ((etaleHomOp Λ Y G).obj I)) := hH
  have : Subsingleton (((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ Y).rightDerived (m + 1)).obj
      ((etaleHomOp Λ Y G).obj I)) :=
    (e.addCommGroupIsoToAddEquiv).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end Stacks.EtaleCohomology
