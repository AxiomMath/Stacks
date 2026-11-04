module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantModuleSheafOpenDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantSectionsConnected

/-!
# A locally constant sheaf on an integral normal scheme is a direct image from a dense open
(statement)

Let `X` be an integral normal scheme, `h : V ⟶ X` an open immersion with `V` nonempty, `Λ` a ring
and `F` a locally constant sheaf of `Λ`-modules on `X_étale`. Then the unit `F ⟶ h_* h⁻¹ F` of
`h⁻¹ ⊣ h_*` is an isomorphism.

Route. For a constant sheaf this is the module form of
[Tag 09Z5](https://stacks.math.columbia.edu/tag/09Z5) (2),
`Stacks.EtaleCohomology.constantModuleSheafOpenDirectImageIso`: `M_X ≅ h_* M_V`, so `M_X` lies in
the essential image of the fully faithful `h_*` and the unit is invertible there (as in
`Stacks.EtaleCohomology.Purity.affineLineConstantUnitIso`). In general, being an isomorphism is
étale local: over a trivializing étale `W ⟶ X`, refined to integral opens (which are normal,
`Stacks.EtaleCohomology.exists_isIntegral_open_of_etale`) and meeting `V` because `X` is
irreducible, the inverse image of the unit is the unit of the base-changed open immersion
`W ×_X V ⟶ W` at the constant sheaf `F|_W`, through the base change of `h_*` along the étale
`W ⟶ X` and the corresponding mate coherence.

## Main definitions

* `Stacks.EtaleCohomology.LisseOpenUnitIsoInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] hasSheafify_over_etaleModules_locallyConstantSections

/-- The proposition that the unit `F ⟶ h_* h⁻¹ F` is an isomorphism for every locally constant
sheaf `F` of `Λ`-modules on an integral normal scheme `X` and every open immersion `h : V ⟶ X`
with `V` nonempty. -/
def LisseOpenUnitIsoInput : Prop :=
  ∀ {X V : Scheme.{u}} [IsIntegral X] [IsNormal X] (h : V ⟶ X) [IsOpenImmersion h] [Nonempty V]
    (Λ : Type) [Ring Λ] (Q : ModuleCat.{u + 1} Λ → Prop) (F : EtaleModules.{u, 0} Λ X),
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q F →
    IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ h).unit.app F)

end Stacks.EtaleCohomology

end
