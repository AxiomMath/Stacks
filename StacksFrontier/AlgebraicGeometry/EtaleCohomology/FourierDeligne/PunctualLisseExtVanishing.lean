module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.PunctualEtaleModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LisseOpenUnitIsoProof
public import StacksFrontier.CategoryTheory.Abelian.ExtOneRightAdjoint
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeHomVanishing

/-!
# No extensions of a locally constant sheaf by a punctual sheaf

Let `X` be an integral normal scheme, `P` a punctual sheaf of `Λ`-modules on `X_étale` (it vanishes
on a nonempty open `j : U ⟶ X`) and `L` a locally constant sheaf. Then `Ext¹(P, L) = 0`: the unit
`L ⟶ j_* j⁻¹ L` is an isomorphism (`Stacks.EtaleCohomology.lisseOpenUnitIsoInput`) and `j⁻¹ P = 0`,
so `CategoryTheory.Abelian.Ext.subsingleton_ext_one_of_isIso_unit_app` applies to `j⁻¹ ⊣ j_*`. In
`D⁺(X_étale, Λ)` this says that every morphism `P[-m] ⟶ L[-k]` with `m = k + 1` vanishes.

This is the step (L3) of the single-level argument for the irreducibility of the Fourier
transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.subsingleton_ext_one_of_isPunctual_of_isLocallyConstantWith`.
* `Stacks.EtaleCohomology.singleFunctor_hom_eq_zero_of_isPunctual_of_isLocallyConstantWith`.

## Implementation notes

The morphisms of `D⁺` are read in the standard model `HasDerivedCategory.standard`, the model of
the Fourier transform.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w u

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits

variable (Λ : Type) [Ring Λ] {X : Scheme.{u}} [IsIntegral X] [IsNormal X]

/-- **(L3) `Ext¹(P, L) = 0` for `P` punctual and `L` locally constant** on an integral normal
scheme. -/
theorem subsingleton_ext_one_of_isPunctual_of_isLocallyConstantWith
    [HasExt.{w} (EtaleModules.{u, 0} Λ X)] {P L : EtaleModules.{u, 0} Λ X}
    (hP : IsPunctualEtaleModule Λ P) (Q : ModuleCat.{u + 1} Λ → Prop)
    (hL : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q L) :
    Subsingleton (Abelian.Ext.{w} P L 1) := by
  obtain ⟨U, jU, hjU, hU, hz⟩ := hP
  have := hjU
  have := hU
  have : IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ jU).unit.app L) :=
    lisseOpenUnitIsoInput jU Λ Q L hL
  exact Abelian.Ext.subsingleton_ext_one_of_isIso_unit_app (etaleModuleInverseImageAdj.{u, 0} Λ jU)
    P hz L

attribute [local instance] HasDerivedCategory.standard in
/-- **(L3) in `D⁺`: every morphism `P[-m] ⟶ L[-k]`, `m = k + 1`, vanishes** for `P` punctual and
`L` locally constant on an integral normal scheme. -/
theorem singleFunctor_hom_eq_zero_of_isPunctual_of_isLocallyConstantWith
    {P L : EtaleModules.{u, 0} Λ X} (hP : IsPunctualEtaleModule Λ P)
    (Q : ModuleCat.{u + 1} Λ → Prop)
    (hL : Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q L) (m k : ℤ)
    (hmk : 1 + k = m)
    (f : (DerivedCategory.Plus.singleFunctor _ m).obj P ⟶
      (DerivedCategory.Plus.singleFunctor _ k).obj L) : f = 0 :=
  Stacks.DerivedCategoryPlus.singleFunctor_hom_eq_zero_of_subsingleton_ext P L m k 1
    (by exact_mod_cast hmk)
    (subsingleton_ext_one_of_isPunctual_of_isLocallyConstantWith Λ hP Q hL) f

end Stacks.EtaleCohomology

end
