module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModulesCurves.RestrictToDenseOpen
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.BiggerSiteGlobalCohomology
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Étale cohomology of `Λ`-modules collapses across an integral morphism

Let `i : Z ⟶ X` be an integral morphism of schemes — a closed immersion, for instance — and let
`A` be a sheaf of `Λ`-modules on `Z_étale`. This file shows `H^n_étale(Z, A) ≅ H^n_étale(X, i_*A)`
for every `n`, with no hypothesis on `A`: the higher direct images along an integral morphism
vanish ([Stacks, Tag 095U] in degree zero,
`Stacks.EtaleCohomology.isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom`), the direct
image preserves injective objects
(`Stacks.EtaleCohomology.etaleModuleDirectImage_preservesInjectiveObjects`), and the Leray
collapse at an acyclic object (`Stacks.RightDerivedComp.objIso`) then identifies `H^n(X, i_*A)`
with the cohomology of `i_* ⋙ Γ_X` at `A`; finally `i_* ⋙ Γ_X ≅ Γ_Z`, because `Γ_X ∘ i_*` is
sections over the base change of the terminal object of `X.Etale`, which is the terminal object
of `Z.Etale` (`Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso`).

This is the module-coefficient, integral-morphism case of the Leray collapse [Stacks, Tag 0733].

## Main definitions

* `Stacks.EtaleCohomology.TorsionModules.gammaComp_etaleModuleDirectImage_iso` —
  `i_* ⋙ Γ_X ≅ Γ_Z`.
* `Stacks.EtaleCohomology.TorsionModules.moduleEtaleCohomology_isIntegralHom_iso` — the
  collapse `H^n(Z, A) ≅ H^n(X, i_*A)`.

## References

* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology.TorsionModules

variable (Λ : Type r) [CommRing Λ] {Z X : Scheme.{u}} (i : Z ⟶ X)

/-- **`Γ_X ∘ i_* ≅ Γ_Z`.** Sections of `i_*A` over the terminal object of `X.Etale` are, by
definition of `i_*` as restriction along base change, sections of `A` over the base change of
that terminal object, which is the terminal object of `Z.Etale` because base change preserves
finite limits. -/
def gammaComp_etaleModuleDirectImage_iso :
    Stacks.EtaleCohomology.etaleModuleDirectImage.{u, r} Λ i ⋙
        Sheaf.Γ X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) ≅
      Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) :=
  Stacks.Cohomology.BiggerSiteGlobal.gammaCompRestrictionIso X.smallEtaleTopology
    Z.smallEtaleTopology (smallEtaleBaseChange i) (ModuleCat.{max (u + 1) r} Λ)
    terminalIsTerminal (terminalIsTerminal.isTerminalObj (smallEtaleBaseChange i)) rfl

variable [IsIntegralHom i]

/-- **Étale cohomology of `Λ`-modules collapses across an integral morphism**:
`H^n_étale(Z, A) ≅ H^n_étale(X, i_*A)` for every sheaf `A` of `Λ`-modules on `Z_étale` and every
`n`. The higher direct images of `A` along `i` vanish, so the Leray collapse at an acyclic object
identifies the right side with the cohomology of `i_* ⋙ Γ_X` at `A`, and `i_* ⋙ Γ_X ≅ Γ_Z`
identifies that with the left side. -/
def moduleEtaleCohomology_isIntegralHom_iso (n : ℕ)
    (A : Sheaf Z.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :
    (moduleEtaleCohomology.{u, r, r} Λ Z n).obj A ≅
      (moduleEtaleCohomology.{u, r, r} Λ X n).obj
        ((Stacks.EtaleCohomology.etaleModuleDirectImage.{u, r} Λ i).obj A) :=
  (Functor.rightDerivedIsoOfNatIso (gammaComp_etaleModuleDirectImage_iso Λ i) n).symm.app A ≪≫
    Stacks.RightDerivedComp.objIso (Stacks.EtaleCohomology.etaleModuleDirectImage.{u, r} Λ i)
      (injectiveResolution A)
      (fun m hm ↦
        Stacks.EtaleCohomology.isZero_rightDerived_etaleModuleDirectImage_of_isIntegralHom
          Λ i A m (by omega))
      (Sheaf.Γ X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) n

end Stacks.EtaleCohomology.TorsionModules

end
