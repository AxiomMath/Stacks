module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffineAcyclic
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactness
public import StacksFrontier.Homology.CompositeCollapse

/-!
# The higher direct images along `ε : S_étale ⟶ S_Zar` vanish at quasi-coherent coefficients

Let `S` be a scheme of a big étale site and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the
morphism of ringed sites of [Stacks, Tag 070R], whose direct image on sheaves of modules is
`AlgebraicGeometry.SmallEtale.restrictModule`. Then

`R ᵖ ε_*(𝓜) = 0` for every `p > 0`

whenever the `𝒪`-module `𝓜` on the small étale site is **quasi-coherent on the site**. The
hypothesis cannot be dropped: `ε_*` is *not* exact at arbitrary coefficients.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_restrictModule`: **the vanishing.**
* `AlgebraicGeometry.SmallEtale.acyclic_restrictModule`: a module quasi-coherent on the site is
  acyclic for `ε_*`, in the sense of `Stacks.RightDerivedComp.acyclic`.

## References

* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 03P2](https://stacks.math.columbia.edu/tag/03P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image of sheaves of modules along the structure-sheaf comparison of `ε` is
additive. -/
public instance pushforward_structureMap_additive :
    (SheafOfModules.pushforward.{u} (structureMap B S hS)).Additive :=
  Stacks.SheafOfModules.pushforward_additive _

/-- Restriction to the small Zariski site is additive. -/
public instance restrictModule_additive :
    (AlgebraicGeometry.SmallEtale.restrictModule B S hS).Additive :=
  Stacks.SheafOfModules.pushforward_additive _

/-- **The higher direct images along `ε : S_étale ⟶ S_Zar` vanish at a module quasi-coherent on
the site.**  For an `𝒪`-module `𝓜` on the small étale site of `S` which is quasi-coherent on the
site, `R ᵖ ε_*(𝓜) = 0` for every `p > 0`, where `ε_*` is
`AlgebraicGeometry.SmallEtale.restrictModule`. -/
public theorem isZero_rightDerived_restrictModule
    (𝓜 : SheafOfModules.{u} (structureSheaf B S hS)) (h𝓜 : 𝓜.IsQuasicoherentOnSite)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((restrictModule B S hS).rightDerived p).obj 𝓜) := by
  refine Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (opensToSmallEtale B S hS) _ _ (structureMap B S hS) p 𝓜 fun V ↦ ?_
  exact ⟨affineOpensPresieve S V, generate_affineOpensPresieve_mem S V, fun W g hg ↦
    isZero_rightDerived_evaluation_of_isAffine B S hS 𝓜 h𝓜 ((opensToSmallEtale B S hS).obj W) hg
      p hp⟩

/-- **A module quasi-coherent on the site is acyclic for `ε_*`**: its higher right derived
images under `AlgebraicGeometry.SmallEtale.restrictModule` vanish. -/
public theorem acyclic_restrictModule
    (𝓜 : SheafOfModules.{u} (structureSheaf B S hS)) (h𝓜 : 𝓜.IsQuasicoherentOnSite) :
    Stacks.RightDerivedComp.acyclic (restrictModule B S hS) 𝓜 :=
  isZero_rightDerived_restrictModule B S hS 𝓜 h𝓜

end AlgebraicGeometry.SmallEtale

end
