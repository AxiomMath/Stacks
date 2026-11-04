module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Point.FlatFiberTensorExact

/-!
# Tensoring with an étale sheaf of modules with flat fibers is exact, on Mathlib's small étale site

For a scheme `S : Scheme.{u}` and a commutative ring `Λ`, sheaves of `Λ`-modules on Mathlib's
small étale site `S.smallEtaleTopology` (`Stacks.EtaleCohomology.EtaleModules`, values in
`ModuleCat.{u + 1} Λ`) carry the tensor product of `CategoryTheory.Sheaf.monoidalCategory`. Given
a family of geometric points `s i : Spec Ω i ⟶ S` covering `S`, their universe lifts form a
conservative family of points (`AlgebraicGeometry.Scheme.isConservative_pointSmallEtale_ulift`),
so the site-independent criterion
`ObjectProperty.IsConservativeFamilyOfPoints.preservesFiniteLimits_tensorRight_of_flat` applies:
`- ⊗ G` is exact as soon as the fibers of `G` at these points are flat. This is the form in which
the cup product `Stacks.ExtCup.cup` on the geometric fibre `X_k̄` is formed, in the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.etaleModules_AB5OfSize`: filtered colimits of modules in
  `Type (u + 1)` are exact.
* `Stacks.EtaleCohomology.isMonoidal_W_etaleModules`: the morphisms inverted by sheafification
  form a monoidal class.
* `Stacks.EtaleCohomology.preservesFiniteLimits_tensorRight_etaleModules_of_flat`: the criterion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ]

/-- Modules in `Type (u + 1)` have colimits of size `u + 1`. -/
local instance : HasColimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.hasColimitsOfSize.{u + 1, 0, u + 1, u + 1} Λ

/-- Modules in `Type (u + 1)` have limits of size `u + 1`. -/
local instance : HasLimitsOfSize.{u + 1, u + 1, u + 1, u + 2} (ModuleCat.{u + 1, 0} Λ) :=
  ModuleCat.instHasLimitsOfSize.{u + 1, u + 1, 0}

/-- Filtered colimits of modules in `Type (u + 1)` of size `u + 1` are exact: they are computed
on the underlying abelian groups. -/
theorem etaleModules_AB5OfSize : AB5OfSize.{u + 1, u + 1} (ModuleCat.{u + 1, 0} Λ) where
  ofShape J _ _ := by
    have : PreservesFilteredColimitsOfSize.{u + 1, u + 1}
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) := inferInstance
    exact HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- The forgetful functor of modules in `Type (u + 1)` preserves filtered colimits of size
`u + 1`. -/
theorem etaleModules_preservesFilteredColimits_forget :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget (ModuleCat.{u + 1, 0} Λ)) :=
  comp_preservesFilteredColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
    (forget AddCommGrpCat.{u + 1})

attribute [local instance] etaleModules_AB5OfSize etaleModules_preservesFilteredColimits_forget
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorLeft
  CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.moduleCat_preservesColimits_tensorRight

/-- **The morphisms inverted by sheafification form a monoidal class** for sheaves of modules on
the small étale site: the site has enough points relative to `u + 1`
(`AlgebraicGeometry.Scheme.hasEnoughPoints_smallEtaleTopology`). -/
theorem isMonoidal_W_etaleModules (S : Scheme.{u}) :
    (S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal :=
  by
  have : GrothendieckTopology.HasEnoughPoints.{u + 1} S.smallEtaleTopology :=
    Scheme.hasEnoughPoints_smallEtaleTopology.{0, u} S
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty S.smallEtaleTopology
  exact hP.isMonoidal_W (ModuleCat.{u + 1} Λ)

attribute [local instance] Sheaf.monoidalCategory

/-- **Tensoring with a sheaf of modules with flat fibers is exact on Mathlib's small étale
site.** Let `s i : Spec Ω i ⟶ S` be geometric points covering `S`, indexed by a `u`-small type.
If the fiber of `G` at the universe lift of every `s i` is a flat `Λ`-module, then `- ⊗ G` is
additive, left exact and right exact. -/
theorem preservesFiniteLimits_tensorRight_etaleModules_of_flat (S : Scheme.{u})
    [(S.smallEtaleTopology.W (A := ModuleCat.{u + 1} Λ)).IsMonoidal]
    {ι : Type*} [Small.{u} ι] {Ω : ι → Type u} [∀ i, Field (Ω i)] [∀ i, IsSepClosed (Ω i)]
    (s : ∀ i, Spec (.of (Ω i)) ⟶ S) (hs : ⋃ i, Set.range (s i) = .univ)
    (G : EtaleModules.{u, 0} Λ S)
    (hG : ∀ i, Module.Flat Λ
      (((Scheme.pointSmallEtale (s i)).ulift.{u + 1}).sheafFiber
        (A := ModuleCat.{u + 1} Λ) |>.obj G)) :
    (tensorRight G).Additive ∧ PreservesFiniteLimits (tensorRight G) ∧
      PreservesFiniteColimits (tensorRight G) := by
  have hP := Scheme.isConservative_pointSmallEtale_ulift.{0, u} s hs
  refine hP.preservesFiniteLimits_tensorRight_of_flat Λ G fun Φ => ?_
  obtain ⟨Φ, hΦ⟩ := Φ
  obtain ⟨i⟩ := hΦ
  exact hG i

end Stacks.EtaleCohomology

end
