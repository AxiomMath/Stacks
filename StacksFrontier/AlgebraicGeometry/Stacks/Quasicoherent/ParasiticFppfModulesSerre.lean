module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedCategoryBIsoClosedInstance
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction

/-!
# The parasitic modules on the fppf site form a Serre subcategory, at module universe `u`

Let `𝒳` be an algebraic stack. **Stacks 0774** (2)(b) says that the parasitic modules form a
Serre subcategory of `Mod(𝒪_𝒳)`. The library has this as
`AlgebraicGeometry.Stack.isSerreClass_parasiticModules` for modules whose sections live in a
universe `t` with `UnivLE.{u + 1, t}`, which excludes the module universe `u` of
`AlgebraicGeometry.Stack.fppfModules`, the category the Verdier quotient `D_QCoh(𝒪_𝒳)` of
**Stacks 07B6** is formed from. At that universe the statement is proved here by a different
route: a module on the fppf site is parasitic exactly when its restriction to the flat-fppf site
vanishes (**Stacks 07AR** (2)), and restriction is exact, so the parasitic modules are the inverse
image of the zero objects under an exact functor, which is a Serre class.

Consequently, for any weak Serre subcategory `𝓛` of `Mod(𝒪_𝒳)`, `Parasitic(𝒪_𝒳) ∩ 𝓛` is a
weak Serre subcategory too (`CategoryTheory.ObjectProperty.isWeakSerreClass_inf`), so that
`D_{Parasitic ∩ 𝓛}(𝒪_𝒳)` is a triangulated subcategory of `D(𝒪_𝒳)`.

## Main results

* `AlgebraicGeometry.Stack.parasiticModules_fppf_eq_inverseImage`: the parasitic modules are
  those whose restriction to the flat-fppf site is zero.
* `AlgebraicGeometry.Stack.isSerreClass_parasiticFppfModules`: **Stacks 0774** (2)(b) on
  `AlgebraicGeometry.Stack.fppfModules`.

## References

* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 07AR](https://stacks.math.columbia.edu/tag/07AR)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

open FlatFppf in
attribute [local instance] hasSheafCompose_forget_ringCat hasSheafCompose_forget_commRingCat
  Stacks.hasSheafCompose_forget₂_commRingCat isContinuous_inclusion_topology
  isCocontinuous_inclusion_topology hasSheafify_addCommGrpCat
  wEqualsLocallyBijective_addCommGrpCat hasSheafify_fppf_addCommGrpCat
  wEqualsLocallyBijective_fppf_addCommGrpCat hasSheafify_associatedTopology_ab
  wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- A module on the fppf site of an algebraic stack is parasitic exactly when its restriction to
the flat-fppf site vanishes: the parasitic modules are the inverse image of the zero objects
under restriction. This is
`AlgebraicGeometry.Stack.FlatFppf.isParasitic_iff_isZero_moduleRestriction` read as an equality
of object properties. -/
theorem parasiticModules_fppf_eq_inverseImage :
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf : ObjectProperty (fppfModules B S hS 𝒳)) =
      ObjectProperty.inverseImage (IsZero (C := FlatFppf.flatFppfModules B S hS 𝒳))
        (FlatFppf.moduleRestriction B S hS 𝒳) := by
  ext F
  exact FlatFppf.isParasitic_iff_isZero_moduleRestriction B S hS 𝒳 F

/-- **Stacks 0774** (2)(b) at the module universe of `AlgebraicGeometry.Stack.fppfModules`. The
parasitic modules form a Serre subcategory of `Mod(𝒪_𝒳)`: they are the inverse image of the zero
objects under restriction to the flat-fppf site, which is exact. -/
instance isSerreClass_parasiticFppfModules :
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf :
      ObjectProperty (fppfModules B S hS 𝒳)).IsSerreClass := by
  let R : fppfModules B S hS 𝒳 ⥤ FlatFppf.flatFppfModules B S hS 𝒳 :=
    FlatFppf.moduleRestriction B S hS 𝒳
  have : PreservesFiniteLimits R := FlatFppf.moduleRestriction_preservesFiniteLimits B S hS 𝒳
  have : PreservesFiniteColimits R := FlatFppf.moduleRestriction_preservesFiniteColimits B S hS 𝒳
  have heq : (parasiticModules.{u, w, u} B S hS 𝒳 .fppf :
      ObjectProperty (fppfModules B S hS 𝒳)) = ObjectProperty.inverseImage IsZero R :=
    parasiticModules_fppf_eq_inverseImage B S hS 𝒳
  rw [heq]
  infer_instance

end AlgebraicGeometry.Stack
