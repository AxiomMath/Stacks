module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedFlatFppfRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StackModuleRule

/-!
# Modules on an algebraic stack have enough injectives

Let `𝒳` be an algebraic stack over `S` and `τ` one of the five topologies of **Stacks 06TP**.
The category `Mod(𝒳_τ, 𝒪_𝒳)` of sheaves of modules on the site `𝒳_τ` over the structure sheaf of
**Stacks 06TV**, at the module universe `u` of the schemes, has enough injectives, and is in fact
a Grothendieck abelian category.  The fppf case, `Mod(𝒪_𝒳)`, is recorded separately.

This is **Stacks 01DU** (sheaves of modules on a ringed site have enough injectives) for the
site of an algebraic stack, which is not small: its objects lie in `Type (u + 1)`, but it is
essentially `u`-small (`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`).

## Main results

* `AlgebraicGeometry.Stack.isGrothendieckAbelian_moduleRingSheaf` and
  `AlgebraicGeometry.Stack.enoughInjectives_moduleRingSheaf`: the two statements for every `τ`.
* `AlgebraicGeometry.Stack.isGrothendieckAbelian_fppfModules`: `Mod(𝒪_𝒳)` is Grothendieck
  abelian.
* `AlgebraicGeometry.Stack.enoughInjectives_fppfModules`: `Mod(𝒪_𝒳)` has enough injectives.

## References

* [Stacks Project, Tag 01DU](https://stacks.math.columbia.edu/tag/01DU)
* [Stacks Project, Tag 06TV](https://stacks.math.columbia.edu/tag/06TV)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Modules on the site of an algebraic stack form a Grothendieck abelian category**, for any
of the five topologies `τ` of **Stacks 06TP**, at the module universe `u` of the schemes. -/
theorem isGrothendieckAbelian_moduleRingSheaf (τ : SiteKind) :
    letI := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ
    letI := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p τ
    IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :=
  let := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids τ
  let := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p τ
  SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _

/-- **Modules on the site of an algebraic stack have enough injectives** (Stacks 01DU), for any of
the five topologies `τ` of **Stacks 06TP**, at the module universe `u` of the schemes. -/
theorem enoughInjectives_moduleRingSheaf (τ : SiteKind) :
    EnoughInjectives (SheafOfModules.{u}
      (Stacks.RelativeCech.moduleRingSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ)) :=
  let := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids τ
  let := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p τ
  have := isGrothendieckAbelian_moduleRingSheaf B S hS 𝒳 τ
  inferInstance

/-- **Modules on the fppf site of an algebraic stack form a Grothendieck abelian category**, at
the module universe `u` of the schemes. -/
theorem isGrothendieckAbelian_fppfModules :
    letI := hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .fppf
    letI := FibredSite.wEqualsLocallyBijective_associatedTopology B S hS 𝒳.val.val.p .fppf
    IsGrothendieckAbelian.{u} (fppfModules B S hS 𝒳) :=
  isGrothendieckAbelian_moduleRingSheaf B S hS 𝒳 .fppf

/-- **Modules on the fppf site of an algebraic stack have enough injectives**, at the module
universe `u` of the schemes. -/
theorem enoughInjectives_fppfModules : EnoughInjectives (fppfModules B S hS 𝒳) :=
  enoughInjectives_moduleRingSheaf B S hS 𝒳 .fppf

end AlgebraicGeometry.Stack

end
