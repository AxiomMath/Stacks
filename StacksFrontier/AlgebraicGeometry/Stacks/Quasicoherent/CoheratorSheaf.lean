module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentOnSiteCoarserFromFppf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentSmallness

/-!
# The inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` of Stacks 0778 on the faithful `LQCoh^fbc(𝒪_𝒳)`

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/Coherator.lean` builds the right adjoint of
the inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` of **Stacks 0778** with `LQCoh^fbc(𝒪_𝒳)` cut out by
`AlgebraicGeometry.Stack.IsLocallyQuasicoherentWithFlatBaseChange`, whose flat base change clause
is the *presheaf* reading `AlgebraicGeometry.Stack.HasFlatBaseChangeProperty`.  That reading is
strictly stronger than the source's **Stacks 0762**, and too strong for the inclusion to exist:
for `𝒳 = 𝔸¹_k = Spec k[t]`, the quasi-coherent module of `k[t]/(t)` and the projection
`𝔸² ⟶ 𝔸¹`, the presheaf-level comparison map on `𝔸² ∖ {0}` is the inclusion
`k[x] ⟶ k[x, x⁻¹]`.  So the input `hinc` of that construction fails for a quasi-coherent module.

This file sets up the same inclusion on the source's subcategory: the sheaves of modules on
`𝒳_étale` which are locally quasi-coherent (**Stacks 06WJ**) and have the flat base change
property read on *sheaves* of modules (**Stacks 0762**,
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheaf`), the weak Serre class
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheaf`.  The auxiliary big étale site
is the canonical `AlgebraicGeometry.associatedBigEtaleSite`, so no choice of étale site appears.
The coherator itself is in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeSheafCoherator.lean`.

## Main definitions

* `AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeSheafModules`: the full
  subcategory `LQCoh^fbc(𝒪_𝒳)` of `Mod(𝒳_étale, 𝒪_𝒳)`.
* `AlgebraicGeometry.Stack.quasicoherentToFlatBaseChangeSheaf`: the inclusion
  `QCoh(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)`, fully faithful.

## Main results

* `AlgebraicGeometry.Stack.locallySmall_locallyQuasicoherentFlatBaseChangeSheafModules`: the
  subcategory is locally `u`-small.

## Implementation notes

The flat base change half of the containment, `hfbc`, is a named hypothesis: it is the
sheaf-level reading of clause (b) of the forward direction of **Stacks 06WK**.  None of these
declarations carries a `stacks` attribute while it is a hypothesis.

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **`LQCoh^fbc(𝒪_𝒳)`**, the full subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` of the locally
quasi-coherent modules with the flat base change property of **Stacks 0762** read on sheaves of
modules, over the canonical big étale site. -/
abbrev locallyQuasicoherentFlatBaseChangeSheafModules :=
  (locallyQuasicoherentFlatBaseChangeSheaf B (associatedBigEtaleSite B) rfl S hS p
    hp).FullSubcategory

/-- **The inclusion `QCoh(𝒪_𝒳) ⟶ LQCoh^fbc(𝒪_𝒳)` of Stacks 0778.**  A quasi-coherent module on
the associated fppf site restricts to a module on the associated étale site with the same
presheaf of modules; it is locally quasi-coherent by
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_toSiteModules_etale`, and it has the flat base
change property by `hfbc`. -/
def quasicoherentToFlatBaseChangeSheaf
    (hfbc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F)) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp ⥤
      locallyQuasicoherentFlatBaseChangeSheafModules B S hS p hp :=
  (locallyQuasicoherentFlatBaseChangeSheaf B (associatedBigEtaleSite B) rfl S hS p hp).lift
    (FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale)
    fun F =>
      ⟨isLocallyQuasicoherent_toSiteModules_etale B (associatedBigEtaleSite B) rfl S hS p hp F,
        hfbc F⟩

/-- **The inclusion of Stacks 0778 is fully faithful**: restricting a module sheaf to a coarser
topology changes neither its presheaf of modules nor its morphisms. -/
def fullyFaithfulQuasicoherentToFlatBaseChangeSheaf
    (hfbc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
      HasFlatBaseChangePropertySheaf B (associatedBigEtaleSite B) rfl S hS p hp
        ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F)) :
    (quasicoherentToFlatBaseChangeSheaf B S hS p hp hfbc).FullyFaithful where
  preimage {_ _} f := ObjectProperty.homMk ⟨f.hom.val⟩
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- **`LQCoh^fbc(𝒪_𝒳)` is locally `u`-small**, as a full subcategory of the Grothendieck abelian
category of module sheaves on the essentially `u`-small associated étale site. -/
theorem locallySmall_locallyQuasicoherentFlatBaseChangeSheafModules :
    LocallySmall.{u} (locallyQuasicoherentFlatBaseChangeSheafModules B S hS p hp) :=
  have : HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  have : (associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u, u + 1, u + 1, u} _
  have := (SheafOfModules.isGrothendieckAbelian_of_essentiallySmall
    (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))).locallySmall
  inferInstance

end AlgebraicGeometry.Stack

end
