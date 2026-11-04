module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineComparisonTransport

/-!
# The equivalence of quasi-coherent modules attached to an isomorphism of schemes

An isomorphism of schemes `e : X ≅ Y` induces an equivalence
`QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` between the categories of quasi-coherent modules.

## Main definitions

* `AlgebraicGeometry.quasicoherentModulesEquivOfSchemeIso` — the equivalence of categories of
  quasi-coherent modules induced by an isomorphism of schemes.

## Implementation notes

Both `e.hom` and `e.inv` are isomorphisms, hence open immersions, so restriction of modules
along them is defined and the two restrictions are mutually inverse equivalences of the
categories of *all* modules: this is `Stacks.DerivedQCoh.modulesRestrictionEquivalence`.
Restriction along an open immersion preserves quasi-coherence
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`), so that equivalence
restricts to the quasi-coherent full subcategories by
`Stacks.DerivedQCoh.liftObjectPropertyEquivalence`.

The direction of the induced functor is the one of the *direct* image: the functor of the
equivalence is restriction along `e.inv`, which sends a module on `X` to a module on `Y`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **An isomorphism of schemes induces an equivalence of the categories of quasi-coherent
modules.** The functor is restriction of modules along `e.inv` and its inverse is restriction
along `e.hom`. -/
noncomputable def quasicoherentModulesEquivOfSchemeIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  have hinv : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  have hhom : IsOpenImmersion e.hom := IsOpenImmersion.of_isIso e.hom
  Stacks.DerivedQCoh.liftObjectPropertyEquivalence
    (Stacks.DerivedQCoh.modulesRestrictionEquivalence e) _ _
    (fun M hM ↦ @Scheme.Modules.isQuasicoherent_restrictFunctor Y X e.inv hinv M hM)
    (fun N hN ↦ @Scheme.Modules.isQuasicoherent_restrictFunctor X Y e.hom hhom N hN)

end AlgebraicGeometry

end
