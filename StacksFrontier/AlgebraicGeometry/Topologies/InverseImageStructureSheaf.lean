module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The inverse-image structure sheaf of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes.  The inverse image `f⁻¹𝒪_Y` of the structure sheaf of
the target is a sheaf of commutative rings on `X`, and the Zariski site of `X` carrying it is a
ringed site `(X, f⁻¹𝒪_Y)`.  Forgetting commutativity gives the sheaf of rings over which sheaves
of `f⁻¹𝒪_Y`-modules are indexed, and the structure map of `f` becomes a homomorphism
`f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of rings.

This is the ring sheaf through which a *relative* condition on an `𝒪_X`-module is expressed: an
`𝒪_X`-module read as an `f⁻¹𝒪_Y`-module.  Relative pseudo-coherence, relative perfectness and
relative Tor dimension are conditions of this kind.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageStructureSheaf` is `f⁻¹𝒪_Y`, a sheaf of commutative
  rings on `X`.
* `AlgebraicGeometry.Scheme.Hom.inverseImageRingedSite` is the ringed site `(X, f⁻¹𝒪_Y)`: the
  Zariski site of `X` carrying that structure sheaf.
* `AlgebraicGeometry.Scheme.Hom.inverseImageRingCatSheaf` is `f⁻¹𝒪_Y` with commutativity
  forgotten, the sheaf of rings over which sheaves of `f⁻¹𝒪_Y`-modules are taken.
* `AlgebraicGeometry.Scheme.Hom.inverseImageRingCatSheafMap` is the structure map
  `f⁻¹𝒪_Y ⟶ 𝒪_X`, as a homomorphism of sheaves of rings.

## Main results

* `AlgebraicGeometry.Scheme.Hom.inverseImageStructureSheaf_eq`: `f⁻¹𝒪_Y` is the structure sheaf
  of the inverse-image ringed space of Tag 0096, by `rfl`.
* `AlgebraicGeometry.Scheme.Hom.homEquiv_inverseImageStructureMap`: the structure map
  `f⁻¹𝒪_Y ⟶ 𝒪_X` corresponds to `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` under the inverse-image/direct-image
  adjunction.
* `AlgebraicGeometry.Scheme.Hom.inverseImageRingCatSheaf_eq`: the sheaf of rings of the
  inverse-image ringed site is `f⁻¹𝒪_Y` composed with the forgetful functor to rings, by `rfl`,
  which is the spelling the `underlyingRingSheaf` abbreviations of the tree unfold to.

## Implementation notes

`f⁻¹𝒪_Y` is Mathlib's `TopCat.Sheaf.pullback`, the left adjoint of `TopCat.Sheaf.pushforward`,
so the sheaf condition comes for free as the second component of the sheaf object and there is no
sheafification argument here.  It is an `abbrev` rather than a `def` because the structure map
`AlgebraicGeometry.inverseImageStructureMap` is already stated at its unfolded spelling, and the
two are to be interchangeable.

Nothing about the structure map is reconstructed: `AlgebraicGeometry.inverseImageStructureMap` is
the adjunct of `f.c`, and `inverseImageRingCatSheafMap` is its image under `sheafCompose` of the
forgetful functor to rings, which is exactly the shape
`SheafOfModules.restrictScalars` consumes.

The target of `inverseImageRingCatSheafMap` is `AlgebraicGeometry.Scheme.ringCatSheaf`, Mathlib's
sheaf of rings of a scheme, so that the category of `𝒪_X`-modules it restricts from is
`AlgebraicGeometry.Scheme.Modules`.  That spelling and the `ringSheaf` of the Zariski ringed site
of `X` have the same underlying presheaf and a `Prop`-valued sheaf condition, so they agree
however the sheaf condition was produced and no bridge isomorphism is needed; the same
observation is recorded for the other ringed-site structure of the tree as
`Stacks.CategoryTheory.RingedSite.ringSheaf_ofScheme`.

The sheaf of rings is called `inverseImageRingCatSheaf`, after
`AlgebraicGeometry.Scheme.ringCatSheaf`, because the name `inverseImageRingSheaf` is taken in this
namespace: `StacksFrontier/AlgebraicGeometry/AffineDifferentialsIso/DeRhamComplexSections.lean`
declares it as an `abbrev` for the `CommRingCat`-valued `f⁻¹𝒪_Y`, which is the same term as
`inverseImageStructureSheaf` below.  That abbreviation is therefore now redundant, and retiring it
in favour of `inverseImageStructureSheaf` is a separate dedup step, not taken here.

The ringed site uses `AlgebraicGeometry.RingedSite`, in which the objects of the site, its
morphisms and the sections of the structure sheaf have independent universes; for the Zariski
site of a scheme in `Scheme.{u}` all three are `u`.  The companion ringed site carrying `𝒪_X`
itself is `Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite`.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The inverse image `f⁻¹𝒪_Y` of the structure sheaf of the target of a morphism of schemes
`f : X ⟶ Y`, a sheaf of commutative rings on `X`. -/
abbrev inverseImageStructureSheaf : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf

/-- `f⁻¹𝒪_Y` is the structure sheaf of the inverse-image ringed space of `f`. -/
theorem inverseImageStructureSheaf_eq :
    inverseImageStructureSheaf f = (RingedSpace.inverseImage Y.toRingedSpace f.base).sheaf :=
  rfl

/-- The structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` corresponds to `f^♯ : 𝒪_Y ⟶ f_*𝒪_X` under the
inverse-image/direct-image adjunction. -/
theorem homEquiv_inverseImageStructureMap :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv
      Y.sheaf X.sheaf (inverseImageStructureMap f) = ⟨f.c⟩ :=
  Equiv.apply_symm_apply _ _

/-- The **inverse-image ringed site** `(X, f⁻¹𝒪_Y)` of a morphism of schemes `f : X ⟶ Y`: the
Zariski site of `X`, equipped with the inverse image of the structure sheaf of `Y`. -/
abbrev inverseImageRingedSite : RingedSite.{u, u, u} where
  C := X.Opens
  J := Opens.grothendieckTopology X
  O := inverseImageStructureSheaf f

/-- `f⁻¹𝒪_Y` with commutativity forgotten: the sheaf of rings over which sheaves of
`f⁻¹𝒪_Y`-modules on the Zariski site of `X` are indexed. -/
abbrev inverseImageRingCatSheaf : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite f).O)

/-- The sheaf of rings of the inverse-image ringed site is `f⁻¹𝒪_Y` composed with the forgetful
functor to rings.  Both sides have that composite as their presheaf and a `Prop`-valued sheaf
condition, so they agree whichever `CategoryTheory.GrothendieckTopology.HasSheafCompose` instance
each found. -/
theorem inverseImageRingCatSheaf_eq :
    inverseImageRingCatSheaf f =
      (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (inverseImageStructureSheaf f) :=
  rfl

/-- The structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of a morphism of schemes, as a homomorphism of sheaves of
rings.  Restriction of scalars along it reads an `𝒪_X`-module as an `f⁻¹𝒪_Y`-module. -/
def inverseImageRingCatSheafMap : inverseImageRingCatSheaf f ⟶ X.ringCatSheaf :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map (inverseImageStructureMap f)

/-- The structure sheaf of the inverse-image ringed site of `f` is the structure sheaf of the
inverse-image ringed space of `f`. -/
theorem inverseImageRingedSite_O :
    (inverseImageRingedSite f).O = (RingedSpace.inverseImage Y.toRingedSpace f.base).sheaf :=
  rfl

end AlgebraicGeometry.Scheme.Hom

end
