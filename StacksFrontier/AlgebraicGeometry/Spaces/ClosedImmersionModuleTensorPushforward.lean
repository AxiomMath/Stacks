module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardTensorMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The canonical map `𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)` for a closed immersion of algebraic spaces

Let `S` be a scheme and `i : Z ⟶ X` a morphism of algebraic spaces over `S`. Let `𝒜` be a sheaf
of rings on `X_étale`, `ℬ` a sheaf of rings on `Z_étale`, and `φ : 𝒜 ⟶ i_{small,*}ℬ` a
homomorphism of sheaves of rings; these data are a morphism of ringed topoi

`f : (Sh(Z_étale), ℬ) ⟶ (Sh(X_étale), 𝒜)`

whose underlying morphism of topoi is that of Stacks 03G2, part (3). Stacks 04G0 states that for
a sheaf of `𝒜`-modules `𝓕` and a sheaf of `ℬ`-modules `𝓖` the canonical map

`𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)`

is an isomorphism when `i` is a closed immersion.

This file builds the morphism of ringed topoi and that canonical map, and reduces its
invertibility to the two adjunction conditions of
`Stacks.SheafOfModules.isIso_pushforwardTensorMap`. The canonical map is the adjoint transpose of
the comparison of Stacks 03EL followed by the counit of `f^* ⊣ f_*` in the second tensor factor,
which is the map the source's proof describes.

It then discharges the first of those conditions, invertibility of the counit, from the
closed-immersion hypothesis on `i` alone: it is full faithfulness of the direct image of modules,
which is the full-faithfulness half of Stacks 08M3 fed with part (1) of Stacks 04E5 and local
surjectivity of `φ`. Stacks 04G0 itself is
`AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isClosedImmersion` in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionTensorPushforwardIso.lean`, which splits the
canonical map differently and needs neither the unit condition nor any hypothesis on `φ`.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleRingedToposOfRings`: the small étale topos of an algebraic
  space, made a ringed topos by an arbitrary sheaf of commutative rings on its small étale site.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHomOfSharp`: the morphism of ringed topoi `f`
  determined by `i`, `𝒜`, `ℬ` and `φ`.
* `AlgebraicGeometry.Space.tensorPushforwardMap`: the canonical map of Stacks 04G0.
* `AlgebraicGeometry.Space.ringedToposHomOfSharp`: the same morphism of ringed topoi as the
  two-field datum of Stacks 01D3, part (2), which is the form the Stacks 08M3 results are stated
  for.
* `AlgebraicGeometry.Space.fullyFaithfulPushforwardModulesOfSharp`: the direct image of sheaves of
  modules along `f` is fully faithful when `i` is a closed immersion and `φ` is locally
  surjective.

## Main results

* `AlgebraicGeometry.Space.isIso_tensorPushforwardMap`: the canonical map is an isomorphism once
  the counit of the adjunction of Stacks 03D7 is invertible at `𝓖` and its unit is invertible at
  `𝓕 ⊗_𝒜 f_*𝓖`.
* `AlgebraicGeometry.Space.isIso_counit_of_isClosedImmersion`: the counit of the adjunction of
  Stacks 03D7 is invertible at every sheaf of `ℬ`-modules.

## Implementation notes

The sheaves of rings are `CommRingCat`-valued, which is the convention of
`AlgebraicGeometry.RingedTopos` and the one under which `𝓕 ⊗_𝒜 f_*𝓖` is again a sheaf of
`𝒜`-modules. Their sections live in `Type u`, the universe of the structure rings of the small
étale ringed topos of Stacks 03G8 and the universe at which the morphism of small étale topoi of
Stacks 03G2, part (3) is available (`AlgebraicGeometry.Space.smallToposMorphismTypeU`); the whole
module development of this tree runs at that universe, for the reason recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/Spaces/ModuleDirectImage.lean`.

The construction of the canonical map needs no hypothesis on `i`, exactly as the
projection-formula map of Stacks 0FZE exists for any morphism of ringed spaces. The
closed-immersion hypothesis is what makes it invertible, through the two conditions of
`AlgebraicGeometry.Space.isIso_tensorPushforwardMap`. For a closed immersion the counit is
invertible as soon as the direct image of modules is fully faithful, which
`Stacks.ToposBridge.fullyFaithfulPushforwardModules` gives from Stacks 04E5, part (1) (available
as `AlgebraicGeometry.Space.fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion`) together with
local surjectivity of `φ`; and the unit is invertible exactly where its source lies in the
essential image of the direct image of modules, which
`Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff_of_isClosedImmersion`
(Stacks 08M3) computes — but only from `MorphismOfTopoi.IsClosedImmersion` for the morphism of
topoi. That hypothesis is available in this tree only for a closed immersion of ringed *spaces*
(`Stacks.ClosedSubtopos.isClosedImmersion_morphismOfTopoi`), its closed-subtopos clause
(Stacks 08M0) being unproved for `AlgebraicGeometry.Space.smallToposMorphismTypeU`; equivalently,
the essential-image half of Stacks 04E5 for algebraic spaces is missing, as
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionChartBaseChangeDense.lean` records. This
file therefore leaves the unit condition open; Stacks 04G0 is proved by another route in
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionTensorPushforwardIso.lean`.

The two sheaves of rings and the two forms of the structure map are what makes the passage to
`AlgebraicGeometry.Space.ringedToposHomOfSharp` necessary: the Stacks 08M3 results are stated for
the two-field morphism of ringed topoi of Stacks 01D3, part (2) and the direct image of modules
built from the direct-image form `φ` of the structure map, whereas the adjunction of Stacks 03D7
is built over the four-field datum, whose direct image restricts scalars along the inverse-image
form first. `AlgebraicGeometry.RingedToposHom.pushforwardModulesIso` compares the two, and
`smallEtaleRingedToposHomOfSharp` is the four-field form of `ringedToposHomOfSharp` on the nose,
so no further comparison is needed. Local surjectivity is taken at the level of sheaves of
*commutative* rings, which is the level at which `φ` is given;
`Stacks.SheafOfModules.isLocallySurjective_structureRingMap` transfers it to the sheaves of rings
that the bridge consumes.

The source's own proof is stalkwise instead, and the entry point of that route is available:
`AlgebraicGeometry.Space.geometricModuleStalkFunctor` is the stalk functor on sheaves of
modules over an arbitrary sheaf of rings at a geometric point, and
`AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk` says that those stalks detect
isomorphisms of sheaves of modules, so invertibility of the canonical map reduces to
invertibility of its stalks — that reduction is
`AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isIso_geometricModuleStalk`.

The identification of the stalk of a tensor product of sheaves of modules on a small étale site
is available too, as `AlgebraicGeometry.Space.geometricModuleStalkTensorIso`.
The `[Category.{u} C]` on
`Stacks.SheafOfModules.SitePointStalkSheafify.tensorSheafifyIso` was not an obstruction but
only how that statement happens to be written: both of its inputs — part (3) of Stacks 04EQ
(`Stacks.isIso_moduleFiberSheafificationComparison`) and the presheaf-level comparison
(`Stacks.moduleFiberTensorIso`) — are proved under `[Category.{v} C] [LocallySmall.{w} C]` with
the universe of the sections free, so their composite holds at the universes of a small étale
site. `Stacks.tensorSheafModuleFiberIso` is that composite.

What the stalkwise route still lacks are the two *other* stalk computations, both for sheaves of
modules over an arbitrary sheaf of rings. The stalk of a direct image along a finite morphism is
Stacks 0DK3, whose comparison map is `AlgebraicGeometry.Space.stalkPushforwardToProduct` and
whose bijectivity is unproved even for sheaves of sets, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FiniteStalkPushforward.lean` record. The stalk of an
inverse image is part (4) of Stacks 04K2, available for sheaves of sets as
`AlgebraicGeometry.Space.smallEtaleInverseImageStalkIso` and for sheaves of abelian groups along
a *representable* morphism as `AlgebraicGeometry.Space.smallEtaleAbelianInverseImageStalkIso`,
but not for sheaves of modules: the general-site statement
`Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.stalkFunctorIso` (Stacks 05V5)
needs a functor between the two sites, which a morphism of algebraic spaces does not supply
unless it is representable.

## References

* [Stacks Project, Tag 04G0](https://stacks.math.columbia.edu/tag/04G0)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 08M0](https://stacks.math.columbia.edu/tag/08M0)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 0DK3](https://stacks.math.columbia.edu/tag/0DK3)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The small étale topos of an algebraic space, made into a ringed topos by an arbitrary sheaf
of commutative rings on its small étale site. `smallEtaleRingedTopos` is the case of the
structure sheaf; Stacks 04G0 needs the general one, its two sheaves of rings being arbitrary. -/
noncomputable abbrev smallEtaleRingedToposOfRings (X : AlgebraicSpaces B S hS)
    (𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) : RingedTopos.{u, u + 1, u} :=
  { C := SmallEtale B S hS X.1
    J := SmallEtale.topology B S hS X.1
    O := 𝒜 }

variable {Z X : AlgebraicSpaces B S hS}

/-- **The morphism of ringed topoi of Stacks 04G0**, `f : (Sh(Z_étale), ℬ) ⟶ (Sh(X_étale), 𝒜)`:
its underlying morphism of topoi is that of Stacks 03G2, part (3), and its structure map is `φ`.

No hypothesis on `i` enters, so this is equally the morphism of ringed topoi of Stacks 0DK4,
whose datum is the same `(i, φ)` in the same direction, with `i` finite instead of a closed
immersion. -/
@[stacks 04G0 "the morphism of ringed topoi determined by `i`, `𝒜`, `ℬ` and `φ`",
  stacks 0DK4 "the morphism of ringed topoi determined by `π`, `𝒜`, `ℬ` and `φ`"]
noncomputable def smallEtaleRingedToposHomOfSharp (i : Z ⟶ X)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ) :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (smallEtaleRingedToposOfRings B S hS Z ℬ) (smallEtaleRingedToposOfRings B S hS X 𝒜) :=
  (show AlgebraicGeometry.RingedToposHom (smallEtaleRingedToposOfRings B S hS Z ℬ)
        (smallEtaleRingedToposOfRings B S hS X 𝒜) from
      { toToposHom := smallToposMorphismTypeU B S hS i
        fSharp := φ }).toRingedToposModulesHom

/-- **The canonical map of Stacks 04G0**, `𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)`: the adjoint
transpose of `f^*(𝓕 ⊗_𝒜 f_*𝓖) = f^*𝓕 ⊗_ℬ f^*f_*𝓖 ⟶ f^*𝓕 ⊗_ℬ 𝓖`, built from the identity of
`f^*𝓕` and the adjunction map `f^*f_*𝓖 ⟶ 𝓖`.

No hypothesis on `i` enters, so this is equally the canonical map of Stacks 0DK4, which is the
adjoint transpose of the same comparison for the same datum with `i` finite. -/
@[stacks 04G0 "the canonical map `𝓕 ⊗_𝒜 f_*𝓖 ⟶ f_*(f^*𝓕 ⊗_ℬ 𝓖)`",
  stacks 0DK4 "the canonical map `𝓖 ⊗_ℬ f_*𝓕 ⟶ f_*(f^*𝓖 ⊗_𝒜 𝓕)`"]
noncomputable def tensorPushforwardMap (i : Z ⟶ X)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ)
    (𝓕 : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedToposOfRings B S hS X 𝒜).O))
    (𝓖 : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedToposOfRings B S hS Z ℬ).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜).obj 𝓕).obj
      ((pushforwardModules (smallEtaleRingedToposHomOfSharp B S hS i φ)).obj 𝓖) ⟶
      (pushforwardModules (smallEtaleRingedToposHomOfSharp B S hS i φ)).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} ℬ).obj
          (((smallEtaleRingedToposHomOfSharp B S hS i φ).pullbackModules).obj 𝓕)).obj 𝓖) :=
  Stacks.SheafOfModules.pushforwardTensorMap (smallEtaleRingedToposHomOfSharp B S hS i φ) 𝓕 𝓖

/-- **Stacks 04G0, the invertibility clause**, reduced to the adjunction of Stacks 03D7: the
canonical map is an isomorphism once the counit of `f^* ⊣ f_*` is invertible at `𝓖` and its unit
is invertible at `𝓕 ⊗_𝒜 f_*𝓖`. -/
@[stacks 04G0 "invertibility, given the counit at `𝓖` and the unit at `𝓕 ⊗_𝒜 f_*𝓖`"]
theorem isIso_tensorPushforwardMap (i : Z ⟶ X)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ)
    (𝓕 : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedToposOfRings B S hS X 𝒜).O))
    (𝓖 : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedToposOfRings B S hS Z ℬ).O))
    (hε : IsIso ((pullbackAdjPushforwardModules
      (smallEtaleRingedToposHomOfSharp B S hS i φ)).counit.app 𝓖))
    (hη : IsIso ((pullbackAdjPushforwardModules
        (smallEtaleRingedToposHomOfSharp B S hS i φ)).unit.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} 𝒜).obj 𝓕).obj
        ((pushforwardModules (smallEtaleRingedToposHomOfSharp B S hS i φ)).obj 𝓖)))) :
    IsIso (tensorPushforwardMap B S hS i φ 𝓕 𝓖) :=
  Stacks.SheafOfModules.isIso_pushforwardTensorMap
    (smallEtaleRingedToposHomOfSharp B S hS i φ) 𝓕 𝓖 hε hη

/-- The morphism of ringed topoi of Stacks 01D3, part (2) determined by `i`, `𝒜`, `ℬ` and `φ`:
its underlying morphism of topoi is that of Stacks 03G2, part (3) and its structure map is `φ`.
`AlgebraicGeometry.Space.smallEtaleRingedToposHomOfSharp` is its four-field form. -/
def ringedToposHomOfSharp (i : Z ⟶ X)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ) :
    _root_.AlgebraicGeometry.RingedToposHom (smallEtaleRingedToposOfRings B S hS Z ℬ)
      (smallEtaleRingedToposOfRings B S hS X 𝒜) where
  toToposHom := smallToposMorphismTypeU B S hS i
  fSharp := φ

/-- **Stacks 08M3 at the morphism of ringed topoi of Stacks 04G0**: the direct image of sheaves
of modules along `f` is fully faithful when `i` is a closed immersion and `φ` is locally
surjective.

The two inputs of `Stacks.SheafOfModules.fullyFaithfulPushforwardModulesOfIsEmbedding` are part
(1) of Stacks 04E5, which makes the direct image on sheaves of sets fully faithful, and the
hypothesis on `φ`. -/
def fullyFaithfulPushforwardModulesOfSharp (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ)
    (hφ : Sheaf.IsLocallySurjective φ) :
    (pushforwardModules (smallEtaleRingedToposHomOfSharp B S hS i φ)).FullyFaithful :=
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i hi
  Stacks.SheafOfModules.fullyFaithfulPushforwardModulesOfIsEmbedding
    (ringedToposHomOfSharp B S hS i φ) ⟨hff.full, hff.faithful⟩ hφ

/-- **The counit hypothesis of Stacks 04G0 is dischargeable at a closed immersion.** For a closed
immersion `i` and a locally surjective `φ`, the counit `f^*f_*𝓖 ⟶ 𝓖` of the adjunction of
Stacks 03D7 is an isomorphism for every sheaf of `ℬ`-modules `𝓖`.

The counit of an adjunction is invertible at every object exactly when the right adjoint is fully
faithful, so this is `fullyFaithfulPushforwardModulesOfSharp`. It is the argument of
`AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit` (Stacks 04CJ, part (2)) with the
structure sheaves replaced by the arbitrary `𝒜` and `ℬ` that Stacks 04G0 quantifies over. -/
theorem isIso_counit_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    {𝒜 : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {ℬ : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}}
    (φ : 𝒜 ⟶ (pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
      (smallToposMorphismTypeU B S hS i)).obj ℬ)
    (hφ : Sheaf.IsLocallySurjective φ)
    (𝓖 : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedToposOfRings B S hS Z ℬ).O)) :
    IsIso ((Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposHomOfSharp B S hS i φ)).counit.app 𝓖) :=
  have hff := fullyFaithfulPushforwardModulesOfSharp B S hS i hi φ hφ
  have := hff.full
  have := hff.faithful
  inferInstance

end AlgebraicGeometry.Space

end
