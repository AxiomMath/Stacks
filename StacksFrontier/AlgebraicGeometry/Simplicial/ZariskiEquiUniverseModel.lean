module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSliceSheafify
public import StacksFrontier.AlgebraicGeometry.Stacks.ColimitsOfHom

/-!
# The total Zariski site as a ringed site, and its equi-universe model

The total Zariski site of a simplicial scheme is recorded in the development only as a ringed
*topos*, `AlgebraicGeometry.SimplicialScheme.zariskiRingedTopos`, at `RingedTopos.{0, u, u}`: an
object of the site is an open subset of the scheme in one simplicial degree, so the objects lie
in `Type u`, while a morphism carries a map of simplicial degrees and a containment, so the
morphisms lie in `Type 0`.

`AlgebraicGeometry.RingedSite` has independent object, morphism and section universes, so the
site is a ringed site at `RingedSite.{u, 0, u}` with nothing to prove; that is recorded here.
What it is *not* is an endpoint of an `AlgebraicGeometry.RingedSite.Hom`, which is declared only
for `RingedSite.{u, u, w}`. Every statement of the localization theory of Stacks 03CF and 04J0
with exactness content — in particular 03CF's clause (b),
`CategoryTheory.SliceTopos.overPullbackCompSheafPullbackOverPostIso`, which is what Stacks 04J0's
square of ringed topoi is built from — is available only for a site whose objects and morphisms
lie in one universe, so none of it can be written down for the total Zariski site directly.

The passage that exists for this is the *equi-universe model* of
`Stacks.SheafOfModules.SmallModelSite`: for a ringed site whose underlying category is
essentially small in the universe of its structure sheaf, the small model of that category,
with the topology induced along the model equivalence and the direct image of the structure
sheaf, is a `RingedSite.{u, u, u}`, and the two categories of sheaves of modules are equivalent
even though their hom types lie in different universes. The total Zariski site satisfies the
hypothesis by `AlgebraicGeometry.SimplicialScheme.essentiallySmall_zariskiOpen`, and this file
instantiates the model and the equivalence at it.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.zariskiRingedSite`: the total Zariski site of a simplicial
  scheme as an `AlgebraicGeometry.RingedSite.{u, 0, u}`.
* `AlgebraicGeometry.SimplicialScheme.zariskiModelRingedSite`: its equi-universe model, an
  `AlgebraicGeometry.RingedSite.{u, u, u}` — hence an object that
  `AlgebraicGeometry.RingedSite.Hom` accepts.
* `AlgebraicGeometry.SimplicialScheme.zariskiModulesEquivModelModules`: the sheaves of
  `𝒪_X`-modules on the total Zariski site are the sheaves of modules on the model.

## Main results

* `AlgebraicGeometry.SimplicialScheme.zariskiRingedSite_ringedTopos`: the ringed site and the
  ringed topos `AlgebraicGeometry.SimplicialScheme.zariskiRingedTopos` have the same underlying
  data, by `rfl`.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
* [Stacks Project, Tag 09VL](https://stacks.math.columbia.edu/tag/09VL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SimplicialScheme

/-- **The total Zariski site of a simplicial scheme as a ringed site.** The objects lie in the
universe of the schemes and the morphisms in `Type 0`, so this is a `RingedSite.{u, 0, u}`;
`AlgebraicGeometry.RingedSite.Hom` does not accept it, which is what
`AlgebraicGeometry.SimplicialScheme.zariskiModelRingedSite` is for. -/
public noncomputable def zariskiRingedSite (X : SimplicialObject Scheme.{u}) :
    AlgebraicGeometry.RingedSite.{u, 0, u} where
  C := ZariskiOpen X
  J := zariskiTopology X
  O := structureSheaf X

/-- The ringed site and the ringed topos of the total Zariski site carry the same data. -/
public theorem zariskiRingedSite_ringedTopos (X : SimplicialObject Scheme.{u}) :
    AlgebraicGeometry.RingedSite.toRingedTopos (zariskiRingedSite X) =
      zariskiRingedTopos X :=
  rfl

/-- **The equi-universe model of the total Zariski site.** The small model of the site, with the
induced topology and the direct image of the structure sheaf: a ringed site whose objects, its
morphisms and the sections of its structure sheaf all lie in the universe of the schemes, and
therefore an endpoint that `AlgebraicGeometry.RingedSite.Hom` accepts. -/
public noncomputable abbrev zariskiModelRingedSite (X : SimplicialObject Scheme.{u}) :
    AlgebraicGeometry.RingedSite.{u, u, u} :=
  Stacks.SheafOfModules.SmallModelSite.ringedSite.{u} (zariskiTopology X) (structureSheaf X)

/-- **The sheaves of `𝒪_X`-modules on the total Zariski site are the sheaves of modules on its
equi-universe model.** Reindexing along the model equivalence, which is an equivalence of the two
categories of sheaves of modules even though their hom types lie in different universes. -/
public noncomputable def zariskiModulesEquivModelModules (X : SimplicialObject Scheme.{u}) :
    Modules X ≌
      SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (zariskiModelRingedSite X).J))
          (zariskiModelRingedSite X).O) :=
  Stacks.SheafOfModules.SmallModelSite.modulesEquivalence.{u} (zariskiTopology X)
    (structureSheaf X)

end AlgebraicGeometry.SimplicialScheme

end
