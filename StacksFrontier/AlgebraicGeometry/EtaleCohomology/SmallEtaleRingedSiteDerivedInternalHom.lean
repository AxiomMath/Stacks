module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteGrothendieck
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.RaisedDerivedInternalHom

/-!
# The derived internal Hom on the small étale ringed site of a scheme

The small étale ringed site `AlgebraicGeometry.smallEtaleRingedSite` of a scheme `S` is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`, and
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` is stated for a
`AlgebraicGeometry.RingedSite.{u, u, u}`, so the derived internal Hom `RSheafHom(-, -)` has
never been writable here: the two do not even have the same type.

`AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomBifunctor` is that bifunctor for a
`RingedSite.{c, u, u}` with essentially `u`-small underlying category, and this file reads it off
at `c = u + 1`. Every hypothesis it carries is already available at the spelling of the ringed
site: essential smallness and the two sheafification facts from
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/SmallEtaleRingedSiteInternalHom.lean`, the same
two at the raised module universe `u + 1` from essential smallness there, and the Grothendieck
abelian structure from
`AlgebraicGeometry.smallEtaleRingedSite_isGrothendieckAbelian`.

## The module universes are not equal, and should not be

`AlgebraicGeometry.SmallEtale.derivedSheafHomBifunctor` is a bifunctor

`D(Mod_u(𝒪))ᵒᵖ ⥤ D(Mod_u(𝒪)) ⥤ D(Mod_{u+1}(𝒪))`.

Its arguments are complexes of 𝒪-modules with sections in `u` and its value is a complex of
𝒪-modules with sections in `u + 1`. That is where the internal Hom complex of Stacks 0A8X
lands: its sections over `U` are maps of presheaves of modules on the slice `C/U`, a family
indexed by the objects of that slice, and the objects of the small étale site lie in
`Type (u + 1)`.

The undescended internal Hom of two module sheaves has the same feature, and
`AlgebraicGeometry.SmallEtale.internalHomSheaf` descends it to `SheafOfModules.{u}` by shrinking
its sections, which are `u`-small by
`AlgebraicGeometry.RingedSite.small_internalHomSheaf_obj`. No such descent is performed here.
Doing it for a complex, and then identifying the derived functors of the two, is a separate
construction; see the implementation notes.

## Main definitions

* `AlgebraicGeometry.SmallEtale.derivedSheafHomBifunctor`: **the derived internal Hom
  `RSheafHom(-, -)` on the small étale ringed site of `S`.**
* `AlgebraicGeometry.SmallEtale.derivedSheafHom`: its value on a pair of objects, which is the
  term `RSheafHom(E, F)`.

## Main results

* `AlgebraicGeometry.SmallEtale.derivedSheafHomResolutionComparison`: the derived internal Hom of
  the classes of complexes `K` and `M` is the class of the internal Hom complex from `K` into the
  chosen K-injective resolution of `M`, so this bifunctor computes what it should.
* `AlgebraicGeometry.SmallEtale.derivedSheafHomResolutionComparison` above; the two derived
  categories the bifunctor needs are inhabited by
  `AlgebraicGeometry.SmallEtale.hasDerivedCategory_sheafOfModules` and
  `AlgebraicGeometry.SmallEtale.hasDerivedCategory_sheafOfModules_raised`, at `u + 1` and at
  `u + 2` respectively. Those are `def`s rather than theorems because
  `CategoryTheory.HasDerivedCategory` is data.

## Implementation notes

The two `HasDerivedCategory` arguments are hypotheses, as they are in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedInternalHom.lean`,
because `CategoryTheory.HasDerivedCategory` is data: declaring either as an instance would give
instance search a second route to a structure.  Their localization universes are *different* —
`u + 1` for the module sheaves with sections in `u` and `u + 2` for those with sections in
`u + 1` — which is why
`AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomBifunctor` carries two of them rather
than one. `AlgebraicGeometry.SmallEtale.hasDerivedCategory_sheafOfModules` and its `_raised`
companion record that both are inhabited, by `CategoryTheory.HasDerivedCategory.standard`.

What is *not* done here is to descend the value back to `SheafOfModules.{u}`. The undescended
and descended internal Homs of two module sheaves are identified by
`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso`, but that is an identification of
single sheaves. To descend `AlgebraicGeometry.SmallEtale.derivedSheafHomBifunctor` one needs the
internal Hom *complex* to be shrinkable degreewise, which asks for the sections of each term
`AlgebraicGeometry.RingedSite.sheafHomTerm` — a product over the pairs `p + n = q` of internal
Homs — to be `u`-small, and then a comparison of the two derived bifunctors. Neither is
available.

## References

* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 0A8X](https://stacks.math.columbia.edu/tag/0A8X)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SmallEtale

/-! ### The two derived categories exist -/

/-- The complexes of sheaves of `𝒪`-modules with sections in the universe of the schemes on the
small étale ringed site of `S` have a derived category, with morphisms in `u + 1`.

This is not declared as an instance: `CategoryTheory.HasDerivedCategory` is data, so a second
route to it would give instance search two incompatible structures. -/
@[instance_reducible]
public def hasDerivedCategory_sheafOfModules :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :=
  HasDerivedCategory.standard _

/-- The complexes of sheaves of `𝒪`-modules with sections in `u + 1` — the universe in which the
internal Hom complex of Stacks 0A8X lands on this site — have a derived category, with morphisms
in `u + 2`. -/
@[instance_reducible]
public def hasDerivedCategory_sheafOfModules_raised :
    HasDerivedCategory.{u + 2}
      (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :=
  HasDerivedCategory.standard _

/-! ### The derived internal Hom -/

variable [HasDerivedCategory.{u + 1}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))]
  [HasDerivedCategory.{u + 2}
    (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))]

/-- **The derived internal Hom `RSheafHom(-, -)` on the small étale ringed site of `S`**,
contravariant in its source.

Its arguments are objects of the derived category of the sheaves of `𝒪`-modules with sections in
the universe of the schemes, and its values lie in the derived category of those with sections in
`u + 1`, which is where the internal Hom complex of Stacks 0A8X lands on a site whose objects
form a type in `Type (u + 1)`.

This is `AlgebraicGeometry.RingedSite.Raised.mixedDerivedSheafHomBifunctor` of the small étale
ringed site; at a ringed site whose three universes coincide that bifunctor is
`AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor`, so this is that construction and not
another one. -/
public def derivedSheafHomBifunctor :
    (DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)))ᵒᵖ ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ⥤
        DerivedCategory (SheafOfModules.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :=
  RingedSite.Raised.mixedDerivedSheafHomBifunctor (smallEtaleRingedSite B S hS)

/-- **`RSheafHom(E, F)` on the small étale ringed site of `S`**: the value of the derived
internal Hom on a pair of objects of the derived category. -/
public abbrev derivedSheafHom
    (E F : DerivedCategory (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O))) :
    DerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :=
  ((derivedSheafHomBifunctor B S hS).obj (op E)).obj F

/-- **The derived internal Hom computes the internal Hom complex of a K-injective resolution.**
For arbitrary complexes `K` and `M` of sheaves of `𝒪`-modules with sections in the universe of
the schemes, `RSheafHom` of their classes is the class of the internal Hom complex from `K` into
the chosen K-injective resolution of `M`. -/
public def derivedSheafHomResolutionComparison
    (K M : CochainComplex
      (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) ℤ) :
    derivedSheafHom B S hS (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M) ≅
      DerivedCategory.Q.obj
        (RingedSite.sheafHomComplex (smallEtaleRingedSite B S hS) K
          ((Stacks.Injectives.kInjectiveResolutionFunctor
            (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf
                (smallEtaleRingedSite B S hS).O))).obj M)).obj :=
  RingedSite.Raised.mixedDerivedSheafHomResolutionComparison
    (smallEtaleRingedSite B S hS) K M

end SmallEtale

end AlgebraicGeometry

end
