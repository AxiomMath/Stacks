module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# The internal Hom of modules on the small étale ringed site of a scheme

The small étale ringed site `AlgebraicGeometry.smallEtaleRingedSite` of a scheme `S` is a
`AlgebraicGeometry.RingedSite.{u + 1, u, u}`: its objects lie in `Type (u + 1)` and its
morphisms in `Type u`.  Two things therefore look unavailable on it.  Sheafification of
presheaves of abelian groups with sections in `u` is not available from the general theory,
because the presheaf category only has colimits of size `u + 1`.  And
`AlgebraicGeometry.RingedSite.internalHomSheaf` of two `SheafOfModules.{u}` lands in
`SheafOfModules.{max (u + 1) u u}`, that is in `SheafOfModules.{u + 1}`, so the internal Hom is
not an endofunctor of the `𝒪`-modules.

Both are artefacts of the spelling and not of the mathematics.  The small étale site is
essentially small at `u` (`AlgebraicGeometry.SmallEtale.essentiallySmall`), which already gives
sheafification there (`AlgebraicGeometry.SmallEtale.hasSheafify`), and on an essentially small
ringed site the internal Hom descends to the module universe
(`AlgebraicGeometry.RingedSite.internalHomSheafSmall`).  What is missing is only that
`AlgebraicGeometry.smallEtaleRingedSite` is a `def`, so instance search does not unfold its `C`
and `J` projections and none of the available instances fire at a goal phrased in terms of the
ringed site.  This file restates them at that spelling and reads off the internal Hom.

## Main definitions

* `AlgebraicGeometry.SmallEtale.internalHomSheaf` is the internal Hom of two sheaves of
  `𝒪`-modules with sections in `u` on the small étale ringed site of `S`, **again as a sheaf of
  `𝒪`-modules with sections in `u`**.
* `AlgebraicGeometry.SmallEtale.internalHomSheafFunctor` is it as a functor in the second
  variable, hence an endofunctor of those module sheaves.
* `AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso` identifies the universe lift of
  `AlgebraicGeometry.SmallEtale.internalHomSheaf` with
  `AlgebraicGeometry.RingedSite.internalHomSheaf`, so nothing is lost: this is that internal Hom,
  read in the smaller universe.

## Main results

* `AlgebraicGeometry.smallEtaleRingedSite_essentiallySmall`,
  `AlgebraicGeometry.smallEtaleRingedSite_hasSheafify` and
  `AlgebraicGeometry.smallEtaleRingedSite_wEqualsLocallyBijective` restate essential smallness
  and the two sheafification facts for the projections of the ringed site, and
  `AlgebraicGeometry.smallEtaleRingedSite_hasSheafify_over` and
  `AlgebraicGeometry.smallEtaleRingedSite_wEqualsLocallyBijective_over` do the same on every
  slice, which is the form the sheaves-of-modules API consumes.

## Implementation notes

The three instances are `change` followed by `infer_instance`, exactly as
`AlgebraicGeometry.Space.smallEtaleRingedSite_hasWeakSheafify_over` is for the small étale ringed
site of an algebraic space.  Each of the three classes is a `Prop`, so a second route to the same
goal cannot produce incompatible data; and since the proofs take no instance argument of their own
class, they cannot enter a loop.

The abelian structure on the module sheaves is *not* restated as an instance.
`SheafOfModules.instAbelian` fires on its own once the two sheafification instances are available,
and `CategoryTheory.Abelian` is data rather than a `Prop`, so a second declaration would give
instance search two routes to two structures.  Kernels and cokernels of these module sheaves
then come from that abelian structure by instance search, with no lemma of their own.

The universe lift appearing in `AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso` is
`Stacks.SheafOfModules.moduleULift.{u + 1}`, the join `max (u + 1) u` of the two site universes at
which `AlgebraicGeometry.RingedSite.internalHomSheafSmallIso` is stated.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04HZ](https://stacks.math.columbia.edu/tag/04HZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Essential smallness and sheafification at the spelling of the ringed site -/

/-- The underlying category of the small étale ringed site of `S` is essentially small at the
universe of the schemes.

The content is `AlgebraicGeometry.SmallEtale.essentiallySmall`; this restates it for the
projection of `AlgebraicGeometry.smallEtaleRingedSite`, which instance search does not unfold. -/
public instance smallEtaleRingedSite_essentiallySmall :
    EssentiallySmall.{u} (smallEtaleRingedSite B S hS).C := by
  change EssentiallySmall.{u} (SmallEtale B S hS)
  infer_instance

/-- Presheaves of abelian groups with sections in the universe of the schemes sheafify on the
small étale ringed site of `S`.

The content is `AlgebraicGeometry.SmallEtale.hasSheafify`; this restates it for the projections of
`AlgebraicGeometry.smallEtaleRingedSite`, which instance search does not unfold. -/
public instance smallEtaleRingedSite_hasSheafify :
    HasSheafify (smallEtaleRingedSite B S hS).J AddCommGrpCat.{u} := by
  change HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u}
  infer_instance

/-- On the small étale ringed site of `S`, the morphisms of presheaves of abelian groups with
sections in the universe of the schemes which sheafification inverts are exactly the locally
bijective ones.

The content is `AlgebraicGeometry.SmallEtale.wEqualsLocallyBijective`; this restates it for the
projections of `AlgebraicGeometry.smallEtaleRingedSite`, which instance search does not
unfold. -/
public instance smallEtaleRingedSite_wEqualsLocallyBijective :
    (smallEtaleRingedSite B S hS).J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  change (SmallEtale.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

/-- Presheaves of abelian groups with sections in the universe of the schemes sheafify on every
slice of the small étale ringed site of `S`, in the `∀`-quantified form that the
sheaves-of-modules API consumes.

A slice of an essentially small category is essentially small
(`Stacks.essentiallySmall_over`), so this is again
`CategoryTheory.hasSheafifyEssentiallySmallSite`. -/
public instance smallEtaleRingedSite_hasSheafify_over :
    ∀ U : (smallEtaleRingedSite B S hS).C,
      HasSheafify ((smallEtaleRingedSite B S hS).J.over U) AddCommGrpCat.{u} := by
  change ∀ U : SmallEtale B S hS,
    HasSheafify ((SmallEtale.topology B S hS).over U) AddCommGrpCat.{u}
  intro U
  have : EssentiallySmall.{u} (Over U) := Stacks.essentiallySmall_over.{u} U
  exact hasSheafifyEssentiallySmallSite.{u} _ _

/-- On every slice of the small étale ringed site of `S`, the morphisms of presheaves of abelian
groups with sections in the universe of the schemes which sheafification inverts are exactly the
locally bijective ones, in the `∀`-quantified form that the sheaves-of-modules API consumes. -/
public instance smallEtaleRingedSite_wEqualsLocallyBijective_over :
    ∀ U : (smallEtaleRingedSite B S hS).C,
      ((smallEtaleRingedSite B S hS).J.over U).WEqualsLocallyBijective AddCommGrpCat.{u} := by
  change ∀ U : SmallEtale B S hS,
    ((SmallEtale.topology B S hS).over U).WEqualsLocallyBijective AddCommGrpCat.{u}
  intro U
  have : EssentiallySmall.{u} (Over U) := Stacks.essentiallySmall_over.{u} U
  exact .ofEssentiallySmall.{u} _

namespace SmallEtale

/-! ### The internal Hom as an endofunctor -/

/-- **The internal Hom of two sheaves of `𝒪`-modules with sections in the universe of the schemes
on the small étale ringed site of `S`, again as a sheaf of `𝒪`-modules with sections in that
universe.**

Its universe lift is `AlgebraicGeometry.RingedSite.internalHomSheaf`
(`AlgebraicGeometry.SmallEtale.moduleULiftInternalHomSheafIso`), so this is that internal Hom and
not another construction; what is new is that it does not leave the module universe. -/
public def internalHomSheaf
    (A M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O) :=
  RingedSite.internalHomSheafSmall (smallEtaleRingedSite B S hS) A M

/-- **The internal Hom on the small étale ringed site of `S` is an endofunctor of the sheaves of
`𝒪`-modules with sections in the universe of the schemes**: the internal Hom out of a fixed `A` is
functorial in its second variable. -/
public def internalHomSheafFunctor
    (A : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O) :=
  RingedSite.internalHomSheafSmallFunctor (smallEtaleRingedSite B S hS) A

/-- The internal Hom of `AlgebraicGeometry.SmallEtale.internalHomSheaf` is the internal Hom of
`AlgebraicGeometry.RingedSite.internalHomSheaf`: the universe lift of the former is isomorphic to
the latter. -/
public def moduleULiftInternalHomSheafIso
    (A M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)) :
    (Stacks.SheafOfModules.moduleULift.{u + 1}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O)).obj
        (internalHomSheaf B S hS A M) ≅
      RingedSite.internalHomSheaf (smallEtaleRingedSite B S hS) A M :=
  RingedSite.internalHomSheafSmallIso (smallEtaleRingedSite B S hS) A M

end SmallEtale

end AlgebraicGeometry

end
