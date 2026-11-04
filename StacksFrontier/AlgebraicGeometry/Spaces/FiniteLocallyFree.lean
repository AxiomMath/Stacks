module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# Finite locally free morphisms of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is **finite locally free** when
it is affine and the direct image `f_*𝒪_X` of the structure sheaf of `X` is a finite locally
free `𝒪_Y`-module on the small étale ringed site of `Y`.  Its **rank** (or **degree**) is the
rank of that direct-image module.  This is Stacks 03ZV, and it is the definition the local
criteria of Stacks 03ZW are criteria for.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardStructureModule` is the direct image `f_*𝒪_X` of the
  structure sheaf of the source, read as an `𝒪_Y`-module.
* `AlgebraicGeometry.Space.IsFiniteLocallyFree` is finite local freeness of a morphism of
  algebraic spaces.
* `AlgebraicGeometry.Space.IsFiniteLocallyFreeOfRank` says in addition that the direct-image
  module has rank `r`.

## Main results

* `AlgebraicGeometry.Space.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree`: a morphism of
  rank `r` is finite locally free.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_iff`: the rank predicate is equivalent
  to affineness together with the rank condition on the direct-image module, so the finite
  local freeness that the predicate carries is not an independent assumption.

## Implementation notes

The structure sheaf of `X` enters as the unit module `SheafOfModules.unit` of the ring sheaf
of `AlgebraicGeometry.Space.smallEtaleRingedSite`, and the direct image is
`AlgebraicGeometry.Space.modulePushforward`, Stacks 03D6(1) for the small étale sites taken
along the structure map `f♯` of Stacks 03G8.  No choice of a morphism of ringed topoi is
involved: `AlgebraicGeometry.Space.modulePushforward` is unconditional.

Finite local freeness of the direct-image module is
`SheafOfModules.IsFiniteLocallyFreeOnSite`, the universe-flexible form of Stacks 03DL(2), and
the rank condition is `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`, the rank
clause of Stacks 0409, which asks for a covering of *every* object of the site rather than of
a final object.  Both are imposed on the small étale ringed site of `Y`.

The module universe is pinned to the universe `u` of the schemes, because
`AlgebraicGeometry.Space.modulePushforward` is: it factors through
`AlgebraicGeometry.Space.modulePushforwardOfStructureMap`, which is typed at
`AlgebraicGeometry.Space.Modules.{u, u}`.  Nothing in this file needs the module universe to be
`u`, and the definitions will generalize verbatim once the direct image does.  The rank
condition would not: `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank` takes its module
at the universe of the structure rings.

Both predicates are stated as conjunctions through `abbrev`, as the source states them, so
that a client can project to either conjunct without an unfolding lemma, and the rank
predicate retains finite local freeness of the morphism, as the phrase "in this case" of the
source requires.

## References

* [Stacks Project, Tag 03ZV](https://stacks.math.columbia.edu/tag/03ZV)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The direct image `f_*𝒪_X` of the structure sheaf of the source of `f : X ⟶ Y`, as a
module on the small étale ringed site of `Y`. -/
noncomputable abbrev pushforwardStructureModule (f : X ⟶ Y) : Modules.{u, u} B S hS Y.1 Y.2 :=
  (modulePushforward B S hS f).obj
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))

/-- **Stacks 03ZV.** A morphism of algebraic spaces is *finite locally free* when it is
affine and the direct image of the structure sheaf of its source is a finite locally free
module on the small étale ringed site of its target. -/
@[stacks 03ZV "finite locally free"]
noncomputable abbrev IsFiniteLocallyFree (f : X ⟶ Y) : Prop :=
  IsAffineHom B S hS f.hom ∧
    SheafOfModules.IsFiniteLocallyFreeOnSite (pushforwardStructureModule B S hS f)

/-- **Stacks 03ZV.** A finite locally free morphism of algebraic spaces has *rank* (or
*degree*) `r` when the direct image of the structure sheaf of its source has rank `r`. -/
@[stacks 03ZV "rank or degree"]
noncomputable abbrev IsFiniteLocallyFreeOfRank (f : X ⟶ Y) (r : ℕ) : Prop :=
  IsFiniteLocallyFree B S hS f ∧
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2)
      (pushforwardStructureModule B S hS f) r

/-- A morphism of algebraic spaces of rank `r` is finite locally free. -/
theorem IsFiniteLocallyFreeOfRank.isFiniteLocallyFree {f : X ⟶ Y} {r : ℕ}
    (h : IsFiniteLocallyFreeOfRank B S hS f r) : IsFiniteLocallyFree B S hS f :=
  h.1

/-- Having rank `r` is affineness together with the rank condition on the direct image of the
structure sheaf: the finite local freeness carried by
`AlgebraicGeometry.Space.IsFiniteLocallyFreeOfRank` already follows from the rank condition,
by `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.isFiniteLocallyFreeOnSite`. -/
theorem isFiniteLocallyFreeOfRank_iff (f : X ⟶ Y) (r : ℕ) :
    IsFiniteLocallyFreeOfRank B S hS f r ↔
      IsAffineHom B S hS f.hom ∧
        RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2)
          (pushforwardStructureModule B S hS f) r :=
  ⟨fun h => ⟨h.1.1, h.2⟩,
    fun h => ⟨⟨h.1, h.2.isFiniteLocallyFreeOnSite⟩, h.2⟩⟩

end AlgebraicGeometry.Space

end
