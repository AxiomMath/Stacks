module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceTargetValues

/-!
# The conormal ideal as a square-zero ideal of the structure sheaf of the ambient space

Let `Z ⊂ X` be a first order thickening of algebraic spaces over a scheme `S`, presented as a
closed subspace, with inclusion `i : Z ⟶ X`.  The conormal module `𝒞_{Z/X}` is available as a
square-zero ideal of `i^{-1}𝒪_X` on the small étale site of the *closed subspace* `Z`
(`AlgebraicGeometry.Space.conormalSquareZeroValues`), and that is the wrong pair for the
consumers: the structure map of a morphism of ringed topoi out of `(Sh(X_étale), 𝒪_X)` can only
be perturbed by an ideal of `𝒪_X` on the site of `X`.

This file carries the datum over.  The passage is in two steps, neither of which is new
mathematics:

* the direct image along `i` of the ideal of values, which is
  `AlgebraicGeometry.Space.squareZeroValuesAt` at the target space `T = X` and the morphism
  `e = i` — nothing in that construction asks `T` to be a closed subspace, so no new transport
  across the two sites is needed, and its ambient sheaf of rings is `i_*i^{-1}𝒪_X`;
* the identification `𝒪_X ≅ i_*i^{-1}𝒪_X`, which is the structure-sheaf half of
  [Stacks Project, Tag 05ZM] at the level of sheaves of rings
  (`AlgebraicGeometry.Space.isIso_thickeningRingUnit`, i.e.
  `AlgebraicGeometry.Space.isIso_ringUnit_of_isThickening` at `𝒪_X`).

The second step is what was missing: `Stacks.Sites.SquareZeroValues.ofIsoAmbient` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/LiftDifferenceSquareZeroValues.lean` reads an
ideal of values in an isomorphic ambient sheaf of rings, and this file instantiates it at the
unit.  The result is `i_*𝒞_{Z/X}` as a square-zero ideal of `𝒪_X` on the small étale site of
`X` itself.

With that in hand the end of the file states what the perturbed structure map of
[Stacks Project, Tag 04D0] needs: a morphism of the small étale ringed topoi of two algebraic
spaces whose structure map is the derivation-modified one is a morphism of *locally* ringed
topoi.

## Main definitions

* `AlgebraicGeometry.Space.conormalAmbientSquareZeroValues`: **the transported ideal of
  values** — `i_*𝒞_{Z/X}` as a square-zero ideal of `𝒪_X` on the small étale site of `X`.
* `AlgebraicGeometry.Space.conormalAmbientSourceSquareZeroValues`: the same read over the
  source sheaf of rings `𝒜` of a morphism `φ : 𝒜 ⟶ 𝒪_X`, which is what lets a derivation of
  `𝒜` itself act on `φ`.
* `AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom`: **the sum `φ + D`** of
  [Stacks Project, Tag 04D0], as a morphism of sheaves of rings `𝒜 ⟶ 𝒪_X` on the small étale
  site of `X`.
* `AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionCommHom`: the same sum read back
  on sheaves of *commutative* rings, which is where the structure map of a morphism of ringed
  topoi lives.
* `AlgebraicGeometry.Space.conormalAmbientDerivationRingedToposHom`: **the sum as a morphism of
  the small étale ringed topoi of `X` and `Y`** — the field `hom` of
  `AlgebraicGeometry.Space.DerivationModification`.

## Main results

* `AlgebraicGeometry.Space.app_thickeningRingUnit_conormalAmbientSquareZeroValues_ι`: the
  transported inclusion, pinned by the unit.
* `AlgebraicGeometry.Space.conormalAmbientSquareZeroValues_ι_smul`: **the transported inclusion
  is `𝒪_X`-linear read as multiplication in `𝒪_X`**, which is the field `ι_smul` that
  `Stacks.Sites.derivationActionHom` consumes.
* `AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom_app_apply`: the values of
  the modified morphism on sections.
* `AlgebraicGeometry.Space.exists_conormalAmbientSquareZeroValues_ι_sub_app`: the modified
  morphism differs from `φ` by a section of the transported ideal — `ι (D x)` on the nose.
* `AlgebraicGeometry.Space.isLocallyRinged_of_sub_eq_conormalAmbientSquareZeroValues_ι`:
  a structure map agreeing with a units-reflecting one modulo the transported ideal is locally
  ringed.
* `AlgebraicGeometry.Space.isLocallyRinged_of_conormalAmbientSourceDerivationActionHom`:
  **the end-to-end statement — the derivation-modified structure map on the small étale site of
  the ambient space `X` is a morphism of locally ringed topoi.**
* `AlgebraicGeometry.Space.isLocallyRinged_conormalAmbientDerivationRingedToposHom`: the same at
  the morphism of ringed topoi this file constructs, where the hypothesis that its structure map
  *is* the modified one holds by construction.
* `AlgebraicGeometry.Space.conormalAmbientDerivationRingedToposHom_eq_of_eq_zero`: modifying by
  the zero derivation returns the morphism of ringed topoi one started from, on the nose.

## Implementation notes

**Why the direct image needs no new work.**  The obstruction recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/MorphismFromStructureMap.lean` is that the
conormal ideal lives on the site of `Z`.  Half of the cure is already available:
`AlgebraicGeometry.Space.squareZeroValuesAt` transports the ideal along the direct image of an
*arbitrary* morphism `e` out of the closed subspace, and `e = i` is allowed.  What is genuinely
new is the second half, the change of ambient sheaf of rings along an isomorphism; that is
`Stacks.Sites.SquareZeroValues.ofIsoAmbient`, proved at an arbitrary site.

**The invertibility of the unit is passed by name, not synthesized.**  `IsIso` of the unit is an
explicit argument of `Stacks.Sites.SquareZeroValues.ofIsoAmbient` rather than an instance: the
ambient sheaf of rings of the datum being transported sits behind a structure projection, so the
two spellings of the unit's codomain agree only after unfolding it, and instance search — which
unifies at reducible transparency — does not find the instance at the spelling it is asked for.
This is the same precaution as the named invertibility arguments of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/ConormalModuleInverseImageKernel.lean`.

**The transported inclusion is characterised by the unit, not by its inverse.**
`CategoryTheory.inv` has no exposed body under the module system, so an equation naming the
inverse cannot be stated usably downstream; the inclusion is pinned instead by `u ∘ ι' = ι`,
which determines it since `u` is injective on sections.

**The universes of the inverse-image sheaf of rings are pinned by hand.**  The source of the
structure map of the end-to-end statement is spelled
`AlgebraicGeometry.Space.inverseImageStructureRingSheaf`, an abbreviation whose *ascribed* type
fixes the universe of its sections.  Written out as
`Stacks.SheafOfModules.Tensor.ringSheaf (g⁻¹𝒪_Y)` the section universe stays a metavariable, the
universe constraints of the hypotheses become unsolvable, and
the scalar action of the derivation's Leibniz rule is then a `(deterministic) timeout at
typeclass` — a failure whose message names instance search while its cause is the universe.

**Every statement about the transported inclusion ascribes the type of its sections.**  The
ambient sheaf of rings of the transported datum is a structure field, so the sections of the
inclusion are typed as `E.ambient.obj.obj V`; the multiplication of
`AlgebraicGeometry.Space.conormalAmbientSquareZeroValues_ι_smul` is then not elaborable, instance
search declining to unfold the projection.  Both sides are therefore ascribed to the sections of
`AlgebraicGeometry.Space.structureRingSheaf`, as in
`AlgebraicGeometry.Space.smul_app_conormalInverseImageι`.

**No `@[stacks]` attribute anywhere in this file.**  The transport carries the thickening as a
closed subspace and the first-order hypothesis, which are data Tag 05ZM does not have, and it is
a step inside the proofs of Tag 04D0 and Tag 02H5 rather than a clause of either; the
locally-ringed statement carries, beyond the hypotheses of Tag 04HA, the unperturbed structure
map with its units reflection, the derivation as an unbundled explicit family, and a
`HasPullback` instance for the units square.

## What is still not done

`AlgebraicGeometry.Space.DerivationModification` is constructed at the end of this file, its
field `hom θ` included — the modified map of sheaves of rings carried back into an
`AlgebraicGeometry.RingedToposHom`, i.e. lifted through `Stacks.forgetCommRingSheaf` and
transposed along the adjunction.
`AlgebraicGeometry.Space.conormalAmbientDerivationRingedToposHom` is that morphism of
ringed topoi, `AlgebraicGeometry.Space.isLocallyRinged_conormalAmbientDerivationRingedToposHom`
is its local ringedness with the hypothesis `hg` of the end-to-end statement discharged by
construction, and `AlgebraicGeometry.Space.conormalAmbientDerivationRingedToposHom_eq_of_eq_zero`
identifies the modification by the zero derivation with the morphism it modifies.  Neither step
is new mathematics: full faithfulness of
`Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf` gives the lift and
`AlgebraicGeometry.RingedToposHom.ofInverseImageMap` the transposition, both already available.
`AlgebraicGeometry.Space.derivationModificationOfFamily` of
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/MorphismFromStructureMap.lean` assembles them
into the datum.

What is still not done is the clauses `square`, `algebra` and `injective` of that datum, and the
derivation itself: the `D = d_{Y/T} ∘ θ` attached to a `θ` by Equation
[Stacks Project, Tag 0619] is not produced here, every statement below taking the derivation
family as given.  Equation (0619) is formalized on the small étale site of the closed subspace, and
transporting it to the site of the ambient space — a change of both the site and the source
sheaf of rings — is the missing step.

## References

* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM), the equivalence whose
  structure-sheaf half the transport is across.
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN), the conormal module.
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0), the modified structure
  map `α = (a')^♯ + D`.
* [Stacks Project, Tag 04HA](https://stacks.math.columbia.edu/tag/04HA), the units square
  criterion for a locally ringed morphism.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)
  (hZ : IsFirstOrderThickening B S hS X Z.1)

include hZ in
/-- **The conormal module of a first order thickening, as a square-zero ideal of `𝒪_X` on the
small étale site of the ambient space `X`.**  This is the datum the perturbed structure map of
[Stacks Project, Tag 04D0] reads its correction term in, and it is the transport of
`AlgebraicGeometry.Space.conormalSquareZeroValues` across the structure-sheaf half of
[Stacks Project, Tag 05ZM].

Both steps are instantiations: the direct image along `i` is
`AlgebraicGeometry.Space.squareZeroValuesAt` at the target space `X` and the morphism `i`, whose
ambient sheaf of rings is `i_*i^{-1}𝒪_X`, and the change of ambient along the unit
`𝒪_X ⟶ i_*i^{-1}𝒪_X` is `Stacks.Sites.SquareZeroValues.ofIsoAmbient`.  The unit is invertible
because `Z ⊂ X` is a thickening, by `AlgebraicGeometry.Space.isIso_thickeningRingUnit`; the
first order hypothesis is what makes the conormal module the ideal in the first place.  The
commutativity of the sections of `𝒪_X` is supplied directly rather than transported, being
already available. -/
def conormalAmbientSquareZeroValues :
    Stacks.Sites.SquareZeroValues
      ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        (conormalModule B S hS X Z)) :=
  (squareZeroValuesAt B S hS Z X (subspaceInclusion B S hS X Z) hZ).ofIsoAmbient
    (thickeningRingUnit B S hS Z) (isIso_thickeningRingUnit B S hS Z hZ.1)
    (fun {V} s t => ringSheaf_mul_comm_smallEtaleRingedSite B S hS X V s t)

/-- **The inclusion of the transported ideal of values, characterised by the unit.**  Composing
it with `𝒪_X ⟶ i_*i^{-1}𝒪_X` returns the inclusion of the ideal of values on the site of `X`
before the transport. -/
theorem app_thickeningRingUnit_conormalAmbientSquareZeroValues_ι
    {V : (SmallEtale B S hS X.1)ᵒᵖ}
    (m : ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
      (conormalModule B S hS X Z)).val.obj V) :
    (thickeningRingUnit B S hS Z).hom.app V
        ((conormalAmbientSquareZeroValues B S hS Z hZ).ι m) =
      (squareZeroValuesAt B S hS Z X (subspaceInclusion B S hS X Z) hZ).ι m :=
  Stacks.Sites.SquareZeroValues.app_ofIsoAmbient_ι
    (squareZeroValuesAt B S hS Z X (subspaceInclusion B S hS X Z) hZ)
    (thickeningRingUnit B S hS Z) (isIso_thickeningRingUnit B S hS Z hZ.1)
    (fun {V} s t => ringSheaf_mul_comm_smallEtaleRingedSite B S hS X V s t) m

/-- **The transported inclusion is linear on sections, with the scalar action read as
multiplication in `𝒪_X`.**  For a morphism of sheaves of rings `q : 𝒜 ⟶ 𝒪_X` the action of
`q x` on `i_*𝒞_{Z/X}` is carried by the inclusion to multiplication by `q x`.

The module structure of the sections is supplied by a `letI` in the statement, as it is on
`AlgebraicGeometry.Space.squareZeroValuesAt_ι_smul`, which this instantiates.  The sections of
`AlgebraicGeometry.Space.conormalModule` carried along
`AlgebraicGeometry.Space.modulePushforward` are a module over
`AlgebraicGeometry.Space.structureRingSheaf` only after both are unfolded, and instance search
declines to; naming the `ModuleCat` structure of the sections spends that step once.

This is the field `ι_smul` that `Stacks.Sites.derivationActionHom` consumes, and it is
`AlgebraicGeometry.Space.squareZeroValuesAt_ι_smul` read across the unit: there the
multiplication is by a morphism into `i_*i^{-1}𝒪_X` whose reduction is `q` followed by the
comorphism of `i`, and `q` composed with the unit is such a morphism, by
`AlgebraicGeometry.Space.thickeningRingUnit_comp_pullbackRingSheafMap`.  The unit being
injective on sections, it is enough to compare the two sides after it. -/
theorem conormalAmbientSquareZeroValues_ι_smul
    {A : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
    (q : A ⟶ structureRingSheaf B S hS X) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : A.obj.obj V)
    (m : ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
      (conormalModule B S hS X Z)).val.obj V) :
    letI : Module ((structureRingSheaf B S hS X).obj.obj V)
        (((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z)).val.obj V) :=
      (((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z)).val.obj V).isModule
    (show ToType ((structureRingSheaf B S hS X).obj.obj V) from
        (conormalAmbientSquareZeroValues B S hS Z hZ).ι (q.hom.app V x • m)) =
      (show ToType ((structureRingSheaf B S hS X).obj.obj V) from q.hom.app V x) *
        (show ToType ((structureRingSheaf B S hS X).obj.obj V) from
          (conormalAmbientSquareZeroValues B S hS Z hZ).ι m) := by
  have hF : (q ≫ thickeningRingUnit B S hS Z) ≫
        thickeningLiftReductionAt B S hS Z X (subspaceInclusion B S hS X Z) =
      q ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun n => q ≫ n) (thickeningRingUnit_comp_pullbackRingSheafMap B S hS Z))
  refine Stacks.Sites.injective_app_of_isIso (thickeningRingUnit B S hS Z)
    (isIso_thickeningRingUnit B S hS Z hZ.1) V ?_
  rw [app_thickeningRingUnit_conormalAmbientSquareZeroValues_ι,
    map_mul ((thickeningRingUnit B S hS Z).hom.app V).hom,
    app_thickeningRingUnit_conormalAmbientSquareZeroValues_ι]
  exact squareZeroValuesAt_ι_smul B S hS Z X (subspaceInclusion B S hS X Z) hZ q
    (q ≫ thickeningRingUnit B S hS Z) hF x m

/-! ### A morphism of sheaves of rings into `𝒪_X` plus a derivation of its source -/

section SourceDerivation

variable {A : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
  (φ : A ⟶ structureRingSheaf B S hS X)

/-- **The transported conormal ideal read over the source sheaf of rings `𝒜` of a morphism
`φ : 𝒜 ⟶ 𝒪_X`.**  This is `AlgebraicGeometry.Space.conormalAmbientSquareZeroValues` with one
restriction of scalars along `φ`; restriction of scalars changes neither the sections nor the
restriction maps, so the inclusion is the same.

It is what lets a derivation of `𝒜` itself act on `φ`, which is the form the modified structure
map of [Stacks Project, Tag 04D0] takes: there `D = d_{Y/T} ∘ θ` is evaluated on the sections of
the source `f^{-1}𝒪_{Y'}`, not on those of `𝒪_{X'}`. -/
def conormalAmbientSourceSquareZeroValues :
    Stacks.Sites.SquareZeroValues
      ((SheafOfModules.restrictScalars φ).obj
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z))) :=
  (conormalAmbientSquareZeroValues B S hS Z hZ).restrictScalars φ

variable (D : ∀ V : (SmallEtale B S hS X.1)ᵒᵖ, A.obj.obj V →+
      ((SheafOfModules.restrictScalars φ).obj
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z))).val.obj V)
  (hmul : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ) (s t : A.obj.obj V),
    D V (s * t) = s • D V t + t • D V s)
  (hmap : ∀ (V W : (SmallEtale B S hS X.1)ᵒᵖ) (h : V ⟶ W) (s : A.obj.obj V),
    D W (A.obj.map h s) =
      ((SheafOfModules.restrictScalars φ).obj
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z))).val.map h (D V s))

/-- **A morphism of sheaves of rings `φ : 𝒜 ⟶ 𝒪_X` plus a derivation of `𝒜` with values in the
conormal module of a first order thickening `Z ⊂ X` is again a morphism of sheaves of rings**,
on the small étale site of the **ambient** space `X`.

This is the sum `α = (a')^♯ + D` of [Stacks Project, Tag 04D0], formed on the site the structure
map of a morphism of ringed topoi out of `(Sh(X_étale), 𝒪_X)` lives on.  The companion
`AlgebraicGeometry.Space.conormalSourceDerivationActionHom` forms the same sum on the site of
the closed subspace `Z`, with `i^{-1}𝒪_X` for its ambient; the two are related by the transport
of this file, and it is this one that the consumers need.

**No multiplicativity is proved here.**  `Stacks.Sites.derivationActionHom` proves the statement
at an arbitrary site; what is added is the instantiation at the transported ideal, whose
linearity read as multiplication in `𝒪_X` is
`AlgebraicGeometry.Space.conormalAmbientSquareZeroValues_ι_smul`.  The quotient map is the
identity of `𝒜`, so the derivation is used as it stands.

The sign convention is that of `Stacks.Sites.derivationActionHom`, namely `φ − ι ∘ D`. -/
def conormalAmbientSourceDerivationActionHom : A ⟶ structureRingSheaf B S hS X :=
  Stacks.Sites.derivationActionHom (q := 𝟙 A)
    (conormalAmbientSourceSquareZeroValues B S hS Z hZ φ) φ D hmul hmap
    (fun V x m => conormalAmbientSquareZeroValues_ι_smul B S hS Z hZ φ V x m)

/-- **The value of `AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom` on
sections.**  A morphism of sheaves of rings whose type does not record its values asserts
nothing by itself; this is what pins it. -/
theorem conormalAmbientSourceDerivationActionHom_app_apply (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : A.obj.obj V) :
    (conormalAmbientSourceDerivationActionHom B S hS Z hZ φ D hmul hmap).hom.app V x =
      φ.hom.app V x -
        (show ToType ((structureRingSheaf B S hS X).obj.obj V) from
          (conormalAmbientSquareZeroValues B S hS Z hZ).ι (D V x)) :=
  rfl

/-- **A unit modulo the transported conormal ideal is a unit.**  A section of `𝒜` has invertible
image under the modified morphism exactly when it has invertible image under `φ`, the two
differing by a section of a square-zero ideal of `𝒪_X`.  This is
`Stacks.Sites.isUnit_derivationActionHom_app_apply_iff`; no new algebra is involved. -/
theorem isUnit_conormalAmbientSourceDerivationActionHom_app_apply_iff
    (V : (SmallEtale B S hS X.1)ᵒᵖ) (x : A.obj.obj V) :
    IsUnit ((conormalAmbientSourceDerivationActionHom B S hS Z hZ φ D hmul hmap).hom.app V x) ↔
      IsUnit (φ.hom.app V x) :=
  Stacks.Sites.isUnit_derivationActionHom_app_apply_iff (q := 𝟙 A)
    (conormalAmbientSourceSquareZeroValues B S hS Z hZ φ) φ D hmul hmap
    (fun W y m => conormalAmbientSquareZeroValues_ι_smul B S hS Z hZ φ W y m) V x

/-- **The modified morphism differs from `φ` by a section of the transported conormal
ideal.**  The difference is `ι (D x)` on the nose, by the sign convention of
`Stacks.Sites.derivationActionHom`. -/
theorem exists_conormalAmbientSquareZeroValues_ι_sub_app
    (V : (SmallEtale B S hS X.1)ᵒᵖ) (x : A.obj.obj V) :
    ∃ m : ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
        (conormalModule B S hS X Z)).val.obj V,
      φ.hom.app V x -
          (conormalAmbientSourceDerivationActionHom B S hS Z hZ φ D hmul hmap).hom.app V x =
        (conormalAmbientSquareZeroValues B S hS Z hZ).ι m :=
  ⟨D V x, by
    rw [conormalAmbientSourceDerivationActionHom_app_apply, sub_sub_cancel]⟩

end SourceDerivation

/-! ### The derivation-modified structure map is locally ringed -/

section LocallyRinged

variable {Y : AlgebraicSpaces B S hS}

/-- **A structure map agreeing with a units-reflecting one modulo the transported conormal ideal
is locally ringed.**

Let `Z ⊂ X` be a first order thickening of algebraic spaces, let
`g : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of small étale ringed topoi and let
`φ : g^{-1}𝒪_Y ⟶ 𝒪_X` be a second structure map which reflects units at every geometric point
of `X`.  If on every section the two differ by a section of `i_*𝒞_{Z/X}`, read as an ideal of
`𝒪_X` by the transport of this file, then `g` is a morphism of *locally* ringed topoi.

A section of that ideal is nilpotent with exponent two (`Stacks.Sites.isNilpotent_ι`), and
`AlgebraicGeometry.Space.isLocallyRinged_of_isNilpotent_sub_sections_smallEtale` turns the
sectionwise nilpotency into the units-square condition of [Stacks Project, Tag 04HA], with the
conservativity of the geometric points discharged there.

**This is what the transport buys.**  Before it the ambient sheaf of rings of the conormal datum
was `i^{-1}𝒪_X` on the small étale site of the closed subspace `Z`, so the hypothesis `hsub` —
an equation between a difference of sections of `𝒪_X` and a section of the ideal — could not be
stated at all.  For the derivation-modified structure map of [Stacks Project, Tag 04D0] the
hypothesis is discharged by
`AlgebraicGeometry.Space.exists_conormalAmbientSquareZeroValues_ι_sub_app`.

**No `@[stacks]` attribute.**  Beyond the hypotheses of [Stacks Project, Tag 04HA] this carries
the thickening presented as a closed subspace, its first-order hypothesis, the unperturbed
structure map `φ` with its units reflection at the geometric points, and a `HasPullback`
instance for the units square. -/
theorem isLocallyRinged_of_sub_eq_conormalAmbientSquareZeroValues_ι
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (φ : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor g.toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O ⟶ (smallEtaleRingedTopos B S hS X).O)
    (hφ : ∀ x : GeometricPoint B S hS X.1,
      RingedTopos.ReflectsUnitsObj
        ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)) φ)
    (hsub : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ) (x : ToType
        (((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor g.toToposHom).obj
          (smallEtaleRingedTopos B S hS Y).O).obj.obj V)),
      ∃ m : ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z)).val.obj V,
        ((sheafCompose (smallEtaleRingedTopos B S hS X).J
              (forget₂ CommRingCat.{u} RingCat.{u})).map φ).hom.app V x -
            ((sheafCompose (smallEtaleRingedTopos B S hS X).J
              (forget₂ CommRingCat.{u} RingCat.{u})).map
              g.fSharpInverseImage).hom.app V x =
          (conormalAmbientSquareZeroValues B S hS Z hZ).ι m)
    [HasPullback (RingedTopos.unitsιOf (smallEtaleRingedTopos B S hS X).O)
      (RingedTopos.forgetRingMap g.fSharpInverseImage)] :
    g.IsLocallyRinged := by
  refine isLocallyRinged_of_isNilpotent_sub_sections_smallEtale B S hS g φ hφ fun V s => ?_
  refine RingedTopos.isNilpotent_sub_app_apply_of_forgetCommRingSheaf φ
    g.fSharpInverseImage V s ?_
  obtain ⟨m, hm⟩ := hsub V s
  rw [hm]
  exact Stacks.Sites.isNilpotent_ι (conormalAmbientSquareZeroValues B S hS Z hZ) V m

/-- `g^{-1}𝒪_Y`, the source of the inverse-image form of the structure map of a morphism of
small étale ringed topoi, read as a sheaf of not necessarily commutative rings.

Named, with its type ascribed, because the universe of its sections is otherwise left as a
metavariable and the scalar action of the derivation's Leibniz rule is then not elaborable. -/
abbrev inverseImageStructureRingSheaf
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)) :
    Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u} :=
  (sheafCompose (smallEtaleRingedTopos B S hS X).J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
    ((Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor g.toToposHom).obj
      (smallEtaleRingedTopos B S hS Y).O)

/-- **The derivation-modified structure map on the small étale site of the ambient space is a
morphism of locally ringed topoi.**

Let `Z ⊂ X` be a first order thickening of algebraic spaces, let
`g : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of small étale ringed topoi, let
`φ : g^{-1}𝒪_Y ⟶ 𝒪_X` be a second structure map which reflects units at every geometric point
of `X`, and let `D` be a derivation of `g^{-1}𝒪_Y` with values in the conormal module `𝒞_{Z/X}`
read on the site of `X` through `φ`.  If the structure map of `g` is `φ` modified by `D` — the
sum `α = (a')^♯ + D` of [Stacks Project, Tag 04D0], formed by
`AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom` — then `g` is a morphism of
locally ringed topoi.

**This is the end-to-end consequence of the transport.**  The difference of the two structure
maps is `ι (D x)`, a section of a square-zero ideal of `𝒪_X`
(`AlgebraicGeometry.Space.exists_conormalAmbientSquareZeroValues_ι_sub_app`), hence nilpotent
with exponent two, and
`AlgebraicGeometry.Space.isLocallyRinged_of_sub_eq_conormalAmbientSquareZeroValues_ι` turns that
into the units-square condition of [Stacks Project, Tag 04HA].  What makes the composition
possible is that the ideal is an ideal of `𝒪_X` itself: before the transport of this file the
ambient sheaf of rings of the conormal datum was `i^{-1}𝒪_X` on the site of `Z`, so the modified
map and the structure map of `g` were morphisms between two different pairs of sheaves of rings
and the hypothesis `hg` could not even be stated.

**No `@[stacks]` attribute.**  Beyond the hypotheses of [Stacks Project, Tag 04HA] and of
[Stacks Project, Tag 04D0] this carries: the thickening presented as a closed subspace, the
unperturbed structure map `φ` with its units reflection, the derivation as an unbundled explicit
family rather than a `PresheafOfModules.Derivation'`, a `HasPullback` instance for the units
square, and `hg` — that the structure map of the given `g` *is* the modified morphism, rather
than a construction of such a `g` out of `φ` and `D`. -/
theorem isLocallyRinged_of_conormalAmbientSourceDerivationActionHom
    (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (φ : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor g.toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O ⟶ (smallEtaleRingedTopos B S hS X).O)
    (hφ : ∀ x : GeometricPoint B S hS X.1,
      RingedTopos.ReflectsUnitsObj
        ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)) φ)
    (D : ∀ V : (SmallEtale B S hS X.1)ᵒᵖ,
      (inverseImageStructureRingSheaf B S hS g).obj.obj V →+
      ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z))).val.obj V)
    (hmul : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
      (s t : (inverseImageStructureRingSheaf B S hS g).obj.obj V),
      D V (s * t) = s • D V t + t • D V s)
    (hmap : ∀ (V W : (SmallEtale B S hS X.1)ᵒᵖ) (h : V ⟶ W)
      (s : (inverseImageStructureRingSheaf B S hS g).obj.obj V),
      D W ((inverseImageStructureRingSheaf B S hS g).obj.map h s) =
        ((SheafOfModules.restrictScalars
            ((sheafCompose (smallEtaleRingedTopos B S hS X).J
              (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
          ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
            (conormalModule B S hS X Z))).val.map h (D V s))
    (hg : (sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map g.fSharpInverseImage =
        conormalAmbientSourceDerivationActionHom B S hS Z hZ
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map φ) D hmul hmap)
    [HasPullback (RingedTopos.unitsιOf (smallEtaleRingedTopos B S hS X).O)
      (RingedTopos.forgetRingMap g.fSharpInverseImage)] :
    g.IsLocallyRinged := by
  refine isLocallyRinged_of_sub_eq_conormalAmbientSquareZeroValues_ι B S hS Z hZ g φ hφ
    fun V x => ?_
  rw [hg]
  exact exists_conormalAmbientSquareZeroValues_ι_sub_app B S hS Z hZ
    ((sheafCompose (smallEtaleRingedTopos B S hS X).J
      (forget₂ CommRingCat.{u} RingCat.{u})).map φ) D hmul hmap V x

end LocallyRinged

/-! ### The derivation-modified structure map as a morphism of ringed topoi -/

section DerivationHom

variable {Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
  (φ : (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor g.toToposHom).obj
      (smallEtaleRingedTopos B S hS Y).O ⟶ (smallEtaleRingedTopos B S hS X).O)
  (D : ∀ V : (SmallEtale B S hS X.1)ᵒᵖ,
      (inverseImageStructureRingSheaf B S hS g).obj.obj V →+
      ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z))).val.obj V)
  (hmul : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (s t : (inverseImageStructureRingSheaf B S hS g).obj.obj V),
    D V (s * t) = s • D V t + t • D V s)
  (hmap : ∀ (V W : (SmallEtale B S hS X.1)ᵒᵖ) (h : V ⟶ W)
    (s : (inverseImageStructureRingSheaf B S hS g).obj.obj V),
    D W ((inverseImageStructureRingSheaf B S hS g).obj.map h s) =
      ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
        ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
          (conormalModule B S hS X Z))).val.map h (D V s))

/-- **The derivation-modified structure map, as a morphism of sheaves of commutative rings.**
`AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom` produces the sum `φ + D` as a
morphism of sheaves of not necessarily commutative rings, because that is the category in which
`Stacks.Sites.derivationActionHom` and the sheaves of modules over a sheaf of rings are indexed.
The structure map of a `AlgebraicGeometry.RingedToposHom` is a morphism of sheaves of
*commutative* rings, so the sum has to be read back there.

Nothing is proved: forgetting commutativity is fully faithful on sheaves
(`Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf`), so a morphism of the
underlying sheaves of rings of two sheaves of commutative rings *is* a morphism of sheaves of
commutative rings, and this is its unique preimage.  The same step builds the structure map of
[Stacks Project, Tag 03G8] (`AlgebraicGeometry.Space.structureSharpCommRing`). -/
def conormalAmbientSourceDerivationActionCommHom :
    (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor g.toToposHom).obj
        (smallEtaleRingedTopos B S hS Y).O ⟶ (smallEtaleRingedTopos B S hS X).O :=
  (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1} (SmallEtale.topology B S hS X.1)).preimage
    (conormalAmbientSourceDerivationActionHom B S hS Z hZ
      ((sheafCompose (smallEtaleRingedTopos B S hS X).J
        (forget₂ CommRingCat.{u} RingCat.{u})).map φ) D hmul hmap)

/-- The morphism of sheaves of rings underlying
`AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionCommHom` is the sum `φ + D`
itself.  This is the only thing the preimage is ever used through. -/
theorem forgetCommRingSheaf_map_conormalAmbientSourceDerivationActionCommHom :
    (sheafCompose (smallEtaleRingedTopos B S hS X).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (conormalAmbientSourceDerivationActionCommHom B S hS Z hZ g φ D hmul hmap) =
      conormalAmbientSourceDerivationActionHom B S hS Z hZ
        ((sheafCompose (smallEtaleRingedTopos B S hS X).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map φ) D hmul hmap :=
  (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
    (SmallEtale.topology B S hS X.1)).map_preimage _

/-- **The derivation-modified structure map as a morphism of the small étale ringed topoi of the
two ambient spaces.**  The morphism of topoi is that of the given `g` and the structure map is
`φ + D`, the sum `α = (a')^♯ + D` of [Stacks Project, Tag 04D0] formed on the site of the ambient
space `X` by `AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionHom`.

This is the field `hom` of `AlgebraicGeometry.Space.DerivationModification`, for a derivation
given as an unbundled explicit family rather than produced from a `θ` by Equation
[Stacks Project, Tag 0619].  Both steps it is assembled from are available and generic: the passage
from the inverse-image form of a structure map to a morphism of ringed topoi is
`AlgebraicGeometry.RingedToposHom.ofInverseImageMap`, which transposes along
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, and the passage from sheaves of rings
to sheaves of commutative rings is
`AlgebraicGeometry.Space.conormalAmbientSourceDerivationActionCommHom`.

**No `@[stacks]` attribute.**  Beyond the data of [Stacks Project, Tag 04D0] this carries the
thickening presented as a `AlgebraicGeometry.Space.ClosedSubspaces`, the derivation as an unbundled
explicit family, and the unperturbed structure map `φ` as an argument independent of `g`. -/
def conormalAmbientDerivationRingedToposHom :
    RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y) :=
  RingedToposHom.ofInverseImageMap (X := smallEtaleRingedTopos B S hS X)
    (Y := smallEtaleRingedTopos B S hS Y) g.toToposHom
    (conormalAmbientSourceDerivationActionCommHom B S hS Z hZ g φ D hmul hmap)

/-- The modification does not move the underlying morphism of topoi: it is the *same term* as
that of `g`, which is what lets the units reflection of `φ` be read off the local ringedness of
`g` at the geometric points. -/
@[simp]
theorem conormalAmbientDerivationRingedToposHom_toToposHom :
    (conormalAmbientDerivationRingedToposHom B S hS Z hZ g φ D hmul hmap).toToposHom =
      g.toToposHom :=
  rfl

/-- The inverse-image form of the structure map of the modification is the sum `φ + D`, read on
sheaves of commutative rings. -/
theorem fSharpInverseImage_conormalAmbientDerivationRingedToposHom :
    (conormalAmbientDerivationRingedToposHom B S hS Z hZ g φ D hmul hmap).fSharpInverseImage =
      conormalAmbientSourceDerivationActionCommHom B S hS Z hZ g φ D hmul hmap :=
  RingedToposHom.ofInverseImageMap_fSharpInverseImage
    (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
    g.toToposHom _

/-- **The modification is a morphism of locally ringed topoi.**  This is the field
`isLocallyRinged` of `AlgebraicGeometry.Space.DerivationModification`, discharged rather than
assumed: the hypothesis `hg` of
`AlgebraicGeometry.Space.isLocallyRinged_of_conormalAmbientSourceDerivationActionHom` — that the
structure map of the morphism of ringed topoi at hand *is* the derivation-modified one — holds by
construction here, being
`AlgebraicGeometry.Space.forgetCommRingSheaf_map_conormalAmbientSourceDerivationActionCommHom`
composed with the characterisation of the structure map of
`AlgebraicGeometry.RingedToposHom.ofInverseImageMap`.

What remains an argument is the units reflection `hφ` of the *unperturbed* structure map `φ` at
the geometric points of `X`; for `φ` the structure map of a morphism of algebraic spaces that is
[Stacks Project, Tag 04KJ] followed by
`AlgebraicGeometry.RingedToposHom.reflectsUnitsObj_of_isLocallyRinged`, applicable because the
morphism of topoi is unchanged by the modification. -/
theorem isLocallyRinged_conormalAmbientDerivationRingedToposHom
    (hφ : ∀ x : GeometricPoint B S hS X.1,
      RingedTopos.ReflectsUnitsObj
        ((etaleSitePoint B S hS X.1 x X.2).sheafFiber (A := Type u)) φ)
    [HasPullback (RingedTopos.unitsιOf (smallEtaleRingedTopos B S hS X).O)
      (RingedTopos.forgetRingMap
        (conormalAmbientDerivationRingedToposHom B S hS Z hZ g φ D hmul hmap).fSharpInverseImage)] :
    (conormalAmbientDerivationRingedToposHom B S hS Z hZ g φ D hmul hmap).IsLocallyRinged :=
  isLocallyRinged_of_conormalAmbientSourceDerivationActionHom B S hS Z hZ
    (conormalAmbientDerivationRingedToposHom B S hS Z hZ g φ D hmul hmap) φ hφ D hmul hmap
    ((congrArg (sheafCompose (smallEtaleRingedTopos B S hS X).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map
        (fSharpInverseImage_conormalAmbientDerivationRingedToposHom
          B S hS Z hZ g φ D hmul hmap)).trans
      (forgetCommRingSheaf_map_conormalAmbientSourceDerivationActionCommHom
        B S hS Z hZ g φ D hmul hmap))

/-- A morphism of ringed topoi is the morphism attached by
`AlgebraicGeometry.RingedToposHom.ofInverseImageMap` to the inverse-image form of its own
structure map.

Stated here rather than beside `AlgebraicGeometry.RingedToposHom.ofInverseImageMap`, which is in
a chapter this development does not own; it is the round trip of that definition and involves no
geometry.  It is what identifies the modification by the zero derivation with the morphism it
modifies. -/
theorem eq_ofInverseImageMap_fSharpInverseImage
    (f : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y)) :
    RingedToposHom.ofInverseImageMap (X := smallEtaleRingedTopos B S hS X)
        (Y := smallEtaleRingedTopos B S hS Y) f.toToposHom f.fSharpInverseImage = f :=
  congrArg (RingedToposHom.mk (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) f.toToposHom)
    (((commRingImageAdjunction f.toToposHom).homEquiv
      (smallEtaleRingedTopos B S hS Y).O (smallEtaleRingedTopos B S hS X).O).apply_symm_apply
        f.fSharp)

/-- **Modifying by the zero derivation changes nothing.**  The sum `φ + D` for the zero
derivation is `φ` on the nose, by the sign convention of `Stacks.Sites.derivationActionHom` and
because an additive map sends the zero section to the zero section. -/
theorem conormalAmbientSourceDerivationActionHom_eq_of_eq_zero
    (hD : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
      (x : (inverseImageStructureRingSheaf B S hS g).obj.obj V), D V x = 0) :
    conormalAmbientSourceDerivationActionHom B S hS Z hZ
        ((sheafCompose (smallEtaleRingedTopos B S hS X).J
          (forget₂ CommRingCat.{u} RingCat.{u})).map φ) D hmul hmap =
      (sheafCompose (smallEtaleRingedTopos B S hS X).J
        (forget₂ CommRingCat.{u} RingCat.{u})).map φ := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun V => RingCat.hom_ext (RingHom.ext fun x => ?_))
  refine (conormalAmbientSourceDerivationActionHom_app_apply B S hS Z hZ
    ((sheafCompose (smallEtaleRingedTopos B S hS X).J
      (forget₂ CommRingCat.{u} RingCat.{u})).map φ) D hmul hmap V x).trans ?_
  have hz : (conormalAmbientSquareZeroValues B S hS Z hZ).ι (D V x) = 0 := by
    rw [hD V x]
    exact map_zero _
  exact sub_eq_self.2 hz

/-- **The field `hom_base` of `AlgebraicGeometry.Space.DerivationModification`, as an
equality.**  The modification of a morphism of small étale ringed topoi by the zero derivation is
that morphism itself — not merely 2-isomorphic to it.

This is the composite of three facts: the sum `φ + D` is `φ` for the zero derivation; forgetting
commutativity is faithful, so the two commutative-ring-level structure maps agree; and
`AlgebraicGeometry.RingedToposHom.ofInverseImageMap` at the structure map of `g` returns `g`. -/
theorem conormalAmbientDerivationRingedToposHom_eq_of_eq_zero
    (D : ∀ V : (SmallEtale B S hS X.1)ᵒᵖ,
        (inverseImageStructureRingSheaf B S hS g).obj.obj V →+
        ((SheafOfModules.restrictScalars
            ((sheafCompose (smallEtaleRingedTopos B S hS X).J
              (forget₂ CommRingCat.{u} RingCat.{u})).map g.fSharpInverseImage)).obj
          ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
            (conormalModule B S hS X Z))).val.obj V)
    (hmul : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
      (s t : (inverseImageStructureRingSheaf B S hS g).obj.obj V),
      D V (s * t) = s • D V t + t • D V s)
    (hmap : ∀ (V W : (SmallEtale B S hS X.1)ᵒᵖ) (h : V ⟶ W)
      (s : (inverseImageStructureRingSheaf B S hS g).obj.obj V),
      D W ((inverseImageStructureRingSheaf B S hS g).obj.map h s) =
        ((SheafOfModules.restrictScalars
            ((sheafCompose (smallEtaleRingedTopos B S hS X).J
              (forget₂ CommRingCat.{u} RingCat.{u})).map g.fSharpInverseImage)).obj
          ((modulePushforward B S hS (subspaceInclusion B S hS X Z)).obj
            (conormalModule B S hS X Z))).val.map h (D V s))
    (hD : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ)
      (x : (inverseImageStructureRingSheaf B S hS g).obj.obj V), D V x = 0) :
    conormalAmbientDerivationRingedToposHom B S hS Z hZ g g.fSharpInverseImage D hmul hmap = g := by
  have hcomm : conormalAmbientSourceDerivationActionCommHom B S hS Z hZ g
      g.fSharpInverseImage D hmul hmap = g.fSharpInverseImage :=
    (fullyFaithfulForgetCommRingSheaf.{u, u, u + 1}
        (SmallEtale.topology B S hS X.1)).map_injective
      ((forgetCommRingSheaf_map_conormalAmbientSourceDerivationActionCommHom
          B S hS Z hZ g g.fSharpInverseImage D hmul hmap).trans
        (conormalAmbientSourceDerivationActionHom_eq_of_eq_zero B S hS Z hZ g
          g.fSharpInverseImage D hmul hmap hD))
  exact (congrArg (RingedToposHom.ofInverseImageMap (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) g.toToposHom) hcomm).trans
    (eq_ofInverseImageMap_fSharpInverseImage B S hS g)

end DerivationHom

end AlgebraicGeometry.Space

end
