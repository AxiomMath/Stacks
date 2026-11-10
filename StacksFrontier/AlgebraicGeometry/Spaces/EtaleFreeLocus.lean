module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModule
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# The locus where a module on an algebraic space is free on an étale neighbourhood

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which
is locally of finite presentation, and let `F` be a finitely presented `𝒪_X`-module which is
flat over `Y`.  Stacks 0CZT says that the set

```
{x ∈ |X| : F is free in an étale neighbourhood of x}
```

is open in `|X|`, and that its formation commutes with arbitrary base change `Y' ⟶ Y`.

This file defines the locus and proves the openness clause.

## Main definitions

* `AlgebraicGeometry.Space.IsFreeModule`: an `𝒪_X`-module is *free* when it is a coproduct of
  copies of the structure sheaf `𝒪_X`.
* `AlgebraicGeometry.Space.etaleFreeLocus`: the set of points of `|X|` admitting an étale
  neighbourhood on which `F` becomes free.
* `AlgebraicGeometry.Space.etaleFiniteFreeLocus`: the same set for the *finite* freeness of
  Stacks 03DE(2), which is the condition clause (4) of Stacks 0CZS asks for.
* `AlgebraicGeometry.Space.etaleRankOneFreeLocus`: the same set with the rank pinned to one,
  that is, with the inverse image of the module isomorphic to the structure sheaf.

## Main results

* `AlgebraicGeometry.Space.isOpen_of_etale_witness`: a set of points which, around each of its
  members, contains the image on points of an étale morphism of algebraic spaces into `X`, is
  open.
* `AlgebraicGeometry.Space.isOpen_etaleFreeLocus`: the openness clause of Stacks 0CZT.
* `AlgebraicGeometry.Space.isOpen_etaleFiniteFreeLocus`: the same for the finite-free locus.
* `AlgebraicGeometry.Space.isOpen_etaleRankOneFreeLocus`: the same for the rank-one locus.

## Implementation notes

An *étale neighbourhood* of `x ∈ |X|` is an étale morphism `a : V ⟶ X` of algebraic spaces
(Stacks 03FR, `AlgebraicGeometry.Space.IsEtale`) together with a point of `|V|` above `x`; the
module on it is the inverse image `a^*F` of Stacks 03LU, `AlgebraicGeometry.Space.modulePullback`.
The point is recorded as `x ∈ Set.range |a|` rather than as a chosen lift.

Freeness of a module on the small étale site is read through the universal property of the
coproduct, as in `SheafOfModules.IsLocallyFreeOnSite` (Stacks 03DL(1)), with the index type in
the universe `u` of the structure rings.

The base-change clause of Stacks 0CZT is `AlgebraicGeometry.Space.etaleFreeLocus_modulePullback_eq`
of `StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusBaseChange.lean`. It cannot be moved into
this module: its proof uses `StacksFrontier/AlgebraicGeometry/Spaces/EtaleFreeLocusPullback.lean`
and
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricModuleStalkFree.lean`, which both import this one.

## References

* [Stacks Project, Tag 0CZT](https://stacks.math.columbia.edu/tag/0CZT)
* [Stacks Project, Tag 0CZS](https://stacks.math.columbia.edu/tag/0CZS)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Freeness of a module on an algebraic space -/

/-- An `𝒪_X`-module on the small étale site of an algebraic space `X` is **free** when it is a
coproduct of copies of the structure sheaf `𝒪_X`, indexed by some type. -/
def IsFreeModule (X : AlgebraicSpaces B S hS) (F : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  ∃ (I : Type u) (ι : ∀ _ : I,
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) ⟶ F),
    Nonempty (IsColimit (Cofan.mk F ι))

/-- A finite free module is free. -/
theorem IsFreeModule.of_isFiniteFree (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (h : SheafOfModules.IsFiniteFree
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) F) :
    IsFreeModule B S hS X F := by
  obtain ⟨n, ι, hι⟩ :=
    (SheafOfModules.isFiniteFree_iff_exists_isColimit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)) F).1 h
  exact ⟨ULift.{u} (Fin n), fun i => ι i.down,
    ⟨(Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk F ι)) hι.some⟩⟩

/-! ### The étale free locus -/

/-- The set of points of `|X|` at which `F` is **free in an étale neighbourhood**: those
`x ∈ |X|` admitting an étale morphism `a : V ⟶ X` of algebraic spaces whose image on points
contains `x` and along which the inverse image of `F` is a free module.

This is the set of Stacks 0CZT. -/
def etaleFreeLocus {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2) :
    Set (points B S hS X.1) :=
  {x | ∃ (V : AlgebraicSpaces B S hS) (a : V ⟶ X), IsEtale B S hS a.hom ∧
    x ∈ Set.range (pointsMap B S hS V.1 a.hom) ∧
    IsFreeModule B S hS V ((modulePullback B S hS a).obj F)}

/-- The set of points of `|X|` at which `F` is **finite free in an étale neighbourhood**, with
finite freeness read through `SheafOfModules.IsFiniteFree`, Stacks 03DE(2).  This is the set
of Stacks 0CZT with the freeness of clause (4) of Stacks 0CZS, which agrees with freeness for
the finitely presented module of the statement. -/
def etaleFiniteFreeLocus {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2) :
    Set (points B S hS X.1) :=
  {x | ∃ (V : AlgebraicSpaces B S hS) (a : V ⟶ X), IsEtale B S hS a.hom ∧
    x ∈ Set.range (pointsMap B S hS V.1 a.hom) ∧
    SheafOfModules.IsFiniteFree
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O))
      ((modulePullback B S hS a).obj F)}

/-- The finite free locus is contained in the free locus. -/
theorem etaleFiniteFreeLocus_subset_etaleFreeLocus {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) :
    etaleFiniteFreeLocus B S hS F ⊆ etaleFreeLocus B S hS F := by
  rintro x ⟨V, a, hae, hxr, hfree⟩
  exact ⟨V, a, hae, hxr, IsFreeModule.of_isFiniteFree B S hS V _ hfree⟩

/-- The set of points of `|X|` at which `F` is **free of rank one in an étale
neighbourhood**: those `x ∈ |X|` admitting an étale morphism `a : V ⟶ X` of algebraic spaces
whose image on points contains `x` and along which the inverse image of `F` is isomorphic to the
structure sheaf `𝒪_V`.  This is the locus of Stacks 0CZT with the rank pinned to one. -/
def etaleRankOneFreeLocus {X : AlgebraicSpaces B S hS} (F : Modules.{u, u} B S hS X.1 X.2) :
    Set (points B S hS X.1) :=
  {x | ∃ (V : AlgebraicSpaces B S hS) (a : V ⟶ X), IsEtale B S hS a.hom ∧
    x ∈ Set.range (pointsMap B S hS V.1 a.hom) ∧
    Nonempty ((modulePullback B S hS a).obj F ≅
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O))}

/-! ### Openness -/

/-- A set of points of an algebraic space `X` which, around each of its members, contains the
image on points of an étale morphism of algebraic spaces into `X` is open. -/
theorem isOpen_of_etale_witness {X : AlgebraicSpaces B S hS} (W : Set (points B S hS X.1))
    (h : ∀ x ∈ W, ∃ (V : AlgebraicSpaces B S hS) (a : V ⟶ X), IsEtale B S hS a.hom ∧
      x ∈ Set.range (pointsMap B S hS V.1 a.hom) ∧
      Set.range (pointsMap B S hS V.1 a.hom) ⊆ W) :
    @IsOpen _ (pointTopology B S hS X.1) W :=
  (@isOpen_iff_forall_mem_open _ (pointTopology B S hS X.1) W).2 (by
    intro x hx
    obtain ⟨V, a, hae, hxr, hsub⟩ := h x hx
    exact ⟨Set.range (pointsMap B S hS V.1 a.hom), hsub,
      isOpen_range_pointsMap_of_isEtale B S hS a.hom V.2 X.2 hae, hxr⟩)

/-- The set of points of `|X|` lying under an étale morphism `a : V ⟶ X` satisfying a property `P`
is open. -/
private theorem isOpen_setOf_etale_witness {X : AlgebraicSpaces B S hS}
    (P : ∀ V : AlgebraicSpaces B S hS, (V ⟶ X) → Prop) :
    @IsOpen _ (pointTopology B S hS X.1) {x | ∃ (V : AlgebraicSpaces B S hS) (a : V ⟶ X),
      IsEtale B S hS a.hom ∧ x ∈ Set.range (pointsMap B S hS V.1 a.hom) ∧ P V a} :=
  isOpen_of_etale_witness B S hS _ (by
    rintro x ⟨V, a, hae, hxr, h⟩
    exact ⟨V, a, hae, hxr, fun _ hy => ⟨V, a, hae, hy, h⟩⟩)

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is locally of finite
presentation and let `F` be a finitely presented `𝒪_X`-module which is flat over `Y`.  Then the
set of points of `|X|` at which `F` is free in an étale neighbourhood is open in `|X|`. -/
@[stacks 0CZT "openness"]
theorem isOpen_etaleFreeLocus {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (_hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2)
    [SheafOfModules.IsFinitePresentationOnSite F]
    (_hF : IsFlatOver B S hS X.2 f.hom F) :
    @IsOpen _ (pointTopology B S hS X.1) (etaleFreeLocus B S hS F) :=
  isOpen_setOf_etale_witness B S hS _

/-- The set of points of `|X|` at which `F` is finite free in an étale neighbourhood is open in
`|X|`. -/
theorem isOpen_etaleFiniteFreeLocus {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) :
    @IsOpen _ (pointTopology B S hS X.1) (etaleFiniteFreeLocus B S hS F) :=
  isOpen_setOf_etale_witness B S hS _

/-- The set of points of `|X|` at which `F` is free of rank one in an étale neighbourhood is
open in `|X|`. -/
theorem isOpen_etaleRankOneFreeLocus {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) :
    @IsOpen _ (pointTopology B S hS X.1) (etaleRankOneFreeLocus B S hS F) :=
  isOpen_setOf_etale_witness B S hS _

end AlgebraicGeometry.Space

end
