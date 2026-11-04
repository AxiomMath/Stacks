module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.IteratedRefinement
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible abelian sheaves form a weak Serre subcategory

Stacks 03RZ asserts, for a scheme `X`, that the constructible sheaves of sets on the small étale
site are closed under finite limits and colimits, that the constructible abelian sheaves form a
weak Serre subcategory, and that the constructible sheaves of modules over a Noetherian ring form
one too. This file proves the second of those three.

The source's argument is: a five term exact sequence of abelian sheaves whose four outer terms are
constructible may be restricted to an affine open, and then to the strata of a single constructible
stratification adapted to all four outer terms; on a stratum constructibility *is* finite local
constancy, restriction to a stratum is exact so the restricted sequence is still exact, and the
finite locally constant abelian sheaves are a weak Serre subcategory (Stacks 093U (2)), so the
middle term is finite locally constant there. That is constructibility of the middle term.

Every one of those four steps is a declaration of the library, and this file is the composition:

* the weak Serre criterion in five term form,
  `CategoryTheory.ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact`;
* the simultaneous stratification of four sheaves,
  `AlgebraicGeometry.exists_stratification_isFiniteLocallyConstant_forall`;
* exactness of restriction to a stratum,
  `AlgebraicGeometry.shortExact_map_smallEtaleSheafPullback_addCommGrp`, in the form
  `Stacks.ConstantSheaf.mapComposableArrows_exact`;
* Stacks 093U (2) on a stratum,
  `AlgebraicGeometry.SmallEtale.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf`.

## Main results

* `AlgebraicGeometry.SmallEtale.abelian_sheaf_addCommGrp`: abelian sheaves on the small étale site
  with coefficients in `AddCommGrpCat.{max (u + 1) w}` form an abelian category.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_zero'`: the zero abelian sheaf is
  constructible.  The primed name marks the weaker hypotheses: the coefficient universe is
  `max (u + 1) w` rather than `u + 1`, and the right-adjointness instance is supplied here
  rather than assumed.
* `AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleAbelianSheaf`: Stacks 03RZ (2),
  the constructible abelian sheaves on the small étale site of a scheme form a weak Serre
  subcategory. No hypothesis on the scheme, in particular no Noetherian hypothesis.
* `AlgebraicGeometry.isSerreClass_isConstructibleAbelianSheaf_of_isClosedUnderSubobjects'`:
  Stacks 09BH (2) now rests on sub-closure alone.

## Implementation notes

**The coefficient universe is `AddCommGrpCat.{max (u + 1) w}` and cannot be lowered.** Stacks
093U (2) is stated on a site with objects in `Type c` and morphisms in `Type v` for coefficients in
`AddCommGrpCat.{max c v w}`; the small étale site of Stacks 021B has objects in `Type (u + 1)` and
morphisms in `Type u`, so its coefficient universe is `max (u + 1) w`. See
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf` for why no
generalisation of 093U (2) would help.

Three instances are therefore supplied locally rather than globally, following the precedent of
`AlgebraicGeometry.SmallEtale.hasSheafify_addCommGrp`: sheafification on the site and on its
slices, and the abelian structure. The last is the reason this file declares
`AlgebraicGeometry.SmallEtale.abelian_sheaf_addCommGrp` at all. `AlgebraicGeometry.SmallEtale`
already has a *global* `abelian_sheaf` instance pinned to `AddCommGrpCat.{u}`; on a goal with
coefficients in `AddCommGrpCat.{max (u + 1) w}` instance search reaches it and the universe
unifier gets stuck on `u =?= max (u + 1) w` rather than rejecting the candidate, so the goal fails
with a universe constraint error instead of falling through to
`CategoryTheory.sheafIsAbelian`. A local instance at the universe actually wanted is tried first
and resolves it.

**No `@[stacks 03RZ]` attribute appears in this file.** Tag 03RZ has three parts and only part (2)
is proved here; part (1), closure of the constructible sheaves of sets under finite limits and
colimits, and part (3), the weak Serre property for constructible sheaves of modules over a
Noetherian ring, are not. Part (3) would additionally need left exactness of inverse image for
module coefficients, the analogue of
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_addCommGrp`, which this library
does not have.

## References

* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe w u

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.hasSheafify_addCommGrp
  SmallEtale.hasSheafifyOver_addCommGrp
  additive_smallEtaleSheafPullback_addCommGrp
  preservesFiniteLimits_smallEtaleSheafPullback_addCommGrp
  preservesFiniteColimits_smallEtaleSheafPullback_addCommGrp

/-- Abelian sheaves on the small étale site of `S` with coefficients in
`AddCommGrpCat.{max (u + 1) w}` form an abelian category.

`AlgebraicGeometry.SmallEtale.abelian_sheaf` is the same statement at `AddCommGrpCat.{u}`; it is a
global instance, and on a goal at this coefficient universe instance search reaches it and gets
stuck rather than backtracking, so the statement is restated here at the universe in which Stacks
093U (2) is available on this site. -/
@[instance_reducible]
public def SmallEtale.abelian_sheaf_addCommGrp (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    Abelian (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{max (u + 1) w}) :=
  letI := SmallEtale.hasSheafify_addCommGrp.{w} B S hS
  CategoryTheory.sheafIsAbelian

attribute [local instance] SmallEtale.abelian_sheaf_addCommGrp

/-- Pushforward of abelian sheaves along the slice of small étale base change, with coefficients in
`AddCommGrpCat.{max (u + 1) w}`, is a right adjoint.

This is what the definition of finite local constancy of an inverse image asks for, and the
instance `AlgebraicGeometry.hasSheafifyOverSmallEtale` which discharges it at `AddCommGrpCat.{u}`
is pinned to that universe. -/
public theorem SmallEtale.isRightAdjoint_overPost_addCommGrp (B : BigEtaleSite.{u})
    {S T : B.Scheme} (f : T ⟶ S) (X : SmallEtale B S.obj S.property) :
    ((Over.post (X := X) (smallEtaleBaseChange B f)).sheafPushforwardContinuous
        AddCommGrpCat.{max (u + 1) w}
      ((SmallEtale.topology B S.obj S.property).over X)
      ((SmallEtale.topology B T.obj T.property).over
        ((smallEtaleBaseChange B f).obj X))).IsRightAdjoint :=
  inferInstance

attribute [local instance] SmallEtale.isRightAdjoint_overPost_addCommGrp

variable (B : BigEtaleSite.{u}) (X : B.Scheme)

/-- **The zero abelian sheaf is constructible.** Its restriction to the single stratum of
`AlgebraicGeometry.ConstructibleStratification.singleReduced` is zero, and the zero sheaf is
finite locally constant by `Stacks.ConstantSheaf.isFiniteLocallyConstant_zero`.

This is the nonemptiness half of the weak Serre criterion. -/
public theorem isConstructibleAbelianSheaf_zero' : IsConstructibleAbelianSheaf B X
    (0 : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) w}) := by
  intro V
  refine ⟨ConstructibleStratification.singleReduced B X V.1, fun i => ?_⟩
  have h0 := Stacks.ConstantSheaf.isFiniteLocallyConstant_zero.{u, u + 1, w}
    (SmallEtale.topology B ((ConstructibleStratification.singleReduced B X V.1).piece i).obj
      ((ConstructibleStratification.singleReduced B X V.1).piece i).property)
  exact Stacks.ConstantSheaf.isFiniteLocallyConstant_congr _
    (((smallEtaleBaseChange B
      ((ConstructibleStratification.singleReduced B X V.1).inclusion i)).sheafPullback
      AddCommGrpCat.{max (u + 1) w} _ _).mapZeroObject).symm

/-- **Stacks 03RZ (2).** The constructible sheaves of abelian groups on the small étale site of a
scheme form a weak Serre subcategory of all abelian sheaves on that site.

There is no hypothesis on the scheme: the Noetherian hypothesis belongs to Stacks 09BH, the strong
Serre statement, not to this one.

The proof is the five term form of the weak Serre condition,
`CategoryTheory.ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact`. Given an exact
`ℱ₀ ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ ℱ₄` with the four outer terms constructible, fix an affine open and
stratify all four of them on one constructible stratification of it with
`AlgebraicGeometry.exists_stratification_isFiniteLocallyConstant_forall`. Restriction to a stratum
is exact, so the restricted five term sequence is still exact, and on a stratum constructibility is
finite local constancy, which is a weak Serre condition by Stacks 093U (2). Hence the restriction
of `ℱ₂` to each stratum is finite locally constant, which is constructibility of `ℱ₂`. -/
@[sga "4 IX 2.6" "special case"]
public theorem SmallEtale.isWeakSerreClass_isConstructibleAbelianSheaf :
    (isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{max (u + 1) w})).IsWeakSerreClass := by
  apply (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact _).2
  refine ⟨⟨0, isConstructibleAbelianSheaf_zero' B X⟩, ?_⟩
  intro S hS h₀ h₁ h₃ h₄
  show IsConstructibleAbelianSheaf B X (S.obj' 2)
  intro V
  obtain ⟨r, hr⟩ := exists_stratification_isFiniteLocallyConstant_forall B X
    (F := ![S.obj' 0, S.obj' 1, S.obj' 3, S.obj' 4])
    (fun j => by fin_cases j <;> assumption) V
  refine ⟨r, fun k => ?_⟩
  have hWS : (Stacks.ConstantSheaf.isFiniteLocallyConstantAbelianSheaf
      (SmallEtale.topology B (r.piece k).obj (r.piece k).property) :
        ObjectProperty (Sheaf (SmallEtale.topology B (r.piece k).obj (r.piece k).property)
          AddCommGrpCat.{max (u + 1) w})).IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isFiniteLocallyConstantAbelianSheaf B
      (r.piece k).obj (r.piece k).property
  exact (Stacks.ConstantSheaf.isFiniteLocallyConstantAbelianSheaf
      (SmallEtale.topology B (r.piece k).obj (r.piece k).property)).prop_obj₂_of_exact
    ((((smallEtaleBaseChange B (r.inclusion k)).sheafPullback AddCommGrpCat.{max (u + 1) w}
      (SmallEtale.topology B X.obj X.property)
      (SmallEtale.topology B (r.piece k).obj
        (r.piece k).property)).mapComposableArrows 4).obj S)
    (Stacks.ConstantSheaf.mapComposableArrows_exact
      ((smallEtaleBaseChange B (r.inclusion k)).sheafPullback AddCommGrpCat.{max (u + 1) w}
        (SmallEtale.topology B X.obj X.property)
        (SmallEtale.topology B (r.piece k).obj (r.piece k).property)) S hS)
    (hr k 0) (hr k 1) (hr k 2) (hr k 3)

/-- **Stacks 09BH (2) from sub-closure alone.** If a subsheaf of a constructible abelian sheaf on
the small étale site of `X` is constructible, then the constructible abelian sheaves form a strong
Serre subcategory.

This is `AlgebraicGeometry.isSerreClass_isConstructibleAbelianSheaf_of_isClosedUnderSubobjects`
with its weak Serre hypothesis discharged by
`AlgebraicGeometry.SmallEtale.isWeakSerreClass_isConstructibleAbelianSheaf`, so 09BH (2) rests here
on a single input. The Noetherian hypothesis 09BH carries is needed for that input, not for this
reduction.

**No `@[stacks 09BH]` attribute is attached in this file**, because this is the reduction and not
the proposition; the tag for part (2) is carried by
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian`, which supplies
sub-closure at `AddCommGrpCat.{u + 1}` from part (1) for sheaves of sets. -/
public theorem isSerreClass_isConstructibleAbelianSheaf_of_isClosedUnderSubobjects'
    [(isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{max (u + 1) w})).IsClosedUnderSubobjects] :
    (isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{max (u + 1) w})).IsSerreClass :=
  have : (isConstructibleAbelianSheafProperty B X :
      ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property)
        AddCommGrpCat.{max (u + 1) w})).IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleAbelianSheaf B X
  isSerreClass_isConstructibleAbelianSheaf_of_isClosedUnderSubobjects B X

end AlgebraicGeometry

end
