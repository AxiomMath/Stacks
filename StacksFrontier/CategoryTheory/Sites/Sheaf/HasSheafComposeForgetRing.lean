module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.RingTheory.FreeRing

/-!
# Forgetting a ring to its underlying set preserves the sheaf condition, on any site

Mathlib proves that the forgetful functor of `MonCat`, `CommMonCat`, `AddMonCat`,
`AddCommMonCat`, `GrpCat`, `CommGrpCat`, `AddGrpCat` and `AddCommGrpCat` is corepresentable,
and derives from each that the corresponding sheaf condition is preserved on an arbitrary site.
The `RingCat` member of that family is missing, and the topos-level ring theory of this
development needs it: `AlgebraicGeometry.RingedToposHom`,
`Stacks.Sheaves.RingedToposModules.pushforwardModules` and
`Stacks.Sheaves.RingedToposModules.pullbackModules` all take
`CategoryTheory.GrothendieckTopology.HasSheafCompose (forget RingCat)` as a hypothesis, which
every caller then has to discharge by hand.

This module supplies the missing corepresentability — `forget RingCat` is corepresented by the
free ring on one generator — and registers the two sheaf-condition facts it yields as
instances, so that a caller writing a statement about ringed topoi no longer has to carry them.

## Main results

* `RingCat.forgetCorepresentableBy`: the free ring `FreeRing PUnit` corepresents
  `forget RingCat`.
* `RingCat.forget_isCorepresentable`: hence `forget RingCat` is corepresentable.
* `Stacks.instHasSheafComposeForgetRingCat`: on any site, and for any universe of sections,
  the sheaf condition for `RingCat`-valued presheaves is preserved by `forget RingCat`.
* `Stacks.instHasSheafComposeForget₂CommRingCatRingCat`: the same for
  `forget₂ CommRingCat RingCat`.
* `Stacks.preservesSheafification_forget₂_commRingCat` and the instance
  `Stacks.instPreservesSheafificationForget₂CommRingCatRingCat`: on every site whose universes
  the universe of sections dominates, `forget₂ CommRingCat RingCat` preserves sheafification.

## Implementation notes

`Stacks.hasSheafCompose_forget₂_commRingCat` is deliberately a `theorem` and not an `instance`,
because the structures of that stack — `AlgebraicGeometry.RingedToposHom`,
`AlgebraicGeometry.ClosedRingedImmersion`, `AlgebraicGeometry.RingedSite` — carry their own
witness of the class, and a second globally applicable instance in scope at those declarations
is the standard source of `synthesized instance is not definitionally equal to expression
inferred by typing rules`. That decision is not disturbed: the instances live here, in a module
those files do not import, and are picked up only by a consumer that asks for them. Where a
witness is in scope as a hypothesis it still wins, since a local instance is tried first.

Both instances pin all three universes to the site and to the universe of sections, with no
universe argument left to be solved for. That is what makes them usable in a *named*
declaration about a morphism of ringed topoi. Reaching the same facts through
`CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize` at the use site instead leaves
`CategoryTheory.Limits.PreservesLimitsOfSize` with an unassigned universe argument, and the
`UnivLE` side conditions of the sheafification instances downstream of it are then postponed as
universe constraints that a named declaration cannot discharge when it abstracts its universe
parameters.

**Why `PreservesSheafification` had to be registered.** Three places in this development record
that `J.PreservesSheafification (forget₂ CommRingCat RingCat)` "does not resolve" and exhausts
the `synthInstance` heartbeat budget, and two of them discharge it by naming
`CategoryTheory.GrothendieckTopology.instPreservesSheafification` instead. That failure is one
of search order, not of mathematics, and it is created by a single Mathlib import: adding
`Mathlib.CategoryTheory.Sites.Equivalence` to a file where `infer_instance` succeeds in
milliseconds makes it time out. That module ends with a globally applicable instance deriving
`J.PreservesSheafification F` from
`((equivSmallModel C).inverse.inducedTopology J).PreservesSheafification F`, whose subgoal has
the same head as its conclusion. Search therefore recurses through `equivSmallModel`, and since
the `EssentiallySmall.{w} C` side condition leaves `w` unconstrained by the goal, each level
spends its budget unfolding `SmallModel`, `ShrinkHoms` and `smallCategorySmallModel` and
searching `UnivLE` — which is the `whnf` timeout those notes observed. An instance for this
functor specifically is tried before Mathlib's general one and ends the search at once, so the
three recorded blockers are removed for any module that imports this one.

The size hypothesis is `UnivLE.{max u v, w}` rather than nothing. Unlike the sheaf condition,
which `Stacks.hasSheafCompose_forget₂_commRingCat` obtains from limit preservation alone,
sheafification is built from colimits over the covers of the site, so `CommRingCat.{w}` must
actually admit colimits indexed by `(J.Cover X)ᵒᵖ`. The inequality is the weakest form of that,
and it is implied by `w = max u v w'`; it is supplied the way
`Stacks.ConstantSheaf.preservesColimitsOfShape_forget_addCommGrp_of_univLE` supplies the
corresponding fact for abelian groups.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

/-- The free ring on one generator corepresents the underlying-set functor on rings: a ring
homomorphism out of `FreeRing PUnit` is exactly the image of the generator. -/
noncomputable def RingCat.forgetCorepresentableBy :
    (forget RingCat.{w}).CorepresentableBy (RingCat.of (FreeRing PUnit.{w + 1})) where
  homEquiv :=
    { toFun := fun f ↦ f.hom (FreeRing.of PUnit.unit)
      invFun := fun r ↦ RingCat.ofHom (FreeRing.lift fun _ ↦ r)
      left_inv := by
        intro f
        apply RingCat.hom_ext
        apply FreeRing.hom_ext
        intro x
        cases x
        simp
      right_inv := fun r ↦ FreeRing.lift_of _ _ }
  homEquiv_comp := by intros; rfl

/-- The forgetful functor `RingCat.{w} ⥤ Type w` is corepresentable, by the free ring on one
generator. This is the `RingCat` member of Mathlib's family of corepresentability results for
the forgetful functors of the algebraic categories. -/
instance RingCat.forget_isCorepresentable : (forget RingCat.{w}).IsCorepresentable :=
  RingCat.forgetCorepresentableBy.isCorepresentable

namespace Stacks

/-- On any site, and for any universe of sections, the sheaf condition for `RingCat`-valued
presheaves is preserved by `forget RingCat`. No size hypothesis relating the site to the
universe of sections is needed: the forgetful functor is corepresentable, hence preserves
limits in every size. -/
instance instHasSheafComposeForgetRingCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget RingCat.{w}) :=
  letI : PreservesLimitsOfSize.{v, max u v} (forget RingCat.{w}) := inferInstance
  hasSheafCompose_of_preservesLimitsOfSize J

/-- On any site, and for any universe of sections, the sheaf condition for `CommRingCat`-valued
presheaves is preserved by `forget₂ CommRingCat RingCat`. This is
`Stacks.hasSheafCompose_forget₂_commRingCat`, registered as an instance. -/
instance instHasSheafComposeForget₂CommRingCatRingCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
  hasSheafCompose_forget₂_commRingCat J

/-- **Forgetting commutativity commutes with sheafification**, on every site whose universes the
universe of sections dominates: a morphism of presheaves of commutative rings that becomes an
isomorphism after sheafification still does so after commutativity is forgotten.

Together with `Stacks.hasSheafCompose_forget₂_commRingCat` this is what makes
`CategoryTheory.sheafifyComposeIso` and `CategoryTheory.constantCommuteCompose` available for
`forget₂ CommRingCat RingCat`, i.e. what identifies the sheaf of rings underlying a sheafified
presheaf of commutative rings with the sheafification of the underlying presheaf of rings.

This is Mathlib's instance for a functor between concrete categories preserving the relevant
multicospan limits and cover-indexed colimits, with its size conditions discharged: the two
forgetful functors to `Type` preserve limits and filtered colimits of every size, the covers of
a site form a filtered category, and `UnivLE.{max u v, w}` shrinks all four facts to the size
of the site. See the module's implementation notes for why instance search does not find it on
its own, and why `UnivLE` is needed here when the sheaf condition needs no size hypothesis. -/
theorem preservesSheafification_forget₂_commRingCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [UnivLE.{max u v, w}] :
    J.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w}) :=
  let : HasColimitsOfSize.{max u v, max u v} CommRingCat.{w} :=
    hasColimitsOfSizeOfUnivLE.{w, w} _
  let : HasColimitsOfSize.{max u v, max u v} RingCat.{w} :=
    hasColimitsOfSizeOfUnivLE.{w, w} _
  let : PreservesFilteredColimitsOfSize.{max u v, max u v} (forget CommRingCat.{w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{w, w, max u v, max u v} _
  let : PreservesFilteredColimitsOfSize.{max u v, max u v} (forget RingCat.{w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{w, w, max u v, max u v} _
  let : PreservesFilteredColimitsOfSize.{max u v, max u v}
      (forget₂ CommRingCat.{w} RingCat.{w}) :=
    preservesFilteredColimitsOfSize_of_univLE.{w, w, max u v, max u v} _
  let : PreservesLimitsOfSize.{max u v, max u v} (forget CommRingCat.{w}) :=
    preservesLimitsOfSize_of_univLE.{w, w, max u v, max u v} _
  let : PreservesLimitsOfSize.{max u v, max u v} (forget RingCat.{w}) :=
    preservesLimitsOfSize_of_univLE.{w, w, max u v, max u v} _
  GrothendieckTopology.instPreservesSheafification J _

/-- `Stacks.preservesSheafification_forget₂_commRingCat`, registered as an instance.

This is the declaration that makes `infer_instance` work for
`J.PreservesSheafification (forget₂ CommRingCat RingCat)`: being an instance for this functor
specifically, it is tried before the general one of
`Mathlib.CategoryTheory.Sites.Equivalence` whose self-matching subgoal is what exhausts the
heartbeat budget. -/
instance instPreservesSheafificationForget₂CommRingCatRingCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [UnivLE.{max u v, w}] :
    J.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w}) :=
  preservesSheafification_forget₂_commRingCat J

end Stacks

end
