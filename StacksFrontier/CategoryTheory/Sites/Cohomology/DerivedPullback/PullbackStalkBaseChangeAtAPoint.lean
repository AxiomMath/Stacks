module

public import Mathlib.CategoryTheory.Sites.Point.OfIsCofiltered
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackWithEnoughPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a module pullback at a point, for a morphism presented by a continuous functor

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi presented by a continuous
functor `u : C' ⥤ C` of the underlying sites, and let `Φ` be a point of `C`. Stacks 05V5
computes the stalk at `Φ` of the pullback `f^*K` of a complex of `O'`-modules as the base
change of the stalk complex of `K` at the point `q = f ∘ Φ` of `C'` along the induced map of
stalk rings `O'_q ⟶ O_Φ`. The weakest form of that computation asks only that *some* point of
`C'` and *some* ring homomorphism carry the comparison.

Even in that weakest form the computation entails the transport of a point of the source site
to a point of the target site, and for a merely continuous `u` no such transport exists: the
site with no objects carries the trivial topology, and every functor out of it is continuous,
so there is a morphism of ringed topoi from the ringed point to a ringed topos whose site has
no points at all. Over that morphism the weakest form of Stacks 05V5 fails, since the point of
the target site it asks for does not exist. The computation therefore needs more of `u` than
continuity, and Stacks 05V5 holds for a morphism of *sites*, whose inverse image on sheaves is
required to be exact.

## Main results

All of the following live in the namespace
`Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints`.

* `nonempty_point_of_pullbackStalkBaseChange`: the comparison at the level of complexes
  transports points — if it holds and the source site has a point, the target site has a point.
* `not_pullbackStalkBaseChange_of_isEmpty_point`: consequently it fails whenever the source
  site has a point and the target site has none.
* `isEmpty_point_pointlessSite`: the site with no objects has no points, its topology being the
  trivial one.
* `not_pullbackStalkBaseChange_toPointlessTopos`: the comparison fails for the morphism of
  ringed topoi from the ringed point over a commutative ring to the ringed topos on the site
  with no objects.

## Implementation notes

**The transport of points is the whole obstruction to the existential form.** A point of a
site is a fibre functor with cofiltered category of elements whose covering sieves are jointly
surjective, and the two transports of such data available are along a representably flat
cover-preserving functor and along a cocontinuous one. Continuity of `u` alone gives the
covering condition on the composite fibre functor `u ⋙ Φ.fiber` — the sheaf condition for the
skyscrapers of `Φ` says exactly that `Φ.fiber` applied to a covering sieve is jointly
surjective — but not the cofilteredness of its category of elements, which is where
representable flatness enters. Cofilteredness fails already for a two-object discrete target
site mapping to the site of the point: there the category of elements of `u ⋙ Φ.fiber` is
discrete with two objects.

**Pointlessness of the target is not the only failure.** For that two-object discrete target
site with the trivial topology the target *does* have points: a fibre functor with cofiltered
category of elements on a discrete category has exactly one element in all, so the points are
the two fibre functors supported at one object. The comparison fails all the same. The
pushforward along `u` is the diagonal `N ↦ (N, N)`, so its left adjoint carries the structure
sheaf `(O', O')` to the direct sum `O ⊕ O`; the stalk of the pullback of the structure sheaf is
therefore free of rank two over the stalk of `O`, while the stalk complex at either point of
the target is free of rank one and stays free of rank one after any extension of scalars. Over
a nonzero commutative ring those are not isomorphic. The failure in both cases is the same
one — the inverse image along a merely continuous functor need not be exact, and
`u ⋙ Φ.fiber` need not be a point.

**The shape of the positive statement.** For a morphism of sites the composite of the ringed
point over `Φ` with `f` is a morphism of ringed topoi, and the comparison is the instance over
that composite of the formula of Stacks 05V5 for a commuting square of morphisms of ringed
topoi, `AlgebraicGeometry.RingedToposHom.pullbackModulesSquareIso`, together with the
identification of the pullback of modules to a ringed point with the module-valued stalk,
`Stacks.Sheaves.RingedPoint.RingedPointSituation.pullbackStalkIso`. The point of the target
site is then named rather than merely asserted to exist, either as the transport
`Φ.comap f.u` of Stacks 05V1 or as the point of the site underlying the composite point of the
topos.

**The trivial topology.** The two ringed topoi used here carry the trivial topology `⊥`, for
which every presheaf is a sheaf (`CategoryTheory.Presheaf.isSheaf_bot`). That makes every
functor out of such a site continuous (`isContinuous_bot`), and it makes the point of the site
of the point immediate from `CategoryTheory.GrothendieckTopology.Point.ofIsCofiltered`, since
the only covering sieve is the maximal one.

## References

* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
* [Stacks Project, Tag 00Y5](https://stacks.math.columbia.edu/tag/00Y5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints

/-! ### The comparison at a point transports points -/

section Transport

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasWeakSheafify X.J AddCommGrpCat] in
/-- **Stacks 05V5 at the level of complexes transports points.** If the stalk complex at a
point `Φ` of the source site of every degreewise pullback is an extension of scalars of a
stalk complex on the target, then the target site has a point: the zero complex already
demands one.

Only the existence of the point is used, not the comparison itself, so this is the weakest
consequence of the comparison. -/
theorem nonempty_point_of_pullbackStalkBaseChange (f : AlgebraicGeometry.RingedToposSiteHom X Y)
    (h : PullbackStalkBaseChange f) (Φ : X.J.Point.{u}) : Nonempty Y.J.Point.{u} := by
  let _ := HasZeroObject.zero'
    (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
  obtain ⟨Ψ, -⟩ := h Φ 0
  exact ⟨Ψ⟩

omit [HasWeakSheafify X.J AddCommGrpCat] in
/-- **The comparison fails over a pointless target.** If the source site has a point and the
target site has none, then the stalk complex of a degreewise pullback is not an extension of
scalars of any stalk complex on the target, for want of a point of the target. -/
theorem not_pullbackStalkBaseChange_of_isEmpty_point
    (f : AlgebraicGeometry.RingedToposSiteHom X Y) (Φ : X.J.Point.{u})
    (hY : IsEmpty Y.J.Point.{u}) : ¬ PullbackStalkBaseChange f :=
  fun h ↦ hY.elim (nonempty_point_of_pullbackStalkBaseChange f h Φ).some

end Transport

/-! ### The site with no objects, and the ringed topos on it -/

/-- The site with no objects, in prescribed universes: the universes of its objects and of its
morphisms are free, as they are for the site of the point, so that the ringed topos on it lives
in the same universes as any other ringed topos. -/
abbrev PointlessSite := ULiftHom.{u} (ULift.{u} (Discrete PEmpty.{1}))

/-- The category structure on the universe lift of the empty discrete category. -/
instance pointlessSiteInnerCategory : Category.{0, u} (ULift.{u} (Discrete PEmpty.{1})) :=
  uliftCategory (Discrete PEmpty.{1})

/-- The category structure on `PointlessSite`, with morphisms in universe `u`. -/
instance pointlessSiteCategory : Category.{u, u} PointlessSite.{u} :=
  ULiftHom.category

/-- `PointlessSite` has no objects. -/
instance isEmptyPointlessSite : IsEmpty PointlessSite.{u} :=
  ⟨fun Z ↦ (ULiftHom.objDown Z).down.as.elim⟩

/-- The opposite of `PointlessSite` has no objects. -/
instance isEmptyPointlessSiteOp : IsEmpty (PointlessSite.{u}ᵒᵖ) :=
  ⟨fun Z ↦ isEmptyElim Z.unop⟩

/-- A functor out of a category with no objects, into any category. -/
def fromIsEmpty (C : Type*) [Category C] [IsEmpty C] (D : Type*) [Category D] : C ⥤ D where
  obj Z := isEmptyElim Z
  map {Z} _ := isEmptyElim Z
  map_id Z := (IsEmpty.false Z).elim
  map_comp {Z} _ _ := (IsEmpty.false Z).elim

/-- A morphism between two functors out of a category with no objects. -/
def homFromIsEmpty {C : Type*} [Category C] [IsEmpty C] {D : Type*} [Category D] (F G : C ⥤ D) :
    F ⟶ G where
  app Z := isEmptyElim Z
  naturality {Z} _ _ := (IsEmpty.false Z).elim

/-- Every functor out of a site carrying the trivial topology is continuous, since for the
trivial topology every presheaf is a sheaf. -/
instance isContinuous_bot {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    (F : C ⥤ D) (K : GrothendieckTopology D) : F.IsContinuous (⊥ : GrothendieckTopology C) K where
  op_comp_isSheaf_of_types _ := by
    rw [← isSheaf_iff_isSheaf_of_type]
    exact Presheaf.isSheaf_bot _

/-- **The site with no objects has no points.** The category of elements of a fibre functor on
it is empty, whereas the category of elements of a point is cofiltered and in particular
nonempty. -/
instance isEmpty_point_pointlessSite :
    IsEmpty ((⊥ : GrothendieckTopology PointlessSite.{u}).Point.{u}) := by
  refine ⟨fun Ψ ↦ ?_⟩
  obtain ⟨⟨Z, _⟩⟩ := IsCofiltered.nonempty (C := Ψ.fiber.Elements)
  exact isEmptyElim Z

/-- The ringed topos on the site with no objects: its topos is the trivial topos, with one
object and one morphism, and its structure sheaf is the unique presheaf of commutative rings
on the empty site. -/
@[sga "4 IV 4.4"]
abbrev pointlessTopos : AlgebraicGeometry.RingedTopos.{u, u, u} where
  C := PointlessSite.{u}
  J := ⊥
  O := ⟨fromIsEmpty _ CommRingCat.{u}, Presheaf.isSheaf_bot _⟩

/-! ### The ringed point, and the morphism from it to the pointless ringed topos -/

/-- The ringed point over a commutative ring `R`: the site of the point with the trivial
topology, carrying the constant sheaf `R`. -/
abbrev ringedPoint (R : CommRingCat.{u}) : AlgebraicGeometry.RingedTopos.{u, u, u} where
  C := Stacks.Sheaves.RingedPoint.PointSite.{u, u}
  J := ⊥
  O := ⟨(Functor.const _).obj R, Presheaf.isSheaf_bot _⟩

/-- The unique object of the site of the point. -/
def pointSiteObj : Stacks.Sheaves.RingedPoint.PointSite.{u, u} :=
  ULiftHom.objUp (ULift.up (Discrete.mk PUnit.unit))

/-- **The point of the site of the point.** Its fibre functor is the one attached to the
functor from the one-object category picking out the unique object of the site; the covering
condition is immediate because the only covering sieve for the trivial topology is the maximal
one. -/
def pointSitePoint :
    (⊥ : GrothendieckTopology (Stacks.Sheaves.RingedPoint.PointSite.{u, u})).Point.{u} :=
  GrothendieckTopology.Point.ofIsCofiltered.{u} (N := Discrete PUnit.{1})
    ((Functor.const _).obj pointSiteObj.{u}) <| by
      intro Z R hR U g
      obtain rfl : R = ⊤ := hR
      exact ⟨Z, 𝟙 Z, trivial, U, 𝟙 U, g, by simp⟩

/-- **The morphism of ringed topoi from the ringed point to the pointless ringed topos.** Its
underlying functor of sites is the functor out of the site with no objects, which is continuous
because that site carries the trivial topology, and its structure map is the unique morphism of
sheaves of commutative rings on the empty site. -/
def toPointlessTopos (R : CommRingCat.{u}) :
    AlgebraicGeometry.RingedToposSiteHom (ringedPoint R) pointlessTopos.{u} where
  u := fromIsEmpty _ _
  fSharp := ⟨homFromIsEmpty _ _⟩

/-- **The weakest form of Stacks 05V5 at the level of complexes is not inhabited.** For the
morphism of ringed topoi from the ringed point over `R` to the ringed topos on the site with no
objects, the stalk complex of a degreewise pullback is not an extension of scalars of any stalk
complex on the target: the target site has no points.

The underlying functor of sites of this morphism is continuous but is not a morphism of sites,
its inverse image on sheaves carrying the final object of the trivial topos to the initial
object rather than the final one. Stacks 05V5 is a statement about a morphism of sites, and
this is the sense in which continuity alone is too weak for it. -/
theorem not_pullbackStalkBaseChange_toPointlessTopos (R : CommRingCat.{u}) :
    ¬ PullbackStalkBaseChange (toPointlessTopos R) :=
  not_pullbackStalkBaseChange_of_isEmpty_point.{u} (toPointlessTopos R) pointSitePoint.{u}
    isEmpty_point_pointlessSite

end Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints

end

end
