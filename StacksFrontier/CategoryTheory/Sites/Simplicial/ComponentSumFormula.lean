module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackSumFormula
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentCommaDecomposition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentInclusion

/-!
# The sum formula for lower shriek on a simplicial site (Stacks 09WG)

On a simplicial site, lower shriek from simplicial degree `n`, restricted back to degree `m`, is
the direct sum over the simplex maps `φ : [n] ⟶ [m]` of the inverse images along the transitions.

Both sides of that formula are left adjoints, so it is equivalent to the corresponding product
formula for the right adjoints, which is a statement about a Kan extension along a component
inclusion and involves no sheafification. Pointwise, that Kan extension is a (co)limit over a
comma category of the two component inclusions, and in each of the two cases of the situation
these comma categories are a disjoint union, indexed by the simplex maps, of pieces with a
distinguished object.

The two cases are not symmetric, and this decides which of the two criteria,
`CategoryTheory.Functor.sheafPullbackCompPushforwardIsoCoproductOfRan` or
`CategoryTheory.Functor.sheafPullbackCompPushforwardIsoCoproductOfLan`, applies. In
**case (A)** the pieces of the comma category on the *right* Kan extension side have an initial
object, so the right Kan extension is a product of evaluations and the ran criterion applies; the
proof then never meets sheafification. In **case (B)** it is the pieces on the *left* Kan
extension side that have a terminal object, so the left Kan extension is a coproduct of
evaluations and the lan criterion applies; there the formula is proved on presheaves and pushed
through sheafification.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.transitionInverseImageAb`: inverse image of abelian
  sheaves along a simplicial transition. In case (A) the transition is represented by a
  continuous functor, so this is its sheaf pullback; in case (B) the transition is a cocontinuous
  functor, so this is restriction of presheaves followed by sheafification.

## Main results

* `CategoryTheory.SimplicialSite.componentLowerShriekRestrictionIsoCoproduct` and
  `CategoryTheory.CocontinuousSimplicialSite.componentLowerShriekRestrictionIsoCoproduct`: the
  formula in the two cases.
* `CategoryTheory.SimplicialSiteSituation.componentLowerShriekRestrictionIsoCoproduct`:
  **Stacks 09WG**, the sum formula.

## Implementation notes

Everything is stated through `CategoryTheory.SimplicialSiteSituation.componentFunctor` and
`.componentTopology` rather than through the raw fibre inclusions
`CategoryTheory.Pseudofunctor.CoGrothendieck.ι` and `CategoryTheory.Grothendieck.ι`, because the
continuity and cocontinuity instances are registered for the former and instance search does not
see through to the latter. The two spellings are definitionally equal, so the comma-category
inputs, which are stated for the raw inclusions, transfer by `exact`.

Some instances have to be supplied by hand, because instance search finds the *pointwise* Kan
extension but not the plain one once the situation is a concrete constructor application:
`HasRightKanExtension` along the degree-`m` inclusion in case (A) and `HasLeftKanExtension` along
the degree-`n` inclusion in case (B), each for both spellings of the inclusion. Both follow from
the pointwise version by
`CategoryTheory.Functor.IsPointwiseRightKanExtension.hasRightKanExtension`, resp. its
left-handed counterpart. Continuity of the transition functors in case (A) likewise has
to be passed explicitly, since it comes from the `isMorphismOfSites` field rather than from an
instance.

The coefficients are abelian groups in the universe of the site. The Grothendieck topology of
every component and of the total site then admits a left exact sheafification, by Mathlib's
instance for concrete categories; no separate sheafification hypothesis is needed.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Pseudofunctor Opposite

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) {n m : SimplexCategory}

/-- Inverse image of abelian sheaves along the simplicial transition attached to a simplex map
`φ : [n] ⟶ [m]`.

In case (A) the transition is a morphism of sites represented by a continuous functor
`u φ : C_n ⥤ C_m`, and this is the sheaf pullback along it. In case (B) the transition is a
cocontinuous functor `u φ : C_m ⥤ C_n` and this is restriction of presheaves along it followed by
sheafification. -/
noncomputable def transitionInverseImageAb (φ : n ⟶ m) :
    Sheaf (S.componentTopology n) Ab.{u} ⥤ Sheaf (S.componentTopology m) Ab.{u} :=
  match S with
  | ⟨Sum.inl C⟩ =>
      haveI : ((C.underlying.map φ).toFunctor).IsContinuous
          (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck :=
        (C.isMorphismOfSites φ).isContinuous
      sheafPullbackConstruction.sheafPullback ((C.underlying.map φ).toFunctor) Ab.{u}
        (C.coverage n).toGrothendieck (C.coverage m).toGrothendieck
  | ⟨Sum.inr C⟩ =>
      ((C.underlying.map φ.op).toFunctor).sheafPullbackCocontinuous Ab.{u}
        (topologyOfCoverings (C.coverage (op m))) (topologyOfCoverings (C.coverage (op n)))

end CategoryTheory.SimplicialSiteSituation

namespace CategoryTheory.SimplicialSite

open CategoryTheory.SimplicialSiteSituation in
/-- **Stacks 09WG** in case (A). Lower shriek from simplicial degree `n`, restricted to degree
`m`, is the direct sum over the simplex maps `φ : [n] ⟶ [m]` of the inverse images along the
transitions. -/
noncomputable def componentLowerShriekRestrictionIsoCoproduct
    (C : SimplicialSite.{u}) (n m : SimplexCategory) :
    sheafPullbackConstruction.sheafPullback
        (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology ⋙
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u})
          m).sheafPushforwardContinuous Ab.{u}
        ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).totalTopology ≅
      ∐ fun φ : n ⟶ m =>
        transitionInverseImageAb (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) φ := by
  haveI hcont : ∀ φ : n ⟶ m, ((C.underlying.map φ).toFunctor).IsContinuous
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).componentTopology m) :=
    fun φ => (C.isMorphismOfSites φ).isContinuous
  haveI hranRaw : ∀ G : (C.underlying.obj m)ᵒᵖ ⥤ Ab.{u},
      (CoGrothendieck.ι C.totalPseudofunctor (op m)).op.HasRightKanExtension G :=
    fun G =>
      (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension _ G).hasRightKanExtension
  haveI hran : ∀ G : ((⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}).component m)ᵒᵖ ⥤ Ab.{u},
      (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m).op.HasRightKanExtension G :=
    fun G =>
      (Functor.pointwiseRightKanExtensionIsPointwiseRightKanExtension _ G).hasRightKanExtension
  exact Functor.sheafPullbackCompPushforwardIsoCoproductOfRan (ht := hcont) Ab.{u} _ _ _
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) n)
    (componentFunctor (⟨Sum.inl C⟩ : SimplicialSiteSituation.{u}) m)
    (fun φ : n ⟶ m => (C.underlying.map φ).toFunctor)
    (fun φ => SimplicialSiteSituation.continuousInclusionTransition C φ)
    (fun P U => isLimitFanRanComponent C U P)

end CategoryTheory.SimplicialSite

namespace CategoryTheory.CocontinuousSimplicialSite

open CategoryTheory.SimplicialSiteSituation in
/-- **Stacks 09WG** in case (B). Lower shriek from simplicial degree `n`, restricted to degree
`m`, is the direct sum over the simplex maps `φ : [n] ⟶ [m]` of the inverse images along the
transitions. -/
noncomputable def componentLowerShriekRestrictionIsoCoproduct
    (C : CocontinuousSimplicialSite.{u}) (n m : SimplexCategory) :
    sheafPullbackConstruction.sheafPullback
        (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n) Ab.{u}
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology n)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology ⋙
      (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u})
          m).sheafPushforwardContinuous Ab.{u}
        ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).componentTopology m)
        (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).totalTopology ≅
      ∐ fun φ : n ⟶ m =>
        transitionInverseImageAb (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) φ := by
  haveI hlanRaw : ∀ G : (C.underlying.obj (op n))ᵒᵖ ⥤ Ab.{u},
      (Grothendieck.ι C.underlying (op n)).op.HasLeftKanExtension G :=
    fun G => (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ G).hasLeftKanExtension
  haveI hlan : ∀ G : ((⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}).component n)ᵒᵖ ⥤ Ab.{u},
      (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n).op.HasLeftKanExtension G :=
    fun G => (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ G).hasLeftKanExtension
  exact Functor.sheafPullbackCompPushforwardIsoCoproductOfLan Ab.{u} _ _ _
    (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) n)
    (componentFunctor (⟨Sum.inr C⟩ : SimplicialSiteSituation.{u}) m)
    (fun φ : n ⟶ m => (C.underlying.map φ.op).toFunctor)
    (fun φ => Grothendieck.ιNatTrans (F := C.underlying) φ.op)
    (fun P V => isColimitCofanLanComponent C V P)

end CategoryTheory.CocontinuousSimplicialSite

namespace CategoryTheory.SimplicialSiteSituation

/-- **Stacks 09WG, the abelian sum formula.** On a simplicial site, lower shriek on abelian
sheaves from simplicial degree `n`, restricted back to degree `m`, is naturally the direct sum
over the simplex maps `φ : [n] ⟶ [m]` of the inverse images along the transitions. -/
@[stacks 09WG "abelian_sum_formula"]
noncomputable def componentLowerShriekRestrictionIsoCoproduct
    (S : SimplicialSiteSituation.{u}) (n m : SimplexCategory) :
    sheafPullbackConstruction.sheafPullback (componentFunctor S n) Ab.{u}
        (S.componentTopology n) S.totalTopology ⋙
      (componentFunctor S m).sheafPushforwardContinuous Ab.{u}
        (S.componentTopology m) S.totalTopology ≅
      ∐ fun φ : n ⟶ m => transitionInverseImageAb S φ := by
  obtain ⟨c⟩ := S
  cases c with
  | inl C => exact SimplicialSite.componentLowerShriekRestrictionIsoCoproduct C n m
  | inr C => exact CocontinuousSimplicialSite.componentLowerShriekRestrictionIsoCoproduct C n m

end CategoryTheory.SimplicialSiteSituation

end
