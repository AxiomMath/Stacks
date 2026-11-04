module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AbstractGroupQuotientStackIsStack
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SmallSections

/-!
# The total space of a torsor under the constant sheaf lives in the value universe of the site

The algebraicity statement for torsors under the constant sheaf,
`AlgebraicGeometry.AbstractGroupQuotientStack.IsAlgebraicTotalSpaceOfConstantSheafTorsor`, is
stated at the value universe `max t (u + 1)` that the torsors of the triples force, whereas the
descent criterion of Stacks 046J,
`AlgebraicGeometry.Space.relativelyRepresentable_of_isPullback_of_flat_surjective`, is stated
for presheaves of `Type u`. This file shows that the difference is one of rendering and not of
content: the total space of a torsor under a sheaf of groups whose own sections are `u`-small is
pointwise `u`-small, so it is the universe lift of a presheaf of `Type u`, and the large-valued
algebraic-space condition on it is *equivalent* to the `Type u`-valued condition on that
presheaf.

The smallness comes from the torsor axiom rather than from any property of the site: on an
object over which the torsor has a section, acting on that section is a *bijection* from the
sections of the group, which is `PseudoTorsor.sectionEquivGroup`, and over an object where it
has none there is nothing to bound. So the sections of a pseudo-torsor are never larger than the
sections of the group acting on it, with no local triviality and no representability used.

## Main results

* `PseudoTorsor.small_presheaf_obj_of_small`: the sections of a pseudo-torsor over an object
  are `u`-small as soon as the sections of the acting sheaf of groups over that object are.
  This refines `PseudoTorsor.small_presheaf_obj`, which bounds them by the universe of the
  sections of the group, to the value universe of the site.
* `AlgebraicGeometry.AbstractGroupQuotientStack.small_totalPresheaf`: the total space of a
  torsor is pointwise `u`-small as soon as the acting sheaf of groups is.
* `AlgebraicGeometry.AbstractGroupQuotientStack.isAlgebraicSpaceULift_totalPresheaf_iff`:
  **the universe bridge.** For such a torsor the large-valued algebraic-space condition on the
  total space holds exactly when the `Type u`-valued one holds of its shrinking, which is the
  form Stacks 046J can be applied in.

## References

* [Stacks Project, Tag 0371](https://stacks.math.columbia.edu/tag/0371)
* [Stacks Project, Tag 046J](https://stacks.math.columbia.edu/tag/046J)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe t₀ w₀ v₀ u₀ t z w u

/-- **The sections of a pseudo-torsor are `u`-small as soon as the sections of the group
are.** `PseudoTorsor.small_presheaf_obj` bounds them by the universe of the sections of the
sheaf of groups; this refines that bound to any universe in which those sections are small,
which is what the value universe of the site needs. The bijection is
`PseudoTorsor.sectionEquivGroup`, and over an object carrying no section there is nothing to
bound. -/
public theorem PseudoTorsor.small_presheaf_obj_of_small {C : Type u₀} [Category.{v₀} C]
    {J : GrothendieckTopology C} {𝒢 : SheafOfGroups.{w₀} (C := C) J}
    (F : PseudoTorsor.{t₀} 𝒢) (V : Cᵒᵖ) [Small.{u} (𝒢.presheaf.obj V)] :
    Small.{u} (F.presheaf.obj V) := by
  by_cases h : Nonempty (F.presheaf.obj V)
  · exact small_map (F.sectionEquivGroup V h.some).symm
  · exact small_of_injective (β := 𝒢.presheaf.obj V) (f := fun x => (h ⟨x⟩).elim)
      fun x _ _ => (h ⟨x⟩).elim

namespace AlgebraicGeometry

/-- A presheaf is an algebraic space in the large value universe exactly when any presheaf of
`Type u` whose universe lift is isomorphic to it is. -/
private theorem isAlgebraicSpaceULift_iff_of_iso_comp_uliftFunctor
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max t u)}
    (e : F ⋙ uliftFunctor.{t} ≅ G) :
    Space.IsAlgebraicSpaceULift.{t} B S hS G ↔ IsAlgebraicSpace B S hS F :=
  ⟨fun h => (Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F).mp
      (Space.isAlgebraicSpaceULift_of_iso B S hS e.symm h),
    fun h => Space.isAlgebraicSpaceULift_of_iso B S hS e
      ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS F).mpr h)⟩

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {G : Type w} [Group G]
  [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{w}]

namespace AbstractGroupQuotientStack

/-- **The total space of a torsor is pointwise `u`-small** as soon as the acting sheaf of
groups is. A section of the total space over `V` is a morphism `V ⟶ U` of the site together
with a section of the torsor, and the morphisms of the site already lie in the value universe
of the site. -/
public theorem small_totalPresheaf
    (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    (h𝒢 : FunctorToTypes.Small.{u} (bigConstantGroupSheaf B S hS G).presheaf) :
    FunctorToTypes.Small.{u} (totalPresheaf T) := by
  intro V
  have hfib : ∀ a : V.unop ⟶ T.base,
      Small.{u} (T.torsor.presheaf.obj (op (Over.mk a))) := fun a =>
    have : Small.{u} (((bigConstantGroupSheaf B S hS G).over T.base).presheaf.obj
        (op (Over.mk a))) := h𝒢 (op V.unop)
    T.torsor.small_presheaf_obj_of_small _
  exact inferInstanceAs (Small.{u} ((a : V.unop ⟶ T.base) × _))

/-- **The universe bridge for the goal of the last clause of Stacks 0371.** For a torsor whose
acting sheaf of groups has `u`-small sections, the large-valued algebraic-space condition on the
total space is equivalent to the `Type u`-valued condition on its shrinking. The right-hand side
is the shape in which Stacks 046J,
`AlgebraicGeometry.Space.relativelyRepresentable_of_isPullback_of_flat_surjective`, applies, so
no large-valued counterpart of that criterion is needed to reach the goal. -/
public theorem isAlgebraicSpaceULift_totalPresheaf_iff
    (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    [FunctorToTypes.Small.{u} (totalPresheaf T)] :
    Space.IsAlgebraicSpaceULift.{t} B S hS (totalPresheaf T) ↔
      IsAlgebraicSpace B S hS (FunctorToTypes.shrink.{u} (totalPresheaf T)) :=
  isAlgebraicSpaceULift_iff_of_iso_comp_uliftFunctor (Space.shrinkCompUliftFunctorIso _)

/-- **The bridge in the form an application of Stacks 046J consumes.** A presheaf of `Type u`
which is an algebraic space over `S` and whose universe lift is the total space of the torsor
makes that total space an algebraic space in the large value universe. Nothing about the torsor
enters: this is `AlgebraicGeometry.Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff` transported
along the isomorphism, recorded here because producing the pair `(F, e)` from
`AlgebraicGeometry.AbstractGroupQuotientStack.small_totalPresheaf` is all that the value
universe of the goal costs. -/
public theorem isAlgebraicSpaceULift_totalPresheaf_of_isAlgebraicSpace
    (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (e : F ⋙ uliftFunctor.{t} ≅ totalPresheaf T) :
    Space.IsAlgebraicSpaceULift.{t} B S hS (totalPresheaf T) :=
  (isAlgebraicSpaceULift_iff_of_iso_comp_uliftFunctor e).mpr hF

/-- The pair `(F, e)` that `isAlgebraicSpaceULift_totalPresheaf_of_isAlgebraicSpace` asks for
always exists when the acting sheaf of groups has `u`-small sections: take the shrinking of the
total space. -/
public theorem exists_comp_uliftFunctor_iso_totalPresheaf
    (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS G))
    (h𝒢 : FunctorToTypes.Small.{u} (bigConstantGroupSheaf B S hS G).presheaf) :
    ∃ F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u, Nonempty (F ⋙ uliftFunctor.{t} ≅ totalPresheaf T) :=
  have := small_totalPresheaf T h𝒢
  ⟨FunctorToTypes.shrink.{u} (totalPresheaf T),
    ⟨Space.shrinkCompUliftFunctorIso (totalPresheaf T)⟩⟩

/-! ### The constant sheaf satisfies the smallness hypothesis

So the bridge above is unconditional for the sheaf the clause is about: nothing beyond the
source's own cardinality bound is assumed. -/

/-- **The constant sheaf of groups has `u`-small sections**, under the source's cardinality
bound. Its sections over an object are the points of the constant group scheme `G_S` there, by
`AlgebraicGeometry.constantGroupSheafRepresentedByConstantGroupScheme_bigFppf`, which is clause
(5) of Stacks 0371; and the points of a scheme over `S` on an object of the site form a hom-set
of `Scheme.{u}`, so they already lie in the value universe of the site. -/
public theorem small_bigConstantGroupSheaf (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (Gabs : Type (max (u + 1) z)) [Small.{u} Gabs] [Group Gabs]
    [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{max (u + 1) z}] :
    FunctorToTypes.Small.{u} (bigConstantGroupSheaf B S hS Gabs).presheaf := by
  obtain ⟨hws, e, -⟩ :=
    constantGroupSheafRepresentedByConstantGroupScheme_bigFppf.{u, z} B S hS Gabs
  intro T
  refine @small_map _ _ ?_ ((CategoryTheory.forget GrpCat.{max (u + 1) z}).mapIso (e.app T)).toEquiv
  exact small_map (Equiv.ulift.{max (u + 1) z}
    (α := ((Over.post (X := B.obj hS) B.inclusion).obj T.unop ⟶
      (constantGroupScheme Gabs S).X)))

/-- The total space of a torsor under the constant sheaf of groups is pointwise `u`-small, with
no hypothesis beyond the source's cardinality bound. -/
public theorem small_totalPresheaf_bigConstantGroupSheaf {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {Gabs : Type (max (u + 1) z)} [Small.{u} Gabs] [Group Gabs]
    [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{max (u + 1) z}]
    (T : SheafOfGroups.Torsors.{t} (bigConstantGroupSheaf B S hS Gabs)) :
    FunctorToTypes.Small.{u} (totalPresheaf T) :=
  small_totalPresheaf T (small_bigConstantGroupSheaf B S hS Gabs)

/-- **The goal of the last clause of Stacks 0371 is equivalent to a `Type u`-valued statement**,
with no hypothesis beyond the source's cardinality bound `Small.{u} Gabs`. This is an
equivalence and not a reduction: the large value universe of
`AlgebraicGeometry.AbstractGroupQuotientStack.IsAlgebraicTotalSpaceOfConstantSheafTorsor` costs
nothing, and what remains to prove is exactly the `Type u`-valued right-hand side, which is the
shape Stacks 046J applies in. -/
public theorem isAlgebraicTotalSpaceOfConstantSheafTorsor_iff {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} {Gabs : Type (max (u + 1) z)} [Small.{u} Gabs]
    [Group Gabs] [HasWeakSheafify (BigFppfOver.topology B S hS) GrpCat.{max (u + 1) z}] :
    IsAlgebraicTotalSpaceOfConstantSheafTorsor.{t} (B := B) (S := S) (hS := hS) (G := Gabs) ↔
      ∀ T : SheafOfGroups.Torsors.{max t (u + 1)} (bigConstantGroupSheaf B S hS Gabs),
        haveI := small_totalPresheaf_bigConstantGroupSheaf T
        IsAlgebraicSpace B S hS (FunctorToTypes.shrink.{u} (totalPresheaf T)) := by
  refine forall_congr' fun T => ?_
  have := small_totalPresheaf_bigConstantGroupSheaf T
  exact isAlgebraicSpaceULift_totalPresheaf_iff T

end AbstractGroupQuotientStack

end AlgebraicGeometry

end
