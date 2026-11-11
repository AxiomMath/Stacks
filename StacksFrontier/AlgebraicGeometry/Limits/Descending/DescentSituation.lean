module

public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.UnderlyingSpace
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Underlying spaces of the limit in the descent situation

In the descent situation for a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, the underlying set and the underlying topological
space of the limiting scheme are the corresponding limits. Moreover a failure of specialization
between two points of the limit is already detected at some stage of the inverse system.

The equalities with limits are expressed by saying that the canonical cones obtained from the
chosen scheme limit cone are limiting; this retains the projections and all their naturality.
The specialization assertion uses Mathlib's `Specializes`, so `Specializes s s'` means that `s'`
lies in the closure of `s`.

## Main definitions

* `AlgebraicGeometry.SmallDescentSituation`: Situation 086P, the descent situation whose
  directed index set is small in the universe of the schemes.

## Main results

* `AlgebraicGeometry.nonempty_isLimit_forget_mapCone`: the underlying-set cone is a limit cone.
* `AlgebraicGeometry.nonempty_isLimit_forgetToTop_mapCone`: the underlying topological-space cone
  is a limit cone.
* `AlgebraicGeometry.exists_not_specializes_map_of_not_specializes`: a failure of specialization
  is detected at one stage.

## Implementation notes

The index type is only assumed `Small` in the scheme universe, as required for the ring colimits
used in the construction of the limit; the index and scheme universes stay independent, and
`Small` allows reindexing in the scheme universe without demanding that the given index type
live there.

## References

* [Stacks Project, Tag 01YY](https://stacks.math.columbia.edu/tag/01YY)
* [Stacks Project, Tag 086P](https://stacks.math.columbia.edu/tag/086P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace AlgebraicGeometry

/-- **Situation 086P.** A directed inverse system `(S_i)_{i ∈ I}` of quasi-compact and
quasi-separated schemes with affine transition morphisms, indexed by a directed *set* `I`,
together with its limit `S = lim S_i`, the projections `f_i : S ⟶ S_i`, and a chosen element
`0 ∈ I`.

The source's directed set is a set, which here means that the index preorder is `u`-small,
`u` being the universe of the schemes: the field `small`. For such an index the limit of
Stacks 01YX, glued from the affine-locally computed limits, is the categorical limit in
`Scheme.{u}`, and the chosen limit cone of the underlying
`AlgebraicGeometry.DescentSituation` records it with its projections. Without the bound the
categorical limit in `Scheme.{u}` of a large system need not be that scheme; see
`StacksFrontier/AlgebraicGeometry/SmallnessNecessary/Basic.lean`. Nonemptiness of `I` is
witnessed by the chosen element `base`. -/
@[stacks 086P]
structure SmallDescentSituation (I : Type v) [Preorder I] [IsDirected I (· ≤ ·)]
    extends DescentSituation.{v, u} I where
  /-- The directed index set is a set: it is small in the universe of the schemes. -/
  small : Small.{u} I

/-- A functor out of schemes that preserves all cofiltered limits with affine transition
morphisms indexed in the scheme universe preserves them for any index category that is small in
and locally small over that universe. -/
private theorem preservesLimit_of_small_index
    {C : Type w} [Category C] (G : Scheme.{u} ⥤ C)
    (h : ∀ {K : Type u} [Category.{u} K] [IsCofiltered K]
      (F : K ⥤ Scheme.{u}) [∀ {i j : K} (f : i ⟶ j), IsAffineHom (F.map f)],
      PreservesLimit F G)
    {J : Type v} [Small.{u} J] [Category.{v} J] [LocallySmall.{u} J]
    [IsCofiltered J] (F : J ⥤ Scheme.{u})
    [∀ {i j : J} (f : i ⟶ j), IsAffineHom (F.map f)] :
    PreservesLimit F G := by
  have : Small.{u} (ShrinkHoms J) := by
    change Small.{u} J
    infer_instance
  let E := (ShrinkHoms.equivalence J).trans (Shrink.equivalence.{u} (ShrinkHoms J))
  let F' : Shrink.{u} (ShrinkHoms J) ⥤ Scheme.{u} := E.inverse ⋙ F
  have : IsCofiltered (Shrink.{u} (ShrinkHoms J)) := IsCofiltered.of_equivalence E
  have : ∀ {i j : Shrink.{u} (ShrinkHoms J)} (f : i ⟶ j), IsAffineHom (F'.map f) := by
    intro i j f
    dsimp only [F', Functor.comp_map]
    infer_instance
  have : PreservesLimit F' G := h F'
  have : PreservesLimit (E.functor ⋙ F') G := inferInstance
  exact preservesLimit_of_iso_diagram G (E.funInvIdAssoc F)

/-- A point specializes to another as soon as it does so in every space inducing the topology. -/
private theorem specializes_of_induced_iInf
    {α : Type u} {ι : Type v} {β : ι → Type*}
    [∀ i, TopologicalSpace (β i)] [t : TopologicalSpace α]
    (f : ∀ i, α → β i)
    (ht : t = ⨅ i, TopologicalSpace.induced (f i) (inferInstance : TopologicalSpace (β i)))
    {x y : α} (hxy : ∀ i, Specializes (f i x) (f i y)) :
    Specializes x y := by
  rw [specializes_iff_pure, ht, nhds_iInf]
  exact le_iInf fun i => by
    simpa only [nhds_induced] using
      (Filter.map_le_iff_le_comap).mp (specializes_iff_pure.mp (hxy i))

/-- A functor out of schemes that preserves cofiltered limits with affine transition morphisms
sends the chosen limit cone of a descent situation to a limit cone. -/
private theorem nonempty_isLimit_mapCone_of_preservesLimit
    {C : Type w} [Category C] (G : Scheme.{u} ⥤ C)
    (h : ∀ {K : Type u} [Category.{u} K] [IsCofiltered K]
      (F : K ⥤ Scheme.{u}) [∀ {i j : K} (f : i ⟶ j), IsAffineHom (F.map f)],
      PreservesLimit F G)
    {I : Type v} [Small.{u} I] [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation.{v, u} I) :
    Nonempty (IsLimit (G.mapCone D.limitCone)) := by
  have : Nonempty I := ⟨D.base⟩
  have : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.system.map f) := D.transition_affine
  have := preservesLimit_of_small_index G h D.system
  exact ⟨isLimitOfPreserves G D.isLimit⟩

/-- **Stacks Project, Tag 01YY, part (1).** The underlying-set cone of the chosen limit in the
descent situation is a limit cone. -/
@[stacks 01YY "part (1)"]
theorem nonempty_isLimit_forget_mapCone
    {I : Type v} [Small.{u} I] [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation.{v, u} I) :
    Nonempty (IsLimit (Scheme.forget.mapCone D.limitCone)) :=
  nonempty_isLimit_mapCone_of_preservesLimit Scheme.forget
    preservesLimit_forget_of_isCofiltered_of_isAffineHom D

/-- **Stacks Project, Tag 01YY, part (2).** The underlying topological-space cone of the chosen
limit in the descent situation is a limit cone. -/
@[stacks 01YY "part (2)"]
theorem nonempty_isLimit_forgetToTop_mapCone
    {I : Type v} [Small.{u} I] [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation.{v, u} I) :
    Nonempty (IsLimit (Scheme.forgetToTop.mapCone D.limitCone)) :=
  nonempty_isLimit_mapCone_of_preservesLimit Scheme.forgetToTop
    preservesLimit_forgetToTop_of_isCofiltered_of_isAffineHom D

/-- **Stacks Project, Tag 01YY, part (3).** If one point of the limiting scheme does not
specialize to another, this failure is detected after projection to one of the schemes in the
inverse system. -/
@[stacks 01YY "part (3)"]
theorem exists_not_specializes_map_of_not_specializes
    {I : Type v} [Small.{u} I] [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation.{v, u} I)
    (s s' : D.limitCone.pt) (h : ¬Specializes s s') :
    ∃ i : I, ¬Specializes
      (D.limitCone.π.app (Opposite.op i) s)
      (D.limitCone.π.app (Opposite.op i) s') := by
  have ht := TopCat.induced_of_isLimit (Scheme.forgetToTop.mapCone D.limitCone)
    (nonempty_isLimit_forgetToTop_mapCone D).some
  change (inferInstance : TopologicalSpace D.limitCone.pt) =
    ⨅ i : Iᵒᵖ, TopologicalSpace.induced
      (D.limitCone.π.app i : D.limitCone.pt → D.system.obj i)
      (inferInstance : TopologicalSpace (D.system.obj i)) at ht
  by_contra! hn
  exact h (specializes_of_induced_iInf
    (fun i : Iᵒᵖ => (D.limitCone.π.app i : D.limitCone.pt → D.system.obj i))
    ht fun i => hn i.unop)

end AlgebraicGeometry

end
