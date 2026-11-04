module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import
  StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVarietyEquivalentDefinitions
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Separated
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Subgroups.Separation

/-!
# An abelian variety from a surjection on rational points

Over an algebraically closed field `K`, a morphism from a proper scheme to a separated scheme
locally of finite type which hits every `K`-rational point is surjective, and its target is then
proper. Applied to a smooth group scheme this gives a criterion for being an abelian variety.

## Main results

* `AlgebraicGeometry.surjective_of_forall_rationalPoint_lift`: the image is closed and contains
  every closed point, all of which are rational, and the target is a Jacobson space.
* `AlgebraicGeometry.isProper_of_forall_rationalPoint_lift`: the target is proper.
* `AlgebraicGeometry.isAbelianVariety_of_forall_rationalPoint_lift`: a smooth group scheme over
  `K` onto whose rational points a connected proper scheme maps is an abelian variety.

## References

* [Stacks Project, Tag 03RO](https://stacks.math.columbia.edu/tag/03RO)
* [Stacks Project, Tag 047L](https://stacks.math.columbia.edu/tag/047L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {K : Type u} [Field K] [IsAlgClosed K]

/-- **A morphism onto a scheme of finite type over an algebraically closed field which hits every
rational point is surjective.** Let `α : Y ⟶ A` be a morphism of schemes over `K`, with `Y`
universally closed over `K`, `A` separated and locally of finite type over `K`. If every
`K`-rational point of `A` lifts to a `K`-rational point of `Y`, then `α` is surjective: its
image is closed, it contains every closed point of `A` because those are rational, and `A` is
a Jacobson space. -/
theorem surjective_of_forall_rationalPoint_lift {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    (q : A ⟶ Spec (.of K)) [UniversallyClosed p] [IsSeparated q] [LocallyOfFiniteType q]
    (α : Y ⟶ A) (hα : α ≫ q = p)
    (h : ∀ a : Spec (.of K) ⟶ A, a ≫ q = 𝟙 _ → ∃ y : Spec (.of K) ⟶ Y, y ≫ α = a) :
    Surjective α := by
  subst hα
  have : UniversallyClosed α := UniversallyClosed.of_comp_of_isSeparated α q
  have := LocallyOfFiniteType.jacobsonSpace q
  have hclosed : IsClosed (Set.range α) := α.isClosedMap.isClosed_range
  refine ⟨fun x => ?_⟩
  by_contra hx
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints (Z := (Set.range α)ᶜ) ⟨x, hx⟩
    hclosed.isOpen_compl.isLocallyClosed
  obtain ⟨y, hy⟩ := h (pointOfClosedPoint q z hzc) (pointOfClosedPoint_comp q z hzc)
  apply hz
  refine ⟨y (IsLocalRing.closedPoint K), ?_⟩
  have h1 := congrArg (fun m => m (IsLocalRing.closedPoint K)) hy
  exact h1.trans (pointOfClosedPoint_apply q z hzc _)

/-- **A proper surjection from a proper scheme makes the target proper.** In the situation of
`AlgebraicGeometry.surjective_of_forall_rationalPoint_lift`, with `Y` proper over `K`, the
target `A` is proper over `K`. -/
theorem isProper_of_forall_rationalPoint_lift {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of K))
    (q : A ⟶ Spec (.of K)) [IsProper p] [IsSeparated q] [LocallyOfFiniteType q]
    (α : Y ⟶ A) (hα : α ≫ q = p)
    (h : ∀ a : Spec (.of K) ⟶ A, a ≫ q = 𝟙 _ → ∃ y : Spec (.of K) ⟶ Y, y ≫ α = a) :
    IsProper q := by
  have hs := surjective_of_forall_rationalPoint_lift p q α hα h
  have := (quasiCompact_iff_compactSpace p).1 inferInstance
  subst hα
  have : UniversallyClosed q := UniversallyClosed.of_comp_surjective α q
  have : CompactSpace A := hs.surj.compactSpace α.continuous
  have : QuasiCompact q := (quasiCompact_iff_compactSpace q).2 inferInstance
  exact ⟨⟩

/-- **A smooth group scheme over an algebraically closed field covered by a connected proper
scheme on rational points is an abelian variety.** Let `A` be a group scheme over `K`, smooth
over `K`, and let `Y` be a connected scheme proper over `K` with a morphism `α : Y ⟶ A` over `K`
through which every `K`-rational point of `A` lifts. Then `A` is an abelian variety: it is
separated, being a group scheme over a field (Tag 047L); proper and connected, because `α` is
surjective; and geometrically reduced, being smooth. -/
theorem isAbelianVariety_of_forall_rationalPoint_lift (A : Grp (Over (Spec (.of K))))
    [Smooth A.X.hom] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of K)) [IsProper p] [ConnectedSpace Y]
    (α : Y ⟶ A.X.left) (hα : α ≫ A.X.hom = p)
    (h : ∀ a : Spec (.of K) ⟶ A.X.left, a ≫ A.X.hom = 𝟙 _ →
      ∃ y : Spec (.of K) ⟶ Y, y ≫ α = a) :
    IsAbelianVariety K A.X := by
  have : IsSeparated A.X.hom := by
    let : GrpObj (Over.mk A.X.hom) :=
      GrpObj.ofIso (show A.X ≅ Over.mk A.X.hom from Over.isoMk (Iso.refl _))
    exact (isSeparated_iff_isClosedImmersion_one A.X.hom).2 inferInstance
  have : IsProper A.X.hom := isProper_of_forall_rationalPoint_lift p A.X.hom α hα h
  have hs := surjective_of_forall_rationalPoint_lift p A.X.hom α hα h
  have : ConnectedSpace A.X.left := hs.surj.connectedSpace α.continuous
  have : GeometricallyReduced A.X.hom := geometricallyReduced_of_smooth A.X.hom
  exact isAbelianVariety_of_isProper_of_connectedSpace_of_geometricallyReduced K A.X

end AlgebraicGeometry
