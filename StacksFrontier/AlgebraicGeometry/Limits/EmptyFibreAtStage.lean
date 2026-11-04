module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.LimitUniverse.AffineTransitionLimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Empty base changes and missed points at a finite stage

Let `X = lim Xᵢ` be a cofiltered inverse limit of schemes with affine transition morphisms. A
quasi-compact scheme over a stage `Xⱼ` whose base change to `X` is empty has empty base change
to some stage `Xᵢ` over `Xⱼ` already; consequently a point of `Xⱼ` outside the image of `X` is
outside the image of some `Xᵢ`, and finitely many such points are missed by a single `Xᵢ`.

## Main results

* `AlgebraicGeometry.exists_isEmpty_pullback_map_of_isEmpty_pullback_π_app`: emptiness of a base
  change descends from the limit to a finite stage.
* `AlgebraicGeometry.exists_notMem_range_map_of_notMem_range_π_app`: a point outside the image of
  the limit is outside the image of a finite stage.
* `AlgebraicGeometry.exists_forall_notMem_range_map_of_finite`: one finite stage misses a given
  finite set of points outside the image of the limit.

## Implementation notes

The first statement is the index-universe-independent form of [Stacks, Tag 05F3]: the base
changes of the stages over `j` form a diagram over the category of objects over `j` whose limit
is the base change of the limit, because pulling back along a morphism and the forgetful functor
of an over category both preserve such limits; were all of them nonempty, the limit would be
nonempty by [Stacks, Tag 01Z2].

The statement about a point is the case of the spectrum of the residue field at the point, whose
image is that point. A single stage serves for finitely many points because missing a point is
inherited under precomposition of the transition morphism, and two morphisms to `j` agree after
passing to a later stage.

## References

* [Stacks Project, Tag 01Z2](https://stacks.math.columbia.edu/tag/01Z2)
* [Stacks Project, Tag 05F3](https://stacks.math.columbia.edu/tag/05F3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v uI u

attribute [local instance] CategoryTheory.IsCofiltered.isConnected

namespace AlgebraicGeometry

variable {I : Type uI} [Category.{v} I] [IsCofiltered I] [LocallySmall.{u} I]
  [InitiallySmall.{u} I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (c : Cone D)

/-- If the base change to the limit of a cofiltered inverse system of schemes with affine
transition morphisms of a quasi-compact scheme over a stage is empty, then so is its base change
to some stage over that one. -/
@[ega "IV 8.3.6" "Nontrivial direction"]
theorem exists_isEmpty_pullback_map_of_isEmpty_pullback_π_app (hc : IsLimit c) (j : I)
    {T : Scheme.{u}} [CompactSpace T] (t : T ⟶ D.obj j)
    (hT : IsEmpty (pullback (c.π.app j) t : Scheme.{u})) :
    ∃ (i : I) (g : i ⟶ j), IsEmpty (pullback (D.map g) t : Scheme.{u}) := by
  by_contra hcon
  simp only [not_exists] at hcon
  have hloc : LocallySmall.{u} (Over j) := locallySmall_of_faithful (Over.forget j)
  let F : Over j ⥤ Scheme.{u} := Over.post D ⋙ Over.pullback t ⋙ Over.forget T
  let cF : Cone F := (Over.pullback t ⋙ Over.forget T).mapCone ((Over.conePost D j).obj c)
  have hcF : IsLimit cF :=
    isLimitOfPreserves (Over.pullback t ⋙ Over.forget T) (Over.isLimitConePost j hc)
  have hne : ∀ a : Over j, Nonempty (F.obj a) := fun a ↦
    not_isEmpty_iff.mp (hcon a.left a.hom)
  have haff : ∀ {a b : Over j} (g : a ⟶ b), IsAffineHom (F.map g) := fun g ↦
    MorphismProperty.overPullbackMap t ((Over.post D).map g)
      (show IsAffineHom (D.map g.left) from inferInstance)
  have hcpt : ∀ a : Over j, CompactSpace (F.obj a) := by
    intro a
    exact inferInstanceAs (CompactSpace (pullback (D.map a.hom) t : Scheme.{u}))
  exact hT.false (Scheme.nonempty_of_isLimit_of_initiallySmall F cF hcF).some

/-- A point of a stage of a cofiltered inverse system of schemes with affine transition
morphisms which is not in the image of the limit is not in the image of some stage over it. -/
theorem exists_notMem_range_map_of_notMem_range_π_app (hc : IsLimit c) (j : I) (x : D.obj j)
    (hx : x ∉ Set.range (c.π.app j).base) :
    ∃ (i : I) (g : i ⟶ j), x ∉ Set.range (D.map g).base := by
  obtain ⟨i, g, hg⟩ := exists_isEmpty_pullback_map_of_isEmpty_pullback_π_app D c hc j
    ((D.obj j).fromSpecResidueField x)
    (by simpa [Scheme.isEmpty_pullback_iff, Scheme.range_fromSpecResidueField] using hx)
  exact ⟨i, g, by simpa [Scheme.isEmpty_pullback_iff, Scheme.range_fromSpecResidueField] using hg⟩

omit [IsCofiltered I] [LocallySmall.{u} I] [InitiallySmall.{u} I]
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] in
/-- A point missed by the image of a stage is missed by the image of every stage over it. -/
theorem notMem_range_map_comp {i i' j : I} (g : i ⟶ j) (h : i' ⟶ i) {x : D.obj j}
    (hx : x ∉ Set.range (D.map g).base) : x ∉ Set.range (D.map (h ≫ g)).base := by
  rintro ⟨y, rfl⟩
  exact hx ⟨(D.map h).base y, by simp⟩

/-- A finite set of points of a stage of a cofiltered inverse system of schemes with affine
transition morphisms, none of which is in the image of the limit, is disjoint from the image of
a single stage over it. -/
theorem exists_forall_notMem_range_map_of_finite (hc : IsLimit c) (j : I) {E : Set (D.obj j)}
    (hE : E.Finite) (hx : ∀ x ∈ E, x ∉ Set.range (c.π.app j).base) :
    ∃ (i : I) (g : i ⟶ j), ∀ x ∈ E, x ∉ Set.range (D.map g).base := by
  induction E, hE using Set.Finite.induction_on with
  | empty => exact ⟨j, 𝟙 j, fun x hx ↦ absurd hx (Set.notMem_empty x)⟩
  | @insert a E ha hEfin ih =>
    obtain ⟨i₁, g₁, hg₁⟩ := ih fun y hy ↦ hx y (Set.mem_insert_of_mem a hy)
    obtain ⟨i₂, g₂, hg₂⟩ := exists_notMem_range_map_of_notMem_range_π_app D c hc j a
      (hx a (Set.mem_insert a E))
    obtain ⟨i₃, u, v, -⟩ := IsCofilteredOrEmpty.cone_objs i₁ i₂
    obtain ⟨i₄, w, hw⟩ := IsCofilteredOrEmpty.cone_maps (u ≫ g₁) (v ≫ g₂)
    refine ⟨i₄, w ≫ u ≫ g₁, fun y hy ↦ ?_⟩
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · rw [hw]
      simpa only [Category.assoc] using notMem_range_map_comp D g₂ (w ≫ v) hg₂
    · simpa only [Category.assoc] using notMem_range_map_comp D g₁ (w ≫ u) (hg₁ y hy)

end AlgebraicGeometry

end
