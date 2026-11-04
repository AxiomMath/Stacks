module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Stability properties of the étale coverings of algebraic spaces

An étale covering of an algebraic space over a scheme is a family of étale morphisms of
algebraic spaces whose images jointly cover its points; that condition,
`AlgebraicGeometry.Space.IsEtaleCovering` (**Stacks 041E**), is declared in
`StacksFrontier.AlgebraicGeometry.Spaces.Coverings` alongside the four other covering
conditions of Stacks 03YH. This module proves the three axioms a collection of covering
families must satisfy to present a topology: a singleton family on an isomorphism is a
covering, the composites of a family of étale coverings over the members of an étale
covering form an étale covering of the original algebraic space, and the base change of an
étale covering along any morphism of algebraic spaces is an étale covering.

## Main results

* `AlgebraicGeometry.Space.isEtaleCovering_comp`: **Stacks 041F**, a dependent family of
  étale coverings composes to an étale covering.
* `AlgebraicGeometry.Space.isEtaleCovering_pullback`: **Stacks 041F**, the base-change
  clause.
* `AlgebraicGeometry.Space.isEtaleCovering_of_isIso`: **Stacks 041F**, the isomorphism
  clause.

## Implementation notes

Algebraic spaces are presheaves on the chosen big fppf site satisfying
`AlgebraicGeometry.IsAlgebraicSpace`, and their morphisms are natural transformations. The
union of images in the source is expressed as the union of ranges of the induced maps on
`AlgebraicGeometry.Space.points`. The composite family is indexed by the dependent sum of
the indexing types and its maps are composites of natural transformations.

The base-change clause is stated for the presheaf fibre product and its first projection,
which is what a consumer forming the fibre product by hand has; the proof bundles the three
presheaves with their algebraicity, so that the cartesian square of Stacks 02X2 and the
base-change stability of étaleness (Stacks 03FU) apply to it, and the joint-surjectivity
clause is Stacks 03H4.

The joint-surjectivity ingredient of the isomorphism clause, shared by all five covering
notions of Stacks 03YH, is `AlgebraicGeometry.Space.pointsMap_surjective_of_isIso` in
`StacksFrontier.AlgebraicGeometry.Spaces.CoproductClopenSubspaces`.

## References

* [Stacks Project, Tag 041F](https://stacks.math.columbia.edu/tag/041F)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Space

/-- Every point of the target of an étale covering is the image of a point of some member. -/
private theorem IsEtaleCovering.exists_pointsMap_eq
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {I : Type v}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Y : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, Y i ⟶ X} (h : IsEtaleCovering B S hS Y f) (p : points B S hS X) :
    ∃ i q, pointsMap B S hS (Y i) (f i) q = p := by
  simpa only [Set.mem_iUnion, Set.mem_range] using
    Set.eq_univ_iff_forall.mp h.jointly_surjective p

/-- An étale covering of each member of an étale covering composes to an
étale covering of the original algebraic space. -/
@[stacks 041F "etale_covering_comp"]
public theorem isEtaleCovering_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} (J : I → Type w)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (Xᵢ : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (f : ∀ i, Xᵢ i ⟶ X)
    (Xᵢⱼ : ∀ i, J i → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (g : ∀ i j, Xᵢⱼ i j ⟶ Xᵢ i)
    (hf : IsEtaleCovering B S hS Xᵢ f)
    (hg : ∀ i, IsEtaleCovering B S hS (Xᵢⱼ i) (g i)) :
    IsEtaleCovering B S hS
      (fun ij : (i : I) × J i => Xᵢⱼ ij.1 ij.2)
      (fun ij => g ij.1 ij.2 ≫ f ij.1) := by
  refine ⟨hf.target_isAlgebraicSpace,
    (fun ij => (hg ij.1).source_isAlgebraicSpace ij.2),
    (fun ij => isEtale_comp B S hS ((hg ij.1).etale ij.2) (hf.etale ij.1)), ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun p => ?_
  obtain ⟨i, q, rfl⟩ := hf.exists_pointsMap_eq p
  obtain ⟨j, r, rfl⟩ := (hg i).exists_pointsMap_eq q
  refine Set.mem_iUnion.mpr ⟨⟨i, j⟩, Set.mem_range.mpr ⟨r, ?_⟩⟩
  refine Quot.inductionOn r (fun t => ?_)
  simp only [pointsMap_class]
  rfl

/-- **Stacks 041F**, the base-change clause. The first projections of the presheaf fibre
products of an étale covering of an algebraic space over `S` with a morphism `g` into its
target form an étale covering of the source of `g`. -/
@[stacks 041F "etale_covering_base_change"]
theorem isEtaleCovering_pullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type v} {X X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X' ⟶ X) (hX' : IsAlgebraicSpace B S hS X')
    (Y : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f : ∀ i, Y i ⟶ X)
    (h : IsEtaleCovering B S hS Y f) :
    IsEtaleCovering B S hS (fun i => CategoryTheory.Limits.pullback g (f i))
      (fun i => CategoryTheory.Limits.pullback.fst g (f i)) := by
  let XObj : AlgebraicSpaces B S hS := ⟨X, h.target_isAlgebraicSpace⟩
  let X'Obj : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let YObj (i : I) : AlgebraicSpaces B S hS := ⟨Y i, h.source_isAlgebraicSpace i⟩
  let gObj : X'Obj ⟶ XObj := ObjectProperty.homMk g
  let fObj (i : I) : YObj i ⟶ XObj := ObjectProperty.homMk (f i)
  let pObj (i : I) : AlgebraicSpaces.fiberProduct B S hS gObj (fObj i) ⟶ X'Obj :=
    ObjectProperty.homMk (CategoryTheory.Limits.pullback.fst g (f i))
  let qObj (i : I) : AlgebraicSpaces.fiberProduct B S hS gObj (fObj i) ⟶ YObj i :=
    ObjectProperty.homMk (CategoryTheory.Limits.pullback.snd g (f i))
  have hsquare (i : I) : CategoryTheory.IsPullback (pObj i) (qObj i) gObj (fObj i) :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS gObj (fObj i)
  refine ⟨hX', fun i => isAlgebraicSpace_pullback B S hS g (f i) hX'
      (h.source_isAlgebraicSpace i) h.target_isAlgebraicSpace,
    fun i => isEtale_of_isPullback B S hS (qObj i) (pObj i) (fObj i) gObj
      (hsquare i).flip (h.etale i), ?_⟩
  refine Set.eq_univ_of_forall fun x' => ?_
  obtain ⟨i, y, hy⟩ := h.exists_pointsMap_eq (pointsMap B S hS X' g x')
  obtain ⟨w, hwp, -⟩ := exists_point_of_isPullback B S hS (hsquare i) x' y hy.symm
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨w, hwp⟩⟩

/-- **Stacks 041F**, the isomorphism clause. An isomorphism of algebraic spaces over `S`,
regarded as a family indexed by a point, is an étale covering. -/
@[stacks 041F "isomorphism_etale_covering"]
lemma isEtaleCovering_of_isIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) [IsIso f]
    (hX : IsAlgebraicSpace B S hS X) :
    IsEtaleCovering B S hS (fun _ : Unit ↦ X') (fun _ ↦ f) := by
  have hX' : IsAlgebraicSpace B S hS X' :=
    isAlgebraicSpace_of_relativelyRepresentable B S hS f
      (Functor.relativelyRepresentable.of_isIso yoneda _) hX
  refine ⟨hX, fun _ ↦ hX', fun _ ↦ isEtale_of_isIso B S hS f, ?_⟩
  rw [Set.iUnion_const, Set.range_eq_univ]
  exact pointsMap_surjective_of_isIso B S hS f

end AlgebraicGeometry.Space

end
