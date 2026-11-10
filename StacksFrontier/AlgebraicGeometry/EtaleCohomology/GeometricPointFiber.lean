module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# Stalks on the small étale site

Let `B` be a big étale site containing a scheme `S`, and let `s` be a geometric point of `S`.
Each object of the small étale site of `S` has a set of lifts of `s`, and these sets form a
functor to `Type u`; its category of elements is the category of étale neighborhoods of `s`
inside the chosen site. The stalk of a presheaf on the small étale site at `s` is the colimit
of the presheaf over that category.

## Main definitions

* `AlgebraicGeometry.geometricPointFiber`: the functor sending an object of the small étale
  site to its set of lifts of the geometric point.
* `AlgebraicGeometry.etaleStalk`: the colimit of a presheaf over those lifts.

## Main results

* `AlgebraicGeometry.SmallEtale.toScheme_map_comp`: a morphism of the small étale site commutes
  with the structure morphisms to `S`.
* `AlgebraicGeometry.exists_isAffine_refinement_geometricPointFiber`: every étale neighborhood
  of the geometric point is refined by an affine one.
* `AlgebraicGeometry.isCofiltered_geometricPointFiber_elements`: the étale neighborhoods form a
  cofiltered category.
* `AlgebraicGeometry.geometricPointFiber_initiallySmall`: the étale neighborhoods have a small
  cofinal subcategory.
* `AlgebraicGeometry.hasColimitsOfShape_geometricPointFiber`: stalks exist in every category
  with small colimits in the universe of the schemes, including sets, abelian groups and rings.

## Implementation notes

The stalk is formed in an arbitrary category admitting the relevant colimit, so the same name
applies to presheaves of sets, abelian groups and rings. Although the objects of the
neighborhood category live one universe higher, affine refinements give an initially small
family. We obtain that family from Mathlib's point `AlgebraicGeometry.Scheme.pointSmallEtale`
of the small étale site: every affine refinement fits below the chosen site's cutoff, because
its size is at most that of the base. Thus ordinary set- and ring-valued stalks need no extra
colimit-existence assumption.

## References

* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
* [Stacks Project, Tag 04FM](https://stacks.math.columbia.edu/tag/04FM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- A morphism of the small étale site of `S` commutes with the structure morphisms to `S`. -/
public theorem SmallEtale.toScheme_map_comp {U V : SmallEtale B S hS} (f : U ⟶ V) :
    (SmallEtale.toScheme B S hS).map f ≫ B.inclusion.map V.obj.hom =
      B.inclusion.map U.obj.hom := by
  change B.inclusion.map ((SmallEtale.inclusion B S hS).map f).left ≫
    B.inclusion.map V.obj.hom = B.inclusion.map U.obj.hom
  simpa only [SmallEtale.inclusion, ObjectProperty.ι_obj, ← Functor.map_comp] using
    congrArg B.inclusion.map (Over.w ((SmallEtale.inclusion B S hS).map f))

/-- The lifts of a geometric point to objects of the small étale site, i.e. the functor

`u : S_étale ⟶ Sets`, `U ↦ {ū such that (U, ū) is an étale neighbourhood of s̄}`

sending `U` to the morphisms `s̄ ⟶ U` over `S`. -/
@[implicit_reducible, stacks 04FM "the functor `u : U ↦ |U_s̄|`"]
public def geometricPointFiber : SmallEtale B S hS ⥤ Type u where
  obj U := {p : s.source ⟶ (SmallEtale.toScheme B S hS).obj U //
    p ≫ B.inclusion.map U.obj.hom = s.hom}
  map {U V} f := ↾ (fun p => ⟨p.1 ≫ (SmallEtale.toScheme B S hS).map f, by
    rw [Category.assoc, SmallEtale.toScheme_map_comp, p.2]⟩)
  map_id U := by ext; simp
  map_comp f g := by ext; simp

/-- Forget the size cutoff on an étale neighborhood. -/
private def neighborhoodInclusion : (geometricPointFiber B S hS s).Elements ⥤
    (Scheme.pointSmallEtale s.hom).fiber.Elements where
  obj U := .mk (obj := MorphismProperty.Over.mk _ (B.inclusion.map U.obj.obj.hom) U.obj.property)
    (Over.homMk U.val.1 U.val.2)
  map {U V} f := Functor.Elements.homMk
    (MorphismProperty.Over.homMk ((SmallEtale.toScheme B S hS).map f.hom)
      (SmallEtale.toScheme_map_comp B S hS f.hom) (by trivial))
    (Over.OverMorphism.ext (congrArg Subtype.val f.map_val))

private instance : (neighborhoodInclusion B S hS s).Faithful where
  map_injective h := Functor.Elements.hom_ext <| ObjectProperty.hom_ext _ <|
    Over.OverMorphism.ext <| ObjectProperty.hom_ext _ <| congrArg (fun k => k.hom.left) h

private instance : (neighborhoodInclusion B S hS s).Full where
  map_surjective f :=
    ⟨Functor.Elements.homMk (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk f.hom.left)
      (ObjectProperty.hom_ext _ f.hom.w))) (Subtype.ext (congrArg (fun k => k.left) f.map_val)),
      Functor.Elements.hom_ext (MorphismProperty.Over.Hom.ext rfl)⟩

/-- Every neighborhood has an affine refinement inside the chosen size cutoff. -/
private theorem exists_neighborhood_refinement
    (U : (Scheme.pointSmallEtale s.hom).fiber.Elements) :
    ∃ V, IsAffine ((SmallEtale.toScheme B S hS).obj V.1) ∧
      Nonempty ((neighborhoodInclusion B S hS s).obj V ⟶ U) := by
  let p : s.source ⟶ U.obj.left := U.val.left
  obtain ⟨R, j, hj, y, hy⟩ : ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ U.obj.left)
      (_ : IsOpenImmersion j) (y : s.source ⟶ Spec R), y ≫ j = U.val.left := by
    obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := p.base (default : s.source)) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j p ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  have hjf : Etale (j ≫ U.obj.hom) := inferInstance
  have hR : B.Contains (Spec R) :=
    (Scheme.size_le_of_locallyOfFiniteType (j ≫ U.obj.hom)).trans_lt hS
  let V : SmallEtale B S hS :=
    ⟨Over.mk (ObjectProperty.homMk (j ≫ U.obj.hom) : B.obj (Spec R) hR ⟶ B.obj S hS), hjf⟩
  have hyS : y ≫ (j ≫ U.obj.hom) = s.hom := by
    rw [← Category.assoc, hy]
    exact Over.w U.val
  refine ⟨.mk (obj := V) ⟨y, hyS⟩, inferInstanceAs (IsAffine (Spec R)),
    ⟨Functor.Elements.homMk (MorphismProperty.Over.homMk j rfl (by trivial))
      (Over.OverMorphism.ext hy)⟩⟩

/-- Every étale neighborhood of a geometric point inside the chosen site is refined by an
affine one. -/
public theorem exists_isAffine_refinement_geometricPointFiber
    (a : (geometricPointFiber B S hS s).Elements) :
    ∃ b : (geometricPointFiber B S hS s).Elements,
      IsAffine ((SmallEtale.toScheme B S hS).obj b.1) ∧ Nonempty (b ⟶ a) := by
  obtain ⟨V, hV, ⟨f⟩⟩ :=
    exists_neighborhood_refinement B S hS s ((neighborhoodInclusion B S hS s).obj a)
  exact ⟨V, hV, ⟨(neighborhoodInclusion B S hS s).preimage f⟩⟩

/-- The étale neighborhoods of a geometric point inside the chosen site are cofiltered: two
neighborhoods are both refined by a third, and two morphisms of neighborhoods are equalized by
a further refinement. -/
public instance isCofiltered_geometricPointFiber_elements :
    IsCofiltered (geometricPointFiber B S hS s).Elements :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful
    (neighborhoodInclusion B S hS s)
    (fun U => (exists_neighborhood_refinement B S hS s U).imp fun _ h => h.2)

/-- The neighborhoods of a geometric point in the chosen small étale site admit a
universe-`u` cofinal subcategory. -/
@[stacks 040R "small neighborhood basis"]
public instance geometricPointFiber_initiallySmall :
    InitiallySmall.{u} (geometricPointFiber B S hS s).Elements := by
  let G := neighborhoodInclusion B S hS s
  obtain ⟨T, hT, h⟩ := InitiallySmall.exists_small_weakly_initial_set.{u}
    (Scheme.pointSmallEtale s.hom).fiber.Elements
  choose V _hVaff hV using fun t : T => exists_neighborhood_refinement B S hS s t.1
  have : Small.{u} T := hT
  apply initiallySmall_of_small_weakly_initial_set (Set.range V)
  intro U
  obtain ⟨t, ht, ⟨f⟩⟩ := h (G.obj U)
  exact ⟨V ⟨t, ht⟩, Set.mem_range_self _, ⟨G.preimage ((hV ⟨t, ht⟩).some ≫ f)⟩⟩

/-- The opposite of the category of étale neighborhoods of a geometric point has colimits in
every category with small colimits. -/
public instance hasColimitsOfShape_geometricPointFiber {A : Type v} [Category.{w} A]
    [HasColimitsOfSize.{u, u} A] :
    HasColimitsOfShape (geometricPointFiber B S hS s).Elementsᵒᵖ A :=
  hasColimitsOfShape_of_finallySmall _ _

/-- The stalk of a presheaf on the small étale site at a geometric point, as the colimit over
its étale neighborhoods. -/
@[stacks 040R]
public def etaleStalk {A : Type v} [Category.{w} A] (F : (SmallEtale B S hS)ᵒᵖ ⥤ A)
    [HasColimit ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F)] : A :=
  colimit ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ F)

end AlgebraicGeometry

end
