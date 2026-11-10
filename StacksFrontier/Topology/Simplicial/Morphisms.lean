module

public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismDefs
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiSite
public import StacksFrontier.Topology.Simplicial.Site

/-!
# Functoriality of the site of a simplicial space

A morphism of simplicial topological spaces induces, by inverse image of open subsets in every
degree, a functor between their simplicial sites. This functor defines a morphism of sites.

## Main definitions

* `Stacks.Topology.Simplicial.SimplicialOpen.pullback`: the functor on simplicial opens induced
  by a morphism of simplicial topological spaces.

## Main results

* `Stacks.Topology.Simplicial.SimplicialOpen.pullback_isMorphismOfSites`: the inverse-image
  functor defines a morphism of sites.
* `Stacks.Topology.Simplicial.SimplicialOpen.pullback_isMorphismOfSites_large`: the same
  statement for sheaves valued in a larger universe.

## Implementation notes

The underlying simplex map of a morphism of simplicial opens is unchanged by pullback. The
required containment of opens follows from the naturality square of the morphism of simplicial
spaces. The simplicial-open category has objects in `Type u` but morphisms in `Type`, so it is
not a `SmallCategory` for arbitrary `u` and cannot use the small-category-only predicate of
Stacks 00X1. We use its universe-general formulation: the pushforward on set-valued
sheaves has a left adjoint preserving finite limits. The larger-universe variant allows
sheaves in any universe `max u w`, independently of the universe `u` of the spaces. This is
the same exactness condition on sheaves of sets as in Stacks 00X1.

Left exactness of the left Kan extension of a representably flat functor is
`Stacks.Topology.lan_preservesFiniteLimits_of_flat`.

## References

* [Stacks Project, Tag 09VN](https://stacks.math.columbia.edu/tag/09VN)
-/

@[expose] public section

open CategoryTheory TopologicalSpace CategoryTheory.Limits
open Opposite

universe u w

namespace Stacks.Topology.Simplicial

namespace SimplicialOpen

/-- Pullback of open subsets degree by degree along a morphism of simplicial topological
spaces. -/
def pullback {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) :
    SimplicialOpen X ⥤ SimplicialOpen Y where
  obj U :=
    { degree := U.degree
      toOpens := (Opens.map (f.app U.degree)).obj U.toOpens }
  map {U V} g :=
    { base := g.base
      le := by
        intro y hy
        have h := SimplicialOpen.Hom.le g hy
        change (Y.map g.base ≫ f.app V.degree : _) y ∈ V.toOpens
        change X.map g.base (f.app U.degree y) ∈ V.toOpens at h
        rw [f.naturality g.base]
        exact h }
  map_id U := by
    apply SimplicialOpen.Hom.ext
    rfl
  map_comp {U V W} (g : U ⟶ V) (h : V ⟶ W) := by
    apply SimplicialOpen.Hom.ext
    rfl

/-- A morphism into a pulled-back simplicial open maps points of its source into the original
open. -/
theorem map_base_app_mem {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) {V : SimplicialOpen Y}
    {U : SimplicialOpen X} (g : V ⟶ (pullback f).obj U) {y : Y.obj V.degree}
    (hy : y ∈ V.toOpens) : X.map g.base (f.app V.degree y) ∈ U.toOpens := by
  rw [← ConcreteCategory.comp_apply, ← f.naturality]
  exact SimplicialOpen.Hom.le g hy

/-- The degreewise inverse-image functor of simplicial opens is representably flat. -/
instance pullback_representablyFlat {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) :
    RepresentablyFlat (pullback f) := by
  constructor
  intro V
  refine { cone_objs := ?_, cone_maps := ?_, nonempty := ?_ }
  · intro A B
    let W : SimplicialOpen X :=
      { degree := V.degree
        toOpens := (Opens.map (X.map A.hom.base)).obj A.right.toOpens ⊓
          (Opens.map (X.map B.hom.base)).obj B.right.toOpens }
    let hV : V ⟶ (pullback f).obj W :=
      { base := 𝟙 _
        le := by
          intro y hy
          simp only [W, pullback, Opens.map_def]
          constructor
          · change X.map A.hom.base (f.app V.degree (Y.map (𝟙 _) y)) ∈ A.right.toOpens
            exact map_base_app_mem f A.hom (by simpa using hy)
          · change X.map B.hom.base (f.app V.degree (Y.map (𝟙 _) y)) ∈ B.right.toOpens
            exact map_base_app_mem f B.hom (by simpa using hy) }
    let WA : W ⟶ A.right := { base := A.hom.base, le := fun _ hx ↦ hx.1 }
    let WB : W ⟶ B.right := { base := B.hom.base, le := fun _ hx ↦ hx.2 }
    exact ⟨StructuredArrow.mk hV,
      StructuredArrow.homMk WA (SimplicialOpen.Hom.ext _ _ (Category.id_comp A.hom.base)),
      StructuredArrow.homMk WB (SimplicialOpen.Hom.ext _ _ (Category.id_comp B.hom.base)),
      trivial⟩
  · intro A B a b
    let W : SimplicialOpen X :=
      { degree := V.degree, toOpens := (Opens.map (X.map A.hom.base)).obj A.right.toOpens }
    let hV : V ⟶ (pullback f).obj W :=
      { base := 𝟙 _
        le := by
          intro y hy
          simp only [W, pullback, Opens.map_def]
          change X.map A.hom.base (f.app V.degree (Y.map (𝟙 _) y)) ∈ A.right.toOpens
          exact map_base_app_mem f A.hom (by simpa using hy) }
    let WA : W ⟶ A.right := { base := A.hom.base, le := fun _ hx ↦ hx }
    let c : StructuredArrow.mk hV ⟶ A :=
      StructuredArrow.homMk WA (SimplicialOpen.Hom.ext _ _ (Category.id_comp A.hom.base))
    refine ⟨StructuredArrow.mk hV, c, ?_⟩
    apply StructuredArrow.hom_ext
    apply SimplicialOpen.Hom.ext
    change A.hom.base ≫ a.right.base = A.hom.base ≫ b.right.base
    exact congrArg SimplicialOpen.Hom.base
      ((StructuredArrow.w a).trans (StructuredArrow.w b).symm)
  · exact ⟨StructuredArrow.mk
      ({ base := 𝟙 _, le := fun _ _ ↦ by simp [pullback] } :
        V ⟶ (pullback f).obj { degree := V.degree, toOpens := ⊤ })⟩

/-- The degreewise inverse-image functor of simplicial opens preserves covering sieves. -/
theorem pullback_coverPreserving {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) :
    CoverPreserving (SimplicialOpen.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology Y) (pullback f) := by
  constructor
  intro U S hS
  rw [SimplicialOpen.mem_grothendieckTopology] at hS ⊢
  obtain ⟨R, hR, hRS⟩ := hS
  refine ⟨R.map (pullback f), ?_, ?_⟩
  · constructor
    · rintro V g ⟨hg⟩
      exact hR.1 _ _ hg
    · intro y hy
      let yu : Y.obj U.degree := y
      obtain ⟨V, g, hg, x, hx, heq⟩ := hR.2 (f.app U.degree yu) hy
      obtain ⟨e, he⟩ := hR.1 V g hg
      let y' := Y.map (eqToHom e.symm) yu
      have hy' : f.app V.degree y' = x := by
        change f.app V.degree (Y.map (eqToHom e.symm) yu) = x
        have hn := congrArg (fun k => k yu) (f.naturality (eqToHom e.symm))
        change f.app V.degree (Y.map (eqToHom e.symm) yu) =
          X.map (eqToHom e.symm) (f.app U.degree yu) at hn
        rw [← heq, he] at hn
        simpa using hn
      refine ⟨(pullback f).obj V, (pullback f).map g, .of hg, y', ?_, ?_⟩
      · change f.app V.degree y' ∈ V.toOpens
        rw [hy']
        exact hx
      · change Y.map g.base y' = yu
        rw [he]
        change Y.map (eqToHom e) (Y.map (eqToHom e.symm) yu) = yu
        rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
        simp
  · exact (R.map_le_functorPushforward (pullback f)).trans
      (Presieve.functorPushforward_monotone hRS)

/-- **Stacks 09VN.** The degreewise inverse-image functor associated to a morphism of simplicial
topological spaces defines a morphism from the site of its source to the site of its target. -/
theorem pullback_isMorphismOfSites_large {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) :
    IsMorphismOfSites.{max u w} (pullback f)
      (SimplicialOpen.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology Y) := by
  let J := SimplicialOpen.grothendieckTopology X
  let K := SimplicialOpen.grothendieckTopology Y
  let F := pullback f
  have : RepresentablyFlat F := pullback_representablyFlat f
  have : F.IsContinuous J K :=
    (Functor.isContinuous_iff_coverPreserving (F := F) (J := J) (K := K)).2
      (pullback_coverPreserving f)
  refine ⟨?_⟩
  refine ⟨Functor.sheafPullbackConstruction.sheafPullback F (Type (max u w)) J K, ?_⟩
  refine ⟨⟨Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type (max u w)) J K⟩, ?_⟩
  have : PreservesFiniteLimits (F.op.lan :
      ((SimplicialOpen X)ᵒᵖ ⥤ Type (max u w)) ⥤
        (SimplicialOpen Y)ᵒᵖ ⥤ Type (max u w)) :=
    Stacks.Topology.lan_preservesFiniteLimits_of_flat F (fun _ => inferInstance)
  exact inferInstance

/-- **Stacks 09VN.** The simplicial-site morphism on sheaves in the universe of the spaces. -/
@[stacks 09VN]
theorem pullback_isMorphismOfSites {X Y : SimplicialObject TopCat.{u}} (f : Y ⟶ X) :
    IsMorphismOfSites.{u} (pullback f)
      (SimplicialOpen.grothendieckTopology X)
      (SimplicialOpen.grothendieckTopology Y) :=
  pullback_isMorphismOfSites_large.{u, u} f

end SimplicialOpen

end Stacks.Topology.Simplicial

end
