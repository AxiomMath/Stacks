module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPoint
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
import StacksFrontier.AlgebraicGeometry.Size.FiniteType

/-!
# GeometricPointFiberUnconditional

Stronger forms of declarations of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointFiber`, stated as separate
declarations beside the ones there: over more general coefficient universes, or with inputs that
are carried there as hypotheses discharged, together with the new results built on them.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- Forget the size cutoff on an étale neighborhood: an étale neighborhood of `s` inside the
chosen site, as an étale neighborhood of `s` in Mathlib's small étale site of `S`. -/
public def neighborhoodInclusionPublic : (geometricPointFiber B S hS s).Elements ⥤
    (Scheme.pointSmallEtale s.hom).fiber.Elements where
  obj U := ⟨MorphismProperty.Over.mk _ (B.inclusion.map U.1.obj.hom) U.1.property,
    Over.homMk U.2.1 U.2.2⟩
  map {U V} f := ⟨MorphismProperty.Over.homMk ((SmallEtale.toScheme B S hS).map f.1)
    (by
      change B.inclusion.map f.1.hom.left ≫ B.inclusion.map V.1.obj.hom =
        B.inclusion.map U.1.obj.hom
      rw [← Functor.map_comp, Over.w]) (by trivial),
    Over.OverMorphism.ext (congrArg Subtype.val f.2)⟩

/-- The functor `neighborhoodInclusionPublic B S hS s` is faithful. -/
public instance : (neighborhoodInclusionPublic B S hS s).Faithful where
  map_injective h := Subtype.ext <| ObjectProperty.hom_ext _ <| Over.OverMorphism.ext <|
    ObjectProperty.hom_ext _ <| congrArg (fun k => k.1.left) h

/-- The functor `neighborhoodInclusionPublic B S hS s` is full. -/
public instance : (neighborhoodInclusionPublic B S hS s).Full where
  map_surjective {U V} f := by
    refine ⟨⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk f.1.left)
      (ObjectProperty.hom_ext _ f.1.w)), Subtype.ext (congrArg (fun k => k.left) f.2)⟩, ?_⟩
    apply Subtype.ext
    apply MorphismProperty.Over.Hom.ext
    rfl

/-- **The étale neighborhoods of `s` inside the chosen site are initial among all étale
neighborhoods of `s`.** The inclusion is fully faithful, the étale neighborhoods of `s` in
Mathlib's small étale site are cofiltered, and every one of them is refined by an affine one
below the cutoff of the chosen site. So a stalk at `s` may be computed from either family of
neighborhoods. -/
public instance initial_neighborhoodInclusion : (neighborhoodInclusionPublic B S hS s).Initial :=
  Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful _ fun U => by
    obtain ⟨V, -, hV⟩ := exists_neighborhood_refinement B S hS s U
    exact ⟨V, hV⟩

end AlgebraicGeometry

end
