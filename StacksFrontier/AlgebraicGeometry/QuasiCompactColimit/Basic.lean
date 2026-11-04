module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Colimits of sheaves are detected sectionwise on a basis of the topology

A colimit in a category of sheaves is the sheafification of the colimit of the underlying
presheaves, so its sections over an open set are not in general the colimit of the sections.
This file supplies the case in which the question can nevertheless be settled sectionwise: a
cocone of sheaves is colimiting as soon as its cocones of sections over the members of a *basis*
of the topology are colimiting.

Both halves of Stacks Tag 05JT and all of Stacks Tag 0817 assert that a canonical cocone of
sheaves of algebras is colimiting, and both reduce to the affine case; this is the device that
performs that reduction, with the affine opens of a scheme as the basis.

## Main definitions

* `Stacks.QuasiCompactColimit.sectionsFunctor`: sections over a fixed open, as a functor on
  sheaves.
* `Stacks.QuasiCompactColimit.sectionsRestrict`: restriction along an inclusion of opens, as a
  natural transformation between two such functors.
* `Stacks.QuasiCompactColimit.descSections` and
  `Stacks.QuasiCompactColimit.descOnBasis`: the morphism on sections over one member of the
  basis determined by a second cocone, and those morphisms assembled into a natural
  transformation on the basis.
* `Stacks.QuasiCompactColimit.descOfBasis`: that natural transformation extended to a morphism
  of sheaves.

## Main results

* `Stacks.QuasiCompactColimit.descSections_naturality`: the sectionwise morphisms commute with
  restriction, which is what makes `descOnBasis` natural.
* `Stacks.QuasiCompactColimit.isColimitOfBasis` and
  `Stacks.QuasiCompactColimit.nonempty_isColimit_of_basis`: **a cocone of sheaves is colimiting
  as soon as its cocones of sections over the members of a basis are**, the second in the
  `Nonempty` form in which Tag 05JT states its colimit assertion.

## Implementation notes

The extension from the basis to all opens is `TopCat.Sheaf.restrictHomEquivHom`, and the two
uniqueness arguments are `TopCat.Sheaf.hom_ext`; a basis is cover dense, so a morphism *into* a
sheaf is determined by, and may be prescribed on, the basis alone. Nothing here constructs a
colimit or needs one to exist: the statements are about a given cocone.

No hypothesis on the space is used -- in particular neither quasi-compactness nor
quasi-separatedness. Those enter Tag 05JT elsewhere, in the verification of the sectionwise
hypothesis over an affine open, not in this reduction.

`Stacks.QuasiCompactColimit.sectionsRestrict` exists to keep the projection `F.1` of a sheaf out
of every statement that is rewritten in. `TopCat.Sheaf C X` is a semireducible definition for
`CategoryTheory.Sheaf (TopologicalSpace.Opens.grothendieckTopology X) C`, which is in turn an
abbreviation for a full subcategory, so a term of the form `c.pt.1.map f` is type-correct only
after that definition is unfolded. `rw` and `simp` elaborate their congruence motives at
`implicit` transparency, which does not unfold it, and the failure is reported as the *goal*
being type-incorrect rather than as the rewrite being wrong. Phrasing restriction as a natural
transformation between functor applications removes the projection from the rewritten terms.

## References

* [The Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [The Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe w v u v' u'

namespace Stacks.QuasiCompactColimit

variable {C : Type u} [Category.{v} C] {X : TopCat.{w}}

/-- Sections over a fixed open set, as a functor on sheaves. -/
def sectionsFunctor (U : Opens X) : TopCat.Sheaf C X ⥤ C :=
  TopCat.Sheaf.forget C X ⋙ (evaluation (Opens X)ᵒᵖ C).obj (op U)

/-- The functor of sections over `U` sends a sheaf `F` to `F(U)`. -/
@[simp]
theorem sectionsFunctor_obj (U : Opens X) (F : TopCat.Sheaf C X) :
    (sectionsFunctor U).obj F = F.1.obj (op U) := rfl

/-- The functor of sections over `U` sends a morphism of sheaves to its component at `U`. -/
@[simp]
theorem sectionsFunctor_map (U : Opens X) {F G : TopCat.Sheaf C X} (f : F ⟶ G) :
    (sectionsFunctor U).map f = f.1.app (op U) := rfl

/-- Restriction along an inclusion `V ⟶ U` of opens, as a natural transformation between the
two functors of sections. -/
def sectionsRestrict {U V : Opens X} (f : V ⟶ U) :
    (sectionsFunctor (C := C) U) ⟶ sectionsFunctor V where
  app F := F.1.map f.op
  naturality _ _ g := (g.1.naturality f.op).symm

/-- The component of `sectionsRestrict f` at a sheaf `F` is the restriction map of `F` along
`f`. -/
@[simp]
theorem sectionsRestrict_app {U V : Opens X} (f : V ⟶ U) (F : TopCat.Sheaf C X) :
    (sectionsRestrict f).app F = F.1.map f.op := rfl

variable {K : Type u'} [Category.{v'} K] {F : K ⥤ TopCat.Sheaf C X}

/-- The morphism on sections over `U` out of the vertex of `c`, determined by a second cocone
`s` when the cocone of sections of `c` over `U` is colimiting. -/
def descSections (c : Cocone F) {U : Opens X}
    (hU : IsColimit ((sectionsFunctor U).mapCocone c)) (s : Cocone F) :
    (sectionsFunctor U).obj c.pt ⟶ (sectionsFunctor U).obj s.pt :=
  hU.desc ((sectionsFunctor (C := C) U).mapCocone s)

/-- The morphism `descSections c hU s` composed with the sections over `U` of the coprojection of
`c` at `k` is the sections over `U` of the coprojection of `s` at `k`. -/
@[simp]
theorem map_descSections (c : Cocone F) {U : Opens X}
    (hU : IsColimit ((sectionsFunctor U).mapCocone c)) (s : Cocone F) (k : K) :
    (sectionsFunctor U).map (c.ι.app k) ≫ descSections c hU s =
      (sectionsFunctor U).map (s.ι.app k) :=
  hU.fac _ k

/-- The morphisms of `Stacks.QuasiCompactColimit.descSections` commute with restriction. -/
theorem descSections_naturality (c s : Cocone F) {U V : Opens X} (f : V ⟶ U)
    (hU : IsColimit ((sectionsFunctor U).mapCocone c))
    (hV : IsColimit ((sectionsFunctor V).mapCocone c)) :
    (sectionsRestrict f).app c.pt ≫ descSections c hV s =
      descSections c hU s ≫ (sectionsRestrict f).app s.pt := by
  refine hU.hom_ext fun k => ?_
  rw [Functor.mapCocone_ι_app, ← Category.assoc, (sectionsRestrict f).naturality,
    Category.assoc, map_descSections, ← Category.assoc, map_descSections]
  exact ((sectionsRestrict f).naturality (s.ι.app k)).symm

/-- The natural transformation on a basis `B` determined by a second cocone `s`, when the
cocones of sections of `c` over the members of `B` are all colimiting. -/
def descOnBasis (c s : Cocone F) {ι : Type*} (B : ι → Opens X)
    (h : ∀ i, IsColimit ((sectionsFunctor (B i)).mapCocone c)) :
    (inducedFunctor B).op ⋙ c.pt.1 ⟶ (inducedFunctor B).op ⋙ s.pt.1 where
  app i := descSections c (h i.unop) s
  naturality _ _ f := descSections_naturality c s ((inducedFunctor B).map f.unop) _ _

/-- The component of `descOnBasis c s B h` at `i` is `descSections c (h i) s`. -/
@[simp]
theorem descOnBasis_app (c s : Cocone F) {ι : Type*} (B : ι → Opens X)
    (h : ∀ i, IsColimit ((sectionsFunctor (B i)).mapCocone c)) (i : ι) :
    (descOnBasis c s B h).app (op i) = descSections c (h i) s := rfl

/-- The morphism of sheaves determined by a second cocone, glued from
`Stacks.QuasiCompactColimit.descOnBasis` along the basis. -/
def descOfBasis (c s : Cocone F) {ι : Type*} {B : ι → Opens X}
    (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, IsColimit ((sectionsFunctor (B i)).mapCocone c)) : c.pt ⟶ s.pt :=
  ⟨TopCat.Sheaf.restrictHomEquivHom c.pt.1 s.pt hB (descOnBasis c s B h)⟩

/-- The sections over the basis member `B i` of `descOfBasis c s hB h` are
`descSections c (h i) s`. -/
theorem descOfBasis_app (c s : Cocone F) {ι : Type*} {B : ι → Opens X}
    (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, IsColimit ((sectionsFunctor (B i)).mapCocone c)) (i : ι) :
    (sectionsFunctor (B i)).map (descOfBasis c s hB h) = descSections c (h i) s :=
  TopCat.Sheaf.extend_hom_app c.pt.1 s.pt hB (descOnBasis c s B h) i

/-- **A cocone of sheaves is colimiting as soon as its cocones of sections over the members of a
basis of the topology are colimiting.** -/
def isColimitOfBasis (c : Cocone F) {ι : Type*} {B : ι → Opens X}
    (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, IsColimit ((sectionsFunctor (B i)).mapCocone c)) : IsColimit c where
  desc s := descOfBasis c s hB h
  fac s k := by
    refine Sheaf.hom_ext (TopCat.Sheaf.hom_ext (F.obj k).1 s.pt hB fun i => ?_)
    have : (sectionsFunctor (B i)).map (c.ι.app k ≫ descOfBasis c s hB h) =
        (sectionsFunctor (B i)).map (s.ι.app k) := by
      rw [Functor.map_comp, descOfBasis_app, map_descSections]
    exact this
  uniq s m hm := by
    refine Sheaf.hom_ext (TopCat.Sheaf.hom_ext c.pt.1 s.pt hB fun i => ?_)
    have : (sectionsFunctor (B i)).map m = (sectionsFunctor (B i)).map (descOfBasis c s hB h) := by
      refine (h i).hom_ext fun k => ?_
      rw [Functor.mapCocone_ι_app, ← Functor.map_comp, hm k, descOfBasis_app, map_descSections]
    exact this

/-- A cocone of sheaves is colimiting as soon as its cocones of sections over the members of a
basis of the topology are colimiting; the `Nonempty` form. -/
theorem nonempty_isColimit_of_basis (c : Cocone F) {ι : Type*} {B : ι → Opens X}
    (hB : Opens.IsBasis (Set.range B))
    (h : ∀ i, Nonempty (IsColimit ((sectionsFunctor (B i)).mapCocone c))) :
    Nonempty (IsColimit c) :=
  ⟨isColimitOfBasis c hB fun i => (h i).some⟩

end Stacks.QuasiCompactColimit
