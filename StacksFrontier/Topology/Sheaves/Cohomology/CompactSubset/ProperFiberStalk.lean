module

public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.FiberNeighborhoods
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SubsetSectionsOfCoeff

/-!
# The stalk of a direct image along a closed map is the sections on the fibre

Let `f : X ⟶ Y` be a closed map of topological spaces whose fibre over `y : Y` is quasi-compact
and whose distinct points in that fibre are separated by disjoint opens of `X`. For a sheaf `F`
on `X` with values in a concrete category this file proves that the canonical map

`(f_* F)_y ⟶ Γ(f⁻¹(y), F|_{f⁻¹(y)})`

is an isomorphism, where `F|_{f⁻¹(y)}` is the inverse image of `F` along the inclusion of the
fibre. This is the degree-zero case of [Stacks, Tag 09V5], at arbitrary coefficients.

Nothing here is new mathematics: both halves are already proved in the library and both are
already coefficient-general. The stalk of `f_* F` at `y` is by definition the colimit of `F(f⁻¹V)`
over the open neighbourhoods `V` of `y`; those preimages are cofinal among the open neighbourhoods
of the fibre precisely because `f` is closed
(`Stacks.Topology.preimageNeighborhoodFunctor_final`), so that colimit is the colimit over *all*
open neighbourhoods of the fibre; and from there to the sections on the fibre is the degree-zero
comparison `Stacks.Topology.isIso_subsetSectionsMap` of [Stacks, Tag 09V3], which needs the fibre
to be quasi-compact and pairwise separated. What this file supplies is the composite, which was
assembled only for *spectral* maps and the specialization fibre
(`Stacks.Topology.isIso_fiberSectionsOfStalkApp`, [Stacks, Tag 0A3E]) and for morphisms of ringed
spaces and sheaves of modules
(`Stacks.Cohomology.ProperBaseChange.isIso_fiberRestrictionMap_app`), and not for a closed map of
topological spaces at arbitrary coefficients — which is the shape that proper base change for
abelian sheaves needs.

## Main definitions

* `Stacks.Topology.fiberStalkSectionsMap`: the comparison `(f_* F)_y ⟶ Γ(f⁻¹(y), F|_{f⁻¹(y)})`,
  the cofinality map followed by `Stacks.Topology.subsetSectionsMap`.
* `Stacks.Topology.fiberStalkSectionsIso`: the comparison as an isomorphism.

## Main results

* `Stacks.Topology.fiberStalkSectionsMap_germ`: the comparison sends the germ at `y` of a section
  of `F` on `f⁻¹(V)` to the section it induces on the fibre. This pins the comparison down: it is
  restriction of sections and not some other map, and it is the form in which a germwise
  computation consumes it.
* `Stacks.Topology.isIso_fiberStalkSectionsMap`: the comparison is an isomorphism for a closed map
  with quasi-compact pairwise separated fibre.
* `Stacks.Topology.fiberPairwiseSeparated_of_isSeparatedMap`: the fibre of a separated map of
  topological spaces is pairwise separated, which is the hypothesis the degree-zero comparison
  asks of the subset. The library had this only for morphisms of ringed spaces
  (`Stacks.Topology.fiberPairwiseSeparated`).

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open scoped AlgebraicGeometry

namespace Stacks.Topology

universe v u

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
variable [HasColimits C] [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable {X Y : TopCat.{v}} (f : X ⟶ Y) (y : Y)

/-- **The fibre of a separated map is pairwise separated**, for a map of topological spaces. This
is the hypothesis that `Stacks.Topology.isIso_subsetSectionsMap` asks of the subset. -/
theorem fiberPairwiseSeparated_of_isSeparatedMap
    (hsep : IsSeparatedMap (f.hom : X → Y)) :
    ∀ x ∈ ((f.hom : X → Y) ⁻¹' ({y} : Set Y)),
      ∀ x' ∈ ((f.hom : X → Y) ⁻¹' ({y} : Set Y)), x ≠ x' →
        ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ x' ∈ B ∧ Disjoint A B := by
  intro x hx x' hx' hxx'
  exact hsep x x' (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx.trans hx'.symm)
    hxx'

omit [HasColimits C] [HasLimits C] in
/-- The stalk diagram of `f_* F` at `y` is the diagram of sections of `F` over the inverse images
of the open neighbourhoods of `y`, viewed as a diagram of open neighbourhoods of the fibre. -/
theorem preimageNeighborhoodFunctor_comp_neighborhoodSections (F : X.Sheaf C) :
    preimageNeighborhoodFunctor f y ⋙
        neighborhoodSections F ((f.hom : X → Y) ⁻¹' ({y} : Set Y)) =
      (OpenNhds.inclusion y).op ⋙ (f _* F.presheaf) :=
  rfl

/-- **The comparison of the stalk of a direct image with the sections on the fibre.** The stalk at
`y` of `f_* F` — the colimit of the sections of `F` on the inverse images of the open
neighbourhoods of `y` — maps to the global sections of the restriction of `F` to the fibre
`f⁻¹(y)`: pass from the colimit over the inverse images to the colimit over all open
neighbourhoods of the fibre, then apply the degree-zero comparison
`Stacks.Topology.subsetSectionsMap` of [Stacks, Tag 09V3]. -/
def fiberStalkSectionsMap (F : X.Sheaf C) :
    (f _* F.presheaf).stalk y ⟶
      ((TopCat.Sheaf.pullback C
          (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))).obj F).presheaf.obj
        (op ⊤) :=
  colimit.pre (neighborhoodSections F ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
      (preimageNeighborhoodFunctor f y) ≫
    subsetSectionsMap F ((f.hom : X → Y) ⁻¹' ({y} : Set Y))

/-- **The comparison is restriction of sections**: it carries the germ at `y` of a section of `F`
on `f⁻¹(V)` to the section that section induces on the fibre. -/
theorem fiberStalkSectionsMap_germ (F : X.Sheaf C) (V : Opens Y) (hy : y ∈ V)
    (s : ToType ((f _* F.presheaf).obj (op V))) :
    fiberStalkSectionsMap f y F ((f _* F.presheaf).germ V y hy s) =
      ambientSection (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({y} : Set Y))) F
        (top_le_map_openNhdsSet ((preimageNeighborhoodFunctor f y).obj (op ⟨V, hy⟩)).unop) s := by
  have hpre : colimit.pre (neighborhoodSections F ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
        (preimageNeighborhoodFunctor f y) ((f _* F.presheaf).germ V y hy s) =
      colimit.ι (neighborhoodSections F ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
        ((preimageNeighborhoodFunctor f y).obj (op ⟨V, hy⟩)) s :=
    (ConcreteCategory.comp_apply _ _ s).symm.trans
      (ConcreteCategory.congr_hom
        (colimit.ι_pre (neighborhoodSections F ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
          (preimageNeighborhoodFunctor f y) (op ⟨V, hy⟩)) s)
  exact (ConcreteCategory.comp_apply _ _ _).trans
    ((congrArg (subsetSectionsMap F ((f.hom : X → Y) ⁻¹' ({y} : Set Y))) hpre).trans
      (subsetSectionsMap_ι F ((f.hom : X → Y) ⁻¹' ({y} : Set Y))
        ((preimageNeighborhoodFunctor f y).obj (op ⟨V, hy⟩)) s))

/-- **The stalk of a direct image along a closed map is the sections on the fibre**, the
degree-zero case of [Stacks, Tag 09V5] at arbitrary coefficients. The inverse images of the open
neighbourhoods of `y` are cofinal among the open neighbourhoods of the fibre because `f` is
closed, and the fibre is quasi-compact and pairwise separated, so the degree-zero comparison of
[Stacks, Tag 09V3] along it is invertible. -/
theorem isIso_fiberStalkSectionsMap
    (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : IsCompact ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
    (hsep : IsSeparatedMap (f.hom : X → Y)) (F : X.Sheaf C) :
    IsIso (fiberStalkSectionsMap f y F) := by
  have : (preimageNeighborhoodFunctor f y).Final :=
    preimageNeighborhoodFunctor_final f y hclosed
  have : IsIso (subsetSectionsMap F ((f.hom : X → Y) ⁻¹' ({y} : Set Y))) :=
    isIso_subsetSectionsMap F _ hcompact
      (fiberPairwiseSeparated_of_isSeparatedMap f y hsep)
  have h : IsIso (colimit.pre (neighborhoodSections F ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
        (preimageNeighborhoodFunctor f y) ≫
      subsetSectionsMap F ((f.hom : X → Y) ⁻¹' ({y} : Set Y))) := IsIso.comp_isIso
  exact h

/-- **The stalk of a direct image along a closed map is the sections on the fibre**, as an
isomorphism. -/
def fiberStalkSectionsIso
    (hclosed : IsClosedMap (f.hom : X → Y))
    (hcompact : IsCompact ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))
    (hsep : IsSeparatedMap (f.hom : X → Y)) (F : X.Sheaf C) :
    (f _* F.presheaf).stalk y ≅
      ((TopCat.Sheaf.pullback C
          (Stacks.subsetInclusion X ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))).obj F).presheaf.obj
        (op ⊤) :=
  haveI := isIso_fiberStalkSectionsMap f y hclosed hcompact hsep F
  asIso (fiberStalkSectionsMap f y F)

end Stacks.Topology

end
