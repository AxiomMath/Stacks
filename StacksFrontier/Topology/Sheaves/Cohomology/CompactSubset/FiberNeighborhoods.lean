module

public import Mathlib.Topology.SeparatedMap
public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageRingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.SubsetSections

/-!
# The fibre of a morphism of ringed spaces at a point

For a morphism of ringed spaces `f : X ⟶ Y` and a point `y : Y`, this file introduces the fibre
`f⁻¹(y)` as a ringed space in its own right — the subspace carrying the inverse image of the
structure sheaf of `X` — together with the two facts about its open neighbourhoods that the
cohomology of [Stacks, Tag 09V5] rests on.

## Main definitions

* `Stacks.Topology.fiberRingedSpace` and `Stacks.Topology.fiberι`: the fibre with the restricted
  structure sheaf, and its inclusion. Both are the inverse-image ringed space of
  `AlgebraicGeometry.RingedSpace.inverseImage` along `Stacks.subsetInclusion`.
* `Stacks.Topology.topToPreimageOfConstant`: a neighbourhood of the value of a constant map pulls
  back to the whole space.
* `Stacks.Topology.stalkToSectionsOfConstant`: for `ψ : F ⟶ h_* G` with `h` constant with value
  `y`, the induced map from the stalk of `F` at `y` to the global sections of `G`.
* `Stacks.Topology.preimageNeighborhoodFunctor`: the diagram of open neighbourhoods of the fibre
  that are pulled back from the point.

## Main results

* `Stacks.Topology.fiberPairwiseSeparated`: the fibre of a separated map is pairwise separated,
  which is the hypothesis `Stacks.Topology.isIso_cohomologyOfClosedMap` asks of a subset.
* `Stacks.Topology.preimageNeighborhoods_cofinal` and
  `Stacks.Topology.preimageNeighborhoodFunctor_final`: for a closed map the pulled-back
  neighbourhoods are cofinal among all open neighbourhoods of the fibre, and the diagram of them
  is a final functor. Together with `fiberPairwiseSeparated` this is what lets the comparison of
  Tag 09V3 be read on the fibre.

## Implementation notes

`stalkToSectionsOfConstant` and its germ formula are stated here without any transparency
relaxation. The cocone's naturality square is pasted by the abstract `paste₂`, whose every term is
a variable, instead of being rewritten in place: the obstruction is the two spellings `OpenNhds y`
and `{ U // y ∈ U }` of the index category, which makes `rw [← Category.assoc]` report `unop V has
type OpenNhds y but is expected to have type { U // y ∈ U }`. The germ formula is likewise a single
`colimit.ι_desc` term with its index given explicitly.

## References

* [Stacks Project, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat
open AlgebraicGeometry

namespace Stacks.Topology

universe u v

noncomputable section

/-- The fibre of a morphism of ringed spaces at a point, carrying the inverse image of the
structure sheaf of the source. -/
abbrev fiberRingedSpace {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (y : Y) : RingedSpace.{u, u} :=
  RingedSpace.inverseImage X
    (Stacks.subsetInclusion X.carrier ((f.hom : X → Y) ⁻¹' {y}))

/-- The inclusion of the fibre of a morphism of ringed spaces at a point. -/
abbrev fiberι {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (y : Y) : fiberRingedSpace f y ⟶ X :=
  RingedSpace.inverseImageProjection X
    (Stacks.subsetInclusion X.carrier ((f.hom : X → Y) ⁻¹' {y}))

/-- A neighbourhood of the value of a constant map pulls back to the whole space. -/
def topToPreimageOfConstant {Z Y : TopCat.{u}} (h : Z ⟶ Y) (y : Y)
    (hy : ∀ z, h z = y) (V : Opens Y) (hV : y ∈ V) :
    (⊤ : Opens Z) ⟶ (Opens.map h).obj V :=
  homOfLE (by intro z _; change h z ∈ V; rw [hy z]; exact hV)

/-- Abstract pasting of a naturality square onto a triangle. Every term is a variable, so no
tactic key-matches inside an opaque composite; this is applied as a term below in place of the
`erw [ψ.naturality]` the obstruction would otherwise force. -/
private theorem paste₂ {D : Type*} [Category D] {A B E H G' : D} (m : A ⟶ B) (b : B ⟶ E)
    (c : A ⟶ G') (d : G' ⟶ E) (e : E ⟶ H) (g : G' ⟶ H)
    (h₁ : m ≫ b = c ≫ d) (h₂ : d ≫ e = g) : m ≫ b ≫ e = c ≫ g := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

/-- **Germs at the value of a constant map restrict to sections on its domain.** Given
`ψ : F ⟶ h_* G` for a map `h : Z ⟶ Y` constant with value `y`, every neighbourhood of `y` pulls
back to all of `Z`, so the section maps of `ψ` followed by restriction to `⊤` form a cocone on
the neighbourhood diagram computing the stalk of `F` at `y`. -/
def stalkToSectionsOfConstant {C : Type v} [Category.{u} C]
    [HasColimits C] {Z Y : TopCat.{u}} (h : Z ⟶ Y) (y : Y)
    (hy : ∀ z, h z = y) (F : TopCat.Presheaf C Y) (G : TopCat.Presheaf C Z)
    (ψ : F ⟶ (TopCat.Presheaf.pushforward C h).obj G) :
    TopCat.Presheaf.stalk F y ⟶ G.obj (op ⊤) :=
  colimit.desc ((OpenNhds.inclusion y).op ⋙ F)
    { pt := G.obj (op ⊤)
      ι :=
        { app := fun U => ψ.app (op U.unop.1) ≫
            G.map (topToPreimageOfConstant h y hy U.unop.1 U.unop.2).op
          naturality := by
            intro U V a
            have h₂ : ((TopCat.Presheaf.pushforward C h).obj G).map
                  ((OpenNhds.inclusion y).map a.unop).op ≫
                G.map (topToPreimageOfConstant h y hy V.unop.1 V.unop.2).op =
                G.map (topToPreimageOfConstant h y hy U.unop.1 U.unop.2).op :=
              (G.map_comp _ _).symm.trans (congrArg G.map (Subsingleton.elim _ _))
            refine (paste₂ _ _ _ _ _ _ (ψ.naturality _) h₂).trans ?_
            exact (Category.comp_id _).symm } }

/-- The defining property of `stalkToSectionsOfConstant`: it sends the germ of a section over a
neighbourhood of `y` to the restriction of that section to `⊤`. -/
theorem stalkToSectionsOfConstant_germ {C : Type v} [Category.{u} C]
    [HasColimits C] {Z Y : TopCat.{u}} (h : Z ⟶ Y) (y : Y)
    (hy : ∀ z, h z = y) (F : TopCat.Presheaf C Y) (G : TopCat.Presheaf C Z)
    (ψ : F ⟶ (TopCat.Presheaf.pushforward C h).obj G)
    (U : Opens Y) (hU : y ∈ U) :
    TopCat.Presheaf.germ F U y hU ≫ stalkToSectionsOfConstant h y hy F G ψ =
      ψ.app (op U) ≫ G.map (topToPreimageOfConstant h y hy U hU).op :=
  colimit.ι_desc (J := (OpenNhds y)ᵒᵖ) _ (op (⟨U, hU⟩ : OpenNhds y))

/-- **The fibre of a separated map is pairwise separated in the source.** This is the hypothesis
`Stacks.Topology.isIso_cohomologyOfClosedMap` and
`Stacks.Topology.isIso_cohomologyOfClosedMapUnivLE` ask of the subset, supplied for the fibre of
a separated morphism of ringed spaces. -/
theorem fiberPairwiseSeparated {X Y : RingedSpace.{u, u}}
    (f : X ⟶ Y) (y : Y) (hf : IsSeparatedMap (f.hom : X → Y)) :
    ∀ x ∈ ((f.hom : X → Y) ⁻¹' ({y} : Set Y)),
      ∀ x' ∈ ((f.hom : X → Y) ⁻¹' ({y} : Set Y)), x ≠ x' →
        ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ x' ∈ V ∧ Disjoint U V := by
  intro x hx x' hx' hxx'
  exact hf x x' (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hx.trans hx'.symm)
    hxx'

/-- **Open neighbourhoods pulled back from the target are cofinal among the open neighbourhoods
of a fibre**, for a closed map: the complement of the image of the complement of a neighbourhood
`U` of the fibre is an open neighbourhood of `y` whose preimage lies in `U`. -/
theorem preimageNeighborhoods_cofinal {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) (y : Y)
    (hf : IsClosedMap f) (hfc : Continuous f) :
    ∀ U : Opens X, (f ⁻¹' ({y} : Set Y)) ⊆ U →
      ∃ V : Opens Y, y ∈ V ∧ (Opens.map (TopCat.ofHom ⟨f, hfc⟩)).obj V ≤ U := by
  intro U hUZ
  have hclosed : IsClosed (f '' ((U : Set X)ᶜ)) := hf _ U.2.isClosed_compl
  refine ⟨⟨(f '' ((U : Set X)ᶜ))ᶜ, hclosed.isOpen_compl⟩, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hUZ (by simp [hxy]))
  · intro x hx
    by_contra hxU
    exact hx ⟨x, by simpa using hxU, rfl⟩

/-- The diagram of open neighbourhoods of a fibre indexed by open neighbourhoods of the point,
sending `V` to its preimage. -/
def preimageNeighborhoodFunctor {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    (OpenNhds y)ᵒᵖ ⥤ (OpenNhdsSet ((f.hom : X → Y) ⁻¹' ({y} : Set Y)))ᵒᵖ where
  obj V := op ⟨(Opens.map f).obj ((OpenNhds.inclusion y).obj V.unop), by
    intro x hx
    change f x ∈ ((OpenNhds.inclusion y).obj V.unop : Opens Y)
    change f x = y at hx
    simpa [OpenNhds.inclusion, hx] using V.unop.property⟩
  map {V W} g := Quiver.Hom.op (ObjectProperty.homMk
    ((Opens.map f).map ((OpenNhds.inclusion y).map g.unop)))
  map_id V := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    simp
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    simp

/-- **For a closed map, the preimage diagram is final**, so a colimit over the open
neighbourhoods of the fibre may be computed over the open neighbourhoods of the point. -/
theorem preimageNeighborhoodFunctor_final {X Y : TopCat.{u}} (f : X ⟶ Y)
    (y : Y) (hf : IsClosedMap (f.hom : X → Y)) :
    (preimageNeighborhoodFunctor f y).Final := by
  apply Functor.final_of_exists_of_isFiltered (preimageNeighborhoodFunctor f y)
  · intro d
    obtain ⟨V, hyV, hVU⟩ := preimageNeighborhoods_cofinal f.hom y hf f.hom.continuous
      d.unop.1 d.unop.2
    exact ⟨op ⟨V, hyV⟩, ⟨Quiver.Hom.op (ObjectProperty.homMk (homOfLE hVU))⟩⟩
  · intro d c s s'
    refine ⟨c, 𝟙 c, ?_⟩
    have h : s = s' :=
      Quiver.Hom.unop_inj (ObjectProperty.hom_ext _ (Subsingleton.elim _ _))
    simp [h]

end

end Stacks.Topology

end
