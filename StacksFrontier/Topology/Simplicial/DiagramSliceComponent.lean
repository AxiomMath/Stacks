module

public import StacksFrontier.Topology.Simplicial.DiagramComponent
public import StacksFrontier.Topology.Simplicial.DiagramSlice

/-!
# The component functors on the slice of the total site of a diagram of spaces

The slice of the total site of a diagram of spaces `X` at an object `(n, W)` is the total site of
the diagram over `(n, W)`, indexed by `A/n`
(`Stacks.Topology.Simplicial.DiagramOpen.sliceEquivalence`). Its component functor at an index
`φ : m ⟶ n` of that slice category is therefore the inclusion of the opens of the space
`(X φ)⁻¹W`, built in `Stacks.Topology.Simplicial.DiagramComponent`; it is continuous and
cocontinuous for the two topologies.

This file identifies that component with the degree-`m` component of the total site, restricted
to the open `(X φ)⁻¹W` of `X_m`: a presheaf on the total site, restricted to the slice and then
to the index `φ`, is its degree-`m` component restricted along the open immersion
`(X φ)⁻¹W ⊆ X_m`.

## Main definitions

* `Stacks.Topology.Simplicial.DiagramOpen.sliceLevelFunctor`: the component functor of the slice
  site at an index `φ : m ⟶ n` of the slice category, as a functor into the total site.
* `Stacks.Topology.Simplicial.DiagramOpen.sliceImageFunctor`: the open immersion
  `(X φ)⁻¹W ⊆ X_m` on opens.

## Main results

* `Stacks.Topology.Simplicial.DiagramOpen.sliceLevelFunctor_eq`: the component functor of the
  slice at `φ` is the composite of the open immersion with the degree-`m` component functor of
  the total site.
* `Stacks.Topology.Simplicial.DiagramOpen.componentSliceIso`: **the identification
  `(P|_{(n,W)})_φ ≅ P_m|_{(X φ)⁻¹W}`** for a presheaf `P` on the total site, valued in any
  category.

## Implementation notes

The comparison is an equality of site functors, not merely an isomorphism: both composites send
an open `P` of `(X φ)⁻¹W` to the object `(m, Subtype.val '' P)` of the total site, and both send
an inclusion to the levelwise arrow. So the identification of restrictions is `Iso.refl`, and the
content of the file is the equality `sliceLevelFunctor_eq`, which holds by `rfl` on objects and by
`DiagramOpen.Hom.ext` on arrows, the two index maps being the identity of `m`.

The restriction of a presheaf on the total site to the slice is restriction along
`sliceInverse X U ⋙ Over.forget U`, which is the functor sending an object of the slice site —
an index `φ : m ⟶ n` and an open of `(X φ)⁻¹W` — to the corresponding object `(m, V)` of the
total site. That is the composite the equality is stated about.

## References

* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w v₁ u₁

namespace Stacks.Topology.Simplicial.DiagramOpen

variable {A : Type u₁} [Category.{v₁} A] {X : A ⥤ TopCat.{u}} {U : DiagramOpen X}
variable {B : Type w} [Category.{v} B]

/-- The open immersion `(X φ)⁻¹W ⊆ X_m` on opens: an open of the space of the over-diagram at
`φ` is an open of `X_m`. -/
def sliceImageFunctor (φ : Over U.index) :
    Opens ((overSpace X U).obj φ) ⥤ Opens (X.obj φ.left) where
  obj P := sliceImage φ P
  map {P Q} h := homOfLE (by
    rintro y ⟨x, hx, rfl⟩
    exact mem_sliceImage (leOfHom h hx))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- **The component functor of the slice site at an index of the slice category**, read as a
functor into the total site: it sends an open of `(X φ)⁻¹W` to the object of the total site it
cuts out in degree `m`. -/
def sliceLevelFunctor (X : A ⥤ TopCat.{u}) (U : DiagramOpen X) (φ : Over U.index) :
    Opens ((overSpace X U).obj φ) ⥤ DiagramOpen X :=
  levelFunctor (overSpace X U) φ ⋙ sliceInverse X U ⋙ Over.forget U

/-- **The component functor of the slice at `φ` is the degree-`m` component functor of the total
site, precomposed with the open immersion `(X φ)⁻¹W ⊆ X_m`.** -/
theorem sliceLevelFunctor_eq (φ : Over U.index) :
    sliceLevelFunctor X U φ = sliceImageFunctor φ ⋙ levelFunctor X φ.left :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ =>
    Hom.ext _ _ ((Category.id_comp _).trans (Category.id_comp _)).symm)

/-- **The identification `(P|_{(n,W)})_φ ≅ P_m|_{(X φ)⁻¹W}`.** The degree-`φ` component of the
restriction of a presheaf on the total site to the slice at `(n, W)` is the degree-`m` component
of that presheaf, restricted along the open immersion `(X φ)⁻¹W ⊆ X_m`. -/
def componentSliceIso (P : (DiagramOpen X)ᵒᵖ ⥤ B) (φ : Over U.index) :
    componentPresheaf ((sliceInverse X U ⋙ Over.forget U).op ⋙ P) φ ≅
      (sliceImageFunctor φ).op ⋙ componentPresheaf P φ.left :=
  Iso.refl _

/-- The component functor of the slice site at an index of the slice category is continuous. -/
instance sliceLevelFunctor_isContinuous [IsoRigid A] (φ : Over U.index) :
    (levelFunctor (overSpace X U) φ).IsContinuous
      (Opens.grothendieckTopology ((overSpace X U).obj φ))
      (grothendieckTopology (overSpace X U)) :=
  levelFunctor_isContinuous (overSpace X U) φ

/-- The component functor of the slice site at an index of the slice category is
cocontinuous. -/
instance sliceLevelFunctor_isCocontinuous [IsoRigid A] (φ : Over U.index) :
    (levelFunctor (overSpace X U) φ).IsCocontinuous
      (Opens.grothendieckTopology ((overSpace X U).obj φ))
      (grothendieckTopology (overSpace X U)) :=
  levelFunctor_isCocontinuous (overSpace X U) φ

end Stacks.Topology.Simplicial.DiagramOpen

end
