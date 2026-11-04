module

public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAffineComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModulePropagation

/-!
# Propagating agreement of maps of associated modules off the affine charts of a slice

Let `X` be an étale chart of an algebraic space. On the slice of the small étale site at `X`, the
arrows factoring through an object with affine underlying scheme form a covering sieve, by the
cover density of the affine étale charts ([Stacks, Tag 04JS]). Consequently two maps `Mᵃ ⟶ Nᵃ` of
associated presheaves of modules on the slice agree as soon as they agree over the objects with
affine underlying scheme, provided `Nᵃ` is a sheaf.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.coverByImage_isAffine_mem_slice`: the arrows of the slice
  at a chart which factor through an object with affine underlying scheme form a covering sieve.
* `AlgebraicGeometry.Space.SmallEtale.hom_ext_associatedModulePresheaf_slice`: a map of
  associated presheaves of modules on the slice is determined by its components at the objects
  with affine underlying scheme.
* `AlgebraicGeometry.Space.SmallEtale.surjective_associatedModuleMap_slice`: if every map
  `Mᵃ ⟶ Nᵃ` agrees over the affine objects with the map induced by a morphism `M ⟶ N`, then every
  such map is induced by a morphism `M ⟶ N`.

## Implementation notes

The affineness condition is written `IsAffine (chartScheme Z.left)`, which is the condition
`IsAffine ((sliceToOver B S hS F X).obj Z).left` of the general statements by `rfl`:
`AlgebraicGeometry.Space.SmallEtale.sliceToOver` is `CategoryTheory.Over.post` of the functor
computing the underlying scheme of a chart.

## References

* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.SmallEtale

open _root_.AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (X : SmallEtale B S hS F)

/-! ### The affine objects of the slice cover -/

include hF in
/-- The arrows of the slice of the small étale site at a chart `X` which factor through an object
with affine underlying scheme form a covering sieve. -/
public theorem coverByImage_isAffine_mem_slice (Z : Over X) :
    Sieve.coverByImage
      (ObjectProperty.ι (fun W : Over X ↦
        IsAffine ((sliceToOver B S hS F X).obj W).left)) Z ∈ ((topology B S hS F).over X) Z := by
  refine ((topology B S hS F).over X).superset_covering ?_
    (coverByImage_affineEtale_mem_over B S hS F hF X Z)
  rintro W g ⟨⟨A, lift, map, fac⟩⟩
  refine ⟨⟨⟨Over.mk (map ≫ Z.hom), A.property⟩, Over.homMk lift ?_, Over.homMk map ?_, ?_⟩⟩
  · show lift ≫ map ≫ Z.hom = W.hom
    rw [← Category.assoc, fac]
    exact Over.w g
  · rfl
  · exact Over.OverMorphism.ext (by simpa using fac)

/-! ### Propagation and the fullness clause on the slice -/

include hF in
/-- Let `M`, `N` be quasi-coherent modules on the scheme underlying a chart `X` of an algebraic
space, and suppose the associated presheaf of `N` on the slice of the small étale site at `X` is a
sheaf. Then two maps `Mᵃ ⟶ Nᵃ` of associated presheaves of modules on the slice which agree over
the objects with affine underlying scheme are equal. -/
public theorem hom_ext_associatedModulePresheaf_slice
    {M N : (chartScheme X).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) N (sliceToOver B S hS F X)))
    {a b : Stacks.Sites.associatedModulePresheaf (chartScheme X) M
        (sliceToOver B S hS F X) ⟶
      Stacks.Sites.associatedModulePresheaf (chartScheme X) N
        (sliceToOver B S hS F X)}
    (h : ∀ Z : Over X, IsAffine (chartScheme Z.left) →
      a.app (op Z) = b.app (op Z)) :
    a = b :=
  Stacks.Sites.hom_ext_associatedModulePresheaf_of_isAffine (chartScheme X)
    (sliceToOver B S hS F X) ((topology B S hS F).over X) hN
    (coverByImage_isAffine_mem_slice B S hS F hF X) h

include hF in
/-- Suppose the associated presheaf of `N` on the slice of the small étale site at `X` is a sheaf.
If every map `Mᵃ ⟶ Nᵃ` of associated presheaves of modules on the slice at `X` agrees, over the
objects of the slice with affine underlying scheme, with the map induced by some morphism
`M ⟶ N`, then every such map is induced by a morphism `M ⟶ N`. -/
public theorem surjective_associatedModuleMap_slice
    {M N : (chartScheme X).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf ((topology B S hS F).over X)
      (Stacks.Sites.associatedPresheaf (chartScheme X) N (sliceToOver B S hS F X)))
    (haff : ∀ a : Stacks.Sites.associatedModulePresheaf (chartScheme X) M
          (sliceToOver B S hS F X) ⟶
        Stacks.Sites.associatedModulePresheaf (chartScheme X) N
          (sliceToOver B S hS F X),
      ∃ φ : M ⟶ N, ∀ Z : Over X, IsAffine (chartScheme Z.left) →
        (Stacks.Sites.associatedModuleMap (chartScheme X)
          (sliceToOver B S hS F X) φ).app (op Z) = a.app (op Z)) :
    Function.Surjective fun φ : M ⟶ N =>
      Stacks.Sites.associatedModuleMap (chartScheme X) (sliceToOver B S hS F X) φ :=
  Stacks.Sites.surjective_associatedModuleMap_of_isAffine (chartScheme X)
    (sliceToOver B S hS F X) ((topology B S hS F).over X) hN
    (coverByImage_isAffine_mem_slice B S hS F hF X) haff

end AlgebraicGeometry.Space.SmallEtale

end
