module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence

/-!
# The Koszul locus of a morphism of algebraic spaces

For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the set of points of `|X|`
at which `f` is Koszul is an open subset of the point space of Tag 03BU, and it is therefore
the point set of an open subspace `U(f) ⊂ X`.

## Main definitions

* `AlgebraicGeometry.Space.koszulOpenSubspace` is the open subspace `U(f)` of the source cut
  out by the Koszul points of `f`.

## Main results

* `AlgebraicGeometry.Space.isOpen_setOf_koszulAt`: the Koszul locus is open in `|X|`.
* `AlgebraicGeometry.Space.isOpenSubspace_koszulOpenSubspace` and
  `AlgebraicGeometry.Space.range_pointsMap_ι_koszulOpenSubspace`: `U(f)` is an open subspace
  of `X` and its point set is exactly the Koszul locus. Together they are
  `AlgebraicGeometry.Space.exists_isOpenSubspace_range_pointsMap_eq_setOf_koszulAt`, the
  first assertion of Tag 06CA.

## Implementation notes

`U(f)` is not obtained from the existence statement of Tag 03BZ. It is the subfunctor
`AlgebraicGeometry.Space.openSubspaceOfPoints` of
`StacksFrontier/AlgebraicGeometry/Spaces/OpenSubspaceCorrespondence.lean`, whose sections over an
object of the site are the sections of `X` all of whose points are Koszul points of `f`. That
subfunctor is defined for an arbitrary set of points, so it has a defining equation, and its
point set is the given set with no hypothesis at all; openness of the Koszul locus and
algebraicity of `X` enter only in the proof that it is an open subspace.

Openness of the Koszul locus is the step the source records as holding "by Definition 06C4":
being Koszul at `x` asks for an open subspace of `X` through `x` on which `f` restricts to a
local complete intersection morphism, and that one witness serves every point of the witness,
so the locus is a union of point sets of open subspaces. Those are open by Tag 03BZ in the
form `AlgebraicGeometry.Space.isOpen_range_pointsMap_of_isOpenImmersion`. In particular this
part of Tag 06CA needs neither the commutative triangle nor flatness and local finite
presentation over its base; it holds for every morphism of presheaves whose source is an
algebraic space, and the statements below are at that generality.

## References

* [Stacks Project, Tag 06CA](https://stacks.math.columbia.edu/tag/06CA)
* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The Koszul locus of a morphism of algebraic spaces is open in the point space of its
source.

A witness for `AlgebraicGeometry.Space.KoszulAt f x` is an open subspace `U` of `X` through
`x` with `f|_U` a local complete intersection morphism, and the same `U` witnesses the Koszul
property at every point of `|U|`. So the point set of `U` is an open neighbourhood of `x`
inside the locus. -/
theorem isOpen_setOf_koszulAt (f : X ⟶ Y) :
    IsOpen {x : points B S hS X | KoszulAt B S hS f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨U, hU, x', hx', hlci⟩
  refine ⟨Set.range (pointsMap B S hS U.toFunctor U.ι), ?_,
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2, ⟨x', hx'⟩⟩
  rintro y ⟨y', rfl⟩
  exact ⟨U, hU, y', rfl, hlci⟩

variable (X) in
/-- **Stacks 06CA, part (1).** The open subspace `U(f) ⊂ X` of the Koszul points of a
morphism `f : X ⟶ Y` of algebraic spaces: the subfunctor of the source whose sections are
those all of whose points are Koszul points of `f`. -/
@[stacks 06CA "part (1): the open subspace of Koszul points"]
def koszulOpenSubspace (f : X ⟶ Y) : Subfunctor X :=
  openSubspaceOfPoints B S hS X {x | KoszulAt B S hS f x}

/-- **Stacks 06CA, part (1).** The point set of `U(f)` is the set of points at which `f` is
Koszul. -/
@[stacks 06CA "part (1): the open subspace of Koszul points"]
theorem range_pointsMap_ι_koszulOpenSubspace (f : X ⟶ Y) :
    Set.range (pointsMap B S hS (koszulOpenSubspace B S hS X f).toFunctor
      (koszulOpenSubspace B S hS X f).ι) = {x | KoszulAt B S hS f x} :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS {x | KoszulAt B S hS f x}

/-- **Stacks 06CA, part (1).** `U(f)` is an open subspace of the source. -/
@[stacks 06CA "part (1): the open subspace of Koszul points"]
theorem isOpenSubspace_koszulOpenSubspace (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsOpenSubspace B S hS (koszulOpenSubspace B S hS X f) :=
  isOpenSubspace_openSubspaceOfPoints B S hS hX {x | KoszulAt B S hS f x}
    (isOpen_setOf_koszulAt B S hS f)

/-- **Stacks 06CA, part (1).** There is an open subspace of the source of a morphism of
algebraic spaces whose point set is exactly the set of points at which the morphism is
Koszul. -/
@[stacks 06CA "part (1): the open subspace of Koszul points"]
theorem exists_isOpenSubspace_range_pointsMap_eq_setOf_koszulAt
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    ∃ U : Subfunctor X, IsOpenSubspace B S hS U ∧
      Set.range (pointsMap B S hS U.toFunctor U.ι) = {x | KoszulAt B S hS f x} :=
  ⟨koszulOpenSubspace B S hS X f, isOpenSubspace_koszulOpenSubspace B S hS hX f,
    range_pointsMap_ι_koszulOpenSubspace B S hS f⟩

/-! ### Behaviour under preimage -/

/-- The subfunctor cut out by a set of points commutes with preimage: pulling
`AlgebraicGeometry.Space.openSubspaceOfPoints` back along a morphism gives the subfunctor cut
out by the preimage of the set of points.

A section of the source lies in the preimage exactly when all of its points map into the set,
and its points map to the points of its image. -/
theorem openSubspaceOfPoints_preimage {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (q : F' ⟶ F)
    (W : Set (points B S hS F)) :
    (openSubspaceOfPoints B S hS F W).preimage q =
      openSubspaceOfPoints B S hS F' (pointsMap B S hS F' q ⁻¹' W) := by
  ext T x
  rw [Subfunctor.preimage_obj, Set.mem_preimage, mem_openSubspaceOfPoints_iff,
    mem_openSubspaceOfPoints_iff, ← yonedaEquiv_symm_naturality_right T.unop q x, pointsMap_comp,
    Set.range_comp, Set.image_subset_iff]

/-- The equality of open subspaces asserted by the second part of Tag 06CA is the equality of
their point sets: forming `AlgebraicGeometry.Space.koszulOpenSubspace` commutes with preimage
along a morphism exactly to the extent that the Koszul locus does.

This is the specialization of `AlgebraicGeometry.Space.openSubspaceOfPoints_preimage` to the
Koszul locus, and it needs no hypothesis on the morphism. -/
theorem koszulOpenSubspace_eq_preimage_of_setOf_koszulAt_eq
    {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (f' : X' ⟶ Y') (pr : X' ⟶ X)
    (hpt : {x' | KoszulAt B S hS f' x'} =
      pointsMap B S hS X' pr ⁻¹' {x | KoszulAt B S hS f x}) :
    koszulOpenSubspace B S hS X' f' = (koszulOpenSubspace B S hS X f).preimage pr := by
  rw [koszulOpenSubspace, koszulOpenSubspace, openSubspaceOfPoints_preimage, hpt]

end AlgebraicGeometry.Space

end
