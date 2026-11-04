module

public import StacksFrontier.AlgebraicGeometry.Groupoids.PairGroupoidDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.FunctionsOnIntersection
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantOpenBetween
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndQuasiAffineBaseChange

/-!
# The groupoid scheme of a descent datum, and its flatness hypotheses

Let `f : X ⟶ S` be a morphism of schemes and let `D` be a descent datum relative to `f`, with
underlying scheme `V` over `X`. Passing through the equivariant scheme of `D` for the pair
groupoid `(X, X ×_S X, s, t, c)` and then through the groupoid attached to an equivariant scheme
produces a groupoid scheme `G'` with object scheme `V` and arrow scheme `V ×_{X,t} (X ×_S X)`.

If `f` is flat and quasi-compact, `X` is affine and `V ⟶ X` is ind-quasi-affine, then the source
and target maps of `G'` are flat and quasi-compact and `V` is quasi-separated, so every
quasi-compact open of `V` lies between an invariant open and a quasi-compact open.

## Main results

* `AlgebraicGeometry.groupoidScheme_source_left_eq` : the source map of a groupoid scheme is its
  inverse map followed by its target map, on underlying schemes.
* `AlgebraicGeometry.flat_groupoidScheme_inverse_left` and
  `AlgebraicGeometry.quasiCompact_groupoidScheme_inverse_left` : the inverse map of a groupoid
  scheme is flat and quasi-compact.
* `AlgebraicGeometry.flat_equivariantActionGroupoid_target_left`,
  `AlgebraicGeometry.quasiCompact_equivariantActionGroupoid_target_left`,
  `AlgebraicGeometry.flat_equivariantActionGroupoid_source_left` and
  `AlgebraicGeometry.quasiCompact_equivariantActionGroupoid_source_left` : the source and target
  maps of the groupoid attached to an equivariant scheme inherit flatness and quasi-compactness
  from the target map of the ambient groupoid.
* `AlgebraicGeometry.flat_pairGroupoid_target_left`,
  `AlgebraicGeometry.quasiCompact_pairGroupoid_target_left`,
  `AlgebraicGeometry.flat_pairGroupoid_source_left` and
  `AlgebraicGeometry.quasiCompact_pairGroupoid_source_left` : the source and target maps of a
  pair groupoid inherit flatness and quasi-compactness from the morphism itself.
* `AlgebraicGeometry.isIndQuasiAffine_of_isIndQuasiAffineHom_hom` : over an affine base, the
  scheme underlying a descent datum whose structure morphism is ind-quasi-affine is itself
  ind-quasi-affine.
* `AlgebraicGeometry.quasiSeparatedSpace_descentDatumGroupoid_objects_left` : the object scheme
  of `G'` is quasi-separated in that situation.
* `AlgebraicGeometry.exists_isInvariantOpen_isCompact_between_descentDatumGroupoid` : every
  quasi-compact open of the object scheme of `G'` lies between an invariant open and a
  quasi-compact open.

## References

* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0APF](https://stacks.math.columbia.edu/tag/0APF)
* [Stacks Project, Tag 0APB](https://stacks.math.columbia.edu/tag/0APB)
* [Stacks Project, Tag 0AP6](https://stacks.math.columbia.edu/tag/0AP6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The source map of a groupoid scheme is its inverse map followed by its target map, read on
underlying schemes. -/
theorem groupoidScheme_source_left_eq {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.source.left = G.inverse.left ≫ G.target.left := by
  rw [← Over.comp_left, G.target_inverse]

/-- The inverse map of a groupoid scheme is flat. -/
instance flat_groupoidScheme_inverse_left {S : Scheme.{u}} (G : GroupoidScheme S) :
    Flat G.inverse.left :=
  haveI := groupoidInverse_left_isIso G
  inferInstance

/-- The inverse map of a groupoid scheme is quasi-compact. -/
instance quasiCompact_groupoidScheme_inverse_left {S : Scheme.{u}} (G : GroupoidScheme S) :
    QuasiCompact G.inverse.left :=
  haveI := groupoidInverse_left_isIso G
  inferInstance

section Equivariant

variable {S : Scheme.{u}} {G : GroupoidScheme S}

/-- The target map of the groupoid attached to an equivariant scheme is flat when the target map
of the ambient groupoid is. -/
instance flat_equivariantActionGroupoid_target_left (V : EquivariantScheme G)
    [Flat G.target.left] : Flat (equivariantActionGroupoid V).target.left := by
  change Flat (pullback.fst (equivariantObjectMap V) G.target).left
  rw [← overPullbackLeftIso_hom_fst]
  infer_instance

/-- The target map of the groupoid attached to an equivariant scheme is quasi-compact when the
target map of the ambient groupoid is. -/
instance quasiCompact_equivariantActionGroupoid_target_left (V : EquivariantScheme G)
    [QuasiCompact G.target.left] :
    QuasiCompact (equivariantActionGroupoid V).target.left := by
  change QuasiCompact (pullback.fst (equivariantObjectMap V) G.target).left
  rw [← overPullbackLeftIso_hom_fst]
  infer_instance

/-- The source map of the groupoid attached to an equivariant scheme is flat when the target map
of the ambient groupoid is. -/
instance flat_equivariantActionGroupoid_source_left (V : EquivariantScheme G)
    [Flat G.target.left] : Flat (equivariantActionGroupoid V).source.left := by
  rw [groupoidScheme_source_left_eq]
  infer_instance

/-- The source map of the groupoid attached to an equivariant scheme is quasi-compact when the
target map of the ambient groupoid is. -/
instance quasiCompact_equivariantActionGroupoid_source_left (V : EquivariantScheme G)
    [QuasiCompact G.target.left] :
    QuasiCompact (equivariantActionGroupoid V).source.left := by
  rw [groupoidScheme_source_left_eq]
  infer_instance

end Equivariant

section PairGroupoid

variable {S X : Scheme.{u}}

/-- The target map of the pair groupoid of `f`, the first projection of `X ×_S X`, is flat when
`f` is. -/
instance flat_pairGroupoid_target_left (f : X ⟶ S) [Flat f] :
    Flat (pairGroupoid f).target.left := by
  change Flat (pullback.fst f f)
  infer_instance

/-- The target map of the pair groupoid of `f`, the first projection of `X ×_S X`, is
quasi-compact when `f` is. -/
instance quasiCompact_pairGroupoid_target_left (f : X ⟶ S) [QuasiCompact f] :
    QuasiCompact (pairGroupoid f).target.left := by
  change QuasiCompact (pullback.fst f f)
  infer_instance

/-- The source map of the pair groupoid of `f`, the second projection of `X ×_S X`, is flat when
`f` is. -/
instance flat_pairGroupoid_source_left (f : X ⟶ S) [Flat f] :
    Flat (pairGroupoid f).source.left := by
  change Flat (pullback.snd f f)
  infer_instance

/-- The source map of the pair groupoid of `f`, the second projection of `X ×_S X`, is
quasi-compact when `f` is. -/
instance quasiCompact_pairGroupoid_source_left (f : X ⟶ S) [QuasiCompact f] :
    QuasiCompact (pairGroupoid f).source.left := by
  change QuasiCompact (pullback.snd f f)
  infer_instance

end PairGroupoid

section IndQuasiAffine

variable {S X : Scheme.{u}} {f : X ⟶ S}

/-- Over an affine base, a scheme whose structure morphism is ind-quasi-affine is itself
ind-quasi-affine. -/
theorem isIndQuasiAffine_of_isIndQuasiAffineHom_hom [IsAffine X] (V : Over X)
    [IsIndQuasiAffineHom V.hom] : IsIndQuasiAffine V.left :=
  (@HasAffineProperty.iff_of_isAffine _ _ hasAffineProperty_isIndQuasiAffineHom
    _ _ V.hom _).mp inferInstance

/-- The object scheme of the groupoid of a descent datum is quasi-separated as soon as the scheme
underlying the datum is ind-quasi-affine. -/
instance quasiSeparatedSpace_descentDatumGroupoid_objects_left (D : DescentDatum f)
    [IsIndQuasiAffine D.over.left] :
    QuasiSeparatedSpace
      (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left :=
  quasiSeparatedSpace_of_isIndQuasiAffine D.over.left

/-- Let `f : X ⟶ S` be flat and quasi-compact with `X` affine, and let `D` be a descent datum
relative to `f` whose underlying scheme `V` is ind-quasi-affine over `X`. Then every
quasi-compact open of `V` is contained in an open invariant under the groupoid of `D`, which in
turn is contained in a quasi-compact open. -/
theorem exists_isInvariantOpen_isCompact_between_descentDatumGroupoid
    [IsAffine X] [Flat f] [QuasiCompact f] (D : DescentDatum f)
    [IsIndQuasiAffineHom D.over.hom]
    (W : (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left.Opens)
    (hW : IsCompact
      (W : Set (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left)) :
    ∃ V W' : (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left.Opens,
      IsInvariantOpen (equivariantActionGroupoid (descentDatumToEquivariant D)) V ∧
        IsCompact
          (W' : Set (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left) ∧
        (W : Set (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left) ⊆
          (V : Set (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left) ∧
        (V : Set (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left) ⊆
          (W' : Set (equivariantActionGroupoid (descentDatumToEquivariant D)).objects.left) :=
  have := isIndQuasiAffine_of_isIndQuasiAffineHom_hom D.over
  GroupoidScheme.exists_isInvariantOpen_isCompact_between _ W hW

end IndQuasiAffine

end AlgebraicGeometry

end
