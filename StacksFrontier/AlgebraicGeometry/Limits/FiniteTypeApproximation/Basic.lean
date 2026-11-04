module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.CompatibleOpens

/-!
# Finite-type approximation of a scheme relative to a quasi-compact open

Let `S` be a quasi-compact and quasi-separated scheme and let `U ⊆ S` be a quasi-compact open
subscheme.  Suppose `U` is the inverse limit of a directed system `D` of schemes of finite
type over `Spec ℤ` with affine transition morphisms.  Noetherian approximation asserts that
this system extends to such a system approximating `S`, compatibly with `D` on `U`.

`AlgebraicGeometry.Scheme.FiniteTypeApproximation` is the bundle of data and properties that
such an extension consists of.  A directed inverse system indexed by a preorder `J` is
represented by a functor out of `Jᵒᵈ`; the reindexing is an order homomorphism; the open
subschemes at the finite stages are a natural transformation with open-immersion components,
and the inverse-image condition is cartesianness of the naturality squares.  Finite type over
`Spec ℤ` is expressed, following Mathlib's convention, by `LocallyOfFiniteType` together with
`QuasiCompact` for the structural morphism to the terminal scheme.

Also here are the two ingredients of the degenerate input `U = ⊥` that absolute Noetherian
approximation feeds to this statement: `AlgebraicGeometry.Scheme.botDiagram`, the system with a
single index constant at the empty open subscheme, and
`AlgebraicGeometry.Scheme.isLimitConstConePUnit`, which exhibits a scheme as the limit of the
system constant at it over a one-object index.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The data and properties of an extension of a directed finite-type inverse system on a
quasi-compact open subscheme `U ⊆ S`, with affine transition morphisms, to such a system on
the ambient scheme `S`.

The field `comparison` records the stagewise identifications of the open subsystem with the
reindexed original system, and `inclusion_compatibility`, `comparison_compatibility` record
the two commutativities required in the Stacks statement. -/
structure FiniteTypeApproximation
    {I : Type u} [Preorder I]
    (D : Iᵒᵈ ⥤ Scheme.{u}) (S : Scheme.{u}) (U : S.Opens)
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D) where
  /-- The directed preorder indexing the extended inverse system. -/
  indexType : Type u
  /-- The preorder on the new index type. -/
  [indexPreorder : Preorder indexType]
  /-- The new index type is nonempty. -/
  [indexNonempty : Nonempty indexType]
  /-- The new index type is directed. -/
  [indexDirected : IsDirected indexType (· ≤ ·)]
  /-- The order-preserving map from the new index preorder to the original one. -/
  index : indexType →o I
  /-- The inverse system approximating the ambient scheme. -/
  ambient : indexTypeᵒᵈ ⥤ Scheme.{u}
  /-- The compatible inverse system of open subschemes. -/
  openPart : indexTypeᵒᵈ ⥤ Scheme.{u}
  /-- The open immersion of the open subsystem into the ambient subsystem. -/
  inclusion : openPart ⟶ ambient
  /-- The stagewise identifications with the reindexed original inverse system. -/
  comparison : openPart ≅ index.monotone.dual.functor ⋙ D
  /-- The limiting cone from the ambient scheme. -/
  ambientCone : (Functor.const indexTypeᵒᵈ).obj S ⟶ ambient
  /-- The limiting cone from the given open subscheme. -/
  openCone : (Functor.const indexTypeᵒᵈ).obj (U : Scheme.{u}) ⟶ openPart
  /-- The transition morphisms of the ambient system are affine. -/
  transition_affine : ∀ {j j' : indexTypeᵒᵈ} (f : j ⟶ j'), IsAffineHom (ambient.map f)
  /-- Each stage of the ambient system is locally of finite type over the terminal scheme. -/
  locallyOfFiniteType : ∀ j, LocallyOfFiniteType (terminal.from (ambient.obj j))
  /-- Each stage of the ambient system is quasi-compact over the terminal scheme. -/
  quasiCompact : ∀ j, QuasiCompact (terminal.from (ambient.obj j))
  /-- The components of the inclusion are open immersions. -/
  inclusion_isOpenImmersion : ∀ j, IsOpenImmersion (inclusion.app j)
  /-- The open subschemes are the inverse images of one another. -/
  transition_isPullback : ∀ {j j' : indexTypeᵒᵈ} (f : j ⟶ j'),
    IsPullback (openPart.map f) (inclusion.app j) (inclusion.app j') (ambient.map f)
  /-- The ambient scheme is the inverse limit of the ambient system. -/
  ambientCone_isLimit : IsLimit (Cone.mk S ambientCone)
  /-- The open subscheme is the inverse limit of the open subsystem. -/
  openCone_isLimit : IsLimit (Cone.mk (U : Scheme.{u}) openCone)
  /-- The open immersions are compatible with the two limiting cones. -/
  inclusion_compatibility : ∀ j, U.ι ≫ ambientCone.app j = openCone.app j ≫ inclusion.app j
  /-- The identifications are compatible with the given cone on the original system. -/
  comparison_compatibility : ∀ j,
    openCone.app j ≫ comparison.hom.app j = p.app (index.monotone.dual.functor.obj j)

/-- The inverse system with a single index whose value is the empty open subscheme of `S`.

This is `@[reducible]` because the cone on it is written `𝟙 _`, whose type matches only after
unfolding; a `FiniteTypeApproximation` over such a cone would otherwise be opaque to instance
search, which unifies at reducible transparency only. -/
@[reducible] def botDiagram (S : Scheme.{u}) : PUnit.{u + 1}ᵒᵈ ⥤ Scheme.{u} :=
  (Functor.const _).obj ((⊥ : S.Opens) : Scheme.{u})

/-- The identity cone on a constant inverse system indexed by a single element is a limit
cone. -/
noncomputable def isLimitConstConePUnit (Z : Scheme.{u}) :
    IsLimit (Cone.mk Z (𝟙 ((Functor.const PUnit.{u + 1}ᵒᵈ).obj Z))) where
  lift s := s.π.app (OrderDual.toDual PUnit.unit)
  fac s j := by
    obtain rfl : j = OrderDual.toDual PUnit.unit := rfl
    simp
  uniq s m h := by simpa using h (OrderDual.toDual PUnit.unit)

end AlgebraicGeometry.Scheme
