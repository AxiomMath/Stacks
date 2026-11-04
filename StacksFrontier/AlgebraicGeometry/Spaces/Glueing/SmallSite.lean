module

public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsCardinalClosure
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Size.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite

/-!
# The big fppf site over a scheme is essentially small, and its topology is subcanonical

Two size facts about the big fppf site of a scheme `S` inside a big fppf site `B`. First,
the schemes of size below a cardinal cutoff form an essentially small full subcategory of
schemes, hence so does the slice over `S`; this is what makes sheafification available on
the slice. Second, the topology of the slice is subcanonical, so representable presheaves on
it are sheaves.

## Main results

* `AlgebraicGeometry.essentiallySmall_affineSchemes_of_cardinalLT`: the affine schemes with a
  coordinate ring of bounded cardinality form an essentially small object property.
* `AlgebraicGeometry.bigFppfOver_subcanonical`: the topology of the big fppf category
  over `S` is subcanonical.

## Implementation notes

The affine schemes of bounded cardinality are indexed by the commutative ring structures on
subsets of a set of the given cardinality, which is what makes them essentially small.
Essential smallness of the size cutoff itself is
`AlgebraicGeometry.essentiallySmall_schemeSizeBelow`: a scheme of bounded size is the colimit
of its affine Zariski site, which is thin and of bounded arrow cardinality, so the scheme
lies in the closure of the bounded affines under colimits of bounded shape.

Subcanonicity of the slice is subcanonicity of the topology of `B`, which is
`AlgebraicGeometry.BigFppfSite.subcanonical_topology`, together with
`CategoryTheory.GrothendieckTopology.subcanonical_over`.
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The affine schemes whose coordinate ring has cardinality below a cardinal `κ` form an
essentially small object property: every such scheme is the spectrum of a commutative ring
structure on a subset of a fixed set of cardinality `κ`. -/
theorem essentiallySmall_affineSchemes_of_cardinalLT (κ : Cardinal.{u}) :
    ObjectProperty.EssentiallySmall.{u}
      (fun X : Scheme.{u} => ∃ A : CommRingCat.{u}, #A < κ ∧ Nonempty (X ≅ Spec A)) := by
  classical
  let A := Σ T : Set κ.out, CommRing T
  let D : A → Scheme.{u} := fun a =>
    @Scheme.Spec.obj (Opposite.op (@CommRingCat.of a.1 a.2))
  refine ⟨ObjectProperty.ofObj D, inferInstance, ?_⟩
  intro X ⟨R, hκ, ⟨hX⟩⟩
  obtain ⟨f⟩ : Nonempty (R ↪ κ.out) := by
    apply (Cardinal.le_def _ _).mp
    simpa only [Cardinal.mk_out] using hκ.le
  let e : Set.range f ≃ R := (Equiv.ofInjective f f.injective).symm
  let : CommRing (Set.range f) := e.commRing
  let a : A := ⟨Set.range f, e.commRing⟩
  refine ⟨D a, ⟨a⟩, ⟨?_⟩⟩
  exact hX ≪≫ Scheme.Spec.mapIso e.ringEquiv.toCommRingCatIso.op

/-- The topology of the big fppf category over `S` is subcanonical. -/
theorem bigFppfOver_subcanonical (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : (BigFppfOver.topology B S hS).Subcanonical := by
  let : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  exact GrothendieckTopology.subcanonical_over B.topology (B.obj hS)

end AlgebraicGeometry

end
