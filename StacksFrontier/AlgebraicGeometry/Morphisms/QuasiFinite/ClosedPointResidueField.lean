module

public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField

/-!
# Closed points of the source and residue field extensions

A point that is closed in the whole source of a morphism is in particular closed in its own
scheme-theoretic fibre, the fibre carrying the subspace topology. For a morphism locally of
finite type this upgrades, through
`AlgebraicGeometry.isClosed_asFiber_iff_finite_residueField`, to finiteness of the residue
field extension at that point.

## Main results

* `AlgebraicGeometry.isClosed_asFiber_of_isClosed`: a point closed in the source is closed in
  its fibre, for an arbitrary morphism of schemes.
* `AlgebraicGeometry.finite_residueField_of_isClosed`: for a morphism locally of finite type,
  the residue field at a point closed in the source is finite over the residue field at its
  image.

## Implementation notes

Neither statement constrains the image point: closedness of `x` in the source already pins the
fibre down, so no hypothesis on `f x` is needed. The case most often cited — `x` closed in the
source lying over a closed point of the target — is therefore the special case obtained by
simply ignoring the extra hypothesis.

As elsewhere in this directory the algebra structure on `κ(x)` over `κ(f x)` is the canonical
one induced by `Scheme.Hom.residueFieldMap`, introduced by a `letI` inside the statement.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- A point closed in the source of a morphism of schemes is closed in its scheme-theoretic
fibre, since the fibre maps to the source by a topological embedding carrying the point to it. -/
public theorem isClosed_asFiber_of_isClosed (f : X ⟶ S) {x : X}
    (hx : IsClosed ({x} : Set X)) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  have hpre : (f.fiberι (f x)) ⁻¹' ({x} : Set X) = {f.asFiber x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (f.fiberι _).isEmbedding.injective.eq_iff' (f.fiberι_asFiber x)
  rw [← hpre]
  exact hx.preimage (f.fiberι _).continuous

/-- For a morphism locally of finite type, the residue field at a point closed in the source is
a finite extension of the residue field at its image. -/
public theorem finite_residueField_of_isClosed (f : X ⟶ S) [LocallyOfFiniteType f] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    Module.Finite (S.residueField (f x)) (X.residueField x) :=
  (isClosed_asFiber_iff_finite_residueField f x).mp (isClosed_asFiber_of_isClosed f hx)

end AlgebraicGeometry
