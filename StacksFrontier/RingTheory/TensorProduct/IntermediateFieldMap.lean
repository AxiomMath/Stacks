module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensoring the inclusion of an intermediate field with an algebra

Let `L / k` be a field extension, let `F` be an intermediate field and let `R` be a `k`-algebra.
Tensoring the inclusion `F ⊆ L` with the identity of `R` gives an algebra map
`IntermediateField.tensorInclusion : F ⊗[k] R →ₐ[k] L ⊗[k] R`, and
`IntermediateField.tensorInclusionRange` is its image as a subring of `L ⊗[k] R`.

Writing `L ⊗[k] R` as the union of these subrings over the finitely generated `F` is how
properties of `L ⊗[k] R` are reduced to the finitely generated case.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace IntermediateField

/-- The inclusion `F ⊗[k] R →ₐ[k] L ⊗[k] R` obtained by tensoring the inclusion of an
intermediate field `F` of `L / k` with the identity of a `k`-algebra `R`. -/
def tensorInclusion {k L R : Type*} [Field k] [Field L] [Algebra k L]
    [CommRing R] [Algebra k R] (F : IntermediateField k L) :
    ↥F ⊗[k] R →ₐ[k] L ⊗[k] R :=
  Algebra.TensorProduct.map F.val (AlgHom.id k R)

/-- The image of `IntermediateField.tensorInclusion`, as a subring of `L ⊗[k] R`. -/
def tensorInclusionRange {k L R : Type*} [Field k] [Field L] [Algebra k L]
    [CommRing R] [Algebra k R] (F : IntermediateField k L) :
    Subring (L ⊗[k] R) :=
  (F.tensorInclusion (R := R)).range.toSubring

end IntermediateField
