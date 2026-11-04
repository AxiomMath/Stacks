module

public import StacksFrontier.AlgebraicGeometry.InvertibleFunctions.ProperVariety
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic

/-!
# Invertible functions on a normal open subscheme of a proper variety

Stacks Tag 04L4: for `k` an algebraically closed field, `Xbar` a proper variety over `k` and
`X ⊆ Xbar` a normal open subscheme, the group `𝒪^*(X)/k^*` is finitely generated.

`AlgebraicGeometry.fg_units_quotient_of_exists_normal_model`
(`StacksFrontier/AlgebraicGeometry/InvertibleFunctions/ProperVariety.lean`) proves this with the
reduction to a normal ambient variety taken as a hypothesis, and
`AlgebraicGeometry.exists_normal_properVariety_model`
(`StacksFrontier/AlgebraicGeometry/NormalProperModel/Basic.lean`) discharges that hypothesis by
replacing `Xbar` with its normalization. This file is their composition, which is the tag.

## Main results

* `AlgebraicGeometry.fg_units_quotient_of_isOpenImmersion_into_properVariety`: Tag 04L4.

## References

* [Stacks Project, Tag 04L4](https://stacks.math.columbia.edu/tag/04L4)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04L4.** Let `k` be an algebraically closed field, let `Xbar` be a
proper variety over `k`, and let `X` be a normal open subscheme of `Xbar`. Then the group of
invertible global functions on `X`, modulo the constants coming from `k`, is finitely generated.

The ambient proper variety may be replaced by its normalization, which is again a proper variety
over `k` and is normal, and over the normal open `X` the normalization morphism is an
isomorphism; so the statement follows from the case of a normal ambient variety. -/
@[stacks 04L4]
theorem fg_units_quotient_of_isOpenImmersion_into_properVariety
    (k : Type u) [Field k] [IsAlgClosed k] {X Xbar : Scheme.{u}}
    (f : Xbar ⟶ Spec (.of k)) [IsProperVariety k f]
    (i : X ⟶ Xbar) [IsOpenImmersion i] [IsNormal X] :
    let φ : k →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ f).appTop).hom
    Group.FG (Units Γ(X, ⊤) ⧸ (Units.map φ.toMonoidHom).range) :=
  fg_units_quotient_of_exists_normal_model k f i (exists_normal_properVariety_model k f i)

end AlgebraicGeometry

end
