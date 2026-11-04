module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Etale.Field
public import StacksCore.Tactic.StacksAttribute

/-!
# The fibre of an étale morphism of affines over a point is reduced

Let `R → A` be a ring map which is unramified and essentially of finite type — an étale ring map
is both — and let `K` be a field which is an `R`-algebra.  Then `A ⊗_R K` is étale over `K`, and
an algebra which is unramified and essentially of finite type over a field is a finite product of
finite separable field extensions, hence reduced.

Geometrically: if `E' ⟶ S` is an étale morphism of affine schemes and `s` is a point of `S`, the
fibre `E'_s = \Spec (\Gamma(E', ⊤) ⊗_{\Gamma(S, ⊤)} κ(s))` is reduced.

## Main results

* `Algebra.FormallyUnramified.isReduced_tensorProduct_of_field`: for `A` unramified and
  essentially of finite type over `R` and `K` a field over `R`, the ring `A ⊗_R K` is reduced.
* `AlgebraicGeometry.isReduced_appTop_tensorProduct_residueField`: the same for the global
  sections of an étale morphism of affine schemes tensored with the residue field of a point of
  the target.

## Implementation notes

Mathlib supplies the whole mathematical content.  `Algebra.FormallyUnramified.isReduced_of_field`
is reducedness of an unramified essentially-of-finite-type algebra over a field, and the base
change instances `Algebra.FormallyUnramified.base_change` and `Algebra.EssFiniteType.baseChange`
put the fibre in that situation.  Both of those put the new base ring on the **left** of the
tensor product, so they prove `IsReduced (K ⊗_R A)`; the orientation `A ⊗_R K` wanted downstream
is obtained from it through `Algebra.TensorProduct.comm`, which is a ring isomorphism, and
reducedness transfers along an injective ring map.

The orientation matters because the consumer of this lemma needs the fibre as an **`A`-algebra**:
`Module.rTensor_eq_zero_of_isReduced_of_comap_mem_closure` takes a reduced algebra over the upper
ring `A`, and `A ⊗_R K` carries that structure as the standard left-factor algebra structure,
whereas `K ⊗_R A` carries it only through the scoped instance
`Algebra.TensorProduct.rightAlgebra`.

No tag is claimed: this is the standard reducedness of étale fibres, used as an input to the
proof of Stacks 0CWB, not a Stacks statement in its own right.

## References

* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
-/

@[expose] public section

open CategoryTheory

open scoped TensorProduct

universe u v w

namespace Algebra.FormallyUnramified

/-- **An unramified algebra tensored with a field is reduced.**  If `A` is unramified and
essentially of finite type over `R` — for instance étale over `R` — and `K` is a field which is an
`R`-algebra, then `A ⊗_R K` is a reduced ring.

The base change `K ⊗_R A` is unramified and essentially of finite type over the field `K`, hence
reduced by `Algebra.FormallyUnramified.isReduced_of_field`; the asserted orientation follows along
the commutativity isomorphism of the tensor product. -/
theorem isReduced_tensorProduct_of_field (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    [Algebra R A] [FormallyUnramified R A] [EssFiniteType R A]
    (K : Type w) [Field K] [Algebra R K] :
    IsReduced (A ⊗[R] K) :=
  have : IsReduced (K ⊗[R] A) := isReduced_of_field K (K ⊗[R] A)
  isReduced_of_injective (Algebra.TensorProduct.comm R A K).toRingEquiv
    (Algebra.TensorProduct.comm R A K).injective

end Algebra.FormallyUnramified

namespace AlgebraicGeometry

/-- **The fibre of an étale morphism of affine schemes over a point is reduced.**  For `f : E' ⟶ S`
étale with `E'` and `S` affine and `s` a point of `S`, the ring
`\Gamma(E', ⊤) ⊗_{\Gamma(S, ⊤)} κ(s)` of the fibre `E'_s` is reduced.

The two algebra structures are the ones the statement forces: `\Gamma(E', ⊤)` is a
`\Gamma(S, ⊤)`-algebra through `f` on global sections, and `κ(s)` through the evaluation map
`AlgebraicGeometry.Scheme.Γevaluation`.  Since source and target are affine, `f` being étale makes
the map on global sections an étale ring map, and the conclusion is
`Algebra.FormallyUnramified.isReduced_tensorProduct_of_field`. -/
theorem isReduced_appTop_tensorProduct_residueField {E' S : Scheme.{u}} [IsAffine E'] [IsAffine S]
    (f : E' ⟶ S) [Etale f] (s : S) :
    letI : Algebra Γ(S, ⊤) Γ(E', ⊤) := f.appTop.hom.toAlgebra
    letI : Algebra Γ(S, ⊤) (S.residueField s) := (S.Γevaluation s).hom.toAlgebra
    _root_.IsReduced (Γ(E', ⊤) ⊗[Γ(S, ⊤)] S.residueField s) := by
  let : Algebra Γ(S, ⊤) Γ(E', ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(S, ⊤) (S.residueField s) := (S.Γevaluation s).hom.toAlgebra
  have : Algebra.Etale Γ(S, ⊤) Γ(E', ⊤) :=
    RingHom.etale_algebraMap.mp (HasRingHomProperty.appTop (P := @Etale) f inferInstance)
  exact Algebra.FormallyUnramified.isReduced_tensorProduct_of_field _ _ _

end AlgebraicGeometry

end
