module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraIsoComparison

/-!
# Relative spectra are functorial in a morphism of algebras on one base

Let `s` be a relative-spectrum situation and let `B` be a second quasi-coherent sheaf of
commutative algebras on the same base `s.base`. A morphism `ψ : s.algebra ⟶ B` of algebra
sheaves induces a morphism `Spec_{s.base}(B) ⟶ Spec_{s.base}(s.algebra)` of relative spectra
over the base, in the direction opposite to `ψ`. It is the morphism corresponding, under the
representing bijection of [Stacks, Tag 01LV], to the pair consisting of the structure morphism
of `Spec_{s.base}(B)` and its universal algebra map precomposed with `ψ`.

This is the generalization of `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso` from an
isomorphism of algebras to an arbitrary morphism; for an isomorphism the two agree, and
`Stacks.RelativeSpec.isIso_relativeSpectrumMapOfAlgebraIso` then says the comparison is an
isomorphism.

## Main definitions

* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom` is the morphism of relative spectra
  induced by a morphism of algebra sheaves on one base.

## Main results

* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_homEquiv` characterizes the morphism by
  its universal element; this is its defining property.
* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_toBase` — it is a morphism over the base.
* `Stacks.RelativeSpec.ι_relativeSpectrumMapOfAlgebraHom` computes it over an affine open `U` of
  the base: on the inverse image of `U` it is the canonical map to the spectrum of the sections
  of `B` over `U`, followed by the spectrum of `ψ` at `U` and the chart of `U`.
* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_appLE` is the same computation read on
  sections: the universal algebra map of `s` followed by the sections of the morphism is the
  sections of `ψ` followed by the universal algebra map of `B`.
* `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom_eq_ofAlgebraIso` identifies the morphism
  attached to the forward direction of an isomorphism of algebras with
  `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso`.

## Implementation notes

The body of `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso` never uses the inverse of the
isomorphism it is given, so the definition here is the same term with the isomorphism replaced
by a morphism, and the two proofs that transfer verbatim — the defining property and the
compatibility with the structure morphisms to the base — are reproduced in that generality.
What does *not* generalize is the conclusion that the comparison is an isomorphism: that one
rests on the functor isomorphism `Stacks.RelativeSpec.relativeSpecFunctorIsoOfAlgebraIso`,
which needs both directions of `ψ`.

The chartwise computations are the universal property of the glued relative spectrum applied to
the defining pair, so they are instances of `Stacks.RelativeSpec.ι_pairToHom` and
`Stacks.RelativeSpec.pairToHom_appLE`: the representing bijection of
`Stacks.RelativeSpec.relativeSpecRepresentableBy` has `Stacks.RelativeSpec.pairToHom` as its
inverse, and this morphism is by construction the value of that inverse.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LR](https://stacks.math.columbia.edu/tag/01LR)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.RelativeSpec

variable (s : RelativeSpecSituation.{u}) (B : AlgebraSheaf s.base) (hB : B.IsQuasicoherent)
  (ψ : s.algebra ⟶ B)

/-- **The morphism of relative spectra induced by a morphism of algebras on one base.** It is
specified by its universal element — the structure morphism of the relative spectrum of the
second algebra together with that algebra's universal map precomposed with `ψ`. -/
def relativeSpectrumMapOfAlgebraHom :
    (gluedSpectrum (s.withAlgebra B hB)).scheme ⟶ (gluedSpectrum s).scheme :=
  (relativeSpecRepresentableBy s).homEquiv.symm
    ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
      algebraHomAsUnder ψ ≫ (universalAlgebraMap (s.withAlgebra B hB))⟩

/-- **The defining property of `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraHom`.** Under
the representing bijection it is the structure morphism of the second relative spectrum paired
with the second universal algebra map precomposed with `ψ`. -/
theorem relativeSpectrumMapOfAlgebraHom_homEquiv :
    (relativeSpecRepresentableBy s).homEquiv (relativeSpectrumMapOfAlgebraHom s B hB ψ) =
      ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
        algebraHomAsUnder ψ ≫ (universalAlgebraMap (s.withAlgebra B hB))⟩ :=
  (relativeSpecRepresentableBy s).homEquiv.apply_symm_apply _

/-- **The comparison of relative spectra along a morphism of algebras is a morphism over the
base.** This is the first component of its universal element. -/
theorem relativeSpectrumMapOfAlgebraHom_toBase :
    relativeSpectrumMapOfAlgebraHom s B hB ψ ≫ (gluedSpectrum s).toBase =
      (gluedSpectrum (s.withAlgebra B hB)).toBase :=
  (relativeSpecRepresentableBy_homEquiv_fst s
      (relativeSpectrumMapOfAlgebraHom s B hB ψ)).symm.trans
    (congrArg Sigma.fst (relativeSpectrumMapOfAlgebraHom_homEquiv s B hB ψ))

/-- **Over an affine open `U` of the base the comparison is the spectrum of `ψ` at `U`**: on the
inverse image of `U` in the relative spectrum of the second algebra it is the canonical map to
the spectrum of the sections of that algebra over `U`, followed by the spectrum of the sections
of `ψ` and the universal algebra map at `U`, and then the chart of `U`. -/
theorem ι_relativeSpectrumMapOfAlgebraHom (U : s.base.affineOpens) :
    ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1).ι ≫
        relativeSpectrumMapOfAlgebraHom s B hB ψ =
      ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (ψ.right.hom.app (op U.1) ≫
            (universalAlgebraMap (s.withAlgebra B hB)).right.app (op U.1)) ≫
          (gluedSpectrum s).chart U :=
  ι_pairToHom (s := s) ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
    algebraHomAsUnder ψ ≫ (universalAlgebraMap (s.withAlgebra B hB))⟩ U

/-- **The comparison of relative spectra, read on sections over an affine open `U` of the
base.** The universal algebra map of `s` at `U`, followed by the sections of the comparison, is
the sections of `ψ` at `U` followed by the universal algebra map of the second algebra. -/
theorem relativeSpectrumMapOfAlgebraHom_appLE (U : s.base.affineOpens)
    (h : (gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1 ≤
      relativeSpectrumMapOfAlgebraHom s B hB ψ ⁻¹ᵁ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)) :
    (universalAlgebraMap s).right.app (op U.1) ≫
        (relativeSpectrumMapOfAlgebraHom s B hB ψ).appLE
          ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)
          ((gluedSpectrum (s.withAlgebra B hB)).toBase ⁻¹ᵁ U.1) h =
      ψ.right.hom.app (op U.1) ≫
        (universalAlgebraMap (s.withAlgebra B hB)).right.app (op U.1) :=
  pairToHom_appLE (s := s) ⟨(gluedSpectrum (s.withAlgebra B hB)).toBase,
    algebraHomAsUnder ψ ≫ (universalAlgebraMap (s.withAlgebra B hB))⟩ U h

/-- For an isomorphism of algebras on one base, the comparison attached to its forward direction
is the comparison of `Stacks.RelativeSpec.relativeSpectrumMapOfAlgebraIso`, which is therefore
an isomorphism. -/
theorem relativeSpectrumMapOfAlgebraHom_eq_ofAlgebraIso (i : s.algebra ≅ B) :
    relativeSpectrumMapOfAlgebraHom s B hB i.hom = relativeSpectrumMapOfAlgebraIso s B hB i :=
  rfl

end Stacks.RelativeSpec

end
