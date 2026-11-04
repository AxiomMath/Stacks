module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStein.FiniteEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineInvolutionUniversalHomeomorphism

/-!
# The Stein factorization of a flat proper morphism with reduced fibres is finite étale

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` and `X ⟶ Y' ⟶ Y` its Stein
factorization (Stacks 0A1C).  Stacks 0E0D says that if `f` is of finite presentation, flat, with
geometrically reduced fibres (Stacks 0E08), then `Y' ⟶ Y` is finite étale.

Stacks 0E0D for the Stein factorization of the library — the normalization of `Y` in `X` — is
`AlgebraicGeometry.Space.isFinite_and_isEtale_normalizationInQcqsHom`.  The Stein factorization
is characterized, up to unique isomorphism, by the two properties that `π : Y' ⟶ Y` is affine and
that the structure map `𝒪_{Y'} ⟶ f'_*𝒪_X` of the first factor is an isomorphism: then
`π_*𝒪_{Y'} = f_*𝒪_X`, so `Y'` is the relative spectrum of `f_*𝒪_X` of Stacks 081X.  The statement
below is made for every factorization with these two properties.

## Main results

* `AlgebraicGeometry.Space.isFinite_and_isEtale_of_steinFactorization_of_inputs`: the statement
  for an arbitrary factorization `f = f' ≫ π` with `π` affine and `𝒪_{Y'} ⟶ f'_*𝒪_X` an
  isomorphism, from the connectedness of the geometric fibres of `f'` (part of Stacks 0A1C),
  Stacks 0E0S and Stacks 0E1E, each in the form stated at its hypothesis.

## Implementation notes

Integrality of `π` is not an input: `π` is affine, and universally closed because `f` is and
`f'` is surjective (its geometric fibres are connected, hence nonempty), so it is integral by
Stacks 0415.  The structure-map hypothesis enters through
`AlgebraicGeometry.Space.ProperFlatStein.bijective_pullbackToGlobalFunctions_of_isIso_fSharp`, and
the proof of the local statement is
`AlgebraicGeometry.Space.ProperFlatStein.isFinite_and_isEtale_of_stein_of_inputs`, which follows
the source.  Stacks 0E1E is consumed there in the shape of the openness of the locus where the
number of geometric connected components of a fibre is one, which the locally constant form
assumed here gives at the value `1`.

## References

* [Stacks Project, Tag 0E0D](https://stacks.math.columbia.edu/tag/0E0D)
* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 0E0S](https://stacks.math.columbia.edu/tag/0E0S)
* [Stacks Project, Tag 0E1E](https://stacks.math.columbia.edu/tag/0E1E)
* [Stacks Project, Tag 0415](https://stacks.math.columbia.edu/tag/0415)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0E0D, from the inputs it consumes.**  Let `f = f' ≫ π : X ⟶ Y` be proper, flat,
of finite presentation, with geometrically reduced fibres, where `π : Y' ⟶ Y` is affine and the
structure map `𝒪_{Y'} ⟶ f'_*𝒪_X` of `f'` is an isomorphism — the Stein factorization of `f`.
Given that the geometric fibres of `f'` are connected (`hconn`), Stacks 0E0S (`hpush`, in the
shape of `AlgebraicGeometry.Space.isIso_structureSharp_and_baseChange_of_geometricFibres`, which
carries that tag) and Stacks 0E1E (`h0E1E`, in the locally constant form registered on
`AlgebraicGeometry.Space.isLocallyConstant_numberGeometricConnectedComponents`), `π` is finite
and étale. -/
theorem isFinite_and_isEtale_of_steinFactorization_of_inputs
    {X Y Y' : AlgebraicSpaces B S hS} (f' : X ⟶ Y') (π : Y' ⟶ Y)
    (hπ : IsAffineHom B S hS π.hom)
    (hstr : IsIso (smallEtaleRingedToposHom B S hS f').fSharp)
    (hf : IsProper B S hS (f' ≫ π).hom) (hfl : IsFlat B S hS (f' ≫ π).hom)
    (hfp : IsFinitePresentation B S hS (f' ≫ π).hom)
    (hred : ∀ y, IsGeometricallyReducedFibreAt B S hS (f' ≫ π).hom X.2 Y.2 y)
    (hconn : ∀ y' : GeometricPoint B S hS Y'.1,
      ConnectedPullback B S hS f'.hom (yonedaEquiv.symm y'.val.value))
    (hpush : ∀ {X₀ Y₀ : AlgebraicSpaces B S hS} (g : X₀ ⟶ Y₀),
      IsProper B S hS g.hom → IsFlat B S hS g.hom → IsFinitePresentation B S hS g.hom →
      (∀ y : GeometricPoint B S hS Y₀.1,
        HasEtaleLocalProperty B (Spec (.of y.1.carrier)) y.1.contained
          (fibreOverFieldValuedPoint B S hS g.hom y.1)
          (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced T)) →
      (∀ y : GeometricPoint B S hS Y₀.1,
        ConnectedPoints B (Spec (.of y.1.carrier)) y.1.contained
          (fibreOverFieldValuedPoint B S hS g.hom y.1)) →
      IsIso (structureSharp B S hS g) ∧
        ∀ (Y' : AlgebraicSpaces B S hS) (g' : Y' ⟶ Y₀),
          IsIso (structureSharp B S hS (pullback.snd g g')))
    (h0E1E : ∀ {P Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
      (hZ : IsAlgebraicSpace B S hS Z) (g : P ⟶ Z), IsProper B S hS g → IsFlat B S hS g →
        IsFinitePresentation B S hS g →
        (∀ z, IsGeometricallyReducedFibreAt B S hS g hP hZ z) →
        IsLocallyConstant (numberGeometricConnectedComponents B S hS g)) :
    IsFinite B S hS π.hom ∧ IsEtale B S hS π.hom := by
  have hsurj := ProperFlatStein.isSurjective_of_connectedPullback B S hS f'.hom hconn
  have huc : UniversallyClosed B S hS π.hom :=
    universallyClosed_of_comp_of_isSurjective B S hS X.2 Y'.2 Y.2 f'.hom π.hom hsurj hf.2.2
  have hπint : IsIntegralHom B S hS π.hom :=
    (isIntegralHom_iff_isAffineHom_and_universallyClosed B S hS Y'.2 Y.2 π.hom).2 ⟨hπ, huc⟩
  exact ProperFlatStein.isFinite_and_isEtale_of_stein_of_inputs B S hS X.2 Y.2 Y'.2 f'.hom π.hom
    hπ hπint hf hfl hfp hred hconn
    (fun V _ c hc _ hP a b sq =>
      ProperFlatStein.bijective_pullbackToGlobalFunctions_of_isIso_fSharp B S hS f' hstr V c hc
        hP a b sq)
    (ProperFlatStein.bijective_pullbackToGlobalFunctions_of_properFlatStructureSharp B S hS hpush)
    (fun hP Z g hgp hgfl hgfp hgred =>
      (h0E1E hP (isAlgebraicSpace_yoneda B S hS Z) g hgp hgfl hgfp hgred).isOpen_fiber 1)

end AlgebraicGeometry.Space

end
