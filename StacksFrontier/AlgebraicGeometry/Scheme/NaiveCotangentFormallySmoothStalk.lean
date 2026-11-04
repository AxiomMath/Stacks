module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothConverse
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentSmoothStalkCriterion

/-!
# Formal smoothness of a morphism of schemes read on the stalk maps and on `Ω_{X/S}`

[Stacks, Tag 0D0L] characterises formal smoothness of a morphism of schemes `f : X ⟶ S` by the
vanishing of the cohomology sheaf `H⁻¹(NL_{X/S})` and local projectivity of
`H⁰(NL_{X/S}) = Ω_{X/S}`. This file rewrites both conditions in the form in which the version for
algebraic spaces, [Stacks, Tag 0D10], is reduced to schemes: the first as the vanishing of `H¹`
of the naive cotangent complex of every stalk map `𝒪_{S,f x} ⟶ 𝒪_{X,x}`, the second as local
projectivity of the sheaf of relative differentials `Ω_{X/S}`.

## Main results

* `Stacks.Smooth.isZero_homology_negOne_naiveCotangentComplex_iff_subsingleton_h1Cotangent`:
  `H⁻¹(NL_{X/S}) = 0` if and only if `H¹(L_{𝒪_{X,x}/𝒪_{S,f x}}) = 0` at every point `x`.
* `Stacks.Smooth.isLocallyProjective_homology_zero_naiveCotangentComplex_iff`: `H⁰(NL_{X/S})`
  is locally projective if and only if `Ω_{X/S}` is.
* `Stacks.Smooth.formallySmoothScheme_iff_subsingleton_h1Cotangent_and_isLocallyProjective`:
  [Stacks, Tag 0D0L] in the stalkwise form.

## Implementation notes

The vanishing of `H⁻¹(NL_{X/S})` is injectivity at every point of the cotangent complex of the
canonical presentation of `𝒪_{X,x}` over `(f⁻¹𝒪_S)_x`
(`Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff`), which is the
vanishing of `H¹(L_{𝒪_{X,x}/(f⁻¹𝒪_S)_x})` (`Algebra.Extension.cotangentComplex_injective_iff`),
and the two base rings `(f⁻¹𝒪_S)_x` and `𝒪_{S,f x}` are identified compatibly with the maps to
`𝒪_{X,x}` (`Stacks.Smooth.subsingleton_h1Cotangent_stalk_inverseImageStructureMap_iff`).

## References

* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L)
* [Stacks Project, Tag 0D10](https://stacks.math.columbia.edu/tag/0D10)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeDifferentialStalk (algebraStalk)

universe u

namespace Stacks.Smooth

/-- The cotangent complex of the canonical presentation of an algebra is injective exactly when
`H¹` of its naive cotangent complex vanishes, the polynomial ring of that presentation being
formally smooth. -/
theorem injective_cotangentComplex_generatorsSelf_iff (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] :
    Function.Injective (Algebra.Generators.self R A).toExtension.cotangentComplex ↔
      Subsingleton (Algebra.H1Cotangent R A) :=
  have : Algebra.FormallySmooth R (Algebra.Generators.self R A).toExtension.Ring :=
    inferInstanceAs (Algebra.FormallySmooth R (MvPolynomial A R))
  Algebra.Extension.cotangentComplex_injective_iff _

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Local projectivity transfers along an isomorphism of modules. -/
private theorem isLocallyProjective_of_iso {M N : X.Modules} (e : M ≅ N)
    (h : Scheme.Modules.IsLocallyProjective M) : Scheme.Modules.IsLocallyProjective N :=
  fun U hU ↦
    @Module.Projective.of_equiv' Γ(X, U) _ Γ(N, U) _ (N.val.obj (.op U)).isModule
      Γ(M, U) _ (M.val.obj (.op U)).isModule (h U hU)
      (AlgebraicGeometry.sectionsLinearEquivOfIso e U)

/-- **`H⁻¹(NL_{X/S}) = 0` is the vanishing of `H¹` of every stalk map.** For a morphism of
schemes `f : X ⟶ S`, the degree `-1` cohomology sheaf of the naive cotangent complex vanishes if
and only if `H¹(L_{𝒪_{X,x}/𝒪_{S,f x}})` vanishes at every point `x` of `X`. -/
theorem isZero_homology_negOne_naiveCotangentComplex_iff_subsingleton_h1Cotangent :
    IsZero ((Scheme.naiveCotangentComplex f).homology (-1)) ↔
      ∀ x : X, letI := (f.stalkMap x).hom.toAlgebra
        Subsingleton (Algebra.H1Cotangent (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
  rw [Stacks.NaiveCotangentEtale.isZero_homology_negOne_naiveCotangentComplex_iff]
  refine forall_congr' fun x ↦ ?_
  let := algebraStalk
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f.toLRSHom.toShHom).hom x
  exact (injective_cotangentComplex_generatorsSelf_iff _ _).trans
    (subsingleton_h1Cotangent_stalk_inverseImageStructureMap_iff f x)

/-- **`H⁰(NL_{X/S})` is locally projective exactly when `Ω_{X/S}` is**, the two being identified
by the degree-zero clause of [Stacks, Tag 0D0J]. -/
theorem isLocallyProjective_homology_zero_naiveCotangentComplex_iff :
    Scheme.Modules.IsLocallyProjective ((Scheme.naiveCotangentComplex f).homology 0) ↔
      Scheme.Modules.IsLocallyProjective (Scheme.Hom.relativeDifferentials f) :=
  ⟨isLocallyProjective_of_iso (Scheme.naiveCotangentComplexHomologyZeroIso f),
    isLocallyProjective_of_iso (Scheme.naiveCotangentComplexHomologyZeroIso f).symm⟩

/-- **[Stacks, Tag 0D0L], read on the stalk maps.** A morphism of schemes `f : X ⟶ S` is
formally smooth if and only if `H¹` of the naive cotangent complex of every stalk map
`𝒪_{S,f x} ⟶ 𝒪_{X,x}` vanishes and `Ω_{X/S}` is locally projective. -/
theorem formallySmoothScheme_iff_subsingleton_h1Cotangent_and_isLocallyProjective :
    FormallySmoothScheme f ↔
      ((∀ x : X, letI := (f.stalkMap x).hom.toAlgebra
          Subsingleton (Algebra.H1Cotangent (S.presheaf.stalk (f x)) (X.presheaf.stalk x))) ∧
        Scheme.Modules.IsLocallyProjective (Scheme.Hom.relativeDifferentials f)) :=
  (formallySmooth_iff_isZero_homology_negOne_and_isLocallyProjective_homology_zero f).trans
    (and_congr (isZero_homology_negOne_naiveCotangentComplex_iff_subsingleton_h1Cotangent f)
      (isLocallyProjective_homology_zero_naiveCotangentComplex_iff f))

end Stacks.Smooth

end
