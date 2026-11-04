module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.LocallyPrincipalFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember

/-!
# Flatness of the universal family of a linear system over an open of the parameter space

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]). The universal
divisor `H_univ ⊂ 𝔸^r_X` is a locally principal closed subscheme, because it is the zero scheme
of the universal section of an invertible module, and `𝔸^r_X → 𝔸^r_k` is flat and locally of
finite presentation, being a base change of `X → Spec k`. By [Stacks, Tag 062Y] it follows that
over an open `U ⊂ 𝔸^r_k` whose fibres meet `H_univ` in effective Cartier divisors, `H_univ` is a
relative effective Cartier divisor, and in particular `q^{-1}(U) → U` is flat.

This is the flatness step of the proof of [Stacks, Tag 0FD6]. The source discharges the
fibrewise Cartier condition from the hypothesis that the image of `ψ` generates `L`: that
hypothesis produces a nonempty open over which no fibre of `q` contains an irreducible component
of `X`, and "a nonvanishing section of an invertible module on an integral scheme is a regular
section". The second half of that sentence is
`AlgebraicGeometry.isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero` below; the first half,
the construction of the open, is not in this file.

## Main results

* `AlgebraicGeometry.isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero`: the inverse image
  of the zero scheme of a section of an invertible module along a morphism from an integral
  scheme is an effective Cartier divisor as soon as the pulled-back section is nonzero.
* `Stacks.Bertini.FamilyDivisors.isLocallyPrincipal_restrictedUniversalDivisor`: the universal
  divisor restricted over an open of the parameter space is locally principal.
* `Stacks.Bertini.FamilyDivisors.flat_restrictedUniversalFamily` and
  `Stacks.Bertini.FamilyDivisors.flat_universalDivisor_restrict`: over an open `U` of `𝔸^r_k`
  all of whose fibres meet `H_univ` in an effective Cartier divisor, `q^{-1}(U) → U` is flat.
* `Stacks.Bertini.FamilyDivisors.isEffectiveCartierDivisor_fibre_restrictedUniversalDivisor`:
  an integral fibre on which the universal section does not vanish identically meets `H_univ`
  in an effective Cartier divisor.
* `Stacks.Bertini.FamilyDivisors.flat_universalDivisor_restrict_of_fibres_isIntegral`: the
  flatness conclusion from integrality of the fibres together with nonvanishing of the
  universal section on each of them.

## Implementation notes

`q^{-1}(U)` is spelled in two ways. The first is the closed subscheme of the open `𝔸^r_X|_U`
cut out by the inverse image `H_univ|_U` of the universal divisor, with `q^{-1}(U) → U` the
composition of its closed immersion with the restriction `𝔸^r_X|_U → U` of `𝔸^r_X → 𝔸^r_k`;
this is the shape in which [Stacks, Tag 062Y] is available, its global locally-principal clause
`Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres` taking a
closed subscheme of the source of a flat morphism of finite presentation and returning, among
other things, flatness of its structure morphism to the base. The second is the open of
`H_univ` lying over `U`, with `q^{-1}(U) → U` the composition of the two restrictions
`H_univ|_U → 𝔸^r_X|_U → U`. The two are identified by
`Stacks.Bertini.FamilyDivisors.restrictedUniversalFamilyIso`, which compares the two cartesian
squares over the cospan `𝔸^r_X|_U → 𝔸^r_X ← H_univ`. They are not written as the restriction
`q ∣_ U` of `Stacks.Bertini.FamilyDivisors.universalFamily` itself: the open
`q ⁻¹ᵁ U` and the open `H_univ|_U` are equal only after unfolding the composition inside `q`,
which `rw` will not do.

The flatness and finite presentation of `𝔸^r_X → 𝔸^r_k` are base changes of the corresponding
properties of `X → Spec k`: flatness holds with no hypothesis, since the base is the spectrum of
a field, and finite presentation comes from the smoothness of `X` over `k`.

The fibrewise effective Cartier condition is left as a hypothesis in
`flat_restrictedUniversalFamily` because that is exactly the hypothesis of Tag 062Y. The variant
`flat_universalDivisor_restrict_of_fibres_isIntegral` discharges it by the regular-section
argument of the source, which needs the fibre to be integral; the source instead arranges that
the universal section vanish on no irreducible component of a fibre, which is the same argument
run on each component and is not formalized here.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Divisors

universe u v

namespace AlgebraicGeometry

/-- **The inverse image of a zero scheme along a morphism from an integral scheme is an
effective Cartier divisor** as soon as the pulled-back section does not vanish identically.

This is the sentence "a nonvanishing section of an invertible module on an integral scheme is a
regular section" of the proof of [Stacks, Tag 0FD6]: the inverse image of the zero scheme is the
zero scheme of the pulled-back section ([Stacks, Tag 0B6Y]), and on an integral scheme a nonzero
section of an invertible module is a nonzerodivisor. -/
public theorem isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero {X Y : Scheme.{u}}
    (g : Y ⟶ X) [IsIntegral Y] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : Γ(L, ⊤))
    (hs : pullbackGlobalSections g L s ≠ 0) :
    IsEffectiveCartierDivisor ((zeroScheme X L s).comap g) := by
  rw [← Stacks.Divisors.zeroScheme_pullback g L s]
  exact isEffectiveCartierDivisor_zeroScheme_of_ne_zero _ _ hs

end AlgebraicGeometry

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- **The parameter space is flat over the parameter space of the base field.** The projection
`𝔸^r_X = 𝔸^r_k ×_k X → 𝔸^r_k` is the base change of `X → Spec k`, which is flat because its
target is the spectrum of a field. -/
public instance flat_parameterBaseMap : Flat D.parameterBaseMap :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map D.toBase).flip
    (inferInstanceAs (Flat D.toBase))

/-- **The parameter space is of finite presentation over the parameter space of the base
field**, when `X` is smooth over `k`: the projection `𝔸^r_X → 𝔸^r_k` is the base change of
`X → Spec k`. -/
public instance locallyOfFinitePresentation_parameterBaseMap [Smooth D.toBase] :
    LocallyOfFinitePresentation D.parameterBaseMap :=
  MorphismProperty.of_isPullback (AffineSpace.isPullback_map D.toBase).flip
    (inferInstanceAs (LocallyOfFinitePresentation D.toBase))

variable (U : D.parameterBase.Opens)

/-- The part `𝔸^r_X|_U` of the parameter space lying over an open `U` of `𝔸^r_k`. -/
public abbrev restrictedParameterSpace : D.parameterSpace.Opens := D.parameterBaseMap ⁻¹ᵁ U

/-- **The universal divisor over an open of the parameter space**, `H_univ ∩ 𝔸^r_X|_U`, as a
closed subscheme of `𝔸^r_X|_U`. Its structure morphism to `U` is the map `q^{-1}(U) → U`. -/
public def restrictedUniversalDivisor : (D.restrictedParameterSpace U).toScheme.IdealSheafData :=
  D.universalDivisor.comap (D.restrictedParameterSpace U).ι

/-- **`H_univ ∩ 𝔸^r_X|_U` is a locally principal closed subscheme of `𝔸^r_X|_U`**, being the
zero scheme of the restriction of the universal section to it. -/
public theorem isLocallyPrincipal_restrictedUniversalDivisor :
    IsLocallyPrincipal (D.restrictedUniversalDivisor U) := by
  rw [restrictedUniversalDivisor, universalDivisor,
    ← Stacks.Divisors.zeroScheme_pullback (D.restrictedParameterSpace U).ι _ D.universalSection]
  exact isLocallyPrincipal_zeroScheme _ _ _

/-- **`q^{-1}(U) → U` is flat** when every fibre of `𝔸^r_X|_U → U` meets the universal divisor
in an effective Cartier divisor.

This is the global locally principal clause of [Stacks, Tag 062Y] applied to the flat morphism
of finite presentation `𝔸^r_X|_U → U` and the locally principal closed subscheme
`H_univ ∩ 𝔸^r_X|_U`: the conclusion is that the latter is a relative effective Cartier divisor,
whose second conjunct is the flatness asserted here. -/
public theorem flat_restrictedUniversalFamily [Smooth D.toBase]
    (hfib : ∀ u : U, IsEffectiveCartierDivisor ((D.restrictedUniversalDivisor U).comap
      ((D.parameterBaseMap ∣_ U).fiberι u))) :
    Flat ((D.restrictedUniversalDivisor U).subschemeι ≫ (D.parameterBaseMap ∣_ U)) :=
  (isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres (D.parameterBaseMap ∣_ U)
    (D.restrictedUniversalDivisor U) (D.isLocallyPrincipal_restrictedUniversalDivisor U) hfib).2

/-- **The comparison isomorphism `q^{-1}(U) ≅ H_univ ∩ 𝔸^r_X|_U`.** The open of the universal
divisor lying over `U` and the closed subscheme of `𝔸^r_X|_U` cut out by the universal divisor
are the two corners of two cartesian squares over the same cospan. -/
public def restrictedUniversalFamilyIso :
    (D.universalDivisor.subschemeι ⁻¹ᵁ D.restrictedParameterSpace U).toScheme ≅
      (D.restrictedUniversalDivisor U).subscheme :=
  (isPullback_morphismRestrict D.universalDivisor.subschemeι
      (D.restrictedParameterSpace U)).isoIsPullback _ _
    (isPullback_subschemeι_comap D.universalDivisor (D.restrictedParameterSpace U).ι)

/-- The comparison isomorphism carries the closed immersion of `H_univ ∩ 𝔸^r_X|_U` into
`𝔸^r_X|_U` to the restriction of the closed immersion of `H_univ`. -/
public theorem restrictedUniversalFamilyIso_hom_subschemeι :
    (D.restrictedUniversalFamilyIso U).hom ≫ (D.restrictedUniversalDivisor U).subschemeι =
      D.universalDivisor.subschemeι ∣_ D.restrictedParameterSpace U :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **`q^{-1}(U) → U` is flat**, with `q^{-1}(U)` spelled as the open of `H_univ` lying over `U`
and the morphism as the composition of the restrictions `H_univ|_U → 𝔸^r_X|_U → U`. -/
public theorem flat_universalDivisor_restrict [Smooth D.toBase]
    (hfib : ∀ u : U, IsEffectiveCartierDivisor ((D.restrictedUniversalDivisor U).comap
      ((D.parameterBaseMap ∣_ U).fiberι u))) :
    Flat ((D.universalDivisor.subschemeι ∣_ D.restrictedParameterSpace U) ≫
      (D.parameterBaseMap ∣_ U)) := by
  rw [← D.restrictedUniversalFamilyIso_hom_subschemeι U, Category.assoc]
  have := D.flat_restrictedUniversalFamily U hfib
  infer_instance

/-- **A fibre of `𝔸^r_X|_U → U` that is integral and on which the universal section does not
vanish identically meets the universal divisor in an effective Cartier divisor.**

This is the derivation of the fibrewise Cartier condition in the proof of [Stacks, Tag 0FD6]:
the fibre of the universal divisor is the zero scheme of the restricted universal section
([Stacks, Tag 0B6Y]), and a nonvanishing section of an invertible module on an integral scheme
is a regular section. -/
public theorem isEffectiveCartierDivisor_fibre_restrictedUniversalDivisor (u : U)
    [IsIntegral ((D.parameterBaseMap ∣_ U).fiber u)]
    (hne : pullbackGlobalSections
      ((D.parameterBaseMap ∣_ U).fiberι u ≫ (D.restrictedParameterSpace U).ι)
      ((Scheme.Modules.pullback D.parameterProjection).obj D.L) D.universalSection ≠ 0) :
    IsEffectiveCartierDivisor ((D.restrictedUniversalDivisor U).comap
      ((D.parameterBaseMap ∣_ U).fiberι u)) := by
  rw [restrictedUniversalDivisor, ← Scheme.IdealSheafData.comap_comp]
  exact isEffectiveCartierDivisor_comap_zeroScheme_of_ne_zero _ _ _ hne

/-- **`q^{-1}(U) → U` is flat** when the fibres of `𝔸^r_X|_U → U` are integral and the universal
section vanishes identically on none of them. -/
public theorem flat_universalDivisor_restrict_of_fibres_isIntegral [Smooth D.toBase]
    (hint : ∀ u : U, IsIntegral ((D.parameterBaseMap ∣_ U).fiber u))
    (hne : ∀ u : U, pullbackGlobalSections
        ((D.parameterBaseMap ∣_ U).fiberι u ≫ (D.restrictedParameterSpace U).ι)
        ((Scheme.Modules.pullback D.parameterProjection).obj D.L) D.universalSection ≠ 0) :
    Flat ((D.universalDivisor.subschemeι ∣_ D.restrictedParameterSpace U) ≫
      (D.parameterBaseMap ∣_ U)) :=
  D.flat_universalDivisor_restrict U fun u =>
    have := hint u
    D.isEffectiveCartierDivisor_fibre_restrictedUniversalDivisor U u (hne u)

end Stacks.Bertini.FamilyDivisors

end
