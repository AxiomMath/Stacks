module

public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.Defs
public import Mathlib.RingTheory.LocalIso

/-!
# Local isomorphisms of rings form a local property of ring maps

A ring map `φ : R → A` is a *local isomorphism*, Mathlib's `Algebra.IsLocalIso`, if every prime
`𝔮` of `A` lies in a principal open `D(a)` of `Spec A`, `a ∉ 𝔮`, on which the composite
`R → A → A_a` is a localization of `R` away from some `f ∈ R`; that is, `R_f → A_a` is an
isomorphism. This property is local in the sense of `RingHom.StacksPropertyIsLocal`.

This is the corrected form of part (2) (open immersion) of Stacks Tag 01SX. As printed, part
(2) asks for the same element `f ∈ R` on both sides, `R_f → A_f`; that criterion is
`RingHom.IsOpenImmersion`, and it is not local
(`RingHom.not_stacksPropertyIsLocal_isOpenImmersion`). Allowing the localization of `A` to be
at an element `a ∈ A ∖ 𝔮` gives the property here, which says that `Spec A → Spec R` is a local
isomorphism, and which is local. The error and its correction are recorded in `errata.md`,
entry 01SX(2).

## Main results

* `RingHom.isLocalIso_stableUnderComposition`: local isomorphisms compose.
* `RingHom.isLocalIso_isStableUnderBaseChange`: local isomorphisms are stable under base
  change.
* `RingHom.stacksPropertyIsLocal_isLocalIso`: being a local isomorphism is a local property of
  ring maps.

## Implementation notes

Composition and base change for the algebra formulation are Mathlib's
`Algebra.IsLocalIso.trans` and the tensor-product instance in `Mathlib.RingTheory.LocalIso`,
and descent along a principal cover of the target is `Algebra.IsLocalIso.of_span_eq_top`. This
file transports them to the ring-map formulation used by `RingHom.StacksPropertyIsLocal`.

## References

* [Stacks Project, Tag 01SR](https://stacks.math.columbia.edu/tag/01SR)
* [Stacks Project, Tag 01SX](https://stacks.math.columbia.edu/tag/01SX)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace RingHom

/-- Local isomorphisms compose. -/
theorem isLocalIso_stableUnderComposition :
    RingHom.StableUnderComposition
      (fun {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) ↦
        @Algebra.IsLocalIso R S _ _ φ.toAlgebra) := by
  intro R S T _ _ _ f g hf hg
  algebraize [f, g, g.comp f]
  exact Algebra.IsLocalIso.trans R S T

/-- The structure map of an algebra that is a local isomorphism is a local isomorphism as a
ring map. -/
private theorem isLocalIso_algebraMap {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsLocalIso R S] :
    @Algebra.IsLocalIso R S _ _ (algebraMap R S).toAlgebra := by
  rwa [toAlgebra_algebraMap]

/-- Local isomorphisms are stable under base change. -/
theorem isLocalIso_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange
      (fun {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) ↦
        @Algebra.IsLocalIso R S _ _ φ.toAlgebra) := by
  refine .mk (isLocalIso_stableUnderComposition.respectsIso fun e ↦ ?_) ?_
  · let := e.toRingHom.toAlgebra
    have : Algebra.IsStandardOpenImmersion _ _ := Algebra.IsStandardOpenImmersion.of_bijective
      (S := _) (R := _) e.bijective
    infer_instance
  · intro R S T _ _ _ _ _ h
    rw [toAlgebra_algebraMap] at h
    exact isLocalIso_algebraMap

/-- Stacks Tag 01SX, part (2) in corrected form: being a local isomorphism (every prime `𝔮` of
`A` has some `a ∈ A ∖ 𝔮` and `f ∈ R` with `R_f → A_a` an isomorphism) is a local property of
ring maps. -/
@[stacks 01SX "part (2) (open immersion), in the corrected form recorded in errata.md: for \
every prime 𝔮 of A there are f ∈ R and a ∈ A ∖ 𝔮 with R_f → A_a an isomorphism (Mathlib's \
Algebra.IsLocalIso); this property is local. Part (2) as printed, with R_f → A_f, is false: \
see not_stacksPropertyIsLocal_isOpenImmersion"]
theorem stacksPropertyIsLocal_isLocalIso :
    RingHom.StacksPropertyIsLocal
      (fun {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) ↦
        @Algebra.IsLocalIso R S _ _ φ.toAlgebra) where
  localizationAwayPreserves := isLocalIso_isStableUnderBaseChange.localizationPreserves.away
  compPrincipalLocalizations := by
    intro R A Rf Aa _ _ _ _ f a _ _ _ _ g hg
    have hRf : Algebra.IsStandardOpenImmersion R Rf := ⟨f, inferInstance⟩
    have hAa : Algebra.IsStandardOpenImmersion A Aa := ⟨a, inferInstance⟩
    exact isLocalIso_stableUnderComposition _ _
      (isLocalIso_stableUnderComposition _ _ isLocalIso_algebraMap hg) isLocalIso_algebraMap
  ofLocalizationFiniteSpanTarget := by
    intro R S _ _ φ s hs h
    let := φ.toAlgebra
    refine Algebra.IsLocalIso.of_span_eq_top hs fun x hx ↦ ?_
    have e : ((algebraMap S (Localization.Away x)).comp φ).toAlgebra =
        (inferInstance : Algebra R (Localization.Away x)) :=
      Algebra.algebra_ext _ _ fun r ↦ (IsScalarTower.algebraMap_apply R S _ r).symm
    have hx' : @Algebra.IsLocalIso R (Localization.Away x) _ _
        ((algebraMap S (Localization.Away x)).comp φ).toAlgebra := h ⟨x, hx⟩
    rwa [e] at hx'

end RingHom
