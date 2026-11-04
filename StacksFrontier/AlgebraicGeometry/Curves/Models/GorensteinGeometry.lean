module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberCartier
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberComponentCartier
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.GorensteinEffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphismOfFlat
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.Fibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.NodalContraction.DvrStalk
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.ValuationFibreDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gorenstein geometry of a regular model

Let `X` be a regular model of a smooth curve `C` over the fraction field `K` of a discrete
valuation ring `R`, in the sense of `Stacks.Models.RegularModelSituation`. Then the structure
morphism `X ⟶ Spec(R)` is a Gorenstein morphism of relative dimension one, and each irreducible
component of the special fibre `X_k`, taken with its reduced induced structure on `X`, is a
Gorenstein scheme.

Both halves of the first assertion are the composite *regular ⇒ Gorenstein scheme ⇒ Gorenstein
morphism along a flat map*: Tag 0DWG for the first step and
`Stacks.Duality.isGorenstein_of_flat` for the second. Relative dimension one comes from the
generic fibre: the model is flat with integral generic fibre `C`, hence integral (Tag 0BCM), the
generic fibre has dimension one because `C` is a curve, and Tag 0B2J carries that dimension —
and equidimensionality — across to the special fibre.

The second assertion is the divisor argument of the source: a component of `X_k` is an
effective Cartier divisor on `X` by the component clause of Tag 0C5Z
(`Stacks.Models.RegularModelSituation.isEffectiveCartierDivisor_specialFiberComponent`), and an
effective Cartier divisor on a Gorenstein scheme is Gorenstein
(`Stacks.Divisors.isGorenstein_subscheme_of_isRegular_of_isEffectiveCartierDivisor`, the
scheme-theoretic form of Tag 0BJJ). The same argument applied to the whole special fibre, which
is an effective Cartier divisor by `Stacks.Models.isEffectiveCartierDivisor_specialFiber`, gives
the intermediate sentence of the source about `X_k` itself.

## Main results

* `Stacks.Models.RegularModelSituation.isGorenstein_model` — the model morphism is Gorenstein.
* `Stacks.Models.RegularModelSituation.relativeDimension_model` — it has relative dimension one.
* `Stacks.Models.RegularModelSituation.isGorenstein_fiber` — consequently every fibre of the
  model is a Gorenstein scheme.
* `Stacks.Models.RegularModelSituation.isGorenstein_specialFiberIdeal` — the special fibre, as a
  closed subscheme of the model, is Gorenstein.
* `Stacks.Models.RegularModelSituation.isGorenstein_specialFiberComponent` — each component of
  the special fibre is Gorenstein.
* `Stacks.Models.RegularModelSituation.isGorenstein_model_and_specialFiberComponents` — the two
  assertions of Tag 0C60 together.

## Implementation notes

**The generic fibre as a fibre.** `Stacks.Models.RegularModelSituation.genericFiber` is the
pullback along `Spec(K) ⟶ Spec(R)`, while the relative-dimension predicate of Tag 02NJ speaks
about `Scheme.Hom.fiber`, the pullback along the canonical map from the spectrum of a residue
field. `Stacks.Models.RegularModelSituation.genericFiberIsoFiberBot` identifies them, using that
the residue field of `R` at `⊥` is a fraction field of `R` and that a base change along an
isomorphism is an isomorphism.

**The two points of `Spec(R)`.** A discrete valuation ring has exactly the primes `⊥` and the
maximal ideal, which is `AlgebraicGeometry.dvr_prime_cases`; the relative-dimension
statement is then checked separately at the generic and the closed point.

## References

* [Stacks Project, Tag 0C60](https://stacks.math.columbia.edu/tag/0C60)
* [Stacks Project, Tag 0C05](https://stacks.math.columbia.edu/tag/0C05)
* [Stacks Project, Tag 0DWG](https://stacks.math.columbia.edu/tag/0DWG)
* [Stacks Project, Tag 0BJJ](https://stacks.math.columbia.edu/tag/0BJJ)
* [Stacks Project, Tag 0C5Z](https://stacks.math.columbia.edu/tag/0C5Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Divisors

universe u

namespace Stacks.Models

namespace RegularModelSituation

variable (S : RegularModelSituation.{u})

/-- The total space of a regular model is a Gorenstein scheme, being regular (Tag 0DWG). -/
public theorem isGorensteinScheme : AlgebraicGeometry.IsGorenstein S.X :=
  isGorenstein_of_isRegular S.X S.regular

/-! ### Part (1): the model morphism is Gorenstein of relative dimension one -/

/-- The structure morphism of a regular model of a smooth curve over a discrete valuation ring is
a Gorenstein morphism.

Local Noetherianity of the fibres is not an extra assumption — it follows from local
Noetherianity of the total space — so it is packaged existentially, as the Gorenstein-morphism
predicate of Tag 0C04 takes a proof of it as an argument. -/
@[stacks 0C60 "part (1): Gorenstein morphism"]
public theorem isGorenstein_model :
    ∃ hf : ∀ y : Spec (.of S.R), IsLocallyNoetherian (S.X_to_R.fiber y),
      S.X_to_R.IsGorenstein hf := by
  let : AlgebraicGeometry.IsGorenstein S.X := S.isGorensteinScheme
  let : IsLocallyNoetherian (Spec (CommRingCat.of S.R)) := inferInstance
  obtain ⟨hf, hG⟩ := Stacks.Duality.isGorenstein_of_flat S.X_to_R
  exact ⟨hf, hG⟩

/-- The generic fibre of a regular model, defined as the pullback along `Spec(K) ⟶ Spec(R)`,
agrees with the scheme-theoretic fibre over the generic point `⊥` of `Spec(R)`. -/
public def genericFiberIsoFiberBot :
    S.genericFiber ≅ S.X_to_R.fiber (⊥ : PrimeSpectrum S.R) := by
  let η : Spec (.of S.R) := (⊥ : PrimeSpectrum S.R)
  let _ : η.asIdeal.IsPrime := η.2
  let e : S.K ≃+* (⊥ : Ideal S.R).ResidueField :=
    IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl S.R)
  let eCat := e.toCommRingCatIso
  let eResidue := Scheme.Spec.residueFieldIso (.of S.R) η
  let i : Spec (.of S.K) ⟶ Spec ((Spec (.of S.R)).residueField η) :=
    (Scheme.Spec.mapIso eCat.op).inv ≫ (Scheme.Spec.mapIso eResidue.op).hom
  have hbase : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) =
      i ≫ (Spec (.of S.R)).fromSpecResidueField η := by
    dsimp [i]
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    simp only [← Spec.map_comp]
    rw [Spec.map_inj]
    ext r
    simp [e, eCat, eResidue]
  have hi : IsIso i := by dsimp [i]; infer_instance
  have heq₁ : S.X_to_R ≫ 𝟙 (Spec (.of S.R)) = 𝟙 S.X ≫ S.X_to_R := by simp
  have heq₂ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ 𝟙 (Spec (.of S.R)) =
      i ≫ (Spec (.of S.R)).fromSpecResidueField η := by simpa using hbase
  have hiso := pullback.map_isIso S.X_to_R
    (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))) S.X_to_R
    ((Spec (.of S.R)).fromSpecResidueField η) (𝟙 S.X) i (𝟙 (Spec (.of S.R))) heq₁ heq₂
  exact @asIso _ _ _ _ _ hiso

/-- The fibre of a regular model over the generic point of `Spec(R)` is integral, being
isomorphic to the smooth curve `C`. -/
public theorem isIntegral_fiber_genericPoint :
    IsIntegral (S.X_to_R.fiber (genericPoint (Spec (.of S.R)))) := by
  have hC : IsIntegral S.C := inferInstance
  have hgen : IsIntegral S.genericFiber := IsIntegral.of_isIso S.genericFiberIso.hom
  have hBot : IsIntegral (S.X_to_R.fiber (⊥ : PrimeSpectrum S.R)) :=
    IsIntegral.of_isIso S.genericFiberIsoFiberBot.hom
  simpa only [genericPoint_eq_bot_of_affine] using hBot

/-- The fibre of a regular model over the generic point of `Spec(R)` has dimension one, being
isomorphic to the curve `C`. -/
public theorem topologicalKrullDim_fiber_bot :
    topologicalKrullDim (S.X_to_R.fiber (⊥ : PrimeSpectrum S.R)) = (1 : WithBot ℕ∞) := by
  calc
    topologicalKrullDim (S.X_to_R.fiber (⊥ : PrimeSpectrum S.R)) =
        topologicalKrullDim S.genericFiber :=
      (IsHomeomorph.topologicalKrullDim_eq _
        S.genericFiberIsoFiberBot.hom.homeomorph.isHomeomorph).symm
    _ = topologicalKrullDim S.C :=
      (IsHomeomorph.topologicalKrullDim_eq _
        S.genericFiberIso.hom.homeomorph.isHomeomorph).symm
    _ = 1 := S.isCurve.topologicalKrullDim_eq_one

/-- Every nonempty fibre of the structure morphism of a regular model of a smooth curve is
equidimensional of dimension one.

The generic fibre is the curve `C`, so it is irreducible of dimension one; the total space is
integral by Tag 0BCM, and Tag 0B2J transports both conclusions to the special fibre. -/
@[stacks 0C60 "part (1): relative dimension one"]
public theorem relativeDimension_model : RelativeDimension S.X_to_R 1 := by
  rw [relativeDimension_iff]
  intro y hy
  have hRint : IsIntegral (Spec (.of S.R)) := inferInstance
  have hgenpt : IsIntegral (S.X_to_R.fiber (genericPoint (Spec (.of S.R)))) :=
    S.isIntegral_fiber_genericPoint
  have hX : IsIntegral S.X :=
    AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_genericFiber S.X_to_R
  have hbot : IsIntegral (S.X_to_R.fiber (⊥ : PrimeSpectrum S.R)) := by
    simpa only [genericPoint_eq_bot_of_affine] using S.isIntegral_fiber_genericPoint
  rcases dvr_prime_cases S.R y with hyGeneric | hySpecial
  · subst y
    exact ⟨TopologicalSpace.Equidimensional.of_preirreducibleSpace _,
      S.topologicalKrullDim_fiber_bot⟩
  · subst y
    have hsurj : Function.Surjective S.X_to_R.base := by
      intro z
      have hne : Nonempty (S.X_to_R.fiber z) := by
        rcases dvr_prime_cases S.R z with hz | hz
        · subst z; infer_instance
        · subst z; exact hy
      obtain ⟨x⟩ := hne
      exact ⟨(S.X_to_R.fiberHomeo _ x).1,
        Set.mem_singleton_iff.mp (Set.mem_preimage.mp (S.X_to_R.fiberHomeo _ x).2)⟩
    have _ : Surjective S.X_to_R := ⟨hsurj⟩
    exact ⟨AlgebraicGeometry.specialFiber_equidimensional S.X_to_R,
      (AlgebraicGeometry.topologicalKrullDim_specialFiber_eq_genericFiber S.X_to_R).trans
        S.topologicalKrullDim_fiber_bot⟩

/-- **Every fibre of a regular model is a Gorenstein scheme.** This is Tag 0C05 applied to
part (1) of Tag 0C60. -/
public theorem isGorenstein_fiber (y : Spec (.of S.R)) :
    AlgebraicGeometry.IsGorenstein (S.X_to_R.fiber y) := by
  obtain ⟨hf, hG⟩ := S.isGorenstein_model
  exact Scheme.Hom.isGorenstein_fiber_of_isGorenstein S.X_to_R hf hG y

/-! ### Part (2): the components of the special fibre -/

/-- **The special fibre of a regular model, as a closed subscheme of the model, is
Gorenstein.** It is an effective Cartier divisor (Tag 0C5Z) on a regular — hence Gorenstein —
scheme, so the scheme-theoretic form of Tag 0BJJ applies. -/
public theorem isGorenstein_specialFiberIdeal :
    AlgebraicGeometry.IsGorenstein S.specialFiberIdeal.subscheme :=
  isGorenstein_subscheme_of_isRegular_of_isEffectiveCartierDivisor S.specialFiberIdeal S.regular
    (isEffectiveCartierDivisor_specialFiber S.residueEquiv S.X_to_R)

/-- Each irreducible component `Cᵢ` of the special fibre of a regular model, taken with its
reduced induced structure as a closed subscheme of the model, is a Gorenstein scheme.

The component is an effective Cartier divisor on `X` by the component clause of Tag 0C5Z, and
`X` is regular, hence Gorenstein, so the scheme-theoretic form of Tag 0BJJ applies. -/
@[stacks 0C60 "part (2)"]
public theorem isGorenstein_specialFiberComponent (Z : irreducibleComponents S.specialFiber) :
    AlgebraicGeometry.IsGorenstein (S.specialFiberComponentIdeal Z).subscheme :=
  isGorenstein_subscheme_of_isRegular_of_isEffectiveCartierDivisor _ S.regular
    (S.isEffectiveCartierDivisor_specialFiberComponent Z)

/-- For a regular model `X` of a smooth curve `C` over `K`: the structure morphism
`X ⟶ Spec(R)` is a Gorenstein morphism of relative dimension one, and each irreducible component
of the special fibre `X_k` is Gorenstein. -/
@[stacks 0C60]
public theorem isGorenstein_model_and_specialFiberComponents :
    (∃ hf : ∀ y : Spec (.of S.R), IsLocallyNoetherian (S.X_to_R.fiber y),
        S.X_to_R.IsGorenstein hf) ∧
      RelativeDimension S.X_to_R 1 ∧
      ∀ Z : irreducibleComponents S.specialFiber,
        AlgebraicGeometry.IsGorenstein (S.specialFiberComponentIdeal Z).subscheme :=
  ⟨S.isGorenstein_model, S.relativeDimension_model, S.isGorenstein_specialFiberComponent⟩

end RegularModelSituation

end Stacks.Models

end
