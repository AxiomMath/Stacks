module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.RingTheory.SquareRootColonCover

@[expose] public noncomputable section

/-!
# (SQ) for an affine scheme

This file turns the ring-theoretic statement
`Stacks.SquareRootCover.exists_isIntegral_surjective_isSquare` into the geometric statement it
encodes:

> **(SQ)** for every scheme `S`, every point `x` of `S`, every affine open `Ω ∋ x` and every
> `u ∈ Γ(S, Ω)` there is a surjective integral morphism `A ⟶ S` such that the image of `u` is a
> square in `𝒪_{A, p}` at every point `p` of `A` over `x`

for `S = Spec R`. The morphism is `Spec` of the structure morphism of
`Stacks.SquareRootCover.Cover a b`, for any presentation `a / b` of the germ of `u` at `x` in
`𝒪_{S, x} = R_x`; no hypothesis on `Ω` is needed beyond `x ∈ Ω`, since only that germ is used.

## Main results

* `Stacks.SquareRootCover.surjective_specMap_of_exists_isPrime_comap_eq`: a morphism of affine
  spectra is surjective as soon as every prime of the source ring is a contraction.
* `Stacks.SquareRootCover.isSquare_germ_specMap_cover`: the pointwise statement, with the germ
  of `u` presented as `a / b`.
* `Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_germ`: **(SQ) for
  `Spec R`.**

## Implementation notes

**The shape of the conclusion.** "The image of `u` in `𝒪_{A, p}`" is written as the germ at `p`
of the pulled back section `f.app Ω u`, not as `f.stalkMap p` applied to the germ of `u` at
`x`. The two are equal by `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`, and the former has
a type not depending on the hypothesis `f.base p = x`: the source of `f.stalkMap p` is the stalk
at `f.base p`, so the latter spelling needs that hypothesis to transport the germ, which makes
the statement dependently typed in a proof. Since every point of `A` over `x` does lie over `Ω`,
the pulled back section is defined at `p` and the two readings agree.

**Where the hypothesis `f.base p = x` is used.** Only to transport the three propositions
"`b ∉ x`", "`x ∈ Ω`" and "`a = u * b` in `R_x`" from `x` to `f.base p`. That transport is a
substitution, so `Stacks.SquareRootCover.isSquare_germ_specMap_cover` is stated with the prime
as a variable and the equality as a hypothesis, which lets it be eliminated.

## References

* [Stacks Project, Tag 0CNZ](https://stacks.math.columbia.edu/tag/0CNZ)
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.SquareRootCover

/-- **A morphism of affine spectra is surjective as soon as every prime of the source ring is a
contraction.** -/
theorem surjective_specMap_of_exists_isPrime_comap_eq {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (h : ∀ 𝔮 : Ideal R, 𝔮.IsPrime → ∃ Q : Ideal T, Q.IsPrime ∧ Q.comap φ.hom = 𝔮) :
    Surjective (Spec.map φ) := by
  refine ⟨fun 𝔮 => ?_⟩
  obtain ⟨Q, hQ, hQe⟩ := h 𝔮.asIdeal 𝔮.2
  exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQe⟩

variable {R : CommRingCat.{u}}

/-- The structure morphism of the cover, as a morphism of `CommRingCat`. -/
abbrev coverSpecHom (a b : R) : R ⟶ CommRingCat.of (Cover a b) :=
  CommRingCat.ofHom (algebraMap R (Cover a b))

/-- **The pointwise statement of (SQ) for `Spec R`.** Let `a b : R`, let `𝔭` be a point of
`Spec R` with `b ∉ 𝔭`, let `Ω ∋ 𝔭` be open and let `u` be a section of the structure sheaf over
`Ω` whose germ at `𝔭` is `a / b`. Then at every point `p` of `Spec (Cover a b)` over `𝔭` the
image of `u` is a square. -/
theorem isSquare_germ_specMap_cover (a b : R) (Ω : (Spec R).Opens) (u : Γ(Spec R, Ω))
    (𝔭 : PrimeSpectrum R) (h𝔭 : 𝔭 ∈ Ω) (hb : b ∉ 𝔭.asIdeal)
    (hu : algebraMap R (Localization.AtPrime 𝔭.asIdeal) a
      = (Spec.stalkIso R 𝔭).hom ((Spec R).presheaf.germ Ω 𝔭 h𝔭 u)
        * algebraMap R (Localization.AtPrime 𝔭.asIdeal) b)
    (p : PrimeSpectrum (CommRingCat.of (Cover a b)))
    (hp : (Spec.map (coverSpecHom a b)).base p = 𝔭) :
    IsSquare ((Spec (CommRingCat.of (Cover a b))).presheaf.germ
      (Spec.map (coverSpecHom a b) ⁻¹ᵁ Ω) p
      (show (Spec.map (coverSpecHom a b)).base p ∈ Ω from hp ▸ h𝔭)
      ((Spec.map (coverSpecHom a b)).app Ω u)) := by
  subst hp
  have : ((Spec.map (coverSpecHom a b)).base p).asIdeal.IsPrime :=
    (PrimeSpectrum.comap (coverSpecHom a b).hom p).2
  have h1 := isSquare_localRingHom a b _ hb hu p.asIdeal rfl
  have h2 := h1.map (Spec.stalkIso (CommRingCat.of (Cover a b)) p).inv.hom
  have hstalk := Scheme.localRingHom_comp_stalkIso_apply (coverSpecHom a b) p
    ((Spec R).presheaf.germ Ω ((Spec.map (coverSpecHom a b)).base p) h𝔭 u)
  have hgerm := Scheme.Hom.germ_stalkMap_apply (f := Spec.map (coverSpecHom a b)) Ω p h𝔭 u
  exact hgerm ▸ hstalk ▸ h2

/-- **(SQ) for `Spec R`.** For every commutative ring `R`, every point `x` of `Spec R`, every
open `Ω ∋ x` and every section `u` of the structure sheaf over `Ω`, there is a scheme `A` and an
integral surjective morphism `f : A ⟶ Spec R` such that at every point `p` of `A` over `x` the
image of `u` in the local ring of `A` at `p` is a square.

The morphism is `Spec` of the structure morphism of `Stacks.SquareRootCover.Cover a b`, where
`a / b` is any presentation of the germ of `u` at `x` in `𝒪_{Spec R, x} = R_x`. -/
theorem exists_isIntegralHom_surjective_isSquare_germ (R : CommRingCat.{u})
    (x : PrimeSpectrum R) (Ω : (Spec R).Opens) (hx : x ∈ Ω) (u : Γ(Spec R, Ω)) :
    ∃ (A : Scheme.{u}) (f : A ⟶ Spec R), IsIntegralHom f ∧ Surjective f ∧
      ∀ (p : A) (hp : f.base p = x),
        IsSquare (A.presheaf.germ (f ⁻¹ᵁ Ω) p (show f.base p ∈ Ω from hp ▸ hx)
          (f.app Ω u)) := by
  obtain ⟨⟨a, s⟩, hw⟩ := IsLocalization.mk'_surjective x.asIdeal.primeCompl
    ((Spec.stalkIso R x).hom ((Spec R).presheaf.germ Ω x hx u))
  obtain ⟨b, hb⟩ := s
  have hu : algebraMap R (Localization.AtPrime x.asIdeal) a
      = (Spec.stalkIso R x).hom ((Spec R).presheaf.germ Ω x hx u)
        * algebraMap R (Localization.AtPrime x.asIdeal) b :=
    IsLocalization.mk'_eq_iff_eq_mul.mp hw
  refine ⟨Spec (CommRingCat.of (Cover a b)), Spec.map (coverSpecHom a b), ?_, ?_, ?_⟩
  · rw [IsIntegralHom.SpecMap_iff, coverSpecHom, CommRingCat.hom_ofHom, algebraMap_cover_eq]
    exact isIntegral_coverHom a b
  · refine surjective_specMap_of_exists_isPrime_comap_eq _ fun 𝔮 h𝔮 => ?_
    rw [coverSpecHom, CommRingCat.hom_ofHom]
    exact exists_isPrime_comap_eq a b 𝔮 h𝔮
  · exact fun p hp => isSquare_germ_specMap_cover a b Ω u x hx hb hu p hp

/-- **(SQ) for `Spec R`, in stalk-map form.** The same statement as
`Stacks.SquareRootCover.exists_isIntegralHom_surjective_isSquare_germ`, with the image of `u` in
the local ring of `A` at `p` written as the stalk map of `f` applied to the germ of `u`. The two
agree by `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply`; this is the literal reading of (SQ),
and its type does not depend on the hypothesis `f.base p = x` either, because the germ is taken
at `f.base p` and only its membership proof uses that hypothesis. -/
theorem exists_isIntegralHom_surjective_isSquare_stalkMap (R : CommRingCat.{u})
    (x : PrimeSpectrum R) (Ω : (Spec R).Opens) (hx : x ∈ Ω) (u : Γ(Spec R, Ω)) :
    ∃ (A : Scheme.{u}) (f : A ⟶ Spec R), IsIntegralHom f ∧ Surjective f ∧
      ∀ (p : A) (hp : f.base p = x),
        IsSquare (f.stalkMap p ((Spec R).presheaf.germ Ω (f.base p)
          (show f.base p ∈ Ω from hp ▸ hx) u)) := by
  obtain ⟨A, f, hint, hsurj, hsq⟩ :=
    exists_isIntegralHom_surjective_isSquare_germ R x Ω hx u
  refine ⟨A, f, hint, hsurj, fun p hp => ?_⟩
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact hsq p hp

end Stacks.SquareRootCover

end
