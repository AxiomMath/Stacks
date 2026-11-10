module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.NormalizedFiniteMap
public import StacksFrontier.RingTheory.Dualizing.NormalizedShift

/-!
# The dimension function of a dualizing complex

Let `A` be a Noetherian ring and `K` a dualizing complex over `A`. For a prime `p` of `A` the
localization `K_p` is a dualizing complex over the Noetherian local ring `A_p`, and exactly one
shift of it is normalized. The integer by which one must shift is the value at `p` of the
*dimension function* `δ_K` attached to `K`: by definition `δ_K(p)` is the unique integer `n` for
which `K_p⟦-n⟧` is a normalized dualizing complex over `A_p`.

The two facts that make this a definition are already available: some shift of a dualizing
complex over a Noetherian local ring is normalized, and only one shift is. Everything else about
`δ_K` is read off those two through the characterisation `Dualizing.dualizingDimension_eq_iff`,
which says that `n = δ_K(p)` is *equivalent* to `K_p⟦-n⟧` being normalized; the definition itself
is an infimum only in order to produce an integer without choice.

For a surjection `f : A → B` of Noetherian rings the complex `RHom_A(B, K)` is a dualizing
complex over `B`, and its dimension function is the restriction of `δ_K` along the induced closed
immersion `Spec B → Spec A`. Over the local rings this is the statement that `RHom` of a
normalized dualizing complex along a finite local homomorphism is normalized, with no shift; the
remaining input is the compatibility of derived Hom along a finite map with localization, which
appears here as the hypothesis `hcomparison` of
`Dualizing.dualizingDimension_derivedHom_of_surjective_of_localizationComparison`.

## Main definitions

* `Dualizing.dualizingDimension` — the dimension function `δ_K` of a dualizing complex `K` over a
  Noetherian ring, evaluated at a prime.

## Main results

* `Dualizing.dualizingDimension_spec` — the localization of `K` at `p`, shifted by
  `-δ_K(p)`, is a normalized dualizing complex over `A_p`.
* `Dualizing.dualizingDimension_eq_iff` — and that shift is the only one, so `δ_K(p)` is
  characterised by the property defining it.
* `Dualizing.dualizingDimension_derivedHom_of_surjective_of_localizationComparison` — for a
  surjection of Noetherian rings the dimension function of `RHom_A(B, K)` is the restriction of
  the dimension function of `K`, given the comparison of derived Hom with localization.

## Implementation notes

The dimension function is the normalizing shift of the localized complex, as in Stacks section
47.17: `δ_K(p)` is the integer `n` such that `K_p⟦-n⟧` is normalized. Its well-definedness is
exactly the uniqueness of that shift, `Dualizing.isNormalizedDualizingComplex_shift_iff_eq`,
together with the existence `Dualizing.exists_isNormalizedDualizingComplex_shift`; the two
together say that the set of normalizing shifts is a singleton, which is what
`Dualizing.exists_isNormalizedDualizingComplex_shift_set_eq_singleton` records and what makes the
infimum in the definition equal to the integer intended.

The localization is the derived extension of scalars along `A → A_p`, and that it is again
dualizing is [Stacks, Tag 0A7G] (`Dualizing.isDualizingComplex_localization`); Noetherianness of
`A_p` is Mathlib's instance for a localization of a Noetherian ring.

Derived categories are at `HasDerivedCategory.standard`, forced by `Dualizing.derivedHom`, which
bakes that model into its own type; `Dualizing.IsNormalizedDualizingComplex` and hence
`Dualizing.dualizingDimension` inherit the pin, while `Dualizing.IsDualizingComplex` takes a free
model. Noetherianness of the target of a surjection is an instance hypothesis rather than a
consequence derived in the statement, because `Dualizing.IsDualizingComplex` over `B` cannot be
written down without it.

## References

* [Stacks Project, Tag 0A7Y](https://stacks.math.columbia.edu/tag/0A7Y)
* [Stacks Project, Tag 0A7W](https://stacks.math.columbia.edu/tag/0A7W)
* [Stacks Project, Tag 0A7N](https://stacks.math.columbia.edu/tag/0A7N)
* [Stacks Project, Tag 0A7L](https://stacks.math.columbia.edu/tag/0A7L)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The normalizing shifts of a dualizing complex over a Noetherian local ring form a singleton:
there is an integer `m` at which the complex is normalized, and `m` is the only one. -/
theorem exists_isNormalizedDualizingComplex_shift_set_eq_singleton
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (L : DerivedCategory (ModuleCat.{max v u} R)) (hL : IsDualizingComplex L) :
    ∃ m : ℤ, IsNormalizedDualizingComplex.{u, v} (L⟦-m⟧) ∧
      {n : ℤ | IsNormalizedDualizingComplex.{u, v} (L⟦-n⟧)} = {m} := by
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, v} L hL
  refine ⟨m, hm, ?_⟩
  ext n
  change IsNormalizedDualizingComplex.{u, v} (L⟦-n⟧) ↔ n = m
  exact isNormalizedDualizingComplex_shift_iff_eq.{u, v} L m hm n

/-- A shift of a dualizing complex over a Noetherian local ring is normalized exactly when the
shift is the infimum of the normalizing shifts — that infimum being the unique one. -/
theorem isNormalizedDualizingComplex_shift_iff_eq_sInf
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (L : DerivedCategory (ModuleCat.{max v u} R)) (hL : IsDualizingComplex L) (n : ℤ) :
    IsNormalizedDualizingComplex.{u, v} (L⟦-n⟧) ↔
      n = sInf {k : ℤ | IsNormalizedDualizingComplex.{u, v} (L⟦-k⟧)} := by
  obtain ⟨m, hm, hset⟩ := exists_isNormalizedDualizingComplex_shift_set_eq_singleton.{u, v} L hL
  rw [hset, csInf_singleton]
  exact isNormalizedDualizingComplex_shift_iff_eq.{u, v} L m hm n

/-- The **dimension function** of a dualizing complex `K` over a Noetherian ring `A`: the value
at a prime `p` is the unique integer `n` for which the localization `K_p`, shifted by `-n`, is a
normalized dualizing complex over `A_p`. The infimum is a device for naming that integer; it is
attained and unique by `Dualizing.dualizingDimension_eq_iff`. -/
@[stacks 0A7W "the function δ attached to a dualizing complex over a Noetherian ring"]
noncomputable def dualizingDimension {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (p : PrimeSpectrum A) : ℤ :=
  sInf {n : ℤ | IsNormalizedDualizingComplex.{u, v}
    (((StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap A (Localization.AtPrime p.asIdeal))).obj K)⟦-n⟧)}

/-- The localization at a prime of a dualizing complex is a dualizing complex over the localized
ring. This is [Stacks, Tag 0A7G] at the localization `A → A_p`. -/
theorem isDualizingComplex_localizationAtPrime {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) :
    IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime p.asIdeal))).obj K) :=
  isDualizingComplex_localization p.asIdeal.primeCompl K hK

/-- Extension of scalars along the identity carries a dualizing complex whose modules live in an
arbitrary universe to a dualizing complex whose modules live above the universe of the ring. The
derived extension functor performs the universe lift internally, so no smallness hypothesis on
`A` is needed. -/
theorem isDualizingComplex_derivedExtensionScalars_self
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) :
    IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap A A)).obj K) := by
  have : IsLocalization (⊥ : Submonoid A) A := IsLocalization.self bot_le
  exact isDualizingComplex_localization (⊥ : Submonoid A) K hK

/-- **The defining property of the dimension function.** A shift of the localization of a
dualizing complex at a prime is normalized exactly when the shift is the value of the dimension
function there. -/
@[stacks 0A7W "δ(p) is the unique integer n with K_p⟦-n⟧ normalized over A_p"]
theorem dualizingDimension_eq_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) (n : ℤ) :
    IsNormalizedDualizingComplex.{u, v}
        (((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap A (Localization.AtPrime p.asIdeal))).obj K)⟦-n⟧) ↔
      n = dualizingDimension.{u, v} K p :=
  isNormalizedDualizingComplex_shift_iff_eq_sInf.{u, v} _
    (isDualizingComplex_localizationAtPrime.{u, v} K hK p) n

/-- **The dimension function is a normalizing shift.** Shifting the localization of a dualizing
complex at a prime by minus the value of the dimension function there gives a normalized
dualizing complex. -/
theorem dualizingDimension_spec {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (p : PrimeSpectrum A) :
    IsNormalizedDualizingComplex.{u, v}
      (((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime p.asIdeal))).obj K)⟦
          -dualizingDimension.{u, v} K p⟧) :=
  (dualizingDimension_eq_iff.{u, v} K hK p _).mpr rfl

/-- **The dimension function of `RHom_A(B, K)` along a surjection.** For a surjection `f : A → B`
of Noetherian rings and a dualizing complex `K` over `A`, the dimension function of the dualizing
complex `RHom_A(B, K)` over `B` is the restriction of the dimension function of `K` along the
closed immersion `Spec B → Spec A`.

The hypothesis `hcomparison` is the compatibility of derived Hom along `f` with localization: the
localization at `q` of `RHom_A(B, K)` is `RHom_{A_p}(B_q, K_p)`, where `g : A_p → B_q` is the
surjection induced by `f` on the local rings. Given it, the equality of the two shifts is the
uniqueness of the normalizing shift over `B_q`, because `RHom_{A_p}(B_q, -)` carries the
normalized dualizing complex `K_p⟦-δ_K(p)⟧` to a normalized dualizing complex
([Stacks, Tag 0A7N]). -/
theorem dualizingDimension_derivedHom_of_surjective_of_localizationComparison
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : Function.Surjective f)
    (K : DerivedCategory (ModuleCat.{max v u} A)) (hK : IsDualizingComplex K)
    (q : PrimeSpectrum B)
    (g : Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal →+*
      Localization.AtPrime q.asIdeal)
    (hg : Function.Surjective g)
    (hcomparison : Nonempty
      (((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap B (Localization.AtPrime q.asIdeal))).obj
          ((derivedHom.{u, v} f).obj K)) ≅
        (derivedHom.{u, v} g).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap A
              (Localization.AtPrime (PrimeSpectrum.comap f q).asIdeal))).obj K))) :
    dualizingDimension.{u, v} ((derivedHom.{u, v} f).obj K) q =
      dualizingDimension.{u, v} K (PrimeSpectrum.comap f q) := by
  have : IsLocalHom g := IsLocalHom.of_surjective g hg
  let p := PrimeSpectrum.comap f q
  let D := (derivedHom.{u, v} f).obj K
  let F := derivedHom.{u, v} g
  let Kp := (StacksDraft.PseudoCoherence.derivedExtensionScalars
    (algebraMap A (Localization.AtPrime p.asIdeal))).obj K
  let m := dualizingDimension.{u, v} K p
  have hD : IsDualizingComplex D :=
    isDualizingComplex_derivedHom_of_finite.{u, v} f (RingHom.Finite.of_surjective f hf) K hK
  have hKp : IsNormalizedDualizingComplex.{u, v} (Kp⟦-m⟧) :=
    dualizingDimension_spec.{u, v} K hK p
  have hFKp : IsNormalizedDualizingComplex.{u, v} (F.obj (Kp⟦-m⟧)) :=
    isNormalizedDualizingComplex_derivedHom.{u, v} g
      (RingHom.Finite.of_surjective g hg) (Kp⟦-m⟧) hKp
  have : F.CommShift ℤ := by
    dsimp only [F, derivedHom]
    infer_instance
  obtain ⟨e⟩ := hcomparison
  have hn : IsNormalizedDualizingComplex.{u, v}
      (((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap B (Localization.AtPrime q.asIdeal))).obj D)⟦-m⟧) :=
    (isNormalizedDualizingComplex_congr.{u, v}
      ((shiftFunctor _ (-m)).mapIso e ≪≫ ((F.commShiftIso (-m)).app Kp).symm)).mpr hFKp
  exact ((dualizingDimension_eq_iff.{u, v} D hD q m).mp hn).symm

end Dualizing

end
