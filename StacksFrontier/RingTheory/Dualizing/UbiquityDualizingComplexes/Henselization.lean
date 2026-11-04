module

public import StacksFrontier.RingTheory.Dualizing.NormalizedShift
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.FlatBaseChange
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.RingTheory.Henselian.Pair.Henselization

import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# Dualizing complexes and henselization

The base change of a dualizing complex to the henselization of a pair, and to the henselization
or a strict henselization of a Noetherian local ring, is again a dualizing complex.

## Main results

* `Dualizing.isDualizingComplex_henselizationPair`: a dualizing complex over a Noetherian ring
  `A` remains dualizing after base change to the henselization `A^h` of a pair `(A, I)`.
* `Dualizing.isDualizingComplex_henselization`: the same for the henselization of a Noetherian
  local ring.
* `Dualizing.isDualizingComplex_strictHenselization`: the same for a henselization of a
  Noetherian local ring along an arbitrary prescribed extension of its residue field, hence in
  particular for a strict henselization, where that extension is a separable algebraic closure.

## Implementation notes

The first two statements are instances of the flat base change criterion
`Dualizing.isDualizingComplex_extendScalars_of_flat` of [Stacks, Tag 0DWC]: its two hypotheses
ask that `A ⧸ I → A^h ⧸ I A^h` be bijective and that `I A^h` lie in the Jacobson radical of
`A^h`.

* For the henselization of a pair `(A, I)` the first hypothesis is the `n = 1` case of
  `flat_henselization_and_bijective_quotientMap` ([Stacks, Tag 0AGU]) and the second is the
  defining Jacobson condition on the henselian pair `(A^h, I A^h)`. Flatness comes from the same
  lemma and Noetherianness from `henselization_isNoetherian_and_completion_equiv`
  ([Stacks, Tag 0AGV]).
* For the henselization of a local ring `A`, taken at `I = 𝔪_A`, the first hypothesis is
  bijectivity of the residue field map, which is the residue field condition defining
  `IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) A^h` transported along
  `𝔪_A A^h = 𝔪_{A^h}`, and the second is the equality of the maximal ideal of a local ring with
  its Jacobson radical.

A strict henselization is *not* covered by that criterion, because the residue field map
`κ → κ^{sep}` is not bijective. There the normalized criterion
`Dualizing.isNormalizedDualizingComplex_extendScalars_of_flat` of [Stacks, Tag 0AWD] is used
instead, whose hypothesis on the ideal is only `𝔪_A A^{sh} = 𝔪_{A^{sh}}`. It applies to a
*normalized* dualizing complex, so the given dualizing complex is first shifted into its
normalization (`Dualizing.exists_isNormalizedDualizingComplex_shift`), then base changed, then
shifted back; the shift is undone using that extension of scalars commutes with the shift on
derived categories and that a shift of a dualizing complex is again one
(`Dualizing.isDualizingComplex_shift`). Nothing in that argument uses that the prescribed
residue extension is a separable algebraic closure, so it is stated for an arbitrary extension
and therefore also covers the henselization; the dedicated henselization statement is kept
because it is free of the universe constraint the normalized criterion imposes — there the ring
and module universes are independent, here the module universe is `max u v w`.

Flatness and Noetherianness of the henselization are conclusions of the cited lemmas rather than
hypotheses, but the conclusion already mentions them: `Dualizing.IsDualizingComplex` over `A^h`
needs `IsNoetherianRing A^h`, and the functor `ModuleCat.extendScalars` is exact — which is what
makes it act on derived categories — only because the map is flat. They are therefore introduced
by `haveI` inside the statement, in the same way as the derived-functor instance of
`Dualizing.derivedHomBaseChange_isIso_of_flat_pseudoCoherent`. All of them are propositions, so
this pins no data.

The statement conjoining all three parts of [Stacks, Tag 0DWD] — these three together with
`Dualizing.isDualizingComplex_adicCompletion` — is
`Dualizing.isDualizingComplex_completion_henselization` in
`StacksFrontier/RingTheory/Dualizing/UbiquityDualizingComplexes/CompletionHenselization.lean`.

## References

* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD)
* [Stacks Project, Tag 0DWC](https://stacks.math.columbia.edu/tag/0DWC)
* [Stacks Project, Tag 0AWD](https://stacks.math.columbia.edu/tag/0AWD)
* [Stacks Project, Tag 0AGU](https://stacks.math.columbia.edu/tag/0AGU)
* [Stacks Project, Tag 0AGV](https://stacks.math.columbia.edu/tag/0AGV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalars_additive
  Dualizing.extendScalars_preservesFiniteLimits_of_flat
  Dualizing.extendScalars_preservesFiniteColimits_of_flat

universe u v w t

namespace Dualizing

/-- **Stacks Project, Tag 0DWD, part (1).** The derived base change of a dualizing complex to
the henselization `A^h` of a pair `(A, I)` with `A` Noetherian is a dualizing complex. -/
@[stacks 0DWD "pair_henselization"]
public theorem isDualizingComplex_henselizationPair
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (Ah : Type w) [CommRing Ah] [Algebra A Ah]
    (hh : HenselianPair Ah (I.map (algebraMap A Ah)))
    (hι : ∀ (B : Type (max u w)) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J →
        ∀ f : A →+* B, I ≤ J.comap f →
          ∃! g : Ah →+* B,
            g.comp (algebraMap A Ah) = f ∧ I.map (algebraMap A Ah) ≤ J.comap g)
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) :
    haveI : Module.Flat A Ah :=
      (flat_henselization_and_bijective_quotientMap A I Ah hh hι).1
    haveI : IsNoetherianRing Ah :=
      (henselization_isNoetherian_and_completion_equiv A I Ah hh hι).2.1
    IsDualizingComplex
      ((ModuleCat.extendScalars.{u, w, v} (algebraMap A Ah)).mapDerivedCategory.obj K) := by
  obtain ⟨hflat, hpow⟩ := flat_henselization_and_bijective_quotientMap A I Ah hh hι
  have : Module.Flat A Ah := hflat
  have : IsNoetherianRing Ah :=
    (henselization_isNoetherian_and_completion_equiv A I Ah hh hι).2.1
  exact isDualizingComplex_extendScalars_of_flat I (by rw [← pow_one I]; exact hpow 1)
    (by simpa only [Ideal.jacobson_bot] using hh.1) K hK

/-- For a henselization of a local ring along the identity extension of its residue field, the
canonical map `A ⧸ 𝔪_A → A^h ⧸ 𝔪_A A^h` is bijective: the target is the residue field of `A^h`,
because `𝔪_A A^h = 𝔪_{A^h}`, and the residue field condition identifies it with `A ⧸ 𝔪_A`. -/
private theorem bijective_quotientMap_maximalIdeal_of_isHenselization
    {A : Type u} [CommRing A] [IsLocalRing A]
    {Ah : Type w} [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] :
    Function.Bijective (Ideal.quotientMap
      ((maximalIdeal A).map (algebraMap A Ah)) (algebraMap A Ah) Ideal.le_comap_map) := by
  obtain ⟨e, he⟩ :=
    IsHenselization.exists_residueFieldEquiv (R := A) (L := ResidueField A) (Rh := Ah)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at he
  let q := Ideal.quotientMap ((maximalIdeal A).map (algebraMap A Ah))
    (algebraMap A Ah) Ideal.le_comap_map
  let g : (Ah ⧸ (maximalIdeal A).map (algebraMap A Ah)) ≃+* ResidueField Ah :=
    Ideal.quotEquivOfEq (IsHenselization.map_maximalIdeal (L := ResidueField A))
  have hc : ∀ x : ResidueField A, g (q x) = e x := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective (R := A) x
    rw [he a]
    rfl
  exact ⟨fun x y hxy => e.injective ((hc x).symm.trans ((congrArg g hxy).trans (hc y))),
    fun y => ⟨e.symm (g y), g.injective ((hc _).trans (e.apply_symm_apply (g y)))⟩⟩

/-- **Stacks Project, Tag 0DWD, part (3), the henselization.** The derived base change of a
dualizing complex to the henselization `A^h` of a Noetherian local ring `A` is a dualizing
complex. -/
@[stacks 0DWD "local_henselization"]
public theorem isDualizingComplex_henselization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {Ah : Type w} [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K) :
    haveI : Module.Flat A Ah := IsHenselization.flat (L := ResidueField A)
    haveI : IsNoetherianRing Ah :=
      isNoetherianRing_of_isHenselization (A := A) (B := Ah) (ResidueField A)
    IsDualizingComplex
      ((ModuleCat.extendScalars.{u, w, v} (algebraMap A Ah)).mapDerivedCategory.obj K) := by
  have : Module.Flat A Ah := IsHenselization.flat (L := ResidueField A)
  have : IsNoetherianRing Ah :=
    isNoetherianRing_of_isHenselization (A := A) (B := Ah) (ResidueField A)
  exact isDualizingComplex_extendScalars_of_flat (maximalIdeal A)
    bijective_quotientMap_maximalIdeal_of_isHenselization
    (by rw [IsHenselization.map_maximalIdeal (L := ResidueField A), ← Ideal.jacobson_bot,
      jacobson_eq_maximalIdeal (⊥ : Ideal Ah) bot_ne_top]) K hK

/-- **Stacks Project, Tag 0DWD, part (3), the strict henselization.** The derived base change of
a dualizing complex to a henselization `A^{sh}` of a Noetherian local ring `A` along a
prescribed extension `κ ⊆ L` of its residue field — for `L` a separable algebraic closure of
`κ`, a strict henselization of `A` — is a dualizing complex. -/
@[stacks 0DWD "local_strict_henselization"]
public theorem isDualizingComplex_strictHenselization
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (L : Type t) [Field L] [Algebra (ResidueField A) L]
    {Ash : Type w} [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [IsHenselization A L Ash]
    (K : DerivedCategory (ModuleCat.{max u v w} A)) (hK : IsDualizingComplex K) :
    haveI : Module.Flat A Ash := IsHenselization.flat (L := L)
    haveI : IsNoetherianRing Ash :=
      isNoetherianRing_of_isHenselization (A := A) (B := Ash) L
    IsDualizingComplex
      ((ModuleCat.extendScalars.{u, w, max u v w}
        (algebraMap A Ash)).mapDerivedCategory.obj K) := by
  have : Module.Flat A Ash := IsHenselization.flat (L := L)
  have : IsNoetherianRing Ash :=
    isNoetherianRing_of_isHenselization (A := A) (B := Ash) L
  have : IsLocalHom (algebraMap A Ash) := IsHenselization.isLocalHom (L := L)
  have hmax : (maximalIdeal A).map (algebraMap A Ash) = maximalIdeal Ash :=
    IsHenselization.map_maximalIdeal (L := L)
  let F := ModuleCat.extendScalars.{u, w, max u v w} (algebraMap A Ash)
  obtain ⟨m, hm⟩ := exists_isNormalizedDualizingComplex_shift.{u, max v w} K hK
  have hshift : IsDualizingComplex ((F.mapDerivedCategory.obj (K⟦-m⟧))⟦m⟧) :=
    isDualizingComplex_shift _
      (isNormalizedDualizingComplex_extendScalars_of_flat.{u, v, w} hmax (K⟦-m⟧) hm).1 m
  exact isDualizingComplex_of_iso
    ((shiftFunctor (DerivedCategory (ModuleCat.{max u v w} Ash)) m).mapIso
        ((F.mapDerivedCategory.commShiftIso (-m)).app K) ≪≫
      (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{max u v w} Ash)) (-m) m
        (by omega)).app (F.mapDerivedCategory.obj K))
    hshift

end Dualizing
