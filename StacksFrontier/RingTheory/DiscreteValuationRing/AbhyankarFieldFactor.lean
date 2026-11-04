module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar
public import StacksFrontier.RingTheory.DiscreteValuationRing.UnramifiedIffEtaleIntegralClosure
public import StacksFrontier.RingTheory.FormallySmooth.AdicArrowIso
public import StacksFrontier.AlgebraicGeometry.Curves.JacobianCriterionNodal
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedConnected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abhyankar's lemma for a given field factor

Let `A` be a discrete valuation ring with fraction field `K`, let `L / K` be a finite separable
extension which is tamely ramified with respect to `A`, and let `F / K` be a finite separable
extension such that the integral closure `A₁` of `A` in `F` is a discrete valuation ring whose
ramification index over `A` is divisible by every ramification index of `L / K`. Abhyankar's lemma
([Stacks, Tag 0BRM]) says that every field factor `E` of `L ⊗_K F` is then unramified with respect
to `A₁`. Here `E` is given as a field together with a surjection `L ⊗_K F → E`, and it may live in
any universe.

The proof localizes: at a maximal ideal `n` of the integral closure of `A` in `E`, with image `m`
in the integral closure of `A` in `L`, the localization `R` of the latter at `m` is a discrete
valuation ring tame over `A` with ramification index that of `m`; Abhyankar's lemma in the form
`IsDiscreteValuationRing.formallySmooth_localizations_of_ramificationIndex_dvd`, applied to
`A → R` and `F`, shows that the localization of `A₁ → E` at `n` is formally smooth for the adic
topology, hence formally unramified. A finite torsion free formally unramified algebra over the
discrete valuation ring `A₁` is étale, and étaleness of the integral closure is unramifiedness.

## Main results

* `IsDiscreteValuationRing.isUnramifiedWithRespectTo_integralClosure_of_tensorProduct_quotient`:
  the statement above.

## References

* [Stacks Project, Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
-/

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v w x y z t

/-- A surjective algebra map from a finite product of fields onto a domain is, up to an
isomorphism, the projection onto one of the factors. -/
theorem Pi.exists_algEquiv_comp_evalAlgHom_eq_of_surjective
    (R : Type u) [CommRing R] {I : Type v} [Finite I] (E : I → Type w)
    [∀ i, Field (E i)] [∀ i, Algebra R (E i)]
    (F : Type x) [CommRing F] [IsDomain F] [Algebra R F]
    (f : (∀ i, E i) →ₐ[R] F) (hf : Function.Surjective f) :
    ∃ (i : I) (g : E i ≃ₐ[R] F), g.toAlgHom.comp (Pi.evalAlgHom R E i) = f := by
  classical
  let _ := Fintype.ofFinite I
  have hsum : ∑ i : I, Pi.single i (1 : E i) = 1 := by
    ext i
    simp
  obtain ⟨i, hi⟩ : ∃ i : I, f (Pi.single i (1 : E i)) ≠ 0 := by
    by_contra! h
    simpa [h] using congrArg f hsum
  let π := Pi.evalAlgHom R E i
  have hπ : Function.Surjective π := Function.surjective_eval i
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker f.toRingHom := by
    intro z (hz : z i = 0)
    change f z = 0
    have hmul : z * Pi.single i (1 : E i) = 0 := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [hz]
      · simp [Pi.single_eq_of_ne hji]
    simpa [hi] using congrArg f hmul
  let g := π.liftOfSurjective hπ f hker
  exact ⟨i, AlgEquiv.ofBijective g
    ⟨g.toRingHom.injective, π.liftOfSurjective_surjective hπ f hker hf⟩,
    π.liftOfSurjective_comp hπ f hker⟩

/-- Integral closure commutes with localization, for an arbitrary model `C` of the integral
closure of `B` in `E`: if `R = S⁻¹B` and `E` is its own localization at `S`, then the integral
closure of `R` in `E` is the localization of `C` at `S`. -/
theorem IsLocalization.integralClosure_of_isIntegralClosure
    (B : Type u) (R : Type v) (E : Type w) (C : Type x)
    [CommRing B] [CommRing R] [CommRing E] [CommRing C]
    [Algebra B R] [Algebra B E] [Algebra R E] [IsScalarTower B R E]
    [Algebra B C] [Algebra C E] [IsScalarTower B C E]
    [IsIntegralClosure C B E]
    [Algebra C (integralClosure R E)]
    [IsScalarTower C (integralClosure R E) E]
    [IsScalarTower B C (integralClosure R E)]
    (S : Submonoid B) [IsLocalization S R]
    [IsLocalization (Algebra.algebraMapSubmonoid E S) E] :
    IsLocalization (Algebra.algebraMapSubmonoid C S) (integralClosure R E) := by
  let D := integralClosure R E
  let C₀ := integralClosure B E
  let e : C₀ ≃ₐ[B] C := IsIntegralClosure.equiv B C₀ E C
  have hsub : C₀ ≤ Subalgebra.restrictScalars B D := fun z hz => hz.tower_top
  let : Algebra C₀ D := (Subalgebra.inclusion hsub).toAlgebra
  have : IsScalarTower C₀ D E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B C₀ D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid C₀ S) D :=
    IsLocalization.integralClosure (R := B) (S := E) (Rf := R) (Sf := E) S
  have hmap : (Algebra.algebraMapSubmonoid C S).map e.symm.toMonoidHom =
      Algebra.algebraMapSubmonoid C₀ S :=
    Algebra.algebraMapSubmonoid_map_eq S e.symm.toAlgHom
  apply IsLocalization.of_ringEquiv_left e.symm.toRingEquiv hmap
  intro c
  apply Subtype.val_injective
  change algebraMap D E (algebraMap C D c) = (e.symm c).1
  rw [← IsScalarTower.algebraMap_apply C D E]
  exact (IsIntegralClosure.algebraMap_equiv B C E C₀ c).symm

/-- Integral closure commutes with localization at a submonoid `S` of `B` whose image in the field
`E` is nonzero: the integral closure of `R = S⁻¹B` in `E` is the localization of `C` at `S`. -/
private theorem IsLocalization.integralClosure_of_isIntegralClosure_of_ne_zero
    (B : Type u) (R : Type v) (E : Type w) (C : Type x)
    [CommRing B] [CommRing R] [Field E] [CommRing C]
    [Algebra B R] [Algebra B E] [Algebra R E] [IsScalarTower B R E]
    [Algebra B C] [Algebra C E] [IsScalarTower B C E]
    [IsIntegralClosure C B E]
    [Algebra C (integralClosure R E)]
    [IsScalarTower C (integralClosure R E) E]
    [IsScalarTower B C (integralClosure R E)]
    (S : Submonoid B) [IsLocalization S R] (hS : ∀ s ∈ S, algebraMap B E s ≠ 0) :
    IsLocalization (Algebra.algebraMapSubmonoid C S) (integralClosure R E) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid E S) E :=
    IsLocalization.self (by
      rintro _ ⟨b, hb, rfl⟩
      exact isUnit_iff_ne_zero.mpr (hS b hb))
  exact IsLocalization.integralClosure_of_isIntegralClosure B R E C S

/-- The image in `C` of the complement of `n ∩ B` is disjoint from the prime `n` of `C`. -/
private theorem Ideal.disjoint_algebraMapSubmonoid_primeCompl_under
    (B : Type u) {C : Type v} [CommRing B] [CommRing C] [Algebra B C]
    (n : Ideal C) [n.IsPrime] :
    Disjoint (Algebra.algebraMapSubmonoid C (n.under B).primeCompl : Set C) n := by
  rw [Set.disjoint_left]
  rintro z ⟨b, hb, rfl⟩ hz
  exact hb hz

/-- The algebra map from a domain `A` to its integral closure in an extension `L` of its fraction
field `K` is injective. -/
private theorem integralClosure.algebraMap_injective_of_isFractionRing
    (A : Type u) (K : Type v) (L : Type w) [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  intro a b h
  apply IsFractionRing.injective A K
  apply (algebraMap K L).injective
  simpa [IsScalarTower.algebraMap_apply A K L] using congrArg Subtype.val h

/-- A map of integral closures of `A` in fields `F → E` compatible with `E / F` is injective. -/
private theorem integralClosure.algebraMap_injective_of_isScalarTower
    (A : Type u) (F : Type v) (E : Type w) [CommRing A] [Field F] [Field E]
    [Algebra A F] [Algebra A E] [Algebra F E]
    [Algebra (integralClosure A F) (integralClosure A E)]
    [IsScalarTower (integralClosure A F) (integralClosure A E) E] :
    Function.Injective (algebraMap (integralClosure A F) (integralClosure A E)) := by
  intro a b h
  apply Subtype.ext
  apply (algebraMap F E).injective
  have h' := congrArg (algebraMap (integralClosure A E) E) h
  rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h'

/-- A map of integral closures of `A` in fields `F → E` compatible with `E / F` is `A`-linear. -/
private theorem integralClosure.isScalarTower_of_isScalarTower
    (A : Type u) (F : Type v) (E : Type w) [CommRing A] [Field F] [Field E]
    [Algebra A F] [Algebra A E] [Algebra F E] [IsScalarTower A F E]
    [Algebra (integralClosure A F) (integralClosure A E)]
    [IsScalarTower (integralClosure A F) (integralClosure A E) E] :
    IsScalarTower A (integralClosure A F) (integralClosure A E) := .of_algebraMap_eq fun a => by
  apply Subtype.val_injective
  change algebraMap A E a = algebraMap (integralClosure A E) E
    (algebraMap (integralClosure A F) (integralClosure A E) (algebraMap A (integralClosure A F) a))
  rw [← IsScalarTower.algebraMap_apply (integralClosure A F) (integralClosure A E) E]
  change algebraMap A E a = algebraMap F E (algebraMap A F a)
  exact IsScalarTower.algebraMap_apply A F E a

/-- Let `(L ⊗_K F) / nil` be a finite product of fields `H i`, compatibly with `L` and `F`. Then
a field quotient `E` of `L ⊗_K F`, compatibly with `L` and `F`, is isomorphic to some `H i`
compatibly with `L` and `F`. -/
private theorem Algebra.TensorProduct.exists_algEquiv_factor_of_surjective
    (K : Type u) (L : Type v) (F : Type w) [Field K] [Field L] [Field F]
    [Algebra K L] [Algebra K F]
    {I : Type x} [Finite I] (H : I → Type y) [∀ i, Field (H i)] [∀ i, Algebra K (H i)]
    [∀ i, Algebra L (H i)] [∀ i, Algebra F (H i)]
    (d : ((L ⊗[K] F) ⧸ nilradical (L ⊗[K] F)) ≃ₐ[K] ∀ i, H i)
    (hdL : ∀ i (l : L), d (Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] F) l)) i = algebraMap L (H i) l)
    (hdF : ∀ i (a : F), d (Ideal.Quotient.mk _
      ((Algebra.TensorProduct.includeRight : F →ₐ[K] L ⊗[K] F) a)) i = algebraMap F (H i) a)
    (E : Type z) [Field E] [Algebra K E] [Algebra L E] [Algebra F E]
    (t : (L ⊗[K] F) →ₐ[K] E) (ht : Function.Surjective t)
    (htL : ∀ l : L, t (l ⊗ₜ[K] 1) = algebraMap L E l)
    (htF : ∀ a : F, t (1 ⊗ₜ[K] a) = algebraMap F E a) :
    ∃ (i : I) (g : H i ≃ₐ[K] E), (∀ l : L, g (algebraMap L (H i) l) = algebraMap L E l) ∧
      ∀ a : F, g (algebraMap F (H i) a) = algebraMap F E a := by
  have hnil : ∀ z ∈ nilradical (L ⊗[K] F), t z = 0 := by
    intro z hz
    have : (RingHom.ker t).IsPrime := RingHom.ker_isPrime t
    exact nilradical_le_prime (RingHom.ker t) hz
  let t₀ := Ideal.Quotient.liftₐ (nilradical (L ⊗[K] F)) t hnil
  have ht₀ : Function.Surjective t₀ := by
    intro e
    obtain ⟨z, rfl⟩ := ht e
    exact ⟨Ideal.Quotient.mk _ z, rfl⟩
  obtain ⟨i, g, hg⟩ := Pi.exists_algEquiv_comp_evalAlgHom_eq_of_surjective K H E
    (t₀.comp d.symm.toAlgHom) (ht₀.comp d.symm.surjective)
  have hg' (z : L ⊗[K] F) : g (d (Ideal.Quotient.mk _ z) i) = t z := by
    have h := AlgHom.congr_fun hg (d (Ideal.Quotient.mk _ z))
    change g (d (Ideal.Quotient.mk _ z) i) = t₀ (Ideal.Quotient.mk _ z)
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
      Pi.evalAlgHom_apply] using h
  refine ⟨i, g, fun l => ?_, fun a => ?_⟩
  · rw [← hdL i l]
    exact (hg' (l ⊗ₜ[K] 1)).trans (htL l)
  · rw [← hdF i a]
    exact (hg' (1 ⊗ₜ[K] a)).trans (htF a)

/-- The residue field of the localization of `B` at a maximal ideal `m` is `A`-isomorphic to
`B ⧸ m`. -/
private theorem nonempty_algEquiv_quotient_residueField
    (A : Type u) {B : Type v} (R : Type w) [CommRing A] [CommRing B] [CommRing R] [IsLocalRing R]
    [Algebra A B] [Algebra B R] [Algebra A R] [IsScalarTower A B R]
    (m : Ideal B) [m.IsMaximal] [IsLocalization.AtPrime R m] :
    Nonempty ((B ⧸ m) ≃ₐ[A] IsLocalRing.ResidueField R) :=
  ⟨{ IsLocalization.AtPrime.equivQuotMaximalIdeal m R with
      commutes' := fun a => by
        change Ideal.Quotient.mk _ (algebraMap B R (algebraMap A B a)) =
          Ideal.Quotient.mk _ (algebraMap A R a)
        rw [← IsScalarTower.algebraMap_apply A B R] }⟩

namespace IsDiscreteValuationRing

/-- The localization of `C` at a prime `n` above the maximal ideal of a discrete valuation ring
`A ⊆ C`, when it is a discrete valuation ring, is an extension of `A`. -/
private theorem isExtension_localization_atPrime
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {C : Type v} [CommRing C] [IsDomain C] [Algebra A C] [FaithfulSMul A C]
    (n : Ideal C) [n.IsPrime] [n.LiesOver (IsLocalRing.maximalIdeal A)]
    [IsDiscreteValuationRing (Localization.AtPrime n)] :
    IsExtension A (Localization.AtPrime n) where
  toFaithfulSMul := (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
    rw [IsScalarTower.algebraMap_eq A C (Localization.AtPrime n)]
    exact (IsLocalization.injective _ n.primeCompl_le_nonZeroDivisors).comp
      (FaithfulSMul.algebraMap_injective A C))
  toIsLocalHom := by
    apply ((local_hom_TFAE (algebraMap A (Localization.AtPrime n))).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq A C (Localization.AtPrime n), ← Ideal.comap_comap]
    change ((IsLocalRing.maximalIdeal (Localization.AtPrime n)).under C).under A = _
    rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime n) n,
      ← Ideal.over_def n (IsLocalRing.maximalIdeal A)]

/-- An extension `A → T` of discrete valuation rings which is essentially of finite type, has
algebraic residue field extension and is formally smooth for the adic topology of `T` is formally
unramified. Indeed formal smoothness forces ramification index one and a separable residue field
extension. -/
theorem formallyUnramified_of_formallySmoothNAdic
    (A : Type u) (T : Type v)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Algebra A T] [IsExtension A T] [Algebra.EssFiniteType A T]
    [Algebra.IsAlgebraic (ResidueField A) (ResidueField T)]
    (h : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A T) (IsLocalRing.maximalIdeal T)) :
    Algebra.FormallyUnramified A T := by
  obtain ⟨he, _⟩ := (formallySmooth_iff_weaklyUnramified_and_isSeparableExtension A T).mp h
  have : Algebra.IsSeparable (ResidueField A) (ResidueField T) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension_of_isAlgebraic
      _ _
  apply Algebra.FormallyUnramified.of_map_maximalIdeal
  obtain ⟨_, hpow, _, _⟩ := ramificationIndex_characterization A T
  change ramificationIndex A T = 1 at he
  simpa only [he, pow_one] using hpow

/-- Let `L / K` be tamely ramified with respect to the discrete valuation ring `A`, and let `R` be
the localization of the integral closure of `A` in `L` at a maximal ideal `m` above `𝔪_A`, a
discrete valuation ring. Then the ramification index of `A → R` is that of `m`, and `A → R`
satisfies the tameness hypothesis of Abhyankar's lemma: residue characteristic zero, or residue
characteristic prime to the ramification index and a separable residue field extension. -/
theorem ramificationIndex_eq_and_tame_of_isLocalization_atPrime
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (htame : IsTamelyRamifiedWithRespectTo A K L)
    (m : Ideal (integralClosure A L)) [m.IsMaximal] [m.LiesOver (IsLocalRing.maximalIdeal A)]
    (R : Type x) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (integralClosure A L) R] [Algebra A R] [IsScalarTower A (integralClosure A L) R]
    [IsLocalization.AtPrime R m] [IsExtension A R] :
    ramificationIndex A R = Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m ∧
      (ringChar (ResidueField A) = 0 ∨
        Nat.Coprime (ringChar (ResidueField A)) (ramificationIndex A R) ∧
          Algebra.IsSeparableExtension (ResidueField A) (ResidueField R)) := by
  let B := integralClosure A L
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (integralClosure.algebraMap_injective_of_isFractionRing A K L)
  obtain ⟨hs, hc⟩ := htame m inferInstance inferInstance
  have hloc : (IsLocalRing.maximalIdeal R).ramificationIdx A = m.ramificationIdx A := by
    have : (IsLocalRing.maximalIdeal R).LiesOver m :=
      ⟨(IsLocalization.AtPrime.under_maximalIdeal R m).symm⟩
    have : Module.Flat B R := IsLocalization.flat R m.primeCompl
    have : Algebra.EssFiniteType B R := Algebra.EssFiniteType.of_isLocalization R m.primeCompl
    have : Algebra.FormallyUnramified B R :=
      Algebra.FormallyUnramified.of_isLocalization m.primeCompl
    have h1 : (IsLocalRing.maximalIdeal R).ramificationIdx B = 1 := Ideal.ramificationIdx_eq_one _ B
    rw [Ideal.ramificationIdx_tower (R := A) m (IsLocalRing.maximalIdeal R), h1, mul_one]
  have he : ramificationIndex A R = Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m := by
    rwa [ramificationIndex_eq_ramificationIdx A R,
      Ideal.ramificationIdx'_eq_ramificationIdx _ _ (IsDiscreteValuationRing.not_a_field A)]
  refine ⟨he, ?_⟩
  obtain hc | hc := hc
  · exact .inl hc
  refine .inr ⟨he ▸ hc, ?_⟩
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  let : Algebra (ResidueField A) (B ⧸ m) :=
    Ideal.Quotient.algebraOfLiesOver m (IsLocalRing.maximalIdeal A)
  have : IsScalarTower A (ResidueField A) (B ⧸ m) := .of_algebraMap_eq fun _ => rfl
  have : Algebra.IsSeparable (ResidueField A) (B ⧸ m) := hs
  obtain ⟨q⟩ := nonempty_algEquiv_quotient_residueField A R m
  let e : (B ⧸ m) ≃ₐ[ResidueField A] ResidueField R :=
    q.extendScalarsOfSurjective
      (show Function.Surjective (algebraMap A (ResidueField A)) from residue_surjective)
  have : Algebra.IsSeparable (ResidueField A) (ResidueField R) :=
    Algebra.IsSeparable.of_algHom _ (B ⧸ m) e.symm.toAlgHom
  exact Stacks.Curves.isSeparableExtension_of_isSeparable

/-- **Abhyankar's lemma at a field factor.** Let `A → B` be an extension of discrete valuation
rings with fraction fields `K → L` which is tame in the sense of Abhyankar's lemma, let `F / K` be
finite, and let `E` be a field which is a quotient of `L ⊗_K F`. Let `p` be a maximal ideal of the
integral closure of `A` in `F` whose ramification index over `A` is divisible by that of `A → B`,
and `q` a maximal ideal of the integral closure of `B` in `E` above it. Then the induced local
homomorphism of localizations is formally smooth for the adic topology. The field `E` may lie in
any universe. -/
theorem exists_formallySmoothNAdic_localization_of_tensorProduct_quotient
    (A : Type u) (B : Type v) (K : Type w) (L : Type x) (F : Type y)
    [CommRing A] [CommRing B] [Field K] [Field L] [Field F]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L] [Algebra K F]
    [Algebra A F] [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K F]
    [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K F]
    (E : Type z) [Field E]
    [Algebra K E] [Algebra L E] [Algebra F E] [Algebra B E]
    [IsScalarTower K L E] [IsScalarTower K F E] [IsScalarTower B L E]
    (t : (L ⊗[K] F) →ₐ[K] E) (ht : Function.Surjective t)
    (htL : ∀ l : L, t (l ⊗ₜ[K] 1) = algebraMap L E l)
    (htF : ∀ f : F, t (1 ⊗ₜ[K] f) = algebraMap F E f)
    (htame : ringChar (ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (ResidueField A)) (ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (ResidueField A) (ResidueField B))
    (f : integralClosure A F →+* integralClosure B E)
    (hf : ∀ z : integralClosure A F, (f z : E) = algebraMap F E (z : F))
    (p : Ideal (integralClosure A F)) [p.IsMaximal]
    (hp : ramificationIndex A B ∣ p.ramificationIdx A)
    (q : Ideal (integralClosure B E)) [q.IsMaximal] (hq : q.comap f = p) :
    ∃ φ : Localization.AtPrime p →+* Localization.AtPrime q,
      Function.Injective φ ∧ IsLocalHom φ ∧
        (∀ z : integralClosure A F, φ (algebraMap _ _ z) = algebraMap _ _ (f z)) ∧
        RingHom.FormallySmoothNAdic.{t} φ (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  classical
  obtain ⟨n, H, hfield, hK, hL, hF, hB, hKL, hKF, hfin, d, hn, hdL, hdF, hdB, hloc⟩ :=
    formallySmooth_localizations_of_ramificationIndex_dvd A B K L F htame
  obtain ⟨i, g, hgL, hgF⟩ := Algebra.TensorProduct.exists_algEquiv_factor_of_surjective K L F H d
    hdL hdF E t ht htL htF
  let gB : H i ≃ₐ[B] E :=
    { g.toRingEquiv with
      commutes' := fun b => by
        change g (algebraMap B (H i) b) = algebraMap B E b
        rw [hdB i b, hgL, ← IsScalarTower.algebraMap_apply B L E] }
  let c : integralClosure B (H i) ≃ₐ[B] integralClosure B E := gB.mapIntegralClosure
  obtain ⟨fᵢ, hfᵢ, hfᵢA, hformal⟩ := hloc i
  have hcf (z : integralClosure A F) : c (fᵢ z) = f z := by
    apply Subtype.ext
    change g (fᵢ z : H i) = (f z : E)
    rw [hfᵢ, hgF, hf]
  let qᵢ := q.comap c.toRingHom
  have : qᵢ.IsMaximal := Ideal.comap_isMaximal_of_surjective _ c.surjective
  have hqᵢ : qᵢ.comap fᵢ = p := by
    rw [← hq]
    change q.comap (c.toRingHom.comp fᵢ) = q.comap f
    congr 1
    exact RingHom.ext hcf
  obtain ⟨_, _, _, _, φ, hφinj, _, hφcomp, hφformal⟩ :=
    hformal p inferInstance hp qᵢ inferInstance hqᵢ
  let b : Localization.AtPrime qᵢ ≃+* Localization.AtPrime q :=
    Localization.localRingEquiv qᵢ q c.toRingEquiv rfl
  have : IsLocalHom b.toRingHom := IsLocalHom.of_surjective _ b.surjective
  refine ⟨b.toRingHom.comp φ, b.injective.comp hφinj, RingHom.isLocalHom_comp b.toRingHom φ, ?_, ?_⟩
  · intro z
    change b (φ (algebraMap _ _ z)) = _
    rw [hφcomp]
    change Localization.localRingHom qᵢ q c.toRingHom rfl
      (algebraMap _ _ (fᵢ z)) = _
    rw [Localization.localRingHom_to_map]
    change algebraMap _ _ (c (fᵢ z)) = algebraMap _ _ (f z)
    rw [hcf]
  · exact RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq (RingEquiv.refl _) b
      (RingHom.ext fun _ => rfl) (map_ringEquiv_maximalIdeal b) hφformal

/-- Let `A₁` be a discrete valuation ring, `C` a finite torsion free `A₁`-algebra which is a
Dedekind domain, `D` a localization of `C` and `q` a maximal ideal of `D` above the maximal ideal
`n` of `C`. If a local homomorphism `(A₁)_{𝔪} → D_q` compatible with `A₁ → D` is formally smooth
for the adic topology, then `C_n` is formally unramified over `A₁`. -/
theorem formallyUnramified_atPrime_of_formallySmoothNAdic_localization
    (A₁ : Type u) (C : Type v) (D : Type w)
    [CommRing A₁] [IsDomain A₁] [IsDiscreteValuationRing A₁]
    [CommRing C] [IsDedekindDomain C] [CommRing D]
    [Algebra A₁ C] [Module.Finite A₁ C] [FaithfulSMul A₁ C]
    [Algebra C D] [Algebra A₁ D] [IsScalarTower A₁ C D]
    (S : Submonoid C) [IsLocalization S D]
    (n : Ideal C) [n.IsMaximal] (q : Ideal D) [q.IsMaximal] (hqn : q.under C = n)
    (φ : Localization.AtPrime (IsLocalRing.maximalIdeal A₁) →+* Localization.AtPrime q)
    (hφcomp : ∀ z : A₁, φ (algebraMap _ _ z) = algebraMap D _ (algebraMap A₁ D z))
    (hφformal : RingHom.FormallySmoothNAdic.{max u v} φ
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))) :
    Algebra.FormallyUnramified A₁ (Localization.AtPrime n) := by
  let T := Localization.AtPrime n
  let U := Localization.AtPrime q
  have : n.LiesOver (IsLocalRing.maximalIdeal A₁) :=
    (Ideal.liesOver_iff _ _).mpr (eq_maximalIdeal (Ideal.IsMaximal.under A₁ n)).symm
  have : IsDiscreteValuationRing T :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C
      (Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A₁) n) T
  have : IsLocalization.AtPrime U n := by
    have hh := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S U q
    change IsLocalization (q.under C).primeCompl U at hh
    simpa only [hqn] using hh
  let b : U ≃ₐ[C] T := IsLocalization.algEquiv n.primeCompl U T
  let a : A₁ ≃ₐ[A₁] Localization.AtPrime (IsLocalRing.maximalIdeal A₁) :=
    IsLocalization.atUnits A₁ (IsLocalRing.maximalIdeal A₁).primeCompl
      (fun z hz => notMem_maximalIdeal.mp hz)
  have hcomm : (algebraMap A₁ T).comp a.symm.toRingEquiv.toRingHom =
      b.toRingEquiv.toRingHom.comp φ := by
    refine RingHom.ext fun y => ?_
    obtain ⟨z, rfl⟩ := a.surjective y
    change algebraMap A₁ T (a.symm (a z)) = b (φ (algebraMap A₁ _ z))
    rw [AlgEquiv.symm_apply_apply, hφcomp, IsScalarTower.algebraMap_apply A₁ C D z]
    change _ = b (algebraMap C U (algebraMap A₁ C z))
    rw [b.commutes, ← IsScalarTower.algebraMap_apply]
  have hformal : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A₁ T)
      (IsLocalRing.maximalIdeal T) :=
    RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq a.symm.toRingEquiv b.toRingEquiv hcomm
      (map_ringEquiv_maximalIdeal b.toRingEquiv) hφformal
  have : IsExtension A₁ T := isExtension_localization_atPrime A₁ n
  have : Algebra.EssFiniteType C T := .of_isLocalization T n.primeCompl
  have : Algebra.EssFiniteType A₁ T := .comp A₁ C T
  obtain ⟨r⟩ := nonempty_algEquiv_quotient_residueField A₁ T n
  have : Module.Finite A₁ (ResidueField T) := Module.Finite.equiv r.toLinearEquiv
  have : Module.Finite (ResidueField A₁) (ResidueField T) :=
    Module.Finite.of_restrictScalars_finite A₁ _ _
  exact formallyUnramified_of_formallySmoothNAdic A₁ T hformal

/-- **Abhyankar's lemma, local step at a localization.** In the situation of
`isUnramifiedWithRespectTo_integralClosure_of_tensorProduct_quotient`, let `n` be a maximal ideal
of the integral closure `C` of `A` in `E` and `R` the localization of the integral closure `B` of
`A` in `L` at `m = n ∩ B`, a discrete valuation ring with fraction field `L`, tame over `A` with
ramification index dividing that of `A₁`. Then `C_n` is formally unramified over `A₁`. -/
theorem formallyUnramified_localization_of_tensorProduct_quotient_of_isLocalization
    (A : Type u) (K : Type v) (L : Type w) (F : Type x)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [Module.Finite K F]
    [IsDiscreteValuationRing (integralClosure A F)]
    (E : Type z) [Field E]
    [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [Algebra A E] [IsScalarTower A K E] [IsScalarTower A F E]
    [Algebra L E] [IsScalarTower K L E] [IsScalarTower A L E]
    (t : (L ⊗[K] F) →ₐ[K] E) (ht : Function.Surjective t)
    (htL : ∀ l : L, t (l ⊗ₜ[K] 1) = algebraMap L E l)
    (htF : ∀ f : F, t (1 ⊗ₜ[K] f) = algebraMap F E f)
    [IsDedekindDomain (integralClosure A E)] [Module.Finite A (integralClosure A E)]
    [Algebra (integralClosure A F) (integralClosure A E)]
    [IsScalarTower (integralClosure A F) (integralClosure A E) E]
    [Algebra (integralClosure A L) (integralClosure A E)]
    [IsScalarTower (integralClosure A L) (integralClosure A E) E]
    (n : Ideal (integralClosure A E)) [n.IsMaximal]
    (R : Type y) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra (integralClosure A L) R] [IsLocalization.AtPrime R (n.under (integralClosure A L))]
    [Algebra R L] [IsScalarTower (integralClosure A L) R L] [IsFractionRing R L]
    [Algebra A R] [IsScalarTower A R L] [IsExtension A R]
    [Algebra R E] [IsScalarTower R L E]
    (hRtame : ringChar (ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (ResidueField A)) (ramificationIndex A R) ∧
        Algebra.IsSeparableExtension (ResidueField A) (ResidueField R))
    (hdivR : ramificationIndex A R ∣
      (IsLocalRing.maximalIdeal (integralClosure A F)).ramificationIdx A) :
    Algebra.FormallyUnramified (integralClosure A F) (Localization.AtPrime n) := by
  let B := integralClosure A L
  let C := integralClosure A E
  let A₁ := integralClosure A F
  let m := n.under B
  have : FaithfulSMul A₁ C := (faithfulSMul_iff_algebraMap_injective A₁ C).mpr
    (integralClosure.algebraMap_injective_of_isScalarTower A F E)
  have : IsScalarTower A A₁ C := integralClosure.isScalarTower_of_isScalarTower A F E
  have : Module.Finite A₁ C := Module.Finite.of_restrictScalars_finite A A₁ C
  have : IsScalarTower B R E := IsScalarTower.to₁₂₄ B R L E
  have hBE : Function.Injective (algebraMap B E) := by
    rw [IsScalarTower.algebraMap_eq B R E, IsScalarTower.algebraMap_eq R L E]
    exact (algebraMap L E).injective.comp ((IsFractionRing.injective R L).comp
      (IsLocalization.injective R m.primeCompl_le_nonZeroDivisors))
  have : IsScalarTower A R E := IsScalarTower.to₁₂₄ A R L E
  let D := integralClosure R E
  have hsub : C ≤ Subalgebra.restrictScalars A D := fun z hz => hz.tower_top
  let cd : C →ₐ[A] D := Subalgebra.inclusion hsub
  let : Algebra C D := cd.toAlgebra
  have : IsScalarTower C D E := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower B C D := .of_algebraMap_eq fun b => by
    apply FaithfulSMul.algebraMap_injective D E
    rw [← IsScalarTower.algebraMap_apply C D E, ← IsScalarTower.algebraMap_apply B C E]
    exact (IsScalarTower.algebraMap_apply B D E b).symm
  have : IsIntegralClosure C B E := IsIntegralClosure.tower_top (R := A)
  have : IsLocalization (Algebra.algebraMapSubmonoid C m.primeCompl) D :=
    IsLocalization.integralClosure_of_isIntegralClosure_of_ne_zero B R E C m.primeCompl
      fun b hb => (map_ne_zero_iff _ hBE).mpr fun h => hb (h ▸ m.zero_mem)
  let q := n.map (algebraMap C D)
  have hdisj := Ideal.disjoint_algebraMapSubmonoid_primeCompl_under B n
  have : q.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint
    (Algebra.algebraMapSubmonoid C m.primeCompl) D n hdisj
  have hqn : q.under C = n :=
    IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid C m.primeCompl) D inferInstance hdisj
  let : Algebra A₁ D := ((algebraMap C D).comp (algebraMap A₁ C)).toAlgebra
  have : IsScalarTower A₁ C D := .of_algebraMap_eq fun _ => rfl
  have hf (z : A₁) : (algebraMap A₁ D z : E) = algebraMap F E (z : F) :=
    (IsScalarTower.algebraMap_apply A₁ C E z).symm
  have hqp : q.comap (algebraMap A₁ D) = IsLocalRing.maximalIdeal A₁ := by
    change (q.under C).under A₁ = _
    rw [hqn]
    exact eq_maximalIdeal (Ideal.IsMaximal.under A₁ n)
  have : IsScalarTower B L E := IsScalarTower.to₁₃₄ B R L E
  have : IsScalarTower A B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨φ, -, -, hφcomp, hφformal⟩ :=
    exists_formallySmoothNAdic_localization_of_tensorProduct_quotient.{u, y, v, w, x, z, max x z}
      A R K L F E t ht htL htF hRtame (algebraMap A₁ D) hf (IsLocalRing.maximalIdeal A₁) hdivR q
      hqp
  exact formallyUnramified_atPrime_of_formallySmoothNAdic_localization A₁ C D
    (Algebra.algebraMapSubmonoid C m.primeCompl) n q hqn φ hφcomp hφformal

/-- **Abhyankar's lemma, local step.** In the situation of
`isUnramifiedWithRespectTo_integralClosure_of_tensorProduct_quotient`, the localization of the
integral closure of `A` in `E` at any maximal ideal is formally unramified over the integral
closure `A₁` of `A` in `F`. -/
theorem formallyUnramified_localization_of_tensorProduct_quotient
    (A : Type u) (K : Type v) (L : Type w) (F : Type x)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [Module.Finite K F] [Algebra.IsSeparable K F]
    [IsDiscreteValuationRing (integralClosure A F)]
    (E : Type z) [Field E]
    [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [Algebra A E] [IsScalarTower A K E] [IsScalarTower A F E]
    [Algebra L E] [IsScalarTower K L E] [IsScalarTower A L E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (t : (L ⊗[K] F) →ₐ[K] E) (ht : Function.Surjective t)
    (htL : ∀ l : L, t (l ⊗ₜ[K] 1) = algebraMap L E l)
    (htF : ∀ f : F, t (1 ⊗ₜ[K] f) = algebraMap F E f)
    (htame : IsTamelyRamifiedWithRespectTo A K L)
    (hdiv : ∀ m : Ideal (integralClosure A L), m.IsMaximal →
      m.LiesOver (IsLocalRing.maximalIdeal A) →
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m ∣
        (IsLocalRing.maximalIdeal (integralClosure A F)).ramificationIdx A)
    [Algebra (integralClosure A F) (integralClosure A E)]
    [IsScalarTower (integralClosure A F) (integralClosure A E) E]
    (n : Ideal (integralClosure A E)) [n.IsMaximal] :
    Algebra.FormallyUnramified (integralClosure A F) (Localization.AtPrime n) := by
  let B := integralClosure A L
  let C := integralClosure A E
  have : Module.Finite K E := Module.Finite.trans F E
  have : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K F E
  have : Module.Finite A C := IsIntegralClosure.finite A K E C
  have : IsDedekindDomain B := integralClosure.isDedekindDomain A K L
  have : IsDedekindDomain C := integralClosure.isDedekindDomain A K E
  have : IsFractionRing B L := integralClosure.isFractionRing_of_finite_extension K L
  have : Module.Finite A B := IsIntegralClosure.finite A K L B
  have hAB := integralClosure.algebraMap_injective_of_isFractionRing A K L
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hAB
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hAB
  let bc : B →ₐ[A] C := (IsScalarTower.toAlgHom A L E).mapIntegralClosure
  let : Algebra B C := bc.toAlgebra
  have : IsScalarTower A B C := .of_algebraMap_eq fun a => (bc.commutes a).symm
  have : IsScalarTower B C E := .of_algebraMap_eq fun _ => rfl
  let m := n.under B
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  have : m.IsMaximal := Ideal.IsMaximal.under B n
  have : m.LiesOver (IsLocalRing.maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr (eq_maximalIdeal (Ideal.IsMaximal.under A m)).symm
  have hm0 : m ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field A) m
  let R := Localization.AtPrime m
  let : Algebra R L := IsLocalization.localizationAlgebraOfSubmonoidLe _ _
    m.primeCompl (nonZeroDivisors B) m.primeCompl_le_nonZeroDivisors
  have : IsScalarTower B R L :=
    IsLocalization.localization_isScalarTower_of_submonoid_le R L m.primeCompl
      (nonZeroDivisors B) m.primeCompl_le_nonZeroDivisors
  have : IsScalarTower A R L := IsScalarTower.to₁₃₄ A B R L
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl R L
  have : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hm0 R
  have : IsExtension A R := isExtension_localization_atPrime A m
  let : Algebra R E := ((algebraMap L E).comp (algebraMap R L)).toAlgebra
  have : IsScalarTower R L E := .of_algebraMap_eq fun _ => rfl
  obtain ⟨hindex, hRtame⟩ :=
    ramificationIndex_eq_and_tame_of_isLocalization_atPrime A K L htame m R
  exact formallyUnramified_localization_of_tensorProduct_quotient_of_isLocalization A K L F E t ht
    htL htF n R hRtame (hindex ▸ hdiv m inferInstance inferInstance)

/-- **Abhyankar's lemma for a given field factor.** Let `A` be a discrete valuation ring with
fraction field `K`, let `L / K` be finite separable and tamely ramified with respect to `A`, and
let `F / K` be finite separable such that the integral closure `A₁` of `A` in `F` is a discrete
valuation ring whose ramification index over `A` is divisible by the ramification index of every
maximal ideal of the integral closure of `A` in `L`. Then every field `E`, in any universe, which
is a quotient of `L ⊗_K F` (via `t`, compatibly with `L` and `F`) is unramified with respect
to `A₁`. -/
@[sga "1 X 3.6" "special case", sga "1 XIII 5.2" "special case"]
theorem isUnramifiedWithRespectTo_integralClosure_of_tensorProduct_quotient
    (A : Type u) (K : Type v) (L : Type w) (F : Type x)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Module.Finite K L] [Algebra.IsSeparable K L]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [Module.Finite K F] [Algebra.IsSeparable K F]
    [IsDiscreteValuationRing (integralClosure A F)]
    [IsFractionRing (integralClosure A F) F]
    (E : Type z) [Field E]
    [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [Algebra A E] [IsScalarTower A K E] [IsScalarTower A F E]
    [Algebra L E] [IsScalarTower K L E] [IsScalarTower A L E]
    [Module.Finite F E] [Algebra.IsSeparable F E]
    (t : (L ⊗[K] F) →ₐ[K] E) (ht : Function.Surjective t)
    (htL : ∀ l : L, t (l ⊗ₜ[K] 1) = algebraMap L E l)
    (htF : ∀ f : F, t (1 ⊗ₜ[K] f) = algebraMap F E f)
    (htame : IsTamelyRamifiedWithRespectTo A K L)
    (hdiv : ∀ m : Ideal (integralClosure A L), m.IsMaximal →
      m.LiesOver (IsLocalRing.maximalIdeal A) →
      Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A) m ∣
        (IsLocalRing.maximalIdeal (integralClosure A F)).ramificationIdx A) :
    IsUnramifiedWithRespectTo (integralClosure A F) F E := by
  classical
  let C := integralClosure A E
  let A₁ := integralClosure A F
  have : Module.Finite K E := Module.Finite.trans F E
  have : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K F E
  have : Module.Finite A C := IsIntegralClosure.finite A K E C
  let ac : A₁ →ₐ[A] C := (IsScalarTower.toAlgHom A F E).mapIntegralClosure
  let : Algebra A₁ C := ac.toAlgebra
  have : IsScalarTower A A₁ C := .of_algebraMap_eq fun a => (ac.commutes a).symm
  have : IsScalarTower A₁ C E := .of_algebraMap_eq fun _ => rfl
  have : IsIntegralClosure C A₁ E := IsIntegralClosure.tower_top (R := A)
  have : Module.IsTorsionFree A₁ C := Module.isTorsionFree_iff_algebraMap_injective.mpr
    fun _ _ h => Subtype.ext ((algebraMap F E).injective (congrArg Subtype.val h))
  have : Module.Finite A₁ C := Module.Finite.of_restrictScalars_finite A A₁ C
  have : Algebra.FormallyUnramified A₁ C := by
    refine Algebra.formallyUnramified_iff_forall.mpr fun p => ?_
    obtain ⟨n, hn, hpn⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
    have : Algebra.IsUnramifiedAt A₁ n :=
      formallyUnramified_localization_of_tensorProduct_quotient A K L F E t ht htL htF htame
        hdiv n
    exact Algebra.isOpen_unramifiedLocus.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes p ⟨n, hn.isPrime⟩).mp hpn) this
  have : Algebra.FinitePresentation A₁ C :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact (isUnramifiedWithRespectTo_iff_etale_integralClosure A₁ F E C).mpr
    Algebra.Etale.of_formallyUnramified_of_flat

end IsDiscreteValuationRing
