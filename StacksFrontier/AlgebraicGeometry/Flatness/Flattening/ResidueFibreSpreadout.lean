module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.IsTensorProduct
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutQuotient
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ResidueFieldFibreInjectivity

/-!
# One good residue fibre spreads out to a neighbourhood

Fix the standing situation of Stacks 0AT6: a finitely presented algebra `B` over `A`, a
multiplicative subset `S ⊆ B`, and a finitely presented module `N` over the localization
`Bₛ`. Fix in addition a flat `A`-module `M` and an `A`-linear map `u : N → M`. Call a prime
`𝔮` of `A` *good* if `u ⊗ id_{κ(𝔮)}` is injective.

This file proves the first half of Claim 2 in the proof of Stacks 05U9: goodness spreads
out. If `𝔭` is good, there is a finitely generated ideal `𝔞 ⊆ 𝔭 A_𝔭` such that every prime
`𝔮 ⊆ 𝔭` of `A` whose extension to `A_𝔭` contains `𝔞` is good.

The argument is the one in the source: Stacks 0AT8 supplies a finitely generated
`𝔞 ⊆ 𝔭 A_𝔭` such that the base change of the situation to `A_𝔭 ⧸ 𝔞` carries a pure
spreadout, and Stacks 0AT7 part (2) turns injectivity on the single fibre `κ(𝔭)` of that
base change into universal injectivity over `A_𝔭 ⧸ 𝔞`; a prime `𝔮 ⊆ 𝔭` with
`𝔞 ⊆ 𝔮 A_𝔭` makes `κ(𝔮)` a module over `A_𝔭 ⧸ 𝔞`, so the universal injectivity applies to
it.

## Main results

* `AlgebraicGeometry.exists_fg_ideal_rTensor_residueField_injective_of_le`: a good prime
  admits a finitely generated ideal of its local ring, contained in the extension of the
  prime, cutting out a set of good primes below it. This is the `hspread` hypothesis of
  `AlgebraicGeometry.rTensor_residueField_injective_of_spreadout_of_step`.

## Implementation notes

Every lemma in this file is the "one fibre" refinement of a lemma already proved in
`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ResidueFieldFibreInjectivity`, where the
injectivity hypothesis is imposed at *every* prime because that is all the proof of Stacks
0AT9 needs. The proofs there use their hypothesis only at the single prime `𝔭`, so the
refinements are the same arguments run from a weaker hypothesis. Everything the two files
share is imported from there rather than restated: the local-quotient base change
`AlgebraicGeometry.isBaseChange_localQuotient_moduleMap`, the induced maps
`AlgebraicGeometry.localQuotientMap` and `AlgebraicGeometry.localQuotientMapULift`, the
fibre comparison `AlgebraicGeometry.fiberBaseChangeLinearEquiv`, and the generic injectivity
lemmas.

The base change of the situation along `A → A_𝔭 ⧸ 𝔞` lands in larger universes, and the
test modules of the universal injectivity produced by Stacks 0AT7 must live in the universe
`max (max u₁ u₃) u₄` that binder pins. The residue field `κ(𝔮)` lives in `u₁`, so it is
`ULift`ed before the universal injectivity is applied to it and transported back afterwards.

## References

* [Stacks Project, Tag 0AT7](https://stacks.math.columbia.edu/tag/0AT7)
* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
* [Stacks Project, Tag 05U9](https://stacks.math.columbia.edu/tag/05U9)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄

namespace AlgebraicGeometry

open TensorProduct

/-- Injectivity on a fibre transfers along an isomorphism of the fibre rings: if
`f ⊗ id_L` is injective and `K ≃ L` over `S`, then `(S ⊗ f) ⊗ id_K` is injective. -/
theorem injective_rTensor_baseChange_of_algEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {K L : Type*} [CommRing K] [CommRing L] [Algebra S K] [Algebra S L]
    [Module R K] [Module R L] [IsScalarTower R S K] [IsScalarTower R S L]
    (e : K ≃ₐ[S] L) (f : P →ₗ[R] Q) (hf : Function.Injective (f.rTensor L)) :
    Function.Injective ((f.baseChange S).rTensor K) := by
  intro x y hxy
  have htransport := congrArg (fiberBaseChangeLinearEquiv (P := Q) e) hxy
  have hx := LinearMap.congr_fun (fiberBaseChangeLinearEquiv_natural e f) x
  have hy := LinearMap.congr_fun (fiberBaseChangeLinearEquiv_natural e f) y
  rw [LinearMap.comp_apply] at hx hy
  exact (fiberBaseChangeLinearEquiv (P := P) e).injective
    (hf (hx.symm.trans (htransport.trans hy)))

/-- If the algebra map of a local `R`-algebra `S` onto a field `L` is surjective, injectivity
of `f ⊗ id_L` gives injectivity of `(S ⊗ f) ⊗ id_{κ(S)}`. -/
theorem injective_rTensor_baseChange_residue_of_surjective
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    {P Q : Type*} [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    {L : Type*} [Field L] [Algebra S L] [Algebra R L] [IsScalarTower R S L]
    (hS : Function.Surjective (algebraMap S L)) (f : P →ₗ[R] Q)
    (hf : Function.Injective (f.rTensor L)) :
    Function.Injective ((f.baseChange S).rTensor (S ⧸ IsLocalRing.maximalIdeal S)) := by
  have hker : RingHom.ker (Algebra.ofId S L) = IsLocalRing.maximalIdeal S :=
    IsLocalRing.ker_eq_maximalIdeal _ hS
  exact injective_rTensor_baseChange_of_algEquiv
    ((Ideal.quotientEquivAlgOfEq S hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S L) hS)) f hf

/-- The residue field of the local quotient `A_𝔭 ⧸ 𝔞` is `κ(𝔭)`, so injectivity of
`u ⊗ id_{κ(𝔭)}` is injectivity of the base change of `u` on the closed fibre. -/
private theorem baseChange_closedFibre_injective_of_localQuotient
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : Function.Injective (u.rTensor p.ResidueField)) :
    letI : Algebra X.A Y.A := hbc.algebraBase
    Function.Injective ((u.baseChange Y.A).rTensor (Y.A ⧸ IsLocalRing.maximalIdeal Y.A)) := by
  let : Algebra X.A Y.A := hbc.algebraBase
  have hIker : I ≤ RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) := by
    rwa [show RingHom.ker (algebraMap (Localization.AtPrime p) p.ResidueField) =
        IsLocalRing.maximalIdeal (Localization.AtPrime p) from IsLocalRing.ker_residue,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
  have hIker' : ∀ a : Localization.AtPrime p, a ∈ I →
      algebraMap (Localization.AtPrime p) p.ResidueField a = 0 := fun a ha =>
    RingHom.mem_ker.mp (hIker ha)
  let g₀ : Localization.AtPrime p ⧸ I →+* p.ResidueField :=
    Ideal.Quotient.lift I (algebraMap (Localization.AtPrime p) p.ResidueField) hIker'
  have hg₀ : Function.Surjective g₀ :=
    Ideal.Quotient.lift_surjective_of_surjective (I := I) hIker'
      (f := algebraMap (Localization.AtPrime p) p.ResidueField)
      (IsLocalRing.residue_surjective (R := Localization.AtPrime p))
  let : Algebra Y.A p.ResidueField := (g₀.comp hbc.baseEquiv.toRingHom).toAlgebra
  have hAlg : (algebraMap Y.A p.ResidueField).comp (algebraMap X.A Y.A) =
      algebraMap X.A p.ResidueField := by
    ext a
    change g₀ (hbc.baseEquiv (algebraMap X.A Y.A a)) = _
    rw [hbc.baseEquiv_algebraMap]
    exact Ideal.Quotient.lift_mk _ _ _
  have : IsScalarTower X.A Y.A p.ResidueField :=
    IsScalarTower.of_algebraMap_eq' hAlg.symm
  exact injective_rTensor_baseChange_residue_of_surjective
    (hg₀.comp hbc.baseEquiv.surjective) u hu

/-- Tensoring with a test module `P`, the lifted map on the local quotient is injective iff the
base change of `u` is. -/
private theorem rTensor_localQuotientMapULift_injective_iff
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    (u : X.N →ₗ[X.A] M) {P : Type*} [AddCommGroup P] [Module Y.A P] :
    letI : Algebra X.A Y.A := hbc.algebraBase
    Function.Injective ((localQuotientMapULift X p I Y hbc u).rTensor P) ↔
      Function.Injective ((u.baseChange Y.A).rTensor P) := by
  let : Algebra X.A Y.A := hbc.algebraBase
  let : Module X.A Y.A := hbc.algebraBase.toModule
  let : Module Y.A Y.N := Y.moduleBase
  let : Module X.A Y.N := Module.compHom Y.N (algebraMap X.A Y.A)
  have : IsScalarTower X.A Y.A Y.N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eN := isBaseChange_localQuotient_moduleMap X p I Y hbc
  let e : ULift.{max (max u₁ u₃) u₄} (Y.A ⊗[X.A] M) ≃ₗ[Y.A] (Y.A ⊗[X.A] M) :=
    ULift.moduleEquiv
  have hmap : (localQuotientMapULift X p I Y hbc u).rTensor P ∘ₗ
      (eN.equiv.toLinearMap.rTensor P) =
      (e.symm.toLinearMap.rTensor P) ∘ₗ (u.baseChange Y.A).rTensor P := by
    rw [← LinearMap.rTensor_comp, ← LinearMap.rTensor_comp]
    change ((e.symm.toLinearMap.comp
      ((u.baseChange Y.A).comp eN.equiv.symm.toLinearMap)).comp
      eN.equiv.toLinearMap).rTensor P = _
    simp [LinearMap.comp_assoc]
  have hN : Function.Bijective (eN.equiv.toLinearMap.rTensor P) :=
    (eN.equiv.rTensor P).bijective
  have hE : Function.Injective (e.symm.toLinearMap.rTensor P) := (e.symm.rTensor P).injective
  rw [← Function.Injective.of_comp_iff' _ hN, ← LinearMap.coe_comp, hmap, LinearMap.coe_comp,
    hE.of_comp_iff]

/-- **Injectivity on the closed fibre of the local quotient, from the one fibre `κ(𝔭)`.**
The residue field of the local quotient `A_𝔭 ⧸ 𝔞` is `κ(𝔭)`, so the single hypothesis
`u ⊗ id_{κ(𝔭)}` injective is exactly injectivity on the closed fibre. -/
private theorem localQuotient_map_ulift_closedFibre_injective
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : Function.Injective (u.rTensor p.ResidueField)) :
    Function.Injective ((localQuotientMapULift X p I Y hbc u).rTensor
      (Y.A ⧸ IsLocalRing.maximalIdeal Y.A)) := by
  exact (rTensor_localQuotientMapULift_injective_iff X p I Y hbc u).mpr
    (baseChange_closedFibre_injective_of_localQuotient X p I Y hbc hI u hu)

/-- **Stacks 0AT7 part (2) at the local quotient.** A pure spreadout and injectivity on the
single fibre `κ(𝔭)` give universal injectivity on the local quotient base change. -/
private theorem localQuotient_map_ulift_universallyInjective
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : Function.Injective (u.rTensor p.ResidueField))
    (hspread : Nonempty (PureSpreadout.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄), max (max u₁ u₃) u₄} Y)) :
    letI : Algebra X.A Y.A := hbc.algebraBase
    UniversallyInjective (localQuotientMapULift X p I Y hbc u) := by
  let : Algebra X.A Y.A := hbc.algebraBase
  let : Module X.A Y.A := hbc.algebraBase.toModule
  have : Module.Flat Y.A (ULift.{max (max u₁ u₃) u₄} (Y.A ⊗[X.A] M)) :=
    Module.Flat.of_linearEquiv ULift.moduleEquiv
  refine universallyInjective_of_injective_mod_maximalIdeal Y hspread
    (localQuotientMapULift X p I Y hbc u) fun m hm => ?_
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  exact (mapQ_injective_iff_rTensor_quotient
    (localQuotientMapULift X p I Y hbc u) (IsLocalRing.maximalIdeal Y.A)).mpr
    (localQuotient_map_ulift_closedFibre_injective X p I Y hbc hI u hu)

/-- Universal injectivity on the local quotient is inherited by every test module carrying
the action of the quotient base ring. -/
private theorem rTensor_injective_of_one_fibre
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : Function.Injective (u.rTensor p.ResidueField))
    (hspread : Nonempty (PureSpreadout.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄), max (max u₁ u₃) u₄} Y))
    {Q : Type (max (max u₁ u₃) u₄)} [AddCommGroup Q] [Module Y.A Q] :
    letI : Algebra X.A Y.A := hbc.algebraBase
    letI : Module X.A Q := Module.compHom Q (algebraMap X.A Y.A)
    letI : IsScalarTower X.A Y.A Q :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    Function.Injective (u.rTensor Q) := by
  let : Algebra X.A Y.A := hbc.algebraBase
  let : Module X.A Y.A := hbc.algebraBase.toModule
  let : Module X.A Q := Module.compHom Q (algebraMap X.A Y.A)
  have : IsScalarTower X.A Y.A Q :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hbase : UniversallyInjectivePoly.{u₁, max (max u₁ u₃) u₄}
      (u.baseChange Y.A) := fun P _ _ =>
    (rTensor_localQuotientMapULift_injective_iff X p I Y hbc u).mp
      (localQuotient_map_ulift_universallyInjective X p I Y hbc hI u hu hspread P)
  exact injective_rTensor_of_universallyInjective_baseChange u Y.A hbase Q

/-- A test module annihilated by the local quotient ideal carries the quotient ring action,
so the one-fibre criterion applies to it. -/
private theorem rTensor_injective_of_annihilated_one_fibre
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : Function.Injective (u.rTensor p.ResidueField))
    (hspread : Nonempty (PureSpreadout.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄), max (max u₁ u₃) u₄} Y))
    {Q : Type (max (max u₁ u₃) u₄)} [AddCommGroup Q]
    [Module (Localization.AtPrime p) Q]
    (hkill : ∀ a : Localization.AtPrime p, a ∈ I → ∀ x : Q, a • x = 0) :
    letI : Module X.A Q := Module.compHom Q
      (algebraMap X.A (Localization.AtPrime p))
    Function.Injective (u.rTensor Q) := by
  let Rp := Localization.AtPrime p
  let : Algebra X.A Y.A := hbc.algebraBase
  let qAct : Rp ⧸ I →+* Module.End Rp Q :=
    Ideal.Quotient.lift I (algebraMap Rp (Module.End Rp Q)) fun a ha =>
      LinearMap.ext (hkill a ha)
  let : Module Y.A Q := Module.compHom Q (qAct.comp hbc.baseEquiv.toRingHom)
  have hcompat (a : X.A) (x : Q) :
      (algebraMap X.A Y.A a) • x = (algebraMap X.A Rp a) • x := by
    change (qAct (hbc.baseEquiv (algebraMap X.A Y.A a))) x = _
    rw [hbc.baseEquiv_algebraMap]
    rfl
  let : Module X.A Q := Module.compHom Q (algebraMap X.A Y.A)
  have : IsScalarTower X.A Y.A Q :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hsame : (Module.compHom Q (algebraMap X.A Rp)) =
      (Module.compHom Q (algebraMap X.A Y.A) : Module X.A Q) :=
    Module.ext (funext₂ fun a x => (hcompat a x).symm)
  exact hsame ▸ rTensor_injective_of_one_fibre X p I Y hbc hI u hu hspread (Q := Q)

/-- **A good fibre propagates to any prime below it on which the local quotient ideal
vanishes.** -/
private theorem rTensor_residueField_injective_of_le_of_localQuotient
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    (p : Ideal X.A) [p.IsPrime]
    (I : Ideal (Localization.AtPrime p))
    (Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄)})
    (hbc : LocalQuotientBaseChange X Y p I)
    [IsLocalRing Y.A]
    (hI : I ≤ p.map (algebraMap X.A (Localization.AtPrime p)))
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : Function.Injective (u.rTensor p.ResidueField))
    (hspread : Nonempty (PureSpreadout.{u₁, max u₁ u₂,
      max u₁ u₃, max u₁ (max u₃ u₄), max (max u₁ u₃) u₄} Y))
    (q : Ideal X.A) [q.IsPrime] (hqp : q ≤ p)
    (hIq : I ≤ q.map (algebraMap X.A (Localization.AtPrime p))) :
    Function.Injective (u.rTensor q.ResidueField) := by
  let Rp := Localization.AtPrime p
  have hunits : ∀ y : p.primeCompl, IsUnit ((algebraMap X.A q.ResidueField) y) := fun y =>
    isUnit_iff_ne_zero.mpr fun hz => y.2 (hqp (Ideal.algebraMap_residueField_eq_zero.mp hz))
  let g : Rp →+* q.ResidueField := IsLocalization.lift (M := p.primeCompl) hunits
  have hg : g.comp (algebraMap X.A Rp) = algebraMap X.A q.ResidueField :=
    IsLocalization.lift_comp _
  let : Algebra Rp q.ResidueField := g.toAlgebra
  have hker : q.map (algebraMap X.A Rp) ≤ RingHom.ker g := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change g (algebraMap X.A Rp a) = 0
    rw [← RingHom.comp_apply, hg]
    exact Ideal.algebraMap_residueField_eq_zero.mpr ha
  have hkill : ∀ a : Rp, a ∈ I → ∀ x : q.ResidueField, a • x = 0 := by
    intro a ha x
    change g a * x = 0
    rw [RingHom.mem_ker.mp (hker (hIq ha)), zero_mul]
  have : IsScalarTower X.A Rp q.ResidueField := IsScalarTower.of_algebraMap_eq' hg.symm
  let Q := ULift.{max (max u₁ u₃) u₄} q.ResidueField
  have hkillQ : ∀ a : Rp, a ∈ I → ∀ x : Q, a • x = 0 := by
    intro a ha x
    apply ULift.down_injective
    simpa [Q] using hkill a ha x.down
  have hlocal := rTensor_injective_of_annihilated_one_fibre
    X p I Y hbc hI u hu hspread (Q := Q) hkillQ
  have hsame : (Module.compHom Q (algebraMap X.A Rp)) = (inferInstance : Module X.A Q) :=
    Module.ext (funext₂ fun a x => IsScalarTower.algebraMap_smul Rp a x)
  rw [hsame] at hlocal
  exact (injective_rTensor_congr_of_linearEquiv u
    (ULift.moduleEquiv : Q ≃ₗ[X.A] q.ResidueField)).mp hlocal

/-- **The spreading-out half of Claim 2 in the proof of Stacks 05U9.** In the standing
situation of Stacks 0AT6, let `M` be a flat `A`-module and `u : N → M` an `A`-linear map.
If `u ⊗ id_{κ(𝔭)}` is injective at a prime `𝔭`, there is a finitely generated ideal
`𝔞 ⊆ 𝔭 A_𝔭` such that `u ⊗ id_{κ(𝔮)}` is injective for every prime `𝔮 ⊆ 𝔭` of `A` with
`𝔞 ⊆ 𝔮 A_𝔭`.

The ideal is the one produced by Stacks 0AT8, over which the base-changed situation carries
a pure spreadout; Stacks 0AT7 part (2) converts the single good fibre into universal
injectivity there, and `κ(𝔮)` is a module over `A_𝔭 ⧸ 𝔞` exactly when `𝔞 ⊆ 𝔮 A_𝔭`. -/
theorem exists_fg_ideal_rTensor_residueField_injective_of_le
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    {M : Type u₄} [AddCommGroup M] [Module X.A M] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (p : Ideal X.A) [p.IsPrime]
    (hp : Function.Injective (u.rTensor p.ResidueField)) :
    ∃ a : Ideal (Localization.AtPrime p), a.FG ∧
      a ≤ p.map (algebraMap X.A (Localization.AtPrime p)) ∧
      ∀ (q : Ideal X.A) [q.IsPrime], q ≤ p →
        a ≤ q.map (algebraMap X.A (Localization.AtPrime p)) →
          Function.Injective (u.rTensor q.ResidueField) := by
  obtain ⟨I, hIfg, hI, Y, ⟨hbc⟩, hspread⟩ :=
    X.exists_fg_ideal_localQuotientBaseChange_pureSpreadout.{u₁, u₂, u₃, u₄,
      max (max u₁ u₃) u₄} p
  let Rp := Localization.AtPrime p
  have hImax : I ≤ IsLocalRing.maximalIdeal Rp := by
    rwa [← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp]
  have : Nontrivial (Rp ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal Rp).ne_top hImax)
  have : IsLocalRing (Rp ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsLocalRing Y.A := hbc.baseEquiv.symm.isLocalRing
  exact ⟨I, hIfg, hI,
    rTensor_residueField_injective_of_le_of_localQuotient X p I Y hbc hI u hp hspread⟩

end AlgebraicGeometry

end
