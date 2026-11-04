module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearEquiv
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthDeterminantFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order

/-!
# Two-periodic complexes on a coherent sheaf: determinants, divisors and components

This file collects the preliminaries for the rational equivalence between the two cohomology
cycles of a `(2, 1)`-periodic complex `(F, φ, ψ)` of a coherent `𝒪_X`-module, for `X` locally of
finite type over the base `(S, δ)` of chapter 42 of the Stacks Project.

* The periodic determinant `det_κ(M, φ, ψ)` of an exact finite-length periodic complex is
  invariant under linear isomorphisms, compatible with restriction of scalars along a local
  homomorphism with bijective residue-field map, and compatible with localization at a prime.
* The order of vanishing is compatible with ring isomorphisms and with closed immersions, through
  the identification of the residue field at the generic point of an integral closed subscheme
  with its function field.
* The pushforward of a principal divisor along a closed immersion has the expected coefficients,
  and the coefficient of a locally finite family of principal divisors is a sum over the members
  through the point.
* A pointwise bound on the relative dimension over the support of a coherent sheaf is equivalent to
  a bound on the delta-dimension of its support.
* Each irreducible component `W_j` of the support of `F` is the support of a reduced integral closed
  subscheme, whose generic point is that of `W_j` and whose delta-dimension is the relative
  dimension of that point; these closed subschemes form a locally finite family.

## References

* [Stacks Project, Tag 02MW](https://stacks.math.columbia.edu/tag/02MW)
* [Stacks Project, Tag 02PJ](https://stacks.math.columbia.edu/tag/02PJ)
* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.FlatShortExact TopologicalSpace

universe u

namespace Stacks.Chow

/-- Two exact finite-length periodic complexes over the same local ring related by a linear
isomorphism intertwining both differentials have the same periodic determinant. -/
private theorem periodicDeterminant_eq_of_linearEquiv
    {R : Type*} {M : Type*} {M' : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (φ' ψ' : M' →ₗ[R] M') (hφ'ψ' : Function.Exact φ' ψ')
    (hψ'φ' : Function.Exact ψ' φ') (e : M ≃ₗ[R] M')
    (hφ : e.toLinearMap.comp φ = φ'.comp e.toLinearMap)
    (hψ : e.toLinearMap.comp ψ = ψ'.comp e.toLinearMap)
    (hM : IsFiniteLength R M) (hM' : IsFiniteLength R M') :
    AlgebraicGeometry.periodicDeterminant φ ψ hφψ hψφ hM =
      AlgebraicGeometry.periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hM' := by
  let α := e.toLinearMap
  have hker : LinearMap.ker α = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
  have hrange : LinearMap.range α = ⊤ := LinearMap.range_eq_top.mpr e.surjective
  have hKφ : LinearMap.ker α ≤ LinearMap.ker φ := hker ▸ bot_le
  have hKψ : LinearMap.ker α ≤ LinearMap.ker ψ := hker ▸ bot_le
  have hQφ : LinearMap.range φ' ≤ LinearMap.range α := hrange ▸ le_top
  have hQψ : LinearMap.range ψ' ≤ LinearMap.range α := hrange ▸ le_top
  let : Subsingleton (LinearMap.ker α) := by
    rw [hker]
    infer_instance
  have hconn :
      (AlgebraicGeometry.connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
        hφ hψ hKφ hKψ hQφ hQψ).1.1 =
      (AlgebraicGeometry.connectingEquivs φ ψ φ' ψ' α hφψ hψφ hφ'ψ' hψ'φ'
        hφ hψ hKφ hKψ hQφ hQψ).1.2 :=
    LinearEquiv.ext fun _ => Subsingleton.elim _ _
  exact AlgebraicGeometry.periodicDeterminant_eq_of_connecting_eq
    φ ψ φ' ψ' α hM hM' hφψ hψφ hφ'ψ' hψ'φ' hφ hψ hKφ hKψ hQφ hQψ hconn

/-- Restriction of scalars along a local homomorphism with bijective residue-field map carries
the determinant map of an exact periodic complex to the determinant map of the restricted one. -/
private theorem periodicGamma_restrictScalars
    {R₀ R M : Type*} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R] [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
    (φ ψ : M →ₗ[R] M) (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M)
    (a : Module.FiniteLength.determinant R (LinearMap.range ψ))
    (b : Module.FiniteLength.determinant R (LinearMap.range φ)) :
    Module.FiniteLength.determinantRestrictScalarsEquiv hκ hM
        (AlgebraicGeometry.periodicGamma φ ψ hψφ hM
          (TensorProduct.tmul (IsLocalRing.ResidueField R) a b)) =
      AlgebraicGeometry.periodicGamma (φ.restrictScalars R₀) (ψ.restrictScalars R₀)
        hψφ (Module.FiniteLength.isFiniteLength_restrictScalars hκ hM)
        (TensorProduct.tmul (IsLocalRing.ResidueField R₀)
          (Module.FiniteLength.determinantRestrictScalarsEquiv hκ
            (hM.of_injective (LinearMap.range ψ).subtype_injective) a)
          (Module.FiniteLength.determinantRestrictScalarsEquiv hκ
            (hM.of_surjective (LinearMap.range_eq_top.mp
              (LinearMap.range_rangeRestrict φ))) b)) := by
  unfold AlgebraicGeometry.periodicGamma
  exact Module.FiniteLength.determinantRestrictScalarsEquiv_exact hκ _ _ _ _ _ _ _ _ a b

/-- The periodic determinant of a complex restricted along a local homomorphism with bijective
residue-field map maps to the periodic determinant of the complex itself. -/
private theorem periodicDeterminant_restrictScalars
    {R₀ R M : Type*} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R] [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
    (φ ψ : M →ₗ[R] M) (hφψ : Function.Exact φ ψ)
    (hψφ : Function.Exact ψ φ) (hM : IsFiniteLength R M) :
    Units.map (IsLocalRing.ResidueField.map (algebraMap R₀ R)).toMonoidHom
      (AlgebraicGeometry.periodicDeterminant (φ.restrictScalars R₀) (ψ.restrictScalars R₀)
        hφψ hψφ (Module.FiniteLength.isFiniteLength_restrictScalars hκ hM)) =
      AlgebraicGeometry.periodicDeterminant φ ψ hφψ hψφ hM := by
  let ρ := RingEquiv.ofBijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)) hκ
  let hM₀ := Module.FiniteLength.isFiniteLength_restrictScalars hκ hM
  let d₀ := AlgebraicGeometry.periodicDeterminant (φ.restrictScalars R₀)
    (ψ.restrictScalars R₀) hφψ hψφ hM₀
  have hlenφ := Module.FiniteLength.moduleLength_restrictScalars hκ
    (hM.of_injective (LinearMap.range φ).subtype_injective)
  have hlenψ := Module.FiniteLength.moduleLength_restrictScalars hκ
    (hM.of_injective (LinearMap.range ψ).subtype_injective)
  apply AlgebraicGeometry.eq_periodicDeterminant
  unfold AlgebraicGeometry.IsPeriodicDeterminant
  apply TensorProduct.ext'
  intro a b
  apply (Module.FiniteLength.determinantRestrictScalarsEquiv hκ hM).injective
  simp only [LinearMap.comp_apply, TensorProduct.comm_tmul, LinearEquiv.coe_coe,
    LinearMap.smul_apply, map_smulₛₗ]
  rw [periodicGamma_restrictScalars, periodicGamma_restrictScalars]
  have hd := LinearMap.congr_fun (AlgebraicGeometry.periodicDeterminant_spec
    (φ.restrictScalars R₀) (ψ.restrictScalars R₀) hφψ hψφ hM₀)
      (TensorProduct.tmul (IsLocalRing.ResidueField R₀)
        (Module.FiniteLength.determinantRestrictScalarsEquiv hκ
          (hM.of_injective (LinearMap.range ψ).subtype_injective) a)
        (Module.FiniteLength.determinantRestrictScalarsEquiv hκ
          (hM.of_injective (LinearMap.range φ).subtype_injective) b))
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply] at hd
  convert hd using 1
  · congr 1
  · congr 1
    change ρ.symm ((-1) ^ (Module.FiniteLength.moduleLength R (LinearMap.range φ) *
        Module.FiniteLength.moduleLength R (LinearMap.range ψ)) *
          ρ (d₀ : IsLocalRing.ResidueField R₀)) = _
    simp only [map_mul, map_pow, map_neg, map_one, RingEquiv.symm_apply_apply]
    rw [hlenφ, hlenψ]
    rfl

/-- A linear isomorphism onto the restriction of scalars of an exact periodic complex identifies
the two periodic determinants along the induced map of residue fields. -/
private theorem periodicDeterminant_eq_of_restrictScalars_equiv
    {R₀ R M N : Type*} [CommRing R₀] [IsLocalRing R₀]
    [CommRing R] [IsLocalRing R] [Algebra R₀ R] [IsLocalHom (algebraMap R₀ R)]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R₀ R)))
    [AddCommGroup M] [Module R₀ M]
    [AddCommGroup N] [Module R₀ N] [Module R N] [IsScalarTower R₀ R N]
    (φ ψ : M →ₗ[R₀] M) (φ' ψ' : N →ₗ[R] N)
    (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hφ'ψ' : Function.Exact φ' ψ') (hψ'φ' : Function.Exact ψ' φ') (e : M ≃ₗ[R₀] N)
    (hφ : e.toLinearMap.comp φ = (φ'.restrictScalars R₀).comp e.toLinearMap)
    (hψ : e.toLinearMap.comp ψ = (ψ'.restrictScalars R₀).comp e.toLinearMap)
    (hM : IsFiniteLength R₀ M) (hN : IsFiniteLength R N) :
    Units.map (IsLocalRing.ResidueField.map (algebraMap R₀ R)).toMonoidHom
      (AlgebraicGeometry.periodicDeterminant φ ψ hφψ hψφ hM) =
        AlgebraicGeometry.periodicDeterminant φ' ψ' hφ'ψ' hψ'φ' hN := by
  rw [periodicDeterminant_eq_of_linearEquiv φ ψ hφψ hψφ
    (φ'.restrictScalars R₀) (ψ'.restrictScalars R₀) hφ'ψ' hψ'φ' e hφ hψ hM
    (Module.FiniteLength.isFiniteLength_restrictScalars hκ hN)]
  exact periodicDeterminant_restrictScalars hκ φ' ψ' hφ'ψ' hψ'φ' hN

/-- The periodic determinant of the localization of a periodic complex at a prime agrees, under
the canonical identification of residue fields, with that of any localized model of it. -/
private theorem periodicDeterminant_localization
    {R A M N : Type*} [CommRing R] [CommRing A] [IsLocalRing A]
    (p : Ideal R) [p.IsPrime] [Algebra R A] [IsLocalization.AtPrime A p]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower R A N] (f : M →ₗ[R] N) [IsLocalizedModule p.primeCompl f]
    (φ ψ : M →ₗ[R] M) (φ' ψ' : N →ₗ[A] N)
    (hφ : ∀ m, f (φ m) = φ' (f m)) (hψ : ∀ m, f (ψ m) = ψ' (f m))
    (hex : Function.Exact (LocalizedModule.map p.primeCompl φ)
      (LocalizedModule.map p.primeCompl ψ))
    (hex' : Function.Exact (LocalizedModule.map p.primeCompl ψ)
      (LocalizedModule.map p.primeCompl φ))
    (hNex : Function.Exact φ' ψ') (hNex' : Function.Exact ψ' φ')
    (hfin : IsFiniteLength (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
    (hNfin : IsFiniteLength A N) :
    ∃ t : p.ResidueField ≃+* IsLocalRing.ResidueField A,
      (∀ r : R, t (algebraMap R p.ResidueField r) =
        IsLocalRing.residue A (algebraMap R A r)) ∧
      Units.map t.toMonoidHom
        (AlgebraicGeometry.periodicDeterminant (LocalizedModule.map p.primeCompl φ)
          (LocalizedModule.map p.primeCompl ψ) hex hex' hfin) =
        AlgebraicGeometry.periodicDeterminant φ' ψ' hNex hNex' hNfin := by
  let e := IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) A
  let : Algebra (Localization.AtPrime p) A := e.toRingHom.toAlgebra
  let : IsScalarTower R (Localization.AtPrime p) A :=
    IsScalarTower.of_algebraMap_eq' (by ext r; exact (e.commutes r).symm)
  let : Module (Localization.AtPrime p) N := Module.compHom N e.toRingHom
  let : IsScalarTower (Localization.AtPrime p) A N :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower R (Localization.AtPrime p) N :=
    IsScalarTower.of_algebraMap_smul (fun r n => by
      change e (algebraMap R (Localization.AtPrime p) r) • n = r • n
      rw [e.commutes, algebraMap_smul])
  let : IsLocalHom (algebraMap (Localization.AtPrime p) A) :=
    e.surjective.isLocalHom
  let t := IsLocalRing.ResidueField.mapEquiv e.toRingEquiv
  refine ⟨t, ?_, ?_⟩
  · intro r
    change t (IsLocalRing.residue (Localization.AtPrime p)
      (algebraMap R (Localization.AtPrime p) r)) = _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue A) (e.commutes r)
  · let E := (IsLocalizedModule.iso p.primeCompl f).extendScalarsOfIsLocalization
      p.primeCompl (Localization.AtPrime p)
    have hcomm (a : M →ₗ[R] M) (a' : N →ₗ[A] N)
        (ha : ∀ m, f (a m) = a' (f m)) :
        E.toLinearMap.comp (LocalizedModule.map p.primeCompl a) =
          (a'.restrictScalars (Localization.AtPrime p)).comp E.toLinearMap := by
      apply LinearMap.restrictScalars_injective R
      apply IsLocalizedModule.linearMap_ext p.primeCompl
        (LocalizedModule.mkLinearMap p.primeCompl M) f
      ext m
      change E (LocalizedModule.map p.primeCompl a (LocalizedModule.mk m 1)) =
        a' (E (LocalizedModule.mk m 1))
      simpa only [LocalizedModule.map_mk, E,
        LinearEquiv.extendScalarsOfIsLocalization_apply, IsLocalizedModule.iso_mk_one] using ha m
    have hκ : Function.Bijective
        (IsLocalRing.ResidueField.map (algebraMap (Localization.AtPrime p) A)) := t.bijective
    exact periodicDeterminant_eq_of_restrictScalars_equiv hκ
      (LocalizedModule.map p.primeCompl φ) (LocalizedModule.map p.primeCompl ψ)
      φ' ψ' hex hex' hNex hNex' E (hcomm φ φ' hφ) (hcomm ψ ψ' hψ) hfin hNfin

/-- The order of an element of a Noetherian domain is invariant under a ring isomorphism. -/
private lemma ringOrd_equiv {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  let E : Ideal S ≃o Ideal R := Ideal.relIsoOfBijective (e : R →+* S) e.bijective
  rw [Ring.ord, Ring.ord, Module.length_quotient, Module.length_quotient]
  have he : E (Ideal.span {e x}) = Ideal.span {x} := by
    ext a
    change e a ∈ Ideal.span {e x} ↔ a ∈ Ideal.span {x}
    rw [Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    refine ⟨fun ⟨b, hb⟩ => ⟨e.symm b, e.injective (by simpa using hb)⟩, ?_⟩
    rintro ⟨b, rfl⟩
    exact ⟨e b, map_mul e x b⟩
  have h := Order.coheight_orderIso E (Ideal.span {e x})
  rw [he] at h
  exact h.symm

/-- The order of vanishing on the fraction field of a one-dimensional Noetherian domain is
invariant under a ring isomorphism together with a compatible isomorphism of fraction fields. -/
private alias ringOrdFrac_equiv := ordFrac_eq_of_ringEquiv


/-- For a surjection onto a one-dimensional Noetherian domain with kernel a prime `p`, the order
of vanishing computed on `R ⧸ p` agrees with the one computed on the target, along the given
isomorphism from the residue field of `p` to the fraction field. -/
private theorem ordFrac_quotient_eq_of_residueField_equiv
    {R S K : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Field K] [Algebra S K] [IsFractionRing S K]
    (p : Ideal R) [p.IsPrime] [Ring.KrullDimLE 1 (R ⧸ p)]
    (f : R →+* S) (hf : Function.Surjective f)
    (e : p.ResidueField ≃+* K)
    (he : ∀ r : R, e (algebraMap R p.ResidueField r) = algebraMap S K (f r))
    (a : p.ResidueField) :
    Ring.ordFrac (R ⧸ p) a = Ring.ordFrac S (e a) := by
  have hker : RingHom.ker f = p := by
    ext r
    rw [RingHom.mem_ker, ← Ideal.algebraMap_residueField_eq_zero]
    rw [← (IsFractionRing.injective S K).eq_iff, map_zero, ← he]
    exact map_eq_zero_iff e e.injective
  let E : (R ⧸ p) ≃+* S :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hf)
  apply (ringOrdFrac_equiv E e ?_ a).symm
  intro r
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  simpa only [E, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk,
    Ideal.algebraMap_quotient_residueField_mk] using he r

/-- A closed immersion induces a bijection on residue fields at every point. -/
private theorem residueFieldMap_bijective_of_closedImmersion
    {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) :
    Function.Bijective (i.residueFieldMap y).hom := by
  refine ⟨RingHom.injective _, ?_⟩
  intro b
  obtain ⟨b', rfl⟩ := Y.residue_surjective y b
  obtain ⟨a, ha⟩ := i.stalkMap_surjective y b'
  refine ⟨X.residue (i y) a, ?_⟩
  have h := congrArg (fun q : X.presheaf.stalk (i y) ⟶ Y.residueField y => q.hom a)
    (Scheme.residue_residueFieldMap i y)
  change (i.residueFieldMap y).hom ((X.residue (i y)).hom a) =
    (Y.residue y).hom ((i.stalkMap y).hom a) at h
  simpa only [ha] using h

/-- A closed immersion has residue degree one at every point. -/
private theorem residueDegree_eq_one_of_closedImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (x : X) :
    i.residueDegree x = 1 := by
  let := (i.residueFieldMap x).hom.toAlgebra
  let e : Y.residueField (i x) ≃ₗ[Y.residueField (i x)] X.residueField x :=
    LinearEquiv.ofBijective (Algebra.linearMap (Y.residueField (i x)) (X.residueField x))
      (residueFieldMap_bijective_of_closedImmersion i x)
  change Module.finrank (Y.residueField (i x)) (X.residueField x) = 1
  rw [← e.finrank_eq, Module.finrank_self]

/-- On an integral scheme the residue at the generic point of the function-field value of a
rational function is its residue-field value. -/
private theorem residue_rationalFunctionsEquivFunctionField
    (Y : Scheme.{u}) [IsIntegral Y] (a : rationalFunctions Y) :
    Y.residue (genericPoint Y) ((rationalFunctionsEquivFunctionField Y).1 a) =
      (rationalFunctionsEquivResidueField Y).1 a := by
  obtain ⟨U, hηU, s, hs⟩ := Y.presheaf.exists_germ_eq
    ((rationalFunctionsEquivFunctionField Y).1 a)
  have hD : Dense (U : Set Y) := by
    rw [dense_iff_closure_eq]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure Y]
    exact closure_mono (Set.singleton_subset_iff.mpr hηU)
  let D : DenseOpen Y := ⟨U, hD⟩
  have heq : ofSection Y D s = a := by
    apply (rationalFunctionsEquivFunctionField Y).1.injective
    rw [(rationalFunctionsEquivFunctionField Y).2 D s hηU]
    exact hs
  rw [← heq, (rationalFunctionsEquivFunctionField Y).2 D s hηU,
    (rationalFunctionsEquivResidueField Y).2 D s hηU]
  rfl

/-- For a closed immersion of an integral scheme, the order of vanishing on the quotient of a
stalk by a prime agrees with the order of vanishing, in the local ring of the subscheme, of the
corresponding rational function. -/
private theorem ordFrac_eq_of_closedImmersion_residueField_equiv
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (i : Y ⟶ X) [IsClosedImmersion i] (y : Y)
    [Ring.KrullDimLE 1 (Y.presheaf.stalk y)]
    (p : PrimeSpectrum (X.presheaf.stalk (i y)))
    [Ring.KrullDimLE 1 ((X.presheaf.stalk (i y)) ⧸ p.asIdeal)]
    (t : p.asIdeal.ResidueField ≃+* X.residueField (i (genericPoint Y)))
    (ht : ∀ r : X.presheaf.stalk (i y),
      t (algebraMap (X.presheaf.stalk (i y)) p.asIdeal.ResidueField r) =
        X.residue (i (genericPoint Y))
          (X.presheaf.stalkSpecializes
            (((genericPoint_spec Y).specializes (Set.mem_univ y)).map i.continuous) r))
    (a : p.asIdeal.ResidueField) :
    Ring.ordFrac ((X.presheaf.stalk (i y)) ⧸ p.asIdeal) a =
      Ring.ordFrac (Y.presheaf.stalk y)
        ((rationalFunctionsEquivFunctionField Y).1
          ((rationalFunctionsEquivResidueField Y).1.symm
            (i.residueFieldMap (genericPoint Y) (t a)))) := by
  let e₁ := RingEquiv.ofBijective (i.residueFieldMap (genericPoint Y)).hom
    (residueFieldMap_bijective_of_closedImmersion i (genericPoint Y))
  let e := t.trans (e₁.trans
    ((rationalFunctionsEquivResidueField Y).1.symm.trans
      (rationalFunctionsEquivFunctionField Y).1))
  apply ordFrac_quotient_eq_of_residueField_equiv p.asIdeal
    (i.stalkMap y).hom (i.stalkMap_surjective y) e ?_ a
  intro r
  apply (Y.residue (genericPoint Y)).hom.injective
  have hr : Y.residue (genericPoint Y)
      ((rationalFunctionsEquivFunctionField Y).1
        ((rationalFunctionsEquivResidueField Y).1.symm
          (i.residueFieldMap (genericPoint Y) (t (algebraMap _ _ r))))) =
      i.residueFieldMap (genericPoint Y) (t (algebraMap _ _ r)) := by
    rw [residue_rationalFunctionsEquivFunctionField]
    exact (rationalFunctionsEquivResidueField Y).1.apply_symm_apply _
  change Y.residue (genericPoint Y)
    ((rationalFunctionsEquivFunctionField Y).1
      ((rationalFunctionsEquivResidueField Y).1.symm
        (i.residueFieldMap (genericPoint Y) (t (algebraMap _ _ r))))) = _
  rw [hr, ht]
  have hc := congrArg
    (fun q : X.presheaf.stalk (i (genericPoint Y)) ⟶ Y.residueField (genericPoint Y) =>
      q.hom (X.presheaf.stalkSpecializes
        (((genericPoint_spec Y).specializes (Set.mem_univ y)).map i.continuous) r))
    (Scheme.residue_residueFieldMap i (genericPoint Y))
  change i.residueFieldMap (genericPoint Y)
      (X.residue (i (genericPoint Y)) _) =
    Y.residue (genericPoint Y) (i.stalkMap (genericPoint Y) _) at hc
  rw [hc, i.stalkSpecializes_stalkMap_apply]
  rfl

/-- Proper pushforward along a closed immersion preserves coefficients: the coefficient of the
pushforward at the image of a point is the coefficient at that point. -/
private theorem properPushforward_closedImmersion_apply
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    (i : X ⟶ Y) [IsClosedImmersion i] (k : ℤ)
    (c : CycleGroup C (i ≫ f) k) (x : X) :
    (properPushforward C (i ≫ f) f i rfl k c).1 (i x) = c.1 x := by
  rw [properPushforward_apply]
  have hpre : i.base ⁻¹' {i x} = {x} := by
    ext z
    exact i.isClosedEmbedding.injective.eq_iff
  rw [hpre, finsum_mem_singleton]
  rw [ite_eq_left (relativeDimension_comp_closedImmersion C.dimensionFunction i f x),
    residueDegree_eq_one_of_closedImmersion, Nat.cast_one, mul_one]

/-- A locally finite sum over a subset agrees with the sum over the whole index type when every
term outside the subset vanishes. -/
private theorem finsum_subtype_eq_of_eq_zero_outside
    {J : Type*} (a : J → ℤ) (s : Set J) (h : ∀ j ∉ s, a j = 0) :
    (∑ᶠ j : s, a j) = ∑ᶠ j, a j := by
  rw [finsum_set_coe_eq_finsum_mem]
  calc
    _ = ∑ᶠ j ∈ (Set.univ : Set J), a j := by
      apply finsum_mem_inter_support_eq'
      intro j hj
      simp only [Set.mem_univ, iff_true]
      by_contra hjs
      exact hj (h j hjs)
    _ = ∑ᶠ j, a j := finsum_mem_univ a

/-- The pushforward of a principal divisor from a closed subscheme vanishes outside that
subscheme. -/
private theorem principalDivisorPushforward_apply_eq_zero_of_notMem_support
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (g : (rationalFunctions V.subscheme)ˣ) {x : X} (hx : x ∉ (V.support : Set X)) :
    principalDivisorPushforward C f V hV g x = 0 := by
  by_contra h
  exact hx (support_principalDivisorPushforward_subset C f V hV g h)

/-- At the image of a point of an integral closed subscheme of delta-dimension `k + 1`, the
pushforward of a principal divisor is the order of vanishing of the rational function there. -/
private theorem principalDivisorPushforward_apply_subschemeι
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hDim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) (z : V.subscheme) :
    letI := hV
    letI : IsLocallyNoetherian V.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
    principalDivisorPushforward C f V hV g (V.subschemeι z) =
      V.subscheme.ord
        ((rationalFunctionsEquivFunctionField V.subscheme).1
          (g : rationalFunctions V.subscheme)) z := by
  let := hV
  let : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  set v := (rationalFunctionsEquivFunctionField V.subscheme).1
    (g : rationalFunctions V.subscheme) with hv
  have hmem : principalCycle V.subscheme v ∈ cyclesOfDimension C (V.subschemeι ≫ f) k := by
    simpa only [add_sub_cancel_right] using
      principalCycle_mem_cyclesOfDimension C (V.subschemeι ≫ f) hDim v
  exact properPushforward_closedImmersion_apply C f V.subschemeι k
    ⟨principalCycle V.subscheme v, hmem⟩ z

/-- The coefficient at a point of a locally finite family of principal divisors is the sum, over
those members whose subscheme passes through the point, of the orders of vanishing there. -/
private theorem principalDivisorFamilyCoefficient_eq_finsum_on_support
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)
    {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : X)
    (y : ∀ j : {j : J // x ∈ (W j).support}, (W j.1).subscheme)
    (hy : ∀ j : {j : J // x ∈ (W j).support}, (W j.1).subschemeι (y j) = x) :
    principalDivisorFamilyCoefficient C f W hW g x =
      ∑ᶠ j : {j : J // x ∈ (W j).support},
        letI := hW j.1
        letI := LocallyOfFiniteType.isLocallyNoetherian ((W j.1).subschemeι ≫ f)
        (W j.1).subscheme.ord
          ((rationalFunctionsEquivFunctionField (W j.1).subscheme).1
            (g j.1 : rationalFunctions (W j.1).subscheme)) (y j) := by
  unfold principalDivisorFamilyCoefficient
  rw [← finsum_subtype_eq_of_eq_zero_outside _ {j : J | x ∈ (W j).support} (fun j hj ↦
    principalDivisorPushforward_apply_eq_zero_of_notMem_support C f (W j) (hW j) (g j) hj)]
  refine finsum_congr fun j ↦ ?_
  have h := principalDivisorPushforward_apply_subschemeι C f k (W j.1) (hW j.1) (hDim j.1)
    (g j.1) (y j)
  rw [hy j] at h
  exact h

/-- A pointwise bound on the relative dimension over the support of a coherent sheaf bounds the
delta-dimension of the support. -/
private theorem schemeDeltaDimension_reducedSupport_le_of_pointwise
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hpoint : ∀ (x : X), x ∈ SheafOfModules.supp F →
      relativeDimension C.dimensionFunction f x ≤ k) :
    schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt) := by
  let I : X.IdealSheafData := reducedSupport F
  let Y := I.subscheme
  let i : Y ⟶ X := I.subschemeι
  let g : Y ⟶ C.S := i ≫ f
  let : LocallyOfFiniteType g := inferInstance
  rw [schemeDeltaDimension_eq_iSup]
  apply iSup_le
  intro Z
  let Q : IrreducibleCloseds Y :=
    ⟨(Z : Set Y), Z.2.1,
      isClosed_of_mem_irreducibleComponents (Z : Set Y) Z.2⟩
  let ξ : Y := Z.2.1.genericPoint
  have hξ : IsGenericPoint ξ (Z : Set Y) := by
    simpa [ξ, isClosed_of_mem_irreducibleComponents (Z : Set Y) Z.2] using
      Z.2.1.isGenericPoint_genericPoint_closure
  have hdim := deltaDimension_eq_of_isGenericPoint C g Q ξ hξ
  have hsupport : i ξ ∈ SheafOfModules.supp F := by
    change i ξ ∈ (I.support : Set X)
    have hrange : i ξ ∈ Set.range I.subschemeι := ⟨ξ, rfl⟩
    exact I.range_subschemeι ▸ hrange
  change (deltaDimension C g Q : EInt) ≤ (k : EInt)
  rw [hdim, relativeDimension_comp_closedImmersion C.dimensionFunction i f ξ]
  exact WithBotTop.coe_le_coe.mpr (hpoint (i ξ) hsupport)

/-- Conversely, a bound on the delta-dimension of the support of a coherent sheaf bounds the
relative dimension at every point of the support. -/
theorem relativeDimension_le_of_support_dimension_le
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hFk : schemeDeltaDimension C
      ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt))
    (x : X) (hx : x ∈ SheafOfModules.supp F) :
    relativeDimension C.dimensionFunction f x ≤ k := by
  let I := reducedSupport F
  obtain ⟨y, rfl⟩ : x ∈ Set.range I.subschemeι := by
    rw [I.range_subschemeι]
    exact hx
  let g := I.subschemeι ≫ f
  let W : irreducibleComponents I.subscheme :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  let Q : IrreducibleCloseds I.subscheme :=
    ⟨W, W.2.1, isClosed_of_mem_irreducibleComponents (W : Set I.subscheme) W.2⟩
  let η : I.subscheme := W.2.1.genericPoint
  have hη : IsGenericPoint η (W : Set I.subscheme) :=
    W.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents (W : Set I.subscheme) W.2)
  have hspec : η ⤳ y := by
    rw [specializes_iff_mem_closure, hη.def]
    exact mem_irreducibleComponent
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction g
  have hle : d y ≤ d η := by
    by_cases h : η = y
    · rw [h]
    · exact (d.strictAnti_specializes hspec h).le
  have hbound : (deltaDimension C g Q : EInt) ≤ (k : EInt) := by
    apply le_trans _ hFk
    rw [schemeDeltaDimension_eq_iSup]
    exact le_iSup (fun Z : irreducibleComponents I.subscheme =>
      (deltaDimension C g
        ⟨Z, Z.2.1, isClosed_of_mem_irreducibleComponents (Z : Set I.subscheme) Z.2⟩ : EInt)) W
  rw [deltaDimension_eq_of_isGenericPoint C g Q η hη] at hbound
  rw [← relativeDimension_comp_closedImmersion C.dimensionFunction I.subschemeι f y,
    ← hd y]
  exact hle.trans (by rw [hd η]; exact WithBotTop.coe_le_coe.mp hbound)

/-- The image in `X` of an irreducible component of the support of a coherent sheaf is closed. -/
private noncomputable def supportComponentClosed {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X)) : Closeds X :=
  letI : F.IsFiniteType := isFiniteType_of_isCoherent F
  ⟨Subtype.val '' (Z : Set (SheafOfModules.supp F)),
    (SheafOfModules.isClosed_supp F).isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_of_mem_irreducibleComponents (Z : Set (SheafOfModules.supp F)) Z.2)⟩

/-- The reduced closed subscheme of `X` carried by an irreducible component of the support of a
coherent sheaf. -/
private noncomputable def supportComponentIdeal {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X)) : X.IdealSheafData :=
  letI : F.IsFiniteType := isFiniteType_of_isCoherent F
  Scheme.IdealSheafData.vanishingIdeal (supportComponentClosed F Z)

/-- Its underlying closed set is the component itself. -/
private theorem supportComponentIdeal_support {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X)) :
    (supportComponentIdeal F Z).support =
      (Subtype.val '' (Z : Set (SheafOfModules.supp F)) : Set X) := by
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  change ((supportComponentIdeal F Z).support : Set X) = (supportComponentClosed F Z : Set X)
  simp [supportComponentIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]

/-- A point lies on the closed subscheme of a component of the support iff it lies on the
component. -/
private theorem mem_supportComponentIdeal_support {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X)) (x : X) :
    x ∈ (supportComponentIdeal F Z).support ↔
      x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F)) := by
  change x ∈ ((supportComponentIdeal F Z).support : Set X) ↔ _
  rw [supportComponentIdeal_support]

/-- Any subfamily of the closed subschemes cut out by the components of the support is a locally
finite family of closed subsets of `X`. -/
private theorem supportComponentIdeal_locallyFinite {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (P : irreducibleComponents (SheafOfModules.supp F : Set X) → Prop) :
    LocallyFinite
      (fun j : {Z : irreducibleComponents (SheafOfModules.supp F : Set X) // P Z} =>
        ((supportComponentIdeal F j.1).support : Set X)) := by
  intro x
  obtain ⟨U, hU, hfin⟩ := locallyFinite_irreducibleComponents_supp F x
  refine ⟨U, hU, ?_⟩
  let A : Set (irreducibleComponents (SheafOfModules.supp F : Set X)) :=
    {Z | ((Subtype.val '' (Z : Set (SheafOfModules.supp F))) ∩ U).Nonempty}
  have hbasefin : A.Finite := by simpa [A] using hfin
  let idx := fun j : {Z : irreducibleComponents (SheafOfModules.supp F : Set X) // P Z} => j.1
  have hpre : (idx ⁻¹' A).Finite := by
    apply Set.Finite.preimage (f := idx) (s := A) _ hbasefin
    intro a ha b hb hab
    exact Subtype.ext hab
  apply hpre.subset
  intro j hj
  change ((Subtype.val '' (j.1 : Set (SheafOfModules.supp F))) ∩ U).Nonempty at hj
  simpa [A, idx] using hj

/-- The closed subscheme attached to a component of the support is integral. -/
private theorem supportComponentIdeal_integral {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X)) :
    IsIntegral (supportComponentIdeal F Z).subscheme := by
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let T := supportComponentClosed F Z
  let I := supportComponentIdeal F Z
  have hsupport : (I.support : Set X) = (T : Set X) := supportComponentIdeal_support F Z
  have hirr : IsIrreducible (T : Set X) :=
    Z.2.1.image _ continuous_subtype_val.continuousOn
  have : IsReduced I.subscheme :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal T
  have : IrreducibleSpace I.subscheme :=
    Scheme.IdealSheafData.irreducibleSpace_subscheme X I (by
      rw [I.range_subschemeι, hsupport]
      exact hirr)
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced I.subscheme
  change IsIntegral I.subscheme
  exact inferInstance

/-- Its generic point is carried to the generic point of the component. -/
private theorem supportComponentIdeal_genericPoint {X : Scheme.{u}}
    [IsLocallyNoetherian X] (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    [IsIntegral (supportComponentIdeal F Z).subscheme] :
    (supportComponentIdeal F Z).subschemeι
      (genericPoint (supportComponentIdeal F Z).subscheme) =
        (Z.2.1.genericPoint).1 := by
  let I := supportComponentIdeal F Z
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : IsIntegral I.subscheme := supportComponentIdeal_integral F Z
  let Zset : Set (SheafOfModules.supp F) := Z
  have hsupport := supportComponentIdeal_support F Z
  have htop : Topology.IsClosedEmbedding (Subtype.val : SheafOfModules.supp F → X) :=
    (SheafOfModules.isClosed_supp F).isClosedEmbedding_subtypeVal
  have hη : IsGenericPoint ((Z.2.1.genericPoint).1) (I.support : Set X) := by
    have hZgen : IsGenericPoint Z.2.1.genericPoint Zset :=
      Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Zset Z.2)
    change closure ({(Z.2.1.genericPoint).1} : Set X) = (I.support : Set X)
    rw [hsupport, ← Set.image_singleton, htop.closure_image_eq, hZgen.def]
  have hI : IsGenericPoint (I.subschemeι (genericPoint I.subscheme))
      (I.support : Set X) := by
    change closure ({I.subschemeι (genericPoint I.subscheme)} : Set X) =
      (I.support : Set X)
    rw [← I.range_subschemeι, ← Set.image_singleton,
      I.subschemeι.isClosedEmbedding.closure_image_eq, genericPoint_closure,
      Set.image_univ]
  exact hI.eq hη

/-- Its delta-dimension is the relative dimension of the generic point of the component. -/
private theorem supportComponentIdeal_schemeDeltaDimension
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (k : ℤ)
    (hδ : relativeDimension C.dimensionFunction f
      (Z.2.1.genericPoint).1 = k) :
    schemeDeltaDimension C
      ((supportComponentIdeal F Z).subschemeι ≫ f) = (k : EInt) := by
  let I := supportComponentIdeal F Z
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : IsLocallyNoetherian X := by
    let : IsLocallyNoetherian C.S := C.isLocallyNoetherian
    exact LocallyOfFiniteType.isLocallyNoetherian f
  let : IsIntegral I.subscheme := supportComponentIdeal_integral F Z
  let i : I.subscheme ⟶ X := I.subschemeι
  let : LocallyOfFiniteType (i ≫ f) := inferInstance
  rw [schemeDeltaDimension_eq_genericPoint C (i ≫ f)]
  rw [relativeDimension_comp_closedImmersion C.dimensionFunction i f
    (genericPoint I.subscheme)]
  rw [supportComponentIdeal_genericPoint F Z]
  exact congrArg (fun n : ℤ => (n : EInt)) hδ

end Stacks.Chow
