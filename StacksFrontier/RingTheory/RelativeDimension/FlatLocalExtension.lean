module

public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.RelativeDimension.ValuationRing
public import StacksFrontier.RingTheory.RelativeDimension.BaseChange
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Spectrum.Prime.LocalDimension
public import Mathlib.RingTheory.Valuation.LocalSubring
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Equality of dimensions for a flat local extension of domains

For an injective, flat, essentially finite type local homomorphism of local domains, the
dimension of the closed fibre plus the transcendence degree of the residue-field extension
equals the transcendence degree of the extension of domains.

## Main results

* `IsLocalRing.ringKrullDim_closedFiber_add_trdeg_eq_trdeg` gives the dimension equality.

## Implementation notes

The closed fibre is the quotient of `B` by the extension of the maximal ideal of `A`.
Transcendence degree over domains is written `Algebra.trdeg A B`; this agrees with the
transcendence degree of the corresponding fraction fields. Cardinal-valued transcendence
degrees are sent to `WithBot ℕ∞` by `Cardinal.toENat`.

## References

* [Stacks Project, Tag 053T](https://stacks.math.columbia.edu/tag/053T)
-/

@[expose] public section

namespace IsLocalRing

universe u

open scoped TensorProduct

/-! ### Domains after valuation base change -/

/-- If `V` is an overring of `A` inside its fraction field and `B` is a flat domain over `A`,
then `V ⊗[A] B` is a domain.  The tensor product embeds into the localization of `B` obtained
by inverting the nonzero elements of `A`; that localization is a domain. -/
private theorem tensorProduct_isDomain_of_flat
    {A B V : Type u} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Module.Flat A B]
    [CommRing V] [Algebra A V] [Algebra V (FractionRing A)]
    [IsScalarTower A V (FractionRing A)]
    (hVK : Function.Injective (algebraMap V (FractionRing A))) :
    IsDomain (V ⊗[A] B) := by
  let : Algebra V (V ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
  let : Algebra (FractionRing A) (FractionRing A ⊗[A] B) :=
    Algebra.TensorProduct.leftAlgebra
  let f : V →ₐ[A] FractionRing A := IsScalarTower.toAlgHom A V (FractionRing A)
  let g : B →ₐ[A] B := AlgHom.id A B
  let : Module.Flat A (FractionRing A) :=
    IsLocalization.flat (FractionRing A) (nonZeroDivisors A)
  have hinj : Function.Injective (Algebra.TensorProduct.map f g) := by
    exact TensorProduct.map_injective_of_flat_flat f.toLinearMap g.toLinearMap
      (fun x y h => hVK (by
        change algebraMap V (FractionRing A) x = algebraMap V (FractionRing A) y at h
        exact h))
      (fun _ _ h => h)
  let M := Algebra.algebraMapSubmonoid B (nonZeroDivisors A)
  have hM : M ≤ nonZeroDivisors B := by
    apply Submonoid.map_le_iff_le_comap.mpr
    exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective A B)
  have : IsDomain (Localization M) := IsLocalization.isDomain_localization hM
  have : IsDomain (FractionRing A ⊗[A] B) :=
    (Localization.tensorRightAlgEquiv (nonZeroDivisors A) B).toRingEquiv.injective.isDomain _
  exact hinj.isDomain _

/-! ### Bridges from the Stacks presentation to the algebra APIs -/

/-- The existential Stacks presentation of an essentially finite type map gives Mathlib's
`Algebra.EssFiniteType` instance. -/
public theorem essFiniteType_of_isEssentiallyOfFiniteType
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (h : IsEssentiallyOfFiniteType R S (algebraMap R S)) : Algebra.EssFiniteType R S := by
  rcases h with ⟨T, _, _, hFT, M, _, hTower, hLoc⟩
  let := hFT
  let := hLoc
  have : IsScalarTower R T S := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    have h' := @IsScalarTower.algebraMap_apply R T S _ _ _ _ _
      (RingHom.toAlgebra (algebraMap R S)) hTower r
    rwa [RingHom.algebraMap_toAlgebra] at h'
  have : Algebra.EssFiniteType R T := Algebra.EssFiniteType.of_finiteType R T
  have : Algebra.EssFiniteType T S := Algebra.EssFiniteType.of_isLocalization S M
  exact Algebra.EssFiniteType.comp R T S

/-- Transcendence degree over `R` is unchanged by an algebraic extension `S → A` on top. -/
private theorem trdeg_eq_of_isAlgebraic_right
    {R S A : Type u} [CommRing R] [Nontrivial R] [CommRing S] [CommRing A] [NoZeroDivisors A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [FaithfulSMul R S]
    [FaithfulSMul S A] [Algebra.IsAlgebraic S A] :
    Algebra.trdeg R S = Algebra.trdeg R A := by
  simpa only [trdeg_eq_zero (R := S) (A := A), add_zero] using trdeg_add_eq R S (A := A)

/-- Transcendence degree over `S` is unchanged by an algebraic extension `R → S` at the bottom. -/
private theorem trdeg_eq_of_isAlgebraic_left
    {R S A : Type u} [CommRing R] [Nontrivial R] [CommRing S] [CommRing A] [NoZeroDivisors A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [FaithfulSMul R S]
    [FaithfulSMul S A] [Algebra.IsAlgebraic R S] :
    Algebra.trdeg S A = Algebra.trdeg R A := by
  simpa only [trdeg_eq_zero (R := R) (A := S), zero_add] using trdeg_add_eq R S (A := A)

/-- Local dimension can be computed using any localization at the point. -/
public theorem localKrullDim_eq_ringKrullDim_add_trdeg
    (k C B : Type u) [Field k] [CommRing C] [CommRing B] [IsLocalRing B]
    [Algebra k C] [Algebra.FiniteType k C] [Algebra C B] [Algebra k B]
    [IsScalarTower k C B] (q : Ideal C) [q.IsPrime] [IsLocalization.AtPrime B q] :
    TopologicalSpace.localKrullDim (PrimeSpectrum C) ⟨q, ‹_›⟩ =
      ringKrullDim B +
        (Cardinal.toENat (Algebra.trdeg k (IsLocalRing.ResidueField B)) : WithBot ℕ∞) := by
  let e := (IsLocalization.algEquiv q.primeCompl B (Localization.AtPrime q)).restrictScalars k
  rw [PrimeSpectrum.localKrullDim_eq_height_add_trdeg_residueField k,
    IsLocalization.AtPrime.ringKrullDim_eq_height q B,
    (IsLocalRing.ResidueField.mapAlgEquiv e).trdeg_eq, WithBot.coe_add]

/-- A local localization is the localization at the inverse image of its maximal ideal. -/
private theorem isLocalization_at_comap_maximalIdeal
    (R S : Type u) [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] :
    IsLocalization.AtPrime S ((IsLocalRing.maximalIdeal S).under R) := by
  apply IsLocalization.of_le M
  · intro r hr
    exact IsLocalRing.notMem_maximalIdeal.mpr (IsLocalization.map_units S ⟨r, hr⟩)
  · intro r hr
    exact IsLocalRing.notMem_maximalIdeal.mp hr

/-- The dimension of the generic fibre of a finite type extension of domains is its
transcendence degree. -/
private theorem ringKrullDim_genericFiber_eq_trdeg
    (R S : Type u) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S] :
    ringKrullDim ((⊥ : Ideal R).Fiber S) =
      (Cardinal.toENat (Algebra.trdeg R S) : WithBot ℕ∞) := by
  let K := (⊥ : Ideal R).ResidueField
  let F := (⊥ : Ideal R).Fiber S
  let : Algebra S F := Algebra.TensorProduct.rightAlgebra
  have hle : Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S := by
    rintro x ⟨r, hr, rfl⟩
    exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (FaithfulSMul.algebraMap_injective R S) hr
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) F :=
    IsLocalization.tensorRight K (nonZeroDivisors R)
  have : IsDomain F := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have : FaithfulSMul S F := (faithfulSMul_iff_algebraMap_injective S F).mpr
    (IsLocalization.injective F hle)
  have : Algebra.IsAlgebraic S F := IsLocalization.isAlgebraic F
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))
  have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
  have : FaithfulSMul K F := (faithfulSMul_iff_algebraMap_injective K F).mpr
    (algebraMap K F).injective
  have : Algebra.IsAlgebraic F (FractionRing F) :=
    IsLocalization.isAlgebraic (FractionRing F) (nonZeroDivisors F)
  rw [trdeg_eq_of_isAlgebraic_right (S := S) (A := F),
    ← trdeg_eq_of_isAlgebraic_left (R := R) (S := K) (A := F),
    trdeg_eq_of_isAlgebraic_right (R := K) (S := F) (A := FractionRing F)]
  exact (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, u, u, 0}
    K F (FractionRing F)).1

/-- Equidimensionality of the special fibre makes its local dimension equal to the
dimension of the generic fibre. -/
@[sga "6 X 7.14" "special case"]
private theorem localKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot
    {R S : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S]
    (hfib : Nontrivial ((IsLocalRing.maximalIdeal R).Fiber S))
    (x : PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) :
    TopologicalSpace.localKrullDim (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) x =
      ringKrullDim ((⊥ : Ideal R).Fiber S) := by
  have hdim :=
    ValuationRing.ringKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot_and_equidimensional
      hfib
  have hlocal (y : PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) :
      TopologicalSpace.localKrullDim (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) y =
        topologicalKrullDim (irreducibleComponent x) := by
    rw [(PrimeSpectrum.localKrullDim_eq_iSup_irreducibleComponents_and_eq_iInf_height
      (IsLocalRing.maximalIdeal R).ResidueField y).1]
    refine le_antisymm (iSup₂_le fun Z hZ => ?_) ?_
    · exact (hdim.2 Z hZ.1 _ (irreducibleComponent_mem_irreducibleComponents x)).le
    · exact le_iSup₂_of_le (irreducibleComponent y)
        ⟨irreducibleComponent_mem_irreducibleComponents y, mem_irreducibleComponent⟩
        (hdim.2 _ (irreducibleComponent_mem_irreducibleComponents y)
          _ (irreducibleComponent_mem_irreducibleComponents x)).ge
  have hglobal : topologicalKrullDim (PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S)) =
      topologicalKrullDim (irreducibleComponent x) := by
    rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    exact le_antisymm (iSup_le fun y => (hlocal y).le) (le_iSup_of_le x (hlocal x).ge)
  exact (hlocal x).trans (hglobal.symm.trans
    ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).trans hdim.1))

/-- For a finite type domain over a valuation ring, the relative dimension at a point of the
special fibre is the dimension of the generic fibre. -/
private theorem relativeDimensionAt_eq_genericFiber_dim
    {R S : Type*} [CommRing R] [IsDomain R] [ValuationRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [FaithfulSMul R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] (hq : q.under R = IsLocalRing.maximalIdeal R) :
    Algebra.relativeDimensionAt R q = ringKrullDim ((⊥ : Ideal R).Fiber S) := by
  obtain ⟨Q, hQ, hQc⟩ := Ideal.Fiber.exists_comap_includeRight_eq q
    (IsLocalRing.maximalIdeal R) hq
  let z : PrimeSpectrum ((IsLocalRing.maximalIdeal R).Fiber S) := ⟨Q, hQ⟩
  rw [Algebra.relativeDimensionAt_eq_localKrullDim q (IsLocalRing.maximalIdeal R) hq Q hQc]
  have h01 : (0 : (IsLocalRing.maximalIdeal R).Fiber S) ≠ 1 := by
    intro h
    apply hQ.ne_top
    apply (Ideal.eq_top_iff_one Q).mpr
    rw [← h]
    exact Q.zero_mem
  let : Nontrivial ((IsLocalRing.maximalIdeal R).Fiber S) := ⟨⟨0, 1, h01⟩⟩
  exact localKrullDim_fiber_maximalIdeal_eq_ringKrullDim_fiber_bot
    (R := R) (S := S) ‹Nontrivial ((IsLocalRing.maximalIdeal R).Fiber S)› z

theorem relativeDimensionAt_eq_localKrullDim_of_field
    (k : Type*) {S : Type*} [Field k] [CommRing S] [Algebra k S]
    (q : Ideal S) [q.IsPrime] :
    Algebra.relativeDimensionAt k q =
      TopologicalSpace.localKrullDim (PrimeSpectrum S) ⟨q, ‹_›⟩ := by
  have hset : PrimeSpectrum.comap (algebraMap k S) ⁻¹'
      {PrimeSpectrum.comap (algebraMap k S) (⟨q, ‹_›⟩ : PrimeSpectrum S)} = Set.univ :=
    Set.eq_univ_iff_forall.mpr fun _ ↦ Subsingleton.elim _ _
  rw [Algebra.relativeDimensionAt, ← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  exact topologicalKrullDimAt_eq_of_homeomorph
    ((Homeomorph.setCongr hset).trans (Homeomorph.Set.univ (PrimeSpectrum S))) _

/-- A local finite-type model computes the dimension and residual transcendence degree of
its closed fibre. -/
private theorem relativeDimensionAt_eq_closedFiber
    (R C B : Type u) [CommRing R] [IsLocalRing R] [CommRing C] [CommRing B]
    [IsLocalRing B] [Algebra R C] [Algebra R B] [Algebra C B]
    [IsScalarTower R C B] [IsLocalHom (algebraMap R B)] [Algebra.FiniteType R C]
    (M : Submonoid C) [IsLocalization M B] :
    Algebra.relativeDimensionAt R ((IsLocalRing.maximalIdeal B).under C) =
      ringKrullDim (IsLocalRing.ResidueField R ⊗[R] B) +
        (Cardinal.toENat (Algebra.trdeg (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField (IsLocalRing.ResidueField R ⊗[R] B))) : WithBot ℕ∞) := by
  let k := IsLocalRing.ResidueField R
  let F := k ⊗[R] C
  let H := k ⊗[R] B
  let : Algebra C F := Algebra.TensorProduct.rightAlgebra
  let : Algebra B H := Algebra.TensorProduct.rightAlgebra
  let f : F →ₐ[k] H := Algebra.TensorProduct.map (AlgHom.id k k)
    (IsScalarTower.toAlgHom R C B)
  let : Algebra F H := f.toRingHom.toAlgebra
  have : IsScalarTower k F H := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hmap : (algebraMap F H).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom.comp (algebraMap C B) := by
    ext x
    change f (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] algebraMap C B x
    rfl
  have : IsLocalization (M.map (algebraMap C F)) H :=
    IsLocalization.tensorProduct_tensorProduct_right R k M B hmap
  have : IsLocalHom (algebraMap B H) := IsLocalHom.of_surjective _
    (TensorProduct.mk_surjective R B k IsLocalRing.residue_surjective)
  change (algebraMap F H).comp (algebraMap C F) =
    (algebraMap B H).comp (algebraMap C B) at hmap
  let Q := (IsLocalRing.maximalIdeal H).under F
  have hQ : Q.under C = (IsLocalRing.maximalIdeal B).under C := by
    change Ideal.comap _ (Ideal.comap _ _) = _
    rw [Ideal.comap_comap, hmap, ← Ideal.comap_comap]
    rw [← Ideal.under_def, Ideal.over_def (IsLocalRing.maximalIdeal H)
      (IsLocalRing.maximalIdeal B)]
  have : IsLocalization.AtPrime H Q :=
    isLocalization_at_comap_maximalIdeal F H (M.map (algebraMap C F))
  rw [← Algebra.relativeDimensionAt_congr (R := R) hQ]
  have hbase := Algebra.IsPushout.relativeDimensionAt_comap_eq R C k F ⟨Q, inferInstance⟩
  change Algebra.relativeDimensionAt R (Q.under C) = Algebra.relativeDimensionAt k Q at hbase
  rw [hbase, relativeDimensionAt_eq_localKrullDim_of_field k]
  exact localKrullDim_eq_ringKrullDim_add_trdeg k F H Q

/-- The valuation-ring dimension formula in terms of the tensor-product closed fibre. -/
private theorem closedFiber_eq_trdeg_of_valuationRing
    (R B : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra R B] [FaithfulSMul R B]
    [IsLocalHom (algebraMap R B)] [Algebra.EssFiniteType R B] :
    ringKrullDim (IsLocalRing.ResidueField R ⊗[R] B) +
        (Cardinal.toENat (Algebra.trdeg (IsLocalRing.ResidueField R)
          (IsLocalRing.ResidueField (IsLocalRing.ResidueField R ⊗[R] B))) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg R B) : WithBot ℕ∞) := by
  let C := Algebra.EssFiniteType.subalgebra R B
  let M := Algebra.EssFiniteType.submonoid R B
  have : IsLocalization M B := Algebra.EssFiniteType.isLocalization R B
  have : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr
    (fun x y h => FaithfulSMul.algebraMap_injective R B
      (congrArg (algebraMap C B) h))
  have hq : ((IsLocalRing.maximalIdeal B).under C).under R = IsLocalRing.maximalIdeal R := by
    rw [Ideal.under_under, Ideal.over_def (IsLocalRing.maximalIdeal B)
      (IsLocalRing.maximalIdeal R)]
  rw [← relativeDimensionAt_eq_closedFiber R C B M,
    relativeDimensionAt_eq_genericFiber_dim _ hq, ringKrullDim_genericFiber_eq_trdeg R C]
  have : Algebra.IsAlgebraic C B := IsLocalization.isAlgebraic B M
  rw [trdeg_eq_of_isAlgebraic_right (R := R) (S := C) (A := B)]

/-- The tensor-product description of the closed fibre gives the usual quotient and
preserves the residue field, including its algebra structure over the base residue field. -/
private theorem closedFiber_dimension_eq
    (R B : Type u) [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)] :
    letI := (IsLocalRing.ResidueField.map (algebraMap R B)).toAlgebra
    ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B)) +
      (Cardinal.toENat (Algebra.trdeg (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField B)) : WithBot ℕ∞) =
    ringKrullDim (IsLocalRing.ResidueField R ⊗[R] B) +
      (Cardinal.toENat (Algebra.trdeg (IsLocalRing.ResidueField R)
        (IsLocalRing.ResidueField (IsLocalRing.ResidueField R ⊗[R] B))) : WithBot ℕ∞) := by
  let := (IsLocalRing.ResidueField.map (algebraMap R B)).toAlgebra
  let k := IsLocalRing.ResidueField R
  let H := k ⊗[R] B
  let : Algebra B H := Algebra.TensorProduct.rightAlgebra
  have hsurj : Function.Surjective (algebraMap B H) :=
    TensorProduct.mk_surjective R B k IsLocalRing.residue_surjective
  have : IsLocalHom (algebraMap B H) := IsLocalHom.of_surjective _ hsurj
  let f : IsLocalRing.ResidueField B →ₐ[k] IsLocalRing.ResidueField H :=
    { IsLocalRing.ResidueField.map (algebraMap B H) with
      commutes' := by
        intro x
        obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
        change IsLocalRing.ResidueField.map (algebraMap B H)
          (IsLocalRing.residue B (algebraMap R B r)) = _
        rw [IsLocalRing.ResidueField.map_residue]
        change algebraMap H (IsLocalRing.ResidueField H)
          (algebraMap B H (algebraMap R B r)) = _
        rw [← IsScalarTower.algebraMap_apply R B H,
          IsScalarTower.algebraMap_apply R k H, ← IsScalarTower.algebraMap_apply]
        rfl }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨h, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨b, rfl⟩ := hsurj h
    exact ⟨IsLocalRing.residue B b, IsLocalRing.ResidueField.map_residue _ _⟩
  let e := AlgEquiv.ofBijective f ⟨f.injective, hf⟩
  let eH : H ≃+* B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B) :=
    (Algebra.TensorProduct.comm _ _ _).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
        (IsLocalRing.maximalIdeal R)).symm.toRingEquiv
  rw [e.trdeg_eq, eH.ringKrullDim]

/-- The closed points of two local algebras lift to a prime of their tensor product. -/
private theorem exists_tensorProduct_prime_over_maximalIdeals
    (R V B : Type u) [CommRing R] [CommRing V] [CommRing B]
    [IsLocalRing R] [IsLocalRing V] [IsLocalRing B] [Algebra R V] [Algebra R B]
    [IsLocalHom (algebraMap R V)] [IsLocalHom (algebraMap R B)] :
    ∃ q : Ideal (V ⊗[R] B), q.IsPrime ∧
      q.comap (algebraMap V (V ⊗[R] B)) = IsLocalRing.maximalIdeal V ∧
      q.comap (Algebra.TensorProduct.includeRight (R := R) (A := V)).toRingHom =
        IsLocalRing.maximalIdeal B := by
  let k := IsLocalRing.ResidueField R
  let kV := IsLocalRing.ResidueField V
  let kB := IsLocalRing.ResidueField B
  let T := kV ⊗[k] kB
  let : Algebra kB T := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R k T := inferInstance
  have : IsScalarTower R kV T := inferInstance
  have : IsScalarTower R kB T := IsScalarTower.of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R k T, IsScalarTower.algebraMap_apply R k kB,
      IsScalarTower.algebraMap_apply k kB T]
  let gV := (IsScalarTower.toAlgHom R kV T).comp (IsScalarTower.toAlgHom R V kV)
  let gB := (IsScalarTower.toAlgHom R kB T).comp (IsScalarTower.toAlgHom R B kB)
  let f : V ⊗[R] B →ₐ[R] T := Algebra.TensorProduct.lift gV gB (fun _ _ => Commute.all _ _)
  let Q : Ideal T := (Classical.arbitrary (PrimeSpectrum T)).asIdeal
  have : Q.IsPrime := (Classical.arbitrary (PrimeSpectrum T)).isPrime
  refine ⟨Q.comap f.toRingHom, inferInstance, ?_, ?_⟩
  · have hg : f.toRingHom.comp (algebraMap V (V ⊗[R] B)) =
        (algebraMap kV T).comp (IsLocalRing.residue V) := by
      ext x
      change f (x ⊗ₜ[R] 1) = _
      simp [f, gV, gB, Algebra.TensorProduct.lift_tmul]
      rfl
    rw [Ideal.comap_comap, hg, ← Ideal.comap_comap,
      Ideal.eq_bot_of_prime (Q.comap (algebraMap kV T))]
    exact IsLocalRing.ker_residue
  · have hg : f.toRingHom.comp (Algebra.TensorProduct.includeRight (R := R) (A := V)).toRingHom =
        (algebraMap kB T).comp (IsLocalRing.residue B) := by
      ext x
      change f (1 ⊗ₜ[R] x) = _
      simp [f, gV, gB, Algebra.TensorProduct.lift_tmul]
      rfl
    rw [Ideal.comap_comap, hg, ← Ideal.comap_comap,
      Ideal.eq_bot_of_prime (Q.comap (algebraMap kB T))]
    exact IsLocalRing.ker_residue

/-- The dimension of the closed fibre of an injective flat essentially finite type local
extension of domains, plus the residue-field transcendence degree, is the transcendence
degree of the extension. -/
@[stacks 053T, ega "IV 5.5.7" "field base"]
public theorem ringKrullDim_closedFiber_add_trdeg_eq_trdeg
    {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (hfinite : IsEssentiallyOfFiniteType A B (algebraMap A B))
    [Module.Flat A B] :
    letI := (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra
    ringKrullDim (B ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A B)) +
      (Cardinal.toENat (Algebra.trdeg (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField B)) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg A B) : WithBot ℕ∞) := by
  classical
  let : Algebra.EssFiniteType A B := essFiniteType_of_isEssentiallyOfFiniteType A B hfinite
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  obtain ⟨V, hAV, hlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing (algebraMap A (FractionRing A))
  let : Algebra A V := ((algebraMap A (FractionRing A)).codRestrict V.toSubring hAV).toAlgebra
  have : IsLocalHom (algebraMap A V) := hlocal
  have : IsScalarTower A V (FractionRing A) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsDomain (V ⊗[A] B) := tensorProduct_isDomain_of_flat (A := A) (B := B)
    (V := V) (show Function.Injective (algebraMap V (FractionRing A)) from Subtype.val_injective)
  let D := V ⊗[A] B
  let : Algebra B D := Algebra.TensorProduct.rightAlgebra
  have : FaithfulSMul A V := (faithfulSMul_iff_algebraMap_injective A V).mpr
    (fun x y h => (IsFractionRing.injective A (FractionRing A))
      (congrArg (algebraMap V (FractionRing A)) h))
  obtain ⟨q, hq, hqV, hqB⟩ := exists_tensorProduct_prime_over_maximalIdeals A V B
  let : q.IsPrime := hq
  let L := Localization.AtPrime q
  have hVL : (IsLocalRing.maximalIdeal L).under V = IsLocalRing.maximalIdeal V := by
    rw [← Ideal.under_under (A := V) (B := D),
      IsLocalization.AtPrime.under_maximalIdeal L q]
    exact hqV
  have : IsLocalHom (algebraMap V L) := ((IsLocalRing.local_hom_TFAE _).out 5 1).mp hVL
  have hBL : (IsLocalRing.maximalIdeal L).under B = IsLocalRing.maximalIdeal B := by
    rw [← Ideal.under_under (A := B) (B := D),
      IsLocalization.AtPrime.under_maximalIdeal L q]
    exact hqB
  have : IsLocalHom (algebraMap B L) := ((IsLocalRing.local_hom_TFAE _).out 5 1).mp hBL
  have : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : FaithfulSMul V D := (faithfulSMul_iff_algebraMap_injective V D).mpr (by
    intro x y h
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B) V
    exact congrArg (Algebra.TensorProduct.comm A V B) h)
  have : FaithfulSMul V L := (faithfulSMul_iff_algebraMap_injective V L).mpr
    ((IsLocalization.injective L q.primeCompl_le_nonZeroDivisors).comp
      (FaithfulSMul.algebraMap_injective V D))
  have : FaithfulSMul B D := (faithfulSMul_iff_algebraMap_injective B D).mpr
    (Module.Flat.tensorProduct_mk_injective A B V)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr
    ((IsLocalization.injective L q.primeCompl_le_nonZeroDivisors).comp
      (FaithfulSMul.algebraMap_injective B D))
  have : Algebra.EssFiniteType V D := Algebra.EssFiniteType.baseChange A B V
  have : Algebra.EssFiniteType D L := Algebra.EssFiniteType.of_isLocalization L q.primeCompl
  have : Algebra.EssFiniteType V L := Algebra.EssFiniteType.comp V D L
  have : Algebra.IsAlgebraic A (FractionRing A) :=
    IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
  have : Algebra.IsAlgebraic A V := Algebra.IsAlgebraic.of_injective
    (IsScalarTower.toAlgHom A V (FractionRing A)) Subtype.val_injective
  have : Algebra.IsAlgebraic B D := (Algebra.TensorProduct.commRight A B V).isAlgebraic
  have : Algebra.IsAlgebraic D L := IsLocalization.isAlgebraic L q.primeCompl
  have : Algebra.IsAlgebraic B L := Algebra.IsAlgebraic.trans B D L
  have ht : Algebra.trdeg V L = Algebra.trdeg A B :=
    (trdeg_eq_of_isAlgebraic_left (R := A) (S := V) (A := L)).trans
      (trdeg_eq_of_isAlgebraic_right (R := A) (S := B) (A := L)).symm
  let C := Algebra.EssFiniteType.subalgebra A B
  let M := Algebra.EssFiniteType.submonoid A B
  have : IsLocalization M B := Algebra.EssFiniteType.isLocalization A B
  let C' := V ⊗[A] C
  let : Algebra C C' := Algebra.TensorProduct.rightAlgebra
  let f : C' →ₐ[V] D := Algebra.TensorProduct.map (AlgHom.id V V)
    (IsScalarTower.toAlgHom A C B)
  let : Algebra C' D := f.toRingHom.toAlgebra
  have : IsScalarTower V C' D := IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  have hmap : (algebraMap C' D).comp (algebraMap C C') =
      (algebraMap B D).comp (algebraMap C B) := by
    ext x
    rfl
  have : IsLocalization (M.map (algebraMap C C')) D :=
    IsLocalization.tensorProduct_tensorProduct_right A V M B hmap
  have : IsLocalization.AtPrime L (q.under C') :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M.map (algebraMap C C')) L q
  have hmodel : ((IsLocalRing.maximalIdeal L).under C').under C =
      (IsLocalRing.maximalIdeal B).under C := by
    rw [← Ideal.under_under (A := C') (B := D),
      IsLocalization.AtPrime.under_maximalIdeal L q]
    change Ideal.comap _ (Ideal.comap _ q) = _
    rw [Ideal.comap_comap, hmap, ← Ideal.comap_comap]
    change (q.under B).under C = _
    rw [show q.under B = IsLocalRing.maximalIdeal B from hqB]
  have hbase := Algebra.IsPushout.relativeDimensionAt_comap_eq A C V C'
    ⟨(IsLocalRing.maximalIdeal L).under C', inferInstance⟩
  change Algebra.relativeDimensionAt A (((IsLocalRing.maximalIdeal L).under C').under C) =
    Algebra.relativeDimensionAt V ((IsLocalRing.maximalIdeal L).under C') at hbase
  rw [Algebra.relativeDimensionAt_congr (R := A) hmodel] at hbase
  have : IsLocalization.AtPrime L ((IsLocalRing.maximalIdeal L).under C') :=
    isLocalization_at_comap_maximalIdeal C' L (q.under C').primeCompl
  rw [relativeDimensionAt_eq_closedFiber A C B M,
    relativeDimensionAt_eq_closedFiber V C' L
      ((IsLocalRing.maximalIdeal L).under C').primeCompl,
    closedFiber_eq_trdeg_of_valuationRing V L, ht] at hbase
  exact (closedFiber_dimension_eq A B).trans hbase

end IsLocalRing
