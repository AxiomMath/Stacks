module

public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.FlatnessAndReducedness
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.NormalityAndDimension
public import StacksFrontier.RingTheory.Henselian.PermanenceOfProperties.NoetherianCompletions
import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GeometricBranches
import StacksFrontier.RingTheory.Depth.UnqualifiedDepth

/-!
# Permanence under henselization: depth, Cohen–Macaulayness, regularity, and fibres

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

06LL, 06LM, 06LN, 0AP3, 07QQ.

## Tag 06LL — Depth of henselizations

The depth of a Noetherian local ring agrees with the depths of its henselization and its strict
henselization.

### Main definitions

There are no new definitions.

### Main results

* `ringDepth_eq_henselization_eq_strictHenselization`: henselization and strict
  henselization preserve the depth of a Noetherian local ring.

### Implementation notes

Henselizations are represented by `IsLocalRing.IsHenselization`. A strict henselization is a
henselization whose residue field is a separable closure of the residue field of the original
ring. The chain of equalities in the source is represented by a conjunction of two equalities.

### References

* [Stacks Project, Tag 06LL](https://stacks.math.columbia.edu/tag/06LL)

## Tag 06LM — Cohen–Macaulay henselizations

A Noetherian local ring is Cohen–Macaulay if and only if its henselization is
Cohen–Macaulay, and if and only if its strict henselization is Cohen–Macaulay.

### Main definitions

There are no new definitions.

### Main results

* `isMaximalCohenMacaulay_iff_henselizations`: Cohen–Macaulayness is invariant under
  henselization and strict henselization.

### Implementation notes

Henselizations are represented by `IsLocalRing.IsHenselization`. A strict henselization is a
henselization whose residue field is a separable closure of the residue field of the original
ring. Cohen–Macaulayness of a local ring `A` is expressed as
`Module.IsMaximalCohenMacaulay A A`. The three equivalent conditions in the source are
represented by two equivalences having the condition on the original ring as their common side.

### References

* [The Stacks Project, Tag 06LM](https://stacks.math.columbia.edu/tag/06LM)

## Tag 06LN — Regularity of henselizations

A Noetherian local ring is regular if and only if its henselization is regular, and if and only
if its strict henselization is regular.

### Main definitions

There are no new definitions.

### Main results

* `isRegularLocalRing_iff_henselizations`: regularity is invariant under henselization
  and strict henselization.

### Implementation notes

Henselizations are represented by `IsLocalRing.IsHenselization`. A strict henselization is a
henselization whose residue field is a separable closure of the residue field of the original
ring. The equivalence of the three conditions in the source is represented by the conjunction
of the two equivalences with the original ring.

### References

* [Stacks Project, Tag 06LN](https://stacks.math.columbia.edu/tag/06LN)

## Tag 0AP3 — Discrete valuation rings and henselizations

A Noetherian local ring is a discrete valuation ring if and only if its henselization is a
discrete valuation ring, and if and only if its strict henselization is a discrete valuation ring.

### Main definitions

There are no new definitions.

### Main results

* `isDiscreteValuationRing_iff_henselizations`: the discrete valuation ring property is
  invariant under henselization and strict henselization.

### Implementation notes

Henselizations are represented by `IsLocalRing.IsHenselization`. A strict henselization is a
henselization whose residue field is a separable closure of the residue field of the original
ring. Since Mathlib's `IsDiscreteValuationRing` takes an `IsDomain` instance as input, each
discrete valuation ring condition existentially packages that instance. The equivalence of the
three conditions in the source is represented by the conjunction of the two equivalences with
the original ring.

### References

* [Stacks Project, Tag 0AP3](https://stacks.math.columbia.edu/tag/0AP3)

## Tag 07QQ — Fibres of henselizations

The fibre of a henselization or strict henselization of a Noetherian local ring over a prime is
the finite product of the residue fields at the primes lying over it. Each of the resulting
residue-field extensions is separable algebraic.

### Main definitions

There are no new definitions.

### Main results

* `henselization_fibres_equiv_pi_residueFields` gives the product decompositions for
  both henselization and strict henselization, including the separable algebraicity of every
  residue-field extension.

### Implementation notes

Henselizations are represented abstractly by `IsLocalRing.IsHenselization`. The fibre is written
as `κ(p) ⊗[R] Rh`, canonically isomorphic by symmetry to the source's `Rh ⊗[R] κ(p)`.
The finite families are required to enumerate exactly the primes lying over the given prime.

### References

* [Stacks Project, Tag 07QQ](https://stacks.math.columbia.edu/tag/07QQ)
-/

@[expose] public section

/-! ### Stacks Tag 06LL -/

section

section

@[expose] public section

open IsLocalRing

universe u v

private lemma depth_quotient_maximalIdeal_eq_zero
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Module.depth A (maximalIdeal A) (A ⧸ maximalIdeal A) = 0 := by
  rw [Module.depth]
  simp only [Ideal.smul_top_eq_map, Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self,
    Submodule.restrictScalars_bot, bot_ne_top, ↓reduceIte, mem_maximalIdeal, mem_nonunits_iff,
    Set.mem_ofPred_eq, ENat.iSup_eq_zero, Nat.cast_eq_zero, List.length_eq_zero_iff, and_imp]
  intro xs hmem hreg
  cases xs with
  | nil => rfl
  | cons f t =>
      have hfreg := (RingTheory.Sequence.isRegular_cons_iff
        (A ⧸ maximalIdeal A) f t).mp hreg
      have hf : f ∈ maximalIdeal A := by
        simpa [mem_maximalIdeal] using hmem f (by simp)
      have hzero : f • (1 : A ⧸ maximalIdeal A) = 0 := by
        simp [Algebra.smul_def, Ideal.Quotient.eq_zero_iff_mem, hf]
      have hone : (1 : A ⧸ maximalIdeal A) = 0 := hfreg.1 (by simpa using hzero)
      exact absurd hone one_ne_zero

private lemma ringDepth_eq_of_isHenselization
    (R : Type u) [CommRing R] [IsLocalRing R]
    (L : Type*) [Field L] [Algebra (ResidueField R) L]
    (S : Type u) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [Algebra R S]
    [IsHenselization R L S] : ringDepth R = ringDepth S := by
  have : IsLocalHom (algebraMap R S) := IsHenselization.isLocalHom (L := L)
  let : Module.Flat R S := IsHenselization.flat (L := L)
  have h := Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal R S
  rw [IsHenselization.map_maximalIdeal (L := L),
    depth_quotient_maximalIdeal_eq_zero, add_zero] at h
  rw [ringDepth_eq_depth_maximalIdeal, ringDepth_eq_depth_maximalIdeal, h]

/-- A Noetherian local ring, its henselization, and its strict henselization have equal depth. -/
@[stacks 06LL]
public theorem ringDepth_eq_henselization_eq_strictHenselization
    (R Rh Rsh : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R κsep Rsh] :
    ringDepth R = ringDepth Rh ∧ ringDepth Rh = ringDepth Rsh := by
  have hN := isNoetherianRing_iff_henselizations R Rh Rsh κsep
  have : IsNoetherianRing Rh := hN.1.mp inferInstance
  have : IsNoetherianRing Rsh := hN.2.mp inferInstance
  have hRh := ringDepth_eq_of_isHenselization R (ResidueField R) Rh
  have hRsh := ringDepth_eq_of_isHenselization R κsep Rsh
  exact ⟨hRh, hRh.symm.trans hRsh⟩

end

end

end

/-! ### Stacks Tag 06LM -/

section

section

@[expose] public section

open IsLocalRing Ideal Pointwise

universe u v

/-- A Noetherian local ring is Cohen–Macaulay if and only if its henselization is, and if and
only if its strict henselization is. -/
@[stacks 06LM, ega "IV 18.6.10" "a)", ega "IV 18.8.13" "a)"]
public theorem isMaximalCohenMacaulay_iff_henselizations
    (R Rh Rsh : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (ksep : Type v) [Field ksep] [Algebra (ResidueField R) ksep]
    [IsSepClosure (ResidueField R) ksep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R ksep Rsh] :
    (Module.IsMaximalCohenMacaulay R R ↔ Module.IsMaximalCohenMacaulay Rh Rh) ∧
      (Module.IsMaximalCohenMacaulay R R ↔ Module.IsMaximalCohenMacaulay Rsh Rsh) := by
  obtain ⟨hdepthRh, hdepthRsh⟩ :=
    ringDepth_eq_henselization_eq_strictHenselization R Rh Rsh ksep
  obtain ⟨hdimRh, hdimRsh⟩ :=
    ringKrullDim_eq_henselization_eq_strictHenselization R Rh Rsh ksep
  simp only [Module.IsMaximalCohenMacaulay]
  rw [← ringDepth_eq_depth_maximalIdeal R, ← ringDepth_eq_depth_maximalIdeal Rh,
    ← ringDepth_eq_depth_maximalIdeal Rsh]
  rw [hdepthRh, hdimRh, hdepthRsh, hdimRsh]
  exact ⟨Iff.rfl, Iff.rfl⟩

end

end

end

/-! ### Stacks Tag 06LN -/

section

section

@[expose] public section

open CategoryTheory IsLocalRing

universe u v

private lemma residueMap_bijective_of_isHenselization
    (R H : Type u) [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [IsLocalHom (algebraMap R H)]
    [IsHenselization R (ResidueField R) H] :
    Function.Bijective (ResidueField.map (algebraMap R H)) := by
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv
    (R := R) (L := ResidueField R) (Rh := H)
  have hfun : ResidueField.map (algebraMap R H) = e := by
    ext x
    obtain ⟨r, rfl⟩ := residue_surjective x
    simpa using (he r).symm
  rw [hfun]
  exact e.bijective

private alias isSepClosed_of_ringEquiv_06ln :=
  Stacks.StrictHenselization.EtaleColimit.isSepClosed_of_ringEquiv

/-- A Noetherian local ring is regular if and only if its henselization is regular, and if and
only if its strict henselization is regular. -/
@[stacks 06LN, ega "IV 18.6.10", ega "IV 18.8.13"]
public theorem isRegularLocalRing_iff_henselizations
    (R Rh Rsh : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R κsep Rsh] :
    (IsRegularLocalRing R ↔ IsRegularLocalRing Rh) ∧
      (IsRegularLocalRing R ↔ IsRegularLocalRing Rsh) := by
  have : IsLocalHom (algebraMap R Rh) := IsHenselization.isLocalHom (L := ResidueField R)
  have : IsLocalHom (algebraMap R Rsh) := IsHenselization.isLocalHom (L := κsep)
  have : HenselianLocalRing Rh := IsHenselization.henselian R (ResidueField R)
  have : HenselianLocalRing Rsh := IsHenselization.henselian R κsep
  have hresRh : Function.Bijective (ResidueField.map (algebraMap R Rh)) :=
    residueMap_bijective_of_isHenselization R Rh
  let f : Rh →ₐ[R] Rsh := HenselianLocalRing.indEtaleAlgHom
    (Sh := Rsh)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    hresRh.2
  have hf : IsLocalHom f := HenselianLocalRing.isLocalHom_indEtaleAlgHom
    (Sh := Rsh)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    hresRh.2
  let : Algebra Rh Rsh := f.toRingHom.toAlgebra
  let : IsScalarTower R Rh Rsh :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  have : IsLocalHom (algebraMap Rh Rsh) := ⟨hf.map_nonunit⟩
  have : IsSepClosed κsep := IsSepClosure.sep_closed (ResidueField R)
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv
    (R := R) (L := κsep) (Rh := Rsh)
  let : IsSepClosed (ResidueField Rsh) := isSepClosed_of_ringEquiv_06ln e
  have hprops := henselization_faithfullyFlat_and_quotient_basis
    (R := R) (Rh := Rh) (Rsh := Rsh) (κsep := κsep)
    (IsHenselization.ind_etale_of_universe_le (R := R) (L := ResidueField R) (Rh := Rh)) hresRh
    (IsHenselization.ind_etale_of_universe_le (R := R) (L := κsep) (Rh := Rsh)) ⟨e, he⟩
  have : Module.FaithfullyFlat R Rh := hprops.1
  have : Module.FaithfullyFlat Rh Rsh := hprops.2.1
  have hnoeth := isNoetherianRing_iff_henselizations R Rh Rsh κsep
  have : IsNoetherianRing Rh := hnoeth.1.mp inferInstance
  have : IsNoetherianRing Rsh := hnoeth.2.mp inferInstance
  have hmaxRh : (maximalIdeal R).map (algebraMap R Rh) = maximalIdeal Rh := hprops.2.2.1
  have hmaxRsh : (maximalIdeal Rh).map (algebraMap Rh Rsh) = maximalIdeal Rsh :=
    hprops.2.2.2.2.1
  have ascendRh (hR : IsRegularLocalRing R) : IsRegularLocalRing Rh := by
    apply isRegularLocalRing_of_flat_of_regular_closedFibre R Rh hR
    rw [hmaxRh]
    let : Field (Rh ⧸ maximalIdeal Rh) := Ideal.Quotient.field _
    infer_instance
  have ascendRsh (hRh : IsRegularLocalRing Rh) : IsRegularLocalRing Rsh := by
    apply isRegularLocalRing_of_flat_of_regular_closedFibre Rh Rsh hRh
    rw [hmaxRsh]
    let : Field (Rsh ⧸ maximalIdeal Rsh) := Ideal.Quotient.field _
    infer_instance
  have descendRh (_ : IsRegularLocalRing Rh) : IsRegularLocalRing R :=
    IsRegularLocalRing.of_flat_of_isLocalHom Rh
  have descendRsh (_ : IsRegularLocalRing Rsh) : IsRegularLocalRing Rh :=
    IsRegularLocalRing.of_flat_of_isLocalHom Rsh
  exact ⟨⟨ascendRh, descendRh⟩,
    ⟨fun hR ↦ ascendRsh (ascendRh hR), fun hRsh ↦ descendRh (descendRsh hRsh)⟩⟩

end

end

end

/-! ### Stacks Tag 0AP3 -/

section

section

@[expose] public section

open IsLocalRing

universe u v

/-- A Noetherian local ring is a discrete valuation ring if and only if its henselization is a
discrete valuation ring, and if and only if its strict henselization is a discrete valuation
ring. -/
@[stacks 0AP3]
public theorem isDiscreteValuationRing_iff_henselizations
    (R Rh Rsh : Type u)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep]
    [IsHenselization R (ResidueField R) Rh]
    [IsHenselization R κsep Rsh] :
    ((∃ _ : IsDomain R, IsDiscreteValuationRing R) ↔
      ∃ _ : IsDomain Rh, IsDiscreteValuationRing Rh) ∧
      ((∃ _ : IsDomain R, IsDiscreteValuationRing R) ↔
        ∃ _ : IsDomain Rsh, IsDiscreteValuationRing Rsh) := by
  have hreg := isRegularLocalRing_iff_henselizations R Rh Rsh κsep
  have hdim :=
    ringKrullDim_eq_henselization_eq_strictHenselization R Rh Rsh κsep
  have hR := (isDiscreteValuationRing_tfae R).out 1 3
  have hRh := (isDiscreteValuationRing_tfae Rh).out 1 3
  have hRsh := (isDiscreteValuationRing_tfae Rsh).out 1 3
  constructor
  · rw [hR, hRh, hreg.1, hdim.1]
  · rw [hR, hRsh, hreg.2, hdim.1, hdim.2]

end

end

end

/-! ### Stacks Tag 07QQ -/

section

section

open IsLocalRing

universe u v

open CategoryTheory CategoryTheory.Limits

/-- Let `Rh` and `Rsh` be respectively a henselization and a strict henselization of a
Noetherian local ring `R`. Over every prime `p` of `R`, their fibres are finite products of the
residue fields at exactly the primes lying over `p`, and all the corresponding residue-field
extensions are separable algebraic. -/
@[stacks 07QQ, ega "IV 18.8.12" "(ii), special case"]
public theorem henselization_fibres_equiv_pi_residueFields
    (R Rh Rsh : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [CommRing Rsh] [IsLocalRing Rsh] [Algebra R Rsh]
    [IsHenselization R (ResidueField R) Rh]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField R) κsep]
    [IsSepClosure (ResidueField R) κsep]
    [IsHenselization R κsep Rsh]
    (p : Ideal R) [p.IsPrime] :
    (∃ (t : ℕ) (q : Fin t → Ideal Rh) (hq : ∀ i, (q i).IsPrime)
        (hlo : ∀ i, (q i).LiesOver p),
      (letI : ∀ i, (q i).IsPrime := hq
       letI : ∀ i, Algebra p.ResidueField (q i).ResidueField := fun i ↦
         (Ideal.ResidueField.map p (q i) (algebraMap R Rh) (hlo i).over).toAlgebra
       Nonempty
         (TensorProduct R p.ResidueField Rh ≃ₐ[p.ResidueField]
           (∀ i, (q i).ResidueField)) ∧
       (∀ i, Algebra.IsSeparable p.ResidueField (q i).ResidueField) ∧
       (∀ i, Algebra.IsAlgebraic p.ResidueField (q i).ResidueField)) ∧
      Function.Injective q ∧
      (∀ q' : Ideal Rh, ∀ _ : q'.IsPrime, q'.LiesOver p ↔ ∃ i, q i = q')) ∧
    (∃ (s : ℕ) (r : Fin s → Ideal Rsh) (hr : ∀ i, (r i).IsPrime)
        (hlo : ∀ i, (r i).LiesOver p),
      (letI : ∀ i, (r i).IsPrime := hr
       letI : ∀ i, Algebra p.ResidueField (r i).ResidueField := fun i ↦
         (Ideal.ResidueField.map p (r i) (algebraMap R Rsh) (hlo i).over).toAlgebra
       Nonempty
         (TensorProduct R p.ResidueField Rsh ≃ₐ[p.ResidueField]
           (∀ i, (r i).ResidueField)) ∧
       (∀ i, Algebra.IsSeparable p.ResidueField (r i).ResidueField) ∧
       (∀ i, Algebra.IsAlgebraic p.ResidueField (r i).ResidueField)) ∧
      Function.Injective r ∧
      (∀ r' : Ideal Rsh, ∀ _ : r'.IsPrime, r'.LiesOver p ↔ ∃ i, r i = r')) := by
  have hnoeth := isNoetherianRing_iff_henselizations R Rh Rsh κsep
  have : IsNoetherianRing Rh := hnoeth.1.mp inferInstance
  have : IsNoetherianRing Rsh := hnoeth.2.mp inferInstance
  constructor
  · exact IsFilteredColimitEtale.exists_fiber_algEquiv_pi_residueField
      (Stacks.Henselization.Shared.isFilteredColimitEtale_of_ind R Rh
        (IsHenselization.ind_etale_of_universe_le (R := R) (ResidueField R) (Rh := Rh))) p
  · exact IsFilteredColimitEtale.exists_fiber_algEquiv_pi_residueField
      (Stacks.Henselization.Shared.isFilteredColimitEtale_of_ind R Rsh
        (IsHenselization.ind_etale_of_universe_le (R := R) κsep (Rh := Rsh))) p

end

end

end
