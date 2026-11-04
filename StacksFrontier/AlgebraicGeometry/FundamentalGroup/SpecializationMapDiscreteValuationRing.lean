module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapHelpers
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.RingTheory.Localization.Cardinality
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.BaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleGaloisCategory
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleSpreadingOut
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationMapFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.DiscreteValuationRing.Existence
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.RingTheory.Henselian.Criteria
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Realizing a specialization map over a discrete valuation ring

Let `f : X ⟶ S` be a proper morphism with geometrically connected fibres, let `s' ⇝ s` be a
specialization of points of a Noetherian scheme `S`, and let `sp : π₁(X_{s̄'}) → π₁(X_{s̄})` be a
specialization map. Then `sp` is isomorphic to the specialization map of a base change
`X_R ⟶ Spec R` for a strictly henselian discrete valuation ring `R` over `S`, the specialization
being the one from the generic point of `Spec R` to its closed point.

"Isomorphic" is not defined in the source; what its proof produces, and what is proved here, is a
commutative square whose two vertical maps are isomorphisms of topological groups:
`π₁(X_{s̄'}) ≅ π₁(X_{η̄})` and `π₁(X_{s̄}) ≅ π₁(X_{ō})` intertwining `sp` and `sp_R`.

## Main results

* `AlgebraicGeometry.exists_isSpecializationMap_isomorphic_over_isDiscreteValuationRing` — the
  realization of a specialization map over a strictly henselian discrete valuation ring.

## Implementation notes

The discrete valuation ring produced is complete with *algebraically closed* residue field, which
is stronger than the source's "strictly henselian", and is what makes the closed point of
`Spec R` carry a geometric point with residue field the residue field of `R` itself. It is
obtained from the strict henselization `A` of `𝒪_{S,s}` appearing in the given specialization map:
the geometric point `s̄'` cuts out a prime `P ⊆ A`, Stacks 00PH produces a discrete valuation ring
dominating `A/P` inside its fraction field, Stacks 0ARL replaces it by an integral extension with
algebraically closed residue field, and the adic completion of that is a complete — hence
henselian — discrete valuation ring with the same residue field.

Everything is proved here except the one input the library cannot prove, carried as the
hypothesis `h0A48` and described on the main theorem.

## References

* [Stacks Project, Tag 0C0N](https://stacks.math.columbia.edu/tag/0C0N)
* [Stacks Project, Tag 00PH](https://stacks.math.columbia.edu/tag/00PH)
* [Stacks Project, Tag 0ARL](https://stacks.math.columbia.edu/tag/0ARL)
* [Stacks Project, Tag 0AP1](https://stacks.math.columbia.edu/tag/0AP1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Stacks.FundamentalGroup

universe u

namespace AlgebraicGeometry

/-! ### Discrete valuation rings with algebraically closed residue field

The first group of lemmas produces, over a Noetherian local ring `A` and a prime `P` of `A`, a
complete discrete valuation ring with algebraically closed residue field receiving a local
homomorphism from `A` whose kernel is exactly `P`.
-/

/-- **Stacks Project, Tag 0ARL**, the key step. Inside an algebraically closed overfield, a
discrete valuation ring has an integral extension which is again a discrete valuation ring with
the same uniformizer and with algebraically closed residue field: a maximal such extension exists
by Zorn's lemma, and maximality forces every monic polynomial over its residue field to have a
root there. -/
@[ega "IV 15.7.7" "partial"]
private theorem exists_isAlgClosed_residueField_subalgebra
    (A Ω : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field Ω] [IsAlgClosed Ω] [Algebra A Ω] [FaithfulSMul A Ω]
    (π : A) (hπ : Irreducible π) :
    ∃ S : Subalgebra A Ω, S ≤ integralClosure A Ω ∧
      ∃ _ : IsDiscreteValuationRing S,
        Irreducible (algebraMap A S π) ∧ IsAlgClosed (ResidueField S) := by
  classical
  let P (S : Subalgebra A Ω) : Prop := S ≤ integralClosure A Ω ∧
    ∃ _ : IsDiscreteValuationRing S, Irreducible (algebraMap A S π)
  have hbot : P ⊥ := by
    let e := Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective A Ω)
    have hdvr : IsDiscreteValuationRing (⊥ : Subalgebra A Ω) :=
      IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e.symm
    refine ⟨bot_le, hdvr, ?_⟩
    apply (MulEquiv.irreducible_iff e).mp
    simpa only [AlgEquiv.commutes, Algebra.algebraMap_self, RingHom.id_apply] using hπ
  obtain ⟨S, _, hS⟩ := zorn_le_nonempty₀ {S | P S} (by
    intro c hcs hc y hy
    have hDVR (i : c) : IsDiscreteValuationRing i.val := (hcs i.property).2.choose
    have hirr (i : c) : Irreducible (algebraMap A i.val π) := (hcs i.property).2.choose_spec
    obtain ⟨hd, hi⟩ := IsDiscreteValuationRing.isDiscreteValuationRing_sSup_chain π c hc ⟨y, hy⟩
      (fun i hi => hDVR ⟨i, hi⟩) (fun i hi => hirr ⟨i, hi⟩)
    exact ⟨sSup c, ⟨sSup_le fun i hi => (hcs hi).1, hd, hi⟩, fun i hi => le_sSup hi⟩) ⊥ hbot
  obtain ⟨hSint, hSdvr, hπS⟩ := hS.prop
  have := hSdvr
  have : Algebra.IsIntegral A S := (Subalgebra.isIntegral_iff S).mpr hSint
  refine ⟨S, hSint, hSdvr, hπS, ?_⟩
  apply IsAlgClosed.of_exists_root
  intro p hp hpirr
  have hlift : p ∈ Polynomial.lifts (residue S) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact residue_surjective _
  obtain ⟨q, hq, _, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hp
  obtain ⟨hqdom, hqdvr, hqmax⟩ :=
    IsDiscreteValuationRing.adjoinRoot_isDiscreteValuationRing S q hqmonic (hq.symm ▸ hpirr)
  have := hqdom
  have := hqdvr
  have : Module.Finite S (AdjoinRoot q) := hqmonic.finite_adjoinRoot
  have : Module.Free S (AdjoinRoot q) := hqmonic.free_adjoinRoot
  have : Module.IsTorsionFree S (AdjoinRoot q) := Module.Free.instIsTorsionFree S (AdjoinRoot q)
  have : IsScalarTower A S (AdjoinRoot q) := inferInstance
  let f : AdjoinRoot q →ₐ[S] Ω := IsAlgClosed.lift
  have hf : Function.Injective f := by
    let _ : Algebra (AdjoinRoot q) Ω := f.toRingHom.toAlgebra
    have : IsScalarTower S (AdjoinRoot q) Ω :=
      IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    exact Algebra.IsAlgebraic.injective_tower_top (AdjoinRoot q)
      (FaithfulSMul.algebraMap_injective S Ω)
  let T : Subalgebra A Ω := f.range.restrictScalars A
  let _ : Algebra S T := f.range.algebra
  let e : AdjoinRoot q ≃ₐ[S] T := AlgEquiv.ofInjective f hf
  have hTdvr : IsDiscreteValuationRing T :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hST : S ≤ T := fun x hx => ⟨algebraMap S (AdjoinRoot q) ⟨x, hx⟩, f.commutes _⟩
  have hπq : Irreducible (algebraMap A (AdjoinRoot q) π) := by
    apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
    · change algebraMap S (AdjoinRoot q) (algebraMap A S π) ≠ 0
      simpa using (FaithfulSMul.algebraMap_injective S (AdjoinRoot q)).ne hπS.ne_zero
    · rw [← hqmax, hπS.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
      rfl
  have hPT : P T := by
    refine ⟨?_, hTdvr, ?_⟩
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      exact isIntegral_trans (R := A) _ ((Algebra.IsIntegral.isIntegral (R := S) y).map f)
    · have he : e (algebraMap A (AdjoinRoot q) π) = algebraMap A T π := by
        apply Subtype.ext
        change f (algebraMap S (AdjoinRoot q) (algebraMap A S π)) = algebraMap A Ω π
        exact f.commutes (algebraMap A S π)
      rw [← he]
      exact (MulEquiv.irreducible_iff e).mpr hπq
  have hTS : T ≤ S := hS.2 hPT hST
  let r : S := ⟨f (AdjoinRoot.root q), hTS ⟨AdjoinRoot.root q, rfl⟩⟩
  have hr : Polynomial.aeval r q = 0 := by
    apply Subtype.val_injective (p := fun x : Ω => x ∈ S)
    change algebraMap S Ω (Polynomial.aeval r q) = algebraMap S Ω 0
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply]
    change Polynomial.aeval (f (AdjoinRoot.root q)) q = 0
    rw [Polynomial.aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
  refine ⟨residue S r, ?_⟩
  rw [← hq, Polynomial.eval_map]
  simpa only [Polynomial.eval₂_at_apply, Polynomial.aeval_def, Algebra.algebraMap_self,
    Polynomial.eval₂_id, RingHom.map_zero] using congrArg (residue S) hr

/-- **Stacks Project, Tag 0ARL.** Every discrete valuation ring `A` admits an extension to a
complete discrete valuation ring `C` with algebraically closed residue field, with
`#C ≤ max {ℵ₀, #A} ^ ℵ₀`: pass to an integral extension with algebraically closed residue field
inside an algebraic closure of the fraction field, then take the adic completion, which is again a
discrete valuation ring by Stacks 0AP1 and has the same residue field. The algebraic closure has
at most `max {ℵ₀, #A}` elements and the completion at most countable sequences of those. -/
@[ega "II 7.1.4" "(i), special case",
  ega "IV 11.8.2" "(i)",
  ega "IV 15.7.7",
  sga "3 XV 3.3" "partial"]
public theorem exists_isAdicComplete_isAlgClosed_residueField_extension
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    ∃ (C : Type u) (hCring : CommRing C) (hCdom : IsDomain C)
      (hCdvr : IsDiscreteValuationRing C),
      let := hCring; let := hCdom; let := hCdvr
      IsAdicComplete (maximalIdeal C) C ∧ IsAlgClosed (ResidueField C) ∧
        (∃ φ : A →+* C, IsLocalHom φ ∧ Function.Injective φ) ∧
        Cardinal.mk C ≤ max Cardinal.aleph0 (Cardinal.mk A) ^ Cardinal.aleph0 := by
  let K := FractionRing A
  let Ω := AlgebraicClosure K
  let : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective A Ω).mpr (by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨S, hSint, hSdvr, _, hres⟩ := exists_isAlgClosed_residueField_subalgebra A Ω π hπ
  let : IsDiscreteValuationRing S := hSdvr
  let : Algebra.IsIntegral A S := (Subalgebra.isIntegral_iff S).mpr hSint
  let : IsDiscreteValuationRing.IsExtension A S := ⟨⟩
  let : IsAlgClosed (ResidueField S) := hres
  let I : Ideal S := maximalIdeal S
  let C := AdicCompletion I S
  obtain ⟨hCdom, hCdvr⟩ :=
    (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := S)).mp ⟨inferInstance, hSdvr⟩
  let : IsDomain C := hCdom
  let : IsDiscreteValuationRing C := hCdvr
  let : IsLocalHom (algebraMap S C) :=
    AdicCompletion.algebraMap_isLocalHom_of_fg I.fg_of_isNoetherianRing
  let : Module.FaithfullyFlat S C :=
    AdicCompletion.faithfullyFlat_of_le_ringJacobson I
      (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal])
  let : FaithfulSMul S C := Module.FaithfullyFlat.faithfulSMul
  have hcard : Cardinal.mk C ≤ max Cardinal.aleph0 (Cardinal.mk A) ^ Cardinal.aleph0 := by
    have hΩ : Cardinal.mk Ω ≤ max Cardinal.aleph0 (Cardinal.mk A) := by
      calc Cardinal.mk Ω ≤ max (Cardinal.mk K) Cardinal.aleph0 :=
            Algebra.IsAlgebraic.cardinalMk_le_max K Ω
        _ = max Cardinal.aleph0 (Cardinal.mk A) := by
            rw [IsFractionRing.cardinalMk A K, max_comm]
    have hS : Cardinal.mk S ≤ max Cardinal.aleph0 (Cardinal.mk A) :=
      (Cardinal.mk_le_of_injective Subtype.val_injective).trans hΩ
    exact (cardinal_mk_adicCompletion_le I).trans (Cardinal.power_le_power_right hS)
  refine ⟨C, inferInstance, inferInstance, inferInstance,
    AdicCompletion.isAdicComplete_of_fg I.fg_of_isNoetherianRing, ?_,
    ⟨(algebraMap S C).comp (algebraMap A S), RingHom.isLocalHom_comp _ _,
      (FaithfulSMul.algebraMap_injective S C).comp (FaithfulSMul.algebraMap_injective A S)⟩,
    hcard⟩
  exact IsAlgClosed.of_ringEquiv (ResidueField S) (ResidueField C)
    (RingEquiv.ofBijective (ResidueField.map (algebraMap S C))
      (AdicCompletion.residueField_map_bijective_of_fg I.fg_of_isNoetherianRing))

/-- Stacks 00PH in the form used below: a Noetherian local domain which is not a field is
dominated by a discrete valuation subring of its own fraction field. The essentially-finite-type
hypothesis of the general statement is satisfied because the extension is trivial. -/
@[ega "II 7.1.7" "L = K", ega "IV 12.0.2" "special case", sga "6 X 7.17" "special case"]
private theorem exists_isDiscreteValuationRing_subalgebra_fractionRing
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : ¬ IsField A) :
    ∃ B : Subalgebra A (FractionRing A), IsDiscreteValuationRing B ∧
      IsLocalHom (algebraMap A B) := by
  let : Algebra.EssFiniteType (FractionRing A) (FractionRing A) := inferInstance
  obtain ⟨B, hB, -, hBloc⟩ :=
    exists_isDiscreteValuationRing_isFractionRing_of_not_isField (R := A)
      (K := FractionRing A) (L := FractionRing A) hA
  exact ⟨B, hB, hBloc⟩

/-- Every prime of a Noetherian local ring is the kernel of a local homomorphism to a complete
discrete valuation ring with algebraically closed residue field.

For the maximal ideal the ring of formal power series over an algebraic closure of the residue
field will do. For a smaller prime `P`, the quotient `A/P` is a Noetherian local domain which is
not a field, so Stacks 00PH dominates it by a discrete valuation ring, and Stacks 0ARL enlarges
that to a complete one with algebraically closed residue field. -/
@[ega "II 7.1.2" "partial",
  ega "II 7.1.4" "special case",
  ega "IV 11.8.2" "more general",
  ega "IV 12.0.2" "special case",
  ega "IV 15.7.7" "more general", sga "3 XV 3.3" "local affine base", sga "6 X 7.17" "special case"]
private theorem exists_isAdicComplete_isAlgClosed_residueField_ker_eq
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (P : Ideal A) [P.IsPrime] :
    ∃ (C : Type u) (hCring : CommRing C) (hCdom : IsDomain C)
      (hCdvr : IsDiscreteValuationRing C),
      let := hCring; let := hCdom; let := hCdvr
      IsAdicComplete (maximalIdeal C) C ∧ IsAlgClosed (ResidueField C) ∧
        ∃ φ : A →+* C, IsLocalHom φ ∧ ∀ a, φ a = 0 ↔ a ∈ P := by
  classical
  by_cases hP : P = maximalIdeal A
  · subst hP
    let k := AlgebraicClosure (ResidueField A)
    let C := PowerSeries k
    have hcomplete : IsAdicComplete (maximalIdeal C) C := by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance
    have halg : IsAlgClosed (ResidueField C) :=
      IsAlgClosed.of_ringEquiv k _ PowerSeries.residueFieldOfPowerSeries.symm
    let φ : A →+* C :=
      PowerSeries.C.comp ((algebraMap (ResidueField A) k).comp (residue A))
    refine ⟨C, inferInstance, inferInstance, inferInstance, hcomplete, halg, φ, inferInstance, ?_⟩
    intro a
    change PowerSeries.C (algebraMap (ResidueField A) k (residue A a)) = 0 ↔ _
    rw [map_eq_zero_iff PowerSeries.C PowerSeries.C_injective,
      map_eq_zero_iff _ (RingHom.injective _), residue_eq_zero_iff]
  · let : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
    let : IsNoetherianRing (A ⧸ P) := Ideal.Quotient.isNoetherianRing P
    let : IsLocalHom (Ideal.Quotient.mk P) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    let : IsLocalRing (A ⧸ P) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    have hnotfield : ¬ IsField (A ⧸ P) := fun hfield =>
      hP (IsLocalRing.eq_maximalIdeal
        ((Ideal.Quotient.maximal_ideal_iff_isField_quotient P).2 hfield))
    obtain ⟨B, hBdvr, hBloc⟩ :=
      exists_isDiscreteValuationRing_subalgebra_fractionRing (A ⧸ P) hnotfield
    let : IsDiscreteValuationRing B := hBdvr
    obtain ⟨C, hCring, hCdom, hCdvr, hCcomplete, hCres, ⟨ψ, hψloc, hψinj⟩, -⟩ :=
      exists_isAdicComplete_isAlgClosed_residueField_extension (B : Type u)
    let := hCring; let := hCdom; let := hCdvr
    refine ⟨C, hCring, hCdom, hCdvr, hCcomplete, hCres, ?_⟩
    have hDB : Function.Injective (algebraMap (A ⧸ P) B) := fun x y h => by
      simpa using congrArg Subtype.val h
    refine ⟨(ψ.comp (algebraMap (A ⧸ P) B)).comp (Ideal.Quotient.mk P), ?_, ?_⟩
    · let : IsLocalHom (algebraMap (A ⧸ P) B) := hBloc
      let : IsLocalHom ψ := hψloc
      exact RingHom.isLocalHom_comp _ _
    · intro a
      constructor
      · intro ha
        refine Ideal.Quotient.eq_zero_iff_mem.mp (hDB (hψinj ?_))
        simpa using ha
      · intro ha
        have hq : Ideal.Quotient.mk P a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
        simp [RingHom.comp_apply, hq]


/-! ### Connectedness, and base change along isomorphisms and composites -/

/-- Base change of finite étale covers along an isomorphism is an equivalence. -/
private theorem isEquivalence_finiteEtaleBaseChange_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (finiteEtaleBaseChange e.hom).IsEquivalence :=
  (CategoryTheory.Equivalence.mk (finiteEtaleBaseChange e.hom) (finiteEtaleBaseChange e.inv)
    (finiteEtaleBaseChangeId.symm ≪≫
      finiteEtaleBaseChangeComp e.inv e.hom (𝟙 Y) e.inv_hom_id.symm)
    ((finiteEtaleBaseChangeComp e.hom e.inv (𝟙 X) e.hom_inv_id.symm).symm ≪≫
      finiteEtaleBaseChangeId)).isEquivalence_functor

/-- Base change along a composite of two morphisms along which base change is an equivalence is an
equivalence. -/
private theorem isEquivalence_finiteEtaleBaseChange_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (finiteEtaleBaseChange f).IsEquivalence)
    (hg : (finiteEtaleBaseChange g).IsEquivalence) :
    (finiteEtaleBaseChange (f ≫ g)).IsEquivalence := by
  have := hf
  have := hg
  exact Functor.isEquivalence_of_iso (finiteEtaleBaseChangeComp f g).symm

/-- Base change cancels on the right: if it is an equivalence along `f` and along `f ≫ g`, then it
is an equivalence along `g`. -/
private theorem isEquivalence_finiteEtaleBaseChange_cancel_right {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (finiteEtaleBaseChange f).IsEquivalence)
    (hfg : (finiteEtaleBaseChange (f ≫ g)).IsEquivalence) :
    (finiteEtaleBaseChange g).IsEquivalence := by
  have := hf
  have := hfg
  have : (finiteEtaleBaseChange g ⋙ finiteEtaleBaseChange f).IsEquivalence :=
    Functor.isEquivalence_of_iso (finiteEtaleBaseChangeComp f g)
  exact Functor.isEquivalence_of_comp_right (finiteEtaleBaseChange g) (finiteEtaleBaseChange f)

/-! ### The closed geometric point of a local ring with algebraically closed residue field -/

/-- The geometric point of `Spec R` at the closed point of a local ring `R` whose residue field is
algebraically closed. -/
private def closedGeometricPoint (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAlgClosed (ResidueField R)] : GeometricPoint (Spec (.of R)) where
  residueField := ResidueField R
  hom := Spec.map (CommRingCat.ofHom (residue R))

/-- The closed geometric point lies over the closed point. -/
private theorem closedGeometricPoint_liesOver (R : Type u) [CommRing R] [IsLocalRing R]
    [IsAlgClosed (ResidueField R)] :
    (closedGeometricPoint R).hom (closedPoint (closedGeometricPoint R).residueField) =
      closedPoint R :=
  IsLocalRing.comap_closedPoint (residue R)

/-- The image of the generic point of the spectrum of a domain under a ring homomorphism is the
prime cut out by its kernel. -/
private theorem specMap_genericPoint_eq_of_ker {A C : Type u} [CommRing A] [CommRing C]
    [IsDomain C] (φ : A →+* C) (P : Ideal A) [P.IsPrime] (hker : ∀ a, φ a = 0 ↔ a ∈ P) :
    Spec.map (CommRingCat.ofHom φ) (genericPoint (Spec (.of C))) = ⟨P, inferInstance⟩ := by
  rw [genericPoint_eq_bot_of_affine (CommRingCat.of C)]
  apply PrimeSpectrum.ext
  ext a
  change a ∈ (PrimeSpectrum.comap φ (⊥ : PrimeSpectrum C)).asIdeal ↔ a ∈ P
  rw [PrimeSpectrum.comap_asIdeal]
  simp [Ideal.mem_comap, hker]

/-! ### Geometric fibres as pullbacks -/

/-- The map from a geometric fibre into a base change through which the geometric point factors
exhibits the geometric fibre as a pullback of the base change. -/
private theorem isPullback_fiberOverGeometricPointMap {X S T : Scheme.{u}}
    (f : X ⟶ S) (s : GeometricPoint S) (g : T ⟶ S) (p : s.source ⟶ T) (hp : p ≫ g = s.hom) :
    IsPullback (fiberOverGeometricPointMap f s g p hp)
      (pullback.snd f s.hom) (pullback.snd f g) p := by
  have h₁ : fiberOverGeometricPointMap f s g p hp ≫ pullback.fst f g = pullback.fst f s.hom :=
    pullback.lift_fst _ _ _
  have h₂ : fiberOverGeometricPointMap f s g p hp ≫ pullback.snd f g
      = pullback.snd f s.hom ≫ p := pullback.lift_snd _ _ _
  refine IsPullback.of_right ?_ h₂ (IsPullback.of_hasPullback f g)
  rw [h₁, hp]
  exact IsPullback.of_hasPullback f s.hom

/-- **Stacks Project, Tag 0A49** in the form used here: for `f` proper, base change along the map
`X_t ⟶ X_{s̄}` of geometric fibres induced by a morphism `t.source ⟶ s.source` over `S` is an
equivalence on finite étale covers. This is base change along an extension of algebraically closed
fields, after identifying `X_t` with the fibre product of `X_{s̄}` and `t.source`. -/
private theorem isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (h0A48 : ProperHenselianFiniteEtaleEquivalence.{u})
    (s t : GeometricPoint S) (q : t.source ⟶ s.source) (hq : q ≫ s.hom = t.hom) :
    (finiteEtaleBaseChange (fiberOverGeometricPointMap f t s.hom q hq)).IsEquivalence := by
  have hpb : IsPullback (fiberOverGeometricPointMap f t s.hom q hq) (pullback.snd f t.hom)
      (pullback.snd f s.hom) q := isPullback_fiberOverGeometricPointMap f t s.hom q hq
  rw [← hpb.isoPullback_hom_fst]
  refine isEquivalence_finiteEtaleBaseChange_comp _ _
    (isEquivalence_finiteEtaleBaseChange_of_iso hpb.isoPullback) ?_
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of s.residueField ⟶ .of t.residueField,
      Spec.map φ = q := ⟨Spec.preimage q, Spec.map_preimage q⟩
  let : Algebra s.residueField t.residueField := φ.hom.toAlgebra
  exact isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_properHenselian_of_isAlgClosed
    (pullback.snd f s.hom) h0A48

/-- Two geometric fibres with the same image in `S` receive a common geometric fibre, along which
base change is an equivalence on either side. -/
private theorem exists_common_geometricFibre {X S U V : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    [GeometricallyConnected f] (h0A48 : ProperHenselianFiniteEtaleEquivalence.{u})
    (s t : GeometricPoint S) (hst : s.hom default = t.hom default)
    (i : U ⟶ X) (p : U ⟶ s.source) (hi : IsPullback i p f s.hom)
    (j : V ⟶ X) (q : V ⟶ t.source) (hj : IsPullback j q f t.hom) :
    ∃ (W : Scheme.{u}) (_ : ConnectedSpace W) (a : W ⟶ U) (b : W ⟶ V),
      (finiteEtaleBaseChange a).IsEquivalence ∧
        (finiteEtaleBaseChange b).IsEquivalence ∧ a ≫ i = b ≫ j := by
  let w := (Scheme.Pullback.exists_preimage_pullback
    (f := s.hom) (g := t.hom) default default hst).choose
  let v₀ := GeometricPoint.ofPoint (pullback s.hom t.hom : Scheme.{u}) w
  let q₁ := v₀.hom ≫ pullback.fst s.hom t.hom
  let q₂ := v₀.hom ≫ pullback.snd s.hom t.hom
  let v : GeometricPoint S := { residueField := v₀.residueField, hom := q₁ ≫ s.hom }
  have hq₂ : q₂ ≫ t.hom = v.hom := by
    dsimp only [v, q₁, q₂]
    rw [Category.assoc, Category.assoc, pullback.condition]
  let a₀ := fiberOverGeometricPointMap f v s.hom q₁ rfl
  let b₀ := fiberOverGeometricPointMap f v t.hom q₂ hq₂
  refine ⟨fiberOverGeometricPoint f v, connectedSpace_fiberOverGeometricPoint f v,
    a₀ ≫ hi.isoPullback.inv, b₀ ≫ hj.isoPullback.inv, ?_, ?_, ?_⟩
  · exact isEquivalence_finiteEtaleBaseChange_comp _ _
      (isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap f h0A48 s v q₁ rfl)
      (isEquivalence_finiteEtaleBaseChange_of_iso hi.isoPullback.symm)
  · exact isEquivalence_finiteEtaleBaseChange_comp _ _
      (isEquivalence_finiteEtaleBaseChange_fiberOverGeometricPointMap f h0A48 t v q₂ hq₂)
      (isEquivalence_finiteEtaleBaseChange_of_iso hj.isoPullback.symm)
  · rw [Category.assoc, Category.assoc, hi.isoPullback_inv_fst, hj.isoPullback_inv_fst]
    change pullback.lift _ _ _ ≫ pullback.fst f s.hom
      = pullback.lift _ _ _ ≫ pullback.fst f t.hom
    rw [pullback.lift_fst, pullback.lift_fst]

/-- Being an equivalence on finite étale covers transports between the inclusions of two geometric
fibres of a proper morphism with geometrically connected fibres whose geometric points have the
same image. -/
private theorem isEquivalence_finiteEtaleBaseChange_of_isPullback_liesOver_eq
    {X S U V : Scheme.{u}} (f : X ⟶ S) [IsProper f] [GeometricallyConnected f]
    (h0A48 : ProperHenselianFiniteEtaleEquivalence.{u})
    (s t : GeometricPoint S) (hst : s.hom default = t.hom default)
    (i : U ⟶ X) (p : U ⟶ s.source) (hi : IsPullback i p f s.hom)
    (j : V ⟶ X) (q : V ⟶ t.source) (hj : IsPullback j q f t.hom)
    (he : (finiteEtaleBaseChange i).IsEquivalence) :
    (finiteEtaleBaseChange j).IsEquivalence := by
  obtain ⟨W, _, a, b, ha, hb, hab⟩ :=
    exists_common_geometricFibre f h0A48 s t hst i p hi j q hj
  refine isEquivalence_finiteEtaleBaseChange_cancel_right b j hb ?_
  rw [← hab]
  exact isEquivalence_finiteEtaleBaseChange_comp a i ha he

/-! ### A henselian local ring with algebraically closed residue field is its own strict
henselization -/

/-- A strict henselization of a Noetherian local ring is Noetherian. This is
`IsLocalRing.isNoetherianRing_of_isHenselization` read through the structure
`Stacks.StrictHenselization.IsStrictHenselization`, whose residue-field datum is keyed on
`(maximalIdeal R).ResidueField` rather than on `IsLocalRing.ResidueField R`. -/
@[ega "IV 18.8.8" "(iv), sufficiency", sga "4 VIII 4.4"]
private theorem isNoetherianRing_of_isStrictHenselization
    (R A κsep : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Field κsep] [Algebra (maximalIdeal R).ResidueField κsep]
    [IsSepClosure (maximalIdeal R).ResidueField κsep]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization R κsep A) : IsNoetherianRing A := by
  let : Algebra (ResidueField R) κsep :=
    ((algebraMap (maximalIdeal R).ResidueField κsep).comp
      (algebraMap (ResidueField R) (maximalIdeal R).ResidueField)).toAlgebra
  let : IsLocalHom (algebraMap R A) := hsh.isLocalHom
  let upA := residueFieldEquivMaximalIdealResidueField A
  have key : ∀ x : R,
      (hsh.residueFieldEquiv.trans upA.symm)
          (algebraMap (ResidueField R) κsep (residue R x))
        = residue A (algebraMap R A x) := by
    intro x
    apply upA.injective
    have hstep : upA ((hsh.residueFieldEquiv.trans upA.symm)
        (algebraMap (ResidueField R) κsep (residue R x)))
        = hsh.residueFieldEquiv (algebraMap (ResidueField R) κsep (residue R x)) :=
      upA.apply_symm_apply _
    rw [hstep]
    have hval : algebraMap (ResidueField R) κsep (residue R x)
        = algebraMap (maximalIdeal R).ResidueField κsep (algebraMap R
            (maximalIdeal R).ResidueField x) := by
      rw [← AlgebraicGeometry.algebraMap_residueField_residue R x]
      rfl
    have hcomp := RingHom.congr_fun hsh.residueFieldEquiv_comp
      (algebraMap R (maximalIdeal R).ResidueField x)
    simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom] at hcomp
    rw [hval, hcomp,
      Ideal.ResidueField.map_algebraMap (maximalIdeal R) (maximalIdeal A) (algebraMap R A)
        (IsLocalRing.maximalIdeal_comap (algebraMap R A)).symm x]
    exact (AlgebraicGeometry.algebraMap_residueField_residue A (algebraMap R A x)).symm
  let : IsLocalRing.IsHenselization R κsep A :=
    IsLocalRing.IsHenselization.of_ind_etale hsh.henselian
      ((CommAlgCat.etale R).ind.prop_of_iso
        (CommAlgCat.isoMk (ULift.algEquiv : ULift.{u} A ≃ₐ[R] A))
        hsh.isFilteredColimitEtale)
      ⟨hsh.residueFieldEquiv.trans upA.symm, key⟩
  exact IsLocalRing.isNoetherianRing_of_isHenselization (A := R) κsep

/-- A henselian local ring with algebraically closed residue field is a strict henselization of
any local ring isomorphic to it: the structure map is étale because it is bijective, and the
residue field is already separably closed. -/
private def isStrictHenselization_of_ringEquiv (R A : Type u) [CommRing R] [IsLocalRing R]
    [CommRing A] [HenselianLocalRing A] [IsAlgClosed (ResidueField A)] (e : R ≃+* A) :
    let : Algebra R A := e.toRingHom.toAlgebra
    Stacks.StrictHenselization.IsStrictHenselization R
      (SeparableClosure (maximalIdeal R).ResidueField) A := by
  let : Algebra R A := e.toRingHom.toAlgebra
  have : IsLocalHom (algebraMap R A) := IsLocalHom.of_surjective _ e.surjective
  let κ := (maximalIdeal R).ResidueField
  let L := SeparableClosure κ
  let er : κ ≃+* (maximalIdeal A).ResidueField :=
    Ideal.residueFieldRingEquiv _ _ e (maximalIdeal_comap e.toRingHom).symm
  have : IsAlgClosed (maximalIdeal A).ResidueField :=
    IsAlgClosed.of_ringEquiv (ResidueField A) _ (residueFieldEquivMaximalIdealResidueField A)
  have : IsAlgClosed κ := IsAlgClosed.of_ringEquiv _ _ er.symm
  let ek : κ ≃+* L :=
    RingEquiv.ofBijective (algebraMap κ L) (IsSepClosed.algebraMap_bijective κ L)
  refine { isLocalHom := inferInstance
           henselian := inferInstance
           sepClosed := inferInstance
           isFilteredColimitEtale := ?_
           maximalIdeal_map := ?_
           residueFieldEquiv := ek.symm.trans er
           residueFieldEquiv_comp := ?_ }
  · apply ObjectProperty.le_ind (CommAlgCat.etale R)
    change Algebra.Etale R (ULift.{u} A)
    apply RingHom.etale_algebraMap.mp
    apply RingHom.Etale.of_bijective
    exact ⟨fun a b h => e.injective (congrArg ULift.down h),
      fun y => ⟨e.symm y.down, congrArg ULift.up (e.apply_symm_apply _)⟩⟩
  · rw [← maximalIdeal_comap e.toRingHom]
    exact Ideal.map_comap_of_surjective _ e.surjective _
  · apply RingHom.ext
    intro y
    change er (ek.symm (ek y)) = _
    rw [ek.symm_apply_apply]
    rfl

/-- The stalk of `Spec R` at the closed geometric point of a henselian local ring `R` with
algebraically closed residue field has `R` itself as a strict henselization, by the structure
morphism which is inverse to `Spec R ⟶ Spec 𝒪_{Spec R, 𝔪}`. -/
private theorem exists_isStrictHenselization_stalk_closedGeometricPoint
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (ResidueField R)] :
    let o := closedGeometricPoint R
    let z := o.hom (closedPoint o.residueField)
    let R₀ := (Spec (.of R)).presheaf.stalk z
    ∃ hAlg : Algebra R₀ R,
      let : Algebra R₀ R := hAlg
      Nonempty (Stacks.StrictHenselization.IsStrictHenselization R₀
        (SeparableClosure (maximalIdeal R₀).ResidueField) R) ∧
      Spec.map (CommRingCat.ofHom (algebraMap R₀ R)) ≫
        (Spec (.of R)).fromSpecStalk z = 𝟙 _ := by
  dsimp only
  generalize hz : (closedGeometricPoint R).hom
    (closedPoint (closedGeometricPoint R).residueField) = z
  have hz' : z = closedPoint R := hz.symm.trans (closedGeometricPoint_liesOver R)
  subst hz'
  let : IsLocalRing ((Spec (.of R)).presheaf.stalk (closedPoint R : Spec (.of R))) :=
    (Spec (.of R)).toLocallyRingedSpace.isLocalRing _
  let e := stalkClosedPointIso (CommRingCat.of R)
  let er := e.commRingCatIsoToRingEquiv
  let : Algebra ((Spec (.of R)).presheaf.stalk (closedPoint R)) R := er.toRingHom.toAlgebra
  refine ⟨inferInstance, ⟨isStrictHenselization_of_ringEquiv _ _ er⟩, ?_⟩
  rw [← Spec_stalkClosedPointIso]
  change Spec.map e.hom ≫ Spec.map e.inv = _
  rw [← Spec.map_comp, e.inv_hom_id, Spec.map_id]

/-! ### Transporting a factorization of a specialization map -/

/-- A factorization `f ≫ g` of a morphism, with base change along `f` an equivalence on finite
étale covers, lets the map induced by `g` be compared with the map induced by `f ≫ g`: there are
isomorphisms of fundamental groups on the source and on the target intertwining the two. -/
private theorem exists_etaleFundamentalGroupEquiv_map_factor {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]
    (fXY : X ⟶ Y) (gYZ : Y ⟶ Z) (hf : (finiteEtaleBaseChange fXY).IsEquivalence)
    (x : GeometricPoint X) (y : GeometricPoint Y) :
    ∃ (e : EtaleFundamentalGroup X x ≃ₜ* EtaleFundamentalGroup Y y)
      (d : EtaleFundamentalGroup Z (x.map (fXY ≫ gYZ)) ≃ₜ*
        EtaleFundamentalGroup Z (y.map gYZ)),
      ∀ σ, etaleFundamentalGroupMap gYZ y (e σ)
        = d (etaleFundamentalGroupMap (fXY ≫ gYZ) x σ) := by
  have := hf
  let t := (nonempty_finiteEtaleFiberFunctorIso Y (x.map fXY) y).some
  refine ⟨(etaleFundamentalGroupContinuousMulEquivOfIsEquivalence fXY x).trans
      (etaleFundamentalGroupContinuousMulEquiv t),
    etaleFundamentalGroupContinuousMulEquiv
      (fiberFunctorMapCompIso fXY gYZ x ≪≫ fiberFunctorTransportIso gYZ t), fun σ ↦ ?_⟩
  change etaleFundamentalGroupMap gYZ y
      (etaleFundamentalGroupMulEquiv t
        (etaleFundamentalGroupMulEquivOfIsEquivalence fXY x σ))
    = etaleFundamentalGroupMulEquiv
        (fiberFunctorMapCompIso fXY gYZ x ≪≫ fiberFunctorTransportIso gYZ t)
        (etaleFundamentalGroupMap (fXY ≫ gYZ) x σ)
  rw [etaleFundamentalGroupMulEquivOfIsEquivalence_apply,
    ← etaleFundamentalGroupMulEquiv_transportIso gYZ t,
    etaleFundamentalGroupMulEquiv_trans, etaleFundamentalGroupMulEquiv_mapCompIso]

/-- The previous lemma for a morphism which is merely *equal* to a composite. -/
private theorem exists_etaleFundamentalGroupEquiv_map_factor_of_eq {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]
    (fXY : X ⟶ Y) (gYZ : Y ⟶ Z) (hXZ : X ⟶ Z) (w : fXY ≫ gYZ = hXZ)
    (hf : (finiteEtaleBaseChange fXY).IsEquivalence)
    (x : GeometricPoint X) (y : GeometricPoint Y) :
    ∃ (e : EtaleFundamentalGroup X x ≃ₜ* EtaleFundamentalGroup Y y)
      (d : EtaleFundamentalGroup Z (x.map hXZ) ≃ₜ* EtaleFundamentalGroup Z (y.map gYZ)),
      ∀ σ, etaleFundamentalGroupMap gYZ y (e σ)
        = d (etaleFundamentalGroupMap hXZ x σ) := by
  subst w
  exact exists_etaleFundamentalGroupEquiv_map_factor fXY gYZ hf x y

/-- The isomorphism of fundamental groups along a base change equivalence moves between `σ ↦ τ`
under the induced map and `τ ↦ σ` under its inverse. -/
private theorem etaleFundamentalGroupMap_eq_iff_eq_symm {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X)
    [(finiteEtaleBaseChange f).IsEquivalence]
    (σ : EtaleFundamentalGroup X x) (τ : EtaleFundamentalGroup Y (x.map f)) :
    etaleFundamentalGroupMap f x σ = τ ↔
      σ = (etaleFundamentalGroupMulEquivOfIsEquivalence f x).symm τ :=
  (etaleFundamentalGroupMulEquivOfIsEquivalence f x).eq_symm_apply.symm

/-- Two continuous homomorphisms given by factorizations as in the definition of a specialization
map are isomorphic, provided the two factorizations are compared by a third one through which base
change is an equivalence on either side. -/
private theorem exists_intertwining_of_factorizations
    {U V A U' V' B W : Scheme.{u}}
    [ConnectedSpace U] [ConnectedSpace V] [ConnectedSpace A]
    [ConnectedSpace U'] [ConnectedSpace V'] [ConnectedSpace B] [ConnectedSpace W]
    (i : U ⟶ A) (i' : U' ⟶ B) (k : B ⟶ A)
    (a : W ⟶ U) (b : W ⟶ U') (w : a ≫ i = b ≫ (i' ≫ k))
    (ha : (finiteEtaleBaseChange a).IsEquivalence)
    (hb : (finiteEtaleBaseChange b).IsEquivalence)
    (hk : (finiteEtaleBaseChange k).IsEquivalence)
    (x : GeometricPoint U) (y : GeometricPoint V)
    (x' : GeometricPoint U') (y' : GeometricPoint V') (z : GeometricPoint W)
    (d : EtaleFundamentalGroup A (x.map i) ≃ₜ* EtaleFundamentalGroup V y)
    (d' : EtaleFundamentalGroup B (x'.map i') ≃ₜ* EtaleFundamentalGroup V' y')
    (sp : EtaleFundamentalGroup U x →ₜ* EtaleFundamentalGroup V y)
    (sp' : EtaleFundamentalGroup U' x' →ₜ* EtaleFundamentalGroup V' y')
    (hsp : ∀ γ, sp γ = d (etaleFundamentalGroupMap i x γ))
    (hsp' : ∀ γ, sp' γ = d' (etaleFundamentalGroupMap i' x' γ)) :
    ∃ (e : EtaleFundamentalGroup U x ≃ₜ* EtaleFundamentalGroup U' x')
      (e' : EtaleFundamentalGroup V y ≃ₜ* EtaleFundamentalGroup V' y'),
      ∀ γ, e' (sp γ) = sp' (e γ) := by
  have := hk
  obtain ⟨ea, da, hda⟩ := exists_etaleFundamentalGroupEquiv_map_factor a i ha z x
  obtain ⟨eb, db, hdb⟩ :=
    exists_etaleFundamentalGroupEquiv_map_factor_of_eq b (i' ≫ k) (a ≫ i) w.symm hb z x'
  let ek := etaleFundamentalGroupContinuousMulEquivOfIsEquivalence k (x'.map i')
  let ck := etaleFundamentalGroupContinuousMulEquiv (fiberFunctorMapCompIso i' k x')
  let D := da.trans d
  let D' := db.trans (ck.trans (ek.symm.trans d'))
  have hD (γ : EtaleFundamentalGroup W z) :
      sp (ea γ) = D (etaleFundamentalGroupMap (a ≫ i) z γ) := by
    rw [hsp, hda]
    rfl
  have hD' (γ : EtaleFundamentalGroup W z) :
      sp' (eb γ) = D' (etaleFundamentalGroupMap (a ≫ i) z γ) := by
    rw [hsp']
    change d' _ = d' (ek.symm (ck (db _)))
    refine congrArg d' (ek.injective ?_)
    rw [ContinuousMulEquiv.apply_symm_apply]
    change etaleFundamentalGroupMap k (x'.map i') (etaleFundamentalGroupMap i' x' (eb γ))
      = etaleFundamentalGroupMulEquiv (fiberFunctorMapCompIso i' k x')
          (db (etaleFundamentalGroupMap (a ≫ i) z γ))
    rw [← hdb, etaleFundamentalGroupMulEquiv_mapCompIso]
  refine ⟨ea.symm.trans eb, D.symm.trans D', fun γ ↦ ?_⟩
  obtain ⟨δ, rfl⟩ := ea.surjective γ
  change D' (D.symm (sp (ea δ))) = sp' (eb (ea.symm (ea δ)))
  rw [ContinuousMulEquiv.symm_apply_apply, hD, ContinuousMulEquiv.symm_apply_apply, hD']

/-! ### Specialization maps over a henselian local ring -/

/-- Over a henselian local ring `R` with algebraically closed residue field, the ring itself is
the strict henselization appearing in the definition of a specialization map, so the trivial
factorization of the two geometric points through `Spec R` already witnesses that a continuous
homomorphism is a specialization map. -/
private theorem isSpecializationMap_of_identity_factorization
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsAlgClosed (ResidueField R)]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of R)) [IsProper fY] [GeometricallyConnected fY]
    [ConnectedSpace (pullback fY (𝟙 (Spec (.of R))) : Scheme.{u})]
    (η : GeometricPoint (Spec (.of R)))
    (yη : GeometricPoint (fiberOverGeometricPoint fY η))
    (yo : GeometricPoint (fiberOverGeometricPoint fY (closedGeometricPoint R)))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint fY η) yη →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint fY (closedGeometricPoint R)) yo)
    (hi : (finiteEtaleBaseChange (fiberOverGeometricPointMap fY (closedGeometricPoint R) (𝟙 _)
      (closedGeometricPoint R).hom (Category.comp_id _))).IsEquivalence)
    (t : finiteEtaleFiberFunctor
        (yη.map (fiberOverGeometricPointMap fY η (𝟙 _) η.hom (Category.comp_id _))) ≅
      finiteEtaleFiberFunctor (yo.map (fiberOverGeometricPointMap fY (closedGeometricPoint R)
        (𝟙 _) (closedGeometricPoint R).hom (Category.comp_id _))))
    (hform : ∀ γ, etaleFundamentalGroupMap
        (fiberOverGeometricPointMap fY (closedGeometricPoint R) (𝟙 _)
          (closedGeometricPoint R).hom (Category.comp_id _)) yo (sp γ)
      = etaleFundamentalGroupMulEquiv t (etaleFundamentalGroupMap
          (fiberOverGeometricPointMap fY η (𝟙 _) η.hom (Category.comp_id _)) yη γ)) :
    IsSpecializationMap fY η (closedGeometricPoint R) yη yo sp := by
  obtain ⟨hAlg, hsh, hg⟩ := exists_isStrictHenselization_stalk_closedGeometricPoint R
  let := hAlg
  let Q (w : Spec (.of R) ⟶ Spec (.of R)) : Prop :=
    ∃ (p₁ : η.source ⟶ Spec (.of R)) (hp₁ : p₁ ≫ w = η.hom)
      (p₂ : (closedGeometricPoint R).source ⟶ Spec (.of R))
      (hp₂ : p₂ ≫ w = (closedGeometricPoint R).hom),
      p₂ (closedPoint (closedGeometricPoint R).residueField) = closedPoint R ∧
      ∃ (hYw : ConnectedSpace (pullback fY w : Scheme.{u}))
        (_ : (finiteEtaleBaseChange (fiberOverGeometricPointMap fY
          (closedGeometricPoint R) w p₂ hp₂)).IsEquivalence),
        let : ConnectedSpace (pullback fY w : Scheme.{u}) := hYw
        ∃ tw : finiteEtaleFiberFunctor (yη.map (fiberOverGeometricPointMap fY η w p₁ hp₁)) ≅
            finiteEtaleFiberFunctor (yo.map (fiberOverGeometricPointMap fY
              (closedGeometricPoint R) w p₂ hp₂)),
          ∀ γ, etaleFundamentalGroupMap (fiberOverGeometricPointMap fY
              (closedGeometricPoint R) w p₂ hp₂) yo (sp γ)
            = etaleFundamentalGroupMulEquiv tw (etaleFundamentalGroupMap
                (fiberOverGeometricPointMap fY η w p₁ hp₁) yη γ)
  have hQ : Q (𝟙 (Spec (.of R))) :=
    ⟨η.hom, Category.comp_id _, (closedGeometricPoint R).hom, Category.comp_id _,
      closedGeometricPoint_liesOver R, inferInstance, hi, t, hform⟩
  exact ⟨R, inferInstance, inferInstance, hAlg, hsh, (congrArg Q hg).mpr hQ⟩

/-! ### Tag 0C0N -/

/-- **Stacks Project, Tag 0C0N.** Let `f : X ⟶ S` be a proper morphism with geometrically
connected fibres over a Noetherian scheme, let `s'` and `s` be geometric points of `S`, and let
`sp : π₁(X_{s'}) → π₁(X_s)` be a specialization map. Then there are a complete — in particular
strictly henselian — discrete valuation ring `R` with algebraically closed residue field, a
morphism `r : Spec R ⟶ S` carrying the generic point of `Spec R` to the image of `s'` and its
closed point to the image of `s`, and a specialization map
`sp_R : π₁((X_R)_{η̄}) → π₁((X_R)_{ō})` of the base change `X_R ⟶ Spec R` from the generic to the
closed point, such that `sp` and `sp_R` are intertwined by isomorphisms of topological groups on
the source and on the target. -/
@[stacks 0C0N "the whole statement, with the same one input this library cannot prove carried as \
the hypothesis `h0A48`: `ProperHenselianFiniteEtaleEquivalence`, Tag 0A48 for a proper — not \
merely finite — scheme over a henselian local ring, whose remaining content is Grothendieck \
existence together with Artin approximation (see \
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleAlgClosedExtension`). It is used \
exactly twice, for Tag 0A49 through \
`isEquivalence_finiteEtaleBaseChange_specMap_algebraMap_of_properHenselian_of_isAlgClosed` and \
for the closed geometric fibre of `X_R ⟶ Spec R`; it is the same datum that is already part of \
`AlgebraicGeometry.IsSpecializationMap`, so it constrains none of the data quantified over. \
Everything else is proved here: the discrete valuation ring (Tags 00PH, 0ARL and 0AP1), that the \
strict henselization of the stalk is Noetherian, the two factorizations of the geometric points, \
and the base-point bookkeeping. `sp_R` is produced as a specialization map in the sense of \
`AlgebraicGeometry.IsSpecializationMap`, and `R` is strictly henselian in the strong sense that \
its residue field is algebraically closed."]
theorem exists_isSpecializationMap_isomorphic_over_isDiscreteValuationRing
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [GeometricallyConnected f] [IsNoetherian S]
    (s' s : GeometricPoint S)
    (x' : GeometricPoint (fiberOverGeometricPoint f s'))
    (x : GeometricPoint (fiberOverGeometricPoint f s))
    (sp : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint f s) x)
    (hsp : IsSpecializationMap f s' s x' x sp)
    (h0A48 : ProperHenselianFiniteEtaleEquivalence.{u}) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : HenselianLocalRing R) (_ : IsAlgClosed (ResidueField R))
      (r : Spec (.of R) ⟶ S) (η o : GeometricPoint (Spec (.of R)))
      (yη : GeometricPoint (fiberOverGeometricPoint (pullback.snd f r) η))
      (yo : GeometricPoint (fiberOverGeometricPoint (pullback.snd f r) o))
      (spR : EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) η) yη →ₜ*
        EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) o) yo),
      η.hom default = genericPoint (Spec (.of R)) ∧
      o.hom default = closedPoint R ∧
      r (η.hom default) = s'.hom default ∧
      r (o.hom default) = s.hom default ∧
      IsSpecializationMap (pullback.snd f r) η o yη yo spR ∧
      ∃ (eη : EtaleFundamentalGroup (fiberOverGeometricPoint f s') x' ≃ₜ*
            EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) η) yη)
        (eo : EtaleFundamentalGroup (fiberOverGeometricPoint f s) x ≃ₜ*
            EtaleFundamentalGroup (fiberOverGeometricPoint (pullback.snd f r) o) yo),
        ∀ γ, eo (sp γ) = spR (eη γ) := by
  classical
  simp only [IsSpecializationMap] at hsp
  obtain ⟨A, hAring, hAloc, hAalg, ⟨hstrict⟩, p', hp', p, hp, hclosed, hXA, hi, t, hform⟩ := hsp
  let := hAring
  let := hAloc
  let := hAalg
  let z : S := s.hom (closedPoint s.residueField)
  let : IsNoetherianRing A :=
    isNoetherianRing_of_isStrictHenselization (S.presheaf.stalk z) A
      (SeparableClosure (maximalIdeal (S.presheaf.stalk z)).ResidueField) hstrict
  let gA : Spec (.of A) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk z) A)) ≫ S.fromSpecStalk z
  let P : Ideal A := (p' default).asIdeal
  have : P.IsPrime := (p' default).isPrime
  obtain ⟨C, hCring, hCdom, hCdvr, hCcomplete, hCres, φ, hφloc, hφker⟩ :=
    exists_isAdicComplete_isAlgClosed_residueField_ker_eq A P
  let := hCring
  let := hCdom
  let := hCdvr
  let : IsAdicComplete (maximalIdeal C) C := hCcomplete
  let : IsAlgClosed (ResidueField C) := hCres
  let : HenselianLocalRing C := henselianLocalRing_of_isAdicComplete_maximalIdeal C
  let : IsLocalHom φ := hφloc
  refine ⟨C, hCring, hCdom, hCdvr, inferInstance, hCres, ?_⟩
  let q : Spec (.of C) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom φ)
  let r : Spec (.of C) ⟶ S := q ≫ gA
  let K := AlgebraicClosure (FractionRing C)
  let η : GeometricPoint (Spec (.of C)) :=
    { residueField := K, hom := Spec.map (CommRingCat.ofHom (algebraMap C K)) }
  let o : GeometricPoint (Spec (.of C)) := closedGeometricPoint C
  have hCK : Function.Injective (algebraMap C K) := by
    intro a b hab
    refine IsFractionRing.injective C (FractionRing C) ((algebraMap (FractionRing C) K).injective
      (show (algebraMap (FractionRing C) K) (algebraMap C (FractionRing C) a)
        = (algebraMap (FractionRing C) K) (algebraMap C (FractionRing C) b) from hab))
  have hηgeneric : η.hom default = genericPoint (Spec (.of C)) := by
    have hdef : (default : Spec (.of K)) = genericPoint (Spec (.of K)) := Subsingleton.elim _ _
    change Spec.map (CommRingCat.ofHom (algebraMap C K)) (default : Spec (.of K)) = _
    rw [hdef, genericPoint_eq_bot_of_affine (CommRingCat.of C)]
    refine specMap_genericPoint_eq_of_ker (algebraMap C K) (⊥ : Ideal C) fun a ↦ ?_
    constructor
    · intro ha
      exact hCK (ha.trans (map_zero (algebraMap C K)).symm)
    · intro ha
      change a = 0 at ha
      simp [ha]
  have hoclosed : o.hom default = closedPoint C :=
    (congrArg o.hom (Subsingleton.elim _ _)).trans (closedGeometricPoint_liesOver C)
  have hPpoint : p' default = ⟨P, inferInstance⟩ := PrimeSpectrum.ext rfl
  have hηA : q (genericPoint (Spec (.of C))) = p' default :=
    (specMap_genericPoint_eq_of_ker φ P hφker).trans hPpoint.symm
  have : ConnectedSpace (pullback f r : Scheme.{u}) :=
    connectedSpace_pullback_spec_of_isProper f C r
  let fC := pullback.snd f r
  have : IsProper fC := inferInstanceAs (IsProper (pullback.snd f r))
  have : GeometricallyConnected fC :=
    inferInstanceAs (GeometricallyConnected (pullback.snd f r))
  have : ConnectedSpace (fiberOverGeometricPoint fC η) :=
    connectedSpace_fiberOverGeometricPoint fC η
  have : ConnectedSpace (fiberOverGeometricPoint fC o) :=
    connectedSpace_fiberOverGeometricPoint fC o
  let yη := GeometricPoint.ofPoint (fiberOverGeometricPoint fC η) (Classical.arbitrary _)
  let yo := GeometricPoint.ofPoint (fiberOverGeometricPoint fC o) (Classical.arbitrary _)
  let BC : Scheme.{u} := pullback fC (𝟙 (Spec (.of C)))
  have : ConnectedSpace BC :=
    connectedSpace_pullback_spec_of_isProper fC C (𝟙 (Spec (.of C)))
  let eC : BC ≅ pullback f r := asIso (pullback.fst fC (𝟙 _))
  let iCη := fiberOverGeometricPointMap fC η (𝟙 _) η.hom (Category.comp_id _)
  let iCo := fiberOverGeometricPointMap fC o (𝟙 _) o.hom (Category.comp_id _)
  have hiCo : (finiteEtaleBaseChange iCo).IsEquivalence := by
    have hcomp : iCo = pullback.fst fC o.hom ≫ eC.inv := by
      apply (cancel_mono eC.hom).mp
      rw [Category.assoc, eC.inv_hom_id, Category.comp_id]
      exact pullback.lift_fst _ _ _
    rw [hcomp]
    exact isEquivalence_finiteEtaleBaseChange_comp _ _
      (h0A48 C fC inferInstance) (isEquivalence_finiteEtaleBaseChange_of_iso eC.symm)
  have := hiCo
  let tC := (nonempty_finiteEtaleFiberFunctorIso BC (yη.map iCη) (yo.map iCo)).some
  let dC := (etaleFundamentalGroupContinuousMulEquiv tC).trans
    (etaleFundamentalGroupContinuousMulEquivOfIsEquivalence iCo yo).symm
  let spR : EtaleFundamentalGroup (fiberOverGeometricPoint fC η) yη →ₜ*
      EtaleFundamentalGroup (fiberOverGeometricPoint fC o) yo :=
    (ContinuousMonoidHom.toContinuousMonoidHom dC).comp (etaleFundamentalGroupMap iCη yη)
  have hspRform : ∀ γ, etaleFundamentalGroupMap iCo yo (spR γ)
      = etaleFundamentalGroupMulEquiv tC (etaleFundamentalGroupMap iCη yη γ) := by
    intro γ
    exact (etaleFundamentalGroupMap_eq_iff_eq_symm iCo yo _ _).mpr rfl
  have hspR : IsSpecializationMap fC η o yη yo spR :=
    isSpecializationMap_of_identity_factorization C fC η yη yo spR hiCo tC hspRform
  have hqc : q (closedPoint C) = closedPoint A := IsLocalRing.comap_closedPoint φ
  refine ⟨r, η, o, yη, yo, spR, hηgeneric, hoclosed, ?_, ?_, hspR, ?_⟩
  · change gA (q (η.hom default)) = s'.hom default
    rw [hηgeneric, hηA]
    have h := congrArg (fun w => w default) hp'
    simpa [gA, Scheme.Hom.comp_base] using h
  · change gA (q (o.hom default)) = s.hom default
    rw [hoclosed, hqc, ← hclosed]
    have h := congrArg (fun w => w (closedPoint s.residueField)) hp
    exact h.trans (congrArg s.hom (Subsingleton.elim _ _))
  · let : ConnectedSpace (pullback f gA : Scheme.{u}) := hXA
    let fA := pullback.snd f gA
    let j : (pullback f r : Scheme.{u}) ⟶ (pullback f gA : Scheme.{u}) :=
      pullback.lift (pullback.fst f r) (pullback.snd f r ≫ q) (by
        simpa [r, Category.assoc] using pullback.condition (f := f) (g := r))
    have hj : IsPullback j (pullback.snd f r) fA q := by
      refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f gA)
      rw [show j ≫ pullback.fst f gA = pullback.fst f r from pullback.lift_fst _ _ _]
      exact IsPullback.of_hasPullback f r
    let k : BC ⟶ (pullback f gA : Scheme.{u}) := eC.hom ≫ j
    let sA' : GeometricPoint (Spec (.of A)) :=
      { residueField := s'.residueField, hom := p' }
    let sA : GeometricPoint (Spec (.of A)) := { residueField := s.residueField, hom := p }
    let iA' := fiberOverGeometricPointMap f s' gA p' hp'
    let iA := fiberOverGeometricPointMap f s gA p hp
    have hiA' : IsPullback iA' (pullback.snd f s'.hom) fA sA'.hom :=
      isPullback_fiberOverGeometricPointMap f s' gA p' hp'
    have hiA : IsPullback iA (pullback.snd f s.hom) fA sA.hom :=
      isPullback_fiberOverGeometricPointMap f s gA p hp
    have hiCζ (ζ : GeometricPoint (Spec (.of C))) :
        IsPullback (fiberOverGeometricPointMap fC ζ (𝟙 _) ζ.hom (Category.comp_id _) ≫ k)
          (pullback.snd fC ζ.hom) fA (ζ.map q).hom := by
      rw [show k = eC.hom ≫ j from rfl, ← Category.assoc,
        show fiberOverGeometricPointMap fC ζ (𝟙 _) ζ.hom (Category.comp_id _) ≫ eC.hom =
          pullback.fst fC ζ.hom from pullback.lift_fst _ _ _]
      exact (IsPullback.of_hasPullback fC ζ.hom).paste_horiz hj
    have hclosedA : sA.hom default = (o.map q).hom default := by
      change p default = q (o.hom default)
      rw [hoclosed, hqc, ← hclosed]
      exact congrArg p (Subsingleton.elim _ _)
    have hgenericA : sA'.hom default = (η.map q).hom default := by
      change p' default = q (η.hom default)
      rw [hηgeneric, hηA]
    have hk : (finiteEtaleBaseChange k).IsEquivalence := by
      refine isEquivalence_finiteEtaleBaseChange_cancel_right iCo k hiCo ?_
      exact isEquivalence_finiteEtaleBaseChange_of_isPullback_liesOver_eq fA h0A48
        sA (o.map q) hclosedA iA (pullback.snd f s.hom) hiA
        (iCo ≫ k) (pullback.snd fC o.hom) (hiCζ o) hi
    obtain ⟨W, hW, a, b, ha, hb, hab⟩ := exists_common_geometricFibre fA h0A48
      sA' (η.map q) hgenericA iA' (pullback.snd f s'.hom) hiA'
      (iCη ≫ k) (pullback.snd fC η.hom) (hiCζ η)
    let : ConnectedSpace W := hW
    let zW := GeometricPoint.ofPoint W (Classical.arbitrary _)
    have := hi
    let dA := (etaleFundamentalGroupContinuousMulEquiv t).trans
      (etaleFundamentalGroupContinuousMulEquivOfIsEquivalence iA x).symm
    refine exists_intertwining_of_factorizations iA' iCη k a b hab ha hb hk
      x' x yη yo zW dA dC sp spR ?_ ?_
    · intro γ
      exact (etaleFundamentalGroupMap_eq_iff_eq_symm iA x _ _).mp (hform γ)
    · intro γ
      rfl

end AlgebraicGeometry

end
