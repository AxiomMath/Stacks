module

public import Mathlib
public import Mathlib.Algebra.Module.LinearMap.Index
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CompleteIntersection.RelativeConormal
public import StacksFrontier.RingTheory.FormallySmooth.Field
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField

@[expose] public section

/-!
# Cartier's equality for field extensions

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07E1, 07E2, 07E3.

## Tag 07E1 — Cartier's equality

For a finitely generated extension of fields, the module of Kähler differentials and the
first homology of the naive cotangent complex are finite-dimensional. Their dimensions satisfy
Cartier's equality.

### Main definitions

The Kähler differentials and first cotangent homology are represented by
`KaehlerDifferential` and `Algebra.H1Cotangent`, respectively.

### Main results

* `trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent`: Cartier's
  dimension formula for a finitely generated field extension.

### Implementation notes

Since finite generation makes the transcendence degree finite, its natural-number value is
written as `Cardinal.toNat (Algebra.trdeg k K)`. The dimension identity is stated in the
integers, so subtraction has its usual meaning.

### References

* [Stacks Project, Tag 07E1](https://stacks.math.columbia.edu/tag/07E1)
* [Matsumura, *Commutative Algebra*, Section 39][MatCA]

## Tag 07E2 — The Jacobi--Zariski sequence for field extensions

For a tower of field extensions `K → L → M`, the Jacobi--Zariski sequence from the first
homology of the naive cotangent complex through the modules of Kähler differentials is exact,
including at both ends.

### Main definitions

There are no new definitions.

### Main results

* `jacobiZariski_exact_of_fieldExtensions` gives the exact seven-term
  Jacobi--Zariski sequence for a tower of fields.

### Implementation notes

Exactness of a sequence of modules is expressed by injectivity of its first map, a
`Function.Exact` assertion for each adjacent pair of maps, and surjectivity of its last map.
The maps are Mathlib's canonical maps on first cotangent homology and Kähler differentials,
together with the canonical connecting homomorphism. Mathlib writes extension of scalars with
the new scalar ring as the left tensor factor, so the source's `H₁(L_{L/K}) ⊗[L] M` appears as
`M ⊗[L] H₁(L_{L/K})`.

### References

* [Stacks Project, Tag 07E2](https://stacks.math.columbia.edu/tag/07E2)
* [Matsumura, *Commutative Algebra*, Section 39][MatCA]

## Tag 07E3 — Change of fields and the naive cotangent complex

For a commutative square of fields whose horizontal extensions are finitely generated, the
canonical maps on Kähler differentials and first cotangent homology have finite-dimensional
kernels and cokernels. Their Euler characteristics differ by the corresponding transcendence
degrees.

### Main definitions

The canonical maps are obtained from `KaehlerDifferential.map` and
`Algebra.H1Cotangent.map` by extension of scalars to the upper-right field.

### Main results

* `finrank_ker_sub_finrank_coker_kaehlerDifferential_map_sub_h1Cotangent_map`:
  the finiteness and dimension formula for the two canonical maps.

### Implementation notes

A cokernel is represented as the quotient of the codomain by the range. The alternating
dimension identity is stated in the integers, so subtraction has its usual mathematical
meaning rather than truncated natural-number subtraction.

### References

* [Stacks Project, Tag 07E3](https://stacks.math.columbia.edu/tag/07E3)
* [Matsumura, *Commutative Algebra*, Section 39][MatCA]

-/

/-! ### Stacks Tag 07E1 -/

section

section

open TensorProduct

universe u v

private lemma finite_h1_of_finiteType
    (k : Type u) (A : Type v) [CommRing k] [IsNoetherianRing k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : Module.Finite A (Algebra.H1Cotangent k A) := by
  let : Algebra.FinitePresentation k A :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := A)).mp inferInstance
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let P := Algebra.Presentation.ofFinitePresentation k A
  let : Module.Finite A P.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite P.fg_ker
  have : Module.Finite A P.toExtension.H1Cotangent := by
    show Module.Finite A (LinearMap.ker P.toExtension.cotangentComplex)
    infer_instance
  exact Module.Finite.of_surjective P.equivH1Cotangent.toLinearMap
    P.equivH1Cotangent.surjective

@[ega "0 21.7.1" "finite rank of Ω¹_{L/K}"]
private lemma finite_differentials_of_essFiniteType
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] : FiniteDimensional K Ω[K⁄k] := by
  infer_instance

@[ega "0 21.7.1" "finite rank of Υ_{L/K}"]
private lemma finite_h1_of_essFiniteType
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] : FiniteDimensional K (Algebra.H1Cotangent k K) := by
  let A := Algebra.EssFiniteType.subalgebra k K
  let M := Algebra.EssFiniteType.submonoid k K
  let : IsLocalization M K := Algebra.EssFiniteType.isLocalization k K
  let : Module.Finite A (Algebra.H1Cotangent k A) := finite_h1_of_finiteType k A
  have : Module.Finite K (K ⊗[A] (Algebra.H1Cotangent k A)) := inferInstance
  exact Module.Finite.of_surjective
    (Algebra.tensorH1CotangentOfIsLocalization k K M).toLinearMap
    (Algebra.tensorH1CotangentOfIsLocalization k K M).surjective

private lemma finrank_sub_finrank_ker_of_exact
    (F : Type*) [Field F] (C V W : Type*) [AddCommGroup C] [Module F C]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F C] [FiniteDimensional F V] [FiniteDimensional F W]
    (f : C →ₗ[F] V) (g : V →ₗ[F] W)
    (hex : Function.Exact f g) (hsurj : Function.Surjective g) :
    (Module.finrank F W : ℤ) - Module.finrank F (LinearMap.ker f) =
      (Module.finrank F V : ℤ) - Module.finrank F C := by
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ := g.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h₂
  rw [LinearMap.exact_iff.mp hex] at h₂
  omega

private lemma cartier_rank_identity_of_model
    (k : Type u) (K : Type v) (A : Type*)
    [Field k] [Field K] [CommRing A] [Algebra k A] [Algebra A K] [Algebra k K]
    [IsScalarTower k A K] [Algebra.EssFiniteType k K]
    (M : Submonoid A) [IsLocalization M K]
    {ι : Type*} [Fintype ι] (P : Algebra.Generators k A ι)
    [FiniteDimensional K (K ⊗[A] P.toExtension.Cotangent)]
    (hcon : (Cardinal.toNat (Algebra.trdeg k K) : ℤ) =
      (Fintype.card ι : ℤ) - Module.finrank K (K ⊗[A] P.toExtension.Cotangent)) :
    (Cardinal.toNat (Algebra.trdeg k K) : ℤ) =
      (Module.finrank K Ω[K⁄k] : ℤ) - Module.finrank K (Algebra.H1Cotangent k K) := by
  let : FiniteDimensional K Ω[K⁄k] := finite_differentials_of_essFiniteType k K
  let : FiniteDimensional K (Algebra.H1Cotangent k K) := finite_h1_of_essFiniteType k K
  let : Algebra.FormallyEtale A K := Algebra.FormallyEtale.of_isLocalization M
  let : Module.Flat A K := IsLocalization.flat K M
  let f := P.toExtension.cotangentComplex
  let g := P.toExtension.toKaehler
  have : FiniteDimensional K (K ⊗[A] P.toExtension.CotangentSpace) := by
    let : Module.Finite A P.toExtension.CotangentSpace :=
      Module.Finite.of_basis P.cotangentSpaceBasis
    infer_instance
  have : FiniteDimensional K (K ⊗[A] Ω[A⁄k]) := by
    exact Module.Finite.of_surjective
      (g.baseChange K) (g.baseChange_surjective K P.toExtension.toKaehler_surjective)
  have hEuler := finrank_sub_finrank_ker_of_exact K
    (K ⊗[A] P.toExtension.Cotangent)
    (K ⊗[A] P.toExtension.CotangentSpace) (K ⊗[A] Ω[A⁄k])
    (f.baseChange K) (g.baseChange K)
    (by simpa [LinearMap.baseChange_eq_ltensor] using
      Module.Flat.lTensor_exact K P.toExtension.exact_cotangentComplex_toKaehler)
    (g.baseChange_surjective K P.toExtension.toKaehler_surjective)
  have hker : Module.finrank K (LinearMap.ker (f.baseChange K)) =
      Module.finrank K (Algebra.H1Cotangent k K) := by
    calc
      _ = Module.finrank K (K ⊗[A] P.toExtension.H1Cotangent) := by
        exact (LinearMap.tensorKerEquiv K K f).finrank_eq.symm
      _ = Module.finrank K (K ⊗[A] Algebra.H1Cotangent k A) := by
        exact (P.equivH1Cotangent.baseChange A K).finrank_eq
      _ = _ := (Algebra.tensorH1CotangentOfIsLocalization k K M).finrank_eq
  have hdiff : Module.finrank K (K ⊗[A] Ω[A⁄k]) = Module.finrank K Ω[K⁄k] :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A K).finrank_eq
  have hfree : Module.finrank K (K ⊗[A] P.toExtension.CotangentSpace) =
      Fintype.card ι := Module.finrank_eq_card_basis (P.cotangentSpaceBasis.baseChange K)
  rw [hker, hdiff, hfree] at hEuler
  omega

private lemma cartier_rank_identity_of_complete_intersection_model
    (k : Type u) (K : Type v) (A : Type*)
    [Field k] [Field K] [CommRing A] [Algebra k A] [Algebra A K] [Algebra k K]
    [IsScalarTower k A K] [Algebra.EssFiniteType k K]
    (M : Submonoid A) [IsLocalization M K]
    {n c : ℕ} (P : Algebra.Presentation k A (Fin n) (Fin c))
    [P.IsRelativeGlobalCompleteIntersection]
    (hnum : c + Cardinal.toNat (Algebra.trdeg k K) = n) :
    (Cardinal.toNat (Algebra.trdeg k K) : ℤ) =
      (Module.finrank K Ω[K⁄k] : ℤ) - Module.finrank K (Algebra.H1Cotangent k K) := by
  obtain ⟨b, _⟩ := P.exists_basis_cotangent_relation
  have : Module.Finite A P.toExtension.Cotangent := Module.Finite.of_basis b
  have : FiniteDimensional K (K ⊗[A] P.toExtension.Cotangent) := inferInstance
  have hcon : (Cardinal.toNat (Algebra.trdeg k K) : ℤ) =
      (Fintype.card (Fin n) : ℤ) -
        Module.finrank K (K ⊗[A] P.toExtension.Cotangent) := by
    rw [Module.finrank_eq_card_basis (b.baseChange K), Fintype.card_fin, Fintype.card_fin]
    omega
  exact cartier_rank_identity_of_model k K A M P.toGenerators hcon

private lemma exists_globalCompleteIntersection_away
    (k A : Type*) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ∃ g : A, g ≠ 0 ∧ IsGlobalCompleteIntersection k (Localization.Away g) := by
  classical
  have : Algebra.FinitePresentation k A :=
    (Algebra.FinitePresentation.of_finiteType (R := k) (A := A)).mp inferInstance
  let P := (Algebra.Presentation.ofFinitePresentation k A).toGenerators
  let p : Ideal P.Ring := (⊥ : Ideal A).comap (algebraMap P.Ring A)
  have : p.IsPrime := Ideal.comap_isPrime _ _
  let R := Localization.AtPrime p
  have : IsRegularLocalRing R := inferInstance
  let c := (IsLocalRing.maximalIdeal R).spanFinrank
  have hc : p.height = c := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p R] at h
    exact_mod_cast h.symm
  obtain ⟨g, hg, hG⟩ :=
    P.exists_isGlobalCompleteIntersection_away_of_spanFinrank_ker_map_le k A ⊥ c
      (by simpa using hc) R (by
        show (p.map (algebraMap P.Ring R)).spanFinrank ≤ c
        rw [IsLocalization.AtPrime.map_eq_maximalIdeal p R])
  exact ⟨g, hg, hG⟩

private lemma exists_relativePresentation_of_isGlobalCompleteIntersection
    (k A : Type*) [Field k] [CommRing A] [Nontrivial A] [Algebra k A]
    (h : IsGlobalCompleteIntersection k A) :
    ∃ (n c : ℕ) (P : Algebra.Presentation k A (Fin n) (Fin c)),
      P.IsRelativeGlobalCompleteIntersection ∧
      ringKrullDim A + (c : WithBot ℕ∞) = n := by
  classical
  obtain h | ⟨n, c, f, e, hcn, hdim⟩ := h
  · exact False.elim (not_subsingleton A h)
  let P := (Algebra.Presentation.naive (v := f)).ofAlgEquiv e.symm
  have hd : ringKrullDim A + (c : WithBot ℕ∞) = n := by
    rw [hdim, ← Nat.cast_add, Nat.sub_add_cancel hcn]
  refine ⟨n, c, P, ⟨fun p _ _ ↦ ?_⟩, hd⟩
  let e' : p.Fiber A ≃ₐ[k] A :=
    (Algebra.TensorProduct.congr p.algEquivResidueFieldOfField.symm
      (AlgEquiv.refl (R := k) (A₁ := A))).trans (Algebra.TensorProduct.lid k A)
  simpa only [Nat.card_fin, e'.toRingEquiv.ringKrullDim] using hd

private lemma isFractionRing_of_field_localization
    (A K : Type*) [CommRing A] [Field K] [Algebra A K] [FaithfulSMul A K]
    (M : Submonoid A) [IsLocalization M K] : IsFractionRing A K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨⟨x, y⟩, h⟩ := IsLocalization.surj M z
  exact ⟨x, y, (eq_div_iff (IsLocalization.map_units K y).ne_zero).mpr h⟩

private lemma exists_globalCompleteIntersection_fractionRing
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K] :
    ∃ (A : Type v) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra k A)
      (_ : Algebra A K) (_ : IsScalarTower k A K),
      IsFractionRing A K ∧ IsGlobalCompleteIntersection k A := by
  classical
  let A := Algebra.EssFiniteType.subalgebra k K
  have : IsFractionRing A K :=
    isFractionRing_of_field_localization A K (Algebra.EssFiniteType.submonoid k K)
  obtain ⟨g, hg, hG⟩ := exists_globalCompleteIntersection_away k A
  let B := Localization.Away g
  have hgK : IsUnit (algebraMap A K g) :=
    isUnit_iff_ne_zero.mpr (map_ne_zero_iff _ (IsFractionRing.injective A K) |>.mpr hg)
  let f : B →ₐ[A] K := IsLocalization.Away.liftAlgHom g (f := Algebra.ofId A K) hgK
  let : Algebra B K := f.toRingHom.toAlgebra
  have : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower k B K := IsScalarTower.to₁₃₄ k A B K
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr hg))
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g) B K
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hG⟩

@[ega "0 21.7.1"]
private lemma cartier_rank_identity
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    (Cardinal.toNat (Algebra.trdeg k K) : ℤ) =
      (Module.finrank K Ω[K⁄k] : ℤ) - Module.finrank K (Algebra.H1Cotangent k K) := by
  classical
  obtain ⟨A, _, _, _, _, _, hfrac, hG⟩ :=
    exists_globalCompleteIntersection_fractionRing k K
  have : IsFractionRing A K := hfrac
  have : Algebra.FiniteType k A := hG.finiteType
  obtain ⟨n, c, P, hP, hd⟩ :=
    exists_relativePresentation_of_isGlobalCompleteIntersection k A hG
  have : P.IsRelativeGlobalCompleteIntersection := hP
  have hdim := (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, v, v, 0}
    k A K).1
  have htr : Cardinal.toENat (Algebra.trdeg k K) =
      (Cardinal.toNat (Algebra.trdeg k K) : ℕ∞) := by
    apply Cardinal.toENat_eq_natCast.mpr
    exact (Cardinal.cast_toNat_of_lt_aleph0 (trdeg_lt_aleph0 k K)).symm
  rw [hdim, htr] at hd
  have hnum : c + Cardinal.toNat (Algebra.trdeg k K) = n := by
    have h : Cardinal.toNat (Algebra.trdeg k K) + c = n := by exact_mod_cast hd
    omega
  exact cartier_rank_identity_of_complete_intersection_model k K A
    (nonZeroDivisors A) P hnum

/-- **Cartier's equality.** For a finitely generated extension of fields `K/k`, the module of
Kähler differentials and the first homology of the naive cotangent complex are
finite-dimensional, and their dimensions differ by the transcendence degree. -/
@[stacks 07E1, ega "0 21.7.1", ega "0 21.7.2" "special case"]
public theorem trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] :
    FiniteDimensional K Ω[K⁄k] ∧
      FiniteDimensional K (Algebra.H1Cotangent k K) ∧
        (Cardinal.toNat (Algebra.trdeg k K) : ℤ) =
          (Module.finrank K Ω[K⁄k] : ℤ) - Module.finrank K (Algebra.H1Cotangent k K) := by
  let := finite_differentials_of_essFiniteType k K
  let := finite_h1_of_essFiniteType k K
  exact ⟨inferInstance, inferInstance, cartier_rank_identity k K⟩

end

end

/-! ### Stacks Tag 07E2 -/

section

section

open Algebra MvPolynomial TensorProduct

universe u₁ u₂ u₃

section Naturality

variable (R S T U : Type*) [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra R U] [Algebra S U] [Algebra T U]
  [IsScalarTower R S U] [IsScalarTower S T U]

omit [IsScalarTower S T U] in
/-- The canonical map between tautological polynomial presentations renames variables. -/
private lemma defaultHom_toAlgHom_self (x : MvPolynomial T S) :
    (Generators.defaultHom (Generators.self S T) (Generators.self S U)).toAlgHom x =
      rename (algebraMap T U) x := by
  apply AlgHom.congr_fun
  ext i : 1
  simp [Generators.Hom.toAlgHom_X, Generators.defaultHom, Generators.self,
    Generators.σ]

set_option backward.isDefEq.respectTransparency false in
/-- The coefficient differential commutes with renaming along the algebra map. -/
private lemma δAux_rename (x : MvPolynomial T S) :
    Generators.H1Cotangent.δAux R (Generators.self S U) (rename (algebraMap T U) x) =
      AlgebraTensorModule.map (Algebra.linearMap T U) (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R])
        (Generators.H1Cotangent.δAux R (Generators.self S T) x) := by
  induction x using MvPolynomial.induction_on with
  | C s => simp [Generators.H1Cotangent.δAux_C]
  | add x y hx hy => simp only [map_add, hx, hy]
  | mul_X x i hx =>
    simp only [map_mul, rename_X, Generators.H1Cotangent.δAux_mul,
      Generators.H1Cotangent.δAux_X, smul_zero, zero_add, hx]
    rw [← @IsScalarTower.algebraMap_smul (Generators.self S U).Ring U,
      ← @IsScalarTower.algebraMap_smul (Generators.self S T).Ring T]
    simp only [Generators.algebraMap_apply, aeval_X, Generators.self_val, id_eq]
    rw [@IsScalarTower.algebraMap_smul T U, map_smul]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the connecting map in the last algebra of a tower. -/
private lemma δ_map_baseChange (x : H1Cotangent S T) :
    H1Cotangent.δ R S U (H1Cotangent.map S S T U x) =
      AlgebraTensorModule.map (Algebra.linearMap T U) (LinearMap.id : Ω[S⁄R] →ₗ[S] Ω[S⁄R])
        (H1Cotangent.δ R S T x) := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨x, rfl⟩ := Extension.Cotangent.mk_surjective x
  show Generators.H1Cotangent.δ _ _ ⟨_, _⟩ = _
  simp only [LinearMap.domRestrict_apply, Extension.Cotangent.map_mk, H1Cotangent.δ,
    Generators.H1Cotangent.δ_eq_δAux]
  show Generators.H1Cotangent.δAux R (Generators.self S U)
    ((Generators.defaultHom (Generators.self S T) (Generators.self S U)).toAlgHom x.1) = _
  rw [defaultHom_toAlgHom_self S T U]
  exact δAux_rename R S T U x.1

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing of absolute first cotangent homology makes relative first homology inject
under a flat extension of the last algebra. -/
private theorem liftBaseChange_injective_of_subsingleton_h1Cotangent
    [Module.Flat T U] [Subsingleton (H1Cotangent R T)] :
    Function.Injective ((H1Cotangent.map S S T U).liftBaseChange U) := by
  have hδ : Function.Injective (H1Cotangent.δ R S T) := by
    rw [← LinearMap.ker_eq_bot, (H1Cotangent.exact_map_δ R S T).linearMap_ker_eq]
    exact LinearMap.range_eq_bot.mpr (Subsingleton.elim _ _)
  have hbase : Function.Injective ((H1Cotangent.δ R S T).baseChange U) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hδ
  let e := AlgebraTensorModule.cancelBaseChange S T U U Ω[S⁄R]
  have hcomm :
      H1Cotangent.δ R S U ∘ₗ (H1Cotangent.map S S T U).liftBaseChange U =
        e.toLinearMap ∘ₗ (H1Cotangent.δ R S T).baseChange U := by
    apply AlgebraTensorModule.ext
    intro u x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.liftBaseChange_tmul,
      map_smul, δ_map_baseChange R S T U, LinearMap.baseChange_tmul]
    generalize H1Cotangent.δ R S T x = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, tmul_add, smul_add, hx, hy]
    | tmul t w =>
      simp only [e, AlgebraTensorModule.map_tmul, Algebra.linearMap_apply, LinearMap.id_apply,
        LinearEquiv.coe_coe, AlgebraTensorModule.cancelBaseChange_tmul, smul_tmul',
        Algebra.smul_def, algebraMap_self, RingHom.id_apply, mul_comm]
  intro x y h
  apply hbase
  apply e.injective
  exact (LinearMap.congr_fun hcomm x).symm.trans
    ((congrArg (H1Cotangent.δ R S U) h).trans (LinearMap.congr_fun hcomm y))

end Naturality

/-- Apply naturality over the prime field, over which every field is formally smooth. -/
private theorem liftBaseChange_injective_of_fields
    (K L M : Type*) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    Function.Injective ((H1Cotangent.map K K L M).liftBaseChange M) := by
  obtain ⟨p, hp⟩ := CharP.exists K
  let := hp
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have : CharP M p := charP_of_injective_algebraMap (algebraMap K M).injective p
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · let : Fact p.Prime := ⟨hp⟩
    let : Algebra (ZMod p) K := ZMod.algebra K p
    let : Algebra (ZMod p) L := ZMod.algebra L p
    let : Algebra (ZMod p) M := ZMod.algebra M p
    have : Algebra.FormallySmooth (ZMod p) L := Algebra.formallySmooth_of_perfectField _ _
    exact liftBaseChange_injective_of_subsingleton_h1Cotangent (ZMod p) K L M
  · have : CharZero K := CharP.charP_to_charZero K
    have : CharZero L := CharP.charP_to_charZero L
    have : CharZero M := CharP.charP_to_charZero M
    have : Algebra.FormallySmooth ℚ L := Algebra.formallySmooth_of_perfectField _ _
    exact liftBaseChange_injective_of_subsingleton_h1Cotangent ℚ K L M

/-- Let `M/L/K` be a tower of field extensions. Then the canonical Jacobi--Zariski sequence

`0 → H₁(L_{L/K}) ⊗[L] M → H₁(L_{M/K}) → H₁(L_{M/L}) →`
`M ⊗[L] Ω[L⁄K] → Ω[M⁄K] → Ω[M⁄L] → 0`

is exact. -/
@[stacks 07E2]
public theorem jacobiZariski_exact_of_fieldExtensions
    (K : Type u₁) (L : Type u₂) (M : Type u₃)
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    let i := (Algebra.H1Cotangent.map K K L M).liftBaseChange M
    let p := Algebra.H1Cotangent.map K L M M
    let δ := Algebra.H1Cotangent.δ K L M
    let d := KaehlerDifferential.mapBaseChange K L M
    let q := KaehlerDifferential.map K L M M
    Function.Injective i ∧
      Function.Exact i p ∧
      Function.Exact p δ ∧
      Function.Exact δ d ∧
      Function.Exact d q ∧
      Function.Surjective q := by
  dsimp only
  exact ⟨liftBaseChange_injective_of_fields K L M,
    H1Cotangent.exact_liftBaseChange_map_of_flat K L M,
    H1Cotangent.exact_map_δ K L M,
    H1Cotangent.exact_δ_mapBaseChange K L M,
    KaehlerDifferential.exact_mapBaseChange_map K L M,
    KaehlerDifferential.map_surjective K L M⟩

end

end

/-! ### Stacks Tag 07E3 -/

section

section

attribute [local instance] SMulCommClass.of_commMonoid

open scoped TensorProduct

universe u₁ u₂ u₃ u₄

end

section

attribute [local instance] SMulCommClass.of_commMonoid

open scoped TensorProduct

universe u₁ u₂ u₃ u₄

private lemma finiteDimensional_ker_of_exact_left
    {F M N P : Type*} [DivisionRing F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [AddCommGroup P] [Module F P]
    (f : M →ₗ[F] N) (g : N →ₗ[F] P) (h : Function.Exact f g)
    [FiniteDimensional F M] : FiniteDimensional F (LinearMap.ker g) := by
  rw [h.linearMap_ker_eq]
  infer_instance

private lemma finiteDimensional_coker_of_exact_right
    {F M N P : Type*} [DivisionRing F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [AddCommGroup P] [Module F P]
    (f : M →ₗ[F] N) (g : N →ₗ[F] P) (h : Function.Exact f g)
    [FiniteDimensional F P] : FiniteDimensional F (N ⧸ LinearMap.range f) := by
  rw [← h.linearMap_ker_eq]
  exact FiniteDimensional.of_injective g.quotKerEquivRange.toLinearMap
    g.quotKerEquivRange.injective

/-- For an exact pair `f, g`, the cokernel of `f` has the dimension of the range of `g`. -/
private lemma finrank_quotient_range_eq_of_exact
    {F A B C : Type*} [DivisionRing F] [AddCommGroup A] [Module F A]
    [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
    {f : A →ₗ[F] B} {g : B →ₗ[F] C} (hex : Function.Exact f g) :
    Module.finrank F (B ⧸ f.range) = Module.finrank F g.range := by
  rw [← hex.linearMap_ker_eq]
  exact g.quotKerEquivRange.finrank_eq

private lemma index_right_sub_left_of_exact_six
    {F A X B C Y D : Type*} [DivisionRing F]
    [AddCommGroup A] [Module F A] [AddCommGroup X] [Module F X]
    [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
    [AddCommGroup Y] [Module F Y] [AddCommGroup D] [Module F D]
    [FiniteDimensional F A] [FiniteDimensional F C]
    (a : A →ₗ[F] X) (g : X →ₗ[F] B) (d : B →ₗ[F] C)
    (c : C →ₗ[F] Y) (o : Y →ₗ[F] D)
    (ha : Function.Injective a) (ho : Function.Surjective o)
    (hag : Function.Exact a g) (hgd : Function.Exact g d)
    (hdc : Function.Exact d c) (hco : Function.Exact c o) :
    o.index - g.index = Module.finrank F C - Module.finrank F A := by
  rw [LinearMap.index_of_surjective ho, LinearMap.index_eq_finrank_sub]
  have hra : Module.finrank F a.range = Module.finrank F A := by
    exact (LinearEquiv.ofInjective a ha).finrank_eq.symm
  have hqd := finrank_quotient_range_eq_of_exact hgd
  have hrc := Submodule.finrank_quotient_add_finrank d.range
  rw [finrank_quotient_range_eq_of_exact hdc] at hrc
  rw [hco.linearMap_ker_eq, hag.linearMap_ker_eq, hra, hqd]
  omega

private lemma index_middle_sub_first_of_exact_six
    {F A X B C Y D : Type*} [DivisionRing F]
    [AddCommGroup A] [Module F A] [AddCommGroup X] [Module F X]
    [AddCommGroup B] [Module F B] [AddCommGroup C] [Module F C]
    [AddCommGroup Y] [Module F Y] [AddCommGroup D] [Module F D]
    [FiniteDimensional F B] [FiniteDimensional F D]
    (a : A →ₗ[F] X) (g : X →ₗ[F] B) (d : B →ₗ[F] C)
    (c : C →ₗ[F] Y) (o : Y →ₗ[F] D)
    (ha : Function.Injective a) (ho : Function.Surjective o)
    (hag : Function.Exact a g) (hgd : Function.Exact g d)
    (hdc : Function.Exact d c) (hco : Function.Exact c o) :
    c.index - a.index = Module.finrank F B - Module.finrank F D := by
  rw [LinearMap.index_eq_finrank_sub, LinearMap.index_of_injective ha]
  have hB := Submodule.finrank_quotient_add_finrank g.range
  rw [finrank_quotient_range_eq_of_exact hgd] at hB
  have hD : Module.finrank F o.range = Module.finrank F D :=
    (LinearEquiv.ofTop o.range (LinearMap.range_eq_top.mpr ho)).finrank_eq
  rw [hdc.linearMap_ker_eq, finrank_quotient_range_eq_of_exact hag,
    finrank_quotient_range_eq_of_exact hco, hD]
  omega

/-- Given a commutative square of fields
```
K  → K'
↑    ↑
k  → k'
```
whose horizontal extensions are finitely generated, the kernels and cokernels of the canonical
maps on Kähler differentials and first cotangent homology are finite-dimensional. The alternating
sum of their dimensions is the difference of the transcendence degrees of the horizontal
extensions. -/
@[stacks 07E3, ega "0 21.7.1"]
public theorem finrank_ker_sub_finrank_coker_kaehlerDifferential_map_sub_h1Cotangent_map
    (k : Type u₁) (K : Type u₂) (k' : Type u₃) (K' : Type u₄)
    [Field k] [Field K] [Field k'] [Field K']
    [Algebra k K] [Algebra k k'] [Algebra K K'] [Algebra k' K'] [Algebra k K']
    [IsScalarTower k K K'] [IsScalarTower k k' K']
    [Algebra.FiniteType k k'] [Algebra.FiniteType K K'] :
    let α := (KaehlerDifferential.map k k' K K').liftBaseChange K'
    let β := (Algebra.H1Cotangent.map k k' K K').liftBaseChange K'
    FiniteDimensional K' (LinearMap.ker α) ∧
      FiniteDimensional K' (Ω[K'⁄k'] ⧸ LinearMap.range α) ∧
      FiniteDimensional K' (LinearMap.ker β) ∧
      FiniteDimensional K' (Algebra.H1Cotangent k' K' ⧸ LinearMap.range β) ∧
      (Module.finrank K' (LinearMap.ker α) : ℤ) -
          Module.finrank K' (Ω[K'⁄k'] ⧸ LinearMap.range α) -
          Module.finrank K' (LinearMap.ker β) +
          Module.finrank K' (Algebra.H1Cotangent k' K' ⧸ LinearMap.range β) =
      (Cardinal.toNat (Algebra.trdeg k k') : ℤ) -
          Cardinal.toNat (Algebra.trdeg K K') := by
  dsimp
  let a := (Algebra.H1Cotangent.map k k k' K').liftBaseChange K'
  let g := Algebra.H1Cotangent.map k k' K' K'
  let d := Algebra.H1Cotangent.δ k k' K'
  let c := KaehlerDifferential.mapBaseChange k k' K'
  let o := KaehlerDifferential.map k k' K' K'
  let a' := (Algebra.H1Cotangent.map k k K K').liftBaseChange K'
  let g' := Algebra.H1Cotangent.map k K K' K'
  let d' := Algebra.H1Cotangent.δ k K K'
  let c' := KaehlerDifferential.mapBaseChange k K K'
  let o' := KaehlerDifferential.map k K K' K'
  have hk := trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent k k'
  have hK := trdeg_eq_finrank_kaehlerDifferential_sub_finrank_h1Cotangent K K'
  let : FiniteDimensional k' Ω[k'⁄k] := hk.1
  let : FiniteDimensional k' (Algebra.H1Cotangent k k') := hk.2.1
  let : FiniteDimensional K' Ω[K'⁄K] := hK.1
  let : FiniteDimensional K' (Algebra.H1Cotangent K K') := hK.2.1
  let : FiniteDimensional K' (K' ⊗[k'] Ω[k'⁄k]) :=
    Module.Finite.base_change k' K' Ω[k'⁄k]
  let : FiniteDimensional K' (K' ⊗[k'] Algebra.H1Cotangent k k') :=
    Module.Finite.base_change k' K' (Algebra.H1Cotangent k k')
  have hag : Function.Exact a g := Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat k k' K'
  have hgd : Function.Exact g d := Algebra.H1Cotangent.exact_map_δ k k' K'
  have hdc : Function.Exact d c := Algebra.H1Cotangent.exact_δ_mapBaseChange k k' K'
  have hco : Function.Exact c o := KaehlerDifferential.exact_mapBaseChange_map k k' K'
  have hag' : Function.Exact a' g' := Algebra.H1Cotangent.exact_liftBaseChange_map_of_flat k K K'
  have hgd' : Function.Exact g' d' := Algebra.H1Cotangent.exact_map_δ k K K'
  have hdc' : Function.Exact d' c' := Algebra.H1Cotangent.exact_δ_mapBaseChange k K K'
  have hco' : Function.Exact c' o' := KaehlerDifferential.exact_mapBaseChange_map k K K'
  have ha : Function.Injective a :=
    (jacobiZariski_exact_of_fieldExtensions k k' K').1
  have ho : Function.Surjective o := KaehlerDifferential.map_surjective k k' K'
  have ha' : Function.Injective a' :=
    (jacobiZariski_exact_of_fieldExtensions k K K').1
  have ho' : Function.Surjective o' := KaehlerDifferential.map_surjective k K K'
  have hLower := index_right_sub_left_of_exact_six a g d c o ha ho hag hgd hdc hco
  have hUpper := index_middle_sub_first_of_exact_six a' g' d' c' o' ha' ho'
    hag' hgd' hdc' hco'
  have hβ : (Algebra.H1Cotangent.map k k' K K').liftBaseChange K' = g ∘ₗ a' := by
    dsimp only [g, a']
    rw [LinearMap.liftBaseChange_comp]
    apply congrArg (LinearMap.liftBaseChange K')
    simp only [Algebra.H1Cotangent.map]
    rw [← Algebra.Extension.H1Cotangent.map_comp]
    exact Algebra.Extension.H1Cotangent.map_eq _ _
  have hα : (KaehlerDifferential.map k k' K K').liftBaseChange K' = o ∘ₗ c' := by
    ext x
    simp [o, c', KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
  have : FiniteDimensional K' (LinearMap.ker a') := by
    rw [LinearMap.ker_eq_bot.mpr ha']
    infer_instance
  have : FiniteDimensional K' (Algebra.H1Cotangent k K' ⧸ LinearMap.range a') :=
    finiteDimensional_coker_of_exact_right a' g' hag'
  have : FiniteDimensional K' (LinearMap.ker g) :=
    finiteDimensional_ker_of_exact_left a g hag
  have : FiniteDimensional K' (Algebra.H1Cotangent k' K' ⧸ LinearMap.range g) :=
    finiteDimensional_coker_of_exact_right g d hgd
  have : FiniteDimensional K' (LinearMap.ker c') :=
    finiteDimensional_ker_of_exact_left d' c' hdc'
  have : FiniteDimensional K' (Ω[K'⁄k] ⧸ LinearMap.range c') :=
    finiteDimensional_coker_of_exact_right c' o' hco'
  have : FiniteDimensional K' (LinearMap.ker o) :=
    finiteDimensional_ker_of_exact_left c o hco
  have : FiniteDimensional K' (Ω[K'⁄k'] ⧸ LinearMap.range o) := by
    rw [LinearMap.range_eq_top.mpr ho]
    infer_instance
  rw [hα, hβ]
  have hindexα := LinearMap.index_comp o c'
  have hindexβ := LinearMap.index_comp g a'
  have hfinαker : FiniteDimensional K' (LinearMap.ker (o ∘ₗ c')) := by
    rw [LinearMap.ker_comp]
    infer_instance
  have hfinαcoker : FiniteDimensional K' (Ω[K'⁄k'] ⧸ LinearMap.range (o ∘ₗ c')) := by
    rw [LinearMap.range_comp]
    infer_instance
  have hfinβker : FiniteDimensional K' (LinearMap.ker (g ∘ₗ a')) := by
    rw [LinearMap.ker_comp]
    infer_instance
  have hfinβcoker :
      FiniteDimensional K' (Algebra.H1Cotangent k' K' ⧸ LinearMap.range (g ∘ₗ a')) := by
    rw [LinearMap.range_comp]
    infer_instance
  refine ⟨hfinαker, hfinαcoker, hfinβker, hfinβcoker, ?_⟩
  rw [← LinearMap.index_eq_finrank_sub (f := o ∘ₗ c')]
  rw [hindexα]
  rw [LinearMap.index_eq_finrank_sub] at hindexβ
  simp only [Module.finrank_tensorProduct, Module.finrank_self, one_mul] at hLower
  linarith [hk.2.2, hK.2.2]

end

section

attribute [local instance] SMulCommClass.of_commMonoid

open scoped TensorProduct

universe u₁ u₂ u₃ u₄

end

end

end
