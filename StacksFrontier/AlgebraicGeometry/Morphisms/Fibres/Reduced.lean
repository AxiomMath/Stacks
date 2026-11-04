module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Properties
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedBaseChange
public import StacksFrontier.RingTheory.Flat.GenericFlatness
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduced fibres

Reducedness and geometric reducedness of the fibres of a finite type morphism of schemes.
Both properties spread from the fibre over a generic point of an irreducible target to all
fibres over a nonempty open subset, and the geometrically reduced locus is compatible with
arbitrary base change.

## Main results

* `AlgebraicGeometry.exists_open_forall_not_isReduced_fiber`: if the generic fibre is
  nonreduced then so is every fibre over a suitable nonempty open subset of the target.
* `AlgebraicGeometry.geometricallyReduced_fiber_set_eq_preimage_of_isPullback`: the locus of
  geometrically reduced fibres commutes with arbitrary base change.
* `AlgebraicGeometry.isReduced_fiber_of_geometricallyReduced_fiberToSpecResidueField`: a
  geometrically reduced fibre is reduced.

## Implementation notes

A finite type morphism is expressed by Mathlib's two predicates `LocallyOfFiniteType` and
`QuasiCompact`. Irreducibility of the target is expressed by `IrreducibleSpace`, and a chosen
generic point by `IsGenericPoint η Set.univ`. A base change is represented by an arbitrary
pullback square, and fibres by `Scheme.Hom.fiberToSpecResidueField`, so geometric reducedness
is taken over the appropriate residue field at each point.

## References

* [Stacks Project, Tag 0575](https://stacks.math.columbia.edu/tag/0575)
* [Stacks Project, Tag 0576](https://stacks.math.columbia.edu/tag/0576)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

private lemma nontrivial_tensor_of_free {R K L M : Type*} [CommRing R]
    [Field K] [Field L] [AddCommGroup M] [Module R M] [Algebra R K] [Algebra R L]
    [Module.Free R M] (hK : Nontrivial (K ⊗[R] M)) :
    Nontrivial (L ⊗[R] M) := by
  let b := Module.Free.chooseBasis R M
  obtain ⟨i⟩ := (b.baseChange K).index_nonempty
  exact ⟨b.baseChange L i, 0, (b.baseChange L).ne_zero i⟩

private lemma tensor_injective_of_flat_quotient {R M N Q K : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q] [AddCommGroup K] [Module R K]
    [Module.Flat R Q] (i : M →ₗ[R] N) (q : N →ₗ[R] Q)
    (hi : Function.Injective i) (hiq : Function.Exact i q) (hq : Function.Surjective q) :
    Function.Injective (LinearMap.lTensor K i) :=
  (flat_tor_zero i q hi hiq hq).1

private lemma not_isReduced_of_nilpotent_mul_ne_zero {B : Type*} [CommRing B]
    (h : B) (hnil : IsNilpotent h) (hneq : ∃ b : B, h * b ≠ 0) : ¬ _root_.IsReduced B := by
  rintro hred; obtain ⟨b, hb⟩ := hneq
  exact hb (by rw [_root_.IsReduced.eq_zero h hnil, zero_mul])

private lemma isReduced_affine_fiber_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    IsReduced ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p) ↔
      _root_.IsReduced (p.asIdeal.Fiber S) := by
  let h : (Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber p ≅
      Spec (.of (p.asIdeal.Fiber S)) := asIso (Spec.fiberToSpecResidueFieldIso R S p).hom.left
  have he := affine_isReduced_iff (CommRingCat.of (p.asIdeal.Fiber S))
  exact ⟨fun hr => he.mp (ObjectProperty.prop_of_iso IsReduced h hr),
    fun hr => ObjectProperty.prop_of_iso IsReduced h.symm (he.mpr hr)⟩

private lemma tensor_one_ne_zero_of_flat_quotient {R K₀ K C B D : Type*}
    [CommRing R] [Field K₀] [Field K] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] [AddCommGroup D] [Module R D]
    [Algebra R K₀] [Algebra R K] [Module.Free R C] [Module.Flat R D]
    (i : C →ₗ[R] B) (q : B →ₗ[R] D)
    (hi : Function.Injective i) (hiq : Function.Exact i q) (hq : Function.Surjective q)
    (h₀ : Nontrivial (K₀ ⊗[R] C)) (h : B) (hi1 : i 1 = h) :
    (1 : K) ⊗ₜ[R] h ≠ 0 := by
  have : Nontrivial (K ⊗[R] C) := nontrivial_tensor_of_free h₀
  have hinj : Function.Injective (LinearMap.lTensor K i) :=
    tensor_injective_of_flat_quotient i q hi hiq hq
  have hone : (1 : K) ⊗ₜ[R] (1 : C) ≠ 0 := by
    rw [← Algebra.TensorProduct.one_def]
    exact one_ne_zero
  have himage : LinearMap.lTensor K i ((1 : K) ⊗ₜ[R] (1 : C)) =
      (1 : K) ⊗ₜ[R] h := by
    simp [LinearMap.lTensor_tmul, hi1]
  exact fun hz => hone (hinj (by rw [himage, hz, map_zero]))

private lemma exists_nonzero_nilpotent_fraction_lift {R B K : Type*}
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Field K] [Algebra R K]
    [IsFractionRing R K]
    (hnr : ¬ _root_.IsReduced (K ⊗[R] B)) :
    ∃ b : B, IsNilpotent ((1 : K) ⊗ₜ[R] b) ∧ (1 : K) ⊗ₜ[R] b ≠ 0 := by
  rw [isReduced_iff] at hnr
  push Not at hnr
  obtain ⟨a, ha, ha0⟩ := hnr
  let g : B →ₗ[R] K ⊗[R] B := TensorProduct.mk R K B 1
  have : IsLocalizedModule (nonZeroDivisors R) g := inferInstance
  obtain ⟨⟨b, c⟩, hcb⟩ := IsLocalizedModule.surj (nonZeroDivisors R) g a
  have hcb' : (c : R) • a = g b := by
    simpa only [Submonoid.smul_def] using hcb
  have hc : c.1 ≠ 0 := nonZeroDivisors.ne_zero c.2
  have hcK : algebraMap R K c.1 ≠ 0 := fun he =>
    hc (IsFractionRing.injective R K (by simp at he))
  have hsc : c.1 • a = (algebraMap R K c.1) • a :=
    (IsScalarTower.algebraMap_smul K c.1 a).symm
  have hnil : IsNilpotent (g b) := by
    obtain ⟨n, hn⟩ := ha
    refine ⟨n, ?_⟩
    rw [← hcb', hsc, smul_pow, hn, smul_zero]
  have hne : g b ≠ 0 := by
    intro hb
    have hzero : (algebraMap R K c.1) • a = 0 := by
      rw [← hsc, hcb', hb]
    exact ha0 ((smul_eq_zero.mp hzero).resolve_left hcK)
  refine ⟨b, ?_, hne⟩
  simpa [g] using hnil

private lemma exists_nonzero_scalar_annihilating_power {R B K : Type*}
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Field K] [Algebra R K]
    [IsFractionRing R K] (b : B)
    (hnil : IsNilpotent ((1 : K) ⊗ₜ[R] b)) :
    ∃ r : R, r ≠ 0 ∧ ∃ n : ℕ, algebraMap R B r * b ^ n = 0 := by
  let g : B →ₗ[R] K ⊗[R] B := TensorProduct.mk R K B 1
  have : IsLocalizedModule (nonZeroDivisors R) g := inferInstance
  have hnil' : IsNilpotent
      (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B) b) := by
    simpa only [Algebra.TensorProduct.includeRight_apply] using hnil
  obtain ⟨n, hn⟩ := hnil'
  have heq : g (b ^ n) = g 0 := by
    show Algebra.TensorProduct.includeRight (R := R) (A := K) (B := B) (b ^ n) = _
    rw [map_pow, hn, map_zero]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors R) g).mp heq
  exact ⟨c.1, nonZeroDivisors.ne_zero c.2, n,
    by simpa [Submonoid.smul_def, Algebra.smul_def] using hc⟩

private lemma no_nonzero_scalar_annihilator_of_tmul_ne_zero {R B K : Type*}
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Field K] [Algebra R K]
    [IsFractionRing R K] (b : B) (hb : (1 : K) ⊗ₜ[R] b ≠ 0) :
    ∀ r : R, r ≠ 0 → algebraMap R B r * b ≠ 0 := by
  intro r hr he
  have hrK : algebraMap R K r ≠ 0 := fun h => hr (IsFractionRing.injective R K (by simpa using h))
  have hmap : (1 : K) ⊗ₜ[R] (algebraMap R B r * b) =
      (algebraMap R K r) • ((1 : K) ⊗ₜ[R] b) := by
    rw [← Algebra.smul_def]
    simpa [Algebra.smul_def] using (TensorProduct.tmul_smul (R := R) r (1 : K) b)
  have he' : algebraMap R K r • ((1 : K) ⊗ₜ[R] b) = 0 := by
    rw [← hmap, he, TensorProduct.tmul_zero]
  exact hb ((smul_eq_zero.mp he').resolve_left hrK)

private lemma algebraMap_tensor_right_apply {B Sf : Type*} [CommRing B] [CommRing Sf]
    [Algebra B Sf] (x : B) : algebraMap B (Sf ⊗[B] B) x = (1 : Sf) ⊗ₜ[B] x :=
  ((Algebra.TensorProduct.includeRight (R := B) (A := Sf) (B := B)).commutes x).symm.trans
    (Algebra.TensorProduct.includeRight_apply x)

private lemma algebraMap_ne_zero_away_of_no_scalar_annihilator
    {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    (f : R) (hf : f ≠ 0) (b : B)
    (hno : ∀ r : R, r ≠ 0 → algebraMap R B r * b ≠ 0) :
    algebraMap B
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) ⊗[B] B) b ≠ 0 := by
  let Sf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f))
  let Bf := Sf ⊗[B] B
  let g : B →ₗ[B] Bf := TensorProduct.mk B Sf B 1
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) g := inferInstance
  have hgb : algebraMap B Bf b = g b := algebraMap_tensor_right_apply b
  intro hz
  change algebraMap B Bf b = 0 at hz
  have hg : g b = g 0 := by
    rw [← hgb]
    simpa using hz
  obtain ⟨c, hc⟩ :=
    (IsLocalizedModule.eq_iff_exists
      (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) g).mp hg
  have hc' : c.1 * b = 0 := by simpa [Submonoid.smul_def, Algebra.smul_def] using hc
  obtain ⟨r, hr, hrc⟩ := (Submonoid.mem_map).mp c.2
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff r f).mp hr
  rw [← hrc, ← hn] at hc'
  exact hno (f ^ n) (pow_ne_zero _ hf) (by simpa using hc')

private lemma nontrivial_tensor_of_nonzero_free {R K M : Type*} [CommRing R]
    [Field K] [AddCommGroup M] [Module R M] [Algebra R K] [Module.Free R M]
    (m : M) (hm : m ≠ 0) : Nontrivial (K ⊗[R] M) := by
  have : Nontrivial M := ⟨⟨m, 0, hm⟩⟩
  let b := Module.Free.chooseBasis R M
  obtain ⟨i⟩ := b.index_nonempty
  exact ⟨b.baseChange K i, 0, (b.baseChange K).ne_zero i⟩

private lemma not_isReduced_tensor_of_flat_quotient {R K₀ K C B D : Type*}
    [CommRing R] [Field K₀] [Field K] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] [AddCommGroup D] [Module R D]
    [Algebra R K₀] [Algebra R K] [Module.Free R C] [Module.Flat R D]
    (i : C →ₗ[R] B) (q : B →ₗ[R] D)
    (hi : Function.Injective i) (hiq : Function.Exact i q) (hq : Function.Surjective q)
    (h₀ : Nontrivial (K₀ ⊗[R] C)) (h : B) (hi1 : i 1 = h) (hnil : IsNilpotent h) :
    ¬ _root_.IsReduced (K ⊗[R] B) := by
  apply not_isReduced_of_nilpotent_mul_ne_zero (1 ⊗ₜ[R] h) ?_ ?_
  · exact hnil.map (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B)
  · exact ⟨1, by simpa using
      tensor_one_ne_zero_of_flat_quotient i q hi hiq hq h₀ h hi1⟩

private noncomputable def mulLiftOfAnnihilator {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (h : B) :
    (B ⧸ (Submodule.span B {h}).annihilator) →ₗ[R] B := by
  let I : Ideal B := (Submodule.span B {h}).annihilator
  let f : B →ₗ[B] B := LinearMap.mulLeft B h
  have hI : I ≤ f.ker := by
    intro x hx
    change h * x = 0
    rw [mul_comm]
    exact (Submodule.mem_annihilator_span_singleton h x).mp hx
  exact (I.liftQ f hI).restrictScalars R

private theorem mulLiftOfAnnihilator_apply {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (h x : B) :
    mulLiftOfAnnihilator (R := R) h
      (Ideal.Quotient.mk ((Submodule.span B {h}).annihilator) x) = h * x := by
  unfold mulLiftOfAnnihilator
  let I : Ideal B := (Submodule.span B {h}).annihilator
  let f : B →ₗ[B] B := LinearMap.mulLeft B h
  have hI : I ≤ f.ker := by
    intro x hx
    show h * x = 0
    rw [mul_comm]
    exact (Submodule.mem_annihilator_span_singleton h x).mp hx
  show (I.liftQ f hI) (Submodule.Quotient.mk x) = h * x
  rw [Submodule.liftQ_apply]
  simp [f, LinearMap.mulLeft]

private lemma mulLiftOfAnnihilator_one {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (h : B) : mulLiftOfAnnihilator (R := R) h 1 = h := by
  simpa using mulLiftOfAnnihilator_apply (R := R) h 1

private lemma mulLiftOfAnnihilator_shortExact {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (h : B) :
    Function.Injective (mulLiftOfAnnihilator (R := R) h) ∧
      Function.Exact (mulLiftOfAnnihilator (R := R) h)
        (((Submodule.span B {h}).mkQ).restrictScalars R) ∧
      Function.Surjective (((Submodule.span B {h}).mkQ).restrictScalars R) := by
  let I : Ideal B := (Submodule.span B {h}).annihilator
  let J : Ideal B := Ideal.span {h}
  let q := J.mkQ.restrictScalars R
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hab : h * a = h * b := by
      rwa [mulLiftOfAnnihilator_apply, mulLiftOfAnnihilator_apply] at hxy
    apply Ideal.Quotient.eq.mpr
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    linear_combination hab
  · rw [LinearMap.exact_iff]
    apply le_antisymm
    · intro x hx
      have hxJ : x ∈ J := by simpa [q, J] using hx
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hxJ
      refine ⟨Ideal.Quotient.mk I c, ?_⟩
      rw [mulLiftOfAnnihilator_apply]
      exact hc.symm
    · rintro x ⟨c, rfl⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [mulLiftOfAnnihilator_apply]
      show h * b ∈ J.mkQ.ker
      rw [J.ker_mkQ]
      exact (Ideal.mem_span_singleton).2 (dvd_mul_of_dvd_left (dvd_refl h) b)
  · exact J.mkQ_surjective

private lemma baseChange_mulLiftOfAnnihilator_one {B : Type*} (Sf : Type*) [CommRing B]
    [CommRing Sf] [Algebra B Sf] (h : B) :
    (mulLiftOfAnnihilator (R := B) h).baseChange Sf
      (1 : Sf ⊗[B] (B ⧸ (Submodule.span B {h}).annihilator)) = algebraMap B (Sf ⊗[B] B) h := by
  rw [Algebra.TensorProduct.one_def, LinearMap.baseChange_tmul, mulLiftOfAnnihilator_one,
    algebraMap_tensor_right_apply]

private lemma exists_common_freeAway_for_annihilator_quotient
    {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (h : B) :
    ∃ f : R, f ≠ 0 ∧
      Algebra.IsFinitePresentationFreeAway R B
        (B ⧸ (Submodule.span B {h}).annihilator) f ∧
      Algebra.IsFinitePresentationFreeAway R B (B ⧸ Ideal.span {h}) f := by
  let C := B ⧸ (Submodule.span B {h}).annihilator
  let D := B ⧸ Ideal.span {h}
  obtain ⟨f₁, hf₁, hC⟩ :=
    Algebra.exists_ne_zero_isFinitePresentationFreeAway (R := R) (S := B) (M := C)
  obtain ⟨f₂, hf₂, hD⟩ :=
    Algebra.exists_ne_zero_isFinitePresentationFreeAway (R := R) (S := B) (M := D)
  refine ⟨f₁ * f₂, mul_ne_zero hf₁ hf₂, ?_, ?_⟩
  · exact hC.of_dvd ⟨f₂, rfl⟩
  · exact hD.of_dvd ⟨f₁, by rw [mul_comm]⟩

private lemma not_isReduced_fiber_of_freeAway
    {R B K₀ K : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Field K₀] [Field K] (f : R) [Algebra (Localization.Away f) K₀]
    [IsFractionRing (Localization.Away f) K₀] [Algebra (Localization.Away f) K]
    (h : B)
    (hC : Algebra.IsFinitePresentationFreeAway R B
      (B ⧸ (Submodule.span B {h}).annihilator) f)
    (hD : Algebra.IsFinitePresentationFreeAway R B (B ⧸ Ideal.span {h}) f)
    (h₀ : Nontrivial (K₀ ⊗[Localization.Away f]
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) ⊗[B]
        (B ⧸ (Submodule.span B {h}).annihilator))))
    (hnil : IsNilpotent (algebraMap B
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) ⊗[B] B) h)) :
    ¬ _root_.IsReduced (K ⊗[Localization.Away f]
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) ⊗[B] B)) := by
  let Rf := Localization.Away f
  let Sf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f))
  let C := B ⧸ (Submodule.span B {h}).annihilator
  let D := B ⧸ Ideal.span {h}
  let Cf := Sf ⊗[B] C
  let Bf := Sf ⊗[B] B
  let Df := Sf ⊗[B] D
  let i₀ := mulLiftOfAnnihilator (R := B) h
  let q₀ := (Submodule.span B {h}).mkQ
  let i : Cf →ₗ[Rf] Bf := (i₀.baseChange Sf).restrictScalars Rf
  let q : Bf →ₗ[Rf] Df := (q₀.baseChange Sf).restrictScalars Rf
  have hseq := mulLiftOfAnnihilator_shortExact (R := B) h
  have hi : Function.Injective i := by
    show Function.Injective (i₀.baseChange Sf)
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap i₀ hseq.1
  have hExact : Function.Exact i q := by
    show Function.Exact (i₀.baseChange Sf) (q₀.baseChange Sf)
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact Sf hseq.2.1
  have hsurj : Function.Surjective q := by
    show Function.Surjective (q₀.baseChange Sf)
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective Sf hseq.2.2
  have : Module.Free Rf Cf := hC.2.2.2
  have : Module.Free Rf Df := hD.2.2.2
  have : Module.Flat Rf Df := Module.Flat.of_free
  have hi1 : i 1 = algebraMap B Bf h := baseChange_mulLiftOfAnnihilator_one Sf h
  exact not_isReduced_tensor_of_flat_quotient i q hi hExact hsurj h₀
    (algebraMap B Bf h) hi1 hnil

private lemma exists_away_all_affine_fibers_not_isReduced
    {R B K : Type u} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] [Field K] [Algebra R K] [IsFractionRing R K]
    (hnr : ¬ _root_.IsReduced (K ⊗[R] B)) :
    ∃ f : R, f ≠ 0 ∧ ∀ p : Spec (.of (Localization.Away f)),
      ¬ IsReduced
        ((Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away f)
          (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f))
            ⊗[B] B)))).fiber p) := by
  obtain ⟨b, hnilFrac, hneFrac⟩ := exists_nonzero_nilpotent_fraction_lift hnr
  obtain ⟨r, hr, n, hkill⟩ := exists_nonzero_scalar_annihilating_power b hnilFrac
  have hno := no_nonzero_scalar_annihilator_of_tmul_ne_zero b hneFrac
  obtain ⟨g, hg, hC₀, hD₀⟩ := exists_common_freeAway_for_annihilator_quotient (R := R) (B := B) b
  let f := g * r
  have hf : f ≠ 0 := mul_ne_zero hg hr
  let C := B ⧸ (Submodule.span B {b}).annihilator
  let D := B ⧸ Ideal.span {b}
  have hC : Algebra.IsFinitePresentationFreeAway R B C f := hC₀.of_dvd ⟨r, rfl⟩
  have hD : Algebra.IsFinitePresentationFreeAway R B D f := hD₀.of_dvd ⟨r, rfl⟩
  let Rf := Localization.Away f
  let Sf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f))
  let Bf := Sf ⊗[B] B
  let Cf := Sf ⊗[B] C
  have : Module.Free Rf Cf := hC.2.2.2
  let i₀ := mulLiftOfAnnihilator (R := B) b
  let i : Cf →ₗ[Rf] Bf := (i₀.baseChange Sf).restrictScalars Rf
  have hi1 : i 1 = algebraMap B Bf b := baseChange_mulLiftOfAnnihilator_one Sf b
  have hlocal : algebraMap B Bf b ≠ 0 := algebraMap_ne_zero_away_of_no_scalar_annihilator f hf b hno
  have h1 : (1 : Cf) ≠ 0 := fun hzero => hlocal (by rw [← hi1, hzero, map_zero])
  have : IsDomain Rf := IsLocalization.Away.isDomain (S := Rf) hf
  let K₀ := FractionRing Rf
  have h₀ : Nontrivial (K₀ ⊗[Rf] Cf) := nontrivial_tensor_of_nonzero_free (1 : Cf) h1
  have hrunit : IsUnit (algebraMap R Rf r) := by
    have hprod : IsUnit (algebraMap R Rf g * algebraMap R Rf r) := by
      simpa [f, map_mul] using IsLocalization.Away.algebraMap_isUnit (S := Rf) f
    exact (IsUnit.mul_iff.mp hprod).2
  have hunitBf : IsUnit (algebraMap R Bf r) := by
    rw [IsScalarTower.algebraMap_apply R Rf Bf r]
    exact hrunit.map _
  have hkillBf : algebraMap R Bf r * (algebraMap B Bf b) ^ n = 0 := by
    rw [IsScalarTower.algebraMap_apply R B Bf r]
    simpa only [map_mul, map_pow, map_zero] using congrArg (algebraMap B Bf) hkill
  have hnilBf : IsNilpotent (algebraMap B Bf b) :=
    ⟨n, hunitBf.mul_left_cancel (by simpa using hkillBf)⟩
  refine ⟨f, hf, fun p => ?_⟩
  change PrimeSpectrum Rf at p
  have : p.asIdeal.IsPrime := p.isPrime
  let Kp := p.asIdeal.ResidueField
  exact fun hred => not_isReduced_fiber_of_freeAway (R := R) (B := B) (K₀ := K₀) (K := Kp)
    f b hC hD h₀ hnilBf ((isReduced_affine_fiber_iff (R := Rf) (S := Bf) p).mp hred)

private lemma spec_away_square_isPullback {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (f : R) :
    let Rf := Localization.Away f
    let Sf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f))
    let Bf := Sf ⊗[B] B
    let : Algebra B Bf := Algebra.TensorProduct.rightAlgebra (R := B) (A := Sf) (B := B)
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap B Bf)))
      (Spec.map (CommRingCat.ofHom (algebraMap Rf Bf)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R Rf))) := by
  dsimp only
  let Rf := Localization.Away f
  let Sf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f))
  let Bf := Sf ⊗[B] B
  let T := B ⊗[R] Rf
  let : Algebra Rf T := Algebra.TensorProduct.rightAlgebra
  let : Algebra B Bf := Algebra.TensorProduct.rightAlgebra (R := B) (A := Sf) (B := B)
  have : IsLocalization.Away (algebraMap R B f) Sf := by
    simp only [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    infer_instance
  let : Algebra Rf Sf := inferInstance
  let : IsScalarTower R Rf Sf := inferInstance
  have : IsLocalization.Away (algebraMap R B f) Bf :=
    IsLocalization.Away.tensorRight (R := B) (S := B) (algebraMap R B f) Sf
  have : IsLocalization.Away (algebraMap R B f) T :=
    IsLocalization.Away.tensor (R := R) (S := B) f Rf
  let eBA : Bf ≃ₐ[B] T := IsLocalization.algEquiv (Submonoid.powers (algebraMap R B f)) Bf T
  let F : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let jY : Spec (.of Rf) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Rf))
  let jX : Spec (.of Bf) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (algebraMap B Bf))
  let F' : Spec (.of Bf) ⟶ Spec (.of Rf) := Spec.map (CommRingCat.ofHom (algebraMap Rf Bf))
  let e : Spec (.of Bf) ≅ pullback F jY :=
    Scheme.Spec.mapIso eBA.toRingEquiv.symm.toCommRingCatIso.op ≪≫ (pullbackSpecIso R B Rf).symm
  have hbase (x : R) : algebraMap B Bf (algebraMap R B x) =
      algebraMap Rf Bf (algebraMap R Rf x) := by
    show Algebra.TensorProduct.includeRight (algebraMap R B x) = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.algebraMap_apply]
    calc
      (1 : Sf) ⊗ₜ[B] algebraMap R B x =
          (algebraMap R Sf x) ⊗ₜ[B] (1 : B) := by
            calc
              _ = (1 : Sf) ⊗ₜ[B] ((algebraMap R B x) • (1 : B)) := by simp
              _ = ((algebraMap R B x) • (1 : Sf)) ⊗ₜ[B] (1 : B) :=
                TensorProduct.tmul_smul _ _ _
              _ = (algebraMap B Sf (algebraMap R B x)) ⊗ₜ[B] (1 : B) := by
                simp [Algebra.smul_def]
              _ = (algebraMap R Sf x) ⊗ₜ[B] (1 : B) := by
                rw [IsScalarTower.algebraMap_apply R B Sf x]
      _ = (algebraMap Rf Sf (algebraMap R Rf x)) ⊗ₜ[B] (1 : B) := by
            rw [IsScalarTower.algebraMap_apply R Rf Sf x]
  have hsq : CommSq jX F' F jY := ⟨by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext hbase))⟩
  show IsPullback jX F' F jY
  refine IsPullback.of_iso_pullback hsq e ?_ ?_
  all_goals
    simp only [e, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc]
    first | rw [pullbackSpecIso_inv_fst] | rw [pullbackSpecIso_inv_snd]
    simp only [Functor.mapIso_hom, Iso.op_hom]
    show Scheme.Spec.map _ ≫ Scheme.Spec.map _ = Scheme.Spec.map _
    rw [← Scheme.Spec.map_comp]
    apply congrArg Scheme.Spec.map
    apply Quiver.Hom.unop_inj
    apply CommRingCat.hom_ext
  · ext b
    exact eBA.symm.commutes b
  · apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    show eBA.toRingEquiv.symm (algebraMap Rf T (algebraMap R Rf x)) =
      algebraMap Rf Bf (algebraMap R Rf x)
    rw [← IsScalarTower.algebraMap_apply R Rf T, IsScalarTower.algebraMap_apply R B T]
    exact (eBA.symm.commutes (algebraMap R B x)).trans (hbase x)

private lemma isReduced_fiber_iff_of_isPullback {P X Y Z : Scheme.{u}}
    {i : P ⟶ X} {f' : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hsq : IsPullback i f' f g) (y : Y) [IsIso (g.residueFieldMap y)] :
    IsReduced (f'.fiber y) ↔ IsReduced (f.fiber (g y)) := by
  let m := pullback.map f' (Y.fromSpecResidueField y) f
    (Z.fromSpecResidueField (g y)) i (Spec.map (g.residueFieldMap y)) g
    hsq.w.symm (by simp)
  have hm : IsIso m := by
    simpa [m] using (isPullback_fiberToSpecResidueField_of_isPullback hsq y).isIso_fst_of_isIso
  let e := @asIso _ _ _ _ m hm
  exact ⟨ObjectProperty.prop_of_iso IsReduced e,
    ObjectProperty.prop_of_iso IsReduced e.symm⟩

private lemma exists_open_forall_not_isReduced_fiber_affine
    {R B : Type u} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B]
    (h : ¬ IsReduced ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiber
      (genericPoint (Spec (.of R))))) :
    ∃ W : Set (Spec (.of R)), IsOpen W ∧ W.Nonempty ∧
      ∀ p ∈ W, ¬ IsReduced ((Spec.map
        (CommRingCat.ofHom (algebraMap R B))).fiber p) := by
  let η : PrimeSpectrum R := ⊥
  have : η.asIdeal.IsPrime := η.isPrime
  let K := η.asIdeal.ResidueField
  let : Field (η.asIdeal.ResidueField) := inferInstance
  let : Algebra R (η.asIdeal.ResidueField) := inferInstance
  have : IsFractionRing R (η.asIdeal.ResidueField) := by
    simpa [η] using (inferInstance : IsFractionRing R (⊥ : Ideal R).ResidueField)
  have hη : genericPoint (Spec (.of R)) = η := genericPoint_eq_bot_of_affine (.of R)
  have hnr : ¬ _root_.IsReduced (K ⊗[R] B) :=
    (isReduced_affine_fiber_iff (R := R) (S := B) η).not.mp (by simpa [hη] using h)
  obtain ⟨a, ha, hfib⟩ :=
    exists_away_all_affine_fibers_not_isReduced (R := R) (B := B) hnr
  let Rf := Localization.Away a
  let Sf := Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers a))
  let Bf := Sf ⊗[B] B
  let : Algebra B Bf := Algebra.TensorProduct.rightAlgebra (R := B) (A := Sf) (B := B)
  let F : Spec (.of B) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  let jY : Spec (.of Rf) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R Rf))
  let jX : Spec (.of Bf) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B Bf))
  let F' : Spec (.of Bf) ⟶ Spec (.of Rf) :=
    Spec.map (CommRingCat.ofHom (algebraMap Rf Bf))
  have hpb : IsPullback jX F' F jY := by
    simpa [Rf, Sf, Bf, F, F', jX, jY] using
      (spec_away_square_isPullback (R := R) (B := B) a)
  let W : (Spec (.of R)).Opens := jY.opensRange
  refine ⟨W, W.2, ?_, ?_⟩
  · have : IsDomain Rf := IsLocalization.Away.isDomain (S := Rf) ha
    exact ⟨jY (genericPoint (Spec (.of Rf))), ⟨_, rfl⟩⟩
  · intro y hy
    obtain ⟨q, hq⟩ := Set.mem_range.mp hy
    rw [← hq]
    intro hred
    exact hfib q ((isReduced_fiber_iff_of_isPullback hpb q).mpr hred)

private lemma exists_affine_nonreduced_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (h : ¬ IsReduced (f.fiber y)) :
    ∃ i : X.affineCover.I₀, ¬ IsReduced ((X.affineCover.f i ≫ f).fiber y) := by
  by_contra! h'
  apply h
  let 𝒰 := X.affineCover.pullback₁ (f.fiberι y)
  have (i : 𝒰.I₀) : IsReduced (𝒰.X i) := by
    let e : 𝒰.X i ≅ (X.affineCover.f i ≫ f).fiber y :=
      pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) _
    exact ObjectProperty.prop_of_iso IsReduced e.symm (h' i)
  exact IsReduced.of_openCover _ 𝒰

private lemma exists_open_forall_not_isReduced_fiber_spec_target
    {X : Scheme.{u}} {R : CommRingCat.{u}} [IsDomain R]
    (f : X ⟶ Spec R) [LocallyOfFiniteType f]
    (h : ¬ IsReduced (f.fiber (genericPoint (Spec R)))) :
    ∃ V : Set (Spec R), IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, ¬ IsReduced (f.fiber y) := by
  obtain ⟨i, hi⟩ := exists_affine_nonreduced_fiber f _ h
  let S := X.affineOpenCover.X i
  let : IsOpenImmersion (X.affineCover.f i) := X.affineCover.map_prop i
  let : LocallyOfFiniteType (X.affineCover.f i) :=
    locallyOfFiniteType_of_isOpenImmersion _
  let : LocallyOfFiniteType (X.affineCover.f i ≫ f) := locallyOfFiniteType_comp _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⟶ S, Spec.map φ = X.affineCover.f i ≫ f :=
    ⟨_, Spec.map_preimage _⟩
  let : Algebra R S := φ.hom.toAlgebra
  have : LocallyOfFiniteType (Spec.map φ) :=
    hφ.symm ▸ (inferInstance : LocallyOfFiniteType (X.affineCover.f i ≫ f))
  have : Algebra.FiniteType R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  have hφnr : ¬ IsReduced ((Spec.map (CommRingCat.ofHom (algebraMap R S))).fiber
      (genericPoint (Spec R))) := by
    show ¬ IsReduced ((Spec.map φ).fiber (genericPoint (Spec R)))
    exact hφ ▸ hi
  obtain ⟨V, hVo, hVne, hV⟩ :=
    exists_open_forall_not_isReduced_fiber_affine (R := R) (B := S) hφnr
  refine ⟨V, hVo, hVne, ?_⟩
  intro y hy hred
  apply hV y hy
  show IsReduced ((Spec.map φ).fiber y)
  rw [hφ]
  exact isReduced_fiber_comp (X.affineCover.f i) f y

private lemma exists_open_forall_not_isReduced_fiber_of_isOpenMap {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (a : Z ⟶ Y) [∀ t, IsIso (a.residueFieldMap t)] (ha : IsOpenMap a) (ζ : Z)
    (h : ¬ IsReduced (f.fiber (a ζ)))
    (H : ¬ IsReduced ((pullback.snd f a).fiber ζ) →
      ∃ V : Set Z, IsOpen V ∧ V.Nonempty ∧ ∀ y ∈ V, ¬ IsReduced ((pullback.snd f a).fiber y)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧ ∀ y ∈ V, ¬ IsReduced (f.fiber y) := by
  obtain ⟨V, hVo, hVne, hV⟩ := H fun hred =>
    h ((isReduced_fiber_iff_of_isPullback (IsPullback.of_hasPullback f a) ζ).mp hred)
  refine ⟨a '' V, ha _ hVo, hVne.image a, ?_⟩
  rintro y ⟨t, ht, rfl⟩ hred
  exact hV t ht
    ((isReduced_fiber_iff_of_isPullback (IsPullback.of_hasPullback f a) t).mpr hred)

private lemma exists_open_forall_not_isReduced_fiber_integral
    {X Y : Scheme.{u}} [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (h : ¬ IsReduced (f.fiber (genericPoint Y))) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, ¬ IsReduced (f.fiber y) := by
  obtain ⟨i, t, -⟩ := Y.affineCover.exists_eq (genericPoint Y)
  let R := Y.affineOpenCover.X i
  let a : Spec R ⟶ Y := Y.affineCover.f i
  have : IsOpenImmersion a := Y.affineCover.map_prop i
  have : Nonempty (Spec R) := ⟨t⟩
  have : IsIntegral (Spec R) := isIntegral_of_isOpenImmersion a
  have : IsDomain R := (affine_isIntegral_iff R).mp inferInstance
  have hη : a (genericPoint (Spec R)) = genericPoint Y :=
    genericPoint_eq_of_isOpenImmersion a
  refine exists_open_forall_not_isReduced_fiber_of_isOpenMap f a a.isOpenEmbedding.isOpenMap
    (genericPoint (Spec R)) (hη ▸ h) fun h' => ?_
  exact exists_open_forall_not_isReduced_fiber_spec_target _ h'

/-- **Stacks Project, Tag 0575.** If the generic fibre of a finite type morphism to an
irreducible scheme is nonreduced, then every fibre over a suitable nonempty open subset of
the target is nonreduced. -/
@[stacks 0575, ega "IV 9.7.2" "more general"]
theorem exists_open_forall_not_isReduced_fiber
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f] (η : Y) (hη : IsGenericPoint η Set.univ)
    (h : ¬ AlgebraicGeometry.IsReduced (f.fiber η)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, ¬ AlgebraicGeometry.IsReduced (f.fiber y) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds Y)
  let a := I.subschemeι
  have ha : Function.Surjective a := by
    rw [← Set.range_eq_univ]
    exact I.range_subschemeι.trans (Scheme.IdealSheafData.coe_support_vanishingIdeal ⊤)
  let e : I.subscheme ≃ₜ Y := a.isClosedEmbedding.isEmbedding.toHomeomorphOfSurjective ha
  have : IrreducibleSpace I.subscheme := e.irreducibleSpace_iff.mpr inferInstance
  have : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have (t : I.subscheme) : IsIso (a.residueFieldMap t) :=
    a.isIso_residueFieldMap_of_surjectiveOnStalks t
  have hη' : a (genericPoint I.subscheme) = η := by
    apply IsGenericPoint.eq _ hη
    simpa only [Set.image_univ, Set.range_eq_univ.mpr ha, closure_univ] using
      (genericPoint_spec I.subscheme).image a.continuous
  exact exists_open_forall_not_isReduced_fiber_of_isOpenMap f a e.isOpenMap
    (genericPoint I.subscheme) (hη' ▸ h) fun h' =>
      exists_open_forall_not_isReduced_fiber_integral _ h'

/-- The locus of geometrically reduced fibres commutes with arbitrary base change. -/
@[stacks 0576]
theorem geometricallyReduced_fiber_set_eq_preimage_of_isPullback
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X) (g : Y' ⟶ Y)
    (h : IsPullback i f' f g) :
    {y' : Y' | GeometricallyReduced (f'.fiberToSpecResidueField y')} =
      g ⁻¹' {y : Y | GeometricallyReduced (f.fiberToSpecResidueField y)} := by
  ext y'
  show GeometricallyReduced (f'.fiberToSpecResidueField y') ↔
    GeometricallyReduced (f.fiberToSpecResidueField (g y'))
  let : Algebra (Y.residueField (g y')) (Y'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  let hp := isPullback_fiberToSpecResidueField_of_isPullback h y'
  have he : IsPullback hp.isoPullback.inv
      (pullback.snd (f.fiberToSpecResidueField (g y')) (Spec.map (g.residueFieldMap y')))
      (f'.fiberToSpecResidueField y') (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨hp.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
  exact ⟨fun hf => (geometricallyReduced_iff_baseChange_fieldExtension
    (Y.residueField (g y')) (Y'.residueField y')
    (f.fiberToSpecResidueField (g y'))).mpr (MorphismProperty.of_isPullback he hf),
    fun hf => MorphismProperty.of_isPullback hp hf⟩

/-- A fibre which is geometrically reduced over the residue field at its point is reduced. -/
theorem isReduced_fiber_of_geometricallyReduced_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (h : GeometricallyReduced (f.fiberToSpecResidueField y)) :
    IsReduced (f.fiber y) :=
  h.geometrically_isReduced (𝟙 _) (𝟙 _) (f.fiberToSpecResidueField y) IsPullback.of_id_fst

end AlgebraicGeometry

end
