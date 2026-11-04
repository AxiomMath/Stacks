module

public import Mathlib
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.Instances.TrivSqZeroExt
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.CompleteLocalRing.CohenStructureTheorem
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.GeometricallyRegular.BaseFieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.FormalSmoothness
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.RegularLocalRing.FlatLocalHom
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksFrontier.RingTheory.TensorProduct.LocalAlgebra
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous

@[expose] public section

/-!
# Formal smoothness and regularity of local homomorphisms

A derivation of a Noetherian local ring extends across a local homomorphism to a complete
Noetherian local ring that is formally smooth for the maximal-ideal-adic topology. For a local
homomorphism `f : A → B` of Noetherian complete local rings, regularity is equivalent to flatness
together with geometric regularity of the special fibre, to flatness together with adic formal
smoothness of the special fibre, and to adic formal smoothness of `f`. By André's theorem the same
equivalences hold for a local homomorphism of Noetherian local rings whose source has a regular
completion map. The special fibre is `IsLocalRing.ResidueField A ⊗[A] B`.

## Main results

* `exists_derivation_extension_of_formallySmoothNAdic`: a derivation extends across a complete,
  adically formally smooth local homomorphism.
* `isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae`: the four
  equivalent characterizations of a regular local homomorphism of Noetherian complete local
  rings.
* `isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae_0h7u`: the four
  equivalent characterizations of a regular local homomorphism of Noetherian local rings whose
  source has a regular completion map.

## References

* [André, *Homomorphismes lisses ou réguliers et diagonales*][Andre-smooth]
* [Stacks Project, Tag 07PL](https://stacks.math.columbia.edu/tag/07PL)
* [Stacks Project, Tag 07PM](https://stacks.math.columbia.edu/tag/07PM)
* [Stacks Project, Tag 0H7U](https://stacks.math.columbia.edu/tag/0H7U)
-/

/-! ### Extending derivations along formally smooth maps -/

section

section

@[expose] public section

/-- Scalar multiplication by an ideal distributes over a product of full modules. -/
private theorem smul_top_prod {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) :
    I • (⊤ : Submodule R (M × N)) =
      Submodule.prod (I • (⊤ : Submodule R M)) (I • (⊤ : Submodule R N)) := by
  apply le_antisymm
  · rw [Submodule.smul_le]
    intro r hr x _
    exact ⟨Submodule.smul_mem_smul hr (Submodule.mem_top : x.1 ∈ (⊤ : Submodule R M)),
      Submodule.smul_mem_smul hr (Submodule.mem_top : x.2 ∈ (⊤ : Submodule R N))⟩
  · intro x hx
    have h₁ : (x.1, (0 : N)) ∈ I • (⊤ : Submodule R (M × N)) := by
      apply Submodule.smul_induction_on
        (p := fun a : M => (a, (0 : N)) ∈ I • (⊤ : Submodule R (M × N))) hx.1
      · intro r hr n hn
        convert Submodule.smul_mem_smul hr
          (show (n, (0 : N)) ∈ (⊤ : Submodule R (M × N)) from Submodule.mem_top) using 1
        simp
      · intro a b ha hb
        simpa only [Prod.mk_add_mk, add_zero] using (I • (⊤ : Submodule R (M × N))).add_mem ha hb
    have h₂ : ((0 : M), x.2) ∈ I • (⊤ : Submodule R (M × N)) := by
      apply Submodule.smul_induction_on
        (p := fun b : N => ((0 : M), b) ∈ I • (⊤ : Submodule R (M × N))) hx.2
      · intro r hr n hn
        convert Submodule.smul_mem_smul hr
          (show ((0 : M), n) ∈ (⊤ : Submodule R (M × N)) from Submodule.mem_top) using 1
        simp
      · intro a b ha hb
        simpa only [Prod.mk_add_mk, zero_add] using (I • (⊤ : Submodule R (M × N))).add_mem ha hb
    convert (I • (⊤ : Submodule R (M × N))).add_mem h₁ h₂ using 1; simp

/-- Congruence modulo `I • ⊤` in a product of modules is congruence in each component. -/
private theorem smodEq_top_prod_iff {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (x y : M × N) :
    x ≡ y [SMOD (I • (⊤ : Submodule R (M × N)))] ↔
      x.1 ≡ y.1 [SMOD (I • (⊤ : Submodule R M))] ∧
        x.2 ≡ y.2 [SMOD (I • (⊤ : Submodule R N))] := by
  simp only [SModEq.sub_mem, smul_top_prod, Submodule.mem_prod, Prod.fst_sub, Prod.snd_sub]

/-- A product of complete modules is complete for the same adic filtration. -/
private theorem isAdicComplete_prod {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) [IsAdicComplete I M] [IsAdicComplete I N] :
    IsAdicComplete I (M × N) := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · constructor
    intro x hx
    have h := fun n => (smodEq_top_prod_iff (I ^ n) x 0).1 (hx n)
    exact Prod.ext (IsHausdorff.haus inferInstance x.1 fun n => (h n).1)
      (IsHausdorff.haus inferInstance x.2 fun n => (h n).2)
  · constructor
    intro f hf
    obtain ⟨l₁, hl₁⟩ := IsPrecomplete.prec inferInstance
      fun {m n} hmn => ((smodEq_top_prod_iff (I ^ m) (f m) (f n)).1 (hf hmn)).1
    obtain ⟨l₂, hl₂⟩ := IsPrecomplete.prec inferInstance
      fun {m n} hmn => ((smodEq_top_prod_iff (I ^ m) (f m) (f n)).1 (hf hmn)).2
    exact ⟨(l₁, l₂), fun n ↦ (smodEq_top_prod_iff (I ^ n) _ _).2 ⟨hl₁ n, hl₂ n⟩⟩

/-- The dual-number ring is complete for the image of an ideal of its base ring. -/
private theorem isAdicComplete_trivSqZeroExt {B : Type*} [CommRing B] (m : Ideal B)
    [IsAdicComplete m B] :
    IsAdicComplete (m.map (TrivSqZeroExt.inlHom B B)) (TrivSqZeroExt B B) := by
  rw [← TrivSqZeroExt.algebraMap_eq_inlHom]
  exact (IsAdicComplete.map_algebraMap_iff m (TrivSqZeroExt B B)).2
    (show IsAdicComplete m (B × B) from isAdicComplete_prod m)

/-- The dual-number homomorphism determined by a derivation and a base map. -/
private def derivationTangentMap {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (D : Derivation ℤ A A) : A →+* TrivSqZeroExt B B where
  toFun a := (f a, f (D a))
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change f (a + b) = f a + f b
      exact map_add f a b
    · change f (D (a + b)) = f (D a) + f (D b)
      simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change f (a * b) = f a * f b
      exact map_mul f a b
    · change f (D (a * b)) = f a * f (D b) + f (D a) * f b
      simp [D.leibniz, mul_comm]

/-- A ring map into the dual numbers that is a section of `fst` gives a derivation. -/
private theorem exists_derivation_of_fst_eq {S : Type*} [CommRing S]
    (φ : S →+* TrivSqZeroExt S S) (hfst : ∀ s, (φ s).fst = s) :
    ∃ D : Derivation ℤ S S, ∀ s, D s = (φ s).snd := by
  refine ⟨Derivation.mk'
    ((TrivSqZeroExt.sndHom S S).toAddMonoidHom.comp φ.toAddMonoidHom).toIntLinearMap ?_,
    fun s => rfl⟩
  intro a b
  show (φ (a * b)).snd = a * (φ b).snd + b * (φ a).snd
  rw [map_mul]
  show (φ a).fst * (φ b).snd + (φ a).snd * (φ b).fst = a * (φ b).snd + b * (φ a).snd
  rw [hfst a, hfst b]
  ring

/-- Derivations extend along adically formally smooth maps with complete target. -/
private theorem exists_derivation_extension_of_formallySmoothNAdic'.{u, v}
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (m : Ideal B) [IsAdicComplete m B]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} f m) (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (f a) = f (D a) := by
  let E := TrivSqZeroExt B B
  let U := ULift.{max u v} E
  let e : E ≃+* U := ULift.ringEquiv.symm
  let i₀ : Ideal E := m.map (TrivSqZeroExt.inlHom B B)
  let j₀ : Ideal E := TrivSqZeroExt.kerIdeal B B
  let i : Ideal U := i₀.map e
  let j : Ideal U := j₀.map e
  let : TopologicalSpace A := ⊥
  let : TopologicalSpace B := m.adicTopology
  let : TopologicalSpace U := i.adicTopology
  have : DiscreteTopology A := ⟨rfl⟩
  have : IsTopologicalRing A := inferInstance
  have : IsLinearTopology A A := inferInstance
  have : IsTopologicalRing B := m.ringFilterBasis.isTopologicalRing
  have : IsLinearTopology B B := m.isLinearTopology
  have : IsTopologicalRing U := i.ringFilterBasis.isTopologicalRing
  have : IsAdicComplete i U :=
    (IsAdicComplete.congr_ringEquiv i₀ e).2 (isAdicComplete_trivSqZeroExt m)
  have hj2 : j ^ 2 = ⊥ := by
    rw [← Ideal.map_pow, TrivSqZeroExt.kerIdeal_sq]
    simp
  have hi : IsAdic i := rfl
  have hm : IsAdic m := rfl
  have hf : IsFormallySmooth.{max u v} f :=
    (isFormallySmooth_iff_formallySmoothNAdic f m hm).mpr hfs
  let F₀ : E →+* B := (TrivSqZeroExt.fstHom B B B).toRingHom
  let F : U →+* B := F₀.comp e.symm.toRingHom
  have hI₀ : i₀ ≤ m.comap F₀ := by
    show m.map (TrivSqZeroExt.inlHom B B) ≤ m.comap F₀
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    simpa [F₀, RingHom.comp_apply] using hb
  have hIF : i ≤ m.comap F := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).mp hx
    exact hI₀ hy
  have hF : Continuous F := by
    apply (RingHom.continuous_adic_iff F i m).mpr
    refine ⟨1, by omega, ?_⟩
    intro x hx
    exact hIF (by simpa using hx)
  have hjker : j = RingHom.ker F := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective e e.surjective).mp hx
      exact hy
    · intro hx
      have hy : e.symm x ∈ j₀ := hx
      have he : x = e (e.symm x) := (e.apply_symm_apply x).symm
      rw [he]
      exact Ideal.mem_map_of_mem e hy
  have : T2Space B := (IsAdic.isHausdorff_iff hm).mp inferInstance
  have hjClosed : IsClosed (j : Set U) := by
    rw [hjker]
    show IsClosed (F ⁻¹' {0})
    exact isClosed_singleton.preimage hF
  let inlU : B →+* U := e.toRingHom.comp (TrivSqZeroExt.inlHom B B)
  let gA : A →+* U := e.toRingHom.comp (derivationTangentMap f D)
  let ψ : B →+* U ⧸ j := (Ideal.Quotient.mk j).comp inlU
  have hInlU : Continuous inlU := by
    apply (RingHom.continuous_adic_iff inlU m i).mpr
    refine ⟨1, by omega, ?_⟩
    intro x hx
    apply Ideal.mem_map_of_mem e
    apply Ideal.mem_map_of_mem (TrivSqZeroExt.inlHom B B)
    simpa using hx
  have hψ : Continuous ψ := continuous_quot_mk.comp hInlU
  have hcomm : ψ.comp f = (Ideal.Quotient.mk j).comp gA := by
    ext a
    show Ideal.Quotient.mk j (inlU (f a)) = Ideal.Quotient.mk j (gA a)
    apply (Ideal.Quotient.eq).2
    rw [hjker]
    show F (inlU (f a) - gA a) = 0
    show f a - f a = 0
    exact sub_self _
  obtain ⟨φ, hφcont, hφf, hφψ⟩ :=
    exists_continuous_lift_of_isFormallySmooth_of_isAdic
      f m hm hf i hi j hjClosed 2 (by omega) (by simp [hj2])
      gA (continuous_of_discreteTopology) ψ hψ hcomm
  let φ₀ : B →+* E := e.symm.toRingHom.comp φ
  have hfst (b : B) : (φ₀ b).fst = b := by
    have hh : Ideal.Quotient.mk j (φ b) = Ideal.Quotient.mk j (inlU b) :=
      congrArg (fun h : B →+* U ⧸ j => h b) hφψ
    have hx := (Ideal.Quotient.eq.mp hh)
    rw [hjker] at hx
    change F (φ b - inlU b) = 0 at hx
    change (φ₀ b).fst - b = 0 at hx
    exact sub_eq_zero.mp hx
  obtain ⟨D', hD'⟩ := exists_derivation_of_fst_eq φ₀ hfst
  refine ⟨D', fun a ↦ ?_⟩
  have hh : φ (f a) = gA a := congrArg (fun h : A →+* U => h a) hφf
  rw [hD']
  show (e.symm (φ (f a))).snd = f (D a)
  rw [hh]
  rfl

/-- A derivation of a Noetherian local ring extends across a local homomorphism to a complete
Noetherian local ring that is formally smooth for its maximal-ideal-adic topology. -/
@[stacks 07PL]
public theorem exists_derivation_extension_of_formallySmoothNAdic.{u, v}
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hfs : RingHom.FormallySmoothNAdic.{max u v, u, v} f (IsLocalRing.maximalIdeal B))
    (D : Derivation ℤ A A) :
    ∃ D' : Derivation ℤ B B, ∀ a : A, D' (f a) = f (D a) :=
  exists_derivation_extension_of_formallySmoothNAdic' f (IsLocalRing.maximalIdeal B) hfs D

end

end

end

/-! ### Regularity of complete local homomorphisms -/

section

section


open scoped TensorProduct

open IsLocalRing

universe u v w

private theorem flat_geometricallyRegular_specialFiber_of_isRegularRingHom
    {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] (h : IsRegularRingHom (algebraMap A B)) :
    Module.Flat A B ∧
      Algebra.IsGeometricallyRegular (ResidueField A) (ResidueField A ⊗[A] B) := by
  obtain ⟨hf, h⟩ := isRegularRingHom_algebraMap_iff.mp h
  refine ⟨(RingHom.flat_algebraMap_iff).mp hf, ⟨?_⟩⟩
  intro K _ _ _
  let k := ResidueField A
  let k' := (maximalIdeal A).ResidueField
  let e : k ≃ₐ[A] k' := AlgEquiv.ofBijective (IsScalarTower.toAlgHom A k k')
    (maximalIdeal A).bijective_algebraMap_quotient_residueField
  let : Algebra k' K := ((algebraMap k K).comp e.symm.toRingHom).toAlgebra
  have : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap k K x = algebraMap k K (e.symm (e x))
    rw [e.symm_apply_apply]
  have : Algebra.EssFiniteType k' K := Algebra.EssFiniteType.of_comp k k' K
  have : Algebra.IsGeometricallyRegular k' (k' ⊗[A] B) := (h (maximalIdeal A)).2
  have : IsRegularRing (K ⊗[k'] (k' ⊗[A] B)) := inferInstance
  let : Algebra A K := ((algebraMap k K).comp (algebraMap A k)).toAlgebra
  have : IsScalarTower A k K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A k' K := IsScalarTower.to₁₃₄ A k k' K
  have : IsRegularRing (K ⊗[A] B) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange A k' K K B).toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange A k K K B).symm.toRingEquiv

@[sga "6 X 7.7" "special case"]
private theorem isRegularLocalRing_of_flat_geometricallyRegular_specialFiber
    {A : Type u} {B : Type v} [CommRing A] [IsRegularLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [Algebra.IsGeometricallyRegular (ResidueField A) (ResidueField A ⊗[A] B)] :
    IsRegularLocalRing B := by
  have : IsRegularRing (ResidueField A ⊗[A] B) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.lid (ResidueField A) (ResidueField A ⊗[A] B)).toRingEquiv
  have : IsRegularRing (ClosedFibre A B) := IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.comm A (ResidueField A) B).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
        (maximalIdeal A)).symm.restrictScalars A)).toRingEquiv
  exact isRegularLocalRing_of_flat_of_closedFibre A B inferInstance
    (IsRegularLocalRing.of_isRegularRing_of_isLocalRing _) inferInstance

private theorem isGeometricallyRegular_of_perfectField
    {k : Type u} {R : Type v} [Field k] [PerfectField k]
    [CommRing R] [Algebra k R] [IsRegularRing R] :
    Algebra.IsGeometricallyRegular k R := by
  constructor
  apply (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k R).mpr
  intro K _ _ _ _
  let e : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    (IsPurelyInseparable.bijective_algebraMap_of_isSeparable k K)
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.lid k R).symm.trans
      (Algebra.TensorProduct.congr e (AlgEquiv.refl : R ≃ₐ[k] R))).toRingEquiv

private theorem isAdicComplete_map_maximalIdeal_of_finite
    {R : Type u} {S : Type v} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete ((maximalIdeal R).map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff, ← AdicCompletion.of_bijective_iff]
  refine ⟨AdicCompletion.of_injective_iff.mpr inferInstance, fun y ↦ ?_⟩
  obtain ⟨t, ht⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite (maximalIdeal R) S y
  have hrange : ∀ s : TensorProduct R (AdicCompletion (maximalIdeal R) R) S,
      AdicCompletion.ofTensorProduct (maximalIdeal R) S s ∈
        LinearMap.range (AdicCompletion.of (maximalIdeal R) S) := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      obtain ⟨r0, hr0⟩ := (AdicCompletion.of_bijective_iff.mpr
        (inferInstance : IsAdicComplete (maximalIdeal R) R)).surjective r
      rw [AdicCompletion.ofTensorProduct_tmul, ← hr0]
      exact ⟨r0 • x, by rw [map_smul]; rfl⟩
    | add a b ha hb =>
      rw [map_add]
      exact (LinearMap.range (AdicCompletion.of (maximalIdeal R) S)).add_mem ha hb
  obtain ⟨x, hx⟩ := hrange t
  exact ⟨x, hx.trans ht⟩

private theorem isRegularRing_tensorProduct_fractionRing
    {A : Type u} {B : Type v} (K : Type w)
    [CommRing A] [CommRing B] [IsRegularRing B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K] : IsRegularRing (K ⊗[A] B) := by
  let : Algebra B (K ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  exact IsRegularRing.of_isLocalization
    (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (K ⊗[A] B)

/-- A regular generic fibre over a perfect field is geometrically regular. -/
private theorem isGeometricallyRegular_genericFiber_of_perfectField
    {A : Type u} {B : Type v} (K : Type w)
    [CommRing A] [IsRegularLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    [Algebra.IsGeometricallyRegular (ResidueField A) (ResidueField A ⊗[A] B)]
    [Field K] [Algebra A K] [IsFractionRing A K] [PerfectField K] :
    Algebra.IsGeometricallyRegular K (K ⊗[A] B) := by
  have : IsRegularLocalRing B :=
    isRegularLocalRing_of_flat_geometricallyRegular_specialFiber (A := A)
  have : IsRegularRing B := (IsLocalRing.isRegularRing_tfae.out 1 3).mp ‹_›
  have : IsRegularRing (K ⊗[A] B) := isRegularRing_tensorProduct_fractionRing K
  exact isGeometricallyRegular_of_perfectField

/-- Derivations extend after a finite base change of a formally smooth complete local algebra. -/
private theorem exists_derivation_extension_tensorProduct
    {A C : Type u} {B : Type v} [CommRing A] [CommRing C]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B] [Algebra A B] [Algebra A C]
    [Module.Finite A C]
    (h : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (maximalIdeal B))
    (D : Derivation ℤ C C) :
    ∃ D' : Derivation ℤ (B ⊗[A] C) (B ⊗[A] C),
      ∀ c : C, D' (1 ⊗ₜ[A] c) = 1 ⊗ₜ[A] D c := by
  have hc := isAdicComplete_map_maximalIdeal_of_finite (R := B) (S := B ⊗[A] C)
  have hs := RingHom.FormallySmoothNAdic.baseChange (R' := C) (maximalIdeal B) h
  exact exists_derivation_extension_of_formallySmoothNAdic'
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom
    ((maximalIdeal B).map (algebraMap B (B ⊗[A] C))) hs D

/-- Derivations extend to localizations. -/
private theorem exists_derivation_extension_of_isLocalization
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (D : Derivation ℤ R R) :
    ∃ D' : Derivation ℤ S S, ∀ r : R,
      D' (algebraMap R S r) = algebraMap R S (D r) := by
  let g := derivationTangentMap (algebraMap R S) D
  have hg : ∀ y : M, IsUnit (g y) := fun y =>
    TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsLocalization.map_units S y)
  let φ : S →+* TrivSqZeroExt S S := IsLocalization.lift hg
  have hfst : (TrivSqZeroExt.fstHom S S S).toRingHom.comp φ = RingHom.id S := by
    apply IsLocalization.ringHom_ext M
    ext r
    show (φ (algebraMap R S r)).fst = algebraMap R S r
    rw [show φ (algebraMap R S r) = g r from IsLocalization.lift_eq hg r]
    rfl
  have hfst' (s : S) : (φ s).fst = s := DFunLike.congr_fun hfst s
  obtain ⟨D', hD'⟩ := exists_derivation_of_fst_eq φ hfst'
  refine ⟨D', fun r => ?_⟩
  rw [hD', show φ (algebraMap R S r) = g r from IsLocalization.lift_eq hg r]
  rfl

/-- A non-p-th-power coefficient is detected by a derivation after a complete formally smooth
extension and localization into an algebra over the fraction field. -/
private theorem exists_derivation_isUnit_of_not_pow_fractionRing
    {A C : Type u} {S : Type v} {M : Type u} {U : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing C] [IsDomain C] [Algebra A C] [Algebra.FiniteType A C]
    {p : ℕ} [Fact p.Prime] [CharP C p]
    [CommRing S] [Algebra C S] (n : Ideal S) [IsAdicComplete n S]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap C S) n)
    [Field M] [Algebra C M] [IsFractionRing C M]
    [CommRing U] [Algebra S U] (Q : Submonoid S) [IsLocalization Q U]
    [Algebra C U] [IsScalarTower C S U] [Algebra M U] [IsScalarTower C M U]
    (f : C) (hf : ¬ ∃ x : M, algebraMap C M f = x ^ p) :
    ∃ D : Derivation ℤ U U, IsUnit (D (algebraMap C U f)) := by
  obtain ⟨D₀, hD₀⟩ :=
    exists_derivation_apply_ne_zero_of_not_pow_fractionRing (R := A) f hf
  obtain ⟨D₁, hD₁⟩ :=
    exists_derivation_extension_of_formallySmoothNAdic' (algebraMap C S) n hfs D₀
  obtain ⟨D₂, hD₂⟩ := exists_derivation_extension_of_isLocalization (S := U) Q D₁
  refine ⟨D₂, ?_⟩
  rw [IsScalarTower.algebraMap_apply C S U, hD₂, hD₁,
    ← IsScalarTower.algebraMap_apply C S U, IsScalarTower.algebraMap_apply C M U]
  exact (isUnit_iff_ne_zero.mpr
    (by simpa only [map_zero] using (IsFractionRing.injective C M).ne hD₀)).map
      (algebraMap M U)

/-- The hypersurface criterion applies to a coefficient detected after localization. -/
private theorem isRegularRing_quotient_polynomial_sub_C_of_not_pow_fractionRing
    {A C : Type u} {S : Type v} {M : Type u} {U : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing C] [IsDomain C] [Algebra A C] [Algebra.FiniteType A C]
    {p : ℕ} [Fact p.Prime] [CharP C p]
    [CommRing S] [Algebra C S] (n : Ideal S) [IsAdicComplete n S]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap C S) n)
    [Field M] [Algebra C M] [IsFractionRing C M]
    [CommRing U] [IsRegularRing U] [Algebra S U]
    (Q : Submonoid S) [IsLocalization Q U]
    [Algebra C U] [IsScalarTower C S U] [Algebra M U] [IsScalarTower C M U]
    (f : C) (hf : ¬ ∃ x : M, algebraMap C M f = x ^ p) (g : Polynomial ℤ) :
    IsRegularRing (Polynomial U ⧸ Ideal.span
      {g.map (algebraMap ℤ U) - Polynomial.C (algebraMap C U f)}) := by
  obtain ⟨D, hD⟩ := exists_derivation_isUnit_of_not_pow_fractionRing
    (A := A) (M := M) (U := U) n hfs Q f hf
  exact isRegularRing_quotient_polynomial_sub_C_of_isUnit_derivation
    (algebraMap C U f) D hD g

open IsPurelyInseparable in
/-- The coefficient of a nontrivial purely inseparable minimal polynomial is not a p-th power. -/
private theorem elemReduct_not_pow_of_elemExponent_pos
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsPurelyInseparable K L] (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    (x : L) (hx : 0 < elemExponent K x) :
    ¬ ∃ y : K, elemReduct K x = y ^ p := by
  rintro ⟨y, hy⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hx)
  have hpow := algebraMap_elemReduct_eq' K p x
  rw [hy, map_pow, hn, pow_succ, pow_mul] at hpow
  have heq : algebraMap K L y = x ^ p ^ n :=
    (frobenius_inj L p) hpow
  have hle : elemExponent K x ≤ n :=
    elemExponent_le_of_pow_mem' p (RingHom.mem_range.mpr ⟨y, heq⟩)
  omega

/-- A coefficient in the fraction field can be detected after clearing denominators by a
p-th power. -/
private theorem exists_derivation_isUnit_of_not_pow_field
    {A C : Type u} {S : Type v} {M : Type u} {U : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing C] [IsDomain C] [Algebra A C] [Algebra.FiniteType A C]
    {p : ℕ} [Fact p.Prime] [CharP C p]
    [CommRing S] [Algebra C S] (n : Ideal S) [IsAdicComplete n S]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap C S) n)
    [Field M] [Algebra C M] [IsFractionRing C M]
    [CommRing U] [Algebra S U] (Q : Submonoid S) [IsLocalization Q U]
    [Algebra C U] [IsScalarTower C S U] [Algebra M U] [IsScalarTower C M U]
    (f : M) (hf : ¬ ∃ x : M, f = x ^ p) :
    ∃ D : Derivation ℤ U U, IsUnit (D (algebraMap M U f)) := by
  obtain ⟨a, d, hd, heq⟩ := IsFractionRing.div_surjective C f
  have hdM : algebraMap C M d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let c := a * d ^ (p - 1)
  have hc : algebraMap C M c = f * (algebraMap C M d) ^ p := by
    rw [← heq]
    simp only [c, map_mul, map_pow]
    rw [show (algebraMap C M d) ^ p =
      (algebraMap C M d) ^ (p - 1) * algebraMap C M d by
        rw [← pow_succ, Nat.sub_add_cancel hp]]
    field_simp
  have hcnot : ¬ ∃ x : M, algebraMap C M c = x ^ p := by
    rintro ⟨x, hx⟩
    refine hf ⟨x / algebraMap C M d, ?_⟩
    rw [div_pow, ← hx, hc]
    exact (mul_div_cancel_right₀ f (pow_ne_zero _ hdM)).symm
  obtain ⟨D, hD⟩ := exists_derivation_isUnit_of_not_pow_fractionRing
    (A := A) (M := M) (U := U) n hfs Q c hcnot
  have hpU : (p : U) = 0 := by
    rw [← map_natCast (algebraMap C U), CharP.cast_eq_zero C p, map_zero]
  have hpow : D ((algebraMap M U (algebraMap C M d)) ^ p) = 0 := by
    simp [Derivation.leibniz_pow, nsmul_eq_mul, hpU]
  have hcU : algebraMap C U c =
      algebraMap M U f * (algebraMap M U (algebraMap C M d)) ^ p := by
    rw [IsScalarTower.algebraMap_apply C M U, hc, map_mul, map_pow]
  rw [hcU, D.leibniz, hpow, smul_zero, zero_add] at hD
  exact ⟨D, (IsUnit.mul_iff.mp hD).2⟩

open IsPurelyInseparable IntermediateField Polynomial in
/-- Regularity is preserved by a simple purely inseparable extension when non-p-th-power
coefficients are detected by derivations with unit values. -/
private theorem isRegularRing_tensorProduct_adjoin_of_exists_derivation
    {K L R : Type*} [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L]
    [CommRing R] [Algebra K R] [IsRegularRing R]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    (hD : ∀ f : K, (¬ ∃ y : K, f = y ^ p) →
      ∃ D : Derivation ℤ R R, IsUnit (D (algebraMap K R f))) (x : L) :
    IsRegularRing (R ⊗[K] K⟮x⟯) := by
  classical
  by_cases hx : elemExponent K x = 0
  · have hxmem : x ∈ (⊥ : IntermediateField K L) := by
      refine ⟨elemReduct K x, ?_⟩
      simpa [hx] using algebraMap_elemReduct_eq' K p x
    rw [adjoin_simple_eq_bot_iff.mpr hxmem]
    exact IsRegularRing.of_ringEquiv
      ((Algebra.TensorProduct.rid K K R).symm.trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[K] R)
          (IntermediateField.botEquiv K L).symm)).toRingEquiv
  obtain ⟨D, hDunit⟩ := hD (elemReduct K x)
    (elemReduct_not_pow_of_elemExponent_pos p x (Nat.pos_of_ne_zero hx))
  let f := minpoly K x
  let q : Polynomial R := X ^ p ^ elemExponent K x - C (algebraMap K R (elemReduct K x))
  have hq : f.map (algebraMap K R) = q := by
    simp [f, q, minpoly_eq' K p x]
  have hreg : IsRegularRing (AdjoinRoot q) := by
    have H := isRegularRing_quotient_polynomial_sub_C_of_isUnit_derivation
        (algebraMap K R (elemReduct K x)) D hDunit
        ((Polynomial.X : Polynomial ℤ) ^ (p ^ elemExponent K x))
    rwa [Polynomial.map_pow, Polynomial.map_X] at H
  let t : Polynomial (R ⊗[K] K) := f.map
    (Algebra.TensorProduct.includeRight (R := K) (A := R) (B := K)).toRingHom
  let e₁ : R ⊗[K] AdjoinRoot f ≃ₐ[R] AdjoinRoot t :=
    AdjoinRoot.tensorAlgEquiv f t rfl
  let e₂ : AdjoinRoot t ≃ₐ[R] AdjoinRoot q :=
    AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid K R R) t q
      (Associated.of_eq (by
        rw [Polynomial.map_map]
        convert hq using 1
        congr 1
        ext a
        simp [Algebra.smul_def]))
  have : IsRegularRing (R ⊗[K] AdjoinRoot f) :=
    IsRegularRing.of_ringEquiv (e₁.trans e₂).symm.toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[K] R)
      (adjoinRootEquivAdjoin K (Algebra.IsIntegral.isIntegral x))).toRingEquiv

/-- Every non-p-th-power in a finite extension of the fraction field is detected on the
corresponding generic fibre of a complete formally smooth algebra. -/
private theorem exists_derivation_isUnit_tensorProduct_of_not_pow
    {A K M : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field M] [Algebra K M] [Algebra A M] [IsScalarTower A K M] [Module.Finite K M]
    (p : ℕ) [Fact p.Prime] [CharP M p]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (maximalIdeal B))
    (f : M) (hf : ¬ ∃ x : M, f = x ^ p) :
    ∃ D : Derivation ℤ (B ⊗[A] M) (B ⊗[A] M),
      IsUnit (D (1 ⊗ₜ[A] f)) := by
  obtain ⟨C, hCfin, hCfrac⟩ :=
    Algebra.exists_finite_subalgebra_isFractionRing A K M
  have : CharP C p := C.subtype.charP Subtype.val_injective p
  let S := B ⊗[A] C
  let U := B ⊗[A] M
  let : Algebra C S := Algebra.TensorProduct.rightAlgebra
  let : Algebra M U := Algebra.TensorProduct.rightAlgebra
  let : Algebra C U := ((algebraMap M U).comp (algebraMap C M)).toAlgebra
  have hCMU : IsScalarTower C M U := IsScalarTower.of_algebraMap_eq' rfl
  let F : S →ₐ[A] U := Algebra.TensorProduct.map (AlgHom.id A B)
    (IsScalarTower.toAlgHom A C M)
  let : Algebra S U := F.toRingHom.toAlgebra
  have hCSU : IsScalarTower C S U := IsScalarTower.of_algebraMap_eq fun c => by
    show (1 : B) ⊗ₜ[A] (c : M) = F (1 ⊗ₜ[A] c)
    rfl
  have : IsScalarTower B S U := IsScalarTower.of_algebraMap_eq fun b => by
    show b ⊗ₜ[A] (1 : M) = F (b ⊗ₜ[A] (1 : C))
    rfl
  let Q : Submonoid S := (nonZeroDivisors C).map
    (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C))
  have : IsLocalization Q U := IsLocalization.tensorProduct_tensorProduct_right A B
    (nonZeroDivisors C) M (by
      ext c
      show F (1 ⊗ₜ[A] c) = 1 ⊗ₜ[A] (c : M)
      rfl)
  let n : Ideal S := (maximalIdeal B).map (algebraMap B S)
  have : IsAdicComplete n S := isAdicComplete_map_maximalIdeal_of_finite
  have hs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap C S) n :=
    RingHom.FormallySmoothNAdic.baseChange (R' := C) (maximalIdeal B) hfs
  exact @exists_derivation_isUnit_of_not_pow_field A C S M U
    _ _ _ _ _ _ _ _ p _ _ _ _ n _ hs _ _ _ _ _ Q _ _ hCSU _ hCMU f hf

open IntermediateField in
/-- Let `L` be a finite purely inseparable extension of a field `K` of characteristic `p` and let
`R` be a regular `K`-algebra. If every element of an intermediate field `M` that is not a `p`-th
power has a unit image under some derivation of `M ⊗[K] R`, then `L ⊗[K] R` is regular. -/
private theorem isRegularRing_tensorProduct_of_exists_derivation
    {K L R : Type*} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [IsPurelyInseparable K L]
    [CommRing R] [Algebra K R] [IsRegularRing R]
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p]
    (hD : ∀ (M : IntermediateField K L) (f : M), (¬ ∃ y : M, f = y ^ p) →
      ∃ D : Derivation ℤ (M ⊗[K] R) (M ⊗[K] R), IsUnit (D (f ⊗ₜ[K] 1))) :
    IsRegularRing (L ⊗[K] R) := by
  have h : ∀ M : IntermediateField K L, IsRegularRing (M ⊗[K] R) := by
    apply IntermediateField.induction_on_adjoin
    · exact IsRegularRing.of_ringEquiv
        ((Algebra.TensorProduct.lid K R).symm.trans
          (Algebra.TensorProduct.congr (IntermediateField.botEquiv K L).symm
            (AlgEquiv.refl : R ≃ₐ[K] R))).toRingEquiv
    · intro M x hM
      let : CommRing (M ⊗[K] R) := inferInstance
      let : Algebra M (M ⊗[K] R) := Algebra.TensorProduct.leftAlgebra
      have : IsRegularRing (M ⊗[K] R) := hM
      have : IsRegularRing ((M ⊗[K] R) ⊗[M] M⟮x⟯) :=
        isRegularRing_tensorProduct_adjoin_of_exists_derivation
          (K := M) (L := L) (R := M ⊗[K] R) p (hD M) x
      have : IsRegularRing (M⟮x⟯ ⊗[M] (M ⊗[K] R)) :=
        IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm M (M ⊗[K] R) M⟮x⟯).toRingEquiv
      exact IsRegularRing.of_ringEquiv
        (Algebra.TensorProduct.cancelBaseChange K M M M⟮x⟯ R).toRingEquiv
  have := h ⊤
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (IntermediateField.topEquiv : (⊤ : IntermediateField K L) ≃ₐ[K] L)
      (AlgEquiv.refl : R ≃ₐ[K] R)).toRingEquiv

/-- Transport a derivation detecting an element along a ring isomorphism. -/
private theorem exists_derivation_isUnit_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (x : R)
    (h : ∃ D : Derivation ℤ R R, IsUnit (D x)) :
    ∃ D : Derivation ℤ S S, IsUnit (D (e x)) := by
  obtain ⟨D, hD⟩ := h
  let : Differential R := ⟨D⟩
  refine ⟨(Differential.equiv e.symm).deriv, ?_⟩
  show IsUnit (e (D (e.symm (e x))))
  rw [e.symm_apply_apply]
  exact hD.map e

/-- A regular complete local algebra that is formally smooth has a geometrically regular
fibre over the fraction field of its complete local domain base. -/
private theorem isGeometricallyRegular_genericFiber_of_formallySmoothNAdic
    {A K : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsRegularRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B] [Algebra A B]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (maximalIdeal B)) :
    Algebra.IsGeometricallyRegular K (K ⊗[A] B) := by
  have : IsRegularRing (K ⊗[A] B) := isRegularRing_tensorProduct_fractionRing K
  obtain hzero | ⟨p, hp, hchar⟩ := CharP.exists' K
  · have := hzero
    exact isGeometricallyRegular_of_perfectField
  constructor
  apply (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    K (K ⊗[A] B)).mpr
  intro L _ _ _ _
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  apply isRegularRing_tensorProduct_of_exists_derivation (K := K) (L := L) p
  intro M f hf
  let : Algebra A M := ((algebraMap K M).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K M := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨D, hD⟩ := exists_derivation_isUnit_tensorProduct_of_not_pow
    (A := A) (K := K) (M := M) p hfs f hf
  let e : (B ⊗[A] M) ≃+* (M ⊗[K] (K ⊗[A] B)) :=
    (Algebra.TensorProduct.comm A B M).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange A K K M B).symm.toRingEquiv
  exact exists_derivation_isUnit_of_ringEquiv
    (R := B ⊗[A] M) (S := M ⊗[K] (K ⊗[A] B)) e (1 ⊗ₜ[A] f) ⟨D, hD⟩

/-- A finite local algebra over a complete Noetherian local ring is complete. -/
private theorem isAdicComplete_maximalIdeal_of_finite
    {R S : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    [CommRing S] [IsLocalRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (maximalIdeal S) S := by
  let J := (maximalIdeal R).map (algebraMap R S)
  have hcomp : IsAdicComplete J S := isAdicComplete_map_maximalIdeal_of_finite
  have hJ : J ≤ maximalIdeal S :=
    (IsAdicComplete.le_jacobson_bot J).trans
      (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top))
  have : IsArtinianRing (S ⧸ J) := by
    have : Module.Finite R (S ⧸ J) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ R J).toLinearMap
        (Ideal.Quotient.mkₐ_surjective R J)
    let : Algebra (R ⧸ maximalIdeal R) (S ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    have : IsScalarTower R (R ⧸ maximalIdeal R) (S ⧸ J) := inferInstance
    have : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ J) :=
      Module.Finite.of_restrictScalars_finite R _ _
    let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
    exact IsArtinianRing.of_finite (R ⧸ maximalIdeal R) (S ⧸ J)
  have : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top hJ)
  have : IsLocalRing (S ⧸ J) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hjac : (⊥ : Ideal (S ⧸ J)).jacobson = (maximalIdeal S).map (Ideal.Quotient.mk J) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := S ⧸ J)
  rw [hjac, ← Ideal.map_pow] at hN
  have hpow : maximalIdeal S ^ N ≤ J := by
    simpa only [Ideal.mk_ker] using (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk J)).mp hN
  exact (completeness_preserved J (maximalIdeal S) (c := 1) (d := N + 1)
    (by omega) (by omega) (by simpa using hJ)
    ((Ideal.pow_le_pow_right (Nat.le_succ N)).trans hpow) S).mp hcomp

/-- A local map inducing an isomorphism of residue fields makes the target residue field purely
inseparable over the source one. -/
private theorem isPurelyInseparable_residueField_of_bijective
    {R A : Type*} [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (f : R →+* A) [IsLocalHom f] (hres : Function.Bijective (ResidueField.map f)) :
    @IsPurelyInseparable (ResidueField R) (ResidueField A) _ _ (ResidueField.map f).toAlgebra := by
  let : Algebra (ResidueField R) (ResidueField A) := (ResidueField.map f).toAlgebra
  exact (AlgEquiv.ofBijective (Algebra.ofId (ResidueField R) (ResidueField A))
    hres).isPurelyInseparable

/-- Finite base change along a local map inducing a residue-field isomorphism requires no
completion when the other algebra is complete Noetherian local. -/
private theorem isAdicComplete_tensorProduct_of_finite
    {R A C : Type*} [CommRing R] [IsLocalRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A] [Module.Finite R A]
    [IsLocalHom (algebraMap R A)]
    [CommRing C] [IsNoetherianRing C] [IsLocalRing C]
    [IsAdicComplete (maximalIdeal C) C] [Algebra R C]
    [IsLocalHom (algebraMap R C)]
    (hres : Function.Bijective (ResidueField.map (algebraMap R A))) :
    IsAdicComplete ((maximalIdeal A).map
      (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := A)).toRingHom)
      (C ⊗[R] A) := by
  obtain ⟨hloc, hleft, hright⟩ := isLocalRing_tensorProduct_of_isIntegral R C A
    (Or.inl (isPurelyInseparable_residueField_of_bijective _ hres))
  have : IsNoetherianRing (C ⊗[R] A) := IsNoetherianRing.of_finite C (C ⊗[R] A)
  have hc : IsAdicComplete (maximalIdeal (C ⊗[R] A)) (C ⊗[R] A) :=
    isAdicComplete_maximalIdeal_of_finite (R := C)
  exact isAdicComplete_of_le_of_fg_of_isAdicComplete
    (Ideal.map_le_iff_le_comap.mpr (fun x hx => map_nonunit _ x hx)) hc
    (IsNoetherian.noetherian _)

/-- A formally smooth local map of complete Noetherian local rings is flat with geometrically
regular special fibre. -/
private theorem flat_geometricallyRegular_of_formallySmoothNAdic
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B)) :
    letI : Algebra A B := f.toAlgebra
    Module.Flat A B ∧ Algebra.IsGeometricallyRegular (ResidueField A) (ResidueField A ⊗[A] B) :=
  ((flat_geometricallyRegular_specialFiber_formallySmooth_tfae f).out 3 1).mp hfs

/-- The Cohen subring reduction realizes a formally smooth complete local algebra by finite
base change from a formally smooth algebra over a regular complete local domain. -/
private theorem exists_regularLocal_formallySmooth_tensorProduct
    {A : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    (g : A →+* B) [IsLocalHom g]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} g (maximalIdeal B)) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsRegularLocalRing R)
      (_ : IsAdicComplete (maximalIdeal R) R) (f : R →+* A)
      (_ : IsLocalHom f),
      Function.Injective f ∧ f.Finite ∧
      ∃ (C : Type (max u v)) (_ : CommRing C) (_ : IsRegularLocalRing C)
        (_ : IsAdicComplete (maximalIdeal C) C) (a : R →+* C)
        (_ : IsLocalHom a) (c : C →+* B),
        c.comp a = g.comp f ∧
        RingHom.FormallySmoothNAdic.{max u v} a (maximalIdeal C) ∧
        (letI : Algebra R A := f.toAlgebra
         letI : Algebra R C := a.toAlgebra
         ∃ t : C ⊗[R] A →+* B, Function.Bijective t ∧
           t.comp (Algebra.TensorProduct.includeRight
             (R := R) (A := C) (B := A)).toRingHom = g) := by
  obtain ⟨d, Λ, hΛ, hdomΛ, _, hreg, hcomp, f, hfinj, hfinite, hres⟩ :=
    IsLocalRing.exists_injective_finite_mvPowerSeries A
  let R := MvPowerSeries (Fin d) Λ
  have : IsDomain R := Function.Injective.isDomain f hfinj
  let : Algebra R A := f.toAlgebra
  have : Module.Finite R A := hfinite
  have hfint : f.IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  have hflocal : IsLocalHom f := hfint.isLocalHom hfinj
  have hresbij : Function.Bijective (ResidueField.map f) := by
    refine ⟨(ResidueField.map f).injective, fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := hres x
    exact ⟨residue R y, (ResidueField.map_residue f y).trans hy⟩
  let : Algebra A B := g.toAlgebra
  have htfae := flat_geometricallyRegular_specialFiber_formallySmooth_tfae g
  have hflatbar : Module.Flat A B ∧ RingHom.FormallySmoothNAdic.{max u v}
      (algebraMap (ResidueField A) (ResidueField A ⊗[A] B))
      (maximalIdeal (ResidueField A ⊗[A] B)) := (htfae.out 3 2).mp hfs
  have hflat := (flat_geometricallyRegular_of_formallySmoothNAdic g hfs).1
  have hbar := hflatbar.2
  obtain ⟨C, hC, hnC, hlC, hcC, a, ha, c, hclocal, hcomm, hs, _, t, q,
      hnD, hlD, htC, htA, hqt, _, _, _, _, _, hqbij⟩ :=
    exists_completeLocal_formallySmooth_lift_with_baseChange f g hresbij hbar
  let : Algebra R C := a.toAlgebra
  have hCflatgeo := flat_geometricallyRegular_of_formallySmoothNAdic a hs
  have : Module.Flat R C := hCflatgeo.1
  have : Algebra.IsGeometricallyRegular (ResidueField R) (ResidueField R ⊗[R] C) := hCflatgeo.2
  have hCreg : IsRegularLocalRing C := isRegularLocalRing_of_flat_geometricallyRegular_specialFiber
    (A := R)
  refine ⟨R, inferInstance, inferInstance, hreg, hcomp, f, hflocal, hfinj, hfinite,
    C, hC, hCreg, hcC, a, ha, c, hcomm, hs, ?_⟩
  let : Algebra R A := f.toAlgebra
  have : Module.Finite R A := hfinite
  have htcomplete := isAdicComplete_tensorProduct_of_finite (R := R) (A := A) (C := C) hresbij
  have hi : Function.Bijective (algebraMap (C ⊗[R] A)
      (AdicCompletion ((maximalIdeal A).map
        (Algebra.TensorProduct.includeRight (R := R) (A := C) (B := A)).toRingHom) (C ⊗[R] A))) :=
    AdicCompletion.of_bijective_iff.mpr htcomplete
  have hgf : g.Flat := by
    let : Algebra A B := g.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr hflat
  exact ⟨t, hqt ▸ (hqbij hgf).comp hi, htA⟩

/-- The generic fibre of a formally smooth local map of complete Noetherian local domains
is geometrically regular; the target need not be a domain. -/
@[ega "IV 7.5.4" "partial"]
private theorem isGeometricallyRegular_genericFiber_of_completeLocal
    {A K : Type u} {B : Type v}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (maximalIdeal B)) :
    Algebra.IsGeometricallyRegular K (K ⊗[A] B) := by
  obtain ⟨R, hR, hdR, hrR, hcR, f, hf, hinj, hfin,
    C, hC, hrC, hcC, a, ha, c, hcomm, hs, t, ht, htA⟩ :=
    exists_regularLocal_formallySmooth_tensorProduct (algebraMap A B) hfs
  let : Algebra R A := f.toAlgebra
  let : Algebra R C := a.toAlgebra
  have : Module.Finite R A := hfin
  let : Algebra R K := ((algebraMap A K).comp f).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq' rfl
  have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr
    ((IsFractionRing.injective A K).comp hinj)
  let K₀ := FractionRing R
  let : Algebra K₀ K := FractionRing.liftAlgebra R K
  have : IsScalarTower R K₀ K := FractionRing.isScalarTower_liftAlgebra R K
  have : Algebra.EssFiniteType A K := Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors A)
  have : Algebra.EssFiniteType R K := Algebra.EssFiniteType.comp R A K
  have : Algebra.EssFiniteType K₀ K := Algebra.EssFiniteType.of_comp R K₀ K
  have : IsRegularRing C := (IsLocalRing.isRegularRing_tfae.out 1 3).mp hrC
  have : Algebra.IsGeometricallyRegular K₀ (K₀ ⊗[R] C) :=
    isGeometricallyRegular_genericFiber_of_formallySmoothNAdic (A := R) hs
  let e : A ⊗[R] C ≃ₐ[A] B :=
    { __ := (Algebra.TensorProduct.comm R A C).toRingEquiv.trans (RingEquiv.ofBijective t ht)
      commutes' := fun x => by
        show t (1 ⊗ₜ[R] x) = algebraMap A B x
        exact DFunLike.congr_fun htA x }
  constructor
  intro L _ _ _
  let : Algebra K₀ L := ((algebraMap K L).comp (algebraMap K₀ K)).toAlgebra
  have : IsScalarTower K₀ K L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A L := ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R A L := IsScalarTower.to₁₂₄ R A K L
  have : IsScalarTower R K₀ L := IsScalarTower.to₁₂₄ R K₀ K L
  have : Algebra.EssFiniteType K₀ L := Algebra.EssFiniteType.comp K₀ K L
  have : IsRegularRing (L ⊗[K₀] (K₀ ⊗[R] C)) := inferInstance
  have : IsRegularRing (L ⊗[R] C) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R K₀ K₀ L C).toRingEquiv
  have : IsRegularRing (L ⊗[A] (A ⊗[R] C)) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R A A L C).symm.toRingEquiv
  have : IsRegularRing (L ⊗[A] B) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[A] L) e).toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange A K K L B).symm.toRingEquiv

/-- A local homomorphism of complete Noetherian local rings that is formally smooth for the
maximal-ideal-adic topology is regular. -/
private theorem isRegularRingHom_of_formallySmoothNAdic
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hfs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B) (maximalIdeal B)) :
    IsRegularRingHom (algebraMap A B) := by
  apply isRegularRingHom_algebraMap_iff.mpr
  have hflat : (algebraMap A B).Flat :=
    (flat_geometricallyRegular_of_formallySmoothNAdic (algebraMap A B) hfs).1
  refine ⟨hflat, fun p hp ↦ ?_⟩
  let A' := A ⧸ p
  have : IsLocalRing A' := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal A') A' := isAdicComplete_maximalIdeal_of_finite (R := A)
  have : IsLocalHom (algebraMap A A') :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hres : Function.Bijective (ResidueField.map (algebraMap A A')) := by
    refine ⟨(ResidueField.map (algebraMap A A')).injective, fun x ↦ ?_⟩
    obtain ⟨y, rfl⟩ := residue_surjective x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨residue A z, ResidueField.map_residue _ z⟩
  obtain ⟨hloc, hleft, hright⟩ := isLocalRing_tensorProduct_of_isIntegral A B A'
    (Or.inl (isPurelyInseparable_residueField_of_bijective _ hres))
  let T := B ⊗[A] A'
  let : CommRing T := inferInstance
  let : Algebra A' T := Algebra.TensorProduct.rightAlgebra
  have : IsNoetherianRing T := IsNoetherianRing.of_finite B T
  have : IsAdicComplete (maximalIdeal T) T := isAdicComplete_maximalIdeal_of_finite (R := B)
  have hsur : Function.Surjective (algebraMap B T) :=
    Algebra.TensorProduct.includeLeft_surjective (R := A) (T := A') B B
      Ideal.Quotient.mk_surjective
  have hs : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A' T) (maximalIdeal T) := by
    have hs := RingHom.FormallySmoothNAdic.baseChange (R' := A') (maximalIdeal B) hfs
    change RingHom.FormallySmoothNAdic.{max u v} (algebraMap A' T)
      ((maximalIdeal B).map (algebraMap B T)) at hs
    rwa [IsLocalRing.map_maximalIdeal_of_surjective _ hsur] at hs
  let K := p.ResidueField
  have hgeo : Algebra.IsGeometricallyRegular K (K ⊗[A'] T) :=
    isGeometricallyRegular_genericFiber_of_completeLocal (A := A') hs
  let : CommRing (K ⊗[A'] T) := inferInstance
  have hfiber : Algebra.IsGeometricallyRegular K (K ⊗[A] B) := by
    constructor
    intro L _ _ _
    let : Algebra A' L := ((algebraMap K L).comp (algebraMap A' K)).toAlgebra
    have : IsScalarTower A' K L := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra A L := ((algebraMap A' L).comp (algebraMap A A')).toAlgebra
    have : IsScalarTower A A' L := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower A K L := IsScalarTower.to₁₃₄ A A' K L
    let e : T ≃ₐ[A'] A' ⊗[A] B :=
      { __ := (Algebra.TensorProduct.comm A B A').toRingEquiv
        commutes' := fun _ => rfl }
    let : CommRing (L ⊗[A'] T) := inferInstance
    have : IsRegularRing (L ⊗[K] (K ⊗[A'] T)) := inferInstance
    have : IsRegularRing (L ⊗[A'] T) := IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange A' K K L T).toRingEquiv
    have : IsRegularRing (L ⊗[A'] (A' ⊗[A] B)) := IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[A'] L) e).toRingEquiv
    have : IsRegularRing (L ⊗[A] B) := IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange A A' A' L B).toRingEquiv
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange A K K L B).symm.toRingEquiv
  have : IsRegularRing (K ⊗[A] B) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.lid K (K ⊗[A] B)).toRingEquiv
  exact ⟨inferInstance, hfiber⟩

/-- Let `f : A → B` be a local homomorphism of Noetherian complete local rings, let `k` be
the residue field of `A`, and let `B̄ = k ⊗[A] B` be the special fibre. The following are
equivalent:

1. `f` is regular;
2. `f` is flat and `B̄` is geometrically regular over `k`;
3. `f` is flat and `k → B̄` is formally smooth for the maximal-ideal-adic topology;
4. `f` is formally smooth for the maximal-ideal-adic topology on `B`. -/
@[stacks 07PM,
  ega "0 19.7.1" "complete case",
  ega "0 19.0.2" "I, complete case",
  ega "IV 7.5.4" "(i)",
  sga "1 III 1.7" "Noetherian complete case",
  ega "IV 7.5.3" "(iv), special case", sga "1 III 1.3" "special case"]
public theorem isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [IsAdicComplete (maximalIdeal B) B]
    (f : A →+* B) [IsLocalHom f] :
    letI : Algebra A B := f.toAlgebra
    let k := ResidueField A
    let Bbar := k ⊗[A] B
    List.TFAE [
      IsRegularRingHom f,
      Module.Flat A B ∧ Algebra.IsGeometricallyRegular k Bbar,
      Module.Flat A B ∧
        RingHom.FormallySmoothNAdic.{max u v}
          (algebraMap k Bbar) (maximalIdeal Bbar),
      RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B)] := by
  let : Algebra A B := f.toAlgebra
  have h := flat_geometricallyRegular_specialFiber_formallySmooth_tfae f
  tfae_have 1 → 2 := flat_geometricallyRegular_specialFiber_of_isRegularRingHom
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 3 ↔ 4 := h.out 2 3
  tfae_have 4 → 1 := isRegularRingHom_of_formallySmoothNAdic
  tfae_finish

end

end

/-! ### André's theorem -/

section

section


open scoped TensorProduct

open IsLocalRing UniformSpace

universe u v

private theorem geometricallyRegular_closedFiber_of_fiber
    {R : Type u} {S : Type v} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    (h : Algebra.IsGeometricallyRegular (maximalIdeal R).ResidueField
      ((maximalIdeal R).Fiber S)) :
    Algebra.IsGeometricallyRegular (ResidueField R) (ResidueField R ⊗[R] S) := by
  let m := maximalIdeal R
  let k := ResidueField R
  let K := m.ResidueField
  have hsurj : Function.Surjective (algebraMap R K) :=
    Ideal.algebraMap_residueField_surjective _
  have hker : RingHom.ker (algebraMap R K) = m := Ideal.ker_algebraMap_residueField m
  let β : k ≃ₐ[R] K := AlgEquiv.ofRingEquiv
    (f := (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)) (fun _ => rfl)
  let βk : k ≃ₐ[k] K := AlgEquiv.ofBijective (Algebra.ofId k K)
    (Ideal.bijective_algebraMap_quotient_residueField m)
  have hβ : β.toRingHom = algebraMap k K := RingHom.ext fun x ↦ by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  let ΦR : (k ⊗[R] S) ≃ₐ[R] m.Fiber S :=
    Algebra.TensorProduct.congr β AlgEquiv.refl
  let Φ : (k ⊗[R] S) ≃ₐ[k] m.Fiber S :=
    AlgEquiv.ofRingEquiv (f := ΦR.toRingEquiv) (by
      intro x
      show β x ⊗ₜ[R] 1 = βk x ⊗ₜ[R] 1
      rw [show β x = βk x by
        show β.toRingHom x = (algebraMap k K) x
        rw [hβ]])
  let : Algebra.IsSeparable k K := AlgEquiv.Algebra.isSeparable βk
  have hK : Algebra.IsGeometricallyRegular K (m.Fiber S) := h
  have hk : Algebra.IsGeometricallyRegular k (m.Fiber S) :=
    (Algebra.isGeometricallyRegular_iff_tower_top_of_isSeparable
      k K (m.Fiber S)).2 hK
  refine ⟨fun L _ _ _ => ?_⟩
  let : IsRegularRing (L ⊗[k] m.Fiber S) := hk.isRegularRing_tensorProduct L
  exact IsRegularRing.of_ringEquiv (R := L ⊗[k] m.Fiber S)
    (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[k] L) Φ.symm).toRingEquiv

/-- On a discrete ring, continuity for the `n`-adic topology on the source is continuity for the
`⊥`-adic topology on the target. -/
private theorem continuous_iff_continuous_bot_adic {S T : Type*} [CommRing S] [CommRing T]
    [τ : TopologicalSpace T] [IsTopologicalRing T] [DiscreteTopology T] (n : Ideal S)
    (ψ : S →+* T) :
    @Continuous S T n.adicTopology τ ψ ↔
      @Continuous S T n.adicTopology (⊥ : Ideal T).adicTopology ψ := by
  have h : τ = (⊥ : Ideal T).adicTopology := is_bot_adic_iff.mpr inferInstance
  subst h
  exact Iff.rfl

/-- A ring map killing, modulo a square-zero ideal `J`, the `k`-th power of `n` is continuous
from the `n`-adic topology to a discrete ring. -/
private theorem continuous_adic_of_pow_le_comap {S A : Type*} [CommRing S] [CommRing A]
    [τ : TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] (n : Ideal S)
    (g : S →+* A) (J : Ideal A) (hJ : J ^ 2 = ⊥) (k : ℕ) (hk : 1 ≤ k) (h : n ^ k ≤ J.comap g) :
    @Continuous S A n.adicTopology τ g := by
  rw [continuous_iff_continuous_bot_adic]
  refine (RingHom.continuous_adic_iff g n ⊥).mpr ⟨k * 2, by omega, fun x hx => ?_⟩
  have hzero : (n ^ (k * 2)).map g ≤ (⊥ : Ideal A) := by
    rw [pow_mul, Ideal.map_pow]
    exact (pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr h) 2).trans_eq hJ
  exact hzero (Ideal.mem_map_of_mem g hx)

private theorem isFormallySmooth_adic_of_formallySmoothNAdic.{w}
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    (m : Ideal R) (n : Ideal S)
    (hφ : @Continuous R S m.adicTopology n.adicTopology φ)
    (h : RingHom.FormallySmoothNAdic.{w} φ n) :
    let : TopologicalSpace R := m.adicTopology
    let : IsTopologicalRing R := m.nonarchimedean.toIsTopologicalRing
    let : IsLinearTopology R R := m.isLinearTopology
    let : TopologicalSpace S := n.adicTopology
    let : IsTopologicalRing S := n.nonarchimedean.toIsTopologicalRing
    let : IsLinearTopology S S := n.isLinearTopology
    IsFormallySmooth.{w} φ := by
  let : TopologicalSpace R := m.adicTopology
  let : IsTopologicalRing R := m.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology R R := m.isLinearTopology
  let : TopologicalSpace S := n.adicTopology
  let : IsTopologicalRing S := n.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology S S := n.isLinearTopology
  refine ⟨hφ, fun A _ _ _ J hJ f hf ψ hψ hcomm ↦ ?_⟩
  have : DiscreteTopology (A ⧸ J) :=
    QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) (isOpen_discrete _)
  obtain ⟨k, hk, hkn⟩ : ∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker ψ := by
    obtain ⟨k, hk, hle⟩ := (RingHom.continuous_adic_iff ψ n (⊥ : Ideal (A ⧸ J))).mp
      ((continuous_iff_continuous_bot_adic n ψ).mp hψ)
    exact ⟨k, hk, fun x hx => hle x hx⟩
  obtain ⟨g, hqg, hgf⟩ := h A J hJ f ψ hcomm ⟨k, hk, hkn⟩
  have hJg : n ^ k ≤ J.comap g := fun x hx ↦ (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp
    ((congrArg (fun q : S →+* A ⧸ J => q x) hqg).trans (hkn hx))
  exact ⟨g, continuous_adic_of_pow_le_comap n g J hJ k hk hJg, hgf, hqg⟩

private theorem formallySmoothNAdic_of_isFormallySmooth_adic.{w}
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (φ : R →+* S)
    (m : Ideal R) (n : Ideal S) (hmn : m.map φ ≤ n)
    (h : let : TopologicalSpace R := m.adicTopology
      let : IsTopologicalRing R := m.nonarchimedean.toIsTopologicalRing
      let : IsLinearTopology R R := m.isLinearTopology
      let : TopologicalSpace S := n.adicTopology
      let : IsTopologicalRing S := n.nonarchimedean.toIsTopologicalRing
      let : IsLinearTopology S S := n.isLinearTopology
      IsFormallySmooth.{w} φ) :
    RingHom.FormallySmoothNAdic.{w} φ n := by
  rintro A _ J hJ f ψ hcomm ⟨k, hk, hkn⟩
  let : TopologicalSpace R := m.adicTopology
  let : IsTopologicalRing R := m.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology R R := m.isLinearTopology
  let : TopologicalSpace S := n.adicTopology
  let : IsTopologicalRing S := n.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology S S := n.isLinearTopology
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  have : DiscreteTopology (A ⧸ J) :=
    QuotientAddGroup.discreteTopology (N := J.toAddSubgroup) (isOpen_discrete _)
  have hmk : m ^ k ≤ J.comap f := by
    intro x hx
    have hφx : φ x ∈ n ^ k :=
      (Ideal.map_pow φ m k ▸ pow_le_pow_left' hmn k) (Ideal.mem_map_of_mem φ hx)
    have hqx := congrArg (fun q : R →+* A ⧸ J => q x) hcomm
    exact (Ideal.Quotient.eq_zero_iff_mem (I := J)).mp (hqx.symm.trans (hkn hφx))
  have hf := continuous_adic_of_pow_le_comap m f J hJ k hk hmk
  have hψ : Continuous ψ := (continuous_iff_continuous_bot_adic n ψ).mpr
    ((RingHom.continuous_adic_iff ψ n ⊥).mpr ⟨k, hk, hkn⟩)
  obtain ⟨g, _, hgf, hqg⟩ := h.2 A J hJ f hf ψ hψ hcomm
  exact ⟨g, hqg, hgf⟩

/-- A local homomorphism of Noetherian local rings that is formally smooth for the
maximal-ideal-adic topology is regular, provided the completion map of the source is regular. -/
private theorem isRegularRingHom_of_formallySmoothNAdic_0h7u
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hA : letI : WithIdeal A := ⟨maximalIdeal A⟩
      IsRegularRingHom
        (Completion.coeRingHom : A →+* Completion A))
    (hformal : RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B)) :
    IsRegularRingHom f := by
  let m : Ideal A := maximalIdeal A
  let n : Ideal B := maximalIdeal B
  have hm : m.FG := IsNoetherian.noetherian m
  have hn : n.FG := IsNoetherian.noetherian n
  have hf : @Continuous A B m.adicTopology n.adicTopology f := by
    apply (RingHom.continuous_adic_iff f m n).mpr
    refine ⟨1, by simp, ?_⟩
    intro x hx
    apply map_maximalIdeal_le f
    apply Ideal.mem_map_of_mem f
    simpa [m] using hx
  let : WithIdeal A := ⟨m⟩
  let : WithIdeal B := ⟨n⟩
  let Ahat := Completion A
  let Bhat := Completion B
  let fhat : Ahat →+* Bhat := Completion.mapRingHom f hf
  let : IsNoetherianRing Ahat := isNoetherianRing_uniformCompletion m
  let : IsNoetherianRing Bhat := isNoetherianRing_uniformCompletion n
  let : IsLocalRing Ahat := isLocalRing_uniformCompletion hm
  let : IsLocalRing Bhat := isLocalRing_uniformCompletion hn
  let : IsLocalHom fhat := isLocalHom_mapRingHom hm hn f hf
  let : IsAdicComplete (maximalIdeal Ahat) Ahat :=
    isAdicComplete_maximalIdeal_uniformCompletion hm
  let : IsAdicComplete (maximalIdeal Bhat) Bhat :=
    isAdicComplete_maximalIdeal_uniformCompletion hn
  have hfhatFormal : RingHom.FormallySmoothNAdic.{max u v} fhat
      (maximalIdeal Bhat) := by
    have hformalTop := isFormallySmooth_adic_of_formallySmoothNAdic
      f m n hf hformal
    have hc := isFormallySmooth_iff_adicCompletion
      m n hm hn f hf
    have hfhatTop := hc.2.mp (hc.1.mp hformalTop)
    let mhat : Ideal Ahat := m.map Completion.coeRingHom
    let nhat : Ideal Bhat := n.map Completion.coeRingHom
    have hmn : mhat.map fhat ≤ nhat := by
      rw [Ideal.map_map, show fhat.comp (Completion.coeRingHom : A →+* Ahat) =
        (Completion.coeRingHom : B →+* Bhat).comp f by
          ext x
          exact Completion.mapRingHom_coe hf x, ← Ideal.map_map]
      exact Ideal.map_mono (map_maximalIdeal_le f)
    rw [maximalIdeal_uniformCompletion_eq_map hn]
    exact formallySmoothNAdic_of_isFormallySmooth_adic fhat mhat nhat hmn hfhatTop
  have hfhatRegular : IsRegularRingHom fhat :=
    ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae
      fhat).out 4 1).mp hfhatFormal
  have hcomp : IsRegularRingHom
      ((Completion.coeRingHom : B →+* Bhat).comp f) := by
    rw [show (Completion.coeRingHom : B →+* Bhat).comp f =
        fhat.comp (Completion.coeRingHom : A →+* Ahat) by
      ext x
      exact (Completion.mapRingHom_coe hf x).symm]
    refine isRegularRingHom_comp _ _ hA hfhatRegular fun p hp ↦ ?_
    let : Algebra A Bhat := (fhat.comp (Completion.coeRingHom : A →+* Ahat)).toAlgebra
    exact Stacks.Flatness.NormalFibreAscent.isNoetherianRing_fiber p
  have hfaithful : (Completion.coeRingHom : B →+* Bhat).FaithfullyFlat :=
    faithfullyFlat_coeRingHom n
      (by simp only [ringJacobson_eq_maximalIdeal]; exact le_rfl)
  exact isRegularRingHom_of_comp_of_flat_of_surjectiveOnSpec f
    (Completion.coeRingHom : B →+* Bhat) hcomp hfaithful.flat
    (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hfaithful).2

/-- Let `f : A → B` be a local homomorphism of Noetherian local rings and assume that the
canonical map from `A` to its maximal-ideal-adic completion is regular. Let `k` be the residue
field of `A` and let `B̄ = k ⊗[A] B` be the special fibre. The following are equivalent:

1. `f` is regular;
2. `f` is flat and `B̄` is geometrically regular over `k`;
3. `f` is flat and `k → B̄` is formally smooth for the maximal-ideal-adic topology;
4. `f` is formally smooth for the maximal-ideal-adic topology on `B`. -/
@[stacks 0H7U,
  ega "0 19.0.2" "I, A→A^∧ regular",
  ega "0 19.7.1" "A → A^ regular",
  ega "IV 7.5.4" "(i)", ega "IV 7.5.3" "(iv), special case", sga "1 III 1.3" "special case"]
public theorem isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae_0h7u
    {A : Type u} {B : Type v}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (f : A →+* B) [IsLocalHom f]
    (hA : letI : WithIdeal A := ⟨maximalIdeal A⟩
      IsRegularRingHom
        (Completion.coeRingHom : A →+* Completion A)) :
    letI : Algebra A B := f.toAlgebra
    let k := ResidueField A
    let Bbar := k ⊗[A] B
    List.TFAE [
      IsRegularRingHom f,
      Module.Flat A B ∧ Algebra.IsGeometricallyRegular k Bbar,
      Module.Flat A B ∧
        RingHom.FormallySmoothNAdic.{max u v}
          (algebraMap k Bbar) (maximalIdeal Bbar),
      RingHom.FormallySmoothNAdic.{max u v} f (maximalIdeal B)] := by
  let : Algebra A B := f.toAlgebra
  let k := ResidueField A
  let Bbar := k ⊗[A] B
  have htail := flat_geometricallyRegular_specialFiber_formallySmooth_tfae f
  tfae_have 2 → 3 := (htail.out 1 2).mp
  tfae_have 3 → 4 := (htail.out 2 3).mp
  tfae_have 4 → 2 := (htail.out 3 1).mp
  tfae_have 1 → 2 := fun h ↦
    ⟨h.1, geometricallyRegular_closedFiber_of_fiber
      (h.2 (maximalIdeal A)).2⟩
  tfae_have 4 → 1 := isRegularRingHom_of_formallySmoothNAdic_0h7u f hA
  tfae_finish

end

end

end
