module

public import StacksFrontier.RingTheory.SerreIntersection.TwistedFlatness
public import StacksFrontier.RingTheory.SerreIntersection.RegularSequenceMultiplicity
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension of the complete tensor product

For ring maps `α β : R →+* B` and `R`-modules `M`, `N`, this file studies the module
`(B ⊗_{R, α} M) ⊗_{R, β} N` over `B`: its length when `N` has finite length, and its reduction
modulo an ideal `I` of `R`.

## Main definitions

* `residueLift`: The ring map `κ → R` induced by `ψ ∘ β`.
* `pairResidueEquiv`: The `B`-linear isomorphism `(B ⊗_{R, α} M) ⊗_{R, β} κ ≅ M`.
* `pairQuot`: The reduction `(B ⊗ M) ⊗ N → (B ⊗ M/IM) ⊗ N/IN`.

## Main results

* `length_pair_eq_mul`: The length of `(B ⊗_{R, α} M) ⊗_{R, β} N` is the product of the lengths
  of `M` and `N`.
* `ker_pairQuot_le`: The kernel of `pairQuot` is contained in `(α(I)B + β(I)B)` times the module.
* `supportDim_quotient_maximalIdeal_smul`: The reduction of a nonzero finite module over a
  Noetherian local ring modulo the maximal ideal has dimension zero.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.SerreIntersection

section Residue

variable {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing R] (α β : R →+* B) (ψ : B →+* R)
  (hψα : ∀ r, ψ (α r) = r) (hker : RingHom.ker ψ = Ideal.map β (maximalIdeal R))

include hker in
/-- The composite `ψ ∘ β` vanishes on the maximal ideal of `R`. -/
theorem psi_beta_mem (r : R) (hr : r ∈ maximalIdeal R) : ψ (β r) = 0 :=
  RingHom.mem_ker.mp (hker ▸ Ideal.mem_map_of_mem β hr)

/-- The ring map `κ → R` induced by `ψ ∘ β`, which kills the maximal ideal. -/
def residueLift : ResidueField R →+* R :=
  Ideal.Quotient.lift (maximalIdeal R) (ψ.comp β) fun r hr => psi_beta_mem β ψ hker r hr

/-- `residueLift` sends the residue class of `r` to `ψ (β r)`. -/
theorem residueLift_residue (r : R) : residueLift β ψ hker (residue R r) = ψ (β r) := rfl

/-- The contraction `(B ⊗_{R, α} M) ⊗_{R, β} κ → M`. -/
def pairResidueFwd (M : Type u) [AddCommGroup M] [Module R M] :
    Pair α β M (ResidueField R) →+ M :=
  TensorProduct.liftAddHom
    { toFun y :=
        { toFun c := residueLift β ψ hker c • contractT α β ψ hψα M y
          map_zero' := by rw [map_zero, zero_smul]
          map_add' c c' := by rw [map_add, add_smul] }
      map_zero' := by ext c; simp
      map_add' y y' := by ext c; simp [smul_add] }
    (fun r y c => by
      change residueLift β ψ hker c • contractT α β ψ hψα M (β r • y) =
        residueLift β ψ hker (r • c) • contractT α β ψ hψα M y
      obtain ⟨c, rfl⟩ := residue_surjective c
      rw [contractT_smul, Algebra.smul_def, map_mul, smul_smul, mul_comm]
      rfl)

/-- `pairResidueFwd` sends `y ⊗ c` to `residueLift c • contractT y`. -/
theorem pairResidueFwd_tmul (M : Type u) [AddCommGroup M] [Module R M] (y : Twist β (Ext α M))
    (c : ResidueField R) :
    pairResidueFwd α β ψ hψα hker M (y ⊗ₜ c) =
      residueLift β ψ hker c • contractT α β ψ hψα M y := rfl

/-- `pairResidueFwd` is `B`-linear for the action of `B` on `M` through `ψ`. -/
theorem pairResidueFwd_smul (M : Type u) [AddCommGroup M] [Module R M] (b : B)
    (z : Pair α β M (ResidueField R)) :
    pairResidueFwd α β ψ hψα hker M (b • z) = ψ b • pairResidueFwd α β ψ hψα hker M z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul y c => rw [TensorProduct.smul_tmul', pairResidueFwd_tmul, pairResidueFwd_tmul,
      contractT_smul, smul_comm]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- For `w ∈ 𝔪 • (B ⊗_{R, α} M)`, the element `w ⊗ 1` of `(B ⊗_{R, α} M) ⊗_{R, β} κ` is zero. -/
theorem tmul_one_eq_zero_of_mem (M : Type u) [AddCommGroup M] [Module R M]
    {w : Twist β (Ext α M)} (hw : w ∈ (maximalIdeal R) • (⊤ : Submodule R (Twist β (Ext α M)))) :
    (w ⊗ₜ[R] (1 : ResidueField R) : Pair α β M (ResidueField R)) = 0 := by
  refine Submodule.smul_induction_on hw (fun s hs y _ => ?_) (fun x y hx hy => ?_)
  · rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    show y ⊗ₜ[R] residue R s = 0
    rw [(residue_eq_zero_iff s).mpr hs, TensorProduct.tmul_zero]
  · rw [TensorProduct.add_tmul, hx, hy, add_zero]

/-- `(B ⊗_{R, α} M) ⊗_{R, β} κ ≅ M`, `B`-linearly for the action of `B` on `M` through `ψ`. -/
def pairResidueEquiv (M : Type u) [AddCommGroup M] [Module R M] :
    Pair α β M (ResidueField R) ≃ₗ[B]
      (ModuleCat.restrictScalars ψ).obj (ModuleCat.of R M) where
  toFun z := pairResidueFwd α β ψ hψα hker M z
  map_add' z z' := map_add _ z z'
  map_smul' b z := pairResidueFwd_smul α β ψ hψα hker M b z
  invFun m := Twist.mk β (Twist.mk α (1 : B) ⊗ₜ (m : M) : Ext α M) ⊗ₜ (1 : ResidueField R)
  left_inv z := by
    induction z using TensorProduct.induction_on with
    | zero =>
      change Twist.mk β (Twist.mk α (1 : B) ⊗ₜ pairResidueFwd α β ψ hψα hker M 0 : Ext α M) ⊗ₜ
        (1 : ResidueField R) = 0
      rw [map_zero, TensorProduct.tmul_zero, Twist.mk_zero, TensorProduct.zero_tmul]
    | tmul y c =>
      obtain ⟨r, rfl⟩ := residue_surjective c
      change Twist.mk β (Twist.mk α (1 : B) ⊗ₜ pairResidueFwd α β ψ hψα hker M
        (y ⊗ₜ residue R r) : Ext α M) ⊗ₜ (1 : ResidueField R) = y ⊗ₜ residue R r
      have hy : (y ⊗ₜ[R] residue R r : Pair α β M (ResidueField R)) = (r • y) ⊗ₜ[R] 1 := by
        rw [TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
        rfl
      rw [hy, pairResidueFwd_tmul, map_one, one_smul]
      have h := sub_mem_smul_top α β ψ hψα hker.le (X := M) (β r • (y : Ext α M))
      have h' := tmul_one_eq_zero_of_mem α β M h
      rw [TensorProduct.sub_tmul, sub_eq_zero] at h'
      exact h'.symm
    | add x y hx hy =>
      change Twist.mk β (Twist.mk α (1 : B) ⊗ₜ pairResidueFwd α β ψ hψα hker M (x + y) :
        Ext α M) ⊗ₜ (1 : ResidueField R) = x + y
      rw [map_add, TensorProduct.tmul_add, ← Twist.mk_add, TensorProduct.add_tmul]
      exact congrArg₂ (· + ·) hx hy
  right_inv m := by
    change pairResidueFwd α β ψ hψα hker M (Twist.mk β (Twist.mk α (1 : B) ⊗ₜ (m : M) : Ext α M)
      ⊗ₜ (1 : ResidueField R)) = m
    rw [pairResidueFwd_tmul, map_one, one_smul]
    change ψ 1 • (m : M) = m
    rw [map_one, one_smul]

include hψα hker in
/-- The length of `(B ⊗_{R, α} M) ⊗_{R, β} κ` over `B` is the length of `M` over `R`. -/
theorem length_pair_residueField (M : Type u) [AddCommGroup M] [Module R M] :
    Module.length B (Pair α β M (ResidueField R)) = Module.length R M := by
  rw [(pairResidueEquiv α β ψ hψα hker M).length_eq]
  exact length_restrictScalars_eq_of_surjective B R ψ (fun r => ⟨α r, hψα r⟩) M

/-- A simple module over a local ring is the residue field. -/
theorem nonempty_linearEquiv_residueField_of_isSimpleModule (S : Type u) [AddCommGroup S]
    [Module R S] [IsSimpleModule R S] : Nonempty (S ≃ₗ[R] ResidueField R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule R S›
  obtain rfl := IsLocalRing.eq_maximalIdeal hI
  exact ⟨e.trans (residueFieldEquivQuotient (R := R)).symm⟩

include hψα hker in
/-- **The length of a complete tensor product is the product of the lengths.** Here `B ⊗_{R, α} M`
is flat over `R` through `β`, and `N` has finite length. -/
@[ega "IV 2.5.5.3" "special case"]
theorem length_pair_eq_mul (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Flat R (Twist β (Ext α M))] (N : Type u) [AddCommGroup N] [Module R N]
    (hN : IsFiniteLength R N) :
    Module.length B (Pair α β M N) = Module.length R M * Module.length R N := by
  induction hN with
  | @of_subsingleton N0 _ _ _ =>
    have : Subsingleton (Pair α β M N0) := ⟨fun x y => by
      have h0 : ∀ z : Pair α β M N0, z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul y n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [h0 x, h0 y]⟩
    rw [Module.length_eq_zero (R := B) (M := Pair α β M N0),
      Module.length_eq_zero (R := R) (M := N0), mul_zero]
  | @of_simple_quotient N' _ _ P _ _ ih =>
    obtain ⟨e⟩ := nonempty_linearEquiv_residueField_of_isSimpleModule (R := R) (N' ⧸ P)
    have hex := Module.length_eq_add_of_exact (R := B)
      (pairMap α β (LinearMap.id : M →ₗ[R] M) P.subtype)
      (pairMap α β (LinearMap.id : M →ₗ[R] M) P.mkQ)
      (pairMap_right_injective α β (Submodule.injective_subtype P))
      (pairMap_right_surjective α β (Submodule.mkQ_surjective P))
      (pairMap_right_exact α β (LinearMap.exact_subtype_mkQ P) (Submodule.mkQ_surjective P))
    have hexR := Module.length_eq_add_of_exact (R := R) P.subtype P.mkQ
      (Submodule.injective_subtype P) (Submodule.mkQ_surjective P) (LinearMap.exact_subtype_mkQ P)
    let eP : Pair α β M (N' ⧸ P) ≃ₗ[B] Pair α β M (ResidueField R) :=
      { pairMap α β (LinearMap.id : M →ₗ[R] M) e.toLinearMap with
        invFun := pairMap α β (LinearMap.id : M →ₗ[R] M) e.symm.toLinearMap
        left_inv := fun z => by
          show pairMap α β _ _ (pairMap α β _ _ z) = z
          rw [pairMap_pairMap, e.symm_comp, LinearMap.id_comp, pairMap_id_apply]
        right_inv := fun z => by
          show pairMap α β _ _ (pairMap α β _ _ z) = z
          rw [pairMap_pairMap, e.comp_symm, LinearMap.id_comp, pairMap_id_apply] }
    rw [hex, ih, eP.length_eq, length_pair_residueField α β ψ hψα hker M, hexR,
      Module.length_eq_one (R := R) (M := N' ⧸ P), mul_add, mul_one]

end Residue

section Sandwich

variable {R B : Type u} [CommRing R] [CommRing B] (α β : R →+* B) (I : Ideal R)
variable (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

omit [AddCommGroup N] [Module R N] in
/-- For `a ∈ I`, the element `α a` annihilates `B ⊗_{R, α} M/IM`. -/
theorem smul_ext_quot_eq_zero {a : R} (ha : a ∈ I) (y : Ext α (M ⧸ I • (⊤ : Submodule R M))) :
    α a • y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul b m =>
    obtain ⟨b, rfl⟩ : ∃ b' : B, Twist.mk α b' = b := ⟨b, rfl⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [TensorProduct.smul_tmul']
    show (a • Twist.mk α b) ⊗ₜ[R] Submodule.Quotient.mk m = 0
    rw [TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top),
      TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- The extension `α(I)B` annihilates `(B ⊗_{R, α} M/IM) ⊗_{R, β} N`. -/
theorem map_left_le_annihilator_pair :
    Ideal.map α I ≤ Module.annihilator B (Pair α β (M ⧸ I • (⊤ : Submodule R M)) N) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul y n =>
    obtain ⟨y, rfl⟩ : ∃ y' : Ext α (M ⧸ I • (⊤ : Submodule R M)), Twist.mk β y' = y := ⟨y, rfl⟩
    rw [TensorProduct.smul_tmul', Twist.smul_mk, smul_ext_quot_eq_zero α I M ha, Twist.mk_zero,
      TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

omit [AddCommGroup M] [Module R M] in
/-- The extension `β(I)B` annihilates `(B ⊗_{R, α} M) ⊗_{R, β} N/IN`. -/
theorem map_right_le_annihilator_pair (M : Type u) [AddCommGroup M] [Module R M] :
    Ideal.map β I ≤ Module.annihilator B (Pair α β M (N ⧸ I • (⊤ : Submodule R N))) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => rw [smul_zero]
  | tmul y n =>
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    rw [TensorProduct.smul_tmul']
    show (a • y) ⊗ₜ[R] Submodule.Quotient.mk n = 0
    rw [TensorProduct.smul_tmul, ← Submodule.Quotient.mk_smul,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top),
      TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- The reduction `(B ⊗ M) ⊗ N → (B ⊗ M/IM) ⊗ N/IN`. -/
def pairQuot : Pair α β M N →ₗ[B]
    Pair α β (M ⧸ I • (⊤ : Submodule R M)) (N ⧸ I • (⊤ : Submodule R N)) :=
  pairMap α β (I • (⊤ : Submodule R M)).mkQ (I • (⊤ : Submodule R N)).mkQ

/-- The reduction `pairQuot` is surjective. -/
theorem pairQuot_surjective : Function.Surjective (pairQuot α β I M N) := by
  have h1 : Function.Surjective (twistMap β (extMap α (I • (⊤ : Submodule R M)).mkQ)) :=
    LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  exact TensorProduct.map_surjective h1 (Submodule.mkQ_surjective _)

/-- The submodule `(α(I)B + β(I)B) • ((B ⊗_{R, α} M) ⊗_{R, β} N)` lies in the kernel of
`pairQuot`. -/
theorem le_ker_pairQuot :
    (Ideal.map α I ⊔ Ideal.map β I) • (⊤ : Submodule B (Pair α β M N)) ≤
      LinearMap.ker (pairQuot α β I M N) := by
  rw [Submodule.smul_le]
  intro b hb z _
  rw [LinearMap.mem_ker, map_smul]
  have hann : Ideal.map α I ⊔ Ideal.map β I ≤ Module.annihilator B
      (Pair α β (M ⧸ I • (⊤ : Submodule R M)) (N ⧸ I • (⊤ : Submodule R N))) :=
    sup_le (map_left_le_annihilator_pair α β I M _) (map_right_le_annihilator_pair α β I N _)
  exact Module.mem_annihilator.mp (hann hb) _

/-- The kernel of `pairQuot` is contained in `(α(I)B + β(I)B) • ((B ⊗_{R, α} M) ⊗_{R, β} N)`. -/
theorem ker_pairQuot_le :
    LinearMap.ker (pairQuot α β I M N) ≤
      (Ideal.map α I ⊔ Ideal.map β I) • (⊤ : Submodule B (Pair α β M N)) := by
  set J := Ideal.map α I ⊔ Ideal.map β I
  intro x hx
  have hex1 : Function.Exact (twistMap β (extMap α (I • (⊤ : Submodule R M)).subtype))
      (twistMap β (extMap α (I • (⊤ : Submodule R M)).mkQ)) :=
    lTensor_exact (Twist α B) (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  have hsurj1 : Function.Surjective (twistMap β (extMap α (I • (⊤ : Submodule R M)).mkQ)) :=
    LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
  have hker := TensorProduct.map_ker hex1 hsurj1 (LinearMap.exact_subtype_mkQ (I • ⊤))
    (Submodule.mkQ_surjective (I • (⊤ : Submodule R N)))
  have hx' : x ∈ LinearMap.ker (TensorProduct.map
      (twistMap β (extMap α (I • (⊤ : Submodule R M)).mkQ)) (I • (⊤ : Submodule R N)).mkQ) := hx
  rw [hker, Submodule.mem_sup] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := hx'
  clear hx
  refine Submodule.add_mem _ ?_ ?_
  · obtain ⟨w, rfl⟩ := hu
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul y n =>
      rw [LinearMap.lTensor_tmul]
      show y ⊗ₜ[R] (n : N) ∈ _
      refine Submodule.smul_induction_on
        (p := fun n₀ => y ⊗ₜ[R] n₀ ∈ J • (⊤ : Submodule B (Pair α β M N))) n.2
        (fun a ha n₀ _ => ?_) (fun n₁ n₂ h₁ h₂ => ?_)
      · rw [TensorProduct.tmul_smul]
        show (β a • y) ⊗ₜ[R] n₀ ∈ J • (⊤ : Submodule B (Pair α β M N))
        rw [← TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul (Ideal.mem_sup_right (Ideal.mem_map_of_mem β ha))
          Submodule.mem_top
      · rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ h₁ h₂
    | add w w' hw hw' => rw [map_add]; exact Submodule.add_mem _ hw hw'
  · obtain ⟨w, rfl⟩ := hv
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul y n =>
      rw [LinearMap.rTensor_tmul]
      obtain ⟨y, rfl⟩ : ∃ y' : Ext α ↥(I • (⊤ : Submodule R M)), Twist.mk β y' = y := ⟨y, rfl⟩
      induction y using TensorProduct.induction_on with
      | zero =>
        show Twist.mk β (extMap α _ 0) ⊗ₜ[R] n ∈ _
        rw [map_zero, Twist.mk_zero, TensorProduct.zero_tmul]
        exact Submodule.zero_mem _
      | tmul b m =>
        obtain ⟨b, rfl⟩ : ∃ b' : B, Twist.mk α b' = b := ⟨b, rfl⟩
        show Twist.mk β (Twist.mk α b ⊗ₜ[R] (m : M) : Ext α M) ⊗ₜ[R] n ∈ _
        refine Submodule.smul_induction_on
          (p := fun m₀ => Twist.mk β (Twist.mk α b ⊗ₜ[R] m₀ : Ext α M) ⊗ₜ[R] n ∈
            J • (⊤ : Submodule B (Pair α β M N))) m.2
          (fun a ha m₀ _ => ?_) (fun m₁ m₂ h₁ h₂ => ?_)
        · rw [← TensorProduct.smul_tmul, Twist.rsmul_mk, ← Twist.smul_mk,
            ← TensorProduct.smul_tmul', ← Twist.smul_mk, ← TensorProduct.smul_tmul']
          exact Submodule.smul_mem_smul (Ideal.mem_sup_left (Ideal.mem_map_of_mem α ha))
            Submodule.mem_top
        · rw [TensorProduct.tmul_add, ← Twist.mk_add, TensorProduct.add_tmul]
          exact Submodule.add_mem _ h₁ h₂
      | add y y' hy hy' =>
        show Twist.mk β (extMap α _ (y + y')) ⊗ₜ[R] n ∈ _
        rw [map_add, ← Twist.mk_add, TensorProduct.add_tmul]
        exact Submodule.add_mem _ hy hy'
    | add w w' hw hw' => rw [map_add]; exact Submodule.add_mem _ hw hw'

end Sandwich

section Growth

open Polynomial

/-- A rational polynomial that is eventually nonnegative at the natural numbers has nonnegative
leading coefficient. -/
private theorem leadingCoeff_nonneg_of_eventually_nat_nonneg {P : ℚ[X]}
    (h : ∀ᶠ t : ℕ in Filter.atTop, 0 ≤ P.eval (t : ℚ)) : 0 ≤ P.leadingCoeff := by
  refine Stacks.HilbertFunction.PolynomialQuotient.leadingCoeff_nonneg_of_eventually_nonneg P ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h
  refine Filter.eventually_atTop.mpr ⟨(N : ℤ), fun k hk => ?_⟩
  have := hN k.toNat (by omega)
  rwa [show ((k.toNat : ℕ) : ℚ) = k by exact_mod_cast Int.toNat_of_nonneg (by omega)] at this

/-- A rational polynomial with positive leading coefficient bounded above at the natural numbers,
eventually, by another polynomial has at most the degree of the other. -/
theorem natDegree_le_of_eventually_le {P Q : ℚ[X]} (hP : 0 < P.leadingCoeff)
    (h : ∀ᶠ t : ℕ in Filter.atTop, P.eval (t : ℚ) ≤ Q.eval (t : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  by_contra hlt
  push Not at hlt
  have hdeg : Q.degree < P.degree := Polynomial.degree_lt_degree hlt
  have hlc : (Q - P).leadingCoeff = -P.leadingCoeff :=
    Polynomial.leadingCoeff_sub_of_degree_lt' hdeg
  have hnn : 0 ≤ (Q - P).leadingCoeff := by
    refine leadingCoeff_nonneg_of_eventually_nat_nonneg ?_
    filter_upwards [h] with t ht
    rw [Polynomial.eval_sub, sub_nonneg]
    exact ht
  linarith

/-- A polynomial computing a function with natural values has nonnegative leading coefficient,
which is positive when the polynomial is nonzero. -/
theorem leadingCoeff_pos_of_eventually_natCast {P : ℚ[X]} (hP0 : P ≠ 0)
    (h : ∀ᶠ t : ℕ in Filter.atTop, ∃ p : ℕ, P.eval (t : ℚ) = (p : ℚ)) : 0 < P.leadingCoeff := by
  have hnonneg : 0 ≤ P.leadingCoeff := by
    refine leadingCoeff_nonneg_of_eventually_nat_nonneg ?_
    filter_upwards [h] with t ⟨p, hp⟩
    rw [hp]
    positivity
  exact lt_of_le_of_ne hnonneg (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hP0))

end Growth

section LocalQuotient

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] in
/-- Nakayama: the reduction of a nonzero finite module modulo the maximal ideal is nonzero. -/
theorem nontrivial_quotient_maximalIdeal_smul (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    Nontrivial (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M)) := by
  have h : (⊤ : Submodule R M) ≠ maximalIdeal R • ⊤ :=
    Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (maximalIdeal_le_jacobson _)
  rw [Submodule.Quotient.nontrivial_iff]
  exact fun hh => h hh.symm

/-- The reduction of a nonzero finite module modulo the maximal ideal has dimension zero. -/
theorem supportDim_quotient_maximalIdeal_smul (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    Module.supportDim R (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M)) = 0 := by
  have hne := nontrivial_quotient_maximalIdeal_smul (R := R) M
  have hann : Module.annihilator R M ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal (mt Module.annihilator_eq_top_iff.mp (not_subsingleton M))
  have hdef : IsIdealOfDefinition (maximalIdeal R + Module.annihilator R M) := by
    rw [isIdealOfDefinition_iff, show maximalIdeal R + Module.annihilator R M = maximalIdeal R
      from sup_eq_left.mpr hann]
    exact (maximalIdeal.isMaximal R).isPrime.radical
  have hle : Module.supportDim R (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M)) ≤ 0 :=
    ((Ideal.idealOfDefinition_support_length_tfae (maximalIdeal R) hne).out 1 4).mp hdef
  have hne' : Module.supportDim R (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M)) ≠ ⊥ :=
    (Module.supportDim_ne_bot_iff_nontrivial R _).mpr hne
  refine le_antisymm hle ?_
  cases h : Module.supportDim R (M ⧸ (maximalIdeal R) • (⊤ : Submodule R M)) with
  | bot => exact absurd h hne'
  | coe x => exact WithBot.coe_le_coe.mpr (zero_le (a := x))

end LocalQuotient

end Stacks.SerreIntersection
