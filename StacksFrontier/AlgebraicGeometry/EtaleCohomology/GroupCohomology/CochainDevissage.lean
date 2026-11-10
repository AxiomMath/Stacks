module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.PrimeToIndexTransfer

/-!
# Dévissage for the degree-two cochain statement

Two reductions for the statement `Stacks.GroupCohomology.VanishesTwo`, that every locally constant
`2`-cocycle with values in a discrete module is the coboundary of a locally constant `1`-cochain.

## Main results

* `Stacks.GroupCohomology.exists_dOne_eq_of_openSubgroup`: the transfer of
  `Stacks.GroupCohomology.exists_dOne_eq_of_transversal` along the right cosets of an open subgroup
  of a compact group, with the cocycle no longer required to be normalized and the trivialization
  over the subgroup given on the subgroup itself.
* `Stacks.GroupCohomology.vanishesTwo_of_shortExact`: **dévissage.** If the statement holds for a
  submodule and for the quotient by it, it holds for the module.

## Implementation notes

The right cosets `U \ G` are indexed by the left coset space `G ⧸ U` through `g ↦ ⟦g⁻¹⟧`, with
representatives `i ↦ (Quotient.out i)⁻¹`, except that the coset of `1` is represented by `1`.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8), part (2).
-/

@[expose] public section

open groupCohomology

universe u v

namespace Stacks.GroupCohomology

/-- The coboundary `dOne` is additive. -/
private theorem dOne_add {G : Type u} [Group G] {M : Type v} [AddCommGroup M]
    [DistribMulAction G M] (x y : G → M) :
    dOne (fun g ↦ x g + y g) = dOne x + dOne y := by
  funext p
  simp only [dOne, smul_add, Pi.add_apply]
  abel

/-! ### Extending a locally constant function from an open subgroup -/

section Extend

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A locally constant function on an open subgroup extends to a locally constant function on the
group. -/
theorem exists_isLocallyConstant_extend (U : OpenSubgroup G) {α : Type v} [Zero α]
    {y : U → α} (hy : IsLocallyConstant y) :
    ∃ y' : G → α, IsLocallyConstant y' ∧ ∀ (w : G) (hw : w ∈ U), y' w = y ⟨w, hw⟩ := by
  classical
  refine ⟨fun g ↦ if hg : g ∈ U then y ⟨g, hg⟩ else 0, ?_, fun w hw ↦ by simp [hw]⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ U
  · obtain ⟨V, hVopen, hxV, hV⟩ := (IsLocallyConstant.iff_exists_open y).1 hy ⟨x, hx⟩
    obtain ⟨W, hWopen, hWV⟩ := isOpen_induced_iff.1 hVopen
    have hxW : x ∈ W := by rw [← hWV] at hxV; exact hxV
    refine ⟨W ∩ (U : Set G), hWopen.inter U.isOpen', ⟨hxW, hx⟩, fun g hg ↦ ?_⟩
    have hgU : g ∈ U := hg.2
    have hmemV : (⟨g, hgU⟩ : U) ∈ V := by rw [← hWV]; exact hg.1
    simp only [dite_eq_left hgU, dite_eq_left hx]
    exact hV _ hmemV
  · refine ⟨(U : Set G)ᶜ, U.isClosed.isOpen_compl, hx, fun g hg ↦ ?_⟩
    simp only [Set.mem_compl_iff, SetLike.mem_coe] at hg
    simp [hg, hx]

end Extend

/-! ### The transfer along an open subgroup -/

section OpenSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {M : Type v} [AddCommGroup M] [DistribMulAction G M]

omit [TotallyDisconnectedSpace G] in
/-- A system of representatives for the right cosets of an open subgroup of a compact group, with
the properties `Stacks.GroupCohomology.exists_dOne_eq_of_transversal` asks for. -/
private theorem exists_transversal (U : OpenSubgroup G) :
    ∃ (ι : Type u) (_ : Fintype ι) (rep : ι → G) (idx : G → ι), IsLocallyConstant idx ∧
      (∀ g : G, g * (rep (idx g))⁻¹ ∈ U) ∧ (∀ i, idx (rep i) = i) ∧
      (∀ w ∈ U, ∀ g : G, idx (w * g) = idx g) ∧ rep (idx 1) = 1 ∧
      Fintype.card ι = U.toSubgroup.index := by
  classical
  have : Fintype (G ⧸ U.toSubgroup) := Fintype.ofFinite _
  set e : G ⧸ U.toSubgroup := QuotientGroup.mk 1 with he
  refine ⟨G ⧸ U.toSubgroup, inferInstance, fun i ↦ if i = e then 1 else (Quotient.out i)⁻¹,
    fun g ↦ QuotientGroup.mk g⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun z : G ↦ z * x⁻¹) ⁻¹' (U : Set G), U.isOpen'.preimage (by fun_prop), by simp,
      fun g hg ↦ ?_⟩
    simp only [Set.mem_preimage, SetLike.mem_coe] at hg
    exact QuotientGroup.eq.2 (by simpa using hg)
  · intro g
    dsimp only
    by_cases h : (QuotientGroup.mk g⁻¹ : G ⧸ U.toSubgroup) = e
    · have hg : g ∈ U := by
        have := QuotientGroup.eq.1 (h.trans (by rw [he]))
        simpa using this
      rw [ite_eq_left h, inv_one, mul_one]
      exact hg
    · have hout : (QuotientGroup.mk (Quotient.out
          (QuotientGroup.mk g⁻¹ : G ⧸ U.toSubgroup)) : G ⧸ U.toSubgroup) =
          QuotientGroup.mk g⁻¹ := Quotient.out_eq _
      have hmem := U.toSubgroup.inv_mem (QuotientGroup.eq.1 hout)
      rw [ite_eq_right h, inv_inv]
      simpa using hmem
  · intro i
    dsimp only
    by_cases h : i = e
    · rw [h, ite_eq_left (rfl : e = e), inv_one]
    · rw [ite_eq_right h, inv_inv]
      exact Quotient.out_eq _
  · intro w hw g
    dsimp only
    refine QuotientGroup.eq.2 ?_
    simpa [mul_assoc] using hw
  · simp [he]
  · rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]

omit [TotallyDisconnectedSpace G] in
/-- **The transfer along an open subgroup of a compact group.** If a locally constant `2`-cocycle
of `G` with values in `M` becomes the coboundary of a locally constant `1`-cochain on an open
subgroup `U`, and if the index of `U` is invertible on `M`, then it is already the coboundary of a
locally constant `1`-cochain on `G`. -/
theorem exists_dOne_eq_of_openSubgroup (hM : HasOpenStabilizers G M) (U : OpenSubgroup G)
    (k : ℤ) (hk : ∀ m : M, (k * (U.toSubgroup.index : ℤ)) • m = m)
    (F : G × G → M) (hFlc : IsLocallyConstant F) (hF : IsCocycle₂ F)
    (y : U → M) (hylc : IsLocallyConstant y)
    (hy : ∀ w v : U, (w : G) • y v - y (w * v) + y w = F ((w : G), (v : G))) :
    ∃ x : G → M, IsLocallyConstant x ∧ dOne x = F := by
  classical
  obtain ⟨ι, hfin, rep, idx, hidxlc, hmem, hidx_rep, hidx_mul, hrep_one, hcard⟩ :=
    exists_transversal U
  set c : M := F (1, 1) with hc
  set F' : G × G → M := fun p ↦ F p - dOne (fun _ : G ↦ c) p with hF'def
  obtain ⟨hF'coc, hF'one⟩ := isCocycle₂_sub_dOne_const hF
  have hdeq : dOne (fun _ : G ↦ c) = fun p : G × G ↦ p.1 • c := by
    funext p
    obtain ⟨g₁, g₂⟩ := p
    simp only [dOne_apply, sub_add_cancel]
  have hdlc : IsLocallyConstant (dOne (fun _ : G ↦ c)) := by
    rw [hdeq]
    exact (hM.isLocallyConstant_smul c).comp_continuous continuous_fst
  have hF'lc : IsLocallyConstant F' := hFlc.comp₂ hdlc (· - ·)
  obtain ⟨y', hy'lc, hy'_apply⟩ := exists_isLocallyConstant_extend U (y := fun w ↦ y w - c)
    (hylc.comp₂ (IsLocallyConstant.const c) (· - ·))
  have hy' : ∀ w ∈ U, ∀ v ∈ U, w • y' v - y' (w * v) + y' w = F' (w, v) := by
    intro w hw v hv
    have hwv : w * v ∈ U := U.toSubgroup.mul_mem hw hv
    have hmain : w • y ⟨v, hv⟩ - y ⟨w * v, hwv⟩ + y ⟨w, hw⟩ = F (w, v) := hy ⟨w, hw⟩ ⟨v, hv⟩
    rw [hy'_apply v hv, hy'_apply (w * v) hwv, hy'_apply w hw]
    simp only [hF'def, dOne_apply, smul_sub]
    rw [← hmain]
    abel
  obtain ⟨x, hxlc, hx⟩ := exists_dOne_eq_of_transversal U.toSubgroup rep idx hidxlc hmem
    hidx_rep hidx_mul hrep_one k (by rwa [hcard]) F' hF'lc hF'coc hF'one y' hy'lc hy'
  refine ⟨fun g ↦ x g + c, hxlc.comp₂ (IsLocallyConstant.const c) (· + ·), ?_⟩
  rw [dOne_add x fun _ ↦ c, hx]
  funext p
  simp only [hF'def, Pi.add_apply, sub_add_cancel]

end OpenSubgroup

/-! ### Dévissage -/

section Devissage

variable {G : Type u} [Group G] [TopologicalSpace G]
  {M₁ : Type v} [AddCommGroup M₁] [DistribMulAction G M₁]
  {M₂ : Type v} [AddCommGroup M₂] [DistribMulAction G M₂]
  {M₃ : Type v} [AddCommGroup M₃] [DistribMulAction G M₃]

omit [TopologicalSpace G] in
/-- A `2`-cocycle whose image under an injective equivariant map is a `2`-cocycle is one. -/
theorem isCocycle₂_of_comp (φ : M₁ →+ M₂) (hφ : Function.Injective φ)
    (hφe : ∀ (g : G) (m : M₁), φ (g • m) = g • φ m) {f : G × G → M₁}
    (hf : IsCocycle₂ (φ ∘ f)) : IsCocycle₂ f :=
  fun g h j ↦ hφ (by simpa only [Function.comp_apply, map_add, hφe] using hf g h j)

/-- **Dévissage for the degree-two cochain statement.** For a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of discrete `G`-modules, the statement for `M₁` and for `M₃` gives it for
`M₂`. -/
theorem vanishesTwo_of_shortExact [IsTopologicalGroup G] (hM₂ : HasOpenStabilizers G M₂)
    (φ : M₁ →+ M₂) (hφ : Function.Injective φ)
    (hφe : ∀ (g : G) (m : M₁), φ (g • m) = g • φ m)
    (ψ : M₂ →+ M₃) (hψ : Function.Surjective ψ)
    (hψe : ∀ (g : G) (m : M₂), ψ (g • m) = g • ψ m)
    (hex : ∀ z : M₂, ψ z = 0 → ∃ m : M₁, φ m = z)
    (h₁ : VanishesTwo G M₁) (h₃ : VanishesTwo G M₃) : VanishesTwo G M₂ := by
  classical
  intro F hFlc hF
  obtain ⟨x₃, hx₃lc, hx₃⟩ := h₃ (fun p ↦ ψ (F p)) (hFlc.comp (ψ : M₂ → M₃))
    (isCocycle₂_comp ψ hψe hF)
  obtain ⟨x₂, hx₂lc, hψx₂⟩ : ∃ x₂ : G → M₂, IsLocallyConstant x₂ ∧ ∀ g, ψ (x₂ g) = x₃ g :=
    ⟨fun g ↦ Function.surjInv hψ (x₃ g), hx₃lc.comp (Function.surjInv hψ),
      fun g ↦ Function.surjInv_eq hψ (x₃ g)⟩
  have hψd : ∀ p, ψ (dOne x₂ p) = ψ (F p) := by
    intro p
    have e := congrFun (dOne_map ψ hψe x₂) p
    simp only [Function.comp_apply] at e
    rw [e, show (fun g ↦ ψ (x₂ g)) = x₃ from funext hψx₂, congrFun hx₃ p]
  have hF₂lc : IsLocallyConstant fun p : G × G ↦ F p - dOne x₂ p :=
    hFlc.comp₂ (isLocallyConstant_dOne hM₂ hx₂lc) (· - ·)
  obtain ⟨F₁, hF₁lc, hF₁eq⟩ : ∃ F₁ : G × G → M₁, IsLocallyConstant F₁ ∧
      ∀ p, φ (F₁ p) = F p - dOne x₂ p := by
    refine ⟨fun p ↦ Function.invFun φ (F p - dOne x₂ p), hF₂lc.comp (Function.invFun φ),
      fun p ↦ ?_⟩
    obtain ⟨m, hm⟩ := hex (F p - dOne x₂ p) (by rw [map_sub, hψd p, sub_self])
    dsimp only
    rw [← hm, Function.leftInverse_invFun hφ m]
  have hF₁coc : IsCocycle₂ F₁ := by
    refine isCocycle₂_of_comp φ hφ hφe ?_
    intro g h j
    simp only [Function.comp_apply, hF₁eq]
    have ha := hF g h j
    have hb := isCocycle₂_dOne x₂ g h j
    rw [show F (g * h, j) - dOne x₂ (g * h, j) + (F (g, h) - dOne x₂ (g, h)) =
        (F (g * h, j) + F (g, h)) - (dOne x₂ (g * h, j) + dOne x₂ (g, h)) by abel, ha, hb,
      smul_sub]
    abel
  obtain ⟨x₁, hx₁lc, hx₁⟩ := h₁ F₁ hF₁lc hF₁coc
  refine ⟨fun g ↦ x₂ g + φ (x₁ g), hx₂lc.comp₂ (hx₁lc.comp (φ : M₁ → M₂)) (· + ·), ?_⟩
  rw [dOne_add, ← dOne_map φ hφe, hx₁]
  funext p
  simp only [Pi.add_apply, Function.comp_apply, hF₁eq]
  abel

end Devissage

end Stacks.GroupCohomology

end
