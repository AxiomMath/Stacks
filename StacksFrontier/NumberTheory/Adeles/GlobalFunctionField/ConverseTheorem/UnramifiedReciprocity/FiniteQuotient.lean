module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.ConverseTheorem.CentralCharacter

/-!
# Reduction of reciprocity to characters with open kernel

Let `G` be a profinite group, `F : ι → G` a family of elements and `D : ι →₀ ℤ`. For a
continuous character `χ : G →* M` to a commutative group (with closed kernel) the element
`∏_i χ(F_i) ^ D(i)` is trivial as soon as `∏_i ψ(F_i) ^ D(i) = 1` for every homomorphism
`ψ` with open kernel to a commutative group: `χ(G)` is the quotient of `G` by the closed subgroup
`ker χ`, which is the intersection of the open subgroups containing it, and each such open
subgroup `N` is the kernel of `G → χ(G) / χ(N)`.

Applied to `G = π₁(X)` and `F_v` a geometric Frobenius element at `v`, this reduces the
unramified reciprocity law for a continuous `χ : π₁(X) →* Eˣ` (`E` a finite extension of `ℚ_ℓ`)
to the case of characters of finite order, i.e. to finite abelian quotients of `π₁(X)`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.finsuppProd_eq_one_of_forall_isOpen_ker`.
* `Stacks.Adeles.GlobalFunctionField.divisorCharacter_eq_one_of_forall_isOpen_ker` — the same
  for `divisorCharacter (fun v => χ (F v))`, `χ : G →* Λˣ` with `Λ` a `T₁` topological ring and
  `g ↦ χ(g)` continuous as a map to `Λ`.
-/

@[expose] public noncomputable section

universe u w

namespace Stacks.Adeles.GlobalFunctionField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **Characters with open kernel detect `∏_i χ(F_i) ^ D(i) = 1`.** -/
public theorem finsuppProd_eq_one_of_forall_isOpen_ker {M : Type w} [CommGroup M] (χ : G →* M)
    (hχ : IsClosed (χ.ker : Set G)) {ι : Type*} (F : ι → G) (D : ι →₀ ℤ)
    (h : ∀ {A : Type w} [CommGroup A] (ψ : G →* A), IsOpen (ψ.ker : Set G) →
      (D.prod fun i n => ψ (F i) ^ n) = 1) :
    (D.prod fun i n => χ (F i) ^ n) = 1 := by
  set χ' : G →* χ.range := χ.rangeRestrict
  have hcoe : ((D.prod fun i n => χ' (F i) ^ n : χ.range) : M) = D.prod fun i n => χ (F i) ^ n :=
    by change χ.range.subtype _ = _; simp only [map_finsuppProd, map_zpow]; rfl
  rw [← hcoe]
  obtain ⟨g, hg⟩ := χ.rangeRestrict_surjective (D.prod fun i n => χ' (F i) ^ n)
  rw [← hg]
  have hker : χ'.ker = χ.ker := χ.ker_rangeRestrict
  suffices g ∈ χ.ker from this
  have hK : χ.ker = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ χ.ker ≤ N} :=
    ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨χ.ker, hχ⟩ : ClosedSubgroup G)
  rw [hK, Subgroup.mem_sInf]
  rintro N ⟨hNo, hKN⟩
  -- `ψ : G → χ(G) / χ(N)` has kernel `N`.
  let ψ : G →* χ.range ⧸ N.map χ' := (QuotientGroup.mk' (N.map χ')).comp χ'
  have hψ : ψ.ker = N := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_map]
    refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
    rintro ⟨y, hy, hyx⟩
    have : y⁻¹ * x ∈ χ.ker := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    simpa using N.mul_mem hy (hKN this)
  have h1 := h ψ (by rwa [hψ])
  have h2 : (D.prod fun i n => ψ (F i) ^ n) = ψ g := by
    rw [MonoidHom.comp_apply, hg]
    simp only [map_finsuppProd, map_zpow]
    rfl
  rwa [h2, ← MonoidHom.mem_ker, hψ] at h1

/-- **Characters with open kernel detect `divisorCharacter (χ ∘ F) D = 1`**, for a character
`χ : G →* Λˣ` of a profinite group with `g ↦ χ(g) ∈ Λ` continuous, `Λ` a `T₁` topological
ring. -/
public theorem divisorCharacter_eq_one_of_forall_isOpen_ker {K : Type*} [Field K]
    {Λ : Type w} [CommRing Λ] [TopologicalSpace Λ] [T1Space Λ] (χ : G →* Λˣ)
    (hχ : Continuous fun g => (χ g : Λ)) (F : Place K → G) (D : Place K →₀ ℤ)
    (h : ∀ {A : Type w} [CommGroup A] (ψ : G →* A), IsOpen (ψ.ker : Set G) →
      (D.prod fun v n => ψ (F v) ^ n) = 1) :
    divisorCharacter (fun v => χ (F v)) (Multiplicative.ofAdd D) = 1 := by
  rw [divisorCharacter_ofAdd]
  refine finsuppProd_eq_one_of_forall_isOpen_ker χ ?_ F D h
  have : (χ.ker : Set G) = (fun g => (χ g : Λ)) ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff,
      Units.val_eq_one]
  rw [this]
  exact isClosed_singleton.preimage hχ

end Stacks.Adeles.GlobalFunctionField

end
