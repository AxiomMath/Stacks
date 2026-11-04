module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeDualShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeDualSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeModuleTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeTensorShortExact
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleModuleDual
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingInduction

/-!
# Multiplicative invariants of duals and tensor products of filtered modules on a space

Let `Z` be an algebraic space and let `c` be an invariant of finite locally free `𝒪_Z`-modules of
given rank, with values in a ring `R`, which is multiplicative on short exact sequences and equal
to `1` in rank `0`; the total Chern class is the example. If `ℰ` has a filtration with invertible
successive quotients `ℒ_1, …, ℒ_r`, then `c(ℰ) = c(ℒ_1) ⋯ c(ℒ_r)`, and if `ℱ` has one with
quotients `𝒩_1, …, 𝒩_s`, then `c(ℰ ⊗ ℱ) = ∏_{i, j} c(ℒ_i ⊗ 𝒩_j)`. If moreover `σ` is a ring
endomorphism of `R` with `c(ℒ^∨) = σ(c(ℒ))` for every invertible `ℒ`, then `c(ℰ^∨) = σ(c(ℰ))`:
the dual of each step `0 ⟶ 𝒜 ⟶ ℰ ⟶ ℒ ⟶ 0` of the filtration is a short exact sequence
`0 ⟶ ℒ^∨ ⟶ ℰ^∨ ⟶ 𝒜^∨ ⟶ 0`.

For the total Chern class, and the endomorphism multiplying the degree `i` part by `(-1)^i`, these
are the reductions of Stacks 0ESD and Stacks 0ESE to invertible modules made in the source's
proofs.

## Main results

* `AlgebraicGeometry.Space.isZero_dual_of_isZero`: the dual of a zero module is zero.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength`: a filtration of
  length `r` by invertible quotients gives rank `r`.
* `AlgebraicGeometry.Space.map_dual_of_hasFiltrationOfLength`: `c(ℰ^∨) = σ(c(ℰ))` for `ℰ` with
  a filtration by invertible successive quotients.
* `AlgebraicGeometry.Space.exists_list_of_hasFiltrationOfLength`: `c(ℰ) = ∏ c(ℒ_i)` over the
  invertible successive quotients of a filtration, also after tensoring with a module.
* `AlgebraicGeometry.Space.exists_lists_tensor_of_hasFiltrationOfLength`:
  `c(ℰ ⊗ ℱ) = ∏_{i, j} c(ℒ_i ⊗ 𝒩_j)`.

## Implementation notes

The invariant takes the rank as an argument, as the Chern classes of chapter 82 do; the
filtrations are `CategoryTheory.ObjectProperty.HasFiltrationOfLength` for the invertible
modules, the form in which the splitting principle produces them.

## References

* [Stacks Project, Tag 0ESD](https://stacks.math.columbia.edu/tag/0ESD)
* [Stacks Project, Tag 0ESE](https://stacks.math.columbia.edu/tag/0ESE)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Limits

universe u v

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] modulesMonoidalCategory modulesMonoidalClosed
  modulesMonoidalPreadditive

attribute [local instance 10000] smallEtaleModulesAbelian

/-- **The dual of a zero `𝒪_F`-module is zero.** -/
theorem isZero_dual_of_isZero {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {E : Modules.{u, u} B S hS F hF} (hE : IsZero E) :
    IsZero ((ihom E).obj (𝟙_ _)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (ihom.adjunction E).homEquiv _ _ |>.symm.injective
  have hET : IsZero (E ⊗ (ihom E).obj (𝟙_ _)) := by
    rw [IsZero.iff_id_eq_zero] at hE ⊢
    rw [← MonoidalCategory.id_whiskerRight, hE, MonoidalPreadditive.zero_whiskerRight]
  exact hET.eq_of_src _ _

variable {Z : AlgebraicSpaces B S hS}

/-- **A module with a filtration of length `r` by invertible successive quotients is finite
locally free of rank `r`**: each step of the filtration is an extension by an invertible module,
of rank one. -/
theorem isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength {r : ℕ}
    {E : Modules.{u, u} B S hS Z.1 Z.2}
    (hE : (PrivateChern.invertibleModules B S hS Z).HasFiltrationOfLength r E) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2) E r := by
  induction hE with
  | zero hE => exact RingedSite.isFiniteLocallyFreeOfRank_zero_of_isZero _ hE
  | @succ r A E ι hι hA hq ih =>
    have hT : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι))
        hι inferInstance
    exact RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact _ hT ih
      (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z hq)

section Invariant

variable {R : Type v} [Ring R]
  (c : ∀ (r : ℕ) (E : Modules.{u, u} B S hS Z.1 Z.2),
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2) E r → R)

omit [Ring R] in
/-- The value of a rank-indexed invariant does not depend on how the rank is written. -/
theorem invariant_congr {r r' : ℕ} (hrr' : r = r') {E : Modules.{u, u} B S hS Z.1 Z.2}
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2) E r)
    (h' : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2) E r') :
    c r E h = c r' E h' := by
  subst hrr'
  rfl

/-- The short exact sequence `0 ⟶ 𝒜 ⟶ ℰ ⟶ ℰ/𝒜 ⟶ 0` of a monomorphism. -/
private theorem shortExact_cokernel {A E : Modules.{u, u} B S hS Z.1 Z.2} (ι : A ⟶ E) [Mono ι] :
    (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel ι))
    inferInstance inferInstance

/-- **The reduction of Stacks 0ESD to invertible modules.** Let `c` be an invariant of finite
locally free `𝒪_Z`-modules of given rank with values in a ring `R`, multiplicative on short exact
sequences and equal to `1` in rank `0`, and `σ` a ring endomorphism of `R` with
`c(ℒ^∨) = σ(c(ℒ))` for `ℒ` invertible. If `ℰ` has a filtration with invertible successive
quotients, and the class of each step of the filtration commutes with that of its quotient, then
`c(ℰ^∨) = σ(c(ℰ))`. -/
theorem map_dual_of_hasFiltrationOfLength (σ : R →+* R)
    (hzero : ∀ E h, c 0 E h = 1)
    (hmul : ∀ (T : ShortComplex (Modules.{u, u} B S hS Z.1 Z.2)), T.ShortExact →
      ∀ (r₁ r₃ : ℕ) h₁ h₂ h₃, c (r₁ + r₃) T.X₂ h₂ = c r₁ T.X₁ h₁ * c r₃ T.X₃ h₃)
    (hinv : ∀ (L : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L),
      c 1 ((ihom L).obj (𝟙_ _))
          (isFiniteLocallyFreeOfRank_dual B S hS Z.1 Z.2 L
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z hL)) =
        σ (c 1 L (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z hL)))
    (hcomm : ∀ (r : ℕ) (A L : Modules.{u, u} B S hS Z.1 Z.2)
      (hA : (PrivateChern.invertibleModules B S hS Z).HasFiltrationOfLength r A)
      (hL : IsInvertibleModule Z L),
      Commute (c r A (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hA))
        (c 1 L (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z hL)))
    {r : ℕ} {E : Modules.{u, u} B S hS Z.1 Z.2}
    (hE : (PrivateChern.invertibleModules B S hS Z).HasFiltrationOfLength r E) :
    c r ((ihom E).obj (𝟙_ _))
        (isFiniteLocallyFreeOfRank_dual B S hS Z.1 Z.2 E
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE)) =
      σ (c r E (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE)) := by
  induction hE with
  | zero hE => rw [hzero, hzero, map_one]
  | @succ r A E ι hι hA hq ih =>
    have hT := shortExact_cokernel ι
    have hq' : IsInvertibleModule Z (cokernel ι) := hq
    have h₁ := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hA
    have h₃ := isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z hq'
    have h₂ := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength (.succ ι hA hq)
    obtain ⟨a, b, w, hab⟩ := exists_shortExact_dual B S hS Z.1 Z.2 hT h₁.isFiniteLocallyFreeOnSite
      h₂.isFiniteLocallyFreeOnSite h₃.isFiniteLocallyFreeOnSite
    have hd₂ := isFiniteLocallyFreeOfRank_dual B S hS Z.1 Z.2 E h₂
    have hd₂' : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2)
        ((ihom E).obj (𝟙_ _)) (1 + r) := add_comm r 1 ▸ hd₂
    have key₁ := hmul _ hab 1 r (isFiniteLocallyFreeOfRank_dual B S hS Z.1 Z.2 _ h₃) hd₂'
      (isFiniteLocallyFreeOfRank_dual B S hS Z.1 Z.2 _ h₁)
    have key₂ := hmul _ hT r 1 h₁ h₂ h₃
    have hL := hinv _ hq'
    calc c (r + 1) ((ihom E).obj (𝟙_ _)) _ = c (1 + r) ((ihom E).obj (𝟙_ _)) hd₂' :=
          invariant_congr c (add_comm r 1) _ _
      _ = σ (c 1 (cokernel ι) h₃) * σ (c r A h₁) := by
          rw [key₁]
          exact congrArg₂ (· * ·) hL ih
      _ = σ (c (r + 1) E h₂) := by
          rw [key₂, map_mul]
          exact ((hcomm r A _ hA hq').map σ).eq.symm

/-- **The invertible successive quotients of a filtration compute a multiplicative invariant.**
Let `c` be an invariant of finite locally free `𝒪_Z`-modules of given rank, multiplicative on short
exact sequences and equal to `1` in rank `0`. If `ℰ` has a filtration of length `r` with
invertible successive quotients, there is a list `ℒ_1, …, ℒ_r` of invertible modules, the
quotients from the bottom up, with `c(ℰ) = c(ℒ_1) ⋯ c(ℒ_r)` and
`c(ℳ ⊗ ℰ) = c(ℳ ⊗ ℒ_1) ⋯ c(ℳ ⊗ ℒ_r)` for every finite locally free `ℳ`. -/
theorem exists_list_of_hasFiltrationOfLength (hzero : ∀ E h, c 0 E h = 1)
    (hmul : ∀ (T : ShortComplex (Modules.{u, u} B S hS Z.1 Z.2)), T.ShortExact →
      ∀ (r₁ r₃ : ℕ) h₁ h₂ h₃, c (r₁ + r₃) T.X₂ h₂ = c r₁ T.X₁ h₁ * c r₃ T.X₃ h₃)
    {r : ℕ} {E : Modules.{u, u} B S hS Z.1 Z.2}
    (hE : (PrivateChern.invertibleModules B S hS Z).HasFiltrationOfLength r E) :
    ∃ Ls : List {L : Modules.{u, u} B S hS Z.1 Z.2 // IsInvertibleModule Z L}, Ls.length = r ∧
      c r E (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE) =
        (Ls.map fun L => c 1 L.1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z L.2)).prod ∧
      ∀ (m : ℕ) (M : Modules.{u, u} B S hS Z.1 Z.2)
        (hM : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2) M m),
        c (m * r) (M ⊗ E) (isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2 hM
            (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE)) =
          (Ls.map fun L => c (m * 1) (M ⊗ L.1) (isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2
            hM (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z L.2))).prod := by
  induction hE with
  | @zero E hE =>
    refine ⟨[], rfl, hzero _ _, fun m M hM => ?_⟩
    have hME : IsZero (M ⊗ E) := by
      rw [IsZero.iff_id_eq_zero] at hE ⊢
      rw [← MonoidalCategory.whiskerLeft_id, hE, MonoidalPreadditive.whiskerLeft_zero]
    rw [invariant_congr c (mul_zero m) _
      (RingedSite.isFiniteLocallyFreeOfRank_zero_of_isZero _ hME), hzero]
    rfl
  | @succ r A E ι hι hA hq ih =>
    obtain ⟨Ls, hlen, hcA, hMA⟩ := ih
    have hT := shortExact_cokernel ι
    have hq' : IsInvertibleModule Z (cokernel ι) := hq
    have h₁ := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hA
    have h₂ := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength (.succ ι hA hq)
    have h₃ := isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z hq'
    refine ⟨Ls ++ [⟨cokernel ι, hq'⟩], by simp [hlen], ?_, fun m M hM => ?_⟩
    · rw [hmul _ hT r 1 h₁ h₂ h₃, hcA]
      simp
    · have hM₁ := isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2 hM h₁
      have hM₃ := isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2 hM h₃
      have hM₂ : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2)
          (M ⊗ E) (m * r + m * 1) :=
        Nat.mul_add m r 1 ▸ isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2 hM h₂
      have key : c (m * r + m * 1) (M ⊗ E) hM₂ = c (m * r) (M ⊗ A) hM₁ *
          c (m * 1) (M ⊗ cokernel ι) hM₃ :=
        hmul _ (shortExact_map_tensorLeft B S hS Z.1 Z.2 hT M hM.isFiniteLocallyFreeOnSite)
          (m * r) (m * 1) hM₁ hM₂ hM₃
      rw [invariant_congr c (Nat.mul_add m r 1) _ hM₂, key, hMA m M hM]
      simp

/-- **The roots of a tensor product.** For an invariant `c` of finite locally free
`𝒪_Z`-modules of given rank, multiplicative on short exact sequences and equal to `1` in rank
`0`, and modules `ℰ`, `ℱ` with filtrations of lengths `r`, `s` by invertible successive quotients,
there are lists `ℒ_1, …, ℒ_r` and `𝒩_1, …, 𝒩_s` of invertible modules with
`c(ℰ) = ∏ c(ℒ_i)`, `c(ℱ) = ∏ c(𝒩_j)` and `c(ℰ ⊗ ℱ) = ∏_{i, j} c(ℒ_i ⊗ 𝒩_j)`, the pairs ordered
lexicographically. This is the reduction of Stacks 0ESE to invertible modules. -/
theorem exists_lists_tensor_of_hasFiltrationOfLength (hzero : ∀ E h, c 0 E h = 1)
    (hmul : ∀ (T : ShortComplex (Modules.{u, u} B S hS Z.1 Z.2)), T.ShortExact →
      ∀ (r₁ r₃ : ℕ) h₁ h₂ h₃, c (r₁ + r₃) T.X₂ h₂ = c r₁ T.X₁ h₁ * c r₃ T.X₃ h₃)
    {r s : ℕ} {E F' : Modules.{u, u} B S hS Z.1 Z.2}
    (hE : (PrivateChern.invertibleModules B S hS Z).HasFiltrationOfLength r E)
    (hF : (PrivateChern.invertibleModules B S hS Z).HasFiltrationOfLength s F') :
    ∃ Ls Ns : List {L : Modules.{u, u} B S hS Z.1 Z.2 // IsInvertibleModule Z L},
      Ls.length = r ∧ Ns.length = s ∧
      c r E (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE) =
        (Ls.map fun L => c 1 L.1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z L.2)).prod ∧
      c s F' (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hF) =
        (Ns.map fun N => c 1 N.1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z N.2)).prod ∧
      c (r * s) (E ⊗ F') (isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE)
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hF)) =
        (Ls.flatMap fun L => Ns.map fun N => c (1 * 1) (L.1 ⊗ N.1)
          (isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z L.2)
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z N.2))).prod := by
  obtain ⟨Ns, hNlen, hcF, hMF⟩ := exists_list_of_hasFiltrationOfLength c hzero hmul hF
  have hF' := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hF
  suffices h : ∃ Ls : List {L : Modules.{u, u} B S hS Z.1 Z.2 // IsInvertibleModule Z L},
      Ls.length = r ∧
      c r E (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE) =
        (Ls.map fun L => c 1 L.1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z L.2)).prod ∧
      c (r * s) (E ⊗ F') (isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2
          (isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hE) hF') =
        (Ls.flatMap fun L => Ns.map fun N => c (1 * 1) (L.1 ⊗ N.1)
          (isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z L.2)
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z N.2))).prod by
    obtain ⟨Ls, hlen, hcE, hcEF⟩ := h
    exact ⟨Ls, Ns, hlen, hNlen, hcE, hcF, hcEF⟩
  induction hE with
  | @zero E hE =>
    refine ⟨[], rfl, hzero _ _, ?_⟩
    have hEF : IsZero (E ⊗ F') := by
      rw [IsZero.iff_id_eq_zero] at hE ⊢
      rw [← MonoidalCategory.id_whiskerRight, hE, MonoidalPreadditive.zero_whiskerRight]
    rw [invariant_congr c (zero_mul s) _
      (RingedSite.isFiniteLocallyFreeOfRank_zero_of_isZero _ hEF), hzero]
    rfl
  | @succ r A E ι hι hA hq ih =>
    obtain ⟨Ls, hlen, hcA, hAF⟩ := ih
    have hT := shortExact_cokernel ι
    have hq' : IsInvertibleModule Z (cokernel ι) := hq
    have h₁ := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength hA
    have h₂ := isFiniteLocallyFreeOfRank_of_hasFiltrationOfLength (.succ ι hA hq)
    have h₃ := isFiniteLocallyFreeOfRank_one_of_isInvertibleModule Z hq'
    refine ⟨Ls ++ [⟨cokernel ι, hq'⟩], by simp [hlen], ?_, ?_⟩
    · rw [hmul _ hT r 1 h₁ h₂ h₃, hcA]
      simp
    · have h₁F := isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2 h₁ hF'
      have h₃F := isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2 h₃ hF'
      have h₂F : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Z.1 Z.2)
          (E ⊗ F') (r * s + 1 * s) :=
        Nat.add_mul r 1 s ▸ isFiniteLocallyFreeOfRank_tensorObj B S hS Z.1 Z.2 h₂ hF'
      have key : c (r * s + 1 * s) (E ⊗ F') h₂F = c (r * s) (A ⊗ F') h₁F *
          c (1 * s) (cokernel ι ⊗ F') h₃F :=
        hmul _ (shortExact_map_tensorRight B S hS Z.1 Z.2 hT F' hF'.isFiniteLocallyFreeOnSite)
          (r * s) (1 * s) h₁F h₂F h₃F
      rw [invariant_congr c (Nat.add_mul r 1 s) _ h₂F, key, hAF, hMF 1 (cokernel ι) h₃]
      simp

end Invariant

end AlgebraicGeometry.Space

end
