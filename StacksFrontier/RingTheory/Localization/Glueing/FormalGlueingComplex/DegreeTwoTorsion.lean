module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Cech.Substrate
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.TorsionCohomologyBaseChange
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex.Exact
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex.Exact

/-!
# Degree-two cocycles of the glueing complex

The glueing complex one step further: the Čech differential from degree two to degree three, its
value on a three-element index set, and the fact that for a degree-two cocycle `z` and an index
`i`, some power of `f i` times `z` is a coboundary.

## Main results

* `FormalGlueing.glueingDifferential_apply_triple`: the Čech differential on `{a, b, c}`.
* `FormalGlueing.exists_pow_smul_eq_glueingDifferential_of_cocycle`: degree-two cohomology of the
  glueing complex is power torsion.
-/

/-! ### The glueing complex one step further: exactness at its third term -/

section

@[expose] public section

namespace FormalGlueing

universe u v w

open TensorProduct Cech

/-- The two-element index set `{a, b}` for `a ≠ b`. -/
public abbrev pairIndex {r : ℕ} {a b : Fin r} (hab : a ≠ b) :
    {s : Finset (Fin r) // s.card = 2} := ⟨{a, b}, Finset.card_pair hab⟩

/-- On the three-element index set `{a, b, c}` with `a < b < c`, the Čech differential of a
degree-two term is the alternating sum of the restrictions of its components indexed by
`{b, c}`, `{a, c}` and `{a, b}`. -/
public theorem glueingDifferential_apply_triple
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] (z : GlueingTerm f M 2)
    {a b c : Fin r} (hab : a < b) (hbc : b < c) :
    glueingDifferential f M 2 z ⟨{a, b, c}, by
        rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]⟩ =
      cechι f M (show ({b, c} : Finset (Fin r)) ⊆ {a, b, c} by
          intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
          (z (pairIndex (show b ≠ c by omega))) -
        cechι f M (show ({a, c} : Finset (Fin r)) ⊆ {a, b, c} by
          intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
          (z (pairIndex (show a ≠ c by omega))) +
        cechι f M (show ({a, b} : Finset (Fin r)) ⊆ {a, b, c} by
          intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
          (z (pairIndex (show a ≠ b by omega))) := by
  let T : {s : Finset (Fin r) // s.card = 3} := ⟨{a, b, c}, by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_pair (by omega)]⟩
  let α : T.val := ⟨a, by simp [T]⟩
  let β : T.val := ⟨b, by simp [T]⟩
  let γ : T.val := ⟨c, by simp [T]⟩
  have hαβ : α ≠ β := by intro h; have := congrArg Subtype.val h; simp [α, β] at this; omega
  have hαγ : α ≠ γ := by intro h; have := congrArg Subtype.val h; simp [α, γ] at this; omega
  have hβγ : β ≠ γ := by intro h; have := congrArg Subtype.val h; simp [β, γ] at this; omega
  have hT : T.val.attach = {α, β, γ} := by
    ext k
    simp only [Finset.mem_attach, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases k with ⟨k, hk⟩
    rcases (show k = a ∨ k = b ∨ k = c by simpa [T] using hk) with h | h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inr (Or.inr (Subtype.ext h))
  have hsa : cechSign T.val α.val = 1 := by
    have : {k ∈ T.val | k < a} = ∅ := by ext k; simp [T]; omega
    simp [cechSign, α, this]
  have hsb : cechSign T.val β.val = -1 := by
    have : {k ∈ T.val | k < b} = {a} := by ext k; simp [T]; omega
    simp [cechSign, β, this]
  have hsc : cechSign T.val γ.val = 1 := by
    have : {k ∈ T.val | k < c} = {a, b} := by ext k; simp [T]; omega
    simp [cechSign, γ, this, Finset.card_pair (show a ≠ b by omega)]
  have hea : eraseIndex 2 T α = pairIndex (show b ≠ c by omega) := by
    apply Subtype.ext; ext k; simp [eraseIndex, T, α]; omega
  have heb : eraseIndex 2 T β = pairIndex (show a ≠ c by omega) := by
    apply Subtype.ext; ext k; simp [eraseIndex, T, β]; omega
  have hec : eraseIndex 2 T γ = pairIndex (show a ≠ b by omega) := by
    apply Subtype.ext; ext k; simp [eraseIndex, T, γ]; omega
  change glueingDifferential f M 2 z T = _
  simp only [glueingDifferential, LinearMap.pi_apply, LinearMap.sum_apply]
  rw [hT, Finset.sum_insert (by simp [hαβ, hαγ]), Finset.sum_pair hβγ]
  simp only [hsa, hsb, hsc, one_smul, neg_smul, LinearMap.neg_apply]
  have hca : ((cechι f M (Finset.erase_subset α.val T.val)).comp
      (LinearMap.proj (eraseIndex 2 T α))) z =
      cechι f M (show ({b, c} : Finset (Fin r)) ⊆ {a, b, c} by
          intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        (z (pairIndex (show b ≠ c by omega))) :=
    restricted_component_congr f z hea (Finset.erase_subset _ _) _
  have hcb : ((cechι f M (Finset.erase_subset β.val T.val)).comp
      (LinearMap.proj (eraseIndex 2 T β))) z =
      cechι f M (show ({a, c} : Finset (Fin r)) ⊆ {a, b, c} by
          intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        (z (pairIndex (show a ≠ c by omega))) :=
    restricted_component_congr f z heb (Finset.erase_subset _ _) _
  have hcc : ((cechι f M (Finset.erase_subset γ.val T.val)).comp
      (LinearMap.proj (eraseIndex 2 T γ))) z =
      cechι f M (show ({a, b} : Finset (Fin r)) ⊆ {a, b, c} by
          intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
        (z (pairIndex (show a ≠ b by omega))) :=
    restricted_component_congr f z hec (Finset.erase_subset _ _) _
  rw [hca, hcb, hcc]
  abel

/-- `M_s` is the localization of `M` away from any element equal to the product of the `f x`,
`x ∈ s`. -/
private theorem isLocalizedModule_away_cechSub
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (M : Type w) [AddCommGroup M] [Module R M] (s : Finset (Fin r)) {a : R}
    (h : ∏ x ∈ s, f x = a) :
    IsLocalizedModule.Away a (LocalizedModule.mkLinearMap (cechSub f s) M) := by
  simpa only [cechSub, h] using
    (inferInstance : IsLocalizedModule (cechSub f s)
      (LocalizedModule.mkLinearMap (cechSub f s) M))

/-- An element of `M_{f j}` mapping to zero in `M_{f i f j}` is killed by a power of `f i`. This
is the private `exists_pow_smul_eq_zero_of_cechι`, restated. -/
theorem exists_pow_smul_eq_zero_of_cechι_singleton
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] (i j : Fin r)
    (z : cechMod f M {j})
    (hz : cechι f M (by simp : ({j} : Finset (Fin r)) ⊆ {i, j}) z = 0) :
    ∃ n : ℕ, f i ^ n • z = 0 :=
  exists_pow_smul_eq_zero_of_cechι f i j z hz

/-- An element of `M_{f j f k}` mapping to zero in `M_{f i f j f k}` is killed by a power of
`f i`, for `i, j, k` distinct. -/
theorem exists_pow_smul_eq_zero_of_cechι_pair
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] {i j k : Fin r}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (z : cechMod f M {j, k})
    (hz : cechι f M (show ({j, k} : Finset (Fin r)) ⊆ {i, j, k} from
      Finset.subset_insert _ _) z = 0) :
    ∃ n : ℕ, f i ^ n • z = 0 := by
  let g := LocalizedModule.mkLinearMap (cechSub f {j, k}) M
  let ρ := cechι f M (show ({j, k} : Finset (Fin r)) ⊆ {i, j, k} from
    Finset.subset_insert _ _)
  have : IsLocalizedModule.Away (f j * f k) g :=
    isLocalizedModule_away_cechSub f M _ (Finset.prod_pair hjk)
  have : IsLocalizedModule.Away (f i * (f j * f k)) (ρ.comp g) := by
    dsimp [ρ, g]
    rw [cechι_comp_mk]
    exact isLocalizedModule_away_cechSub f M _ (by
      rw [Finset.prod_insert (by simp [hij, hik]), Finset.prod_pair hjk])
  exact exists_pow_smul_eq_zero_of_localization_map (f i) (f j * f k) g ρ z hz

/-- Every element of `M_{f i f j}` becomes, after multiplication by a power of `f i`, the image of
an element of `M_{f j}`, for `i ≠ j`. -/
theorem exists_pow_smul_eq_cechι_singleton
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] {i j : Fin r} (hij : i ≠ j)
    (v : cechMod f M {i, j}) :
    ∃ (e : ℕ) (x : cechMod f M {j}),
      f i ^ e • v = cechι f M (by simp : ({j} : Finset (Fin r)) ⊆ {i, j}) x := by
  have hp : ∏ x ∈ ({i, j} : Finset (Fin r)), f x = f i * f j := Finset.prod_pair hij
  have hloc : IsLocalizedModule.Away (f i * f j)
      (LocalizedModule.mkLinearMap (cechSub f {i, j}) M) :=
    isLocalizedModule_away_cechSub f M _ hp
  obtain ⟨e, m, hm⟩ := IsLocalizedModule.Away.surj
    (LocalizedModule.mkLinearMap (cechSub f {i, j}) M) (f i * f j) v
  let pj : cechSub f {j} := ⟨(∏ x ∈ ({j} : Finset (Fin r)), f x) ^ e, e, rfl⟩
  refine ⟨e, LocalizedModule.mk m pj, ?_⟩
  have hj : (∏ x ∈ ({j} : Finset (Fin r)), f x) = f j := Finset.prod_singleton _ _
  have hmk : (pj : R) • LocalizedModule.mk m pj =
      LocalizedModule.mkLinearMap (cechSub f {j}) M m := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel pj m
  set ρ := cechι f M (by simp : ({j} : Finset (Fin r)) ⊆ {i, j})
  have h1 : f j ^ e • ρ (LocalizedModule.mk m pj) = f i ^ e • (f j ^ e • v) := by
    rw [← map_smul, show f j ^ e = (pj : R) by simp [pj, hj], hmk, cechι_mk, smul_smul,
      ← mul_pow, hj]
    exact hm.symm
  have h2 : (f i * f j) ^ e • (ρ (LocalizedModule.mk m pj) - f i ^ e • v) = 0 := by
    rw [smul_sub, sub_eq_zero, mul_pow, ← smul_smul, h1,
      smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  have hinj := IsLocalizedModule.smul_injective (S := cechSub f {i, j})
    (LocalizedModule.mkLinearMap (cechSub f {i, j}) M) ⟨(f i * f j) ^ e, e, by rw [hp]⟩
  have h3 : ρ (LocalizedModule.mk m pj) - f i ^ e • v = 0 := hinj <| by
    change (f i * f j) ^ e • _ = (f i * f j) ^ e • (0 : cechMod f M {i, j})
    rw [h2, smul_zero]
  exact (sub_eq_zero.mp h3).symm

/-- An element of `M_s`, for a two-element index set `s`, mapping to zero in `M_{insert i s}` is
killed by a power of `f i`. -/
theorem exists_pow_smul_eq_zero_of_cechι_insert
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] (i : Fin r) {a b : Fin r} (hab : a ≠ b)
    (x : cechMod f M {a, b})
    (hx : cechι f M (Finset.subset_insert i ({a, b} : Finset (Fin r))) x = 0) :
    ∃ n : ℕ, f i ^ n • x = 0 := by
  by_cases hi : i ∈ ({a, b} : Finset (Fin r))
  · -- the restriction map is injective, with the restriction back as a left inverse
    have hback : insert i ({a, b} : Finset (Fin r)) ⊆ {a, b} :=
      Finset.insert_subset hi le_rfl
    have h := congrArg (cechι f M hback) hx
    rw [cechι_cechι, cechι_rfl, LinearMap.id_apply, map_zero] at h
    exact ⟨0, by rw [h, smul_zero]⟩
  · have hia : i ≠ a := fun h ↦ hi (h ▸ by simp)
    have hib : i ≠ b := fun h ↦ hi (h ▸ by simp)
    exact exists_pow_smul_eq_zero_of_cechι_pair f hia hib hab x hx

/-- **The cocycle relation on a triple, restricted to a superset.** If `z` is a degree-two
cocycle and `a < b < c` lie in `T`, then the restrictions to `M_T` of its components on `{b, c}`,
`{a, c}` and `{a, b}` satisfy `z_{bc} - z_{ac} + z_{ab} = 0`. -/
theorem cocycle_triple_restrict
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] (z : GlueingTerm f M 2)
    (hz : glueingDifferential f M 2 z = 0)
    {a b c : Fin r} (hab : a < b) (hbc : b < c) (T : Finset (Fin r))
    (hT : ({a, b, c} : Finset (Fin r)) ⊆ T) :
    cechι f M (show ({b, c} : Finset (Fin r)) ⊆ T from fun x hx ↦ hT (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto))
        (z (pairIndex (show b ≠ c by omega))) -
      cechι f M (show ({a, c} : Finset (Fin r)) ⊆ T from fun x hx ↦ hT (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto))
        (z (pairIndex (show a ≠ c by omega))) +
      cechι f M (show ({a, b} : Finset (Fin r)) ⊆ T from fun x hx ↦ hT (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto))
        (z (pairIndex (show a ≠ b by omega))) = 0 := by
  have h := congrArg (cechι f M hT)
    ((glueingDifferential_apply_triple f z hab hbc).symm.trans (congrFun hz _))
  simp only [map_add, map_sub, cechι_cechι] at h
  rw [h, Pi.zero_apply, map_zero]

/-- The component of a degree-two term on `{a, b}`, restricted to a superset `T`, does not depend
on how the two-element set is spelled. -/
theorem cechι_pairIndex_comm
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] (z : GlueingTerm f M 2)
    {a b : Fin r} (hab : a ≠ b) {T : Finset (Fin r)}
    (h₁ : ({a, b} : Finset (Fin r)) ⊆ T) (h₂ : ({b, a} : Finset (Fin r)) ⊆ T) :
    cechι f M h₁ (z (pairIndex hab)) = cechι f M h₂ (z (pairIndex hab.symm)) := by
  have hst : pairIndex hab = pairIndex hab.symm := by
    apply Subtype.ext
    exact Finset.pair_comm a b
  exact restricted_component_congr f z hst h₁ h₂

/-- **The oriented cocycle relation.** For a degree-two cocycle `z`, an index `i` and `a < b`
both different from `i`, with `σ(j) = 1` for `i < j` and `σ(j) = -1` otherwise, the restrictions
to `M_T` satisfy `σ(b) z_{ib} - σ(a) z_{ia} - z_{ab} = 0`. -/
theorem cocycle_oriented_restrict
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] (z : GlueingTerm f M 2)
    (hz : glueingDifferential f M 2 z = 0) {i a b : Fin r} (hab : a < b)
    (hia : i ≠ a) (hib : i ≠ b) (T : Finset (Fin r))
    (hT : ({i, a, b} : Finset (Fin r)) ⊆ T) :
    (if i < b then (1 : R) else -1) • cechι f M (show ({i, b} : Finset (Fin r)) ⊆ T from
        fun x hx ↦ hT (by simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto))
        (z (pairIndex hib)) -
      (if i < a then (1 : R) else -1) • cechι f M (show ({i, a} : Finset (Fin r)) ⊆ T from
        fun x hx ↦ hT (by simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto))
        (z (pairIndex hia)) -
      cechι f M (show ({a, b} : Finset (Fin r)) ⊆ T from
        fun x hx ↦ hT (by simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢; tauto))
        (z (pairIndex (show a ≠ b by omega))) = 0 := by
  have mem : ∀ {x : Fin r}, x = i ∨ x = a ∨ x = b → x ∈ T := fun hx ↦ hT (by
    simp only [Finset.mem_insert, Finset.mem_singleton]; exact hx)
  rcases lt_or_gt_of_ne hia with hia' | hia'
  · -- `i < a < b`
    have hc := cocycle_triple_restrict f z hz hia' hab T (fun x hx ↦ mem (by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx))
    rw [ite_eq_left (hia'.trans hab), ite_eq_left hia', one_smul, one_smul]
    rw [← neg_eq_zero, ← hc]
    abel
  · rcases lt_or_gt_of_ne hib with hib' | hib'
    · -- `a < i < b`
      have hc := cocycle_triple_restrict f z hz hia' hib' T (fun x hx ↦ mem (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx; tauto))
      rw [ite_eq_left hib', ite_eq_right (by omega), one_smul, neg_smul, one_smul,
        cechι_pairIndex_comm f z hia _ (fun x hx ↦ mem (by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx; tauto))]
      rw [← hc]
      abel
    · -- `a < b < i`
      have hc := cocycle_triple_restrict f z hz hab hib' T (fun x hx ↦ mem (by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx; tauto))
      rw [ite_eq_right (by omega), ite_eq_right (by omega), neg_smul, one_smul, neg_smul, one_smul,
        cechι_pairIndex_comm f z hia _ (fun x hx ↦ mem (by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx; tauto)),
        cechι_pairIndex_comm f z hib _ (fun x hx ↦ mem (by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx; tauto))]
      rw [← neg_eq_zero, ← hc]
      abel

/-- **Degree-two cohomology of the glueing complex is power torsion.** For a degree-two cocycle
`z` and an index `i`, some power of `f i` times `z` is a coboundary. -/
theorem exists_pow_smul_eq_glueingDifferential_of_cocycle
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    {M : Type w} [AddCommGroup M] [Module R M] (z : GlueingTerm f M 2)
    (hz : glueingDifferential f M 2 z = 0) (i : Fin r) :
    ∃ (n : ℕ) (w : GlueingTerm f M 1), f i ^ n • z = glueingDifferential f M 1 w := by
  classical
  -- the oriented components `σ(j) z_{ij}` and their lifts to `M_{f j}`
  let σ : Fin r → R := fun j ↦ if i < j then 1 else -1
  have hlift : ∀ j : Fin r, ∀ hij : i ≠ j, ∃ (e : ℕ) (x : cechMod f M {j}),
      f i ^ e • (σ j • z (pairIndex hij)) =
        cechι f M (by simp : ({j} : Finset (Fin r)) ⊆ {i, j}) x :=
    fun j hij ↦ exists_pow_smul_eq_cechι_singleton f hij _
  choose e x hx using hlift
  let E : ℕ := ∑ j : Fin r, if hij : i = j then 0 else e j hij
  have heE : ∀ j (hij : i ≠ j), e j hij ≤ E := fun j hij ↦ by
    have := Finset.single_le_sum (f := fun k ↦ if hik : i = k then 0 else e k hik)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    simpa [hij] using this
  let x' : ∀ j : Fin r, cechMod f M {j} := fun j ↦
    if hij : i = j then 0 else f i ^ (E - e j hij) • x j hij
  have hx'i : x' i = 0 := dite_eq_left rfl
  have hx'T : ∀ j (hij : i ≠ j) (T : Finset (Fin r)) (hT : ({i, j} : Finset (Fin r)) ⊆ T),
      cechι f M (show ({j} : Finset (Fin r)) ⊆ T from fun y hy ↦ hT (by
          simp only [Finset.mem_singleton] at hy; simp [hy])) (x' j) =
        f i ^ E • σ j • cechι f M hT (z (pairIndex hij)) := by
    intro j hij T hT
    have hjT : ({j} : Finset (Fin r)) ⊆ {i, j} := by simp
    rw [← cechι_cechι f M hjT hT]
    simp only [x', dite_eq_right hij, map_smul]
    rw [← hx j hij, map_smul, map_smul, smul_smul, ← pow_add, Nat.sub_add_cancel (heE j hij)]
  -- the degree-one term with components `x'`
  let w : GlueingTerm f M 1 := fun s ↦
    cechι f M (show {(Finset.card_eq_one.mp s.2).choose} ⊆ s.val from
      (Finset.card_eq_one.mp s.2).choose_spec.symm.le) (x' (Finset.card_eq_one.mp s.2).choose)
  have hw : ∀ j : Fin r, w (singletonIndex j) = x' j := by
    intro j
    have key : ∀ (k : Fin r) (hk : k = j) (h : ({k} : Finset (Fin r)) ⊆ {j}),
        cechι f M h (x' k) = x' j := by
      rintro k rfl h
      rw [cechι_rfl, LinearMap.id_apply]
    exact key _ (Finset.singleton_inj.mp
      (Finset.card_eq_one.mp (singletonIndex j).2).choose_spec.symm) _
  -- on each pair, the defect is killed by a power of `f i`
  have hpair : ∀ s : {s : Finset (Fin r) // s.card = 2}, ∃ m : ℕ,
      f i ^ m • (glueingDifferential f M 1 w s - f i ^ E • z s) = 0 := by
    rintro ⟨T, hT⟩
    obtain ⟨a, b, hab, rfl⟩ : ∃ a b : Fin r, a < b ∧ T = {a, b} := by
      obtain ⟨a, b, hne, rfl⟩ := Finset.card_eq_two.mp hT
      rcases lt_or_gt_of_ne hne with h | h
      · exact ⟨a, b, h, rfl⟩
      · exact ⟨b, a, h, Finset.pair_comm a b⟩
    change ∃ m : ℕ, f i ^ m • (glueingDifferential f M 1 w (pairIndex hab.ne) -
      f i ^ E • z (pairIndex hab.ne)) = 0
    rw [glueingDifferential_apply_pair f w hab, hw, hw]
    apply exists_pow_smul_eq_zero_of_cechι_insert f i hab.ne
    have hsub : ({i, a, b} : Finset (Fin r)) ⊆ insert i ({a, b} : Finset (Fin r)) := le_rfl
    simp only [map_sub, map_smul, cechι_cechι]
    by_cases hia : i = a
    · subst hia
      have hib : i ≠ b := hab.ne
      rw [hx'i, map_zero, sub_zero, hx'T b hib _ (by
          intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto)]
      simp [σ, hab]
    · by_cases hib : i = b
      · subst hib
        rw [hx'i, map_zero, zero_sub, hx'T a hia _ (by
            intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto)]
        have hσ : σ a = -1 := ite_eq_right (by omega)
        rw [hσ, neg_one_smul, smul_neg, neg_neg,
          cechι_pairIndex_comm f z hia _ (by
            intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto)]
        exact sub_self _
      · rw [hx'T b hib _ (by
            intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto),
          hx'T a hia _ (by
            intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢; tauto),
          ← smul_sub, ← smul_sub]
        rw [cocycle_oriented_restrict f z hz hab hia hib _ hsub, smul_zero]
  choose m hm using hpair
  let N : ℕ := ∑ s, m s
  have hN : ∀ s, m s ≤ N := fun s ↦
    Finset.single_le_sum (f := m) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ s)
  refine ⟨N + E, f i ^ N • w, ?_⟩
  rw [map_smul]
  funext s
  have h := congrArg (f i ^ (N - m s) • ·) (hm s)
  simp only [smul_zero, smul_sub, smul_smul, ← pow_add] at h
  rw [show N - m s + m s = N by have := hN s; omega,
    show N - m s + (m s + E) = N + E by have := hN s; omega] at h
  simp only [Pi.smul_apply]
  exact (sub_eq_zero.mp h).symm

end FormalGlueing

end

end
