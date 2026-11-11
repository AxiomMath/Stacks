module

public import StacksCore.FieldTheory.SeparableDegree
import StacksCore.Tactic.StacksAttribute

/-!
# Embeddings of a finitely generated algebraic extension, by successive roots

In Situation 09H6, `E = F(α₀, …, α_{n-1})` is algebraic over `F`, `Kᵢ = F(α₀, …, α_{i-1})` and
`Pᵢ` is the minimal polynomial of `αᵢ` over `Kᵢ`. Given an `F`-embedding `φᵢ : Kᵢ → L` and a root
`b` of `Pᵢ` twisted by `φᵢ`, there is a unique extension `φᵢ₊₁ : Kᵢ₊₁ → L` sending `αᵢ` to `b`
(`IntermediateField.liftAdjoinImageIioSucc`), since `Kᵢ₊₁ = Kᵢ[x]/(Pᵢ)`. Iterating this builds the
embeddings from the roots alone (`IntermediateField.rootTowerAlgHom`), and Stacks 09H7 says that
`φ ↦ (φ(α₀), …, φ(α_{n-1}))` is a bijection onto the tuples of successive roots
(`IntermediateField.bijOn_algHom_apply_rootTowerAlgHom`).
-/

@[expose] public section

open Polynomial IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

namespace IntermediateField

variable {L : Type*} [Field L] [Algebra F L]

variable (F) in
/-- The identification of `F(α₀, …, αᵢ)` with `F(α₀, …, α_{i-1})(αᵢ)`, as a ring map. -/
def adjoinImageIioSuccToAdjoinSimple (α : ℕ → E) (i : ℕ) :
    adjoin F (α '' Set.Iio (i + 1)) →+* adjoin (adjoin F (α '' Set.Iio i)) {α i} where
  toFun y := ⟨y, (adjoin_image_Iio_succ α i).le y.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (F) in
/-- `IntermediateField.adjoinImageIioSuccToAdjoinSimple` is the identity on elements. -/
theorem adjoinImageIioSuccToAdjoinSimple_apply (α : ℕ → E) (i : ℕ)
    (y : adjoin F (α '' Set.Iio (i + 1))) :
    adjoinImageIioSuccToAdjoinSimple F α i y = ⟨y, (adjoin_image_Iio_succ α i).le y.2⟩ :=
  rfl

variable (F) in
@[simp]
theorem coe_adjoinImageIioSuccToAdjoinSimple (α : ℕ → E) (i : ℕ)
    (y : adjoin F (α '' Set.Iio (i + 1))) :
    (adjoinImageIioSuccToAdjoinSimple F α i y : E) = y := by
  rw [adjoinImageIioSuccToAdjoinSimple_apply, Subtype.coe_mk]

/-- The ring map underlying `IntermediateField.liftAdjoinImageIioSucc`. -/
noncomputable def liftAdjoinImageIioSuccRingHom (α : ℕ → E) (i : ℕ)
    (hx : IsIntegral (adjoin F (α '' Set.Iio i)) (α i))
    (ψ : adjoin F (α '' Set.Iio i) →ₐ[F] L) (b : L)
    (hb : ((minpoly (adjoin F (α '' Set.Iio i)) (α i)).map (ψ : _ →+* L)).IsRoot b) :
    adjoin F (α '' Set.Iio (i + 1)) →+* L :=
  ((AdjoinRoot.lift (ψ : _ →+* L) b ((eval_map _ _).symm.trans hb.eq_zero)).comp
      (adjoinRootEquivAdjoin _ hx).symm.toRingHom).comp
    (adjoinImageIioSuccToAdjoinSimple F α i)

theorem liftAdjoinImageIioSuccRingHom_apply (α : ℕ → E) (i : ℕ)
    (hx : IsIntegral (adjoin F (α '' Set.Iio i)) (α i))
    (ψ : adjoin F (α '' Set.Iio i) →ₐ[F] L) (b : L)
    (hb : ((minpoly (adjoin F (α '' Set.Iio i)) (α i)).map (ψ : _ →+* L)).IsRoot b)
    (y : adjoin F (α '' Set.Iio (i + 1))) :
    liftAdjoinImageIioSuccRingHom α i hx ψ b hb y =
      AdjoinRoot.lift (ψ : _ →+* L) b ((eval_map _ _).symm.trans hb.eq_zero)
        ((adjoinRootEquivAdjoin _ hx).symm (adjoinImageIioSuccToAdjoinSimple F α i y)) :=
  rfl

/-- Given an `F`-embedding `ψ : F(α₀, …, α_{i-1}) → L` and a root `b` of the minimal polynomial
of `αᵢ` over `F(α₀, …, α_{i-1})` twisted by `ψ`, this is the `F`-embedding
`F(α₀, …, αᵢ) → L` extending `ψ` and sending `αᵢ` to `b`. It is built from
`F(α₀, …, αᵢ) = F(α₀, …, α_{i-1})[x]/(Pᵢ)`. -/
noncomputable def liftAdjoinImageIioSucc (α : ℕ → E) (i : ℕ)
    (hx : IsIntegral (adjoin F (α '' Set.Iio i)) (α i))
    (ψ : adjoin F (α '' Set.Iio i) →ₐ[F] L) (b : L)
    (hb : ((minpoly (adjoin F (α '' Set.Iio i)) (α i)).map (ψ : _ →+* L)).IsRoot b) :
    adjoin F (α '' Set.Iio (i + 1)) →ₐ[F] L where
  toRingHom := liftAdjoinImageIioSuccRingHom α i hx ψ b hb
  commutes' r := by
    have h : adjoinImageIioSuccToAdjoinSimple F α i (algebraMap F _ r) =
        algebraMap (adjoin F (α '' Set.Iio i)) _ (algebraMap F _ r) :=
      Subtype.ext <| by simp
    change liftAdjoinImageIioSuccRingHom α i hx ψ b hb _ = _
    rw [liftAdjoinImageIioSuccRingHom_apply, h, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    exact ψ.commutes r

variable (α : ℕ → E) (i : ℕ) (hx : IsIntegral (adjoin F (α '' Set.Iio i)) (α i))
  (ψ : adjoin F (α '' Set.Iio i) →ₐ[F] L) (b : L)
  (hb : ((minpoly (adjoin F (α '' Set.Iio i)) (α i)).map (ψ : _ →+* L)).IsRoot b)

variable (F) in
/-- `F(α₀, …, α_{i-1}) ≤ F(α₀, …, αᵢ)`. -/
theorem adjoin_image_Iio_le_succ :
    adjoin F (α '' Set.Iio i) ≤ adjoin F (α '' Set.Iio (i + 1)) :=
  adjoin.mono _ _ _ <| Set.image_mono <| Set.Iio_subset_Iio (Nat.le_add_right i 1)

variable (F) in
/-- `αᵢ ∈ F(α₀, …, αᵢ)`. -/
theorem mem_adjoin_image_Iio_succ : α i ∈ adjoin F (α '' Set.Iio (i + 1)) :=
  subset_adjoin _ _ ⟨i, Nat.lt_add_one i, rfl⟩

/-- `liftAdjoinImageIioSucc` extends `ψ`. -/
theorem liftAdjoinImageIioSucc_comp_inclusion :
    (liftAdjoinImageIioSucc α i hx ψ b hb).comp
      (inclusion (adjoin_image_Iio_le_succ F α i)) = ψ := by
  ext k
  rw [AlgHom.comp_apply]
  have h : adjoinImageIioSuccToAdjoinSimple F α i (inclusion (adjoin_image_Iio_le_succ F α i) k) =
      algebraMap (adjoin F (α '' Set.Iio i)) _ k := Subtype.ext <| by simp
  change liftAdjoinImageIioSuccRingHom α i hx ψ b hb (inclusion _ k) = _
  rw [liftAdjoinImageIioSuccRingHom_apply, h, AlgEquiv.commutes, AdjoinRoot.algebraMap_eq,
    AdjoinRoot.lift_of]
  rfl

/-- `liftAdjoinImageIioSucc` sends `αᵢ` to `b`. -/
theorem liftAdjoinImageIioSucc_apply_self :
    liftAdjoinImageIioSucc α i hx ψ b hb ⟨α i, mem_adjoin_image_Iio_succ F α i⟩ = b := by
  have h : adjoinImageIioSuccToAdjoinSimple F α i ⟨α i, mem_adjoin_image_Iio_succ F α i⟩ =
      AdjoinSimple.gen _ (α i) := Subtype.ext <| by simp
  change liftAdjoinImageIioSuccRingHom α i hx ψ b hb _ = _
  rw [liftAdjoinImageIioSuccRingHom_apply, h, adjoinRootEquivAdjoin_symm_apply_gen,
    AdjoinRoot.lift_root]

/-- `liftAdjoinImageIioSucc` is the only `F`-embedding extending `ψ` and sending `αᵢ` to `b`. -/
theorem eq_liftAdjoinImageIioSucc (φ : adjoin F (α '' Set.Iio (i + 1)) →ₐ[F] L)
    (h₁ : φ.comp (inclusion (adjoin_image_Iio_le_succ F α i)) = ψ)
    (h₂ : φ ⟨α i, mem_adjoin_image_Iio_succ F α i⟩ = b) :
    φ = liftAdjoinImageIioSucc α i hx ψ b hb := by
  refine algHom_ext_of_eq_adjoin F rfl fun x ⟨j, hj, hjx⟩ ↦ ?_
  subst hjx
  rcases (Nat.lt_succ_iff_lt_or_eq.1 hj) with hj | rfl
  · have hk : α j ∈ adjoin F (α '' Set.Iio i) := subset_adjoin _ _ ⟨j, hj, rfl⟩
    have e₁ := congr($h₁ ⟨α j, hk⟩)
    have e₂ := congr($(liftAdjoinImageIioSucc_comp_inclusion α i hx ψ b hb) ⟨α j, hk⟩)
    exact e₁.trans e₂.symm
  · exact h₂.trans (liftAdjoinImageIioSucc_apply_self α _ hx ψ b hb).symm

end IntermediateField

variable (F) in
/-- The unique `F`-embedding of `F(α₀, …, α_{i-1})` into `L` sending `αⱼ` to `βⱼ` for `j < i`,
built step by step in Situation 09H6 from the root conditions alone: it is `none` as soon as
some `βⱼ` (`j < i`) is not a root of `Pⱼ` twisted by the embedding built at step `j`, and
otherwise the embedding at step `j + 1` is `IntermediateField.liftAdjoinImageIioSucc` of the one
at step `j`. -/
noncomputable def IntermediateField.rootTowerAlgHom [Algebra.IsAlgebraic F E] {L : Type*}
    [Field L] [Algebra F L] (α : ℕ → E) {n : ℕ} (β : Fin n → L) :
    (i : ℕ) → i ≤ n → Option (adjoin F (α '' Set.Iio i) →ₐ[F] L)
  | 0, _ => some ((Algebra.ofId F L).comp ((botEquiv F E).toAlgHom.comp
      (equivOfEq (by simp)).toAlgHom))
  | i + 1, hi => (rootTowerAlgHom α β i (Nat.le_of_succ_le hi)).bind fun ψ ↦
      haveI := Classical.propDecidable
      if hb : ((minpoly (adjoin F (α '' Set.Iio i)) (α i)).map (ψ : _ →+* L)).IsRoot
          (β ⟨i, hi⟩) then
        some (liftAdjoinImageIioSucc α i
          (Algebra.IsAlgebraic.isAlgebraic (R := F) (α i)).isIntegral.tower_top ψ (β ⟨i, hi⟩) hb)
      else none

/-- At step `0` the embedding is the structure map. -/
theorem IntermediateField.rootTowerAlgHom_zero [Algebra.IsAlgebraic F E] {L : Type*}
    [Field L] [Algebra F L] (α : ℕ → E) {n : ℕ} (β : Fin n → L) (h : 0 ≤ n) :
    rootTowerAlgHom F α β 0 h = some ((Algebra.ofId F L).comp ((botEquiv F E).toAlgHom.comp
      (equivOfEq (by simp)).toAlgHom)) := by
  rw [rootTowerAlgHom]

/-- If the embedding at step `i` exists and `βᵢ` is a root of the twisted `Pᵢ`, the embedding at
step `i + 1` is its extension sending `αᵢ` to `βᵢ`. -/
theorem IntermediateField.rootTowerAlgHom_succ_of_eq_some [Algebra.IsAlgebraic F E] {L : Type*}
    [Field L] [Algebra F L] (α : ℕ → E) {n : ℕ} (β : Fin n → L) (i : ℕ) (hi : i < n)
    {ψ : adjoin F (α '' Set.Iio i) →ₐ[F] L} (hψ : rootTowerAlgHom F α β i hi.le = some ψ)
    (hb : ((minpoly (adjoin F (α '' Set.Iio i)) (α i)).map (ψ : _ →+* L)).IsRoot (β ⟨i, hi⟩)) :
    rootTowerAlgHom F α β (i + 1) hi = some (liftAdjoinImageIioSucc α i
      (Algebra.IsAlgebraic.isAlgebraic (R := F) (α i)).isIntegral.tower_top ψ (β ⟨i, hi⟩) hb) := by
  rw [rootTowerAlgHom, hψ, Option.bind_some]
  split_ifs with h
  · rfl
  · exact absurd hb h

/-- **Stacks 09H7**.
Let `E = F(α₀, …, α_{n-1})` be an algebraic extension of `F` and `L` a field extension of `F`.
Write `Kᵢ = F(α₀, …, α_{i-1})` and `Pᵢ` for the minimal polynomial of `αᵢ` over `Kᵢ`. Then
`φ ↦ (φ(α₀), …, φ(α_{n-1}))` is a bijection from the `F`-embeddings `E → L` onto the tuples
`(β₀, …, β_{n-1})` such that, for each `i < n`, `βᵢ` is a root of `Pᵢ` twisted by the embedding
`φᵢ : Kᵢ → L` determined by `β₀, …, β_{i-1}`; here `φ₀` is the structure map and `φᵢ₊₁` is the
unique extension of `φᵢ` sending `αᵢ` to `βᵢ`, which exists because `Kᵢ₊₁ = Kᵢ[x]/(Pᵢ)`
(`IntermediateField.rootTowerAlgHom`). -/
@[stacks 09H7 "for an arbitrary field extension `L` of `F` in place of an algebraic closure"]
theorem IntermediateField.bijOn_algHom_apply_rootTowerAlgHom [Algebra.IsAlgebraic F E]
    {L : Type*} [Field L] [Algebra F L]
    (α : ℕ → E) (n : ℕ) (hgen : adjoin F (α '' Set.Iio n) = ⊤) :
    Set.BijOn (fun (φ : E →ₐ[F] L) (i : Fin n) ↦ φ (α i)) Set.univ
      {β | ∀ (i : ℕ) (hi : i < n), ∃ ψ, rootTowerAlgHom F α β i hi.le = some ψ ∧
        ((minpoly (adjoin F (α '' Set.Iio i)) (α i)).map (ψ : _ →+* L)).IsRoot (β ⟨i, hi⟩)} := by
  have hroot (φ : E →ₐ[F] L) (i : ℕ) :
      ((minpoly (adjoin F (α '' Set.Iio i)) (α i)).map
        ((φ.comp (val _) : adjoin F (α '' Set.Iio i) →ₐ[F] L) : _ →+* L)).IsRoot (φ (α i)) := by
    have := hom_eval₂ (minpoly (adjoin F (α '' Set.Iio i)) (α i)) (algebraMap _ E) (φ : E →+* L)
      (α i)
    rw [← aeval_def, minpoly.aeval, map_zero] at this
    rw [IsRoot, eval_map]
    exact this.symm
  have hmaps (φ : E →ₐ[F] L) (i : ℕ) (hi : i ≤ n) :
      rootTowerAlgHom F α (fun j : Fin n ↦ φ (α j)) i hi = some (φ.comp (val _)) := by
    induction i with
    | zero =>
      rw [rootTowerAlgHom_zero]
      congr 1
      exact algHom_ext_of_eq_adjoin F rfl fun x ⟨j, hj, _⟩ ↦ absurd hj (Nat.not_lt_zero j)
    | succ i ih =>
      rw [rootTowerAlgHom_succ_of_eq_some α _ i hi (ih (Nat.le_of_succ_le hi)) (hroot φ i)]
      congr 1
      exact (eq_liftAdjoinImageIioSucc α i _ (φ.comp (val _)) (φ (α i)) (hroot φ i)
        (φ.comp (val _)) (AlgHom.ext fun _ ↦ rfl) rfl).symm
  refine ⟨fun φ _ i hi ↦ ⟨_, hmaps φ i hi.le, hroot φ i⟩, fun φ _ φ' _ h ↦ ?_, fun β hβ ↦ ?_⟩
  · refine AlgHom.ext fun x ↦ ?_
    have hx : x ∈ adjoin F (α '' Set.Iio n) := hgen ▸ mem_top
    induction hx using adjoin_induction with
    | mem x hx => obtain ⟨i, hi, rfl⟩ := hx; exact congr_fun h ⟨i, hi⟩
    | algebraMap => simp
    | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
    | mul _ _ _ _ h₁ h₂ => simp [h₁, h₂]
    | inv _ _ h => simp [h]
  · have key (i : ℕ) (hi : i ≤ n) : ∃ ψ, rootTowerAlgHom F α β i hi = some ψ ∧
        ∀ (j : ℕ) (hj : j < i), ψ ⟨α j, subset_adjoin _ _ ⟨j, hj, rfl⟩⟩ =
          β ⟨j, hj.trans_le hi⟩ := by
      induction i with
      | zero =>
        exact ⟨_, rootTowerAlgHom_zero (F := F) α β hi, fun j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
      | succ i ih =>
        obtain ⟨ψ, hψ, hψβ⟩ := ih (Nat.le_of_succ_le hi)
        obtain ⟨ψ', hψ', hb⟩ := hβ i hi
        obtain rfl : ψ' = ψ := Option.some_injective _ (hψ'.symm.trans hψ)
        refine ⟨_, rootTowerAlgHom_succ_of_eq_some α β i hi hψ' hb, fun j hj ↦ ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact (congr($(liftAdjoinImageIioSucc_comp_inclusion α i _ ψ' _ hb)
            ⟨α j, subset_adjoin _ _ ⟨j, hj, rfl⟩⟩)).trans (hψβ j hj)
        · exact liftAdjoinImageIioSucc_apply_self α j _ ψ' _ hb
    obtain ⟨ψ, -, hψβ⟩ := key n le_rfl
    refine ⟨ψ.comp ((equivOfEq hgen).trans topEquiv).symm.toAlgHom, trivial, ?_⟩
    funext ⟨i, hi⟩
    exact hψβ i hi
