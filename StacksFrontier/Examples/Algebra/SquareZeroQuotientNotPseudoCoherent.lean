module

public import Mathlib
public import StacksFrontier.Homology.PseudoCoherent.Annihilator
public import StacksFrontier.RingTheory.Nilpotent.Ideal

/-!
# A limit of square-zero thickenings of `𝔽₂` with a quotient that is not pseudo-coherent

Write `𝔽₂ = ZMod 2`. For `n : ℕ` let `A_n = 𝔽₂ ⊕ 𝔽₂^n` be the trivial square-zero extension of
`𝔽₂` by `𝔽₂^n`, and let `A_{n+1} → A_n` restrict a vector to its first `n` coordinates. Every
transition map is surjective with kernel of square zero, every `A_n` is finite, hence Noetherian,
and `A_0 = 𝔽₂` is a field. The limit of the tower is `A = 𝔽₂ ⊕ 𝔽₂^ℕ`, the trivial square-zero
extension by the module of all sequences.

The element `f = (0, (1, 1, …))` of `A` has annihilator the ideal `0 ⊕ 𝔽₂^ℕ`: indeed
`(a, v) * f = (0, a • (1, 1, …))`. That ideal is an infinite-dimensional `𝔽₂`-vector space on which
`A` acts through `𝔽₂`, so it is not finitely generated. Hence the cyclic `A`-module `A ⧸ (f)` is
not pseudo-coherent, by
`StacksDraft.PseudoCoherence.fg_ker_toSpanSingleton_of_isModulePseudoCoherent_quotient`.

## Main definitions

* `towerRing n`, `towerMap h`, `towerTransition n`, `tower`: the tower `(A_n)`, whose map
  `A_m → A_n` is `towerMap h` (`tower_map_eq`).
* `limitRing`, `limitProj n`, `limitCone`: the ring `A` and its cone over `tower`.
* `onesElement`: the element `f`.

## Main results

* `surjective_tower_map_succ`, `locallyNilpotent_ker_tower_map_succ`: the transition maps are
  surjective with locally nilpotent kernel.
* `limitConeIsLimit`: `A` is the limit of the tower; `limitIso` is the resulting isomorphism.
* `towerRingZeroEquiv`, `isField_towerRing_zero`: `A_0` is the field `𝔽₂`.
* `not_fg_ker_toSpanSingleton_onesElement`: the annihilator of `f` is not finitely generated.
* `not_isModulePseudoCoherent_quotient`: `A ⧸ (f)` is not a pseudo-coherent `A`-module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TrivSqZeroExt

namespace Stacks.Examples.SquareZeroQuotientNotPseudoCoherent

/-! ### The tower -/

/-- The ring `A_n = 𝔽₂ ⊕ 𝔽₂^n`, the trivial square-zero extension of `ZMod 2` by `ZMod 2 ^ n`. -/
abbrev towerRing (n : ℕ) : Type := TrivSqZeroExt (ZMod 2) (Fin n → ZMod 2)

/-- The map `A_m → A_n` for `n ≤ m`, restricting a vector to its first `n` coordinates. -/
noncomputable def towerMap {m n : ℕ} (h : n ≤ m) : towerRing m →+* towerRing n :=
  (TrivSqZeroExt.map (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.castLE h))).toRingHom

@[simp]
theorem fst_towerMap {m n : ℕ} (h : n ≤ m) (x : towerRing m) : (towerMap h x).fst = x.fst :=
  fst_map _ x

@[simp]
theorem snd_towerMap {m n : ℕ} (h : n ≤ m) (x : towerRing m) (j : Fin n) :
    (towerMap h x).snd j = x.snd (Fin.castLE h j) := by
  simp [towerMap]

/-- The transition map `A_{n+1} → A_n`, restricting a vector to its first `n` coordinates. -/
noncomputable def towerTransition (n : ℕ) : towerRing (n + 1) →+* towerRing n :=
  towerMap (Nat.le_succ n)

/-- The tower `⋯ → A_2 → A_1 → A_0` as a functor `ℕᵒᵖ ⥤ CommRingCat`. -/
noncomputable def tower : ℕᵒᵖ ⥤ CommRingCat.{0} :=
  Functor.ofOpSequence (X := fun n => CommRingCat.of (towerRing n))
    fun n => CommRingCat.ofHom (towerTransition n)

theorem tower_map_succ (n : ℕ) :
    tower.map (homOfLE (Nat.le_succ n)).op = CommRingCat.ofHom (towerTransition n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

private theorem towerMap_refl (n : ℕ) : towerMap (le_refl n) = RingHom.id (towerRing n) := by
  ext x j
  · simp
  · simp

private theorem towerMap_comp_towerTransition {m n : ℕ} (h : n ≤ m) :
    (towerMap h).comp (towerTransition m) = towerMap (h.trans (Nat.le_succ m)) := by
  ext x j
  · simp [towerTransition]
  · simp [towerTransition]

/-- Every map of the tower is a restriction map `towerMap`. -/
theorem tower_map_eq {m n : ℕ} (h : n ≤ m) :
    tower.map (homOfLE h).op = CommRingCat.ofHom (towerMap h) := by
  induction m, h using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl n)).op = 𝟙 (Opposite.op n) from rfl]
    exact (tower.map_id _).trans (CommRingCat.ofHom_id.symm.trans
      (congrArg CommRingCat.ofHom (towerMap_refl n).symm))
  | succ m hnm ih =>
    rw [show (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op from rfl,
      Functor.map_comp, tower_map_succ, ih]
    exact (CommRingCat.ofHom_comp _ _).symm.trans
      (congrArg CommRingCat.ofHom (towerMap_comp_towerTransition hnm))

private theorem surjective_towerTransition (n : ℕ) : Function.Surjective (towerTransition n) := by
  intro y
  obtain ⟨v, hv⟩ := LinearMap.funLeft_surjective_of_injective (ZMod 2) (ZMod 2) _
    (Fin.castLE_injective (Nat.le_succ n)) y.snd
  refine ⟨inl y.fst + inr v, ?_⟩
  ext j
  · simp [towerTransition]
  · simp [towerTransition, ← hv]

/-- The transition maps of the tower are surjective. -/
theorem surjective_tower_map_succ :
    ∀ n, Function.Surjective (tower.map (homOfLE (Nat.le_succ n)).op).hom := by
  intro n
  rw [tower_map_succ]
  exact surjective_towerTransition n

private theorem isNilpotent_of_mem_ker_towerTransition (n : ℕ) (x : towerRing (n + 1))
    (hx : x ∈ RingHom.ker (towerTransition n)) : IsNilpotent x := by
  have h0 : x.fst = 0 := by
    simpa [towerTransition] using congrArg TrivSqZeroExt.fst (RingHom.mem_ker.mp hx)
  refine ⟨2, ?_⟩
  ext j
  · simp [pow_two, h0]
  · simp [pow_two, h0]

/-- The kernels of the transition maps of the tower are locally nilpotent; they are even of
square zero. -/
theorem locallyNilpotent_ker_tower_map_succ :
    ∀ n, (RingHom.ker (tower.map (homOfLE (Nat.le_succ n)).op).hom).LocallyNilpotent := by
  intro n
  rw [tower_map_succ]
  exact isNilpotent_of_mem_ker_towerTransition n

/-- Each ring `A_n` is Noetherian, being finite. -/
instance (n : ℕ) : IsNoetherianRing (towerRing n) :=
  haveI : Module.Finite (ZMod 2) (towerRing n) :=
    inferInstanceAs (Module.Finite (ZMod 2) (ZMod 2 × (Fin n → ZMod 2)))
  IsNoetherianRing.of_finite (ZMod 2) (towerRing n)

/-- The ring `A_0` is `ZMod 2`. -/
noncomputable def towerRingZeroEquiv : towerRing 0 ≃+* ZMod 2 :=
  RingEquiv.ofBijective (TrivSqZeroExt.fstHom (ZMod 2) (ZMod 2) (Fin 0 → ZMod 2)).toRingHom
    ⟨fun _ _ h => TrivSqZeroExt.ext h (Subsingleton.elim _ _), fun r => ⟨inl r, rfl⟩⟩

/-- The ring `A_0` is a field. -/
theorem isField_towerRing_zero : IsField (towerRing 0) :=
  MulEquiv.isField (Field.toIsField (ZMod 2)) towerRingZeroEquiv.toMulEquiv

/-! ### The limit -/

/-- The ring `A = 𝔽₂ ⊕ 𝔽₂^ℕ`, the trivial square-zero extension of `ZMod 2` by the module of all
sequences. -/
abbrev limitRing : Type := TrivSqZeroExt (ZMod 2) (ℕ → ZMod 2)

/-- The projection `A → A_n`, restricting a sequence to its first `n` terms. -/
noncomputable def limitProj (n : ℕ) : limitRing →+* towerRing n :=
  (TrivSqZeroExt.map (LinearMap.funLeft (ZMod 2) (ZMod 2) (Fin.val : Fin n → ℕ))).toRingHom

@[simp]
theorem fst_limitProj (n : ℕ) (x : limitRing) : (limitProj n x).fst = x.fst :=
  fst_map _ x

@[simp]
theorem snd_limitProj (n : ℕ) (x : limitRing) (j : Fin n) : (limitProj n x).snd j = x.snd j := by
  simp [limitProj]

private theorem towerTransition_comp_limitProj (n : ℕ) :
    (towerTransition n).comp (limitProj (n + 1)) = limitProj n := by
  ext x j
  · simp [towerTransition]
  · simp [towerTransition]

/-- The cone over `tower` with vertex `A` and legs the projections `limitProj n`. -/
noncomputable def limitCone : Cone tower where
  pt := CommRingCat.of limitRing
  π := NatTrans.ofOpSequence (fun n => CommRingCat.ofHom (limitProj n)) fun n => by
    rw [tower_map_succ]
    exact (Category.id_comp _).trans <|
      (congrArg CommRingCat.ofHom (towerTransition_comp_limitProj n).symm).trans
        (CommRingCat.ofHom_comp _ _)

theorem limitCone_π_app (n : ℕ) :
    limitCone.π.app (Opposite.op n) = CommRingCat.ofHom (limitProj n) :=
  rfl

/-- The leg of a cone over `tower` at `A_n`, as a ring map. -/
noncomputable def coneLeg (s : Cone tower) (n : ℕ) : s.pt →+* towerRing n :=
  (s.π.app (Opposite.op n)).hom

private theorem towerMap_comp_coneLeg (s : Cone tower) {m n : ℕ} (h : n ≤ m) :
    (towerMap h).comp (coneLeg s m) = coneLeg s n := by
  have hw := s.w (homOfLE h).op
  rw [tower_map_eq h] at hw
  exact congrArg CommRingCat.Hom.hom hw

private theorem fst_coneLeg (s : Cone tower) (x : s.pt) (n : ℕ) :
    (coneLeg s (n + 1) x).fst = (coneLeg s 0 x).fst := by
  rw [← RingHom.congr_fun (towerMap_comp_coneLeg s (Nat.zero_le (n + 1))) x]
  simp

private theorem snd_coneLeg (s : Cone tower) (x : s.pt) {n : ℕ} (j : Fin n) :
    (coneLeg s n x).snd j = (coneLeg s (j + 1) x).snd (Fin.last j) := by
  rw [← RingHom.congr_fun (towerMap_comp_coneLeg s (show (j : ℕ) + 1 ≤ n from j.isLt)) x]
  simp
  rfl

/-- The map from the vertex of a cone over `tower` to `A`. -/
noncomputable def coneLift (s : Cone tower) : s.pt →+* limitRing where
  toFun x := inl (coneLeg s 0 x).fst + inr fun i => (coneLeg s (i + 1) x).snd (Fin.last i)
  map_one' := by
    ext i
    · simp
    · simp
  map_mul' x y := by
    ext i
    · simp
    · simp [fst_coneLeg]
  map_zero' := by
    ext i
    · simp
    · simp
  map_add' x y := by
    ext i
    · simp
    · simp

/-- The lift `coneLift s` is compatible with the projections. -/
theorem limitProj_comp_coneLift (s : Cone tower) (n : ℕ) :
    (limitProj n).comp (coneLift s) = coneLeg s n := by
  ext x j
  · cases n with
    | zero => simp [coneLift]
    | succ n => simp [coneLift, fst_coneLeg]
  · simp [coneLift, snd_coneLeg s x j]

/-- A ring map to `A` compatible with the projections is `coneLift s`. -/
theorem eq_coneLift (s : Cone tower) (m : s.pt →+* limitRing)
    (h : ∀ n, (limitProj n).comp m = coneLeg s n) : m = coneLift s := by
  ext x i
  · simpa [coneLift] using congrArg TrivSqZeroExt.fst (RingHom.congr_fun (h 0) x)
  · have := congrArg (fun y : towerRing (i + 1) => y.snd (Fin.last i))
      (RingHom.congr_fun (h (i + 1)) x)
    simpa [coneLift] using this

/-- `A` is the limit of the tower. -/
noncomputable def limitConeIsLimit : IsLimit limitCone where
  lift s := CommRingCat.ofHom (coneLift s)
  fac s j := congrArg CommRingCat.ofHom (limitProj_comp_coneLift s j.unop)
  uniq s m hm := CommRingCat.hom_ext
    (eq_coneLift s m.hom fun n => congrArg CommRingCat.Hom.hom (hm (Opposite.op n)))

/-- The limit of the tower is `A`. -/
noncomputable def limitIso : limit tower ≅ CommRingCat.of limitRing :=
  (limit.isLimit tower).conePointUniqueUpToIso limitConeIsLimit

@[simp]
theorem limitIso_hom_comp_ofHom_limitProj (n : ℕ) :
    limitIso.hom ≫ CommRingCat.ofHom (limitProj n) = limit.π tower (Opposite.op n) :=
  (limit.isLimit tower).conePointUniqueUpToIso_hom_comp limitConeIsLimit (Opposite.op n)

/-! ### The quotient that is not pseudo-coherent -/

/-- The element `(0, (1, 1, …))` of `A`. -/
def onesElement : limitRing := inr fun _ => 1

theorem limitProj_zero_onesElement : limitProj 0 onesElement = 0 := by
  ext j
  · simp [onesElement]
  · exact j.elim0

/-- The annihilator of `onesElement` is the ideal of elements with vanishing `ZMod 2`
component. -/
theorem mem_ker_toSpanSingleton_onesElement_iff (a : limitRing) :
    a ∈ LinearMap.ker (LinearMap.toSpanSingleton limitRing limitRing onesElement) ↔
      a.fst = 0 := by
  rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  constructor
  · intro h
    simpa [onesElement] using congrArg (fun x : limitRing => x.snd 0) h
  · intro h
    ext i
    · simp [onesElement]
    · simp [onesElement, h]

/-- The annihilator of `onesElement` is not a finitely generated ideal: it is an
infinite-dimensional `ZMod 2`-vector space, on which `A` acts through `ZMod 2`. -/
theorem not_fg_ker_toSpanSingleton_onesElement :
    ¬ (LinearMap.ker (LinearMap.toSpanSingleton limitRing limitRing onesElement)).FG := by
  rintro ⟨s, hs⟩
  let V : Submodule (ZMod 2) (ℕ → ZMod 2) :=
    Submodule.span (ZMod 2) (TrivSqZeroExt.snd '' (s : Set limitRing))
  let N : Submodule limitRing limitRing :=
    { carrier := {x | x.fst = 0 ∧ x.snd ∈ V}
      add_mem' := fun hx hy => ⟨by simp [hx.1, hy.1], V.add_mem hx.2 hy.2⟩
      zero_mem' := ⟨rfl, V.zero_mem⟩
      smul_mem' := fun a x hx => ⟨by simp [hx.1], by
        simpa [hx.1] using V.smul_mem a.fst hx.2⟩ }
  have hle : LinearMap.ker (LinearMap.toSpanSingleton limitRing limitRing onesElement) ≤ N := by
    rw [← hs, Submodule.span_le]
    intro x hx
    refine ⟨(mem_ker_toSpanSingleton_onesElement_iff x).mp ?_, Submodule.subset_span ⟨x, hx, rfl⟩⟩
    rw [← hs]
    exact Submodule.subset_span hx
  have hV (v : ℕ → ZMod 2) : v ∈ V :=
    (hle ((mem_ker_toSpanSingleton_onesElement_iff (inr v)).mpr (fst_inr _ v))).2
  have : Module.Finite (ZMod 2) V :=
    Module.Finite.span_of_finite (ZMod 2) ((s.finite_toSet).image _)
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Finite (ℕ → ZMod 2) :=
    Finite.of_surjective (Subtype.val : V → ℕ → ZMod 2) fun v => ⟨⟨v, hV v⟩, rfl⟩
  exact not_finite (ℕ → ZMod 2)

/-- The cyclic `A`-module `A ⧸ (onesElement)` is not pseudo-coherent. -/
theorem not_isModulePseudoCoherent_quotient [HasDerivedCategory (ModuleCat.{0} limitRing)] :
    ¬ StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := limitRing)
      (limitRing ⧸ Ideal.span {onesElement}) := fun h =>
  not_fg_ker_toSpanSingleton_onesElement
    (StacksDraft.PseudoCoherence.fg_ker_toSpanSingleton_of_isModulePseudoCoherent_quotient
      onesElement h)

end Stacks.Examples.SquareZeroQuotientNotPseudoCoherent

end
