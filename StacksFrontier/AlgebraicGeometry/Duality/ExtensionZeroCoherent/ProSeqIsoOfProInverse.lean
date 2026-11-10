module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving

/-!
# A map of inverse sequences with pro-inverses is an isomorphism of pro-objects

Let `φ : A ⟶ B` be a map of inverse sequences `ℕᵒᵖ ⥤ 𝒟`. Say that `φ` *has pro-inverses* when for
every `n` there are `m ≥ n` and `s : B_m ⟶ A_n` with `φ_m ≫ s` and `s ≫ φ_n` the transition maps.
This is how pro-isomorphisms are stated in [Stacks, Tag 0G3C] and [Stacks, Tag 0G3N]. This file
shows that such a `φ` gives an isomorphism `ProSeq.of A ≅ ProSeq.of B` of pro-objects, by
interleaving the maps `φ` and `s` along a strictly increasing sequence of indices
(`InverseSequence.ProIso.Interleaving`).

## Main results

* `CategoryTheory.ProSeq.isoOfProInverse`: the isomorphism of pro-objects.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite InverseSequence

universe v u

namespace CategoryTheory.ProSeq

variable {𝒟 : Type u} [Category.{v} 𝒟] {A B : ℕᵒᵖ ⥤ 𝒟} (φ : A ⟶ B)
  (h : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (s : B.obj (op m) ⟶ A.obj (op n)),
    φ.app (op m) ≫ s = A.map (homOfLE h).op ∧ s ≫ φ.app (op n) = B.map (homOfLE h).op)

/-- A strictly later index at which a pro-inverse of `φ` is defined. -/
def proInverseNext (n : ℕ) : ℕ := (h n).choose + 1

/-- `proInverseNext φ h n` is strictly later than `n`. -/
lemma lt_proInverseNext (n : ℕ) : n < proInverseNext φ h n :=
  Nat.lt_succ_of_le (h n).choose_spec.choose

/-- The pro-inverse of `φ` at `n`, defined at the strictly later index `proInverseNext φ h n`. -/
def proInverseAt (n : ℕ) : B.obj (op (proInverseNext φ h n)) ⟶ A.obj (op n) :=
  tr B (Nat.le_succ (h n).choose) ≫ (h n).choose_spec.choose_spec.choose

/-- `φ` followed by its pro-inverse is a transition map of the source. -/
lemma app_proInverseAt (n : ℕ) :
    φ.app (op (proInverseNext φ h n)) ≫ proInverseAt φ h n =
      tr A (lt_proInverseNext φ h n).le := by
  have hs₁ := (h n).choose_spec.choose_spec.choose_spec.1
  have hnat : tr A (Nat.le_succ (h n).choose) ≫ φ.app (op (h n).choose) =
      φ.app (op ((h n).choose + 1)) ≫ tr B (Nat.le_succ (h n).choose) :=
    φ.naturality _
  change φ.app (op ((h n).choose + 1)) ≫ tr B (Nat.le_succ (h n).choose) ≫
      (h n).choose_spec.choose_spec.choose =
        tr A ((h n).choose_spec.choose.trans (Nat.le_succ (h n).choose))
  rw [← Category.assoc, ← hnat, Category.assoc]
  exact (congrArg (tr A (Nat.le_succ (h n).choose) ≫ ·) hs₁).trans (ProIso.tr_trans A _ _)

/-- The pro-inverse followed by `φ` is a transition map of the target. -/
lemma proInverseAt_app (n : ℕ) :
    proInverseAt φ h n ≫ φ.app (op n) = tr B (lt_proInverseNext φ h n).le := by
  have hs₂ := (h n).choose_spec.choose_spec.choose_spec.2
  change (tr B (Nat.le_succ (h n).choose) ≫ (h n).choose_spec.choose_spec.choose) ≫
      φ.app (op n) = tr B ((h n).choose_spec.choose.trans (Nat.le_succ (h n).choose))
  rw [Category.assoc]
  exact (congrArg (tr B (Nat.le_succ (h n).choose) ≫ ·) hs₂).trans (ProIso.tr_trans B _ _)

/-- The strictly increasing sequence of indices along which `φ` and its pro-inverses
interleave. -/
def proInverseIdx : ℕ → ℕ
  | 0 => 0
  | k + 1 => proInverseNext φ h (proInverseIdx k)

/-- The interleaving indices are strictly increasing. -/
lemma proInverseIdx_strictMono : StrictMono (proInverseIdx φ h) :=
  strictMono_nat_of_lt_succ fun k => lt_proInverseNext φ h (proInverseIdx φ h k)

/-- The interleaving of `φ` with its pro-inverses. -/
def interleavingOfProInverse : ProIso.Interleaving A B where
  idx := proInverseIdx φ h
  idx_strictMono := proInverseIdx_strictMono φ h
  fwd i := φ.app (op (proInverseIdx φ h (2 * i + 2))) ≫
    tr B ((proInverseIdx_strictMono φ h).monotone (show 2 * i + 1 ≤ 2 * i + 2 by omega))
  bwd i := proInverseAt φ h (proInverseIdx φ h (2 * i))
  fwd_bwd i := by
    have hle : proInverseIdx φ h (2 * i + 1) ≤ proInverseIdx φ h (2 * i + 2) :=
      (proInverseIdx_strictMono φ h).monotone (show 2 * i + 1 ≤ 2 * i + 2 by omega)
    calc (φ.app (op (proInverseIdx φ h (2 * i + 2))) ≫ tr B hle) ≫
          proInverseAt φ h (proInverseIdx φ h (2 * i))
        = tr A hle ≫ (φ.app (op (proInverseIdx φ h (2 * i + 1))) ≫
            proInverseAt φ h (proInverseIdx φ h (2 * i))) :=
          (congrArg (· ≫ proInverseAt φ h (proInverseIdx φ h (2 * i)))
            (φ.naturality (homOfLE hle).op).symm).trans
            (Category.assoc _ _ _)
      _ = tr A hle ≫ tr A (lt_proInverseNext φ h (proInverseIdx φ h (2 * i))).le :=
          congrArg (tr A hle ≫ ·) (app_proInverseAt φ h (proInverseIdx φ h (2 * i)))
      _ = _ := ProIso.tr_trans A _ _
  bwd_fwd i := by
    have hle : proInverseIdx φ h (2 * i + 1) ≤ proInverseIdx φ h (2 * i + 2) :=
      (proInverseIdx_strictMono φ h).monotone (show 2 * i + 1 ≤ 2 * i + 2 by omega)
    calc proInverseAt φ h (proInverseIdx φ h (2 * (i + 1))) ≫
          φ.app (op (proInverseIdx φ h (2 * i + 2))) ≫ tr B hle
        = (proInverseAt φ h (proInverseIdx φ h (2 * i + 2)) ≫
            φ.app (op (proInverseIdx φ h (2 * i + 2)))) ≫ tr B hle :=
          (Category.assoc _ _ _).symm
      _ = tr B (lt_proInverseNext φ h (proInverseIdx φ h (2 * i + 2))).le ≫ tr B hle :=
          congrArg (· ≫ tr B hle) (proInverseAt_app φ h (proInverseIdx φ h (2 * i + 2)))
      _ = _ := ProIso.tr_trans B _ _

/-- **A map of inverse sequences with pro-inverses is an isomorphism of pro-objects.** -/
def isoOfProInverse : ProSeq.of A ≅ ProSeq.of B :=
  isoOfProIso (interleavingOfProInverse φ h).proIso

/-- **Pro-inverses transport along isomorphisms of inverse sequences.** If `α' : A' ⟶ B'` has
pro-inverses and `α : A ⟶ B` agrees with it through isomorphisms `A ≅ A'` and `B ≅ B'`, then `α`
has pro-inverses. -/
lemma proInverse_of_natIso {A' B' : ℕᵒᵖ ⥤ 𝒟} (α' : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B')
    (w : φ ≫ eB.hom = eA.hom ≫ α')
    (h' : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (s : B'.obj (op m) ⟶ A'.obj (op n)),
      α'.app (op m) ≫ s = A'.map (homOfLE h).op ∧ s ≫ α'.app (op n) = B'.map (homOfLE h).op) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (s : B.obj (op m) ⟶ A.obj (op n)),
      φ.app (op m) ≫ s = A.map (homOfLE h).op ∧ s ≫ φ.app (op n) = B.map (homOfLE h).op := by
  intro n
  obtain ⟨m, hnm, s, hs₁, hs₂⟩ := h' n
  have wm := congrArg (fun t => NatTrans.app t (op m)) w
  have wn := congrArg (fun t => NatTrans.app t (op n)) w
  simp only [NatTrans.comp_app] at wm wn
  refine ⟨m, hnm, eB.hom.app (op m) ≫ s ≫ eA.inv.app (op n), ?_, ?_⟩
  · rw [← Category.assoc, wm, Category.assoc, ← Category.assoc (α'.app _), hs₁,
      ← eA.hom.naturality_assoc, Iso.hom_inv_id_app, Category.comp_id]
  · have hα : φ.app (op n) = eA.hom.app (op n) ≫ α'.app (op n) ≫ eB.inv.app (op n) := by
      rw [← Category.assoc, ← wn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [hα, Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc, ← Category.assoc s,
      hs₂]
    have := eB.inv.naturality (homOfLE hnm).op
    rw [this, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end CategoryTheory.ProSeq

end
