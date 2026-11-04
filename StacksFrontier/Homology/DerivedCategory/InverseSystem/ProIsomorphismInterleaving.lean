module

public import Mathlib
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Pro-isomorphisms of inverse systems built from interleaved families of maps

Two inverse systems `X` and `Y` indexed by `ℕᵒᵖ` are isomorphic as pro-objects as soon as they
admit *interleaved* maps: a strictly increasing sequence of indices `n₀ < n₁ < n₂ < ⋯` together
with maps `X_{n_{2i+2}} ⟶ Y_{n_{2i+1}}` and `Y_{n_{2i+1}} ⟶ X_{n_{2i}}` whose two composites are
the transition maps of `X` and of `Y`. No naturality is asked of the interleaved maps; it is a
consequence of the two composition conditions, because a forward map at one stage followed by a
transition map factors through the backward map of the intervening stage.

This is the shape in which pro-isomorphisms arise in practice, and it is what feeds the
comparison of derived limits of pro-isomorphic systems.

## Main definitions

* `ProIso.Interleaving`: interleaved families of maps between two inverse systems indexed by
  `ℕᵒᵖ`.

## Main results

* `ProIso.Interleaving.proIso`: interleaved families of maps give a pro-isomorphism. The
  reindexings are `m ↦ n_{2m+2}` and `m ↦ n_{2m+1}`.
* `ProIso.whiskerRight`: a pro-isomorphism is carried to a pro-isomorphism by any functor.
* `ProIso.ofNatIso`: an isomorphism of inverse systems is a pro-isomorphism.
* `ProIso.Interleaving.nonempty_iso_of_isDerivedLimit`: derived limits of interleaved inverse
  systems in a pretriangulated category are non-canonically isomorphic. This is Tag 0H9L read off
  from interleaved maps.

## Implementation notes

The reindexings of `ProIso.Interleaving.proIso` are `α m = n_{2m+2}` and `β m = n_{2m+1}`, which
makes both the refinement conditions `m ≤ α m`, `m ≤ β m` and the two "inverse up to refinement"
identities immediate: at the index `β m = n_{2m+1}` the forward map of the pro-isomorphism is the
interleaved map `X_{n_{2m+2}} ⟶ Y_{n_{2m+1}}` itself, pushed forward from the stage
`n_{2 n_{2m+1} + 2}` that the formula prescribes. Choosing instead the least admissible stage for
each index would force the indices of the interleaved maps to be rewritten inside their own
types.

The transition maps of an inverse system depend on an inequality only through the proposition it
proves, so all the identities below hold for any proofs of the inequalities involved; the
statements name the canonical ones.

## References

* [Stacks Project, Tag 0H9L](https://stacks.math.columbia.edu/tag/0H9L)
-/

section

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u v' u'

variable {D : Type u} [Category.{v} D]

namespace InverseSequence.ProIso

/-- A strictly increasing map `ℕ → ℕ` is bounded below by the identity. -/
theorem le_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) : n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ k ih => exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hf (Nat.lt_succ_self k)))

/-- A pro-isomorphism of inverse systems indexed by `ℕᵒᵖ` is carried to one by any functor:
compose all of its data with the functor. -/
def whiskerRight {C : Type u} [Category.{v} C] {E : Type u'} [Category.{v'} E]
    {F G : ℕᵒᵖ ⥤ C} (a : InverseSequence.ProIso F G) (H : C ⥤ E) :
    InverseSequence.ProIso (F ⋙ H) (G ⋙ H) where
  α := a.α
  β := a.β
  αmono := a.αmono
  βmono := a.βmono
  αle := a.αle
  βle := a.βle
  φ m := H.map (a.φ m)
  ψ m := H.map (a.ψ m)
  φnat h := by
    simpa only [InverseSequence.tr, Functor.comp_map, ← H.map_comp] using congrArg H.map (a.φnat h)
  ψnat h := by
    simpa only [InverseSequence.tr, Functor.comp_map, ← H.map_comp] using congrArg H.map (a.ψnat h)
  ψφ m := by
    simpa only [InverseSequence.tr, Functor.comp_map, ← H.map_comp] using congrArg H.map (a.ψφ m)
  φψ m := by
    simpa only [InverseSequence.tr, Functor.comp_map, ← H.map_comp] using congrArg H.map (a.φψ m)

/-- An isomorphism of inverse systems indexed by `ℕᵒᵖ` is a pro-isomorphism, with both
reindexings the identity. -/
def ofNatIso {C : Type u} [Category.{v} C] {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) :
    InverseSequence.ProIso F G where
  α := id
  β := id
  αmono := monotone_id
  βmono := monotone_id
  αle _ := le_rfl
  βle _ := le_rfl
  φ m := e.hom.app (op m)
  ψ m := e.inv.app (op m)
  φnat h := by simp [InverseSequence.tr]
  ψnat h := by simp [InverseSequence.tr]
  ψφ m := by simp [InverseSequence.tr]
  φψ m := by simp [InverseSequence.tr]

/-- **Interleaved maps between two inverse systems.** A strictly increasing sequence of indices
`n₀ < n₁ < n₂ < ⋯` together with maps `X_{n_{2i+2}} ⟶ Y_{n_{2i+1}}` and
`Y_{n_{2i+1}} ⟶ X_{n_{2i}}` whose composites, in both orders, are the transition maps of the two
systems. -/
structure Interleaving (X Y : ℕᵒᵖ ⥤ D) where
  /-- The sequence of indices `n₀ < n₁ < n₂ < ⋯` at which the interleaved maps are given. -/
  idx : ℕ → ℕ
  /-- The sequence of indices is strictly increasing. -/
  idx_strictMono : StrictMono idx
  /-- The forward map `X_{n_{2i+2}} ⟶ Y_{n_{2i+1}}`. -/
  fwd (i : ℕ) : X.obj (op (idx (2 * i + 2))) ⟶ Y.obj (op (idx (2 * i + 1)))
  /-- The backward map `Y_{n_{2i+1}} ⟶ X_{n_{2i}}`. -/
  bwd (i : ℕ) : Y.obj (op (idx (2 * i + 1))) ⟶ X.obj (op (idx (2 * i)))
  /-- A forward map followed by the backward map of the same stage is the transition map
  `X_{n_{2i+2}} ⟶ X_{n_{2i}}`. -/
  fwd_bwd (i : ℕ) :
    fwd i ≫ bwd i = InverseSequence.tr X (idx_strictMono.monotone (show 2 * i ≤ 2 * i + 2 by omega))
  /-- A backward map followed by the forward map of the previous stage is the transition map
  `Y_{n_{2i+3}} ⟶ Y_{n_{2i+1}}`. -/
  bwd_fwd (i : ℕ) :
    bwd (i + 1) ≫ fwd i =
      InverseSequence.tr Y (idx_strictMono.monotone (show 2 * i + 1 ≤ 2 * (i + 1) + 1 by omega))

/-- Maps `f i : X_{g (2i+c)} ⟶ Y_{g (2i+d)}` that commute with the transition maps one step at a
time do so for any two stages. -/
private theorem comp_tr_eq_tr_comp_of_succ {X Y : ℕᵒᵖ ⥤ D} {g : ℕ → ℕ} (hg : Monotone g) (c d : ℕ)
    (f : ∀ i, X.obj (op (g (2 * i + c))) ⟶ Y.obj (op (g (2 * i + d))))
    (hf : ∀ i, f (i + 1) ≫ InverseSequence.tr Y (hg (by omega)) =
      InverseSequence.tr X (hg (by omega)) ≫ f i) {i i' : ℕ} (h : i ≤ i') :
    f i' ≫ InverseSequence.tr Y (hg (by omega)) = InverseSequence.tr X (hg (by omega)) ≫ f i := by
  induction i', h using Nat.le_induction with
  | base => rw [tr_refl, tr_refl, Category.comp_id, Category.id_comp]
  | succ k hk ih =>
      rw [← tr_trans Y (hg (by omega : 2 * i + d ≤ 2 * k + d)) (hg (by omega)), ← Category.assoc,
        hf k, Category.assoc, ih, ← Category.assoc, tr_trans X]

namespace Interleaving

variable {X Y : ℕᵒᵖ ⥤ D} (a : Interleaving X Y)

/-- The odd stages of the index sequence dominate the index: `m ≤ n_{2m+1}`. -/
theorem le_idx_odd (m : ℕ) : m ≤ a.idx (2 * m + 1) :=
  le_trans (by omega) (le_of_strictMono a.idx_strictMono (2 * m + 1))

/-- The even stages of the index sequence dominate the index: `m ≤ n_{2m}`. -/
theorem le_idx_even (m : ℕ) : m ≤ a.idx (2 * m) :=
  le_trans (by omega) (le_of_strictMono a.idx_strictMono (2 * m))

/-- The even stages of the index sequence dominate the successor of the index:
`m + 1 ≤ n_{2m+2}`. -/
theorem succ_le_idx_even (m : ℕ) : m + 1 ≤ a.idx (2 * m + 2) :=
  le_trans (by omega) (le_of_strictMono a.idx_strictMono (2 * m + 2))

/-- Passing from the forward map at stage `i + 1` to the one at stage `i` is a transition map:
the two differ by the transition maps of `X` and of `Y`. -/
theorem fwd_succ (i : ℕ) :
    a.fwd (i + 1) ≫
        InverseSequence.tr Y
          (a.idx_strictMono.monotone (show 2 * i + 1 ≤ 2 * (i + 1) + 1 by omega)) =
      InverseSequence.tr X
          (a.idx_strictMono.monotone (show 2 * i + 2 ≤ 2 * (i + 1) + 2 by omega)) ≫
        a.fwd i := by
  rw [← a.bwd_fwd i, ← Category.assoc, a.fwd_bwd (i + 1)]

/-- Passing from the backward map at stage `j + 1` to the one at stage `j` is a transition map:
the two differ by the transition maps of `Y` and of `X`. -/
theorem bwd_succ (j : ℕ) :
    a.bwd (j + 1) ≫
        InverseSequence.tr X (a.idx_strictMono.monotone (show 2 * j ≤ 2 * (j + 1) by omega)) =
      InverseSequence.tr Y (a.idx_strictMono.monotone (show 2 * j + 1 ≤ 2 * (j + 1) + 1 by omega)) ≫
        a.bwd j := by
  rw [← a.fwd_bwd j, ← Category.assoc, a.bwd_fwd j]

/-- The forward maps at any two stages differ by the transition maps of `X` and of `Y`. -/
theorem fwd_tr {i i' : ℕ} (h : i ≤ i') :
    a.fwd i' ≫
        InverseSequence.tr Y (a.idx_strictMono.monotone (show 2 * i + 1 ≤ 2 * i' + 1 by omega)) =
      InverseSequence.tr X (a.idx_strictMono.monotone (show 2 * i + 2 ≤ 2 * i' + 2 by omega)) ≫
        a.fwd i := by
  exact comp_tr_eq_tr_comp_of_succ a.idx_strictMono.monotone 2 1 a.fwd a.fwd_succ h

/-- The backward maps at any two stages differ by the transition maps of `Y` and of `X`. -/
theorem bwd_tr {j j' : ℕ} (h : j ≤ j') :
    a.bwd j' ≫ InverseSequence.tr X (a.idx_strictMono.monotone (show 2 * j ≤ 2 * j' by omega)) =
      InverseSequence.tr Y (a.idx_strictMono.monotone (show 2 * j + 1 ≤ 2 * j' + 1 by omega)) ≫
        a.bwd j := by
  exact comp_tr_eq_tr_comp_of_succ a.idx_strictMono.monotone 1 0 a.bwd a.bwd_succ h

/-- **Interleaved maps give a pro-isomorphism.** The reindexings are `m ↦ n_{2m+2}` and
`m ↦ n_{2m+1}`, and the two families of maps are the interleaved ones followed by transition
maps. -/
def proIso : InverseSequence.ProIso X Y where
  α m := a.idx (2 * m + 2)
  β m := a.idx (2 * m + 1)
  αmono _ _ h := a.idx_strictMono.monotone (by omega)
  βmono _ _ h := a.idx_strictMono.monotone (by omega)
  αle m := le_trans (by omega) (le_of_strictMono a.idx_strictMono (2 * m + 2))
  βle m := a.le_idx_odd m
  φ m := a.fwd m ≫ InverseSequence.tr Y (a.le_idx_odd m)
  ψ m := a.bwd m ≫ InverseSequence.tr X (a.le_idx_even m)
  φnat {m m'} h := by
    rw [← Category.assoc, ← a.fwd_tr h]
    simp only [Category.assoc, tr_trans]
  ψnat {m m'} h := by
    rw [← Category.assoc, ← a.bwd_tr h]
    simp only [Category.assoc, tr_trans]
  ψφ m := by
    have key : a.fwd (a.idx (2 * m + 1)) ≫ InverseSequence.tr Y (a.le_idx_odd (a.idx (2 * m + 1))) =
        InverseSequence.tr X (a.idx_strictMono.monotone
          (show 2 * m + 2 ≤ 2 * a.idx (2 * m + 1) + 2 by
            have := a.le_idx_odd m; omega)) ≫ a.fwd m :=
      a.fwd_tr (a.le_idx_odd m)
    rw [key]
    simp only [Category.assoc]
    rw [← Category.assoc (a.fwd m), a.fwd_bwd m]
    simp only [tr_trans]
  φψ m := by
    have key : a.bwd (a.idx (2 * m + 2)) ≫
          InverseSequence.tr X (a.le_idx_even (a.idx (2 * m + 2))) =
        InverseSequence.tr Y (a.idx_strictMono.monotone
          (show 2 * (m + 1) + 1 ≤ 2 * a.idx (2 * m + 2) + 1 by
            have := a.succ_le_idx_even m; omega)) ≫ a.bwd (m + 1) :=
      a.bwd_tr (a.succ_le_idx_even m)
    rw [key]
    simp only [Category.assoc]
    rw [← Category.assoc (a.bwd (m + 1)), a.bwd_fwd m]
    simp only [tr_trans]

/-- **Derived limits of interleaved inverse systems agree.** If two inverse systems of a
pretriangulated category admit interleaved maps, then any two derived limits of them are
isomorphic, although not canonically. This is Tag 0H9L, applied to the pro-isomorphism the
interleaved maps produce. -/
theorem nonempty_iso_of_isDerivedLimit {E : Type u} [Category.{v} E] [HasZeroObject E]
    [HasShift E ℤ] [Preadditive E] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    {F G : ℕᵒᵖ ⥤ E} (a : Interleaving F G) [HasProduct fun n : ℕ => F.obj (op n)]
    [HasProduct fun n : ℕ => G.obj (op n)] (K K' : E)
    (hK : Pretriangulated.IsDerivedLimit F K) (hK' : Pretriangulated.IsDerivedLimit G K') :
    Nonempty (K ≅ K') :=
  Rlim.Pro.nonempty_iso_of_isDerivedLimit_of_pro_isomorphism F G K K' hK hK' a.proIso

end Interleaving

end InverseSequence.ProIso

end

end
