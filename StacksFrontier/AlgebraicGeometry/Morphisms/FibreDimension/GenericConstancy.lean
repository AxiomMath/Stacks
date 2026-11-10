module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Surjective
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg

/-!
# Constancy of the dimension of the fibres near the generic point

Let `f : X ⟶ Y` be a morphism of finite type with `Y` irreducible with generic point `η`. If the
generic fibre `X_η` has dimension `n`, then there is a nonempty open `V ⊆ Y` over which every
fibre has dimension `n`.

The proof is the source's. The locus in `X` where the fibre has local dimension more than `n` is
closed and misses the generic fibre, so after shrinking `Y` it is empty; the locus where the
local dimension is exactly `n` is also closed and meets the generic fibre, so after shrinking `Y`
again it surjects onto `Y`. Over the resulting open subset every fibre has all its local
dimensions at most `n` and at least one of them equal to `n`.

## Main results

* `AlgebraicGeometry.exists_nonempty_open_fiberDimension_eq` is **Stacks Tag 05F7**.
* `AlgebraicGeometry.exists_nonempty_open_fiberDimension_le` is its upper-bound half, which asks
  only for an upper bound on the dimension of the generic fibre. Both are built from the same
  construction of the open subset, so the upper bound is proved once.

## Implementation notes

A morphism of finite type is, following Mathlib, `AlgebraicGeometry.LocallyOfFiniteType`
together with `AlgebraicGeometry.QuasiCompact`. The two closed loci are taken as reduced induced
closed subschemes, via `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, so that the
shrinking steps — Tags 02NE and 05F5 — can be applied to morphisms of schemes.

The source's `Z' = {x | dim_x(X_{f(x)}) > n - 1}` is read with `n - 1` truncated subtraction, so
for `n = 0` it is the whole of `X`; this is why the second locus is described by a disjunction on
whether `n` is zero.

## References

* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A space of finite dimension `n` has a point at which its local dimension is `n`: the
dimension is the supremum of the local dimensions, and a supremum of extended naturals below `⊤`
is attained. -/
@[ega "0 14.1.6" "partial"]
private lemma exists_topologicalKrullDimAt_eq {S : Type*} [TopologicalSpace S] (n : ℕ)
    (h : topologicalKrullDim S = (n : WithBot ℕ∞)) :
    ∃ x : S, topologicalKrullDimAt S x = (n : WithBot ℕ∞) := by
  classical
  have hsup : (⨆ x : S, topologicalKrullDimAt S x) = (n : WithBot ℕ∞) := by
    simpa only [topologicalKrullDim_eq_iSup_localKrullDim,
      ← topologicalKrullDimAt_eq_localKrullDim] using h
  have hS : Nonempty S := by
    by_contra hne
    exact WithBot.coe_ne_bot
      (h.symm.trans ((topologicalKrullDim_eq_bot_iff_isEmpty S).mpr (not_nonempty_iff.mp hne)))
  let d : S → ℕ∞ := fun x ↦ (topologicalKrullDimAt S x).unbot (topologicalKrullDimAt_ne_bot x)
  have hdsup : (⨆ x : S, d x) = (n : ℕ∞) := by
    apply WithBot.coe_injective
    calc ((⨆ x : S, d x) : ℕ∞) = ⨆ x : S, (d x : WithBot ℕ∞) :=
        WithBot.coe_iSup ⟨⊤, fun _ _ ↦ le_top⟩
      _ = ⨆ x : S, topologicalKrullDimAt S x := by
        refine congrArg _ (funext fun x ↦ ?_)
        exact WithBot.coe_unbot _ (topologicalKrullDimAt_ne_bot x)
      _ = (n : WithBot ℕ∞) := hsup
  obtain ⟨x, hx⟩ := ENat.exists_eq_iSup_of_lt_top (f := d) (by simp [hdsup])
  refine ⟨x, ?_⟩
  calc topologicalKrullDimAt S x = (d x : WithBot ℕ∞) :=
        (WithBot.coe_unbot _ (topologicalKrullDimAt_ne_bot x)).symm
    _ = (n : WithBot ℕ∞) := congrArg (fun k : ℕ∞ ↦ (k : WithBot ℕ∞)) (by rw [hx, hdsup])

/-- The local dimension of a fibre is at least zero. -/
private lemma zero_le_topologicalKrullDimAt_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    (0 : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  rw [← WithBot.coe_unbot _ (topologicalKrullDimAt_ne_bot (X := f.fiber (f x)) (f.asFiber x))]
  exact WithBot.coe_le_coe.mpr bot_le

/-- If the local dimension of a fibre is not at most `k`, it is at least `k + 1`. -/
private lemma succ_le_topologicalKrullDimAt_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (k : ℕ)
    (h : ¬ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (k : WithBot ℕ∞)) :
    ((k + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  have hne := topologicalKrullDimAt_ne_bot (X := f.fiber (f x)) (f.asFiber x)
  have hnot : ¬ (topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)).unbot hne ≤ (k : ℕ∞) :=
    fun hdk ↦ h ((WithBot.coe_unbot _ hne).symm.trans_le (WithBot.coe_le_coe.mpr hdk))
  calc ((k + 1 : ℕ) : WithBot ℕ∞)
      ≤ (((topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)).unbot hne : ℕ∞) :
          WithBot ℕ∞) := by
        refine WithBot.coe_le_coe.mpr ?_
        simpa using ENat.natCast_add_one_le_iff.mpr (lt_of_not_ge hnot)
    _ = topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := WithBot.coe_unbot _ hne

/-- A point of `X` lies in the image of the reduced induced subscheme on a closed set `C` exactly
when it lies in `C`. -/
private lemma mem_range_vanishingIdeal_subschemeι {X : Scheme.{u}} (C : Closeds X) (x : X) :
    x ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal C).subschemeι ↔ x ∈ C := by
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

/-- **The upper half of the proof of Tag 05F7.** If the generic fibre has dimension at most `n`,
then over some open neighbourhood of the generic point every point of `X` has local fibre
dimension at most `n`. The locus in `X` where that dimension exceeds `n` is closed (Tag 02FZ) and
misses the generic fibre, so its image is a closed subset of `Y` avoiding `η`; the neighbourhood
is the complement.

This is the half of Tag 05F7 which does not need the dimension of the generic fibre to be known
exactly, and it is what `AlgebraicGeometry.exists_nonempty_open_fiberDimension_le` and the lower
half of `AlgebraicGeometry.exists_nonempty_open_fiberDimension_eq` are both built from. -/
private theorem exists_open_nhds_forall_topologicalKrullDimAt_fiber_le {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IrreducibleSpace Y] [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) (η : Y)
    (hη : IsGenericPoint η Set.univ) (hdim : f.fiberDimension η ≤ (n : WithBot ℕ∞)) :
    ∃ U : Y.Opens, η ∈ U ∧ ∀ y ∈ U, f.fiberDimension y ≤ (n : WithBot ℕ∞) := by
  classical
  let d : X → WithBot ℕ∞ := fun x ↦ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)
  -- The closed locus where the fibre has local dimension more than `n`, as a subscheme.
  let Cbad : Closeds X := ⟨{x | d x ≤ (n : WithBot ℕ∞)}ᶜ,
    (isOpen_setOf_fiberDimensionAt_le f n).isClosed_compl⟩
  let Ibad : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Cbad
  let gbad : Ibad.subscheme ⟶ Y := Ibad.subschemeι ≫ f
  have hηnot_bad : η ∉ Set.range gbad := by
    rintro ⟨z, hz⟩
    exact (mem_range_vanishingIdeal_subschemeι Cbad _).mp ⟨z, rfl⟩
      ((Scheme.Hom.fiberDimension_le_iff f η _).mp hdim _ hz)
  have : QuasiCompact gbad := by dsimp only [gbad]; infer_instance
  obtain ⟨U₀, hηU₀, hgbadU₀⟩ := exists_open_nhds_disjoint_range_of_quasiCompact gbad η
    (AlgebraicGeometry.mem_genericPoints_of_isGenericPoint_univ hη) hηnot_bad
  refine ⟨U₀, hηU₀, fun y hy ↦ (Scheme.Hom.fiberDimension_le_iff f y _).mpr ?_⟩
  rintro x rfl
  by_contra hnot
  obtain ⟨z, hzx⟩ := (mem_range_vanishingIdeal_subschemeι Cbad x).mpr hnot
  have hzU₀ : z ∈ gbad ⁻¹ᵁ U₀ := by
    change f (Ibad.subschemeι z) ∈ U₀
    rwa [hzx]
  simp [hgbadU₀] at hzU₀

/-- **Stacks Project, Tag 05F7, the upper bound.** Let `f : X ⟶ Y` be a morphism of finite type
with `Y` irreducible with generic point `η`. If the generic fibre has dimension at most `n`, then
the fibres over some nonempty open subset of `Y` all have dimension at most `n`.

The source states the equality, which needs the dimension of the generic fibre on the nose; the
inequality is what the bound `dim(fibre) ≤ dim X - dim Y` is read off, and it is the half of the
proof that does not use the lower bound. -/
public theorem exists_nonempty_open_fiberDimension_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) (η : Y)
    (hη : IsGenericPoint η Set.univ) (hdim : f.fiberDimension η ≤ (n : WithBot ℕ∞)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ y ∈ V, f.fiberDimension y ≤ (n : WithBot ℕ∞) := by
  obtain ⟨U, hηU, hupper⟩ :=
    exists_open_nhds_forall_topologicalKrullDimAt_fiber_le f n η hη hdim
  exact ⟨U, ⟨η, hηU⟩, hupper⟩

/-- The lower half of the proof of Tag 05F7: if the generic fibre has dimension `n`, then over
some open neighbourhood of the generic point every fibre has dimension at least `n`. -/
private theorem exists_open_nhds_forall_le_fiberDimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) (η : Y)
    (hη : IsGenericPoint η Set.univ) (hdim : f.fiberDimension η = (n : WithBot ℕ∞)) :
    ∃ V : Y.Opens, η ∈ V ∧ ∀ y ∈ V, (n : WithBot ℕ∞) ≤ f.fiberDimension y := by
  classical
  let d : X → WithBot ℕ∞ := fun x ↦ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)
  obtain ⟨qη, hqη⟩ := exists_topologicalKrullDimAt_eq n hdim
  let xη : X := f.fiberι η qη
  have hxη : f xη = η := by
    have h : xη ∈ Set.range (f.fiberι η) := ⟨qη, rfl⟩
    rwa [f.range_fiberι η] at h
  have hdη : d xη = (n : WithBot ℕ∞) := by
    change topologicalKrullDimAt (f.fiber (f xη)) (f.asFiber xη) = _
    rw [Scheme.Hom.topologicalKrullDimAt_fiber_fiberι]
    exact hqη
  -- The closed locus where the fibre has local dimension at least `n`, as a subscheme.
  let Clower : Closeds X := ⟨{x | n = 0 ∨ ¬ d x ≤ ((n - 1 : ℕ) : WithBot ℕ∞)}, by
    by_cases h0 : n = 0
    · simp [h0]
    · have hset : {x : X | n = 0 ∨ ¬ d x ≤ ((n - 1 : ℕ) : WithBot ℕ∞)} =
          {x | d x ≤ ((n - 1 : ℕ) : WithBot ℕ∞)}ᶜ := by ext x; simp [h0]
      rw [hset]
      exact (isOpen_setOf_fiberDimensionAt_le f (n - 1)).isClosed_compl⟩
  let Ilower : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Clower
  let glow : Ilower.subscheme ⟶ Y := Ilower.subschemeι ≫ f
  obtain ⟨zη, hzη⟩ : xη ∈ Set.range Ilower.subschemeι := by
    rw [mem_range_vanishingIdeal_subschemeι]
    change n = 0 ∨ ¬ d xη ≤ ((n - 1 : ℕ) : WithBot ℕ∞)
    by_cases h0 : n = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [hdη]
      exact not_le_of_gt (by exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero h0) Nat.one_pos)
  have hglowη : glow zη = η := by
    change f (Ilower.subschemeι zη) = η
    rwa [hzη]
  have hgeneric_fiber_nonempty : Nonempty (glow.fiber η) := by
    obtain ⟨z, -⟩ : zη ∈ Set.range (glow.fiberι η) := by rwa [glow.range_fiberι η]
    exact ⟨z⟩
  have : LocallyOfFiniteType glow := by dsimp only [glow]; infer_instance
  have : QuasiCompact glow := by dsimp only [glow]; infer_instance
  obtain ⟨V, hVnonempty, hVsurjective⟩ :=
    exists_nonempty_open_surjective_baseChange glow η hη hgeneric_fiber_nonempty
  have hηV : η ∈ V := by
    obtain ⟨y, hy⟩ := hVnonempty
    by_contra hηnotV
    exact (V.is_open'.not_specializes hηnotV hy) (hη.specializes (Set.mem_univ y))
  refine ⟨V, hηV, fun y hyV ↦ ?_⟩
  have hz : (⟨y, hyV⟩ : V) ∈ Set.range (Limits.pullback.snd glow V.ι) :=
    hVsurjective.surj ⟨y, hyV⟩
  rw [Scheme.Pullback.range_snd] at hz
  obtain ⟨z, hz⟩ := hz
  have hxy : f (Ilower.subschemeι z) = y := hz
  have hx_lower : Ilower.subschemeι z ∈ Clower :=
    (mem_range_vanishingIdeal_subschemeι Clower _).mp ⟨z, rfl⟩
  refine Scheme.Hom.le_fiberDimension_of_le_topologicalKrullDimAt_fiber f hxy ?_
  by_cases h0 : n = 0
  · subst n
    simpa using zero_le_topologicalKrullDimAt_fiber f (Ilower.subschemeι z)
  · have hsucc := succ_le_topologicalKrullDimAt_fiber f (Ilower.subschemeι z) (n - 1)
      (hx_lower.resolve_left h0)
    rwa [Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)] at hsucc

/-- **Stacks Project, Tag 05F7.** Let `f : X ⟶ Y` be a morphism of finite type with `Y`
irreducible with generic point `η`. If the generic fibre has dimension `n`, then the fibres over
some nonempty open subset of `Y` all have dimension `n`. -/
@[stacks 05F7, ega "IV 9.5.6" "dim X_s = n near η"]
public theorem exists_nonempty_open_fiberDimension_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) (η : Y)
    (hη : IsGenericPoint η Set.univ) (hdim : f.fiberDimension η = (n : WithBot ℕ∞)) :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ y ∈ V, f.fiberDimension y = (n : WithBot ℕ∞) := by
  obtain ⟨U, hηU, hupper⟩ :=
    exists_open_nhds_forall_topologicalKrullDimAt_fiber_le f n η hη hdim.le
  obtain ⟨V, hηV, hlower⟩ := exists_open_nhds_forall_le_fiberDimension f n η hη hdim
  refine ⟨U ⊓ V, ⟨η, ⟨hηU, hηV⟩⟩, ?_⟩
  rintro y ⟨hyU, hyV⟩
  exact le_antisymm (hupper y hyU) (hlower y hyV)

end AlgebraicGeometry

end
