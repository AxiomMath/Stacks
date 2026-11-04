module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.Images

/-!
# The short exact sequence of cycles of a short exact sequence of complexes

Let `0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` be a short exact sequence of homological complexes in an abelian
category and let `n` be a degree. Taking cycles in degree `n` is left exact, so
`0 ⟶ Zⁿ(K₁) ⟶ Zⁿ(K₂) ⟶ Zⁿ(K₃)` is exact; replacing `Zⁿ(K₃)` by the image of `Zⁿ(K₂)` gives a
short exact sequence

`0 ⟶ Zⁿ(K₁) ⟶ Zⁿ(K₂) ⟶ Im(Zⁿ(K₂) ⟶ Zⁿ(K₃)) ⟶ 0`.

Placed in degree `n` it maps to the original sequence by the inclusions of cycles. A connecting
morphism of the original sequence can then be computed on this sequence of objects.

## Main definitions

* `HomologicalComplex.shortExactCycles`: the short complex `Zⁿ(K₁) ⟶ Zⁿ(K₂) ⟶ Im`.
* `HomologicalComplex.cyclesImageι`: the inclusion `Im ⟶ Zⁿ(K₃)`.

## Main results

* `HomologicalComplex.shortExactCycles_shortExact`: the sequence of cycles is short exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  (S : ShortComplex (HomologicalComplex C c)) (n : ι)

/-- **The short complex of cycles** `Zⁿ(K₁) ⟶ Zⁿ(K₂) ⟶ Im(Zⁿ(K₂) ⟶ Zⁿ(K₃))` of a short complex
of homological complexes. -/
abbrev shortExactCycles : ShortComplex C :=
  ShortComplex.mk (cyclesMap S.f n) (Abelian.factorThruImage (cyclesMap S.g n)) (by
    rw [← cancel_mono (Abelian.image.ι (cyclesMap S.g n)), Category.assoc,
      Abelian.image.fac, ← cyclesMap_comp, S.zero, cyclesMap_zero, zero_comp])

/-- The inclusion of the image of the cycles of `K₂` into the cycles of `K₃`. -/
abbrev cyclesImageι : (shortExactCycles S n).X₃ ⟶ S.X₃.cycles n :=
  Abelian.image.ι (cyclesMap S.g n)

/-- The second map of the sequence of cycles, followed by the inclusion of the image, is the
map induced on cycles. -/
@[reassoc (attr := simp)]
theorem shortExactCycles_g_cyclesImageι :
    (shortExactCycles S n).g ≫ cyclesImageι S n = cyclesMap S.g n :=
  Abelian.image.fac _

variable {S}

/-- **The sequence of cycles of a short exact sequence of complexes is short exact.** -/
theorem shortExactCycles_shortExact (hS : S.ShortExact) :
    (shortExactCycles S n).ShortExact := by
  have hSn := hS.map_of_exact (HomologicalComplex.eval C c n)
  have hfm : ∀ m, Mono (S.f.f m) := fun m =>
    (hS.map_of_exact (HomologicalComplex.eval C c m)).mono_f
  have := hfm n
  have hmono : Mono (cyclesMap S.f n) := by
    refine ⟨fun a b hab => ?_⟩
    rw [← cancel_mono (S.X₁.iCycles n), ← cancel_mono (S.f.f n), Category.assoc,
      Category.assoc, ← cyclesMap_i, reassoc_of% hab]
  refine ShortComplex.ShortExact.mk' ?_ hmono (inferInstanceAs (Epi (Abelian.factorThruImage _)))
  have hz' : ∀ {W : C} (z : W ⟶ S.X₂.cycles n),
      z ≫ Abelian.factorThruImage (cyclesMap S.g n) = 0 →
        (z ≫ S.X₂.iCycles n) ≫ S.g.f n = 0 := fun {W} z hz => by
    rw [Category.assoc, ← cyclesMap_i, ← Category.assoc,
      ← Abelian.image.fac (cyclesMap S.g n), reassoc_of% hz, zero_comp, zero_comp]
  refine ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι' _ _ fun z hz => ?_)
  obtain ⟨w, hw⟩ := KernelFork.IsLimit.lift' hSn.fIsKernel _ (hz' z hz)
  change w ≫ S.f.f n = _ at hw
  have := hfm (c.next n)
  refine ⟨S.X₁.liftCycles w (c.next n) rfl ?_, ?_⟩
  · rw [← cancel_mono (S.f.f (c.next n)), Category.assoc, ← S.f.comm, reassoc_of% hw, iCycles_d,
      Limits.comp_zero, Limits.zero_comp]
  · rw [← cancel_mono (S.X₂.iCycles n), Category.assoc, cyclesMap_i, liftCycles_i_assoc, hw]

end HomologicalComplex

end
