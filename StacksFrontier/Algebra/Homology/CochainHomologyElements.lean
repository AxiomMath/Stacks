module

public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ComplexShape

/-!
# Elements of the cohomology of an `ℕ`-indexed cochain complex of modules

For a cochain complex `K` of modules indexed by `ℕ`, the degree-`p` cohomology is the quotient of
the cocycles by the coboundaries. This file records that description on elements, in the form a
comparison of two complexes by explicit cochains consumes:

* every class is the class of a cocycle (`exists_eq_homologyπ_cyclesMk`);
* the class of a cocycle vanishes exactly when the cocycle is a coboundary, which in degree zero
  means that it is zero (`homologyπ_cyclesMk_eq_zero_iff_zero`,
  `homologyπ_cyclesMk_eq_zero_iff_succ`);
* a morphism of complexes acts on classes through its components
  (`homologyMap_homologyπ_cyclesMk`).

## References

* [Stacks Project, Tag 0118](https://stacks.math.columbia.edu/tag/0118)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Stacks.CochainHomologyElements

variable {R : Type u} [Ring R]

/-- The cocycle condition in an `ℕ`-indexed cochain complex. -/
abbrev IsCocycle (K : CochainComplex (ModuleCat.{v} R) ℕ) {p : ℕ} (z : K.X p) : Prop :=
  K.d p (p + 1) z = 0

/-- The class of a cocycle. -/
noncomputable abbrev cls (K : CochainComplex (ModuleCat.{v} R) ℕ) {p : ℕ} (z : K.X p)
    (hz : IsCocycle K z) : K.homology p :=
  K.homologyπ p (K.cyclesMk z (p + 1) (by simp) hz)

/-- A cycle whose underlying element is a cocycle `z` is `cyclesMk z`. -/
private theorem eq_cyclesMk_of_iCycles_eq (K : CochainComplex (ModuleCat.{v} R) ℕ) {p : ℕ}
    (c : K.cycles p) (z : K.X p) (hz : IsCocycle K z) (h : K.iCycles p c = z) :
    c = K.cyclesMk z (p + 1) (by simp) hz :=
  (ModuleCat.mono_iff_injective (K.iCycles p)).1 inferInstance
    (h.trans (K.i_cyclesMk z (p + 1) (by simp) hz).symm)

/-- **Every class is the class of a cocycle.** -/
theorem exists_eq_cls (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) (x : K.homology p) :
    ∃ (z : K.X p) (hz : IsCocycle K z), x = cls K z hz := by
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ p)).1 inferInstance x
  exact ⟨K.iCycles p c, congrArg (fun k : K.cycles p ⟶ K.X (p + 1) => k c) (K.iCycles_d p (p + 1)),
    congrArg _ <| eq_cyclesMk_of_iCycles_eq K c _ _ rfl⟩

/-- **The class of a cocycle of degree `p + 1` vanishes exactly when it is a coboundary.** -/
theorem cls_eq_zero_iff_succ (K : CochainComplex (ModuleCat.{v} R) ℕ) (p : ℕ) (z : K.X (p + 1))
    (hz : IsCocycle K z) : cls K z hz = 0 ↔ ∃ y : K.X p, K.d p (p + 1) y = z := by
  have hS := ShortComplex.exact_of_g_is_cokernel
    (.mk (K.toCycles p (p + 1)) (K.homologyπ (p + 1)) (K.toCycles_comp_homologyπ p (p + 1)))
    (K.homologyIsCokernel p (p + 1) (by simp))
  have hi := K.i_cyclesMk z (p + 2) (by simp) hz
  constructor
  · intro h0
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS _ h0
    exact ⟨y, (congrArg (fun k : K.X p ⟶ K.X (p + 1) => k y) (K.toCycles_i p (p + 1))).symm.trans
      ((congrArg (K.iCycles (p + 1)) hy).trans hi)⟩
  · rintro ⟨y, hy⟩
    have : K.toCycles p (p + 1) y = K.cyclesMk z (p + 2) (by simp) hz :=
      eq_cyclesMk_of_iCycles_eq K _ z hz
        ((congrArg (fun k : K.X p ⟶ K.X (p + 1) => k y) (K.toCycles_i p (p + 1))).trans hy)
    exact (congrArg (K.homologyπ (p + 1)) this.symm).trans
      (congrArg (fun k : K.X p ⟶ K.homology (p + 1) => k y) (K.toCycles_comp_homologyπ p (p + 1)))

/-- **The class of a cocycle of degree `0` vanishes exactly when the cocycle is zero.** -/
theorem cls_eq_zero_iff_zero (K : CochainComplex (ModuleCat.{v} R) ℕ) (z : K.X 0)
    (hz : IsCocycle K z) : cls K z hz = 0 ↔ z = 0 := by
  have hiso : IsIso (K.homologyπ 0) := K.isIso_homologyπ 0 0 (by simp) (by
    rw [HomologicalComplex.shape _ _ _ (by simp)])
  have hinj := (ModuleCat.mono_iff_injective (K.homologyπ 0)).1 inferInstance
  have hi := K.i_cyclesMk z 1 (by simp) hz
  constructor
  · intro h0
    have : K.cyclesMk z 1 (by simp) hz = 0 := hinj (h0.trans (map_zero _).symm)
    rw [← hi, this, map_zero]
  · rintro rfl
    have : K.cyclesMk (0 : K.X 0) 1 (by simp) hz = 0 :=
      (eq_cyclesMk_of_iCycles_eq K 0 0 hz (map_zero _)).symm
    exact (congrArg (K.homologyπ 0) this).trans (map_zero _)

/-- **A morphism of complexes acts on classes through its components.** -/
theorem homologyMap_cls {K K' : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ K') (p : ℕ)
    (z : K.X p) (hz : IsCocycle K z) (hz' : IsCocycle K' (φ.f p z)) :
    HomologicalComplex.homologyMap φ p (cls K z hz) = cls K' (φ.f p z) hz' := by
  show (K.homologyπ p ≫ HomologicalComplex.homologyMap φ p) _ = _
  rw [HomologicalComplex.homologyπ_naturality]
  refine congrArg (K'.homologyπ p) (eq_cyclesMk_of_iCycles_eq K' _ _ hz' ?_)
  show (HomologicalComplex.cyclesMap φ p ≫ K'.iCycles p) _ = _
  rw [HomologicalComplex.cyclesMap_i]
  exact congrArg (φ.f p) (K.i_cyclesMk z (p + 1) (by simp) hz)

/-- A morphism of complexes preserves cocycles. -/
theorem isCocycle_map {K K' : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ K') {p : ℕ}
    {z : K.X p} (hz : IsCocycle K z) : IsCocycle K' (φ.f p z) :=
  (congrArg (fun k : K.X p ⟶ K'.X (p + 1) => k z) (φ.comm p (p + 1))).trans
    ((congrArg (φ.f (p + 1)) hz).trans (map_zero _))

end Stacks.CochainHomologyElements

end
