module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.GenericFibreTrivialization
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Tensor
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Stalk

/-!
# The canonical map `M̃ ⊗ Ñ → (M ⊗_S N)~` on `Proj` is not an isomorphism

Tag 01MK produces, for graded modules `M` and `N` over a graded ring `S`, a canonical morphism
of `𝒪_{Proj(S)}`-modules

  `M̃ ⊗_{𝒪} Ñ ⟶ (M ⊗_S N)~`,

namely `Stacks.AlgebraicGeometry.ProjSheafFunctoriality.associatedModuleSheafTensorMap`. Tag
01ML's headline is that this morphism is **not** an isomorphism in general. This file proves
that headline, by a counterexample in which both sides can be read off a single point.

Take `S = k[X]` graded with `deg X = 2`, so that every odd graded piece of `S` is zero, and
take `M = N = S(1)`. Then `Proj(S)` is the single point `𝔭 = (0)`, and:

* a degree-zero fraction of `S(1)` at `𝔭` has a numerator in `S_{d+1}` over a denominator in
  `S_d`, and one of `d`, `d + 1` is odd, so one of the two is zero — hence `M̃` is the zero
  sheaf, and so is `M̃ ⊗_{𝒪} Ñ`;
* `X ⊗ 1` is a degree-zero element of `S(1) ⊗_S S(1)` (degrees `2` and `-1 + 1 = 0` add to
  `0`), and `(X ⊗ 1)/1` is a nonzero degree-zero fraction — hence `(M ⊗_S N)~` is not the zero
  sheaf at `𝔭`.

So the morphism is one from a sheaf with vanishing stalk to a sheaf with nonvanishing stalk.

## Main definitions

* `Stacks.EvenWeightProj.grading`: `k[X]` graded with the variable in degree `2`.
* `Stacks.EvenWeightProj.pt`: the only point of `Proj` of that graded ring.
* `Stacks.EvenWeightProj.oddTwist` and `Stacks.EvenWeightProj.tensorTwist`: the gradings of
  `S(1)` and of `S(1) ⊗_S S(1)`.

## Main results

* `Stacks.EvenWeightProj.grading_eq_bot_of_odd`: the odd graded pieces of `k[X]` vanish.
* `Stacks.EvenWeightProj.degreeZeroModuleAt_oddTwist_eq_bot`: the stalk of `S(1)~` at the point
  is zero.
* `Stacks.EvenWeightProj.degreeZeroModuleAt_tensorTwist_ne_bot`: the stalk of
  `(S(1) ⊗_S S(1))~` at the point is not zero.
* `Stacks.EvenWeightProj.not_isIso_associatedModuleSheafTensorMap`: **Tag 01MK's morphism is
  not an isomorphism.**

## Implementation notes

The witness is not the source's. The source's remark argues with `S = k[x, y, z]` of weights
`1, 2, 3` and `M = S(1)`, `N = S(2)`, and compares the three fibre dimensions `2`, `2` and `1`
of `M₍z₎`, `N₍z₎` and `S(3)₍z₎` at the vertex ideal; that computation is complete in
`StacksFrontier/RingTheory/GradedAlgebra/Examples/` and is assembled into the algebraic
non-bijectivity
`Stacks.WeightedPolynomialSituation.not_bijective_localizedTwistTensorMap`. Deducing the
sheaf-level statement *from that example* needs a bridge between the two models of the chart
sections — the example's `Stacks.ProjStandardOpenBaseChange.twistAway`, a submodule of
`Localization (Submonoid.powers z)`, against the sheaf machinery's
`GradedModuleDegreeZeroLocalization` — and then a localization of the chart module at the
vertex ideal; neither exists in the library. The counterexample here needs neither: a parity
obstruction kills the whole of `M̃`, so the comparison happens between a zero module and a
nonzero one.

The argument runs at a stalk, not on sections, because the stalk of a tensor product of
sheaves of modules *is* the tensor product of the stalks
(`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, Tag 01CB), whereas the sections
of the sheafified tensor product over an open have no such description.

## References

* [Stacks Project, Tag 01ML](https://stacks.math.columbia.edu/tag/01ML)
* [Stacks Project, Tag 01MK](https://stacks.math.columbia.edu/tag/01MK)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.GradedLocalization
open Stacks.GradedModule (tensorGrading tmul_mem_tensorGrading)
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct

namespace Stacks.EvenWeightProj

universe u

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- The weight assigning degree `2` to the single variable of `k[X]`. -/
public def evenWeight : Fin 1 → ℕ := fun _ => 2

variable (k : Type u) [Field k]

/-- The polynomial ring `k[X]`. -/
public abbrev Poly := MvPolynomial (Fin 1) k

/-- The grading of `k[X]` in which the variable has degree `2`. -/
public abbrev grading : ℕ → Submodule k (Poly k) :=
  MvPolynomial.weightedHomogeneousSubmodule k evenWeight

/-- The graded-algebra structure of the even-weight grading. -/
public instance gradingGradedAlgebra : GradedAlgebra (grading k) :=
  MvPolynomial.weightedGradedAlgebra k evenWeight

/-- Every monomial has even weight. -/
public theorem two_dvd_weight (d : Fin 1 →₀ ℕ) : 2 ∣ Finsupp.weight evenWeight d := by
  rw [Finsupp.weight_apply]
  exact Finset.dvd_sum fun i _ => ⟨d i, by simp [evenWeight, Nat.mul_comm]⟩

/-- The odd graded pieces of `k[X]` vanish: every monomial has even weight. -/
public theorem grading_eq_bot_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) : grading k n = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun p hp => ?_
  by_contra hp0
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hp0
  exact hn (((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hp hd) ▸ two_dvd_weight d)

/-- The variable, of degree `2`. -/
public abbrev xvar : Poly k := MvPolynomial.X 0

/-- The variable is homogeneous of degree two. -/
public theorem xvar_mem : xvar k ∈ grading k 2 :=
  MvPolynomial.isWeightedHomogeneous_X k evenWeight 0

/-- The only point of `Proj` of `k[X]`: the zero ideal, which is prime and does not contain
the variable. -/
public def pt : ProjectiveSpectrum (grading k) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    exact Ideal.isPrime_bot
  not_irrelevant_le := by
    intro h
    have hX : xvar k ∈ HomogeneousIdeal.irrelevant (grading k) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ (by norm_num) (xvar_mem k)
    have h0 : xvar k ∈ (⊥ : HomogeneousIdeal (grading k)).toIdeal :=
      HomogeneousIdeal.mem_iff.mpr (h hX)
    rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h0
    exact MvPolynomial.X_ne_zero 0 h0

/-- A denominator allowed at the point is a nonzero polynomial. -/
public theorem ne_zero_of_mem_primeCompl
    (s : (pt k).asHomogeneousIdeal.toIdeal.primeCompl) : (s : Poly k) ≠ 0 := by
  intro h
  refine s.2 ?_
  change (s : Poly k) ∈ (⊥ : HomogeneousIdeal (grading k)).toIdeal
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot]
  exact h

/-- The grading of the twist `S(1)`, whose degree-`i` piece is `S_{i+1}`. -/
public abbrev oddTwist : ℤ → Submodule ℤ (Poly k) :=
  ProjectiveSpectrum.Proj.twistGrading (S := Poly k) (grading k) 1

/-- The grading of the tensor product `S(1) ⊗_S S(1)`. -/
public abbrev tensorTwist : ℤ → AddSubgroup (Poly k ⊗[Poly k] Poly k) :=
  tensorGrading (S := Poly k) (oddTwist k) (oddTwist k)

/-- The decomposition of the tensor grading, as an instance for this situation. -/
public instance tensorTwistDecomposition : DirectSum.Decomposition (tensorTwist k) :=
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_decomposition (S := Poly k)
    (grading k) (oddTwist k) (oddTwist k)

/-- The graded action on the tensor grading, as an instance for this situation. -/
public instance tensorTwistGradedSMul : SetLike.GradedSMul (grading k) (tensorTwist k) :=
  Stacks.AlgebraicGeometry.ProjSheafFunctoriality.tensorGrading_gradedSMul (S := Poly k)
    (grading k) (oddTwist k) (oddTwist k)

/-- The degree-zero localization at the point acts on a fibre at the point through the full
localization of `S` there. -/
public instance fiberModule (M : Type u) [AddCommGroup M] [Module (Poly k) M] :
    Module (HomogeneousLocalization.AtPrime (grading k) (pt k).asHomogeneousIdeal.toIdeal)
      (ProjectiveSpectrum.Proj.ModuleFiber (M := M) (grading k) (pt k)) :=
  Module.compHom _ (algebraMap
    (HomogeneousLocalization.AtPrime (grading k) (pt k).asHomogeneousIdeal.toIdeal)
    (Localization (pt k).asHomogeneousIdeal.toIdeal.primeCompl))

open Stacks.AlgebraicGeometry.ProjStalkGlobalSections in
/-- **The sheaf `S(1)~` vanishes at the point.** A degree-zero fraction of `S(1)` has a
numerator of odd degree over a denominator of even degree, and one of the two is forced to be
zero. -/
public theorem degreeZeroModuleAt_oddTwist_eq_bot :
    degreeZeroModuleAt (grading k) (oddTwist k) (pt k) = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro z ⟨d, m, s, hm, hs, rfl⟩
  by_cases hd : 2 ∣ d
  · have hm' : m ∈ grading k (d + 1) := hm
    rw [grading_eq_bot_of_odd k (n := d + 1) (by omega)] at hm'
    rw [show m = 0 by simpa using hm']
    exact LocalizedModule.zero_mk _
  · refine absurd ?_ (ne_zero_of_mem_primeCompl k s)
    rw [grading_eq_bot_of_odd k hd] at hs
    simpa using hs

open Stacks.AlgebraicGeometry.ProjStalkGlobalSections in
/-- **The sheaf `(S(1) ⊗_S S(1))~` does not vanish at the point**: the fraction `(X ⊗ 1)/1` is
a nonzero degree-zero fraction. -/
public theorem degreeZeroModuleAt_tensorTwist_ne_bot :
    degreeZeroModuleAt (grading k) (tensorTwist k) (pt k) ≠ ⊥ := by
  have hx : xvar k ∈ oddTwist k 1 := by
    change xvar k ∈ ProjectiveSpectrum.Proj.integerGrading (grading k) ((2 : ℕ) : ℤ)
    rw [ProjectiveSpectrum.Proj.integerGrading_natCast,
      ProjectiveSpectrum.Proj.mem_homogeneousSubmodule]
    exact xvar_mem k
  have h1 : (1 : Poly k) ∈ oddTwist k (-1) := by
    change (1 : Poly k) ∈ ProjectiveSpectrum.Proj.integerGrading (grading k) ((0 : ℕ) : ℤ)
    rw [ProjectiveSpectrum.Proj.integerGrading_natCast,
      ProjectiveSpectrum.Proj.mem_homogeneousSubmodule]
    simpa using SetLike.one_mem_graded (grading k)
  have hmem : LocalizedModule.mk (xvar k ⊗ₜ[Poly k] (1 : Poly k))
      (1 : (pt k).asHomogeneousIdeal.toIdeal.primeCompl) ∈
      degreeZeroModuleAt (grading k) (tensorTwist k) (pt k) :=
    Submodule.subset_span
      ⟨0, _, 1, tmul_mem_tensorGrading (oddTwist k) (oddTwist k) (by norm_num) hx h1,
        by simpa using SetLike.one_mem_graded (grading k), rfl⟩
  intro hbot
  rw [hbot, Submodule.mem_bot, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hmem
  obtain ⟨u, hu⟩ := hmem
  simp only [Submonoid.smul_def, one_smul, smul_zero] at hu
  have hu' : (u : Poly k) * xvar k = 0 := by
    have hlid := congrArg (fun z => (TensorProduct.lid (Poly k) (Poly k)) z) hu
    simpa only [map_smul, TensorProduct.lid_tmul, smul_eq_mul, mul_one, map_zero] using hlid
  rcases mul_eq_zero.mp hu' with h | h
  · exact ne_zero_of_mem_primeCompl k u h
  · exact MvPolynomial.X_ne_zero 0 h

/-! ### The sheaf-level conclusion -/

/-- A tensor product whose left factor vanishes vanishes. -/
local instance subsingletonTensorProductOfLeft {R : Type*} [CommRing R] {A B : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [Subsingleton A] :
    Subsingleton (A ⊗[R] B) := by
  have h : ∀ z : A ⊗[R] B, z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul m n => rw [Subsingleton.elim m 0, TensorProduct.zero_tmul]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact ⟨fun a b => by rw [h a, h b]⟩

open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
  Stacks.AlgebraicGeometry.ProjStalkGlobalSections in
/-- **Stacks Project, Tag 01ML.** The canonical morphism of Tag 01MK,
`M̃ ⊗_{𝒪} Ñ ⟶ (M ⊗_S N)~`, is not an isomorphism in general: for `S = k[X]` with `deg X = 2`
and `M = N = S(1)` its source has vanishing stalk at the only point of `Proj(S)` while its
target does not.

An isomorphism of sheaves of modules is bijective on every stalk; the stalk of the source is
the tensor product of the stalks of `M̃` and `Ñ` by Tag 01CB, and the stalk of `M̃` is zero. -/
public theorem not_isIso_associatedModuleSheafTensorMap :
    ¬ IsIso (associatedModuleSheafTensorMap (grading k) (oddTwist k) (oddTwist k)) := by
  intro hiso
  set X := (AlgebraicGeometry.Proj (grading k)).toRingedSpace
  set F := ProjectiveSpectrum.Proj.associatedModuleSheaf (grading k) (oddTwist k)
  set T := ProjectiveSpectrum.Proj.associatedModuleSheaf (grading k) (tensorTwist k)
  have hsubBot : Subsingleton (degreeZeroModuleAt (grading k) (oddTwist k) (pt k)) := by
    rw [degreeZeroModuleAt_oddTwist_eq_bot k]
    infer_instance
  have hsubF : Subsingleton (grpStalk X F.val (pt k)) :=
    (associatedModuleSheafStalkEquiv (grading k) (oddTwist k) (pt k)).toEquiv.subsingleton
  have := hsubF
  have hsubTensor : Subsingleton (grpStalk X
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj F).obj F).val
      (pt k)) :=
    (tensorStalkIso X (pt k) F F).toEquiv.subsingleton
  have hbij := @Stacks.SheafOfModules.bijective_stalkMapL_of_isIso _ _ _
    (associatedModuleSheafTensorMap (grading k) (oddTwist k) (oddTwist k)) hiso (pt k)
  have hsubT : Subsingleton (associatedModuleSheafStalk (grading k) (tensorTwist k) (pt k)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hbij.surjective a
    obtain ⟨b', rfl⟩ := hbij.surjective b
    exact congrArg _ (hsubTensor.elim a' b')
  refine degreeZeroModuleAt_tensorTwist_ne_bot k ?_
  have hsubTarget : Subsingleton (degreeZeroModuleAt (grading k) (tensorTwist k) (pt k)) :=
    (associatedModuleSheafStalkEquiv (grading k) (tensorTwist k) (pt k)).symm.toEquiv.subsingleton
  refine (Submodule.eq_bot_iff _).mpr fun z hz => ?_
  exact congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ :
    degreeZeroModuleAt (grading k) (tensorTwist k) (pt k)) 0)

end Stacks.EvenWeightProj

end
