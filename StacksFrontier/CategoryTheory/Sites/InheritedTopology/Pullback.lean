module

import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.CategoryTheory.FiberedInGroupoids
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs


/-! # Images of pullback squares under a functor fibred in groupoids

A functor fibred in groupoids `q : 𝒴 ⥤ 𝒞` preserves pullback squares (Stacks,
Categories Lemma 4.35.15). This is what lets the overlaps of a covering family of the
inherited topology be pushed down to genuine fibre products in the base site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} {𝒴 : Type u₃} [Category.{v₁} 𝒞] [Category.{v₃} 𝒴]

/-- Every arrow `m : T ⟶ q.obj W` is the image of an arrow `μ` of `𝒴`, up to an `eqToHom`. -/
private lemma IsFiberedInGroupoids.exists_map_eq_eqToHom_comp {q : 𝒴 ⥤ 𝒞}
    (hq : q.IsFiberedInGroupoids) {W : 𝒴} {T : 𝒞} (m : T ⟶ q.obj W) :
    ∃ (Z : 𝒴) (μ : Z ⟶ W) (h : q.obj Z = T), q.map μ = eqToHom h ≫ m := by
  obtain ⟨Z, μ, hμ⟩ := hq.exists_lift m W rfl
  exact ⟨Z, μ, IsHomLift.domain_eq q m μ, by simpa using IsHomLift.fac' q m μ⟩

/-- If `μ` lies over `m` and `m ≫ q.map p = a`, then `μ ≫ p` lies over `a`. -/
private lemma isHomLift_eqToHom_comp_map {q : 𝒴 ⥤ 𝒞} {Z W V : 𝒴} {T : 𝒞} {μ : Z ⟶ W}
    {m : T ⟶ q.obj W} (h : q.obj Z = T) (hμ : q.map μ = eqToHom h ≫ m) (p : W ⟶ V)
    {a : T ⟶ q.obj V} (hm : m ≫ q.map p = a) : q.IsHomLift (eqToHom h ≫ a) (μ ≫ p) := by
  refine IsHomLift.of_commSq q _ _ rfl rfl ⟨?_⟩
  simp [q.map_comp, hμ, ← hm]

/-- For a functor fibred in groupoids, arrows into the image of a pullback apex agree once
they agree after the images of both projections. -/
private theorem IsFiberedInGroupoids.map_hom_ext {q : 𝒴 ⥤ 𝒞} (hq : q.IsFiberedInGroupoids)
    {U Vi Vj W : 𝒴} {fi : Vi ⟶ U} {fj : Vj ⟶ U} {pi : W ⟶ Vi} {pj : W ⟶ Vj}
    (hpb : IsPullback pi pj fi fj) {T : 𝒞} {m m' : T ⟶ q.obj W}
    (hi : m ≫ q.map pi = m' ≫ q.map pi) (hj : m ≫ q.map pj = m' ≫ q.map pj) : m = m' := by
  obtain ⟨Z, μ, hZ, hmμ⟩ := hq.exists_map_eq_eqToHom_comp m
  have : q.IsHomLift ((eqToHom hZ ≫ m') ≫ q.map pi) (μ ≫ pi) := by
    rw [Category.assoc]
    exact isHomLift_eqToHom_comp_map hZ hmμ pi hi
  obtain ⟨μ', ⟨hμ'lift, hμ'fac⟩, _⟩ :=
    (hq.isStronglyCartesian pi).universal_property' (φ := pi) (eqToHom hZ ≫ m') (μ ≫ pi)
  have hpi_eq : μ ≫ pi = μ' ≫ pi := hμ'fac.symm
  have hmμ' : q.map μ' = eqToHom hZ ≫ m' := by
    simpa using IsHomLift.fac' q (eqToHom hZ ≫ m') μ'
  have hpj_eq : μ ≫ pj = μ' ≫ pj := by
    have hcj := hq.isStronglyCartesian fj
    have hμpj := isHomLift_eqToHom_comp_map hZ hmμ pj hj
    have hμ'pj := isHomLift_eqToHom_comp_map hZ hmμ' pj rfl
    apply IsStronglyCartesian.ext q (q.map fj) fj (g := eqToHom hZ ≫ m' ≫ q.map pj)
    rw [Category.assoc, Category.assoc, ← hpb.w, ← Category.assoc, ← Category.assoc, hpi_eq]
  have hqeq := congrArg q.map (hpb.hom_ext hpi_eq hpj_eq)
  rw [hmμ, hmμ'] at hqeq
  exact (cancel_epi (eqToHom hZ)).mp hqeq

/-- For a functor fibred in groupoids, a cone over the image of a pullback cospan factors
through the image of the pullback apex. -/
private theorem IsFiberedInGroupoids.exists_map_lift {q : 𝒴 ⥤ 𝒞} (hq : q.IsFiberedInGroupoids)
    {U Vi Vj W : 𝒴} {fi : Vi ⟶ U} {fj : Vj ⟶ U} {pi : W ⟶ Vi} {pj : W ⟶ Vj}
    (hpb : IsPullback pi pj fi fj) {T : 𝒞} (a : T ⟶ q.obj Vi) (b : T ⟶ q.obj Vj)
    (hab : a ≫ q.map fi = b ≫ q.map fj) :
    ∃ ℓ : T ⟶ q.obj W, ℓ ≫ q.map pi = a ∧ ℓ ≫ q.map pj = b := by
  obtain ⟨Z, α, hZ, hmα⟩ := hq.exists_map_eq_eqToHom_comp a
  have hlift_afi : q.IsHomLift ((eqToHom hZ ≫ b) ≫ q.map fj) (α ≫ fi) := by
    rw [Category.assoc, ← hab]
    exact isHomLift_eqToHom_comp_map hZ hmα fi rfl
  obtain ⟨β, ⟨hβlift, hβfac⟩, _⟩ :=
    (hq.isStronglyCartesian fj).universal_property' (φ := fj) (eqToHom hZ ≫ b) (α ≫ fi)
  have hmβ : q.map β = eqToHom hZ ≫ b := by simpa using IsHomLift.fac' q (eqToHom hZ ≫ b) β
  refine ⟨eqToHom hZ.symm ≫ q.map (hpb.lift α β hβfac.symm), ?_, ?_⟩
  · rw [Category.assoc, ← q.map_comp, hpb.lift_fst, hmα]
    simp
  · rw [Category.assoc, ← q.map_comp, hpb.lift_snd, hmβ]
    simp

/-- **Stacks, Categories Lemma 4.35.15.** A functor fibred in groupoids carries a
pullback square of `𝒴` to a pullback square of `𝒞`.

The universal property must be checked at an arbitrary apex `T : 𝒞`, not necessarily in
the image of `q`: the test cone is lifted into `𝒴` using that `q` is fibred in
groupoids, factored through the `𝒴`-pullback by the universal property of the strongly
cartesian `fi` and `fj`, and pushed back down. -/
theorem IsFiberedInGroupoids.isPullback_map {q : 𝒴 ⥤ 𝒞} (hq : q.IsFiberedInGroupoids)
    {U Vi Vj W : 𝒴} (fi : Vi ⟶ U) (fj : Vj ⟶ U)
    (pi : W ⟶ Vi) (pj : W ⟶ Vj)
    (hpb : IsPullback pi pj fi fj) :
    IsPullback (q.map pi) (q.map pj) (q.map fi) (q.map fj) := by
  have hw : q.map pi ≫ q.map fi = q.map pj ≫ q.map fj := by
    rw [← q.map_comp, ← q.map_comp, hpb.w]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => (hq.exists_map_lift hpb s.fst s.snd s.condition).choose)
    (fun s => (hq.exists_map_lift hpb s.fst s.snd s.condition).choose_spec.1)
    (fun s => (hq.exists_map_lift hpb s.fst s.snd s.condition).choose_spec.2)
    fun s m h₁ h₂ => hq.map_hom_ext hpb
      (h₁.trans (hq.exists_map_lift hpb s.fst s.snd s.condition).choose_spec.1.symm)
      (h₂.trans (hq.exists_map_lift hpb s.fst s.snd s.condition).choose_spec.2.symm))

end CategoryTheory.Functor
