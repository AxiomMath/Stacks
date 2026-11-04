module

import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import StacksCore.CategoryTheory.FiberedInGroupoids

/-!
# Characterization of categories fibred in groupoids (Stacks 003V)

Stacks Tag 003V (Lemma 4.35.2): a functor `p : 𝒮 ⥤ 𝒞` is fibred in groupoids
(the canonical `IsFiberedInGroupoids`, Stacks 003S) **iff** `p` is a fibred
category and every fibre `p.Fiber S` is a groupoid; moreover in that case every
morphism of `𝒮` is strongly cartesian. This file proves that equivalence together
with its two directions, so downstream tags can use the single canonical predicate
instead of re-defining local `IsFibered ∧ fibers-groupoid` shadows.
-/

@[expose] public section

open CategoryTheory Functor

namespace CategoryTheory.Functor.IsFiberedInGroupoids

variable {𝒮 𝒞 : Type*} [Category 𝒮] [Category 𝒞] {p : 𝒮 ⥤ 𝒞}

/-- In a CFG, any lift of a base morphism is strongly cartesian over it. -/
private theorem isStronglyCartesian_of_isHomLift (hp : p.IsFiberedInGroupoids) {R S : 𝒞}
    {a b : 𝒮} (f : R ⟶ S) (φ : a ⟶ b) [IsHomLift p f φ] : p.IsStronglyCartesian f φ := by
  have hdom : p.obj a = R := IsHomLift.domain_eq p f φ
  have hcod : p.obj b = S := IsHomLift.codomain_eq p f φ
  refine ⟨fun {a'} g φ' hlift => ?_⟩
  set g' : p.obj a' ⟶ p.obj a := g ≫ eqToHom hdom.symm with hg'
  have hpφ : p.map φ = eqToHom hdom ≫ f ≫ eqToHom hcod.symm := IsHomLift.fac' p f φ
  have hcomm : g' ≫ p.map φ = p.map φ' := by
    rw [hg', hpφ]
    have := IsHomLift.fac' p (g ≫ f) φ'
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at this ⊢
    simpa [Category.assoc] using this.symm
  obtain ⟨χ, ⟨hχmap, hχcomp⟩, huniq⟩ := hp.unique_lift φ φ' g' hcomm
  refine ⟨χ, ⟨?_, hχcomp⟩, ?_⟩
  · apply IsHomLift.of_fac p g χ rfl hdom
    rw [hχmap, hg']; simp
  · intro ψ ⟨hψlift, hψcomp⟩
    refine huniq ψ ⟨?_, hψcomp⟩
    have := IsHomLift.fac' p g ψ
    rw [hg']; simp only [this]; simp

/-- In a CFG, every morphism is strongly cartesian over its own image. -/
theorem isStronglyCartesian (hp : p.IsFiberedInGroupoids) {x y : 𝒮} (φ : y ⟶ x) :
    p.IsStronglyCartesian (p.map φ) φ :=
  isStronglyCartesian_of_isHomLift hp (p.map φ) φ

/-- In a CFG, any lift of a base morphism is strongly cartesian over it. -/
theorem isStronglyCartesian_homLift (hp : p.IsFiberedInGroupoids) {R S : 𝒞} {a b : 𝒮}
    (f : R ⟶ S) (φ : a ⟶ b) [IsHomLift p f φ] : p.IsStronglyCartesian f φ :=
  isStronglyCartesian_of_isHomLift hp f φ

/-- A category fibred in groupoids is a fibred category. -/
theorem isFibered (hp : p.IsFiberedInGroupoids) : p.IsFibered :=
  IsFibered.of_exists_isStronglyCartesian (fun a R f => by
    obtain ⟨b, φ, hφ⟩ := hp.exists_lift f a rfl
    have := hφ
    exact ⟨b, φ, hp.isStronglyCartesian_homLift f φ⟩)

/-- Each fibre of a category fibred in groupoids is a groupoid. -/
theorem fiber_isGroupoid (hp : p.IsFiberedInGroupoids) (S : 𝒞) :
    IsGroupoid (p.Fiber S) where
  all_isIso {a b} f := by
    set φ0 : (Fiber.fiberInclusion (p := p) (S := S)).obj a ⟶
        (Fiber.fiberInclusion (p := p) (S := S)).obj b := Fiber.fiberInclusion.map f with hφ0
    have := hp.isStronglyCartesian_homLift (𝟙 S) φ0
    have hf : IsIso φ0 := IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 S) φ0
    have hinv : p.IsHomLift (𝟙 S) (@CategoryTheory.inv _ _ _ _ φ0 hf) := by
      simpa using IsHomLift.inv (p := p) (f := 𝟙 S) (φ := φ0)
    refine ⟨⟨⟨@CategoryTheory.inv _ _ _ _ φ0 hf, hinv⟩, ?_, ?_⟩⟩
    · apply Fiber.fiberInclusion.map_injective
      simp only [Functor.map_comp, Functor.map_id]
      change φ0 ≫ @CategoryTheory.inv _ _ _ _ φ0 hf = _
      simp
    · apply Fiber.fiberInclusion.map_injective
      simp only [Functor.map_comp, Functor.map_id]
      change @CategoryTheory.inv _ _ _ _ φ0 hf ≫ φ0 = _
      simp

/-- If `p` is a fibred category whose fibres are groupoids, then **every** morphism is
strongly cartesian over its image (the substantive content of Stacks 003V). -/
theorem everyStronglyCartesian_of_fiberGroupoid [p.IsFibered]
    (hg : ∀ S, IsGroupoid (p.Fiber S)) {x y : 𝒮} (φ : y ⟶ x) :
    p.IsStronglyCartesian (p.map φ) φ := by
  -- chosen strongly cartesian lift of `p.map φ` ending at `x`
  set w : 𝒮 := IsPreFibered.pullbackObj (rfl : p.obj x = p.obj x) (p.map φ) with hw
  set φc : w ⟶ x := IsPreFibered.pullbackMap (rfl : p.obj x = p.obj x) (p.map φ) with hφc
  have : p.IsHomLift (p.map φ) φ := IsHomLift.map φ
  -- factor φ through φc: v : y ⟶ w over 𝟙, with v ≫ φc = φ
  set v : y ⟶ w := IsStronglyCartesian.map p (p.map φ) φc
    (show p.map φ = 𝟙 (p.obj y) ≫ p.map φ by simp) φ with hv
  have hvfac : v ≫ φc = φ := IsStronglyCartesian.fac p (p.map φ) φc _ φ
  have hvlift : p.IsHomLift (𝟙 (p.obj y)) v := IsStronglyCartesian.map_isHomLift p (p.map φ) φc _ φ
  -- v is a morphism of the fibre over `p.obj y`; that fibre is a groupoid, so v is iso
  have hwproj : p.obj w = p.obj y :=
    IsPreFibered.pullbackObj_proj (rfl : p.obj x = p.obj x) (p.map φ)
  let yF : p.Fiber (p.obj y) := ⟨y, rfl⟩
  let wF : p.Fiber (p.obj y) := ⟨w, hwproj⟩
  let vF : yF ⟶ wF := ⟨v, hvlift⟩
  have : IsGroupoid (p.Fiber (p.obj y)) := hg (p.obj y)
  have hvFiso : IsIso vF := IsGroupoid.all_isIso vF
  have : IsIso v := by
    have : IsIso (Fiber.fiberInclusion.map vF) := inferInstance
    simpa [Fiber.fiberInclusion, vF] using this
  -- φ = v ≫ φc with v iso over 𝟙 and φc strongly cartesian
  have : p.IsStronglyCartesian (𝟙 (p.obj y)) v := IsStronglyCartesian.of_isIso p (𝟙 (p.obj y)) v
  have hcomp : p.IsStronglyCartesian (𝟙 (p.obj y) ≫ p.map φ) (v ≫ φc) :=
    IsStronglyCartesian.comp p
  rw [hvfac, Category.id_comp] at hcomp
  exact hcomp

/-- **Reverse direction (Stacks 003V).** A fibred category whose fibres are
groupoids is a category fibred in groupoids. -/
theorem mk' [p.IsFibered] (hg : ∀ S, IsGroupoid (p.Fiber S)) : p.IsFiberedInGroupoids where
  exists_lift {V U} f x hx :=
    ⟨IsPreFibered.pullbackObj hx f, IsPreFibered.pullbackMap hx f, inferInstance⟩
  unique_lift {x y z} φ ψ f hf := by
    have := everyStronglyCartesian_of_fiberGroupoid hg φ
    have : p.IsHomLift (f ≫ p.map φ) ψ := by rw [hf]; exact IsHomLift.map ψ
    obtain ⟨χ, ⟨hχlift, hχcomp⟩, huniq⟩ :=
      IsStronglyCartesian.universal_property p (p.map φ) φ f (f ≫ p.map φ) rfl ψ
    refine ⟨χ, ⟨by simpa using IsHomLift.fac' p f χ, hχcomp⟩, ?_⟩
    intro χ' ⟨hχ'map, hχ'comp⟩
    exact huniq χ' ⟨hχ'map ▸ IsHomLift.map χ', hχ'comp⟩

/-- **Stacks 003V (Lemma 4.35.2).** A functor `p : 𝒮 ⥤ 𝒞` is fibred in groupoids
if and only if it is a fibred category all of whose fibres are groupoids. -/
@[stacks 003V]
theorem iff_isFibered_and_fiber_isGroupoid :
    p.IsFiberedInGroupoids ↔ p.IsFibered ∧ ∀ S, IsGroupoid (p.Fiber S) := by
  constructor
  · intro hp
    exact ⟨hp.isFibered, hp.fiber_isGroupoid⟩
  · rintro ⟨hfib, hg⟩
    have := hfib
    exact mk' hg

end CategoryTheory.Functor.IsFiberedInGroupoids
