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
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs


/-!
# Fibre products in a category fibred in groupoids

Let `p : S ⥤ C` be a category fibred in groupoids, let `gx : x ⟶ y` and `gz : z ⟶ y` be
morphisms of `S`, and assume the fibre product `p(x) ×_{p(y)} p(z)` exists in `C`. Then:

1. the fibre product `x ×_y z` exists in `S`, and
2. for *any* fibre product `x ×_y z` in `S`, with projections `pr₁`, `pr₂`, the object
   `p(x ×_y z)` together with `p(pr₁)` and `p(pr₂)` is a fibre product of
   `p(x) ⟶ p(y) ⟵ p(z)` in `C`; that is, `p` carries the pullback square of `S` to a
   pullback square of `C`.

Fibre products are expressed with `CategoryTheory.IsPullback` and
`CategoryTheory.Limits.HasPullback`.

## Main results

* `CategoryTheory.Functor.IsFiberedInGroupoids.isPullback_of_map_isPullback`: a commuting square
  of `S` whose image under `p` is a pullback square is a pullback square.
* `CategoryTheory.Functor.IsFiberedInGroupoids.hasPullback`: the fibre product `x ×_y z` exists
  in `S`.
* `CategoryTheory.Functor.IsFiberedInGroupoids.map_isPullback`: `p` carries pullback squares of
  `S` over `gx` and `gz` to pullback squares of `C`.

## References

* [Stacks Project, Tag 06N6](https://stacks.math.columbia.edu/tag/06N6)
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]

/-- Two morphisms into the source of a strongly Cartesian morphism `φ` with the same image under
`p` are equal as soon as their composites with `φ` are. -/
private theorem eq_of_map_eq_of_comp_eq (p : S ⥤ C) {a b : S} (φ : a ⟶ b)
    [p.IsStronglyCartesian (p.map φ) φ] {T : S} {u u' : T ⟶ a} (hmap : p.map u' = p.map u)
    (h : u ≫ φ = u' ≫ φ) : u = u' := by
  have : p.IsHomLift (p.map u) u' := by rw [← hmap]; infer_instance
  exact IsStronglyCartesian.ext p (p.map φ) φ (p.map u) h

/-- A category fibred in groupoids reflects fibre products: a commuting square of `S` whose
image under `p` is a pullback square of `C` is itself a pullback square. -/
theorem IsFiberedInGroupoids.isPullback_of_map_isPullback {p : S ⥤ C}
    (hp : p.IsFiberedInGroupoids) {w x y z : S} {pr₁ : w ⟶ x} {pr₂ : w ⟶ z}
    {gx : x ⟶ y} {gz : z ⟶ y} (hw : pr₁ ≫ gx = pr₂ ≫ gz)
    (hC : IsPullback (p.map pr₁) (p.map pr₂) (p.map gx) (p.map gz)) :
    IsPullback pr₁ pr₂ gx gz := by
  have := hp.isStronglyCartesian pr₁
  have := hp.isStronglyCartesian gz
  refine IsPullback.mk' hw ?_ ?_
  · intro T u u' h₁ h₂
    have hmap : p.map u' = p.map u := hC.hom_ext
      (by rw [← p.map_comp, ← p.map_comp, h₁]) (by rw [← p.map_comp, ← p.map_comp, h₂])
    exact eq_of_map_eq_of_comp_eq p pr₁ hmap h₁
  · intro T α β hαβ
    obtain ⟨h, ⟨hhmap, hhcomp⟩, -⟩ := hp.unique_lift pr₁ α
      (hC.lift (p.map α) (p.map β) (by rw [← p.map_comp, ← p.map_comp, hαβ]))
      (hC.lift_fst _ _ _)
    exact ⟨h, hhcomp, eq_of_map_eq_of_comp_eq p gz (by rw [p.map_comp, hhmap, hC.lift_snd])
      (by rw [Category.assoc, ← hw, ← Category.assoc, hhcomp, hαβ])⟩

/-- If the fibre product of `p.map gx` and `p.map gz` exists in `C`, then `gx` and `gz` have a
fibre product in `S` whose image under `p` is a fibre product in `C`. -/
private theorem IsFiberedInGroupoids.exists_isPullback
    (p : S ⥤ C) (hp : p.IsFiberedInGroupoids)
    {x y z : S} (gx : x ⟶ y) (gz : z ⟶ y)
    [Limits.HasPullback (p.map gx) (p.map gz)] :
    ∃ (w : S) (pr1 : w ⟶ x) (pr2 : w ⟶ z),
      IsPullback pr1 pr2 gx gz ∧
      IsPullback (p.map pr1) (p.map pr2) (p.map gx) (p.map gz) := by
  obtain ⟨W, fst, snd, hpb⟩ : ∃ (W : C) (fst : W ⟶ p.obj x) (snd : W ⟶ p.obj z),
      IsPullback fst snd (p.map gx) (p.map gz) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨w, a, hlift⟩ := hp.exists_lift fst x rfl
  have := hlift
  obtain rfl : p.obj w = W := IsHomLift.domain_eq p fst a
  obtain rfl : fst = p.map a := by simpa using IsHomLift.fac p fst a
  obtain ⟨pr2, ⟨hpr2map, hpr2comp⟩, -⟩ :=
    hp.unique_lift gz (a ≫ gx) snd (by rw [p.map_comp]; exact hpb.w.symm)
  have hC : IsPullback (p.map a) (p.map pr2) (p.map gx) (p.map gz) := by
    rw [hpr2map]; exact hpb
  exact ⟨w, a, pr2, hp.isPullback_of_map_isPullback hpr2comp.symm hC, hC⟩

/-- Let `p` be fibred in groupoids and let `gx : x ⟶ y`, `gz : z ⟶ y` be morphisms of `S`. If
the fibre product of `p.map gx` and `p.map gz` exists in `C`, then the fibre product of `gx` and
`gz` exists in `S`. -/
@[stacks 06N6 "(1)"]
theorem IsFiberedInGroupoids.hasPullback
    (p : S ⥤ C) (hp : p.IsFiberedInGroupoids)
    {x y z : S} (gx : x ⟶ y) (gz : z ⟶ y)
    [Limits.HasPullback (p.map gx) (p.map gz)] :
    Limits.HasPullback gx gz := by
  obtain ⟨w, pr1, pr2, hS, -⟩ := IsFiberedInGroupoids.exists_isPullback p hp gx gz
  exact hS.hasPullback

/-- For any fibre product `x ×_y z` in `S`, realized by a pullback square with vertex `P` and
projections `pr₁ : P ⟶ x`, `pr₂ : P ⟶ z`, the image `p.obj P` together with `p.map pr₁` and
`p.map pr₂` is a fibre product of `p.map gx` and `p.map gz` in `C`: `p` carries the pullback
square of `S` to a pullback square of `C`. -/
@[stacks 06N6 "(2)"]
theorem IsFiberedInGroupoids.map_isPullback
    (p : S ⥤ C) (hp : p.IsFiberedInGroupoids)
    {x y z : S} (gx : x ⟶ y) (gz : z ⟶ y)
    [Limits.HasPullback (p.map gx) (p.map gz)]
    {P : S} (pr₁ : P ⟶ x) (pr₂ : P ⟶ z)
    (hP : IsPullback pr₁ pr₂ gx gz) :
    IsPullback (p.map pr₁) (p.map pr₂) (p.map gx) (p.map gz) := by
  obtain ⟨w, pr1, pr2, hS, hSC⟩ := IsFiberedInGroupoids.exists_isPullback p hp gx gz
  set e : P ≅ w := hP.isoIsPullback x z hS
  have einv_fst : e.inv ≫ pr₁ = pr1 := hP.isoIsPullback_inv_fst x z hS
  have einv_snd : e.inv ≫ pr₂ = pr2 := hP.isoIsPullback_inv_snd x z hS
  refine IsPullback.of_iso hSC (p.mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · simpa using (congrArg p.map einv_fst).symm
  · simpa using (congrArg p.map einv_snd).symm
  all_goals simp

end CategoryTheory.Functor
