module

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
public import Mathlib.CategoryTheory.Comma.Over.Basic

public import StacksCore.CategoryTheory.FiberedInGroupoids

/-!
# Categories fibred in groupoids over a slice category (Stacks 02XT)

If `p : 𝒮 ⥤ 𝒞` is fibred in groupoids and factors through the slice category `Over U = 𝒞/U`
as `p = p' ⋙ Over.forget U`, then the factoring functor `p' : 𝒮 ⥤ Over U` is again fibred in
groupoids.

Both clauses of `Functor.IsFiberedInGroupoids` transfer along `Over.forget U`, for the two
reasons that make the slice category well behaved over its base.

* *Existence of lifts.*  A morphism `f : V ⟶ p'.obj x` of `Over U` is a morphism
  `f.left : V.left ⟶ (p'.obj x).left` of `𝒞` compatible with the structure morphisms, so it can
  be lifted along `p`; what has to be checked is that the resulting object `y` of `𝒮` lies over
  `V` *in `Over U`*, not merely over `V.left` in `𝒞`.  That is forced: `Over.w` applied to
  `p'.map φ` identifies the structure morphism of `p'.obj y` with that of `V`, and an object of
  `Over U` is determined by its underlying object and its structure morphism, since the
  remaining component of the comma-category datum lives in a singleton type.  This last point
  is the private lemma `over_ext_of_left`.
* *Existence and uniqueness of fill-ins.*  `Over.forget U` is faithful, so a commuting triangle
  in `Over U` is the same as a commuting triangle of underlying morphisms in `𝒞`, and the unique
  fill-in produced by `p` is automatically a morphism of `Over U` (`Over.OverMorphism.ext`) and
  is unique as such.

The factorisation is an arbitrary one, given as a hypothesis `p' ⋙ Over.forget U = p` rather
than by construction, so the statement applies to any presentation of `p` as a functor to the
slice category.  No hypothesis on `U` is needed.
-/

@[expose] public section

namespace CategoryTheory.Functor

open CategoryTheory

/-- Object extensionality for `Over U`: an object is determined by its `left` and `hom`,
since `right` lives in a singleton type. -/
private lemma over_ext_of_left {C : Type*} [Category C] {U : C} (A B : Over U)
    (h1 : A.left = B.left) (h2 : A.hom = eqToHom h1 ≫ B.hom) : A = B := by
  obtain ⟨A_left, ⟨_⟩, _⟩ := A
  obtain ⟨B_left, ⟨_⟩, _⟩ := B
  obtain rfl : A_left = B_left := h1
  obtain rfl : _ = _ := by simpa using h2
  rfl

/-- **Stacks 02XT.** If `p : 𝒮 ⥤ 𝒞` is fibred in groupoids and factors through the slice
category `Over U` as `p' ⋙ Over.forget U = p`, then `p' : 𝒮 ⥤ Over U` is fibred in
groupoids: lifts of morphisms of `Over U` and unique fill-ins for `p'` are obtained from those
for `p`, because the structure morphism of a lifted object is forced and `Over.forget U` is
faithful. -/
@[stacks 02XT]
theorem IsFiberedInGroupoids.of_comp_over
    {𝒮 𝒞 : Type*} [Category 𝒮] [Category 𝒞] (U : 𝒞)
    (p : 𝒮 ⥤ 𝒞) (p' : 𝒮 ⥤ Over U)
    (h : p' ⋙ Over.forget U = p) (hp : p.IsFiberedInGroupoids) :
    p'.IsFiberedInGroupoids := by
  subst h
  refine ⟨fun {V W} f x hx ↦ ?_, fun {x y z} φ ψ g hcomm ↦ ?_⟩
  · -- Existence of lifts: lift `f.left` along `p`, then check the `hom` field matches.
    subst hx
    obtain ⟨y, φ, hlift⟩ := hp.exists_lift f.left x rfl
    have hy_left : (p'.obj y).left = V.left :=
      IsHomLift.domain_eq (p' ⋙ Over.forget U) f.left φ
    have hφ : (p'.map φ).left
        = eqToHom hy_left ≫ f.left ≫ eqToHom (rfl : (p'.obj x).left = (p'.obj x).left).symm :=
      IsHomLift.fac' (p' ⋙ Over.forget U) f.left φ
    have hyhom : (p'.obj y).hom = eqToHom hy_left ≫ V.hom := by
      rw [(Over.w (p'.map φ)).symm, hφ]
      simp [Over.w f]
    have hy : p'.obj y = V := over_ext_of_left _ _ hy_left hyhom
    refine ⟨y, φ, IsHomLift.of_fac' p' f φ hy rfl ?_⟩
    apply Over.OverMorphism.ext
    rw [hφ]
    simp only [Over.comp_left]
    rw [show (eqToHom hy : p'.obj y ⟶ V).left = eqToHom hy_left by subst hy; simp]
    simp
  · -- Unique factorization: transport the hypothesis along `Over.forget U`.
    have hcomm' : g.left ≫ (p' ⋙ Over.forget U).map φ = (p' ⋙ Over.forget U).map ψ :=
      congrArg (·.left) hcomm
    obtain ⟨χ, ⟨hχmap, hχcomp⟩, hχunique⟩ := hp.unique_lift φ ψ g.left hcomm'
    exact ⟨χ, ⟨Over.OverMorphism.ext hχmap, hχcomp⟩, fun χ' ⟨h1, h2⟩ ↦
      hχunique χ' ⟨congrArg (·.left) h1, h2⟩⟩

end CategoryTheory.Functor
