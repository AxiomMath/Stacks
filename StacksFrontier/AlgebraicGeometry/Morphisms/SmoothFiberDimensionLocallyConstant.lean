module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothConnectedComponents
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportClopen
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# The fibre dimension of a smooth morphism is locally constant

For a smooth morphism `f : X ⟶ S`, the dimension `dim_x X_{f(x)}` of the fibre at `x` is a
locally constant function of `x`: on a standard smooth chart through `x` the morphism is a
relative global complete intersection, whose fibre dimension at every point of the chart is the
number of variables minus the number of relations ([Stacks, Tag 02K0]).

Consequently, if `S` is the spectrum of a local ring and `f` is moreover universally closed, the
relative dimension of `f` is read off the closed fibre: every point of `X` specializes to a point
of the closed fibre, and a chart through the latter contains the former.

## Main results

* `AlgebraicGeometry.exists_isOpen_fiberDimensionAt_eq_of_smooth`: the fibre dimension is constant
  near each point; local constancy follows
  (`AlgebraicGeometry.isLocallyConstant_fiberDimensionAt_of_smooth`).
* `AlgebraicGeometry.smoothOfRelativeDimension_of_fiberDimensionAt_closedFibre`.
* `AlgebraicGeometry.smoothOfRelativeDimension_zero_or_one`: a smooth proper morphism with
  geometrically connected fibres to the spectrum of a local ring, whose closed fibre has
  dimension at most one, is smooth of relative dimension zero or one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **On a standard smooth chart the fibre dimension is constant.** -/
theorem exists_isOpen_fiberDimensionAt_eq_of_smooth {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]
    (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, ∀ y ∈ V,
      topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) = (n : WithBot ℕ∞) := by
  classical
  obtain ⟨U, hU, V, hV, hxV, hVU, hstd⟩ := Smooth.exists_isStandardSmooth f x
  let A := ToType Γ(S, U)
  let B := ToType Γ(X, V)
  let : Algebra A B := (f.appLE U V hVU).hom.toAlgebra
  let hs : Algebra.IsStandardSmooth A B := hstd.toAlgebra
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  let g : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (f.appLE U V hVU).hom)
  let j : Spec (.of B) ⟶ X := hV.fromSpec
  let i : Spec (.of A) ⟶ S := hU.fromSpec
  have : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
  have : IsOpenImmersion i := hU.isOpenImmersion_fromSpec
  let : P.toPresentation.IsRelativeGlobalCompleteIntersection :=
    P.isRelativeGlobalCompleteIntersection
  refine ⟨V, hxV, Nat.card ι - Nat.card σ, fun y hy => ?_⟩
  let q : Spec (.of B) := hV.primeIdealOf ⟨y, hy⟩
  have hq : j q = y := hV.fromSpec_primeIdealOf ⟨y, hy⟩
  rw [← hq, ← fiberDimensionAt_eq_of_open_square j f g i
    (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU).symm q]
  exact fiberDimensionAt_eq_card_sub_card P.toPresentation q

/-- **Over a local base, the relative dimension of a smooth universally closed morphism is read
off the closed fibre.** If every point of `X` over the closed point of `Spec R` has fibre dimension
`n`, then `f` is smooth of relative dimension `n`. -/
theorem smoothOfRelativeDimension_of_fiberDimensionAt_closedFibre {R : Type u} [CommRing R]
    [IsLocalRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Smooth f] [UniversallyClosed f]
    (n : ℕ) (h : ∀ y : X, f y = IsLocalRing.closedPoint R →
      topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) = (n : WithBot ℕ∞)) :
    SmoothOfRelativeDimension n f := by
  refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f n fun y => ?_
  -- `y` specializes to a point `y'` of the closed fibre
  obtain ⟨y', hy'cl, hy'⟩ : IsLocalRing.closedPoint R ∈ f.base '' closure {y} :=
    (f.isClosedMap _ isClosed_closure).stableUnderSpecialization
      (IsLocalRing.specializes_closedPoint _) ⟨y, subset_closure rfl, rfl⟩
  obtain ⟨V, hy'V, m, hm⟩ := exists_isOpen_fiberDimensionAt_eq_of_smooth f y'
  have hyV : y ∈ V := (specializes_iff_mem_closure.2 hy'cl).mem_open V.2 hy'V
  rw [hm y hyV, ← hm y' hy'V]
  exact h y' hy'

/-- **The fibres of a smooth morphism with geometrically connected fibres are integral.** -/
theorem isIntegral_fiber_of_smooth_of_geometricallyConnected {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] [GeometricallyConnected f] (s : S) : IsIntegral (f.fiber s) := by
  have hs : Smooth (f.fiberToSpecResidueField s) :=
    inferInstanceAs (Smooth (pullback.snd f (S.fromSpecResidueField s)))
  exact @Stacks.Chow.isIntegral_of_connectedSpace_of_smooth (S.residueField s) _ _
    (f.fiberToSpecResidueField s) hs inferInstance

/-- **A smooth proper morphism with geometrically connected fibres to the spectrum of a local
ring, whose closed fibre has dimension at most one, is smooth of relative dimension zero or
one.** The closed fibre is integral, so its dimension at every point is its dimension, which is
`0` or `1`; and the relative dimension is read off the closed fibre. -/
theorem smoothOfRelativeDimension_zero_or_one {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hd : topologicalKrullDim (f.fiber (IsLocalRing.closedPoint R)) ≤ 1) :
    SmoothOfRelativeDimension 0 f ∨ SmoothOfRelativeDimension 1 f := by
  set s := IsLocalRing.closedPoint R
  have hint := isIntegral_fiber_of_smooth_of_geometricallyConnected f
  -- the dimension at a point of the closed fibre is the dimension of the closed fibre
  have hdim : ∀ y : X, f y = s →
      topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) = topologicalKrullDim (f.fiber s) := by
    intro y hy
    have := hint (f y)
    have : LocallyOfFiniteType (f.fiberToSpecResidueField (f y)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd f _))
    rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible
      ((Spec (.of R)).residueField (f y)) (f.fiber (f y)) (f.fiberToSpecResidueField (f y))
      (f.asFiber y), hy]
  -- the dimension of the closed fibre is `0` or `1`
  have := hint s
  have hne : topologicalKrullDim (f.fiber s) ≠ ⊥ := by
    rw [Ne, topologicalKrullDim, Order.krullDim_eq_bot_iff, not_isEmpty_iff]
    obtain ⟨z⟩ := (inferInstance : Nonempty (f.fiber s))
    exact ⟨⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.1 hne
  rw [← he] at hd
  have he1 : e ≤ 1 := by exact_mod_cast hd
  have hetop : e ≠ ⊤ := fun h => by simp [h] at he1
  obtain ⟨m, rfl⟩ := WithTop.ne_top_iff_exists.1 hetop
  have key : SmoothOfRelativeDimension m f :=
    smoothOfRelativeDimension_of_fiberDimensionAt_closedFibre f m fun y hy => by
      rw [hdim y hy, ← he]
      rfl
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (WithTop.coe_le_coe.mp he1) with rfl | rfl
  · exact .inl key
  · exact .inr key

end AlgebraicGeometry

end
