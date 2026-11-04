module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ConnectedComponents
public import StacksFrontier.RingTheory.Smooth.StandardSmoothProperties

/-!
# A smooth morphism has constant relative dimension on each connected component

Let `f : X ⟶ Y` be a smooth morphism of schemes. Near every point of `X` the morphism is given by
a standard smooth algebra, and the dimension of the fibre through every point of such a chart is
the number of variables minus the number of relations of the chart (Stacks 02K0). So the
function `x ↦ dim_x(X_{f(x)})` is locally constant on `X`, hence constant on every connected
component of `X`, and the restriction of `f` to a connected component `X_i` of `X`, landing in
the connected component of `Y` containing its image, has relative dimension equal to that
constant in the sense of Stacks 02NJ.

This is what lets the flat pullback class `f^*` of Stacks 0B78, which is defined for a flat
morphism of fixed relative dimension, be read as an element of the completed bivariant group
`A^*(X ⟶ Y)^∧` of Stacks 0FE0 for an arbitrary smooth morphism `f`: the completed group is a
product over the connected components of `X`.

## Main results

* `AlgebraicGeometry.exists_fiberDimensionAt_eq_of_smooth` — the dimension of the fibre through a
  point of the source is constant, and a natural number, on a neighbourhood of every point.
* `AlgebraicGeometry.Scheme.Hom.smoothComponentDimension` — the relative dimension of a smooth
  morphism on a connected component of its source.
* `AlgebraicGeometry.Scheme.Hom.relativeDimension_resConnectedComponent_of_smooth` — the
  restriction of a smooth morphism to a connected component has that relative dimension.

## References

* [Stacks Project, Tag 02K0](https://stacks.math.columbia.edu/tag/02K0)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 0B78](https://stacks.math.columbia.edu/tag/0B78)
* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- On the source of a standard smooth chart of `f`, the dimension of the fibre through every
point is the number of variables minus the number of relations of the chart. -/
theorem fiberDimensionAt_eq_of_isStandardSmooth_appLE {U : Y.Opens} (hU : IsAffineOpen U)
    {V : X.Opens} (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (hstd : (f.appLE U V e).hom.IsStandardSmooth) :
    ∃ n : ℕ, ∀ y ∈ V, topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) = (n : WithBot ℕ∞) := by
  classical
  let A := ToType Γ(Y, U)
  let B := ToType Γ(X, V)
  let : Algebra A B := (f.appLE U V e).hom.toAlgebra
  have hs : Algebra.IsStandardSmooth A B := hstd
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hs.out
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype σ := Fintype.ofFinite σ
  refine ⟨Nat.card ι - Nat.card σ, fun y hyV => ?_⟩
  let g : Spec (.of B) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (f.appLE U V e).hom)
  let j : Spec (.of B) ⟶ X := hV.fromSpec
  let i : Spec (.of A) ⟶ Y := hU.fromSpec
  have : IsOpenImmersion j := hV.isOpenImmersion_fromSpec
  have : IsOpenImmersion i := hU.isOpenImmersion_fromSpec
  let q : Spec (.of B) := hV.primeIdealOf ⟨y, hyV⟩
  let : P.toPresentation.IsRelativeGlobalCompleteIntersection :=
    P.isRelativeGlobalCompleteIntersection
  rw [← show j q = y from hV.fromSpec_primeIdealOf ⟨y, hyV⟩]
  exact (fiberDimensionAt_eq_of_open_square j f g i
    (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm q).symm.trans
    (fiberDimensionAt_eq_card_sub_card P.toPresentation q)

/-- **The fibre dimension of a smooth morphism is locally constant.** Every point of the source
has an open neighbourhood on which the dimension of the fibre through each point is one and the
same natural number. -/
theorem exists_fiberDimensionAt_eq_of_smooth [Smooth f] (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V) (n : ℕ),
      ∀ y ∈ V, topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) = (n : WithBot ℕ∞) := by
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := Smooth.exists_isStandardSmooth f x
  exact ⟨V, hxV, fiberDimensionAt_eq_of_isStandardSmooth_appLE f hU hV e hstd⟩

/-- The dimension of the fibre through a point of the source of a smooth morphism, as a function
on the source, is locally constant. -/
theorem isLocallyConstant_fiberDimensionAt_of_smooth [Smooth f] :
    IsLocallyConstant fun x : X => topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  obtain ⟨V, hxV, n, hn⟩ := exists_fiberDimensionAt_eq_of_smooth f x
  exact ⟨V, V.2, hxV, fun y hy => (hn y hy).trans (hn x hxV).symm⟩

/-- A morphism `g : P ⟶ Y'` sitting in a commuting square of open immersions over `f : X ⟶ Y`
has relative dimension `d` as soon as the fibre of `f` through the image of every point of `P`
has dimension `d` there. -/
theorem relativeDimension_of_open_square {P X Y' Y : Scheme.{u}} (j : P ⟶ X) (f : X ⟶ Y)
    (g : P ⟶ Y') (i : Y' ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion i] [LocallyOfFiniteType g]
    (h : j ≫ f = g ≫ i) {d : ℕ}
    (hd : ∀ x : P, topologicalKrullDimAt (f.fiber (f (j x))) (f.asFiber (j x)) =
      (d : WithBot ℕ∞)) :
    RelativeDimension g d := by
  intro s hs
  have hFT : LocallyOfFiniteType (g.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (Limits.pullback.snd g (Y'.fromSpecResidueField s))
    infer_instance
  have hlocal : ∀ w : g.fiber s, topologicalKrullDimAt (g.fiber s) w = (d : WithBot ℕ∞) := by
    intro w
    rw [← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι g s w,
      fiberDimensionAt_eq_of_open_square j f g i h]
    exact hd _
  refine ⟨@equidimensional_of_topologicalKrullDimAt_eq _ _ (g.fiber s)
    (g.fiberToSpecResidueField s) hFT _ hlocal, ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hloc : ∀ w : g.fiber s, localKrullDim (g.fiber s) w = (d : WithBot ℕ∞) := fun w ↦ by
    rw [← topologicalKrullDimAt_eq_localKrullDim, hlocal]
  simp_rw [hloc]
  have : Nonempty (g.fiber s) := hs
  exact iSup_const

namespace Scheme.Hom

variable [LocallyConnectedSpace X] [LocallyConnectedSpace Y]

/-- **The relative dimension of a smooth morphism on a connected component** `X_i` of its source:
the dimension of the fibre through a chosen point of `X_i`, which is a natural number. -/
def smoothComponentDimension [Smooth f] (i : ConnectedComponents X) : ℕ :=
  (exists_fiberDimensionAt_eq_of_smooth f
    (ConnectedComponents.surjective_coe i).choose).choose_spec.choose_spec.choose

omit [LocallyConnectedSpace Y] in
/-- The dimension of the fibre through every point of a connected component `X_i` of the source
of a smooth morphism is `smoothComponentDimension f i`. -/
theorem fiberDimensionAt_eq_smoothComponentDimension [Smooth f] (i : ConnectedComponents X)
    (y : X) (hy : y ∈ X.connectedComponentOpens i) :
    topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) =
      (f.smoothComponentDimension i : WithBot ℕ∞) := by
  have h := (exists_fiberDimensionAt_eq_of_smooth f
    (ConnectedComponents.surjective_coe i).choose).choose_spec
  rw [smoothComponentDimension, ← h.choose_spec.choose_spec _ h.choose]
  have hmk : ConnectedComponents.mk y = ConnectedComponents.mk
      (ConnectedComponents.surjective_coe i).choose := by
    rw [(ConnectedComponents.surjective_coe i).choose_spec]
    exact hy
  exact (isLocallyConstant_fiberDimensionAt_of_smooth f).apply_eq_of_isPreconnected
    isPreconnected_connectedComponent (ConnectedComponents.coe_eq_coe'.mp hmk)
    mem_connectedComponent

/-- **A smooth morphism has constant relative dimension on each connected component.** The
restriction `X_i ⟶ Y_{a(i)}` of a smooth morphism `f` to a connected component of its source has
relative dimension `smoothComponentDimension f i` in the sense of Stacks 02NJ. -/
theorem relativeDimension_resConnectedComponent_of_smooth [Smooth f] [LocallyOfFiniteType f]
    (i : ConnectedComponents X) :
    RelativeDimension (f.resConnectedComponent i) (f.smoothComponentDimension i) :=
  relativeDimension_of_open_square (X.connectedComponentOpens i).ι f
    (f.resConnectedComponent i) (Y.connectedComponentOpens _).ι
    (f.resConnectedComponent_comp_ι i).symm
    fun y => f.fiberDimensionAt_eq_smoothComponentDimension i _ y.2

end Scheme.Hom

end AlgebraicGeometry

end
