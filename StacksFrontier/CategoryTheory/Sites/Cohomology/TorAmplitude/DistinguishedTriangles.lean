module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude along a distinguished triangle

Let `(C, O)` be a ringed site, let `T` be a derived tensor product on `D(O)` and let
`K ⟶ L ⟶ M ⟶ K[1]` be a distinguished triangle in `D(O)`. Tor amplitude of two of the three
vertices forces Tor amplitude of the third, in the three combinations of intervals for which
the long exact cohomology sequence of `- ⊗^L_O F[0]` closes up.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_obj₃`: Tor amplitude of `K` in
  `[a + 1, b + 1]` and of `L` in `[a, b]` give Tor amplitude of `M` in `[a, b]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_obj₂`: Tor amplitude of `K` and
  of `M` in `[a, b]` gives Tor amplitude of `L` in `[a, b]`.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_obj₁`: Tor amplitude of `L` in
  `[a + 1, b + 1]` and of `M` in `[a, b]` give Tor amplitude of `K` in `[a + 1, b + 1]`.

## Implementation notes

The only property of the derived tensor product used is that `- ⊗^L_O F[0]` is an exact functor
of triangulated categories, which is the `commShift_left` and `exact_left` data of
`Stacks.SheafOfModules.DerivedTensorProduct`; the three statements are therefore proved by one
application each of the long exact sequence of a homological functor on the image triangle.

## References

* [Stacks Project, Tag 08G2](https://stacks.math.columbia.edu/tag/08G2)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : DerivedTensorProduct.{u, v, w, d} X)

/-- **Stacks 08G2 (1).** In a distinguished triangle `K ⟶ L ⟶ M ⟶ K[1]` of `D(O)`, if `K` has
Tor amplitude in `[a + 1, b + 1]` and `L` has Tor amplitude in `[a, b]`, then `M` has Tor
amplitude in `[a, b]`. -/
@[stacks 08G2 "(1)"]
theorem hasTorAmplitude_obj₃
    (tri : Triangle (RingedSite.DerivedModules.{u, v, w, d} X))
    (htri : tri ∈ distinguishedTriangles) (a b : ℤ)
    (hK : HasTorAmplitude T tri.obj₁ (a + 1) (b + 1))
    (hL : HasTorAmplitude T tri.obj₂ a b) :
    HasTorAmplitude T tri.obj₃ a b := by
  rw [hasTorAmplitude_iff_lt_or_lt] at hK hL ⊢
  intro F i hi
  -- exactness at `H^i(Φ M)` in `H^i(Φ L) ⟶ H^i(Φ M) ⟶ H^{i+1}(Φ K)`
  have hex := (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X)
    0).homologySequence_exact₃ ((T.tensorModule F).mapTriangle.obj tri)
    ((T.tensorModule F).map_distinguished tri htri) i (i + 1) rfl
  refine hex.isZero_X₂ ((hL F i hi).eq_of_src _ _) ?_
  exact (hK F (i + 1) (by omega)).eq_of_tgt _ _

/-- **Stacks 08G2 (2).** In a distinguished triangle `K ⟶ L ⟶ M ⟶ K[1]` of `D(O)`, if `K` and
`M` both have Tor amplitude in `[a, b]`, then so does `L`. -/
@[stacks 08G2 "(2)"]
theorem hasTorAmplitude_obj₂
    (tri : Triangle (RingedSite.DerivedModules.{u, v, w, d} X))
    (htri : tri ∈ distinguishedTriangles) (a b : ℤ)
    (hK : HasTorAmplitude T tri.obj₁ a b)
    (hM : HasTorAmplitude T tri.obj₃ a b) :
    HasTorAmplitude T tri.obj₂ a b := by
  rw [hasTorAmplitude_iff_lt_or_lt] at hK hM ⊢
  intro F i hi
  -- exactness at `H^i(Φ L)` in `H^i(Φ K) ⟶ H^i(Φ L) ⟶ H^i(Φ M)`
  have hex := (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X)
    0).homologySequence_exact₂ ((T.tensorModule F).mapTriangle.obj tri)
    ((T.tensorModule F).map_distinguished tri htri) i
  exact hex.isZero_X₂ ((hK F i hi).eq_of_src _ _) ((hM F i hi).eq_of_tgt _ _)

/-- **Stacks 08G2 (3).** In a distinguished triangle `K ⟶ L ⟶ M ⟶ K[1]` of `D(O)`, if `L` has
Tor amplitude in `[a + 1, b + 1]` and `M` has Tor amplitude in `[a, b]`, then `K` has Tor
amplitude in `[a + 1, b + 1]`. -/
@[stacks 08G2 "(3)"]
theorem hasTorAmplitude_obj₁
    (tri : Triangle (RingedSite.DerivedModules.{u, v, w, d} X))
    (htri : tri ∈ distinguishedTriangles) (a b : ℤ)
    (hL : HasTorAmplitude T tri.obj₂ (a + 1) (b + 1))
    (hM : HasTorAmplitude T tri.obj₃ a b) :
    HasTorAmplitude T tri.obj₁ (a + 1) (b + 1) := by
  rw [hasTorAmplitude_iff_lt_or_lt] at hL hM ⊢
  intro F i hi
  -- exactness at `H^i(Φ K)` in `H^{i-1}(Φ M) ⟶ H^i(Φ K) ⟶ H^i(Φ L)`
  have hex := (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X)
    0).homologySequence_exact₁ ((T.tensorModule F).mapTriangle.obj tri)
    ((T.tensorModule F).map_distinguished tri htri) (i - 1) i (by omega)
  refine hex.isZero_X₂ ?_ ((hL F i hi).eq_of_tgt _ _)
  exact (hM F (i - 1) (by omega)).eq_of_src _ _

end Stacks.SheafOfModules.DerivedTensorProduct

end
