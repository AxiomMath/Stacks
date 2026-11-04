module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.InfinitesimalNeighbourhood.NeighbourhoodOrder

/-!
# A locally Noetherian formal algebraic space is a colimit of thickenings of algebraic spaces

**Stacks 0GHM.** Let `X` be a locally Noetherian formal algebraic space over `S`. Then
`X = colim X_n` for a system `X_1 ⟶ X_2 ⟶ X_3 ⟶ ⋯` of finite order thickenings of locally
Noetherian algebraic spaces over `S`, where `X_1 = X_red` and `X_n` is the `n`th infinitesimal
neighbourhood of `X_1` in `X_m` for all `m ≥ n`.

The system is indexed from `0` here: the `k`-th term is `X_{k+1}`, the subsheaf of `X` of
sections `t` over affine objects `T` with `K(t)^(k+1) = 0`, where `K(t)` is the ideal of
`T ×_X X_red ⟶ T` (`AlgebraicGeometry.FormalSpace.reductionNeighbourhood`). The Noetherian affine
case is `AlgebraicGeometry.FormalSpace.exists_finiteOrderThickening_presentation_formalSpectrum`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_infinitesimalNeighbourhood_presentation`:
  **Stacks 0GHM**.

## References

* [Stacks Project, Tag 0GHM](https://stacks.math.columbia.edu/tag/0GHM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0GHM.** Let `X` be a locally Noetherian formal algebraic space over `S`. Then `X` is
the colimit of a system `E_0 ⟶ E_1 ⟶ E_2 ⟶ ⋯` (the source's `X_1 ⟶ X_2 ⟶ ⋯`, shifted by one) of
locally Noetherian algebraic spaces over `S` such that

* `E_0 ⟶ X` is the reduction of `X`;
* each transition `E_n ⟶ E_m` (`n ≤ m`) is a finite order thickening: every base change of it
  along a scheme `T ⟶ E_m` is a closed immersion whose ideal sheaf has vanishing `(m+1)`st
  power;
* `E_n` is the `n`th infinitesimal neighbourhood of `E_0` in `E_m`: for every affine `T` and
  `t ∈ E_m(T)`, if `K` is the ideal of `T` cutting out `T ×_{E_m} E_0` (read on affine objects
  `T' ⟶ T`), then `T ×_{E_m} E_n` is cut out by `K^(n+1)`. -/
theorem exists_infinitesimalNeighbourhood_presentation (X : FppfSheaf B S hS)
    (hX : IsLocallyNoetherian B S hS X) :
    ∃ (E : ℕ ⥤ FppfSheaf B S hS) (c : E ⟶ (Functor.const ℕ).obj X),
      Nonempty (IsColimit (Cocone.mk X c)) ∧
      (∀ n, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (E.obj n).obj) ∧
      (∀ n, Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (E.obj n).obj
        (fun T : Scheme.{u} => _root_.AlgebraicGeometry.IsLocallyNoetherian T)) ∧
      IsReduction B S hS X (E.obj 0) (c.app 0) ∧
      (∀ ⦃n m : ℕ⦄ (h : n ≤ m), Space.HasSchemePropertyULift.{u + 1} B S hS
        (fun _ _ f => Stacks.Thickenings.IsNthOrderThickening m f) (E.map (homOfLE h)).hom) ∧
      (∀ ⦃n m : ℕ⦄ (h : n ≤ m) (T : BigFppfOver B S hS),
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        ∀ (t : (E.obj m).obj.obj (op T)) (K : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)),
          (∀ (T' : BigFppfOver B S hS) (g : T' ⟶ T),
            IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
            ((∃ r, (E.map (homOfLE (Nat.zero_le m))).hom.app (op T') r =
                (E.obj m).obj.map g.op t) ↔
              K ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map g).appTop.hom)) →
          ∀ (T' : BigFppfOver B S hS) (g : T' ⟶ T),
            IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
            ((∃ r, (E.map (homOfLE h)).hom.app (op T') r = (E.obj m).obj.map g.op t) ↔
              K ^ (n + 1) ≤ RingHom.ker ((BigFppfOver.toScheme B S hS).map g).appTop.hom)) := by
  obtain ⟨Wred, i, hred⟩ := exists_isReduction_of_isFormalAlgebraicSpace B S hS X hX.1
  refine ⟨reductionNeighbourhoodDiagram i, (reductionNeighbourhoodCocone i).ι,
    ⟨isColimit_reductionNeighbourhoodCocone hX hred⟩,
    fun n => isAlgebraicSpaceULift_reductionNeighbourhood hX hred n,
    fun n => hasEtaleLocalPropertyULift_isLocallyNoetherian_reductionNeighbourhood hX hred n,
    isReduction_reductionNeighbourhood_zero hX hred,
    fun n m h => hasSchemePropertyULift_isNthOrderThickening_homOfLe hX hred h,
    fun n m h T hT t K hK T' g hT' => ?_⟩
  have := hT
  exact reductionNeighbourhood_isInfinitesimalNeighbourhood hred h t K hK T' g hT'

end AlgebraicGeometry.FormalSpace

end
