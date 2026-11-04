module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaNotProjective
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.CentreFamily
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.ExceptionalFamily

/-!
# The model facts of Hironaka's example, from the special fibre

`Stacks.Examples.HironakaNotProjective.ModelFacts` lists what the non-projectivity of Hironaka's
threefold needs from the local model, the tower over `𝔸³_k` with centres `(x, y)` and
`(x - y², z)`: a nodal decomposition `A ∪ B` of the fibre over the origin with `A ≅ ℙ¹_k`, and two
constancy statements for Euler characteristics of invertible modules. The two constancy statements
are proved in `./CentreFamily.lean` (the family over the first centre) and
`./ExceptionalFamily.lean` (the exceptional divisor of the second blow-up over the second
centre). This file assembles them: given the nodal decomposition of the special fibre, with `B`
identified with a fibre of the exceptional divisor of the second blow-up, the model facts hold.

## Main results

* `Stacks.Examples.HironakaLocalModel.modelFacts_of_nodal`.

## References

* [Stacks Project, Tag 08J1](https://stacks.math.columbia.edu/tag/08J1)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.TwoStepTower AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.Examples.HironakaConicChart Stacks.Examples.HironakaNotProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Examples.HironakaLocalModel

variable (k : Type u) [Field k]

/-- **The model facts from the nodal decomposition of the special fibre.** Suppose the fibre
`Z_O` of the model tower over the origin is the union of two closed subschemes `V(IA)` and
`V(IB)` meeting in a `k`-rational point, with `V(IA) ≅ ℙ¹_k`, and `V(IB)` is, over the source of
the tower, a fibre of the exceptional divisor of the second blow-up over some `k`-point `o'` of
the second centre. Then the model facts of
`Stacks.Examples.HironakaNotProjective.ModelFacts` hold: the clause `famI` is
`Stacks.Examples.HironakaLocalModel.eulerSum_eq_of_isPullback_modelKPoint` and the clause `famJ`
is `Stacks.Examples.HironakaLocalModel.eulerSum_fibre_strictTower_eq_exceptionalFibre`,
transported to `V(IB)` along the identification. -/
theorem modelFacts_of_nodal
    (h : ∃ (ZO : Scheme.{u}) (qO : ZO ⟶ modelSpace k) (gO : ZO ⟶ Spec (.of k))
      (_ : IsPullback qO gO (modelTower k) (modelKPoint k 0)) (IA IB : ZO.IdealSheafData),
      IA ⊓ IB = ⊥ ∧ IsIso ((IA ⊔ IB).subschemeι ≫ gO) ∧
      (∃ eA : IA.subscheme ≅ AlgebraicGeometry.Proj (polyGrading k 1),
        eA.hom ≫ projToSpecCoeff k 1 = IA.subschemeι ≫ gO) ∧
      ∃ o' : Spec (.of k) ⟶
          (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)).subscheme,
        ∀ {F' : Scheme.{u}}
          (q' : F' ⟶ exceptionalDivisor (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)))
          (g' : F' ⟶ Spec (.of k)),
          IsPullback q' g' (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
            (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))) o' →
          ∃ e : IB.subscheme ≅ F',
            e.hom ≫ q' ≫ (exceptionalIdeal
              (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))).subschemeι =
                IB.subschemeι ≫ qO ∧
              e.hom ≫ g' = IB.subschemeι ≫ gO) :
    ModelFacts k := by
  obtain ⟨ZO, qO, gO, sq, IA, IB, hinf, hsup, ⟨eA, heA⟩, o', hB⟩ := h
  refine ModelFacts.intro ZO qO gO sq IA IB hinf hsup eA heA ?_ ?_
  · intro H _ c hc0 hc1 Z q g hq
    exact eulerSum_eq_of_isPullback_modelKPoint k H c 0 hc0 hc1 rfl rfl q g hq qO gO sq
  · intro H _ d hd0 hd2 hd1 Z q g hq
    obtain ⟨e, he₁, he₂⟩ :=
      hB (pullback.fst _ o') (pullback.snd _ o') (IsPullback.of_hasPullback _ _)
    rw [eulerSum_fibre_strictTower_eq_exceptionalFibre k H d hd0 hd2 hd1 q g hq o'
      (pullback.fst _ o') (pullback.snd _ o') (IsPullback.of_hasPullback _ _)]
    exact (eulerSum_pullback_eq_of_iso k _ _ _ _ e he₁ he₂ H).symm

end Stacks.Examples.HironakaLocalModel

end
