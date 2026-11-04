module

public import StacksFrontier.AlgebraicGeometry.DevissageColimit.Basic
public import StacksFrontier.AlgebraicGeometry.HighTwistDevissage.Cohomology

/-!
# Two-class descending dévissage in the cohomology of `𝒪_X`-modules

`StacksFrontier/AlgebraicGeometry/DevissageColimit/Basic.lean` proves the two-class descending
dévissage principle for an abstract cohomological δ-functor. This file instantiates it at
`Hⁿ(U, -)`, exactly as
`StacksFrontier/AlgebraicGeometry/HighTwistDevissage/Cohomology.lean` instantiates the one-class
form:

> Let `Q ⊆ P` be classes of `𝒪_X`-modules. If `Hᵖ(U, F) = 0` for every `F` in `P` and every
> `p > e`, if in each positive degree the vanishing of `Hᵖ(U, -)` on `Q` forces it on `P`, and if
> every `F` in `Q` is the quotient term of a short exact sequence `0 → F' → G → F → 0` with `F'`
> in `P` and `G` acyclic over `U` in positive degrees, then `Hᵖ(U, F) = 0` for every `F` in `P`
> and every `p > 0`.

The two classes are what [Stacks, Tag 0EBD] needs: the dévissage sequence of
[Stacks, Tag 01Q3] clause (8) exists only for `F` of finite type, while its kernel is
quasi-coherent and nothing more. The reduction hypothesis is where [Stacks, Tag 01PG] and
Cohomology, Lemma 20.19.1 enter, through
`Stacks.DevissageColimit.isZero_obj_of_colimitPresentation`.

## Main results

* `Stacks.DevissageColimit.isZero_hgroup_of_descending_devissage_of_reduction_of_deltaFunctor`:
  the principle above, from an arbitrary witness of
  `Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor`.
* `Stacks.DevissageColimit.isZero_hgroup_of_descending_devissage_of_reduction`: the same with the
  δ-functor discharged by `Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived`, so
  that the long exact cohomology sequence is no longer a hypothesis. This is the usable form.

## Implementation notes

The degree bookkeeping is the one of
`Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj`: the δ-functor's degree-`0` part
is `Γ(U, -)` rather than `H⁰(U, -)`, so every translation between `IsZero ((D.functor p).obj F)`
and `IsZero (Hgroup R U p F)` is guarded by `0 < p`. The reduction hypothesis is stated only in
positive degrees for the same reason, and that is also the only range in which the engine consumes
it.

No tag attribute is attached: this is an engine for the cohomological tags of Chapter 30 and the
statement of none of them.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 0EBD](https://stacks.math.columbia.edu/tag/0EBD)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u w

namespace Stacks.DevissageColimit

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{w}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} R)]

/-- **Two-class descending dévissage for the cohomology of `𝒪_X`-modules**, from a witness of the
long exact cohomology sequence over `U`.

The dévissage sequence is required only for the smaller class `Q`; its first term is only asked to
lie in the larger class `P`, and the passage from `Q` to `P` in a fixed positive degree is the
hypothesis `hred`. -/
theorem isZero_hgroup_of_descending_devissage_of_reduction_of_deltaFunctor {U : Opens X}
    {D : DeltaFunctor (SheafOfModules.{w} R) AddCommGrpCat}
    (hD : Stacks.CohomologyVanishing.IsCohomologyDeltaFunctor R U D)
    (P Q : SheafOfModules.{w} R → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ F : SheafOfModules.{w} R, P F → IsZero (Hgroup R U p F))
    (hred : ∀ p : ℕ, 0 < p →
      (∀ G : SheafOfModules.{w} R, Q G → IsZero (Hgroup R U p G)) →
      ∀ F : SheafOfModules.{w} R, P F → IsZero (Hgroup R U p F))
    (step : ∀ G : SheafOfModules.{w} R, Q G →
      ∃ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact ∧ S.X₃ = G ∧ P S.X₁ ∧
        ∀ m : ℕ, 0 < m → IsZero (Hgroup R U m S.X₂))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{w} R) (hF : P F) : IsZero (Hgroup R U p F) := by
  refine (Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj R hD hp F).1
    (isZero_obj_of_descending_devissage_of_reduction D P Q e ?_ ?_ ?_ p hp F hF)
  · intro q hq G hG
    exact (Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj R hD (by omega) G).2
      (hbound q hq G hG)
  · intro q hq h G hG
    refine (Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj R hD hq G).2
      (hred q hq (fun Y hY => ?_) G hG)
    exact (Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj R hD hq Y).1 (h Y hY)
  · intro G hG
    obtain ⟨S, hS, hX₃, hP₁, hacyc⟩ := step G hG
    refine ⟨S, hS, hX₃, hP₁, fun m hm => ?_⟩
    exact (Stacks.HighTwistDevissage.isZero_hgroup_iff_isZero_functor_obj R hD hm S.X₂).2
      (hacyc m hm)

variable [HasDerivedCategory (SheafOfModules.{w} R)] [HasDerivedCategory AddCommGrpCat.{w}]

/-- **Two-class descending dévissage for the cohomology of `𝒪_X`-modules**, with the long exact
cohomology sequence discharged by
`Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived`.

If `Hᵖ(U, F) = 0` for every `F` in `P` and every `p > e`, if vanishing on `Q` in a positive degree
forces vanishing on `P` in that degree, and if every `F` in `Q` is the quotient term of a short
exact sequence `0 → F' → G → F → 0` with `F'` in `P` and `Hᵐ(U, G) = 0` for all `m > 0`, then
`Hᵖ(U, F) = 0` for every `F` in `P` and every `p > 0`. -/
theorem isZero_hgroup_of_descending_devissage_of_reduction (U : Opens X)
    (P Q : SheafOfModules.{w} R → Prop) (e : ℕ)
    (hbound : ∀ p : ℕ, e < p → ∀ F : SheafOfModules.{w} R, P F → IsZero (Hgroup R U p F))
    (hred : ∀ p : ℕ, 0 < p →
      (∀ G : SheafOfModules.{w} R, Q G → IsZero (Hgroup R U p G)) →
      ∀ F : SheafOfModules.{w} R, P F → IsZero (Hgroup R U p F))
    (step : ∀ G : SheafOfModules.{w} R, Q G →
      ∃ S : ShortComplex (SheafOfModules.{w} R), S.ShortExact ∧ S.X₃ = G ∧ P S.X₁ ∧
        ∀ m : ℕ, 0 < m → IsZero (Hgroup R U m S.X₂))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{w} R) (hF : P F) : IsZero (Hgroup R U p F) :=
  isZero_hgroup_of_descending_devissage_of_reduction_of_deltaFunctor R
    (Stacks.CohomologyVanishing.isCohomologyDeltaFunctor_rightDerived R U) P Q e hbound hred step
    p hp F hF

end Stacks.DevissageColimit

end
