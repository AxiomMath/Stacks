module

public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackLocus
public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition

/-!
# Open and closed numerical conditions read on the points of an algebraic space

The numerical invariants `χ_i` of Situation 0DNC may be defined on the points `|T|` of the test
scheme `T` read as an algebraic space, that is on the points of the represented presheaf, rather
than on the underlying topological space of the scheme `T`. The two are identified by the
homeomorphism of Stacks 03BX, naturally in `T`, through
`AlgebraicGeometry.Space.CoherentSituation.schemePointsFunction`. Along that identification, the
criteria for a numerical condition to cut out an open and closed substack of `Coh_{X/Y}` hold for
a family of functions on the points of the represented presheaves, compatible with the maps of
points induced by the morphisms of `Coh_{X/Y}`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isOpenAndClosedCondition_of_isClopen_points`: a
  numerical condition read on points is open and closed as soon as its loci are.
* `AlgebraicGeometry.Space.CoherentSituation.isOpenAndClosedCondition_of_locally_factors_points`:
  and this holds when the family factors near every point through a locally Noetherian scheme.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

namespace CoherentSituation

/-- **A numerical condition read on points is open and closed as soon as its loci are.** Let
`χ` attach to every object `A` of `Coh_{X/Y}` a family of functions on the points of the
represented presheaf of its test scheme, compatible with the maps of points induced by the
morphisms of `Coh_{X/Y}`. If on every object the locus where all `χ_A i` take the prescribed
values is open and closed, then the condition "`χ_A i t = c i` for all `i` and all `t`" cuts out
an open and closed substack. -/
theorem isOpenAndClosedCondition_of_isClopen_points {ι : Type*} {β : Type*}
    (χ : ∀ A : CoherentObject D, ι → points B S hS (yoneda.obj A.T.left) → β) (c : ι → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : ι)
      (t : points B S hS (yoneda.obj A'.T.left)),
      χ A' i t = χ A i (pointsMap B S hS (yoneda.obj A'.T.left) (yoneda.map φ.base.left) t))
    (hclopen : ∀ A : CoherentObject D,
      IsClopen {t : points B S hS (yoneda.obj A.T.left) | ∀ i, χ A i t = c i}) :
    IsOpenAndClosedCondition D fun A => ∀ i t, χ A i t = c i := by
  have h := isOpenAndClosedCondition_of_isClopen (schemePointsFunction χ) c
    (schemePointsFunction_hom hχ)
    fun A => (hclopen A).preimage (schemePointsHomeomorph B S hS A.T.left).symm.continuous
  simpa only [forall_schemePointsFunction_eq_iff] using h

/-- **The Noetherian reduction, read on points.** Let `χ` be as in
`AlgebraicGeometry.Space.CoherentSituation.isOpenAndClosedCondition_of_isClopen_points`. Suppose
that near every point `t` of every object `A` there are an open map `p : X' → |T_A|` hitting `t`
at `t'`, a locally Noetherian scheme `T₀`, a map `g : X' → T₀` continuous at `t'` and locally
constant functions `χ₀ i` on `T₀` with `χ_A i ∘ p = χ₀ i ∘ g` near `t'`. Then the condition
"`χ_A i t = c i` for all `i` and all `t`" cuts out an open and closed substack. -/
theorem isOpenAndClosedCondition_of_locally_factors_points {ι : Type*} {β : Type*}
    (χ : ∀ A : CoherentObject D, ι → points B S hS (yoneda.obj A.T.left) → β) (c : ι → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : ι)
      (t : points B S hS (yoneda.obj A'.T.left)),
      χ A' i t = χ A i (pointsMap B S hS (yoneda.obj A'.T.left) (yoneda.map φ.base.left) t))
    (hfac : ∀ (A : CoherentObject D) (t : points B S hS (yoneda.obj A.T.left)), ∃ (X' : Type u)
      (_ : TopologicalSpace X') (p : X' → points B S hS (yoneda.obj A.T.left)) (t' : X'),
        p t' = t ∧ IsOpenMap p ∧
        ∃ V ∈ 𝓝 t', ∃ (T₀ : Scheme.{u}) (_ : IsLocallyNoetherian T₀) (g : X' → T₀)
          (χ₀ : ι → T₀ → β), ContinuousAt g t' ∧ (∀ i, IsLocallyConstant (χ₀ i)) ∧
            ∀ i, ∀ y ∈ V, χ A i (p y) = χ₀ i (g y)) :
    IsOpenAndClosedCondition D fun A => ∀ i t, χ A i t = c i := by
  refine isOpenAndClosedCondition_of_isClopen_points χ c hχ fun A => ?_
  refine isClopen_setOf_forall_eq_of_locally_factors (fun t => ?_) c
  obtain ⟨X', _, p, t', hpt, hp, V, hV, T₀, hT₀, g, χ₀, hg, hχ₀, hfac⟩ := hfac A t
  exact ⟨X', inferInstance, p, t', hpt, hp, V, hV, T₀, inferInstance,
    TopologicalSpace.IsLocallyNoetherianSpace.locallyConnectedSpace T₀
      (isLocallyNoetherianSpace_of_isLocallyNoetherian T₀), g, χ₀, hg, hχ₀, hfac⟩

end CoherentSituation

end AlgebraicGeometry.Space

end
