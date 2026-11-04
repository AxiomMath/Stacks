module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.FiniteTrace
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.AxiomsBasic
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteProjectionDeRhamInjective
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosed

/-!
# The input (FIN) of axiom (A6) for Hodge cohomology

The proof of axiom (A6) in Proposition 0FWD (paragraph "Proof of Axiom (A6) for `X` irreducible"),
which Remark 0FWE applies to Hodge cohomology, takes, for `k` algebraically closed of
characteristic zero and `X` irreducible smooth projective of dimension `d` over `k`, a finite
syntomic surjective `f : X ⟶ ℙ^d_k` and uses that `f^*` is injective on the degree-`2d` part of
the cohomology of `ℙ^d_k`. For Hodge cohomology
`H^*_{Hodge}(X/k) = ⨁_n ⨁_{p + q = n} H^q(X, Ω^p_{X/k})` this holds summand by summand: `f_*𝒪_X`
is finite locally free of a constant rank `e ≥ 1`, and the trace on differential forms gives a map
`Θ : H^q(X, Ω^p_{X/k}) ⟶ H^q(ℙ^d_k, Ω^p_{ℙ^d_k/k})` with `Θ ∘ f^* = e`, invertible in `k`.

This is the hypothesis `Stacks.WeilDeRham.FiniteProjectionInjective` of
`Stacks.WeilDeRham.traceAxiom_cycleClass_of_isAlgClosed`, proved here for the data
`Stacks.HodgeWeil.hodgeFirstChernClassData k`.

## Main results

* `Stacks.HodgeWeil.hodge_finiteProjectionInjective`: **(FIN) for Hodge cohomology over an
  algebraically closed field of characteristic zero.**

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace Stacks.HodgeWeil

variable (k : Type u) [Field k]

/-- **(FIN) for Hodge cohomology** (Stacks, Proposition 0FWD, proof of axiom (A6), read for Hodge
cohomology by Remark 0FWE): over an algebraically closed field `k` of characteristic zero, every
irreducible smooth projective `X` of relative dimension `d` has a morphism `f : X ⟶ ℙ^d_k` over
`k` with `f^*` injective on the degree-`2d` part of `H^*_{Hodge}(ℙ^d_k/k)`. -/
theorem hodge_finiteProjectionInjective [IsAlgClosed k] [CharZero k] :
    Stacks.WeilDeRham.FiniteProjectionInjective (hodgeFirstChernClassData k) := by
  intro X d hirr hd
  have : IrreducibleSpace X.obj.left := hirr
  have : Smooth X.obj.hom := SmoothProjectiveScheme.smooth X
  obtain ⟨f₀, hf, hfin, hsurj, hflat, hsyn, -⟩ :=
    Stacks.WeilDeRham.exists_isFinite_syntomic_toProjectiveSpace_of_relativeDimension (k := k)
      (X := X.obj.left) X.obj.hom (SmoothProjectiveScheme.isProjective X) d hd
  have : SmoothOfRelativeDimension d (projToSpecCoeff k d) :=
    smoothOfRelativeDimension_projToSpecCoeff k d
  have : Smooth (projToSpecCoeff k d) := SmoothOfRelativeDimension.smooth d _
  have : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading k d)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff k d)
  have : IrreducibleSpace (AlgebraicGeometry.Proj (polyGrading k d)) :=
    irreducibleSpace_proj k d
  have : PreconnectedSpace (AlgebraicGeometry.Proj (polyGrading k d)) :=
    PreirreducibleSpace.preconnectedSpace _
  have : Nonempty X.obj.left := IrreducibleSpace.toNonempty
  obtain ⟨e, he, hrank⟩ :=
    Stacks.WeilDeRham.exists_pos_isFiniteLocallyFreeOfRank_of_isFinite_flat f₀
  let f : X ⟶ Stacks.WeilDeRham.projectiveSpace k d := homMk f₀ hf
  refine ⟨f, fun a ha h0 => ?_⟩
  obtain ⟨x, rfl⟩ := (mem_hodgeGrade _ _ _ a).1 ha
  change hodgePullbackOf f (DirectSum.of _ _ x) = 0 at h0
  rw [hodgePullbackOf_of] at h0
  have hx := DirectSum.of_injective (β := hodgePiece (formsAlgebras X.obj.hom)) (2 * (d : ℤ))
    (h0.trans (map_zero _).symm)
  have hinj : Function.Injective (hodgePiecePullback f.hom.left X.obj.hom
      (Stacks.WeilDeRham.projectiveSpace k d).obj.hom (𝟙 _) (hodgeSquare_w f) (2 * (d : ℤ))) :=
    (DirectSum.map_injective _).2 fun i =>
      injective_hodgePullback_of_charZero f₀ hsyn e (projToSpecCoeff k d) X.obj.hom
        (hodgeSquare_w f) he i.1.1 i.1.2
  rw [hinj (hx.trans (map_zero _).symm)]
  exact map_zero _

end Stacks.HodgeWeil

end
