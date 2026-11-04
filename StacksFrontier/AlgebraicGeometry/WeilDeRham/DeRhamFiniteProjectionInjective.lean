module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteProjectionDeRhamInjective
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.TraceAxiomAlgClosed
public import StacksFrontier.AlgebraicGeometry.DeRham.WeilCohomology.DeRhamWeilData

/-!
# The input (FIN) of axiom (A6) for de Rham cohomology

The proof of axiom (A6) for de Rham cohomology in Proposition 0FWD (paragraph "Proof of Axiom (A6)
for `X` irreducible") takes, for `k` algebraically closed of characteristic zero and `X`
irreducible smooth projective of dimension `d` over `k`, a finite syntomic `f : X ⟶ ℙ^d_k` and uses
that `f^* : H^{2d}_{dR}(ℙ^d_k/k) ⟶ H^{2d}_{dR}(X/k)` is injective (the de Rham trace of `f` gives
`Θ ∘ f^* = deg(f)`). This is the hypothesis `Stacks.WeilDeRham.FiniteProjectionInjective` of
`Stacks.WeilDeRham.traceAxiom_cycleClass_of_isAlgClosed`; this file proves it for the de Rham data
`Stacks.DeRhamWeil.deRhamFirstChernClassData k`, from
`Stacks.WeilDeRham.exists_isFinite_syntomic_toProjectiveSpace_deRhamCohomologyTrace`, whose
`ℙ^d_k = Proj k[T₀, …, T_d]` is the `Stacks.WeilDeRham.projectiveSpace k d` of (FIN).

## Main results

* `Stacks.WeilDeRham.injective_pullbackPiece_of_injective`: the pullback of the data in one degree
  is the pullback `Scheme.Hom.deRhamCohomologyPullback` of the abelian realization, read through
  the comparison of realizations, hence injective when the latter is.
* `Stacks.WeilDeRham.deRham_finiteProjectionInjective`: **(FIN) for de Rham cohomology over an
  algebraically closed field of characteristic zero.**

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FLC](https://stacks.math.columbia.edu/tag/0FLC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u

namespace Stacks.WeilDeRham

variable {k : Type u} [Field k]

/-- **The pullback of de Rham cohomology in one degree is injective when its abelian realization
is**: `DeRhamWeil.pullbackPiece f n` is `Scheme.Hom.deRhamCohomologyPullback` conjugated by the
comparison isomorphism of the two realizations of de Rham cohomology. -/
theorem injective_pullbackPiece_of_injective {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) (n : ℤ)
    (h : Function.Injective (Scheme.Hom.deRhamCohomologyPullback ((toScheme k).map f) Y.obj.hom
      X.obj.hom (𝟙 _) (DeRhamWeil.square_w f) n).hom) :
    Function.Injective (DeRhamWeil.pullbackPiece f n) := by
  intro x y hxy
  have e₁ := (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (DeRhamWeil.algebras Y) (DeRhamWeil.differential Y) n).addCommGroupIsoToAddEquiv.symm.injective
  have e₂ := (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
    (DeRhamWeil.algebras X) (DeRhamWeil.differential X) n).addCommGroupIsoToAddEquiv.injective
  exact e₁ (h (e₂ hxy))

variable (k) in
/-- **(FIN) for de Rham cohomology** (Stacks, Proposition 0FWD, proof of axiom (A6)): over an
algebraically closed field `k` of characteristic zero, every irreducible smooth projective `X` of
relative dimension `d` has a morphism `f : X ⟶ ℙ^d_k` over `k` with `f^*` injective on
`H^{2d}_{dR}(ℙ^d_k/k)`. -/
theorem deRham_finiteProjectionInjective [IsAlgClosed k] [CharZero k] :
    FiniteProjectionInjective (DeRhamWeil.deRhamFirstChernClassData k) := by
  intro X d hirr hd
  have := hirr
  obtain ⟨f₀, hf, -, -, -, e, -, -, hinj⟩ :=
    exists_isFinite_syntomic_toProjectiveSpace_deRhamCohomologyTrace (k := k)
      (X := (toScheme k).obj X) X.obj.hom (isProjective X) d hd
  let f : X ⟶ projectiveSpace k d := homMk f₀ hf
  refine ⟨f, fun a ha h0 => ?_⟩
  obtain ⟨x, rfl⟩ := (DirectSum.mem_rangeGrading k _ _ a).1 ha
  change DeRhamWeil.pullback f (DirectSum.of _ _ x) = 0 at h0
  rw [DeRhamWeil.pullback_of] at h0
  rw [injective_pullbackPiece_of_injective f _ ((hinj (2 * (d : ℤ))).2)
    ((DirectSum.of_injective (β := DeRhamWeil.piece X) (2 * (d : ℤ))
      (h0.trans (map_zero _).symm)).trans (map_zero _).symm)]
  exact map_zero _

end Stacks.WeilDeRham

end
