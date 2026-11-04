module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ClosedBiduality

/-!
# The biduality of a ringed site as a natural transformation

For a ringed site `(C, O)` and `K ∈ D(O)`, the biduality morphisms `L ⟶ R𝓗om(R𝓗om(L, K), K)` of
Stacks 0A89 form a natural transformation `𝟭 ⟶ D ∘ D` for the duality functor
`D = R𝓗om(-, K)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.stdDual`: `D = R𝓗om(-, K)` at the standard model.
* `AlgebraicGeometry.RingedSite.stdBiduality`: the biduality `𝟭 ⟶ D ∘ D`.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The duality functor `D = R𝓗om(-, K)` of `D(O)`, at the standard model. -/
abbrev stdDual (K : StdDerived X) : (StdDerived X)ᵒᵖ ⥤ StdDerived X :=
  (stdSheafHom X).flip.obj K

/-- **The biduality of a ringed site**, as a natural transformation `𝟭 ⟶ D ∘ D` (Stacks 0A89). -/
def stdBiduality (K : StdDerived X) : 𝟭 _ ⟶ (stdDual X K).rightOp ⋙ stdDual X K where
  app L := derivedBiduality X K L
  naturality _ _ g := derivedBiduality_naturality X K g

/-- The component of `stdBiduality X K` at `L` is the biduality morphism
`derivedBiduality X K L : L ⟶ R𝓗om(R𝓗om(L, K), K)`. -/
theorem stdBiduality_app (K L : StdDerived X) : (stdBiduality X K).app L = derivedBiduality X K L :=
  rfl

/-- The component of `stdBiduality X K` at `L` is an isomorphism if and only if the biduality
morphism `derivedBiduality X K L` is. -/
theorem isIso_stdBiduality_app_iff (K L : StdDerived X) :
    IsIso ((stdBiduality X K).app L) ↔ IsIso (derivedBiduality X K L) :=
  Iff.rfl

end AlgebraicGeometry.RingedSite

end
