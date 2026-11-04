module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneIsProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceTwist

/-!
# The twists across the chart comparison with a polynomial ring

`Stacks.SymGraded.chartIsoProjPoly` identifies the chart of the projective bundle of
`𝒪_X^{n+1}` over an open `U` with `Proj Γ(X, U)[T₀, …, Tₙ]`. It is the composite of
`AlgebraicGeometry.Proj.map` of two graded ring isomorphisms — the chart comparison of
`Stacks.SymGraded.chartGradedHom` and the reindexing of
`Stacks.AlgebraicGeometry.ProjPoly.projIsoULiftIndex` — so the twists correspond across it by
[Stacks, Tag 01N1] part (3) applied twice.

## Main results

* `Stacks.SymGraded.nonempty_pullback_chartIsoProjPoly_hom_twistingSheaf`: the inverse image of
  the degree-`m` twist of `Proj Γ(X, U)[T₀, …, Tₙ]` along the comparison is the degree-`m` twist
  of `Proj Γ(U, Sym(𝒪_X^{n+1}))`.
* `Stacks.SymGraded.nonempty_pullback_chartIsoProjPoly_inv_twistingSheaf`: the same read along
  the inverse.

## Implementation notes

`Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap` asks for the *source* grading to be
generated in degree one and for the homomorphism to be surjective. Both homomorphisms here are
isomorphisms of graded rings, so surjectivity is immediate; the two sources are polynomial rings,
graded by total degree, for which generation in degree one is
`MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top`.

`Stacks.SymGraded.nonempty_pullback_inv_of_pullback_hom` turns a comparison of inverse images
along the forward morphism of an isomorphism into one along its inverse; it is
`Stacks.SymGraded.nonempty_iso_of_nonempty_pullback_iso`'s trick in the form needed here.

## References

* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.SymGraded

/-! ### Reading a comparison of inverse images along the inverse of an isomorphism -/

/-- **A comparison of inverse images along an isomorphism, read along its inverse.** -/
theorem nonempty_pullback_inv_of_pullback_hom {A B : Scheme.{u}} (e : A ≅ B) (M : B.Modules)
    (N : A.Modules) (h : Nonempty ((Scheme.Modules.pullback e.hom).obj M ≅ N)) :
    Nonempty ((Scheme.Modules.pullback e.inv).obj N ≅ M) := by
  obtain ⟨α⟩ := h
  refine ⟨((Scheme.Modules.pullback e.inv).mapIso α).symm ≪≫ ?_⟩
  exact (Scheme.Modules.pullbackComp e.inv e.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr e.inv_hom_id).app M ≪≫ (Scheme.Modules.pullbackId B).app M

/-! ### The twists across the chart comparison -/

variable {X : Scheme.{u}} (n : ℕ) (U : X.Opens)

/-- **The twists correspond across the chart comparison with a polynomial ring.** -/
theorem nonempty_pullback_chartIsoProjPoly_hom_twistingSheaf (m : ℤ) :
    Nonempty ((Scheme.Modules.pullback (chartIsoProjPoly (X := X) n U).hom).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ↥(siteRing X (op U)) n) m) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U) m) := by
  obtain ⟨β⟩ := Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap _ _
    (Stacks.AlgebraicGeometry.ProjPoly.renameGradedHom ↥(siteRing X (op U))
      ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1))))
    (Stacks.AlgebraicGeometry.ProjPoly.irrelevant_le_map_renameGradedHom _
      (Equiv.ulift.{u, 0}).symm)
    (MvPolynomial.rename_surjective _ (Equiv.ulift.{u, 0}).symm.surjective)
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) _) m
  obtain ⟨γ⟩ := Stacks.ProjectiveSpace.nonempty_pullbackTwist_projMap _ _
    (chartGradedHom (X := X) n U) (irrelevant_le_map_chartGradedHom n U)
    (chartSectionsRingEquiv n U).surjective
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (ULift.{u} (Fin (n + 1))) _) m
  refine ⟨?_⟩
  rw [chartIsoProjPoly_hom]
  exact ((Scheme.Modules.pullbackComp
      (AlgebraicGeometry.Proj.map (chartGradedHom (X := X) n U)
        (irrelevant_le_map_chartGradedHom n U))
      (Stacks.AlgebraicGeometry.ProjPoly.projIsoULiftIndex ↥(siteRing X (op U)) n).hom).app
      _).symm ≪≫
    (Scheme.Modules.pullback (AlgebraicGeometry.Proj.map (chartGradedHom (X := X) n U)
      (irrelevant_le_map_chartGradedHom n U))).mapIso β ≪≫ γ

/-- **The twists correspond across the inverse of the chart comparison.** -/
theorem nonempty_pullback_chartIsoProjPoly_inv_twistingSheaf (m : ℤ) :
    Nonempty ((Scheme.Modules.pullback (chartIsoProjPoly (X := X) n U).inv).obj
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
          ((freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).grading U) m) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading ↥(siteRing X (op U)) n) m) :=
  nonempty_pullback_inv_of_pullback_hom (chartIsoProjPoly (X := X) n U) _ _
    (nonempty_pullback_chartIsoProjPoly_hom_twistingSheaf n U m)

end Stacks.SymGraded

end
