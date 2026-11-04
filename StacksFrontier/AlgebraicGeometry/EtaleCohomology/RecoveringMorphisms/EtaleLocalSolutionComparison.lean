module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.BaseChangeGeometricFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.EtaleLocalRingFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.PresentationEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift

/-!
# Stacks 04GX for the two étale local rings of Stacks 04I6

Step (3) of the proof of [Stacks Project, Tag 04I6] compares two sets of solutions of one and the
same system `P` presenting an affine étale chart `V` of an affine `Y`: its solutions in the étale
local ring `𝒪^{ét}_{Y,ȳ}` and its solutions in `𝒪^{ét}_{X,x̄}`, the coefficients of the second
being those of the first pushed along a local homomorphism between the two rings.  Both rings are
strictly henselian, so [Stacks Project, Tag 04GX] says the comparison is bijective.

This file applies 04GX to the local homomorphism
`AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso`, whose locality is
`AlgebraicGeometry.isLocalHom_etaleLocalRingHomOfSheafFiberIso`, and the étaleness instance
`AlgebraicGeometry.etale_etaleLocalRing_quotientSpanRange`.  Nothing in it is about the comparison
map of sheaves `AlgebraicGeometry.comparisonSheafHom`.

## Main results

* `AlgebraicGeometry.bijOn_etaleLocalSolutions_etaleLocalRingHom` — **the solution-set bijection
  of step (3)**: postcomposition with `φ` is a bijection from the solutions of `P` in
  `𝒪^{ét}_{Y,ȳ}` onto its solutions in `𝒪^{ét}_{X,x̄}` over the composite coefficient map.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme}
  (g : RingedToposHom
    (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
    (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (x : GeometricPoint X.obj) (y : GeometricPoint Y.obj)
  (e : (geometricPointSitePoint B Y.obj Y.property y).sheafFiber (A := Type u) ≅
    g.toToposHom.inverseImage ⋙
      (geometricPointSitePoint B X.obj X.property x).sheafFiber (A := Type u))
  [IsAffine Y.obj] {V : SmallEtale B Y.obj Y.property}
  [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V)]
  {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(Y.obj, ⊤)}

/-- **[Stacks Project, Tag 04GX] for the two étale local rings of [Stacks Project, Tag 04I6].**
Let `(g, g^♯)` be a locally ringed morphism of the small étale ringed topoi of `X` and `Y`, let
`x̄` be a geometric point of `X` and `ȳ` a geometric point of `Y` whose geometric stalk functor is
`g⁻¹` followed by that of `x̄`, and let `V` be an affine étale chart of an affine `Y` with a
standard presentation `Γ(V, ⊤) = Γ(Y, ⊤)[x₁, …, x_n] ⧸ (P₁, …, P_n)`.  Then applying the
homomorphism `φ : 𝒪^{ét}_{Y,ȳ} ⟶ 𝒪^{ét}_{X,x̄}` of
`AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso` coordinatewise is a bijection from the
solutions of `P` in `𝒪^{ét}_{Y,ȳ}` onto its solutions in `𝒪^{ét}_{X,x̄}` with coefficients pushed
along `φ ∘ γ_Y`.

The three hypotheses of 04GX are all in place: both rings are strictly henselian local rings by
`AlgebraicGeometry.strictlyHenselianLocalRing_etaleLocalRing`; `φ` is local by
`AlgebraicGeometry.isLocalHom_etaleLocalRingHomOfSheafFiberIso`, which is where the *locally*
ringed hypothesis is used; and the presented ring is étale over `𝒪^{ét}_{Y,ȳ}` by
`AlgebraicGeometry.etale_etaleLocalRing_quotientSpanRange`.

By `AlgebraicGeometry.geometricPointFiberEquivEtaleLocalSolutions` the source is the set of lifts
of `ȳ` to `V`, and by `AlgebraicGeometry.baseChangeGeometricPointFiberEquivSolutions` the target is
the set of lifts of `x̄` to `X ×_Y V` as soon as the coefficient map `φ ∘ γ_Y` is identified with
`γ_X ∘ f^♯`. -/
theorem bijOn_etaleLocalSolutions_etaleLocalRingHom
    (pres : Stacks.EtaleCohomology.StandardPresentationOver
      ((SmallEtale.toScheme B Y.obj Y.property).obj V)
      (SmallEtale.schemeStructureHom B Y.obj Y.property V) P)
    (hg : g.IsLocallyRinged) :
    Set.BijOn
      (fun a : Fin n → ↥(etaleLocalRing B Y.obj Y.property y) ↦
        fun i ↦ etaleLocalRingHomOfSheafFiberIso B g x y e (a i))
      {a | MvPolynomial.IsSolution P (etaleCoefficientGerm B Y.obj Y.property y) a}
      {b | MvPolynomial.IsSolution P
        ((etaleLocalRingHomOfSheafFiberIso B g x y e).comp
          (etaleCoefficientGerm B Y.obj Y.property y)) b} := by
  have := etale_etaleLocalRing_quotientSpanRange (B := B) (hS := Y.property) (V := V) y pres
  have h := bijOn_solutions_of_etale (etaleLocalRingHomOfSheafFiberIso B g x y e)
    (isLocalHom_etaleLocalRingHomOfSheafFiberIso B g x y e hg) n
    (fun j ↦ MvPolynomial.map (etaleCoefficientGerm B Y.obj Y.property y) (P j))
  have hset : {s : Fin n → ↥(etaleLocalRing B X.obj X.property x) |
        MvPolynomial.IsSolution
          (fun j ↦ MvPolynomial.map (etaleCoefficientGerm B Y.obj Y.property y) (P j))
          (etaleLocalRingHomOfSheafFiberIso B g x y e) s} =
      {b | MvPolynomial.IsSolution P
        ((etaleLocalRingHomOfSheafFiberIso B g x y e).comp
          (etaleCoefficientGerm B Y.obj Y.property y)) b} :=
    Set.ext fun b ↦ MvPolynomial.isSolution_map_iff P _ _ b
  rw [← hset]
  exact h

end AlgebraicGeometry

end
