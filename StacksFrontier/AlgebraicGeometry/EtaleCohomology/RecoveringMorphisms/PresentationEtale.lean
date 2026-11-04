module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.GeometricFiberSolutions
public import StacksFrontier.RingTheory.Etale.BaseChangeStandardPresentation

/-!
# A standard presentation of an étale chart presents an étale algebra over the base and over a germ

Step (3) of the proof of [Stacks Project, Tag 04I6] runs
`MvPolynomial.bijective_homOverMap_of_etale` — [Stacks Project, Tag 04GX] — on the system `P`
presenting an affine étale chart `V` of an affine scheme `S`, read over the étale local ring
`𝒪^{ét}_{S,s̄}`.  That statement asks for the instance

`Algebra.Etale 𝒪^{ét}_{S,s̄} (𝒪^{ét}_{S,s̄}[x₁, …, x_n] ⧸ (P^{γ}))`,

and `Stacks.EtaleCohomology.StandardPresentationOver` does not carry it: that datum records only
the isomorphism of the presented ring with `Γ(V, ⊤)` and its compatibility with the structure map,
and in particular no Jacobian determinant, so
`Algebra.etale_mvPolynomialQuotient_of_isUnit_det` cannot be applied to it directly.

This file supplies the instance from the datum, in two steps.  Over the base it is the étaleness of
the chart itself: `V` is an object of the small étale site, so its structure morphism is étale
(`AlgebraicGeometry.SmallEtale.etale_structureMorphism`), both schemes are affine, so the ring map
on global functions is étale (`AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`), and the
presentation transports that along an isomorphism of `Γ(S, ⊤)`-algebras.  Over the germ it is base
change, `Algebra.etale_mvPolynomialQuotientMap_of_etale`.

## Main results

* `Stacks.EtaleCohomology.StandardPresentationOver.algEquiv` — a standard presentation of an affine
  étale chart is an isomorphism of `Γ(S, ⊤)`-algebras.
* `Stacks.EtaleCohomology.StandardPresentationOver.etale` — the presented ring is étale over
  `Γ(S, ⊤)`.
* `AlgebraicGeometry.etale_etaleLocalRing_quotientSpanRange` — **the instance
  [Stacks Project, Tag 04GX] asks for**: the system `P`, its coefficients pushed into the étale
  local ring at a geometric point along `AlgebraicGeometry.etaleCoefficientGerm`, presents an étale
  algebra over that local ring.

## References

* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {B : AlgebraicGeometry.BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  [IsAffine S] {V : AlgebraicGeometry.SmallEtale B S hS}
  [IsAffine ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V)]
  {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(S, ⊤)}
  (pres : StandardPresentationOver ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V)
    (AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS V) P)

namespace StandardPresentationOver

/-- **A standard presentation of an étale chart is an isomorphism of algebras over the base.**  The
`Γ(S, ⊤)`-algebra structure on `Γ(V, ⊤)` is the one given by the structure morphism of the chart,
and on the presented ring it is the canonical one; the compatibility recorded in the field
`comp_iso_hom` of `Stacks.EtaleCohomology.StandardPresentationOver` is exactly the statement that
the isomorphism commutes with them. -/
def algEquiv :
    letI := (AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS V).appTop.hom.toAlgebra
    ↥Γ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V, ⊤) ≃ₐ[↥Γ(S, ⊤)]
      (MvPolynomial (Fin n) ↥Γ(S, ⊤) ⧸ Ideal.span (Set.range P)) :=
  letI := (AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS V).appTop.hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := pres.iso.commRingCatIsoToRingEquiv) fun r => by
    exact ConcreteCategory.congr_hom pres.comp_iso_hom r

include pres in
/-- **The ring presented by a standard presentation of an affine étale chart is étale over the
base.**  The chart is étale over `S` because it is an object of the small étale site
(`AlgebraicGeometry.SmallEtale.etale_structureMorphism`); both schemes being affine, the ring map
on global functions is étale, and the presentation carries that to the presented ring. -/
theorem etale :
    Algebra.Etale ↥Γ(S, ⊤) (MvPolynomial (Fin n) ↥Γ(S, ⊤) ⧸ Ideal.span (Set.range P)) :=
  let := (AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS V).appTop.hom.toAlgebra
  have : Algebra.Etale ↥Γ(S, ⊤)
      ↥Γ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj V, ⊤) :=
    (AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine (P := @AlgebraicGeometry.Etale)
      (f := AlgebraicGeometry.SmallEtale.schemeStructureHom B S hS V)).1 inferInstance
  Algebra.Etale.of_equiv pres.algEquiv

end StandardPresentationOver

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

variable {B : BigEtaleSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsAffine S]
  {V : SmallEtale B S hS} [IsAffine ((SmallEtale.toScheme B S hS).obj V)]
  {n : ℕ} {P : Fin n → MvPolynomial (Fin n) Γ(S, ⊤)}

/-- **The hypothesis of [Stacks Project, Tag 04GX] at a geometric point.**  For an affine étale
chart `V` of an affine scheme `S` with a standard presentation
`Γ(V, ⊤) = Γ(S, ⊤)[x₁, …, x_n] ⧸ (P₁, …, P_n)` and a geometric point `s̄` of `S`, the system `P`
with its coefficients pushed into the étale local ring `𝒪^{ét}_{S,s̄}` along
`AlgebraicGeometry.etaleCoefficientGerm` presents an étale algebra over that local ring.

This is `Stacks.EtaleCohomology.StandardPresentationOver.etale` base-changed along the germ map, by
`Algebra.etale_mvPolynomialQuotientMap_of_etale`.  Together with
`AlgebraicGeometry.etaleLocalRing_strictHenselian` and the locality of
`AlgebraicGeometry.etaleLocalRingHomOfSheafFiberIso` it completes the hypotheses of
`MvPolynomial.bijective_homOverMap_of_etale`. -/
theorem etale_etaleLocalRing_quotientSpanRange (s : GeometricPoint S)
    (pres : Stacks.EtaleCohomology.StandardPresentationOver
      ((SmallEtale.toScheme B S hS).obj V) (SmallEtale.schemeStructureHom B S hS V) P) :
    Algebra.Etale ↥(etaleLocalRing B S hS s)
      (MvPolynomial (Fin n) ↥(etaleLocalRing B S hS s) ⧸
        Ideal.span (Set.range fun j ↦
          MvPolynomial.map (etaleCoefficientGerm B S hS s) (P j))) :=
  have := pres.etale
  Algebra.etale_mvPolynomialQuotientMap_of_etale_ringHom (etaleCoefficientGerm B S hS s) P

end AlgebraicGeometry

end
