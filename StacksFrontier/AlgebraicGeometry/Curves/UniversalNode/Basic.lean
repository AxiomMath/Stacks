module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The universal nodal family

The morphism `Spec ℤ[u, v, a]/(uv - a) ⟶ Spec ℤ[a]` is the universal family of nodal curve
singularities: étale locally, every at-worst-nodal family of relative dimension one is a base
change of it near a singular point of a fibre.

Eliminating `a` presents that family as `Spec ℤ[u, v] ⟶ Spec ℤ[a]`, the morphism sending the
parameter `a` to the product `uv` of the two coordinates. This file provides both
presentations and the isomorphism between them, so that statements phrased against the
two-variable model are statements about the universal nodal family.

## Main definitions

* `Stacks.Curves.nodalParameterBase` — the affine line `Spec ℤ[a]` over the integers, the base
  of the universal nodal family.
* `Stacks.Curves.nodalModel` — the total space `Spec ℤ[u, v]` of the universal nodal family in
  its two-variable presentation.
* `Stacks.Curves.nodalModelMap` — the universal nodal family `Spec ℤ[u, v] ⟶ Spec ℤ[a]`,
  sending the smoothing parameter to `uv`.
* `Stacks.Curves.nodalRelation` — the equation `uv - a` in three variables.
* `Stacks.Curves.nodalParam` — the parameter map `R[a] ⟶ R[u, v, a]/(uv - a)`.

## Main results

* `Stacks.Curves.nodalEliminateEquiv` — the isomorphism `R[u, v, a]/(uv - a) ≃ₐ[R] R[u, v]`
  that eliminates `a`.
* `Stacks.Curves.nodalEliminateEquiv_comp_nodalParam` — that isomorphism carries the parameter
  map to `a ↦ uv`, so the two presentations of the family agree over the base.
* `Stacks.Curves.nodalModelIso` and
  `Stacks.Curves.nodalModelIso_hom_comp_specMap_nodalParam` — the same statement for schemes:
  `Spec R[u, v] ≅ Spec R[u, v, a]/(uv - a)`, and the universal family
  `Spec R[u, v, a]/(uv - a) ⟶ Spec R[a]` precomposed with that isomorphism is `a ↦ uv`;
  over `ULift ℤ` this is `nodalModelMap`.

## References

* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

/-! ### The two-variable presentation -/

/-- The affine line over the integers, serving as the base of the universal node. -/
public abbrev nodalParameterBase : Scheme.{u} :=
  Spec (.of (Polynomial (ULift.{u} ℤ)))

/-- The total space of the universal nodal family, presented as `Spec ℤ[u,v]`. -/
public abbrev nodalModel : Scheme.{u} :=
  Spec (.of (MvPolynomial (Fin 2) (ULift.{u} ℤ)))

/-- The universal nodal family `Spec ℤ[u, v] ⟶ Spec ℤ[a]`, sending the parameter `a` to `uv`. -/
public def nodalModelMap : nodalModel.{u} ⟶ nodalParameterBase.{u} :=
  Spec.map (CommRingCat.ofHom
    (Polynomial.aeval (MvPolynomial.X 0 * MvPolynomial.X 1)).toRingHom)

/-! ### The three-variable presentation, and the elimination of the parameter -/

variable (R : Type u) [CommRing R]

/-- The equation `uv - a` of the universal nodal family in the three variables `u`, `v`, `a`. -/
public def nodalRelation : MvPolynomial (Fin 3) R :=
  MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.X 2

/-- The coordinate ring `R[u, v, a]/(uv - a)` of the universal nodal family. -/
public abbrev nodalQuotient : Type u :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span {nodalRelation R}

/-- The parameter map `R[a] ⟶ R[u, v, a]/(uv - a)`, sending the variable to the class of `a`.
Its spectrum is the universal nodal family. -/
public def nodalParam : Polynomial R →ₐ[R] nodalQuotient R :=
  (Ideal.Quotient.mkₐ R _).comp (Polynomial.aeval (MvPolynomial.X 2 : MvPolynomial (Fin 3) R))

/-- Eliminating `a` from `R[u, v, a]/(uv - a)`: the algebra map substituting `uv` for `a`. -/
public def nodalEliminate : nodalQuotient R →ₐ[R] MvPolynomial (Fin 2) R :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval
      (fun i : Fin 3 => ![MvPolynomial.X 0, MvPolynomial.X 1,
        MvPolynomial.X 0 * MvPolynomial.X 1] i)) <| by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [nodalRelation]

/-- `nodalEliminate` is computed by substitution on representatives. -/
public theorem nodalEliminate_mk (x : MvPolynomial (Fin 3) R) :
    nodalEliminate R (Ideal.Quotient.mk _ x) =
      MvPolynomial.aeval
        (fun i : Fin 3 => ![MvPolynomial.X 0, MvPolynomial.X 1,
          MvPolynomial.X 0 * MvPolynomial.X 1] i) x := rfl

/-- `nodalEliminate` sends the classes of `u`, `v`, `a` to `u`, `v`, `uv` respectively. -/
@[simp] public theorem nodalEliminate_mk_X (i : Fin 3) :
    nodalEliminate R (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      ![MvPolynomial.X 0, MvPolynomial.X 1,
        MvPolynomial.X 0 * MvPolynomial.X 1] i := by
  rw [nodalEliminate_mk]; simp

/-- Reintroducing the parameter: `R[u, v] ⟶ R[u, v, a]/(uv - a)` on the two coordinates. -/
public def nodalIntroduce : MvPolynomial (Fin 2) R →ₐ[R] nodalQuotient R :=
  MvPolynomial.aeval (fun i : Fin 2 => Ideal.Quotient.mk _ (MvPolynomial.X i.castSucc))

/-- `nodalIntroduce` sends each coordinate of `R[u, v]` to its class in `R[u, v, a]/(uv - a)`. -/
@[simp] public theorem nodalIntroduce_X (i : Fin 2) :
    nodalIntroduce R (MvPolynomial.X i) =
      Ideal.Quotient.mk _ (MvPolynomial.X i.castSucc) := by
  simp [nodalIntroduce]

/-- In `R[u, v, a]/(uv - a)` the class of the parameter is the product of the coordinates. -/
public theorem mk_X_two :
    Ideal.Quotient.mk (Ideal.span {nodalRelation R}) (MvPolynomial.X 2) =
      Ideal.Quotient.mk _ (MvPolynomial.X 0 * MvPolynomial.X 1) := by
  rw [eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span rfl

/-- **The two presentations of the universal nodal family agree.** Eliminating the parameter
`a` is an isomorphism `R[u, v, a]/(uv - a) ≃ₐ[R] R[u, v]`. -/
public def nodalEliminateEquiv : nodalQuotient R ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (nodalEliminate R) (nodalIntroduce R)
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [Ideal.Quotient.mkₐ_eq_mk, mk_X_two])

/-- The isomorphism `nodalEliminateEquiv` acts as the algebra map `nodalEliminate`. -/
@[simp] public theorem nodalEliminateEquiv_apply (x : nodalQuotient R) :
    nodalEliminateEquiv R x = nodalEliminate R x := rfl

/-- **The isomorphism is one of families over the base.** Eliminating `a` carries the
parameter map `R[a] ⟶ R[u, v, a]/(uv - a)` to the map `a ↦ uv`, which is the one defining
`nodalModelMap`. -/
public theorem nodalEliminateEquiv_comp_nodalParam :
    (nodalEliminateEquiv R).toAlgHom.comp (nodalParam R) =
      Polynomial.aeval (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) R) := by
  apply Polynomial.algHom_ext
  simp [nodalParam, Ideal.Quotient.mkₐ_eq_mk]

/-! ### The scheme-level comparison -/

/-- The isomorphism of coordinate rings eliminating the parameter, as an isomorphism in
`CommRingCat`. -/
public def nodalQuotientIso :
    CommRingCat.of (nodalQuotient R) ≅ CommRingCat.of (MvPolynomial (Fin 2) R) :=
  (nodalEliminateEquiv R).toRingEquiv.toCommRingCatIso

/-- The two presentations of the total space of the universal nodal family are isomorphic
as schemes: `Spec R[u, v] ≅ Spec R[u, v, a]/(uv - a)`. -/
public def nodalModelIso :
    Spec (.of (MvPolynomial (Fin 2) R)) ≅ Spec (.of (nodalQuotient R)) :=
  Scheme.Spec.mapIso (nodalQuotientIso R).op

/-- **The universal nodal family in its two presentations.** The family
`Spec R[u, v, a]/(uv - a) ⟶ Spec R[a]`, precomposed with the isomorphism that eliminates the
parameter, is the morphism `Spec R[u, v] ⟶ Spec R[a]` sending the parameter to `uv` — which
for `R = ULift ℤ` is `nodalModelMap`. -/
public theorem nodalModelIso_hom_comp_specMap_nodalParam :
    (nodalModelIso R).hom ≫ Spec.map (CommRingCat.ofHom (nodalParam R).toRingHom) =
      Spec.map (CommRingCat.ofHom
        (Polynomial.aeval (MvPolynomial.X 0 * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) R)).toRingHom) := by
  change Spec.map (nodalQuotientIso R).hom ≫ _ = _
  rw [← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
  exact DFunLike.congr_fun (nodalEliminateEquiv_comp_nodalParam R) x

/-- Specialised to the integers, the universal nodal family is `nodalModelMap`. -/
public theorem nodalModelIso_hom_comp_specMap_nodalParam_int :
    (nodalModelIso (ULift.{u} ℤ)).hom ≫
        Spec.map (CommRingCat.ofHom (nodalParam (ULift.{u} ℤ)).toRingHom) =
      nodalModelMap.{u} :=
  nodalModelIso_hom_comp_specMap_nodalParam _

end Stacks.Curves

end
