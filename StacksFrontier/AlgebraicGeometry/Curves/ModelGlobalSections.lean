module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.NonsingularProjectiveModel
public import StacksFrontier.AlgebraicGeometry.FunctionField.DominantMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricIrreducibleComponents.FunctionField
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres

/-!
# Global functions on a nonsingular projective model after extension of the base field

Let `k` be a field and let `X` be a geometrically irreducible curve over `k`. For a field
extension `K/k` let `Y_K` be a nonsingular projective model of the reduction `(X_K)_red` of the
base change of `X` to `K`. Being birational to `(X_K)_red`, the model is again geometrically
irreducible over `K`; so if it is geometrically reduced — in particular if it is smooth — it is
geometrically integral, and a proper geometrically integral scheme over `K` has only the
constants as global regular functions, that is `H⁰(Y_K, 𝒪_{Y_K}) = K`.

## Main definitions

* `AlgebraicGeometry.reducedBaseChange` is the reduction `(X_K)_red` of the base change of a
  `k`-scheme along a field extension `K/k`, and
  `AlgebraicGeometry.reducedBaseChangeStructureMap` is its structure morphism over `K`.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_comp_of_universalHomeomorphism`: irreducibility of
  all base changes passes along a universal homeomorphism.
* `AlgebraicGeometry.NonsingularProjectiveModel.geometricallyIrreducible_structureMap`: a
  nonsingular projective model of a geometrically irreducible curve is geometrically irreducible.
* `AlgebraicGeometry.isIso_globalSections_of_geometricallyReduced_model_reducedBaseChange`: the
  global regular functions on a geometrically reduced nonsingular projective model of
  `(X_K)_red` are the constants `K`.
* `AlgebraicGeometry.isIso_globalSections_of_smooth_model_reducedBaseChange`: the same conclusion
  under smoothness of the model.

## Implementation notes

The equality `H⁰(Y, 𝒪_Y) = K` is expressed canonically, as in
`AlgebraicGeometry.isIso_globalSections_of_geometricallyIntegral`, by saying that the
homomorphism `K ⟶ Γ(Y, ⊤)` induced by the structure morphism is an isomorphism.

Geometric irreducibility is transported from `(X_K)_red` to the model through the function field,
using Tag 054Q (`AlgebraicGeometry.geometricallyIrreducible_tfae_functionField`): for an
irreducible scheme over `K` geometric irreducibility says exactly that the separable closure of
`K` in the residue field at the generic point is trivial, that residue field is the function
field because the stalk there is already a field, and a nonsingular projective model comes
equipped with a `K`-algebra isomorphism of function fields. That `(X_K)_red` itself is
geometrically irreducible over `K` is the composite of two steps: geometric irreducibility is
stable under base change, and the reduction morphism is a universal homeomorphism, so every base
change of it is a homeomorphism.

The hypothesis that `(X_K)_red` is a curve over `K` is an instance argument rather than a
derived fact: it is presupposed by the source's notation `Y_K` for a nonsingular projective
model of `(X_K)_red`, since a model is only defined for a curve.

## References

* [Stacks Project, Tag 0BY4](https://stacks.math.columbia.edu/tag/0BY4)
* [Stacks Project, Tag 0BY2](https://stacks.math.columbia.edu/tag/0BY2)
* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Irreducibility of all base changes passes from a morphism to its composition with a universal
homeomorphism: a base change of the latter is a homeomorphism, so the two base changes have
homeomorphic underlying spaces. -/
public theorem geometricallyIrreducible_comp_of_universalHomeomorphism
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ S)
    [UniversalHomeomorphism i] [GeometricallyIrreducible f] :
    GeometricallyIrreducible (i ≫ f) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun L _ y => ?_⟩
  have hirr : IrreducibleSpace ↥(pullback f y) :=
    pullback_of_geometrically ‹GeometricallyIrreducible f›.geometrically_irreducibleSpace L y
  have hbase : IsHomeomorph (pullback.snd i (pullback.fst f y)) :=
    ‹UniversalHomeomorphism i›.universally_isHomeomorph _ _ _
      (IsPullback.of_hasPullback i (pullback.fst f y)).flip
  have h : IrreducibleSpace ↥(pullback i (pullback.fst f y)) :=
    (IsHomeomorph.homeomorph _ hbase).irreducibleSpace_iff.mpr hirr
  exact (pullbackRightPullbackFstIso f y i).hom.homeomorph.irreducibleSpace_iff.mp h

/-- A `K`-algebra isomorphism transports triviality of the separable closure of `K`. -/
private theorem separableClosure_eq_bot_of_algEquiv {K L L' : Type*} [Field K] [Field L]
    [Field L'] [Algebra K L] [Algebra K L'] (e : L ≃ₐ[K] L') (h : separableClosure K L = ⊥) :
    separableClosure K L' = ⊥ := by
  rw [← separableClosure.map_eq_of_algEquiv e, h, IntermediateField.map_bot]

/-- For a curve over a field, the separable closure of the base field is trivial in the function
field exactly when it is trivial in the residue field at the generic point: the stalk at the
generic point is already a field, so the residue map there is an isomorphism of algebras. -/
private theorem separableClosure_functionField_eq_bot_iff_residueField
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsCurve K f] :
    letI : Algebra K (X.residueField (genericPoint X)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        X.Γevaluation (genericPoint X)).hom.toAlgebra
    letI : Algebra K X.functionField := functionFieldAlgebra K f
    (separableClosure K X.functionField = ⊥ ↔
      separableClosure K (X.residueField (genericPoint X)) = ⊥) := by
  let _ : Algebra K (X.residueField (genericPoint X)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
      X.Γevaluation (genericPoint X)).hom.toAlgebra
  let _ : Algebra K X.functionField := functionFieldAlgebra K f
  let e : X.functionField ≃ₐ[K] X.residueField (genericPoint X) :=
    AlgEquiv.ofRingEquiv (f := genericResidueEquiv X) fun _ => rfl
  exact ⟨separableClosure_eq_bot_of_algEquiv e, separableClosure_eq_bot_of_algEquiv e.symm⟩

namespace NonsingularProjectiveModel

/-- A nonsingular projective model of a geometrically irreducible curve over a field `K` is
itself geometrically irreducible over `K`: the condition only depends on the function field, and
the model is equipped with a `K`-algebra isomorphism of function fields. -/
public theorem geometricallyIrreducible_structureMap (K : Type u) [Field K] {Z : Scheme.{u}}
    {sZ : Z ⟶ Spec (.of K)} [IsCurve K sZ] [GeometricallyIrreducible sZ]
    (M : NonsingularProjectiveModel K Z sZ) :
    GeometricallyIrreducible M.structureMap := by
  let _ : IsCurve K M.structureMap := M.isCurve
  let _ : Algebra K Z.functionField := functionFieldAlgebra K sZ
  let _ : Algebra K M.Y.functionField := functionFieldAlgebra K M.structureMap
  have hZ : separableClosure K Z.functionField = ⊥ :=
    (separableClosure_functionField_eq_bot_iff_residueField K sZ).mpr
      (((geometricallyIrreducible_tfae_functionField K Z sZ (genericPoint Z)
        (genericPoint_spec Z)).out 1 3).mp ‹GeometricallyIrreducible sZ›)
  have hY : separableClosure K M.Y.functionField = ⊥ :=
    separableClosure_eq_bot_of_algEquiv M.functionFieldEquiv hZ
  exact ((geometricallyIrreducible_tfae_functionField K M.Y M.structureMap
    (genericPoint M.Y) (genericPoint_spec M.Y)).out 1 3).mpr
      ((separableClosure_functionField_eq_bot_iff_residueField K M.structureMap).mp hY)

end NonsingularProjectiveModel

/-- The reduction `(X_K)_red` of the base change of a scheme over a field `k` along a field
extension `K/k`. -/
public abbrev reducedBaseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) : Scheme.{u} :=
  (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reduction

/-- The structure morphism of `(X_K)_red` over the extension field `K`. -/
public abbrev reducedBaseChangeStructureMap (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) :
    reducedBaseChange k K sX ⟶ Spec (.of K) :=
  (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι ≫
    pullback.snd sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))

/-- The reduction of the base change of a geometrically irreducible scheme along a field
extension is geometrically irreducible over the larger field. -/
public instance geometricallyIrreducible_reducedBaseChangeStructureMap
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [GeometricallyIrreducible sX] :
    GeometricallyIrreducible (reducedBaseChangeStructureMap k K sX) := by
  let _ : UniversalHomeomorphism
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι :=
    inferInstanceAs (UniversalHomeomorphism
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).nilradical.subschemeι)
  exact geometricallyIrreducible_comp_of_universalHomeomorphism _ _

/-- **Stacks Project, Tag 0BY4, part (3).** Let `k` be a field, let `X` be a geometrically
irreducible curve over `k`, let `K/k` be a field extension and let `Y_K` be a nonsingular
projective model of `(X_K)_red`. If `Y_K` is geometrically reduced over `K`, then `K` is the
ring of global regular functions on `Y_K`.

The instance binder `[IsCurve K (reducedBaseChangeStructureMap k K sX)]` is not an added
hypothesis: it is a consequence of `[IsCurve k sX]` and `[GeometricallyIrreducible sX]`, proved
as the instance `AlgebraicGeometry.isCurve_reducedBaseChangeStructureMap'`. That instance lives in
`StacksFrontier/AlgebraicGeometry/Curves/ModelNormalization.lean`, which imports this file, so it
cannot be used here and the fact is named instead. -/
@[stacks 0BY4 "part (3), with the source's own footnote hypothesis: the model is assumed \
only geometrically reduced, not smooth. The binder `[IsCurve K (reducedBaseChangeStructureMap \
k K sX)]` adds nothing: it follows from `[IsCurve k sX]` and `[GeometricallyIrreducible sX]` by \
the instance `AlgebraicGeometry.isCurve_reducedBaseChangeStructureMap'`, which is proved in a \
module importing this one and so is unavailable here"]
public theorem isIso_globalSections_of_geometricallyReduced_model_reducedBaseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsCurve k sX] [GeometricallyIrreducible sX]
    [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX))
    (hred : GeometricallyReduced M.structureMap) :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ M.structureMap.appTop) := by
  let _ : IsCurve K M.structureMap := M.isCurve
  let _ : IsProjectiveVariety K M.structureMap := M.isProjectiveVariety
  let _ : GeometricallyReduced M.structureMap := hred
  let _ : GeometricallyIrreducible M.structureMap :=
    M.geometricallyIrreducible_structureMap K
  let _ : GeometricallyIntegral M.structureMap :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible M.structureMap
  exact isIso_globalSections_of_geometricallyIntegral K M.structureMap

/-- **Stacks Project, Tag 0BY4, part (3).** Let `k` be a field, let `X` be a geometrically
irreducible curve over `k`, let `K/k` be a field extension and let `Y_K` be a nonsingular
projective model of `(X_K)_red`. If `Y_K` is smooth over `K`, then `K` is the ring of global
regular functions on `Y_K`.

The instance binder `[IsCurve K (reducedBaseChangeStructureMap k K sX)]` adds nothing, for the
reason given on
`AlgebraicGeometry.isIso_globalSections_of_geometricallyReduced_model_reducedBaseChange`. -/
@[stacks 0BY4 "part (3). The binder `[IsCurve K (reducedBaseChangeStructureMap k K sX)]` adds \
nothing: it follows from `[IsCurve k sX]` and `[GeometricallyIrreducible sX]` by the instance \
`AlgebraicGeometry.isCurve_reducedBaseChangeStructureMap'`, which is proved in a module importing \
this one and so is unavailable here"]
public theorem isIso_globalSections_of_smooth_model_reducedBaseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsCurve k sX] [GeometricallyIrreducible sX]
    [IsCurve K (reducedBaseChangeStructureMap k K sX)]
    (M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
      (reducedBaseChangeStructureMap k K sX))
    (hsm : Smooth M.structureMap) :
    IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ M.structureMap.appTop) :=
  have : Smooth M.structureMap := hsm
  isIso_globalSections_of_geometricallyReduced_model_reducedBaseChange k K sX M
    (geometricallyReduced_of_smooth M.structureMap)

end AlgebraicGeometry

end
