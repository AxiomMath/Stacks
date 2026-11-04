module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreSliceChartZeroScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartShrinkingQuasiFiniteEtale

/-!
# The Stacks 02GF criterion at an étale chart of a zero locus, in the site spelling

`AlgebraicGeometry.Space.unramifiedAt_chartBaseChangeHom_globalFunctionsMap_comp_over_field`
concludes unramifiedness of

`chartBaseChangeHom B S hS X Z W ≫ π`,

the composite of the base change of a closed immersion along an étale chart with a morphism of
schemes to the spectrum of a field, at a point of the chart of the closed subspace. The
unramifiedness clause of **Stacks 06N2** as
`AlgebraicGeometry.Stack`
`.exists_fibreIsUnramifiedNear_zeroLocusOnOpen_of_forall_germ_mem_maximalIdeal` assumes it, on
the other hand, in the spelling

`(BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd W.1.hom ≫ β)`,

a single morphism of the big fppf site mapped down to schemes, whose source is the object of the
site that the chart of the subspace *is*. This file crosses the two spellings, at the point of
the chart where the slicing sequence of **Stacks 06MD** does its generating.

The crossing is not a transport. `AlgebraicGeometry.Space.chartBaseChangeHom` is **defined** as
`(BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd W.1.hom)`, so the two morphisms differ by
`CategoryTheory.Functor.map_comp` alone: no point is moved, no isomorphism intervenes and the
hypotheses are the ones the upstream criterion already carries.

## Main results

* `Stack.forall_unramifiedAt_toScheme_map_rep_snd_comp_of_eq_vanishingSubfunctor`:
  for a closed subspace of `X` which is the zero locus of the pullbacks along `g : X ⟶ Y` of
  global regular functions on `Y`, and a point `w` of an affine étale chart `W` of `X` at which
  the germs of the functions read through `p : W ⟶ U` generate the maximal ideal and whose
  residue field is finite separable over that of `Spec k`, the morphism of the site from the
  chart of the subspace to the site object on `Spec k` is unramified at **every** point above `w`.

## Implementation notes

The closed subspace is taken as a variable with the equation naming it as the zero locus, in the
subfunctor-level form `Z.1 = V(g^*f₁, …, g^*f_r)`; being a closed subspace is a proposition, so
`Subtype.ext` turns that into an equation of bundled closed subspaces which the proof substitutes.
This matters: the representability datum `Z.2.2.rep` appears in the type of the point `z`, so the
identification has to be made on the bundled object and before `z` is introduced, not patched up
afterwards.

The structure morphism of the chart over `Spec k` is likewise taken as a variable `π` with the
equation `(BigFppfOver.toScheme B S hS).map β = π`, which typechecks because the scheme
underlying `AlgebraicGeometry.Stack.fieldPointObject` is `Spec k` definitionally; stating the
residue-field hypotheses at `π` rather than at the composite keeps them in the shape the
upstream criterion wants.

The point `w` is a parameter and the conclusion ranges over the points above it, rather than the
hypotheses being stated at the image of a given point: that is where the slicing sequence of
**Stacks 06MD** generates.

The finiteness hypothesis the criterion of **Stacks 02GF** carries is asked for of
`(BigFppfOver.toScheme B S hS).map β`, the structure morphism of the *chart*, and not of the
composite: the chart of the closed subspace is a closed immersion into the chart
(`AlgebraicGeometry.Space.isClosedImmersion_chartBaseChangeHom`), so the composite inherits it.

## References

* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N2](https://stacks.math.columbia.edu/tag/06N2)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Opposite

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The criterion of Stacks 02GF at an étale chart of a zero locus, in the site spelling.**
Let `g : X ⟶ Y` be a morphism of algebraic spaces, let `f₁, …, f_r` be global sections of the
structure sheaf of `Y`, let `U` be an étale chart of `Y`, let `W` be an **affine** étale chart of
`X` with a morphism `p : W ⟶ U` of the site over `g`, and let `β : W ⟶ Spec k` be a morphism of
the site to the site object on the spectrum of a field, with underlying morphism of schemes `π`.
Let `Z ⊆ X` be the closed subspace `V(g^*f₁, …, g^*f_r)` and let `w` be a point of the chart
scheme of `W` at which the germs of the functions `p^*f₁|_U, …, p^*f_r|_U` generate the maximal
ideal and whose residue field is finite separable over the residue field of `Spec k`. Then for
**every** point `z` of the chart `Z ×_X W` above `w`, the morphism of schemes underlying
`Z ×_X W ⟶ W ⟶ Spec k`, taken as a single morphism of the site, is unramified at `z`. -/
theorem forall_unramifiedAt_toScheme_map_rep_snd_comp_of_eq_vanishingSubfunctor
    {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) {r : ℕ}
    (f : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS Y)).sections)
    (U : Space.SmallEtale B S hS Y.1) (W : Space.SmallEtale B S hS X.1)
    (p : W.1.left ⟶ U.1.left) (hp : yoneda.map p ≫ U.1.hom = W.1.hom ≫ g.hom)
    (hW : IsAffine (Space.chartScheme W))
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (toBase : Spec (.of k) ⟶ S)
    (β : W.1.left ⟶ fieldPointObject B S hS k hk toBase)
    (π : Space.chartScheme W ⟶ Spec (.of k)) (hπ : (BigFppfOver.toScheme B S hS).map β = π)
    (Z : Space.ClosedSubspaces B S hS X.1)
    (hZ : Z.1 = Space.vanishingSubfunctor B S hS X fun i =>
      Space.globalFunctionsMap B S hS g (f i))
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map β)]
    (w : Space.chartScheme W)
    (hgen : Ideal.ofList (List.ofFn fun i => (Space.chartScheme W).presheaf.germ ⊤ w trivial
          (((BigFppfOver.toScheme B S hS).map p).appTop.hom ((f i).eval (op U)))) =
      maximalIdeal ((Space.chartScheme W).presheaf.stalk w))
    (hsep : letI := (π.residueFieldMap w).hom.toAlgebra
      Module.Finite ((Spec (.of k)).residueField (π w))
          ((Space.chartScheme W).residueField w) ∧
        Algebra.IsSeparable ((Spec (.of k)).residueField (π w))
          ((Space.chartScheme W).residueField w)) :
    ∀ z : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback W.1.hom),
      Space.chartBaseChangeHom B S hS X Z W z = w →
        _root_.AlgebraicGeometry.UnramifiedAt
          ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd W.1.hom ≫ β)) z := by
  subst hπ
  have hZ' : Z = Space.vanishingSubspace B S hS X fun i =>
    Space.globalFunctionsMap B S hS g (f i) := Subtype.ext hZ
  subst hZ'
  intro z hzw
  subst hzw
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      ((Space.vanishingSubspace B S hS X fun i =>
        Space.globalFunctionsMap B S hS g (f i)).2.2.rep.snd W.1.hom ≫ β)) := by
    rw [Functor.map_comp]
    infer_instance
  exact Space.unramifiedAt_of_eq_chartBaseChangeHom_globalFunctionsMap_comp B S hS g f U W p hp
    hW ((BigFppfOver.toScheme B S hS).map β) _ (Functor.map_comp _ _ _) z hgen hsep

end AlgebraicGeometry.Stack

end
