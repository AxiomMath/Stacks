module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FlatLength
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksCore.Tactic.StacksAttribute

/-!
# The canonical weighting of a flat quasi-finite morphism restricts along a base change

Let `f : X ⟶ Y` be flat, locally quasi-finite and locally of finite presentation and let

```
X' --p--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square. Then `f'` has the same three properties, and the canonical weighting
`AlgebraicGeometry.flatQuasiFiniteWeight` of `f'` is the restriction of that of `f`:

`flatQuasiFiniteWeight f' = flatQuasiFiniteWeight f ∘ p`.

Neither factor of the weight is base-change invariant on its own. For `Spec L ⟶ Spec k` with
`L/k` purely inseparable of degree `p` the weight is `1 * p`, and after the base change along
`k ⟶ L` the source becomes `Spec (L[s]/s^p)`, whose weight is `p * 1`: the length has absorbed
exactly the inseparable degree that the residue field extension lost. Only the product is
invariant, and that combined invariance is what the two inputs below supply.

## Main results

* `Stacks.Chow.length_fiberStalk_mul_finInsepDegree_of_isPullback` — the first paragraph of the
  proof of Stacks tag `0H5P` for an arbitrary cartesian square rather than for the canonical
  fibre product: the length of the local ring of the fibre of the induced morphism of fibres,
  times the inseparable degree of `κ(x')` over `κ(f' x')`, is the inseparable degree of `κ(p x')`
  over `κ(f (p x'))`.
* `AlgebraicGeometry.flatQuasiFiniteWeight_of_isPullback` — the displayed identity above, and
  the final claim of Stacks Example `0GKI`.

## Implementation notes

The proof factors the weight at `x'` through the local ring of the scheme-theoretic fibre of
`f'` at `x'`, which `AlgebraicGeometry.quotientStalkEquivFiberStalk` identifies with the
quotient appearing in the formula. On those fibres the comparison morphism
`N = AlgebraicGeometry.restrictedFiberMap f f' p g sq.w (f' x')` from the fibre of `f'` at
`f' x'` to the fibre of `f` at `g (f' x')` is a base change of the spectrum of the residue field
map of `g`, hence flat, so Stacks tag `02M1` in the form
`length_baseChange_eq_length_mul_length_quotient` splits the length upstairs as the length
downstairs times the length of the local ring of the fibre of `N`. That last length is precisely
the factor which
`Stacks.Chow.length_fiberStalk_mul_finInsepDegree_of_isPullback` trades against the two
inseparable degrees.

The `κ(·)`-algebra structures on residue fields are never instances: each statement introduces
the ones it uses in its own `let` bindings, in the form the imported tag `0H5P` results produce
them. The base points `f (p x')` and `g (f' x')` are equal but not definitionally so, so the
point of the fibre of `f` is `f.asFiber (p x')` transported along that equality; the two
`eqToHom` transport lemmas of the imported development dispose of it, and the `02M1` step is run
with the transported point so that no `eqToHom` ever has to be reduced.

## References

* [Stacks Project, Tag 0GKI](https://stacks.math.columbia.edu/tag/0GKI)
* [Stacks Project, Tag 0F3D](https://stacks.math.columbia.edu/tag/0F3D)
* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 02M1](https://stacks.math.columbia.edu/tag/02M1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-- **Stacks Project, Tag 0H5P, first paragraph, for an arbitrary cartesian square.** At a point
`x'` of the source of a base change `f'` of `f` along `g`, the length of the local ring of the
fibre of the induced morphism of fibres through `x'`, times the inseparable degree of `κ(x')`
over `κ(f' x')`, is the inseparable degree of `κ(p x')` over `κ(f (p x'))`.

This is `Stacks.Chow.length_fiberStalk_mul_finInsepDegree_eq` applied to the cartesian square of
Tag `0H4N` for the given square, after identifying the residue fields of the two fibres with
`κ(x')` and `κ(p x')`. -/
theorem length_fiberStalk_mul_finInsepDegree_of_isPullback {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {p : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
    (sq : IsPullback p f' f g) (x' : X')
    (N : f'.fiber (f' x') ⟶ f.fiber (g (f' x')))
    (hN : N = restrictedFiberMap f f' p g sq.w (f' x')) :
    letI : Algebra ↥(Y'.residueField (f' x')) ↥(X'.residueField x') :=
      (f'.residueFieldMap x').hom.toAlgebra
    letI : Algebra ↥(Y.residueField (f (p x'))) ↥(X.residueField (p x')) :=
      (f.residueFieldMap (p x')).hom.toAlgebra
    (Module.length ((N.fiber (N (f'.asFiber x'))).presheaf.stalk (N.asFiber (f'.asFiber x')))
          ((N.fiber (N (f'.asFiber x'))).presheaf.stalk (N.asFiber (f'.asFiber x')))).toNat *
        Field.finInsepDegree ↥(Y'.residueField (f' x')) ↥(X'.residueField x') =
      Field.finInsepDegree ↥(Y.residueField (f (p x'))) ↥(X.residueField (p x')) := by
  subst hN
  let _ : Algebra ↥(Y'.residueField (f' x')) ↥(X'.residueField x') :=
    (f'.residueFieldMap x').hom.toAlgebra
  let _ : Algebra ↥(Y.residueField (f (p x'))) ↥(X.residueField (p x')) :=
    (f.residueFieldMap (p x')).hom.toAlgebra
  let _ : Algebra ↥(Y.residueField (g (f' x'))) ↥(Y'.residueField (f' x')) :=
    (g.residueFieldMap (f' x')).hom.toAlgebra
  let _ : Algebra ↥(Y.residueField (g (f' x')))
      ↥((f.fiber (g (f' x'))).residueField
        (restrictedFiberMap f f' p g sq.w (f' x') (f'.asFiber x'))) :=
    ((Scheme.ΓSpecIso (.of ↥(Y.residueField (g (f' x'))))).inv ≫
      (f.fiberToSpecResidueField (g (f' x'))).appTop ≫
      (f.fiber (g (f' x'))).Γevaluation
        (restrictedFiberMap f f' p g sq.w (f' x') (f'.asFiber x'))).hom.toAlgebra
  let _ : Algebra ↥(Y'.residueField (f' x'))
      ↥((f'.fiber (f' x')).residueField (f'.asFiber x')) :=
    ((Scheme.ΓSpecIso (.of ↥(Y'.residueField (f' x')))).inv ≫
      (f'.fiberToSpecResidueField (f' x')).appTop ≫
      (f'.fiber (f' x')).Γevaluation (f'.asFiber x')).hom.toAlgebra
  have hx : f (p x') = g (f' x') := congrArg (fun m : X' ⟶ Y => m x') sq.w
  have hy : restrictedFiberMap f f' p g sq.w (f' x') (f'.asFiber x') =
      eqToHom (congrArg (fun u : Y => f.fiber u) hx) (f.asFiber (p x')) :=
    restrictedFiberMap_asFiber f f' p g sq.w x'
  have hfin : Module.Finite ↥(Y.residueField (g (f' x')))
      ↥((f.fiber (g (f' x'))).residueField
        (restrictedFiberMap f f' p g sq.w (f' x') (f'.asFiber x'))) :=
    module_finite_residueField_fiber_eqToHom f (p x') (g (f' x')) hx _ hy
  have hsq : IsPullback (restrictedFiberMap f f' p g sq.w (f' x'))
      (f'.fiberToSpecResidueField (f' x')) (f.fiberToSpecResidueField (g (f' x')))
      (Spec.map (g.residueFieldMap (f' x'))) :=
    isPullback_fiberToSpecResidueField_of_isPullback sq (f' x')
  have hM := length_fiberStalk_mul_finInsepDegree_eq
    ↥(Y.residueField (g (f' x'))) ↥(Y'.residueField (f' x'))
    (f.fiberToSpecResidueField (g (f' x'))) (f'.fiberToSpecResidueField (f' x'))
    (restrictedFiberMap f f' p g sq.w (f' x')) hsq (f'.asFiber x') hfin
  have hC1 : Field.finInsepDegree ↥(Y'.residueField (f' x'))
        ↥((f'.fiber (f' x')).residueField (f'.asFiber x')) =
      Field.finInsepDegree ↥(Y'.residueField (f' x')) ↥(X'.residueField x') :=
    finInsepDegree_residueField_fiber f' x'
  have hC2 : Field.finInsepDegree ↥(Y.residueField (g (f' x')))
        ↥((f.fiber (g (f' x'))).residueField
          (restrictedFiberMap f f' p g sq.w (f' x') (f'.asFiber x'))) =
      Field.finInsepDegree ↥(Y.residueField (f (p x'))) ↥(X.residueField (p x')) :=
    finInsepDegree_residueField_fiber_eqToHom f (p x') (g (f' x')) hx _ hy
  rw [← hC1, ← hC2]
  exact hM

end Stacks.Chow

namespace AlgebraicGeometry

/-- The length of `𝒪_{X,x}/𝔪_{f x}𝒪_{X,x}` is the length of the local ring of the fibre of `f`
at a point `y` over a base point `s` propositionally equal to `f x`, with `y` the transport of
`f.asFiber x`. -/
private theorem length_quotient_map_maximalIdeal_eq_length_fiberStalk {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) {s : Y} (hp : f x = s) {y : f.fiber s}
    (hy : y = eqToHom (congrArg (fun u : Y => f.fiber u) hp) (f.asFiber x)) :
    Module.length (X.presheaf.stalk x)
        ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMap x).hom
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) =
      Module.length ((f.fiber s).presheaf.stalk y) ((f.fiber s).presheaf.stalk y) := by
  subst hp hy
  rw [Module.length_eq_of_surjective (R := (X.presheaf.stalk x) ⧸
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))))
    (S := X.presheaf.stalk x) Ideal.Quotient.mk_surjective]
  exact Module.length_eq_of_ringEquiv (quotientStalkEquivFiberStalk f x)

/-- **Stacks Project, Tag 02M1, for a flat morphism of schemes.** The length of the local ring at
`q` is the length of the local ring at the image of `q` times the length of the local ring of the
fibre through `q`. -/
private theorem length_stalk_eq_length_stalk_mul_length_fiberStalk {X Y : Scheme.{u}} (N : X ⟶ Y)
    [Flat N] (q : X) :
    Module.length (X.presheaf.stalk q) (X.presheaf.stalk q) =
      Module.length (Y.presheaf.stalk (N q)) (Y.presheaf.stalk (N q)) *
        Module.length ((N.fiber (N q)).presheaf.stalk (N.asFiber q))
          ((N.fiber (N q)).presheaf.stalk (N.asFiber q)) := by
  let R := Y.presheaf.stalk (N q)
  let A := X.presheaf.stalk q
  let _ : Algebra R A := (N.stalkMap q).hom.toAlgebra
  have _ : IsLocalHom (algebraMap R A) := inferInstanceAs (IsLocalHom (N.stalkMap q).hom)
  have _ : Module.Flat R A := Flat.stalkMap N q
  have h := length_baseChange_eq_length_mul_length_quotient R A R
  have hquot := length_quotient_map_maximalIdeal_eq_length_fiberStalk N q rfl (y := N.asFiber q) rfl
  rw [(Algebra.TensorProduct.rid R A A).toLinearEquiv.length_eq] at h
  exact h.symm.trans (congrArg _ hquot)

/-- **Stacks Project, Example 0GKI, final claim.** Let `f : X ⟶ Y` be flat, locally quasi-finite
and locally of finite presentation and let `f' : X' ⟶ Y'` be a base change of `f` along
`g : Y' ⟶ Y`, with `p : X' ⟶ X` the projection. Then the canonical weighting of `f'` is the
restriction along `p` of the canonical weighting of `f`.

The weight at a point is the length of the local ring of the scheme-theoretic fibre through it
times the inseparable degree of the residue field extension. The comparison morphism of fibres
`N` is flat, so Tag `02M1` splits the length upstairs as the length downstairs times the length
of the local ring of the fibre of `N`, and
`Stacks.Chow.length_fiberStalk_mul_finInsepDegree_of_isPullback` trades that last length against
the two inseparable degrees. -/
@[stacks 0GKI "the final claim: any base change `f'` of `f` satisfies the same three hypotheses \
-- which is `AlgebraicGeometry.Flat.isStableUnderBaseChange`, \
`AlgebraicGeometry.locallyQuasiFinite_isStableUnderBaseChange` and \
`AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange`, recorded on the tag in \
`StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.WeightingBaseChange` -- and that the canonical \
weighting `w` of the example restricts along the projection to the canonical weighting of `f'`",
  stacks 0F3D "base-change invariance of the function of the formula"]
theorem flatQuasiFiniteWeight_of_isPullback {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    {p : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback p f' f g)
    [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f] :
    flatQuasiFiniteWeight f' = flatQuasiFiniteWeight f ∘ p := by
  have _ : LocallyQuasiFinite f' := MorphismProperty.of_isPullback sq inferInstance
  funext x'
  let _ : Algebra ↥(Y'.residueField (f' x')) ↥(X'.residueField x') :=
    (f'.residueFieldMap x').hom.toAlgebra
  let _ : Algebra ↥(Y.residueField (f (p x'))) ↥(X.residueField (p x')) :=
    (f.residueFieldMap (p x')).hom.toAlgebra
  -- the comparison morphism of fibres, and its flatness
  set N := restrictedFiberMap f f' p g sq.w (f' x') with hNdef
  have _ : Flat N := MorphismProperty.of_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback sq (f' x')).flip
    (Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField
      (Field.toIsField ↥(Y.residueField (g (f' x')))) _))
  -- the point of the fibre of `f'` at which everything is read
  set q : f'.fiber (f' x') := f'.asFiber x' with hqdef
  -- Step 1: `02M1` for the flat morphism `N` of fibres at `q`, which is
  -- `length_stalk_eq_length_stalk_mul_length_fiberStalk N q`, used in Step 4
  -- Step 2: the weight of `f'` at `x'`, read on the fibre of `f'`
  have hw' : flatQuasiFiniteWeight f' x' =
      ((Module.length ((f'.fiber (f' x')).presheaf.stalk q)
          ((f'.fiber (f' x')).presheaf.stalk q)).toNat : ℤ) *
        (Field.finInsepDegree ↥(Y'.residueField (f' x')) ↥(X'.residueField x') : ℤ) := by
    simp only [flatQuasiFiniteWeight]
    rw [length_quotient_map_maximalIdeal_eq_length_fiberStalk f' x' rfl (y := q) rfl]
  -- Step 3: the weight of `f` at `p x'`, read on the fibre of `f` at the transported point
  have hw : flatQuasiFiniteWeight f (p x') =
      ((Module.length ((f.fiber (g (f' x'))).presheaf.stalk (N q))
          ((f.fiber (g (f' x'))).presheaf.stalk (N q))).toNat : ℤ) *
        (Field.finInsepDegree ↥(Y.residueField (f (p x'))) ↥(X.residueField (p x')) : ℤ) := by
    have hx : f (p x') = g (f' x') := congrArg (fun m : X' ⟶ Y => m x') sq.w
    have hy : N q = eqToHom (congrArg (fun u : Y => f.fiber u) hx) (f.asFiber (p x')) := by
      rw [hNdef, hqdef]
      exact Stacks.Chow.restrictedFiberMap_asFiber f f' p g sq.w x'
    simp only [flatQuasiFiniteWeight]
    rw [length_quotient_map_maximalIdeal_eq_length_fiberStalk f (p x') hx hy]
  -- Step 4: trade the length of the fibre of `N` against the two inseparable degrees
  have hins := Stacks.Chow.length_fiberStalk_mul_finInsepDegree_of_isPullback f sq x' N hNdef
  rw [Function.comp_apply, hw', hw, length_stalk_eq_length_stalk_mul_length_fiberStalk N q,
    ENat.toNat_mul]
  push_cast
  rw [mul_assoc]
  exact congrArg (fun n : ℕ => ((Module.length ((f.fiber (g (f' x'))).presheaf.stalk (N q))
    ((f.fiber (g (f' x'))).presheaf.stalk (N q))).toNat : ℤ) * (n : ℤ)) hins

end AlgebraicGeometry

end
