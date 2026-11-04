module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FamilyCoeff
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.RestrictionAction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Weighting
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingBaseChangeFibre
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingInverse
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksCore.Tactic.StacksAttribute

/-!
# The weighting of a family of zero-cycles is compatible with base change

Let `f : X ⟶ S` be locally of finite type and locally quasi-finite and let `α` be a family of
`0`-cycles on the fibres of `X/S`. For an arbitrary morphism `g : S' ⟶ S` the function
`w_{g^*α}` attached to the base-changed family on `X ×_S S' ⟶ S'` is the pullback of `w_α` along
the projection `X ×_S S' ⟶ X`.

At a point `z` of `X ×_S S'` with images `x` in `X` and `s'` in `S'` the claim unwinds, after
cancelling the coefficient of `α` at `x`, to

`mult(z) * [κ(z) : κ(s')]_i = [κ(x) : κ(s)]_i`,

`mult(z)` being the multiplicity with which `z` enters the base-changed family, that is the
length of the local ring of the fibre of the induced morphism of fibres. That identity is
`Stacks.Chow.length_fiberStalk_mul_finInsepDegree_eq`.

## Main results

* `Stacks.Chow.residueFieldFiberAlgEquiv` — the residue field of a scheme-theoretic fibre at
  `q.asFiber x` is the residue field at `x`, as an algebra over the residue field of `q x`.
* `Stacks.Chow.finInsepDegree_residueField_fiber` and
  `Stacks.Chow.module_finite_residueField_fiber` — the inseparable degree and the finiteness of
  that extension, read on the fibre.
* `Stacks.Chow.relativeDimension_fiberToSpecResidueField_eq_zero_of_locallyQuasiFinite` — every
  point of a fibre of a locally quasi-finite morphism has relative dimension zero.
* `Stacks.Chow.baseChangeFamily_apply_eq_mul_fiberStalkLength` — the fibrewise coefficient of a
  base-changed family of `0`-cycles is the coefficient of the original family at the image point
  times the length of the local ring of the fibre of the induced morphism of fibres.
* `Stacks.Chow.length_fiberStalk_mul_finInsepDegree_pullback` — the displayed identity above.
* `Stacks.Chow.relativeCycleWeight_baseChangeFamily` — compatibility of `α ↦ w_α` with base
  change.

## Implementation notes

The `κ(s)`-algebra structure on the residue field of a fibre is the one cut out by
`Scheme.Hom.fiberToSpecResidueField`, written through global sections and evaluation; it is
never an instance, and every statement introduces it in its own `let` binding, in the form in
which `Stacks.Chow.length_fiberStalk_mul_finInsepDegree_eq` produces it.

The image `f x` of a point of `X ×_S S'` in `S` and the image `g s'` of its image in `S'` are
equal, but not definitionally so: the equality is `pullback.condition` read at the point. The
comparison of the residue field of the fibre over `g s'` with `κ(x)` is therefore stated with the
base point of the fibre a free variable and the point of the fibre transported along
`eqToHom`, which the two substitutions in the proof dispose of; this keeps the `eqToHom` out of
any position where the elaborator would have to reduce it.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace Stacks.Chow

/-! ### The residue field of a scheme-theoretic fibre -/

/-- The residue field of the scheme-theoretic fibre of `q : X ⟶ Y` over `q x` at the point
`q.asFiber x` is isomorphic, as an algebra over `κ(q x)`, to `κ(x)`. On the fibre the algebra
structure is the one cut out by `Scheme.Hom.fiberToSpecResidueField`, on `κ(x)` the one cut out
by `Scheme.Hom.residueFieldMap`. -/
def residueFieldFiberAlgEquiv {X Y : Scheme.{u}} (q : X ⟶ Y) (x : X) :
    letI : Algebra (Y.residueField (q x)) ((q.fiber (q x)).residueField (q.asFiber x)) :=
      ((Scheme.ΓSpecIso (Y.residueField (q x))).inv ≫
        (q.fiberToSpecResidueField (q x)).appTop ≫
        (q.fiber (q x)).Γevaluation (q.asFiber x)).hom.toAlgebra
    letI : Algebra (Y.residueField (q x)) (X.residueField x) :=
      (q.residueFieldMap x).hom.toAlgebra
    (X.residueField x : Type u) ≃ₐ[Y.residueField (q x)]
      ((q.fiber (q x)).residueField (q.asFiber x) : Type u) := by
  let _ : Algebra (Y.residueField (q x)) ((q.fiber (q x)).residueField (q.asFiber x)) :=
    ((Scheme.ΓSpecIso (Y.residueField (q x))).inv ≫
      (q.fiberToSpecResidueField (q x)).appTop ≫
      (q.fiber (q x)).Γevaluation (q.asFiber x)).hom.toAlgebra
  let _ : Algebra (Y.residueField (q x)) (X.residueField x) :=
    (q.residueFieldMap x).hom.toAlgebra
  refine AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective (q.fiberResidueFieldHom x).hom
      (q.bijective_fiberResidueFieldHom x)) fun a => ?_
  have h := DFunLike.congr_fun
    (congrArg CommRingCat.Hom.hom (q.fiberResidueFieldHom_algebraMap x)) a
  simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] at h
  exact h.symm

/-- The residue field of a scheme-theoretic fibre has the same inseparable degree over the
residue field of the base point as the residue field of the corresponding point of the source. -/
theorem finInsepDegree_residueField_fiber {X Y : Scheme.{u}} (q : X ⟶ Y) (x : X) :
    letI : Algebra (Y.residueField (q x)) ((q.fiber (q x)).residueField (q.asFiber x)) :=
      ((Scheme.ΓSpecIso (Y.residueField (q x))).inv ≫
        (q.fiberToSpecResidueField (q x)).appTop ≫
        (q.fiber (q x)).Γevaluation (q.asFiber x)).hom.toAlgebra
    letI : Algebra (Y.residueField (q x)) (X.residueField x) :=
      (q.residueFieldMap x).hom.toAlgebra
    Field.finInsepDegree (Y.residueField (q x))
        ((q.fiber (q x)).residueField (q.asFiber x)) =
      Field.finInsepDegree (Y.residueField (q x)) (X.residueField x) := by
  let _ : Algebra (Y.residueField (q x)) ((q.fiber (q x)).residueField (q.asFiber x)) :=
    ((Scheme.ΓSpecIso (Y.residueField (q x))).inv ≫
      (q.fiberToSpecResidueField (q x)).appTop ≫
      (q.fiber (q x)).Γevaluation (q.asFiber x)).hom.toAlgebra
  let _ : Algebra (Y.residueField (q x)) (X.residueField x) :=
    (q.residueFieldMap x).hom.toAlgebra
  exact (Field.finInsepDegree_eq_of_equiv _ _ _ (residueFieldFiberAlgEquiv q x)).symm

/-- If the residue-field extension at `x` is finite, so is the extension cut out on the residue
field of the scheme-theoretic fibre at the corresponding point. -/
theorem module_finite_residueField_fiber {X Y : Scheme.{u}} (q : X ⟶ Y) (x : X)
    (hfin : letI : Algebra (Y.residueField (q x)) (X.residueField x) :=
        (q.residueFieldMap x).hom.toAlgebra
      Module.Finite (Y.residueField (q x)) (X.residueField x)) :
    letI : Algebra (Y.residueField (q x)) ((q.fiber (q x)).residueField (q.asFiber x)) :=
      ((Scheme.ΓSpecIso (Y.residueField (q x))).inv ≫
        (q.fiberToSpecResidueField (q x)).appTop ≫
        (q.fiber (q x)).Γevaluation (q.asFiber x)).hom.toAlgebra
    Module.Finite (Y.residueField (q x)) ((q.fiber (q x)).residueField (q.asFiber x)) := by
  let _ : Algebra (Y.residueField (q x)) ((q.fiber (q x)).residueField (q.asFiber x)) :=
    ((Scheme.ΓSpecIso (Y.residueField (q x))).inv ≫
      (q.fiberToSpecResidueField (q x)).appTop ≫
      (q.fiber (q x)).Γevaluation (q.asFiber x)).hom.toAlgebra
  let _ : Algebra (Y.residueField (q x)) (X.residueField x) :=
    (q.residueFieldMap x).hom.toAlgebra
  have _ : Module.Finite (Y.residueField (q x)) (X.residueField x) := hfin
  exact Module.Finite.equiv (residueFieldFiberAlgEquiv q x).toLinearEquiv

/-! ### Transport along the base point of a fibre -/

/-- The inseparable degree comparison of `Stacks.Chow.finInsepDegree_residueField_fiber` read on
the fibre over a point `s` equal to `f x` but not definitionally so: the point of the fibre is
`f.asFiber x` transported along the equality of base points. -/
theorem finInsepDegree_residueField_fiber_eqToHom {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (s : S)
    (hp : f x = s) (y : f.fiber s)
    (hy : y = eqToHom (congrArg (fun u : S => f.fiber u) hp) (f.asFiber x)) :
    letI : Algebra ↥(S.residueField s) ↥((f.fiber s).residueField y) :=
      ((Scheme.ΓSpecIso (.of ↥(S.residueField s))).inv ≫
        (f.fiberToSpecResidueField s).appTop ≫ (f.fiber s).Γevaluation y).hom.toAlgebra
    letI : Algebra ↥(S.residueField (f x)) ↥(X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    Field.finInsepDegree ↥(S.residueField s) ↥((f.fiber s).residueField y) =
      Field.finInsepDegree ↥(S.residueField (f x)) ↥(X.residueField x) := by
  subst hp
  subst hy
  exact finInsepDegree_residueField_fiber f x

/-- The finiteness of `Stacks.Chow.module_finite_residueField_fiber` read on the fibre over a
point `s` equal to `f x` but not definitionally so. -/
theorem module_finite_residueField_fiber_eqToHom {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyQuasiFinite f] (x : X) (s : S) (hp : f x = s) (y : f.fiber s)
    (hy : y = eqToHom (congrArg (fun u : S => f.fiber u) hp) (f.asFiber x)) :
    letI : Algebra ↥(S.residueField s) ↥((f.fiber s).residueField y) :=
      ((Scheme.ΓSpecIso (.of ↥(S.residueField s))).inv ≫
        (f.fiberToSpecResidueField s).appTop ≫ (f.fiber s).Γevaluation y).hom.toAlgebra
    Module.Finite ↥(S.residueField s) ↥((f.fiber s).residueField y) := by
  subst hp
  subst hy
  exact module_finite_residueField_fiber f x (module_finite_residueFieldMap f x)

/-! ### Relative dimension on the fibres of a locally quasi-finite morphism -/

/-- Every point of a scheme-theoretic fibre of a locally quasi-finite morphism has relative
dimension zero over the residue field of the base point: see
`Stacks.Chow.relativeDimension_fiber_eq_zero_of_locallyQuasiFinite`. -/
alias relativeDimension_fiberToSpecResidueField_eq_zero_of_locallyQuasiFinite :=
  Stacks.Chow.relativeDimension_fiber_eq_zero_of_locallyQuasiFinite

/-! ### The coefficient of a base-changed family of zero-cycles -/

/-- **Stacks Project, Tag 0H4N for `0`-cycles.** The fibrewise coefficient of the base change of
a family of `0`-cycles along `g : S' ⟶ S` at a point `x` of the fibre over `t` is the coefficient
of the original family at the image of `x` under the induced morphism `N` of fibres, times the
length of the local ring of the scheme-theoretic fibre of `N` through `x`.

For a locally quasi-finite `f` every point of a fibre has relative dimension zero, so the case
distinction in `Stacks.Chow.flatPullbackWeight_eq_fiberStalkLength` is always resolved
positively. -/
theorem baseChangeFamily_apply_eq_mul_fiberStalkLength {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (g : S' ⟶ S) (α : FamilyOfCycles f 0)
    (t : S') (x : (pullback.snd f g).fiber t)
    (N : (pullback.snd f g).fiber t ⟶ f.fiber (g t))
    (hN : N = restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
      pullback.condition t) :
    (baseChangeFamily f g 0 α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ) (N x) *
        ((Module.length ((N.fiber (N x)).presheaf.stalk (N.asFiber x))
            ((N.fiber (N x)).presheaf.stalk (N.asFiber x))).toNat : ℤ) := by
  subst hN
  have : LocallyOfFiniteType ((pullback.snd f g).fiberToSpecResidueField t) := by
    show LocallyOfFiniteType (pullback.snd (pullback.snd f g) (S'.fromSpecResidueField t))
    infer_instance
  have hdim : relativeDimension (fieldChowSituation ↥(S'.residueField t)).dimensionFunction
      ((pullback.snd f g).fiberToSpecResidueField t) x = ((0 : ℕ) : ℤ) := by
    rw [Nat.cast_zero]
    exact relativeDimension_fiberToSpecResidueField_eq_zero_of_locallyQuasiFinite
      (pullback.snd f g) t x
  have hfold := flatPullbackWeight_eq_fiberStalkLength (fieldChowSituation ↥(S'.residueField t))
    ((pullback.snd f g).fiberToSpecResidueField t)
    (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t)
    ((0 : ℕ) : ℤ) x
  rw [if_pos hdim] at hfold
  rw [baseChangeFamily_apply, ← hfold]
  rfl

/-! ### The degree identity at a point of a base change -/

/-- **Stacks Project, Tag 0H5P, first paragraph.** At a point `z` of `X ×_S S'` with images `x`
in `X` and `t` in `S'`, the length of the local ring of the fibre of the induced morphism of
fibres through `z` times the inseparable degree of `κ(z)` over `κ(t)` is the inseparable degree
of `κ(x)` over `κ(f x)`.

The fibre of `(X ×_S S')_t ⟶ X_{g t}` through `z` is the spectrum of `κ(t) ⊗_{κ(g t)} κ(x)`, so
this is `Stacks.Chow.length_fiberStalk_mul_finInsepDegree_eq` applied to the cartesian square of
Tag 0H4N, after identifying the residue fields of the two fibres with `κ(z)` and `κ(x)`. -/
theorem length_fiberStalk_mul_finInsepDegree_pullback {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (g : S' ⟶ S)
    (z : (pullback f g : Scheme.{u}))
    (N : (pullback.snd f g).fiber ((pullback.snd f g) z) ⟶
      f.fiber (g ((pullback.snd f g) z)))
    (hN : N = restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
      ((pullback.snd f g) z)) :
    letI : Algebra ↥(S'.residueField ((pullback.snd f g) z))
        ↥((pullback f g : Scheme.{u}).residueField z) :=
      ((pullback.snd f g).residueFieldMap z).hom.toAlgebra
    letI : Algebra ↥(S.residueField (f ((pullback.fst f g) z)))
        ↥(X.residueField ((pullback.fst f g) z)) :=
      (f.residueFieldMap ((pullback.fst f g) z)).hom.toAlgebra
    (Module.length
          ((N.fiber (N ((pullback.snd f g).asFiber z))).presheaf.stalk
            (N.asFiber ((pullback.snd f g).asFiber z)))
          ((N.fiber (N ((pullback.snd f g).asFiber z))).presheaf.stalk
            (N.asFiber ((pullback.snd f g).asFiber z)))).toNat *
        Field.finInsepDegree ↥(S'.residueField ((pullback.snd f g) z))
          ↥((pullback f g : Scheme.{u}).residueField z) =
      Field.finInsepDegree ↥(S.residueField (f ((pullback.fst f g) z)))
        ↥(X.residueField ((pullback.fst f g) z)) := by
  subst hN
  let _ : Algebra ↥(S'.residueField ((pullback.snd f g) z))
      ↥((pullback f g : Scheme.{u}).residueField z) :=
    ((pullback.snd f g).residueFieldMap z).hom.toAlgebra
  let _ : Algebra ↥(S.residueField (f ((pullback.fst f g) z)))
      ↥(X.residueField ((pullback.fst f g) z)) :=
    (f.residueFieldMap ((pullback.fst f g) z)).hom.toAlgebra
  let _ : Algebra ↥(S.residueField (g ((pullback.snd f g) z)))
      ↥(S'.residueField ((pullback.snd f g) z)) :=
    (g.residueFieldMap ((pullback.snd f g) z)).hom.toAlgebra
  let _ : Algebra ↥(S.residueField (g ((pullback.snd f g) z)))
      ↥((f.fiber (g ((pullback.snd f g) z))).residueField
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
          ((pullback.snd f g) z) ((pullback.snd f g).asFiber z))) :=
    ((Scheme.ΓSpecIso (.of ↥(S.residueField (g ((pullback.snd f g) z))))).inv ≫
      (f.fiberToSpecResidueField (g ((pullback.snd f g) z))).appTop ≫
      (f.fiber (g ((pullback.snd f g) z))).Γevaluation
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
          ((pullback.snd f g) z) ((pullback.snd f g).asFiber z))).hom.toAlgebra
  let _ : Algebra ↥(S'.residueField ((pullback.snd f g) z))
      ↥(((pullback.snd f g).fiber ((pullback.snd f g) z)).residueField
        ((pullback.snd f g).asFiber z)) :=
    ((Scheme.ΓSpecIso (.of ↥(S'.residueField ((pullback.snd f g) z)))).inv ≫
      ((pullback.snd f g).fiberToSpecResidueField ((pullback.snd f g) z)).appTop ≫
      ((pullback.snd f g).fiber ((pullback.snd f g) z)).Γevaluation
        ((pullback.snd f g).asFiber z)).hom.toAlgebra
  have hx : f ((pullback.fst f g) z) = g ((pullback.snd f g) z) :=
    congrArg (fun m : (pullback f g : Scheme.{u}) ⟶ S => m z) pullback.condition
  have hy : restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
        ((pullback.snd f g) z) ((pullback.snd f g).asFiber z) =
      eqToHom (congrArg (fun u : S => f.fiber u) hx) (f.asFiber ((pullback.fst f g) z)) :=
    restrictedFiberMap_asFiber f (pullback.snd f g) (pullback.fst f g) g pullback.condition z
  have hfin : Module.Finite ↥(S.residueField (g ((pullback.snd f g) z)))
      ↥((f.fiber (g ((pullback.snd f g) z))).residueField
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
          ((pullback.snd f g) z) ((pullback.snd f g).asFiber z))) :=
    module_finite_residueField_fiber_eqToHom f ((pullback.fst f g) z)
      (g ((pullback.snd f g) z)) hx _ hy
  have hsq : IsPullback
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
        ((pullback.snd f g) z))
      ((pullback.snd f g).fiberToSpecResidueField ((pullback.snd f g) z))
      (f.fiberToSpecResidueField (g ((pullback.snd f g) z)))
      (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(S.residueField (g ((pullback.snd f g) z)))
          ↥(S'.residueField ((pullback.snd f g) z))))) :=
    isPullback_restrictedFiberMap_baseChange f g ((pullback.snd f g) z)
  have hM := length_fiberStalk_mul_finInsepDegree_eq
    ↥(S.residueField (g ((pullback.snd f g) z))) ↥(S'.residueField ((pullback.snd f g) z))
    (f.fiberToSpecResidueField (g ((pullback.snd f g) z)))
    ((pullback.snd f g).fiberToSpecResidueField ((pullback.snd f g) z))
    (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
      ((pullback.snd f g) z))
    hsq ((pullback.snd f g).asFiber z) hfin
  have hC1 : Field.finInsepDegree ↥(S'.residueField ((pullback.snd f g) z))
        ↥(((pullback.snd f g).fiber ((pullback.snd f g) z)).residueField
          ((pullback.snd f g).asFiber z)) =
      Field.finInsepDegree ↥(S'.residueField ((pullback.snd f g) z))
        ↥((pullback f g : Scheme.{u}).residueField z) :=
    finInsepDegree_residueField_fiber (pullback.snd f g) z
  have hC2 : Field.finInsepDegree ↥(S.residueField (g ((pullback.snd f g) z)))
        ↥((f.fiber (g ((pullback.snd f g) z))).residueField
          (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
            ((pullback.snd f g) z) ((pullback.snd f g).asFiber z))) =
      Field.finInsepDegree ↥(S.residueField (f ((pullback.fst f g) z)))
        ↥(X.residueField ((pullback.fst f g) z)) :=
    finInsepDegree_residueField_fiber_eqToHom f ((pullback.fst f g) z)
      (g ((pullback.snd f g) z)) hx _ hy
  rwa [← hC1, ← hC2]

/-! ### Compatibility of the weighting with base change -/

/-- **Stacks Project, Tag 0H5P.** For a locally quasi-finite morphism locally of finite type the
construction `α ↦ w_α` is compatible with an arbitrary base change `g : S' ⟶ S`: the function
attached to the base-changed family of `0`-cycles on the fibres of `X ×_S S' ⟶ S'` is the
pullback of `w_α` along the projection to `X`. -/
theorem relativeCycleWeight_baseChangeFamily {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (g : S' ⟶ S) (α : FamilyOfCycles f 0) :
    relativeCycleWeight (Limits.pullback.snd f g) (baseChangeFamily f g 0 α) =
      relativeCycleWeight f α ∘ Limits.pullback.fst f g := by
  funext z
  let _ : Algebra ↥(S'.residueField ((pullback.snd f g) z))
      ↥((pullback f g : Scheme.{u}).residueField z) :=
    ((pullback.snd f g).residueFieldMap z).hom.toAlgebra
  let _ : Algebra ↥(S.residueField (f ((pullback.fst f g) z)))
      ↥(X.residueField ((pullback.fst f g) z)) :=
    (f.residueFieldMap ((pullback.fst f g) z)).hom.toAlgebra
  show (baseChangeFamily f g 0 α ((pullback.snd f g) z) :
        AlgebraicCycle ((pullback.snd f g).fiber ((pullback.snd f g) z)) ℤ)
        ((pullback.snd f g).asFiber z) *
      (Field.finInsepDegree ↥(S'.residueField ((pullback.snd f g) z))
        ↥((pullback f g : Scheme.{u}).residueField z) : ℤ) =
    (α (f ((pullback.fst f g) z)) :
        AlgebraicCycle (f.fiber (f ((pullback.fst f g) z))) ℤ)
        (f.asFiber ((pullback.fst f g) z)) *
      (Field.finInsepDegree ↥(S.residueField (f ((pullback.fst f g) z)))
        ↥(X.residueField ((pullback.fst f g) z)) : ℤ)
  have hcoeff : (α (g ((pullback.snd f g) z)) :
        AlgebraicCycle (f.fiber (g ((pullback.snd f g) z))) ℤ)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
          ((pullback.snd f g) z) ((pullback.snd f g).asFiber z)) =
      (α (f ((pullback.fst f g) z)) :
        AlgebraicCycle (f.fiber (f ((pullback.fst f g) z))) ℤ)
        (f.asFiber ((pullback.fst f g) z)) := by
    rw [familyCoeff_restrictedFiberMap f g 0 α ((pullback.snd f g) z)
      ((pullback.snd f g).asFiber z), Scheme.Hom.fiberι_asFiber]
    rfl
  have hdeg := length_fiberStalk_mul_finInsepDegree_pullback f g z
    (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
      ((pullback.snd f g) z)) rfl
  rw [baseChangeFamily_apply_eq_mul_fiberStalkLength f g α ((pullback.snd f g) z)
      ((pullback.snd f g).asFiber z)
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
        ((pullback.snd f g) z)) rfl,
    hcoeff, mul_assoc, ← Nat.cast_mul, hdeg]

end Stacks.Chow

end
