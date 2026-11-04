module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonAssembly
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonFactors
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonSection

/-!
# The tensor-comparison obligation split along the [stacks 068I] morphism

`Dualizing.TensorComparisonCompatibility` is the equation

`μ_{X, A} ≫ tensorComparisonOfIso X = 𝟙_{X ⊗ᴸ_R R'} ⊗ derivedBaseChangeAlgebraIso`,

and it is the only remaining input of `Dualizing.KFlatAlgebraActionEq`.  Its one unknown factor is
the lax monoidal structure map `μ` of derived base change along `R → R'`, which
`Dualizing.derivedTensorBaseChangeSection` inverts by a transpose of a component of
[stacks 0E1W]; so every reading of the obligation recorded in this directory ends in a determinate
value for `μ`, equivalently for `ν`, equivalently for that component
(`Dualizing.tensorComparisonCompatibility_iff_eq_inv`).

This file divides the obligation differently.  The [stacks 068I] morphism
`Dualizing.tensorBaseChangeMor` is a *second* candidate for the lax structure map: it is built
from the monoidality isomorphism of [stacks 068I] and the two tensor comparisons of [stacks 0A63],
it is invertible outright (`Dualizing.isIso_tensorBaseChangeMor`), and it has a chain-level value
at a pair of K-flat complexes (`Dualizing.tensorBaseChangeMor_comp_eq_q_obj`).  Replacing `μ` by
it splits the obligation into two:

* the **identification** `μ' = μ` — which is the keystone in the shape of
  `Dualizing.tensorBaseChangeMor_eq_iff_section_comp`, reduced to pairs of K-flat complexes by
  `Dualizing.tensorBaseChangeMor_eq_of_kFlat`, and whose component of [stacks 0E1W] is read at the
  *contravariant* object `Q L` for a K-flat `L` — the slot that
  `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat` and
  `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` were built to serve; and
* the **comparison identity** `μ' ≫ tensorComparisonOfIso X = 𝟙 ⊗ derivedBaseChangeAlgebraIso`, in
  which the lax structure map `μ`, its section `ν`, the component of [stacks 0E1W], the morphism
  of [stacks 0E1X], both transposes of [stacks 0GMT] and the `homEquiv` of [stacks 0A63] all fail
  to occur.  Every factor of it is a component of an isomorphism with a chain-level value at a
  K-flat complex.

The two are jointly equivalent to the obligation and neither is redundant: granted the comparison
identity, the obligation *is* the identification
(`Dualizing.tensorBaseChangeMor_eq_iff_tensorComparisonCompatibility`), the comparison across the
square being invertible by `Stacks.CategoryTheory.BaseChange.isIso_tensorComparisonOfIso`.

This is the bridge whose absence the docstrings of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeIdentification` and
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeBridge` record.  Both say
that a proof of the [stacks 068I] identification would leave
`Dualizing.TensorComparisonCompatibility` still to be derived, and that no declaration derives one
from the other; that is now false in the one direction that matters, and what the identification
leaves is named here.

**What is not done here.**  `Dualizing.TensorComparisonCompatibility` is not proved and no tag
loses its conditional caveat.  What changes is which unknown the obligation is reduced to: not a
value for `μ` — equivalently for a component of [stacks 0E1W] at the pair
`(A[0], baseChangeR X ⊗ᴸ_{R'} baseChangeR A[0])` — but the [stacks 068I] identification at a
K-flat *pair*, where `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates one side and
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat` the other,
together with one equation in which [stacks 0E1W] does not occur.

The second half is not itself free of work.  Its `μ'` is read at `(X, A[0])`, and
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates `μ'` at a pair of *K-flat* classes, while
the algebra is not K-flat over `R`; so a value for it there asks for a K-flat resolution of
`A` over `R`, transported by the naturality of `Dualizing.tensorBaseChangeNatIso` in its second
variable — which is `Dualizing.tensorBaseChangeMor_app_of_iso`, proved below.  That transport is
carried out in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonAlgebraResolution`, which
moves the whole comparison identity onto such a resolution: no new resolution API was needed,
`Dualizing.exists_kFlat_iso` already producing one from [stacks 06Y4].  It is the same resolution
the witness `eX` of
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` would ask
for at the obligation's own [stacks 0E1W] slot, so the split does not remove it; what it removes
is [stacks 0E1W] itself, and with it the circle in which a value for `μ` was the unknown and `ν`,
which is defined by a transpose of that component, was the only thing available to express it.

## Main results

* `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_of_values` — the comparison across a
  square of adjunctions in terms of given values for three of its four factors.  Stated over
  variable categories so that an instantiation at the base-change square *computes* its type
  instead of unifying two spellings of it.
* `Dualizing.tensorBaseChangeMor_app_of_iso` — the [stacks 068I] morphism transported along an
  isomorphism of its second variable, which is what reads it at the algebra: the algebra is not
  K-flat over `R`, while `Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates that morphism at
  a pair of K-flat classes.
* `Dualizing.tensorComparisonOfIso_app_q_obj` — **the comparison across the base-change square at
  the class of a K-flat complex**, with each of its three component-formula factors moved to a
  class of a cochain complex.  This is the transpose-free analogue of
  `Dualizing.tensorComparisonCompatibility_lhs_app_q_obj`, and it is the left-hand factor of both
  the comparison identity below and the hypothesis of
  `Dualizing.tensorComparisonCompatibility_of_section_q_obj`.
* `Dualizing.tensorComparisonCompatibility_iff_tensorBaseChangeMor` — **granted the
  [stacks 068I] identification at `(X, A[0])`, the obligation is the comparison identity.**
* `Dualizing.tensorBaseChangeMor_eq_iff_tensorComparisonCompatibility` — **granted the comparison
  identity at `X`, the obligation is the [stacks 068I] identification at `(X, A[0])`.**
* `Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` — **the split**: the obligation
  at every object of `D(R)` from the identification at pairs of K-flat complexes and the
  comparison identity at the classes of K-flat complexes.

## Implementation notes

`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_of_values` takes the three values as
implicit arguments determined by their defining equations, so that `subst` leaves a goal closed by
`rfl`; passing them explicitly would make the statement reprint the four-factor composite.

It has to be applied by `exact` to three component formulas already bound by `have`, not by
`refine … ?_ ?_ ?_` against the written right-hand side.  The latter form of
`Dualizing.tensorComparisonOfIso_app_q_obj` dies at `(deterministic) timeout at isDefEq, 200000
heartbeats`: splitting the goal makes the elaborator assign the three implicit values by matching
the written composite against `Lg.map (pf.inv.app X) ≫ ?u ≫ Rf'.map ?c ≫ ?p`, in which `Rf'.map
?c` has to be recognized in a `mapDerivedCategory.map` of a composite comparison, across the same
two spellings of the comparison's target that
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.SquareCounitConjugate` documents as
definitionally but not syntactically equal.  Binding the three formulas first determines the
values from *their* statements, and the one defeq check left — the written composite against the
computed one — takes the whole declaration to under four seconds.

The reductions below are `congrArg` and `Eq.trans` against a known first argument, never `rw`
inside the obligation: `Dualizing.TensorComparisonCompatibility` is a `def` whose body is the
equation, the idiom `replace h : _ = _ := h` and `show _ = _` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonReduction` moving between
the two.  The source of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` at this square is
spelled with `Dualizing.derivedExtendRestrictScalarsTensorFunctor` while the target of both
candidate structure maps is spelled with the tensor bifunctor of [stacks 0A63]; the two agree
definitionally but not syntactically, so `Dualizing.derivedExtendRestrictScalarsTensorFunctor_map`
is the `rfl` that `rw` would have to cross and does not.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedTensor
open CochainComplex.DerivedExtensionScalars

namespace Stacks.CategoryTheory.BaseChange

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {A' : Type u₃} {B' : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Lg' : B ⥤ B'}

/-- **The comparison across a square of adjunctions, from values for three of its four factors.**
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` is the inverse projection formula over
the base, the inverse of the base-change isomorphism `Θ` at `Lf X`, the right adjoint `Rf'`
applied to the comparison `γ` of the two composites around the square at `X`, and the projection
formula over `A'` at `Lg X`.  Given values for the last three, this is the comparison with those
values substituted; the first factor is left alone, being the one for which no component formula
is in play.

Nothing is assumed of the values beyond their defining equations, and nothing of the square beyond
the four isomorphisms.  The point of stating it over variable categories is that an instantiation
at a concrete square — the base-change square of a Tor-independent pair of ring maps, say — has
its type *computed* from the arguments rather than unified against a second spelling of the
comparison's source, which is where keyed matching across
`Dualizing.derivedExtendRestrictScalarsTensorFunctor_map` fails. -/
theorem tensorComparisonOfIso_eq_of_values {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) (X : A)
    {u : Lg.obj (Rf.obj (Lf.obj X)) ⟶ Rf'.obj (Lg'.obj (Lf.obj X))}
    {c : Lg'.obj (Lf.obj X) ⟶ Lf'.obj (Lg.obj X)}
    {p : Rf'.obj (Lf'.obj (Lg.obj X)) ⟶ Tens'.obj (Lg.obj X)}
    (hu : Θ.inv.app (Lf.obj X) = u) (hc : γ.hom.app X = c)
    (hp : pf'.hom.app (Lg.obj X) = p) :
    tensorComparisonOfIso pf pf' γ Θ X = Lg.map (pf.inv.app X) ≫ u ≫ Rf'.map c ≫ p := by
  subst hu
  subst hc
  subst hp
  rfl

/-- **The comparison across a square of adjunctions may be cancelled on the right.**  Each of the
four factors of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` is a component of an
isomorphism of functors, or a functor applied to one, so the comparison is invertible
(`Stacks.CategoryTheory.BaseChange.isIso_tensorComparisonOfIso`) and two morphisms into its source
with the same composite agree.

Stated over variable categories for the reason recorded on
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_of_values`, and proved by composing
with the inverse rather than through `CategoryTheory.cancel_mono`, which asks for a `Mono`
instance that instance resolution does not produce from the invertibility here. -/
theorem eq_of_comp_tensorComparisonOfIso_eq {Tens : A ⥤ A} {Tens' : A' ⥤ A'}
    (pf : Lf ⋙ Rf ≅ Tens) (pf' : Lf' ⋙ Rf' ≅ Tens')
    (γ : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (Θ : Lg' ⋙ Rf' ≅ Rf ⋙ Lg) (X : A)
    {W : A'} {a b : W ⟶ Lg.obj (Tens.obj X)}
    (h : a ≫ tensorComparisonOfIso pf pf' γ Θ X =
      b ≫ tensorComparisonOfIso pf pf' γ Θ X) :
    a = b := by
  haveI := isIso_tensorComparisonOfIso pf pf' γ Θ X
  rw [← Category.comp_id a, ← IsIso.hom_inv_id (tensorComparisonOfIso pf pf' γ Θ X),
    ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Stacks.CategoryTheory.BaseChange

namespace Dualizing

section BaseChangeMorTransport

universe uR₀ uA₀ uM₀

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR₀} {A : Type uA₀} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR₀ uA₀ uM₀} R) ⥤
    DerivedCategory (ModuleCat.{max uR₀ uA₀ uM₀} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR₀, uA₀, max uR₀ uA₀ uM₀} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [hF : F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR₀ uA₀ uM₀} R) (ComplexShape.up ℤ))]
  (D : TotalDerivedExtensionScalars.{uR₀, max uR₀ uA₀ uM₀, uA₀,
    max uR₀ uA₀ uM₀ + 1, max uR₀ uA₀ uM₀ + 1} f)

include hF in
/-- **The [stacks 068I] morphism transported along an isomorphism of its second variable.**
`Dualizing.tensorBaseChangeMor` is a component of the isomorphism
`Dualizing.tensorBaseChangeNatIso`, so it is natural in both variables; its value at `(X, Y)` is
therefore determined by its value at `(X, Y')` for any isomorphism `b : Y ≅ Y'`, the morphism of
`D(A)` that the naturality square is postcomposed with being `F` applied to the tensor bifunctor
of [stacks 0A63] at an isomorphism, hence invertible.

This is what reads the [stacks 068I] morphism at the chapter's second variable.
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` evaluates it at a pair of localizations of *K-flat*
complexes, while the obligation
`Dualizing.TensorComparisonCompatibility` fixes the second variable to the algebra
`Dualizing.derivedAlgebraSingle`, which is not K-flat over `R`; so its value there is this
transport along a K-flat resolution, which exists by `Dualizing.exists_kFlat_iso`.

Compare `Dualizing.tensorBaseChangeMor_eq_of_iso`, which transports the *equation* `μ' = μ` in
both variables at once and so needs no inverse on the right; here it is the morphism itself that
is transported, and the inverse of `b` appears. -/
theorem tensorBaseChangeMor_app_of_iso
    (X : DerivedCategory (ModuleCat.{max uR₀ uA₀ uM₀} R))
    {Y Y' : DerivedCategory (ModuleCat.{max uR₀ uA₀ uM₀} R)} (b : Y ≅ Y') :
    tensorBaseChangeMor.{uR₀, uA₀, uM₀} f F comparison D X Y =
      (derivedHomAdjunctionOverRing.{uA₀, max uR₀ uA₀ uM₀,
            max uR₀ uA₀ uM₀ + 1} A).tensor.map
          ((𝟙 (F.obj X), F.map b.hom) : (F.obj X, F.obj Y) ⟶ (F.obj X, F.obj Y')) ≫
        tensorBaseChangeMor.{uR₀, uA₀, uM₀} f F comparison D X Y' ≫
          F.map ((derivedHomAdjunctionOverRing.{uR₀, max uR₀ uA₀ uM₀,
              max uR₀ uA₀ uM₀ + 1} R).tensor.map
            ((𝟙 X, b.inv) : (X, Y') ⟶ (X, Y))) := by
  have hnat := (tensorBaseChangeNatIso.{uR₀, uA₀, uM₀} f F comparison D).hom.naturality
    ((𝟙 X, b.hom) : ((X, Y) : DerivedCategory (ModuleCat.{max uR₀ uA₀ uM₀} R) ×
      DerivedCategory (ModuleCat.{max uR₀ uA₀ uM₀} R)) ⟶ (X, Y'))
  have hpair : (CategoryTheory.Prod.mkHom (F.map (𝟙 X)) (F.map b.hom) :
        (F.obj X, F.obj Y) ⟶ (F.obj X, F.obj Y')) =
      ((𝟙 (F.obj X), F.map b.hom) : (F.obj X, F.obj Y) ⟶ (F.obj X, F.obj Y')) :=
    congrArg (fun z => (z, F.map b.hom)) (F.map_id X)
  dsimp only [Functor.comp_map, Functor.prod_map] at hnat
  rw [hpair] at hnat
  dsimp only [tensorBaseChangeMor]
  rw [← Category.assoc, hnat, Category.assoc, ← F.map_comp,
    (derivedHomAdjunctionOverRing.{uR₀, max uR₀ uA₀ uM₀,
      max uR₀ uA₀ uM₀ + 1} R).tensor_map_comp (𝟙 X) b.hom (𝟙 X) b.inv,
    Category.comp_id, b.hom_inv_id,
    (derivedHomAdjunctionOverRing.{uR₀, max uR₀ uA₀ uM₀,
      max uR₀ uA₀ uM₀ + 1} R).tensor_map_id, F.map_id]
  exact (Category.comp_id _).symm

end BaseChangeMorTransport

universe uR uA uRp v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Ff : DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} A))
  (alphaf : DerivedCategory.Q ⋙ Ff ⟶
    (ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
      (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (Fi : DerivedCategory (ModuleCat.{max v uR uA uRp} R') ⥤
    DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (alphai : DerivedCategory.Q ⋙ Fi ⟶
    (ModuleCat.extendScalars.{uRp, max uA uRp, max v uR uA uRp}
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)

variable [hf : Ff.IsLeftDerivedFunctor alphaf
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))]
  [hR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ))]
  [hi : Fi.IsLeftDerivedFunctor alphai
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R') (ComplexShape.up ℤ))]

include hf hA hR hi in
/-- **The comparison across the base-change square at the class of a K-flat complex, with every
factor at a class of a cochain complex.**  Three of the four factors of
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` are read by the comparison at objects
that are not presented as classes:
`Dualizing.restrictionBaseChangeIsoGeneral` at `Ff (Q K)`, the base-change square isomorphism
`Dualizing.derivedBaseChangeSquareIso` at `Q K`, and the projection formula over `R'` at
`baseChangeR (Q K)`.  Substituting the three component formulas of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonFactors` and
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_baseChangeR_q_obj` moves each to a class:
the comparison of [stacks 0661] to `Q (A ⊗_R K)`, where
`Dualizing.restrictionBaseChangeIsoGeneral_inv_app_q_obj` evaluates it; the square isomorphism to
the two composite comparisons around the square, which are model data; and the projection formula
to `Q (R' ⊗_R K)`, where `Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` evaluates
it.  The inverse projection formula over `R` is left alone, being the factor for which no
component formula is in play — exactly as in
`Dualizing.tensorComparisonCompatibility_lhs_app_q_obj`, which does the same for the
0GMT-transposed reading of the obligation's left-hand side.  A consumer who needs that factor
evaluated should not look for a formula for it:
`Stacks.CategoryTheory.BaseChange.comp_tensorComparisonOfIso_eq_iff_tail` moves it to the other
side of whatever equation the comparison is read against, where only `pf.hom` occurs and
`Dualizing.derivedExtendRestrictScalarsTensorIso_hom_app_q_obj` applies.

This is that reading in the *transpose-free* shape — the one
`Dualizing.tensorComparisonCompatibility_iff_section` and
`Dualizing.tensorComparisonCompatibility_iff_tensorBaseChangeMor` consume — so no unit of
[stacks 0GMT] and no `homEquiv` of [stacks 0A63] occurs on either side.

The three invertibilities are instance binders rather than K-flatness hypotheses, as in
`Dualizing.derivedBaseChangeSquareIso_hom_app_q_obj`: at a K-flat `K` a consumer supplies them
from `Dualizing.isIso_alphaf_app_of_kFlat`, `Dualizing.isIso_comparisonR_app_of_kFlat` and
`Dualizing.isIso_compComparisonOfEq_right_app_of_kFlat`, and the statement is then free of any
hypothesis on `K`. -/
theorem tensorComparisonOfIso_app_q_obj
    (K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ)
    [IsIso (alphaf.app K)] [IsIso (comparisonR.app K)]
    [IsIso ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
      max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
      max v uR uA uRp + 1}
      (algebraMap R R')
      (Algebra.TensorProduct.includeRight :
        R' →ₐ[R] TensorProduct R A R').toRingHom
      baseChangeR comparisonR Fi alphai
      (algebraMap R (TensorProduct R A R'))
      algebraMap_tensorProduct_comp_right).app K)] :
    Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
        (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
        (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
        (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
          Fi alphai)
        (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
          comparisonA hA) (DerivedCategory.Q.obj K) =
      baseChangeR.map
          ((derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp}
            (algebraMap R A) Ff alphaf).inv.app (DerivedCategory.Q.obj K)) ≫
        (((ModuleCat.restrictScalars.{max v uR uA uRp}
                (algebraMap R A)).mapDerivedCategory ⋙ baseChangeR).map (alphaf.app K) ≫
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).inv.app
              (DerivedCategory.Q.obj
                (((ModuleCat.extendScalars.{uR, uA, max v uR uA uRp}
                  (algebraMap R A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
              (baseChangeA ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory).map
                (CategoryTheory.inv (alphaf.app K))) ≫
          (ModuleCat.restrictScalars.{max v uR uA uRp}
                (Algebra.TensorProduct.includeRight :
                  R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
              ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uA,
                    max uA uRp, max v uRp, max v uR uA uRp + 1, max v uR uA uRp + 1,
                    max v uR uA uRp + 1}
                    (algebraMap R A) (algebraMap A (TensorProduct R A R'))
                    Ff alphaf baseChangeA comparisonA
                    (algebraMap R (TensorProduct R A R'))
                    algebraMap_tensorProduct_comp_left).app K ≫
                CategoryTheory.inv
                  ((StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq.{uR, uRp,
                    max uA uRp, max v uA, max v uR uA uRp + 1, max v uR uA uRp + 1,
                    max v uR uA uRp + 1}
                    (algebraMap R R')
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom
                    baseChangeR comparisonR Fi alphai
                    (algebraMap R (TensorProduct R A R'))
                    algebraMap_tensorProduct_comp_right).app K)) ≫
            ((Fi ⋙ (ModuleCat.restrictScalars.{max v uR uA uRp}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory).map
                (comparisonR.app K) ≫
              (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
                    (Algebra.TensorProduct.includeRight :
                      R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai).hom.app
                  (DerivedCategory.Q.obj
                    (((ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
                      (algebraMap R R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≫
                (derivedExtendRestrictScalarsTensorFunctor.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom).map
                  (CategoryTheory.inv (comparisonR.app K))) := by
  have hu := restrictionBaseChangeIsoGeneral_inv_app_of_iso hTor baseChangeR comparisonR
    baseChangeA comparisonA (Ff.obj (DerivedCategory.Q.obj K)) _ (asIso (alphaf.app K))
  have hc := derivedBaseChangeSquareIso_hom_app_q_obj baseChangeR comparisonR baseChangeA
    comparisonA Ff alphaf Fi alphai K
  have hp := derivedExtendRestrictScalarsTensorIso_hom_app_baseChangeR_q_obj baseChangeR
    comparisonR Fi alphai K
  exact Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso_eq_of_values _ _ _ _ _ hu hc hp

include hf hA hR hi in
/-- **Granted the [stacks 068I] identification, the obligation is the comparison identity.**  If
the [stacks 068I] morphism `Dualizing.tensorBaseChangeMor` at `(X, A[0])` is the lax monoidal
structure map of derived base change along `R → R'`, then
`Dualizing.TensorComparisonCompatibility` at `X` holds exactly when that morphism, followed by the
comparison `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` of the two derived tensor
products across the square, is the tensoring of the identity with
`Dualizing.derivedBaseChangeAlgebraIso`.

In the right-hand side neither the lax structure map `Dualizing.derivedTensorBaseChange`, nor its
section `Dualizing.derivedTensorBaseChangeSection`, nor any component of [stacks 0E1W], nor the
morphism of [stacks 0E1X], nor a transpose of [stacks 0GMT] or [stacks 0A63] occurs: every factor
is a component of an isomorphism built from the monoidality of [stacks 068I], the two projection
formulas, `Dualizing.derivedBaseChangeSquareIso` and the comparison of [stacks 0661], each of
which has a chain-level value at a K-flat complex. -/
theorem tensorComparisonCompatibility_iff_tensorBaseChangeMor
    (D : TotalDerivedExtensionScalars.{uR, max v uR uA uRp, uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1} (algebraMap R R'))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hmu : tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X
          (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) =
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR X
          (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
        Ff alphaf Fi alphai X ↔
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
            (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
            (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
              Fi alphai)
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA) X =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
            max v uR uA uRp + 1} R').tensor.map
          ((𝟙 (baseChangeR.obj X),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).hom) :
            (baseChangeR.obj X,
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj X,
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)) := by
  constructor
  · intro h
    replace h : _ = _ := h
    exact Eq.trans (congrArg (fun z => z ≫ _) hmu) h
  · intro h
    show _ = _
    exact Eq.trans (congrArg (fun z => z ≫ _) hmu.symm) h

include hf hA hR hi in
/-- **Granted the comparison identity, the obligation is the [stacks 068I] identification.**  The
comparison `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` of the two derived tensor
products across the square is invertible, by
`Stacks.CategoryTheory.BaseChange.isIso_tensorComparisonOfIso`, hence monic; so two morphisms with
the same composite with it agree.  If the [stacks 068I] morphism composed with it is the tensoring
of the identity with `Dualizing.derivedBaseChangeAlgebraIso`, then
`Dualizing.TensorComparisonCompatibility` at `X` says precisely that the lax monoidal structure
map of derived base change along `R → R'` has the same composite, which is to say that the two
agree.

Taken with `Dualizing.tensorComparisonCompatibility_iff_tensorBaseChangeMor` this says the two
halves of the split are jointly equivalent to the obligation, and that neither is redundant: the
comparison identity alone determines the obligation only up to the identification, and the
identification alone only up to the comparison identity. -/
theorem tensorBaseChangeMor_eq_iff_tensorComparisonCompatibility
    (D : TotalDerivedExtensionScalars.{uR, max v uR uA uRp, uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1} (algebraMap R R'))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (h : tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
            (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
            (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
              Fi alphai)
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA) X =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
            max v uR uA uRp + 1} R').tensor.map
          ((𝟙 (baseChangeR.obj X),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).hom) :
            (baseChangeR.obj X,
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj X,
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom))) :
    tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D X
          (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) =
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR X
          (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ↔
      TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
        Ff alphaf Fi alphai X := by
  constructor
  · intro hmu
    exact (tensorComparisonCompatibility_iff_tensorBaseChangeMor hTor baseChangeR comparisonR
      baseChangeA comparisonA Ff alphaf Fi alphai D X hmu).mpr h
  · intro hc
    replace hc : _ = _ := hc
    exact Stacks.CategoryTheory.BaseChange.eq_of_comp_tensorComparisonOfIso_eq
      (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
      (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
      (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
        Fi alphai)
      (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
        comparisonA hA) X (h.trans hc.symm)

include hf hA hR hi in
/-- **The split: the obligation at every object, from the [stacks 068I] identification at K-flat
pairs and the comparison identity at K-flat classes.**  Both sides of
`Dualizing.TensorComparisonCompatibility` are natural in the object it is read at, so
`Dualizing.tensorComparisonCompatibility_of_kFlat` restricts it to the classes of K-flat
complexes; there
`Dualizing.tensorComparisonCompatibility_iff_tensorBaseChangeMor` turns it into the comparison
identity, the identification it needs being supplied by
`Dualizing.tensorBaseChangeMor_eq_of_kFlat` from its values at pairs of K-flat complexes.

So the chapter's keystone is these two hypotheses.  The first is the keystone in the shape of
`Dualizing.tensorBaseChangeMor_eq_iff_section_comp` — one equation `ν ≫ μ' = 𝟙` whose component of
[stacks 0E1W] is read at the contravariant object `Q L` for a K-flat `L`, which is the slot
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_tensorKFlat` evaluates it
at.  The second mentions no component of [stacks 0E1W] at all. -/
theorem tensorComparisonCompatibility_of_tensorBaseChangeMor
    (D : TotalDerivedExtensionScalars.{uR, max v uR uA uRp, uRp,
      max v uR uA uRp + 1, max v uR uA uRp + 1} (algebraMap R R'))
    (hmu : ∀ K L : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K → CochainComplex.KFlat.{uR, max v uA uRp} L →
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) =
        derivedTensorBaseChange.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR
          (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L))
    (h : ∀ K : CochainComplex (ModuleCat.{max v uR uA uRp} R) ℤ,
      CochainComplex.KFlat.{uR, max v uA uRp} K →
      tensorBaseChangeMor.{uR, uRp, max v uA} (algebraMap R R') baseChangeR comparisonR D
            (DerivedCategory.Q.obj K)
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) ≫
          Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
            (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
            (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
              Fi alphai)
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA) (DerivedCategory.Q.obj K) =
        (derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
            max v uR uA uRp + 1} R').tensor.map
          ((𝟙 (baseChangeR.obj (DerivedCategory.Q.obj K)),
              (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                comparisonA hA).hom) :
            (baseChangeR.obj (DerivedCategory.Q.obj K),
                baseChangeR.obj
                  (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A))) ⟶
              (baseChangeR.obj (DerivedCategory.Q.obj K),
                derivedAlgebraSingle.{uRp, max uA uRp, max v uR}
                  (Algebra.TensorProduct.includeRight :
                    R' →ₐ[R] TensorProduct R A R').toRingHom)))
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X :=
  tensorComparisonCompatibility_of_kFlat hTor baseChangeR comparisonR baseChangeA comparisonA
    Ff alphaf Fi alphai
    (fun K hK => (tensorComparisonCompatibility_iff_tensorBaseChangeMor hTor baseChangeR
      comparisonR baseChangeA comparisonA Ff alphaf Fi alphai D (DerivedCategory.Q.obj K)
      (tensorBaseChangeMor_eq_of_kFlat.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
        comparisonR D hmu (DerivedCategory.Q.obj K)
        (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)))).mpr (h K hK)) X

end Dualizing

end
