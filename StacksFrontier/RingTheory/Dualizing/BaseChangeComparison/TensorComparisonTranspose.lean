module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeTranspose
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonFactors

/-!
# The tensor-comparison obligation with the lax structure map transposed away

`Dualizing.TensorComparisonCompatibility` is the equation

`μ_{X, A} ≫ tensorComparisonOfIso X = 𝟙_{X ⊗ᴸ_R R'} ⊗ derivedBaseChangeAlgebraIso`,

and it is the only remaining input of `Dualizing.KFlatAlgebraActionEq`.  Its left-hand side is the
lax monoidal structure map `μ` of derived base change along `R → R'`, which is a double adjoint
transpose of the derived-Hom base-change morphism of [stacks 0E1X]; expanding `μ` therefore
replaces one factor of the obligation by the whole of [stacks 0E1X].

That expansion is avoidable.  `Dualizing.derivedTensorBaseChange_comp_eq_iff` transposes any
equation of the shape `μ ≫ c = t` into one in which neither `μ` nor [stacks 0E1X] occurs, at the
cost of a single occurrence of the change-of-rings isomorphism of [stacks 0E1W] — and the
obligation is exactly of that shape, with `c` the comparison
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` of the two derived tensor products across
the base-change square and `t` the tensoring of the identity with
`Dualizing.derivedBaseChangeAlgebraIso`.  This file performs the instantiation.

In the transposed form the obligation is an equation in `D(R)` between two morphisms

`X ⊗ᴸ_R A ⟶ ((X ⊗ᴸ_R R') ⊗ᴸ_{R'} (A ⊗_R R'))|_R`,

whose factors are the comparison of the two tensor products across the square, the unit of
[stacks 0GMT] along `R → R'`, the coevaluation and evaluation of [stacks 0A63] over `R` and over
`R'`, the base change `Dualizing.derivedBaseChangeAlgebraIso` of the algebra, and the inverse of
the isomorphism of [stacks 0E1W].

**What is not done here.**  `Dualizing.TensorComparisonCompatibility` is not proved, and no tag
loses its conditional caveat.  What the transposed equation still needs is an identification of
the isomorphism of [stacks 0E1W] along `R → R'`, at the pair
`(A, (X ⊗ᴸ_R R') ⊗ᴸ_{R'} (A ⊗_R R'))`, with the four-factor comparison across the square — the two
projection formulas, `Dualizing.derivedBaseChangeSquareIso` and the comparison of [stacks 0661].
Each of those four has a chain-level value at a K-flat complex
(`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonFactors`), and so does
[stacks 0E1W], through
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` and
`Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso`.

The comparison of the Hom-complex change-of-rings map with the tensor side *at that level* is
available — `Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry_monoidalIso` —
and its two transposes are now localized, in
`StacksFrontier.Homology.HomComplex.RHom.ChangeOfRingsTransposeLocalization`: the
extension--restriction transpose of [stacks 0GMT] by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_homEquiv_Q_map`, which
needs no K-flatness at all, and the tensor--Hom transpose of [stacks 0A63] by
`StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv_map_uncurry`, whose hypotheses are a
K-flat Hom-source and a K-injective target — exactly the K-flat/K-injective join of
`Stacks.DerivedHom.BaseChange.exists_kFlatKInjectiveJoin`, the extension of scalars of a K-flat
complex being K-flat.  The result is
`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_derived_of_hom`: the comparison as an
equation of the derived category, at an arbitrary morphism, in which the only chain maps left are
`q` and the two localizations
`DerivedCategory.Q.map (CochainComplex.ExtendScalars.extendScalarsMonoidalIso f P K).inv` and
`DerivedCategory.Q.map (Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q)`; and
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_homComplex` names the
second of those as `Stacks.DerivedHom.BaseChange.derivedHomChangeOfRingsModelIso`, the factor
through which
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` reads the
component of [stacks 0E1W].

**What still separates that from the hypothesis of
`Dualizing.tensorComparisonCompatibility_of_homEquiv`**, in the order it has to be done:

* the conjugation of
  `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` has to
  be carried out: that formula presents the component of [stacks 0E1W] as
  `derivedHomChangeOfRingsModelIso` surrounded by the units and counits of the two scalar
  equivalences, the scalar-restriction comparison `δ`, and three transports along
  `Stacks.DerivedHom.BaseChange.isoQObjPreimage`.  Everything in that list is a named public
  morphism.  The `derivedHomChangeOfRingsModelIso` factor itself is no longer part of the
  question: `Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_hom_eq_monoidalIso`
  values it with the degreewise monoidality isomorphism as its only chain map, and
  `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models_monoidalIso` carries
  that substitution into the morphism of [stacks 0E1X].  What has not been composed with the
  equation above is the conjugation proper --- the units, counits, `δ` and the three transports.
* the transposes above are stated for `StacksDraft.DerivedHom.DerivedInternalHom.Model.homEquiv`
  over `ULift R`, while this file's hypothesis uses
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing`, which is the former transported along
  `StacksDraft.DerivedHom.derivedScalarEquivalence`.  The bridge is
  `StacksDraft.DerivedHom.DerivedHomAdjunction.transportHomEquiv_apply_functor_obj`, with
  `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing_homEquiv_apply` as the worked instance.
* the left-hand side is still open: the four factors of
  `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` each have a value at a K-flat complex
  (`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonFactors`), but their
  composite has not been identified with the derived monoidality isomorphism
  `CochainComplex.ExtendScalars.derivedMonoidalIso`, which is what the localized comparison above
  has on its tensor side.  Two of the four are now gone from the question:
  `StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonMate` transposes the
  comparison of [stacks 0661] away, so what has to be identified is
  `Dualizing.tensorComparisonOfIso_eq_homEquiv_square`'s right-hand side — the inverse projection
  formula over `R`, a double transpose of the square isomorphism
  `Dualizing.derivedBaseChangeSquareIso` conjugating the counit of [stacks 0GMT] along `R → A`, and
  the projection formula over `R'`.  `Dualizing.restrictionBaseChangeIsoGeneral` and its component
  formula `Dualizing.restrictionBaseChangeIsoGeneral_inv_app_of_iso` are no longer needed for it.

Two of those three items are settled, in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonAssembly`, and the first
is not what it looks like.

* The **left-hand side** is closed at a K-flat representative, and without any identification with
  `CochainComplex.ExtendScalars.derivedMonoidalIso`:
  `Dualizing.tensorComparisonCompatibility_lhs_app_q_obj` evaluates it at `X = Q K`, and neither
  the square isomorphism `Dualizing.derivedBaseChangeSquareIso` nor the counit of [stacks 0GMT]
  along `R → A` survives.  What is left of it is the two projection formulas, the two transposes
  of [stacks 0GMT], chain-level data, and one inverse of the composite comparison along
  `R → R' → A ⊗_R R'` at `K`, which K-flatness of `K` supplies.  The step that makes this possible
  is `Dualizing.squareIso_counit_conjugate_comp_comparison_app_q_obj`, which reads the square
  isomorphism's characterizing equation at `(A ⊗_R K)|_R` in the direction that needs no inverse —
  that complex is *not* K-flat over `R` unless `A` is flat over `R`.
* The **right-hand side** does not need the conjugation of
  `Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` at all,
  and the [stacks 0E1W] isomorphism can be removed from it outright:
  `Dualizing.tensorComparisonCompatibility_rhs_eq_section` shows it is the transpose over
  [stacks 0GMT] of `ν_{X, A[0]} ≫ (𝟙 ⊗ derivedBaseChangeAlgebraIso)`, for `ν` the two-sided
  inverse `Dualizing.derivedTensorBaseChangeSection` of the lax monoidal structure map `μ`.  No
  K-flat representative is involved and nothing is assumed of `X`.

So the residue of `Dualizing.TensorComparisonCompatibility` is a determinate value for `ν` —
equivalently for `μ`, equivalently for the component of [stacks 0E1W], the three being
interdefinable: `Dualizing.derivedTensorBaseChangeSection` is a transpose of a component of
[stacks 0E1W] by definition, and `Dualizing.homEquiv_derivedTensorBaseChangeSection` reads the
component back off it.  The second item above is that interdefinability in the one direction the
obligation needs, so the conjugation of
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q` is not a
*separate* obligation from the identification of `μ` — it is the same one.

That paragraph is now a theorem rather than a remark, and it needs neither of the two transposes
this file introduces.  `Dualizing.tensorComparisonCompatibility_iff_section` of
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorComparisonSection` divides the
obligation by `μ`, which `Dualizing.isIso_derivedTensorBaseChange` proves invertible
unconditionally, and `Dualizing.tensorComparisonCompatibility_iff_eq_inv` divides it by the
comparison across the square, which
`Stacks.CategoryTheory.BaseChange.isIso_tensorComparisonOfIso` proves invertible because each of
its four factors is.  So the obligation at `X` *is* the equation
`tensorComparisonOfIso X = ν_{X, A[0]} ≫ (𝟙 ⊗ derivedBaseChangeAlgebraIso)`, in which no
transpose, no unit of [stacks 0GMT], no `homEquiv` of [stacks 0A63], no component of
[stacks 0E1W] and no morphism of [stacks 0E1X] occurs, and equivalently it is a determinate value
for `μ`.

The coherence of `μ` that the *other* open obligation of this chapter needs --- the second input
of [stacks 0E2H] --- is not this identification but the pentagon of `μ`, and that pentagon now has
a name and a second address:
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.CurryingCoherence` proves it equivalent to
the compatibility of the morphism of [stacks 0E1X], hence of [stacks 0E1W], with the currying
isomorphism of [stacks 0A65].  Both obligations are therefore waiting on the same missing datum, a
determinate chain-level value for `μ`, and neither is waiting on anything else.

That identification has its smallest shape in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorBaseChangeIdentification`:
`Dualizing.tensorBaseChangeMor_eq_iff_section_comp` asks only for `ν ≫ μ' = 𝟙` with `μ'` the
[stacks 068I] morphism `Dualizing.tensorBaseChangeMor`, which is manifestly invertible and
manifestly chain-level, and `Dualizing.tensorBaseChangeMor_eq_of_kFlat` reduces that to pairs of
K-flat complexes.  It is not an independent route — `ν` occurs in it, and `ν` is where
[stacks 0E1W] is — but it is the shape in which the one remaining unknown appears exactly once.

That one occurrence may be read in either direction, and
`Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` reads it in the direction that inverts nothing:
the component of [stacks 0E1W] is moved across the equation, leaving its inverse on the left and
the bare transpose of the unit of [stacks 0GMT] at `X ⊗ᴸ_R Y` on the right.  That is the direction
in which the representative model comparison is valued without an inverted transpose,
`Stacks.DerivedHom.BaseChangeIso.derivedHomChangeOfRingsModelIso_inv_eq_monoidalIso`; the hom
value has one, and the value of `μ'` it would have to be compared with,
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj`, inverts nothing.  What separates the two is the
inverse of the conjugation
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_hom_app_kFlatKInjective_Q`, whose
four factors are all components of isomorphisms.  Its third factor is the comparison
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso` of the two composite left adjoints,
which that formula displays through
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_inv_app` and which is equally
available in the forward direction, by
`Stacks.DerivedHom.BaseChange.derivedExtensionScalarsLiftIso_hom_app`.  So no factor of the
conjugation lacks a value in either direction.

The inverse of the composite is now stated too, which is what that paragraph was waiting for.
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app` is the inverse of the
four-factor display, and
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective` is the
inverse component formula at a K-flat/K-injective pair, with the representative model comparison
entering through its `inv` and the comparison of the two derived extensions of scalars through its
`hom` — each the direction that inverts nothing.
`Stacks.DerivedHom.BaseChange.scalarRestrictionTransportedIso_inv_app` and
`Stacks.DerivedHom.BaseChange.scalarRestrictionIso_inv_app_of_iso` carry the remaining
scalar-restriction factors of it to classes of cochain complexes.  So both sides of
`Dualizing.tensorBaseChangeMor_eq_iff_natIso_inv` at a pair of K-flat complexes are now composites
of named morphisms with nothing inverted on either side, and what remains is to compare them
factor by factor.

## Main results

* `Dualizing.tensorComparisonCompatibility_of_homEquiv` — **the reduction**: the obligation at an
  object `X` of `D(R)` follows from its transpose over [stacks 0GMT], in which the lax monoidal
  structure map and the morphism of [stacks 0E1X] do not occur.

## Implementation notes

The morphism fed to the tensor bifunctor of [stacks 0A63] is written with
`CategoryTheory.Prod.mkHom` rather than as a raw pair: a raw pair forces the elaborator to compare
`Dualizing.derivedAlgebraSingle` against the unfolded single complex in which
`Dualizing.derivedBaseChangeAlgebraIso` is stated, which it declines to do while elaborating a
composite.  `Prod.mkHom` reads both objects off its two arguments instead.

The instantiation itself is a term, not a rewrite: the source of
`Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` at this square is spelled with
`Dualizing.derivedExtendRestrictScalarsTensorFunctor` while
`Dualizing.derivedTensorBaseChange` spells it with the tensor bifunctor of [stacks 0A63], and the
two agree only definitionally — `Dualizing.derivedExtendRestrictScalarsTensorFunctor_map` is the
`rfl` in question, and keyed matching does not see through it.

No `@[stacks]` attribute is placed here: the obligation is still open, so nothing in this file
covers a tag.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open CochainComplex.DerivedExtensionScalars

namespace Dualizing

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
/-- **The tensor-comparison obligation follows from its transpose over [stacks 0GMT].**  The
transpose of `Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso` at `X` agreeing with the
transpose of `𝟙 ⊗ derivedBaseChangeAlgebraIso`, read backwards through the change-of-rings
isomorphism of [stacks 0E1W] along `R → R'`, implies
`Dualizing.TensorComparisonCompatibility` at `X`.

This is `Dualizing.derivedTensorBaseChange_comp_eq_iff` at the base-change square.  Neither the
lax monoidal structure map `μ` of derived base change nor the derived-Hom base-change morphism of
[stacks 0E1X] occurs in the hypothesis: the obligation has become a question about [stacks 0E1W]
at the single pair `(A, (X ⊗ᴸ_R R') ⊗ᴸ_{R'} (A ⊗_R R'))`. -/
theorem tensorComparisonCompatibility_of_homEquiv
    (X : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (h : (derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
            comparisonR).homEquiv _ _
          (Stacks.CategoryTheory.BaseChange.tensorComparisonOfIso
            (derivedExtendRestrictScalarsTensorIso.{uR, uA, max v uRp} (algebraMap R A) Ff alphaf)
            (derivedExtendRestrictScalarsTensorIso.{uRp, max uA uRp, max v uR}
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom Fi alphai)
            (derivedBaseChangeSquareIso Ff alphaf baseChangeA comparisonA baseChangeR comparisonR
              Fi alphai)
            (restrictionBaseChangeIsoGeneral hTor baseChangeR comparisonR hR baseChangeA
              comparisonA hA) X) =
        (derivedHomAdjunctionOverRing.{uR, max v uR uA uRp, max v uR uA uRp + 1} R).homEquiv X
            (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) _
          ((derivedExtensionScalarsAdjunction.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
                comparisonR).homEquiv X _
              (((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                    max v uR uA uRp + 1} R').homEquiv _ _ _).symm
                ((derivedHomAdjunctionOverRing.{uRp, max v uR uA uRp,
                    max v uR uA uRp + 1} R').tensor.map
                  (Prod.mkHom (𝟙 (baseChangeR.obj X))
                    (derivedBaseChangeAlgebraIso hTor baseChangeR comparisonR hR baseChangeA
                      comparisonA hA).hom))) ≫
            (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uRp, max v uA}
              (algebraMap R R') baseChangeR comparisonR).inv.app
                (Opposite.op (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)), _))) :
    TensorComparisonCompatibility hTor baseChangeR comparisonR baseChangeA comparisonA
      Ff alphaf Fi alphai X :=
  (derivedTensorBaseChange_comp_eq_iff.{uR, uRp, max v uA} (algebraMap R R') baseChangeR
    comparisonR X (derivedAlgebraSingle.{uR, uA, max v uRp} (algebraMap R A)) _ _ _).mpr h

end Dualizing

end
