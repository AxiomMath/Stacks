module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaMateModel
public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionTensorPrefix

/-!
# The right-hand side of the mate identity of [stacks 0E2H], valued

`Dualizing.ProjectionFormula.projEval_app_eq_iff_mate` states the owed coherence of
[stacks 0E2H] as a mate identity whose right-hand side is the [stacks 0A63] transpose over `A` of
derived restriction of a presentation followed by
`Dualizing.ProjectionFormula.homRestrictComponent`, the component of the change-of-rings
isomorphism of [stacks 0E1W].  This file values that transpose.

`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app` and its three
refinements already value the [stacks 0A63] transpose of the inverse component of [stacks 0E1W].
They are stated with the transported internal-Hom bifunctor
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom`, whereas
`Dualizing.ProjectionFormula.homRestrictComponent` is stated with the internal Hom of the
tensor--Hom bundle `StacksDraft.DerivedHom.derivedHomAdjunctionOverRing` of [stacks 0A63]; the two
bifunctors are equal on the nose by `Dualizing.derivedHomAdjunctionOverRing_hom_eq`, so the
transfer costs nothing but the universe bookkeeping -- the consumer's `.{u, v}` against the
framework's `.{uR, uA, uM}` at `uR = uA = u`, `uM = v`.

That bookkeeping is what this file carries out, and after it the whole existing family applies at
the consumer's pair: the prefix is split off by naturality of the transpose in its first variable,
and what is left is valued with no scalar-equivalence data at all.

## Main results

* `Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_eq_natIso` -- **the bridge**: the
  [stacks 0A63] transpose over `A` of `Dualizing.ProjectionFormula.homRestrictComponent` is the
  transpose of the inverse component of [stacks 0E1W] in the vocabulary the framework states it
  with.  It holds by `rfl`, which is the content: no comparison map is needed.
* `Dualizing.ProjectionFormula.homEquiv_restrict_comp_homRestrictComponent` -- **the split**: the
  transpose of a prefix followed by the component is the fixed tensor of the prefix followed by
  the transpose of the component alone, so the prefix of the mate identity's right-hand side is
  carried outside the transpose.
* `Dualizing.ProjectionFormula.homEquiv_restrict_comp_homRestrictComponent_eq` -- the split
  against any value of the transpose of the component, so that each value below applies to the
  mate identity's right-hand side with the prefix in place.
* `Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_scalarEquivalence` -- the transpose
  of the component, valued **unconditionally**, in the vocabulary of [stacks 0E1W]: one counit of
  its scalar equivalence, the scalar equivalence of the scalar-restriction comparison `δ`, one
  fixed-universe transpose, and one inverse unit.
* `Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_of_counit_values` -- the transpose of
  the component, valued, with the two counits of
  `StacksDraft.DerivedHom.derivedScalarEquivalence` passed in as hypotheses.
* `Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_of_presentations` -- **the transpose
  of the component with no equivalence data left**: given a presentation of each of those two
  counits' arguments as isomorphic to a localized complex, every factor is a component of
  `CategoryTheory.Functor.mapDerivedCategoryFactors`, a localization of the unit or the counit of
  the `ULift` equivalence of complexes, one of the two presentations, or one of `eF`,
  `modelRestrictScalarsNatIso`, `δ` and `τ`.

## Implementation notes

Each value is proved by `exact` against the corresponding member of the family in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTranspose`.  `exact` and
not `rw`: the two statements' instance arguments for the scalar-change adjunctions are elaborated
in different files -- there from the `letI` bindings the framework carries, here from the ambient
instances of the consumer -- and agree only at default transparency, which is below what keyed
matching uses.

No `@[stacks]` attribute is placed here: this is one evaluation of existing constructions and
covers no tag.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom
open Stacks.DerivedHom.BaseChange

namespace Dualizing.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

universe u v

variable {A B : Type u} [CommRing A] [CommRing B]

/-- **The bridge.**  The [stacks 0A63] transpose over `A` of
`Dualizing.ProjectionFormula.homRestrictComponent` -- the component of the change-of-rings
isomorphism of [stacks 0E1W] read with the internal Hom of the tensor--Hom bundle of
[stacks 0A63] -- is the transpose of the inverse component of the change-of-rings isomorphism
read with the transported internal-Hom bifunctor
`Stacks.DerivedHom.ScalarTransportedInternalHom.hom` that [stacks 0E1W] is stated with.

The two bifunctors are equal on the nose by `Dualizing.derivedHomAdjunctionOverRing_hom_eq`, and
the consumer's universes `.{u, v}` instantiate the framework's `.{uR, uA, uM}` at `uR = uA = u`
and `uM = v`, so there is nothing to prove.  Stating it is what makes the whole family of values
in `StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.HomRestrictScalarsTranspose` applicable
at the consumer's pair. -/
theorem homEquiv_homRestrictComponent_eq_natIso (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
            (Opposite.op (E.functor.obj N), W)))
        N ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
        (homRestrictComponent.{u, v} φ E N W) =
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u,
              max u v} B).inverse.obj
            ((DerivedInternalHom.Model.hom (ULift.{max u v} B)).obj
              (Opposite.op ((Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u,
                  max u v} B).functor.obj (E.functor.obj N)),
                (Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u,
                  max u v} B).functor.obj W))))
        N ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
        ((derivedHomRestrictScalarsNatIso.{u, u, v} φ E.functor
          (modelComparison.{u, v} φ E)).inv.app (Opposite.op N, W)) :=
  rfl

/-- **The split.**  For any morphism `s` into the internal Hom over `B` of `Ext N` and `W`, the
[stacks 0A63] transpose over `A` of derived restriction of `s` followed by
`Dualizing.ProjectionFormula.homRestrictComponent` is the derived tensor product over `A` of that
restriction with the identity of `N`, followed by the transpose of the component alone.

This is naturality of the transpose of [stacks 0A63] in its first variable, at the shape the
right-hand side of `Dualizing.ProjectionFormula.projEval_app_eq_iff_mate` has: it carries the
presentation of the internal Hom out of the transpose, leaving the transpose of the component of
[stacks 0E1W] by itself, which is what the value below is about. -/
theorem homEquiv_restrict_comp_homRestrictComponent (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W Z : DerivedCategory (ModuleCat.{max u v} B))
    (s : Z ⟶ (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
      (Opposite.op (E.functor.obj N), W)) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj Z) N
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map s ≫
          homRestrictComponent.{u, v} φ E N W) =
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj Z, N))
          (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
              (Opposite.op (E.functor.obj N), W)), N))
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map s, 𝟙 N) ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
              (Opposite.op (E.functor.obj N), W)))
          N ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
          (homRestrictComponent.{u, v} φ E N W) :=
  (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv_naturality_left
    ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map s)
    (homRestrictComponent.{u, v} φ E N W)

/-- **The split against any value of the transpose of the component.**  Combining
`Dualizing.ProjectionFormula.homEquiv_restrict_comp_homRestrictComponent` with a value of the
transpose of `Dualizing.ProjectionFormula.homRestrictComponent` alone: the right-hand side of the
mate identity of [stacks 0E2H] is the derived tensor product over `A` of the restricted
presentation with the identity of `N`, followed by that value.

The value is taken as a hypothesis, so this applies to any member of the family below -- and to
any further value a consumer proves. -/
theorem homEquiv_restrict_comp_homRestrictComponent_eq (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W Z : DerivedCategory (ModuleCat.{max u v} B))
    (s : Z ⟶ (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
      (Opposite.op (E.functor.obj N), W))
    (val : (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
            (Opposite.op (E.functor.obj N), W)), N) ⟶
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
    (h : (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
            (Opposite.op (E.functor.obj N), W)))
        N ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
        (homRestrictComponent.{u, v} φ E N W) = val) :
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj Z) N
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj W)
        ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map s ≫
          homRestrictComponent.{u, v} φ E N W) =
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj Z, N))
          (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
              (Opposite.op (E.functor.obj N), W)), N))
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map s, 𝟙 N) ≫ val := by
  rw [homEquiv_restrict_comp_homRestrictComponent.{u, v} φ E N W Z s, h]

/-- **The transpose of the component of [stacks 0E1W], valued unconditionally.**

`Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_eq_natIso` carried into
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence`:
the [stacks 0A63] transpose over `A` of `Dualizing.ProjectionFormula.homRestrictComponent` with
the two counits read as the counit and the inverse unit of the scalar equivalence of
[stacks 0E1W], so that the whole value is in one vocabulary and no hypothesis is needed.

Seventeen of the eighteen factors that
`Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso_inv_app_kFlatKInjective_Q` spends on
the curried component are gone: transposing cancels the conjugation by the scalar equivalence
outright, and what is left is one counit, the scalar equivalence of the scalar-restriction
comparison `δ`, one fixed-universe transpose, and one inverse unit. -/
theorem homEquiv_homRestrictComponent_scalarEquivalence (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    let Esc := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} A
    let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} B
    let φ' : ULift.{max u v} A →+* ULift.{max u v} B :=
      (ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max u v, max u v, max u v} φ').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max u v} φ').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max u v} φ').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max u v} φ').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max u v} φ').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings φ'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ φ' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ Esc.inverse := scalarRestrictionIso.{u, u, v} φ
    let τ : U ⋙ Esc.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := Esc.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : Esc.functor ⋙ T.B ≅ E.functor ⋙ S.functor :=
      (Esc.toAdjunction.comp a').leftAdjointUniq
        (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v} φ
          E.functor (modelComparison.{u, v} φ E)).comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max u v} A)
    let HB := DerivedInternalHom.Model.hom (ULift.{max u v} B)
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        (U.obj ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
          (Opposite.op (E.functor.obj N), W)))
        N (U.obj W) (homRestrictComponent.{u, v} φ E N W) =
      Esc.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max u v} A)).map
              ((Esc.functor.map (δ.hom.app (HB.obj
                      (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W))) ≫
                  Esc.counitIso.hom.app
                    (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)),
                      S.functor.obj W))),
                𝟙 (Esc.functor.obj N)) :
                  ((Esc.functor.obj (U.obj (S.inverse.obj (HB.obj
                        (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)))),
                      Esc.functor.obj N) :
                    DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A)) ×
                      DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A))) ⟶
                    (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)),
                        S.functor.obj W)),
                      Esc.functor.obj N)) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)))
              (Esc.functor.obj N) (Esc.functor.obj (U.obj W))
              (V.map (HB.map (CategoryTheory.Prod.mkHom (eF.hom.app N).op
                  (𝟙 (S.functor.obj W)))) ≫
                (modelRestrictScalarsNatIso φ' T.B T.alphaB).inv.app
                    (Opposite.op (Esc.functor.obj N), S.functor.obj W) ≫
                  HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (Esc.functor.obj N)))
                    (τ.inv.app W)))) ≫
        Esc.unitIso.inv.app (U.obj W) := by
  intro Esc S φ' U V T a' δ τ eF HR HB
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app_scalarEquivalence.{u, u, v} φ E.functor
    (modelComparison.{u, v} φ E) (Opposite.op N) W

/-- **The transpose of the component of [stacks 0E1W], valued, with its two counits passed in.**

`Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_eq_natIso` carried into
`Stacks.DerivedHom.BaseChange.homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_counit_values`:
the [stacks 0A63] transpose over `A` of the component is the scalar equivalence of the
scalar-restriction comparison `δ` followed by the first counit, tensored with the identity of the
scalar lift of `N`, then one fixed-universe transpose of the comparison `eF` of the two derived
extensions of scalars followed by the inverse representative model comparison and the transported
restriction comparison `τ`, and finally the second counit.

Neither counit sits at a class, so both are taken as hypotheses: the equation holds with whatever
the consumer can prove them to be. -/
theorem homEquiv_homRestrictComponent_of_counit_values (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    let Esc := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} A
    let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} B
    let φ' : ULift.{max u v} A →+* ULift.{max u v} B :=
      (ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max u v, max u v, max u v} φ').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max u v} φ').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max u v} φ').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max u v} φ').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max u v} φ').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings φ'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ φ' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ Esc.inverse := scalarRestrictionIso.{u, u, v} φ
    let τ : U ⋙ Esc.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := Esc.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : Esc.functor ⋙ T.B ≅ E.functor ⋙ S.functor :=
      (Esc.toAdjunction.comp a').leftAdjointUniq
        (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v} φ
          E.functor (modelComparison.{u, v} φ E)).comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max u v} A)
    let HB := DerivedInternalHom.Model.hom (ULift.{max u v} B)
    ∀ (c₁ : Esc.functor.obj (Esc.inverse.obj (V.obj (HB.obj
            (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)))) ⟶
          V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)))
    (c₂ : Esc.inverse.obj (Esc.functor.obj (U.obj W)) ⟶ U.obj W)
    (hc₁ : (derivedScalarEquivalence.{u, max u v,
          max u v + 1} A).symm.toAdjunction.counit.app
        (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W))) = c₁)
    (hc₂ : (derivedScalarEquivalence.{u, max u v, max u v + 1} A).toAdjunction.counit.app
        (U.obj W) = c₂),
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        (U.obj ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
          (Opposite.op (E.functor.obj N), W)))
        N (U.obj W) (homRestrictComponent.{u, v} φ E N W) =
      Esc.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max u v} A)).map
              ((Esc.functor.map (δ.hom.app (HB.obj
                      (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W))) ≫
                  c₁,
                𝟙 (Esc.functor.obj N)) :
                  ((Esc.functor.obj (U.obj (S.inverse.obj (HB.obj
                        (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)))),
                      Esc.functor.obj N) :
                    DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A)) ×
                      DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A))) ⟶
                    (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)),
                        S.functor.obj W)),
                      Esc.functor.obj N)) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)))
              (Esc.functor.obj N) (Esc.functor.obj (U.obj W))
              (V.map (HB.map (CategoryTheory.Prod.mkHom (eF.hom.app N).op
                  (𝟙 (S.functor.obj W)))) ≫
                (modelRestrictScalarsNatIso φ' T.B T.alphaB).inv.app
                    (Opposite.op (Esc.functor.obj N), S.functor.obj W) ≫
                  HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (Esc.functor.obj N)))
                    (τ.inv.app W)))) ≫
        c₂ := by
  intro Esc S φ' U V T a' δ τ eF HR HB c₁ c₂ hc₁ hc₂
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_counit_values.{u, u, v} φ E.functor
    (modelComparison.{u, v} φ E) (Opposite.op N) W c₁ c₂ hc₁ hc₂

/-- **The transpose of the component of [stacks 0E1W] with no equivalence data left.**

`Dualizing.ProjectionFormula.homEquiv_homRestrictComponent_of_counit_values` leaves two counits of
`StacksDraft.DerivedHom.derivedScalarEquivalence`, and neither of them sits at a class.  Given a
presentation of each of their arguments as isomorphic to a localized complex -- which always
exists, `DerivedCategory.Q` being essentially surjective -- both are valued, and what is left of
the [stacks 0A63] transpose over `A` of `Dualizing.ProjectionFormula.homRestrictComponent` is a
composite of: the two components of `CategoryTheory.Functor.mapDerivedCategoryFactors` for the two
restriction functors of the `ULift` equivalence, the localization of the unit and of the counit of
that equivalence of complexes, the two presentations, the comparison `eF` of the two derived
extensions of scalars, the representative model comparison `modelRestrictScalarsNatIso`, and the
two components `δ` and `τ` of the scalar-restriction comparison.

This is the value the right-hand side of `Dualizing.ProjectionFormula.projEval_app_eq_iff_mate`
is to be compared against, once
`Dualizing.ProjectionFormula.homEquiv_restrict_comp_homRestrictComponent` has carried the
presentation of the internal Hom out of the transpose. -/
theorem homEquiv_homRestrictComponent_of_presentations (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (N : DerivedCategory (ModuleCat.{max u v} A))
    (W : DerivedCategory (ModuleCat.{max u v} B)) :
    let Esc := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} A
    let S := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, max u v} B
    let φ' : ULift.{max u v} A →+* ULift.{max u v} B :=
      (ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom
    letI : (ModuleCat.extendScalars.{max u v, max u v, max u v} φ').IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max u v} φ').IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v} φ').isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max u v} φ').IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max u v} φ').isLeftAdjoint
    let U := (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory
    let V := (ModuleCat.restrictScalars.{max u v} φ').mapDerivedCategory
    let T := CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings φ'
      (HomologicalComplex.zero : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} B)) ℤ)
    let a' := @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction
      _ _ _ _ φ' _ _ T.B T.alphaB T.isLeftDerivedB
    let δ : S.inverse ⋙ U ≅ V ⋙ Esc.inverse := scalarRestrictionIso.{u, u, v} φ
    let τ : U ⋙ Esc.functor ≅ S.functor ⋙ V :=
      Iso.compInverseIso (H := Esc.symm)
        ((Iso.inverseCompIso (G := S.symm) δ.symm).symm ≪≫
          (Functor.associator _ _ _).symm)
    let eF : Esc.functor ⋙ T.B ≅ E.functor ⋙ S.functor :=
      (Esc.toAdjunction.comp a').leftAdjointUniq
        (((CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v} φ
          E.functor (modelComparison.{u, v} φ E)).comp S.toAdjunction).ofNatIsoRight δ)
    let HR := DerivedInternalHom.Model.hom (ULift.{max u v} A)
    let HB := DerivedInternalHom.Model.hom (ULift.{max u v} B)
    let dse := derivedScalarEquivalence.{u, max u v, max u v + 1} A
    let ulm := uliftModuleEquivalence.{u, max u v, max u v} A
    let ulc := Stacks.DerivedHom.ScalarTransportedInternalHom.uliftComplexEquivalence.{u,
      max u v} A
    ∀ (Zc : CochainComplex (ModuleCat.{max u v} (ULift.{max u v} A)) ℤ)
    (e₁ : V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)) ≅
      DerivedCategory.Q.obj Zc)
    (Wc : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (e₂ : U.obj W ≅ DerivedCategory.Q.obj Wc),
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).homEquiv
        (U.obj ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).hom.obj
          (Opposite.op (E.functor.obj N), W)))
        N (U.obj W) (homRestrictComponent.{u, v} φ E N W) =
      Esc.inverse.map
          ((DerivedInternalHom.Model.tensor (ULift.{max u v} A)).map
              ((Esc.functor.map (δ.hom.app (HB.obj
                      (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W))) ≫
                  (dse.inverse.map (dse.functor.map e₁.hom) ≫
                      (ulm.inverse.mapDerivedCategory.map
                            (ulm.functor.mapDerivedCategoryFactors.hom.app Zc) ≫
                          ulm.inverse.mapDerivedCategoryFactors.hom.app (ulc.functor.obj Zc) ≫
                            DerivedCategory.Q.map (ulc.unitIso.inv.app Zc)) ≫
                    e₁.inv),
                𝟙 (Esc.functor.obj N)) :
                  ((Esc.functor.obj (U.obj (S.inverse.obj (HB.obj
                        (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)))),
                      Esc.functor.obj N) :
                    DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A)) ×
                      DerivedCategory (ModuleCat.{max u v} (ULift.{max u v} A))) ⟶
                    (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)),
                        S.functor.obj W)),
                      Esc.functor.obj N)) ≫
            DerivedInternalHom.Model.homEquiv
              (V.obj (HB.obj (Opposite.op (S.functor.obj (E.functor.obj N)), S.functor.obj W)))
              (Esc.functor.obj N) (Esc.functor.obj (U.obj W))
              (V.map (HB.map (CategoryTheory.Prod.mkHom (eF.hom.app N).op
                  (𝟙 (S.functor.obj W)))) ≫
                (modelRestrictScalarsNatIso φ' T.B T.alphaB).inv.app
                    (Opposite.op (Esc.functor.obj N), S.functor.obj W) ≫
                  HR.map (CategoryTheory.Prod.mkHom (𝟙 (Opposite.op (Esc.functor.obj N)))
                    (τ.inv.app W)))) ≫
        (dse.functor.map (dse.inverse.map e₂.hom) ≫
            (ulm.functor.mapDerivedCategory.map
                  (ulm.inverse.mapDerivedCategoryFactors.hom.app Wc) ≫
                ulm.functor.mapDerivedCategoryFactors.hom.app (ulc.inverse.obj Wc) ≫
                  DerivedCategory.Q.map (ulc.counitIso.hom.app Wc)) ≫
          e₂.inv) := by
  intro Esc S φ' U V T a' δ τ eF HR HB dse ulm ulc Zc e₁ Wc e₂
  exact homEquiv_derivedHomRestrictScalarsNatIso_inv_app_of_presentations.{u, u, v} φ E.functor
    (modelComparison.{u, v} φ E) (Opposite.op N) W Zc e₁ Wc e₂

end Dualizing.ProjectionFormula

end
