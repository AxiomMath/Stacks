module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

@[expose] public noncomputable section

/-!
# Derived extension of scalars along a ring isomorphism

Let `e : R ≃+* S` be an isomorphism of commutative rings. Extension of scalars along `e` is
exact — it is restriction of scalars along `e⁻¹` — so the comparison exhibiting the total
derived functor `- ⊗ᴸ_R S` as the left derived functor of degreewise extension of scalars is
invertible on *every* complex, not only on the K-flat ones. Consequently derived extension of
scalars along `e` and derived restriction of scalars along `e` are mutually inverse equivalences
of the derived categories, in both orders.

Both isomorphisms come from uniqueness of the total left derived functor: on each side the
composite restricts along the localization functor to an isomorphic copy of the localization
functor itself, which makes both it and the identity functor left derived functors of the same
functor on complexes.

## Main definitions

* `CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexRestrictIso` and
  `CochainComplex.DerivedExtensionScalars.restrictExtensionOfScalarsComplexIso`: the two
  complex-level comparisons, saying that degreewise extension and restriction of scalars along
  `e` undo each other after localization.
* `CochainComplex.DerivedExtensionScalars.totalDerivedExtendRestrictScalarsSelfIso`: derived
  extension of scalars along `e` followed by restriction of scalars along `e` is the identity
  functor of `D(R)`.
* `CochainComplex.DerivedExtensionScalars.totalDerivedRestrictExtendScalarsSelfIso`: restriction
  of scalars along `e` followed by derived extension of scalars along `e` is the identity
  functor of `D(S)`.

## Main results

* `CochainComplex.DerivedExtensionScalars.isIso_comparison_of_ringEquiv`: along a ring
  isomorphism, every complex computes derived extension of scalars — extension of scalars along
  an isomorphism is exact, so degreewise extension of scalars inverts quasi-isomorphisms, and
  the comparison of a left derived functor of a functor inverting the weak equivalences is
  invertible. No K-flat resolution argument is involved.
* `CochainComplex.DerivedExtensionScalars.totalDerivedExtendRestrictScalarsSelfIso_comparison`
  and
  `CochainComplex.DerivedExtensionScalars.totalDerivedRestrictExtendScalarsSelfIso_comparison`:
  the two isomorphisms are pinned by the comparison maps they are built from, so that they can
  be used in a coherence argument.

Of the two self-isomorphisms, it is `totalDerivedRestrictExtendScalarsSelfIso` — restriction
first, then extension, the derived form of `ModuleCat.restrictExtendScalarsSelfIso` — that the
affine case of [Stacks, Tag 0DI7] consumes: there derived extension of scalars along
`PseudoCoherence.liftBaseToStageMap F A₀ i`, which re-indexes through `ULift`, is split by
`PseudoCoherence.derivedExtensionScalarsComp` into extension along `ULift.ringEquiv` applied to
the restriction of scalars along `ULift.ringEquiv`, and that is this composite at
`e = ULift.ringEquiv`. The other direction, `totalDerivedExtendRestrictScalarsSelfIso`, is the
derived form of `ModuleCat.extendRestrictScalarsSelfIso` and is included because the same
argument gives it.

## Implementation notes

The two derived categories are instance arguments throughout, as they are in
`StacksFrontier.Homology.Tor.DerivedExtensionScalars` and
`StacksFrontier.Homology.Tor.DerivedExtensionScalarsComp`: `HasDerivedCategory` carries the
localized category as data, so a statement proved at one model says nothing about another, and
consumers work at locally small models. Nothing below pins the standard model of a derived
category, either in a type or inside a body.

The three private declarations below repeat, at module universe `max u v`, module-level
isomorphisms that already exist at module universe equal to the ring universe:
`ModuleCat.extendScalarsIsoRestrictScalarsSymm` and `ModuleCat.restrictExtendScalarsSelfIso`
(`StacksFrontier/Homology/ExtendScalars/AlongARingIsomorphism.lean`, lines 61 and 67) and
`ModuleCat.extendRestrictScalarsSelfIso`
(`StacksFrontier/AlgebraicGeometry/Perfect/RelativeTorAmplitudeRestriction.lean`, line 101). The
complexes here live in a module universe independent of the ring universe, as they must — the
derived functors of the two files above are built there — so those statements do not apply.
Widening their universe parameters in place would change the interface of files this one does
not own; a repository-wide pass should generalize them there and delete these three copies.

## References

* [The Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [The Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

open CategoryTheory

universe u v wR wS

namespace CochainComplex.DerivedExtensionScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extension of scalars along a ring isomorphism `e` is restriction of scalars along `e⁻¹`,
for modules in a universe above the ring's. -/
private def extendScalarsIsoRestrictScalarsSymmLarge (e : R ≃+* S) :
    ModuleCat.extendScalars.{u, u, max u v} e.toRingHom ≅
      ModuleCat.restrictScalars.{max u v} e.symm.toRingHom :=
  Adjunction.leftAdjointUniq (ModuleCat.extendRestrictScalarsAdj.{v, u, u} e.toRingHom)
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).symm.toAdjunction

/-- Along a ring isomorphism, extension of scalars undoes restriction of scalars, for modules
in a universe above the ring's. -/
private def restrictExtendScalarsSelfIsoLarge (e : R ≃+* S) :
    ModuleCat.restrictScalars.{max u v} e.toRingHom ⋙
        ModuleCat.extendScalars.{u, u, max u v} e.toRingHom ≅
      𝟭 (ModuleCat.{max u v} S) :=
  Functor.isoWhiskerLeft _ (extendScalarsIsoRestrictScalarsSymmLarge.{u, v} e) ≪≫
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).unitIso.symm

/-- Along a ring isomorphism, restriction of scalars undoes extension of scalars, for modules
in a universe above the ring's. -/
private def extendRestrictScalarsSelfIsoLarge (e : R ≃+* S) :
    ModuleCat.extendScalars.{u, u, max u v} e.toRingHom ⋙
        ModuleCat.restrictScalars.{max u v} e.toRingHom ≅
      𝟭 (ModuleCat.{max u v} R) :=
  Functor.isoWhiskerRight (extendScalarsIsoRestrictScalarsSymmLarge.{u, v} e)
      (ModuleCat.restrictScalars.{max u v} e.toRingHom) ≪≫
    (ModuleCat.restrictScalarsComp'.{max u v} e.toRingHom e.symm.toRingHom
      (e.symm.toRingHom.comp e.toRingHom) rfl).symm ≪≫
    ModuleCat.restrictScalarsId'.{max u v} _ (by ext x; simp)

section Target

variable [HasDerivedCategory.{wS} (ModuleCat.{max u v} S)]

/-- Degreewise extension of scalars along a ring isomorphism, followed by localization, inverts
quasi-isomorphisms: extension of scalars along an isomorphism is exact, hence preserves
homology. -/
private lemma isInvertedBy_extensionOfScalarsComplex (e : R ≃+* S) :
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)).IsInvertedBy
      (extensionOfScalarsComplexGeneral.{u, v, u, wS} e.toRingHom) := by
  have : Limits.PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max u v} e.toRingHom) :=
    Limits.preservesFiniteLimits_of_natIso
      (extendScalarsIsoRestrictScalarsSymmLarge.{u, v} e).symm
  have : Limits.PreservesFiniteColimits
      (ModuleCat.extendScalars.{u, u, max u v} e.toRingHom) :=
    Limits.preservesFiniteColimits_of_natIso
      (extendScalarsIsoRestrictScalarsSymmLarge.{u, v} e).symm
  intro K L g hg
  have : QuasiIso g := hg
  have h : QuasiIso (((ModuleCat.extendScalars.{u, u, max u v} e.toRingHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g) := inferInstance
  exact Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} S) (ComplexShape.up ℤ)) _ h

/-- Degreewise restriction of scalars along a ring isomorphism, followed by degreewise extension
of scalars along it and localization, is the localization functor. -/
@[no_expose]
public def restrictExtensionOfScalarsComplexIso (e : R ≃+* S) :
    (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        extensionOfScalarsComplexGeneral.{u, v, u, wS} e.toRingHom ≅
      DerivedCategory.Q (C := ModuleCat.{max u v} S) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (restrictExtendScalarsSelfIsoLarge.{u, v} e)
          (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso (ModuleCat.{max u v} S) (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫
    Functor.leftUnitor _

end Target

section

variable [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
  [HasDerivedCategory.{wS} (ModuleCat.{max u v} S)]

/-- **Along a ring isomorphism, every complex computes derived extension of scalars.** The
comparison of `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` is
invertible, not merely on K-flat complexes: degreewise extension of scalars along an isomorphism
inverts quasi-isomorphisms, and a left derived functor of a functor inverting the weak
equivalences has invertible comparison. -/
public theorem isIso_comparison_of_ringEquiv (e : R ≃+* S) :
    IsIso (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).comparison :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts _ _
    (isInvertedBy_extensionOfScalarsComplex.{u, v} e)

/-- Degreewise extension of scalars along a ring isomorphism, followed by localization and by
derived restriction of scalars along it, is the localization functor. -/
@[no_expose]
public def extensionOfScalarsComplexRestrictIso (e : R ≃+* S) :
    extensionOfScalarsComplexGeneral.{u, v, u, wS} e.toRingHom ⋙
        (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory ≅
      DerivedCategory.Q (C := ModuleCat.{max u v} R) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((ModuleCat.extendScalars.{u, u, max u v} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso (extendRestrictScalarsSelfIsoLarge.{u, v} e)
          (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
      DerivedCategory.Q ≪≫
    Functor.leftUnitor _

/-- The comparison from the localization functor of `D(R)` to itself, going through derived
extension of scalars along `e` and restriction of scalars along `e`. The source is written
without an associator, which is a definitional identity of functors, so that the components of
this isomorphism are the stated composites on the nose. -/
private def extendRestrictCounit (e : R ≃+* S) :
    DerivedCategory.Q ⋙ ((totalDerivedExtensionScalars.{u, u, v} e.toRingHom).functor ⋙
        (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory) ≅
      DerivedCategory.Q (C := ModuleCat.{max u v} R) :=
  Functor.isoWhiskerRight
      (@asIso _ _ _ _ (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).comparison
        (isIso_comparison_of_ringEquiv.{u, v} e))
      (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory ≪≫
    extensionOfScalarsComplexRestrictIso.{u, v} e

/-- The comparison from the localization functor of `D(S)` to itself, going through restriction
of scalars along `e` and derived extension of scalars along `e`. The associators are omitted,
being definitional identities of functors, so that the components of this isomorphism are the
stated composites on the nose. -/
private def restrictExtendCounit (e : R ≃+* S) :
    DerivedCategory.Q ⋙ ((ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).functor) ≅
      DerivedCategory.Q (C := ModuleCat.{max u v} S) :=
  Functor.isoWhiskerRight
      (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategoryFactors
      (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).functor ≪≫
    Functor.isoWhiskerLeft
      ((ModuleCat.restrictScalars.{max u v} e.toRingHom).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (@asIso _ _ _ _ (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).comparison
        (isIso_comparison_of_ringEquiv.{u, v} e)) ≪≫
    restrictExtensionOfScalarsComplexIso.{u, v} e

/-- **Derived restriction of scalars along a ring isomorphism undoes derived extension of
scalars along it.** Both the composite and the identity functor of `D(R)` are left derived
functors of the localization functor, so they agree. -/
@[no_expose]
public def totalDerivedExtendRestrictScalarsSelfIso (e : R ≃+* S) :
    (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).functor ⋙
        (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{max u v} R)) :=
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) _
    (extendRestrictCounit.{u, v} e)
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
    (𝟭 (DerivedCategory (ModuleCat.{max u v} R)))
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{max u v} R)))
  Functor.leftDerivedUnique _ _ (extendRestrictCounit.{u, v} e).hom
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{max u v} R))).hom
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))

/-- The isomorphism is the one factoring the comparison `extendRestrictCounit`. -/
private lemma totalDerivedExtendRestrictScalarsSelfIso_fac (e : R ≃+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (totalDerivedExtendRestrictScalarsSelfIso.{u, v} e).hom.app (DerivedCategory.Q.obj P) =
      (extendRestrictCounit.{u, v} e).hom.app P := by
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
    (𝟭 (DerivedCategory (ModuleCat.{max u v} R)))
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{max u v} R)))
  have h := Functor.leftDerived_fac_app (𝟭 (DerivedCategory (ModuleCat.{max u v} R)))
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{max u v} R))).hom
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) _
    (extendRestrictCounit.{u, v} e).hom P
  simpa [totalDerivedExtendRestrictScalarsSelfIso, Functor.leftDerivedUnique,
    Functor.leftDerivedNatIso, Functor.leftDerivedNatTrans] using h

/-- **The pinning of `totalDerivedExtendRestrictScalarsSelfIso`.** On every complex of
`R`-modules the isomorphism is the comparison of derived extension of scalars, restricted along
`e`, followed by the complex-level comparison. The type of the isomorphism alone would not
distinguish it from its negative, so this equation is part of the statement. -/
public theorem totalDerivedExtendRestrictScalarsSelfIso_comparison (e : R ≃+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) :
    (totalDerivedExtendRestrictScalarsSelfIso.{u, v} e).hom.app (DerivedCategory.Q.obj P) =
      (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory.map
          ((totalDerivedExtensionScalars.{u, u, v} e.toRingHom).comparison.app P) ≫
        (extensionOfScalarsComplexRestrictIso.{u, v} e).hom.app P :=
  totalDerivedExtendRestrictScalarsSelfIso_fac.{u, v} e P

/-- **Derived extension of scalars along a ring isomorphism undoes restriction of scalars along
it.** Both the composite and the identity functor of `D(S)` are left derived functors of the
localization functor. This is the composite the affine case of [Stacks, Tag 0DI7] produces. -/
@[no_expose]
public def totalDerivedRestrictExtendScalarsSelfIso (e : R ≃+* S) :
    (ModuleCat.restrictScalars.{max u v} e.toRingHom).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).functor ≅
      𝟭 (DerivedCategory (ModuleCat.{max u v} S)) :=
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} S) (ComplexShape.up ℤ)) _
    (restrictExtendCounit.{u, v} e)
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} S) (ComplexShape.up ℤ))
    (𝟭 (DerivedCategory (ModuleCat.{max u v} S)))
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{max u v} S)))
  Functor.leftDerivedUnique _ _ (restrictExtendCounit.{u, v} e).hom
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{max u v} S))).hom
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} S) (ComplexShape.up ℤ))

/-- The isomorphism is the one factoring the comparison `restrictExtendCounit`. -/
private lemma totalDerivedRestrictExtendScalarsSelfIso_fac (e : R ≃+* S)
    (P : CochainComplex (ModuleCat.{max u v} S) ℤ) :
    (totalDerivedRestrictExtendScalarsSelfIso.{u, v} e).hom.app (DerivedCategory.Q.obj P) =
      (restrictExtendCounit.{u, v} e).hom.app P := by
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} S) (ComplexShape.up ℤ))
    (𝟭 (DerivedCategory (ModuleCat.{max u v} S)))
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{max u v} S)))
  have h := Functor.leftDerived_fac_app (𝟭 (DerivedCategory (ModuleCat.{max u v} S)))
    (Functor.rightUnitor (DerivedCategory.Q (C := ModuleCat.{max u v} S))).hom
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} S) (ComplexShape.up ℤ)) _
    (restrictExtendCounit.{u, v} e).hom P
  simpa [totalDerivedRestrictExtendScalarsSelfIso, Functor.leftDerivedUnique,
    Functor.leftDerivedNatIso, Functor.leftDerivedNatTrans] using h

/-- **The pinning of `totalDerivedRestrictExtendScalarsSelfIso`.** On every complex of
`S`-modules the isomorphism is the comparison of derived restriction of scalars, followed by the
comparison of derived extension of scalars and by the complex-level comparison. The type of the
isomorphism alone would not distinguish it from its negative, so this equation is part of the
statement. -/
public theorem totalDerivedRestrictExtendScalarsSelfIso_comparison (e : R ≃+* S)
    (P : CochainComplex (ModuleCat.{max u v} S) ℤ) :
    (totalDerivedRestrictExtendScalarsSelfIso.{u, v} e).hom.app (DerivedCategory.Q.obj P) =
      (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).functor.map
          ((ModuleCat.restrictScalars.{max u v}
            e.toRingHom).mapDerivedCategoryFactors.hom.app P) ≫
        (totalDerivedExtensionScalars.{u, u, v} e.toRingHom).comparison.app
            (((ModuleCat.restrictScalars.{max u v} e.toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
          (restrictExtensionOfScalarsComplexIso.{u, v} e).hom.app P :=
  totalDerivedRestrictExtendScalarsSelfIso_fac.{u, v} e P

end

end CochainComplex.DerivedExtensionScalars

end
