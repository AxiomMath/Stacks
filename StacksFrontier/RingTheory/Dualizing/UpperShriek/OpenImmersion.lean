module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.Perfect.DerivedReduction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Independence

/-!
# Upper shriek along a map whose spectrum map is an isomorphism

[Stacks, Tag 0C0H] computes the algebraic upper shriek functor of a map `φ : R → R'` with
`Spec(R') → Spec(R)` an open immersion: it is derived base change `- ⊗_R^L R'`.  This file
proves the case in which that open immersion is an isomorphism, that is the case of a
bijective ring homomorphism.

## Main results

* `Dualizing.upperShriekFunctor_iso_derivedExtensionScalars_of_bijective` — for a bijective
  `f : R →+* S`, upper shriek along `f` is derived base change along `f`.

## Implementation notes

For a bijective `f` the zero-variable presentation `MvPolynomial (Fin 0) R ≃+* R → S`
presents `f`, and for it upper shriek is the shift-free composite of derived base change
along `MvPolynomial.C` with `RHom` along the surjection.  Both are then identified with
derived base change along `f` by uniqueness of adjoints: derived base change along
`MvPolynomial.C` is left adjoint to restriction, `RHom` along a bijective map is the inverse
of the restriction equivalence hence also a left adjoint to restriction, and restriction
along `f` factors as the composite of the two restrictions.

Passing from the zero-variable presentation to an arbitrary one is [Stacks, Tag 0BZJ], which
this library proves only under the hypothesis `Dualizing.PolynomialEvalDuality`; that
hypothesis is therefore carried here too.

The Noetherian hypothesis of the source is not needed for this case and is omitted.  Of the
remaining content of Tag 0C0H, localization at one element *is* proved, in
`StacksFrontier.RingTheory.Dualizing.UpperShriek.LocalizationAway`
(`Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_away`, with nothing carried);
it is not proved here, and it is stated with `- ⊗_R^L R_f` read as derived tensor product with
the unit object rather than as the total left derived functor of extension of scalars used
below, so neither statement subsumes the other.  The general affine open immersion is
proved in `StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatEpimorphism`, as
`Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion`, which carries
the tag; the statement here is the special case in the shape of a total left derived functor of
extension of scalars, and carries no attribute.

## References

* [Stacks Project, Tag 0C0H](https://stacks.math.columbia.edu/tag/0C0H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-- The adjunction between a total left derived model of extension of scalars and derived
restriction of scalars, with the universal property supplied as an explicit argument. -/
private noncomputable def adjunctionOfModel {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (F : DerivedCategory (ModuleCat.{max v u} R) ⥤ DerivedCategory (ModuleCat.{max v u} S))
    (alpha : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, max v u} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (hF : F.IsLeftDerivedFunctor alpha
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ))) :
    F ⊣ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory :=
  letI := hF
  CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, v} f F alpha

private theorem mapDerivedCategory_isEquivalence
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (e : C ≌ D) [e.functor.Additive] :
    e.functor.mapDerivedCategory.IsEquivalence := by
  let Φ := e.functor.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let : Φ.functor.IsEquivalence :=
    (e.mapHomologicalComplex (ComplexShape.up ℤ)).isEquivalence_functor
  let : Φ.IsInduced := by
    refine ⟨?_⟩
    ext X Y f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f e.functor
  let : Φ.IsLocalizedEquivalence := Φ.isLocalizedEquivalence_of_isInduced
  let : CatCommSq Φ.functor DerivedCategory.Q DerivedCategory.Q e.functor.mapDerivedCategory :=
    ⟨e.functor.mapDerivedCategoryFactors.symm⟩
  exact Φ.isEquivalence DerivedCategory.Q DerivedCategory.Q _

/-- **Upper shriek along a bijective ring map**, the case of [Stacks, Tag 0C0H] in which
`Spec(S) → Spec(R)` is an isomorphism: for a bijective `f : R →+* S` the upper shriek functor
attached to any polynomial presentation of `f` is the total left derived functor of extension of
scalars along `f`.  The tag itself, for an arbitrary open immersion, is
`Dualizing.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion`.
The hypothesis `hBZH` is the input of [Stacks, Tag 0BZJ] that this module does not prove,
carried here because the comparison of `p` with the zero-variable presentation is Tag 0BZJ.
The library does prove it, as `Dualizing.polynomialEvalDuality`, so any use downstream of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityProof` can discharge it. -/
theorem upperShriekFunctor_iso_derivedExtensionScalars_of_bijective
    (hBZH : PolynomialEvalDuality.{max v u})
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hbij : Function.Bijective f)
    (p : PolynomialPresentation f) :
    Nonempty (PolynomialPresentation.upperShriekFunctor.{u, v} p ≅
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        f).functor) := by
  let e₀ : MvPolynomial (Fin 0) R ≃+* R := MvPolynomial.isEmptyRingEquiv R (Fin 0)
  let C : R →+* MvPolynomial (Fin 0) R := MvPolynomial.C
  let g : MvPolynomial (Fin 0) R →+* S := f.comp e₀.toRingHom
  have hg : Function.Bijective g := hbij.comp e₀.bijective
  let p₀ : PolynomialPresentation f :=
    { variableCount := 0
      toRingHom := g
      commutes := by
        ext r
        show f (e₀ (MvPolynomial.C r)) = f r
        congr 1
        show (MvPolynomial.C r).coeff 0 = r
        simp
      surjective := hg.2 }
  let F := p₀.derivedExtension.{u, v}
  let RH := derivedHom.{u, v} g
  let ResC := (ModuleCat.restrictScalars.{max v u} C).mapDerivedCategory
  let Resg := (ModuleCat.restrictScalars.{max v u} g).mapDerivedCategory
  let : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, max v u} C) :=
    extendScalars_preservesFiniteLimits_of_flat' C (RingHom.flat_algebraMap_iff.mpr inferInstance)
  let αC := (ModuleCat.extendScalars.{u, u, max v u} C).mapDerivedCategoryFactors.hom
  have hF : F.IsLeftDerivedFunctor αC
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)) := by
    dsimp [F, p₀, PolynomialPresentation.derivedExtension]
    exact Functor.isLeftDerivedFunctor_of_inverts _ _
      (ModuleCat.extendScalars.{u, u, max v u} C).mapDerivedCategoryFactors
  let adjC := adjunctionOfModel.{u, v} C F αC hF
  let adjC' : F ⊣ ResC := adjC
  let eGMod := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.ofBijective g hg)
  let : Resg.IsEquivalence := by
    show eGMod.functor.mapDerivedCategory.IsEquivalence
    exact mapDerivedCategory_isEquivalence eGMod
  let adjGRight : Resg ⊣ RH :=
    (restrictScalarsDerived_adj_derivedHom.{u, v} g).some
  let adjGEquiv := Resg.asEquivalence.toAdjunction
  let isoRH : RH ≅ Resg.asEquivalence.inverse := adjGRight.rightAdjointUniq adjGEquiv
  let adjGLeft : RH ⊣ Resg :=
    Resg.asEquivalence.symm.toAdjunction.ofNatIsoLeft isoRH.symm
  let adjBase := adjC'.comp adjGLeft
  have hres :
      (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory ≅ Resg ⋙ ResC := by
    rw [← p₀.commutes]
    exact (StacksDraft.Perfect.derivedRestrictScalarsComp C g).symm
  let adjBase' := adjBase.ofNatIsoRight hres.symm
  let αf := (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
    f).comparison
  let adjf := adjunctionOfModel.{u, v} f
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v} f).functor αf
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
      f).isLeftDerived
  let eShift : p₀.upperShriekFunctor.{u, v} ≅ F ⋙ RH := by
    dsimp [PolynomialPresentation.upperShriekFunctor, F, RH, p₀]
    exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (shiftFunctorZero
        (DerivedCategory (ModuleCat.{max v u} S)) ℤ))
  exact ⟨(PolynomialPresentation.upperShriekFunctor_iso hBZH f p p₀).some ≪≫ eShift ≪≫
    Adjunction.leftAdjointUniq adjBase' adjf⟩

end Dualizing

end
