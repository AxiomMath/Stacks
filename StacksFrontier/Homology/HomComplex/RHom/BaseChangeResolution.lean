module

public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsResolution

/-!
# A closed value for the derived-Hom base-change morphism of Stacks 0E1X

`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange` is defined as the inverse transpose,
under the derived extension-of-scalars adjunction of Stacks 0GMT, of
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate`, and the only equation recorded
about it is that transpose
(`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv`). A consumer that needs the
morphism itself — rather than its transpose — had nothing.

Two steps close that. First, the inverse transpose of *any* adjunction is the functor applied to
the morphism followed by the counit (`CategoryTheory.Adjunction.homEquiv_counit`), which needs no
hypothesis at all; this gives `derivedHomBaseChange_eq_counit`. Second, the two pieces that
appear in the result — the unit of Stacks 0GMT at the covariant argument, and its counit at the
target internal-Hom object — are pinned at arbitrary objects by
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_model`
and `..._counit_app_eq_of_model`. Composing gives `derivedHomBaseChange_eq_of_models`, in which
every factor is either degreewise data of the extension–restriction adjunction on cochain
complexes, the model comparison, a localization comparison, the change-of-rings isomorphism of
Stacks 0E1W, or a chosen model isomorphism.

## Main results

* `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_counit`: the unconditional
  expansion of the inverse transpose.
* `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_eq_of_models`: the value with the
  unit and the counit replaced by their pinned forms at chosen models.

## References

* [The Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [The Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.DerivedHom.ExtensionOfScalars

universe uR uA uM

attribute [local instance] HasDerivedCategory.standard

/-- **The derived-Hom base-change morphism of Stacks 0E1X, unconditionally expanded.** The
definition is an inverse transpose under the adjunction of Stacks 0GMT; by
`CategoryTheory.Adjunction.homEquiv_counit` that transpose expands with no hypothesis into the
derived extension functor applied to
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate`, followed by the counit of the
adjunction at the target internal-Hom object. Together with
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_homEquiv` this is the morphism itself,
rather than its transpose. -/
theorem derivedHomBaseChange_eq_counit
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K M : DerivedCategory (ModuleCat.{max uR uA uM} R)),
    derivedHomBaseChange.{uR, uA, uM} f F comparison K M =
      F.map ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR,
              max uR uA uM} R).map
            (𝟙 (Opposite.op K),
              (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA,
                uM} f F comparison).unit.app M) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app (Opposite.op K, F.obj M)) ≫
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
            f F comparison).counit.app
          ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).obj
            (Opposite.op (F.obj K), F.obj M)) := by
  let : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  intro F comparison hF K M
  have := hF
  refine Eq.trans ?_ (Adjunction.homEquiv_counit
    (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{uR, uA, uM}
      f F comparison) _ _ _)
  exact ((Equiv.symm_apply_eq _).mpr
    (derivedHomBaseChange_homEquiv.{uR, uA, uM} f F comparison K M).symm).symm

open CochainComplex.DerivedExtensionScalars in
/-- **The derived-Hom base-change morphism of Stacks 0E1X, with no unit and no counit left in
it.** Choosing a K-flat model `φ` of the covariant argument and any model `ψ` of the target
internal-Hom object — both of which always exist, by
`CochainComplex.DerivedExtensionScalars.exists_kFlat_model` and essential surjectivity of
`DerivedCategory.Q` — every factor of `derivedHomBaseChange_eq_counit` is replaced by named data:
the degreewise unit and counit of the extension–restriction adjunction on cochain complexes, the
localization comparison `CategoryTheory.Functor.mapDerivedCategoryFactors`, the model comparison
`comparison` and its inverse at the K-flat model, the change-of-rings isomorphism of
Stacks 0E1W, and the two model isomorphisms.

Nothing is assumed of `K` or `M`. In particular `M` may be a derived tensor product, which is the
case the K-flat hypothesis of
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction_unit_app_eq_of_kFlat`
excluded and the whole reason this file exists. -/
theorem derivedHomBaseChange_eq_of_models
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A) :
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
    letI : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
    ∀ (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
      DerivedCategory (ModuleCat.{max uR uA uM} A))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]
    (K M : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (X : CochainComplex (ModuleCat.{max uR uA uM} R) ℤ)
    (hX : CochainComplex.KFlat.{uR, max uM uA} X)
    (φ : M ≅ DerivedCategory.Q.obj X)
    (Y : CochainComplex (ModuleCat.{max uR uA uM} A) ℤ)
    (ψ : (_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uA, max uR uA uM} A).obj
        (Opposite.op (F.obj K), F.obj M) ≅ DerivedCategory.Q.obj Y),
    letI : IsIso (comparison.app X) :=
      CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM}
        f F comparison X hX
    derivedHomBaseChange.{uR, uA, uM} f F comparison K M =
      F.map ((_root_.Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR,
              max uR uA uM} R).map
            (𝟙 (Opposite.op K),
              φ.hom ≫
                (DerivedCategory.Q.map
                    (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR,
                      uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).unit.app X) ≫
                  (ModuleCat.restrictScalars.{max uR uA uM, uR,
                      uA} f).mapDerivedCategoryFactors.inv.app
                      (((ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
                        (ComplexShape.up ℤ)).obj X) ≫
                    (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
                      (inv (comparison.app X))) ≫
                (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
                  (show (DerivedCategory.Q ⋙ F).obj X ⟶ F.obj M from F.map φ.inv)) ≫
          (Stacks.DerivedHom.BaseChange.derivedHomRestrictScalarsNatIso.{uR, uA, uM} f F
            comparison).hom.app (Opposite.op K, F.obj M)) ≫
        F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).mapDerivedCategory.map
            ψ.hom) ≫
          (F.map ((ModuleCat.restrictScalars.{max uR uA uM, uR,
                uA} f).mapDerivedCategoryFactors.hom.app Y) ≫
            comparison.app (((ModuleCat.restrictScalars.{max uR uA uM, uR,
                uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj Y) ≫
              DerivedCategory.Q.map
                (((ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR,
                  uA} f).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app Y)) ≫
          ψ.inv := by
  let : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).isRightAdjoint
  let : (ModuleCat.restrictScalars.{max uR uA uM, uR, uA} f).IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uR uM, uR, uA} f).isLeftAdjoint
  let : (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR uM, uR, uA} f).left_adjoint_additive
  intro F comparison hF K M X hX φ Y ψ
  have := hF
  have : IsIso (comparison.app X) :=
    CochainComplex.DerivedExtensionScalars.isIso_comparison_app_of_kFlat.{uR, uA, uM}
      f F comparison X hX
  rw [derivedHomBaseChange_eq_counit.{uR, uA, uM} f F comparison K M,
    derivedExtensionScalarsAdjunction_unit_app_eq_of_model.{uR, uA, uM} f F comparison M X hX φ,
    derivedExtensionScalarsAdjunction_counit_app_eq_of_model.{uR, uA, uM} f F comparison _ Y ψ]

end Stacks.DerivedHom.ExtensionOfScalars

end
