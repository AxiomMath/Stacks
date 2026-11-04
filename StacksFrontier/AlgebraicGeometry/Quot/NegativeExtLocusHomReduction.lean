module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCartesianPullback
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocus
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFunctorTransport

/-!
# Stacks 0DLC, part (3): the reduction to the case `W = Y`

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, `K` a
pseudo-coherent and `E` a `Y`-perfect object of `D(𝒪_X)`, and `W ⊆ Y` an open characterized as in
Stacks 0DLC, part (1).  The source reduces part (3) to the case `W = Y`: it "is entirely
formulated in terms of the category `Spaces/W` and the restrictions `X_W`, `K_W`, `E_W`".  This
file proves that reduction, as part (2) was reduced in
`StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocus.lean`.

The content is an isomorphism of functors on the test schemes `T` over an algebraic space `V`
over `Y`: the relative derived Hom functor of `X_V ⟶ V` at the restrictions `K_V`, `E_V` is the
relative derived Hom functor of `f` at `K`, `E`, restricted to the test schemes over `V`.  Its
components are the identifications `(X_V)_T = X_T` of the iterated base change, and its
naturality is the coherence of the derived pullback pseudofunctor, through the transport lemmas of
`StacksFrontier/AlgebraicGeometry/Quot/RelativeHomFunctorTransport.lean`.

## Main definitions

* `AlgebraicGeometry.Space.baseChangeOverBaseChangeIso`: `(X_V)_T ≅ X_T` for a test scheme `T`
  over `V`, and `AlgebraicGeometry.Space.baseChangeOverBaseChangeNatIso` its naturality.
* `AlgebraicGeometry.Space.relativeDerivedHomBaseChangeIso`: the isomorphism of the relative
  derived Hom functor of `X_V ⟶ V` at `K_V`, `E_V` with the restriction of that of `f` at `K`,
  `E`.

## Main results

* `RelativeDerivedHomRepresentableOfFibres.relativeDerivedHomRepresentableOverLocus`
  (in `AlgebraicGeometry.Space`): **Stacks 0DLC, part (3), reduces to the case `W = Y`**.
  Nothing is registered.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DKT](https://stacks.math.columbia.edu/tag/0DKT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable {X Y : AlgebraicSpaces B S hS}

/-- **The iterated base change.**  For an algebraic space `V` over `Y` and a test scheme `T` over
`V`, the base change of `X_V ⟶ V` along `T` is the base change of `f` along `T`, regarded as a
test scheme over `Y`: both are cartesian over `T ⟶ Y`, by pasting the two cartesian squares. -/
def baseChangeOverBaseChangeIso (f : X ⟶ Y) (V : Over Y) (T : SchemesOver V.left) :
    overBaseChange (overInclusion f V) ((schemesOverToOver V.left).obj T) ≅
      overBaseChange f ((schemesOverToOver Y).obj
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).obj T)) :=
  have hsq : IsPullback (overProjection f V) (overInclusion f V) f V.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f V.hom
  have hT : IsPullback (overProjection (overInclusion f V) ((schemesOverToOver V.left).obj T))
      (overInclusion (overInclusion f V) ((schemesOverToOver V.left).obj T))
      (overInclusion f V) T.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS _ T.hom
  (hT.paste_horiz hsq).isoIsPullback _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f _)

/-- The iterated base change commutes with the projections to `X`. -/
@[reassoc]
theorem baseChangeOverBaseChangeIso_hom_projection (f : X ⟶ Y) (V : Over Y)
    (T : SchemesOver V.left) :
    (baseChangeOverBaseChangeIso f V T).hom ≫ overProjection f ((schemesOverToOver Y).obj
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).obj T)) =
      overProjection (overInclusion f V) ((schemesOverToOver V.left).obj T) ≫
        overProjection f V :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The iterated base change commutes with the projections to `T`. -/
@[reassoc]
theorem baseChangeOverBaseChangeIso_hom_inclusion (f : X ⟶ Y) (V : Over Y)
    (T : SchemesOver V.left) :
    (baseChangeOverBaseChangeIso f V T).hom ≫ overInclusion f ((schemesOverToOver Y).obj
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).obj T)) =
      overInclusion (overInclusion f V) ((schemesOverToOver V.left).obj T) :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The iterated base change is natural in the test scheme**: the identifications
`(X_V)_T ≅ X_T` form an isomorphism of the two base change functors on the test schemes over
`V`. -/
def baseChangeOverBaseChangeNatIso (f : X ⟶ Y) (V : Over Y) :
    schemesOverToOver V.left ⋙ overBaseChangeFunctor (overInclusion f V) ⋙ Over.forget _ ≅
      (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom ⋙ schemesOverToOver Y) ⋙
        overBaseChangeFunctor f ⋙ Over.forget X :=
  NatIso.ofComponents (fun T => baseChangeOverBaseChangeIso f V T) (fun {T T'} a => by
    refine overBaseChange_hom_ext f ?_ ?_
    · change (overBaseChangeMap _ _ ≫ (baseChangeOverBaseChangeIso f V T').hom) ≫
          overProjection f _ = ((baseChangeOverBaseChangeIso f V T).hom ≫
            overBaseChangeMap f _) ≫ overProjection f _
      simp only [Category.assoc, baseChangeOverBaseChangeIso_hom_projection,
        overBaseChangeMap_comp_projection, overBaseChangeMap_comp_projection_assoc]
    · change (overBaseChangeMap _ _ ≫ (baseChangeOverBaseChangeIso f V T').hom) ≫
          overInclusion f _ = ((baseChangeOverBaseChangeIso f V T).hom ≫
            overBaseChangeMap f _) ≫ overInclusion f _
      simp only [Category.assoc, baseChangeOverBaseChangeIso_hom_inclusion,
        overBaseChangeMap_comp_inclusion, baseChangeOverBaseChangeIso_hom_inclusion_assoc]
      exact (overBaseChangeMap_comp_inclusion (overInclusion f V)
        ((schemesOverToOver V.left).map a)).trans rfl)

/-- **The relative derived Hom functor restricts along a base change.**  For an algebraic space
`V` over `Y`, the functor `T ↦ Hom(K_{X_V,T}, E_{X_V,T})` of `X_V ⟶ V` at the restrictions
`K_V`, `E_V` is the functor `T ↦ Hom(K_T, E_T)` of `f` at `K`, `E`, restricted to the test schemes
over `V`: reindexing, then postcomposition with the projection `X_V ⟶ X`, then the iterated base
change `AlgebraicGeometry.Space.baseChangeOverBaseChangeNatIso`. -/
def relativeDerivedHomBaseChangeIso (f : X ⟶ Y) (V : Over Y) (K E : derivedModules B S hS X) :
    relativeDerivedHom (overInclusion f V)
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K)
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E) ≅
      (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom).op ⋙
        relativeDerivedHom f K E :=
  (smallEtaleDerivedPullbackData B S hS).relHomFunctorReindexIso
      (smallEtaleDerivedPullbackData_isCoherent B S hS) (schemesOverToOver V.left)
      (overBaseChangeCone (overInclusion f V)) _ _ ≪≫
    (smallEtaleDerivedPullbackData B S hS).relHomPostcompIso
      (smallEtaleDerivedPullbackData_isCoherent B S hS)
      ((overBaseChangeCone (overInclusion f V)).reindex (schemesOverToOver V.left))
      (overProjection f V) K E ≪≫
    ((smallEtaleDerivedPullbackData B S hS).relHomIsoOfIso
      (smallEtaleDerivedPullbackData_isCoherent B S hS)
      (((overBaseChangeCone (overInclusion f V)).reindex (schemesOverToOver V.left)).postcomp
        (overProjection f V))
      ((overBaseChangeCone f).reindex
        (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom ⋙ schemesOverToOver Y))
      (baseChangeOverBaseChangeNatIso f V)
      (fun T => baseChangeOverBaseChangeIso_hom_projection f V T) K E).symm ≪≫
    ((smallEtaleDerivedPullbackData B S hS).relHomFunctorReindexIso
      (smallEtaleDerivedPullbackData_isCoherent B S hS)
      (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) V.hom ⋙ schemesOverToOver Y)
      (overBaseChangeCone f) K E).symm

/-- **Stacks 0DLC: part (3) reduces to the case `W = Y`.**  For a locus `W`
of part (1), the base change `X_W ⟶ W` is proper, flat and of finite presentation, `K_W` is
pseudo-coherent (Stacks 08H4), `E_W` is `W`-perfect (Stacks 0DKT at the representable
`X_W ⟶ X`, `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_pull_of_isPullback`), and the
negative fibre
extensions of `K_W`, `E_W` vanish at every point of `W` with values in a field
(`AlgebraicGeometry.Space.IsNegativeExtLocus.hasNoNegativeExtAt_restrict`); the case `W = Y` for
`X_W ⟶ W` then gives part (3) for `W`, through
`AlgebraicGeometry.Space.relativeDerivedHomBaseChangeIso`. -/
theorem RelativeDerivedHomRepresentableOfFibres.relativeDerivedHomRepresentableOverLocus
    (h : RelativeDerivedHomRepresentableOfFibres B S hS) :
    RelativeDerivedHomRepresentableOverLocus B S hS := by
  intro X Y f hp hflat hfp K E hK hE W hW
  let ι := openSubspaceImmersion B S hS W
  let OW : Over Y := Over.mk ι
  let fW := overInclusion f OW
  let pW := overProjection f OW
  have hsqW : IsPullback pW fW f ι := AlgebraicSpaces.isPullback_fiberProduct B S hS f OW.hom
  have hpW : IsProper B S hS fW.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback hsqW hp
  have hflatW : IsFlat B S hS fW.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hsqW hflat
  have hfpW : IsFinitePresentation B S hS fW.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hsqW hfp
  have hrep : yoneda.relativelyRepresentable pW.hom :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS hsqW).flip W.2.2.rep
  have hKW : (smallEtaleRingedSite B S hS (overBaseChange f OW).1
      (overBaseChange f OW).2).IsPseudoCoherent
      (((smallEtaleDerivedPullbackData B S hS).pull pW).obj K) :=
    isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS pW hrep K hK
  have hEW :=
    isPerfectRelativeToCanonical_pull_of_isPullback hsqW hrep hflatW hfpW.1 hflat hfp.1 E hE
  exact (h fW hpW hflatW hfpW _ _ hKW hEW hW.hasNoNegativeExtAt_restrict).of_iso
    (relativeDerivedHomBaseChangeIso f OW K E)

end AlgebraicGeometry.Space

end
