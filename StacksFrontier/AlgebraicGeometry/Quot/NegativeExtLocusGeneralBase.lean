module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedEtaleBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomEtaleRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightTExactCohomologyClass

/-!
# Stacks 0DLC, part (2), over a general base, from Stacks 0DKY

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, `K` a
pseudo-coherent and `E` a `Y`-perfect object of `D(𝒪_X)`, and assume the negative fibre
extensions `Ext^i(K_y, E_y)`, `i < 0`, vanish at every point `y` of `Y` with values in a field.
This file proves `Ext^i(K_V, E_V) = 0` for `i < 0` and every algebraic space `V` over `Y`, the
case `W = Y` of Stacks 0DLC, part (2), with no condition on `Y`, granted Stacks 0DKY alone
(`AlgebraicGeometry.Space.RelativeDerivedHomDualExists`, not yet proved here).

## The argument

As in the source, one works étale locally on `V`.  Put `G = Rf_{V*} R𝓗om(K_V, E_V)` on `V`.  By
Stacks 08JA and the Leray identity, `Ext^i(K_V, E_V) = H^i(V, G)`, so it suffices that `G` has no
cohomology in negative degrees, and this is étale local on `V`
(`AlgebraicGeometry.Space.isGE_of_isGE_smallEtaleDerivedModulePullback_chartToSpace`).  On an
affine étale chart `c : T ⟶ V`, with `X_T = X_V ×_V T`, `i : X_T ⟶ X_V` and `f_T : X_T ⟶ T`:

* étale base change (Stacks 08GE) and the étale restriction of the derived internal Hom
  (Stacks 08JB) give `Lc^* G ≅ Rf_{T*} R𝓗om(K_T, E_T)`;
* `T` is affine, hence quasi-compact and quasi-separated, and `X_T ⟶ X` is representable (it is the
  base change of the morphism `T ⟶ Y` from a scheme to an algebraic space), so `K_T` is
  pseudo-coherent (Stacks 08H4) and `E_T` is `T`-perfect (Stacks 0DKT at a representable
  morphism), and Stacks 0DKY over `T` gives `Rf_{T*} R𝓗om(K_T, E_T) ≅ R𝓗om(L, 𝒪_T)` for a
  pseudo-coherent `L` on `T`, compatibly with base change;
* the field points of `T` are field points of `Y`, so `L` has no cohomology in positive degrees
  (`AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE`), and then `R𝓗om(L, 𝒪_T)` has none in
  negative degrees (`AlgebraicGeometry.Space.isGE_smallEtaleDerivedDual`).

No covering of `V` by charts through affine charts of `Y` is needed: the morphism from a scheme
to an algebraic space is representable because the diagonal of an algebraic space is
(`AlgebraicGeometry.Space.relativelyRepresentable_of_isAlgebraicSpace`).

## Main results

* `AlgebraicGeometry.Space.isGE_smallEtaleDerivedDual`: the dual of an object with no cohomology
  in positive degrees has none in negative degrees.
* `AlgebraicGeometry.Space.hasNoNegativeExtAt_pull_iff_of_isPullback`: the fibres of a base change
  of `f` are fibres of `f`.
* `AlgebraicGeometry.Space.isGE_pushforwardSheafHom_of_dualExists`: `Rf_{V*} R𝓗om(K_V, E_V)` has
  no cohomology in negative degrees.
* `AlgebraicGeometry.Space.negativeExtVanishesOfFibres_of_dualExists`: Stacks 0DLC, part (2), in
  the case `W = Y`, granted Stacks 0DKY.
* `AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_dualExists_of_steps`: part
  (3) in the case `W = Y`, from Stacks 0DKY, Stacks 0DL9 and the internal steps (S) and (L), part
  (2) being discharged by the above.

Nothing is registered: every statement carries Stacks 0DKY as a hypothesis.

## Implementation notes

Only `AlgebraicGeometry.Space.isGE_smallEtaleDerivedDual` pins the standard model of the derived
category (at the priority of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedSheafHom.lean`,
in its own section), as it works on the equi-universe model; everything else is elaborated at the
instances of `StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocus.lean`, the objects of
`D(𝒪)` being typed as `AlgebraicGeometry.Space.derivedModules` where an instance is searched.

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
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

/-! ### The dual of a connective object -/

section Dual

/- `D(𝒪_Y)`, the derived equivalence with the model and the derived internal Hom of the model are
stated at the standard model of the derived category.  At plain priority another
`HasDerivedCategory` instance on the sheaves of modules of the model, in a lower universe, is found
first, and `AlgebraicGeometry.RingedSite.isGE_derivedSheafHom` no longer applies. -/
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The dual of an object with no cohomology in positive degrees has none in negative
degrees**: if `L` in `D(𝒪_Y)` is `≤ 0`, then `R𝓗om(L, 𝒪_Y)` is `≥ 0`.  On the equi-universe
model this is `AlgebraicGeometry.RingedSite.isGE_derivedSheafHom` with `d = b = 0`, and the derived
equivalence with the model is exact in both directions. -/
theorem isGE_smallEtaleDerivedDual (Y : AlgebraicSpaces B S hS)
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hL : L.IsLE 0) : (smallEtaleDerivedDual B S hS Y L).IsGE 0 := by
  let E := smallEtaleModelModulesEquivalence B S hS Y
  let O := (DerivedCategory.singleFunctor _ 0).obj
    (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))
  have : E.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have := hL
  let H := ((RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS Y.1 Y.2)).obj
    (Opposite.op (E.functor.mapDerivedCategory.obj L))).obj (E.functor.mapDerivedCategory.obj O)
  have : H.IsGE 0 := RingedSite.isGE_derivedSheafHom (smallEtaleModelRingedSite B S hS Y.1 Y.2)
    (E.functor.mapDerivedCategory.obj L) (E.functor.mapDerivedCategory.obj O) 0 0
    (Stacks.Homology.isLE_mapDerivedCategory_obj E.functor L 0)
    (DerivedCategory.isGE_mapDerivedCategory_obj E.functor O 0)
  exact DerivedCategory.isGE_mapDerivedCategory_obj E.inverse H 0

end Dual

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The fibres of a base change -/

section Fibres

variable {X Y X' Y' : AlgebraicSpaces B S hS}

/-- **The fibres of a base change are fibres of the morphism.**  For a cartesian square
`X' = X ×_Y Y'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`, and a test scheme `T₀` over
`Y'`, the negative extensions of `L(g')^*K` and `L(g')^*E` at `T₀` (for `f'`) are those of `K` and
`E` at `T₀` regarded as a test scheme over `Y`: the fibre of `X'` over `T₀` is the fibre of `X`,
by pasting the two cartesian squares. -/
theorem hasNoNegativeExtAt_pull_iff_of_isPullback {f : X ⟶ Y} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} (sq : IsPullback g' f' f g) (K E : derivedModules B S hS X)
    (T₀ : SchemesOver Y') :
    HasNoNegativeExtAt f' (((smallEtaleDerivedPullbackData B S hS).pull g').obj K)
        (((smallEtaleDerivedPullbackData B S hS).pull g').obj E) T₀ ↔
      HasNoNegativeExtAt f K E
        ((CostructuredArrow.map (S := schemeSpaceFunctor B S hS) g).obj T₀) := by
  let T₁ : SchemesOver Y := (CostructuredArrow.map (S := schemeSpaceFunctor B S hS) g).obj T₀
  have hpb : IsPullback (baseChangeProjection f' T₀ ≫ g') (baseChangeInclusion f' T₀) f T₁.hom :=
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f' T₀.hom).paste_horiz sq
  have hT₁ : IsPullback (baseChangeProjection f T₁) (baseChangeInclusion f T₁) f T₁.hom :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f T₁.hom
  refine forall₂_congr fun i _ => ?_
  rw [subsingleton_pull_comp_iff]
  exact (subsingleton_pull_iff_of_iso (hpb.isoIsPullback _ _ hT₁)
    (hpb.isoIsPullback_hom_fst _ _ hT₁) K E i).symm

end Fibres

/-! ### The derived direct image of the derived internal Hom, étale locally -/

section Local

variable {X Y : AlgebraicSpaces B S hS}

/-- **A connective object has no negative cohomology classes**: if `G` in `D(𝒪_Y)` has no
cohomology in negative degrees, then `H^i(Y, G) = Hom(𝒪_Y, G[i]) = 0` for `i < 0`, `𝒪_Y` being in
degree zero and `G[i]` having no cohomology below degree `-i > 0`. -/
theorem subsingleton_structureObject_hom_shift_of_isGE (G : derivedModules B S hS Y)
    (hG : G.IsGE 0) (i : ℤ) (hi : i < 0) :
    Subsingleton (structureObject B S hS Y ⟶ G⟦i⟧) := by
  have := hG
  have : (G⟦i⟧).IsGE (-i) := DerivedCategory.TStructure.t.isGE_shift G 0 i (-i)
  have : (G⟦i⟧).IsGE 1 := DerivedCategory.TStructure.t.isGE_of_ge _ 1 (-i) (by omega)
  exact ⟨fun a b => (DerivedCategory.TStructure.t.zero a 0 1).trans
    (DerivedCategory.TStructure.t.zero b 0 1).symm⟩

/-- **`Rf_{V*} R𝓗om(K_V, E_V)` on an étale neighbourhood with quasi-compact and quasi-separated
source.**  Granted Stacks 0DKY (`h0DKY`, not yet proved here), in the situation of Stacks 0DLC
with the negative fibre extensions vanishing at every point of `Y` with values in a field, let `V`
be an algebraic space over `Y` and `c : T ⟶ V` étale, with `T` quasi-compact and quasi-separated
and `T ⟶ Y` representable.  Then `Lc^* Rf_{V*} R𝓗om(K_V, E_V)` has no cohomology in negative
degrees.

By Stacks 08GE and 08JB it is `Rf_{T*} R𝓗om(K_T, E_T)` for the base change `f_T : X_T ⟶ T`; that
is `R𝓗om(L, 𝒪_T)` by Stacks 0DKY over `T`, and `L ≤ 0` by
`AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE`, the field points of `T` being field points
of `Y`. -/
theorem isGE_pull_pushforwardSheafHom_of_dualExists (h0DKY : RelativeDerivedHomDualExists B S hS)
    (f : X ⟶ Y) (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀)
    (V : Over Y) {T : AlgebraicSpaces B S hS} (c : T ⟶ V.left) (hc : IsEtale B S hS c.hom)
    (hqc : IsQuasiCompactSpace B S hS T.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal T.1)
    (hrep : yoneda.relativelyRepresentable (c ≫ V.hom).hom) :
    (((smallEtaleDerivedPullbackData B S hS).pull c).obj
      ((spaceDerivedPushforward B S hS (overInclusion f V)).obj
        (((smallEtaleDerivedSheafHom B S hS (overBaseChange f V)).obj (Opposite.op
          (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K))).obj
          (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)))).IsGE 0 := by
  let P := smallEtaleDerivedPullbackData B S hS
  let fV := overInclusion f V
  let pV := overProjection f V
  have hsqV : IsPullback pV fV f V.hom := AlgebraicSpaces.isPullback_fiberProduct B S hS f V.hom
  let C : Over V.left := Over.mk c
  let i := overProjection fV C
  let f' := overInclusion fV C
  have sq : IsPullback i f' fV c := AlgebraicSpaces.isPullback_fiberProduct B S hS fV c
  have hpaste : IsPullback (i ≫ pV) f' f (c ≫ V.hom) := sq.paste_horiz hsqV
  have hi : IsEtale B S hS i.hom := isEtale_of_isPullback B S hS f' i c fV sq.flip hc
  have hp' : IsProper B S hS f'.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback hpaste hp
  have hflat' : IsFlat B S hS f'.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hpaste hflat
  have hfp' : IsFinitePresentation B S hS f'.hom :=
    (isFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hpaste hfp
  have hrep' : yoneda.relativelyRepresentable (i ≫ pV).hom :=
    (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS hpaste).flip hrep
  have hK' := isPseudoCoherent_smallEtaleDerivedModulePullback_of_representable B S hS (i ≫ pV)
    hrep' K hK
  have hE' :=
    isPerfectRelativeToCanonical_pull_of_isPullback hpaste hrep' hflat' hfp'.1 hflat hfp.1 E hE
  obtain ⟨L, hL, ⟨e⟩, hbc⟩ := h0DKY B.contains_terminal f' hqc hqs hp' hflat' hfp' _ _ hE' hK'
  have hL0 : L.IsLE 0 := fieldFibreDualVanishingIsLE B S hS T L hL fun T₀ hT₀ =>
    (hasNoNegativeExtAt_iff_of_dual f' _ _ L T₀
      (hbc _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f' T₀.hom)).some).1
      ((hasNoNegativeExtAt_pull_iff_of_isPullback hpaste K E T₀).2 (hfib _ hT₀))
  let D : derivedModules B S hS C.left := smallEtaleDerivedDual B S hS C.left L
  have : D.IsGE 0 := isGE_smallEtaleDerivedDual B S hS T L hL0
  let H := (smallEtaleDerivedSheafHom B S hS (overBaseChange fV C))
  refine DerivedCategory.TStructure.t.isGE_of_iso (X := D) (e.symm ≪≫
    (spaceDerivedPushforward B S hS f').mapIso
      ((H.mapIso ((P.compIso i pV).app K).op).app _ ≪≫
        (H.obj _).mapIso ((P.compIso i pV).app E).symm).symm ≪≫
    (spaceDerivedPushforward B S hS f').mapIso
      (smallEtaleDerivedSheafHomEtaleRestrictionIso B S hS i hi _ _).symm ≪≫
    ((spaceDerivedPushforwardPullBaseChangeIso B S hS sq hc).app _).symm) 0

/-- **`Rf_{V*} R𝓗om(K_V, E_V)` has no cohomology in negative degrees**, for every algebraic space
`V` over `Y`, granted Stacks 0DKY (`h0DKY`, not yet proved here), in the situation of
Stacks 0DLC with the negative fibre extensions vanishing at every point of `Y` with values in a
field.  The question is étale local on `V`, and on an affine étale chart of `V` it is
`AlgebraicGeometry.Space.isGE_pull_pushforwardSheafHom_of_dualExists`: an affine chart is
quasi-compact and quasi-separated, and its morphism to `Y`, from a scheme to an algebraic space,
is representable. -/
theorem isGE_pushforwardSheafHom_of_dualExists (h0DKY : RelativeDerivedHomDualExists B S hS)
    (f : X ⟶ Y) (hp : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀)
    (V : Over Y) :
    ((spaceDerivedPushforward B S hS (overInclusion f V)).obj
      (((smallEtaleDerivedSheafHom B S hS (overBaseChange f V)).obj (Opposite.op
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K))).obj
        (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E))).IsGE 0 :=
  isGE_of_isGE_smallEtaleDerivedModulePullback_chartToSpace B S hS
    (SmallEtale.coversTop_affineCharts B S hS V.left.1) _ 0 fun ⟨U, hU⟩ =>
      isGE_pull_pushforwardSheafHom_of_dualExists h0DKY f hp hflat hfp K E hK hE hfib V
        (chartToSpace B S hS V.left U) (isEtale_chartToSpace B S hS V.left U)
        (isQuasiCompactSpace_yoneda_of_isAffine B S hS _ hU)
        (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS B.contains_terminal
          (isAffineSpace_yoneda B S hS _ hU))
        (relativelyRepresentable_of_isAlgebraicSpace B S hS Y.2 _)

end Local

/-! ### Stacks 0DLC, part (2), in the case `W = Y` -/

variable (B S hS) in
/-- **Stacks 0DLC, part (2), in the case `W = Y`, over a general base, granted Stacks 0DKY.**  The
hypothesis `h0DKY` is Stacks 0DKY, not yet proved here.  For a proper, flat, finitely
presented `f : X ⟶ Y`, a pseudo-coherent `K` and a `Y`-perfect `E` whose negative fibre extensions
vanish at every point with values in a field, `Ext^i_{𝒪_{X_V}}(K_V, E_V) = 0` for `i < 0` and
every algebraic space `V` over `Y`.

By Stacks 08JA and the Leray identity, `Ext^i(K_V, E_V) = H^i(V, Rf_{V*} R𝓗om(K_V, E_V))`, which
vanishes for `i < 0` since `Rf_{V*} R𝓗om(K_V, E_V)` has no cohomology in negative degrees
(`AlgebraicGeometry.Space.isGE_pushforwardSheafHom_of_dualExists`). -/
theorem negativeExtVanishesOfFibres_of_dualExists (h0DKY : RelativeDerivedHomDualExists B S hS) :
    NegativeExtVanishesOfFibres B S hS := by
  intro X Y f hp hflat hfp K E hK hE hfib V i hi
  exact ((homShiftEquivStructureHomSheafHom B S hS _ _ i).trans
    (structureHomShiftEquivPushforward B S hS (overInclusion f V) _ i)).subsingleton_congr.2
    (subsingleton_structureObject_hom_shift_of_isGE _
      (isGE_pushforwardSheafHom_of_dualExists h0DKY f hp hflat hfp K E hK hE hfib V) i hi)

/-! ### Part (3) in the case `W = Y`, with part (2) discharged -/

variable (B S hS) in
/-- **Stacks 0DLC, part (3), in the case `W = Y`**, from Stacks 0DKY (`h0DKY`, not yet proved here),
Stacks 0DL9 (`h0DL9`, pending) and the internal steps (S) and (L) (`hS'`, `hL`): the
assembly `AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_steps` with its
part (2) input discharged by
`AlgebraicGeometry.Space.negativeExtVanishesOfFibres_of_dualExists`. -/
theorem relativeDerivedHomRepresentableOfFibres_of_dualExists_of_steps
    (h0DKY : RelativeDerivedHomDualExistsNaturalCompatible B S hS)
    (h0DL9 : DerivedHomHypercoveringDescent B S hS)
    (hS' : RelativeDerivedHomIsSheafOfDescent B S hS)
    (hL : RelHomStructureRepresentableOfIsLE B S hS) :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_steps
    (negativeExtVanishesOfFibres_of_dualExists B S hS h0DKY.relativeDerivedHomDualExists)
    h0DKY h0DL9 hS' hL

end AlgebraicGeometry.Space

end
