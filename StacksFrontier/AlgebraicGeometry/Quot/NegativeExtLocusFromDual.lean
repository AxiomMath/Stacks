module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedExtLeray

/-!
# Stacks 0DLC, part (2), over a quasi-compact and quasi-separated base, from Stacks 0DKY

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces, `K` a
pseudo-coherent and `E` a `Y`-perfect object of `D(𝒪_X)`, and assume the negative fibre
extensions `Ext^i(K_y, E_y)`, `i < 0`, vanish at every point `y` of `Y` with values in a field
(the case `W = Y` of Stacks 0DLC, part (2), to which the source reduces it).  The source proves
`Ext^i(K_V, E_V) = 0` for `i < 0` and every algebraic space `V` over `Y` as follows: Stacks 0DKY
gives a pseudo-coherent `L` on `Y` with `Rf'_* R𝓗om(K_V, E_V) ≅ R𝓗om(L_V, 𝒪_V)` after every base
change; by Stacks 08JA and 0D6H, `Ext^i(K_V, E_V) = Ext^i(L_V, 𝒪_V)`; at the points with values
in a field this says that the negative extensions of `L_y` into the structure sheaf vanish, so
`L` has no cohomology in positive degrees (Stacks 0BCC, "from fibres to stalks"); and then
neither has `L_V`, so `Ext^i(L_V, 𝒪_V) = 0` for `i < 0`.

This file carries that argument out when `Y` is quasi-compact and quasi-separated, the generality
at which `AlgebraicGeometry.Space.RelativeDerivedHomDualExists` (the content of Stacks 0DKY) is
stated, with the identifications of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleDerivedExtLeray.lean`.
The step from fibres to stalks is carried as the explicit hypothesis
`AlgebraicGeometry.Space.FieldFibreDualVanishingIsLE`.  Nothing is registered.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNatural`: the content of Stacks 0DKY in
  degree zero, natural in the test scheme, the form part (3) of Stacks 0DLC consumes.
* `AlgebraicGeometry.Space.FieldFibreDualVanishingIsLE`: the fibre-to-stalk step of the proof
  of Stacks 0DLC: a pseudo-coherent object of `D(𝒪_Y)` whose negative extensions into the
  structure sheaf vanish at every point with values in a field has no cohomology in positive
  degrees.

## Main results

* `AlgebraicGeometry.Space.hasNoNegativeExtAt_iff_of_dual`: at a test scheme over `Y`, the
  negative extensions of `K` and `E` vanish exactly when those of the pullback of `L` into the
  structure sheaf do.
* `AlgebraicGeometry.Space.negativeExtVanishesOfFibres_of_quasiCompact_of_quasiSeparated`:
  Stacks 0DLC, part (2), in the case `W = Y`, for `Y` quasi-compact and quasi-separated, granted
  Stacks 0DKY and the fibre-to-stalk step.

## Elsewhere

* The case of a general `Y`, worked étale locally on `V` as in the source, granted Stacks 0DKY
  alone: `AlgebraicGeometry.Space.negativeExtVanishesOfFibres_of_dualExists`
  (`StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocusGeneralBase.lean`).
* The fibre-to-stalk step `AlgebraicGeometry.Space.FieldFibreDualVanishingIsLE` is proved as
  `AlgebraicGeometry.Space.fieldFibreDualVanishingIsLE`
  (`StacksFrontier/AlgebraicGeometry/Spaces/FieldFibreDualVanishing.lean`).
* Part (1), the openness of the locus, granted Stacks 0DKY:
  `AlgebraicGeometry.Space.existsNegativeExtLocus_of_dualExists`
  (`StacksFrontier/AlgebraicGeometry/Quot/NegativeExtLocusOpen.lean`).

## References

* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0BCC](https://stacks.math.columbia.edu/tag/0BCC)
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

variable (B S hS) in
/-- **The fibre-to-stalk step of the proof of Stacks 0DLC**, as a proposition: a pseudo-coherent
object `L` of `D(𝒪_Y)` such that `Ext^i(L_y, 𝒪_y) = 0` for all `i < 0` at every point
`y : Spec(k) ⟶ Y` with values in a field has no cohomology in positive degrees.  In the source
this is Stacks 0BCC applied at the local rings, after identifying the negative extensions of
`L ⊗^L κ(y)` into `κ(y)` with the duals of its positive cohomology. -/
def FieldFibreDualVanishingIsLE : Prop :=
  ∀ (Y : AlgebraicSpaces B S hS) (L : derivedModules B S hS Y),
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L →
    (∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → ∀ i : ℤ, i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).obj L ⟶
        (structureObject B S hS ((schemeSpaceFunctor B S hS).obj T₀.left))⟦i⟧)) →
    L.IsLE 0

variable {X Y : AlgebraicSpaces B S hS}

/-- **Fibre extensions through the dual.**  If the base change of `f` to a test scheme `T₀` over
`Y` carries `Rf'_* R𝓗om(K_{T₀}, E_{T₀}) ≅ R𝓗om(L_{T₀}, 𝒪_{T₀})`, then the negative extensions of
`K_{T₀}` and `E_{T₀}` vanish exactly when those of `L_{T₀}` into `𝒪_{T₀}` do. -/
theorem hasNoNegativeExtAt_iff_of_dual (f : X ⟶ Y) (K E : derivedModules B S hS X)
    (L : derivedModules B S hS Y) (T₀ : SchemesOver Y)
    (e : (spaceDerivedPushforward B S hS (baseChangeInclusion f T₀)).obj
        (((smallEtaleDerivedSheafHom B S hS _).obj
          (Opposite.op (((smallEtaleDerivedPullbackData B S hS).pull
            (baseChangeProjection f T₀)).obj K))).obj
          (((smallEtaleDerivedPullbackData B S hS).pull (baseChangeProjection f T₀)).obj E)) ≅
      smallEtaleDerivedDual B S hS _ (((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).obj L)) :
    HasNoNegativeExtAt f K E T₀ ↔ ∀ i : ℤ, i < 0 →
      Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).obj L ⟶
        (structureObject B S hS ((schemeSpaceFunctor B S hS).obj T₀.left))⟦i⟧) :=
  forall₂_congr fun i _ =>
    (homShiftEquivOfPushforwardSheafHomIso B S hS (baseChangeInclusion f T₀) _ _ _ e
      i).subsingleton_congr

/-- **Stacks 0DLC, part (2), in the case `W = Y`, over a quasi-compact and quasi-separated
base**, granted Stacks 0DKY (`h0DKY`) and the fibre-to-stalk step (`hLE`).  For a proper, flat,
finitely presented `f : X ⟶ Y` with `Y` quasi-compact and quasi-separated, a pseudo-coherent `K`
and a `Y`-perfect `E` whose negative fibre extensions vanish at every point with values in a
field, `Ext^i_{𝒪_{X_V}}(K_V, E_V) = 0` for `i < 0` and every algebraic space `V` over `Y`.

The `L` of Stacks 0DKY has no cohomology in positive degrees, by `hLE` applied to the fibre
condition read through `AlgebraicGeometry.Space.hasNoNegativeExtAt_iff_of_dual`; and
`Ext^i(K_V, E_V) = Ext^i(L_V, 𝒪_V)` vanishes for `i < 0` by
`AlgebraicGeometry.Space.subsingleton_pull_hom_structureObject_shift`. -/
theorem negativeExtVanishesOfFibres_of_quasiCompact_of_quasiSeparated
    (h0DKY : RelativeDerivedHomDualExists B S hS) (hLE : FieldFibreDualVanishingIsLE B S hS)
    (hZ : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hqc : IsQuasiCompactSpace B S hS Y.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1) (hp : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (K E : derivedModules B S hS X)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hfib : ∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → HasNoNegativeExtAt f K E T₀)
    (V : Over Y) (i : ℤ) (hi : i < 0) :
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧) := by
  obtain ⟨L, hL, -, hbc⟩ := h0DKY hZ f hqc hqs hp hflat hfp K E hE hK
  have hL0 : L.IsLE 0 := hLE Y L hL fun T₀ hT₀ =>
    (hasNoNegativeExtAt_iff_of_dual f K E L T₀
      (hbc _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f T₀.hom)).some).1 (hfib T₀ hT₀)
  obtain ⟨e⟩ := hbc _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f V.hom)
  exact (homShiftEquivOfPushforwardSheafHomIso B S hS (overInclusion f V) _ _ _ e
    i).subsingleton_congr.2
    (subsingleton_pull_hom_structureObject_shift B S hS V.hom L hL0 i hi)

variable (B S hS) in
/-- **The content of Stacks 0DKY, natural in the base change**, as a proposition, in the form
Stacks 0DLC, part (3), consumes it: for a morphism `f : X ⟶ Y` of algebraic spaces with `Y`
quasi-compact and quasi-separated and `f` proper, flat and of finite presentation, a `Y`-perfect
`E` and a pseudo-coherent `K` in `D(𝒪_X)`, there is a pseudo-coherent `L` in `D(𝒪_Y)` such that the
functor `T ↦ Hom(K_T, E_T)` on the test schemes over `Y` is the functor `T ↦ Hom(L_T, 𝒪_T)`,
naturally in `T`.

Objectwise this is `AlgebraicGeometry.Space.RelativeDerivedHomDualExists` read through
Stacks 08JA and 0D6H (`AlgebraicGeometry.Space.homShiftEquivOfPushforwardSheafHomIso` at
`i = 0`); the naturality in `T` is the compatibility of the isomorphisms of Stacks 0DKY with
further base change, which the source's construction of `L` provides and which
`AlgebraicGeometry.Space.RelativeDerivedHomDualExists` does not record. -/
def RelativeDerivedHomDualExistsNatural : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    IsQuasiCompactSpace B S hS Y.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
    IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      ∃ L : derivedModules B S hS Y, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L ∧
        Nonempty (relativeDerivedHom f K E ≅
          (smallEtaleDerivedPullbackData B S hS).relHomFunctor
            (smallEtaleDerivedPullbackData_isCoherent B S hS) (schemesOverCone Y) L
            (structureObject B S hS Y))

end AlgebraicGeometry.Space

end
