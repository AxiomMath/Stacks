module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesNegativeSelfExt
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusGeneralBase
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomReduction
public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusOpen
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomDualHeldInputs
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeDerivedHomZariskiGluing
public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectBaseChangeStableProof
public import StacksFrontier.AlgebraicGeometry.Quot.RelativelyPerfectDirectImageHeld
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RepresentedHomotopyPullbackCoherenceConsequences

/-!
# Stacks 0DKX, 0DKY, 0DLC and 0DLD with no pending input

Stacks 0DKW is proved on this branch with no pending input
(`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_proved`). It was the
last input of the proofs of Stacks 0DKX, 0DKY and 0DLC on this branch
(`AlgebraicGeometry.Space.relativelyPerfectPushforwardBaseChange_of_relativelyPerfectColimit`,
`relativeDerivedHomDualExistsNaturalCompatible_of_relativelyPerfectPushforwardBaseChange`,
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_pushforwardBaseChange`), and
through Stacks 0DLC of parts (b) and (c) of Stacks 0DLD. This file records these statements with
that input discharged.

## Main results

* `AlgebraicGeometry.Space.relativelyPerfectColimitHolds_proved`: Stacks 0DKW in the form the
  proof of Stacks 0DKX consumes.
* `AlgebraicGeometry.Space.isPerfect_derivedPushforward_and_isIso_baseChange`: **Stacks 0DKX**.
* `AlgebraicGeometry.Space.exists_isPseudoCoherent_pushforward_sheafHom_iso_dual`:
  **Stacks 0DKY**.
* `AlgebraicGeometry.Space.exists_negativeExtLocus_and_vanishing_and_representable`:
  **Stacks 0DLC**, parts (1), (2) and (3).
* `AlgebraicGeometry.Space.ComplexesSituation.conditions_negativeSelfExt_selfHom_overBaseChange`:
  **Stacks 0DLD**, parts (a), (b) and (c).
* the propositions of the consumers: `relativelyPerfectPushforwardBaseChange_proved`,
  `relativeDerivedHomDualExistsNaturalCompatible_proved` (and its objectwise and natural forms),
  `existsNegativeExtLocus_proved`, `negativeExtVanishesOfFibres_proved`,
  `negativeExtVanishesOverLocus_proved`, `relativeDerivedHomRepresentableOfFibres_proved` and
  `relativeDerivedHomRepresentableOverLocus_proved`.

## References

* [Stacks Project, Tag 0DKX](https://stacks.math.columbia.edu/tag/0DKX)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0DLC](https://stacks.math.columbia.edu/tag/0DLC)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

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

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 0DKX -/

/-- **Stacks 0DKW**, in the form `AlgebraicGeometry.Space.RelativelyPerfectColimitHolds` that the
proof of Stacks 0DKX consumes: every Situation 0DKU over `S` indexed by a directed preorder in
`Type u` satisfies the conclusion of Stacks 0DKW
(`AlgebraicGeometry.Space.RelativeDescentSituation.relativelyPerfectColimit_proved`). -/
theorem relativelyPerfectColimitHolds_proved : RelativelyPerfectColimitHolds B S hS :=
  fun _ _ _ _ D => D.relativelyPerfectColimit_proved

/-- **The 0DKX input of the proof of Stacks 0DKY**,
`AlgebraicGeometry.Space.RelativelyPerfectPushforwardBaseChange`, with no pending input:
`AlgebraicGeometry.Space.relativelyPerfectPushforwardBaseChange_of_relativelyPerfectColimit`
with Stacks 0DKW discharged. -/
theorem relativelyPerfectPushforwardBaseChange_proved :
    RelativelyPerfectPushforwardBaseChange B S hS :=
  relativelyPerfectPushforwardBaseChange_of_relativelyPerfectColimit B S hS
    fun hT => relativelyPerfectColimitHolds_proved B _ hT

/-- **Stacks 0DKX.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is flat,
proper and of finite presentation, and let `E ∈ D(𝒪_X)` be `Y`-perfect (Stacks 0DKN). Then
`Rf_*E` is a perfect object of `D(𝒪_Y)`, and its formation commutes with arbitrary base change:
for every cartesian square
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
the base change map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` (Stacks 07A7) is an isomorphism. -/
@[stacks 0DKX]
theorem isPerfect_derivedPushforward_and_isIso_baseChange
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (E : derivedModules B S hS X) (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
        (hpb : IsPullback g' f' f g),
        IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E) :=
  relativelyPerfectPushforwardBaseChange_proved B S hS f hproper hflat hfp E hE

/-! ### Stacks 0DKY -/

/-- **Stacks 0DKY, in its natural and compatible form**,
`AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNaturalCompatible`, with no pending input:
`relativeDerivedHomDualExistsNaturalCompatible_of_relativelyPerfectPushforwardBaseChange` with
Stacks 0DKX discharged. -/
theorem relativeDerivedHomDualExistsNaturalCompatible_proved :
    RelativeDerivedHomDualExistsNaturalCompatible B S hS :=
  relativeDerivedHomDualExistsNaturalCompatible_of_relativelyPerfectPushforwardBaseChange B S hS
    (relativelyPerfectPushforwardBaseChange_proved B S hS)

/-- **Stacks 0DKY, objectwise**, `AlgebraicGeometry.Space.RelativeDerivedHomDualExists`, with no
pending input. -/
theorem relativeDerivedHomDualExists_proved : RelativeDerivedHomDualExists B S hS :=
  (relativeDerivedHomDualExistsNaturalCompatible_proved B S hS).relativeDerivedHomDualExists

/-- **Stacks 0DKY, natural in the base change**,
`AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNatural`, with no pending input. -/
theorem relativeDerivedHomDualExistsNatural_proved : RelativeDerivedHomDualExistsNatural B S hS :=
  (relativeDerivedHomDualExistsNaturalCompatible_proved B S hS).relativeDerivedHomDualExistsNatural

/-- **Stacks 0DKY.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, and let `E`, `K`
be objects of `D(𝒪_X)`. Assume that `Y` is quasi-compact and quasi-separated, that `f` is proper,
flat and of finite presentation, that `E` is `Y`-perfect (Stacks 0DKN) and that `K` is
pseudo-coherent. Then there is a pseudo-coherent `L ∈ D(𝒪_Y)` with
`Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_Y)`, and the same holds after arbitrary base change: for every
cartesian square `X' = X ×_Y Y'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`,
`Rf'_* R𝓗om(L(g')^*K, L(g')^*E) ≅ R𝓗om(Lg^*L, 𝒪_{Y'})`.

(`hZ` says that the site contains `Spec ℤ`, through which quasi-separatedness of `Y` is
expressed.) -/
@[stacks 0DKY]
theorem exists_isPseudoCoherent_pushforward_sheafHom_iso_dual
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hqc : IsQuasiCompactSpace B S hS Y.1) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
    (hproper : IsProper B S hS f.hom) (hflat : IsFlat B S hS f.hom)
    (hfp : IsFinitePresentation B S hS f.hom) (K E : derivedModules B S hS X)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E)
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K) :
    ∃ L : derivedModules B S hS Y, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPseudoCoherent L ∧
      Nonempty ((spaceDerivedPushforward B S hS f).obj
          (((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op K)).obj E) ≅
        smallEtaleDerivedDual B S hS Y L) ∧
      ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
        IsPullback g' f' f g →
        Nonempty ((spaceDerivedPushforward B S hS f').obj
            (((smallEtaleDerivedSheafHom B S hS X').obj
              (Opposite.op (((smallEtaleDerivedPullbackData B S hS).pull g').obj K))).obj
                (((smallEtaleDerivedPullbackData B S hS).pull g').obj E)) ≅
          smallEtaleDerivedDual B S hS Y'
            (((smallEtaleDerivedPullbackData B S hS).pull g).obj L)) :=
  relativeDerivedHomDualExists_proved B S hS hZ f hqc hqs hproper hflat hfp K E hE hK

/-! ### Stacks 0DLC -/

/-- **Stacks 0DLC, part (1)**, `AlgebraicGeometry.Space.ExistsNegativeExtLocus`, with no pending
input. -/
theorem existsNegativeExtLocus_proved : ExistsNegativeExtLocus B S hS :=
  existsNegativeExtLocus_of_dualExists B S hS (relativeDerivedHomDualExists_proved B S hS)

/-- **Stacks 0DLC, part (2), in the case `W = Y`**,
`AlgebraicGeometry.Space.NegativeExtVanishesOfFibres`, with no pending input. -/
theorem negativeExtVanishesOfFibres_proved : NegativeExtVanishesOfFibres B S hS :=
  negativeExtVanishesOfFibres_of_dualExists B S hS (relativeDerivedHomDualExists_proved B S hS)

/-- **Stacks 0DLC, part (2)**, `AlgebraicGeometry.Space.NegativeExtVanishesOverLocus`, with no
pending input. -/
theorem negativeExtVanishesOverLocus_proved : NegativeExtVanishesOverLocus B S hS :=
  NegativeExtVanishesOfFibres.negativeExtVanishesOverLocus
    (negativeExtVanishesOfFibres_proved B S hS)

/-- **Stacks 0DLC, part (3), in the case `W = Y`**,
`AlgebraicGeometry.Space.RelativeDerivedHomRepresentableOfFibres`, with no pending input:
`AlgebraicGeometry.Space.relativeDerivedHomRepresentableOfFibres_of_pushforwardBaseChange` with
Stacks 0DKX discharged. -/
theorem relativeDerivedHomRepresentableOfFibres_proved :
    RelativeDerivedHomRepresentableOfFibres B S hS :=
  relativeDerivedHomRepresentableOfFibres_of_pushforwardBaseChange
    (relativelyPerfectPushforwardBaseChange_proved B S hS)

/-- **Stacks 0DLC, part (3)**, `AlgebraicGeometry.Space.RelativeDerivedHomRepresentableOverLocus`,
with no pending input. -/
theorem relativeDerivedHomRepresentableOverLocus_proved :
    RelativeDerivedHomRepresentableOverLocus B S hS :=
  RelativeDerivedHomRepresentableOfFibres.relativeDerivedHomRepresentableOverLocus
    (relativeDerivedHomRepresentableOfFibres_proved B S hS)

/-- **Stacks 0DLC.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is proper,
flat and of finite presentation, and let `K`, `E ∈ D(𝒪_X)` with `K` pseudo-coherent and `E`
`Y`-perfect (Stacks 0DKN). For a point `y : Spec(k) ⟶ Y` with values in a field write `K_y`, `E_y`
for the pullbacks to the fibre `X_y`.
1. There is an open `W ⊆ Y` characterized by: `y ∈ |W|` if and only if
   `Ext^i_{𝒪_{X_y}}(K_y, E_y) = 0` for `i < 0`
   (`AlgebraicGeometry.Space.IsNegativeExtLocus`).
2. For such a `W` and every algebraic space `V` over `Y` whose morphism to `Y` factors through `W`,
   `Ext^i_{𝒪_{X_V}}(K_V, E_V) = 0` for `i < 0`, where `X_V` is the base change of `X` and `K_V`,
   `E_V` are the derived pullbacks of `K` and `E` to `X_V`.
3. For such a `W`, the functor `V ↦ Hom_{𝒪_{X_V}}(K_V, E_V)` on the schemes over `W` is
   representable by an algebraic space affine and of finite presentation over `W` (in particular
   it is a sheaf). -/
@[stacks 0DLC]
theorem exists_negativeExtLocus_and_vanishing_and_representable
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hproper : IsProper B S hS f.hom)
    (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
    (K E : derivedModules B S hS X) (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K)
    (hE : IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E) :
    (∃ W : OpenSubspaces B S hS Y.1, IsNegativeExtLocus f K E W) ∧
      (∀ W : OpenSubspaces B S hS Y.1, IsNegativeExtLocus f K E W →
        ∀ V : Over Y, (∃ g : V.left ⟶ openSubspaceAsSpace B S hS W,
            g ≫ openSubspaceImmersion B S hS W = V.hom) →
        ∀ i : ℤ, i < 0 →
          Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj K ⟶
            (((smallEtaleDerivedPullbackData B S hS).pull (overProjection f V)).obj E)⟦i⟧)) ∧
      (∀ W : OpenSubspaces B S hS Y.1, IsNegativeExtLocus f K E W →
        IsAffineFinitePresentationAlgebraicSpaceOver (openSubspaceAsSpace B S hS W)
          (relativeDerivedHomOverOpen f K E W)) :=
  ⟨existsNegativeExtLocus_proved B S hS f hproper hflat hfp K E hK hE,
    negativeExtVanishesOverLocus_proved B S hS f hproper hflat hfp K E hK hE,
    relativeDerivedHomRepresentableOverLocus_proved B S hS f hproper hflat hfp K E hK hE⟩

/-! ### Stacks 0DLD -/

namespace ComplexesSituation

variable {B S hS} (D : ComplexesSituation B S hS)

/-- **Stacks 0DLD.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is proper,
flat and of finite presentation, and let `E ∈ D(𝒪_X)`. Assume that `E` is `Y`-perfect
(Stacks 0DKN) and that `Ext^i_{𝒪_{X_y}}(E_y, E_y) = 0` for `i < 0` at every point
`y : Spec(k) ⟶ Y` with values in a field, `E_y` the derived pullback to the fibre `X_y`. Then
* (a) both conditions hold for `X_V ⟶ V` and `E_V` after every base change `V ⟶ Y`;
* (b) `Ext^i_{𝒪_{X_V}}(E_V, E_V) = 0` for `i < 0` and every algebraic space `V` over `Y`;
* (c) `V ↦ Hom_{𝒪_{X_V}}(E_V, E_V)` is representable by an algebraic space affine and of finite
  presentation over `Y`.
Here `X_V` is the base change of `X` and `E_V` the derived pullback of `E` to `X_V`. -/
@[stacks 0DLD]
theorem conditions_negativeSelfExt_selfHom_overBaseChange (E : derivedModules B S hS D.X)
    (h1 : IsPerfectRelativeToCanonical B S hS D.f D.flat D.finitePresentation.1 E)
    (h2 : HasNoNegativeFieldFibreExt D.f E) :
    (∀ V : Over D.Y,
      IsPerfectRelativeToCanonical B S hS (overInclusion D.f V) (D.overInclusion_isFlat V)
          (D.overInclusion_isLocallyOfFinitePresentation V)
          (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E) ∧
        HasNoNegativeFieldFibreExt (overInclusion D.f V)
          (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E)) ∧
      (∀ (V : Over D.Y) (i : ℤ), i < 0 →
        Subsingleton
          (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E ⟶
            (((smallEtaleDerivedPullbackData B S hS).pull (overProjection D.f V)).obj E)⟦i⟧)) ∧
      IsAffineFinitePresentationAlgebraicSpaceOver D.Y (relativeDerivedHom D.f E E) :=
  ⟨D.conditions_overBaseChange E h1 h2,
    D.subsingleton_hom_shift_overBaseChange_of (negativeExtVanishesOfFibres_proved B S hS) E h1 h2,
    D.relativeDerivedHom_self_isAffineFinitePresentation_of
      (relativeDerivedHomRepresentableOfFibres_proved B S hS) E h1 h2⟩

end ComplexesSituation

end AlgebraicGeometry.Space

end
