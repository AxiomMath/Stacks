module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackThickeningPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.Thickening

/-!
# Stacks 0DL4 with Stacks 0DL3 discharged

`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackThickeningPerfect.lean` proves Stacks 0DL4 from
Stacks 0DL3, carried there as the hypothesis `h0DL3` (pseudo-coherence ascends along a morphism
all of whose base changes to schemes are `n`th-order thickenings). Stacks 0DL3 is registered
on the base, for the inclusion of a closed subspace which is a finite-order thickening:
`AlgebraicGeometry.Space.isPseudoCoherent_of_derivedPullback_of_isFiniteOrderThickening`. This
file reads `h0DL3` off it and records Stacks 0DL4 without it.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_of_pull_of_presheaf_thickOrder`: pseudo-coherence
  ascends along a morphism whose base changes to schemes are `n`th-order thickenings.
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_pull_of_isThickeningHom`: relative
  perfection ascends along a finite-order thickening of the base.
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening_proved`:
  the same, with the thickening in the form of the scheme base changes.
* `ComplexesSituation.isRelativelyPerfect_of_isFiniteOrderThickening_proved`: relative perfection
  ascends along a finite-order thickening of test schemes in the situation of Stacks 0DLE.

## References

* [Stacks Project, Tag 0DL4](https://stacks.math.columbia.edu/tag/0DL4)
* [Stacks Project, Tag 0DL3](https://stacks.math.columbia.edu/tag/0DL3)
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

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0DL3, for a morphism whose base changes to schemes are `n`th-order thickenings**
(the hypothesis `h0DL3` of
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening`). Such
a morphism `i : X ⟶ X'` is an isomorphism onto its range, which is an `n`th-order thickening of
`X'` (`AlgebraicGeometry.Space.presheaf_thickOrder_iff_isThickeningHom_and_isNthOrderThickening`);
the base's Stacks 0DL3
(`AlgebraicGeometry.Space.isPseudoCoherent_of_derivedPullback_of_isFiniteOrderThickening`) applies
to the inclusion of the range, and `Li^*K'` is the derived pullback of `K'` to the range followed
by the derived pullback along the isomorphism `X ≅ range i`, which preserves pseudo-coherence in
both directions (Stacks 08H4). -/
theorem isPseudoCoherent_of_pull_of_presheaf_thickOrder {X X' : AlgebraicSpaces B S hS}
    (i : X ⟶ X') (n : ℕ)
    (hi : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf i.hom)
    (K' : derivedModules B S hS X')
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
      (((smallEtaleDerivedPullbackData B S hS).pull i).obj K')) :
    (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherent K' := by
  obtain ⟨hth, hn⟩ :=
    (presheaf_thickOrder_iff_isThickeningHom_and_isNthOrderThickening B S hS i n).1 hi
  have := hth.1
  let Z : ClosedSubspaces B S hS X'.1 := ⟨Subfunctor.range i.hom, hn.1.1⟩
  let ψ : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X :=
    ObjectProperty.homMk (inv (Subfunctor.toRange i.hom))
  have hψ : ψ ≫ i = subspaceInclusion B S hS X' Z :=
    ObjectProperty.hom_ext _ (by
      change inv (Subfunctor.toRange i.hom) ≫ i.hom = (Subfunctor.range i.hom).ι
      exact (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι i.hom).symm)
  refine isPseudoCoherent_of_derivedPullback_of_isFiniteOrderThickening B S hS Z ⟨n, hn⟩ K' ?_
  obtain ⟨M, hM, ⟨eM⟩⟩ := isPseudoCoherent_smallEtaleDerivedModulePullback ψ _ hK
  exact ⟨M, hM, ⟨eM ≪≫ (((smallEtaleDerivedPullbackData B S hS).compIso ψ i).app K').symm ≪≫
    eqToIso (by rw [hψ]; rfl)⟩⟩

/-- **Stacks 0DL4, with the thickening in the form of its scheme base changes**:
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening` with
Stacks 0DL3 discharged by
`AlgebraicGeometry.Space.isPseudoCoherent_of_pull_of_presheaf_thickOrder`. -/
theorem isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening_proved
    {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    (hpb : IsPullback i f f' j) {n : ℕ}
    (hj : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf j.hom)
    (hflat : IsFlat B S hS f'.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f'.hom)
    (E' : derivedModules B S hS X')
    (hE : IsPerfectRelativeToCanonical B S hS f
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb hflat)
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hpb
        hlfp)
      (((smallEtaleDerivedPullbackData B S hS).pull i).obj E')) :
    IsPerfectRelativeToCanonical B S hS f' hflat hlfp E' :=
  isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening
    isPseudoCoherent_of_pull_of_presheaf_thickOrder hpb hj hflat hlfp E' hE

/-- Consider a cartesian square
```
X --i--> X'
|f       |f'
v        v
Y --j--> Y'
```
of algebraic spaces over `S`. Assume `f'` is flat and locally of finite presentation and `j` is
a finite-order thickening: `j` is an isomorphism onto its range, which is a finite-order
thickening of `Y'` (Stacks 05ZK). Let `E' ∈ D(𝒪_{X'})`. If `E = Li^*E'` is `Y`-perfect
(Stacks 0DKN), then `E'` is `Y'`-perfect. -/
@[stacks 0DL4]
theorem isPerfectRelativeToCanonical_of_pull_of_isThickeningHom
    {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    (hpb : IsPullback i f f' j) (hj : IsThickeningHom B S hS j)
    (hjfin : IsFiniteOrderThickening B S hS Y' (Subfunctor.range j.hom))
    (hflat : IsFlat B S hS f'.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f'.hom)
    (E' : derivedModules B S hS X')
    (hE : IsPerfectRelativeToCanonical B S hS f
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb hflat)
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hpb
        hlfp)
      (((smallEtaleDerivedPullbackData B S hS).pull i).obj E')) :
    IsPerfectRelativeToCanonical B S hS f' hflat hlfp E' := by
  obtain ⟨n, hn⟩ :=
    (exists_presheaf_thickOrder_iff_isThickeningHom_and_isFiniteOrderThickening B S hS j).2
      ⟨hj, hjfin⟩
  exact isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening_proved hpb hn hflat hlfp
    E' hE

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-- **Stacks 0DL4 in the situation of Stacks 0DLE**: for a finite-order thickening `T ⟶ T'` of
test schemes over `Y`, an object `E'` of `D(𝒪_{X_{T'}})` whose derived restriction to `X_T` is
isomorphic to a `T`-perfect object is `T'`-perfect. This is
`AlgebraicGeometry.Space.ComplexesSituation.isRelativelyPerfect_of_isFiniteOrderThickening` with
Stacks 0DL3 discharged. -/
theorem isRelativelyPerfect_of_isFiniteOrderThickening_proved
    {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (hfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
    (E' : derivedModules B S hS (D.space T')) (E : derivedModules B S hS (D.space T))
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E' ≅ E)
    (hE : D.IsRelativelyPerfect T E) : D.IsRelativelyPerfect T' E' :=
  D.isRelativelyPerfect_of_isFiniteOrderThickening
    isPseudoCoherent_of_pull_of_presheaf_thickOrder h hfin E' E e hE

end ComplexesSituation

end AlgebraicGeometry.Space

end
