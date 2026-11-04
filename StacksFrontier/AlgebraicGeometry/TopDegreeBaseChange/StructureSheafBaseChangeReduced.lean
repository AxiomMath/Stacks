module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.MorphismExtension
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.StructureDirectImage
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModel
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimensionOneCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreFirstCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FlatNeighbourhoodOfSpecialFibre
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SpecialFibreFiniteness
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SurjectivityAfterBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.VanishingNeighbourhood
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# `𝒪 = f_*𝒪` after base change to a reduced scheme

Let `f : X ⟶ Y` be a proper morphism all of whose fibres have dimension at most one, with
`𝒪_Y = f_*𝒪_X` and `R¹f_*𝒪_X = 0`. For a morphism `g : Y' ⟶ Y` from a reduced scheme such that
the base change `f' : X' ⟶ Y'` is surjective, `𝒪_{Y'} = f'_*𝒪_{X'}`.

The map `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` is surjective by [Stacks, Tag 0E7I], the fibres of `f` having
vanishing first cohomology by [Stacks, Tag 0E7F]. It is injective because a function `s` on an
open `U ⊆ Y'` whose pullback vanishes has empty nonvanishing locus, `f'` being surjective, so `s`
is nilpotent, hence zero, `Y'` being reduced. This is the argument by which the source concludes
`𝒪_{Y_s} = c_*𝒪_{X_s}` for the special fibre of a contraction in the proof of
[Stacks, Tag 0E97].

## Main results

* `injective_app_of_surjective`: pullback of functions along a surjection onto a reduced scheme
  is injective.
* `isIso_unitToPushforwardUnit_pullback_snd` and `isIso_unitToPushforwardObjUnit_of_isPullback`:
  `𝒪_{Y'} = f'_*𝒪_{X'}`.
* `isZero_firstDirectImageStructureSheaf_of_isPullback`: `R¹f'_*𝒪_{X'} = 0` when the fibres of
  `f` have dimension at most one and no `H¹(𝒪)` ([Stacks, Tag 0E7G] globally).
* `isZero_rightDerived_of_isPullback`: `Rⁱf'_*𝒪_{X'} = 0` for `i > 0`.

## References

* [Stacks Project, Tag 0E7I](https://stacks.math.columbia.edu/tag/0E7I)
* [Stacks Project, Tag 0E7F](https://stacks.math.columbia.edu/tag/0E7F)
* [Stacks Project, Tag 0E97](https://stacks.math.columbia.edu/tag/0E97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 2000] HasDerivedCategory.standard

/-- **Pullback of functions along a surjection onto a reduced scheme is injective**: if
`f.app U s = 0` then the nonvanishing locus of `s` has empty preimage, hence is empty. -/
theorem injective_app_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [IsReduced Y]
    (U : Y.Opens) : Function.Injective (f.app U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine eq_zero_of_basicOpen_eq_bot s (le_bot_iff.mp fun y hy => ?_)
  obtain ⟨x, rfl⟩ := f.surjective y
  have hx : x ∈ f ⁻¹ᵁ Y.basicOpen s := hy
  rw [Scheme.preimage_basicOpen, hs, Scheme.basicOpen_zero] at hx
  exact hx

/-- `𝒪_Y ⟶ f_*𝒪_X` is a monomorphism for a surjection onto a reduced scheme. -/
theorem mono_unitToPushforwardUnit_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [IsReduced Y] : Mono (Scheme.Modules.unitToPushforwardUnit f) :=
  mono_of_val_app_injective _ fun U => injective_app_of_surjective f U.unop

/-- **[Stacks, Tag 0E7G], globally after base change.** Let `f : X ⟶ Y` be proper and let
`g' : X' ⟶ X`, `f' : X' ⟶ Y'` be a base change of `f` along `g : Y' ⟶ Y`. If every fibre of `f`
over a point of the image of `g` has dimension at most one and vanishing `H¹(𝒪)`, then
`R¹f'_*𝒪_{X'} = 0`: around each point of `Y'` the vanishing holds over the preimage of the
neighbourhood that [Stacks, Tag 0E7G] provides, and higher direct images commute with restriction
to opens. -/
theorem isZero_firstDirectImageStructureSheaf_of_isPullback {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g)
    (hdim : ∀ y' : Y', topologicalKrullDim (f.fiber (g y')) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hH : ∀ y' : Y', IsZero (firstCohomologyStructureSheaf (f.fiber (g y')))) :
    IsZero (firstDirectImageStructureSheaf f') := by
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y' => ?_
  obtain ⟨V, hyV, -, huniv⟩ :=
    exists_isOpen_isZero_restrict_firstDirectImage_of_isPullback_of_isZero_cohomologyOne_fiber
      f (g y') (hdim y') (hH y')
  let V' : Y'.Opens := g ⁻¹ᵁ V
  have sq' : IsPullback ((f' ⁻¹ᵁ V').ι ≫ g') (f' ∣_ V') f (V'.ι ≫ g) :=
    (isPullback_morphismRestrict f' V').flip.paste_horiz sq
  have hz : IsZero (firstDirectImageStructureSheaf (f' ∣_ V')) := huniv sq' (by
    rintro _ ⟨v, rfl⟩
    exact v.2)
  have hres : IsZero ((Scheme.Modules.restrictFunctor V'.ι).obj
      (firstDirectImageStructureSheaf f')) := by
    refine IsZero.of_iso ?_
      (AlgebraicGeometry.ProjectiveCoherentImage.higherDirectImageRestrictObjIso f' V'
        (SheafOfModules.unit X'.ringCatSheaf) 1).symm
    exact IsZero.of_iso hz (((Scheme.Modules.pushforward (f' ∣_ V')).rightDerivedPlus
      ((1 : ℕ) : ℤ)).mapIso (Scheme.Modules.restrictUnitIso (f' ⁻¹ᵁ V').ι))
  let x : V'.toScheme := ⟨y', hyV⟩
  let S := Scheme.Modules.toPresheaf V'.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
  exact (S.map_isZero hres).of_iso
    ((Scheme.Modules.restrictStalkNatIso V'.ι x).app _).symm

/-- The fibres of `f` have vanishing `H¹(𝒪)` when `R¹f_*𝒪_X = 0` and the fibres have dimension at
most one. -/
private theorem isZero_firstCohomology_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) (y : Y) :
    IsZero (firstCohomologyStructureSheaf (f.fiber y)) :=
  isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage f y (hdim y) hR

/-- **`𝒪_{Y'} = f'_*𝒪_{X'}` after base change to a reduced scheme.** Let `f : X ⟶ Y` be proper
with fibres of dimension at most one, `𝒪_Y = f_*𝒪_X` and `R¹f_*𝒪_X = 0`, and let
`g : Y' ⟶ Y` be a morphism from a reduced scheme such that the base change
`f' = pullback.snd f g` is surjective. Then `𝒪_{Y'} ⟶ f'_*𝒪_{X'}` is an isomorphism. -/
theorem isIso_unitToPushforwardUnit_pullback_snd {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f))
    (h0 : Epi (Scheme.Modules.unitToPushforwardUnit f))
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsReduced Y'] [Surjective (pullback.snd f g)] :
    IsIso (Scheme.Modules.unitToPushforwardUnit (pullback.snd f g)) := by
  have := epi_unitToPushforwardUnit_of_baseChange f hdim
    (isZero_firstCohomology_fiber f hdim hR) h0 g
  have := mono_unitToPushforwardUnit_of_surjective (pullback.snd f g)
  exact isIso_of_mono_of_epi _

/-- `𝒪_Y = e_*𝒪_X` for an isomorphism `e`. -/
theorem isIso_unitToPushforwardObjUnit_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom) :=
  AlgebraicGeometry.isIso_unitToPushforwardObjUnit_of_forall_isIso_app e fun W =>
    Functor.map_isIso (forget₂ CommRingCat RingCat) (e.app W.unop)

/-- **`𝒪_{Y'} = f'_*𝒪_{X'}` for a cartesian square over a reduced scheme.** The form of
`isIso_unitToPushforwardUnit_pullback_snd` for an arbitrary cartesian square
`g' : X' ⟶ X`, `f' : X' ⟶ Y'` over `f` and `g : Y' ⟶ Y`. -/
theorem isIso_unitToPushforwardObjUnit_of_isPullback {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f))
    (h0 : Epi (Scheme.Modules.unitToPushforwardUnit f)) [IsReduced Y'] [Surjective f'] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) := by
  have hf' : sq.isoPullback.hom ≫ pullback.snd f g = f' := sq.isoPullback_hom_snd
  have : Surjective (pullback.snd f g) := by
    rw [← sq.isoPullback_inv_snd]
    infer_instance
  have h := isIso_unitToPushforwardUnit_pullback_snd f hdim hR h0 g
  rw [← hf']
  exact Stacks.Curves.StableModel.isIso_unitToPushforwardObjUnit_comp _ _
    (isIso_unitToPushforwardObjUnit_of_isIso _) h

/-- **The higher direct images of `𝒪` vanish after base change.** Let `f : X ⟶ Y` be proper with
fibres of dimension at most one and `R¹f_*𝒪_X = 0`, and let `f' : X' ⟶ Y'` be a base change of
`f`. Then `Rⁱf'_*𝒪_{X'} = 0` for every `i > 0`: in degree one by
`isZero_firstDirectImageStructureSheaf_of_isPullback`, the fibres of `f` having vanishing
`H¹(𝒪)` by [Stacks, Tag 0E7F], and in degrees at least two by clause (1) of
[Stacks, Tag 0E7H], the fibres of `f'` having dimension at most one. -/
theorem isZero_rightDerived_of_isPullback {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) (i : ℕ) (hi : 0 < i) :
    IsZero (((Scheme.Modules.pushforward f').rightDerived i).obj
      (SheafOfModules.unit X'.ringCatSheaf)) := by
  have : IsProper f' := MorphismProperty.of_isPullback sq inferInstance
  refine IsZero.of_iso ?_ ((Stacks.DerivedIndexing.rightDerivedIso
    (Scheme.Modules.pushforward f') i).app _)
  rcases Nat.lt_or_ge i 2 with h | h
  · obtain rfl : i = 1 := by omega
    exact isZero_firstDirectImageStructureSheaf_of_isPullback f sq (fun y' => hdim (g y'))
      fun y' => isZero_firstCohomology_fiber f hdim hR (g y')
  · have : LocallyOfFiniteType f := inferInstance
    exact isZero_higherDirectImage_of_one_lt_of_isProper f'
      (fun y' => topologicalKrullDim_fiber_le_of_isPullback sq 1 y' (hdim (g y')))
      (SheafOfModules.unit X'.ringCatSheaf) (i : ℤ) (by omega)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
