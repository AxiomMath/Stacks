module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroEuler
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroSupport
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Basic
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Vanishing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Functoriality

/-!
# The closed-fibre member of a triple whose punctured-spectrum member vanishes

Let `A` be a Noetherian local ring and `f ∈ 𝔪`. For a coherent triple `T` whose
punctured-spectrum member `T.F` vanishes, the support of the closed-fibre member `T.F₀` is
contained in the closed point of the closed fibre. Hence `T.F₀` vanishes if and only if the closed
point is not an associated point of `T.F₀`, and in that case `T` has Euler characteristic `0`.

## Main results

* `AlgebraicGeometry.supp_pullback_eq_preimage`: the support of the inverse image of a module
  along an open immersion is the preimage of its support.
* `AlgebraicGeometry.notMem_supp_of_isZero_pullback`: if the inverse image of a module along an
  open immersion vanishes, no point of the image lies in the support of the module.
* `AlgebraicGeometry.isZero_pullback_of_forall_notMem_supp`: if no point of the image of an open
  immersion lies in the support of a module, the inverse image of the module vanishes.
* `Stacks.Algebraization.CoherentTriple.isZero_pullback_puncturedClosedFibre_F₀_of_isZero_F`:
  if `T.F` vanishes, so does the inverse image of `T.F₀` on the punctured closed fibre.
* `Stacks.Algebraization.CoherentTriple.notMem_supp_F₀_of_mem_puncturedClosedFibre`: if `T.F`
  vanishes, no point of the punctured closed fibre lies in the support of `T.F₀`.
* `Stacks.Algebraization.CoherentTriple.supp_F₀_subset_closedPoint`: if `T.F` vanishes, the
  support of `T.F₀` is contained in the closed point of the closed fibre.
* `Stacks.Algebraization.CoherentTriple.isZero_F₀_of_isZero_F`: if `T.F` vanishes and the closed
  point is not an associated point of `T.F₀`, then `T.F₀` vanishes.
* `CoherentTriple.not_isAssociatedPoint_closedPoint_iff_isZero_F₀_of_isZero_F`: if `T.F`
  vanishes, the closed point is not an associated point of `T.F₀` if and only if `T.F₀` vanishes.
* `Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_zero_of_isZero_F`: a coherent
  triple whose punctured-spectrum member vanishes and whose closed-fibre member has no associated
  point at the closed point has Euler characteristic `0`.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 0F26](https://stacks.math.columbia.edu/tag/0F26)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

/-! ### The support and the inverse image along an open immersion -/

/-- For an open immersion `g : X ⟶ Y`, the support of the inverse image of `F` along `g` is the
preimage under `g` of the support of `F`. -/
@[ega "0 4.3.1" "special case"]
public theorem AlgebraicGeometry.supp_pullback_eq_preimage {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (F : Y.Modules) :
    SheafOfModules.supp ((Scheme.Modules.pullback g).obj F) = g ⁻¹' SheafOfModules.supp F := by
  ext x
  have e : (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).obj
        ((Scheme.Modules.pullback g).obj F) ≅
      (Scheme.Modules.toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} (g x)).obj F :=
    (Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback g).app F).symm ≪≫
      (Scheme.Modules.restrictStalkNatIso g x).app F
  refine ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).trans ?_).trans
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F (g x)).symm
  exact Equiv.nontrivial_congr e.addCommGroupIsoToAddEquiv.toEquiv

/-- For an open immersion `g : X ⟶ Y` along which the inverse image of `F` vanishes, no point
`g x` lies in the support of `F`. -/
public theorem AlgebraicGeometry.notMem_supp_of_isZero_pullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] (F : Y.Modules)
    (hz : IsZero ((Scheme.Modules.pullback g).obj F)) (x : X) :
    g x ∉ SheafOfModules.supp F := by
  have h := SheafOfModules.supp_eq_empty_of_isZero hz
  rw [AlgebraicGeometry.supp_pullback_eq_preimage] at h
  exact Set.eq_empty_iff_forall_notMem.mp h x

/-- For an open immersion `g : X ⟶ Y` such that no point `g x` lies in the support of `F`, the
inverse image of `F` along `g` vanishes. -/
public theorem AlgebraicGeometry.isZero_pullback_of_forall_notMem_supp {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsOpenImmersion g] (F : Y.Modules)
    (h : ∀ x : X, g x ∉ SheafOfModules.supp F) :
    IsZero ((Scheme.Modules.pullback g).obj F) :=
  Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _
    (by rw [AlgebraicGeometry.supp_pullback_eq_preimage]
        exact Set.eq_empty_iff_forall_notMem.2 h)

namespace Stacks.Algebraization

/-! ### The support of the closed-fibre member -/

/-- If the punctured-spectrum member `T.F` of a coherent triple vanishes, so does the inverse
image of the closed-fibre member `T.F₀` on the punctured closed fibre. -/
public theorem CoherentTriple.isZero_pullback_puncturedClosedFibre_F₀_of_isZero_F {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T : CoherentTriple A f) (hT : IsZero T.F) :
    IsZero ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj T.F₀) :=
  IsZero.of_iso (isZero_obj_of_isZero (Scheme.Modules.pullback
    (morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A))) hT)
    T.alpha.symm

/-- If the punctured-spectrum member `T.F` of a coherent triple vanishes, no point of the
punctured closed fibre lies in the support of the closed-fibre member `T.F₀`. -/
public theorem CoherentTriple.notMem_supp_F₀_of_mem_puncturedClosedFibre {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T : CoherentTriple A f) (hT : IsZero T.F)
    {y : closedFibre A f} (hy : y ∈ (puncturedClosedFibre A f : Set (closedFibre A f))) :
    y ∉ SheafOfModules.supp T.F₀ := by
  have h := AlgebraicGeometry.notMem_supp_of_isZero_pullback (puncturedClosedFibre A f).ι T.F₀
    (T.isZero_pullback_puncturedClosedFibre_F₀_of_isZero_F hT) ⟨y, hy⟩
  simpa using h

/-- For `f` in the maximal ideal, if the punctured-spectrum member `T.F` of a coherent triple
vanishes, the support of the closed-fibre member `T.F₀` is contained in the closed point of the
closed fibre. -/
public theorem CoherentTriple.supp_F₀_subset_closedPoint {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f) (hT : IsZero T.F) :
    SheafOfModules.supp T.F₀ ⊆
      {(IsLocalRing.closedPoint (A ⧸ Ideal.span {f}) : closedFibre A f)} := by
  intro y hy
  by_contra hne
  refine T.notMem_supp_F₀_of_mem_puncturedClosedFibre hT ?_ hy
  rw [puncturedClosedFibre_eq_puncturedSpectrum A f hf]
  exact hne

/-! ### The vanishing of the closed-fibre member -/

/-- For a Noetherian local ring `A` and `f` in the maximal ideal, if the punctured-spectrum member
`T.F` of a coherent triple vanishes, then the closed point of the closed fibre is not an associated
point of the closed-fibre member `T.F₀` if and only if `T.F₀` vanishes. -/
private theorem CoherentTriple.not_isAssociatedPoint_iff_isZero_F₀ {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} [IsLocalRing (A ⧸ Ideal.span {f})]
    (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f) (hT : IsZero T.F) :
    ¬ Stacks.Divisors.IsAssociatedPoint T.F₀
        (IsLocalRing.closedPoint (A ⧸ Ideal.span {f})) ↔ IsZero T.F₀ := by
  have : T.F₀.IsCoherent := T.coherent_F₀
  have : T.F₀.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  rw [AlgebraicGeometry.isZero_iff_associatedPoints_eq_empty, Set.eq_empty_iff_forall_notMem]
  refine ⟨fun hass y hy => hass ?_, fun hz hass => hz _ hass⟩
  exact (T.supp_F₀_subset_closedPoint hf hT
    (AlgebraicGeometry.associatedPoints_subset_support T.F₀ hy) : y = _) ▸ hy

/-- For a Noetherian local ring `A` and `f` in the maximal ideal, if the punctured-spectrum member
`T.F` of a coherent triple vanishes and the closed point of the closed fibre is not an associated
point of the closed-fibre member `T.F₀`, then `T.F₀` vanishes. -/
public theorem CoherentTriple.isZero_F₀_of_isZero_F {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A} [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f) (hT : IsZero T.F)
    (hass : ¬ Stacks.Divisors.IsAssociatedPoint T.F₀
      (IsLocalRing.closedPoint (A ⧸ Ideal.span {f}))) :
    IsZero T.F₀ :=
  (T.not_isAssociatedPoint_iff_isZero_F₀ hf hT).1 hass

/-- For a Noetherian local ring `A` and `f` in the maximal ideal, if the punctured-spectrum member
`T.F` of a coherent triple vanishes, then the closed point of the closed fibre is not an associated
point of the closed-fibre member `T.F₀` if and only if `T.F₀` vanishes. -/
public theorem CoherentTriple.not_isAssociatedPoint_closedPoint_iff_isZero_F₀_of_isZero_F
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    (hT : IsZero T.F) :
    ¬ Stacks.Divisors.IsAssociatedPoint T.F₀
        (IsLocalRing.closedPoint (A ⧸ Ideal.span {f})) ↔ IsZero T.F₀ :=
  T.not_isAssociatedPoint_iff_isZero_F₀ hf hT

/-- For a Noetherian local ring `A` and `f` in the maximal ideal, a coherent triple
whose punctured-spectrum member vanishes and whose closed-fibre member has no associated point at
the closed point of the closed fibre has Euler characteristic `0`. -/
public theorem CoherentTriple.eulerCharacteristic_eq_zero_of_isZero_F {A : Type u} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {f : A} [IsLocalRing (A ⧸ Ideal.span {f})]
    (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f) (hT : IsZero T.F)
    (hass : ¬ Stacks.Divisors.IsAssociatedPoint T.F₀
      (IsLocalRing.closedPoint (A ⧸ Ideal.span {f}))) :
    T.eulerCharacteristic = 0 :=
  CoherentTriple.eulerCharacteristic_eq_zero_of_isZero hf hT
    (T.isZero_F₀_of_isZero_F hf hT hass)

end Stacks.Algebraization

end
