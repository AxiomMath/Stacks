module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Criterion
public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.RingTheory.Serre.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Serre.FlatAscent
public import StacksFrontier.RingTheory.Smooth.RegularRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Serre's condition `(Rₖ)` is local in the smooth topology

For every natural number `k`, being locally Noetherian and regular in codimension at most
`k` is local for smooth coverings of schemes.

## Main results

* `AlgebraicGeometry.isRegularInCodimension_iff_hasPropertyRk` compares the scheme-theoretic
  condition on an affine scheme with the ring-theoretic one.
* `AlgebraicGeometry.isLocallyNoetherian_and_isRegularInCodimension_isLocal_smooth` gives
  smooth locality of the combined property.

## Implementation notes

Ascent is property `(Rₖ)` of a smooth algebra over a Noetherian ring with `(Rₖ)`, obtained
from the flat ascent criterion together with regularity of the fibres of a smooth map;
descent is the faithfully flat descent of `(Rₖ)`. Both are applied to the global sections of
the affine schemes involved.

## References

* [Stacks Project, Tag 036C](https://stacks.math.columbia.edu/tag/036C)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- On an affine scheme, regularity in codimension `k` is property `(Rₖ)` of the ring of
global sections. -/
theorem isRegularInCodimension_iff_hasPropertyRk (Y : Scheme.{u}) [IsAffine Y] (k : ℕ) :
    IsRegularInCodimension Y k ↔ HasPropertyRk Γ(Y, ⊤) k := by
  have hU : IsAffineOpen (⊤ : Y.Opens) := isAffineOpen_top Y
  constructor
  · intro h q hq hqk
    let x : (⊤ : Y.Opens) := ⟨hU.fromSpec ⟨q, hq⟩, trivial⟩
    let : Algebra Γ(Y, ⊤) (Y.presheaf.stalk x.1) :=
      Y.presheaf.algebra_section_stalk ⟨x.1, x.2⟩
    have : IsLocalization.AtPrime (Y.presheaf.stalk x.1) q :=
      hU.isLocalization_stalk' ⟨q, hq⟩ (by simp)
    have hdim : ringKrullDim (Y.presheaf.stalk x.1) ≤ (k : WithBot ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Y.presheaf.stalk x.1)]
      exact_mod_cast hqk
    have : IsRegularLocalRing (Y.presheaf.stalk x.1) := h x.1 hdim
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (Y.presheaf.stalk x.1)).toRingEquiv.symm
  · intro h x hx
    let xU : (⊤ : Y.Opens) := ⟨x, trivial⟩
    let : Algebra Γ(Y, ⊤) (Y.presheaf.stalk x) :=
      Y.presheaf.algebra_section_stalk ⟨xU.1, xU.2⟩
    let q : Ideal Γ(Y, ⊤) := (hU.primeIdealOf xU).asIdeal
    have : q.IsPrime := (hU.primeIdealOf xU).2
    have : IsLocalization.AtPrime (Y.presheaf.stalk x) q := hU.isLocalization_stalk xU
    let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (Y.presheaf.stalk x)
    have hdim : ringKrullDim (Localization.AtPrime q) ≤ (k : WithBot ℕ∞) :=
      (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).trans_le hx
    have hqk : q.height ≤ (k : ℕ∞) := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at hdim
      exact_mod_cast hdim
    have : IsRegularLocalRing (Localization.AtPrime q) := h q hqk
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

/-- Regularity of the local ring in codimension `k` is read through any morphism inducing an
isomorphism on the stalk at the given point. -/
private lemma regularInCodimensionAt_iff_of_stalkMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) [IsIso (f.stalkMap x)] (k : ℕ) :
    (ringKrullDim (X.presheaf.stalk x) ≤ (k : WithBot ℕ∞) →
        IsRegularLocalRing (X.presheaf.stalk x)) ↔
      (ringKrullDim (Y.presheaf.stalk (f x)) ≤ (k : WithBot ℕ∞) →
        IsRegularLocalRing (Y.presheaf.stalk (f x))) := by
  let e : X.presheaf.stalk x ≃+* Y.presheaf.stalk (f x) :=
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.symm
  constructor
  · intro h hd
    have := h ((ringKrullDim_eq_of_ringEquiv e).trans_le hd)
    exact IsRegularLocalRing.of_ringEquiv e
  · intro h hd
    have := h ((ringKrullDim_eq_of_ringEquiv e).symm.trans_le hd)
    exact IsRegularLocalRing.of_ringEquiv e.symm

/-- Being locally Noetherian and regular in codimension `k` passes to the source of an open
immersion. -/
private lemma isLocallyNoetherian_and_isRegularInCodimension_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (k : ℕ)
    (hX : IsLocallyNoetherian X ∧ IsRegularInCodimension X k) :
    IsLocallyNoetherian Y ∧ IsRegularInCodimension Y k := by
  have : IsLocallyNoetherian X := hX.1
  exact ⟨isLocallyNoetherian_of_isOpenImmersion f, fun y hy =>
    (regularInCodimensionAt_iff_of_stalkMap f y k).mpr (hX.2 (f y)) hy⟩

private instance isRegularInCodimension_isClosedUnderIsomorphisms (k : ℕ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} => IsLocallyNoetherian X ∧ IsRegularInCodimension X k) where
  of_iso e hX := isLocallyNoetherian_and_isRegularInCodimension_of_isOpenImmersion e.inv k hX

private instance isRegularInCodimension_isLocal_zariski (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} => IsLocallyNoetherian X ∧ IsRegularInCodimension X k)
      Scheme.zariskiPrecoverage := by
  refine isLocal_zariskiPrecoverage_of_openCover _ ?_ ?_
  · intro X U hX
    exact isLocallyNoetherian_and_isRegularInCodimension_of_isOpenImmersion U.ι k hX
  · intro X U hU h
    refine ⟨(isLocallyNoetherian_iff_openCover (X.openCoverOfIsOpenCover U hU)).2
      fun x => (h x).1, fun x hx => ?_⟩
    obtain ⟨i, hxi⟩ := hU.exists_mem x
    let y : (U i).toScheme := ⟨x, hxi⟩
    exact (regularInCodimensionAt_iff_of_stalkMap (U i).ι y k).mp ((h i).2 y) hx

/-- Property `(Rₖ)` ascends along a smooth algebra over a Noetherian ring. -/
@[ega "IV 17.5.8" "(iii)"]
private theorem hasPropertyRk_of_smooth (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.Smooth R S] (k : ℕ) (hR : HasPropertyRk R k) :
    HasPropertyRk S k := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine property_Rk_of_flat_of_fibre_of_base R S k (fun p hp => ?_) hR
  have : p.IsPrime := hp
  have : IsRegularRing (p.Fiber S) := Algebra.isRegularRing_of_smooth p.ResidueField (p.Fiber S)
  have : IsRegularRing (fibreRing R S p) :=
    IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm R p.ResidueField S).toRingEquiv
  exact fun q hq _ => IsRegularRing.isRegularLocalRing_localization q

/-- **Stacks Project, Tag 036C.** Being locally Noetherian and regular in codimension `k` is
local for smooth coverings. -/
@[stacks 036C, ega "IV 17.5.8" "(iii)"]
instance isLocallyNoetherian_and_isRegularInCodimension_isLocal_smooth (k : ℕ) :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} => IsLocallyNoetherian X ∧ IsRegularInCodimension X k)
      (Scheme.precoverage @Smooth) := by
  refine isLocal_smoothPrecoverage_of_affine
    (fun X : Scheme.{u} => IsLocallyNoetherian X ∧ IsRegularInCodimension X k) ?_ ?_
  · intro X S hX hS f hsm hSprop
    have : IsAffine X := hX
    have : IsAffine S := hS
    have : IsLocallyNoetherian S := hSprop.1
    have : Smooth f := hsm
    have hmap : (f.appTop).hom.Smooth := by
      simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
        hsm.smooth_appLE (isAffineOpen_top S) (isAffineOpen_top X) le_rfl
    have : IsNoetherianRing Γ(S, ⊤) := hSprop.1.component_noetherian ⟨⊤, isAffineOpen_top S⟩
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    have : Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤) := RingHom.smooth_algebraMap.mp hmap
    exact ⟨LocallyOfFiniteType.isLocallyNoetherian f,
      (isRegularInCodimension_iff_hasPropertyRk X k).mpr
        (hasPropertyRk_of_smooth Γ(S, ⊤) Γ(X, ⊤) k
          ((isRegularInCodimension_iff_hasPropertyRk S k).mp hSprop.2))⟩
  · intro X S hX hS f hsm hsurj hXprop
    have : IsAffine X := hX
    have : IsAffine S := hS
    have : Smooth f := hsm
    have hff : (f.appTop).hom.FaithfullyFlat :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, hsurj⟩
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    have : IsNoetherianRing Γ(X, ⊤) := hXprop.1.component_noetherian ⟨⊤, isAffineOpen_top X⟩
    have : Module.FaithfullyFlat Γ(S, ⊤) Γ(X, ⊤) := by
      rw [← RingHom.faithfullyFlat_algebraMap_iff]
      simpa [RingHom.algebraMap_toAlgebra] using hff
    obtain ⟨hNoethR, hRkR⟩ :=
      isNoetherianRing_and_isRegularLocalRing_atPrime_of_faithfullyFlat
        (R := Γ(S, ⊤)) (S := Γ(X, ⊤)) (k := (k : ℕ∞))
        ((isRegularInCodimension_iff_hasPropertyRk X k).mp hXprop.2)
    have hLocNoethS : IsLocallyNoetherian S :=
      (isLocallyNoetherian_iff_of_iSup_eq_top
        (S := fun _ : Unit => ⟨⊤, isAffineOpen_top S⟩) (by simp)).2 fun _ => by
          simpa using hNoethR
    exact ⟨hLocNoethS, (isRegularInCodimension_iff_hasPropertyRk S k).mpr hRkR⟩

end AlgebraicGeometry
