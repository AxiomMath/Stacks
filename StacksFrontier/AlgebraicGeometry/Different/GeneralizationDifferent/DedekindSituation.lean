module

public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.DedekindCase
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.TheDifferent
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Different.GeneralizationDifferent.DedekindTraceElement

/-!
# The situation of the generalized different when the Dedekind different is defined

Let `f : Y ⟶ X` be a locally quasi-finite morphism of affine locally Noetherian schemes for which
the Dedekind different of `Γ(X, ⊤) → Γ(Y, ⊤)` is defined. Then `f` is flat over the open `V ⊆ Y`
covered by the basic opens `D(g)` with `Γ(Y, ⊤)_g` flat over `Γ(X, ⊤)`, and `V` contains the
associated points of `Y` and the inverse image of those of `X`: this is condition (1) of the
generalization of the different.

## Main definitions

* `Stacks.Discriminant.flatBasicOpenUnion`: the union of the flat basic opens.
* `Stacks.Discriminant.generalizedDifferentSituationOfDedekind`: the resulting situation.

## Main results

* `Stacks.Discriminant.flat_resLE_iff`: on affine charts, flatness of the restricted morphism is
  flatness of the coordinate-ring map.
* `Stacks.Discriminant.flat_resLE_basicOpen_of_flat_away`: `f` is flat over `D(g)` when
  `Γ(Y, ⊤)_g` is flat over `Γ(X, ⊤)`.

## Implementation notes

Flatness on a chart inside `V` is checked on stalks, through `Scheme.Hom.resLEStalkMap`. The
associated points are compared with associated primes through
`Stacks.AlgebraicGeometry.AssociatedPointPrime.isAssociatedPoint_iff_mem_associatedPrimes`, and
flatness at such a prime spreads to a basic open by
`Stacks.Discriminant.exists_flat_away_of_flat_atPrime`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Discriminant

variable {X Y : Scheme.{u}} {f : Y ⟶ X}

/-- On affine charts, the restriction of a morphism is flat exactly when its coordinate-ring map
is. -/
theorem flat_resLE_iff {U : X.Opens} {W : Y.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W)
    (hWU : W ≤ f ⁻¹ᵁ U) : Flat (f.resLE U W hWU) ↔ (f.appLE U W hWU).hom.Flat := by
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat), Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top, CommRingCat.hom_comp U.topIso.hom,
    RingHom.Flat.respectsIso.cancel_left_isIso, CommRingCat.hom_comp,
    RingHom.Flat.respectsIso.cancel_right_isIso]

/-- A flat restriction of `f` to an open of the source is flat on stalks at its points. -/
theorem flat_stalkMap_of_flat_resLE {U : X.Opens} {W : Y.Opens} (hWU : W ≤ f ⁻¹ᵁ U)
    (H : Flat (f.resLE U W hWU)) {y : Y} (hy : y ∈ W) : (f.stalkMap y).hom.Flat := by
  have h := Flat.stalkMap (f.resLE U W hWU) ⟨y, hy⟩
  exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff (f.resLEStalkMap hWU ⟨y, hy⟩)).mp h

/-- A restriction of `f` to an open of the source on whose points `f` is flat on stalks is
flat. -/
theorem flat_resLE_of_flat_stalkMap {U : X.Opens} {W : Y.Opens} (hWU : W ≤ f ⁻¹ᵁ U)
    (H : ∀ y ∈ W, (f.stalkMap y).hom.Flat) : Flat (f.resLE U W hWU) :=
  Flat.of_stalkMap _ fun y =>
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff (f.resLEStalkMap hWU y)).mpr (H y.1 y.2)

/-- If `Γ(Y, ⊤)_g` is flat over `Γ(X, ⊤)`, then `f` is flat over the basic open `D(g)`. -/
theorem flat_resLE_basicOpen_of_flat_away [IsAffine X] [IsAffine Y] (g : Γ(Y, ⊤))
    (hg : letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
      Module.Flat Γ(X, ⊤) (Localization.Away g)) :
    Flat (f.resLE ⊤ (Y.basicOpen g) (by simp)) := by
  rw [flat_resLE_iff (isAffineOpen_top X) ((isAffineOpen_top Y).basicOpen g)]
  let : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ(Y, Y.basicOpen g) := (f.appLE ⊤ (Y.basicOpen g) (by simp)).hom.toAlgebra
  have : IsScalarTower Γ(X, ⊤) Γ(Y, ⊤) Γ(Y, Y.basicOpen g) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change (f.appLE ⊤ (Y.basicOpen g) (by simp)).hom x =
        (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom (f.appTop.hom x)
      rw [← CommRingCat.comp_apply]
      rfl
  let e := (IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g)
    Γ(Y, Y.basicOpen g)).toLinearEquiv.restrictScalars Γ(X, ⊤)
  exact RingHom.flat_algebraMap_iff.mpr (Module.Flat.of_linearEquiv e.symm)

section Situation

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f]

/-- The open of `Y` covered by the basic opens `D(g)` with `B_g` flat over `A`. -/
def flatBasicOpenUnion [IsAffine X] [IsAffine Y] (f : Y ⟶ X) : Y.Opens :=
  letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  ⨆ g : {g : Γ(Y, ⊤) // Module.Flat Γ(X, ⊤) (Localization.Away g)}, Y.basicOpen g.1

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] in
/-- `f` is flat on stalks at the points of `Stacks.Discriminant.flatBasicOpenUnion f`. -/
theorem flat_stalkMap_of_mem_flatBasicOpenUnion [IsAffine X] [IsAffine Y] {y : Y}
    (hy : y ∈ flatBasicOpenUnion f) : (f.stalkMap y).hom.Flat := by
  obtain ⟨g, hg⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact flat_stalkMap_of_flat_resLE _ (flat_resLE_basicOpen_of_flat_away g.1 g.2) hg

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyQuasiFinite f] in
/-- A point lies in `Stacks.Discriminant.flatBasicOpenUnion f` as soon as some `g` outside its
prime has `Γ(Y, ⊤)_g` flat over `Γ(X, ⊤)`. -/
theorem mem_flatBasicOpenUnion [IsAffine X] [IsAffine Y] {y : Y}
    (h : letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
      ∃ g : Γ(Y, ⊤), g ∉ ((isAffineOpen_top Y).primeIdealOf ⟨y, trivial⟩).asIdeal ∧
        Module.Flat Γ(X, ⊤) (Localization.Away g)) :
    y ∈ flatBasicOpenUnion f := by
  obtain ⟨g, hgq, hg⟩ := h
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, ?_⟩
  change y ∈ Y.basicOpen g
  rw [← PrimeSpectrum.mem_basicOpen, ← (isAffineOpen_top Y).fromSpec_preimage_basicOpen] at hgq
  change (isAffineOpen_top Y).fromSpec ((isAffineOpen_top Y).primeIdealOf ⟨y, trivial⟩) ∈
    Y.basicOpen g at hgq
  rwa [(isAffineOpen_top Y).fromSpec_primeIdealOf] at hgq

/-- **Condition (1) of the generalization of the different for `Spec B → Spec A` when the
Dedekind different of `A → B` is defined.** The open `V` of `Y` covered by the basic opens over
which `f` is flat contains the associated points of `Y` and the inverse image of those of
`X`. -/
def generalizedDifferentSituationOfDedekind [IsAffine X] [IsAffine Y]
    (setup : letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
      DedekindDifferentSetup Γ(X, ⊤) Γ(Y, ⊤)) :
    GeneralizedDifferentSituation f :=
  letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := f.appTop.hom.toAlgebra
  haveI := setup.isNoetherianRing
  haveI := setup.finite
  have hflat := flatAtPrimesOverAssociatedPrimes_of_dedekindDifferentSetup setup
  have hass : ∀ {Z : Scheme.{u}} [IsAffine Z] [IsLocallyNoetherian Z] {z : Z},
      z ∈ Stacks.Divisors.schemeAssociatedPoints Z →
        ((isAffineOpen_top Z).primeIdealOf ⟨z, trivial⟩).asIdeal ∈
          associatedPrimes Γ(Z, ⊤) Γ(Z, ⊤) := fun {Z} _ _ z hz =>
    haveI : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Z
    haveI : (SheafOfModules.unit Z.ringCatSheaf).IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
        (SheafOfModules.unit Z.ringCatSheaf)).1
    (Stacks.AlgebraicGeometry.AssociatedPointPrime.isAssociatedPoint_iff_mem_associatedPrimes
      (SheafOfModules.unit Z.ringCatSheaf) (isAffineOpen_top Z) trivial).mp hz
  have key : ∀ y : Y, Module.Flat Γ(X, ⊤)
      (Localization.AtPrime ((isAffineOpen_top Y).primeIdealOf ⟨y, trivial⟩).asIdeal) →
      y ∈ flatBasicOpenUnion f := fun y hy =>
    mem_flatBasicOpenUnion (exists_flat_away_of_flat_atPrime _ hy)
  { V := flatBasicOpenUnion f
    flat := fun U W hWU hWV =>
      (flat_resLE_iff U.2 W.2 hWU).mp
        (flat_resLE_of_flat_stalkMap hWU fun _ hy => flat_stalkMap_of_mem_flatBasicOpenUnion
          (hWV hy))
    schemeAssociatedPoints_source_subset := fun y hy =>
      key y (hflat.1 _ (hass hy))
    preimage_schemeAssociatedPoints_base_subset := fun y hy => by
      refine key y (hflat.2 _ ?_)
      have h := IsAffineOpen.comap_primeIdealOf_appLE (f := f) ⊤ (isAffineOpen_top X) ⊤
        (isAffineOpen_top Y) (by simp) (x := y) trivial
      have h' := hass
        (show f.base y ∈ Stacks.Divisors.schemeAssociatedPoints X from hy)
      have e1 : f.appLE ⊤ ⊤ (by simp) = f.appTop := Scheme.Hom.appLE_eq_app f
      rw [← h] at h'
      change Ideal.comap (f.appLE ⊤ ⊤ (by simp)).hom _ ∈ _ at h'
      rw [e1] at h'
      exact h' }

end Situation

end Stacks.Discriminant

end
