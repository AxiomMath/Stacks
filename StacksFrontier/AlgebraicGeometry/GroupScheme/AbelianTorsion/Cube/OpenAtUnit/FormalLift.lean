module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.FormalNeighbourhood
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianTorsion.Cube.OpenAtUnit.Induction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete

/-!
# Triviality near a fibre from compatible sections on the thickenings

A variant of `Stacks.FormalNeighbourhood.exists_isTrivial_of_forall_truncation` whose hypothesis
is the output of the thickening induction `Stacks.CubeOpenAtUnit.exists_lift_of_faces`: a section
`t₀` of `ℒ / Iℒ` generating `ℒ` along `V(I)`, which lifts to every `ℒ / Iⁿ⁺¹ℒ`. The closed fibre
is given by an arbitrary closed immersion `v` cut out by `I · 𝒪_P`.

## Main results

* `Stacks.CubeOpenAtUnit.exists_isTrivial_of_lifts`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization Stacks.FormalNeighbourhood
open Stacks.Cohomology.FormalFunctions (baseIdealSheaf)

universe u

namespace Stacks.CubeOpenAtUnit

variable {R : Type u} [CommRing R] {P : Scheme.{u}} (f : P ⟶ Spec (.of R)) (I : Ideal R)

/-- Two closed immersions with the same ideal sheaf have the same image. -/
theorem range_eq_of_ker_eq {V V' : Scheme.{u}} (v : V ⟶ P) (v' : V' ⟶ P) [IsClosedImmersion v]
    [IsClosedImmersion v'] (h : v.ker = v'.ker) : Set.range v.base = Set.range v'.base := by
  rw [← v.isClosedEmbedding.isClosed_range.closure_eq,
    ← v'.isClosedEmbedding.isClosed_range.closure_eq, ← Scheme.Hom.support_ker v,
    ← Scheme.Hom.support_ker v', h]

/-- **A section vanishing nowhere on the closed fibre, from compatible lifts.** -/
theorem exists_forall_mem_nonvanishingLocus_of_lifts [IsNoetherianRing R] [IsProper f]
    (L : P.Modules) [hL : Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.property L]
    [L.IsQuasicoherent] {V : Scheme.{u}} (v : V ⟶ P) [IsClosedImmersion v]
    (hv : v.ker = baseIdealSheaf R I f ^ 1)
    (t₀ : Γ(quo f I L 1, ⊤))
    (ht₀ : ∀ y, y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback v).obj L)
      ((idealQuotientPushforwardIso (baseIdealSheaf R I f) 1 L v hv).hom.app ⊤ t₀))
    (hlift : ∀ n, ∃ t : Γ(quo f I L (n + 1), ⊤),
      (idealPowerQuotientDrop (baseIdealSheaf R I f) (Nat.le_add_left 1 n) L).app ⊤ t = t₀) :
    ∃ s : Γ(L, ⊤), ∀ y, v.base y ∈ Stacks.Ample.nonvanishingLocus L s := by
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian f
  have hL' : Stacks.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L := hL
  have hcoh : Stacks.SheafOfModules.IsCoherent L :=
    AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent
      (Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible P L)
  obtain ⟨c, hc⟩ := exists_forall_exists_π_eq_drop f I L hcoh
  obtain ⟨t, ht⟩ := hlift c
  obtain ⟨s, hs⟩ := hc t
  refine ⟨s, fun y => ?_⟩
  have hu : ((Scheme.Modules.pullbackPushforwardAdjunction v).unit.app L).app ⊤ s =
      (idealQuotientPushforwardIso (baseIdealSheaf R I f) 1 L v hv).hom.app ⊤ t₀ := by
    rw [← idealQuotientPushforwardMap_π (baseIdealSheaf R I f) 1 L v hv,
      Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
    rw [idealQuotientPushforwardIso_hom]
    congr 1
    exact hs.trans ht
  have h := Stacks.Models.nonvanishingLocus_unit_app_top v L s
  rw [hu] at h
  have hy := ht₀ y
  rw [h] at hy
  exact hy

/-- **An invertible module with compatible lifts of a generator along `V(I)` is trivial near each
point of `V(I)`.** -/
theorem exists_isTrivial_of_lifts [IsNoetherianRing R] [IsProper f] (L : P.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.property L]
    [L.IsQuasicoherent] {V : Scheme.{u}} (v : V ⟶ P) [IsClosedImmersion v]
    (hv : v.ker = baseIdealSheaf R I f ^ 1)
    (t₀ : Γ(quo f I L 1, ⊤))
    (ht₀ : ∀ y, y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback v).obj L)
      ((idealQuotientPushforwardIso (baseIdealSheaf R I f) 1 L v hv).hom.app ⊤ t₀))
    (hlift : ∀ n, ∃ t : Γ(quo f I L (n + 1), ⊤),
      (idealPowerQuotientDrop (baseIdealSheaf R I f) (Nat.le_add_left 1 n) L).app ⊤ t = t₀)
    (x : Spec (.of R)) (hx : x ∈ Set.range (truncationBase I 0).base) :
    ∃ U : (Spec (.of R)).Opens, x ∈ U ∧
      AlgebraicGeometry.SheafOfModules.IsTrivial (pullback f U.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback f U.ι).IsSheaf)
        ((RingedSpaceModuleAdjunction.modulePullback
          (pullback.fst f U.ι).toLRSHom.toShHom).obj L) := by
  obtain ⟨s, hs⟩ := exists_forall_mem_nonvanishingLocus_of_lifts f I L v hv t₀ ht₀ hlift
  have : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hL
  refine
    AlgebraicGeometry.SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus
      f L f.isClosedMap ((Stacks.NonvanishingSpelling.sectionsEquiv P L).symm s) x ?_
  intro y hy
  rw [Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq]
  have hmem : y ∈ Set.range (truncationι f I 0).base := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hy]
    exact hx
  rw [range_eq_of_ker_eq (truncationι f I 0) v (by rw [ker_truncationι, hv])] at hmem
  obtain ⟨z, rfl⟩ := hmem
  exact hs z

end Stacks.CubeOpenAtUnit

end
