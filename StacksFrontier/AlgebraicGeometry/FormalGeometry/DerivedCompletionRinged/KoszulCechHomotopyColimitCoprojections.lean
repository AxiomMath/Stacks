module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechHomotopyColimit
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimitsCoprojections

/-!
# The Čech complex as a derived colimit of Koszul complexes, with its coprojections named

Let `(𝒞, 𝒪)` be a ringed site and `f_1, …, f_r` global sections of `𝒪`.
`AlgebraicGeometry.RingedSite.isHomotopyColimit_koszulPowerSystem` of
`KoszulCechHomotopyColimit.lean` says that the extended alternating Čech complex `Č(f)` is, in
`D(𝒪)`, the homotopy colimit of the Koszul complexes on the positive powers of the `f_i`. This
file records the refinement that keeps the cocone: the coprojections of the derived colimit datum
may be taken to be the images under `Q` of the canonical maps `Kⁿ ⟶ Č(f)` of
[Stacks, Tag 0913].

## Main results

* `AlgebraicGeometry.RingedSite.exists_isHomotopyColimitWithCoprojections_koszulPowerSystem`:
  `Q(Č(f))` carries a derived colimit datum ([Stacks, Tag 0CRH]) for the Koszul system whose
  coprojections are `Q` of the canonical maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The extended alternating Čech complex is the homotopy colimit of the Koszul complexes, with
the coprojections named as the canonical maps `Q(Kⁿ) ⟶ Q(Č(f))`.**

The Čech complex carries a derived colimit datum ([Stacks, Tag 0CRH],
`CategoryTheory.Pretriangulated.IsHomotopyColimitWithCoprojections`) for the system of Koszul
complexes on the positive powers of `f_1, …, f_r` whose coprojections are the images under
`Q` of the canonical maps `AlgebraicGeometry.RingedSite.koszulCechComplexMap` of
[Stacks, Tag 0913].

Two steps are composed, and the point is that each of them keeps its cocone.
`DerivedCategory.isHomotopyColimitWithCoprojections_Q_obj_colimit` is [Stacks, Tag 0949] with the
coprojections of the termwise colimit named, and
`CategoryTheory.Pretriangulated.IsHomotopyColimitWithCoprojections.of_iso` transports the datum
along `Q` of the identification of the two colimits, which carries the coprojections of
`colimit (koszulPowerSystem X f)` to those of
`AlgebraicGeometry.RingedSite.koszulCechComplexCocone` by
`CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`. The morphism to the shifted
direct sum is existentially bound, a derived colimit datum pinning no such morphism.

This is what `AlgebraicGeometry.RingedSite.isHomotopyColimit_koszulPowerSystem` leaves out: the
latter asserts `CategoryTheory.Pretriangulated.IsHomotopyColimit`, which quantifies the
structural map of its triangle away, so the cocone cannot be read off it. The pinned form is
what [Stacks, Tag 0A0A] with its projections named
(`AlgebraicGeometry.RingedSite.isDerivedLimitWithProjections_derivedSheafHom_of_coprojections`)
consumes. -/
theorem exists_isHomotopyColimitWithCoprojections_koszulPowerSystem :
    ∃ c : DerivedCategory.Q.obj (extendedAlternatingCech X f) ⟶
        (∐ (koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)⟦(1 : ℤ)⟧,
      IsHomotopyColimitWithCoprojections (koszulPowerSystem X f ⋙ DerivedCategory.Q)
        (DerivedCategory.Q.obj (extendedAlternatingCech X f))
        (fun n => DerivedCategory.Q.map (koszulCechComplexMap X f n)) c := by
  obtain ⟨c, hc⟩ :=
    DerivedCategory.isHomotopyColimitWithCoprojections_Q_obj_colimit (koszulPowerSystem X f)
  let e := DerivedCategory.Q.mapIso
    ((colimit.isColimit (koszulPowerSystem X f)).coconePointUniqueUpToIso
      (isColimitKoszulCechComplexCocone X f))
  refine ⟨e.inv ≫ c, (hc.of_iso e).of_eq_coprojections fun n => ?_⟩
  rw [Functor.mapIso_hom, ← Functor.map_comp, colimit.comp_coconePointUniqueUpToIso_hom,
    koszulCechComplexCocone_ι_app]
  rfl

end AlgebraicGeometry.RingedSite

end
