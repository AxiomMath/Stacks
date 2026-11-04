module

public import StacksFrontier.AlgebraicGeometry.TwistedThickeningLift.FirstOrder
public import StacksFrontier.AlgebraicGeometry.AmpleThickeningDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleSurjectiveThickening.Basic
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleAndExtension.Separated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.SeparatedDescent

/-!
# The cohomological lift of Stacks Tag 09MS, discharged

`Stacks.AmpleClosedImmersion.SectionsLiftAfterPower i L` asks that every global section `t` of a
positive tensor power of `i^* L` with affine nonvanishing locus have a power lifting to `X`, in
the sense that some global section `T` of a positive tensor power of `L` has
`i^{-1}(X_T) = Z_t`. It is the one input the converse of [Stacks Project, Tag 09MS] needed in this
repository.

* For a **first-order** thickening of a quasi-compact separated scheme this is
  `Stacks.TwistedThickeningLift.exists_preimage_nonvanishingLocus_eq`, transported to the tensor
  powers the property is stated with.
* For a thickening of a quasi-compact separated **locally Noetherian** scheme, the dévissage
  along the powers of the ideal sheaf
  (`Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_of_isThickening_of_isLocallyNoetherian`)
  reduces it to the first-order case.
* Hence the converse of [Stacks Project, Tag 09MS] holds with **no extra hypothesis**:
  `Stacks.TwistedThickeningLift.isAmple_of_isAmple_modulePullback`. Separatedness of `X` is not
  assumed: `Z` is separated because `i^* L` is ample ([Stacks Project, Tag 01PY]), and `X` then is
  by [Stacks Project, Tag 09MQ], `i` being surjective and universally closed.

No `stacks` attribute is attached here: [Stacks Project, Tag 09MS] is registered elsewhere, and the
converse below is consumed by the proof of [Stacks Project, Tag 09MW].

## Main results

* `Stacks.TwistedThickeningLift.sectionsLiftAfterPower_of_isFirstOrderThickening`.
* `Stacks.TwistedThickeningLift.sectionsLiftAfterPower_of_isLocallyNoetherian`.
* `Stacks.TwistedThickeningLift.isAmple_of_isAmple_modulePullback`: if `i : Z ⟶ X` is a surjective
  closed immersion onto a locally Noetherian scheme and `i^* L` is ample, then `L` is ample.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 01PY](https://stacks.math.columbia.edu/tag/01PY)
* [Stacks Project, Tag 09MQ](https://stacks.math.columbia.edu/tag/09MQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample (IsInvertibleModule tensorPowModule)
open Stacks.AmpleClosedImmersion (SectionsLiftAfterPower)

universe u

namespace Stacks.TwistedThickeningLift

/-- **The cohomological lift for a first-order thickening of a quasi-compact separated scheme.** -/
theorem sectionsLiftAfterPower_of_isFirstOrderThickening {S S' : Scheme.{u}} (m : S ⟶ S')
    (hm : Stacks.Thickenings.IsFirstOrderThickening m) [CompactSpace S'] [S'.IsSeparated]
    (N : S'.Modules) [IsInvertibleModule S' N] : SectionsLiftAfterPower m N := by
  have : IsClosedImmersion m := hm.1
  intro n hn t haff
  let eX : ∀ k : ℤ, pow N k ≅ tensorPowModule S' N k := fun k =>
    Stacks.PowerFamilyBridge.tensorPowerModuleIso S' N k
  let eZ : tensorPowModule S (Stacks.AmpleLocallyClosed.pullbackModule m N) (n : ℤ) ≅
      Stacks.AmpleLocallyClosed.pullbackModule m (pow N n) :=
    (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso m N n).symm ≪≫
      (modulePullback m.toLRSHom.toShHom).mapIso (eX n).symm
  have hs : Stacks.Ample.nonvanishingLocus _ (eZ.hom.app ⊤ t) =
      Stacks.Ample.nonvanishingLocus _ t :=
    Stacks.Ample.nonvanishingLocus_congr eZ t
  obtain ⟨k, hk, T, hT⟩ := exists_preimage_nonvanishingLocus_eq hm.2 n (eZ.hom.app ⊤ t)
    (Stacks.AmpleTheory.powNonvanishingOpen S _ n t)
    (by rw [Stacks.AmpleTheory.coe_powNonvanishingOpen, hs]) haff
  refine ⟨n * k, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    (eX _).hom.app ⊤ T, Opens.ext ?_⟩
  show m.base ⁻¹' Stacks.Ample.nonvanishingLocus _ ((eX _).hom.app ⊤ T) =
    Stacks.Ample.nonvanishingLocus _ t
  rw [Stacks.Ample.nonvanishingLocus_congr, hT, hs]

/-- **The cohomological lift for a thickening of a quasi-compact separated locally Noetherian
scheme.** The dévissage reduces it to the first-order case. -/
theorem sectionsLiftAfterPower_of_isLocallyNoetherian {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [Surjective i] [IsLocallyNoetherian X] [CompactSpace Z]
    [X.IsSeparated] (L : X.Modules) [IsInvertibleModule X L] : SectionsLiftAfterPower i L :=
  Stacks.AmpleThickeningDevissage.sectionsLiftAfterPower_of_isThickening_of_isLocallyNoetherian
    (fun _ _ m hm _ _ N _ => sectionsLiftAfterPower_of_isFirstOrderThickening m hm N)
    ⟨inferInstance, Surjective.surj⟩ L

/-- **A scheme carrying an ample invertible module is separated** ([Stacks Project, Tag 01PY]),
read at `Stacks.Ample.IsAmple`. -/
theorem isSeparated_of_isAmple {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]
    (h : Stacks.Ample.IsAmple X L) : X.IsSeparated :=
  ((Stacks.AmpleBridge.isAmple_iff_isAmple X L).mp h).isSeparated

/-- **The converse of [Stacks Project, Tag 09MS], with no extra hypothesis.** If `i : Z ⟶ X` is a
surjective closed immersion onto a locally Noetherian scheme and `i^* L` is ample, then `L` is
ample. The source assumes `X` Noetherian; local Noetherianness suffices, quasi-compactness of `X`
following from that of `Z`. -/
theorem isAmple_of_isAmple_modulePullback {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Surjective i] [IsLocallyNoetherian X] (L : X.Modules) [IsInvertibleModule X L]
    (h : Stacks.Ample.IsAmple Z ((modulePullback i.toLRSHom.toShHom).obj L)) :
    Stacks.Ample.IsAmple X L := by
  have : CompactSpace Z := h.compactSpace
  have : Z.IsSeparated := isSeparated_of_isAmple _ h
  have : X.IsSeparated := Scheme.isSeparated_of_surjective_universallyClosed i
  exact Stacks.AmpleSurjectiveThickening.isAmple_of_isAmple_modulePullback i L
    (sectionsLiftAfterPower_of_isLocallyNoetherian i L) h

end Stacks.TwistedThickeningLift

end
