module

public import StacksFrontier.AlgebraicGeometry.Descent.TrivialOnOpen0BF3
public import StacksFrontier.AlgebraicGeometry.FiniteTrivialize.Basic
public import StacksFrontier.AlgebraicGeometry.InvertibleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# A section nonvanishing along a fibre of a closed morphism trivializes near the fibre

Let `p : P ⟶ S` be a morphism of schemes whose underlying map is closed, let `L` be an invertible
`𝒪_P`-module, let `σ` be a global section of `L` and let `s ∈ S`. If `σ` vanishes at no point of
`P` lying over `s`, then there is an open neighbourhood `U` of `s` such that `L` is trivial over
`P ×_S U`. This is the "straightforward topological argument (omitted)" that closes the proofs of
[Stacks, Tag 0BF1](https://stacks.math.columbia.edu/tag/0BF1) and
[Stacks, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2): there the section is a lift of a
trivializing section of `L` on the fibre `P_s`, and the conclusion is the one
[Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3) asserts.

## Main results

* `SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus`: if `σ`
  vanishes at no point over `s`, then `L` is trivial over `P ×_S U` for some open `U ∋ s`.
* `SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_fiber`: the same conclusion when the
  pullback of `σ` to the fibre `P ×_S Spec κ(s)` vanishes nowhere, which is the form in which the
  source produces the section.

## Implementation notes

The argument is the tube lemma `Stacks.SheafOfModules.exists_isOpen_mem_preimage_subset` for
the closed map `p` and the open nonvanishing locus of `σ` (Tag 01CY), followed by Tag 0H78
(`Stacks.SheafOfModules.preimage_nonvanishingLocus`): the pullback of `σ` to `P ×_S U` vanishes
nowhere, and a nowhere vanishing section of an invertible module trivializes it
(`AlgebraicGeometry.isTrivial_of_nonvanishingLocus_eq_univ`). The module on `P ×_S U` is the
`modulePullback` along `pullback.fst p U.ι`, the spelling of "`L` over `P_U`" used in
`StacksFrontier/AlgebraicGeometry/Descent/TrivialOnOpen0BF3.lean`, and the fibre over `s` is the base
change along `S.fromSpecResidueField s`.

Invertibility is taken in the `AlgebraicGeometry.SheafOfModules.IsInvertible` spelling of the
cube files; the Tag 01CY nonvanishing API is reached through
`Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible`.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {S P : Scheme.{u}} (p : P ⟶ S)
  (L : _root_.SheafOfModules.{u} (structureSheafRing P.toRingedSpace))
  [IsInvertible P.presheaf
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L]

/-- **A section vanishing at no point over `s` trivializes the module near the fibre.** Let the
underlying map of `p : P ⟶ S` be closed, let `L` be invertible on `P` and let `σ` be a global
section of `L` vanishing at no point of `P` over `s`. Then `L` is trivial over `P ×_S U` for some
open neighbourhood `U` of `s`.

The nonvanishing locus of `σ` is open and contains the fibre, so by the tube lemma it contains
`p⁻¹ U` for an open `U ∋ s`; the pullback of `σ` to `P ×_S U` then vanishes nowhere (Tag 0H78),
and so trivializes the pullback of `L`. -/
theorem exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus
    (hp : IsClosedMap p.base) (σ : L.sections) (s : S)
    (hσ : ∀ x : P, p.base x = s →
      x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := P.toRingedSpace) L σ) :
    ∃ U : S.Opens, s ∈ U ∧
      IsTrivial (pullback p U.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback p U.ι).IsSheaf)
        ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L) := by
  have _ : ∀ x : P.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk P.toRingedSpace x) :=
    fun x => P.isLocalRing x
  have : Stacks.SheafOfModules.IsInvertible P.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) P.IsSheaf) L :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  obtain ⟨V, hVo, hsV, hVsub⟩ := Stacks.SheafOfModules.exists_isOpen_mem_preimage_subset hp
    (Stacks.SheafOfModules.isOpen_nonvanishingLocus (X := P.toRingedSpace) L σ) (y := s)
    (fun x hx => hσ x hx)
  let U : S.Opens := ⟨V, hVo⟩
  refine ⟨U, hsV, ?_⟩
  let q : pullback p U.ι ⟶ P := pullback.fst p U.ι
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible (pullback p U.ι).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback p U.ι).IsSheaf)
      ((modulePullback q.toLRSHom.toShHom).obj L) :=
    Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry _ L ‹_›
  refine isTrivial_of_nonvanishingLocus_eq_univ (X := pullback p U.ι)
    ((modulePullback q.toLRSHom.toShHom).obj L)
    (Stacks.SheafOfModules.modulePullbackSection q.toLRSHom L σ) ?_
  refine (Stacks.SheafOfModules.preimage_nonvanishingLocus q.toLRSHom L σ).symm.trans
    (Set.eq_univ_of_forall fun y => hVsub ?_)
  show p.base (q.base y) ∈ V
  have hy : p.base (q.base y) = U.ι.base ((pullback.snd p U.ι).base y) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  rw [hy]
  exact ((pullback.snd p U.ι).base y).2

/-- **A section whose restriction to the fibre vanishes nowhere trivializes the module near the
fibre.** As `exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus`, with the hypothesis
read on the fibre `P ×_S Spec κ(s)`: every point of `P` over `s` is the image of a point of the
fibre, and the nonvanishing locus of the pulled-back section is the preimage of that of `σ`
(Tag 0H78). -/
theorem exists_isTrivial_modulePullback_fst_ι_of_fiber
    (hp : IsClosedMap p.base) (σ : L.sections) (s : S)
    (hσ : ∀ y : ↥(pullback p (S.fromSpecResidueField s) : Scheme.{u}),
      y ∈ Stacks.SheafOfModules.nonvanishingLocus
        (X := (pullback p (S.fromSpecResidueField s)).toRingedSpace)
        ((modulePullback (pullback.fst p (S.fromSpecResidueField s)).toLRSHom.toShHom).obj L)
        (Stacks.SheafOfModules.modulePullbackSection
          (pullback.fst p (S.fromSpecResidueField s)).toLRSHom L σ)) :
    ∃ U : S.Opens, s ∈ U ∧
      IsTrivial (pullback p U.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback p U.ι).IsSheaf)
        ((modulePullback (pullback.fst p U.ι).toLRSHom.toShHom).obj L) := by
  refine exists_isTrivial_modulePullback_fst_ι_of_mem_nonvanishingLocus p L hp σ s ?_
  intro x hx
  have hxr : x ∈ Set.range (pullback.fst p (S.fromSpecResidueField s)) := by
    rw [Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
    exact hx
  obtain ⟨y, rfl⟩ := hxr
  have hy : y ∈ (pullback.fst p (S.fromSpecResidueField s)).base ⁻¹'
      Stacks.SheafOfModules.nonvanishingLocus (X := P.toRingedSpace) L σ :=
    (Stacks.SheafOfModules.preimage_nonvanishingLocus
      (pullback.fst p (S.fromSpecResidueField s)).toLRSHom L σ).symm ▸ hσ y
  exact hy

end AlgebraicGeometry.SheafOfModules

end
