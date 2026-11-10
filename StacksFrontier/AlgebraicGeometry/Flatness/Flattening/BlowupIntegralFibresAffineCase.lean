module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresGeometric
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.BlowupIntegralFibresSituation
public import StacksFrontier.AlgebraicGeometry.IdealSheafFiniteType.Basic

/-!
# Stacks 0811 over an affine base whose boundary is principal

Over an affine base `S`, with the distinguished open the basic open of a global section `s` and
with the generic fibre rank constant, the affine engine [Stacks, Tag 0810] solves the
strict-transform problem of [Stacks, Tag 0811] outright: it produces a centre supported exactly
on `V(s)` over every point of whose blowup the strict transform is free of the constant rank on
an open of the base change.

## Main results

* `AlgebraicGeometry.isFiniteType_of_fg_ideal_top`: on an affine scheme a quasi-coherent sheaf of
  ideals whose ideal of global sections is finitely generated is of finite type.
* `AlgebraicGeometry.FlatteningSituation.isSolvable_of_affine_of_basicOpen`: the statement above.

## Implementation notes

[Stacks, Tag 0810] is available in the `Stacks.Blowup` realization of the blowup, while
`AlgebraicGeometry.FreeOnSurjectiveOpen` and [Stacks, Tag 080F] are stated in the
`AlgebraicGeometry` one. The two are compared by `Stacks.Blowup.blowUpPullbackIso` and
`Stacks.Blowup.strictTransformSheafIso`, and the property is carried across by
`AlgebraicGeometry.FreeOnSurjectiveOpen.map`.

The open `V` of the conclusion is the union of the neighbourhoods [Stacks, Tag 0810] produces,
one per point of the blowup; each of them carries a point above that point, which is what makes
`V` surject onto the blowup.

The finite-type half of admissibility is read off the single affine open `⊤` by
`Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover`, and turned into finite presentation of the
closed immersion by `AlgebraicGeometry.finitePresentation_subschemeι_iff_isFiniteType`.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
* [Stacks Project, Tag 01TV](https://stacks.math.columbia.edu/tag/01TV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **On an affine scheme a quasi-coherent sheaf of ideals finitely generated on global sections
is of finite type.** The affine open `⊤` covers the scheme by itself, so finite generation there
propagates to every affine open. -/
theorem isFiniteType_of_fg_ideal_top {S : Scheme.{u}} [IsAffine S] (ℐ : S.IdealSheafData)
    (h : (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩).FG) : ℐ.IsFiniteType :=
  Stacks.IdealSheafFiniteType.fg_ideal_of_fg_cover ℐ
    (fun _ : Unit ↦ (⟨⊤, isAffineOpen_top S⟩ : S.affineOpens)) (by simp) fun _ ↦ h

namespace FlatteningSituation

/-- **[Stacks, Tag 0811] over an affine base with principal boundary and constant generic fibre
rank.** With `S` affine, the distinguished open the basic open of `s : Γ(S, ⊤)` and the stalk of
`F` at every generic point of a fibre over it free of rank `r`, the situation is solvable: the
centre produced by [Stacks, Tag 0810] is of finite presentation, is supported exactly on `V(s)`,
and over every point of its blowup the strict transform of `F` is free of rank `r` on an open of
the base change. -/
theorem isSolvable_of_affine_of_basicOpen (D : FlatteningSituation.{u}) [IsAffine D.S]
    (s : Γ(D.S, ⊤)) (hU : D.U = D.S.basicOpen s) (r : ℕ)
    (hrank : ∀ x : D.X, D.f.base x ∈ D.S.basicOpen s →
      D.f.base ⁻¹' {D.f.base x} ⊆ closure {x} →
      letI := Stacks.ModuleStalkSpecialization.stalkModule D.F x
      Nonempty (Module.Basis (Fin r) (D.X.presheaf.stalk x) (D.F.presheaf.stalk x))) :
    D.IsSolvable := by
  classical
  have hFU : (D.F.restrict (D.f ⁻¹ᵁ D.S.basicOpen s).ι).IsFinitePresentation := by
    rw [← hU]
    exact D.finitePresentation_restrict
  obtain ⟨ℐ, hfg, hsupp, hchart⟩ :=
    exists_idealSheafData_forall_blowUp_exists_free_of_rank D.f D.finitePresentation D.F s r
      hFU hrank
  -- The centre is `U`-admissible.
  have hfp : FinitePresentation ℐ.subschemeι :=
    (finitePresentation_subschemeι_iff_isFiniteType ℐ).mpr (isFiniteType_of_fg_ideal_top ℐ hfg)
  have hdisj : Disjoint (D.U : Set D.S) (ℐ.support : Set D.S) := by
    rw [hsupp, hU]
    exact disjoint_compl_right
  -- The conclusion of tag 0810, in the `Stacks.Blowup` realization.
  choose W x hxW hsnd hiso using hchart
  have hStacks : FreeOnSurjectiveOpen (pullback.snd D.f (Stacks.Blowup.blowUpToBase ℐ))
      (Stacks.StrictTransform.sheaf D.f (Stacks.Blowup.blowUpToBase ℐ)
        (Stacks.Blowup.exceptionalIdeal ℐ) D.F) := by
    refine ⟨inferInstance, ⨆ z : Stacks.Blowup.blowUp ℐ, W z, fun y hy ↦ ?_, fun z ↦ ?_⟩
    · obtain ⟨z, hyz⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
      exact ⟨r, freeAtPointOfRank_of_restrict_iso_free _ hyz r (hiso z).some⟩
    · exact ⟨⟨x z, TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hxW z⟩⟩, hsnd z⟩
  -- Transport it to the `AlgebraicGeometry` realization of the blowup.
  have hAG : FreeOnSurjectiveOpen (pullback.snd D.f (blowUpToBase ℐ))
      (Stacks.StrictTransform.sheaf D.f (blowUpToBase ℐ) (exceptionalIdeal ℐ) D.F) := by
    refine FreeOnSurjectiveOpen.map (Stacks.Blowup.blowUpPullbackIso D.f ℐ).symm
      (blowUpIso ℐ).symm ?_ ?_ hStacks
    · have hb := Stacks.Blowup.blowUpPullbackIso_hom_blowUpPullbackToBlowUp D.f ℐ
      change pullback.snd D.f (Stacks.Blowup.blowUpToBase ℐ) ≫ (blowUpIso ℐ).inv =
        (Stacks.Blowup.blowUpPullbackIso D.f ℐ).inv ≫ pullback.snd D.f (blowUpToBase ℐ)
      rw [← Iso.inv_hom_id_assoc (Stacks.Blowup.blowUpPullbackIso D.f ℐ)
        (pullback.snd D.f (Stacks.Blowup.blowUpToBase ℐ)), hb, Category.assoc, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    · exact ((Scheme.Modules.pullbackId _).app _).symm ≪≫
        (Scheme.Modules.pullbackCongr
          (Stacks.Blowup.blowUpPullbackIso D.f ℐ).inv_hom_id.symm).app _ ≪≫
        ((Scheme.Modules.pullbackComp (Stacks.Blowup.blowUpPullbackIso D.f ℐ).inv
          (Stacks.Blowup.blowUpPullbackIso D.f ℐ).hom).app _).symm ≪≫
        (Scheme.Modules.pullback (Stacks.Blowup.blowUpPullbackIso D.f ℐ).inv).mapIso
          (Stacks.Blowup.strictTransformSheafIso D.f ℐ D.F)
  exact ⟨ℐ, hfp, hdisj,
    (freeOnSurjectiveOpen_strictTransform_iff_sheaf D.f D.F ℐ).mpr hAG⟩

end FlatteningSituation

end AlgebraicGeometry

end
