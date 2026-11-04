module

public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalPicardAlgebraization

/-!
# Extending invertible modules from `U₀` from an essential-surjectivity input

Let `(A, 𝔪)` be a Noetherian local ring and `f ∈ 𝔪` a nonzerodivisor with `H³_𝔪(A/fA) = 0`, and
let `U`, resp. `U₀`, be the punctured spectrum of `A`, resp. of `A/fA`. The proof of
[Stacks, Tag 0F2D] has two halves:

1. every invertible module on `U₀` lifts to an invertible object of `Coh(U, f𝒪_U)`, by
   [Stacks, Tag 0C6R] and `H²(U₀, 𝒪_{U₀}) = H³_𝔪(A/fA) = 0`;
2. such an object is the completion of a finite locally free module on an open `U' ⊇ U₀` of
   `U` — the essential-surjectivity half of the completion equivalence on finite locally free
   objects — and that module is invertible near `U₀`.

The second half uses the equivalence only through its essential surjectivity. [Stacks, Tag 0F2D]
takes it from [Stacks, Tag 0EKZ], and [Stacks, Tag 0F2E] takes it from [Stacks, Tag 0EKY]
instead. This file proves the argument once, for any input of that form, so that both tags are
the same proof.

## Main results

* `Stacks.PuncturedSpectrumPicard.exists_completion_iso_of_forall_isCompletionNearClosed` — the
  essential-surjectivity input, read on the punctured spectrum with the ideal sheaf `f𝒪_U`.
* `Stacks.PuncturedSpectrumPicard.picardColimitSurjective_of_forall_isCompletionNearClosed` —
  the argument of [Stacks, Tag 0F2D] from that input.

## References

* [Stacks Project, Tag 0F2D](https://stacks.math.columbia.edu/tag/0F2D)
* [Stacks Project, Tag 0F2E](https://stacks.math.columbia.edu/tag/0F2E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace Stacks.PuncturedSpectrumPicard

open Stacks.Picard (ofScheme schemePullbackClass schemePullbackClass_comp
  classOf_picardRepresentative pullbackClass_classOf)

variable (A : Type u) [CommRing A] [IsLocalRing A] (f : A)

/-- **The essential-surjectivity input on the punctured spectrum.** If every object of
`Coh(U, f𝒪_U)` with finite free stalks is the completion of a finite locally free module on an
open neighbourhood of `U₀` in `U` (in the situation `(f) ⊆ 𝔪` of [Stacks, Tag 0EHC]), then the same
holds with `U` written as any open equal to the punctured spectrum and the ideal sheaf written as
`f𝒪`. -/
theorem exists_completion_iso_of_forall_isCompletionNearClosed [IsNoetherianRing A]
    (hf : f ∈ maximalIdeal A)
    (hES : ∀ F : Stacks.Coherent.CoherentAdicSystems
        (Stacks.Algebraization.idealOnOpen (principalLocalSituation A f hf)),
      Stacks.Algebraization.HasFiniteFreeStalks (principalLocalSituation A f hf) F →
        Stacks.Algebraization.IsCompletionNearClosedFiniteLocallyFree
          (principalLocalSituation A f hf) F)
    (W : (Spec (.of A)).Opens) (hW : W = (principalLocalSituation A f hf).U)
    (F : Stacks.Coherent.CoherentAdicSystems
      (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {f}) W.ι))
    (hfree : ∀ (m : ℕ) (y : W.toScheme), ∃ r : ℕ,
      Nonempty ((Stacks.ModuleSkyscraper.modulesStalkFunctor W.toScheme y).obj (F.obj.obj (op m))
        ≃ₗ[W.toScheme.presheaf.stalk y]
        (Fin r → (W.toScheme.presheaf.stalk y ⧸ AlgebraicGeometry.IdealSheafData.stalk
          (Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {f}) W.ι) y ^
            (m + 1))))) :
    ∃ V : W.toScheme.Opens,
      (W.ι.base ⁻¹' Set.range (Stacks.Algebraization.closedImmersion A f).base) ⊆
          (V : Set W.toScheme) ∧
        ∃ G : AlgebraicGeometry.SheafOfModules.CoherentModules V.toScheme.ringCatSheaf,
          Scheme.Modules.IsFiniteLocallyFree G.obj ∧
          Nonempty (((Stacks.Algebraization.completionFunctor V.toScheme
              ((Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {f}) W.ι).comap
                V.ι)).obj G).obj ≅
            (F.obj ⋙ Scheme.Modules.restrictFunctor V.ι)) := by
  subst hW
  have hJ : Stacks.Algebraization.idealOnOpen (principalLocalSituation A f hf) =
      Stacks.Cohomology.FormalFunctions.baseIdealSheaf A (Ideal.span {f})
        (principalLocalSituation A f hf).U.ι :=
    (baseIdealSheaf_eq_comap A (Ideal.span {f}) (principalLocalSituation A f hf).U.ι).symm
  have h := hES
  unfold Stacks.Algebraization.HasFiniteFreeStalks
    Stacks.Algebraization.IsCompletionNearClosedFiniteLocallyFree
    Stacks.Algebraization.systemObj at h
  rw [hJ] at h
  exact h F hfree

/-- **The argument of [Stacks, Tag 0F2D], from an essential-surjectivity input.** Let `(A, 𝔪)` be
a Noetherian local ring and `f ∈ 𝔪` a nonzerodivisor with `H³_𝔪(A/fA) = 0`. If every object of
`Coh(U, f𝒪_U)` with finite free stalks is the completion of a finite locally free module on an
open neighbourhood of `U₀` in `U`, then `colim_{U₀ ⊆ U' ⊆ U open} Pic(U') ⟶ Pic(U₀)` is
surjective.

A class on `U₀` extends to a compatible family along the infinitesimal neighbourhoods
`Uₙ = V((f𝒪_U)ⁿ⁺¹)` by [Stacks, Tag 0C6R] (`exists_compatible_idealPowerStages`); the
representing invertible modules form a finite locally free object of `Coh(U, f𝒪_U)`; by the
input it is the completion of a finite locally free `𝒢` on an open `V ⊇ U₀`; `𝒢` restricts to
the given module on `U₀` and is therefore invertible on an open `U' ⊇ U₀`
(`exists_opens_isInvertible_of_pullback_iso`). -/
theorem picardColimitSurjective_of_forall_isCompletionNearClosed [IsNoetherianRing A]
    (hf : f ∈ maximalIdeal A) (hreg : IsSMulRegular A f)
    (hvanish3 : IsZero (Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} A
      {closedPoint A} ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (A ⧸ Ideal.span {f}))) 3))
    (hES : ∀ F : Stacks.Coherent.CoherentAdicSystems
        (Stacks.Algebraization.idealOnOpen (principalLocalSituation A f hf)),
      Stacks.Algebraization.HasFiniteFreeStalks (principalLocalSituation A f hf) F →
        Stacks.Algebraization.IsCompletionNearClosedFiniteLocallyFree
          (principalLocalSituation A f hf) F) :
    PicardColimitSurjective A f := by
  intro c₀
  obtain ⟨d, hd0, hd⟩ := exists_compatible_idealPowerStages A f hf hreg hvanish3 c₀
  let L := stageModules A f d hd
  have hfreeL : ∀ n, Scheme.Modules.IsFiniteLocallyFree (L.obj n) :=
    fun n => isFiniteLocallyFree_classModule (d n)
  obtain ⟨V, hV, G, hG, ⟨e⟩⟩ := exists_completion_iso_of_forall_isCompletionNearClosed A f hf hES
    (Stacks.Divisors.puncturedSpectrum A) (principalLocalSituation_U A f hf).symm L.adicSystem
    (fun m y => L.exists_stalk_linearEquiv_pi hfreeL m y)
  have hrange : Set.range (puncturedPrincipalIdeal A f ^ (0 + 1)).subschemeι.base ⊆
      (V : Set (Stacks.Divisors.puncturedSpectrum A).toScheme) := by
    rintro _ ⟨z, rfl⟩
    refine hV ⟨((Stacks.Algebraization.closedImmersion A f ⁻¹ᵁ
      Stacks.Divisors.puncturedSpectrum A).ι).base ((fibreStageIso A f).inv.base z), ?_⟩
    have h1 : (fibreStageIso A f).inv ≫ morphismRestrict (Stacks.Algebraization.closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A) =
        (puncturedPrincipalIdeal A f ^ (0 + 1)).subschemeι := by
      rw [← fibreStageIso_hom_subschemeι, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc, morphismRestrict_ι, Scheme.Hom.comp_base, TopCat.hom_comp,
      ContinuousMap.comp_apply] using congrArg (fun φ => φ.base z)
        (congrArg (· ≫ (Stacks.Divisors.puncturedSpectrum A).ι) h1)
  obtain ⟨j, hj, ⟨ej⟩⟩ := L.exists_pullback_iso_of_completion_iso V hrange G e
  obtain ⟨W, hW, hinv⟩ := exists_opens_isInvertible_of_pullback_iso G.obj hG j (d 0) ej
  have hjW : Set.range j.base ⊆ Set.range W.ι.base := by rwa [Scheme.Opens.range_ι]
  let j' := IsOpenImmersion.lift W.ι j hjW
  have hj' : j' ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  let cW : ofScheme W.toScheme := Stacks.SheafOfModules.picardClass _ _ _ hinv
  have hcW : schemePullbackClass j' cW = d 0 := by
    refine (pullbackClass_classOf j'.toLRSHom.toShHom _ hinv).trans ?_
    rw [← classOf_picardRepresentative _ (d 0)]
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).mpr
      ⟨(Scheme.Modules.pullbackComp j' W.ι).app G.obj ≪≫
        (Scheme.Modules.pullbackCongr hj').app G.obj ≪≫ ej⟩
  let eW := V.ι.isoImage W
  refine ⟨V.ι ''ᵁ W, (fibreStageIso A f).hom ≫ j' ≫ eW.hom, ?_, schemePullbackClass eW.inv cW, ?_⟩
  · rw [Category.assoc, Category.assoc, Scheme.Hom.isoImage_hom_ι, ← Category.assoc j',
      hj', hj, fibreStageIso_hom_subschemeι]
  · rw [schemePullbackClass_comp, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, ← schemePullbackClass_comp, hcW, hd0, schemePullbackClass_comp,
      Iso.hom_inv_id, Stacks.Picard.schemePullbackClass_id]

end Stacks.PuncturedSpectrumPicard

end
