module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.BlowupAlgebraizationPullback
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ExtensionCohomologicalDimensionOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AnnihilatedComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicUnitConditionDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalComparisonMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.GrothendieckExistenceProper
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.PrincipalPowerSubscheme
public import StacksFrontier.AlgebraicGeometry.RestrictIso

/-!
# Extending across the blowup, after completing the base, in the proof of Stacks 0EJK

In Situation [Stacks, Tag 0EHC] let `b : X' ⟶ X = Spec(A)` be the blowup of `X` in `I`, let
`U' = b⁻¹(U)` and let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)`. The last paragraph of the proof of
[Stacks, Tag 0EJK] shows: if there is an object `(𝒢ₙ)` of `Coh(X', I𝒪_{X'})` and a map
`(b|_{U'}^*ℱₙ) ⟶ (𝒢ₙ|_{U'})` whose levelwise kernels and cokernels are annihilated by a power of
`I`, then `(ℱₙ)` extends to `X`.

The proof passes to the `I`-adic completion `Â` of `A`, where extendability becomes membership in
the essential image of the completion functor ([Stacks, Tag 0EIN]). Let `c : Spec(Â) ⟶ X`, let
`X̂' = X' ×_X Spec(Â)` with projections `p : X̂' ⟶ X'`, flat, and `b̂ : X̂' ⟶ Spec(Â)`, proper,
and let `Û = c⁻¹(U)`, `Û' = b̂⁻¹(Û)`.

1. Grothendieck's existence theorem ([Stacks, Tag 088C]) over the complete ring `Â` gives a
   coherent `𝒪_{X̂'}`-module `𝒢` whose completion is `(p^*𝒢ₙ)`.
2. Pulling the given map back along the flat morphism `Û' ⟶ U'` gives a map
   `(b̂|_{Û'}^* c^*ℱₙ) ⟶ (𝒢|_{Û'})^∧` whose kernels and cokernels are still annihilated by a power
   of `I`, so ([Stacks, Tag 0889]) the pullback of `(c^*ℱₙ)` to `Û'` is a completion.
3. The blowup is an isomorphism off its centre ([Stacks, Tag 02OS]), hence so is its base change
   `b̂|_{Û'} : Û' ⟶ Û` over `Û ∖ V(IÂ)`; by [Stacks, Tag 088B] and [Stacks, Tag 0889] again the
   pullback `(c^*ℱₙ)` of `(ℱₙ)` to `Û` is a completion, and [Stacks, Tag 0EIN] concludes.

## Main results

* `Stacks.Algebraization.extendsToX_of_blowup_extension` — the last step of the proof of
  [Stacks, Tag 0EJK].
* `Stacks.Algebraization.essImage_completionFunctor_of_essImage_coherentAdicPullback` — along a
  proper morphism which is an isomorphism off `V(𝒥)`, an object of `Coh(Y, 𝒥)` whose pullback is
  a completion is itself a completion ([Stacks, Tag 088B] with [Stacks, Tag 0889]).

## Implementation notes

The base change of the blowup is the fibre product `X' ×_X Spec(Â)` itself rather than the blowup
of `Spec(Â)` in `IÂ` ([Stacks, Tag 0805]): only its properness over `Spec(Â)`, the flatness of
`p`, the identification of `IÂ𝒪_{X̂'}` with the inverse image of `I𝒪_{X'}`, and the base change
of the isomorphism off the centre are used, and all four hold for the fibre product directly.

## References

* [Stacks Project, Tag 0EJK](https://stacks.math.columbia.edu/tag/0EJK)
* [Stacks Project, Tag 0EIN](https://stacks.math.columbia.edu/tag/0EIN)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 088C](https://stacks.math.columbia.edu/tag/088C)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Coherent

/-- The inverse system underlying `f^*(𝒢_n)` is the termwise pullback `𝒢 ⋙ f^*`. -/
theorem coherentAdicPullback_obj_functor {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (G : CoherentAdicSystems J) :
    ((coherentAdicPullback f J).obj G).obj = G.obj ⋙ Scheme.Modules.pullback f :=
  rfl

end Stacks.Coherent

namespace Stacks.Algebraization

/-- **Stacks 088B and 0889 (1) together.** Let `f : X ⟶ Y` be a proper morphism of Noetherian
schemes which is an isomorphism over the complement of `V(𝒥)`. If the pullback `f^*(𝒢_n)` of an
object of `Coh(Y, 𝒥)` is the completion of a coherent `𝒪_X`-module, then `(𝒢_n)` is the
completion of a coherent `𝒪_Y`-module. -/
theorem essImage_completionFunctor_of_essImage_coherentAdicPullback {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (J : Y.IdealSheafData) (f : X ⟶ Y) [IsProper f]
    (hf : IsIso (f ∣_ J.support.compl)) (G : Stacks.Coherent.CoherentAdicSystems J)
    (h : (completionFunctor X (J.comap f)).essImage
      ((Stacks.Coherent.coherentAdicPullback f J).obj G)) :
    (completionFunctor Y J).essImage G := by
  obtain ⟨𝓕, ⟨e⟩⟩ := h
  have : 𝓕.obj.IsCoherent := 𝓕.property
  obtain ⟨α, hα⟩ := Stacks.Coherent.exists_isKernelCokernelAnnihilatedByPower_comparisonMap J J f
    hf G 𝓕.obj e.symm
  exact essImage_of_essImage_of_isKernelCokernelAnnihilatedByPower Y J α hα ⟨_, ⟨Iso.refl _⟩⟩

/-- The ideal sheaf `I Â` on `Spec(Â)` is the inverse image of `I` along `Spec(Â) ⟶ Spec(A)`. -/
theorem comap_completionMap_specIdealSheaf (S : AlgebraizationSituation.{u}) :
    (Stacks.LocalCohomology.specIdealSheaf S.A S.I).comap (completionMap S) =
      Scheme.IdealSheafData.ofIdealTop ((completedSituation S).I.map
        (Scheme.ΓSpecIso (.of (completedSituation S).A)).inv.hom) := by
  rw [Stacks.LocalCohomology.specIdealSheaf, Stacks.AlgebraicGeometry.comap_ofIdealTop,
    Ideal.map_map]
  change Scheme.IdealSheafData.ofIdealTop (S.I.map (((Scheme.ΓSpecIso (.of S.A)).inv ≫
    (completionMap S).appTop).hom)) = Scheme.IdealSheafData.ofIdealTop
      ((S.I.map (algebraMap S.A (AdicCompletion S.I S.A))).map
        (Scheme.ΓSpecIso (.of (AdicCompletion S.I S.A))).inv.hom)
  rw [Ideal.map_map, completionMap, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- `I · 𝒪_T` for a scheme `T` over `Spec(Â)` is the inverse image of `I` along
`T ⟶ Spec(Â) ⟶ Spec(A)`. -/
theorem baseIdealSheaf_completion_eq_comap (S : AlgebraizationSituation.{u}) {T : Scheme.{u}}
    (g : T ⟶ (completedSituation S).X) :
    Stacks.Cohomology.FormalFunctions.baseIdealSheaf (completedSituation S).A
        (completedSituation S).I g =
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I).comap (g ≫ completionMap S) := by
  rw [Stacks.PuncturedSpectrumPicard.baseIdealSheaf_eq_comap, Scheme.IdealSheafData.comap_comp,
    comap_completionMap_specIdealSheaf]

/-- The ideal `I𝒪_U` on `U`, pulled back to `Û = c⁻¹(U)`, is the inverse image of `I` along
`Û ⟶ Spec(Â) ⟶ Spec(A)`. -/
private theorem comap_ker_comap_completionMap (S : AlgebraizationSituation.{u}) :
    (S.Yι.ker.comap S.U.ι).comap (completionMap S ∣_ S.U) =
      (Stacks.LocalCohomology.specIdealSheaf S.A S.I).comap
        ((completionMap S ⁻¹ᵁ S.U).ι ≫ completionMap S) := by
  rw [← idealOnX_eq_ker_Yι S, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]
  rfl

/-- The base change `X' ×_X Spec(Â) ⟶ Spec(Â)` of the blowup, restricted over `Û`, is an
isomorphism over the complement of the support of `I𝒪_Û`. -/
private theorem isIso_completedBlowup_restrict_compl_support (S : AlgebraizationSituation.{u}) :
    IsIso ((pullback.snd (situationBlowUpToBase S) (completionMap S) ∣_
      (completionMap S ⁻¹ᵁ S.U)) ∣_
        ((S.Yι.ker.comap S.U.ι).comap (completionMap S ∣_ S.U)).support.compl) := by
  let ℐ := Stacks.LocalCohomology.specIdealSheaf S.A S.I
  let c := completionMap S
  let b := situationBlowUpToBase S
  let bh : pullback b c ⟶ (completedSituation S).X := pullback.snd b c
  let Uh : (completedSituation S).X.Opens := c ⁻¹ᵁ S.U
  let J : Uh.toScheme.IdealSheafData := (S.Yι.ker.comap S.U.ι).comap (c ∣_ S.U)
  let W : S.X.Opens := ℐ.support.compl
  have hJ : J = ℐ.comap (Uh.ι ≫ c) := comap_ker_comap_completionMap S
  have hb : IsIso (b ∣_ W) :=
    Stacks.Blowup.isIso_blowUpToBase_restrict_of_subset_compl_support_reesData ℐ W
      fun _ hx => hx
  have hbh : IsIso (bh ∣_ c ⁻¹ᵁ W) :=
    Stacks.Algebraization.isIso_morphismRestrict_of_isPullback (IsPullback.of_hasPullback b c) W
      hb
  have hV : J.support.compl ≤ Uh.ι ⁻¹ᵁ c ⁻¹ᵁ W := fun x hx hmem =>
    hx (by rwa [hJ, Scheme.IdealSheafData.support_comap])
  have hle : Uh.ι ''ᵁ J.support.compl ≤ c ⁻¹ᵁ W := by
    refine ((Scheme.Hom.image_le_image_iff Uh.ι _ _).mpr hV).trans ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_le_right
  change IsIso ((bh ∣_ Uh) ∣_ J.support.compl)
  rw [← MorphismProperty.isomorphisms.iff,
    (MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict bh Uh J.support.compl)]
  exact Stacks.RestrictIso.isIso_morphismRestrict_of_le bh hle hbh

/-- **The last step of the proof of Stacks 0EJK.** Let `b : X' ⟶ X` be the blowup of
`X = Spec(A)` in `I` and `U' = b⁻¹(U)`. Let `(ℱₙ)` be an object of `Coh(U, I𝒪_U)` and `(𝒢ₙ)` an
object of `Coh(X', I𝒪_{X'})`, and let `σ : (b|_{U'}^*ℱₙ) ⟶ (𝒢ₙ|_{U'})` be a map whose levelwise
kernels and cokernels are annihilated by a power of `I𝒪_{U'}`. Then `(ℱₙ)` extends to `X`. -/
theorem extendsToX_of_blowup_extension (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (G : Stacks.Coherent.CoherentAdicSystems (situationExceptionalIdeal S))
    (σ : (blowupPullbackSystem S F).obj ⟶
      G.obj ⋙ Scheme.Modules.restrictFunctor (situationBlowUpU S).ι)
    (hσ : IsKernelCokernelAnnihilatedByPower (blowupIdealU S) σ) :
    ExtendsToX S (toKerSystem S F) := by
  rw [extendsToX_iff_pullback_isCompletion]
  let ℐ := Stacks.LocalCohomology.specIdealSheaf S.A S.I
  let c := completionMap S
  let b := situationBlowUpToBase S
  let p : pullback b c ⟶ situationBlowUp S := pullback.fst b c
  let bh : pullback b c ⟶ (completedSituation S).X := pullback.snd b c
  have hpb : p ≫ b = bh ≫ c := pullback.condition
  have : Flat c := Flat.SpecMap_iff.mpr
    (RingHom.flat_algebraMap_iff.mpr (AdicCompletion.flat_of_isNoetherian S.I))
  have : IsAdicComplete (completedSituation S).I (completedSituation S).A :=
    AdicCompletion.isAdicComplete_self S.I (Ideal.fg_of_isNoetherianRing S.I)
  have : IsLocallyNoetherian (pullback b c) := LocallyOfFiniteType.isLocallyNoetherian bh
  have : CompactSpace (pullback b c : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace bh
  have : IsNoetherian (pullback b c) := {}
  let Uh : (completedSituation S).X.Opens := c ⁻¹ᵁ S.U
  let U'h : (pullback b c).Opens := bh ⁻¹ᵁ Uh
  let f : U'h.toScheme ⟶ Uh.toScheme := bh ∣_ Uh
  let J : Uh.toScheme.IdealSheafData := (S.Yι.ker.comap S.U.ι).comap (c ∣_ S.U)
  have hJ : J = ℐ.comap (Uh.ι ≫ c) := comap_ker_comap_completionMap S
  -- the blowup is an isomorphism off its centre, and so is its base change
  have hf : IsIso (f ∣_ J.support.compl) := isIso_completedBlowup_restrict_compl_support S
  refine essImage_completionFunctor_of_essImage_coherentAdicPullback J f hf _ ?_
  -- Grothendieck existence on the base change `X' ×_X Spec(Â)`, which is proper over `Spec(Â)`
  let L := Stacks.Cohomology.FormalFunctions.baseIdealSheaf (completedSituation S).A
    (completedSituation S).I bh
  have hLdef : L = ℐ.comap (bh ≫ c) := baseIdealSheaf_completion_eq_comap S bh
  have hExc : situationExceptionalIdeal S = ℐ.comap b := rfl
  have hL : (situationExceptionalIdeal S).comap p = L := by
    rw [hExc, ← Scheme.IdealSheafData.comap_comp, hpb, hLdef]
  let E : (pullback b c : Scheme.{u}).IdealSheafData := (situationExceptionalIdeal S).comap p
  have : (completionFunctor (pullback b c) E).IsEquivalence := by
    rw [show E = L from hL]
    exact isEquivalence_completionFunctor_of_isProper (completedSituation S).A
      (completedSituation S).I bh
  let Gh := (Stacks.Coherent.coherentAdicPullback p (situationExceptionalIdeal S)).obj G
  let 𝒢 := (completionFunctor (pullback b c) E).objPreimage Gh
  let eG : ((completionFunctor (pullback b c) E).obj 𝒢).obj ≅ Gh.obj :=
    (ObjectProperty.ι _).mapIso ((completionFunctor (pullback b c) E).objObjPreimageIso Gh)
  -- the comparison morphism `Û' ⟶ U'`
  have hq : U'h ≤ p ⁻¹ᵁ situationBlowUpU S := by
    change bh ⁻¹ᵁ c ⁻¹ᵁ S.U ≤ p ⁻¹ᵁ b ⁻¹ᵁ S.U
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hpb]
  let q : U'h.toScheme ⟶ (situationBlowUpU S).toScheme := p.resLE _ _ hq
  have hq' : q ≫ (situationBlowUpU S).ι = U'h.ι ≫ p := Scheme.Hom.resLE_comp_ι _ _
  have hf' : f ≫ Uh.ι = U'h.ι ≫ bh := morphismRestrict_ι bh Uh
  have hsq : f ≫ (c ∣_ S.U) = q ≫ blowupRestrict S := by
    rw [← cancel_mono S.U.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      morphismRestrict_ι, reassoc_of% hf', reassoc_of% hq', hpb]
  have hmor : (q ≫ (situationBlowUpU S).ι) ≫ b = f ≫ Uh.ι ≫ c := by
    rw [hq', Category.assoc, hpb, reassoc_of% hf']
  have hIdeal : (blowupIdealU S).comap q = J.comap f := by
    rw [hJ, blowupIdealU, hExc, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hmor]
  have hLJ : E.comap U'h.ι = J.comap f := by
    rw [show E = L from hL, hJ, hLdef, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, reassoc_of% hf']
  -- the source and the target of the pulled-back map
  let eS : ((Stacks.Coherent.coherentAdicPullback f J).obj
      ((Stacks.Coherent.coherentAdicPullback (c ∣_ S.U) (S.Yι.ker.comap S.U.ι)).obj
        (toKerSystem S F))).obj ≅
      (blowupPullbackSystem S F).obj ⋙ Scheme.Modules.pullback q :=
    eqToIso (Stacks.Coherent.coherentAdicPullback_obj_functor f J _) ≪≫
      Functor.isoWhiskerRight
        (eqToIso (Stacks.Coherent.coherentAdicPullback_obj_functor (c ∣_ S.U) _ _) ≪≫
          Functor.isoWhiskerRight (eqToIso (toKerSystem_obj S F))
            (Scheme.Modules.pullback (c ∣_ S.U))) (Scheme.Modules.pullback f) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F.obj (Scheme.Modules.pullbackComp f (c ∣_ S.U) ≪≫
        Scheme.Modules.pullbackCongr hsq ≪≫
        (Scheme.Modules.pullbackComp q (blowupRestrict S)).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (blowupPullbackSystem_obj S F).symm)
        (Scheme.Modules.pullback q)
  let eT : (G.obj ⋙ Scheme.Modules.restrictFunctor (situationBlowUpU S).ι) ⋙
      Scheme.Modules.pullback q ≅
      ((completionFunctor U'h.toScheme (J.comap f)).obj
        (restrictCoherentModules U'h.ι 𝒢)).obj :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G.obj
        (Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback _)
          (Scheme.Modules.pullback q) ≪≫
        Scheme.Modules.pullbackComp q (situationBlowUpU S).ι ≪≫
        Scheme.Modules.pullbackCongr hq' ≪≫ (Scheme.Modules.pullbackComp U'h.ι p).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (eqToIso (Stacks.Coherent.coherentAdicPullback_obj_functor p _ G).symm ≪≫ eG.symm)
        (Scheme.Modules.pullback U'h.ι) ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback U'h.ι).symm ≪≫
      completionRestrictOpenIso U'h.ι E 𝒢 ≪≫
      completionFunctorObjCongr hLJ _
  let σq := Functor.whiskerRight σ (Scheme.Modules.pullback q)
  have hσq : IsKernelCokernelAnnihilatedByPower (J.comap f) σq := by
    rw [← hIdeal]
    exact Stacks.Coherent.isKernelCokernelAnnihilatedByPower_whiskerRight_pullback q _ σ hσ
  obtain ⟨F', a, β, -⟩ := exists_unique_algebraization_of_isNoetherian (J.comap f)
    (restrictCoherentModules U'h.ι 𝒢) _ (eS.hom ≫ σq ≫ eT.hom)
    (isKernelCokernelAnnihilatedByPower_iso_comp _ eS _
      (isKernelCokernelAnnihilatedByPower_comp_iso _ σq eT hσq))
  exact ⟨F', ⟨(ObjectProperty.isoMk _ β).symm⟩⟩

end Stacks.Algebraization

end
