module

public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.CokernelToExtension
public import StacksCore.CategoryTheory.Abelian.CommSq
public import StacksCore.Tactic.StacksAttribute

/-!
# Cokernels of adequate module-valued functors

The cokernel of a morphism between adequate module-valued functors on the category of
commutative algebras over a ring is adequate.

## Main results

* `AdequateFunctor.isAdequate_cokernel` states that adequate functors are closed under cokernels.

## Implementation notes

The cokernel is the categorical cokernel in the category of module-valued functors, so its
canonical quotient map and universal property are retained.

## References

* [Stacks Project, Tag 06V2](https://stacks.math.columbia.edu/tag/06V2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
universe u v w u₁ v₁ w'

namespace AdequateFunctor


/-- An adequate functor embeds into the module-valued functor of some module. -/
private lemma adequate_has_mono_into_moduleExtension
    {A : Type u} [CommRing A] {F : ModuleValuedFunctor.{max u v w, v} A}
    (hF : IsAdequate.{max u v w, v} (A := A) (𝟭 _) F) :
    ∃ (M : ModuleCat.{max u v w} A)
      (i : F ⟶ moduleExtension.{max u v w, v} A M), Mono i := by
  obtain ⟨M, N, f, ⟨e⟩⟩ := (isAdequate_iff F).mp hF
  exact ⟨M, e.hom ≫ kernel.ι f, inferInstance⟩

/-- Adequacy is preserved by the universe lift of a module-valued functor. -/
private lemma adequate_ulift
    {A : Type u} [CommRing A] {F : ModuleValuedFunctor.{w, v} A}
    (hF : IsAdequate.{w, v} (A := A) (𝟭 _) F) :
    IsAdequate.{max u v w, v} (A := A) (𝟭 _)
      ((presheafOfModulesUliftFunctor.{max u v, w}
        (algebraRingDiagram A)).obj F) := by
  rcases hF with ⟨M, N, f, ⟨e⟩⟩
  let E := presheafOfModulesUliftFunctor.{max u v, w}
    (algebraRingDiagram A)
  exact ⟨M, N, f, ⟨(presheafOfModulesUliftIso.{max u v}
    (algebraRingDiagram A) (E.obj F)).trans e⟩⟩

/-- The universe lift of presheaves of modules preserves the cokernel of a given morphism. -/
private lemma presheafUlift_preserves_cokernel
    {A : Type u} [CommRing A]
    {F G : ModuleValuedFunctor.{w, v} A} (f : F ⟶ G) :
    PreservesColimit (parallelPair f 0)
      (presheafOfModulesUliftFunctor.{w', w}
        (algebraRingDiagram A)) := by
  let R := algebraRingDiagram A
  let E := presheafOfModulesUliftFunctor.{w', w} R
  let c := E.mapCocone (CokernelCofork.ofπ (cokernel.π f) (cokernel.condition f))
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
  refine PresheafOfModules.evaluationJointlyReflectsColimits
    (F := parallelPair f 0 ⋙ E) c ?_
  intro X
  have : PreservesColimit (parallelPair f 0)
      (E ⋙ PresheafOfModules.evaluation R X) := by
    change PreservesColimit (parallelPair f 0)
      (PresheafOfModules.evaluation R X ⋙ ModuleCat.uliftFunctor.{w', w} (R.obj X))
    infer_instance
  exact isColimitOfPreserves (E ⋙ PresheafOfModules.evaluation R X)
    (cokernelIsCokernel f)

/-- Cokernels of morphisms between adequate functors are adequate. -/
@[stacks 06V2]
public lemma isAdequate_cokernel {A : Type u} [CommRing A]
    {F G : ModuleValuedFunctor.{w, v} A} (φ : F ⟶ G)
    (hF : IsAdequate (𝟭 _) F) (hG : IsAdequate (𝟭 _) G) :
    IsAdequate (𝟭 _) (cokernel φ) := by
  let E := presheafOfModulesUliftFunctor.{max u v, w}
    (algebraRingDiagram A)
  have hG' : IsAdequate.{max u v w, v} (A := A) (𝟭 _) (E.obj G) := adequate_ulift hG
  let φ' : E.obj F ⟶ E.obj G := E.map φ
  obtain ⟨M, iG, hiG⟩ := adequate_has_mono_into_moduleExtension hG'
  let ψ₁ : E.obj F ⟶ moduleExtension.{max u v w, v} A M := φ' ≫ iG
  obtain ⟨N, iW, hiW⟩ := adequate_has_mono_into_moduleExtension
    (isAdequate_cokernel_to_moduleExtension A (E.obj F) M ψ₁ (adequate_ulift hF))
  let a : cokernel φ' ⟶ cokernel ψ₁ :=
    cokernel.map φ' ψ₁ (𝟙 _) iG (by simp [ψ₁])
  let q : cokernel φ' ⟶ moduleExtension.{max u v w, v} A N := a ≫ iW
  let : Mono q := by dsimp [q]; infer_instance
  let ψ : E.obj G ⟶ moduleExtension.{max u v w, v} A N :=
    cokernel.π φ' ≫ q
  obtain ⟨P, m, hm⟩ := adequate_has_mono_into_moduleExtension
    (isAdequate_cokernel_to_moduleExtension A (E.obj G) N ψ hG')
  let fQ : moduleExtension.{max u v w, v} A N ⟶
      moduleExtension.{max u v w, v} A P := cokernel.π ψ ≫ m
  let fac : StrongEpiMonoFactorisation ψ :=
    StrongEpiMonoFactorisation.mk
      (MonoFactorisation.mk (cokernel φ') q (cokernel.π φ') (by simp [ψ, q]))
  have hKImg : IsLimit (KernelFork.ofι (f := fQ) (Abelian.image.ι ψ)
      (by simp [Abelian.image, fQ])) := by
    refine Fork.IsLimit.mk _ (fun s => kernel.lift (cokernel.π ψ) s.ι ?_) ?_ ?_
    · exact (cancel_mono m).1 (by simp [fQ, Category.assoc])
    · intro s; simp [Abelian.image, fQ]
    · intro s k hk
      exact (cancel_mono (Abelian.image.ι ψ)).1 (by simpa [Abelian.image] using hk)
  let eK : cokernel φ' ≅ kernel fQ :=
    (IsImage.isoExt fac.toMonoIsImage
      (Abelian.imageStrongEpiMonoFactorisation ψ).toMonoIsImage).trans <|
      IsLimit.conePointUniqueUpToIso
      (s := KernelFork.ofι (Abelian.image.ι ψ) (by simp [Abelian.image, fQ]))
      (t := KernelFork.ofι (kernel.ι fQ) (kernel.condition fQ))
      hKImg (kernelIsKernel fQ)
  have : PreservesColimit (parallelPair φ 0) E :=
    presheafUlift_preserves_cokernel (A := A) φ
  let eQ : E.obj (cokernel φ) ≅ cokernel φ' := PreservesCokernel.iso E φ
  refine ⟨N, P, moduleHomOfExtensionNatTrans fQ, ?_⟩
  change Nonempty (E.obj (cokernel φ) ≅
    kernel ((moduleExtensionFunctor.{max u v w, v} A).map
      (moduleHomOfExtensionNatTrans fQ)))
  refine ⟨?_⟩
  simpa only [← moduleExtension_natTrans_eq_map fQ] using
    (eQ.trans eK)


end AdequateFunctor
