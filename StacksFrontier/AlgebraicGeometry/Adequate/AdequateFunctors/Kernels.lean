module

public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.Cokernels
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksCore.Tactic.StacksAttribute

/-!
# Kernels of maps of adequate functors

The kernel of a morphism between adequate module-valued functors on the category of
commutative algebras over a ring is adequate.

## Main results

* `AdequateFunctor.isAdequate_kernel` states that adequate functors are closed under kernels.
* `AdequateFunctor.isAdequate_moduleExtension` states that the module-valued functor of a module
  is adequate, being the kernel of its own map to the zero finite free functor.

## Implementation notes

The source's kernel is the categorical kernel of the morphism of module-valued functors.
Thus the statement retains its canonical inclusion and universal property.

## References

* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
universe u v w s

namespace AdequateFunctor


section ProofImplementation

/-- The universe lift of `B ⊗[A] M` is `B ⊗[A] ULift M`, as `B`-modules. -/
private noncomputable def uliftTensorEquiv (A : Type u) (B : Type v) [CommRing A]
    [CommRing B] [Algebra A B] (M : Type w) [AddCommGroup M] [Module A M] :
    ULift.{s, max v w} (TensorProduct A B M) ≃ₗ[B] TensorProduct A B (ULift.{s, w} M) :=
  (ULift.moduleEquiv (R := B)).trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
      (ULift.moduleEquiv (R := A)).symm)

/-- The universe lift of the module-valued functor of `M` is the module-valued functor of the
universe lift of `M`. -/
private noncomputable def moduleExtensionUliftIso {A : Type u} [CommRing A]
    (M : ModuleCat.{w} A) :
    (presheafOfModulesUliftFunctor.{max u v, max u v w}
      (algebraRingDiagram.{v} A)).obj
        (moduleExtension.{w, v} A M) ≅
      moduleExtension.{max u v w, v} A ((ModuleCat.uliftFunctor.{max u v} A).obj M) := by
  refine PresheafOfModules.isoMk (fun X =>
    (uliftTensorEquiv A (X.unop.unop) M).toModuleIso) ?_
  intro X Y f
  dsimp [algebraRingDiagram]
  ext x
  cases x with
  | up x =>
      induction x using TensorProduct.induction_on with
      | zero => rfl
      | tmul b m =>
          change (uliftTensorEquiv A (Y.unop.unop) M)
              (ULift.up (f.unop.unop.hom b ⊗ₜ[A] m)) =
            TensorProduct.map f.unop.unop.hom.toLinearMap LinearMap.id
              (b ⊗ₜ[A] ULift.up m)
          rw [TensorProduct.map_tmul]
          rfl
      | add x y hx hy =>
          convert congrArg₂ (· + ·) hx hy using 1 <;> apply map_add

/-- The module-valued functor of a module is adequate: it is the kernel of its own map to the
zero finite free functor. -/
public lemma isAdequate_moduleExtension {A : Type u} [CommRing A]
    (M : ModuleCat.{w} A) : IsAdequate (𝟭 _) (moduleExtension.{w, v} A M) := by
  let M' : ModuleCat.{max u v w} A := (ModuleCat.uliftFunctor.{max u v} A).obj M
  let F' := moduleExtension.{max u v w, v} A M'
  let z : ModuleCat.{max u v w} A := finiteFreeModule.{max u v w} A 0
  let f : M' ⟶ z := 0
  have hf : (moduleExtensionFunctor.{max u v w, v} A).map f = 0 := by
    ext X x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => simp [f, moduleExtensionFunctor_map_app_tmul]
    | add x y hx hy => simp [hx, hy]
  refine ⟨M', z, f, ?_⟩
  show Nonempty ((presheafOfModulesUliftFunctor.{max u v, max u v w}
      (algebraRingDiagram.{v} A)).obj (moduleExtension.{w, v} A M) ≅
    kernel ((moduleExtensionFunctor.{max u v w, v} A).map f))
  exact ⟨moduleExtensionUliftIso (A := A) M ≪≫
    (kernelZeroIsoSource (X := F')
      (Y := moduleExtension.{max u v w, v} A z)).symm ≪≫
    (kernelIsoOfEq hf).symm⟩

/-- The universe lift of presheaves of modules preserves finite limits. -/
private theorem uliftPreservesFiniteLimits {A : Type u} [CommRing A] :
    PreservesFiniteLimits
      (presheafOfModulesUliftFunctor.{max u v, w} (algebraRingDiagram.{v} A)) := by
  let L : ModuleValuedFunctor.{w, v} A ⥤ ModuleValuedFunctor.{max w (max u v), v} A :=
    presheafOfModulesUliftFunctor.{max u v, w} (algebraRingDiagram.{v} A)
  refine ⟨fun J _ _ => { preservesLimit := ?_ }⟩
  intro D
  refine { preserves := ?_ }
  intro c hc
  refine ⟨PresheafOfModules.evaluationJointlyReflectsLimits (D ⋙ L) (L.mapCone c) ?_⟩
  intro X
  have h₁ : IsLimit ((PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X).mapCone c) :=
    isLimitOfPreserves _ hc
  have h₂ : IsLimit ((ModuleCat.uliftFunctor.{max u v, w}
      ((algebraRingDiagram.{v} A).obj X)).mapCone
        ((PresheafOfModules.evaluation (algebraRingDiagram.{v} A) X).mapCone c)) :=
    isLimitOfPreserves _ h₁
  exact IsLimit.ofIsoLimit h₂ (Cone.ext (Iso.refl _) (by intro j; rfl))

/-- The universe lift of a kernel is the kernel of the universe lift. -/
private noncomputable def uliftKernelIso {A : Type u} [CommRing A]
    {F G : ModuleValuedFunctor.{w, v} A} (f : F ⟶ G) :
    (presheafOfModulesUliftFunctor.{max u v, w}
      (algebraRingDiagram.{v} A)).obj (kernel f) ≅
      kernel ((presheafOfModulesUliftFunctor.{max u v, w}
        (algebraRingDiagram.{v} A)).map f) := by
  let L := presheafOfModulesUliftFunctor.{max u v, w} (algebraRingDiagram.{v} A)
  letI : PreservesFiniteLimits L := uliftPreservesFiniteLimits (A := A)
  exact PreservesKernel.iso L f


/-- The kernel of a map of adequate module-valued functors is adequate. -/
@[stacks 06V3]
public lemma isAdequate_kernel {A : Type u} [CommRing A]
    {F G : ModuleValuedFunctor.{w, v} A} (φ : F ⟶ G)
    (hF : IsAdequate (𝟭 _) F) (hG : IsAdequate (𝟭 _) G) :
    IsAdequate (𝟭 _) (kernel φ) := by
  let L := presheafOfModulesUliftFunctor.{max u v, w} (algebraRingDiagram.{v} A)
  let F' := L.obj F
  let G' := L.obj G
  let φ' := L.map φ
  obtain ⟨M, N, f, ⟨eF₀⟩⟩ := hF
  obtain ⟨M', N', g, ⟨eG₀⟩⟩ := hG
  let E := moduleExtensionFunctor.{max u v w, v} A
  have hFpres : IsKernelPresentation (𝟭 _) F' f := ⟨
    (presheafOfModulesUliftIso.{max u v, max u v w}
      (algebraRingDiagram.{v} A) F') ≪≫ eF₀⟩
  have hGpres : IsKernelPresentation (𝟭 _) G' g := ⟨
    (presheafOfModulesUliftIso.{max u v, max u v w}
      (algebraRingDiagram.{v} A) G') ≪≫ eG₀⟩
  have hFadequate : IsAdequate (𝟭 _) F' := ⟨M, N, f, hFpres⟩
  obtain ⟨eF⟩ := (isKernelPresentation_iff F' f).mp hFpres
  obtain ⟨eG⟩ := (isKernelPresentation_iff G' g).mp hGpres
  let : PreservesBinaryBiproduct M M' E :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct E
  let uF : F' ⟶ E.obj M := eF.hom ≫ kernel.ι (E.map f)
  let uG : G' ⟶ E.obj M' := eG.hom ≫ kernel.ι (E.map g)
  let P := M ⊞ M'
  let eP := Functor.mapBiprod E M M'
  let graph : F' ⟶ E.obj M ⊞ E.obj M' := biprod.lift uF (φ' ≫ uG)
  let j : F' ⟶ E.obj P := graph ≫ eP.inv
  have eP_fst : eP.hom ≫ biprod.fst = E.map biprod.fst := by
    show (Functor.mapBiprod E M M').hom ≫ biprod.fst = E.map biprod.fst
    rw [Functor.mapBiprod_hom]
    simp
  have eP_snd : eP.hom ≫ biprod.snd = E.map biprod.snd := by
    show (Functor.mapBiprod E M M').hom ≫ biprod.snd = E.map biprod.snd
    rw [Functor.mapBiprod_hom]
    simp
  have eP_inv_fst : eP.inv ≫ E.map biprod.fst = biprod.fst := by
    rw [← eP_fst, Iso.inv_hom_id_assoc]
  have eP_inv_snd : eP.inv ≫ E.map biprod.snd = biprod.snd := by
    rw [← eP_snd, Iso.inv_hom_id_assoc]
  have hj_fst : j ≫ E.map biprod.fst = uF := by
    dsimp [j, graph]
    rw [Category.assoc, eP_inv_fst]
    simp
  have hj_snd : j ≫ E.map biprod.snd = φ' ≫ uG := by
    dsimp [j, graph]
    rw [Category.assoc, eP_inv_snd]
    simp
  have : Mono uF := inferInstance
  have : Mono uG := inferInstance
  have : Mono j := by
    refine ⟨?_⟩
    intro X a b hab
    have hh := congrArg (fun q => q ≫ E.map biprod.fst) hab
    have hu : a ≫ uF = b ≫ uF := by
      rw [← hj_fst]
      simpa only [Category.assoc] using hh
    exact (cancel_mono uF).1 hu
  let cokerCofork := CokernelCofork.ofπ (cokernel.π j) (cokernel.condition j)
  let hJ : IsLimit (KernelFork.ofι j (CokernelCofork.condition cokerCofork)) :=
    Abelian.monoIsKernelOfCokernel cokerCofork (cokernelIsCokernel j)
  have hP : IsAdequate (𝟭 _) (E.obj P) := isAdequate_moduleExtension (A := A) P
  let hQ := isAdequate_cokernel j hFadequate hP
  obtain ⟨K, T, k, ⟨eQ⟩⟩ := hQ
  let qLift := presheafOfModulesUliftIso.{max u v, max u v w}
    (algebraRingDiagram.{v} A) (cokernel j)
  let m : cokernel j ⟶ E.obj K := qLift.inv ≫ eQ.hom ≫ kernel.ι (E.map k)
  have : Mono qLift.inv := inferInstance
  have : Mono eQ.hom := inferInstance
  have : Mono (kernel.ι (E.map k)) := inferInstance
  have : Mono m := ⟨fun {X} a b h => by
    apply (cancel_mono qLift.inv).1
    apply (cancel_mono eQ.hom).1
    apply (cancel_mono (kernel.ι (E.map k))).1
    change a ≫ (qLift.inv ≫ eQ.hom ≫ kernel.ι (E.map k)) =
      b ≫ (qLift.inv ≫ eQ.hom ≫ kernel.ι (E.map k)) at h
    rwa [← Category.assoc, ← Category.assoc] at h⟩
  let t : E.obj P ⟶ E.obj K := cokernel.π j ≫ m
  have hT : IsLimit (KernelFork.ofι j (show j ≫ t = 0 by simp [t])) :=
    isKernelCompMono hJ m rfl
  obtain ⟨κ, hκ⟩ := Functor.Full.map_surjective (F := E) t
  let H : P ⟶ K ⊞ M' := biprod.lift κ biprod.snd
  let : PreservesBinaryBiproduct K M' E :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct E
  let eH := Functor.mapBiprod E K M'
  let j₂ : E.obj P ⟶ E.obj K ⊞ E.obj M' :=
    biprod.lift t (E.map biprod.snd)
  have hE : E.map H ≫ eH.hom = j₂ := by
    simpa [eH, H, j₂, hκ] using (biprod.map_lift_mapBiprod E K M' κ biprod.snd)
  let η : kernel φ' ⟶ E.obj P := kernel.ι φ' ≫ j
  have hη : η ≫ j₂ = 0 := by
    apply biprod.hom_ext
    · simp [η, j₂, Category.assoc, t]
    · simp [η, j₂, Category.assoc, hj_snd]
  have hs₁ (s : Fork j₂ 0) : s.ι ≫ t = 0 := by
    calc
      s.ι ≫ t = s.ι ≫ j₂ ≫ biprod.fst := by simp [j₂]
      _ = 0 := by
        rw [← Category.assoc, Fork.condition]
        simp
  have hs₂ (s : Fork j₂ 0) : s.ι ≫ E.map biprod.snd = 0 := by
    calc
      s.ι ≫ E.map biprod.snd = s.ι ≫ j₂ ≫ biprod.snd := by simp [j₂]
      _ = 0 := by
        rw [← Category.assoc, Fork.condition]
        simp
  let factorToF (s : Fork j₂ 0) : s.pt ⟶ F' :=
    hT.lift (KernelFork.ofι s.ι (hs₁ s))
  have factorToF_comp (s : Fork j₂ 0) : factorToF s ≫ j = s.ι := Fork.IsLimit.lift_ι hT
  have factorToF_phi (s : Fork j₂ 0) : factorToF s ≫ φ' = 0 := by
    have hz : factorToF s ≫ φ' ≫ uG = 0 := by
      rw [← hj_snd, ← Category.assoc, factorToF_comp, hs₂ s]
    exact (cancel_mono uG).1 (by simpa using hz)
  let liftPair (s : Fork j₂ 0) : s.pt ⟶ kernel φ' :=
    kernel.lift φ' (factorToF s) (factorToF_phi s)
  have liftPair_comp (s : Fork j₂ 0) : liftPair s ≫ η = s.ι := by
    show kernel.lift φ' (factorToF s) (factorToF_phi s) ≫ kernel.ι φ' ≫ j = s.ι
    rw [kernel.lift_ι_assoc, factorToF_comp]
  have hPair : IsLimit (KernelFork.ofι η hη) := by
    refine Fork.IsLimit.mk _ liftPair (fun s => liftPair_comp s) ?_
    intro s a ha
    apply (cancel_mono (kernel.ι φ')).1
    apply (cancel_mono j).1
    calc
      a ≫ kernel.ι φ' ≫ j = s.ι := by simpa [η, Category.assoc] using ha
      _ = liftPair s ≫ kernel.ι φ' ≫ j := by
        symm
        simpa [η, Category.assoc] using liftPair_comp s
  let hFinal := IsKernel.ofCompIso (f := j₂) (l := E.map H) eH hE hPair
  let eKernel := (uliftKernelIso (A := A) φ).trans
    (hFinal.conePointUniqueUpToIso (kernelIsKernel (E.map H)))
  refine ⟨P, K ⊞ M', H, ?_⟩
  show Nonempty ((presheafOfModulesUliftFunctor.{max u v, w}
    (algebraRingDiagram.{v} A)).obj (kernel φ) ≅ kernel (E.map H))
  exact ⟨eKernel⟩

end ProofImplementation


end AdequateFunctor
