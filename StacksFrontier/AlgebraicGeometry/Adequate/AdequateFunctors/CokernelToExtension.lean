module

public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.Algebra.Module.Adequate.Colimit
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.FiniteFreeLift
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksCore.Tactic.StacksAttribute

/-!
# Cokernels into module functors preserve adequacy

The cokernel of a morphism from an adequate module-valued functor to a functor
associated to an ordinary module is adequate.

## Main results

* `AdequateFunctor.isAdequate_cokernel_to_moduleExtension` states that the cokernel is
  adequate.

## Implementation notes

The functor associated to a module is its extension-of-scalars functor. The
cokernel is taken in the category of module-valued functors on commutative
algebras over the base ring.

## References

* [Stacks Project, Tag 06V1](https://stacks.math.columbia.edu/tag/06V1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u v w u₁ v₁

namespace AdequateFunctor



/-- The snake input whose rows compute the cokernel of `ker f ⟶ M` from the cokernels of the
columns of the square built from `f` and `g`. -/
private noncomputable def relationSnake (C : Type u) [Category C] [Abelian C]
    {P Q M : C} (f : P ⟶ Q) (g : P ⟶ M) : ShortComplex.SnakeInput C := by
  let L1 : ShortComplex C := ShortComplex.mk (kernel.ι f) (cokernel.π (kernel.ι f)) (by simp)
  let L2 : ShortComplex C := ShortComplex.mk (biprod.inl : M ⟶ M ⊞ Q)
    (biprod.snd : M ⊞ Q ⟶ Q) (by simp)
  let v : L1 ⟶ L2 := {
    τ₁ := kernel.ι f ≫ g
    τ₂ := biprod.lift g f
    τ₃ := Abelian.factorThruCoimage f
    comm₁₂ := by apply biprod.hom_ext <;> simp [L1, L2, Category.assoc]
    comm₂₃ := by
      simp [L1, L2]
  }
  have hL1 : L1.Exact :=
    ShortComplex.exact_of_g_is_cokernel L1 (cokernelIsCokernel (kernel.ι f))
  have hL2 : L2.Exact := (ShortComplex.Splitting.ofHasBinaryBiproduct M Q).exact
  exact {
    L₀ := kernel v
    L₁ := L1
    L₂ := L2
    L₃ := cokernel v
    v₀₁ := kernel.ι v
    v₁₂ := v
    v₂₃ := cokernel.π v
    h₀ := kernelIsKernel v
    h₃ := cokernelIsCokernel v
    L₁_exact := hL1
    epi_L₁_g := by infer_instance
    L₂_exact := hL2
    mono_L₂_f := by infer_instance
  }

/-- The map from the middle cokernel of `AdequateFunctor.relationSnake` to `cokernel f`
whose kernel is the cokernel of `ker f ⟶ M`. -/
private noncomputable def relationMap {C : Type u} [Category C] [Abelian C]
    {P Q M : C} (f : P ⟶ Q) (g : P ⟶ M) : cokernel (relationSnake C f g).v₁₂.τ₂ ⟶
      cokernel f := by
  let S := relationSnake C f g
  let e₂ : cokernel (S.v₁₂.τ₂) ≅ S.L₃.X₂ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.v₁₂.τ₂) S.h₃τ₂
  let e₃ : cokernel (S.v₁₂.τ₃) ≅ S.L₃.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.v₁₂.τ₃) S.h₃τ₃
  let ec : cokernel (S.v₁₂.τ₃) ≅ cokernel f :=
    by
      change cokernel (Abelian.factorThruCoimage f) ≅ cokernel f
      exact (cokernelEpiComp (cokernel.π (kernel.ι f))
        (Abelian.factorThruCoimage f)).symm ≪≫ cokernelIsoOfEq (Abelian.coimage.fac f)
  exact e₂.hom ≫ S.L₃.g ≫ e₃.inv ≫ ec.hom

/-- The cokernel of a map from a kernel is the kernel of the relation map between the two
cokernels. This is the snake lemma applied to the split row `M → M ⊞ Q → Q`. -/
private theorem relationMap_kernel {C : Type u} [Category C] [Abelian C]
    {P Q M : C} (f : P ⟶ Q) (g : P ⟶ M) :
    Nonempty (cokernel (kernel.ι f ≫ g) ≅ kernel (relationMap f g)) := by
  let S := relationSnake C f g
  let e₂ : cokernel (S.v₁₂.τ₂) ≅ S.L₃.X₂ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.v₁₂.τ₂) S.h₃τ₂
  let e₃ : cokernel (S.v₁₂.τ₃) ≅ S.L₃.X₃ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.v₁₂.τ₃) S.h₃τ₃
  let ec : cokernel (S.v₁₂.τ₃) ≅ cokernel f :=
    by
      show cokernel (Abelian.factorThruCoimage f) ≅ cokernel f
      exact (cokernelEpiComp (cokernel.π (kernel.ι f))
        (Abelian.factorThruCoimage f)).symm ≪≫ cokernelIsoOfEq (Abelian.coimage.fac f)
  let : Mono S.v₁₂.τ₃ := by
    show Mono (Abelian.factorThruCoimage f)
    infer_instance
  let e₀ := IsLimit.conePointUniqueUpToIso (kernelIsKernel S.v₁₂.τ₃) S.h₀τ₃
  have hzero : IsZero S.L₀.X₃ := IsZero.of_iso (isZero_kernel_of_mono S.v₁₂.τ₃) e₀.symm
  have hδ : S.L₂'.f = 0 := hzero.eq_of_src _ _
  have hmono : Mono S.L₃.f := (S.L₂'.exact_iff_mono hδ).1 S.L₂'_exact
  let := hmono
  have htEpi : Epi (kernel.lift S.L₃.g S.L₃.f S.L₃.zero) :=
    (ShortComplex.exact_iff_epi_kernel_lift S.L₃).1 S.L₃_exact
  have htMono : Mono (kernel.lift S.L₃.g S.L₃.f S.L₃.zero) :=
    mono_of_mono_fac (kernel.lift_ι S.L₃.g S.L₃.f S.L₃.zero)
  let : IsIso (kernel.lift S.L₃.g S.L₃.f S.L₃.zero) := isIso_of_mono_of_epi _
  let eT : S.L₃.X₁ ≅ kernel S.L₃.g := asIso (kernel.lift S.L₃.g S.L₃.f S.L₃.zero)
  have hkernel : IsLimit (KernelFork.ofι S.L₃.f S.L₃.zero) :=
    IsKernel.isoKernel S.L₃.g S.L₃.f (kernelIsKernel S.L₃.g) eT
      (kernel.lift_ι S.L₃.g S.L₃.f S.L₃.zero)
  let et : S.L₃.X₃ ≅ cokernel f := e₃.symm ≪≫ ec
  let d := S.L₃.g ≫ et.hom
  have hdzero : S.L₃.f ≫ d = 0 := by simp [d]
  have hkerd : IsLimit (KernelFork.ofι S.L₃.f hdzero) :=
    IsKernel.ofIso S.L₃.g hkernel (KernelFork.ofι S.L₃.f hdzero)
      (Iso.refl _) et (Iso.refl _) (by simp [d]) (by simp)
  let e₁ : cokernel (S.v₁₂.τ₁) ≅ S.L₃.X₁ :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.v₁₂.τ₁) S.h₃τ₁
  let l := e₁.hom ≫ S.L₃.f
  have hldzero : l ≫ d = 0 := by simp [l, d, Category.assoc, hdzero]
  have hl : IsLimit (KernelFork.ofι l hldzero) :=
    IsKernel.isoKernel d l hkerd e₁ (by simp [l])
  let ek : kernel d ≅ kernel (e₂.hom ≫ d) :=
    kernel.mapIso d (e₂.hom ≫ d) e₂.symm (Iso.refl _) (by simp)
  exact ⟨(IsLimit.conePointUniqueUpToIso hl (kernelIsKernel d)) ≪≫ ek⟩

/-- A morphism of presheaves of modules which is an isomorphism of underlying presheaves is an
isomorphism.

`CategoryTheory.Functor.ReflectsIsomorphisms` for `PresheafOfModules.toPresheaf` is available by
instance search when the sections and the scalars share a universe, as at
`StacksFrontier.AlgebraicGeometry.Descent.Parasitic.ParasiticPushforward`; it does not fire at the
independent universes of module-valued functors, which is what this supplies. -/
public theorem toPresheaf_reflectsIsomorphisms {C : Type u₁} [Category.{v₁} C]
    {R : Cᵒᵖ ⥤ RingCat.{u}} :
    (PresheafOfModules.toPresheaf R).ReflectsIsomorphisms := by
  refine ⟨?_⟩
  intro X Y f hf
  have : IsIso ((PresheafOfModules.toPresheaf R).map f) := hf
  have hb (Z) : Function.Bijective (f.app Z) := by
    have : IsIso (((PresheafOfModules.toPresheaf R).map f).app Z) := inferInstance
    have hb' : Function.Bijective
        (fun a => (((PresheafOfModules.toPresheaf R).map f).app Z).hom a) :=
      (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
    have hfa (a : X.obj Z) :
        (((PresheafOfModules.toPresheaf R).map f).app Z) a = f.app Z a := by
      simpa using PresheafOfModules.toPresheaf_map_app_apply f Z a
    constructor
    · intro a b hab
      exact hb'.injective ((hfa a).trans (hab.trans (hfa b).symm))
    · intro b
      obtain ⟨a, ha⟩ := hb'.surjective b
      exact ⟨a, (hfa a).symm.trans ha⟩
  have hmono : Mono f := PresheafOfModules.mono_of_injective fun Z => (hb Z).injective
  have hepi : Epi f := PresheafOfModules.epi_of_surjective fun Z => (hb Z).surjective
  let : Mono f := hmono
  let : Epi f := hepi
  exact isIso_of_mono_of_epi f

/-- Extension of scalars from modules to module-valued functors preserves coproducts. -/
public theorem moduleExtension_preservesCoproduct {A : Type u} [CommRing A]
    {ι : Type (max u v w)} (F : ι → ModuleCat.{max u v w} A) :
    PreservesColimit (Discrete.functor F)
      (moduleExtensionFunctor.{max u v w, v} A) := by
  let E := moduleExtensionFunctor.{max u v w, v} A
  let R := algebraRingDiagram.{v} A
  let c := E.mapCocone (colimit.cocone (Discrete.functor F))
  refine preservesColimit_of_preserves_colimit_cocone (colimit.isColimit _) ?_
  refine PresheafOfModules.evaluationJointlyReflectsColimits
    (F := Discrete.functor F ⋙ E) c ?_
  intro X
  have : PreservesColimit (Discrete.functor F) (E ⋙ PresheafOfModules.evaluation R X) := by
    let G := ModuleCat.extendScalars
      (algebraMap A (X.unop.unop) : A →+* X.unop.unop)
    let : PreservesColimitsOfShape (Discrete ι) G :=
      (Adjunction.ofIsLeftAdjoint G).leftAdjoint_preservesColimits.preservesColimitsOfShape
    let : PreservesColimit (Discrete.functor F) G := inferInstance
    exact preservesColimit_of_natIso (Discrete.functor F)
      (moduleExtensionEvaluationIso A X).symm
  exact isColimitOfPreserves (E ⋙ PresheafOfModules.evaluation R X)
    (colimit.isColimit (Discrete.functor F))

/-- The module-valued functor of `M` agrees with that of its universe lift. -/
private noncomputable def moduleExtensionULiftIso {A : Type u} [CommRing A]
    (M : ModuleCat.{w} A) :
    moduleExtension.{w, v} A M ≅
      moduleExtension.{max u v w, v} A
        (ModuleCat.of A (ULift.{max u v} (M : Type w))) := by
  refine PresheafOfModules.isoMk (fun X => ?_) ?_
  · let B := X.unop.unop
    exact (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl B B) (ULift.moduleEquiv.{u, w, max u v} (R := A) (M := M)).symm).toModuleIso
  · intro X Y f
    ext x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul b m =>
      simp only []
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The cokernel of a map from an adequate functor to the functor of a module
is adequate. -/
@[stacks 06V1]
public theorem isAdequate_cokernel_to_moduleExtension
    (A : Type u) [CommRing A]
    (F : ModuleValuedFunctor.{max u v w, v} A)
    (M : ModuleCat.{w} A)
    (φ : F ⟶ moduleExtension.{w, v} A M)
    (hF : IsAdequate (𝟭 _) F) : IsAdequate (𝟭 _) (cokernel φ) := by
  classical
  let R := algebraRingDiagram.{v} A
  let U := presheafOfModulesUliftFunctor.{max u v, max u v w} R
  let F' := U.obj F
  let eF : F' ≅ F := presheafOfModulesUliftIso.{max u v, max u v w} R F
  obtain ⟨ι, L, hL, ⟨cover, hcover⟩⟩ :=
    exists_coproduct_linearlyAdequate_surjective (A := A) F hF
  let cover' : (∐ L) ⟶ F := cover ≫ eF.hom
  have hcover' : ∀ X, Function.Surjective (cover'.app X) := by
    intro X y
    have : Epi (eF.hom.app X) := inferInstance
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective _).mp (inferInstance : Epi (eF.hom.app X)) y
    obtain ⟨x, hx⟩ := hcover X z
    exact ⟨x, by simp [cover', hx, hz]⟩
  have hcoverEpi : Epi cover' := PresheafOfModules.epi_of_surjective hcover'
  let E := moduleExtensionFunctor.{max u v w, v} A
  let M' : ModuleCat.{max u v w} A := ModuleCat.of A (ULift.{max u v} (M : Type w))
  let eM := moduleExtensionULiftIso.{u, v, w} (A := A) M
  let φ' : F ⟶ E.obj M' := φ ≫ eM.hom
  let : (PresheafOfModules.toPresheaf R).ReflectsIsomorphisms :=
    toPresheaf_reflectsIsomorphisms
  let : HasExactColimitsOfShape (Discrete ι)
      (ModuleValuedFunctor.{max u v w, v} A) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete ι)
      (PresheafOfModules.toPresheaf R)
  choose n m f hpres using fun i =>
    (isLinearlyAdequate_iff_exists_module_map (A := A) (F := L i)).mp (hL i)
  let e (i : ι) : L i ≅ kernel (E.map (f i)) :=
    Classical.choice ((isKernelPresentation_iff (A := A) (F := L i) (f := f i)).mp (hpres i))
  let ii (i : ι) : L i ⟶ E.obj (finiteFreeModule.{max u v w} A (n i)) :=
    (e i).hom ≫ kernel.ι (E.map (f i))
  have hi (i : ι) : ii i ≫ E.map (f i) = 0 := by simp [ii]
  have hker_i (i : ι) : IsLimit (KernelFork.ofι (ii i) (hi i)) :=
    kernel.isoKernel (E.map (f i)) (ii i) (e i) (by simp [ii])
  have hmono_i (i : ι) : Mono (ii i) := mono_of_isLimit_fork (hker_i i)
  have hexact_i (i : ι) : (ShortComplex.mk (ii i) (E.map (f i)) (hi i)).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (hker_i i)
  choose ψ hψ using fun i => by
    let : Mono (ii i) := hmono_i i
    exact exists_lift_from_finite_free_kernel.{max u v w, v, u}
      (A := A) (M := (M' : Type (max u v w))) (n i) (m i) (L i) (ii i) (E.map (f i))
      ((Sigma.ι L i) ≫ cover' ≫ φ') (hi i) (hexact_i i)
  let P : ModuleCat.{max u v w} A := ∐ fun i => finiteFreeModule.{max u v w} A (n i)
  let Q : ModuleCat.{max u v w} A := ∐ fun i => finiteFreeModule.{max u v w} A (m i)
  let g₀ (i : ι) : ModuleCat.of A (finiteFreeModule.{max u v w} A (n i)) ⟶ M' :=
    moduleHomOfExtensionNatTrans.{max u v w, v, u} (ψ i)
  let g : P ⟶ M' := Sigma.desc fun i => g₀ i
  let C := ModuleValuedFunctor.{max u v w, v} A
  let D := Discrete.functor (fun i => finiteFreeModule.{max u v w} A (n i)) ⋙ E
  let G := Discrete.functor (fun i => finiteFreeModule.{max u v w} A (m i)) ⋙ E
  let α : D ⟶ G := Discrete.natTrans fun i => E.map (f i.as)
  let H := Discrete.functor L
  let eH : H ≅ kernel α := Discrete.natIso fun i =>
    let ev := (evaluation (Discrete ι) C).obj i
    let eEv := PreservesKernel.iso ev α
    e i.as ≪≫ eEv.symm
  let δ : P ⟶ Q := Sigma.desc fun i => f i ≫
    Sigma.ι (fun i => finiteFreeModule.{max u v w} A (m i)) i
  let : PreservesColimit (Discrete.functor (fun i => finiteFreeModule.{max u v w} A (n i))) E :=
    moduleExtension_preservesCoproduct.{u, v, w} (A := A)
      (fun i => finiteFreeModule.{max u v w} A (n i))
  let : PreservesColimit (Discrete.functor (fun i => finiteFreeModule.{max u v w} A (m i))) E :=
    moduleExtension_preservesCoproduct.{u, v, w} (A := A)
      (fun i => finiteFreeModule.{max u v w} A (m i))
  let eP : colimit D ≅ E.obj P :=
    (preservesColimitIso E (Discrete.functor (fun i => finiteFreeModule.{max u v w} A (n i)))).symm
  let eQ : colimit G ≅ E.obj Q :=
    (preservesColimitIso E (Discrete.functor (fun i => finiteFreeModule.{max u v w} A (m i)))).symm
  have hiP (i : Discrete ι) : colimit.ι D i ≫ eP.hom =
      E.map (Sigma.ι (fun j => finiteFreeModule.{max u v w} A (n j)) i.as) :=
    ι_preservesColimitIso_inv E _ i
  have hiQ (i : Discrete ι) : colimit.ι G i ≫ eQ.hom =
      E.map (Sigma.ι (fun j => finiteFreeModule.{max u v w} A (m j)) i.as) :=
    ι_preservesColimitIso_inv E _ i
  have hcompat : colim.map α ≫ eQ.hom = eP.hom ≫ E.map δ := by
    apply colimit.hom_ext
    intro i
    have hcol : colimit.ι D i ≫ colim.map α = α.app i ≫ colimit.ι G i :=
      ι_colimMap α i
    calc
      colimit.ι D i ≫ colim.map α ≫ eQ.hom =
          E.map (f i.as) ≫ E.map (Sigma.ι
            (fun j => finiteFreeModule.{max u v w} A (m j)) i.as) := by
        rw [← Category.assoc, hcol, Category.assoc]
        show α.app i ≫ (colimit.ι G i ≫ eQ.hom) = _
        rw [hiQ i]
        rfl
      _ = E.map (Sigma.ι (fun j => finiteFreeModule.{max u v w} A (n j)) i.as ≫ δ) := by
        have hδi : Sigma.ι (fun j => finiteFreeModule.{max u v w} A (n j)) i.as ≫ δ =
            f i.as ≫ Sigma.ι (fun j => finiteFreeModule.{max u v w} A (m j)) i.as := by
          simp [δ]
        rw [hδi, Functor.map_comp]
      _ = colimit.ι D i ≫ eP.hom ≫ E.map δ := by
        calc
          E.map (Sigma.ι (fun j => finiteFreeModule.{max u v w} A (n j)) i.as ≫ δ) =
              E.map (Sigma.ι (fun j => finiteFreeModule.{max u v w} A (n j)) i.as) ≫ E.map δ :=
            Functor.map_comp E _ _
          _ = (colimit.ι D i ≫ eP.hom) ≫ E.map δ := by rw [hiP i]
          _ = colimit.ι D i ≫ eP.hom ≫ E.map δ := by simp [Category.assoc]
  let : PreservesFiniteLimits (colim (J := Discrete ι) (C := C)) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  let : PreservesLimit (parallelPair α 0) (colim (J := Discrete ι) (C := C)) := inferInstance
  let eK := (colim.mapIso eH) ≪≫
    PreservesKernel.iso (colim (J := Discrete ι) (C := C)) α ≪≫
      kernel.mapIso (colim.map α) (E.map δ) eP eQ hcompat
  have hcoverMap : cover' ≫ φ' = eK.hom ≫ kernel.ι (E.map δ) ≫ E.map g := by
    apply colimit.hom_ext
    intro i
    have he : colimit.ι (Discrete.functor L) i ≫ eK.hom ≫ kernel.ι (E.map δ) =
        ii i.as ≫ E.map (Sigma.ι (fun j => finiteFreeModule.{max u v w} A (n j)) i.as) := by
      change colimit.ι (Discrete.functor L) i ≫ colim.map eH.hom ≫
        (PreservesKernel.iso colim α).hom ≫
        (kernel.mapIso (colimMap α) (E.map δ) eP eQ hcompat).hom ≫
        kernel.ι (E.map δ) = _
      have hmap : (kernel.mapIso (colimMap α) (E.map δ) eP eQ hcompat).hom ≫
          kernel.ι (E.map δ) = kernel.ι (colim.map α) ≫ eP.hom := by
        simp [kernel.mapIso, kernel.map]
      have hηi : eH.hom.app i ≫ (kernel.ι α).app i =
          (e i.as).hom ≫ kernel.ι (E.map (f i.as)) := by
        let ev := (evaluation (Discrete ι) C).obj i
        change (e i.as).hom ≫ (PreservesKernel.iso ev α).inv ≫ ev.map (kernel.ι α) = _
        rw [PreservesKernel.iso_inv_ι]
        rfl
      rw [← Category.assoc, colimit.ι_map, Category.assoc, Category.assoc, hmap,
        ← Category.assoc (PreservesKernel.iso colim α).hom, PreservesKernel.iso_hom,
        kernelComparison_comp_ι, colimit.ι_map_assoc, hiP i, reassoc_of% hηi]
    calc
      colimit.ι (Discrete.functor L) i ≫ cover' ≫ φ' =
          Sigma.ι L i.as ≫ cover' ≫ φ' := by rfl
      _ = ii i.as ≫ ψ i.as := (hψ i.as).symm
      _ = ii i.as ≫ E.map (g₀ i.as) := by
        have hψmap : ψ i.as = E.map (g₀ i.as) := by
          dsimp [g₀, E]
          exact moduleExtension_natTrans_eq_map (ψ i.as)
        rw [hψmap]
      _ = ii i.as ≫ E.map (Sigma.ι
          (fun j => finiteFreeModule.{max u v w} A (n j)) i.as ≫ g) := by
        have hdesc : Sigma.ι (fun j => finiteFreeModule.{max u v w} A (n j)) i.as ≫ g =
            g₀ i.as := by simp [g]
        have hcomp : E.map (g₀ i.as) = E.map (Sigma.ι
            (fun j => finiteFreeModule.{max u v w} A (n j)) i.as ≫ g) :=
          congrArg E.map hdesc.symm
        exact congrArg (fun k => ii i.as ≫ k) hcomp
      _ = (ii i.as ≫ E.map (Sigma.ι
          (fun j => finiteFreeModule.{max u v w} A (n j)) i.as)) ≫ E.map g := by
        simp only [Functor.map_comp, Category.assoc]
      _ = colimit.ι (Discrete.functor L) i ≫ eK.hom ≫ kernel.ι (E.map δ) ≫ E.map g := by
        calc
          _ = (colimit.ι (Discrete.functor L) i ≫ eK.hom ≫ kernel.ι (E.map δ)) ≫ E.map g := by
            rw [← he]
          _ = colimit.ι (Discrete.functor L) i ≫ eK.hom ≫ kernel.ι (E.map δ) ≫ E.map g := by
            simp only [Category.assoc]
  have hEpi : Epi cover' := hcoverEpi
  let eCover := cokernelEpiComp cover' φ'
  let eTarget := cokernel.mapIso φ φ' (Iso.refl _) eM (by simp [φ'])
  have eC : cokernel (cover' ≫ φ') ≅ cokernel φ := eCover ≪≫ eTarget.symm
  let v := kernel.ι (E.map δ) ≫ E.map g
  have : HasCokernel v := HasCokernels.has_colimit v
  let eDomain := cokernel.mapIso (cover' ≫ φ') v eK (Iso.refl _) (by simpa [v] using hcoverMap)
  let eRel := Classical.choice (relationMap_kernel (E.map δ) (E.map g))
  let : PreservesColimit (Discrete.functor (pairFunction M' Q)) E := by infer_instance
  let : PreservesBiproduct (pairFunction M' Q) E :=
    preservesBiproduct_of_preservesCoproduct E
  let : PreservesBinaryBiproduct M' Q E := preservesBinaryBiproduct_of_preservesBiproduct E M' Q
  let eB := E.mapBiprod M' Q
  have hB : E.map (biprod.lift g δ) ≫ eB.hom = biprod.lift (E.map g) (E.map δ) :=
    biprod.map_lift_mapBiprod E M' Q g δ
  let ePair := cokernel.mapIso (E.map (biprod.lift g δ))
    (biprod.lift (E.map g) (E.map δ)) (Iso.refl _) eB hB
  let eSrc : cokernel ((relationSnake _ (E.map δ) (E.map g)).v₁₂.τ₂) ≅
      E.obj (cokernel (biprod.lift g δ)) :=
    ePair.symm ≪≫ (moduleExtensionCokernelIso.{max u v w, v, u}
      (A := A) (biprod.lift g δ)).symm
  let eTgt : cokernel (E.map δ) ≅ E.obj (cokernel δ) :=
    (moduleExtensionCokernelIso.{max u v w, v, u} (A := A) δ).symm
  let relationNat : E.obj (cokernel (biprod.lift g δ)) ⟶ E.obj (cokernel δ) :=
    eSrc.inv ≫ relationMap (E.map δ) (E.map g) ≫ eTgt.hom
  let relationModuleMap := moduleHomOfExtensionNatTrans.{max u v w, v, u} relationNat
  have hRelationMap : relationMap (E.map δ) (E.map g) ≫ eTgt.hom =
      eSrc.hom ≫ E.map relationModuleMap := by
    have h := moduleExtension_natTrans_eq_map relationNat
    change eSrc.inv ≫ relationMap (E.map δ) (E.map g) ≫ eTgt.hom =
      E.map relationModuleMap at h
    rw [← h, Iso.hom_inv_id_assoc]
  let eKernelRelation := kernel.mapIso (relationMap (E.map δ) (E.map g))
    (E.map relationModuleMap) eSrc eTgt hRelationMap
  have hRelKernel : IsAdequate (𝟭 _) (kernel (E.map relationModuleMap)) :=
    (isAdequate_iff (kernel (E.map relationModuleMap))).2
      ⟨cokernel (biprod.lift g δ), cokernel δ, E.map relationModuleMap, ⟨Iso.refl _⟩⟩
  have hRel : IsAdequate (𝟭 _) (kernel (relationMap (E.map δ) (E.map g))) :=
    hRelKernel.of_iso eKernelRelation
  have hV : IsAdequate (𝟭 _) (cokernel v) := hRel.of_iso eRel
  exact hV.of_iso (eC.symm ≪≫ eDomain)


end AdequateFunctor
