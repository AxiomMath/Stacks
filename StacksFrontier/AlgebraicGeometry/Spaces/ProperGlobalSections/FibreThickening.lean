module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.AdicSectionsTower
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitEqualizerTorsion
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleKer
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperGlobalSections.Finiteness
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk

/-!
# The fibres of a proper algebraic space over the infinitesimal neighbourhoods of a closed subscheme

Let `V` be an affine object of the big fppf site over `S`, `A = Γ(V, 𝒪_V)`, `I ⊆ A` an ideal and
`f : X ⟶ V` a morphism of algebraic spaces.  The closed subscheme `Spec (A / Iⁿ) ⊆ V`
(`AlgebraicGeometry.Space.adicCompletionQuotientObj`) is a closed subspace of the algebraic space
represented by `V`, and its inverse image `X ×_V Spec (A / Iⁿ)` is a closed subspace of `X`.  This
file identifies the sheaf of ideals of that closed subspace with the kernel of
`𝒪_X ⟶ 𝒪_X / Iⁿ 𝒪_X`, the quotient of the theorem on formal functions.

## Main definitions

* `AlgebraicGeometry.Space.adicQuotientSubspace`: `Spec (A / Iⁿ)` as a closed subspace of `V`.
* `AlgebraicGeometry.Space.fibreThickening`: its inverse image `X ×_V Spec (A / Iⁿ)` in `X`.
* `AlgebraicGeometry.Space.idealKernel`: the kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X`, as a sheaf of
  ideals.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_adicQuotientSubspace`: the ideal of
  `Spec (A / Iⁿ)` on the identity chart of `V` is `Iⁿ`.
* `AlgebraicGeometry.Space.definingIdealAt_fibreThickening`: on an affine étale chart `U` of
  `X` the ideal of `X ×_V Spec (A / Iⁿ)` is the extension of `Iⁿ` to `𝒪(U)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Subspace

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))

/-- `Spec (A / Iⁿ)` as a closed subspace of the algebraic space represented by `V`. -/
def adicQuotientSubspace (n : ℕ) : ClosedSubspaces B S hS (yoneda.obj V) :=
  ⟨Subfunctor.range (yoneda.map (adicCompletionQuotientObjHom B S hS V I n)),
    isClosedSubspace_range_yoneda_map B S hS _ inferInstance⟩

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] in
/-- The kernel of pullback of functions along a morphism `s : P ⟶ V` of the site through which
`yoneda.map s` factors as an isomorphism onto the range of a monomorphism `yoneda.map j`, followed
by the inclusion, is the kernel of pullback along `j`. -/
theorem ker_Γ_map_eq_of_range_iso {W P : BigFppfOver B S hS} (j : W ⟶ V) [Mono (yoneda.map j)]
    (s : P ⟶ V) (t : yoneda.obj P ⟶ (Subfunctor.range (yoneda.map j)).toFunctor) (ht : IsIso t)
    (h : t ≫ (Subfunctor.range (yoneda.map j)).ι = yoneda.map s) :
    RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map s).op).hom =
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map j).op).hom := by
  let e := t ≫ inv (Subfunctor.toRange (yoneda.map j))
  have hr : inv (Subfunctor.toRange (yoneda.map j)) ≫ yoneda.map j =
      (Subfunctor.range (yoneda.map j)).ι := by
    rw [IsIso.inv_comp_eq, Subfunctor.toRange_ι]
  have he : yoneda.map s = e ≫ yoneda.map j := by
    show _ = (t ≫ inv (Subfunctor.toRange (yoneda.map j))) ≫ yoneda.map j
    rw [Category.assoc, hr, h]
  have hsnd : s = yoneda.preimage e ≫ j := yoneda.map_injective (he.trans (by simp))
  have : IsIso e := by dsimp only [e]; infer_instance
  have : IsIso (yoneda.map (yoneda.preimage e)) := by rw [Functor.map_preimage]; infer_instance
  have : IsIso (yoneda.preimage e) := isIso_of_fully_faithful yoneda _
  rw [hsnd, Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp,
    RingHom.ker_comp_of_injective _
      (ConcreteCategory.bijective_of_isIso (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage e)).op)).1]

/-- **The ideal of `Spec (A / Iⁿ)` on the identity chart of `V` is `Iⁿ`.** -/
theorem definingIdealAt_adicQuotientSubspace (n : ℕ) :
    definingIdealAt B S hS (schemeSpace V) (adicQuotientSubspace V I n)
      (op (idEtaleChart B S hS V)) = I ^ n := by
  refine (definingIdealAt_eq_ker B S hS (schemeSpace V) (adicQuotientSubspace V I n)
    (idEtaleChart B S hS V)).trans ?_
  have : Mono (adicCompletionQuotientObjHom B S hS V I n) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have hP := (adicQuotientSubspace V I n).2.2.rep.isPullback (idEtaleChart B S hS V).1.hom
  have : IsIso (idEtaleChart B S hS V).1.hom := inferInstanceAs (IsIso (𝟙 (yoneda.obj V)))
  refine (ker_Γ_map_eq_of_range_iso V (adicCompletionQuotientObjHom B S hS V I n) _ _
    hP.isIso_fst_of_isIso (hP.w.trans (Category.comp_id _))).trans ?_
  rw [Scheme.Γ_map_op]
  exact ker_appTop_adicCompletionQuotientObjHom (V := V) (K := I) n

variable {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V)

/-- **The fibre `X ×_V Spec (A / Iⁿ)`**, as the closed subspace of `X` inverse image of
`Spec (A / Iⁿ) ⊆ V`. -/
abbrev fibreThickening (n : ℕ) : ClosedSubspaces B S hS X.1 :=
  preimageSubspace B S hS f (adicQuotientSubspace V I n)

/-- **The ideal of `X ×_V Spec (A / Iⁿ)` on an affine étale chart** `U` of `X` is the extension
of `Iⁿ` along `Γ(V) ⟶ Γ(U)`. -/
theorem definingIdealAt_fibreThickening (n : ℕ) (U : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left)] :
    definingIdealAt B S hS X (fibreThickening V I f n) (op U) =
      Ideal.map ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (U.1.hom ≫ f.hom))).appTop.hom (I ^ n) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (idEtaleChart B S hS V).1.left) :=
    inferInstanceAs (IsAffine ((BigFppfOver.toScheme B S hS).obj V))
  rw [definingIdealAt_preimage_eq_map B S hS f (adicQuotientSubspace V I n)
    (idEtaleChart B S hS V) U (yoneda.preimage (U.1.hom ≫ f.hom))
    (by rw [Functor.map_preimage]; exact Category.comp_id _),
    definingIdealAt_adicQuotientSubspace]
  rfl

end Subspace

section IdealKernel

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {X : AlgebraicSpaces B S hS} {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)))) (J : Ideal A)

/-- Evaluation of the functions `φ a` on an étale chart `U`. -/
abbrev idealChartEval (U : SmallEtale B S hS X.1) :
    A →+* ToType ((structureRingSheaf B S hS X).obj.obj (op U)) :=
  (globalSectionEval _ (op U)).comp φ

/-- **The kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X`**, as a sheaf of ideals of `𝒪_X`. -/
def idealKernel : (structureSheafModule B S hS X).Submodule :=
  SheafOfModules.Submodule.ker (idealQuotientπ φ (structureSheafModule B S hS X) J)

/-- The inclusion `J 𝒪_X ⟶ 𝒪_X` factors through the kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X`. -/
def idealMultipleToKernel :
    idealMultiple φ (structureSheafModule B S hS X) J ⟶ (idealKernel φ J).toSheafOfModules :=
  (idealKernel φ J).factorThru (idealMultipleι φ (structureSheafModule B S hS X) J) fun U x =>
    (SheafOfModules.Submodule.mem_ker _ U _).2 (by
      change ((idealMultipleι φ (structureSheafModule B S hS X) J) ≫
        idealQuotientπ φ (structureSheafModule B S hS X) J).val.app U x = 0
      rw [idealMultipleι_idealQuotientπ]
      rfl)

/-- The factorisation `J 𝒪_X ⟶ ker (𝒪_X ⟶ 𝒪_X / J 𝒪_X)` composed with the inclusion of the kernel
is the inclusion `J 𝒪_X ⟶ 𝒪_X`. -/
@[reassoc (attr := simp)]
theorem idealMultipleToKernel_ι :
    idealMultipleToKernel φ J ≫ (idealKernel φ J).ι =
      idealMultipleι φ (structureSheafModule B S hS X) J :=
  (idealKernel φ J).factorThru_ι _ _

/-- The kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X` factors through `J 𝒪_X`. -/
def kernelToIdealMultiple :
    (idealKernel φ J).toSheafOfModules ⟶ idealMultiple φ (structureSheafModule B S hS X) J :=
  haveI := (idealShortComplex_shortExact φ (structureSheafModule B S hS X) J).mono_f
  ((idealShortComplex_shortExact φ (structureSheafModule B S hS X) J).exact.fIsKernel).lift
    (KernelFork.ofι (idealKernel φ J).ι (SheafOfModules.Submodule.ker_ι_comp _))

/-- The factorisation `ker (𝒪_X ⟶ 𝒪_X / J 𝒪_X) ⟶ J 𝒪_X` composed with the inclusion `J 𝒪_X ⟶ 𝒪_X`
is the inclusion of the kernel. -/
@[reassoc (attr := simp)]
theorem kernelToIdealMultiple_ι :
    kernelToIdealMultiple φ J ≫ idealMultipleι φ (structureSheafModule B S hS X) J =
      (idealKernel φ J).ι :=
  have := (idealShortComplex_shortExact φ (structureSheafModule B S hS X) J).mono_f
  ((idealShortComplex_shortExact φ (structureSheafModule B S hS X) J).exact.fIsKernel).fac _
    WalkingParallelPair.zero

/-- `J 𝒪_X` is the kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X`. -/
def idealKernelIso :
    (idealKernel φ J).toSheafOfModules ≅ idealMultiple φ (structureSheafModule B S hS X) J where
  hom := kernelToIdealMultiple φ J
  inv := idealMultipleToKernel φ J
  hom_inv_id := (cancel_mono (idealKernel φ J).ι).1 (by
    rw [Category.assoc, idealMultipleToKernel_ι, kernelToIdealMultiple_ι, Category.id_comp])
  inv_hom_id := (cancel_mono (idealMultipleι φ (structureSheafModule B S hS X) J)).1 (by
    rw [Category.assoc, kernelToIdealMultiple_ι, idealMultipleToKernel_ι, Category.id_comp])

/-- The kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X` is quasi-coherent. -/
theorem isQuasicoherentOnSite_idealKernel :
    (idealKernel φ J).toSheafOfModules.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso (idealKernelIso φ J).symm
    (isQuasicoherentOnSite_idealMultiple φ _ J inferInstance)

/-- **The sections of `ker (𝒪_X ⟶ 𝒪_X / J 𝒪_X)` over an affine étale chart `U` are the extension
of `J` to `𝒪(U)`.** -/
theorem mem_idealKernel_iff_of_isAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (x : ToType ((structureRingSheaf B S hS X).obj.obj (op U))) :
    x ∈ (idealKernel φ J).obj (op U) ↔ x ∈ Ideal.map (idealChartEval φ U) J := by
  have hsmul : ∀ (a : A) (t : ToType ((structureRingSheaf B S hS X).obj.obj (op U))),
      (globalSmul _ (φ a) (structureSheafModule B S hS X)).val.app (op U) t =
        t * idealChartEval φ U a := fun a t => (globalSmul_app _ _ _ _ _).trans
    (mul_comm (G := (smallEtaleRingedSite B S hS X.1 X.2).O.obj.obj (op U)) ((φ a).1 (op U)) t)
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · let x' : (idealKernel φ J).toSheafOfModules.val.obj (op U) := ⟨x, hx⟩
    have hx' : x = (idealMultipleι φ (structureSheafModule B S hS X) J).val.app (op U)
        ((kernelToIdealMultiple φ J).val.app (op U) x') := by
      show x = ((kernelToIdealMultiple φ J) ≫
        idealMultipleι φ (structureSheafModule B S hS X) J).val.app (op U) x'
      rw [kernelToIdealMultiple_ι]
      rfl
    have hmem := (Submodule.eq_top_iff'.1 (span_idealMultipleFactor_sections φ
      (structureSheafModule B S hS X) J inferInstance U hU))
      ((kernelToIdealMultiple φ J).val.app (op U) x')
    rw [hx']
    refine Submodule.span_induction (p := fun y _ =>
      (idealMultipleι φ (structureSheafModule B S hS X) J).val.app (op U) y ∈
        Ideal.map (idealChartEval φ U) J) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨a, ha, t, rfl⟩
      have h1 : (idealMultipleι φ (structureSheafModule B S hS X) J).val.app (op U)
          ((idealMultipleFactor φ (structureSheafModule B S hS X) J ha).val.app (op U) t) =
          (globalSmul _ (φ a) (structureSheafModule B S hS X)).val.app (op U) t := by
        rw [← idealMultipleFactor_ι φ _ J ha]
        rfl
      rw [h1]
      exact (congrArg (fun z => z ∈ Ideal.map (idealChartEval φ U) J) (hsmul a t)).mpr
        (Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (idealChartEval φ U) ha))
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro y z _ _ hy hz
      rw [map_add]
      exact Submodule.add_mem _ hy hz
    · intro r y _ hy
      rw [map_smul]
      exact Submodule.smul_mem _ r hy
  · refine (Ideal.map_le_iff_le_comap.2 fun a ha => ?_) hx
    refine (SheafOfModules.Submodule.mem_ker _ (op U) _).2 ?_
    have h : (globalSmul _ (φ a) (structureSheafModule B S hS X) ≫
        idealQuotientπ φ (structureSheafModule B S hS X) J).val.app (op U)
          (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op U))) = 0 := by
      rw [← comp_globalSmul, globalSmul_idealQuotient_eq_zero φ _ J ha, comp_zero]
      rfl
    have h2 := (hsmul a 1).trans (one_mul (idealChartEval φ U a))
    exact (congrArg (fun y => (idealQuotientπ φ (structureSheafModule B S hS X) J).val.app (op U) y)
      h2.symm).trans h

end IdealKernel

section PullbackCompatibility

variable (V : BigFppfOver B S hS)

/-- **Restriction of functions along a morphism of algebraic spaces over `V` is compatible with
the pullback of functions from `V`**: `g^♯ ∘ f^* = (g ≫ f)^*` on `Γ(V)`. -/
theorem globalSectionsRingHomSite_comp_pullbackRingHom {X Y : AlgebraicSpaces B S hS}
    (g : X ⟶ Y) (f : Y ⟶ schemeSpace V) :
    (globalSectionsRingHomSite B S hS g).comp (pullbackRingHom B V f) =
      pullbackRingHom B V (g ≫ f) := by
  ext a : 1
  apply Subtype.ext
  funext U
  obtain ⟨W, q, hqsurj, hqet⟩ := Y.2.exists_atlas
  have hrep := hqet.1
  have hpb := hrep.isPullback' (U.unop.1.hom ≫ g.hom)
  have hsnd_et := hqet.2 _ _ _ hpb
  set k := U.unop.1.hom ≫ g.hom
  let PC : SmallEtale B S hS X.1 :=
    chartFromEtaleHom B S hS X (hrep.pullback k)
      (yoneda.map (hrep.snd k) ≫ U.unop.1.hom)
      (chart_preimage_etale B S hS X U.unop.1.hom U.unop.2 (hrep.snd k) hsnd_et)
  let d : ChartDiagram B S hS X.1 Y.1 g.hom :=
    ⟨PC, ⟨CostructuredArrow.mk q, hqet⟩, hrep.fst' k, by
      show (yoneda.map (hrep.snd k) ≫ U.unop.1.hom) ≫ g.hom = yoneda.map (hrep.fst' k) ≫ q
      rw [Category.assoc]
      exact hpb.w.symm⟩
  let ι : PC ⟶ U.unop := ObjectProperty.homMk (CostructuredArrow.homMk (hrep.snd k) rfl)
  have hL : (((globalSectionsRingHomSite B S hS g).comp (pullbackRingHom B V f)) a).1 (op PC) =
      (pullbackRingHom B V (g ≫ f) a).1 (op PC) := by
    rw [RingHom.comp_apply,
      globalSectionsRingHomSite_val_chartDiagram B S hS g (pullbackRingHom B V f a) d]
    show (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hrep.fst' k)).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (q ≫ f.hom))).op).hom a) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage ((yoneda.map (hrep.snd k) ≫ U.unop.1.hom) ≫ (g ≫ f).hom))).op).hom a
    have hpre : yoneda.preimage ((yoneda.map (hrep.snd k) ≫ U.unop.1.hom) ≫ (g ≫ f).hom) =
        hrep.fst' k ≫ yoneda.preimage (q ≫ f.hom) := by
      refine yoneda.map_injective ?_
      simp only [Functor.map_comp, Functor.map_preimage]
      exact (((Category.assoc _ _ _).trans (congrArg (yoneda.map (hrep.snd k) ≫ ·)
        (Category.assoc _ _ _).symm)).trans (Category.assoc _ _ _).symm).trans
        ((congrArg (· ≫ f.hom) (hrep.w k).symm).trans (Category.assoc _ _ _))
    rw [hpre, Functor.map_comp, op_comp, Functor.map_comp, CommRingCat.hom_comp]
    rfl
  have compat : ∀ x : RingCat.sectionsSubring (structureRingSheaf B S hS X).obj,
      x.1 (op PC) = (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (hrep.snd k)).op).hom (x.1 U) := fun x => (x.2 ι.op).symm
  exact gamma_injective_of_etale_surjection B S hS (hrep.snd k) (hqsurj.2 _ _ _ hpb) hsnd_et
    ((compat _).symm.trans (hL.trans (compat _)))

end PullbackCompatibility

section FibreIdeal

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
  (I : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ schemeSpace V)

/-- **The sheaf of ideals of `X ×_V Spec (A / Iⁿ)` is the kernel of `𝒪_X ⟶ 𝒪_X / Iⁿ 𝒪_X`.** -/
theorem definingIdealSheaf_fibreThickening (n : ℕ) :
    definingIdealSheaf B S hS X (fibreThickening V I f n) =
      idealKernel (pullbackRingHom B V f) (I ^ n) := by
  obtain ⟨W, hW⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B S hS X
    (idealKernel (pullbackRingHom B V f) (I ^ n))
    (isQuasicoherentOnSite_idealKernel (pullbackRingHom B V f) (I ^ n))
  have hcomp : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj U.1.left) →
      definingIdealAt B S hS X W (op U) =
        definingIdealAt B S hS X (fibreThickening V I f n) (op U) := by
    intro U hU
    have := hU
    refine Ideal.ext fun x => ?_
    rw [← definingIdealSheaf_obj, hW, definingIdealAt_fibreThickening]
    exact mem_idealKernel_iff_of_isAffine (pullbackRingHom B V f) (I ^ n) U hU x
  have hFW : fibreThickening V I f n = W := Subtype.ext (le_antisymm
    (le_of_forall_definingIdealAt_le B S hS X _ _ fun U hU => (hcomp U hU).le)
    (le_of_forall_definingIdealAt_le B S hS X _ _ fun U hU => (hcomp U hU).ge))
  rw [hFW, hW]

/-- The cokernel of the inclusion of a sheaf of ideals equal to the defining ideal of a closed
subspace `Z` is the direct image of the structure sheaf of `Z`. -/
noncomputable def cokernelIsoPushforwardOfDefiningIdealSheafEq {Y : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS Y.1) (N : (structureSheafModule B S hS Y).Submodule)
    (h : definingIdealSheaf B S hS Y Z = N) :
    cokernel (C := Modules.{u, u} B S hS Y.1 Y.2) N.ι ≅ pushforwardStructureSheaf B S hS Y Z := by
  subst h
  exact conormalAlgebraDegreeZeroIso B S hS Y Z

/-- The projection onto the cokernel of `N ⟶ 𝒪_Y`, followed by
`cokernelIsoPushforwardOfDefiningIdealSheafEq`, is the projection from `𝒪_Y` to the direct image
of the structure sheaf of `Z`. -/
theorem π_comp_cokernelIsoPushforwardOfDefiningIdealSheafEq_hom {Y : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS Y.1) (N : (structureSheafModule B S hS Y).Submodule)
    (h : definingIdealSheaf B S hS Y Z = N) :
    cokernel.π (C := Modules.{u, u} B S hS Y.1 Y.2) N.ι ≫
        (cokernelIsoPushforwardOfDefiningIdealSheafEq Z N h).hom =
      structureProjection B S hS Y Z := by
  subst h
  exact cokernel_π_comp_conormalAlgebraDegreeZeroIso_hom B S hS Y Z

variable {A : Type u} [CommRing A]
  (φ : A →+* ↥(GlobalSectionRing ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS X.1 X.2).O)))) (J : Ideal A)

/-- `𝒪_X / J 𝒪_X` is the cokernel of the inclusion of the kernel of `𝒪_X ⟶ 𝒪_X / J 𝒪_X`. -/
noncomputable def idealQuotientIsoCokernelKernel :
    idealQuotient φ (structureSheafModule B S hS X) J ≅
      cokernel (C := Modules.{u, u} B S hS X.1 X.2) (idealKernel φ J).ι where
  hom := cokernel.desc _ (cokernel.π _) (by
    rw [← idealMultipleToKernel_ι, Category.assoc, cokernel.condition, comp_zero])
  inv := cokernel.desc _ (idealQuotientπ φ (structureSheafModule B S hS X) J) (by
    rw [← kernelToIdealMultiple_ι, Category.assoc, idealMultipleι_idealQuotientπ, comp_zero])
  hom_inv_id := (cancel_epi (idealQuotientπ φ (structureSheafModule B S hS X) J)).1 (by
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id])
  inv_hom_id := (cancel_epi (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2)
      (idealKernel φ J).ι)).1 (by
    rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc, Category.comp_id])

/-- The projection `𝒪_X ⟶ 𝒪_X / J 𝒪_X`, followed by `idealQuotientIsoCokernelKernel`, is the
projection onto the cokernel of the inclusion of `ker (𝒪_X ⟶ 𝒪_X / J 𝒪_X)`. -/
theorem idealQuotientπ_comp_idealQuotientIsoCokernelKernel_hom :
    idealQuotientπ φ (structureSheafModule B S hS X) J ≫ (idealQuotientIsoCokernelKernel φ J).hom =
      cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) (idealKernel φ J).ι :=
  cokernel.π_desc _ _ _

/-- **`𝒪_X / Iⁿ 𝒪_X` is the direct image of the structure sheaf of `X ×_V Spec (A / Iⁿ)`**,
compatibly with the projections from `𝒪_X`. -/
noncomputable def idealQuotientIsoPushforwardFibreThickening (n : ℕ) :
    idealQuotient (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n) ≅
      pushforwardStructureSheaf B S hS X (fibreThickening V I f n) :=
  idealQuotientIsoCokernelKernel (pullbackRingHom B V f) (I ^ n) ≪≫
    cokernelIsoPushforwardOfDefiningIdealSheafEq _ _ (definingIdealSheaf_fibreThickening V I f n)

/-- The projection `𝒪_X ⟶ 𝒪_X / Iⁿ 𝒪_X`, followed by
`idealQuotientIsoPushforwardFibreThickening`, is the projection from `𝒪_X` to the direct image of
the structure sheaf of `X ×_V Spec (A / Iⁿ)`. -/
theorem idealQuotientπ_comp_idealQuotientIsoPushforwardFibreThickening_hom (n : ℕ) :
    idealQuotientπ (pullbackRingHom B V f) (structureSheafModule B S hS X) (I ^ n) ≫
        (idealQuotientIsoPushforwardFibreThickening V I f n).hom =
      structureProjection B S hS X (fibreThickening V I f n) := by
  rw [idealQuotientIsoPushforwardFibreThickening, Iso.trans_hom, ← Category.assoc,
    idealQuotientπ_comp_idealQuotientIsoCokernelKernel_hom,
    π_comp_cokernelIsoPushforwardOfDefiningIdealSheafEq_hom]

end FibreIdeal

end AlgebraicGeometry.Space
