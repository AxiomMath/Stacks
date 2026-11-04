module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension.Realization
import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic

/-!
# First-order thickenings come from square-zero extensions

## Main results

* `Stacks.Thickenings.firstOrderThickening_squareZeroExtension`: every first-order
  thickening over the base comes from such an extension.

## References

* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Thickenings

private theorem surjective_stalkMap_of_isIso {P Q : PresheafedSpace CommRingCat.{u}}
    (α : P ⟶ Q) [IsIso α] (z : P) :
    Function.Surjective (ConcreteCategory.hom (α.stalkMap z)) :=
  (ConcreteCategory.bijective_of_isIso _).2

private theorem firstOrderThickening_sections_mul_eq_zero
    {X Y : Scheme.{u}} (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i)
    (U : Y.Opens) (a b : Γ(Y, U)) (ha : i.app U a = 0) (hb : i.app U b = 0) :
    a * b = 0 := by
  let : IsClosedImmersion i := hi.1
  apply TopCat.Presheaf.section_ext Y.sheaf U
  intro x hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  let j : V ⟶ U := homOfLE hVU
  have hk : ∀ c : Γ(Y, U), i.app U c = 0 → Y.presheaf.map j.op c ∈ RingHom.ker (i.app V).hom := by
    intro c hc
    rw [RingHom.mem_ker]
    have hn := ConcreteCategory.congr_hom (i.naturality j.op) c
    change i.app V (Y.presheaf.map j.op c) = X.presheaf.map _ (i.app U c) at hn
    exact hn.trans (by rw [hc, map_zero])
  have hz : Y.presheaf.map j.op a * Y.presheaf.map j.op b = 0 := by
    have hsq := congrArg (fun J : Y.IdealSheafData => J.ideal ⟨V, hV⟩) hi.2
    have hm := Ideal.mul_mem_mul (hk a ha) (hk b hb)
    rw [← Scheme.Hom.ker_apply i ⟨V, hV⟩] at hm
    change _ ∈ i.ker.ideal ⟨V, hV⟩ * i.ker.ideal ⟨V, hV⟩ at hm
    change i.ker.ideal ⟨V, hV⟩ ^ 2 = ⊥ at hsq
    rw [← pow_two, hsq] at hm
    exact hm
  show Y.presheaf.germ U x hx (a * b) = Y.presheaf.germ U x hx 0
  rw [← TopCat.Presheaf.germ_res_apply Y.presheaf j x hxV (a * b)]
  simp only [map_mul, hz, map_zero]

/-- The comparison map `𝒪_Y ⟶ i_* 𝒪_X` of an immersion `i : X ⟶ Y`, as a morphism of sheaves of
modules. -/
private abbrev immersionStructureMap {X Y : Scheme.{u}} (i : X ⟶ Y) :=
  SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom

private theorem immersionKernel_sections_exact {X Y : Scheme.{u}} (i : X ⟶ Y)
    (U : Y.Opens) :
    Function.Exact ((kernel.ι (immersionStructureMap i)).val.app (Opposite.op U))
      ((immersionStructureMap i).val.app (Opposite.op U)) := by
  let S := ShortComplex.kernelSequence (immersionStructureMap i)
  let F := SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)
  have h : (S.map F).Exact :=
    ((S.map F).exact_and_mono_f_iff_f_is_kernel.mpr
      ⟨KernelFork.mapIsLimit _ (kernelIsKernel (immersionStructureMap i)) F⟩).1
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h

private theorem immersionKernel_sections_injective {X Y : Scheme.{u}} (i : X ⟶ Y)
    (U : Y.Opens) :
    Function.Injective ((kernel.ι (immersionStructureMap i)).val.app (Opposite.op U)) :=
  (ModuleCat.mono_iff_injective _).mp
    (inferInstanceAs (Mono ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map
      (kernel.ι (immersionStructureMap i)))))

/-- For a first-order thickening `i : X ⟶ Y` there is a quasi-coherent `𝒪_X`-module whose direct
image is the kernel of the comparison map `𝒪_Y ⟶ i_* 𝒪_X`. -/
@[ega "IV 16.5.14" "partial"]
private theorem firstOrderThickening_kernel_descends {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    ∃ (I : X.Modules), I.IsQuasicoherent ∧
      Nonempty ((Scheme.Modules.pushforward i).obj I ≅ kernel (immersionStructureMap i)) := by
  let : IsClosedImmersion i := hi.1
  have hqc : (kernel (immersionStructureMap i)).IsQuasicoherent := by
    have h := (Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae i).out 1 5
    exact (h.mp hi.1).2
  let K : AlgebraicGeometry.Scheme.QuasicoherentModules Y := ⟨kernel (immersionStructureMap i), hqc⟩
  have he : (AlgebraicGeometry.quasicoherentPushforward i).essImage K := by
    apply (Stacks.ClosedImmersion.pushforwardQcoh_essImage_iff i
      (kernel (immersionStructureMap i)) hqc).mpr
    intro U a ha m
    change Γ(Y, U) at a
    apply immersionKernel_sections_injective i U
    refine Eq.trans
      (((kernel.ι (immersionStructureMap i)).val.app (Opposite.op U)).hom.map_smul a m) ?_
    refine Eq.trans ?_
      ((kernel.ι (immersionStructureMap i)).val.app (Opposite.op U)).hom.map_zero.symm
    show (a : Γ(Y, U)) * (show Γ(Y, U) from
      ((kernel.ι (immersionStructureMap i)).val.app (Opposite.op U)) m) = 0
    apply firstOrderThickening_sections_mul_eq_zero i hi U a _ ha
    exact (immersionKernel_sections_exact i U).apply_apply_eq_zero m
  obtain ⟨I, ⟨e⟩⟩ := he
  exact ⟨I.obj, I.property, ⟨(SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapIso e⟩⟩

private def firstOrderThickeningBaseIso {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    (X : TopCat) ≅ (Y : TopCat) := by
  letI : IsClosedImmersion i := hi.1
  have h : IsHomeomorph i.base := isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i).isEmbedding,
      hi.isThickening.2⟩
  letI : IsIso i.base := (TopCat.isIso_iff_isHomeomorph i.base).mpr h
  exact asIso i.base

private theorem firstOrderThickeningBaseIso_hom {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    (firstOrderThickeningBaseIso i hi).hom = i.base := rfl

private theorem baseIso_preimage_inv {X Y : TopCat.{u}} (e : X ≅ Y) (U : Opens X) :
    (Opens.map e.hom).obj ((Opens.map e.inv).obj U) = U := by
  rw [← Opens.map_comp_obj, e.hom_inv_id, Opens.map_id_obj]

private def transportedStructureSheaf {X Y : Scheme.{u}}
    (e : (X : TopCat) ≅ (Y : TopCat)) : TopCat.Sheaf CommRingCat.{u} X :=
  (TopCat.Sheaf.pushforward CommRingCat e.inv).obj Y.sheaf

private def transportedStructureIso {X Y : Scheme.{u}}
    (e : (X : TopCat) ≅ (Y : TopCat)) :
    Y.toSheafedSpace ≅ thickenedSpace X (transportedStructureSheaf e) :=
  SheafedSpace.isoMk (PresheafedSpace.isoOfComponents e.symm (Iso.refl _))

private def transportedQuotient {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    transportedStructureSheaf (firstOrderThickeningBaseIso i hi) ⟶ X.sheaf where
  hom := {
    app := fun U => i.app ((Opens.map (firstOrderThickeningBaseIso i hi).inv).obj U.unop) ≫
      X.presheaf.map (eqToHom
        (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) U.unop).symm).op
    naturality := by
      intro U V f
      change Y.presheaf.map _ ≫ (i.app _ ≫ X.presheaf.map _) =
        (i.app _ ≫ X.presheaf.map _) ≫ X.presheaf.map f
      rw [i.naturality_assoc, Category.assoc]
      congr 1
      exact ((X.presheaf.map_comp _ _).symm.trans
        (congrArg X.presheaf.map (Subsingleton.elim _ _))).trans
        (X.presheaf.map_comp _ _) }

private def transportedKernelInclusion {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) (I : X.Modules)
    (j : (Scheme.Modules.pushforward i).obj I ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (U : (Opens X)ᵒᵖ) :
    I.val.obj U →+ (transportedStructureSheaf (firstOrderThickeningBaseIso i hi)).presheaf.obj U :=
  ((j.val.app (Opposite.op
    ((Opens.map (firstOrderThickeningBaseIso i hi).inv).obj U.unop))).hom.toAddMonoidHom).comp
      (I.val.map (eqToHom
        (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) U.unop)).op).hom.toAddMonoidHom

private theorem transportedKernelInclusion_naturality {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) (I : X.Modules)
    (j : (Scheme.Modules.pushforward i).obj I ⟶ SheafOfModules.unit Y.ringCatSheaf)
    {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) (x : I.val.obj U) :
    transportedKernelInclusion i hi I j V (I.val.map f x) =
      (transportedStructureSheaf (firstOrderThickeningBaseIso i hi)).presheaf.map f
        (transportedKernelInclusion i hi I j U x) := by
  show j.val.app _ (I.val.map (eqToHom
    (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) V.unop)).op (I.val.map f x)) =
    (SheafOfModules.unit Y.ringCatSheaf).val.map
      ((Opens.map (firstOrderThickeningBaseIso i hi).inv).op.map f) (j.val.app _ (I.val.map _ x))
  have hgen : ∀ {P Q Q' R : (Opens ↥X)ᵒᵖ} (p : P ⟶ Q) (q : Q ⟶ R) (p' : P ⟶ Q')
      (q' : Q' ⟶ R) (w : I.val.presheaf.obj P),
      I.val.presheaf.map q (I.val.presheaf.map p w) =
        I.val.presheaf.map q' (I.val.presheaf.map p' w) := by
    intro P Q Q' R p q p' q' w
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      Subsingleton.elim (p ≫ q) (p' ≫ q')]
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply j.val
    ((Opens.map (firstOrderThickeningBaseIso i hi).inv).op.map f)
    (I.val.map (eqToHom (baseIso_preimage_inv
      (firstOrderThickeningBaseIso i hi) U.unop)).op x))
  exact DFunLike.congr_arg (ConcreteCategory.hom (j.val.app
    ((Opens.map (firstOrderThickeningBaseIso i hi).inv).op.obj V))) (hgen _ _ _ _ x)

/-- A functor into a concrete category sends a section-retraction pair to the identity. -/
private theorem map_map_apply_of_comp_eq_id {C D : Type*} [Category C] [Category D]
    {FD : D → D → Type*} {CD : D → Type*} [∀ A B, FunLike (FD A B) (CD A) (CD B)]
    [ConcreteCategory D FD] (F : C ⥤ D) {P Q : C} (p : P ⟶ Q) (q : Q ⟶ P) (h : p ≫ q = 𝟙 P)
    (w : CD (F.obj P)) :
    (ConcreteCategory.hom (F.map q)) (ConcreteCategory.hom (F.map p) w) = w := by
  rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

private theorem transportedKernelInclusion_smul {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) (I : X.Modules)
    (j : (Scheme.Modules.pushforward i).obj I ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (U : (Opens X)ᵒᵖ)
    (a : (transportedStructureSheaf (firstOrderThickeningBaseIso i hi)).presheaf.obj U)
    (x : I.val.obj U) :
    transportedKernelInclusion i hi I j U
      (((I.val.obj U).smul ((transportedQuotient i hi).hom.app U a)).hom x) =
        a * transportedKernelInclusion i hi I j U x := by
  have hid : (eqToHom (baseIso_preimage_inv
        (firstOrderThickeningBaseIso i hi) U.unop).symm).op ≫
      (eqToHom (baseIso_preimage_inv
        (firstOrderThickeningBaseIso i hi) U.unop)).op = 𝟙 _ := Subsingleton.elim _ _
  have hc : X.ringCatSheaf.obj.map (eqToHom (baseIso_preimage_inv
        (firstOrderThickeningBaseIso i hi) U.unop)).op
        ((transportedQuotient i hi).hom.app U a) =
      i.app ((Opens.map (firstOrderThickeningBaseIso i hi).inv).obj U.unop) a :=
    map_map_apply_of_comp_eq_id X.presheaf _ _ hid _
  refine Eq.trans (DFunLike.congr_arg (ConcreteCategory.hom (j.val.app
      (Opposite.op ((Opens.map (firstOrderThickeningBaseIso i hi).inv).obj U.unop))))
    (I.val.map_smul (eqToHom (baseIso_preimage_inv
      (firstOrderThickeningBaseIso i hi) U.unop)).op
      ((transportedQuotient i hi).hom.app U a) x)) ?_
  rw [hc]
  exact (j.val.app _).hom.map_smul a _

private def transportedInclusion {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    X.toSheafedSpace ⟶ thickenedSpace X
      (transportedStructureSheaf (firstOrderThickeningBaseIso i hi)) :=
  InducedCategory.homMk { base := 𝟙 (X : TopCat), c := (transportedQuotient i hi).hom }

private theorem transportedInclusion_eq {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    i.toLRSHom.toShHom ≫ (transportedStructureIso (firstOrderThickeningBaseIso i hi)).hom =
      transportedInclusion i hi := by
  apply SheafedSpace.ext _ _ (firstOrderThickeningBaseIso i hi).hom_inv_id
  apply NatTrans.ext
  funext U
  show (𝟙 _ ≫ i.app _) ≫ X.presheaf.map _ = i.app _ ≫ X.presheaf.map _
  simp only [Category.id_comp]
  congr 2
  exact Subsingleton.elim _ _

private theorem transportedQuotient_locallySurjective {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    TopCat.Presheaf.IsLocallySurjective (transportedQuotient i hi).hom := by
  let : IsClosedImmersion i := hi.1
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
  intro x
  have hs : (transportedInclusion i hi).hom.stalkMap x =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map (transportedQuotient i hi).hom := by
    show (TopCat.Presheaf.stalkFunctor CommRingCat x).map (transportedQuotient i hi).hom ≫
        TopCat.Presheaf.stalkPushforward CommRingCat (𝟙 (X : TopCat)) X.presheaf x =
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map (transportedQuotient i hi).hom
    rw [TopCat.Presheaf.stalkPushforward.id]
    show (TopCat.Presheaf.stalkFunctor CommRingCat x).map (transportedQuotient i hi).hom ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (TopCat.Presheaf.Pushforward.id X.presheaf).hom = _
    refine Eq.trans ((TopCat.Presheaf.stalkFunctor CommRingCat x).map_comp
      (transportedQuotient i hi).hom
      (TopCat.Presheaf.Pushforward.id X.presheaf).hom).symm ?_
    congr 1
  have key : ∀ {A B C : CommRingCat.{u}} (p : A ⟶ B) (q : B ⟶ C),
      Function.Surjective (ConcreteCategory.hom p) →
      Function.Surjective (ConcreteCategory.hom q) →
      Function.Surjective (ConcreteCategory.hom (p ≫ q)) := by
    intro A B C p q hp hq
    rw [ConcreteCategory.coe_comp]
    exact hq.comp hp
  have keyEq : ∀ {A B C : CommRingCat.{u}} (hAB : A = B) (q : B ⟶ C),
      Function.Surjective (ConcreteCategory.hom q) →
      Function.Surjective (ConcreteCategory.hom (eqToHom hAB ≫ q)) := by
    intro A B C hAB q hq
    subst hAB
    rw [eqToHom_refl, Category.id_comp]
    exact hq
  let : IsIso (transportedStructureIso (firstOrderThickeningBaseIso i hi)).hom.hom :=
    ⟨(transportedStructureIso (firstOrderThickeningBaseIso i hi)).inv.hom,
      congrArg (fun f => f.hom)
        (transportedStructureIso (firstOrderThickeningBaseIso i hi)).hom_inv_id,
      congrArg (fun f => f.hom)
        (transportedStructureIso (firstOrderThickeningBaseIso i hi)).inv_hom_id⟩
  rw [← hs]
  have hh := PresheafedSpace.stalkMap.congr_hom
    (transportedInclusion i hi).hom
    (i.toLRSHom.toShHom ≫ (transportedStructureIso (firstOrderThickeningBaseIso i hi)).hom).hom
    (congrArg (fun f => f.hom) (transportedInclusion_eq i hi).symm) x
  rw [hh]
  refine keyEq _ _ ?_
  show Function.Surjective ((i.toLRSHom.toShHom.hom ≫
    (transportedStructureIso (firstOrderThickeningBaseIso i hi)).hom.hom).stalkMap x)
  rw [PresheafedSpace.stalkMap.comp]
  refine key _ _ ?_ ?_
  · exact surjective_stalkMap_of_isIso
      (transportedStructureIso (firstOrderThickeningBaseIso i hi)).hom.hom _
  · exact i.stalkMap_surjective x

private theorem transportedKernelInclusion_mem_kernel {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) (I : X.Modules)
    (j : (Scheme.Modules.pushforward i).obj I ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (hj : ∀ (V : (Opens Y)ᵒᵖ) (w : ((Scheme.Modules.pushforward i).obj I).val.obj V),
      i.app V.unop (j.val.app V w) = 0)
    (U : (Opens X)ᵒᵖ) (x : I.val.obj U) :
    (transportedQuotient i hi).hom.app U (transportedKernelInclusion i hi I j U x) = 0 := by
  have hj' := hj (Opposite.op ((Opens.map (firstOrderThickeningBaseIso i hi).inv).obj U.unop))
    (I.val.map (eqToHom (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) U.unop)).op x)
  show X.presheaf.map _ (i.app _ (j.val.app _
    (I.val.map (eqToHom
      (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) U.unop)).op x))) = 0
  rw [hj', map_zero]

private theorem transportedKernel_app_mem_kernel {X Y : Scheme.{u}} (i : X ⟶ Y) (I : X.Modules)
    (e : (Scheme.Modules.pushforward i).obj I ≅ kernel (immersionStructureMap i))
    (V : (Opens Y)ᵒᵖ) (w : ((Scheme.Modules.pushforward i).obj I).val.obj V) :
    i.app V.unop ((e.hom ≫ kernel.ι (immersionStructureMap i)).val.app V w) = 0 :=
  (immersionKernel_sections_exact i V.unop).apply_apply_eq_zero (e.hom.val.app V w)

private theorem transportedQuotient_eq_zero {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) (U : (Opens X)ᵒᵖ)
    (a : (transportedStructureSheaf (firstOrderThickeningBaseIso i hi)).presheaf.obj U)
    (ha : (transportedQuotient i hi).hom.app U a = 0) :
    i.app ((Opens.map (firstOrderThickeningBaseIso i hi).inv).obj U.unop) a = 0 := by
  apply (ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom
    (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) U.unop).symm).op)).1
  exact ha.trans (map_zero _).symm

private theorem transportedKernelInclusion_exact {X Y : Scheme.{u}}
    (i : X ⟶ Y) (hi : Stacks.Thickenings.IsFirstOrderThickening i) (I : X.Modules)
    (e : (Scheme.Modules.pushforward i).obj I ≅ kernel (immersionStructureMap i))
    (U : (Opens X)ᵒᵖ)
    (a : (transportedStructureSheaf (firstOrderThickeningBaseIso i hi)).presheaf.obj U)
    (ha : (transportedQuotient i hi).hom.app U a = 0) :
    ∃! x, transportedKernelInclusion i hi I
      (e.hom ≫ kernel.ι (immersionStructureMap i)) U x = a := by
  let V := (Opens.map (firstOrderThickeningBaseIso i hi).inv).obj U.unop
  let t := eqToHom (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) U.unop)
  obtain ⟨k, hk⟩ := (immersionKernel_sections_exact i V) a |>.mp
    (transportedQuotient_eq_zero i hi U a ha)
  let v : I.val.obj (Opposite.op (i ⁻¹ᵁ V)) := e.inv.val.app (Opposite.op V) k
  refine ⟨I.val.map (eqToHom (baseIso_preimage_inv
    (firstOrderThickeningBaseIso i hi) U.unop).symm).op v, ?_, ?_⟩
  · show (kernel.ι (immersionStructureMap i)).val.app (Opposite.op V)
      (e.hom.val.app (Opposite.op V) (I.val.map t.op (I.val.map (eqToHom
        (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) U.unop).symm).op v))) = a
    have hv : I.val.map t.op (I.val.map (eqToHom
        (baseIso_preimage_inv (firstOrderThickeningBaseIso i hi) U.unop).symm).op v) = v := by
      exact map_map_apply_of_comp_eq_id I.val.presheaf _ t.op (Subsingleton.elim _ _) v
    rw [hv]
    show (kernel.ι (immersionStructureMap i)).val.app (Opposite.op V)
      (e.hom.val.app (Opposite.op V) (e.inv.val.app (Opposite.op V) k)) = a
    have he := ConcreteCategory.congr_hom
      (congrArg (fun f => f.val.app (Opposite.op V)) e.inv_hom_id) k
    change e.hom.val.app _ (e.inv.val.app _ k) = k at he
    exact (congrArg ((kernel.ι (immersionStructureMap i)).val.app (Opposite.op V)) he).trans hk
  · intro x hx
    have hinj := immersionKernel_sections_injective i V
    have hx' : e.hom.val.app (Opposite.op V) (I.val.map t.op x) = k :=
      hinj (hx.trans hk.symm)
    have he := ConcreteCategory.congr_hom
      (congrArg (fun f => f.val.app (Opposite.op V)) e.hom_inv_id) (I.val.map t.op x)
    change e.inv.val.app _ (e.hom.val.app _ (I.val.map t.op x)) = I.val.map t.op x at he
    rw [hx'] at he
    show x = I.val.map _ v
    rw [show v = I.val.map t.op x from he]
    exact (map_map_apply_of_comp_eq_id I.val.presheaf t.op _ (Subsingleton.elim _ _) x).symm

private def firstOrderThickeningExtension {X Y S : Scheme.{u}}
    (i : X ⟶ Y) (g : Y ⟶ S) (hi : Stacks.Thickenings.IsFirstOrderThickening i)
    (I : X.Modules) (hI : I.IsQuasicoherent)
    (e : (Scheme.Modules.pushforward i).obj I ≅ kernel (immersionStructureMap i)) :
    SquareZeroExtension (i ≫ g) where
  A := transportedStructureSheaf (firstOrderThickeningBaseIso i hi)
  π := transportedQuotient i hi
  locallySurjective_π := transportedQuotient_locallySurjective i hi
  inclusion := transportedInclusion i hi
  inclusion_base := rfl
  inclusion_sheaf := HEq.rfl
  toBase := (transportedStructureIso (firstOrderThickeningBaseIso i hi)).inv ≫
    g.toLRSHom.toShHom
  over_base := by
    rw [← transportedInclusion_eq]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rfl
  I := I
  quasicoherent := hI
  ι := transportedKernelInclusion i hi I (e.hom ≫ kernel.ι (immersionStructureMap i))
  naturality := transportedKernelInclusion_naturality i hi I _
  mem_kernel := transportedKernelInclusion_mem_kernel i hi I _
    (transportedKernel_app_mem_kernel i I e)
  exact_kernel := transportedKernelInclusion_exact i hi I e
  smul_lift := transportedKernelInclusion_smul i hi I _
  square_zero := by
    intro U x y
    have h : ∀ z, i.app ((Opens.map (firstOrderThickeningBaseIso i hi).inv).obj U.unop)
        (transportedKernelInclusion i hi I (e.hom ≫ kernel.ι (immersionStructureMap i)) U z) = 0 :=
      fun z => transportedQuotient_eq_zero i hi U _ (transportedKernelInclusion_mem_kernel i hi I _
        (transportedKernel_app_mem_kernel i I e) U z)
    exact firstOrderThickening_sections_mul_eq_zero i hi _ _ _ (h x) (h y)

/-- Every first-order thickening `i : X ⟶ Y` over a base is obtained from a square-zero extension
whose kernel has direct image along `i` isomorphic to the kernel of the comparison map
`𝒪_Y ⟶ i_* 𝒪_X`, that is, to the ideal sheaf of the thickening. -/
public theorem firstOrderThickening_squareZeroExtension_kernel {X Y S : Scheme.{u}}
    (i : X ⟶ Y) (g : Y ⟶ S) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    ∃ E : SquareZeroExtension (i ≫ g),
      Nonempty ((Scheme.Modules.pushforward i).obj E.I ≅
        kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom)) ∧
      ∃ r : Realization E, r.ambient = Y ∧ HEq r.immersion i ∧ HEq r.toBase g := by
  obtain ⟨I, hI, ⟨e⟩⟩ := firstOrderThickening_kernel_descends i hi
  let E := firstOrderThickeningExtension i g hi I hI e
  refine ⟨E, ⟨e⟩, {
    ambient := Y
    sheafedIso := transportedStructureIso (firstOrderThickeningBaseIso i hi)
    immersion := i
    toBase := g
    immersion_isFirstOrder := hi
    over_base := rfl
    inclusion_eq := transportedInclusion_eq i hi
    toBase_eq := rfl }, rfl, HEq.rfl, HEq.rfl⟩

/-- Every first-order thickening over a base is obtained from a square-zero extension. -/
@[stacks 05YV "converse: every first-order thickening has this form"]
public theorem firstOrderThickening_squareZeroExtension {X Y S : Scheme.{u}}
    (i : X ⟶ Y) (g : Y ⟶ S) (hi : Stacks.Thickenings.IsFirstOrderThickening i) :
    ∃ E : SquareZeroExtension (i ≫ g),
      ∃ r : Realization E, r.ambient = Y ∧ HEq r.immersion i ∧ HEq r.toBase g := by
  obtain ⟨E, -, hr⟩ := firstOrderThickening_squareZeroExtension_kernel i g hi
  exact ⟨E, hr⟩

end Stacks.Thickenings
