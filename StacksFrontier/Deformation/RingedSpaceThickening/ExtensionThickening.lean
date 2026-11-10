module

public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningExtension

/-!
# The first order thickening of an extension of `k⁻¹𝒪_T`-algebras

An extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `k⁻¹𝒪_T`-algebras (for `k : X ⟶ T`) is the same
thing as a first order thickening `i : X ⟶ X'` over `T` with `Ker(i^♯) ≅ i_*𝒢` (the footnote
to **Stacks 0GPZ**). This file builds the thickening: the ringed space `X' = (X, 𝒪_{X'})`
(`space`), the morphism `i` which is the identity on spaces and the reduction on structure
sheaves (`thickening`), the morphism `X' ⟶ T` given by the algebra structure (`over`), the
identification `thickeningKernelIso` of `Ker(i^♯)` with `i_*𝒢`, and checks that reading
`𝒪_{X'}` back on `X` as in
`StacksFrontier/Deformation/RingedSpaceThickening/ThickeningExtension.lean` returns the extension
(`isoThickeningExtensionOf`).

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

variable {X T : RingedSpace.{u, u}} {k : X ⟶ T}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (P : SquareZeroAlgebraExtension k G)

/-- The ringed space `X' = (X, 𝒪_{X'})` of an extension. -/
def space : RingedSpace.{u, u} where
  carrier := X.carrier
  presheaf := P.sheaf.obj
  IsSheaf := P.sheaf.property

/-- The thickening `i : X ⟶ X'`: the identity on spaces and the reduction on structure sheaves. -/
def thickening : X ⟶ P.space :=
  ⟨{ base := 𝟙 X.carrier, c := P.reduction.hom }⟩

/-- The morphism `X' ⟶ T` given by the algebra structure. -/
def «over» : P.space ⟶ T :=
  ⟨{ base := k.hom.base
     c := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} k.hom.base).homEquiv _ _
       P.base).hom }⟩

/-- `i : X ⟶ X'` is a morphism over `T`. -/
theorem thickening_comp_over : P.thickening ≫ P.over = k := by
  have h : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} k.hom.base).homEquiv _ _
      P.base ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} k.hom.base).map P.reduction =
      (ObjectProperty.homMk k.hom.c : T.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat.{u} k.hom.base).obj X.sheaf) :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      k.hom.base).homEquiv_naturality_right _ _).symm.trans
      ((congrArg _ P.base_comp_reduction).trans (Equiv.apply_symm_apply _ _))
  refine InducedCategory.hom_ext ?_
  change PresheafedSpace.Hom.mk k.hom.base
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} k.hom.base).homEquiv _ _
      P.base ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} k.hom.base).map P.reduction).hom) = k.hom
  rw [h]
  rfl

/-- The comorphism of `i : X ⟶ X'` is the reduction. -/
theorem structureSheafHom_thickening_app (U : (Opens P.space.carrier)ᵒᵖ)
    (a : (structureSheafRing P.space).obj.obj U) :
    (structureSheafHom P.thickening).hom.app U a = P.reduction.hom.app U a :=
  rfl

/-- The product of two local sections of `𝒪_{X'}` killed by `i^♯` vanishes. -/
theorem thickening_mul_eq_zero (U : (Opens P.space.carrier)ᵒᵖ)
    (a b : (structureSheafRing P.space).obj.obj U)
    (ha : (structureSheafHom P.thickening).hom.app U a = 0)
    (hb : (structureSheafHom P.thickening).hom.app U b = 0) : a * b = 0 :=
  P.sq_eq_zero U ⟨a, ha⟩ ⟨b, hb⟩

/-- `i : X ⟶ X'` is a thickening of ringed spaces. -/
theorem isThickening_thickening : IsThickening P.thickening := by
  refine ⟨?_, ?_, ?_⟩
  · change IsIso (𝟙 X.carrier)
    infer_instance
  · have h : Presheaf.IsLocallySurjective (Opens.grothendieckTopology P.space.carrier)
        ((PresheafOfModules.toPresheaf _).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.thickening)).val) :=
      ⟨fun s => P.reduction_surjective.imageSieve_mem s⟩
    have h2 : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf _).map
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom P.thickening))) := h
    exact (SheafOfModules.toSheaf _).epi_of_epi_map inferInstance
  · intro U a ha x hx
    refine ⟨U, le_rfl, hx, 2, ?_⟩
    have hid : ((structureSheafRing P.space).obj.map (homOfLE (le_rfl (a := U))).op) a = a := by
      rw [show (homOfLE (le_rfl (a := U))).op = 𝟙 (op U) from rfl,
        CategoryTheory.Functor.map_id]
      rfl
    rw [hid, pow_two]
    exact P.thickening_mul_eq_zero (op U) a a ha ha

/-- **`i : X ⟶ X'` is a first order thickening.** -/
theorem isFirstOrderThickening_thickening : IsFirstOrderThickening (thickening P) := by
  refine ⟨P.isThickening_thickening, fun U => ?_⟩
  rw [show (2 : ℕ) = 1 + 1 from rfl, Submodule.pow_succ, Submodule.pow_one]
  refine le_antisymm (Ideal.mul_le.2 ?_) bot_le
  intro r hr s hs
  rw [Ideal.mem_bot]
  exact P.thickening_mul_eq_zero (op U) r s hr hs

/-! ### The ideal of `i : X ⟶ X'` is `𝒢` -/

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` over one open. -/
def thickeningInclApp (U : (Opens P.space.carrier)ᵒᵖ) :
    ((modulePushforward P.thickening).obj
      (show SheafOfModules.{u} (structureSheafRing X) from G)).val.obj U ⟶
      (SheafOfModules.unit (structureSheafRing P.space)).val.obj U :=
  ConcreteCategory.ofHom
    { toFun := fun g => P.incl U g
      map_add' := fun g g' => P.incl_add U g g'
      map_smul' := fun r g => P.incl_smul U r g }

/-- **The inclusion `i_*𝒢 ⟶ 𝒪_{X'}`** of the ideal of `i : X ⟶ X'`. -/
def thickeningIncl :
    (modulePushforward P.thickening).obj (show SheafOfModules.{u} (structureSheafRing X) from G) ⟶
      SheafOfModules.unit (structureSheafRing P.space) where
  val :=
    { app := P.thickeningInclApp
      naturality := fun {U V} g => by
        ext m
        exact (P.incl_map U g m).symm }

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` on sections. -/
theorem thickeningIncl_app (U : (Opens P.space.carrier)ᵒᵖ) (g : G.val.obj U) :
    P.thickeningIncl.val.app U g = P.incl U g :=
  rfl

/-- The inclusion `i_*𝒢 ⟶ 𝒪_{X'}` is killed by `i^♯`. -/
theorem thickeningIncl_comp :
    P.thickeningIncl ≫ structureSheafModuleHom P.thickening = 0 := by
  ext U m
  exact P.reduction_incl U m

section Lift

variable {W : SheafOfModules.{u} (structureSheafRing P.space)}
  (k : W ⟶ SheafOfModules.unit (structureSheafRing P.space))
  (hk : k ≫ structureSheafModuleHom P.thickening = 0)

include hk in
/-- A section of a map into `𝒪_{X'}` killed by `i^♯` lies in the kernel of the reduction. -/
theorem mem_kernelIdeal_of_comp_eq_zero (U : (Opens P.space.carrier)ᵒᵖ) (w : W.val.obj U) :
    (show P.sheaf.obj.obj U from k.val.app U w) ∈
      Stacks.Sites.Conormal.kernelIdeal P.reduction.hom U :=
  congrArg (fun φ : W ⟶ _ => φ.val.app U w) hk

/-- The factorization through `i_*𝒢` of a map into `𝒪_{X'}` killed by `i^♯`, over one open. -/
def thickeningLiftApp (U : (Opens P.space.carrier)ᵒᵖ) :
    W.val.obj U ⟶ ((modulePushforward P.thickening).obj
      (show SheafOfModules.{u} (structureSheafRing X) from G)).val.obj U :=
  ConcreteCategory.ofHom
    { toFun := fun w => P.ideal.app U ⟨_, P.mem_kernelIdeal_of_comp_eq_zero k hk U w⟩
      map_add' := fun w w' =>
        (congrArg (P.ideal.app U) (Subtype.ext (map_add (k.val.app U).hom w w') :
          (⟨_, P.mem_kernelIdeal_of_comp_eq_zero k hk U (w + w')⟩ :
            Stacks.Sites.Conormal.kernelIdeal P.reduction.hom U) =
            ⟨_, P.mem_kernelIdeal_of_comp_eq_zero k hk U w⟩ +
              ⟨_, P.mem_kernelIdeal_of_comp_eq_zero k hk U w'⟩)).trans (map_add _ _ _)
      map_smul' := fun r w =>
        (congrArg (P.ideal.app U) (Subtype.ext (map_smul (k.val.app U).hom r w) :
          (⟨_, P.mem_kernelIdeal_of_comp_eq_zero k hk U (r • w)⟩ :
            Stacks.Sites.Conormal.kernelIdeal P.reduction.hom U) =
            (show P.sheaf.obj.obj U from r) •
              ⟨_, P.mem_kernelIdeal_of_comp_eq_zero k hk U w⟩)).trans
          (P.ideal.app_smul U r _) }

/-- The factorization through `i_*𝒢` of a map into `𝒪_{X'}` killed by `i^♯`. -/
def thickeningLift : W ⟶ (modulePushforward P.thickening).obj
    (show SheafOfModules.{u} (structureSheafRing X) from G) where
  val :=
    { app := P.thickeningLiftApp k hk
      naturality := fun {U V} g => by
        ext w
        exact (congrArg (P.ideal.app V) (Subtype.ext
          (PresheafOfModules.naturality_apply k.val g w))).trans (P.ideal.app_map g _) }

end Lift

/-- **`i_*𝒢 ⟶ 𝒪_{X'}` is a kernel of `i^♯`.** -/
def isLimitThickeningKernelFork :
    IsLimit (KernelFork.ofι P.thickeningIncl P.thickeningIncl_comp) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} k hk => P.thickeningLift k hk)
    (fun {_} k hk => by
      ext U w
      exact P.incl_ideal U _)
    (fun {_} k hk m hm => by
      ext U w
      change _ = P.ideal.app U _
      have h := congrArg (fun φ : _ ⟶ SheafOfModules.unit (structureSheafRing P.space) =>
        φ.val.app U w) hm
      refine (P.ideal_incl U _).symm.trans ?_
      congr 1
      exact Subtype.ext h)

/-- **The ideal of `i : X ⟶ X'` is `𝒢`**: `Ker(i^♯) ≅ i_*𝒢`. -/
def thickeningKernelIso :
    AlgebraicGeometry.SheafOfModules.idealSheaf P.thickening ≅
      (modulePushforward P.thickening).obj
        (show SheafOfModules.{u} (structureSheafRing X) from G) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _) P.isLimitThickeningKernelFork

/-- `i_*𝒢 ≅ Ker(i^♯)` followed by the inclusion of the kernel is the inclusion of `𝒢`. -/
theorem thickeningKernelIso_inv_ι :
    P.thickeningKernelIso.inv ≫ kernel.ι (structureSheafModuleHom P.thickening) =
      P.thickeningIncl :=
  IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit _) P.isLimitThickeningKernelFork
    WalkingParallelPair.zero

/-! ### Reading `𝒪_{X'}` back on `X` returns the extension -/

/-- The extension of `k⁻¹𝒪_T`-algebras underlying the thickening `X ⟶ X'` of an extension. -/
abbrev thickeningExtensionOf : SquareZeroAlgebraExtension k G :=
  thickeningExtension P.isFirstOrderThickening_thickening P.over k P.thickening_comp_over G
    (thickeningIdealIso P.isFirstOrderThickening_thickening G P.thickeningKernelIso)

/-- The inclusion of `𝒢` into the extension read back on `X`, on sections. -/
theorem thickeningExtensionOf_incl_ideal (U : (Opens X.carrier)ᵒᵖ)
    (y : Stacks.Sites.Conormal.kernelIdeal P.reduction.hom U) :
    P.thickeningExtensionOf.incl U (P.ideal.app U y) =
      (inverseImageUnit P.thickening).hom.app U y.1 := by
  have h1 : P.thickeningKernelIso.hom.val.app U (P.thickeningKernelIso.inv.val.app U
      (P.ideal.app U y)) = P.ideal.app U y :=
    ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app U) P.thickeningKernelIso.inv_hom_id) _
  have h2 : (kernel.ι (structureSheafModuleHom P.thickening)).val.app U
      (P.thickeningKernelIso.inv.val.app U (P.ideal.app U y)) = y.1 :=
    (congrArg (fun φ => φ.val.app U (P.ideal.app U y)) P.thickeningKernelIso_inv_ι).trans
      (P.incl_ideal U y)
  have h3 := thickeningExtension_incl_kernelIso P.isFirstOrderThickening_thickening P.over k
    P.thickening_comp_over G P.thickeningKernelIso U.unop
    (P.thickeningKernelIso.inv.val.app U (P.ideal.app U y))
  exact (congrArg (P.thickeningExtensionOf.incl U) h1.symm).trans
    (h3.trans (congrArg ((inverseImageUnit P.thickening).hom.app U) h2))

/-- The comparison `𝒪_{X'} ⟶ i⁻¹𝒪_{X'}`: the unit of `i⁻¹ ⊣ i_*`, `i` being the identity on
spaces. -/
def toThickeningExtensionOf : P ⟶ P.thickeningExtensionOf where
  hom := inverseImageUnit P.thickening
  hom_reduction := inverseImageUnit_comp_structureRingMap P.thickening
  base_hom := by
    apply ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} k.hom.base).homEquiv
      _ _).injective
    refine ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      k.hom.base).homEquiv_naturality_right _ _).trans ?_
    refine Eq.trans ?_ (Equiv.apply_symm_apply _ _).symm
    exact (Category.comp_id _).symm
  ideal_hom U y :=
    (congrArg (P.thickeningExtensionOf.ideal.app U)
      (Subtype.ext (P.thickeningExtensionOf_incl_ideal U y).symm)).trans
      (P.thickeningExtensionOf.ideal_incl U _)

/-- **The extension underlying the thickening of an extension is the extension.** -/
def isoThickeningExtensionOf : P ≅ P.thickeningExtensionOf :=
  isoOfHom P.toThickeningExtensionOf

end AlgebraicGeometry.RingedSpaceThickening.SquareZeroAlgebraExtension

end
