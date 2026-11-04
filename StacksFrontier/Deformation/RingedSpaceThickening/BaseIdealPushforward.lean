module

public import StacksFrontier.Deformation.RingedSpaceThickening.BaseThickeningExtension

/-!
# `t_*𝒥` is the ideal sheaf `Ker(t^♯)` of the thickening

For a first order thickening `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})`, the `𝒪_S`-module
`𝒥 = AlgebraicGeometry.RingedSpaceThickening.baseIdealModule` used by **Stacks 0GQ3** is the
kernel of `t⁻¹𝒪_{S'} ⟶ 𝒪_S`. This file checks it against the ideal sheaf of `t` on `S'`, the
kernel of `t^♯ : 𝒪_{S'} ⟶ t_*𝒪_S`: pushing `𝒥` forward along `t` gives exactly that kernel, as
`𝒪_{S'}`-modules (`baseIdealPushforwardIso`), with the inclusion `t_*𝒥 ⟶ 𝒪_{S'}` given on
sections by the identification `baseIdealSectionsEquiv` of the sections of `𝒥` over `t⁻¹V` with
the kernel of `t^♯` on `V`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.baseIdealPushforwardIncl`: the inclusion
  `t_*𝒥 ⟶ 𝒪_{S'}`.
* `AlgebraicGeometry.RingedSpaceThickening.baseIdealPushforwardIso`: `t_*𝒥 ≅ Ker(t^♯)`.
* `AlgebraicGeometry.RingedSpaceThickening.baseIdealIsoPullback`: `𝒥 ≅ t^*Ker(t^♯)`.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {S S' : RingedSpace.{u, u}} {t : S ⟶ S'} (ht : IsFirstOrderThickening t)

/-- `baseIdealSectionsEquiv` is additive. -/
theorem baseIdealSectionsEquiv_add (V : Opens S'.carrier)
    (x y : RingHom.ker (t.hom.c.app (op V)).hom) :
    baseIdealSectionsEquiv ht V (x + y) =
      baseIdealSectionsEquiv ht V x + baseIdealSectionsEquiv ht V y := by
  rw [baseIdealSectionsEquiv_apply, baseIdealSectionsEquiv_apply, baseIdealSectionsEquiv_apply,
    ← map_add]
  congr 1
  exact Subtype.ext (map_add _ _ _)

/-- The inclusion `t_*𝒥 ⟶ 𝒪_{S'}` over one open: the inverse of `baseIdealSectionsEquiv`. -/
def baseIdealPushforwardInclApp (V : (Opens S'.carrier)ᵒᵖ) :
    ((modulePushforward t).obj (baseIdealModule ht)).val.obj V ⟶
      (SheafOfModules.unit (structureSheafRing S')).val.obj V :=
  ConcreteCategory.ofHom
    { toFun := fun m => ((baseIdealSectionsEquiv ht V.unop).symm m).1
      map_add' := fun m m' => by
        let e := baseIdealSectionsEquiv ht V.unop
        have h := (baseIdealSectionsEquiv_add ht V.unop (e.symm m) (e.symm m')).trans
          (congrArg₂ (· + ·) (e.apply_symm_apply m) (e.apply_symm_apply m'))
        exact congrArg Subtype.val (e.symm_apply_eq.2 h.symm)
      map_smul' := fun r m => by
        let e := baseIdealSectionsEquiv ht V.unop
        have h := (baseIdealSectionsEquiv_mul ht V.unop r (e.symm m)).trans
          (congrArg (_ • ·) (e.apply_symm_apply m))
        exact congrArg Subtype.val (e.symm_apply_eq.2 h.symm) }

/-- `baseIdealPushforwardInclApp` on a section. -/
theorem baseIdealPushforwardInclApp_apply (V : (Opens S'.carrier)ᵒᵖ)
    (m : ((modulePushforward t).obj (baseIdealModule ht)).val.obj V) :
    baseIdealPushforwardInclApp ht V m = ((baseIdealSectionsEquiv ht V.unop).symm m).1 :=
  rfl

/-- The inverse of `baseIdealSectionsEquiv` commutes with restriction. -/
theorem baseIdealSectionsEquiv_symm_map {V W : Opens S'.carrier} (h : W ≤ V)
    (m : (baseIdealModule ht).val.obj (op ((Opens.map t.hom.base).obj V))) :
    ((baseIdealSectionsEquiv ht W).symm
      ((baseIdealModule ht).val.map ((Opens.map t.hom.base).map (homOfLE h)).op m)).1 =
      S'.presheaf.map (homOfLE h).op ((baseIdealSectionsEquiv ht V).symm m).1 := by
  obtain ⟨x, rfl⟩ := (baseIdealSectionsEquiv ht V).surjective m
  rw [Equiv.symm_apply_apply, ← baseIdealSectionsEquiv_map, Equiv.symm_apply_apply]

/-- **The inclusion `t_*𝒥 ⟶ 𝒪_{S'}`** of `𝒪_{S'}`-modules. -/
def baseIdealPushforwardIncl :
    (modulePushforward t).obj (baseIdealModule ht) ⟶
      SheafOfModules.unit (structureSheafRing S') where
  val :=
    { app := baseIdealPushforwardInclApp ht
      naturality := fun {V W} g => by
        ext m
        exact baseIdealSectionsEquiv_symm_map ht (leOfHom g.unop) m }

/-- The inclusion `t_*𝒥 ⟶ 𝒪_{S'}` on sections. -/
theorem baseIdealPushforwardIncl_app (V : (Opens S'.carrier)ᵒᵖ)
    (m : ((modulePushforward t).obj (baseIdealModule ht)).val.obj V) :
    (baseIdealPushforwardIncl ht).val.app V m = ((baseIdealSectionsEquiv ht V.unop).symm m).1 :=
  rfl

/-- The inclusion `t_*𝒥 ⟶ 𝒪_{S'}` is killed by `t^♯`. -/
theorem baseIdealPushforwardIncl_comp :
    baseIdealPushforwardIncl ht ≫ structureSheafModuleHom t = 0 := by
  ext V m
  exact ((baseIdealSectionsEquiv ht V.unop).symm m).2

section Lift

variable {W : SheafOfModules.{u} (structureSheafRing S')}
  (k : W ⟶ SheafOfModules.unit (structureSheafRing S')) (hk : k ≫ structureSheafModuleHom t = 0)

include hk in
/-- A section of a map into `𝒪_{S'}` killed by `t^♯` lies in the kernel of `t^♯`. -/
theorem mem_ker_of_comp_eq_zero (V : (Opens S'.carrier)ᵒᵖ) (w : W.val.obj V) :
    (show S'.presheaf.obj V from k.val.app V w) ∈ RingHom.ker (t.hom.c.app V).hom :=
  congrArg (fun φ : W ⟶ _ => φ.val.app V w) hk

/-- The factorization through `t_*𝒥` of a map into `𝒪_{S'}` killed by `t^♯`, over one open. -/
def baseIdealLiftApp (V : (Opens S'.carrier)ᵒᵖ) :
    W.val.obj V ⟶ ((modulePushforward t).obj (baseIdealModule ht)).val.obj V :=
  ConcreteCategory.ofHom
    { toFun := fun w => baseIdealSectionsEquiv ht V.unop ⟨_, mem_ker_of_comp_eq_zero k hk V w⟩
      map_add' := fun w w' =>
        (congrArg (baseIdealSectionsEquiv ht V.unop)
          (Subtype.ext (map_add (k.val.app V).hom w w') :
            (⟨_, mem_ker_of_comp_eq_zero k hk V (w + w')⟩ : RingHom.ker (t.hom.c.app V).hom) =
              ⟨_, mem_ker_of_comp_eq_zero k hk V w⟩ + ⟨_, mem_ker_of_comp_eq_zero k hk V w'⟩)).trans
          (baseIdealSectionsEquiv_add ht V.unop _ _)
      map_smul' := fun r w =>
        (congrArg (baseIdealSectionsEquiv ht V.unop)
          (Subtype.ext (map_smul (k.val.app V).hom r w) :
            (⟨_, mem_ker_of_comp_eq_zero k hk V (r • w)⟩ : RingHom.ker (t.hom.c.app V).hom) =
              (show S'.presheaf.obj (op V.unop) from r) •
                ⟨_, mem_ker_of_comp_eq_zero k hk V w⟩)).trans
          (baseIdealSectionsEquiv_mul ht V.unop r _) }

/-- The factorization through `t_*𝒥` of a map into `𝒪_{S'}` killed by `t^♯`. -/
def baseIdealLift : W ⟶ (modulePushforward t).obj (baseIdealModule ht) where
  val :=
    { app := baseIdealLiftApp ht k hk
      naturality := fun {V V'} g => by
        ext w
        exact (congrArg (baseIdealSectionsEquiv ht V'.unop) (Subtype.ext
          (PresheafOfModules.naturality_apply k.val g w))).trans
            (baseIdealSectionsEquiv_map ht (leOfHom g.unop) _) }

end Lift

/-- **`t_*𝒥 ⟶ 𝒪_{S'}` is a kernel of `t^♯ : 𝒪_{S'} ⟶ t_*𝒪_S`.** -/
def isLimitBaseIdealKernelFork :
    IsLimit (KernelFork.ofι (baseIdealPushforwardIncl ht) (baseIdealPushforwardIncl_comp ht)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {_} k hk => baseIdealLift ht k hk)
    (fun {_} k hk => by
      ext V w
      change ((baseIdealSectionsEquiv ht V.unop).symm (baseIdealSectionsEquiv ht V.unop _)).1 = _
      rw [Equiv.symm_apply_apply])
    (fun {_} k hk m hm => by
      ext V w
      change _ = baseIdealSectionsEquiv ht V.unop _
      exact (baseIdealSectionsEquiv ht V.unop).symm_apply_eq.1 (Subtype.ext
        (congrArg (fun φ : _ ⟶ SheafOfModules.unit (structureSheafRing S') => φ.val.app V w) hm)))

/-- **`t_*𝒥 ≅ Ker(t^♯)`**: the pushforward of `𝒥` is the ideal sheaf of `t`. -/
def baseIdealPushforwardIso :
    (modulePushforward t).obj (baseIdealModule ht) ≅
      AlgebraicGeometry.SheafOfModules.idealSheaf t :=
  IsLimit.conePointUniqueUpToIso (isLimitBaseIdealKernelFork ht) (limit.isLimit _)

/-- `t_*𝒥 ≅ Ker(t^♯)` followed by the inclusion of the kernel is the inclusion of `t_*𝒥`. -/
theorem baseIdealPushforwardIso_hom_ι :
    (baseIdealPushforwardIso ht).hom ≫ kernel.ι (structureSheafModuleHom t) =
      baseIdealPushforwardIncl ht :=
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitBaseIdealKernelFork ht) (limit.isLimit _)
    WalkingParallelPair.zero

/-- **`𝒥 ≅ t^*Ker(t^♯)`**: the `𝒪_S`-module `𝒥` is the pullback of the ideal sheaf of `t`, the
module `AlgebraicGeometry.RingedSpaceThickening.baseIdealOnReduction t` from which the prescribed
map of `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution` starts. Both push forward to
`Ker(t^♯)` (the second by **Stacks 08KZ**, `isIso_unit_app_idealSheaf`), and `t_*` is fully
faithful for a thickening. -/
def baseIdealIsoPullback :
    (show SheafOfModules.{u} (structureSheafRing S) from baseIdealModule ht) ≅
      (modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t) :=
  haveI : (modulePushforward t).Full :=
    (closedQuotientOfIsThickening t ht.1).full_modulePushforward
  haveI : (modulePushforward t).Faithful :=
    (closedQuotientOfIsThickening t ht.1).faithful_modulePushforward
  haveI := isIso_unit_app_idealSheaf t ht
  (Functor.FullyFaithful.ofFullyFaithful (modulePushforward t)).preimageIso
    (baseIdealPushforwardIso ht ≪≫ asIso ((modulePullbackPushforwardAdjunction t).unit.app
      (AlgebraicGeometry.SheafOfModules.idealSheaf t)))

/-- `t_*` of `𝒥 ≅ t^*Ker(t^♯)` is `t_*𝒥 ≅ Ker(t^♯)` followed by the unit of `t^* ⊣ t_*`. -/
theorem modulePushforward_map_baseIdealIsoPullback_hom :
    (modulePushforward t).map (baseIdealIsoPullback ht).hom =
      (baseIdealPushforwardIso ht).hom ≫ (modulePullbackPushforwardAdjunction t).unit.app
        (AlgebraicGeometry.SheafOfModules.idealSheaf t) :=
  have : (modulePushforward t).Full :=
    (closedQuotientOfIsThickening t ht.1).full_modulePushforward
  have : (modulePushforward t).Faithful :=
    (closedQuotientOfIsThickening t ht.1).faithful_modulePushforward
  have := isIso_unit_app_idealSheaf t ht
  (Functor.FullyFaithful.ofFullyFaithful (modulePushforward t)).map_preimage _

end AlgebraicGeometry.RingedSpaceThickening

end
