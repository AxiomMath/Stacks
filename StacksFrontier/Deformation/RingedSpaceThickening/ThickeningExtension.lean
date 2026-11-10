module

public import StacksFrontier.Deformation.RingedSpaceThickening.BaseIdealPushforward

/-!
# The square-zero extension underlying a first order thickening

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces and `h : X' ⟶ T` a
morphism with `i ≫ h = k`. The underlying spaces of `X` and `X'` are homeomorphic but not
identified, so `𝒪_{X'}` is read on `X` as `i⁻¹𝒪_{X'}`; with the algebra structure
`k⁻¹𝒪_T ⟶ i⁻¹𝒪_{X'}` transposed from `h^♯` and the reduction `i⁻¹𝒪_{X'} ⟶ 𝒪_X`, it is a
square-zero extension of `k⁻¹𝒪_T`-algebras of `𝒪_X` by `Ker(i^♯)`. Given an identification `κ`
of `Ker(i^♯)` with `i_*𝒢`, this is an extension by `𝒢` (`thickeningExtension`), the objects
classified by **Stacks 0GPZ**: this is how a solution of the problem (08U7) of **Stacks 08U7**,
a first order thickening with a morphism to `S'`, is read as an extension of
`f⁻¹𝒪_{S'}`-algebras in the proof of **Stacks 0GQ3**.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.thickeningBase`: the algebra structure
  `k⁻¹𝒪_T ⟶ i⁻¹𝒪_{X'}`.
* `AlgebraicGeometry.RingedSpaceThickening.thickeningIdealIso`: `Ker(i⁻¹𝒪_{X'} ⟶ 𝒪_X) ≅ 𝒢`
  from `κ`.
* `AlgebraicGeometry.RingedSpaceThickening.thickeningExtension`: the extension.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.thickeningExtension_incl_kernelIso`: the inclusion
  `𝒢 ⟶ i⁻¹𝒪_{X'}` on sections is `κ⁻¹` followed by the inclusion of `Ker(i^♯)`.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X X' T : RingedSpace.{u, u}} {i : X ⟶ X'} (hi : IsFirstOrderThickening i)
  (h : X' ⟶ T) (k : X ⟶ T) (hk : i ≫ h = k)

/-- The map `𝒪_T ⟶ k_*i⁻¹𝒪_{X'}`: `h^♯` followed by the unit of `i`. -/
def thickeningBaseTranspose :
    T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} k.hom.base).obj (inverseImageBaseRing i) :=
  (ObjectProperty.homMk h.hom.c : T.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).obj X'.sheaf) ≫
    (TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).map (inverseImageUnit i) ≫
    eqToHom (congrArg (fun m : X ⟶ T =>
      (TopCat.Sheaf.pushforward CommRingCat.{u} m.hom.base).obj (inverseImageBaseRing i)) hk)

/-- The `k⁻¹𝒪_T`-algebra structure of `i⁻¹𝒪_{X'}`, transposed from `thickeningBaseTranspose`. -/
def thickeningBase : inverseImageBaseRing k ⟶ inverseImageBaseRing i :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} k.hom.base).homEquiv _ _).symm
    (thickeningBaseTranspose h k hk)

/-- `thickeningBaseTranspose` followed by the reduction is `k^♯`. -/
theorem thickeningBaseTranspose_comp :
    thickeningBaseTranspose h k hk ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} k.hom.base).map (structureRingMap i) =
      ObjectProperty.homMk k.hom.c := by
  subst hk
  have h1 := congrArg ((TopCat.Sheaf.pushforward CommRingCat.{u} h.hom.base).map)
    (inverseImageUnit_comp_structureRingMap i)
  rw [Functor.map_comp] at h1
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Category.id_comp _)).trans h1))).trans ?_)
  rfl

/-- The reduction `i⁻¹𝒪_{X'} ⟶ 𝒪_X` is a morphism of `k⁻¹𝒪_T`-algebras. -/
theorem thickeningBase_comp : thickeningBase h k hk ≫ structureRingMap i = structureRingMap k :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    k.hom.base).homEquiv_naturality_right_symm _ _).symm.trans
      (congrArg _ (thickeningBaseTranspose_comp h k hk))

variable (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf))

/-- **The identification of `Ker(i⁻¹𝒪_{X'} ⟶ 𝒪_X)` with `𝒢`** given an identification `κ` of the
ideal sheaf of `i` with `i_*𝒢`: both push forward to `Ker(i^♯)`, and `i_*` is fully faithful. -/
def thickeningIdealIso
    (κ : AlgebraicGeometry.SheafOfModules.idealSheaf i ≅
      (modulePushforward i).obj (show SheafOfModules.{u} (structureSheafRing X) from G)) :
    (show SheafOfModules.{u} (structureSheafRing X) from baseIdealModule hi) ≅ G :=
  haveI : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  haveI : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  (Functor.FullyFaithful.ofFullyFaithful (modulePushforward i)).preimageIso
    (baseIdealPushforwardIso hi ≪≫ κ)

/-- `i_*` of `thickeningIdealIso` is `t_*𝒥 ≅ Ker(i^♯) ≅ i_*𝒢`. -/
theorem modulePushforward_map_thickeningIdealIso_hom
    (κ : AlgebraicGeometry.SheafOfModules.idealSheaf i ≅
      (modulePushforward i).obj (show SheafOfModules.{u} (structureSheafRing X) from G)) :
    (modulePushforward i).map (thickeningIdealIso hi G κ).hom =
      (baseIdealPushforwardIso hi).hom ≫ κ.hom :=
  have : (modulePushforward i).Full :=
    (closedQuotientOfIsThickening i hi.1).full_modulePushforward
  have : (modulePushforward i).Faithful :=
    (closedQuotientOfIsThickening i hi.1).faithful_modulePushforward
  (Functor.FullyFaithful.ofFullyFaithful (modulePushforward i)).map_preimage _

variable (ψ : (show SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf) from baseIdealModule hi) ≅ G)

/-- The identification of the kernel of `i⁻¹𝒪_{X'} ⟶ 𝒪_X` with `𝒢`, on sections. -/
def thickeningIdealRestriction :
    Stacks.Sites.Conormal.IdealRestriction.{u, u, u, u} (structureRingMap i) G where
  app U := (ψ.hom.val.app U).hom.toAddMonoidHom.comp ((baseIdealRestriction hi).app U)
  app_smul U r a := by
    change ψ.hom.val.app U ((baseIdealRestriction hi).app U (r • a)) = _
    rw [(baseIdealRestriction hi).app_smul]
    exact (ψ.hom.val.app U).hom.map_smul _ _
  app_map {U V} g a := by
    change ψ.hom.val.app V ((baseIdealRestriction hi).app V _) = _
    rw [(baseIdealRestriction hi).app_map]
    exact PresheafOfModules.naturality_apply ψ.hom.val g _

/-- An isomorphism of sheaves of modules has a left inverse on sections. -/
private theorem sheafOfModules_iso_inv_hom_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (U : Cᵒᵖ) (m : M.val.obj U) : e.inv.val.app U (e.hom.val.app U m) = m :=
  ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app U) e.hom_inv_id) m

/-- An isomorphism of sheaves of modules has a right inverse on sections. -/
private theorem sheafOfModules_iso_hom_inv_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (e : M ≅ N) (U : Cᵒᵖ) (n : N.val.obj U) : e.hom.val.app U (e.inv.val.app U n) = n :=
  ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app U) e.inv_hom_id) n

/-- **The extension `0 ⟶ 𝒢 ⟶ i⁻¹𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `k⁻¹𝒪_T`-algebras** attached to a first
order thickening `i : X ⟶ X'`, a morphism `h : X' ⟶ T` with `i ≫ h = k`, and an identification
`ψ` of the kernel of `i` with `𝒢`. -/
def thickeningExtension : SquareZeroAlgebraExtension k G where
  sheaf := inverseImageBaseRing i
  base := thickeningBase h k hk
  reduction := structureRingMap i
  base_comp_reduction := thickeningBase_comp h k hk
  reduction_surjective := isLocallySurjective_structureRingMap i hi.1
  ideal := thickeningIdealRestriction hi G ψ
  ideal_bijective U := by
    have hψ : Function.Bijective (ψ.hom.val.app U) := by
      have h1 := congrArg (fun m => m.val.app U) ψ.hom_inv_id
      have h2 := congrArg (fun m => m.val.app U) ψ.inv_hom_id
      exact ⟨fun a b hab => (ConcreteCategory.congr_hom h1 a).symm.trans
        ((congrArg (ψ.inv.val.app U) hab).trans (ConcreteCategory.congr_hom h1 b)),
        fun b => ⟨ψ.inv.val.app U b, ConcreteCategory.congr_hom h2 b⟩⟩
    exact hψ.comp (baseIdealRestriction_bijective hi U)

omit hi in
/-- `thickeningBaseTranspose` on sections: `h^♯` followed by the unit of `i`, transported from
`i⁻¹h⁻¹V` to `k⁻¹V`. -/
theorem thickeningBaseTranspose_app (V : Opens T.carrier) (z : T.presheaf.obj (op V)) :
    (thickeningBaseTranspose h k hk).hom.app (op V) z =
      (inverseImageBaseRing i).obj.map (eqToHom (by subst hk; rfl)).op
        ((inverseImageUnit i).hom.app (op ((Opens.map h.hom.base).obj V))
          (h.hom.c.app (op V) z)) := by
  subst hk
  exact (ConcreteCategory.congr_hom ((inverseImageBaseRing i).obj.map_id _) _).symm

/-! ### The inclusions of the ideals, on sections -/

omit hi in
/-- The inclusion of the ideal sheaf of a morphism of ringed spaces is injective on sections. -/
theorem idealSheafι_injective (V : (Opens X'.carrier)ᵒᵖ) :
    Function.Injective ((kernel.ι (structureSheafModuleHom i)).val.app V) := by
  apply (ModuleCat.mono_iff_injective _).mp
  change Mono ((SheafOfModules.evaluation (R := structureSheafRing X') V).map
    (kernel.ι (structureSheafModuleHom i)))
  infer_instance

omit hi in
/-- A section of the ideal sheaf of `i`, included in `𝒪_{X'}`, is killed by `i^♯`. -/
theorem idealSheafι_mem_ker (V : Opens X'.carrier)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op V)) :
    (show X'.presheaf.obj (op V) from (kernel.ι (structureSheafModuleHom i)).val.app (op V) y) ∈
      RingHom.ker (i.hom.c.app (op V)).hom := by
  have h' := congrArg (fun φ : AlgebraicGeometry.SheafOfModules.idealSheaf i ⟶
    (modulePushforward i).obj (SheafOfModules.unit (structureSheafRing X)) => φ.val.app (op V) y)
    (kernel.condition (structureSheafModuleHom i))
  exact h'

/-- The section of `𝒥` over `i⁻¹V` attached to a section of the ideal sheaf of `i` over `V` is
its preimage under `t_*𝒥 ≅ Ker(i^♯)`. -/
theorem baseIdealSectionsEquiv_idealSheafι (V : Opens X'.carrier)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op V)) :
    baseIdealSectionsEquiv hi V ⟨_, idealSheafι_mem_ker V y⟩ =
      (baseIdealPushforwardIso hi).inv.val.app (op V) y := by
  obtain ⟨m, rfl⟩ : ∃ m, (baseIdealPushforwardIso hi).hom.val.app (op V) m = y :=
    ⟨_, sheafOfModules_iso_hom_inv_apply _ _ y⟩
  rw [sheafOfModules_iso_inv_hom_apply]
  have h2 := congrArg (fun φ => φ.val.app (op V) m) (baseIdealPushforwardIso_hom_ι hi)
  refine ((baseIdealSectionsEquiv hi V).symm_apply_eq.1 ?_).symm
  exact Subtype.ext h2.symm

/-- The inclusion `Ker(i⁻¹𝒪_{X'} ⟶ 𝒪_X) ≅ 𝒢 ⟶ i⁻¹𝒪_{X'}` on the section of `𝒥` attached to a
section `x` of `Ker(i^♯)` over `V`. -/
theorem thickeningExtension_incl (V : Opens X'.carrier) (x : RingHom.ker (i.hom.c.app (op V)).hom) :
    (thickeningExtension hi h k hk G ψ).incl (op ((Opens.map i.hom.base).obj V))
      (ψ.hom.val.app _ (baseIdealSectionsEquiv hi V x)) =
        (inverseImageUnit i).hom.app (op V) x.1 :=
  (thickeningExtension hi h k hk G ψ).incl_ideal _ ⟨_, _⟩

/-- `thickeningIdealIso` on sections: it is `κ`, read through `t_*𝒥 ≅ Ker(i^♯)`. -/
theorem thickeningIdealIso_hom_app
    (κ : AlgebraicGeometry.SheafOfModules.idealSheaf i ≅
      (modulePushforward i).obj (show SheafOfModules.{u} (structureSheafRing X) from G))
    (V : Opens X'.carrier) (y : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op V)) :
    (thickeningIdealIso hi G κ).hom.val.app (op ((Opens.map i.hom.base).obj V))
      ((baseIdealPushforwardIso hi).inv.val.app (op V) y) = κ.hom.val.app (op V) y := by
  have h1 := congrArg
    (fun φ => φ.val.app (op V) ((baseIdealPushforwardIso hi).inv.val.app (op V) y))
    (modulePushforward_map_thickeningIdealIso_hom hi G κ)
  refine h1.trans ?_
  change κ.hom.val.app (op V) (((baseIdealPushforwardIso hi).inv ≫
    (baseIdealPushforwardIso hi).hom).val.app (op V) y) = _
  rw [Iso.inv_hom_id]
  rfl

/-- **The inclusion `𝒢 ⟶ i⁻¹𝒪_{X'}` on sections**: for a section `y` of `Ker(i^♯)` over `V`, the
section `κ(y)` of `𝒢` over `i⁻¹V` is included as the image of `y ∈ 𝒪_{X'}(V)` in
`i⁻¹𝒪_{X'}`. -/
theorem thickeningExtension_incl_kernelIso
    (κ : AlgebraicGeometry.SheafOfModules.idealSheaf i ≅
      (modulePushforward i).obj (show SheafOfModules.{u} (structureSheafRing X) from G))
    (V : Opens X'.carrier) (y : (AlgebraicGeometry.SheafOfModules.idealSheaf i).val.obj (op V)) :
    (thickeningExtension hi h k hk G (thickeningIdealIso hi G κ)).incl
      (op ((Opens.map i.hom.base).obj V)) (κ.hom.val.app (op V) y) =
        (inverseImageUnit i).hom.app (op V)
          ((kernel.ι (structureSheafModuleHom i)).val.app (op V) y) := by
  rw [← thickeningIdealIso_hom_app, ← baseIdealSectionsEquiv_idealSheafι]
  exact thickeningExtension_incl hi h k hk G _ V _

end AlgebraicGeometry.RingedSpaceThickening

end
