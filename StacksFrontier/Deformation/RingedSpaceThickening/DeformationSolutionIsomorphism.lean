module

public import StacksFrontier.Deformation.RingedSpaceThickening.DeformationSolutionExtension
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionIsomorphism
public import StacksFrontier.Deformation.RingedSpaceThickening.ThickeningBaseFunctoriality

/-!
# Isomorphic solutions of (08U7) are those with isomorphic underlying extensions

A solution of the problem (08U7) of **Stacks 08U7** in the form
`AlgebraicGeometry.RingedSpaceThickening.DeformationSolution` is a first order thickening
`i : X ⟶ X'` over `S'` with `Ker(i^♯) ≅ i_*𝒢`; two solutions are isomorphic
(`AlgebraicGeometry.RingedSpaceThickening.Isomorphic`, the relation of **Stacks 08UC**) when an
invertible morphism of ringed spaces `X'₁ ⟶ X'₂` under `X` and over `S'` is the identity on `𝒢`.
This file shows that this happens exactly when the underlying extensions of
`f⁻¹𝒪_{S'}`-algebras (the structure sheaves read on `X`) are isomorphic
(`isomorphic_iff_nonempty_iso`).

A morphism of solutions `h` induces the comparison `extensionMap` of the extensions, and `h` is
the identity on `𝒢` exactly when the comparison is (`kernel_comm_iff_extensionMap_incl`), which
gives one direction (`SolutionHom.extensionSolutionHom`). For the other, an isomorphism `ψ` of the
extensions gives morphisms of solutions `solutionHomOfExtensionIso` from the thickening
`ExtensionSolution.toDeformationSolution` of the first extension to both solutions, and the
first is inverted.

## References

* [Stacks Project, Tag 0GQ3](https://stacks.math.columbia.edu/tag/0GQ3)
* [Stacks Project, Tag 08U7](https://stacks.math.columbia.edu/tag/08U7)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

/-- `pushforwardIsoOfComp` on sections: restriction along the equality of preimages. -/
theorem pushforwardIsoOfComp_hom_app_apply {X Y Z : RingedSpace.{u, u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (j : X ⟶ Z) (hj : a ≫ b = j) (M : SheafOfModules.{u} (structureSheafRing X))
    (V : Opens Z.carrier) (m : ((modulePushforward j).obj M).val.obj (op V)) :
    ((pushforwardIsoOfComp a b j hj).hom.app M).val.app (op V) m =
      M.val.map (eqToHom (by subst hj; rfl)).op m := by
  subst hj
  exact (ConcreteCategory.congr_hom (M.val.map_id _) m).symm

namespace SquareZeroAlgebraExtension

variable {X S : RingedSpace.{u, u}} {k : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {P Q : SquareZeroAlgebraExtension k G}

/-- A map of extensions which is the identity on `𝒢` in terms of the inclusions is the identity
on `𝒢` in terms of the identifications of the kernels. -/
theorem ideal_app_of_incl (N : P.sheaf ⟶ Q.sheaf) (hred : N ≫ Q.reduction = P.reduction)
    (hN : ∀ (U : (Opens X.carrier)ᵒᵖ) (g : G.val.obj U), N.hom.app U (P.incl U g) = Q.incl U g)
    (U : (Opens X.carrier)ᵒᵖ) (y : Stacks.Sites.Conormal.kernelIdeal P.reduction.hom U) :
    Q.ideal.app U ⟨(N.hom.app U).hom y.1, map_mem_kernelIdeal N hred U y⟩ = P.ideal.app U y := by
  have hy : (N.hom.app U).hom y.1 = Q.incl U (P.ideal.app U y) := by
    rw [← hN, P.incl_ideal]
  exact (congrArg (Q.ideal.app U) (Subtype.ext hy)).trans (Q.ideal_incl U _)

/-- A morphism of extensions is the identity on `𝒢`, read through the inclusions. -/
theorem Hom.hom_incl (φ : P ⟶ Q) (U : (Opens X.carrier)ᵒᵖ) (g : G.val.obj U) :
    (φ.hom.hom.app U).hom (P.incl U g) = Q.incl U g := by
  have h := (φ.ideal_hom U ⟨P.incl U g, P.incl_mem U g⟩).trans (P.ideal_incl U g)
  exact (Q.incl_ideal U _).symm.trans (congrArg (Q.incl U) h)

end SquareZeroAlgebraExtension

/-- Two spellings of the restriction along an equality of opens agree. -/
theorem map_eqToHom_apply_eq_map_eqToHom_op_apply {Y : TopCat.{u}}
    {F : (Opens Y)ᵒᵖ ⥤ CommRingCat.{u}} {A B : Opens Y} (h : B = A) (p : op A = op B)
    (x : F.obj (op A)) : (F.map (eqToHom p)).hom x = (F.map (eqToHom h).op).hom x := by
  subst h
  rfl

section

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'} {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {c' : (modulePullback f).obj ((modulePullback t).obj
    (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶
      (show SheafOfModules.{u} (structureSheafRing X) from G)}
  {Q₁ Q₂ : DeformationSolution t ht f G c'} (h : Q₁.X' ⟶ Q₂.X') (hh : Q₁.i ≫ h = Q₂.i)

include hh in
/-- The two preimages in `X` of an open of `X'₂` agree. -/
theorem opensMap_eq_of_thickening_comm (V : Opens Q₂.X'.carrier) :
    (Opens.map Q₁.i.hom.base).obj ((Opens.map h.hom.base).obj V) =
      (Opens.map Q₂.i.hom.base).obj V :=
  congrArg (fun m : X ⟶ Q₂.X' => (Opens.map m.hom.base).obj V) hh

/-- **The condition "identity on `𝒢`" of a morphism of solutions, on sections.** -/
theorem kernel_comm_iff :
    Q₂.idealInclusion ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom h) =
        (pushforwardIsoOfComp Q₁.i h Q₂.i hh).hom.app G ≫
          (modulePushforward h).map Q₁.idealInclusion ↔
      ∀ (V : Opens Q₂.X'.carrier) (g : G.val.obj (op ((Opens.map Q₂.i.hom.base).obj V))),
        h.hom.c.app (op V) (Q₂.idealInclusion.val.app (op V) g) =
          Q₁.idealInclusion.val.app (op ((Opens.map h.hom.base).obj V))
            (G.val.map (eqToHom (opensMap_eq_of_thickening_comm h hh V)).op g) := by
  refine ⟨fun H V g => (congrArg (fun φ => φ.val.app (op V) g) H).trans
    (congrArg (Q₁.idealInclusion.val.app _)
      (pushforwardIsoOfComp_hom_app_apply Q₁.i h Q₂.i hh G V g)), fun H => ?_⟩
  ext V g
  exact (H V.unop g).trans (congrArg (Q₁.idealInclusion.val.app _)
    (pushforwardIsoOfComp_hom_app_apply Q₁.i h Q₂.i hh G V.unop g)).symm

/-- The underlying map of the comparison of the extensions underlying `Q₂` and `Q₁` along `h`. -/
abbrev extensionMap : (Q₂.toExtensionSolution).extension.sheaf ⟶
    (Q₁.toExtensionSolution).extension.sheaf :=
  thickeningBase h Q₂.i hh

/-- The comparison is compatible with the reductions. -/
theorem extensionMap_reduction :
    extensionMap h hh ≫ (Q₁.toExtensionSolution).extension.reduction =
      (Q₂.toExtensionSolution).extension.reduction :=
  thickeningBase_comp h Q₂.i hh

/-- The inclusion of `𝒢` into the extension underlying a solution, on sections over `i⁻¹V`. -/
theorem toExtensionSolution_incl (Q : DeformationSolution t ht f G c') (V : Opens Q.X'.carrier)
    (g : G.val.obj (op ((Opens.map Q.i.hom.base).obj V))) :
    (Q.toExtensionSolution).extension.incl (op ((Opens.map Q.i.hom.base).obj V)) g =
      (inverseImageUnit Q.i).hom.app (op V) (Q.idealInclusion.val.app (op V) g) := by
  have h1 : Q.kernelIso.hom.val.app (op V) (Q.kernelIso.inv.val.app (op V) g) = g :=
    ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app (op V)) Q.kernelIso.inv_hom_id)
      (show ((modulePushforward Q.i).obj
        (show SheafOfModules.{u} (structureSheafRing X) from G)).val.obj (op V) from g)
  have h2 := thickeningExtension_incl_kernelIso Q.i_firstOrder Q.f' (f ≫ t) Q.comm G Q.kernelIso V
    (Q.kernelIso.inv.val.app (op V) g)
  rwa [h1] at h2

/-- **A morphism under `X` is the identity on `𝒢` exactly when the induced comparison of the
underlying extensions is.** -/
theorem kernel_comm_iff_extensionMap_incl :
    Q₂.idealInclusion ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom h) =
        (pushforwardIsoOfComp Q₁.i h Q₂.i hh).hom.app G ≫
          (modulePushforward h).map Q₁.idealInclusion ↔
      ∀ (U : (Opens X.carrier)ᵒᵖ) (g : G.val.obj U),
        (extensionMap h hh).hom.app U ((Q₂.toExtensionSolution).extension.incl U g) =
          (Q₁.toExtensionSolution).extension.incl U g := by
  have : IsIso Q₂.i.hom.base := Q₂.i_firstOrder.1.1
  have : IsIso Q₁.i.hom.base := Q₁.i_firstOrder.1.1
  rw [kernel_comm_iff h hh]
  let E₁ := (Q₁.toExtensionSolution).extension
  have key : ∀ (V : Opens Q₂.X'.carrier) (g : G.val.obj (op ((Opens.map Q₂.i.hom.base).obj V))),
      (h.hom.c.app (op V) (Q₂.idealInclusion.val.app (op V) g) =
        Q₁.idealInclusion.val.app (op ((Opens.map h.hom.base).obj V))
          (G.val.map (eqToHom (opensMap_eq_of_thickening_comm h hh V)).op g)) ↔
      (extensionMap h hh).hom.app _ ((Q₂.toExtensionSolution).extension.incl _ g) =
        E₁.incl _ g := by
    intro V g
    let hV := opensMap_eq_of_thickening_comm h hh V
    let e₂ : op ((Opens.map Q₁.i.hom.base).obj ((Opens.map h.hom.base).obj V)) ⟶
        op ((Opens.map Q₂.i.hom.base).obj V) := (eqToHom hV.symm).op
    let e₁ : op ((Opens.map Q₂.i.hom.base).obj V) ⟶
        op ((Opens.map Q₁.i.hom.base).obj ((Opens.map h.hom.base).obj V)) := (eqToHom hV).op
    have he₁₂ : e₁ ≫ e₂ = 𝟙 _ := by simp [e₁, e₂]
    have hg : G.val.map e₂ (G.val.map e₁ g) = g := by
      rw [← PresheafOfModules.map_comp_apply, PresheafOfModules.congr_map_apply _ he₁₂,
        PresheafOfModules.map_id]
      rfl
    have hL : (extensionMap h hh).hom.app _ ((Q₂.toExtensionSolution).extension.incl _ g) =
        (E₁.sheaf.obj.map e₂).hom ((inverseImageUnit Q₁.i).hom.app
          (op ((Opens.map h.hom.base).obj V)) (h.hom.c.app (op V)
            (Q₂.idealInclusion.val.app (op V) g))) := by
      rw [toExtensionSolution_incl]
      exact (homEquiv_symm_app_inverseImageUnit Q₂.i _ V _).trans
        (thickeningBaseTranspose_app h Q₂.i hh V _)
    have hR : E₁.incl _ g = (E₁.sheaf.obj.map e₂).hom ((inverseImageUnit Q₁.i).hom.app
          (op ((Opens.map h.hom.base).obj V)) (Q₁.idealInclusion.val.app _ (G.val.map e₁ g))) :=
      (congrArg (E₁.incl _) hg.symm).trans ((E₁.incl_map _ e₂ _).symm.trans
        (congrArg (E₁.sheaf.obj.map e₂).hom
          (toExtensionSolution_incl Q₁ ((Opens.map h.hom.base).obj V) (G.val.map e₁ g))))
    have hinj : Function.Injective (fun a => (E₁.sheaf.obj.map e₂).hom
        ((inverseImageUnit Q₁.i).hom.app (op ((Opens.map h.hom.base).obj V)) a)) :=
      (ConcreteCategory.bijective_of_isIso (E₁.sheaf.obj.map e₂)).1.comp
        (bijective_inverseImageUnit_app Q₁.i _).1
    rw [hL, hR]
    exact hinj.eq_iff.symm
  refine ⟨fun H U g => ?_, fun H V g => (key V g).2 (H _ g)⟩
  induction U using Opposite.rec with | op U => ?_
  obtain ⟨V, rfl⟩ := exists_map_obj_eq Q₂.i U
  exact (key V g).1 (H V g)

/-- **A morphism of solutions gives a morphism of the underlying extensions**, in the opposite
direction. -/
def SolutionHom.extensionSolutionHom {Q₁ Q₂ : DeformationSolution t ht f G c'}
    (e : SolutionHom Q₁ Q₂) :
    (Q₂.toExtensionSolution).extension ⟶ (Q₁.toExtensionSolution).extension where
  hom := extensionMap e.hom e.thickening_comm
  hom_reduction := extensionMap_reduction e.hom e.thickening_comm
  base_hom := (thickeningBase_comp_thickeningBase e.hom Q₂.f' Q₂.i (f ≫ t) e.thickening_comm
    Q₂.comm).trans (thickeningBase_congr e.base_comm _ _ _)
  ideal_hom := SquareZeroAlgebraExtension.ideal_app_of_incl _
    (extensionMap_reduction e.hom e.thickening_comm)
    ((kernel_comm_iff_extensionMap_incl e.hom e.thickening_comm).1 e.kernel_comm)

/-- Isomorphic solutions have isomorphic underlying extensions. -/
theorem nonempty_iso_of_isomorphic {Q₁ Q₂ : DeformationSolution t ht f G c'}
    (h : Isomorphic Q₁ Q₂) :
    Nonempty ((Q₁.toExtensionSolution).extension ≅ (Q₂.toExtensionSolution).extension) :=
  h.elim fun e _ => ⟨(SquareZeroAlgebraExtension.isoOfHom e.extensionSolutionHom).symm⟩

/-! ### From an isomorphism of extensions to a morphism of solutions -/

section FromIso

variable (E : ExtensionSolution ht f G (prescribedFMap ht f _ c'))
  (Q : DeformationSolution t ht f G c')
  (ψ : E.extension ≅ (Q.toExtensionSolution).extension)

/-- The morphism of ringed spaces `X'_E ⟶ X'_Q` attached to an isomorphism `ψ` of the
extensions: `i_Q` on spaces, and `𝒪_{X'_Q} ⟶ i_*i⁻¹𝒪_{X'_Q} ⟶ i_*𝒪_{X'_E}` on structure
sheaves. -/
def homOfExtensionIso : E.toDeformationSolution.X' ⟶ Q.X' :=
  ⟨{ base := Q.i.hom.base
     c := (inverseImageUnit Q.i ≫
       (TopCat.Sheaf.pushforward CommRingCat.{u} Q.i.hom.base).map ψ.inv.hom).hom }⟩

/-- The morphism `homOfExtensionIso` is a morphism under `X`. -/
theorem homOfExtensionIso_thickening_comm :
    E.toDeformationSolution.i ≫ homOfExtensionIso E Q ψ = Q.i := by
  have h : inverseImageUnit Q.i ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} Q.i.hom.base).map ψ.inv.hom ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} Q.i.hom.base).map E.extension.reduction =
      ObjectProperty.homMk Q.i.hom.c := by
    refine (congrArg (inverseImageUnit Q.i ≫ ·) (((TopCat.Sheaf.pushforward CommRingCat.{u}
      Q.i.hom.base).map_comp _ _).symm.trans (congrArg _ ψ.inv.hom_reduction))).trans ?_
    exact inverseImageUnit_comp_structureRingMap Q.i
  refine InducedCategory.hom_ext ?_
  change PresheafedSpace.Hom.mk Q.i.hom.base
    ((inverseImageUnit Q.i ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} Q.i.hom.base).map ψ.inv.hom ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} Q.i.hom.base).map E.extension.reduction).hom) =
      Q.i.hom
  rw [h]
  rfl

/-- The morphism `homOfExtensionIso` is a morphism over `S'`. -/
theorem homOfExtensionIso_base_comm :
    homOfExtensionIso E Q ψ ≫ Q.f' = E.toDeformationSolution.f' := by
  have hb : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base).homEquiv
      _ _ E.extension.base = thickeningBaseTranspose Q.f' (f ≫ t) Q.comm ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} (f ≫ t).hom.base).map ψ.inv.hom := by
    let a := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} (f ≫ t).hom.base
    exact (congrArg (a.homEquiv _ _) ψ.inv.base_hom.symm).trans
      ((a.homEquiv_naturality_right _ _).trans (congrArg (· ≫ _) (Equiv.apply_symm_apply _ _)))
  have hw : (homOfExtensionIso E Q ψ ≫ Q.f').hom.base = E.extension.over.hom.base := by
    change (Q.i ≫ Q.f').hom.base = (f ≫ t).hom.base
    rw [Q.comm]
  refine InducedCategory.hom_ext (PresheafedSpace.Hom.ext _ _ hw ?_)
  ext V z
  have hR : (E.toDeformationSolution.f'.hom.c.app (op V)).hom z =
      (ψ.inv.hom.hom.app _).hom ((thickeningBaseTranspose Q.f' (f ≫ t) Q.comm).hom.app (op V) z) :=
    congrArg (fun φ => (φ.hom.app (op V)).hom z) hb
  rw [hR, thickeningBaseTranspose_app]
  have hn := NatTrans.naturality_apply ψ.inv.hom.hom
    (eqToHom (congrArg (fun m : X ⟶ S' => (Opens.map m.hom.base).obj V) Q.comm).symm).op
    ((inverseImageUnit Q.i).hom.app (op ((Opens.map Q.f'.hom.base).obj V))
      (Q.f'.hom.c.app (op V) z))
  refine Eq.trans ?_ hn.symm
  rw [NatTrans.comp_app, Functor.whiskerRight_app, eqToHom_app, CommRingCat.comp_apply]
  exact map_eqToHom_apply_eq_map_eqToHom_op_apply _ _ _

/-- The comparison of extensions induced by `homOfExtensionIso` is `ψ⁻¹`. -/
theorem extensionMap_homOfExtensionIso :
    extensionMap (homOfExtensionIso E Q ψ) (homOfExtensionIso_thickening_comm E Q ψ) =
      (ψ.inv ≫ E.extension.toThickeningExtensionOf).hom := by
  let a := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} Q.i.hom.base
  refine (a.homEquiv _ _).symm_apply_eq.2 ?_
  refine Eq.trans ?_ (a.homEquiv_unit _ _ _).symm
  refine Eq.trans ?_ (congrArg (inverseImageUnit Q.i ≫ ·)
    ((TopCat.Sheaf.pushforward CommRingCat.{u} Q.i.hom.base).map_comp _ _).symm)
  rfl

/-- **The morphism of solutions attached to an isomorphism of the underlying extensions.** -/
def solutionHomOfExtensionIso : SolutionHom E.toDeformationSolution Q where
  hom := homOfExtensionIso E Q ψ
  thickening_comm := homOfExtensionIso_thickening_comm E Q ψ
  base_comm := homOfExtensionIso_base_comm E Q ψ
  kernel_comm := (kernel_comm_iff_extensionMap_incl _ _).2 fun U g => by
    rw [extensionMap_homOfExtensionIso]
    exact SquareZeroAlgebraExtension.Hom.hom_incl (ψ.inv ≫ E.extension.toThickeningExtensionOf) U g

end FromIso

/-- **Solutions with isomorphic underlying extensions are isomorphic.** -/
theorem isomorphic_of_iso {Q₁ Q₂ : DeformationSolution t ht f G c'}
    (ψ : (Q₁.toExtensionSolution).extension ≅ (Q₂.toExtensionSolution).extension) :
    Isomorphic Q₁ Q₂ := by
  let E := Q₁.toExtensionSolution
  let a₁ := solutionHomOfExtensionIso E Q₁ (Iso.refl _)
  let a₂ := solutionHomOfExtensionIso E Q₂ ψ
  have : IsIso a₁.hom := a₁.isIso_hom
  have h1 : Q₁.i ≫ inv a₁.hom = E.toDeformationSolution.i :=
    (IsIso.comp_inv_eq _).2 a₁.thickening_comm.symm
  have hc : Q₁.i ≫ (inv a₁.hom ≫ a₂.hom) = Q₂.i :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ a₂.hom) h1).trans a₂.thickening_comm)
  have hid : thickeningBase a₁.hom Q₁.i a₁.thickening_comm ≫
      thickeningBase (inv a₁.hom) E.toDeformationSolution.i h1 = 𝟙 _ :=
    (thickeningBase_comp_thickeningBase (inv a₁.hom) a₁.hom _ _ h1 a₁.thickening_comm).trans
      ((thickeningBase_congr (IsIso.inv_hom_id a₁.hom) _ _ (Category.comp_id _)).trans
        (thickeningBase_id))
  have hinc₁ := (kernel_comm_iff_extensionMap_incl a₁.hom a₁.thickening_comm).1 a₁.kernel_comm
  have hinc₂ := (kernel_comm_iff_extensionMap_incl a₂.hom a₂.thickening_comm).1 a₂.kernel_comm
  refine ⟨{ hom := inv a₁.hom ≫ a₂.hom
            thickening_comm := hc
            base_comm := (Category.assoc _ _ _).trans ((congrArg (inv a₁.hom ≫ ·)
              a₂.base_comm).trans ((IsIso.inv_comp_eq _).2 a₁.base_comm.symm))
            kernel_comm := (kernel_comm_iff_extensionMap_incl _ hc).2 fun U g => ?_ }, ?_⟩
  · change (thickeningBase (inv a₁.hom ≫ a₂.hom) Q₂.i hc).hom.app U _ = _
    rw [← thickeningBase_comp_thickeningBase (inv a₁.hom) a₂.hom _ _ h1 a₂.thickening_comm]
    change (thickeningBase (inv a₁.hom) E.toDeformationSolution.i h1).hom.app U
      ((thickeningBase a₂.hom Q₂.i a₂.thickening_comm).hom.app U _) = _
    rw [show (thickeningBase a₂.hom Q₂.i a₂.thickening_comm).hom.app U
      ((Q₂.toExtensionSolution).extension.incl U g) =
        (E.toDeformationSolution.toExtensionSolution).extension.incl U g from hinc₂ U g,
      ← hinc₁ U g]
    exact ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app U) hid) _
  · exact SolutionHom.isIso_hom _

/-- **Two solutions of Stacks 08U7 are isomorphic exactly when their underlying extensions of
`f⁻¹𝒪_{S'}`-algebras are.** -/
theorem isomorphic_iff_nonempty_iso (Q₁ Q₂ : DeformationSolution t ht f G c') :
    Isomorphic Q₁ Q₂ ↔
      Nonempty ((Q₁.toExtensionSolution).extension ≅ (Q₂.toExtensionSolution).extension) :=
  ⟨nonempty_iso_of_isomorphic, fun ⟨ψ⟩ => isomorphic_of_iso ψ⟩

end

end AlgebraicGeometry.RingedSpaceThickening

end
