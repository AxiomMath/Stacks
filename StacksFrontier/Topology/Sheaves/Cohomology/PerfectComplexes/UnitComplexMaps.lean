module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.LeftDualLocalCoevaluation

/-!
# Morphisms out of the structure sheaf in degree zero

A morphism of sheaves of modules out of the structure sheaf is determined by the image of `1`
over the whole space, and a morphism of cochain complexes out of `O[0]` is determined by a
global section of degree `0` killed by the differential. Cocycles differing by a boundary give
the same morphism in the derived category.

## Main definitions

* `unitHomOfTop`: The morphism out of the structure sheaf sending `1` to a global section.
* `cocycleHom`: The morphism of complexes out of `O[0]` sending `1` to a global cocycle.
* `cocycleOf`: The global cocycle that a morphism out of `O[0]` sends `1` to.
* `res`: Restriction of a section of a sheaf of modules to a smaller open.

## Main results

* `eq_cocycleHom`: Every morphism out of `O[0]` is `cocycleHom` of its cocycle.
* `Q_map_cocycleHom_eq`: Cocycles differing by a boundary give the same morphism of the
  derived category.
* `cocycleOf_eq_add_of_homotopy`: Homotopic morphisms out of `O[0]` have cocycles differing
  by a boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace Stacks.Cohomology.LeftDualPerfect

/-- Degree zero of a morphism out of a single complex, after an additive functor. -/
theorem singleObjXSelf_inv_comp_singleMap_comp_f {V₁ V₂ : Type*} [Category* V₁] [Category* V₂]
    [HasZeroMorphisms V₁] [HasZeroMorphisms V₂] [HasZeroObject V₁] [HasZeroObject V₂]
    (F : V₁ ⥤ V₂) [F.PreservesZeroMorphisms] (A : V₁) {G : CochainComplex V₁ ℤ}
    (γ : (HomologicalComplex.single V₁ (ComplexShape.up ℤ) 0).obj A ⟶ G) :
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (F.obj A)).inv ≫
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).inv.app A ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map γ).f 0 =
      F.map ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).inv ≫ γ.f 0) := by
  simp [Functor.map_comp]

variable {T : TopCat.{u}} {S : Sheaf (Opens.grothendieckTopology T) RingCat.{u}}

/-- The section of a sheaf of modules determined by its value on the whole space. -/
def sectionsOfTop (A : SheafOfModules.{u} S) (s : A.val.obj (op ⊤)) : A.sections :=
  PresheafOfModules.sectionsMk (fun T => A.val.map (homOfLE le_top : T.unop ⟶ ⊤).op s)
    (fun T T' g => by
      rw [← PresheafOfModules.map_comp_apply]
      rfl)

/-- The morphism out of the structure sheaf sending `1` to a given global section. -/
def unitHomOfTop (A : SheafOfModules.{u} S) (s : A.val.obj (op ⊤)) :
    SheafOfModules.unit (S) ⟶ A :=
  A.unitHomEquiv.symm (sectionsOfTop A s)

/-- The morphism `unitHomOfTop A s` sends `1` over the whole space to `s`. -/
theorem unitHomOfTop_app_top (A : SheafOfModules.{u} S) (s : A.val.obj (op ⊤)) :
    (unitHomOfTop A s).val.app (op ⊤)
      (1 : (S).obj.obj (op ⊤)) = s := by
  have := congrArg (fun t => t.val (op ⊤)) (A.unitHomEquiv.apply_symm_apply (sectionsOfTop A s))
  simp only [SheafOfModules.unitHomEquiv_apply_coe] at this
  rw [unitHomOfTop, this]
  refine (A.val.congr_map_apply (f := (homOfLE le_top : (⊤ : Opens T) ⟶ ⊤).op)
    (g := 𝟙 (op (⊤ : Opens T))) rfl s).trans ?_
  simp only [PresheafOfModules.map_id]
  rfl

/-- The element `1` of the ring of global sections, as a section of the structure sheaf. -/
abbrev oneS (S : Sheaf (Opens.grothendieckTopology T) RingCat.{u}) :
    (SheafOfModules.unit S).val.obj (op ⊤) :=
  (1 : S.obj.obj (op ⊤))

/-- The morphism `unitHomOfTop A s` sends `oneS S` to `s`. -/
theorem unitHomOfTop_app_oneS (A : SheafOfModules.{u} S) (s : A.val.obj (op ⊤)) :
    (unitHomOfTop A s).val.app (op ⊤) (oneS S) = s :=
  unitHomOfTop_app_top A s

/-- A morphism out of the structure sheaf is determined by the image of `1` over the whole
space. -/
theorem unitHom_ext {A : SheafOfModules.{u} S}
    {f g : SheafOfModules.unit (S) ⟶ A}
    (h : f.val.app (op ⊤) (oneS S) = g.val.app (op ⊤) (oneS S)) : f = g := by
  apply A.unitHomEquiv.injective
  ext T
  simp only [SheafOfModules.unitHomEquiv_apply_coe]
  have e : (1 : (S).obj.obj T) =
      (SheafOfModules.unit (S)).val.map
        (homOfLE le_top : T.unop ⟶ ⊤).op (oneS S) :=
    (PresheafOfModules.unit_map_one _ (homOfLE le_top : T.unop ⟶ ⊤).op).symm
  rw [e]
  have hf := PresheafOfModules.naturality_apply f.val (homOfLE le_top : T.unop ⟶ ⊤).op (oneS S)
  have hg := PresheafOfModules.naturality_apply g.val (homOfLE le_top : T.unop ⟶ ⊤).op (oneS S)
  rw [h] at hf
  exact hf.trans hg.symm

/-- Every morphism out of the structure sheaf is `unitHomOfTop` of the image of `1` over the
whole space. -/
theorem eq_unitHomOfTop {A : SheafOfModules.{u} S}
    (f : SheafOfModules.unit (S) ⟶ A) :
    f = unitHomOfTop A (f.val.app (op ⊤) (oneS S)) :=
  unitHom_ext (by rw [unitHomOfTop_app_top])

/-- Composing `unitHomOfTop A s` with `g` gives `unitHomOfTop` of the image of `s` under `g`. -/
theorem unitHomOfTop_comp {A B : SheafOfModules.{u} S} (s : A.val.obj (op ⊤)) (g : A ⟶ B) :
    unitHomOfTop A s ≫ g = unitHomOfTop B (g.val.app (op ⊤) s) :=
  unitHom_ext (by
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
      unitHomOfTop_app_oneS])

/-- The morphism `unitHomOfTop A s` is additive in the global section `s`. -/
theorem unitHomOfTop_add {A : SheafOfModules.{u} S} (s t : A.val.obj (op ⊤)) :
    unitHomOfTop A (s + t) = unitHomOfTop A s + unitHomOfTop A t :=
  unitHom_ext (by
    simp only [SheafOfModules.add_val, PresheafOfModules.add_app, ModuleCat.hom_add,
      LinearMap.add_apply, unitHomOfTop_app_oneS])

variable {R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}

/-- The element `1` of the ring of global sections. -/
abbrev one (R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)).val.obj (op ⊤) :=
  oneS (Stacks.SheafOfModules.Tensor.ringSheaf R)

/-- The structure sheaf in degree zero. -/
abbrev unitComplexR (R : Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}) :
    CochainComplex (Mod R) ℤ :=
  (CochainComplex.singleFunctor (Mod R) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- The morphism of complexes out of `O_Y[0]` sending `1` to a global section of degree `0`
killed by the differential. -/
def cocycleHom (A : CochainComplex (Mod R) ℤ) (s : (A.X 0).val.obj (op ⊤))
    (hs : (A.d 0 1).val.app (op ⊤) s = 0) : unitComplexR R ⟶ A :=
  HomologicalComplex.mkHomFromSingle (unitHomOfTop (A.X 0) s) (fun k hk => by
    obtain rfl : k = 1 := by simpa using hk.symm
    refine unitHom_ext ?_
    rw [unitHomOfTop_comp, unitHomOfTop_app_top, hs]
    rfl)

/-- The degree-zero component of `cocycleHom A s hs` is `unitHomOfTop (A.X 0) s`. -/
theorem cocycleHom_f (A : CochainComplex (Mod R) ℤ) (s : (A.X 0).val.obj (op ⊤))
    (hs : (A.d 0 1).val.app (op ⊤) s = 0) :
    (cocycleHom A s hs).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫ unitHomOfTop (A.X 0) s :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The global section of degree `0` that a morphism out of `O_Y[0]` sends `1` to. -/
def cocycleOf {A : CochainComplex (Mod R) ℤ} (β : unitComplexR R ⟶ A) :
    (A.X 0).val.obj (op ⊤) :=
  ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫ β.f 0).val.app (op ⊤)
    (one R)

/-- Equal morphisms of sheaves of modules agree on global sections. -/
private theorem app_top_congr {M N : Mod R} {f g : M ⟶ N} (h : f = g) (x : M.val.obj (op ⊤)) :
    f.val.app (op ⊤) x = g.val.app (op ⊤) x :=
  congrArg (fun φ => φ.val.app (op ⊤) x) h

/-- The section `cocycleOf β` is killed by the differential `d⁰`. -/
theorem cocycleOf_d {A : CochainComplex (Mod R) ℤ} (β : unitComplexR R ⟶ A) :
    (A.d 0 1).val.app (op ⊤) (cocycleOf β) = 0 := by
  have h : β.f 0 ≫ A.d 0 1 = 0 := (β.comm 0 1).trans (by simp)
  exact app_top_congr (f := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
    β.f 0 ≫ A.d 0 1) (g := 0) (by rw [h, comp_zero]) (one R)

/-- Every morphism of complexes out of `O_Y[0]` is `cocycleHom` of its cocycle. -/
theorem eq_cocycleHom {A : CochainComplex (Mod R) ℤ} (β : unitComplexR R ⟶ A) :
    β = cocycleHom A (cocycleOf β) (cocycleOf_d β) :=
  HomologicalComplex.from_single_hom_ext
    (((Iso.inv_comp_eq _).mp (eq_unitHomOfTop _)).trans (cocycleHom_f _ _ _).symm)

/-- The image of a global degree-zero cocycle under a morphism of complexes is a cocycle. -/
theorem cocycleHom_d_comp {A B : CochainComplex (Mod R) ℤ} (s : (A.X 0).val.obj (op ⊤))
    (hs : (A.d 0 1).val.app (op ⊤) s = 0) (g : A ⟶ B) :
    (B.d 0 1).val.app (op ⊤) ((g.f 0).val.app (op ⊤) s) = 0 := by
  refine (app_top_congr (g.comm 0 1) s).trans ?_
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply, hs,
    map_zero]

/-- Composing `cocycleHom A s hs` with `g` gives `cocycleHom` of the image of `s` under `g`. -/
theorem cocycleHom_comp {A B : CochainComplex (Mod R) ℤ} (s : (A.X 0).val.obj (op ⊤))
    (hs : (A.d 0 1).val.app (op ⊤) s = 0) (g : A ⟶ B) :
    cocycleHom A s hs ≫ g = cocycleHom B ((g.f 0).val.app (op ⊤) s) (cocycleHom_d_comp s hs g) :=
  HomologicalComplex.from_single_hom_ext
    ((congrArg (· ≫ g.f 0) (cocycleHom_f A s hs)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (unitHomOfTop_comp s (g.f 0))).trans (cocycleHom_f B _ _).symm)))

/-- The null-homotopic map out of `O[0]` whose degree-zero component is `1 ↦ d u`. -/
def boundaryHomotopyData (A : CochainComplex (Mod R) ℤ) (u : (A.X (-1)).val.obj (op ⊤)) :
    ∀ i j, (ComplexShape.up ℤ).Rel j i → ((unitComplexR R).X i ⟶ A.X j) :=
  fun i j hij =>
    if hi : i = 0 then
      ((unitComplexR R).XIsoOfEq hi).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫
          unitHomOfTop (A.X (-1)) u ≫ (A.XIsoOfEq (by simp at hij; omega)).hom
    else 0

/-- The degree-zero component of the null-homotopic map of `boundaryHomotopyData A u` sends `1`
to `d u`. -/
theorem nullHomotopicMap'_boundaryHomotopyData_f (A : CochainComplex (Mod R) ℤ)
    (u : (A.X (-1)).val.obj (op ⊤)) :
    (Homotopy.nullHomotopicMap' (boundaryHomotopyData A u)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom ≫
        unitHomOfTop (A.X 0) ((A.d (-1) 0).val.app (op ⊤) u) := by
  rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
    (show (ComplexShape.up ℤ).Rel 0 1 by simp)]
  simp only [CochainComplex.singleFunctor_obj_d, boundaryHomotopyData, one_ne_zero, ↓reduceDIte,
    comp_zero, Int.reduceNeg, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.comp_id,
    Category.id_comp, Category.assoc, zero_add, Iso.cancel_iso_hom_left]
  exact unitHomOfTop_comp u (A.d (-1) 0)

/-- Adding the boundary `d u` to a cocycle adds the null-homotopic map of
`boundaryHomotopyData A u` to its `cocycleHom`. -/
theorem cocycleHom_add_boundary (A : CochainComplex (Mod R) ℤ) (s : (A.X 0).val.obj (op ⊤))
    (hs : (A.d 0 1).val.app (op ⊤) s = 0) (u : (A.X (-1)).val.obj (op ⊤))
    (hs' : (A.d 0 1).val.app (op ⊤) (s + (A.d (-1) 0).val.app (op ⊤) u) = 0) :
    cocycleHom A (s + (A.d (-1) 0).val.app (op ⊤) u) hs' =
      cocycleHom A s hs + Homotopy.nullHomotopicMap' (boundaryHomotopyData A u) :=
  HomologicalComplex.from_single_hom_ext (by
    rw [HomologicalComplex.add_f_apply, cocycleHom_f, cocycleHom_f,
      nullHomotopicMap'_boundaryHomotopyData_f, unitHomOfTop_add, Preadditive.comp_add])

/-- Two global cocycles of degree `0` differing by a boundary give the same morphism of the
derived category out of `O[0]`. -/
theorem Q_map_cocycleHom_eq [HasDerivedCategory (Mod R)] (A : CochainComplex (Mod R) ℤ)
    (s₁ s₂ : (A.X 0).val.obj (op ⊤)) (hs₁ : (A.d 0 1).val.app (op ⊤) s₁ = 0)
    (hs₂ : (A.d 0 1).val.app (op ⊤) s₂ = 0) (u : (A.X (-1)).val.obj (op ⊤))
    (h : s₁ = s₂ + (A.d (-1) 0).val.app (op ⊤) u) :
    DerivedCategory.Q.map (cocycleHom A s₁ hs₁) = DerivedCategory.Q.map (cocycleHom A s₂ hs₂) := by
  subst h
  rw [cocycleHom_add_boundary A s₂ hs₂ u hs₁, Functor.map_add,
    DerivedCategory.Q_map_eq_of_homotopy (h := Homotopy.nullHomotopy' (boundaryHomotopyData A u)),
    Functor.map_zero, add_zero]

/-- The cocycle of `β ≫ g` is the image under `g` of the cocycle of `β`. -/
theorem cocycleOf_comp {A B : CochainComplex (Mod R) ℤ} (β : unitComplexR R ⟶ A) (g : A ⟶ B) :
    cocycleOf (β ≫ g) = (g.f 0).val.app (op ⊤) (cocycleOf β) :=
  rfl

/-- The cocycle of `cocycleHom A s hs` is `s`. -/
theorem cocycleOf_cocycleHom (A : CochainComplex (Mod R) ℤ) (s : (A.X 0).val.obj (op ⊤))
    (hs : (A.d 0 1).val.app (op ⊤) s = 0) : cocycleOf (cocycleHom A s hs) = s := by
  have h : (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
      (cocycleHom A s hs).f 0 = unitHomOfTop (A.X 0) s := by
    rw [cocycleHom_f, Iso.inv_hom_id_assoc]
  exact (app_top_congr h (one R)).trans (unitHomOfTop_app_top _ _)

/-- A homotopy between two morphisms out of `O[0]` makes their cocycles differ by a
boundary. -/
theorem cocycleOf_eq_add_of_homotopy {A : CochainComplex (Mod R) ℤ}
    {β₁ β₂ : unitComplexR R ⟶ A} (H : Homotopy β₁ β₂) :
    cocycleOf β₁ = cocycleOf β₂ + (A.d (-1) 0).val.app (op ⊤)
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
        H.hom 0 (-1)).val.app (op ⊤) (one R)) := by
  have h := H.comm 0
  rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by simp),
    prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)] at h
  have hd : (unitComplexR R).d 0 1 = 0 := by simp
  rw [hd, zero_comp, zero_add] at h
  refine (app_top_congr (congrArg (_ ≫ ·) h) (one R)).trans ?_
  rw [Preadditive.comp_add]
  rw [add_comm]
  rfl

/-- A morphism out of `O_Y[0]` whose cocycle is `s` equals `cocycleHom A s hs`. -/
theorem cocycleHom_eq_of_cocycleOf_eq {A : CochainComplex (Mod R) ℤ} (β : unitComplexR R ⟶ A)
    (s : (A.X 0).val.obj (op ⊤)) (hs : (A.d 0 1).val.app (op ⊤) s = 0) (h : cocycleOf β = s) :
    cocycleHom A s hs = β := by
  subst h
  exact (eq_cocycleHom β).symm

/-- If the cocycle of `g ∘ cocycleHom s` differs from that of `ι⁻¹ ≫ γ'` by a boundary, then
`(ι ≫ cocycleHom s) ≫ g` and `γ'` agree in the derived category. -/
theorem Q_map_iso_comp_cocycleHom_comp [HasDerivedCategory (Mod R)]
    {A B E : CochainComplex (Mod R) ℤ} (ι : E ≅ unitComplexR R)
    (s : (A.X 0).val.obj (op ⊤)) (hs : (A.d 0 1).val.app (op ⊤) s = 0) (g : A ⟶ B)
    (γ' : E ⟶ B) (u : (B.X (-1)).val.obj (op ⊤))
    (h : (g.f 0).val.app (op ⊤) s = cocycleOf (ι.inv ≫ γ') + (B.d (-1) 0).val.app (op ⊤) u) :
    DerivedCategory.Q.map ((ι.hom ≫ cocycleHom A s hs) ≫ g) = DerivedCategory.Q.map γ' := by
  rw [Category.assoc, Functor.map_comp, cocycleHom_comp,
    Q_map_cocycleHom_eq B _ _ _ (cocycleOf_d (ι.inv ≫ γ')) u h,
    cocycleHom_eq_of_cocycleOf_eq _ _ _ rfl, ← Functor.map_comp, Iso.hom_inv_id_assoc]

/-- Restriction of a section of a sheaf of modules to a smaller open. -/
abbrev res (M : Mod R) {V' V : Opens T} (h : V' ≤ V) (s : M.val.obj (op V)) :
    M.val.obj (op V') :=
  M.val.map (homOfLE h).op s

/-- Restricting twice is restricting once along the composite inclusion. -/
theorem res_res (M : Mod R) {V'' V' V : Opens T} (h₁ : V'' ≤ V') (h₂ : V' ≤ V)
    (s : M.val.obj (op V)) : res M h₁ (res M h₂ s) = res M (h₁.trans h₂) s := by
  rw [res, res, ← PresheafOfModules.map_comp_apply]
  rfl

/-- A morphism of sheaves of modules commutes with restriction of sections. -/
theorem map_res {M N : Mod R} (φ : M ⟶ N) {V' V : Opens T} (h : V' ≤ V)
    (s : M.val.obj (op V)) : φ.val.app (op V') (res M h s) = res N h (φ.val.app (op V) s) :=
  PresheafOfModules.naturality_apply _ _ _

/-- Restriction of sections is additive. -/
theorem res_add (M : Mod R) {V' V : Opens T} (h : V' ≤ V) (s t : M.val.obj (op V)) :
    res M h (s + t) = res M h s + res M h t :=
  map_add _ _ _

/-- Restricting an identity of the form `f(t) = c + d u` to a smaller open. -/
theorem restrict_cocycle_identity {F G : CochainComplex (Mod R) ℤ} (f : F ⟶ G) {V' V : Opens T}
    (hV : V' ≤ V) (t : (F.X 0).val.obj (op V)) (c : (G.X 0).val.obj (op ⊤))
    (u : (G.X (-1)).val.obj (op V))
    (hid : (f.f 0).val.app (op V) t = res (G.X 0) le_top c + (G.d (-1) 0).val.app (op V) u) :
    (f.f 0).val.app (op V') (res (F.X 0) hV t) =
      res (G.X 0) le_top c + (G.d (-1) 0).val.app (op V') (res (G.X (-1)) hV u) := by
  rw [map_res, hid, res_add, res_res, map_res]

/-- The restriction of a cocycle is a cocycle. -/
theorem restrict_cocycle {F : CochainComplex (Mod R) ℤ} {V' V : Opens T} (hV : V' ≤ V)
    (t : (F.X 0).val.obj (op V)) (ht : (F.d 0 1).val.app (op V) t = 0) :
    (F.d 0 1).val.app (op V') (res (F.X 0) hV t) = 0 := by
  rw [map_res, ht]
  exact map_zero _

end Stacks.Cohomology.LeftDualPerfect
