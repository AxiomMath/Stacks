module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectRestrictOpen
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFreeComp
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitModuleZariskiHomGlueNested
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.MatrixCocycleOfOverlapCharts

/-!
# Local solutions for the comparison functor of Tag 0EXD, moved between opens

Let `p` be a prime and let

```
E ⟶ X'
↓    ↓
Z ⟶ X
```

be a commutative square of schemes in characteristic `p`.  The Zariski glueing in the essential
surjectivity half of [Stacks, Tag 0EXD] starts from an object `T` of the categorical fibre product
`𝒮_Z ×_{𝒮_E} 𝒮_{X'}` and, over each member `V` of an open cover of `X`, a *local solution*: an
isomorphism `β : G_V(𝒪^{⊕n}) ≅ T|_V` between the comparison functor of the square restricted over
`V` (`AlgebraicGeometry.frobeniusColimitComparisonRestrict`) at a free module and the restriction
of `T` (`AlgebraicGeometry.frobeniusColimitLocRestrict`).  This file moves such data between nested
opens and records the coherences the glueing consumes.

## Main definitions

* `AlgebraicGeometry.frobeniusColimitFreeVectorBundlePullbackIso`: the transition functor carries
  the free module of rank `n` to the free module of rank `n`.
* `AlgebraicGeometry.frobeniusColimitLocResHom`: restriction to `U' ≤ U` of a morphism between
  restrictions to `U` of two objects of the categorical fibre product.
* `AlgebraicGeometry.frobeniusColimitLocalSolution`: a local solution over `V`, moved to `W ≤ V`.
* `AlgebraicGeometry.frobeniusColimitFreeRes`, `…FreeResIso`, `…ResChart`: restriction of
  morphisms of free modules, of isomorphisms of free modules and of free charts
  `(V.ι)^*N ≅ 𝒪^{⊕n}`.

## Main results

* `AlgebraicGeometry.frobeniusColimitLocResHom_trans`, `…LocalSolution_trans`: moving twice is
  moving once.
* `AlgebraicGeometry.frobeniusColimitFreeRes_localSolution`: the comparison of two local solutions
  restricts to the comparison of the moved solutions.

## Implementation notes

Every coherence here is first proved as a statement about abstract functors and isomorphisms
(`CategoryTheory.resHom_trans`, `CategoryTheory.locSol_trans`, `CategoryTheory.resSol`,
`CategoryTheory.resLam`) and then instantiated.  Rewriting directly in the concrete categorical
fibre products of the restricted squares unfolds the Frobenius colimits and exhausts the heartbeat
budget, while the abstract statements are cheap and the instantiation is a single `exact`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-! ### Free modules under the transition functors -/

section Free

/-- **The transition functor carries the free finite locally free module of rank `n` to the free
one**, on the categories of finite locally free modules over the Frobenius colimits. -/
noncomputable def frobeniusColimitFreeVectorBundlePullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hY : IsInCharacteristic Y p) (hX : IsInCharacteristic X p) (n : ℕ) :
    (frobeniusColimitVectorBundlesPullback p f hY hX).obj
        (frobeniusColimitFreeVectorBundle p hX n) ≅
      frobeniusColimitFreeVectorBundle p hY n :=
  ObjectProperty.isoMk _
    (_root_.SheafOfModules.pullbackObjFreeIso (frobeniusColimitStructureSheafHom p f hY hX) _)

/-- The free identifications are compatible with the triangle comparison. -/
theorem frobeniusColimitFreeVectorBundlePullbackIso_triangle {X Y Z : Scheme.{u}} (f : Z ⟶ Y)
    (g : Y ⟶ X) (fg : Z ⟶ X) (hZ : IsInCharacteristic Z p) (hY : IsInCharacteristic Y p)
    (hX : IsInCharacteristic X p) (w : f ≫ g = fg) (n : ℕ) :
    (frobeniusColimitVectorBundlesPullbackTriangleIso p f g fg hZ hY hX w).hom.app
          (frobeniusColimitFreeVectorBundle p hX n) ≫
        (frobeniusColimitFreeVectorBundlePullbackIso p fg hZ hX n).hom =
      (frobeniusColimitVectorBundlesPullback p f hZ hY).map
          (frobeniusColimitFreeVectorBundlePullbackIso p g hY hX n).hom ≫
        (frobeniusColimitFreeVectorBundlePullbackIso p f hZ hY n).hom := by
  subst w
  refine ObjectProperty.hom_ext _ ?_
  simp only [frobeniusColimitVectorBundlesPullbackTriangleIso_rfl,
    ObjectProperty.FullSubcategory.comp_hom, frobeniusColimitVectorBundlesPullbackComp_hom_app_hom,
    frobeniusColimitFreeVectorBundlePullbackIso, frobeniusColimitVectorBundlesPullback_map_hom]
  exact frobeniusColimitPullbackComp_free p f g hZ hY hX _

end Free


/-! ### Abstract bookkeeping for restrictions -/

section Abstract

variable {C D₁ D₂ D₃ : Type*} [Category C] [Category D₁] [Category D₂] [Category D₃]

/-- The pentagon for the restriction comparisons, in terms of the inverse isomorphisms. -/
private theorem inv_app_comp_map_inv_app_of_pentagon {C D₁ D₂ D₃ : Type*} [Category C]
    [Category D₁] [Category D₂] [Category D₃] (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂) (L₃ : C ⥤ D₃)
    (N₁₂ : D₁ ⥤ D₂) (N₂₃ : D₂ ⥤ D₃) (N₁₃ : D₁ ⥤ D₃) (R₂ : L₁ ⋙ N₁₂ ≅ L₂) (R₃ : L₂ ⋙ N₂₃ ≅ L₃)
    (R₃' : L₁ ⋙ N₁₃ ≅ L₃) (NC : N₁₂ ⋙ N₂₃ ≅ N₁₃)
    (pent : ∀ S, N₂₃.map (R₂.hom.app S) ≫ R₃.hom.app S = NC.hom.app (L₁.obj S) ≫ R₃'.hom.app S)
    (S : C) :
    R₃.inv.app S ≫ N₂₃.map (R₂.inv.app S) = R₃'.inv.app S ≫ NC.inv.app (L₁.obj S) := by
  rw [← cancel_mono (NC.hom.app (L₁.obj S) ≫ R₃'.hom.app S)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  rw [← pent, ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

omit [Fact p.Prime] in
/-- **Restricting twice is restricting once**, for an abstract system of restriction functors
satisfying the pentagon. -/
theorem _root_.CategoryTheory.resHom_trans (L₁ : C ⥤ D₁) (L₂ : C ⥤ D₂) (L₃ : C ⥤ D₃)
    (N₁₂ : D₁ ⥤ D₂) (N₂₃ : D₂ ⥤ D₃) (N₁₃ : D₁ ⥤ D₃) (R₂ : L₁ ⋙ N₁₂ ≅ L₂) (R₃ : L₂ ⋙ N₂₃ ≅ L₃)
    (R₃' : L₁ ⋙ N₁₃ ≅ L₃) (NC : N₁₂ ⋙ N₂₃ ≅ N₁₃)
    (pent : ∀ S, N₂₃.map (R₂.hom.app S) ≫ R₃.hom.app S = NC.hom.app (L₁.obj S) ≫ R₃'.hom.app S)
    {S S' : C} (α : L₁.obj S ⟶ L₁.obj S') :
    R₃.inv.app S ≫ N₂₃.map (R₂.inv.app S ≫ N₁₂.map α ≫ R₂.hom.app S') ≫ R₃.hom.app S' =
      R₃'.inv.app S ≫ N₁₃.map α ≫ R₃'.hom.app S' := by
  have hS := pent S
  have hS' := pent S'
  have hn := NC.hom.naturality α
  dsimp at hn
  have hSi := inv_app_comp_map_inv_app_of_pentagon L₁ L₂ L₃ N₁₂ N₂₃ N₁₃ R₂ R₃ R₃' NC pent S
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hS', reassoc_of% hSi, reassoc_of% hn, Iso.inv_hom_id_app_assoc]

omit [Fact p.Prime] in
/-- **Moving a local solution twice is moving it once**, in an abstract system of restriction
functors on the targets (`L`, `N`, the comparisons `C` and the pentagon) and on the sources (`P`,
the triangle comparison and the comparisons `NI` of the comparison functors `G`). -/
theorem _root_.CategoryTheory.locSol_trans {D𝒳 DV DW DW' CV CW CW' : Type*} [Category D𝒳]
    [Category DV] [Category DW] [Category DW'] [Category CV] [Category CW] [Category CW']
    (LV : D𝒳 ⥤ DV) (LW : D𝒳 ⥤ DW) (LW' : D𝒳 ⥤ DW')
    (NVW : DV ⥤ DW) (NWW' : DW ⥤ DW') (NVW' : DV ⥤ DW') (Ch : LV ⋙ NVW ≅ LW)
    (Ch' : LW ⋙ NWW' ≅ LW') (Chh : LV ⋙ NVW' ≅ LW') (NC : NVW ⋙ NWW' ≅ NVW')
    (pent : ∀ S, NWW'.map (Ch.hom.app S) ≫ Ch'.hom.app S = NC.hom.app (LV.obj S) ≫ Chh.hom.app S)
    (GV : CV ⥤ DV) (GW : CW ⥤ DW) (GW' : CW' ⥤ DW') (PVW : CV ⥤ CW) (PWW' : CW ⥤ CW')
    (PVW' : CV ⥤ CW') {FV : CV} {FW : CW} {FW' : CW'}
    (NIh : NVW.obj (GV.obj FV) ≅ GW.obj (PVW.obj FV))
    (NIh' : NWW'.obj (GW.obj FW) ≅ GW'.obj (PWW'.obj FW))
    (NIh'' : NWW'.obj (GW.obj (PVW.obj FV)) ≅ GW'.obj (PWW'.obj (PVW.obj FV)))
    (NIhh : NVW'.obj (GV.obj FV) ≅ GW'.obj (PVW'.obj FV))
    (hnc : ∀ {A B : DV} (f : A ⟶ B), NWW'.map (NVW.map f) ≫ NC.hom.app B =
      NC.hom.app A ≫ NVW'.map f)
    {FIh : PVW.obj FV ≅ FW}
    (hnat : NWW'.map (GW.map FIh.hom) ≫ NIh'.hom = NIh''.hom ≫ GW'.map (PWW'.map FIh.hom))
    {tri : PVW ⋙ PWW' ≅ PVW'}
    (hloc : NC.hom.app (GV.obj FV) ≫ NIhh.hom =
      NWW'.map NIh.hom ≫ NIh''.hom ≫ GW'.map (tri.hom.app FV))
    {FIh' : PWW'.obj FW ≅ FW'} {FIhh : PVW'.obj FV ≅ FW'} {T : D𝒳}
    (hfree : tri.hom.app FV ≫ FIhh.hom = PWW'.map FIh.hom ≫ FIh'.hom)
    (β : GV.obj FV ≅ LV.obj T) :
    (Ch'.app T).symm ≪≫ NWW'.mapIso ((Ch.app T).symm ≪≫ NVW.mapIso β.symm ≪≫ NIh ≪≫
      GW.mapIso FIh) ≪≫ NIh' ≪≫ GW'.mapIso FIh' =
    (Chh.app T).symm ≪≫ NVW'.mapIso β.symm ≪≫ NIhh ≪≫ GW'.mapIso FIhh := by
  have h1 := inv_app_comp_map_inv_app_of_pentagon LV LW LW' NVW NWW' NVW' Ch Ch' Chh NC pent T
  have h2 : NC.inv.app (LV.obj T) ≫ NWW'.map (NVW.map β.inv) =
      NVW'.map β.inv ≫ NC.inv.app (GV.obj FV) := by
    rw [← cancel_mono (NC.hom.app (GV.obj FV))]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, hnc,
      Iso.inv_hom_id_app_assoc]
  have h3 : NWW'.map NIh.hom ≫ NIh''.hom = NC.hom.app (GV.obj FV) ≫ NIhh.hom ≫
      GW'.map (tri.inv.app FV) := by
    rw [← cancel_mono (GW'.map (tri.hom.app FV))]
    simp [hloc]
  have h4 : tri.inv.app FV ≫ PWW'.map FIh.hom ≫ FIh'.hom = FIhh.hom := by
    rw [← hfree, Iso.inv_hom_id_app_assoc]
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, CategoryTheory.Functor.map_comp,
    Category.assoc, Iso.app_inv]
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% hnat, reassoc_of% h3,
    Iso.inv_hom_id_app_assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp, h4]

omit [Fact p.Prime] in
/-- **The comparison of two local solutions restricts to the comparison of the restricted
solutions**, abstractly. -/
theorem _root_.CategoryTheory.resSol {C₀ C₁ D₀ D₁ : Type*} [Category C₀] [Category C₁]
    [Category D₀] [Category D₁] (N : D₀ ⥤ D₁) (G₀ : C₀ ⥤ D₀) (G₁ : C₁ ⥤ D₁) (P : C₀ ⥤ C₁)
    (NI : P ⋙ G₁ ≅ G₀ ⋙ N) {F₁ F₂ : C₀} {F₁' F₂' : C₁} (FI₁ : P.obj F₁ ≅ F₁')
    (FI₂ : P.obj F₂ ≅ F₂') {L : D₀} {L' : D₁} (Cm : N.obj L ≅ L') (ρ₁ : L ≅ G₀.obj F₁)
    (ρ₂ : L ≅ G₀.obj F₂) (f : F₁ ⟶ F₂) (hf : G₀.map f = ρ₁.inv ≫ ρ₂.hom) :
    G₁.map (FI₁.inv ≫ P.map f ≫ FI₂.hom) =
      (Cm.symm ≪≫ N.mapIso ρ₁ ≪≫ (NI.app F₁).symm ≪≫ G₁.mapIso FI₁).inv ≫
        (Cm.symm ≪≫ N.mapIso ρ₂ ≪≫ (NI.app F₂).symm ≪≫ G₁.mapIso FI₂).hom := by
  have hn := NI.hom.naturality f
  dsimp at hn
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv,
    Functor.mapIso_hom, Category.assoc, Iso.app_hom, Iso.app_inv, Iso.hom_inv_id_assoc,
    CategoryTheory.Functor.map_comp]
  rw [← CategoryTheory.Functor.map_comp_assoc N ρ₁.inv, ← hf, ← reassoc_of% hn]
  simp

omit [Fact p.Prime] in
/-- **Restricting a glued local isomorphism**, abstractly: the restriction to `W ≤ V` of the
isomorphism `L_V (G M) ≅ G_V (M|_V) ≅ G_V F ≅ L_V T` built from a chart `M|_V ≅ F` and a local
solution is the restricted chart followed by the moved local solution. -/
theorem _root_.CategoryTheory.resLam {D𝒳 DV DW CX CV CW : Type*} [Category D𝒳] [Category DV]
    [Category DW] [Category CX] [Category CV] [Category CW]
    (LV : D𝒳 ⥤ DV) (LW : D𝒳 ⥤ DW) (N : DV ⥤ DW) (Ch : LV ⋙ N ≅ LW) (GX : CX ⥤ D𝒳)
    (GV : CV ⥤ DV) (GW : CW ⥤ DW) (PV : CX ⥤ CV) (PW : CX ⥤ CW) (Pvw : CV ⥤ CW)
    (LRIV : ∀ M, LV.obj (GX.obj M) ≅ GV.obj (PV.obj M))
    (LRIW : ∀ M, LW.obj (GX.obj M) ≅ GW.obj (PW.obj M))
    (NI : Pvw ⋙ GW ≅ GV ⋙ N) (tri : PV ⋙ Pvw ≅ PW) {M : CX}
    (hP1b : Ch.hom.app (GX.obj M) ≫ (LRIW M).hom =
      N.map (LRIV M).hom ≫ (NI.app (PV.obj M)).inv ≫ GW.map (tri.hom.app M))
    {F : CV} {FW : CW} (c : PV.obj M ≅ F) (FI : Pvw.obj F ≅ FW) {T : D𝒳}
    (β : GV.obj F ≅ LV.obj T) :
    Ch.inv.app (GX.obj M) ≫ N.map ((LRIV M).hom ≫ GV.map c.hom ≫ β.hom) ≫ Ch.hom.app T =
      (LRIW M).hom ≫ GW.map (tri.inv.app M ≫ Pvw.map c.hom ≫ FI.hom) ≫
        ((Ch.app T).symm ≪≫ N.mapIso β.symm ≪≫ (NI.app F).symm ≪≫ GW.mapIso FI).inv := by
  have h1 : Ch.inv.app (GX.obj M) ≫ N.map (LRIV M).hom =
      (LRIW M).hom ≫ GW.map (tri.inv.app M) ≫ NI.hom.app (PV.obj M) := by
    have e1 : GW.map (tri.hom.app M) ≫ GW.map (tri.inv.app M) = 𝟙 _ := by
      rw [← GW.map_comp, Iso.hom_inv_id_app]; exact GW.map_id _
    rw [← cancel_epi (Ch.hom.app (GX.obj M)), Iso.hom_inv_id_app_assoc, reassoc_of% hP1b,
      reassoc_of% e1, Iso.app_inv, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  have hn : GW.map (Pvw.map c.hom) ≫ NI.hom.app F = NI.hom.app (PV.obj M) ≫ N.map (GV.map c.hom) :=
    NI.hom.naturality c.hom
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have e2 : GW.map FI.hom ≫ GW.map FI.inv = 𝟙 _ := by
    rw [← GW.map_comp, Iso.hom_inv_id]; exact GW.map_id _
  rw [reassoc_of% h1, reassoc_of% e2, reassoc_of% hn]

end Abstract

/-! ### Restricting isomorphisms to a smaller open -/

section Res

variable {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)

/-- **Restriction of a morphism between restrictions to `U` to a morphism between restrictions to
`U' ≤ U`**, through the restriction comparisons. -/
noncomputable def frobeniusColimitLocResHom {U U' : X.Opens} (h : U' ≤ U)
    {S S' : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')}
    (α : (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S') :
    (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U').obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U').obj S' :=
  (frobeniusColimitLocRestrictComp p b z q e hX' hZ hE hw h).inv.app S ≫
    (frobeniusColimitLocNested p b z q e hX' hZ hE hw h).map α ≫
    (frobeniusColimitLocRestrictComp p b z q e hX' hZ hE hw h).hom.app S'

variable {U U' : X.Opens} (h : U' ≤ U)
  {S S' S'' : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')}

/-- Restriction to `U' ≤ U` of morphisms between restrictions to `U` preserves composition. -/
theorem frobeniusColimitLocResHom_comp
    (α : (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S')
    (α' : (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S' ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S'') :
    frobeniusColimitLocResHom p b z q e hX' hZ hE hw h (α ≫ α') =
      frobeniusColimitLocResHom p b z q e hX' hZ hE hw h α ≫
        frobeniusColimitLocResHom p b z q e hX' hZ hE hw h α' := by
  simp [frobeniusColimitLocResHom]

/-- Restriction to `U' ≤ U` of morphisms between restrictions to `U` preserves identities. -/
theorem frobeniusColimitLocResHom_id :
    frobeniusColimitLocResHom p b z q e hX' hZ hE hw h
        (𝟙 ((frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S)) = 𝟙 _ := by
  simp [frobeniusColimitLocResHom]

/-- **Restricting a morphism twice, to `U' ≤ U` and then to `U'' ≤ U'`, is restricting it once to
`U'' ≤ U`.** -/
theorem frobeniusColimitLocResHom_trans {U'' : X.Opens} (h' : U'' ≤ U')
    (α : (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S') :
    frobeniusColimitLocResHom p b z q e hX' hZ hE hw h'
        (frobeniusColimitLocResHom p b z q e hX' hZ hE hw h α) =
      frobeniusColimitLocResHom p b z q e hX' hZ hE hw (h'.trans h) α :=
  CategoryTheory.resHom_trans _ _ _ _ _ _ _ _ _ _
    (frobeniusColimitLocRestrictComp_pentagon p b z q e hX' hZ hE hw h h') α

end Res


/-! ### The local solutions, moved to a smaller open -/

section Local

variable {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)
  (T : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX'))

local notation "G[" U "]" => frobeniusColimitComparisonRestrict p b z q e hX hX' hZ hE hw U
local notation "L[" U "]" => frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U
local notation "N[" h "]" => frobeniusColimitLocNested p b z q e hX' hZ hE hw h
local notation "NI[" h "]" => frobeniusColimitLocNestedIso p b z q e hX hX' hZ hE hw h
local notation "C[" h "]" => frobeniusColimitLocRestrictComp p b z q e hX' hZ hE hw h
local notation "F[" U ", " n "]" =>
  frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX U) n
local notation "FI[" h ", " n "]" => frobeniusColimitFreeVectorBundlePullbackIso p
  (Scheme.homOfLE _ h) (isInCharacteristic_toScheme hX _) (isInCharacteristic_toScheme hX _) n

/-- **A local free solution over `V`, moved to an open `W ≤ V`.** -/
noncomputable def frobeniusColimitLocalSolution {V : X.Opens} (n : ℕ)
    (β : G[V].obj F[V, n] ≅ L[V].obj T) {W : X.Opens} (h : W ≤ V) :
    L[W].obj T ≅ G[W].obj F[W, n] :=
  (C[h].app T).symm ≪≫ N[h].mapIso β.symm ≪≫ NI[h] F[V, n] ≪≫ G[W].mapIso FI[h, n]

/-- **Moving a local solution twice is moving it once.** -/
theorem frobeniusColimitLocalSolution_trans {V : X.Opens} (n : ℕ)
    (β : G[V].obj F[V, n] ≅ L[V].obj T) {W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) :
    (C[h'].app T).symm ≪≫ N[h'].mapIso (frobeniusColimitLocalSolution p b z q e hX hX' hZ hE hw
        T n β h) ≪≫ NI[h'] F[W, n] ≪≫ G[W'].mapIso FI[h', n] =
      frobeniusColimitLocalSolution p b z q e hX hX' hZ hE hw T n β (h'.trans h) :=
  CategoryTheory.locSol_trans _ _ _ _ _ _ _ _ _ _
    (frobeniusColimitLocRestrictComp_pentagon p b z q e hX' hZ hE hw h h') _ _ _ _ _ _
    (NI[h] F[V, n]) (NI[h'] F[W, n]) (NI[h'] _) (NI[h'.trans h] F[V, n])
    (fun f => frobeniusColimitLocNestedComp_naturality p b z q e hX' hZ hE hw h h' f)
    (frobeniusColimitLocNestedIso_naturality p b z q e hX hX' hZ hE hw h' FI[h, n].hom)
    (frobeniusColimitLocNestedComp_locIso p b z q e hX hX' hZ hE hw h h' F[V, n])
    (frobeniusColimitFreeVectorBundlePullbackIso_triangle p (X.homOfLE h')
      (X.homOfLE h) (X.homOfLE (h'.trans h)) (isInCharacteristic_toScheme hX W')
      (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V)
      (Scheme.homOfLE_homOfLE X h' h) n) β

/-- The comparison of the comparison functors with restriction from `U` to `U' ≤ U`, as a natural
isomorphism. -/
noncomputable def frobeniusColimitLocNestedNatIso {U U' : X.Opens} (h : U' ≤ U) :
    frobeniusColimitVectorBundlesPullback p (X.homOfLE h) (isInCharacteristic_toScheme hX U')
        (isInCharacteristic_toScheme hX U) ⋙ G[U'] ≅ G[U] ⋙ N[h] :=
  NatIso.ofComponents (fun M => (NI[h] M).symm) (fun f => by
    simp only [Functor.comp_map, Iso.symm_hom]
    rw [Iso.comp_inv_eq, Category.assoc,
      frobeniusColimitLocNestedIso_naturality p b z q e hX hX' hZ hE hw h f,
      Iso.inv_hom_id_assoc])

/-- **Restriction of a morphism of free modules over `W` to `W' ≤ W`**, through the free
identifications. -/
noncomputable def frobeniusColimitFreeRes {W W' : X.Opens} (h : W' ≤ W) {n n' : ℕ}
    (f : F[W, n] ⟶ F[W, n']) : F[W', n] ⟶ F[W', n'] :=
  FI[h, n].inv ≫ (frobeniusColimitVectorBundlesPullback p (X.homOfLE h)
    (isInCharacteristic_toScheme hX W') (isInCharacteristic_toScheme hX W)).map f ≫ FI[h, n'].hom

/-- **The comparison of two local solutions restricts to the comparison of the restricted
solutions.** -/
theorem frobeniusColimitFreeRes_localSolution {V₁ V₂ : X.Opens} {n₁ n₂ : ℕ}
    (β₁ : G[V₁].obj F[V₁, n₁] ≅ L[V₁].obj T) (β₂ : G[V₂].obj F[V₂, n₂] ≅ L[V₂].obj T)
    {W W' : X.Opens} (h₁ : W ≤ V₁) (h₂ : W ≤ V₂) (h : W' ≤ W) (f : F[W, n₁] ⟶ F[W, n₂])
    (hf : G[W].map f =
      (frobeniusColimitLocalSolution p b z q e hX hX' hZ hE hw T n₁ β₁ h₁).inv ≫
        (frobeniusColimitLocalSolution p b z q e hX hX' hZ hE hw T n₂ β₂ h₂).hom) :
    G[W'].map (frobeniusColimitFreeRes p hX h f) =
      (frobeniusColimitLocalSolution p b z q e hX hX' hZ hE hw T n₁ β₁ (h.trans h₁)).inv ≫
        (frobeniusColimitLocalSolution p b z q e hX hX' hZ hE hw T n₂ β₂ (h.trans h₂)).hom := by
  rw [← frobeniusColimitLocalSolution_trans p b z q e hX hX' hZ hE hw T n₁ β₁ h₁ h,
    ← frobeniusColimitLocalSolution_trans p b z q e hX hX' hZ hE hw T n₂ β₂ h₂ h]
  exact CategoryTheory.resSol N[h] G[W] G[W'] _
    (frobeniusColimitLocNestedNatIso p b z q e hX hX' hZ hE hw h) FI[h, n₁] FI[h, n₂]
    (C[h].app T) _ _ f hf

end Local

/-! ### Restricting charts and isomorphisms of free modules -/

section Charts

variable {X : Scheme.{u}} (hX : IsInCharacteristic X p)

/-- The restriction of a chart `(V.ι)^* N ≅ free` to an open `W ≤ V`. -/
noncomputable def frobeniusColimitResChart {V W : X.Opens} (h : W ≤ V) {n : ℕ}
    {N : frobeniusColimitVectorBundles X p hX}
    (c : (frobeniusColimitVectorBundlesPullback p V.ι (isInCharacteristic_toScheme hX V) hX).obj N ≅
      frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX V) n) :
    (frobeniusColimitVectorBundlesPullback p W.ι (isInCharacteristic_toScheme hX W) hX).obj N ≅
      frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX W) n :=
  ((frobeniusColimitVectorBundlesPullbackTriangleIso p (X.homOfLE h) V.ι W.ι
      (isInCharacteristic_toScheme hX W) (isInCharacteristic_toScheme hX V) hX
      (Scheme.homOfLE_ι X h)).app N).symm ≪≫
    (frobeniusColimitVectorBundlesPullback p (X.homOfLE h) (isInCharacteristic_toScheme hX W)
      (isInCharacteristic_toScheme hX V)).mapIso c ≪≫
    frobeniusColimitFreeVectorBundlePullbackIso p (X.homOfLE h) (isInCharacteristic_toScheme hX W)
      (isInCharacteristic_toScheme hX V) n

/-- The restriction of an isomorphism of free modules over `W` to `W' ≤ W`. -/
noncomputable def frobeniusColimitFreeResIso {W W' : X.Opens} (h : W' ≤ W) {n n' : ℕ}
    (f : frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX W) n ≅
      frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX W) n') :
    frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX W') n ≅
      frobeniusColimitFreeVectorBundle p (isInCharacteristic_toScheme hX W') n' where
  hom := frobeniusColimitFreeRes p hX h f.hom
  inv := frobeniusColimitFreeRes p hX h f.inv
  hom_inv_id := by simp [frobeniusColimitFreeRes]
  inv_hom_id := by simp [frobeniusColimitFreeRes]

end Charts


end AlgebraicGeometry

end
