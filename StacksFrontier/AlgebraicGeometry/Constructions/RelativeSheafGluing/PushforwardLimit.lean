module

public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeSheafGluing.Uniqueness

/-!
# Relative gluing of quasi-coherent sheaves: the limit of pushforwards

The transition data of a `RelativeSheafGluingData` on sections, the diagram of pushforwards of
the local modules to the glued scheme, and the comparison
(`RelativeSheafGluingData.isIso_chartProj`) of the restriction of its limit to each chart with the
prescribed local module.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.AlgebraicGeometry.ModuleLimits

namespace Stacks.AlgebraicGeometry.RelativeSheafGluing

variable {S : Scheme.{u}} {𝒰 : S.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

namespace RelativeSheafGluingData

variable {d : Scheme.Cover.RelativeGluingData 𝒰} (D : RelativeSheafGluingData d)

section Glueing

open AlgebraicGeometry.Scheme.Modules

variable {M N : d.glued.Modules}
  (c : ∀ i, (Scheme.Modules.pullback (colimit.ι d.functor i)).obj M ⟶
    (Scheme.Modules.pullback (colimit.ι d.functor i)).obj N)

/-! ### Towards existence: the transition data on sections

The glued module is the limit, over the opposite of the chart category, of the pushforwards of
the local modules; its sections over an open `W` of the glued scheme are the families of sections
`s i` of `D.obj i` over `(colimit.ι d.functor i) ⁻¹ᵁ W` which the transition maps carry to one
another.  The material below puts the transition data of the datum into the form that
construction consumes: `transSec` is the transition map on sections, and `transSec_comp` is the
cocycle condition for it, obtained from `transitionIso_cocycle` through `cocycle_restrict`. -/

/-- The transition isomorphism of the datum, transported to the restriction functor, where it
acts on sections. -/
noncomputable def transRestrict {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (D.obj j).restrict (d.functor.map hij) ⟶ D.obj i :=
  (Scheme.Modules.restrictFunctorIsoPullback (d.functor.map hij)).hom.app (D.obj j) ≫
    (D.transitionIso hij).hom

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
private lemma isIso_transRestrict {i j : 𝒰.I₀} (hij : i ⟶ j) : IsIso (D.transRestrict hij) := by
  show IsIso ((Scheme.Modules.restrictFunctorIsoPullback (d.functor.map hij)).hom.app (D.obj j) ≫
    (D.transitionIso hij).hom)
  infer_instance

/-- The transition map of the datum, on sections: restriction along the transition morphism
identifies the sections of the `j`-th module over the image of an open of the `i`-th chart with
the sections of the `i`-th module over that open. -/
noncomputable def transSec {i j : 𝒰.I₀} (hij : i ⟶ j) (V : (d.functor.obj i).Opens) :
    Γ(D.obj j, d.functor.map hij ''ᵁ V) ⟶ Γ(D.obj i, V) :=
  (D.transRestrict hij).app V

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
private lemma isIso_transSec {i j : 𝒰.I₀} (hij : i ⟶ j) (V : (d.functor.obj i).Opens) :
    IsIso (D.transSec hij V) := by
  have := D.isIso_transRestrict hij
  show IsIso ((D.transRestrict hij).app V)
  infer_instance

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The transition map on sections commutes with the restriction maps. -/
private lemma transSec_presheaf_map {i j : 𝒰.I₀} (hij : i ⟶ j)
    {V V' : (d.functor.obj i).Opens} (h : V' ≤ V)
    (hi : d.functor.map hij ''ᵁ V' ≤ d.functor.map hij ''ᵁ V)
    (s : Γ(D.obj j, d.functor.map hij ''ᵁ V)) :
    D.transSec hij V' ((D.obj j).presheaf.map (homOfLE hi).op s) =
      (D.obj i).presheaf.map (homOfLE h).op (D.transSec hij V s) :=
  app_presheaf_map_le (D.transRestrict hij) h s

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- **The cocycle condition on sections.**  Transporting a section along the transition map of a
composite arrow is transporting it along the two factors in turn. -/
private lemma transSec_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)
    (V : (d.functor.obj i).Opens)
    (hle : d.functor.map hjk ''ᵁ (d.functor.map hij ''ᵁ V) ≤ d.functor.map (hij ≫ hjk) ''ᵁ V) :
    D.transSec (hij ≫ hjk) V =
      (D.obj k).presheaf.map (homOfLE hle).op ≫
        D.transSec hjk (d.functor.map hij ''ᵁ V) ≫ D.transSec hij V := by
  have hc := cocycle_restrict (d.functor.map_comp hij hjk) (D.transitionIso hij).hom
    (D.transitionIso hjk).hom (D.transitionIso (hij ≫ hjk)).hom
    (D.transitionIso_cocycle hij hjk)
  have h : D.transSec (hij ≫ hjk) V = _ :=
    congrArg (fun t => Scheme.Modules.Hom.app t V) hc
  refine h.trans ?_
  show (D.obj k).presheaf.map _ ≫ (D.obj k).presheaf.map _ ≫
    D.transSec hjk (d.functor.map hij ''ᵁ V) ≫ D.transSec hij V = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    Subsingleton.elim (_ ≫ _) ((homOfLE hle).op)]

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- `RelativeSheafGluingData.transSec_comp`, on sections. -/
private lemma transSec_comp_apply {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)
    (V : (d.functor.obj i).Opens)
    (hle : d.functor.map hjk ''ᵁ (d.functor.map hij ''ᵁ V) ≤ d.functor.map (hij ≫ hjk) ''ᵁ V)
    (s : Γ(D.obj k, d.functor.map (hij ≫ hjk) ''ᵁ V)) :
    D.transSec (hij ≫ hjk) V s =
      D.transSec hij V (D.transSec hjk (d.functor.map hij ''ᵁ V)
        ((D.obj k).presheaf.map (homOfLE hle).op s)) := by
  have h := ConcreteCategory.congr_hom (D.transSec_comp hij hjk V hle) s
  simpa only [ConcreteCategory.comp_apply] using h

/-- **Local directedness, in the form the existence construction needs.**  The part of the `j`-th
chart lying over an open contained in the image of the `i`-th chart is covered by the images of
the transition morphisms coming from the charts that map to both `i` and `j`. -/
private lemma preimage_le_iSup_image {i j : 𝒰.I₀} {W : d.glued.Opens}
    (hW : W ≤ (colimit.ι d.functor i).opensRange) :
    colimit.ι d.functor j ⁻¹ᵁ W ≤
      ⨆ k : Σ k : 𝒰.I₀, (k ⟶ i) × (k ⟶ j),
        d.functor.map k.2.2 ''ᵁ (colimit.ι d.functor k.1 ⁻¹ᵁ W) := by
  intro y hy
  obtain ⟨xi, hxi⟩ : ∃ x, colimit.ι d.functor i x = colimit.ι d.functor j y := hW hy
  obtain ⟨k, fi, fj, z, hzi, hzj⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := d.functor)).mp hxi
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, fi, fj⟩, z, ?_, hzj⟩
  show colimit.ι d.functor k z ∈ W
  rw [← colimit.w d.functor fj, Scheme.Hom.comp_apply, hzj]
  exact hy

/-! ### Existence: the glued module as a limit of pushforwards

The glued module is the limit, over the opposite of the chart category, of the pushforwards
`(colimit.ι d.functor i)_* (D.obj i)`.  Its sections over an open `W` of the glued scheme are the
families of sections of the `D.obj i` over the preimages of `W` which the transition maps carry
to one another. -/

section Existence

variable {X Y Z : Scheme.{u}}

/-- The action on sections of a morphism out of a restriction, read as a map out of the sections
over the image open.  Pinning the type this way is what lets the calculus below be carried out
entirely in terms of `Γ(·, ·)`; cf. `RelativeSheafGluingData.transSec`. -/
noncomputable def restrictHomApp (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    {N : X.Modules} (θ : M.restrict f ⟶ N) (V : X.Opens) : Γ(M, f ''ᵁ V) ⟶ Γ(N, V) :=
  θ.app V

private lemma restrictHomApp_nat_aux (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    {N : X.Modules} (θ : M.restrict f ⟶ N) {V V' : X.Opens} (h : V' ≤ V)
    (hi : f ''ᵁ V' ≤ f ''ᵁ V) :
    θ.app V ≫ N.presheaf.map (homOfLE h).op =
      M.presheaf.map (homOfLE hi).op ≫ θ.app V' := by
  have hnat := θ.mapPresheaf.naturality (homOfLE h).op
  simp only [mapPresheaf_app, unop_op] at hnat
  rw [← hnat, restrict_map,
    Subsingleton.elim ((Scheme.Hom.opensFunctor f).map (homOfLE h)).op (homOfLE hi).op]
  rfl

/-- A morphism out of a restriction commutes with the restriction maps, at morphism level. -/
private lemma restrictHomApp_nat (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    {N : X.Modules} (θ : M.restrict f ⟶ N) {V V' : X.Opens} (h : V' ≤ V)
    (hi : f ''ᵁ V' ≤ f ''ᵁ V) :
    restrictHomApp f θ V ≫ N.presheaf.map (homOfLE h).op =
      M.presheaf.map (homOfLE hi).op ≫ restrictHomApp f θ V' :=
  restrictHomApp_nat_aux f θ h hi

private lemma pushSecApp_eq' (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules} {N : X.Modules}
    (θ : M.restrict f ⟶ N) (U : Y.Opens) :
    pushSecApp f θ U =
      M.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫ restrictHomApp f θ (f ⁻¹ᵁ U) := rfl

/-- `pushMap` on sections, read through the preimage along the composite. -/
private lemma pushMap_app' (f : X ⟶ Y) {g : Y ⟶ Z} {h : X ⟶ Z} (hg : f ≫ g = h)
    [IsOpenImmersion f] {M : Y.Modules} {N : X.Modules} (θ : M.restrict f ⟶ N) (W : Z.Opens)
    (h1 : f ''ᵁ (h ⁻¹ᵁ W) ≤ g ⁻¹ᵁ W) :
    (pushMap f hg θ).app W =
      M.presheaf.map (homOfLE h1).op ≫ restrictHomApp f θ (h ⁻¹ᵁ W) := by
  have hpi : h ⁻¹ᵁ W ≤ f ⁻¹ᵁ (g ⁻¹ᵁ W) := by rw [← Scheme.Hom.comp_preimage, hg]
  have hi : f ''ᵁ (h ⁻¹ᵁ W) ≤ f ''ᵁ (f ⁻¹ᵁ (g ⁻¹ᵁ W)) := Scheme.Hom.image_mono _ hpi
  rw [pushMap_app f hg θ W hpi, pushSecApp_eq', Category.assoc,
    restrictHomApp_nat f θ hpi hi, ← Category.assoc, ← M.presheaf.map_comp,
    Subsingleton.elim ((homOfLE (Scheme.Hom.image_preimage_le f (g ⁻¹ᵁ W))).op ≫
      (homOfLE hi).op) ((homOfLE h1).op)]

/-- A restriction map of an `𝒪`-module between two opens which are equal is an isomorphism. -/
private lemma isIso_presheaf_map (M : X.Modules) {V V' : X.Opens} (h : V' ≤ V) (he : V' = V) :
    IsIso (M.presheaf.map (homOfLE h).op) := by
  refine ⟨⟨M.presheaf.map (homOfLE he.ge).op, ?_, ?_⟩⟩
  · rw [← M.presheaf.map_comp,
      Subsingleton.elim ((homOfLE h).op ≫ (homOfLE he.ge).op) (𝟙 (op V)), M.presheaf.map_id]
  · rw [← M.presheaf.map_comp,
      Subsingleton.elim ((homOfLE he.ge).op ≫ (homOfLE h).op) (𝟙 (op V')), M.presheaf.map_id]

/-- Glueing of sections of an `𝒪`-module, in terms of `Γ`. -/
private lemma exists_gluing_module (M : X.Modules) {κ : Type*} (U : κ → X.Opens) (V : X.Opens)
    (iUV : ∀ a, U a ≤ V) (hcover : V ≤ iSup U) (sf : ∀ a, Γ(M, U a))
    (h : TopCat.Presheaf.IsCompatible M.presheaf U sf) :
    ∃ t : Γ(M, V), ∀ a, M.presheaf.map (homOfLE (iUV a)).op t = sf a := by
  obtain ⟨t, ht, -⟩ :=
    (Stacks.AlgebraicGeometry.QcqsLocalization.abSheaf M).existsUnique_gluing' U V
      (fun a => homOfLE (iUV a)) hcover sf h
  exact ⟨t, ht⟩

/-- Sections over `W`, as a functor on `𝒪`-modules.  It preserves limits because limits of
`𝒪`-modules are computed on the underlying presheaves. This is
`Stacks.AlgebraicGeometry.QcohLimits.sectionsFunctor`. -/
private noncomputable def secFun (X : Scheme.{u}) (W : X.Opens) : X.Modules ⥤ AddCommGrpCat.{u} :=
  QcohLimits.sectionsFunctor X W

private instance presSecFun (X : Scheme.{u}) (W : X.Opens) :
    PreservesLimitsOfSize.{u, u} (secFun X W) := by
  constructor
  intro J _
  have h3 : PreservesLimitsOfShape J
      ((evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab.{u}).obj (op W)) :=
    evaluation_preservesLimitsOfShape (op W)
  exact comp_preservesLimitsOfShape _ _

end Existence

section Diagram

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The image of an open under a composite of transition morphisms. -/
private lemma image_map_image {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)
    (V : (d.functor.obj i).Opens) :
    d.functor.map hjk ''ᵁ (d.functor.map hij ''ᵁ V) = d.functor.map (hij ≫ hjk) ''ᵁ V := by
  rw [← Scheme.Hom.comp_image]
  exact image_congr (d.functor.map_comp hij hjk).symm V

/-- The preimage of an open of the glued scheme in the `i`-th chart, computed through an arrow
`i ⟶ j`. -/
private lemma preimage_ι_eq (W : d.glued.Opens) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    colimit.ι d.functor i ⁻¹ᵁ W = d.functor.map hij ⁻¹ᵁ (colimit.ι d.functor j ⁻¹ᵁ W) := by
  rw [← Scheme.Hom.comp_preimage, colimit.w]

/-- A transition morphism carries the preimage of `W` in the source chart into its preimage in
the target chart. -/
lemma image_preimage_ι_le (W : d.glued.Opens) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    d.functor.map hij ''ᵁ (colimit.ι d.functor i ⁻¹ᵁ W) ≤ colimit.ι d.functor j ⁻¹ᵁ W := by
  rw [preimage_ι_eq W hij]
  exact Scheme.Hom.image_preimage_le _ _

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- `RelativeSheafGluingData.transSec_presheaf_map`, at morphism level. -/
lemma transSec_nat {i j : 𝒰.I₀} (hij : i ⟶ j) {V V' : (d.functor.obj i).Opens}
    (h : V' ≤ V) (hi : d.functor.map hij ''ᵁ V' ≤ d.functor.map hij ''ᵁ V) :
    D.transSec hij V ≫ (D.obj i).presheaf.map (homOfLE h).op =
      (D.obj j).presheaf.map (homOfLE hi).op ≫ D.transSec hij V' :=
  restrictHomApp_nat_aux _ (D.transRestrict hij) h hi

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The cocycle condition on sections, in the shape the glueing argument consumes: the opens over
which the three transition maps are read may be chosen freely. -/
private lemma transSec_comp_aux {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)
    {V : (d.functor.obj i).Opens} {Vj : (d.functor.obj j).Opens} {Vk : (d.functor.obj k).Opens}
    (hA : d.functor.map (hij ≫ hjk) ''ᵁ V ≤ Vk) (hB : d.functor.map hjk ''ᵁ Vj ≤ Vk)
    (hC : d.functor.map hij ''ᵁ V ≤ Vj) :
    (D.obj k).presheaf.map (homOfLE hA).op ≫ D.transSec (hij ≫ hjk) V =
      ((D.obj k).presheaf.map (homOfLE hB).op ≫ D.transSec hjk Vj) ≫
        ((D.obj j).presheaf.map (homOfLE hC).op ≫ D.transSec hij V) := by
  have hle : d.functor.map hjk ''ᵁ (d.functor.map hij ''ᵁ V) ≤
      d.functor.map (hij ≫ hjk) ''ᵁ V := (image_map_image hij hjk V).le
  have hiJ : d.functor.map hjk ''ᵁ (d.functor.map hij ''ᵁ V) ≤ d.functor.map hjk ''ᵁ Vj :=
    Scheme.Hom.image_mono _ hC
  have hmm : (D.obj k).presheaf.map (homOfLE hA).op ≫ (D.obj k).presheaf.map (homOfLE hle).op =
      (D.obj k).presheaf.map (homOfLE hB).op ≫ (D.obj k).presheaf.map (homOfLE hiJ).op := by
    rw [← (D.obj k).presheaf.map_comp, ← (D.obj k).presheaf.map_comp,
      Subsingleton.elim ((homOfLE hA).op ≫ (homOfLE hle).op)
        ((homOfLE hB).op ≫ (homOfLE hiJ).op)]
  rw [D.transSec_comp hij hjk V hle]
  simp only [Category.assoc]
  rw [reassoc_of% (D.transSec_nat hjk hC hiJ),
    ← Category.assoc ((D.obj k).presheaf.map (homOfLE hA).op),
    ← Category.assoc ((D.obj k).presheaf.map (homOfLE hB).op), hmm]

/-- The pushforward to the glued scheme of the `i`-th local module. -/
noncomputable abbrev push (i : 𝒰.I₀) : d.glued.Modules :=
  (Scheme.Modules.pushforward (colimit.ι d.functor i)).obj (D.obj i)

/-- The transition morphism between pushforwards attached to an arrow of charts. -/
noncomputable def pushTrans {i j : 𝒰.I₀} (hij : i ⟶ j) : D.push j ⟶ D.push i :=
  pushMap (d.functor.map hij) (colimit.w d.functor hij) (D.transRestrict hij)

/-- `RelativeSheafGluingData.pushTrans` on sections is the transition map on
sections. -/
private lemma pushTrans_app {i j : 𝒰.I₀} (hij : i ⟶ j) (W : d.glued.Opens) :
    (D.pushTrans hij).app W =
      (D.obj j).presheaf.map (homOfLE (image_preimage_ι_le W hij)).op ≫
        D.transSec hij (colimit.ι d.functor i ⁻¹ᵁ W) :=
  pushMap_app' _ (colimit.w d.functor hij) _ W (image_preimage_ι_le W hij)

lemma pushTrans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    D.pushTrans (hij ≫ hjk) = D.pushTrans hjk ≫ D.pushTrans hij := by
  refine Scheme.Modules.hom_ext _ _ fun W => ?_
  rw [Hom.comp_app, pushTrans_app, pushTrans_app, pushTrans_app]
  exact D.transSec_comp_aux hij hjk (image_preimage_ι_le W (hij ≫ hjk))
    (image_preimage_ι_le W hjk) (image_preimage_ι_le W hij)

private lemma isIso_pushTrans_id (i : 𝒰.I₀) : IsIso (D.pushTrans (𝟙 i)) := by
  rw [Hom.isIso_iff_isIso_app]
  intro W
  have heq : d.functor.map (𝟙 i) ''ᵁ (colimit.ι d.functor i ⁻¹ᵁ W) =
      colimit.ι d.functor i ⁻¹ᵁ W := by
    rw [image_congr (d.functor.map_id i) _, Scheme.Hom.id_image]
  have h1 := isIso_presheaf_map (D.obj i) (image_preimage_ι_le W (𝟙 i)) heq
  have h2 := D.isIso_transSec (𝟙 i) (colimit.ι d.functor i ⁻¹ᵁ W)
  rw [pushTrans_app]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 h2

lemma pushTrans_id (i : 𝒰.I₀) : D.pushTrans (𝟙 i) = 𝟙 (D.push i) := by
  have := D.isIso_pushTrans_id i
  have h3 := D.pushTrans_comp (𝟙 i) (𝟙 i)
  rw [Category.comp_id] at h3
  exact ((cancel_epi (D.pushTrans (𝟙 i))).mp (by rw [Category.comp_id]; exact h3)).symm

/-- **The diagram of pushforwards.**  The glued module is the limit of this functor. -/
noncomputable def pushFunctor : 𝒰.I₀ᵒᵖ ⥤ d.glued.Modules where
  obj a := D.push a.unop
  map {_ _} hab := D.pushTrans hab.unop
  map_id a := D.pushTrans_id a.unop
  map_comp {_ _ _} f g := D.pushTrans_comp g.unop f.unop

private instance : LocallySmall.{u} 𝒰.I₀ := ⟨fun _ _ => small_subsingleton _⟩

private instance essentiallySmall_I₀_op : EssentiallySmall.{u} 𝒰.I₀ᵒᵖ :=
  have : EssentiallySmall.{u} 𝒰.I₀ := essentiallySmall_of_small_of_locallySmall _
  inferInstance

instance : HasLimitsOfShape 𝒰.I₀ᵒᵖ d.glued.Modules :=
  hasLimitsOfShape_of_essentiallySmall.{u} 𝒰.I₀ᵒᵖ d.glued.Modules

private instance presSecChart (W : d.glued.Opens) :
    PreservesLimitsOfShape 𝒰.I₀ᵒᵖ (secFun d.glued W) :=
  preservesLimitsOfShape_of_equiv (equivSmallModel 𝒰.I₀ᵒᵖ).symm _

private instance presForgetChart : PreservesLimitsOfShape 𝒰.I₀ᵒᵖ (forget AddCommGrpCat.{u}) :=
  preservesLimitsOfShape_of_equiv (equivSmallModel 𝒰.I₀ᵒᵖ).symm _

end Diagram

section Comparison

/-- The inverse of the transition map on sections. -/
private noncomputable def transSecInv {i j : 𝒰.I₀} (hij : i ⟶ j) (V : (d.functor.obj i).Opens) :
    Γ(D.obj i, V) ⟶ Γ(D.obj j, d.functor.map hij ''ᵁ V) :=
  have := D.isIso_transSec hij V
  inv (D.transSec hij V)

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
private lemma transSec_transSecInv {i j : 𝒰.I₀} (hij : i ⟶ j) (V : (d.functor.obj i).Opens)
    (x : Γ(D.obj i, V)) : D.transSec hij V (D.transSecInv hij V x) = x := by
  have := D.isIso_transSec hij V
  exact ConcreteCategory.congr_hom (IsIso.inv_hom_id (D.transSec hij V)) x

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- The transition map on sections is injective. -/
private lemma transSec_inj {i j : 𝒰.I₀} (hij : i ⟶ j) (V : (d.functor.obj i).Opens)
    {x y : Γ(D.obj j, d.functor.map hij ''ᵁ V)}
    (h : D.transSec hij V x = D.transSec hij V y) : x = y := by
  have := D.isIso_transSec hij V
  have hh := ConcreteCategory.congr_hom (IsIso.hom_inv_id (D.transSec hij V))
  calc x = inv (D.transSec hij V) (D.transSec hij V x) := (hh x).symm
    _ = inv (D.transSec hij V) (D.transSec hij V y) := by rw [h]
    _ = y := hh y

/-- The image in the `a`-th chart of the preimage of `W` in the `k`-th chart is the preimage of
the part of `W` lying in the range of the `k`-th chart. -/
private lemma image_preimage_ι_eq (W : d.glued.Opens) {a k : 𝒰.I₀} (fa : k ⟶ a) :
    d.functor.map fa ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W) =
      colimit.ι d.functor a ⁻¹ᵁ ((colimit.ι d.functor k).opensRange ⊓ W) := by
  have h1 : colimit.ι d.functor k ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W) =
      colimit.ι d.functor a ''ᵁ (d.functor.map fa ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W)) := by
    rw [← Scheme.Hom.comp_image]
    exact image_congr (colimit.w d.functor fa).symm _
  rw [← Scheme.Hom.image_preimage_eq_opensRange_inf (colimit.ι d.functor k) W, h1,
    Scheme.Hom.preimage_image_eq]

/-- The pieces of the covering shrink along an arrow of charts. -/
private lemma piece_le (W : d.glued.Opens) {a l k : 𝒰.I₀} (g : l ⟶ k) (fa : k ⟶ a) :
    d.functor.map (g ≫ fa) ''ᵁ (colimit.ι d.functor l ⁻¹ᵁ W) ≤
      d.functor.map fa ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W) :=
  (image_map_image g fa _).ge.trans (Scheme.Hom.image_mono _ (image_preimage_ι_le W g))

/-- A piece of the covering depends only on its chart, since the chart category is thin. -/
private lemma piece_congr (W : d.glued.Opens) {a l : 𝒰.I₀} (f f' : l ⟶ a) :
    d.functor.map f ''ᵁ (colimit.ι d.functor l ⁻¹ᵁ W) =
      d.functor.map f' ''ᵁ (colimit.ι d.functor l ⁻¹ᵁ W) :=
  image_congr (congrArg (fun t => d.functor.map t) (Subsingleton.elim f f')) _

/-- **Local directedness on overlaps.**  The intersection of two pieces of the covering is
covered by the pieces coming from the charts mapping to both. -/
private lemma overlap_cover (W : d.glued.Opens) {i a : 𝒰.I₀}
    (p q : Σ k : 𝒰.I₀, (k ⟶ i) × (k ⟶ a)) :
    (d.functor.map p.2.2 ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W)) ⊓
        (d.functor.map q.2.2 ''ᵁ (colimit.ι d.functor q.1 ⁻¹ᵁ W)) ≤
      ⨆ r : Σ l : 𝒰.I₀, (l ⟶ p.1) × (l ⟶ q.1),
        d.functor.map (r.2.1 ≫ p.2.2) ''ᵁ (colimit.ι d.functor r.1 ⁻¹ᵁ W) := by
  have hr : ∀ r : Σ l : 𝒰.I₀, (l ⟶ p.1) × (l ⟶ q.1),
      d.functor.map (r.2.1 ≫ p.2.2) ''ᵁ (colimit.ι d.functor r.1 ⁻¹ᵁ W) =
        colimit.ι d.functor a ⁻¹ᵁ ((colimit.ι d.functor r.1).opensRange ⊓ W) :=
    fun r => image_preimage_ι_eq W (r.2.1 ≫ p.2.2)
  rw [image_preimage_ι_eq W p.2.2, image_preimage_ι_eq W q.2.2, ← Scheme.Hom.preimage_inf]
  simp only [hr, ← Scheme.Hom.preimage_iSup]
  refine Scheme.Hom.preimage_mono _ ?_
  calc ((colimit.ι d.functor p.1).opensRange ⊓ W) ⊓
        ((colimit.ι d.functor q.1).opensRange ⊓ W)
      ≤ ((colimit.ι d.functor p.1).opensRange ⊓ (colimit.ι d.functor q.1).opensRange) ⊓ W :=
        le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (inf_le_left.trans inf_le_right)
    _ ≤ (⨆ r : Σ l : 𝒰.I₀, (l ⟶ p.1) × (l ⟶ q.1),
          (colimit.ι d.functor r.1).opensRange) ⊓ W :=
        inf_le_inf_right W (chart_inf_le_iSup p.1 q.1)
    _ = ⨆ r : Σ l : 𝒰.I₀, (l ⟶ p.1) × (l ⟶ q.1),
          ((colimit.ι d.functor r.1).opensRange ⊓ W) := iSup_inf_eq _ _

variable {i : 𝒰.I₀} {W : d.glued.Opens}

/-- A section over an open contained in the range of the `i`-th chart, transported to the chart
`k` along an arrow `k ⟶ i`. -/
private noncomputable def chartSec (s : Γ(D.obj i, colimit.ι d.functor i ⁻¹ᵁ W)) (k : 𝒰.I₀)
    (fi : k ⟶ i) : Γ(D.obj k, colimit.ι d.functor k ⁻¹ᵁ W) :=
  D.transSec fi (colimit.ι d.functor k ⁻¹ᵁ W)
    ((D.obj i).presheaf.map (homOfLE (image_preimage_ι_le W fi)).op s)

private lemma chartSec_restrict (s : Γ(D.obj i, colimit.ι d.functor i ⁻¹ᵁ W)) {l k : 𝒰.I₀}
    (g : l ⟶ k) (fi : k ⟶ i) :
    D.transSec g (colimit.ι d.functor l ⁻¹ᵁ W)
        ((D.obj k).presheaf.map (homOfLE (image_preimage_ι_le W g)).op (D.chartSec s k fi)) =
      D.chartSec s l (g ≫ fi) := by
  have h := ConcreteCategory.congr_hom
    (D.transSec_comp_aux g fi (image_preimage_ι_le W (g ≫ fi)) (image_preimage_ι_le W fi)
      (image_preimage_ι_le W g)) s
  simp only [ConcreteCategory.comp_apply] at h
  exact h.symm

/-- The piece of the glued section over the image of the `k`-th chart. -/
private noncomputable def gluePiece (s : Γ(D.obj i, colimit.ι d.functor i ⁻¹ᵁ W)) (a k : 𝒰.I₀)
    (fi : k ⟶ i) (fa : k ⟶ a) :
    Γ(D.obj a, d.functor.map fa ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W)) :=
  D.transSecInv fa (colimit.ι d.functor k ⁻¹ᵁ W) (D.chartSec s k fi)

private lemma transSec_gluePiece (s : Γ(D.obj i, colimit.ι d.functor i ⁻¹ᵁ W)) (a k : 𝒰.I₀)
    (fi : k ⟶ i) (fa : k ⟶ a) :
    D.transSec fa (colimit.ι d.functor k ⁻¹ᵁ W) (D.gluePiece s a k fi fa) =
      D.chartSec s k fi :=
  D.transSec_transSecInv fa _ _

private lemma gluePiece_restrict (s : Γ(D.obj i, colimit.ι d.functor i ⁻¹ᵁ W))
    {a l k : 𝒰.I₀} (g : l ⟶ k) (fi : k ⟶ i) (fa : k ⟶ a) {fl : l ⟶ a} (hfl : fl = g ≫ fa)
    (hle : d.functor.map fl ''ᵁ (colimit.ι d.functor l ⁻¹ᵁ W) ≤
      d.functor.map fa ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W)) :
    (D.obj a).presheaf.map (homOfLE hle).op (D.gluePiece s a k fi fa) =
      D.gluePiece s a l (g ≫ fi) fl := by
  subst hfl
  refine D.transSec_inj (g ≫ fa) (colimit.ι d.functor l ⁻¹ᵁ W) ?_
  rw [transSec_gluePiece]
  have h := ConcreteCategory.congr_hom
    (D.transSec_comp_aux g fa hle
      (le_refl (d.functor.map fa ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W)))
      (image_preimage_ι_le W g)) (D.gluePiece s a k fi fa)
  simp only [ConcreteCategory.comp_apply] at h
  rw [h, module_presheaf_map_self, transSec_gluePiece, chartSec_restrict]

/-- The pieces glue: there is a section over the whole preimage of `W` in the `a`-th chart
restricting to each of them. -/
private lemma exists_glueSec (hW : W ≤ (colimit.ι d.functor i).opensRange)
    (s : Γ(D.obj i, colimit.ι d.functor i ⁻¹ᵁ W)) (a : 𝒰.I₀) :
    ∃ t : Γ(D.obj a, colimit.ι d.functor a ⁻¹ᵁ W),
      ∀ (k : 𝒰.I₀) (fi : k ⟶ i) (fa : k ⟶ a)
        (hle : d.functor.map fa ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W) ≤
          colimit.ι d.functor a ⁻¹ᵁ W),
        (D.obj a).presheaf.map (homOfLE hle).op t = D.gluePiece s a k fi fa := by
  have hcompat : TopCat.Presheaf.IsCompatible (D.obj a).presheaf
      (fun p : Σ k : 𝒰.I₀, (k ⟶ i) × (k ⟶ a) =>
        d.functor.map p.2.2 ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W))
      (fun p => D.gluePiece s a p.1 p.2.1 p.2.2) := by
    intro p q
    have hleft : ∀ r : Σ l : 𝒰.I₀, (l ⟶ p.1) × (l ⟶ q.1),
        d.functor.map (r.2.1 ≫ p.2.2) ''ᵁ (colimit.ι d.functor r.1 ⁻¹ᵁ W) ≤
          d.functor.map p.2.2 ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W) :=
      fun r => piece_le W r.2.1 p.2.2
    have hright : ∀ r : Σ l : 𝒰.I₀, (l ⟶ p.1) × (l ⟶ q.1),
        d.functor.map (r.2.1 ≫ p.2.2) ''ᵁ (colimit.ι d.functor r.1 ⁻¹ᵁ W) ≤
          d.functor.map q.2.2 ''ᵁ (colimit.ι d.functor q.1 ⁻¹ᵁ W) :=
      fun r => (piece_congr W (r.2.1 ≫ p.2.2) (r.2.2 ≫ q.2.2)).le.trans
        (piece_le W r.2.2 q.2.2)
    refine eq_of_locally_eq_module (D.obj a)
      (fun r : Σ l : 𝒰.I₀, (l ⟶ p.1) × (l ⟶ q.1) =>
        d.functor.map (r.2.1 ≫ p.2.2) ''ᵁ (colimit.ι d.functor r.1 ⁻¹ᵁ W))
      _ (fun r => le_inf (hleft r) (hright r)) (overlap_cover W p q) _ _ ?_
    intro r
    rw [presheaf_map_presheaf_map (D.obj a) _ _ (homOfLE (hleft r)).op,
      presheaf_map_presheaf_map (D.obj a) _ _ (homOfLE (hright r)).op,
      D.gluePiece_restrict s r.2.1 p.2.1 p.2.2 rfl (hleft r),
      D.gluePiece_restrict s r.2.2 q.2.1 q.2.2 (Subsingleton.elim _ _) (hright r)]
    exact congrArg (fun z => D.gluePiece s a r.1 z (r.2.1 ≫ p.2.2)) (Subsingleton.elim _ _)
  obtain ⟨t, ht⟩ := exists_gluing_module (D.obj a) _ (colimit.ι d.functor a ⁻¹ᵁ W)
    (fun p : Σ k : 𝒰.I₀, (k ⟶ i) × (k ⟶ a) => image_preimage_ι_le W p.2.2)
    (preimage_le_iSup_image hW) _ hcompat
  exact ⟨t, fun k fi fa _ => ht ⟨k, fi, fa⟩⟩

/-- The `a`-th component of a section of the glued module. -/
noncomputable def pic (a : 𝒰.I₀) (W : d.glued.Opens) :
    Γ(limit D.pushFunctor, W) ⟶ Γ(D.obj a, colimit.ι d.functor a ⁻¹ᵁ W) :=
  (limit.π D.pushFunctor (op a)).app W

/-- The components of a section of the glued module form a compatible family. -/
lemma pic_compat {a b : 𝒰.I₀} (f : a ⟶ b) (W : d.glued.Opens)
    (x : Γ(limit D.pushFunctor, W)) :
    D.transSec f (colimit.ι d.functor a ⁻¹ᵁ W)
        ((D.obj b).presheaf.map (homOfLE (image_preimage_ι_le W f)).op (D.pic b W x)) =
      D.pic a W x := by
  have key : (D.pic b W ≫ ((D.obj b).presheaf.map (homOfLE (image_preimage_ι_le W f)).op ≫
      D.transSec f (colimit.ι d.functor a ⁻¹ᵁ W)) :
        Γ(limit D.pushFunctor, W) ⟶ Γ(D.obj a, colimit.ι d.functor a ⁻¹ᵁ W)) = D.pic a W := by
    rw [← pushTrans_app]
    exact congrArg (fun z => Scheme.Modules.Hom.app z W) (limit.w D.pushFunctor (op f))
  simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom key x

/-- Two sections over the preimage of `W` in the `a`-th chart agree if their restrictions to the
images of the charts mapping to both `i` and `a` agree. -/
private lemma eq_of_restrict_eq_pieces (hW : W ≤ (colimit.ι d.functor i).opensRange) {a : 𝒰.I₀}
    {x y : Γ(D.obj a, colimit.ι d.functor a ⁻¹ᵁ W)}
    (h : ∀ p : Σ k : 𝒰.I₀, (k ⟶ i) × (k ⟶ a),
      (D.obj a).presheaf.map (homOfLE (image_preimage_ι_le W p.2.2)).op x =
        (D.obj a).presheaf.map (homOfLE (image_preimage_ι_le W p.2.2)).op y) :
    x = y :=
  eq_of_locally_eq_module (D.obj a)
    (fun p : Σ k : 𝒰.I₀, (k ⟶ i) × (k ⟶ a) =>
      d.functor.map p.2.2 ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W))
    _ (fun p => image_preimage_ι_le W p.2.2) (preimage_le_iSup_image hW) _ _ h

private lemma pic_inj (hW : W ≤ (colimit.ι d.functor i).opensRange)
    (x y : Γ(limit D.pushFunctor, W)) (h : D.pic i W x = D.pic i W y) : x = y := by
  refine Concrete.isLimit_ext (D.pushFunctor ⋙ secFun d.glued W)
    (isLimitOfPreserves (secFun d.glued W) (limit.isLimit D.pushFunctor)) x y ?_
  intro a
  obtain ⟨b, rfl⟩ : ∃ b, a = op b := ⟨a.unop, rfl⟩
  show D.pic b W x = D.pic b W y
  refine D.eq_of_restrict_eq_pieces hW fun p => ?_
  refine D.transSec_inj p.2.2 (colimit.ι d.functor p.1 ⁻¹ᵁ W) ?_
  rw [pic_compat, pic_compat, ← D.pic_compat p.2.1 W x, ← D.pic_compat p.2.1 W y, h]

private lemma pic_surj (hW : W ≤ (colimit.ι d.functor i).opensRange)
    (s : Γ(D.obj i, colimit.ι d.functor i ⁻¹ᵁ W)) :
    ∃ x : Γ(limit D.pushFunctor, W), D.pic i W x = s := by
  choose t ht using D.exists_glueSec hW s
  have ht' : ∀ (a k : 𝒰.I₀) (fi : k ⟶ i) (fa : k ⟶ a) {U : (d.functor.obj a).Opens}
      (hU : U ≤ d.functor.map fa ''ᵁ (colimit.ι d.functor k ⁻¹ᵁ W))
      (hle : U ≤ colimit.ι d.functor a ⁻¹ᵁ W),
      (D.obj a).presheaf.map (homOfLE hle).op (t a) =
        (D.obj a).presheaf.map (homOfLE hU).op (D.gluePiece s a k fi fa) := by
    intro a k fi fa U hU hle
    rw [← ht a k fi fa (image_preimage_ι_le W fa),
      presheaf_map_presheaf_map (D.obj a) _ (homOfLE hU).op (homOfLE hle).op]
  have hcomp : ∀ {a b : 𝒰.I₀} (f : a ⟶ b),
      D.transSec f (colimit.ι d.functor a ⁻¹ᵁ W)
        ((D.obj b).presheaf.map (homOfLE (image_preimage_ι_le W f)).op (t b)) = t a := by
    intro a b f
    refine D.eq_of_restrict_eq_pieces hW fun p => ?_
    have hi : d.functor.map f ''ᵁ
        (d.functor.map p.2.2 ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W)) ≤
        d.functor.map f ''ᵁ (colimit.ι d.functor a ⁻¹ᵁ W) :=
      Scheme.Hom.image_mono _ (image_preimage_ι_le W p.2.2)
    have hB : d.functor.map f ''ᵁ
        (d.functor.map p.2.2 ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W)) ≤
        d.functor.map (p.2.2 ≫ f) ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W) :=
      (image_map_image p.2.2 f _).le
    have hle2 : d.functor.map f ''ᵁ
        (d.functor.map p.2.2 ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W)) ≤
        colimit.ι d.functor b ⁻¹ᵁ W := hi.trans (image_preimage_ι_le W f)
    have hL := ConcreteCategory.congr_hom
      (D.transSec_nat f (image_preimage_ι_le W p.2.2) hi)
      ((D.obj b).presheaf.map (homOfLE (image_preimage_ι_le W f)).op (t b))
    simp only [ConcreteCategory.comp_apply] at hL
    rw [hL, presheaf_map_presheaf_map (D.obj b) _ _ (homOfLE hle2).op,
      ht' b p.1 p.2.1 (p.2.2 ≫ f) hB hle2, ht a p.1 p.2.1 p.2.2 (image_preimage_ι_le W p.2.2)]
    refine D.transSec_inj p.2.2 (colimit.ι d.functor p.1 ⁻¹ᵁ W) ?_
    rw [transSec_gluePiece]
    have h := ConcreteCategory.congr_hom
      (D.transSec_comp_aux p.2.2 f
        (le_refl (d.functor.map (p.2.2 ≫ f) ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W))) hB
        (le_refl (d.functor.map p.2.2 ''ᵁ (colimit.ι d.functor p.1 ⁻¹ᵁ W))))
      (D.gluePiece s b p.1 p.2.1 (p.2.2 ≫ f))
    simp only [ConcreteCategory.comp_apply, module_presheaf_map_self] at h
    rw [← h, transSec_gluePiece]
  have hself : t i = s := by
    refine D.eq_of_restrict_eq_pieces hW fun p => ?_
    rw [ht i p.1 p.2.1 p.2.2 (image_preimage_ι_le W p.2.2)]
    refine D.transSec_inj p.2.2 (colimit.ι d.functor p.1 ⁻¹ᵁ W) ?_
    rw [transSec_gluePiece]
    exact congrArg (D.chartSec s p.1) (Subsingleton.elim p.2.1 p.2.2)
  have hsec : ∀ {a b : 𝒰.I₀ᵒᵖ} (g : a ⟶ b),
      (D.pushFunctor ⋙ secFun d.glued W ⋙ forget AddCommGrpCat.{u}).map g (t a.unop) =
        t b.unop := by
    intro a b g
    have h3 : ((D.obj a.unop).presheaf.map (homOfLE (image_preimage_ι_le W g.unop)).op ≫
        D.transSec g.unop (colimit.ι d.functor b.unop ⁻¹ᵁ W)) (t a.unop) = t b.unop := by
      rw [ConcreteCategory.comp_apply]
      exact hcomp g.unop
    have h2 : (D.pushTrans g.unop).app W (t a.unop) = t b.unop := by
      rw [D.pushTrans_app]
      exact h3
    exact h2
  have hL := isLimitOfPreserves (secFun d.glued W) (limit.isLimit D.pushFunctor)
  have hL2 := isLimitOfPreserves (forget AddCommGrpCat.{u}) hL
  refine ⟨(Types.isLimitEquivSections hL2).symm ⟨fun a => t a.unop, hsec⟩, ?_⟩
  exact (Types.isLimitEquivSections_symm_apply hL2 ⟨fun a => t a.unop, hsec⟩ (op i)).trans hself

private lemma isIso_pic (hW : W ≤ (colimit.ι d.functor i).opensRange) : IsIso (D.pic i W) := by
  have hb : Function.Bijective (D.pic i W) :=
    ⟨fun x y h => D.pic_inj hW x y h, fun s => D.pic_surj hW s⟩
  have : IsIso ((forget AddCommGrpCat.{u}).map (D.pic i W)) := (isIso_iff_bijective _).mpr hb
  exact isIso_of_reflects_iso (D.pic i W) (forget AddCommGrpCat.{u})

/-- **The local comparison.**  The restriction of the glued module to the `i`-th chart is the
`i`-th local module. -/
noncomputable def chartProj (i : 𝒰.I₀) :
    (limit D.pushFunctor).restrict (colimit.ι d.functor i) ⟶ D.obj i :=
  (Scheme.Modules.restrictFunctor (colimit.ι d.functor i)).map
      (limit.π D.pushFunctor (op i)) ≫
    (Scheme.Modules.restrictAdjunction (colimit.ι d.functor i)).counit.app (D.obj i)

lemma chartProj_app (i : 𝒰.I₀) (V : (d.functor.obj i).Opens) :
    restrictHomApp (colimit.ι d.functor i) (D.chartProj i) V =
      D.pic i (colimit.ι d.functor i ''ᵁ V) ≫
        (D.obj i).presheaf.map
          (homOfLE (Scheme.Hom.preimage_image_eq (colimit.ι d.functor i) V).ge).op := by
  show (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor
        (colimit.ι d.functor i)).map (limit.π D.pushFunctor (op i))) V ≫
    Scheme.Modules.Hom.app ((Scheme.Modules.restrictAdjunction
        (colimit.ι d.functor i)).counit.app (D.obj i)) V :
      Γ(limit D.pushFunctor, colimit.ι d.functor i ''ᵁ V) ⟶ Γ(D.obj i, V)) = _
  rw [Scheme.Modules.restrictAdjunction_counit_app_app,
    presheaf_map_eq_presheaf_map (D.obj i) _
      (homOfLE (Scheme.Hom.preimage_image_eq (colimit.ι d.functor i) V).ge).op]
  rfl

lemma isIso_chartProj (i : 𝒰.I₀) : IsIso (D.chartProj i) := by
  rw [Hom.isIso_iff_isIso_app]
  intro V
  have := D.isIso_pic (Scheme.Hom.image_le_opensRange (colimit.ι d.functor i) V)
  have := isIso_presheaf_map (D.obj i)
    (Scheme.Hom.preimage_image_eq (colimit.ι d.functor i) V).ge
    (Scheme.Hom.preimage_image_eq (colimit.ι d.functor i) V).symm
  change IsIso (restrictHomApp (colimit.ι d.functor i) (D.chartProj i) V)
  rw [chartProj_app]
  infer_instance

end Comparison

end Glueing

end RelativeSheafGluingData

end Stacks.AlgebraicGeometry.RelativeSheafGluing
