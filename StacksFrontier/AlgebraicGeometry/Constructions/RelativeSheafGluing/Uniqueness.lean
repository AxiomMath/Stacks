module

public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeSheafGluing.OpenImmersionSections

/-!
# Relative gluing of quasi-coherent sheaves: the data and uniqueness

This file defines `RelativeSheafGluingData`, a compatible family of quasi-coherent modules on a
relative scheme gluing datum, and its `RelativeSheafGluingData.Realization`s on the glued scheme.
It proves that a family of chart morphisms compatible along the transition maps is the inverse
image of a single morphism (`RelativeSheafGluingData.exists_hom_of_chartHom`), and deduces that a
realization is unique up to a unique isomorphism
(`RelativeSheafGluingData.existsUnique_iso_realization`, Stacks Project, Tag 01LI).
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

/-- A compatible family of quasi-coherent modules on a relative scheme gluing datum. -/
structure RelativeSheafGluingData (d : Scheme.Cover.RelativeGluingData 𝒰) where
  /-- The module on each member of the relative gluing datum. -/
  obj : ∀ i, (d.functor.obj i).Modules
  /-- Each local module is quasi-coherent. -/
  isQuasicoherent : ∀ i, (obj i).IsQuasicoherent
  /-- Restriction along a transition map identifies the corresponding local modules. -/
  transitionIso : ∀ {i j} (hij : i ⟶ j),
    (Scheme.Modules.pullback (d.functor.map hij)).obj (obj j) ≅ obj i
  /-- The transition isomorphisms obey the cocycle condition, with the canonical comparison
  between an iterated pullback and pullback along the composite. -/
  transitionIso_cocycle : ∀ {i j k} (hij : i ⟶ j) (hjk : j ⟶ k),
    (Scheme.Modules.pullbackCongr (d.functor.map_comp hij hjk)).hom.app (obj k) ≫
        (Scheme.Modules.pullbackComp (d.functor.map hij) (d.functor.map hjk)).inv.app (obj k) ≫
          (Scheme.Modules.pullback (d.functor.map hij)).map (transitionIso hjk).hom ≫
            (transitionIso hij).hom =
      (transitionIso (hij ≫ hjk)).hom

namespace RelativeSheafGluingData

variable {d : Scheme.Cover.RelativeGluingData 𝒰} (D : RelativeSheafGluingData d)

/-- A realization of relative sheaf gluing on the canonical relatively glued scheme. -/
structure Realization where
  /-- The glued module. -/
  sheaf : d.glued.Modules
  /-- The glued module is quasi-coherent. -/
  isQuasicoherent : sheaf.IsQuasicoherent
  /-- Identification of each prescribed local module with the restriction of the glued one. -/
  localIso : ∀ i, D.obj i ≅
    (Scheme.Modules.pullback (colimit.ι d.functor i)).obj sheaf
  /-- The local identifications recover the prescribed transition isomorphisms. -/
  compatible : ∀ {i j} (hij : i ⟶ j),
    (D.transitionIso hij).hom ≫ (localIso i).hom =
      (Scheme.Modules.pullback (d.functor.map hij)).map (localIso j).hom ≫
        (Scheme.Modules.pullbackComp (d.functor.map hij) (colimit.ι d.functor j)).hom.app sheaf ≫
          (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app sheaf

/-- Each chart map `d.cover.f i` of the cover of the glued scheme is an open immersion. -/
local instance (i : 𝒰.I₀) : IsOpenImmersion (d.cover.f i) :=
  d.cover.map_prop i

/-- Local directedness of the chart diagram, in the form the glueing argument needs: the
intersection of the images of two charts in the glued scheme is covered by the images of the
charts mapping to both of them. -/
lemma chart_inf_le_iSup (i j : 𝒰.I₀) :
    (colimit.ι d.functor i).opensRange ⊓ (colimit.ι d.functor j).opensRange ≤
      ⨆ k : Σ k : 𝒰.I₀, (k ⟶ i) × (k ⟶ j), (colimit.ι d.functor k.1).opensRange := by
  intro x hx
  obtain ⟨⟨xi, hxi⟩, ⟨xj, hxj⟩⟩ :
      x ∈ (colimit.ι d.functor i).opensRange ∧ x ∈ (colimit.ι d.functor j).opensRange := hx
  obtain ⟨k, fi, fj, z, hzi, -⟩ :=
    (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := d.functor)).mp (hxi.trans hxj.symm)
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨k, fi, fj⟩, z, ?_⟩
  rw [← colimit.w d.functor fi, Scheme.Hom.comp_apply, hzi]
  exact hxi

private lemma chartContained_isBasis :
    TopologicalSpace.Opens.IsBasis
      { U : TopologicalSpace.Opens d.glued |
        ∃ i : 𝒰.I₀, U ≤ (d.cover.f i).opensRange } := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨i, hxi⟩ := d.cover.isOpenCover_opensRange.exists_mem x
  refine ⟨U ⊓ (d.cover.f i).opensRange, ⟨i, inf_le_right⟩, ?_, inf_le_left⟩
  exact ⟨hx, hxi⟩

private lemma hom_ext_of_chart_pullbacks
    {M N : d.glued.Modules} (φ ψ : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.pullback (d.cover.f i)).map φ =
      (Scheme.Modules.pullback (d.cover.f i)).map ψ) : φ = ψ := by
  have hr (i) : (Scheme.Modules.restrictFunctor (d.cover.f i)).map φ =
      (Scheme.Modules.restrictFunctor (d.cover.f i)).map ψ := by
    apply (cancel_mono
      ((Scheme.Modules.restrictFunctorIsoPullback (d.cover.f i)).hom.app N)).1
    rw [(Scheme.Modules.restrictFunctorIsoPullback (d.cover.f i)).hom.naturality,
      (Scheme.Modules.restrictFunctorIsoPullback (d.cover.f i)).hom.naturality, h i]
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  apply (show TopCat.Sheaf _ d.glued from ⟨N.presheaf, N.isSheaf⟩).eq_of_locally_eq'
    (U := fun i => (d.cover.f i).opensRange ⊓ W) W (fun _ => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, d.cover.isOpenCover_opensRange.iSup_eq_top, top_inf_eq])
  intro i
  have he : φ.app ((d.cover.f i).opensRange ⊓ W) =
      ψ.app ((d.cover.f i).opensRange ⊓ W) := by
    have hh := congrArg
      (fun t => Scheme.Modules.Hom.app t ((d.cover.f i) ⁻¹ᵁ W)) (hr i)
    change φ.app ((d.cover.f i) ''ᵁ ((d.cover.f i) ⁻¹ᵁ W)) =
      ψ.app ((d.cover.f i) ''ᵁ ((d.cover.f i) ⁻¹ᵁ W)) at hh
    exact Eq.mp (congrArg (fun T => φ.app T = ψ.app T)
      ((d.cover.f i).image_preimage_eq_opensRange_inf W)) hh
  have hnφ := φ.mapPresheaf.naturality
    (homOfLE (show (d.cover.f i).opensRange ⊓ W ≤ W from inf_le_right)).op
  have hnψ := ψ.mapPresheaf.naturality
    (homOfLE (show (d.cover.f i).opensRange ⊓ W ≤ W from inf_le_right)).op
  change _ = _ at hnφ hnψ
  exact congrArg (fun t => (ConcreteCategory.hom t) s)
    (hnφ.symm.trans ((congrArg
      (fun t => M.presheaf.map (homOfLE inf_le_right).op ≫ t) he).trans hnψ))

private lemma iso_unique_of_local (A B : D.Realization)
    (e e' : A.sheaf ≅ B.sheaf)
    (he : ∀ i, (A.localIso i).hom ≫
      (Scheme.Modules.pullback (colimit.ι d.functor i)).map e.hom =
        (B.localIso i).hom)
    (he' : ∀ i, (A.localIso i).hom ≫
      (Scheme.Modules.pullback (colimit.ι d.functor i)).map e'.hom =
        (B.localIso i).hom) : e = e' := by
  apply Iso.ext
  refine hom_ext_of_chart_pullbacks _ _ fun i => ?_
  apply (cancel_epi (A.localIso i).hom).1
  change (A.localIso i).hom ≫
      (Scheme.Modules.pullback (colimit.ι d.functor i)).map e.hom =
    (A.localIso i).hom ≫
      (Scheme.Modules.pullback (colimit.ι d.functor i)).map e'.hom
  exact (he i).trans (he' i).symm

section Glueing

open AlgebraicGeometry.Scheme.Modules

/-- The comparison of two realizations over the `i`-th chart. -/
private noncomputable def comparison (A B : D.Realization) (i : 𝒰.I₀) :
    (Scheme.Modules.pullback (colimit.ι d.functor i)).obj A.sheaf ⟶
      (Scheme.Modules.pullback (colimit.ι d.functor i)).obj B.sheaf :=
  (A.localIso i).inv ≫ (B.localIso i).hom

/-- Two families of isomorphisms satisfying the same compatibility over a functor have a
compatible comparison. -/
private lemma comparison_aux {C E : Type*} [Category C] [Category E] (L : C ⥤ E)
    {Tj Aj Bj : C} {Ti Ai Bi : E} (αj : Tj ≅ Aj) (βj : Tj ≅ Bj) (αi : Ti ≅ Ai) (βi : Ti ≅ Bi)
    (t : L.obj Tj ⟶ Ti) (cA : L.obj Aj ⟶ Ai) (cB : L.obj Bj ⟶ Bi)
    (hA : t ≫ αi.hom = L.map αj.hom ≫ cA) (hB : t ≫ βi.hom = L.map βj.hom ≫ cB) :
    cA ≫ αi.inv ≫ βi.hom = L.map (αj.inv ≫ βj.hom) ≫ cB := by
  have h1 : L.map αj.hom ≫ cA ≫ αi.inv = t := by
    rw [← Category.assoc, ← hA, Category.assoc, αi.hom_inv_id, Category.comp_id]
  have key : cA ≫ αi.inv = L.map αj.inv ≫ t := by
    rw [← h1, ← Category.assoc, ← L.map_comp, αj.inv_hom_id, L.map_id, Category.id_comp]
  rw [L.map_comp, Category.assoc, ← hB, ← Category.assoc, key, Category.assoc]

private lemma comparison_compatible (A B : D.Realization) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    ((Scheme.Modules.pullbackComp (d.functor.map hij)
            (colimit.ι d.functor j)).hom.app A.sheaf ≫
        (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app A.sheaf) ≫
      comparison D A B i =
      (Scheme.Modules.pullback (d.functor.map hij)).map (comparison D A B j) ≫
        ((Scheme.Modules.pullbackComp (d.functor.map hij)
              (colimit.ι d.functor j)).hom.app B.sheaf ≫
          (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app B.sheaf) :=
  comparison_aux (Scheme.Modules.pullback (d.functor.map hij)) (A.localIso j) (B.localIso j)
    (A.localIso i) (B.localIso i) (D.transitionIso hij).hom _ _ (A.compatible hij)
    (B.compatible hij)

/-- A family of morphisms of the inverse images of two modules on the glued scheme, one over each
chart, compatible with the canonical comparisons along the transition maps of the datum.  This is
the local datum from which a global morphism is glued. -/
def IsChartCompatible {M N : d.glued.Modules}
    (c : ∀ i, (Scheme.Modules.pullback (colimit.ι d.functor i)).obj M ⟶
      (Scheme.Modules.pullback (colimit.ι d.functor i)).obj N) : Prop :=
  ∀ {i j : 𝒰.I₀} (hij : i ⟶ j),
    ((Scheme.Modules.pullbackComp (d.functor.map hij)
            (colimit.ι d.functor j)).hom.app M ≫
        (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app M) ≫ c i =
      (Scheme.Modules.pullback (d.functor.map hij)).map (c j) ≫
        ((Scheme.Modules.pullbackComp (d.functor.map hij)
              (colimit.ι d.functor j)).hom.app N ≫
          (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app N)

variable {M N : d.glued.Modules}
  (c : ∀ i, (Scheme.Modules.pullback (colimit.ι d.functor i)).obj M ⟶
    (Scheme.Modules.pullback (colimit.ι d.functor i)).obj N)

/-- A chart morphism, transported to the restriction functor, where it acts on sections. -/
private noncomputable def chartRestrictHom (i : 𝒰.I₀) :
    M.restrict (colimit.ι d.functor i) ⟶ N.restrict (colimit.ι d.functor i) :=
  ofPullbackHom (colimit.ι d.functor i) (c i)

/-- The local datum of a chart morphism over the range of the `i`-th chart, given on sections. -/
private noncomputable def chartHom (i : 𝒰.I₀) (V : d.glued.Opens)
    (hV : V ≤ (colimit.ι d.functor i).opensRange) : Γ(M, V) ⟶ Γ(N, V) :=
  chartApp (colimit.ι d.functor i) (chartRestrictHom c i) V hV

/-- The local datum of a chart morphism commutes with the restriction maps. -/
private lemma chartHom_map (i : 𝒰.I₀) (V W : d.glued.Opens)
    (hV : V ≤ (colimit.ι d.functor i).opensRange) (hWV : W ≤ V) (s : Γ(M, V)) :
    chartHom c i W (hWV.trans hV) (M.presheaf.map (homOfLE hWV).op s) =
      N.presheaf.map (homOfLE hWV).op (chartHom c i V hV s) :=
  chartApp_map (colimit.ι d.functor i) (chartRestrictHom c i) V W hV hWV s

/-- The local datum of a chart morphism is linear over the structure sheaf. -/
private lemma chartHom_smul (i : 𝒰.I₀) (V : d.glued.Opens)
    (hV : V ≤ (colimit.ι d.functor i).opensRange) (r : Γ(d.glued, V)) (s : Γ(M, V)) :
    chartHom c i V hV (r • s) = r • chartHom c i V hV s :=
  chartApp_smul (colimit.ι d.functor i) (chartRestrictHom c i) V hV r s

lemma image_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} [IsOpenImmersion f]
    [IsOpenImmersion f'] (h : f = f') (U : X.Opens) : f ''ᵁ U = f' ''ᵁ U := by
  subst h; rfl

/-- The local data attached to two charts joined by an arrow agree on every open contained
in the smaller chart. -/
private lemma chartHom_arrow (hc : IsChartCompatible c) {i j : 𝒰.I₀} (hij : i ⟶ j)
    {V : d.glued.Opens} (hVi : V ≤ (colimit.ι d.functor i).opensRange)
    (hVj : V ≤ (colimit.ι d.functor j).opensRange) :
    chartHom c i V hVi = chartHom c j V hVj := by
  have hwi : colimit.ι d.functor i ''ᵁ (colimit.ι d.functor i ⁻¹ᵁ V) = V :=
    image_preimage_eq_self _ hVi
  have hwj : colimit.ι d.functor j ''ᵁ
      (d.functor.map hij ''ᵁ (colimit.ι d.functor i ⁻¹ᵁ V)) = V :=
    (Scheme.Hom.comp_image (d.functor.map hij) (colimit.ι d.functor j) _).symm.trans
      ((image_congr (colimit.w d.functor hij) _).trans hwi)
  set ψ := (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app M ≫
    c i ≫ (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).inv.app N with hψ
  have h2 : (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app M ≫ c i =
        ψ ≫ (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app N := by
    rw [hψ, Category.assoc, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  have h1 : (Scheme.Modules.pullbackComp (d.functor.map hij)
        (colimit.ι d.functor j)).hom.app M ≫ ψ =
      (Scheme.Modules.pullback (d.functor.map hij)).map (c j) ≫
        (Scheme.Modules.pullbackComp (d.functor.map hij)
          (colimit.ι d.functor j)).hom.app N := by
    rw [hψ, ← Category.assoc, ← Category.assoc, hc hij,
      Category.assoc, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hcongr := ofPullbackHom_congr (colimit.w d.functor hij) ψ (c i) h2
  have hcomp := ofPullbackHom_comp (d.functor.map hij) (colimit.ι d.functor j) (c j) ψ h1
  rw [← hcomp] at hcongr
  rw [chartHom, chartHom, chartApp_eq _ _ hVi _ hwi, chartApp_eq _ _ hVj _ hwj]
  exact secHom_comp_congr (d.functor.map hij) (colimit.ι d.functor j)
    (colimit.w d.functor hij) (chartRestrictHom c j) (chartRestrictHom c i)
    hcongr _ V hwi hwj

/-- The local data attached to any two charts agree on every open contained in both. -/
private lemma chartHom_agree (hc : IsChartCompatible c) (i j : 𝒰.I₀) (V : d.glued.Opens)
    (hVi : V ≤ (colimit.ι d.functor i).opensRange)
    (hVj : V ≤ (colimit.ι d.functor j).opensRange) :
    chartHom c i V hVi = chartHom c j V hVj := by
  refine ConcreteCategory.hom_ext _ _ fun s => ?_
  refine eq_of_locally_eq_module N
    (fun k : Σ k : 𝒰.I₀, (k ⟶ i) × (k ⟶ j) =>
      V ⊓ (colimit.ι d.functor k.1).opensRange) V (fun _ => inf_le_left)
    (by rw [← inf_iSup_eq]; exact le_inf le_rfl ((le_inf hVi hVj).trans (chart_inf_le_iSup i j)))
    _ _ fun k => ?_
  rw [← chartHom_map c i V (V ⊓ (colimit.ι d.functor k.1).opensRange) hVi inf_le_left s,
    ← chartHom_map c j V (V ⊓ (colimit.ι d.functor k.1).opensRange) hVj inf_le_left s,
    ← chartHom_arrow c hc k.2.1 inf_le_right (inf_le_left.trans hVi),
    ← chartHom_arrow c hc k.2.2 inf_le_right (inf_le_left.trans hVj)]

/-- **A compatible family of morphisms over the charts comes from a global morphism of modules on
the relatively glued scheme.**  The inverse image of the global morphism on the `i`-th chart is
the `i`-th member of the family.

This is the gluing step of [Stacks, Tag 01LI]: taken at the comparison of two realizations it
gives their uniqueness, and it is stated for an arbitrary pair of modules on the glued scheme
because the induced morphism of [Stacks, Tag 01LK] is glued from the same data. -/
theorem exists_hom_of_chartHom (hc : IsChartCompatible c) :
    ∃ ψ : M ⟶ N, ∀ i,
      (Scheme.Modules.pullback (colimit.ι d.functor i)).map ψ = c i := by
  have hcov : ⨆ i : 𝒰.I₀, (colimit.ι d.functor i).opensRange = ⊤ :=
    d.cover.isOpenCover_opensRange.iSup_eq_top
  have hcovT : ⨆ a : {V : d.glued.Opens //
      ∃ i : 𝒰.I₀, V ≤ (colimit.ι d.functor i).opensRange}, (a : d.glued.Opens) = ⊤ :=
    top_le_iff.mp (hcov.ge.trans (iSup_le fun i =>
      le_iSup_of_le ⟨(colimit.ι d.functor i).opensRange, i, le_rfl⟩ le_rfl))
  obtain ⟨ψ, hψ, -⟩ := existsUnique_hom_of_cover_app (M := M) (N := N)
    (U := fun a : {V : d.glued.Opens //
      ∃ i : 𝒰.I₀, V ≤ (colimit.ι d.functor i).opensRange} => (a : d.glued.Opens)) hcovT
    (fun a V hV => chartHom c a.2.choose V (hV.trans a.2.choose_spec))
    (fun a V hV => chartHom_smul c a.2.choose V (hV.trans a.2.choose_spec))
    (fun a V W hV hWV s =>
      chartHom_map c a.2.choose V W (hV.trans a.2.choose_spec) hWV s)
    (fun a b V hVa hVb => chartHom_agree c hc a.2.choose b.2.choose V
      (hVa.trans a.2.choose_spec) (hVb.trans b.2.choose_spec))
  refine ⟨ψ, fun i => ?_⟩
  have hres : (Scheme.Modules.restrictFunctor (colimit.ι d.functor i)).map ψ =
      chartRestrictHom c i := by
    refine Scheme.Modules.hom_ext _ _ fun W => ?_
    have hle : colimit.ι d.functor i ''ᵁ W ≤ (colimit.ι d.functor i).opensRange :=
      Scheme.Hom.image_le_opensRange _ W
    have h := hψ ⟨(colimit.ι d.functor i).opensRange, i, le_rfl⟩
      (colimit.ι d.functor i ''ᵁ W) hle
    rw [chartHom_agree c hc _ i _ _ hle, chartHom, chartApp_eq _ _ hle W rfl,
      secHom_self] at h
    exact h
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback
    (colimit.ι d.functor i)).hom.naturality ψ
  rw [hres] at hnat
  apply (cancel_epi ((Scheme.Modules.restrictFunctorIsoPullback
    (colimit.ι d.functor i)).hom.app M)).1
  rw [← hnat, chartRestrictHom, ofPullbackHom, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

/-- The comparison of two realizations is induced by a global morphism of the glued modules. -/
private lemma exists_hom_of_realizations (A B : D.Realization) :
    ∃ ψ : A.sheaf ⟶ B.sheaf, ∀ i,
      (Scheme.Modules.pullback (colimit.ι d.functor i)).map ψ = comparison D A B i :=
  exists_hom_of_chartHom (comparison D A B) fun hij => comparison_compatible D A B hij


/-- **Stacks Project, Tag 01LI.**  *Uniqueness of the module on the canonical total space.*  A
quasi-coherent module on the relatively glued scheme carrying the prescribed local identifications
is unique up to a unique isomorphism: any two such modules `F`, `F'` admit exactly one isomorphism
`F ≅ F'` whose inverse image on each chart carries the local identification of `F` to that of `F'`.

The total space is the canonical one here; the same statement on an arbitrary gluing of `d` is
`RelativeSheafGluingData.existsUnique_iso_realizationOn`.  The other half of Tag 01LI's "moreover"
sentence, that the total space itself is unique up to a unique isomorphism over `S` compatible
with the charts, is `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.existsUnique_iso`, and the
combination of the two into a single uniqueness statement for the pair `(X, F)` is
`RelativeSheafGluingData.existsUnique_pairIso`. -/
lemma existsUnique_iso_realization (A B : D.Realization) :
    ∃! e : A.sheaf ≅ B.sheaf,
      ∀ i, (A.localIso i).hom ≫
          (Scheme.Modules.pullback (colimit.ι d.functor i)).map e.hom =
        (B.localIso i).hom := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_hom_of_realizations D A B
  obtain ⟨ψ', hψ'⟩ := exists_hom_of_realizations D B A
  have hcomp : ψ ≫ ψ' = 𝟙 A.sheaf := by
    apply hom_ext_of_chart_pullbacks
    intro i
    have h : (Scheme.Modules.pullback (colimit.ι d.functor i)).map (ψ ≫ ψ') =
        (Scheme.Modules.pullback (colimit.ι d.functor i)).map (𝟙 A.sheaf) := by
      rw [CategoryTheory.Functor.map_comp, hψ i, hψ' i]
      simp [comparison]
    exact h
  have hcomp' : ψ' ≫ ψ = 𝟙 B.sheaf := by
    apply hom_ext_of_chart_pullbacks
    intro i
    have h : (Scheme.Modules.pullback (colimit.ι d.functor i)).map (ψ' ≫ ψ) =
        (Scheme.Modules.pullback (colimit.ι d.functor i)).map (𝟙 B.sheaf) := by
      rw [CategoryTheory.Functor.map_comp, hψ' i, hψ i]
      simp [comparison]
    exact h
  have hkey : ∀ i, (A.localIso i).hom ≫
      (Scheme.Modules.pullback (colimit.ι d.functor i)).map ψ = (B.localIso i).hom := by
    intro i
    rw [hψ i]
    simp [comparison]
  exact ⟨⟨ψ, ψ', hcomp, hcomp'⟩, hkey, fun e he => iso_unique_of_local D A B e _ he hkey⟩

end Glueing

end RelativeSheafGluingData

end Stacks.AlgebraicGeometry.RelativeSheafGluing
