module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional

/-!
# A quasi-coherent module on an affine algebraic space is the union of its finite type submodules

Let `V` be an affine algebraic space over a scheme `S` and `ℋ` a quasi-coherent `𝒪_V`-module.  This
file proves that the supremum of the quasi-coherent subobjects of `ℋ` of finite type is `ℋ`
itself, which is the colimit assertion of Stacks 0829 for an affine algebraic space.

The argument is the one for an affine scheme.  The chart `V ≅ Spec R` of `V` itself is terminal
in the small étale site, so every section of `ℋ` over it generates a quasi-coherent subobject of
finite type, the image of the corresponding morphism `𝒪_V ⟶ ℋ`.  Over an affine chart `W` of `V`
the sections of `ℋ` are the base change of the sections over the terminal chart, by Descent,
Proposition 03DX(2), so every section over `W` is a finite combination of restrictions of sections
over the terminal chart, and so lies in a finite supremum of such images.  Affine charts cover
every chart, so the inclusion of the supremum is locally surjective, hence an epimorphism, hence
an isomorphism.

## Main results

* `nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isAffineSpace`: a quasi-coherent
  module on an affine algebraic space is the colimit of its finite type quasi-coherent subobjects.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Terminal

variable {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ : BigFppfOver B S hS} (e : V ≅ yoneda.obj T₀)

/-- An isomorphism from a representable presheaf is an étale chart. -/
theorem isEtaleChart_mk_inv : IsEtaleChart B S hS V (CostructuredArrow.mk e.inv) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.inv, ?_⟩
  intro a b g fst snd h
  have h' : IsPullback (g ≫ CategoryTheory.inv e.inv) (𝟙 (yoneda.obj a)) e.inv g :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have _ : IsIso (yoneda.map snd) := by
    have h2 : IsIso ((h.isoIsPullback _ _ h').hom ≫ 𝟙 (yoneda.obj a)) := inferInstance
    rwa [h.isoIsPullback_hom_snd _ _ h'] at h2
  have _ : IsIso snd := isIso_of_reflects_iso snd yoneda
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map snd) := inferInstance
  show Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- The chart of an algebraic space `V` given by an isomorphism `e : V ≅ yoneda.obj T₀`, with
structure morphism `e.inv`. -/
def invIsoChart : SmallEtale B S hS V :=
  ⟨CostructuredArrow.mk e.inv, isEtaleChart_mk_inv B S hS e⟩

/-- The morphism from a chart to the chart given by an isomorphism with a representable. -/
def toIsoChart (W : SmallEtale B S hS V) : W ⟶ invIsoChart B S hS e :=
  ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage (W.obj.hom ≫ e.hom)) (by
    change yoneda.map (yoneda.preimage (W.obj.hom ≫ e.hom)) ≫ e.inv = W.obj.hom
    rw [Functor.map_preimage, Category.assoc, e.hom_inv_id, Category.comp_id]))

/-- Any two morphisms from a chart to the chart `invIsoChart B S hS e` are equal. -/
theorem toIsoChart_unique {W : SmallEtale B S hS V} (a b : W ⟶ invIsoChart B S hS e) : a = b := by
  have ha := a.hom.w
  have hb := b.hom.w
  have h : yoneda.map a.hom.left = yoneda.map b.hom.left := by
    have h' : yoneda.map a.hom.left ≫ e.inv = yoneda.map b.hom.left ≫ e.inv := by
      change yoneda.map a.hom.left ≫ e.inv = W.obj.hom ≫ 𝟙 _ at ha
      change yoneda.map b.hom.left ≫ e.inv = W.obj.hom ≫ 𝟙 _ at hb
      rw [ha, hb]
    exact (cancel_mono e.inv).mp h'
  have h₂ : a.hom.left = b.hom.left := yoneda.map_injective h
  exact ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h₂)

/-- If `T₀` is affine, then the scheme underlying the chart `invIsoChart B S hS e` is affine. -/
theorem isAffine_isoChart (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)) :
    IsAffine ((SmallEtale.toOver B S hS V ⋙ BigFppfOver.toScheme B S hS).obj
      (invIsoChart B S hS e)) := hT

end Terminal

section Generation

variable {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
  {T₀ : BigFppfOver B S hS} (e : V ≅ yoneda.obj T₀)
  (H : Modules.{u, u} B S hS V hV)

/-- The global section of `ℋ` determined by a section over the terminal chart. -/
def isoChartSection (n : H.val.obj (op (invIsoChart B S hS e))) : H.sections where
  val W := H.val.map (toIsoChart B S hS e W.unop).op n
  property {W W'} f := by
    let W₀ : SmallEtale B S hS V := W.unop
    let W₁ : SmallEtale B S hS V := W'.unop
    let f₀ : W₁ ⟶ W₀ := f.unop
    have h₁ := PresheafOfModules.map_comp_apply H.val (toIsoChart B S hS e W₀).op f₀.op n
    have h₂ : f₀ ≫ toIsoChart B S hS e W₀ = toIsoChart B S hS e W₁ := toIsoChart_unique B S hS e _ _
    have h₃ : H.val.map (f₀ ≫ toIsoChart B S hS e W₀).op n =
        H.val.map (toIsoChart B S hS e W₁).op n := by rw [h₂]
    exact h₁.symm.trans h₃

/-- The morphism `𝒪_V ⟶ ℋ` determined by a section over the terminal chart. -/
def isoChartSectionHom (n : H.val.obj (op (invIsoChart B S hS e))) :
    SheafOfModules.unit _ ⟶ H :=
  H.unitHomEquiv.symm (isoChartSection B S hS hV e H n)

/-- The morphism `isoChartSectionHom B S hS hV e H n` sends the section `1` over a chart `W` to
the restriction of `n` to `W`. -/
theorem isoChartSectionHom_app_one (n : H.val.obj (op (invIsoChart B S hS e)))
    (W : SmallEtale B S hS V) :
    (isoChartSectionHom B S hS hV e H n).val.app (op W)
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V hV).O).obj.obj
        (op W)) =
      H.val.map (toIsoChart B S hS e W).op n := by
  have h := H.unitHomEquiv_apply_coe (isoChartSectionHom B S hS hV e H n) (op W)
  have h' : H.unitHomEquiv (isoChartSectionHom B S hS hV e H n) =
      isoChartSection B S hS hV e H n := Equiv.apply_symm_apply _ _
  rw [h'] at h
  exact h.symm

set_option synthInstance.maxHeartbeats 200000 in
/-- The image of a morphism out of the structure sheaf is a finite type quasi-coherent
subobject. -/
theorem imageSubobject_unit_mem [H.IsQuasicoherentOnSite]
    (u : SheafOfModules.unit _ ⟶ H) :
    finiteTypeQuasicoherentSubobjectProperty B S hS V hV H (imageSubobject u) := by
  refine ⟨isQuasicoherentOnSite_image B S hS V hV
    (isClosedUnderKernels_quasicoherentSheaves B S hS V hV
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS V hV))
    (isClosedUnderCokernels_quasicoherentSheaves B S hS V hV) u
    (SheafOfModules.isQuasicoherentOnSite_unit _) inferInstance, ?_⟩
  have : Epi (factorThruImageSubobject u) := by
    dsimp [factorThruImageSubobject]
    apply epi_comp
  exact Stacks.SheafOfModules.isFiniteType_of_epi
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V hV).O))
    (factorThruImageSubobject u)
    inferInstance

end Generation

/-- **Stacks 0829, the colimit assertion, for an affine algebraic space.**  The supremum of the
quasi-coherent subobjects of finite type of a quasi-coherent module on an affine algebraic space
is the whole module. -/
theorem nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isAffineSpace
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (hVa : IsAffineSpace B S hS V) (H : Modules.{u, u} B S hS V hV)
    [hH : H.IsQuasicoherentOnSite] :
    Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS V hV H)) := by
  classical
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS V hV).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS V)
    infer_instance
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS V hV) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have hfiltered : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS V hV H) :=
    isFiltered_finiteTypeQuasicoherentSubobject B S hS V hV H
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hVa
  let T : Subobject H := ⨆ G : FiniteTypeQuasicoherentSubobject B S hS V hV H, G.obj
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS V hV H hH
  have hgen : ∀ (W : SmallEtale B S hS V) (n : H.val.obj (op (invIsoChart B S hS e))),
      H.val.map (toIsoChart B S hS e W).op n ∈ LinearMap.range (T.arrow.val.app (op W)).hom := by
    intro W n
    let u := isoChartSectionHom B S hS hV e H n
    let Gn : FiniteTypeQuasicoherentSubobject B S hS V hV H :=
      ⟨imageSubobject u, imageSubobject_unit_mem B S hS hV H u⟩
    have hle : Gn.obj ≤ T :=
      le_iSup (fun G : FiniteTypeQuasicoherentSubobject B S hS V hV H => G.obj) Gn
    have hfac : u = (factorThruImageSubobject u ≫ Subobject.ofLE _ _ hle) ≫ T.arrow := by
      rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
    refine ⟨(factorThruImageSubobject u ≫ Subobject.ofLE _ _ hle).val.app (op W)
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V hV).O).obj.obj
        (op W)), ?_⟩
    rw [← isoChartSectionHom_app_one B S hS hV e H n W]
    show (((factorThruImageSubobject u ≫ Subobject.ofLE _ _ hle) ≫ T.arrow).val.app (op W)) _ = _
    rw [← hfac]
  have hepi : Epi T.arrow := by
    refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective T.arrow ⟨fun {W} s => ?_⟩
    refine (SmallEtale.topology B S hS V).superset_covering ?_
      (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS V W)
    intro W' g hg
    obtain ⟨O, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    refine (Presheaf.imageSieve _ s).downward_closed ?_ a
    have hW'aff := isAffine_chartScheme_openChart B S hS V W O.down
    let f := toIsoChart B S hS e (openChart B S hS V W O.down.1)
    have hsurj := (hcart _ _ (isAffine_isoChart B S hS e hT₀) hW'aff f).2
    obtain ⟨x, hx⟩ := hsurj (H.val.map (openChartInclusion B S hS V W O.down.1).op s)
    have key : ∀ y, sectionsBaseChange H f y ∈
        LinearMap.range (T.arrow.val.app (op (openChart B S hS V W O.down.1))).hom := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | tmul b n =>
        rw [chartBaseChange_tmul]
        exact Submodule.smul_mem _ b (hgen _ n)
      | add a c ha hc => rw [map_add]; exact Submodule.add_mem _ ha hc
    obtain ⟨t, ht⟩ := key x
    exact ⟨t, ht.trans hx⟩
  have : IsIso T.arrow := isIso_of_mono_of_epi T.arrow
  have htop : T = ⊤ := by
    simpa only [T, Subobject.mk_arrow] using Subobject.mk_eq_top_of_isIso T.arrow
  exact ⟨isColimitSubobjectCocone_of_iSup_eq_top
    (finiteTypeQuasicoherentSubobjectProperty B S hS V hV H) htop⟩


end AlgebraicGeometry.Space

end
