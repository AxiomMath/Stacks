module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctors.ZeroLimit

/-!
# The isomorphism condition after base change is limit preserving on affine schemes

Let `u : F ⟶ G` be a homomorphism of quasi-coherent modules on a scheme `X` over `S`, with `F`
of finite type, `G` of finite presentation and `X ⟶ S` quasi-compact. If an inverse system of
affine schemes over `S`, indexed by a cofiltered category, has limit `T`, and if `u` becomes an
isomorphism after base change to `T`, then it already becomes an isomorphism after base change
to one of the stages.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_pullback_comp_map_iff`,
  `AlgebraicGeometry.Scheme.Modules.isIso_pullback_map_iff_of_isIso` and
  `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_pullback_ι`: invertibility of an inverse
  image along a composition, along an isomorphism, and its locality on an open cover.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isIsomorphismAfterBaseChange_of_isColimit`:
  the isomorphism condition after base change to the limit descends to a stage.
* `Stacks.Flatness.ModuleMapBaseChangeSituation.isomorphismFunctor_preservesColimit_of_isAffine`:
  the isomorphism functor preserves the corresponding filtered colimit (Tag 05MJ).

## Implementation notes

The argument is that of
`Stacks.Flatness.ModuleMapBaseChangeSituation.exists_isZeroAfterBaseChange_of_isColimit`, whose
affine charts along the limit, their coordinate rings and the filtered colimit of those rings are
reused. On a chart, vanishing of an extension of scalars is replaced by bijectivity of one, so the
descent step is Tag 05LI(4),
`Stacks.FinitePresentation.ColimitDescent.exists_bijective_baseChange_of_isColimit`; this is why
the target is of finite presentation and not merely of finite type. The gluing step is the
locality of invertibility on an open cover.

## References

* [Stacks Project, Tag 05MJ](https://stacks.math.columbia.edu/tag/05MJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- **Invertibility of an inverse image along a composition.** The inverse image of a
homomorphism of modules along a composition is an isomorphism exactly when the iterated inverse
image is. -/
theorem isIso_pullback_comp_map_iff (f : X ⟶ Y) (g : Y ⟶ Z) {M N : Z.Modules} (φ : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback (f ≫ g)).map φ) ↔
      IsIso ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ)) :=
  (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp f g) φ).symm

/-- **Inverse image along an isomorphism detects invertibility.** -/
theorem isIso_pullback_map_iff_of_isIso (f : X ⟶ Y) [IsIso f] {M N : Y.Modules} (φ : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback f).map φ) ↔ IsIso φ := by
  let γ : Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (inv f) ≅ 𝟭 Y.Modules :=
    Scheme.Modules.pullbackComp (inv f) f ≪≫
      Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f) ≪≫ Scheme.Modules.pullbackId Y
  refine ⟨fun h => ?_, fun h => Functor.map_isIso (Scheme.Modules.pullback f) φ⟩
  exact (NatIso.isIso_map_iff γ φ).1
    (Functor.map_isIso (Scheme.Modules.pullback (inv f)) ((Scheme.Modules.pullback f).map φ))

/-- **An inverse image which is already invertible stays invertible after a further inverse
image.** -/
theorem isIso_pullback_map_of_comp (f : X ⟶ Y) (g : Y ⟶ Z) {M N : Z.Modules} (φ : M ⟶ N)
    (h : IsIso ((Scheme.Modules.pullback g).map φ)) :
    IsIso ((Scheme.Modules.pullback (f ≫ g)).map φ) :=
  (isIso_pullback_comp_map_iff f g φ).2
    (have := h; Functor.map_isIso (Scheme.Modules.pullback f) _)

/-- **Invertibility of a homomorphism of modules is local, in inverse-image form.** A
homomorphism of sheaves of modules whose inverse image along the inclusion of each member of an
open cover is an isomorphism is itself an isomorphism. -/
theorem isIso_of_isIso_pullback_ι {M N : X.Modules} {ι : Type*} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (φ : M ⟶ N)
    (hlocal : ∀ i, IsIso ((Scheme.Modules.pullback (U i).ι).map φ)) : IsIso φ := by
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict φ U
    (TopologicalSpace.IsOpenCover.mk hU) fun i => ?_
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback (U i).ι) φ).2
    (hlocal i)

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.Flatness.ModuleMapBaseChangeSituation

/-- **Invertibility of an inverse image along a morphism factoring through an affine chart.**
If a morphism `Spec R ⟶ X` factors as the spectrum of `f : A ⟶ R` followed by the chart
inclusion, then the inverse image along it of the homomorphism of the situation is an
isomorphism exactly when the extension of scalars to `R` of the chart homomorphism's module of
global sections is bijective. -/
theorem pullback_isIso_iff_of_factorsThrough_chart (D : ModuleMapBaseChangeSituation.{u})
    (W : D.X.Opens) (A R : CommRingCat.{u}) (eW : (W : Scheme.{u}) ≅ Spec A) (f : A ⟶ R)
    {g : Spec R ⟶ D.X} (hg : g = Spec.map f ≫ D.chartInclusion W A eW) :
    letI : Algebra A R := f.hom.toAlgebra
    Function.Bijective (LinearMap.baseChange R (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom)
      ↔ IsIso ((Scheme.Modules.pullback g).map D.hom) := by
  calc _ ↔ IsIso ((Scheme.Modules.pullback (Spec.map f)).map (D.chartHom W A eW)) :=
        D.pullback_chartHom_isIso_iff W A R eW f
    _ ↔ IsIso ((Scheme.Modules.pullback (Spec.map f ≫ D.chartInclusion W A eW)).map D.hom) :=
        (Scheme.Modules.isIso_pullback_comp_map_iff _ _ D.hom).symm
    _ ↔ IsIso ((Scheme.Modules.pullback g).map D.hom) := by rw [hg]

/-- **Invertibility of an inverse image on an affine chart descends to a stage.** Let `E` be a
cofiltered inverse system of schemes with affine transition morphisms and limit cone `cE`, let
`p` be a morphism from a stage `i₀` to the source of the situation, let `W` be an affine open of
that source and `U` an affine open of the stage lying over `W`.  If the inverse image of the
homomorphism of the situation along the chart map on the limit is an isomorphism, then it is
already an isomorphism along the chart map at some later stage. -/
private theorem exists_stage_chart_isIso_pullback (D : ModuleMapBaseChangeSituation.{u})
    [D.F.IsFiniteType] [D.G.IsFinitePresentation] {I : Type u} [Category.{u} I] [IsCofiltered I]
    (E : I ⥤ Scheme.{u}) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (E.map g)] (cE : Cone E)
    (hcE : IsLimit cE) (i₀ : I) {p : E.obj i₀ ⟶ D.X} {W : D.X.Opens} (hW : IsAffineOpen W)
    (U : (E.obj i₀).Opens) (hU : IsAffineOpen U) (hsub : U ≤ p ⁻¹ᵁ W)
    (h : IsIso ((Scheme.Modules.pullback (chartLimitMap E cE i₀ U hsub ≫ W.ι)).map D.hom)) :
    ∃ k : Over i₀,
      IsIso ((Scheme.Modules.pullback (chartStageMap E i₀ U hsub k ≫ W.ι)).map D.hom) := by
  classical
  let d : Over i₀ ⥤ Scheme.{u} := opensDiagram E i₀ U
  let dc : Cone d := opensCone E cE i₀ U
  have hdAffine (k : Over i₀) : IsAffine (d.obj k) := hU.preimage (E.map k.hom)
  have hdcAffine : IsAffine dc.pt :=
    have : IsAffineHom (cE.π.app i₀) := isAffineHom_π_app E cE hcE i₀
    hU.preimage (cE.π.app i₀)
  let A : CommRingCat.{u} := Γ(D.X, W)
  let eW : (W : Scheme.{u}) ≅ Spec A := hW.isoSpec
  let R : (Over i₀)ᵒᵖ ⥤ CommRingCat.{u} := d.op ⋙ Scheme.Γ
  let cΓ : Cocone R := Scheme.Γ.mapCocone dc.op
  have hcΓ : IsColimit cΓ := isColimitΓMapCoconeOpensConeOp E cE hcE i₀ hU
  let fstage : ∀ k : Over i₀, A ⟶ R.obj (op k) := chartStageRingMap E i₀ U hsub
  let flimit : A ⟶ cΓ.pt := chartLimitRingMap E cE i₀ U hsub
  let _ (k : (Over i₀)ᵒᵖ) : Algebra (A : Type u) (R.obj k : Type u) :=
    (fstage k.unop).hom.toAlgebra
  let _ : Algebra (A : Type u) (cΓ.pt : Type u) := flimit.hom.toAlgebra
  have halgR : ∀ ⦃k l : (Over i₀)ᵒᵖ⦄ (g : k ⟶ l) (a : A),
      (R.map g).hom (algebraMap A (R.obj k) a) = algebraMap A (R.obj l) a := fun _ l g a =>
    congrArg (fun z : A ⟶ R.obj l => z.hom a)
      (chartStageRingMap_comp_appTop E i₀ U hsub g.unop)
  have halgι : ∀ (k : (Over i₀)ᵒᵖ) (a : A),
      (cΓ.ι.app k).hom (algebraMap A (R.obj k) a) = algebraMap A cΓ.pt a := fun k a =>
    congrArg (fun z : A ⟶ cΓ.pt => z.hom a)
      (chartStageRingMap_comp_π_appTop E cE i₀ U hsub k.unop)
  have hfin : Module.Finite (A : Type u)
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.F)) :=
    D.module_finite_moduleSpecΓ_chart W A eW
  have hfp : Module.FinitePresentation (A : Type u)
      (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback (D.chartInclusion W A eW)).obj D.G)) :=
    D.module_finitePresentation_moduleSpecΓ_chart W A eW
  have hchart (V : Scheme.{u}) [IsAffine V] (m : V ⟶ W) (f : A ⟶ Γ(V, ⊤))
      (hf : f = W.topIso.inv ≫ m.appTop) :
      letI : Algebra A Γ(V, ⊤) := f.hom.toAlgebra
      Function.Bijective (LinearMap.baseChange Γ(V, ⊤)
        (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom) ↔
          IsIso ((Scheme.Modules.pullback (m ≫ W.ι)).map D.hom) := by
    have hg : V.isoSpec.inv ≫ m ≫ W.ι = Spec.map f ≫ D.chartInclusion W A eW := by
      rw [← Category.assoc, hW.isoSpec_inv_comp m, Category.assoc, hf]
    rw [D.pullback_isIso_iff_of_factorsThrough_chart W A _ eW f hg,
      Scheme.Modules.isIso_pullback_comp_map_iff,
      Scheme.Modules.isIso_pullback_map_iff_of_isIso]
  have hbaseLim : Function.Bijective (LinearMap.baseChange (cΓ.pt : Type u)
      (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom) :=
    (hchart dc.pt _ flimit rfl).2 h
  obtain ⟨k, hk⟩ :=
    Stacks.FinitePresentation.ColimitDescent.exists_bijective_baseChange_of_isColimit
      R cΓ halgR halgι (isColimitOfPreserves (forget CommRingCat) hcΓ)
      (moduleSpecΓFunctor.map (D.chartHom W A eW)).hom hbaseLim
  refine ⟨k.unop, ?_⟩
  exact (hchart (d.obj k.unop) _ (fstage k.unop) rfl).1 hk

/-- **The isomorphism condition after base change descends to a stage.** If an inverse system
of affine schemes over the base, indexed by a cofiltered category in the universe of the
schemes, has limit `T` and the homomorphism of the situation becomes an isomorphism after base
change to `T`, then it already becomes an isomorphism after base change to one of the stages. -/
theorem exists_isIsomorphismAfterBaseChange_of_isColimit (D : ModuleMapBaseChangeSituation.{u})
    [QuasiCompact D.f] [D.F.IsFiniteType] [D.G.IsFinitePresentation] {I : Type u}
    [Category.{u} I] [IsCofiltered I] (T : I ⥤ Over D.S) (hT : ∀ i, IsAffine (T.obj i).left)
    (c : Cocone T.op) (hc : IsColimit c) (h : D.IsIsomorphismAfterBaseChange c.pt.unop) :
    ∃ i, D.IsIsomorphismAfterBaseChange (T.obj i) := by
  classical
  let K : Over D.S ⥤ Scheme.{u} := Over.pullback D.f ⋙ Over.forget D.X
  let E : I ⥤ Scheme.{u} := T ⋙ K
  let cE : Cone E := K.mapCone c.unop
  have hcE : IsLimit cE := isLimitOfPreserves K hc.unop
  have haff {i j : I} (g : i ⟶ j) : IsAffineHom (E.map g) := by
    have := hT i
    have := hT j
    exact isAffineHom_overPullback_map_left D.f (T.map g)
  obtain ⟨i₀⟩ : Nonempty I := IsCofiltered.nonempty
  let p : E.obj i₀ ⟶ D.X := ((Over.pullback D.f).obj (T.obj i₀)).hom
  have hstruct {i j : I} (g : i ⟶ j) :
      E.map g ≫ ((Over.pullback D.f).obj (T.obj j)).hom =
        ((Over.pullback D.f).obj (T.obj i)).hom := Over.w ((Over.pullback D.f).map (T.map g))
  have hlimstruct (i : I) :
      cE.π.app i ≫ ((Over.pullback D.f).obj (T.obj i)).hom =
        ((Over.pullback D.f).obj c.pt.unop).hom :=
    Over.w ((Over.pullback D.f).map (c.unop.π.app i))
  have : IsAffine (T.obj i₀).left := hT i₀
  have : CompactSpace (E.obj i₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst (T.obj i₀).hom D.f)
  obtain ⟨n, W, U, hW, hU, hcover, hsub⟩ := exists_finite_affineOpenCover_subordinate p
  have hlimiso :
      IsIso ((Scheme.Modules.pullback ((Over.pullback D.f).obj c.pt.unop).hom).map D.hom) := by
    rw [show ((Over.pullback D.f).obj c.pt.unop).hom =
      (pullbackSymmetry c.pt.unop.hom D.f).hom ≫ pullback.fst D.f c.pt.unop.hom from
      (pullbackSymmetry_hom_comp_fst c.pt.unop.hom D.f).symm]
    exact Scheme.Modules.isIso_pullback_map_of_comp _ _ D.hom h
  have hchart (j : Fin n) : ∃ k : Over i₀,
      IsIso ((Scheme.Modules.pullback
        (chartStageMap E i₀ (U j) (hsub j) k ≫ (W j).ι)).map D.hom) := by
    refine exists_stage_chart_isIso_pullback D E cE hcE i₀ (hW j) (U j) (hU j) (hsub j) ?_
    rw [chartLimitMap_comp_ι, hlimstruct i₀]
    exact Scheme.Modules.isIso_pullback_map_of_comp _ _ D.hom hlimiso
  choose chartStage hchartStage using hchart
  obtain ⟨k₀, hk₀⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image chartStage)
  have hiso (j : Fin n) :
      IsIso ((Scheme.Modules.pullback
        ((E.map k₀.hom ⁻¹ᵁ U j).ι ≫ E.map k₀.hom ≫ p)).map D.hom) := by
    obtain ⟨g⟩ := hk₀ (Finset.mem_image.2 ⟨j, Finset.mem_univ j, rfl⟩)
    have hstage : IsIso ((Scheme.Modules.pullback
        (chartStageMap E i₀ (U j) (hsub j) k₀ ≫ (W j).ι)).map D.hom) := by
      rw [← opensDiagram_map_comp_chartStageMap E i₀ (U j) (hsub j) g, Category.assoc]
      exact Scheme.Modules.isIso_pullback_map_of_comp _ _ D.hom (hchartStage j)
    rwa [chartStageMap_comp_ι, chartOpensι_eq] at hstage
  have hwhole : IsIso ((Scheme.Modules.pullback (E.map k₀.hom ≫ p)).map D.hom) := by
    exact Scheme.Modules.isIso_of_isIso_pullback_ι _
      (Scheme.Hom.iSup_preimage_eq_top (E.map k₀.hom) hcover) _ fun j =>
        (Scheme.Modules.isIso_pullback_comp_map_iff _ _ D.hom).1 (hiso j)
  refine ⟨k₀.left, ?_⟩
  rw [show E.map k₀.hom ≫ p = ((Over.pullback D.f).obj (T.obj k₀.left)).hom from
    hstruct k₀.hom, show ((Over.pullback D.f).obj (T.obj k₀.left)).hom =
      (pullbackSymmetry (T.obj k₀.left).hom D.f).hom ≫
        pullback.fst D.f (T.obj k₀.left).hom from
      (pullbackSymmetry_hom_comp_fst (T.obj k₀.left).hom D.f).symm] at hwhole
  exact (Scheme.Modules.isIso_pullback_map_iff_of_isIso
    (pullbackSymmetry (T.obj k₀.left).hom D.f).hom _).1
    ((Scheme.Modules.isIso_pullback_comp_map_iff _ _ D.hom).1 hwhole)

/-- **Stacks Project, Tag 05MJ.** The isomorphism functor of a homomorphism of quasi-coherent
modules with source of finite type and target of finite presentation, along a quasi-compact
morphism, preserves the filtered colimit attached to a cofiltered inverse system of affine
schemes over the base. -/
@[stacks 05MJ "iso_limit"]
theorem isomorphismFunctor_preservesColimit_of_isAffine (D : ModuleMapBaseChangeSituation.{u})
    [QuasiCompact D.f] [D.F.IsFiniteType] [D.G.IsFinitePresentation] (I : Type u)
    [Category.{u} I] [IsCofiltered I] (T : I ⥤ Over D.S) (hT : ∀ i, IsAffine (T.obj i).left) :
    PreservesColimit T.op D.isomorphismFunctor := by
  classical
  refine ⟨fun {c} hc => ⟨Types.FilteredColimit.isColimitOf (T.op ⋙ D.isomorphismFunctor)
    (D.isomorphismFunctor.mapCocone c) (fun x => ?_) fun j k x y _ => ?_⟩⟩
  · obtain ⟨i, hi⟩ := exists_isIsomorphismAfterBaseChange_of_isColimit D T hT c hc x.down
    exact ⟨op i, ⟨hi⟩,
      (show Subsingleton (PLift (D.IsIsomorphismAfterBaseChange c.pt.unop)) from
        inferInstance).elim _ _⟩
  · obtain ⟨l, f, g, _⟩ := IsFilteredOrEmpty.cocone_objs j k
    exact ⟨l, f, g, (show Subsingleton (PLift (D.IsIsomorphismAfterBaseChange (T.obj l.unop)))
      from inferInstance).elim _ _⟩

end Stacks.Flatness.ModuleMapBaseChangeSituation

end
