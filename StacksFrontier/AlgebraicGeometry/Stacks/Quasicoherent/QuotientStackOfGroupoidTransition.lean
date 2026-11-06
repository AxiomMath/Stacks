module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackOfGroupoidSourceSections

/-!
# The isomorphism `𝒢 ≅ x^*ℱ|_{U_étale}` is compatible with the transitions

Let `ℱ` be the quasi-coherent module on `[U/R]` built from a quasi-coherent module `(𝒢, α)` on a
groupoid `(U, R, s, t, c)` in algebraic spaces, and `ψ : 𝒢 ≅ x^*ℱ|_{U_étale}` the canonical
isomorphism. This file proves that `ψ` carries `α` to the transition morphism of the image of `ℱ`
under the functor of Stacks 06WT, so that `ψ` is an isomorphism of quasi-coherent modules on the
groupoid; hence the functor is essentially surjective.

## Main results

* `AlgebraicGeometry.Stack.quotientStackModuleOfGroupoidHom_comm`: compatibility of `ψ` with the
  transitions.
* `AlgebraicGeometry.Stack.quotientStackToGroupoidObjIso`: `Φ(ℱ) ≅ (𝒢, α)`.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- A chart section restricted along a morphism of charts into a square refining it. -/
theorem modulePullbackChartSection_restrict {X Y : AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} C S hS Y.1 Y.2) (e d : ChartDiagram C S hS X.1 Y.1 f.hom)
    (i : d.U ⟶ e.U) (ι : d.V ⟶ e.V)
    (hsq : (SmallEtale.toOver C S hS X.1).map i ≫ e.g = d.g ≫ (SmallEtale.toOver C S hS Y.1).map ι)
    (s : M.val.obj (op e.V)) :
    ((modulePullback C S hS f).obj M).val.map i.op (modulePullbackChartSection C S hS f M e s) =
      modulePullbackChartSection C S hS f M d (M.val.map ι.op s) := by
  have hn := (modulePullbackChartFMap C S hS f M).naturality e d i ι hsq s
  exact (congrArg (((modulePullback C S hS f).obj M).val.map i.op)
    (modulePullbackChartFMap_app C S hS f M e s)).symm.trans
    (hn.symm.trans (modulePullbackChartFMap_app C S hS f M d _))

/-- **Maps out of an inverse image are determined on chart sections of affine squares** whose
chart of the source also carries an affine square over a second morphism `g'`. -/
theorem modulePullback_hom_ext_of_affine_chartSection {X Y Y' : AlgebraicSpaces C S hS}
    (f : X ⟶ Y) (g' : X ⟶ Y') (M : Modules.{u, u} C S hS Y.1 Y.2)
    (N : Modules.{u, u} C S hS X.1 X.2) (u v : (modulePullback C S hS f).obj M ⟶ N)
    (h : ∀ e : ChartDiagram C S hS X.1 Y.1 f.hom, HasAffineChartDiagram C S hS g' e.U →
      IsAffine ((BigFppfOver.toScheme C S hS).obj e.V.1.left) → ∀ s : M.val.obj (op e.V),
        u.val.app (op e.U) (modulePullbackChartSection C S hS f M e s) =
          v.val.app (op e.U) (modulePullbackChartSection C S hS f M e s)) : u = v := by
  refine modulePullback_hom_ext_of_chartSection C S hS f M N u v fun e s => ?_
  let R : Sieve e.U := Sieve.generate (fun Z (i : Z ⟶ e.U) =>
    ∃ (V₀ : SmallEtale C S hS Y.1) (ι : V₀ ⟶ e.V)
      (g : (SmallEtale.toOver C S hS X.1).obj Z ⟶ (SmallEtale.toOver C S hS Y.1).obj V₀)
      (hg : Z.1.hom ≫ f.hom = yoneda.map g ≫ V₀.1.hom),
      HasAffineChartDiagram C S hS g' Z ∧ IsAffine ((BigFppfOver.toScheme C S hS).obj V₀.1.left) ∧
        (SmallEtale.toOver C S hS X.1).map i ≫ e.g = g ≫ (SmallEtale.toOver C S hS Y.1).map ι)
  have hR : R ∈ SmallEtale.topology C S hS X.1 e.U := by
    refine smallEtale_sieve_of_pointwise_covering C S hS X.1 e.U R fun z => ?_
    obtain ⟨V₀, ι, hV₀, y₀, hy₀⟩ := exists_affine_chart_at C S hS Y.1 e.V
      ((BigFppfOver.toScheme C S hS).map e.g z)
    obtain ⟨T', π, p', hp', hsq, w', hw'1, -⟩ := exists_chart_pullback C S hS f e.U e.g e.comm.symm
      ι z y₀ hy₀.symm
    obtain ⟨T₀, ι', hT₀, w₀, hw₀⟩ := exists_hasAffineChartDiagram C S hS g' T' w'
    refine ⟨T₀, ι' ≫ π, ⟨T₀, 𝟙 _, ι' ≫ π, ⟨V₀, ι, (SmallEtale.toOver C S hS X.1).map ι' ≫ p',
      ?_, hT₀, hV₀, ?_⟩, Category.id_comp _⟩, w₀, ?_⟩
    · rw [Functor.map_comp, Category.assoc, hp', ← Category.assoc]
      exact congrArg (· ≫ f.hom) (CostructuredArrow.w ι'.hom).symm
    · rw [Functor.map_comp, Category.assoc, Category.assoc, hsq]
    · rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hw₀, hw'1]
  refine Stacks.SheafOfModules.ChangeOfRings.sections_ext N hR ?_
  rintro Z' i ⟨Z, j, i', ⟨V₀, ι, g, hg, hZ, hV₀, hsq⟩, rfl⟩
  refine Stacks.SheafOfModules.ChangeOfRings.map_comp_eq_of_map_eq N i' j ?_
  have key : ∀ T : (modulePullback C S hS f).obj M ⟶ N,
      N.val.map i'.op (T.val.app (op e.U) (modulePullbackChartSection C S hS f M e s)) =
        T.val.app (op Z) (modulePullbackChartSection C S hS f M ⟨Z, V₀, g, hg⟩
          (M.val.map ι.op s)) := fun T =>
    (PresheafOfModules.naturality_apply T.val i'.op _).symm.trans
      (congrArg (T.val.app (op Z)) (modulePullbackChartSection_restrict f M e ⟨Z, V₀, g, hg⟩
        i' ι hsq s))
  exact (key u).trans ((h ⟨Z, V₀, g, hg⟩ hZ hV₀ _).trans (key v).symm)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- **The target comparison on chart sections**: over a square of affine charts over `t`, the
section `c_t(t^*ψ(t^*x))` read in `Γ(V, (s ∘ v)^*𝒢)` is `α(t^*x)` read on `V`. -/
theorem pointEval_targetComparison_chartSection (V : Space.SmallEtale C S hS G.arrows.obj)
    (hV : IsAffine ((Space.SmallEtale.toOver C S hS G.arrows.obj ⋙
      BigFppfOver.toScheme C S hS).obj V)) (W : Space.AffineEtale C S hS G.objects.obj)
    (k : (Space.SmallEtale.toOver C S hS G.arrows.obj).obj V ⟶
      (Space.SmallEtale.toOver C S hS G.objects.obj).obj W.obj)
    (hk : V.1.hom ≫ G.target.hom = yoneda.map k ≫ W.obj.1.hom) (x : M.F.obj.val.obj (op W.obj)) :
    pointEval G M (affineArrowChartPoint G V hV)
        ((quotientStackTargetComparison G (quotientStackModuleOfGroupoid G M)).val.app (op V)
          (Space.modulePullbackChartSection C S hS G.target _ ⟨V, W.obj, k, hk⟩
            ((quotientStackModuleOfGroupoidHom G M).val.app (op W.obj) x))) =
      arrowChartRestrict G M V (M.alpha.val.app (op V)
        (Space.modulePullbackChartSection C S hS G.target M.F.obj ⟨V, W.obj, k, hk⟩ x)) := by
  obtain ⟨gt, hb, harr, hcm⟩ := quotientStackTarget_comparisonMorphism G ⟨V, W.obj, k, hk⟩
  have hc : (quotientStackTargetComparison G (quotientStackModuleOfGroupoid G M)).val.app (op V)
      (Space.modulePullbackChartSection C S hS G.target _ ⟨V, W.obj, k, hk⟩
        ((quotientStackModuleOfGroupoidHom G M).val.app (op W.obj) x)) =
      (quotientStackModuleOfGroupoid G M).val.map ((pointwiseToQuotientStack G).map
        (gt ≫ chartDiagramPoint G G.target.hom V W.obj k hk)).op
        ((quotientStackModuleOfGroupoidHom G M).val.app (op W.obj) x) := by
    rw [← hcm]
    exact Space.comparisonAlgebraicSpacesModules_chartSection (d := ⟨V, W.obj, k, hk⟩)
      (s := (quotientStackModuleOfGroupoidHom G M).val.app (op W.obj) x) ..
  have h1 := pointEval_map_quotientStackModuleOfGroupoidHom G M (affineArrowChartPoint G V hV) W
    (gt ≫ chartDiagramPoint G G.target.hom V W.obj k hk) x
  have h2 := pointSectionRestrict_comp G M gt (chartDiagramPoint G G.target.hom V W.obj k hk)
    (chartPointSection G M W.obj x)
  have hk0 : yoneda.map k ≫ W.obj.obj.hom =
      yonedaEquiv.symm (G.target.hom.app _ (yonedaEquiv V.obj.hom)) :=
    hk.symm.trans ((congrArg (· ≫ G.target.hom) (Equiv.symm_apply_apply yonedaEquiv
      V.obj.hom).symm).trans (yonedaEquiv_symm_comp' (yonedaEquiv V.obj.hom) G.target.hom))
  have hk' : yoneda.map ((chartDiagramPoint G G.target.hom V W.obj k hk).base ≫ 𝟙 _) ≫
      W.obj.obj.hom = yonedaEquiv.symm (G.target.hom.app _ (yonedaEquiv V.obj.hom)) := by
    rw [Category.comp_id]
    exact hk0
  have h3 := pointSectionRestrict_pointChartSection G M
    (chartDiagramPoint G G.target.hom V W.obj k hk)
    (pointwiseArrow_chartDiagramPoint G G.target.hom V W.obj k hk) W.obj (𝟙 _)
    (chartPoint_comm G W.obj) hk' x
  have hk1 : V.1.hom ≫ G.target.hom = yoneda.map (k ≫ 𝟙 _) ≫ W.obj.1.hom := by
    rw [Category.comp_id]
    exact hk
  have h4 := pointSectionRestrict_arrowChart G M V W.obj (k ≫ 𝟙 _) hk1 gt hb harr hk' x
  have h5 := Space.modulePullbackChartSection_congr C S hS G.target M.F.obj hk1 hk
    (Category.comp_id k) x
  refine (congrArg (pointEval G M (affineArrowChartPoint G V hV)) hc).trans ?_
  refine h1.trans (h2.symm.trans ?_)
  refine (congrArg (pointSectionRestrict G M gt) h3).trans (h4.trans ?_)
  exact congrArg (fun w => arrowChartRestrict G M V (M.alpha.val.app (op V) w)) h5

/-- `c_s ∘ s^*ψ ∘ α = c_t ∘ t^*ψ`: the compatibility of `ψ` with the transitions, through the
comparison map of the triangle through the source. -/
theorem quotientStackModuleOfGroupoidHom_comm_sourceComparison :
    M.alpha ≫ (Space.modulePullback C S hS G.source).map (quotientStackModuleOfGroupoidHom G M) ≫
        quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M) =
      (Space.modulePullback C S hS G.target).map (quotientStackModuleOfGroupoidHom G M) ≫
        quotientStackTargetComparison G (quotientStackModuleOfGroupoid G M) := by
  refine Space.modulePullback_hom_ext_of_affine_chartSection G.target G.source M.F.obj _ _ _
    fun e he hV x => ?_
  obtain ⟨U₀, V₀, g, hg⟩ := e
  obtain ⟨hU, W', q, hq, hW'⟩ := he
  refine injective_pointEval G M (affineArrowChartPoint G U₀ hU) ?_
  have l3 := pointEval_sourceComparison G M U₀ hU ⟨W', hW'⟩ q hq.symm
    (M.alpha.val.app (op U₀)
      (Space.modulePullbackChartSection C S hS G.target M.F.obj ⟨U₀, V₀, g, hg⟩ x))
  have r2 := Space.modulePullbackChartSection_map C S hS G.target _
    (quotientStackModuleOfGroupoidHom G M) ⟨U₀, V₀, g, hg⟩ x
  have r3 := pointEval_targetComparison_chartSection G M U₀ hU ⟨V₀, hV⟩ g hg x
  refine l3.trans ?_
  refine Eq.trans ?_ (congrArg (fun w => pointEval G M (affineArrowChartPoint G U₀ hU)
    ((quotientStackTargetComparison G (quotientStackModuleOfGroupoid G M)).val.app (op U₀) w))
      r2).symm
  exact r3.symm

/-- **`ψ : 𝒢 ≅ x^*ℱ|_{U_étale}` is compatible with the transitions**: it carries `α` to the
transition morphism of the image of `ℱ` under the functor of Stacks 06WT. -/
theorem quotientStackModuleOfGroupoidHom_comm :
    M.alpha ≫ (Space.modulePullback C S hS G.source).map (quotientStackModuleOfGroupoidHom G M) =
      (Space.modulePullback C S hS G.target).map (quotientStackModuleOfGroupoidHom G M) ≫
        quotientStackTransition G (quotientStackModuleOfGroupoid G M)
          (isQuasicoherentOnSite_quotientStackModuleOfGroupoid G M) := by
  have := isIso_quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)
    (isQuasicoherentOnSite_quotientStackModuleOfGroupoid G M)
  refine (Iso.cancel_iso_hom_right _ _
    (asIso (quotientStackSourceComparison G (quotientStackModuleOfGroupoid G M)))).1 ?_
  rw [asIso_hom, Category.assoc, Category.assoc, quotientStackTransition_comp_sourceComparison]
  exact quotientStackModuleOfGroupoidHom_comm_sourceComparison G M

/-- The quasi-coherent module on `[U/R]` attached to `(𝒢, α)`, as an object of
`QCoh(𝒪_{[U/R]})`. -/
def quotientStackQuasicoherentOfGroupoid :
    FibredSite.quasicoherentModules.{u, u + 1, u + 1, u} C S hS (quotientStack G).p
      (isFiberedInGroupoids_quotientStack G) :=
  ⟨quotientStackModuleOfGroupoid G M, isQuasicoherentOnSite_quotientStackModuleOfGroupoid G M⟩

/-- **The morphism `(𝒢, α) ⟶ Φ(ℱ)`** of quasi-coherent modules on the groupoid. -/
def quotientStackToGroupoidObjHom :
    M ⟶ (quotientStackToGroupoid G).obj (quotientStackQuasicoherentOfGroupoid G M) where
  hom := quotientStackModuleOfGroupoidHom G M
  comm := quotientStackModuleOfGroupoidHom_comm G M

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Space.QuasicoherentModule

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}

/-- A morphism of quasi-coherent modules on a groupoid whose underlying morphism of modules is an
isomorphism is an isomorphism. -/
theorem isIso_of_isIso_hom {M N : QuasicoherentModule C S hS G} (f : M ⟶ N) [IsIso f.hom] :
    IsIso f := by
  refine ⟨⟨⟨inv f.hom, ?_⟩, Hom.ext (IsIso.hom_inv_id f.hom), Hom.ext (IsIso.inv_hom_id f.hom)⟩⟩
  have hc := f.comm
  rw [Functor.map_inv, Functor.map_inv, IsIso.eq_inv_comp, ← Category.assoc, ← hc,
    Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Space.QuasicoherentModule

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
  (M : Space.QuasicoherentModule C S hS G)

/-- The morphism `(𝒢, α) ⟶ Φ(ℱ)` of quasi-coherent modules on the groupoid is an isomorphism. -/
instance : IsIso (quotientStackToGroupoidObjHom G M) :=
  haveI : IsIso (quotientStackToGroupoidObjHom G M).hom :=
    isIso_quotientStackModuleOfGroupoidHom G M
  Space.QuasicoherentModule.isIso_of_isIso_hom _

/-- The image of the quasi-coherent module on `[U/R]` attached to `(𝒢, α)` is isomorphic to
`(𝒢, α)`. -/
def quotientStackToGroupoidObjIso :
    (quotientStackToGroupoid G).obj (quotientStackQuasicoherentOfGroupoid G M) ≅ M :=
  (asIso (quotientStackToGroupoidObjHom G M)).symm

/-- **The functor of Stacks 06WT is essentially surjective.** -/
instance : (quotientStackToGroupoid G).EssSurj :=
  ⟨fun M => ⟨quotientStackQuasicoherentOfGroupoid G M, ⟨quotientStackToGroupoidObjIso G M⟩⟩⟩

end AlgebraicGeometry.Stack

end
