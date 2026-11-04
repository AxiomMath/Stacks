module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.RelativeWeakAssassin
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.RepresentedFibreComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTarget
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTargetDescent
public import StacksFrontier.AlgebraicGeometry.Divisors.RelativeAssassinTwo.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityLimitStageCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionAtPoint

/-!
# The relative weak assassin of a base change as an inverse image

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `g : Y' ⟶ Y` be
arbitrary, let `X' = X ×_Y Y'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'`, and put
`F' = (g')^*F` for an `𝒪_X`-module `F`. The inclusion
`WeakAss_{X'/Y'}(F') ⊆ (g')^{-1} WeakAss_{X/Y}(F)` holds after an arbitrary base change: it is
Stacks 0CV2 part (1) read on sets. When `F` is quasi-coherent, `f` is locally of finite type and
every point of `|Y'|` has transcendence degree `0` over its image in `|Y|` — for instance when
`g` is locally quasi-finite — the two sets are equal, which is Stacks 0CV3.

## Main results

* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_modulePullback_subset_preimage`: the
  inclusion valid for an arbitrary base change.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_representedPullback_of_isAlgebraic`:
  the reverse implication for a cartesian square of schemes of the site whose base change
  morphism induces algebraic extensions of residue fields, which is Stacks 05KL read on the
  algebraic spaces these schemes represent.
* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_modulePullback_eq_preimage`:
  **Stacks 0CV3**, the relative weak assassin of `F'` is the inverse image of that of `F`.
* `relativeWeaklyAssociatedPoints_modulePullback_eq_preimage_of_isLocallyQuasiFinite`: the same
  for a locally quasi-finite `g`.

## References

* [Stacks Project, Tag 0CV3](https://stacks.math.columbia.edu/tag/0CV3)
* [Stacks Project, Tag 0CV2](https://stacks.math.columbia.edu/tag/0CV2)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 05KL](https://stacks.math.columbia.edu/tag/05KL)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝐓" => BigFppfOver.toScheme B S hS

/-! ### The represented case -/

/-- **Stacks 05KL on represented algebraic spaces.** Let `α : U ⟶ V` and `β : V' ⟶ V` be
morphisms of the site with `α` locally of finite type and with every residue field extension of
`β` algebraic, and let `N` be a quasi-coherent module on the algebraic space `U` represents. If
the image in `U` of a point `w` of the fibre product `P = U ×_V V'` lies in the relative weak
assassin of `N` along `α`, then `w` lies in the relative weak assassin of the pullback of `N`
along `P ⟶ V'`. -/
theorem isRelativeWeaklyAssociatedPoint_representedPullback_of_isAlgebraic
    {U V V' : BigFppfOver B S hS} (α : U ⟶ V) (β : V' ⟶ V)
    [LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map α)]
    (alg : ∀ v' : (BigFppfOver.toScheme B S hS).obj V',
      letI := (((BigFppfOver.toScheme B S hS).map β).residueFieldMap v').hom.toAlgebra
      Algebra.IsAlgebraic (((BigFppfOver.toScheme B S hS).obj V).residueField
        ((BigFppfOver.toScheme B S hS).map β v'))
        (((BigFppfOver.toScheme B S hS).obj V').residueField v'))
    (N : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (hN : N.IsQuasicoherentOnSite) (w : points B S hS (yoneda.obj (pullback α β)))
    (hw : IsRelativeWeaklyAssociatedPoint B S hS (representedSpaceMap B S hS α) N
      (pointsMap B S hS _ (yoneda.map (pullback.fst α β)) w)) :
    IsRelativeWeaklyAssociatedPoint B S hS (representedSpaceMap B S hS (pullback.snd α β))
      ((modulePullback B S hS (representedSpaceMap B S hS (pullback.fst α β))).obj N) w := by
  have hMqc : (representedChartModule B S hS N).IsQuasicoherent :=
    isQuasicoherent_restrictToChartScheme B S hS (schemeSpace U) N hN (idEtaleChart B S hS U)
  have h1 := (isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints
    B S hS α N hN _).1 hw
  rw [pointsToScheme_pointsMap_yoneda B S hS (pullback.fst α β) w,
    relativeWeaklyAssociatedPoints_eq_relativeAssassin] at h1
  have sqS : IsPullback (𝐓.map (pullback.fst α β)) (𝐓.map (pullback.snd α β)) (𝐓.map α)
      (𝐓.map β) := (IsPullback.of_hasPullback α β).map 𝐓
  set e := sqS.isoPullback
  have hefst : e.hom ≫ pullback.fst (𝐓.map α) (𝐓.map β) = 𝐓.map (pullback.fst α β) :=
    sqS.isoPullback_hom_fst
  have hesnd : e.hom ≫ pullback.snd (𝐓.map α) (𝐓.map β) = 𝐓.map (pullback.snd α β) :=
    sqS.isoPullback_hom_snd
  set t := pointsToScheme B S hS (pullback α β) w
  have h2 : e.hom t ∈ pullback.fst (𝐓.map α) (𝐓.map β) ⁻¹'
      Stacks.Divisors.relativeAssassin (𝐓.map α) (representedChartModule B S hS N) := by
    rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, hefst]
  rw [preimage_relativeAssassin_eq_pullback_of_isAlgebraic_residueField (𝐓.map α) (𝐓.map β)
    (representedChartModule B S hS N) alg] at h2
  have : ((Scheme.Modules.pullback (pullback.fst (𝐓.map α) (𝐓.map β))).obj
      (representedChartModule B S hS N)).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _
      (pullback.fst (𝐓.map α) (𝐓.map β)).toLRSHom.toShHom (representedChartModule B S hS N) hMqc
  have h3 := (mem_relativeAssassin_isoOver_iff e (pullback.snd (𝐓.map α) (𝐓.map β))
    ((Scheme.Modules.pullback (pullback.fst (𝐓.map α) (𝐓.map β))).obj
      (representedChartModule B S hS N)) t).2 h2
  rw [hesnd] at h3
  have hmod : (Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback (pullback.fst (𝐓.map α) (𝐓.map β))).obj
          (representedChartModule B S hS N)) ≅
      representedChartModule B S hS
        ((modulePullback B S hS (representedSpaceMap B S hS (pullback.fst α β))).obj N) :=
    (Scheme.Modules.pullbackComp e.hom (pullback.fst (𝐓.map α) (𝐓.map β))).app
        (representedChartModule B S hS N) ≪≫
      eqToIso (congrArg (fun m ↦ (Scheme.Modules.pullback m).obj
        (representedChartModule B S hS N)) hefst) ≪≫
      (nonempty_restrictToChartScheme_baseChange_of_isQuasicoherent
        (pullback.fst α β) N hN).some.symm
  rw [relativeAssassin_eq_of_moduleIso _ hmod] at h3
  have : LocallyOfFiniteType (𝐓.map (pullback.snd α β)) := by
    rw [← hesnd]; infer_instance
  rw [← relativeWeaklyAssociatedPoints_eq_relativeAssassin] at h3
  have hqc' := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    (representedSpaceMap B S hS (pullback.fst α β)) N hN
  exact (isRelativeWeaklyAssociatedPoint_iff_mem_relativeWeaklyAssociatedPoints B S hS
    (pullback.snd α β) _ hqc' w).2 h3

/-! ### The inclusion valid after an arbitrary base change -/

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

/-- The relative weak assassin of `(g')^*F` along `f'` is contained in the inverse image under
`|g'|` of the relative weak assassin of `F` along `f`, for an arbitrary base change. -/
theorem relativeWeaklyAssociatedPoints_modulePullback_subset_preimage
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2) :
    relativeWeaklyAssociatedPoints B S hS f' ((modulePullback B S hS g').obj F) ⊆
      pointsMap B S hS X'.1 g'.hom ⁻¹' relativeWeaklyAssociatedPoints B S hS f F :=
  fun _ hx' ↦ isRelativeWeaklyAssociatedPoint_of_baseChange B S hS sq F hx'

/-! ### The reverse implication -/

/-- If every point of the fibre of `f` over the image in `Y` of a field-valued representative `q`
of `|f'|(x')` lying above `|g'|(x')` is weakly associated to the restriction of `F`, then `x'`
lies in the relative weak assassin of `(g')^*F` along `f'`. -/
theorem isRelativeWeaklyAssociatedPoint_baseChange_of_fibreEvery
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (q : FieldValuedPoint B S hS Y'.1) {x' : points B S hS X'.1}
    (hq : q.class B S hS Y'.1 = pointsMap B S hS X'.1 f'.hom x')
    (h : IsWeaklyAssociatedOnFibreEvery B S hS f F
      (FieldValuedPoint.map B S hS Y'.1 g.hom q) (pointsMap B S hS X'.1 g'.hom x')) :
    IsRelativeWeaklyAssociatedPoint B S hS f' ((modulePullback B S hS g').obj F) x' := by
  obtain ⟨θ, hθ⟩ := exists_point_fibre_of_pointsMap_eq_class B S hS f' hq
  refine ⟨q, hq, θ, hθ, (isWeaklyAssociatedPoint_baseChangeFibre_iff B S hS sq q F θ).2 (h _ ?_)⟩
  rw [pointsMap_baseChangeFibreMap B S hS sq q θ, hθ]

/-- A square of algebraic spaces is cartesian when its underlying square of presheaves is. -/
private theorem isPullback_of_isPullback_hom
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) : IsPullback g' f' f g :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι fun F ↦ IsAlgebraicSpace B S hS F) sq

/-- **The reverse inclusion of Stacks 0CV3, read on étale charts.** In a cartesian square of
algebraic spaces with `f` locally of finite type and `F` quasi-coherent, suppose that for every
commuting square of étale scheme charts `V' ⟶ Y'`, `V ⟶ Y` over `g`, with morphism of charts
`β : V' ⟶ V`, every residue field extension of `β` is algebraic. Then a point of `X'` whose
image in `X` lies in `WeakAss_{X/Y}(F)` lies in `WeakAss_{X'/Y'}((g')^*F)`. -/
theorem isRelativeWeaklyAssociatedPoint_baseChange_of_isAlgebraic_charts
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (f_lft : IsLocallyOfFiniteType B S hS f.hom)
    (alg : ∀ (V' V : BigFppfOver B S hS) (a : yoneda.obj V' ⟶ Y'.1) (b : yoneda.obj V ⟶ Y.1)
      (β : V' ⟶ V),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝐓).presheaf a →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝐓).presheaf b →
      yoneda.map β ≫ b = a ≫ g.hom → ∀ v' : 𝐓.obj V',
        letI := ((𝐓.map β).residueFieldMap v').hom.toAlgebra
        Algebra.IsAlgebraic ((𝐓.obj V).residueField (𝐓.map β v')) ((𝐓.obj V').residueField v'))
    {x' : points B S hS X'.1}
    (hx : IsRelativeWeaklyAssociatedPoint B S hS f F (pointsMap B S hS X'.1 g'.hom x')) :
    IsRelativeWeaklyAssociatedPoint B S hS f' ((modulePullback B S hS g').obj F) x' := by
  have hF : F.IsQuasicoherentOnSite := inferInstance
  have sqA : IsPullback g' f' f g := isPullback_of_isPullback_hom B S hS sq
  obtain ⟨V, b, b_surj, b_et⟩ := Y.2.exists_atlas
  let ψ : schemeSpace V ⟶ Y := ObjectProperty.homMk b
  have ψ_et : IsEtale B S hS ψ.hom := (isEtale_iff_presheaf_of_yoneda B S hS b).2 b_et
  have ψ_surj : Function.Surjective (pointsMap B S hS (yoneda.obj V) b) :=
    (surjective_iff_surjective_pointsMap B S hS Y.1 Y.2 V b).1 b_surj
  let XV : AlgebraicSpaces B S hS := ⟨pullback f.hom ψ.hom,
    isAlgebraicSpace_pullback B S hS f.hom ψ.hom X.2 (schemeSpace V).2 Y.2⟩
  let prX : XV ⟶ X := ObjectProperty.homMk (pullback.fst f.hom ψ.hom)
  let fV : XV ⟶ schemeSpace V := ObjectProperty.homMk (pullback.snd f.hom ψ.hom)
  have sqX : IsPullback prX fV f ψ :=
    isPullback_of_isPullback_hom B S hS (IsPullback.of_hasPullback f.hom ψ.hom)
  have prX_et : IsEtale B S hS prX.hom :=
    isEtale_of_isPullback B S hS fV prX ψ f sqX.flip ψ_et
  obtain ⟨U, φ, α, φ_et, φ_surj, hφα⟩ := exists_etale_surjective_schemeSpace_chart B S hS V fV
  let Y'V : AlgebraicSpaces B S hS := ⟨pullback g.hom ψ.hom,
    isAlgebraicSpace_pullback B S hS g.hom ψ.hom Y'.2 (schemeSpace V).2 Y.2⟩
  let prY : Y'V ⟶ Y' := ObjectProperty.homMk (pullback.fst g.hom ψ.hom)
  let gV : Y'V ⟶ schemeSpace V := ObjectProperty.homMk (pullback.snd g.hom ψ.hom)
  have sqY : IsPullback prY gV g ψ :=
    isPullback_of_isPullback_hom B S hS (IsPullback.of_hasPullback g.hom ψ.hom)
  have prY_et : IsEtale B S hS prY.hom :=
    isEtale_of_isPullback B S hS gV prY ψ g sqY.flip ψ_et
  obtain ⟨V', φ', β, φ'_et, φ'_surj, hφ'β⟩ := exists_etale_surjective_schemeSpace_chart B S hS V gV
  let e' : schemeSpace V' ⟶ Y' := φ' ≫ prY
  have e'_et : IsEtale B S hS e'.hom := isEtale_comp B S hS φ'_et prY_et
  have he' : schemeSpaceMap β ≫ ψ = e' ≫ g := by
    rw [← hφ'β, Category.assoc, Category.assoc, sqY.w]
  let X'' : AlgebraicSpaces B S hS := ⟨pullback fV.hom (schemeSpaceMap β).hom,
    isAlgebraicSpace_pullback B S hS fV.hom (schemeSpaceMap β).hom XV.2 (schemeSpace V').2
      (schemeSpace V).2⟩
  let p₁ : X'' ⟶ XV := ObjectProperty.homMk (pullback.fst fV.hom (schemeSpaceMap β).hom)
  let p₂ : X'' ⟶ schemeSpace V' :=
    ObjectProperty.homMk (pullback.snd fV.hom (schemeSpaceMap β).hom)
  have sq'' : IsPullback p₁ p₂ fV (schemeSpaceMap β) :=
    isPullback_of_isPullback_hom B S hS (IsPullback.of_hasPullback fV.hom (schemeSpaceMap β).hom)
  have sqP : IsPullback (schemeSpaceMap (pullback.fst α β)) (schemeSpaceMap (pullback.snd α β))
      (schemeSpaceMap α) (schemeSpaceMap β) :=
    isPullback_of_isPullback_hom B S hS ((IsPullback.of_hasPullback α β).map yoneda)
  let ρ₁ : schemeSpace (pullback α β) ⟶ X'' :=
    sq''.lift (schemeSpaceMap (pullback.fst α β) ≫ φ) (schemeSpaceMap (pullback.snd α β))
      (by rw [Category.assoc, hφα, sqP.w])
  have sq₁ : IsPullback (schemeSpaceMap (pullback.fst α β)) ρ₁ φ p₁ :=
    IsPullback.of_bot (by rw [sq''.lift_snd, hφα]; exact sqP) (sq''.lift_fst _ _ _).symm sq''
  have ρ₁_et : IsEtale B S hS ρ₁.hom :=
    isEtale_of_isPullback B S hS (schemeSpaceMap (pullback.fst α β)) ρ₁ φ p₁ sq₁ φ_et
  let ρ₂ : X'' ⟶ X' := sqA.lift (p₁ ≫ prX) (p₂ ≫ e')
    (by rw [Category.assoc, sqX.w, ← Category.assoc, sq''.w, Category.assoc, he',
      Category.assoc]; rfl)
  have sq₂ : IsPullback ρ₂ p₂ f' e' :=
    IsPullback.of_right (by rw [sqA.lift_fst, ← he']; exact sq''.paste_horiz sqX)
      (sqA.lift_snd _ _ _) sqA
  have ρ₂_et : IsEtale B S hS ρ₂.hom := isEtale_of_isPullback B S hS p₂ ρ₂ e' f' sq₂.flip e'_et
  let ρ := ρ₁ ≫ ρ₂
  have ρ_et : IsEtale B S hS ρ.hom := isEtale_comp B S hS ρ₁_et ρ₂_et
  obtain ⟨v, hv⟩ := ψ_surj (pointsMap B S hS Y'.1 g.hom (pointsMap B S hS X'.1 f'.hom x'))
  obtain ⟨z, hz, -⟩ := exists_point_of_isPullback B S hS sqY
    (pointsMap B S hS X'.1 f'.hom x') v hv.symm
  obtain ⟨v', hv'⟩ := φ'_surj z
  obtain ⟨x'', hx''ρ, hx''p⟩ := exists_point_of_isPullback B S hS sq₂ x' v' (by
    show _ = pointsMap B S hS _ (φ'.hom ≫ prY.hom) v'
    rw [pointsMap_comp, Function.comp_apply, hv', hz])
  obtain ⟨u, hu⟩ := φ_surj (pointsMap B S hS X''.1 p₁.hom x'')
  obtain ⟨w, hwu, hwx⟩ := exists_point_of_isPullback B S hS sq₁ u x'' hu
  have hρw : pointsMap B S hS _ ρ.hom w = x' := by
    show pointsMap B S hS _ (ρ₁.hom ≫ ρ₂.hom) w = x'
    rw [pointsMap_comp, Function.comp_apply, hwx, hx''ρ]
  let ι : schemeSpace U ⟶ X := φ ≫ prX
  have ι_et : IsEtale B S hS ι.hom := isEtale_comp B S hS φ_et prX_et
  have hια : ι ≫ f = schemeSpaceMap α ≫ ψ := by
    rw [← hφα, Category.assoc, Category.assoc, sqX.w]
  have hρ₁fst : ρ₁ ≫ p₁ = schemeSpaceMap (pullback.fst α β) ≫ φ := sq''.lift_fst _ _ _
  have hρ₁snd : ρ₁ ≫ p₂ = schemeSpaceMap (pullback.snd α β) := sq''.lift_snd _ _ _
  have hρ₂fst : ρ₂ ≫ g' = p₁ ≫ prX := sqA.lift_fst _ _ _
  have hρ₂snd : ρ₂ ≫ f' = p₂ ≫ e' := sqA.lift_snd _ _ _
  have hfstι : schemeSpaceMap (pullback.fst α β) ≫ ι = ρ ≫ g' := by
    show _ = ρ₁ ≫ ρ₂ ≫ g'
    rw [hρ₂fst, reassoc_of% hρ₁fst]
  have hsnde : schemeSpaceMap (pullback.snd α β) ≫ e' = ρ ≫ f' := by
    show _ = ρ₁ ≫ ρ₂ ≫ f'
    rw [hρ₂snd, reassoc_of% hρ₁snd]
  have hιu : pointsMap B S hS _ ι.hom u = pointsMap B S hS X'.1 g'.hom x' := by
    have key := congrArg (fun k : schemeSpace (pullback α β) ⟶ X ↦
      pointsMap B S hS _ k.hom w) hfstι
    change pointsMap B S hS _ ((schemeSpaceMap (pullback.fst α β)).hom ≫ ι.hom) w =
      pointsMap B S hS _ (ρ.hom ≫ g'.hom) w at key
    rw [pointsMap_comp, pointsMap_comp, Function.comp_apply, Function.comp_apply, hwu,
      hρw] at key
    exact key
  have hwu' : pointsMap B S hS (yoneda.obj (pullback α β)) (yoneda.map (pullback.fst α β)) w =
      u := hwu
  have h₁ : IsRelativeWeaklyAssociatedPoint B S hS (ι ≫ f) ((modulePullback B S hS ι).obj F) u :=
    (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS ι ι_et f F u).2 (hιu ▸ hx)
  rw [hια] at h₁
  have h₂ := isRelativeWeaklyAssociatedPoint_of_comp_of_isEtale B S hS (schemeSpaceMap α) ψ ψ_et
    _ h₁
  have : LocallyOfFiniteType (𝐓.map α) :=
    f_lft U V ι.hom b α ((isEtale_iff_presheaf_of_yoneda B S hS ι.hom).1 ι_et) b_et
      (congrArg (fun k ↦ k.hom) hια).symm
  have halg := alg V' V e'.hom b β ((isEtale_iff_presheaf_of_yoneda B S hS e'.hom).1 e'_et) b_et
    (congrArg (fun k ↦ k.hom) he')
  have hNqc : ((modulePullback B S hS ι).obj F).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS ι F hF
  have h₃ := isRelativeWeaklyAssociatedPoint_representedPullback_of_isAlgebraic B S hS α β halg
    ((modulePullback B S hS ι).obj F) hNqc w (by rwa [hwu'])
  have h₄ := isRelativeWeaklyAssociatedPoint_comp_of_isEtale B S hS
    (representedSpaceMap B S hS (pullback.snd α β)) e' e'_et _ h₃
  have hmod : (modulePullback B S hS (representedSpaceMap B S hS (pullback.fst α β))).obj
        ((modulePullback B S hS ι).obj F) ≅
      (modulePullback B S hS ρ).obj ((modulePullback B S hS g').obj F) :=
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS (pullback.fst α β)) ι).app F ≪≫
      eqToIso (congrArg (fun k ↦ (modulePullback B S hS k).obj F) hfstι) ≪≫
      ((modulePullbackCompIso B S hS ρ g').app F).symm
  have h₅ : IsRelativeWeaklyAssociatedPoint B S hS (ρ ≫ f')
      ((modulePullback B S hS ρ).obj ((modulePullback B S hS g').obj F)) w := by
    rw [← hsnde]
    exact (isRelativeWeaklyAssociatedPoint_congr _ hmod w).1 h₄
  have h₆ := (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS ρ ρ_et f' _ w).1 h₅
  rwa [hρw] at h₆

/-- **Stacks 0CV3, read on étale charts.** Under the hypotheses of
`isRelativeWeaklyAssociatedPoint_baseChange_of_isAlgebraic_charts`, the relative weak assassin of
`(g')^*F` along `f'` is the inverse image under `|g'|` of that of `F` along `f`. -/
private theorem relativeWeaklyAssociatedPoints_modulePullback_eq_preimage_of_isAlgebraic_charts
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (f_lft : IsLocallyOfFiniteType B S hS f.hom)
    (alg : ∀ (V' V : BigFppfOver B S hS) (a : yoneda.obj V' ⟶ Y'.1) (b : yoneda.obj V ⟶ Y.1)
      (β : V' ⟶ V),
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝐓).presheaf a →
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u}) 𝐓).presheaf b →
      yoneda.map β ≫ b = a ≫ g.hom → ∀ v' : 𝐓.obj V',
        letI := ((𝐓.map β).residueFieldMap v').hom.toAlgebra
        Algebra.IsAlgebraic ((𝐓.obj V).residueField (𝐓.map β v')) ((𝐓.obj V').residueField v')) :
    relativeWeaklyAssociatedPoints B S hS f' ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' relativeWeaklyAssociatedPoints B S hS f F :=
  Set.Subset.antisymm
    (relativeWeaklyAssociatedPoints_modulePullback_subset_preimage B S hS sq F) fun _ hx' ↦
    isRelativeWeaklyAssociatedPoint_baseChange_of_isAlgebraic_charts B S hS sq F f_lft alg hx'

/-! ### Stacks 0CV3 -/

/-- Let

```
X' --g'--> X
|f'        |f
Y' --g---> Y
```

be a cartesian square of algebraic spaces over `S`, let `F` be a quasi-coherent `𝒪_X`-module and
put `F' = (g')^*F`. Assume that `f` is locally of finite type and that for every `y' ∈ |Y'|` the
transcendence degree of `y'/g(y')` is `0` (Stacks 04NM). Then the relative weak assassin
`WeakAss_{X'/Y'}(F')` of Stacks 0CV0 is the inverse image of `WeakAss_{X/Y}(F)` under `|g'|`. -/
@[stacks 0CV3]
theorem relativeWeaklyAssociatedPoints_modulePullback_eq_preimage
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (f_lft : IsLocallyOfFiniteType B S hS f.hom)
    (g_trdeg : ∀ y' : points B S hS Y'.1, HasTranscendenceDegreeAt B S hS g.hom y' 0) :
    relativeWeaklyAssociatedPoints B S hS f' ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' relativeWeaklyAssociatedPoints B S hS f F := by
  refine relativeWeaklyAssociatedPoints_modulePullback_eq_preimage_of_isAlgebraic_charts B S hS
    sq F f_lft fun V' V a b β a_et b_et comm v' ↦ ?_
  let c : EtaleChartAtPoint B S hS g.hom (pointsMap B S hS (yoneda.obj V') a
      ((schemePointRepresentative B S hS V' v').class B S hS (yoneda.obj V'))) :=
    { U := V'
      V := V
      a := a
      b := b
      h := β
      a_etale := a_et
      b_etale := b_et
      comm := comm
      representative := schemePointRepresentative B S hS V' v'
      point := IsLocalRing.closedPoint (schemePointRepresentative B S hS V' v').carrier
      maps_to := rfl }
  have hc : c.sourcePoint B S hS = v' :=
    (sourcePoint_eq_schemePoint ..).trans (schemePointRepresentative_point B S hS V' v')
  have htr := g_trdeg _ c
  rw [hc] at htr
  exact isAlgebraic_residueField_of_hasResidueFieldTranscendenceDegree_zero _ v' htr

/-- **Stacks 0CV3 for a locally quasi-finite base change.** In a cartesian square of algebraic
spaces over `S` with `f` locally of finite type and `g` locally quasi-finite, and for a
quasi-coherent `𝒪_X`-module `F`, the relative weak assassin of `(g')^*F` along `f'` is the inverse
image under `|g'|` of the relative weak assassin of `F` along `f`. -/
theorem relativeWeaklyAssociatedPoints_modulePullback_eq_preimage_of_isLocallyQuasiFinite
    (sq : IsPullback g'.hom f'.hom f.hom g.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    [F.IsQuasicoherentOnSite] (f_lft : IsLocallyOfFiniteType B S hS f.hom)
    (g_lqf : IsLocallyQuasiFinite B S hS g.hom) :
    relativeWeaklyAssociatedPoints B S hS f' ((modulePullback B S hS g').obj F) =
      pointsMap B S hS X'.1 g'.hom ⁻¹' relativeWeaklyAssociatedPoints B S hS f F := by
  refine relativeWeaklyAssociatedPoints_modulePullback_eq_preimage_of_isAlgebraic_charts B S hS
    sq F f_lft fun V' V a b β a_et b_et comm v' ↦ ?_
  obtain ⟨-, hqf⟩ := g_lqf V' V a b β a_et b_et comm
  have : LocallyQuasiFinite (𝐓.map β) := hqf
  let := ((𝐓.map β).residueFieldMap v').hom.toAlgebra
  have := residueField_finite_of_locallyQuasiFinite (𝐓.map β) v'
  exact Algebra.IsAlgebraic.of_finite _ _

end AlgebraicGeometry.Space

end
