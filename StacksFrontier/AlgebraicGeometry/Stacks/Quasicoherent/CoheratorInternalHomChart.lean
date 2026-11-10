module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineSpannedSections


/-!
# The restriction to an algebraic space commutes with the internal Hom

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism from the algebraic stack of an algebraic space `U` to an
algebraic stack, and `d : ℱ ↦ f^*ℱ|_{U_étale}` the restriction of Stacks 0GQS. For a module `ℱ`
cartesian between affine objects (for instance a quasi-coherent one, by Stacks 0GZV) and any
`𝒢`, the comparison map `d(𝓗om_{𝒪_𝒳}(ℱ, 𝒢)) ⟶ 𝓗om_{𝒪_U}(d(ℱ), d(𝒢))`, restriction of morphisms
along the slices, is an isomorphism.

Over an affine étale chart `V` lying over the object `x` of `𝒳`, both sides are computed by the
sections of `ℱ` over `x` and the relations among them: a morphism `ℱ|_x ⟶ 𝒢|_x` is the same as a
family of sections of `𝒢` over `x` satisfying those relations
(`Stacks.SheafOfModules.FreeSheafification.exists_hom_of_terminal`), and a morphism out of
`d(ℱ)|_V` is determined by its values on them
(`Stacks.SheafOfModules.FreeSheafification.hom_ext_of_terminal`). Affine charts cover, so the
comparison is bijective everywhere.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.chartInternalHomComparison`: the comparison map.
* `AlgebraicGeometry.Stack.FlatFppf.isIso_chartInternalHomComparison`: it is an isomorphism.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 0GQT](https://stacks.math.columbia.edu/tag/0GQT)
* [Stacks Project, Tag 0GN2](https://stacks.math.columbia.edu/tag/0GN2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.FlatFppf

universe u w

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

/-- The object of `𝒳` attached to an étale chart `W` of `U` lies over the scheme of `W`. -/
theorem chartFunctor_obj_base (W : Space.SmallEtale B S hS U) :
    𝒳.val.val.p.obj ((chartFunctor B S hS 𝒳 U hU f).obj W) = W.obj.left :=
  Functor.congr_obj f.hom.hom.w (chartObject.{u, w} B S hS U hU W)

/-- The object of `𝒳` attached to an affine étale chart of `U` lies over an affine scheme. -/
theorem isAffine_chartFunctor_obj (W : Space.SmallEtale B S hS U)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj ((Space.SmallEtale.toOver B S hS U).obj W))) :
    IsAffine ((𝒳.val.val.p ⋙ BigFppfOver.toScheme B S hS).obj
      ((chartFunctor B S hS 𝒳 U hU f).obj W)) := by
  change IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj
    ((chartFunctor B S hS 𝒳 U hU f).obj W)))
  rwa [chartFunctor_obj_base]

/-- The structure map `𝒪_U ⟶ u^*𝒪_𝒳` of the restriction `d` is bijective on every group of
sections. -/
theorem bijective_chartRingHom_app (W : (Space.SmallEtale B S hS U)ᵒᵖ) :
    Function.Bijective ((chartRingHom B S hS 𝒳 U hU f).app W) := by
  have : IsIso ((chartRingHom B S hS 𝒳 U hU f).app W) := by
    dsimp only [chartRingHom, Space.etaleChartStructureHom, Functor.whiskerRight_app,
      NatTrans.op_app]
    rw [eqToHom_app, eqToHom_op, eqToHom_map]
    rw [← eqToIso.hom]
    exact Iso.isIso_hom _
  exact ConcreteCategory.bijective_of_isIso _

/-- **The comparison map `d(Hom(F, G)) ⟶ Hom(d(F), d(G))`** of the restriction
`d : ℱ ↦ f^*ℱ|_{U_étale}`, at the universe of the internal Homs. -/
def chartInternalHomComparison
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳)) :
    spaceChartRestriction B S hS 𝒳 U hU f
        (RingedSite.internalHomSheaf (fppfRingedSite B S hS 𝒳) F G) ⟶
      Space.smallEtaleInternalHom B S hS U hU (spaceChartRestriction B S hS 𝒳 U hU f F)
        (spaceChartRestriction B S hS 𝒳 U hU f G) :=
  ⟨PresheafOfModules.internalHomPushforwardMap (chartFunctor B S hS 𝒳 U hU f)
    (fppfRingedSite B S hS 𝒳).O.obj (Space.smallEtaleRingedSite B S hS U hU).O.obj
    (chartRingHom B S hS 𝒳 U hU f) F.val G.val⟩

/-- Over an affine étale chart `V`, the sections of `d(F)` over `V` generate `d(F)` over every
affine object of the slice at `V`, for `F` cartesian between affine objects. -/
theorem hspan_chart (F : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F)
    (V : (Space.smallEtaleRingedSite B S hS U hU).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((Space.SmallEtale.toOver B S hS U).obj V)))
    (W : Over V)
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((Space.SmallEtale.toOver B S hS U).obj W.left)))
    (m : ((spaceChartRestriction B S hS 𝒳 U hU f F).over V).val.obj (op W)) :
    ∃ c : F.val.obj (op ((chartFunctor B S hS 𝒳 U hU f).obj V)) →₀
        ((Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS U hU).O).over
          V).obj.obj (op W),
      (c.sum fun i r ↦ r • (show ((spaceChartRestriction B S hS 𝒳 U hU f F).over V).val.obj
        (op W) from ((spaceChartRestriction B S hS 𝒳 U hU f F).over V).val.map
          ((Over.isTerminalMkId V).from W).op i)) = m := by
  classical
  let hp := 𝒳.val.isFiberedInGroupoids
  let x := (chartFunctor B S hS 𝒳 U hU f).obj V
  let g := (chartFunctor B S hS 𝒳 U hU f).map W.hom
  let := fibredSectionAlgebra (B := B) (S := S) (hS := hS) (p := 𝒳.val.val.p) g
  let := fibredSectionsModule hp F x
  let := fibredSectionsModule hp F ((chartFunctor B S hS 𝒳 U hU f).obj W.left)
  let := fibredSectionsModuleOver hp F g
  have : IsScalarTower (fibredSectionRing B S hS 𝒳.val.val.p x)
      (fibredSectionRing B S hS 𝒳.val.val.p ((chartFunctor B S hS 𝒳 U hU f).obj W.left))
      (F.val.obj (op ((chartFunctor B S hS 𝒳 U hU f).obj W.left))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨c₀, hc₀⟩ := Module.BaseChange.exists_finsupp_of_surjective_liftBaseChange
    (fibredSectionsRestrict hp F g)
    (hF g (isAffine_chartFunctor_obj B S hS 𝒳 U hU f V hV)
      (isAffine_chartFunctor_obj B S hS 𝒳 U hU f W.left hW)).2 m
  obtain ⟨c, rfl⟩ := Finsupp.mapRange_surjective
    ((chartRingHom B S hS 𝒳 U hU f).app (op W.left)).hom (map_zero _)
    (bijective_chartRingHom_app B S hS 𝒳 U hU f (op W.left)).2 c₀
  exact ⟨c, (Finsupp.sum_mapRange_index fun _ ↦ by exact zero_smul _ _).symm.trans hc₀⟩

/-- The sections of `d(F)` over an affine chart `V` generate `d(F)` locally on the slice at `V`. -/
theorem hgen_chart (F : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F)
    (V : (Space.smallEtaleRingedSite B S hS U hU).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((Space.SmallEtale.toOver B S hS U).obj V)))
    (W : Over V) (m : ((spaceChartRestriction B S hS 𝒳 U hU f F).over V).val.obj (op W)) :
    ∃ T : Sieve W, T ∈ ((Space.smallEtaleRingedSite B S hS U hU).J.over V) W ∧
      ∀ ⦃W' : Over V⦄ (g : W' ⟶ W), T.arrows g →
        ∃ c : F.val.obj (op ((chartFunctor B S hS 𝒳 U hU f).obj V)) →₀
            ((Stacks.SheafOfModules.Tensor.ringSheaf
              (Space.smallEtaleRingedSite B S hS U hU).O).over V).obj.obj (op W'),
          (c.sum fun i r ↦ r • (show ((spaceChartRestriction B S hS 𝒳 U hU f F).over V).val.obj
            (op W') from ((spaceChartRestriction B S hS 𝒳 U hU f F).over V).val.map
              ((Over.isTerminalMkId V).from W').op i)) =
            ((spaceChartRestriction B S hS 𝒳 U hU f F).over V).val.map g.op m :=
  Stacks.SheafOfModules.FreeSheafification.hgen_of_presieve (Over.mk (𝟙 V))
    (Over.isTerminalMkId V) ((spaceChartRestriction B S hS 𝒳 U hU f F).over V)
    (I := F.val.obj (op ((chartFunctor B S hS 𝒳 U hU f).obj V))) (fun i ↦ i)
    (fun W' ↦ IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((Space.SmallEtale.toOver B S hS U).obj W'.left)))
    (fun W ↦ by
      obtain ⟨I, Y, a, haff, hcov⟩ :=
        Space.SmallEtale.exists_affine_ofArrows_over_ringedSite B S hS U hU W
      exact ⟨Presieve.ofArrows Y a, hcov, fun _ _ hg ↦ by rcases hg with ⟨j⟩; exact haff j⟩)
    (fun W' hW' m' ↦ hspan_chart B S hS 𝒳 U hU f F hF V hV W' hW' m') W m

/-- The comparison map at an étale chart `V`, evaluated at the terminal object of the slice at `V`,
is the evaluation at the terminal object of the slice at the object of `𝒳` attached to `V`. -/
theorem chartInternalHomComparison_app_terminal
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (V : (Space.smallEtaleRingedSite B S hS U hU).C)
    (α : (RingedSite.internalHomSheaf (fppfRingedSite B S hS 𝒳) F G).val.obj
      (op ((chartFunctor B S hS 𝒳 U hU f).obj V)))
    (i : F.val.obj (op ((chartFunctor B S hS 𝒳 U hU f).obj V))) :
    ((ConcreteCategory.hom ((chartInternalHomComparison B S hS 𝒳 U hU f F G).val.app (op V))) α).app
        (op (Over.mk (𝟙 V))) i =
      α.app (op (Over.mk (𝟙 ((chartFunctor B S hS 𝒳 U hU f).obj V)))) i :=
  PresheafOfModules.app_over_mk_congr (fppfRingedSite B S hS 𝒳).O.obj α
    ((chartFunctor B S hS 𝒳 U hU f).map_id V) i

/-- **The comparison map `d(Hom(F, G)) ⟶ Hom(d(F), d(G))` is bijective over an affine chart**,
for `F` cartesian between affine objects. -/
theorem bijective_chartInternalHomComparison_app_of_isAffine
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F)
    (V : (Space.smallEtaleRingedSite B S hS U hU).C)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((Space.SmallEtale.toOver B S hS U).obj V))) :
    Function.Bijective ((chartInternalHomComparison B S hS 𝒳 U hU f F G).val.app (op V)) := by
  classical
  let hp := 𝒳.val.isFiberedInGroupoids
  let x := (chartFunctor B S hS 𝒳 U hU f).obj V
  have hx := isAffine_chartFunctor_obj B S hS 𝒳 U hU f V hV
  let c := (chartInternalHomComparison B S hS 𝒳 U hU f F G).val.app (op V)
  let := fibredSectionsModule hp F x
  let := fibredSectionsModule hp G x
  let φ : (Space.smallEtaleInternalHom B S hS U hU (spaceChartRestriction B S hS 𝒳 U hU f F)
      (spaceChartRestriction B S hS 𝒳 U hU f G)).val.obj (op V) →
      ((restrFun (Space.smallEtaleRingedSite B S hS U hU).O.obj
        V).obj (spaceChartRestriction B S hS 𝒳 U hU f F).val ⟶
      (restrFun (Space.smallEtaleRingedSite B S hS U hU).O.obj V).obj
        (spaceChartRestriction B S hS 𝒳 U hU f G).val) := fun γ ↦ γ
  have hφ : ∀ a b, φ a = φ b → a = b := fun _ _ h ↦ h
  have hgenX := hgen_over_of_isCartesianBetweenAffines B S hS 𝒳.val.val.p hp F hF hx
  have hrelX := hrel_over_of_isCartesianBetweenAffines B S hS 𝒳.val.val.p hp F hF hx
  have hgenU := hgen_chart B S hS 𝒳 U hU f F hF V hV
  constructor
  · intro α β h
    have hαβ : (⟨α⟩ : F.over x ⟶ G.over x) = ⟨β⟩ :=
      Stacks.SheafOfModules.FreeSheafification.hom_ext_of_terminal (Over.mk (𝟙 x))
        (Over.isTerminalMkId x) (F.over x) (fun i ↦ i) hgenX fun i ↦ by
          have := congrArg (fun γ ↦ (φ γ).app (op (Over.mk (𝟙 V)))
            (show F.val.obj (op x) from i)) h
          exact (chartInternalHomComparison_app_terminal B S hS 𝒳 U hU f F G V α i).symm.trans
            (this.trans (chartInternalHomComparison_app_terminal B S hS 𝒳 U hU f F G V β i))
    exact congrArg _root_.SheafOfModules.Hom.val hαβ
  · intro ψ
    let T := op (Over.mk (𝟙 V))
    let ψT := (φ ψ).app T
    let gP : F.val.obj (op x) → G.val.obj (op x) := fun i ↦ ψT i
    have hlin : ∀ (r : fibredSectionRing B S hS 𝒳.val.val.p x) (m : F.val.obj (op x)),
        r • gP m = gP (r • m) := fun r m ↦ by
      obtain ⟨s, rfl⟩ := (bijective_chartRingHom_app B S hS 𝒳 U hU f (op V)).2 r
      exact (ψT.hom.map_smul
        (show (ORestr (Space.smallEtaleRingedSite B S hS U hU).O.obj V).obj T from s)
        (show ((restrFun (Space.smallEtaleRingedSite B S hS U hU).O.obj
          V).obj (spaceChartRestriction B S hS 𝒳 U hU f F).val).obj T from m)).symm
    have hgP : ∀ k : Module.BaseChange.Relations (fibredSectionRing B S hS 𝒳.val.val.p x)
        (F.val.obj (op x)), (k.1.sum fun i r ↦ r • gP i) = 0 := fun k ↦ by
      calc (k.1.sum fun i r ↦ r • gP i) = k.1.sum fun i r ↦ gP (r • i) :=
            Finset.sum_congr rfl fun i _ ↦ hlin _ _
        _ = gP (k.1.sum fun i r ↦ r • i) := (map_finsuppSum ψT.hom _ _).symm
        _ = 0 := by rw [k.2]; exact map_zero ψT.hom
    obtain ⟨α', hα'⟩ := Stacks.SheafOfModules.FreeSheafification.exists_hom_of_terminal
      (Over.mk (𝟙 x)) (Over.isTerminalMkId x) (F.over x) (F.val.obj (op x))
      (Module.BaseChange.Relations (fibredSectionRing B S hS 𝒳.val.val.p x) (F.val.obj (op x)))
      (fun i ↦ i) (fun k ↦ k.1) (fun k ↦ k.2) hgenX hrelX (G.over x) gP hgP
    refine ⟨α'.val, ?_⟩
    have := Space.smallEtaleRingedSite_hasSheafify_over B S hS U hU V
    have := Space.smallEtaleRingedSite_wEqualsLocallyBijective_over B S hS U hU V
    have key : ∀ i : F.val.obj (op x), (φ (c α'.val)).app T i = (φ ψ).app T i := fun i ↦
      (chartInternalHomComparison_app_terminal B S hS 𝒳 U hU f F G V α'.val i).trans (hα' i)
    have hψ : (⟨φ (c α'.val)⟩ : (spaceChartRestriction B S hS 𝒳 U hU f F).over V ⟶
        (spaceChartRestriction B S hS 𝒳 U hU f G).over V) = ⟨φ ψ⟩ :=
      Stacks.SheafOfModules.FreeSheafification.hom_ext_of_terminal
      (Over.mk (𝟙 V)) (Over.isTerminalMkId V) ((spaceChartRestriction B S hS 𝒳 U hU f F).over V)
      (I := F.val.obj (op x)) (fun i ↦ i) hgenU key
    exact hφ _ _ (congrArg _root_.SheafOfModules.Hom.val hψ)

/-- A sheaf of modules gives a sheaf of types. -/
theorem isSheaf_types_of_sheafOfModules {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    (M : _root_.SheafOfModules.{u + 1} R) :
    Presieve.IsSheaf J (M.val.presheaf ⋙ forget AddCommGrpCat.{u + 1}) :=
  (isSheaf_iff_isSheaf_of_type J _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget J M.val.presheaf (forget AddCommGrpCat.{u + 1})).1
      M.isSheaf)

/-- **The comparison map `d(Hom(F, G)) ⟶ Hom(d(F), d(G))` is an isomorphism** for `F` cartesian
between affine objects (for instance quasi-coherent) and `G` arbitrary. -/
theorem isIso_chartInternalHomComparison
    (F G : _root_.SheafOfModules.{u} (ambientRingStructureSheaf B S hS 𝒳))
    (hF : IsCartesianBetweenAffines 𝒳.val.isFiberedInGroupoids F) :
    IsIso (chartInternalHomComparison B S hS 𝒳 U hU f F G) := by
  let c := chartInternalHomComparison B S hS 𝒳 U hU f F G
  have hb : ∀ V : (Space.smallEtaleRingedSite B S hS U hU).C,
      Function.Bijective (c.val.app (op V)) := fun V ↦
    Presieve.bijective_app_of_bijective_cover
      (isSheaf_types_of_sheafOfModules (spaceChartRestriction B S hS 𝒳 U hU f
        (RingedSite.internalHomSheaf (fppfRingedSite B S hS 𝒳) F G)))
      (isSheaf_types_of_sheafOfModules (Space.smallEtaleInternalHom B S hS U hU
        (spaceChartRestriction B S hS 𝒳 U hU f F) (spaceChartRestriction B S hS 𝒳 U hU f G)))
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf _).map c.val) (forget _))
      (fun W ↦ IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((Space.SmallEtale.toOver B S hS U).obj W)))
      (fun W ↦ by
        obtain ⟨I, Y, a, haff, hcov, -⟩ := Space.SmallEtale.exists_affine_etale_ofArrows B S hS U W
        exact ⟨Presieve.ofArrows Y a, hcov, fun _ _ hg ↦ by
          rcases hg with ⟨j⟩; exact haff j⟩)
      (fun W hW ↦ bijective_chartInternalHomComparison_app_of_isAffine B S hS 𝒳 U hU f F G hF W hW)
      V
  have : IsIso ((_root_.SheafOfModules.forget _).map c) :=
    PresheafOfModules.isIso_of_isIso_app _ fun V ↦
      (ConcreteCategory.isIso_iff_bijective _).2 (hb V.unop)
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.forget _)

end AlgebraicGeometry.Stack.FlatFppf

end
