module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.Copower
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleResolution

/-!
# The simplex-coefficient resolution of a sheaf of modules on a simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of rings on its total site. For a sheaf of
`O`-modules `M` on the total site, the degree-`n` term `B_n(M)` of the *simplex-coefficient
resolution* of `M` is the sheaf of `O`-modules whose sections over an object `U` of simplicial
degree `k` are the direct sum `⨁_{α : [n] ⟶ [k]} M(U)`, one copy of `M(U)` for each simplex map
`[n] ⟶ [k]`. A simplex map `θ : [m] ⟶ [n]` relabels the summands by precomposition, which makes
`n ↦ B_n(M)` a simplicial sheaf of `O`-modules, and summing the summands augments it onto `M`.

The alternating-face complex `… ⟶ B_2(M) ⟶ B_1(M) ⟶ B_0(M) ⟶ M ⟶ 0` is exact. This is the
module-coefficient counterpart of the simplex-coefficient resolution of an abelian sheaf in
`StacksFrontier/CategoryTheory/Sites/Simplicial/AugmentationResolution.lean`, which is the complex of
the proof of Stacks 0D78; the proof of Stacks 0D7C is that proof with modules as coefficients.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.simplexIndicesFunctor`: the presheaves of simplex labels
  `U ↦ Hom([n], [deg U])`, as a simplicial object.
* `CategoryTheory.SimplicialSiteSituation.moduleBarPresheaf`: the presheaf of modules underlying
  `B_n(M)`, the copower of `M` by the presheaf of `n`-simplex labels.
* `CategoryTheory.SimplicialSiteSituation.moduleBarSimplicial`: the simplicial sheaf of modules
  `n ↦ B_n(M)`.
* `CategoryTheory.SimplicialSiteSituation.moduleBarAugmented`: its augmentation onto `M`.
* `CategoryTheory.SimplicialSiteSituation.moduleBarComplex`: its alternating-face complex.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleBarPresheaf_isSheaf`: the presheaf `B_n(M)` is
  already a sheaf, being on every simplicial component a finite direct sum of copies of `M`.
* `CategoryTheory.SimplicialSiteSituation.moduleBarComplex_exactAt`,
  `.moduleBarComplex_exact_zero` and `.moduleBarAugmentation_epi`: **the simplex-coefficient
  complex resolves `M`**: it is exact in every positive degree and at the augmentation, and the
  augmentation is an epimorphism.

## Implementation notes

The exactness is objectwise. Over an object `U` of degree `k` the augmented simplicial module
`n ↦ ⨁_{α : [n] ⟶ [k]} M(U)` is the image of the augmented standard simplex `Δ[k]` under the
copower functor `ModuleCat.copower (M(U))`, so Mathlib's extra degeneracy of `Δ[k]` contracts it.
That gives exactness of presheaves of modules; the passage to sheaves of modules uses that the
forgetful functor from sheaves to presheaves of modules is fully faithful and left exact, and runs
downwards from the augmentation, exactly as for the resolution of the structure sheaf in
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleResolution.lean`, whose
lemmas are private there and are restated here.

No sheafification occurs: over the component of degree `m` the presheaf `B_n(M)` is the direct
sum of the copies of `M` indexed by the finite set of simplex maps `[n] ⟶ [m]`, a sheaf, and a
presheaf on the total site is a sheaf as soon as it is one on every component.

## References

* [Stacks Project, Tag 0D7C](https://stacks.math.columbia.edu/tag/0D7C)
* [Stacks Project, Tag 0D78](https://stacks.math.columbia.edu/tag/0D78)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor
open scoped Simplicial ZeroObject

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] SimplicialSite.totalPseudofunctor
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete totalCategory Quiver.Hom.toLoc
  CoGrothendieck.category CoGrothendieck.categoryStruct CoGrothendieck.ι Cat.str
  Grothendieck.ι Grothendieck.instCategory uliftFunctor componentFunctor component
  simplexIndices totalSimplexDegree PresheafOfModules.presheaf

/-! ### Exactness on sheaves of modules from exactness on presheaves -/

section Exactness

private lemma epi_map_kernelLift_of_exact'
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Abelian D]
    [HasFiniteLimits C] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (T : ShortComplex C) (h : (T.map F).Exact) :
    Epi (F.map (kernel.lift T.g T.f T.zero)) := by
  let k := (KernelFork.ofι (kernel.ι T.g) (kernel.condition T.g)).map F
  let hk := KernelFork.mapIsLimit _ (kernelIsKernel T.g) F
  let l := h.leftHomologyDataOfIsLimitKernelFork k hk
  have : Epi l.f' := h.epi_f' l
  have hl : l.f' = F.map (kernel.lift T.g T.f T.zero) := by
    apply Fork.IsLimit.hom_ext hk
    show l.f' ≫ l.i = F.map (kernel.lift T.g T.f T.zero) ≫ F.map (kernel.ι T.g)
    rw [l.f'_i, ← F.map_comp, kernel.lift_ι]
    rfl
  rwa [hl] at this


private lemma exact_of_map'
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Abelian D]
    [HasFiniteLimits C] [HasZeroObject C] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] (T : ShortComplex C) [HasCokernel T.f]
    [PreservesColimit (parallelPair T.f 0) F] (h : (T.map F).Exact) : T.Exact := by
  let r := ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel T
  have hr : r.IsPreservedBy F := ⟨inferInstance, inferInstance⟩
  have hz : IsZero r.H := by
    apply IsZero.of_full_of_faithful_of_isZero F
    exact ((r.map F).exact_iff).1 h
  have he : Epi (kernel.lift T.g T.f T.zero) :=
    F.epi_of_epi_map (epi_map_kernelLift_of_exact' F T h)
  let l : T.LeftHomologyData :=
    { K := kernel T.g
      H := 0
      i := kernel.ι T.g
      π := 0
      wi := kernel.condition T.g
      hi := kernelIsKernel T.g
      wπ := comp_zero
      hπ := CokernelCofork.IsColimit.ofEpiOfIsZero _ he (isZero_zero C) }
  have : IsIso (ShortComplex.leftRightHomologyComparison' l r) :=
    (isZero_zero C).isIso hz _
  exact ⟨⟨ShortComplex.HomologyData.ofIsIsoLeftRightHomologyComparison' l r,
    isZero_zero C⟩⟩

/-- A short complex is exact as soon as its image under a fully faithful, additive, left exact
functor into an abelian category is exact and the image of the next short complex is exact too. -/
private lemma exact_of_map_of_exact_next'
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Abelian D]
    [HasFiniteLimits C] [HasZeroObject C] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    [PreservesFiniteLimits F] (T : ShortComplex C) {Y : C} (t : T.X₃ ⟶ Y)
    (ht : T.g ≫ t = 0) (h : (T.map F).Exact)
    (hnext : ((ShortComplex.mk T.g t ht).map F).Exact) : T.Exact := by
  let p := kernel.lift t T.g ht
  have hp : T.f ≫ p = 0 := by
    rw [← cancel_mono (kernel.ι t), Category.assoc, kernel.lift_ι,
      Limits.zero_comp, T.zero]
  let T' := ShortComplex.mk T.f p hp
  let φ : T' ⟶ T :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι t
      comm₁₂ := by simp [T']
      comm₂₃ := by simp [T', p] }
  have : Epi (F.mapShortComplex.map φ).τ₁ := by
    show Epi (F.map (𝟙 T.X₁))
    rw [F.map_id]
    infer_instance
  have : IsIso (F.mapShortComplex.map φ).τ₂ := by
    show IsIso (F.map (𝟙 T.X₂))
    rw [F.map_id]
    infer_instance
  have : Mono (F.mapShortComplex.map φ).τ₃ := by
    show Mono (F.map (kernel.ι t))
    infer_instance
  have hm : (T'.map F).Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (F.mapShortComplex.map φ)).2 h
  have ep : Epi (F.map p) := epi_map_kernelLift_of_exact' F (ShortComplex.mk T.g t ht) hnext
  have : Epi (T'.map F).g := ep
  have hc : IsColimit ((CokernelCofork.ofπ p hp).map F) := hm.gIsCokernel
  have hc' := (CokernelCofork.isColimitMapCoconeEquiv _ F).symm hc
  have hC := isColimitOfReflects F hc'
  let : HasCokernel T.f := ⟨⟨_, hC⟩⟩
  let : PreservesColimit (parallelPair T.f 0) F :=
    preservesColimit_of_preserves_colimit_cocone hC hc'
  exact exact_of_map' F T h

/-- A short complex of presheaves of modules is exact as soon as all its evaluations are. -/
private lemma presheaf_exact_of_evaluation'
    {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (T : ShortComplex (PresheafOfModules.{u} R))
    (h : ∀ U, (T.map (PresheafOfModules.evaluation R U)).Exact) : T.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  ext1 U
  have hz : IsZero ((PresheafOfModules.evaluation R U).obj T.homology) :=
    IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).1 (h U))
      (T.mapHomologyIso (PresheafOfModules.evaluation R U)).symm
  exact hz.eq_of_src _ _

end Exactness

/-! ### Sheaves on the total site are detected on the components -/

section Sheaf

/-- A presheaf of types on the total site whose restriction to every simplicial component is a
sheaf is a sheaf: the covering families of the total site lie in single components. -/
theorem isSheaf_of_isSheaf_componentFunctor_op_comp (S : SimplicialSiteSituation.{u})
    (P : S.totalCategoryᵒᵖ ⥤ Type u)
    (h : ∀ n, Presieve.IsSheaf (S.componentTopology n)
      ((componentFunctor S n).op ⋙ P)) :
    Presieve.IsSheaf S.totalTopology P := by
  have isSheafFor_map_of_comp' : ∀ {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
      (F : C ⥤ D) (P : Dᵒᵖ ⥤ Type u) {X : C} (R : Presieve X),
      Presieve.IsSheafFor (F.op ⋙ P) R → Presieve.IsSheafFor P (R.map F) := by
    intro C _ D _ F P X R h
    obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
    rw [Presieve.map_ofArrows, Presieve.isSheafFor_arrows_iff]
    rw [Presieve.isSheafFor_arrows_iff] at h
    exact fun x hx => h x fun i j Z a b hab =>
      hx i j (F.obj Z) (F.map a) (F.map b) (by simpa only [← F.map_comp] using congrArg F.map hab)
  rcases S with ⟨C | C⟩
  · have := C.totalCoverage_hasPullbacks
    have := C.totalCoverage_isStableUnderBaseChange
    rw [show SimplicialSiteSituation.totalTopology ⟨Sum.inl C⟩ =
        C.totalCoverage.toGrothendieck from rfl,
      Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
    rintro X R ⟨T, hT, rfl⟩
    exact isSheafFor_map_of_comp' _ P T
      ((h X.base.unop).isSheafFor_of_mem_precoverage hT)
  · let K := coverageFromIsSite (SimplicialCoverings.total C.underlying C.coverage)
      (CategoryTheory.SimplicialCoverings.total_isSite C.underlying C.coverage C.isSite
        C.isCocontinuous C.hasCoverPullbacks)
    show Presieve.IsSheaf K.toPrecoverage.toGrothendieck P
    rw [Coverage.toGrothendieck_toPrecoverage, Presieve.isSheaf_coverage]
    rintro X R ⟨E, hE, rfl⟩
    obtain ⟨T, hT, hE⟩ := hE
    change E = T.map (Grothendieck.ι C.underlying X.base) at hE
    rw [hE, PreZeroHypercover.presieve₀_map]
    exact isSheafFor_map_of_comp' _ P T.presieve₀
      ((h X.base.unop).isSheafFor_of_mem_precoverage ⟨T, hT, rfl⟩)

end Sheaf

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology RingCat.{u})

/-! ### The simplex labels -/

/-- The presheaves of simplex labels `U ↦ Hom([n], [deg U])` of
`CategoryTheory.SimplicialSiteSituation.simplexIndices`, as a simplicial object: a simplex map
`θ : [m] ⟶ [n]` relabels by precomposition with `θ`. -/
def simplexIndicesFunctor : SimplicialObject (S.totalCategoryᵒᵖ ⥤ Type u) where
  obj n := simplexIndices.{u, u} S n.unop
  map θ := simplexIndicesMap.{u, u} S θ.unop
  map_id n := by
    simp [simplexIndicesMap, simplexIndices]
  map_comp θ θ' := by
    simp only [simplexIndicesMap, unop_comp, op_comp, Functor.map_comp,
      Functor.whiskerRight_comp, Functor.whiskerLeft_comp]

/-! ### The terms of the resolution -/

variable {S O} (M : SheafOfModules.{u} O)

/-- The presheaf of modules underlying the degree-`n` term `B_n(M)` of the simplex-coefficient
resolution: the copower of `M` by the presheaf of `n`-simplex labels. Over an object of degree
`k` it is `⨁_{α : [n] ⟶ [k]} M(U)`. -/
abbrev moduleBarPresheaf (n : SimplexCategory) : PresheafOfModules.{u} O.obj :=
  PresheafOfModules.copowerObj M.val (simplexIndices.{u, u} S n)

/-- Over the component of degree `m`, the sections of `B_n(M)` are the functions from the simplex
maps `[n] ⟶ [m]` to the sections of `M`. -/
private def moduleBarComponentUnderlyingIso (n m : SimplexCategory) :
    (componentFunctor S m).op ⋙ (moduleBarPresheaf M n).presheaf ⋙ forget AddCommGrpCat.{u} ≅
      ((componentFunctor S m).op ⋙ M.val.presheaf ⋙ forget AddCommGrpCat.{u}) ⋙
        coyoneda.obj (Opposite.op (ULift.{u} (n ⟶ m))) := by
  rcases S with ⟨C | C⟩ <;>
  refine NatIso.ofComponents (fun U => ((Finsupp.equivFunOnFinite :
      (ULift.{u} (n ⟶ m) →₀ M.val.obj (Opposite.op ((componentFunctor _ m).obj U.unop))) ≃
        (ULift.{u} (n ⟶ m) → M.val.obj (Opposite.op ((componentFunctor _ m).obj U.unop)))).trans
      TypeCat.homEquiv.symm).toIso) ?_
  all_goals
    intro U V f
    dsimp [PresheafOfModules.presheaf]
    ext x i
    refine (congrArg (fun y : ULift.{u} (n ⟶ m) →₀ _ => y i)
      (PresheafOfModules.copowerObj_map_apply M.val _
        ((componentFunctor _ m).map f.unop).op x)).trans ?_
    have hid : ∀ a, (ConcreteCategory.hom ((simplexIndices.{u, u} _ n).map
        ((componentFunctor _ m).map f.unop).op)) a = a :=
      fun a => ULift.ext (Category.comp_id a.down)
    have hinj : Function.Injective (ConcreteCategory.hom ((simplexIndices.{u, u} _ n).map
        ((componentFunctor _ m).map f.unop).op)) := fun a b h => by rwa [hid, hid] at h
    conv_lhs => rw [← hid i]
    exact (Finsupp.mapDomain_apply_of_injective hinj _ _).trans rfl

/-- **The presheaf `B_n(M)` is a sheaf**: over the component of degree `m` it is a finite direct
sum of copies of `M`, a sheaf, and the total site is detected on the components. -/
theorem moduleBarPresheaf_isSheaf (n : SimplexCategory) :
    Presheaf.IsSheaf S.totalTopology (moduleBarPresheaf M n).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{u})
  rw [isSheaf_iff_isSheaf_of_type]
  apply isSheaf_of_isSheaf_componentFunctor_op_comp
  intro m
  rw [← isSheaf_iff_isSheaf_of_type]
  apply (Presheaf.isSheaf_of_iso_iff (moduleBarComponentUnderlyingIso M n m)).2
  exact Presheaf.isSheaf_comp_of_isSheaf _ _ _
    (Presheaf.isSheaf_comp_of_isSheaf _ ((componentModuleRestriction S O m).obj M).val.presheaf
      (forget AddCommGrpCat.{u}) ((componentModuleRestriction S O m).obj M).isSheaf)

/-- The degree-`n` term `B_n(M)` of the simplex-coefficient resolution, as a sheaf of modules. -/
def moduleBarSheaf (n : SimplexCategory) : SheafOfModules.{u} O where
  val := moduleBarPresheaf M n
  isSheaf := moduleBarPresheaf_isSheaf M n

/-- The simplex-coefficient resolution on presheaves of modules: the copower of `M` by the
simplicial presheaf of simplex labels. -/
abbrev moduleBarSimplicialPresheaf : SimplicialObject (PresheafOfModules.{u} O.obj) :=
  simplexIndicesFunctor S ⋙ PresheafOfModules.copowerFunctor M.val

/-- **The simplex-coefficient resolution** `n ↦ B_n(M)`, as a simplicial sheaf of `O`-modules: a
simplex map `θ : [m] ⟶ [n]` relabels the summand at `α : [n] ⟶ [k]` as the summand at `θ ≫ α`. -/
def moduleBarSimplicial : SimplicialObject (SheafOfModules.{u} O) where
  obj n := moduleBarSheaf M n.unop
  map θ := ⟨(moduleBarSimplicialPresheaf M).map θ⟩
  map_id n := (SheafOfModules.forget O).map_injective ((moduleBarSimplicialPresheaf M).map_id n)
  map_comp θ θ' :=
    (SheafOfModules.forget O).map_injective ((moduleBarSimplicialPresheaf M).map_comp θ θ')

/-- The augmentation `B_n(M) ⟶ M`, summing the summands. -/
def moduleBarAugmentation (n : SimplexCategory) : moduleBarSheaf M n ⟶ M :=
  ⟨PresheafOfModules.copowerSum M.val (simplexIndices.{u, u} S n)⟩

/-- The simplex-coefficient resolution augmented onto `M`. -/
def moduleBarAugmented : SimplicialObject.Augmented (SheafOfModules.{u} O) where
  left := moduleBarSimplicial M
  right := M
  hom :=
    { app := fun n => moduleBarAugmentation M n.unop
      naturality := by
        intro m n θ
        apply (SheafOfModules.forget O).map_injective
        change PresheafOfModules.copowerMap M.val _ ≫ PresheafOfModules.copowerSum M.val _ =
          PresheafOfModules.copowerSum M.val _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact PresheafOfModules.copowerMap_comp_copowerSum M.val _ }

/-- The alternating-face complex `… ⟶ B_2(M) ⟶ B_1(M) ⟶ B_0(M)` of the simplex-coefficient
resolution. -/
def moduleBarComplex : ChainComplex (SheafOfModules.{u} O) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (moduleBarSimplicial M)

/-! ### Exactness -/

/-- The augmented standard simplex `Δ[m]` carried to modules by the copower by `A`. -/
private abbrev copowerStdSimplex {R : Type u} [Ring R] (A : ModuleCat.{u} R)
    (m : SimplexCategory) : SimplicialObject.Augmented (ModuleCat.{u} R) :=
  ((SimplicialObject.Augmented.whiskering (Type u) (ModuleCat.{u} R)).obj
    (ModuleCat.copower A)).obj (SSet.Augmented.stdSimplex.obj m)

/-- Over an object `U` of degree `k`, the simplex-coefficient resolution is the copower of `M(U)`
by the standard simplex `Δ[k]`. -/
private def moduleBarSimplicialEvaluationIso (U : S.totalCategoryᵒᵖ) :
    moduleBarSimplicial M ⋙ (SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U) ≅
      (copowerStdSimplex (M.val.obj U) ((totalSimplexDegree S).obj U.unop).unop).left :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by ext; rfl

/-- The same identification, augmentation included. -/
private def moduleBarAugmentedEvaluationIso (U : S.totalCategoryᵒᵖ) :
    ((SimplicialObject.Augmented.whiskering _ _).obj
      (SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U)).obj
        (moduleBarAugmented M) ≅
    copowerStdSimplex (M.val.obj U) ((totalSimplexDegree S).obj U.unop).unop := by
  let e : (ModuleCat.copower (M.val.obj U)).obj (⊤_ (Type u)) ≅ M.val.obj U :=
    (Finsupp.LinearEquiv.finsuppUnique (O.obj.obj U) (M.val.obj U) (⊤_ (Type u))).toModuleIso
  refine Comma.isoMk (moduleBarSimplicialEvaluationIso M U) e.symm ?_
  apply NatTrans.ext
  funext n
  refine ModuleCat.copower_hom_ext fun a => ?_
  change ModuleCat.copowerMk a ≫ 𝟙 _ ≫ (ModuleCat.copower (M.val.obj U)).map (terminal.from _) =
    ModuleCat.copowerMk a ≫ ModuleCat.copowerDesc (fun _ => 𝟙 (M.val.obj U)) ≫ e.inv
  rw [Category.id_comp, ModuleCat.copowerMk_comp_map, ← Category.assoc,
    ModuleCat.copowerMk_comp_desc, Category.id_comp]
  ext y
  change Finsupp.single _ y =
    (Finsupp.LinearEquiv.finsuppUnique (O.obj.obj U) (M.val.obj U) (⊤_ (Type u))).symm y
  rw [LinearEquiv.eq_symm_apply, Finsupp.LinearEquiv.finsuppUnique_apply, Finsupp.single_apply,
    if_pos (Subsingleton.elim _ _)]

/-- Objectwise, the simplex-coefficient complex is exact in every positive degree. -/
private lemma moduleBarComplex_evaluation_exactAt (U : S.totalCategoryᵒᵖ) (n : ℕ) (hn : 0 < n) :
    (((SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U).mapHomologicalComplex
      _).obj (moduleBarComplex M)).ExactAt n := by
  let e := (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      (SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U)).app
        (moduleBarSimplicial M) ≪≫
    (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      (moduleBarSimplicialEvaluationIso M U)
  apply HomologicalComplex.ExactAt.of_iso (e := e.symm)
  exact exactAt_of_extraDegeneracy _
    ((SSet.Augmented.StandardSimplex.extraDegeneracy
      ((totalSimplexDegree S).obj U.unop).unop).map (ModuleCat.copower (M.val.obj U))) n hn

/-- The augmentation annihilates the first differential. -/
theorem moduleBarComplex_d_comp_augmentation :
    (moduleBarComplex M).d 1 0 ≫ (moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌) = 0 :=
  augmented_d_comp (moduleBarAugmented M)

/-- Objectwise, the simplex-coefficient complex is exact at the augmentation. -/
private lemma moduleBarComplex_evaluation_exact_zero (U : S.totalCategoryᵒᵖ) :
    ((ShortComplex.mk ((moduleBarComplex M).d 1 0)
      ((moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌))
      (moduleBarComplex_d_comp_augmentation M)).map
        (SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U)).Exact := by
  let F := SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U
  let A := ((SimplicialObject.Augmented.whiskering _ _).obj F).obj (moduleBarAugmented M)
  let ed := ((SSet.Augmented.StandardSimplex.extraDegeneracy
    ((totalSimplexDegree S).obj U.unop).unop).map
      (ModuleCat.copower (M.val.obj U))).ofIso (moduleBarAugmentedEvaluationIso M U).symm
  let e := (AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso F).app
    (moduleBarSimplicial M)
  have hz : ((AlgebraicTopology.alternatingFaceMapComplex _).obj A.left).d 1 0 ≫
      A.hom.app (Opposite.op ⦋0⦌) = 0 := by
    have h := (AlgebraicTopology.AlternatingFaceMapComplex.ε.app A).comm 1 0
    exact h.symm.trans Limits.zero_comp
  let T := ShortComplex.mk _ _ hz
  let T' := (ShortComplex.mk ((moduleBarComplex M).d 1 0)
      ((moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌))
      (moduleBarComplex_d_comp_augmentation M)).map F
  have ei : T' ≅ T := ShortComplex.isoMk
    (HomologicalComplex.Hom.isoApp e 1) (HomologicalComplex.Hom.isoApp e 0) (Iso.refl _)
    (by exact e.hom.comm 1 0)
    (by ext x; rfl)
  exact ShortComplex.exact_of_iso ei.symm (extraDegeneracy_exact_zero A ed)

/-- Objectwise, the augmentation is surjective: a section is the sum of itself placed at a
single simplex label, and the constant simplex map at `0` is always available. -/
private lemma moduleBarAugmentation_surjective (n : SimplexCategory) (U : S.totalCategoryᵒᵖ) :
    Function.Surjective ((moduleBarAugmentation M n).val.app U) := by
  intro x
  let a : (simplexIndices.{u, u} S n).obj U :=
    ULift.up (SimplexCategory.const n ((totalSimplexDegree S).obj U.unop).unop 0)
  refine ⟨(ModuleCat.copowerMk a).hom x, ?_⟩
  show (ModuleCat.copowerMk a ≫ (PresheafOfModules.copowerSum M.val _).app U).hom x = x
  rw [PresheafOfModules.copowerMk_comp_copowerSum_app]
  rfl

/-- The augmentation `B_0(M) ⟶ M` is an epimorphism of presheaves of modules. -/
private lemma moduleBarAugmentation_forget_epi :
    Epi ((SheafOfModules.forget O).map ((moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌))) := by
  constructor
  intro F f g h
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨y, rfl⟩ := moduleBarAugmentation_surjective M ⦋0⦌ U x
  exact congrArg (fun k => k.app U y) h

/-- The augmentation `B_0(M) ⟶ M` is an epimorphism of sheaves of modules. -/
theorem moduleBarAugmentation_epi :
    Epi ((moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌)) :=
  (SheafOfModules.forget O).epi_of_epi_map (moduleBarAugmentation_forget_epi M)

private lemma moduleBarComplex_presheaf_exact_positive (n : ℕ) :
    (((moduleBarComplex M).sc' (n + 2) (n + 1) n).map (SheafOfModules.forget O)).Exact := by
  apply presheaf_exact_of_evaluation'
  intro U
  let F := SheafOfModules.forget O ⋙ PresheafOfModules.evaluation O.obj U
  let K := (F.mapHomologicalComplex _).obj (moduleBarComplex M)
  exact (K.exactAt_iff' (n + 2) (n + 1) n (by simp) (by simp)).1
    (moduleBarComplex_evaluation_exactAt M U (n + 1) (by omega))

private lemma moduleBarComplex_presheaf_exact_zero :
    ((ShortComplex.mk ((moduleBarComplex M).d 1 0)
      ((moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌))
      (moduleBarComplex_d_comp_augmentation M)).map (SheafOfModules.forget O)).Exact :=
  presheaf_exact_of_evaluation' _ (moduleBarComplex_evaluation_exact_zero M)

/-- **The simplex-coefficient complex is exact at the augmentation.** -/
theorem moduleBarComplex_exact_zero :
    (ShortComplex.mk ((moduleBarComplex M).d 1 0)
      ((moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌))
      (moduleBarComplex_d_comp_augmentation M)).Exact := by
  let : HasZeroObject (SheafOfModules.{u} O) := hasZeroObject_of_hasTerminal_object
  let T := ShortComplex.mk ((moduleBarComplex M).d 1 0)
      ((moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌))
      (moduleBarComplex_d_comp_augmentation M)
  apply exact_of_map_of_exact_next' (SheafOfModules.forget O) T (0 : T.X₃ ⟶ 0)
    (Limits.comp_zero) (moduleBarComplex_presheaf_exact_zero M)
  exact (ShortComplex.exact_iff_epi _
    (show (SheafOfModules.forget O).map (0 : T.X₃ ⟶ 0) = 0 from Functor.map_zero _ _ _)).2
    (moduleBarAugmentation_forget_epi M)

/-- **The simplex-coefficient complex is exact in every positive degree.** -/
theorem moduleBarComplex_exactAt (n : ℕ) (hn : 0 < n) : (moduleBarComplex M).ExactAt n := by
  let : HasZeroObject (SheafOfModules.{u} O) := hasZeroObject_of_hasTerminal_object
  cases n with
  | zero => omega
  | succ k =>
    let K := moduleBarComplex M
    apply (K.exactAt_iff' (k + 2) (k + 1) k (by simp) (by simp)).2
    cases k with
    | zero =>
      exact exact_of_map_of_exact_next' (SheafOfModules.forget O) (K.sc' 2 1 0)
        ((moduleBarAugmented M).hom.app (Opposite.op ⦋0⦌))
        (moduleBarComplex_d_comp_augmentation M)
        (moduleBarComplex_presheaf_exact_positive M 0)
        (moduleBarComplex_presheaf_exact_zero M)
    | succ k =>
      exact exact_of_map_of_exact_next' (SheafOfModules.forget O)
        (K.sc' (k + 3) (k + 2) (k + 1)) (K.d (k + 1) k) (K.d_comp_d _ _ _)
        (moduleBarComplex_presheaf_exact_positive M (k + 1))
        (moduleBarComplex_presheaf_exact_positive M k)

end CategoryTheory.SimplicialSiteSituation

end
