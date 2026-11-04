module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Cohomology.GlobalGeneration.Stalks
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion
public import StacksFrontier.Topology.Sheaves.Modules.SupportSection

/-!
# The support of a quotient `M/ℱ` on an algebraic space, read on one étale chart

Let `X` be an algebraic space, `M` a quasi-coherent `𝒪_X`-module, `ℱ ⊆ M` a quasi-coherent
submodule, `W` an étale scheme chart of `X` and `ℱ'` a submodule, on the chart scheme, of a module
identified with the restriction `M|_W` of Stacks 03G6 (`AlgebraicGeometry.Space.restrictToChart`),
contained in `ℱ|_W`. Then `(M/ℱ)|_W` is a quotient of the quotient by `ℱ'`; hence if the quotient
by `ℱ'` is supported away from an open of `W` lying over `U ⊆ X` and covering it, then `M/ℱ` is
supported away from `U`. This is clause (b) of Stacks 085N on `X`, from the chart statement.

## Main results

* `AlgebraicGeometry.Space.epi_restrictToChartFunctor_map`: restriction of modules to an étale
  scheme chart carries an epimorphism of quasi-coherent modules to an epimorphism.
* `AlgebraicGeometry.Space.restrictToChartFunctor_map_zero`: the restriction sends the zero
  morphism to the zero morphism.
* `AlgebraicGeometry.Space.supp_restrictToChart_cokernel_subset`: if `ℱ'` is carried into the
  image of `ℱ|_W ⟶ M|_W`, then the support of `(M/ℱ)|_W` is contained in the support of the
  quotient by `ℱ'`.
* `AlgebraicGeometry.Space.disjoint_supportOfSheaf_cokernel_of_chart`: **clause (b) of
  Stacks 085N on `X` from the chart statement**: the support (Stacks 04KA) of `M/ℱ` misses `U` as
  soon as the Zariski support of the quotient by `ℱ'` misses an open `V` of the chart lying over
  `U` and covering it.
* `AlgebraicGeometry.Space.RelativeProjSituation.disjoint_supportOfSheaf_cokernel_of_point`: the
  same in Situation 0849 at an étale scheme point `f : T ⟶ X`.

## References

* [Stacks Project, Tag 085N](https://stacks.math.columbia.edu/tag/085N)
* [Stacks Project, Tag 07TY](https://stacks.math.columbia.edu/tag/07TY)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.ImageSubsheaf

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- **Restriction to an étale scheme chart carries an epimorphism of quasi-coherent `𝒪_X`-modules
to an epimorphism.** -/
theorem epi_restrictToChartFunctor_map {M N : Modules.{u, u} B S hS X.1 X.2} (p : M ⟶ N)
    [hp : Epi p] (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS X.1) :
    Epi ((restrictToChartFunctor B S hS X.2 W).map p) := by
  let J := Opens.grothendieckTopology (etaleChartScheme B S hS W)
  let : HasSheafify J AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, u} _ _
  let : J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, u} _
  let F₁ := SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
    SheafOfModules.forget _ ⋙
    PresheafOfModules.pushforward.{u} (chartRestrictionRingHom B S hS X.2 W)
  have hg : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map (F₁.map p)) := by
    refine ⟨fun {O} s x hx => ?_⟩
    obtain ⟨_, ⟨O', hO' : IsAffineOpen O', rfl⟩, hxO', hO'O⟩ :=
      (etaleChartScheme B S hS W).isBasis_affineOpens.exists_subset_of_mem_open hx O.2
    obtain ⟨m, hm⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite p hp hM hN
      ((chartOpens B S hS W).obj O') hO'
      (((F₁.obj N).map (homOfLE hO'O).op s).down)
    exact ⟨O', homOfLE hO'O, ⟨ULift.up m, congrArg ULift.up hm⟩, hxO'⟩
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    ((Presheaf.isLocallySurjective_presheafToSheaf_map_iff J _).2 hg)

/-- Restriction to an étale scheme chart sends the zero morphism to the zero morphism. -/
theorem restrictToChartFunctor_map_zero (W : SmallEtale B S hS X.1)
    (M N : Modules.{u, u} B S hS X.1 X.2) :
    (restrictToChartFunctor B S hS X.2 W).map (0 : M ⟶ N) = 0 := by
  have : (SheafOfModules.forget.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget _
  have := Stacks.PresheafOfModules.preservesZeroMorphisms_pushforward.{u}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
    (chartRestrictionRingHom B S hS X.2 W)
  have h : (SheafOfModules.uliftForPresentationFunctor.{u + 1, u, u, u, u}
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
        SheafOfModules.forget.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
        PresheafOfModules.pushforward.{u}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS X.1 X.2).O).obj)
          (chartRestrictionRingHom B S hS X.2 W) ⋙
        PresheafOfModules.sheafification.{u}
          (𝟙 (etaleChartScheme B S hS W).ringCatSheaf.obj)).PreservesZeroMorphisms :=
    inferInstance
  exact h.map_zero M N

/-- A morphism of sheaves of modules out of `M₂` which kills the image of `f : M₁ ⟶ M₂` after
composition kills every section of the image submodule of `f`. -/
theorem app_eq_zero_of_mem_imageSubmodule {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M₁ M₂ M₃ : SheafOfModules.{u} R} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃)
    (hfg : f ≫ g = 0) {O : Cᵒᵖ} {a : M₂.val.obj O} (ha : a ∈ (imageSubmodule f).obj O) :
    g.val.app O a = 0 := by
  refine ((Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget M₃) _
    ((mem_localImage_obj_iff f a).1 ha)).isSeparatedFor.ext (fun V k hk => ?_)
  obtain ⟨b, hb⟩ := hk
  change M₃.val.map k.op (g.val.app O a) = M₃.val.map k.op 0
  rw [map_zero, ← PresheafOfModules.naturality_apply g.val k.op a]
  have h0 : g.val.app (op V) (f.val.app (op V) b) = 0 := by
    change (f ≫ g).val.app (op V) b = 0
    rw [hfg]
    rfl
  exact (congrArg (g.val.app (op V)) hb).symm.trans h0

variable (M : Modules.{u, u} B S hS X.1 X.2) (ℱ : M.Submodule)

/-- **The support of `(M/ℱ)|_W` is contained in that of the quotient by a chart-level submodule
`ℱ'` which `ℱ|_W` contains**, that is, which an identification `e : A ≅ M|_W` carries into the
image of `ℱ|_W ⟶ M|_W`. -/
theorem supp_restrictToChart_cokernel_subset (hM : M.IsQuasicoherentOnSite)
    (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite) (W : SmallEtale B S hS X.1)
    {A : SheafOfModules.{u} (etaleChartScheme B S hS W).ringCatSheaf}
    (e : A ≅ restrictToChart B S hS X.2 M W) (ℱ' : A.Submodule)
    (hcompat : ∀ (O : (TopologicalSpace.Opens (etaleChartScheme B S hS W))ᵒᵖ)
      (a : A.val.obj O), a ∈ ℱ'.obj O →
        e.hom.val.app O a ∈
          (imageSubmodule ((restrictToChartFunctor B S hS X.2 W).map ℱ.ι)).obj O) :
    SheafOfModules.supp (restrictToChart B S hS X.2 (cokernel ℱ.ι) W) ⊆
      SheafOfModules.supp (cokernel ℱ'.ι) := by
  have hQ : (cokernel ℱ.ι).IsQuasicoherentOnSite :=
    @isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 _ _ hℱ hM ℱ.ι
  let r := (restrictToChartFunctor B S hS X.2 W).map (cokernel.π ℱ.ι)
  have hr : Epi r := epi_restrictToChartFunctor_map (cokernel.π ℱ.ι) hM hQ W
  have hRz : (restrictToChartFunctor B S hS X.2 W).map ℱ.ι ≫ r = 0 := by
    rw [← Functor.map_comp, cokernel.condition, restrictToChartFunctor_map_zero]
  have hzero : ℱ'.ι ≫ e.hom ≫ r = 0 := by
    ext O a
    exact app_eq_zero_of_mem_imageSubmodule _ r hRz (hcompat O a.1 a.2)
  let c := cokernel.desc ℱ'.ι (e.hom ≫ r) hzero
  have hc : Epi c := by
    have := @epi_comp _ _ _ _ _ e.hom inferInstance r hr
    exact epi_of_epi_fac (cokernel.π_desc ℱ'.ι (e.hom ≫ r) hzero)
  rintro x ⟨a, ha⟩
  obtain ⟨b, hb⟩ := (AlgebraicGeometry.epi_iff_stalk_surjective
    (etaleChartScheme B S hS W).ringCatSheaf c).mp hc x a
  exact ⟨b, fun hbz => ha (hb ▸ hbz ▸ map_zero _)⟩

/-- **Clause (b) of Stacks 085N on `X`, from the chart statement.**  Let `W` be an étale scheme
chart of `X`, `ℱ ⊆ M` a quasi-coherent submodule of a quasi-coherent `𝒪_X`-module, and `ℱ'` a
submodule of a module `A` on the chart scheme identified with `M|_W` by `e`, which `e` carries into
the image of `ℱ|_W ⟶ M|_W` (the chart compatibility `ℱ' ⊆ ℱ|_W`).  If the support of `A/ℱ'` misses
an open `V` of the chart whose image covers `U`, then the support of `M/ℱ` misses `U`. -/
theorem disjoint_supportOfSheaf_cokernel_of_chart (hM : M.IsQuasicoherentOnSite)
    (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite) (W : SmallEtale B S hS X.1)
    {A : SheafOfModules.{u} (etaleChartScheme B S hS W).ringCatSheaf}
    (e : A ≅ restrictToChart B S hS X.2 M W) (ℱ' : A.Submodule)
    (hcompat : ∀ (O : (TopologicalSpace.Opens (etaleChartScheme B S hS W))ᵒᵖ)
      (a : A.val.obj O), a ∈ ℱ'.obj O →
        e.hom.val.app O a ∈
          (imageSubmodule ((restrictToChartFunctor B S hS X.2 W).map ℱ.ι)).obj O)
    (V : (etaleChartScheme B S hS W).Opens)
    (hV : (V : Set (etaleChartScheme B S hS W)) ∩
      (⟨(cokernel ℱ'.ι).val, (cokernel ℱ'.ι).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u} (etaleChartScheme B S hS W).toRingedSpace).supp = ∅)
    (U : Set (points B S hS X.1))
    (hUV : ∀ x ∈ U, ∃ t ∈ V, pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W))
      W.obj.hom ((pointsEquivScheme B S hS ((SmallEtale.toOver B S hS X.1).obj W)).symm t) = x) :
    Disjoint (supportOfSheaf B S hS X.1
      ((SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj (cokernel ℱ.ι))) U := by
  have hQ : (cokernel ℱ.ι).IsQuasicoherentOnSite :=
    @isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 _ _ hℱ hM ℱ.ι
  refine Set.disjoint_right.2 fun x hxU hx => ?_
  obtain ⟨t, htV, rfl⟩ := hUV x hxU
  have ht : t ∈ SheafOfModules.supp (restrictToChart B S hS X.2 (cokernel ℱ.ι) W) := by
    rwa [supp_restrictToChart_eq_preimage_supportOfSheaf_of_isQuasicoherent B S hS X W
      (cokernel ℱ.ι)]
  exact hV.subset ⟨htV, supp_restrictToChart_cokernel_subset M ℱ hM hℱ W e ℱ' hcompat ht⟩

/-- **Clause (b) of Stacks 085N on `X`, at an étale scheme point.**  Let `f : T ⟶ X` be an étale
scheme point of the space of Situation 0849, `ℱ ⊆ 𝒜_d` a quasi-coherent submodule, and `ℱ'` a
submodule of a module `A` on `T` identified with the restriction `𝒜_d|_T` by `e`, carried by `e`
into the image of `ℱ|_T ⟶ 𝒜_d|_T`.  If the support of `A/ℱ'` misses an open `V ⊆ T` whose image
covers `U`, the support of `𝒜_d/ℱ` misses `U`. -/
theorem RelativeProjSituation.disjoint_supportOfSheaf_cokernel_of_point
    (s : RelativeProjSituation.{u, u}) {T : BigFppfOver s.site s.base s.containsBase}
    {f : yoneda.obj T ⟶ s.space.1}
    (hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf f)
    {d : ℤ} (ℱ : (s.algebra.piece d).Submodule) (hℱ : ℱ.toSheafOfModules.IsQuasicoherentOnSite)
    {A : SheafOfModules.{u}
      ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).ringCatSheaf}
    (e : A ≅ restrictToChart s.site s.base s.containsBase s.space.2 (s.algebra.piece d)
      ⟨CostructuredArrow.mk f, hf⟩)
    (ℱ' : A.Submodule)
    (hcompat : ∀ (O : (TopologicalSpace.Opens
        ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T))ᵒᵖ)
      (a : A.val.obj O), a ∈ ℱ'.obj O →
        e.hom.val.app O a ∈ (imageSubmodule ((restrictToChartFunctor s.site s.base s.containsBase
          s.space.2 ⟨CostructuredArrow.mk f, hf⟩).map ℱ.ι)).obj O)
    (V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens)
    (hV : (V : Set ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T)) ∩
      (⟨(cokernel ℱ'.ι).val, (cokernel ℱ'.ι).isSheaf⟩ :
        RingedSpace.ModuleSheaf.{u}
          ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).toRingedSpace).supp = ∅)
    {U : Set (points s.site s.base s.containsBase s.space.1)}
    (hUV : U ⊆ (fun t ↦ pointsMap s.site s.base s.containsBase (yoneda.obj T) f
      ((schemePointsHomeomorph s.site s.base s.containsBase T).symm t)) '' V) :
    Disjoint (supportOfSheaf s.site s.base s.containsBase s.space.1
      ((SheafOfModules.toSheaf (structureRingSheaf s.site s.base s.containsBase s.space)).obj
        (cokernel ℱ.ι))) U :=
  disjoint_supportOfSheaf_cokernel_of_chart (X := s.space) (s.algebra.piece d) ℱ
    (s.isQuasicoherent d) hℱ ⟨CostructuredArrow.mk f, hf⟩ e ℱ' hcompat V hV U
    (fun _ hx => hUV hx)

end AlgebraicGeometry.Space

end
