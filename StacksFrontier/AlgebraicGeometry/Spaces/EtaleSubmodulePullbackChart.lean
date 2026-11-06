module

public import StacksFrontier.AlgebraicGeometry.Spaces.AnnihilatorSubsheafPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.GradedAlgebraChartSubmodule
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackCompIsoEtaleRestriction

/-!
# Étale pullback of submodules, and chart restriction along composed charts

Let `f : Y ⟶ X` be an étale morphism of algebraic spaces and `M` an `𝒪_X`-module, with étale
pullback `M|_Y = f^*M` (`AlgebraicGeometry.Space.etaleModulePullback`). This file shows that
`f^*` preserves modules of finite type, and compares the chart restrictions of `f^*M` and of
submodules `f^*N ⊆ f^*M` along charts of `Y` with those of `M` and `N` along the composite charts
of `X`.

## Main definitions

* `Stacks.SheafOfModules.mapSubmodule`: the image of a submodule `N ⊆ M` under a functor `Φ` of
  sheaves of modules, the sections of `Φ M` lying locally in the range of `Φ` of the inclusion.
  `AlgebraicGeometry.Space.restrictSubmoduleToChart` is the case of the chart restriction
  functor (`AlgebraicGeometry.Space.restrictSubmoduleToChart_eq_mapSubmodule`, by definition).

The étale pullback `f^*N ⊆ f^*M` of a submodule is
`AlgebraicGeometry.Space.etaleSubmoduleRestrict`, whose sections over a chart `V` of `Y` are the
sections of `N` over the composite chart of `X`; `f^*` carries `N` isomorphically onto `f^*N`
(`AlgebraicGeometry.Space.etaleSubmoduleRestrictIso`, compatibly with the inclusions).

## Main results

* `AlgebraicGeometry.Space.isFiniteTypeOnSite_etaleModulePullback`: `f^*M` is of finite type when
  `M` is.
* `Stacks.SheafOfModules.mapSubmodule_eq_mapSubmodule_comp_of_iso`: images of submodules compose
  along a composite of functors, provided the first carries the submodule isomorphically onto a
  submodule through which it factors.
* `AlgebraicGeometry.Space.restrictToChartScheme_etaleModulePullback`: **the chart restriction of
  `f^*M` along a chart `V` of `Y` is the chart restriction of `M` along the composite chart**, an
  equality of modules on the chart scheme.
* `AlgebraicGeometry.Space.restrictSubmoduleToChart_etaleSubmoduleRestrict`: **the chart
  restriction of `f^*N` is the image of `N` under the composite of the étale pullback and the
  chart restriction.**
* `AlgebraicGeometry.Space.etaleModulePullback_comp_restrictToChartSchemeFunctor` and
  `AlgebraicGeometry.Space.restrictSubmoduleToChart_etaleSubmoduleRestrict_heq`: the étale pullback
  followed by the chart restriction along `V` *is* the chart restriction along the composite
  chart, as functors; hence the chart restriction of `f^*N` along `V` is the chart restriction of
  `N` along the composite chart (a heterogeneous equality, the ambient modules being equal but
  not syntactically).

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' w'' v v' v'' v₁ v₂ v₃ u₁ u₂ u₃ m u

namespace Stacks.SheafOfModules

section MapSubmodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
    {R' : Sheaf J' RingCat.{w'}}

/-- **The image of a submodule under a functor of sheaves of modules.** For a functor
`Φ : Mod(R) ⥤ Mod(R')` and a submodule `N ⊆ M`, the submodule of `Φ M` of sections lying locally
in the range of `Φ` applied to the inclusion of `N`. -/
def mapSubmodule (Φ : _root_.SheafOfModules.{v} R ⥤ _root_.SheafOfModules.{v'} R')
    {M : _root_.SheafOfModules.{v} R} (N : M.Submodule) : (Φ.obj M).Submodule :=
  localClosure _ (presheafRangeSubmodule (Φ.map N.ι).val)

variable (Φ : _root_.SheafOfModules.{v} R ⥤ _root_.SheafOfModules.{v'} R')
    {M : _root_.SheafOfModules.{v} R}

/-- `Φ` applied to the inclusion of `N` lands in the image of `N`. -/
theorem app_mem_mapSubmodule (N : M.Submodule) (X : C'ᵒᵖ)
    (m : (Φ.obj N.toSheafOfModules).val.obj X) :
    (Φ.map N.ι).val.app X m ∈ (mapSubmodule Φ N).obj X :=
  app_mem_localClosure_presheafRangeSubmodule _ X m

/-- **The local closure of a range only grows along a factorisation.** If `a = c ≫ b`, a section
lying locally in the range of `a` lies locally in the range of `b`. -/
theorem localClosure_presheafRangeSubmodule_le_of_fac {P A B : _root_.SheafOfModules.{v'} R'}
    {a : A ⟶ P} {b : B ⟶ P} (c : A ⟶ B) (h : c ≫ b = a) :
    localClosure P (presheafRangeSubmodule a.val) ≤
      localClosure P (presheafRangeSubmodule b.val) := by
  intro Y x hx
  refine GrothendieckTopology.superset_covering _ (fun Z g hg => ?_) hx
  obtain ⟨m, hm⟩ := hg
  refine ⟨c.val.app _ m, ?_⟩
  rw [← hm, ← h]
  rfl

/-- The image of a submodule under `Φ` is monotone in the submodule. -/
theorem mapSubmodule_mono {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    mapSubmodule Φ N₁ ≤ mapSubmodule Φ N₂ :=
  localClosure_presheafRangeSubmodule_le_of_fac (Φ.map (sheafFactorThruSubmodule N₁.ι N₂
    (fun W y => h W y.2))) (by rw [← Φ.map_comp, sheafFactorThruSubmodule_ι])

variable {C'' : Type u₃} [Category.{v₃} C''] {J'' : GrothendieckTopology C''}
    {R'' : Sheaf J'' RingCat.{w''}}

/-- **The image of a submodule under a composite functor.** If `Φ` carries `N` isomorphically
onto a submodule `N'` of `Φ M` — an isomorphism `e` from `Φ N` to the module of `N'` through which
`Φ` of the inclusion factors — then the image under `Ψ` of `N'` is the image of `N` under
`Φ ⋙ Ψ`. -/
theorem mapSubmodule_eq_mapSubmodule_comp_of_iso (Ψ : _root_.SheafOfModules.{v'} R' ⥤
      _root_.SheafOfModules.{v''} R'') (N : M.Submodule) {N' : (Φ.obj M).Submodule}
    (e : Φ.obj N.toSheafOfModules ≅ N'.toSheafOfModules) (he : e.hom ≫ N'.ι = Φ.map N.ι) :
    mapSubmodule Ψ N' = mapSubmodule (Φ ⋙ Ψ) N := by
  have he' : e.inv ≫ Φ.map N.ι = N'.ι := by rw [← he, Iso.inv_hom_id_assoc]
  refine le_antisymm (localClosure_presheafRangeSubmodule_le_of_fac (Ψ.map e.inv) ?_)
    (localClosure_presheafRangeSubmodule_le_of_fac (Ψ.map e.hom) ?_)
  · rw [Functor.comp_map, ← Ψ.map_comp, he']
  · rw [Functor.comp_map, ← Ψ.map_comp, he]

/-- **Images of a submodule under equal functors agree**, as submodules of the (equal) images of
the module. -/
theorem mapSubmodule_heq_of_eq {Φ Ψ : _root_.SheafOfModules.{v} R ⥤ _root_.SheafOfModules.{v'} R'}
    (h : Φ = Ψ) (N : M.Submodule) : mapSubmodule Φ N ≍ mapSubmodule Ψ N := by
  subst h
  rfl

end MapSubmodule

section PushforwardFunctor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {G : D ⥤ E} [hcont : G.IsContinuous K L]
    {R : CategoryTheory.Sheaf L RingCat.{w}}
    {F : C ⥤ D} {RC : Cᵒᵖ ⥤ RingCat.{w}}

/-- **`Stacks.SheafOfModules.pushforward_ulift_pushforward_id` as an equality of functors**: the
direct image along `G` with identity structure map, followed by raising the universe of the
sections, forgetting to presheaves, the direct image along `F` and any further functor `Q`, is
the same composite along `F ⋙ G` without the first step. -/
theorem pushforward_comp_ulift_comp_pushforward_eq {T : Type*} [Category T]
    (ρ : RC ⟶ (F ⋙ G).op ⋙ R.obj) (Q : PresheafOfModules.{max w'' v} RC ⥤ T) :
    _root_.SheafOfModules.pushforward.{v}
        (𝟙 ((G.sheafPushforwardContinuous RingCat.{w} K L).obj R)) ⋙
      (_root_.SheafOfModules.uliftForPresentationFunctor.{u₂, v₂, w, v, w''} ⋙
        _root_.SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward (F := F) ρ ⋙ Q) =
      _root_.SheafOfModules.uliftForPresentationFunctor.{u₃, v₃, w, v, w''} ⋙
        _root_.SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward (F := F ⋙ G) ρ ⋙ Q :=
  rfl

end PushforwardFunctor

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### Finite type along an étale morphism -/

/-- **An étale pullback of an `𝒪_X`-module of finite type is of finite type.** Along an étale
`f : Y ⟶ X` the étale pullback is isomorphic to the pullback of modules of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, Stacks 03LW), which preserves
finite type (`AlgebraicGeometry.Space.isFiniteTypeOnSite_modulePullback`). -/
theorem isFiniteTypeOnSite_etaleModulePullback (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : SheafOfModules.IsFiniteTypeOnSite M) :
    ((etaleModulePullback B S hS f hf).obj M).IsFiniteTypeOnSite := by
  let e := (modulePullbackIsoEtaleModulePullback B S hS f hf).app M
  -- instance search for `Epi e.hom` gets stuck on a universe constraint
  exact @isFiniteTypeOnSite_of_epi B S hS Y.1 Y.2 _ _ e.hom
    ⟨fun g h w => by rw [← e.inv_hom_id_assoc g, w, e.inv_hom_id_assoc]⟩
    (isFiniteTypeOnSite_modulePullback B S hS f M hM)

/-! ### The étale pullback of a submodule -/

/-- **`f^*` of the inclusion of `N` is the inclusion of `f^*N` after the comparison**
`AlgebraicGeometry.Space.etaleSubmoduleRestrictIso`: both are the identity on sections. -/
theorem etaleSubmoduleRestrictIso_inv_comp_ι (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    {M : Modules.{u, u} B S hS X.1 X.2} (N : M.Submodule) :
    (etaleSubmoduleRestrictIso B S hS f hf N).inv ≫ (etaleSubmoduleRestrict B S hS f hf N).ι =
      (etaleModulePullback B S hS f hf).map N.ι := by
  ext V x
  rfl

/-! ### Restriction to charts along composed charts -/

/-- **`AlgebraicGeometry.Space.restrictSubmoduleToChart` is the image of the submodule under the
chart restriction functor**, `Stacks.SheafOfModules.mapSubmodule`; this holds by definition. -/
theorem restrictSubmoduleToChart_eq_mapSubmodule (M : Modules.{u, u} B S hS X.1 X.2)
    (N : M.Submodule) (V : SmallEtale B S hS X.1) :
    restrictSubmoduleToChart M N V =
      Stacks.SheafOfModules.mapSubmodule (restrictToChartSchemeFunctor B S hS X.1 X.2 V) N :=
  rfl

/-- The étale pullback followed by the chart restriction along `V` is the chart restriction
along the composite chart. -/
private theorem etaleModulePullback_comp_restrictToChartSchemeFunctor_aux (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (V : SmallEtale B S hS Y.1) :
    etaleModulePullback.{u, m} B S hS f hf ⋙
        restrictToChartSchemeFunctor.{u, m} B S hS Y.1 Y.2 V =
      restrictToChartSchemeFunctor.{u, m} B S hS X.1 X.2
        ((smallEtalePostcomp B S hS f hf).obj V) := by
  let : HasSheafify (Opens.grothendieckTopology (chartScheme V)) AddCommGrpCat.{max u m} :=
    hasSheafifyEssentiallySmallSite _ _
  let : (Opens.grothendieckTopology (chartScheme V)).WEqualsLocallyBijective
      AddCommGrpCat.{max u m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  let Q : PresheafOfModules.{max u m} (chartScheme V).ringCatSheaf.obj ⥤
      _root_.SheafOfModules.{max u m} (chartScheme V).ringCatSheaf :=
    PresheafOfModules.sheafification (𝟙 (chartScheme V).ringCatSheaf.obj)
  exact Stacks.SheafOfModules.pushforward_comp_ulift_comp_pushforward_eq
    (F := openChartFunctor B S hS Y.1 V)
    (G := smallEtalePostcomp B S hS f hf)
    (K := (smallEtaleRingedSite B S hS Y.1 Y.2).J)
    (L := (smallEtaleRingedSite B S hS X.1 X.2).J)
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (hcont := smallEtaleRingedSite_isContinuous_smallEtalePostcomp B S hS f hf)
    (chartSchemeRestrictionRingHom B S hS X.1 ((smallEtalePostcomp B S hS f hf).obj V)) Q

/-- **The chart restriction of an étale pullback along a chart of the source is the chart
restriction of the module along the composite chart.** For an étale `f : Y ⟶ X`, a module `M`
on `X` and an étale chart `V` of `Y`, the two modules on the Zariski site of the chart scheme
are equal, not merely isomorphic. -/
theorem restrictToChartScheme_etaleModulePullback (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, m} B S hS X.1 X.2) (V : SmallEtale B S hS Y.1) :
    restrictToChartScheme B S hS Y.1 Y.2 ((etaleModulePullback B S hS f hf).obj M) V
      = restrictToChartScheme B S hS X.1 X.2 M ((smallEtalePostcomp B S hS f hf).obj V) :=
  congrArg (·.obj M) (etaleModulePullback_comp_restrictToChartSchemeFunctor_aux B S hS f hf V)

/-- **The chart restriction of the étale pullback of a submodule is the image of the submodule
under the composite of the étale pullback and the chart restriction.** -/
theorem restrictSubmoduleToChart_etaleSubmoduleRestrict (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) (N : M.Submodule) (V : SmallEtale B S hS Y.1) :
    restrictSubmoduleToChart ((etaleModulePullback B S hS f hf).obj M)
        (etaleSubmoduleRestrict B S hS f hf N) V =
      Stacks.SheafOfModules.mapSubmodule
        (etaleModulePullback B S hS f hf ⋙ restrictToChartSchemeFunctor B S hS Y.1 Y.2 V) N :=
  Stacks.SheafOfModules.mapSubmodule_eq_mapSubmodule_comp_of_iso
    (etaleModulePullback B S hS f hf) (restrictToChartSchemeFunctor B S hS Y.1 Y.2 V) N
    (etaleSubmoduleRestrictIso B S hS f hf N).symm
    (etaleSubmoduleRestrictIso_inv_comp_ι B S hS f hf N)

/-- **The étale pullback followed by the chart restriction along a chart of the source is the
chart restriction along the composite chart**, as functors of the module: the functor-level form
of `AlgebraicGeometry.Space.restrictToChartScheme_etaleModulePullback`. -/
theorem etaleModulePullback_comp_restrictToChartSchemeFunctor (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (V : SmallEtale B S hS Y.1) :
    etaleModulePullback.{u, m} B S hS f hf ⋙
        restrictToChartSchemeFunctor.{u, m} B S hS Y.1 Y.2 V =
      restrictToChartSchemeFunctor.{u, m} B S hS X.1 X.2
        ((smallEtalePostcomp B S hS f hf).obj V) :=
  etaleModulePullback_comp_restrictToChartSchemeFunctor_aux B S hS f hf V

/-- **The chart restriction of the étale pullback of a submodule along a chart `V` of `Y` is the
chart restriction of the submodule along the composite chart of `X`.** The two submodules live
in the chart restrictions of `f^*M` along `V` and of `M` along the composite chart, which are
equal (`AlgebraicGeometry.Space.restrictToChartScheme_etaleModulePullback`) but not
syntactically, so the identification is a heterogeneous equality. -/
theorem restrictSubmoduleToChart_etaleSubmoduleRestrict_heq (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) (M : Modules.{u, u} B S hS X.1 X.2) (N : M.Submodule)
    (V : SmallEtale B S hS Y.1) :
    restrictSubmoduleToChart ((etaleModulePullback B S hS f hf).obj M)
        (etaleSubmoduleRestrict B S hS f hf N) V ≍
      restrictSubmoduleToChart M N ((smallEtalePostcomp B S hS f hf).obj V) :=
  (heq_of_eq (restrictSubmoduleToChart_etaleSubmoduleRestrict B S hS f hf M N V)).trans
    (Stacks.SheafOfModules.mapSubmodule_heq_of_eq
      (etaleModulePullback_comp_restrictToChartSchemeFunctor B S hS f hf V) N)

end AlgebraicGeometry.Space

end
