module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Transpose
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBijectiveOfModel

/-!
# The canonical comparison of chart restrictions along a diagram of charts

Let `a : X ⟶ Z` be a morphism of algebraic spaces, `G` an `𝒪_Z`-module, `V` an étale scheme chart
of `Z` and `W` an étale scheme chart of `X` lying over it through a morphism `g` of chart schemes.
`AlgebraicGeometry.Space.chartRestrictionPushforwardHom` is the canonical morphism
`G|_V ⟶ g_*((a^*G)|_W)` whose components are the chart sections of the unit of
[Stacks, Tag 03D7]. This file defines its adjunct along the Zariski pullback–pushforward
adjunction,

`g^*(G|_V) ⟶ (a^*G)|_W`,

the canonical comparison of chart restrictions, and proves that it is an isomorphism when `G` is
quasi-coherent.

## Main definitions

* `AlgebraicGeometry.Space.chartOpenDiagramOfLE`: the diagram of étale charts cut out by a pair
  of Zariski opens `O' ⊆ g⁻¹ O`.
* `AlgebraicGeometry.Space.chartRestrictionPullbackComparison`: the comparison
  `g^*(G|_V) ⟶ (a^*G)|_W`.

## Main results

* `AlgebraicGeometry.Space.bijective_of_extendScalars_iso_of_model`: a morphism out of a base
  change is bijective when a model of it over isomorphic rings is.
* `AlgebraicGeometry.Space.chartRestrictionPullbackComparison_pullbackSection`: the comparison
  carries the pullback of a section to its chart section.
* `AlgebraicGeometry.Space.bijective_chartRestrictionPullbackComparison_app`: for `G`
  quasi-coherent the comparison is bijective on sections over affine opens `O' ⊆ g⁻¹ O`.
* `AlgebraicGeometry.Space.isIso_chartRestrictionPullbackComparison`: for `G` quasi-coherent the
  comparison is an isomorphism.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped ChangeOfRings TensorProduct

universe u

namespace AlgebraicGeometry.Space

/-! ### Bijectivity of a map out of a base change, read through a model -/

section Model

universe v

variable {A A' : Type v} [CommRing A] [CommRing A'] (ψ : A →+* A')
    {M : ModuleCat.{v} A} {Q P : ModuleCat.{v} A'}
    (α : (ModuleCat.extendScalars ψ).obj M ≅ Q) (κ : Q ⟶ P)
    {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R']
    {Mc Pc : Type*} [AddCommGroup Mc] [Module R Mc] [AddCommGroup Pc] [Module R' Pc]
    (eR : R ≃+* A) (eR' : R' ≃+* A')
    (hcomp : ∀ r : R, ψ (eR r) = eR' (algebraMap R R' r))
    (eM : Mc ≃+ M) (heM : ∀ (r : R) (x : Mc), eM (r • x) = eR r • eM x)
    (eP : P ≃+ Pc) (heP : ∀ (a : R') (p : P), eP (eR' a • p) = a • eP p)

include hcomp heM heP in
/-- A morphism out of a base change is bijective when a model of it over isomorphic rings is:
let `α : A' ⊗_A M ≅ Q` be an isomorphism of `A'`-modules and `κ : Q ⟶ P` a morphism. If, over
rings isomorphic to `A` and `A'`, there is a bijective `c : R' ⊗_R Mc ⟶ Pc` agreeing with
`b ⊗ m ↦ b • κ(α(1 ⊗ m))` through the identifications, then `κ` is bijective. -/
theorem bijective_of_extendScalars_iso_of_model
    (c : R' ⊗[R] Mc → Pc) (hcadd : ∀ z w, c (z + w) = c z + c w)
    (hc : ∀ (a : R') (x : Mc),
      c (a ⊗ₜ[R] x) = a • eP (κ.hom (α.hom.hom ((1 : A') ⊗ₜ[A,ψ] eM x))))
    (hcb : Function.Bijective c) : Function.Bijective κ.hom := by
  have key := Stacks.ModuleCat.bijective_extendScalars_homEquiv_symm_of_model ψ
    ((ModuleCat.extendRestrictScalarsAdj ψ).homEquiv _ _ (α.hom ≫ κ)) eR eR' hcomp eM heM eP heP
    c hcadd (fun a x => (hc a x).trans rfl) hcb
  rw [Equiv.symm_apply_apply] at key
  have h : (κ.hom : Q → P) = (α.hom ≫ κ).hom ∘ α.inv.hom := by
    funext q
    rw [Function.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
    exact congrArg κ.hom (α.inv_hom_id_apply q).symm
  rw [h]
  exact key.comp (ConcreteCategory.bijective_of_isIso α.inv)

end Model

section Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Z : AlgebraicSpaces B S hS} (a : X ⟶ Z)
    (V : SmallEtale B S hS Z.1) (W : SmallEtale B S hS X.1)
    (g : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Z.1).obj V)
    (hg : yoneda.map g ≫ V.obj.hom = W.obj.hom ≫ a.hom)

/-- The restriction of `g` to a Zariski open `O'` of the chart of `X` lying in the preimage of a
Zariski open `O` of the chart of `Z`, as a morphism of schemes over the base. -/
def chartOpenDiagramHomOfLE (O : (etaleChartScheme B S hS V).Opens)
    (O' : (etaleChartScheme B S hS W).Opens)
    (hle : O' ≤ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O) :
    chartOpenOver B S hS W O' ⟶ chartOpenOver B S hS V O :=
  Over.homMk (ObjectProperty.homMk
    (((BigFppfOver.toScheme B S hS).map g).resLE O O' hle)) (by
      apply ObjectProperty.hom_ext
      change ((BigFppfOver.toScheme B S hS).map g).resLE O O' hle ≫ O.ι ≫ _ = _
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
      exact congrArg (fun k ↦ O'.ι ≫ k) (congrArg (fun m ↦ m.hom) (Over.w g)))

/-- The restriction of `g` to `O' ⊆ g⁻¹ O` is compatible with the inclusions of the two opens into
their charts. -/
theorem chartOpenDiagramHomOfLE_comp_ι (O : (etaleChartScheme B S hS V).Opens)
    (O' : (etaleChartScheme B S hS W).Opens)
    (hle : O' ≤ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O) :
    chartOpenOverι B S hS W O' ≫ g =
      chartOpenDiagramHomOfLE B S hS V W g O O' hle ≫ chartOpenOverι B S hS V O := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact (Scheme.Hom.resLE_comp_ι ((BigFppfOver.toScheme B S hS).map g) hle).symm

/-- The diagram of étale scheme charts over `a` cut out by a pair of Zariski opens `O' ⊆ g⁻¹ O`:
the chart `O'` cuts out of `W` above, the chart `O` cuts out of `V` below, and the restriction of
`g` between them. -/
def chartOpenDiagramOfLE (O : (etaleChartScheme B S hS V).Opens)
    (O' : (etaleChartScheme B S hS W).Opens)
    (hle : O' ≤ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O) :
    ChartDiagram B S hS X.1 Z.1 a.hom where
  U := (chartOpens B S hS W).obj O'
  V := (chartOpens B S hS V).obj O
  g := chartOpenDiagramHomOfLE B S hS V W g O O' hle
  comm := by
    change (yoneda.map (chartOpenOverι B S hS W O') ≫ W.obj.hom) ≫ a.hom =
      yoneda.map (chartOpenDiagramHomOfLE B S hS V W g O O' hle) ≫
        yoneda.map (chartOpenOverι B S hS V O) ≫ V.obj.hom
    rw [Category.assoc, ← hg, ← Category.assoc, ← Functor.map_comp, ← Category.assoc,
      ← Functor.map_comp, chartOpenDiagramHomOfLE_comp_ι]

variable (G : Modules.{u, u} B S hS Z.1 Z.2)

/-- The canonical comparison of chart restrictions `g^*(G|_V) ⟶ (a^*G)|_W`: the adjunct of
`AlgebraicGeometry.Space.chartRestrictionPushforwardHom` along the Zariski pullback–pushforward
adjunction of `g`. -/
def chartRestrictionPullbackComparison :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
        (chartRestrictionSheaf B S hS Z G V) ⟶
      chartRestrictionSheaf B S hS X ((modulePullback B S hS a).obj G) W :=
  ((Scheme.Modules.pullbackPushforwardAdjunction ((BigFppfOver.toScheme B S hS).map g)).homEquiv
    _ _).symm (chartRestrictionPushforwardHom B S hS a V W g hg G)

/-- For Zariski opens `O' ⊆ g⁻¹ O` and a section `x` of `G|_V` over `O`, that is a section of
`G` over the chart `O` cuts out, the comparison sends the pullback of `x` to the chart section of
`x` along the diagram of charts `O' ⟶ O`. -/
theorem chartRestrictionPullbackComparison_pullbackSection
    (O : (etaleChartScheme B S hS V).Opens) (O' : (etaleChartScheme B S hS W).Opens)
    (hle : O' ≤ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O)
    (x : (chartRestrictionSheaf B S hS Z G V).val.obj (op O)) :
    ((chartRestrictionPullbackComparison B S hS a V W g hg G).val.app (op O')
        (Scheme.Modules.pullbackSection _ _ O O' hle x)).down =
      modulePullbackChartSection B S hS a G (chartOpenDiagramOfLE B S hS a V W g hg O O' hle)
        x.down := by
  rw [chartRestrictionPullbackComparison, Scheme.Modules.pullbackSection_homEquiv,
    Equiv.apply_symm_apply]
  change ((modulePullback B S hS a).obj G).val.map
      ((chartOpens B S hS W).map (homOfLE hle)).op
      ((chartRestrictionPushforwardHom B S hS a V W g hg G).val.app (op O) x).down = _
  rw [chartRestrictionPushforwardHom_val_app]
  have h := modulePullbackChartSection_naturality B S hS a G
    (chartOpenDiagram B S hS a V W g hg O) (chartOpenDiagramOfLE B S hS a V W g hg O O' hle)
    ((chartOpens B S hS W).map (homOfLE hle)) (𝟙 _) (by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      change (etaleChartScheme B S hS W).homOfLE hle ≫
          ((BigFppfOver.toScheme B S hS).map g).resLE O _ le_rfl =
        ((BigFppfOver.toScheme B S hS).map g).resLE O O' hle ≫ 𝟙 _
      rw [Scheme.Hom.map_resLE, Category.comp_id]) x.down
  refine h.symm.trans ?_
  congr 1
  exact congrArg (fun k => k x.down) (congrArg ConcreteCategory.hom (G.val.map_id _))

/-- Pulling back regular functions along the restriction of `f` to `V ⊆ f⁻¹ U`, read on the two
open subschemes, is pulling back along `f` from `U` to `V`. -/
theorem topIso_hom_comp_appLE {A C : Scheme.{u}} (f : A ⟶ C) (U : C.Opens) (V : A.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) :
    U.topIso.hom ≫ f.appLE U V hVU = (f.resLE U V hVU).appTop ≫ V.topIso.hom := by
  rw [← cancel_epi U.topIso.inv, ← Category.assoc, Iso.inv_hom_id, Category.id_comp,
    ← cancel_mono V.topIso.inv, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hι : ∀ {Y : Scheme.{u}} (T : Y.Opens),
      Scheme.Hom.appLE T.ι T ⊤ (Scheme.Opens.ι_preimage_self T).ge = T.topIso.inv := fun T =>
    (Scheme.Opens.ι_appLE T T ⊤ _).trans (Scheme.Opens.topIso_inv T).symm
  have hB : Scheme.Hom.appLE (f.resLE U V hVU) ⊤ ⊤
        (Scheme.Hom.preimage_top (f.resLE U V hVU)).ge = (f.resLE U V hVU).appTop := by
    rw [show Scheme.Hom.appLE (f.resLE U V hVU) ⊤ ⊤
          (Scheme.Hom.preimage_top (f.resLE U V hVU)).ge =
        (f.resLE U V hVU).appTop ≫ V.toScheme.presheaf.map (𝟙 (op ⊤)) from rfl,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← hι U, ← hB, ← hι V, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
  congr 1
  exact (Scheme.Hom.resLE_comp_ι f hVU).symm

/-- The comparison on sections over a Zariski open `O'`, read as a morphism of modules over the
regular functions on `O'`. -/
def chartRestrictionPullbackComparisonApp (O' : (etaleChartScheme B S hS W).Opens) :
    ModuleCat.of Γ(etaleChartScheme B S hS W, O')
        Γ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj
          (chartRestrictionSheaf B S hS Z G V), O') ⟶
      ModuleCat.of Γ(etaleChartScheme B S hS W, O')
        Γ(chartRestrictionSheaf B S hS X ((modulePullback B S hS a).obj G) W, O') :=
  ModuleCat.ofHom ((chartRestrictionPullbackComparison B S hS a V W g hg G).val.app (op O')).hom

/-- Over affine opens `O' ⊆ g⁻¹ O`, the comparison is bijective on sections, for `G`
quasi-coherent. -/
theorem bijective_chartRestrictionPullbackComparison_app (hG : G.IsQuasicoherentOnSite)
    (O : (etaleChartScheme B S hS V).Opens) (hO : IsAffineOpen O)
    (O' : (etaleChartScheme B S hS W).Opens) (hO' : IsAffineOpen O')
    (hle : O' ≤ (BigFppfOver.toScheme B S hS).map g ⁻¹ᵁ O) :
    Function.Bijective
      ((chartRestrictionPullbackComparison B S hS a V W g hg G).val.app (op O')).hom := by
  have : (chartRestrictionSheaf B S hS Z G V).IsQuasicoherent :=
    isQuasicoherent_chartRestrictionSheaf B S hS Z G hG V
  let α := affinePullbackSectionsBaseChangeIso ((BigFppfOver.toScheme B S hS).map g)
    (chartRestrictionSheaf B S hS Z G V) hO hO' hle
  let ψ := ((BigFppfOver.toScheme B S hS).map g).appLE O O' hle
  let alg := chartDiagramAlgebra B S hS a (chartOpenDiagramOfLE B S hS a V W g hg O O' hle)
  let eR : chartRing B S hS Z.1 Z.2 (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).V ≃+*
      Γ(etaleChartScheme B S hS V, O) := O.topIso.commRingCatIsoToRingEquiv
  let eR' : chartRing B S hS X.1 X.2 (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).U ≃+*
      Γ(etaleChartScheme B S hS W, O') := O'.topIso.commRingCatIsoToRingEquiv
  exact bijective_of_extendScalars_iso_of_model ψ.hom α
    (chartRestrictionPullbackComparisonApp B S hS a V W g hg G O')
    (R := chartRing B S hS Z.1 Z.2 (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).V)
    (R' := chartRing B S hS X.1 X.2 (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).U)
    (Mc := G.val.obj (op (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).V))
    (Pc := ((modulePullback B S hS a).obj G).val.obj
      (op (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).U)) eR eR'
    (fun r => congrArg (fun k => k.hom r)
      (topIso_hom_comp_appLE ((BigFppfOver.toScheme B S hS).map g) O O' hle))
    AddEquiv.ulift.symm (fun r x => by
      have h1 : eR r • (show Γ(chartRestrictionSheaf B S hS Z G V, O) from
            AddEquiv.ulift.symm x) =
          (show Γ(chartRestrictionSheaf B S hS Z G V, O) from
            AddEquiv.ulift.symm ((show chartRing B S hS Z.1 Z.2
              (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).V from
                O.topIso.inv.hom (eR r)) • x)) := rfl
      refine Eq.trans ?_ h1.symm
      refine congrArg AddEquiv.ulift.symm (congrArg (· • x) ?_)
      exact (CategoryTheory.Iso.hom_inv_id_apply O.topIso r).symm)
    AddEquiv.ulift (fun r p => by
      have h1 : eR' r • p =
          (show Γ(chartRestrictionSheaf B S hS X ((modulePullback B S hS a).obj G) W, O') from
            AddEquiv.ulift.symm ((show chartRing B S hS X.1 X.2
              (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).U from
                O'.topIso.inv.hom (eR' r)) •
              (show ((modulePullback B S hS a).obj G).val.obj
                  (op (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).U) from
                AddEquiv.ulift p))) := rfl
      refine (congrArg AddEquiv.ulift h1).trans ?_
      refine (AddEquiv.apply_symm_apply _ _).trans (congrArg (· •
        (show ((modulePullback B S hS a).obj G).val.obj
            (op (chartOpenDiagramOfLE B S hS a V W g hg O O' hle).U) from
          AddEquiv.ulift p)) ?_)
      exact CategoryTheory.Iso.hom_inv_id_apply O'.topIso r)
    (modulePullbackChartBaseChange B S hS a G (chartOpenDiagramOfLE B S hS a V W g hg O O' hle))
    (map_add _) (fun r x => by
      refine (modulePullbackChartBaseChange_tmul B S hS a G _ r x).trans (congrArg (r • ·) ?_)
      rw [affinePullbackSectionsBaseChangeIso_one_tmul]
      exact (chartRestrictionPullbackComparison_pullbackSection B S hS a V W g hg G O O' hle
        (AddEquiv.ulift.symm x)).symm)
    (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS a G hG
      (chartOpenDiagramOfLE B S hS a V W g hg O O' hle) hO' hO)

/-- For `G` quasi-coherent the canonical comparison `g^*(G|_V) ⟶ (a^*G)|_W` is an
isomorphism. -/
theorem isIso_chartRestrictionPullbackComparison (hG : G.IsQuasicoherentOnSite) :
    IsIso (chartRestrictionPullbackComparison B S hS a V W g hg G) := by
  let φ := (BigFppfOver.toScheme B S hS).map g
  let I := {p : (etaleChartScheme B S hS V).Opens × (etaleChartScheme B S hS W).Opens //
    IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ p.2 ≤ φ ⁻¹ᵁ p.1}
  let Bf : I → (etaleChartScheme B S hS W).Opens := fun p => p.1.2
  have hbasis : Opens.IsBasis (Set.range Bf) := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨_, ⟨O, hO, rfl⟩, hxO, -⟩ :=
      (etaleChartScheme B S hS V).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (φ.base x)) isOpen_univ
    obtain ⟨_, ⟨O', hO', rfl⟩, hxO', hO'le⟩ :=
      (etaleChartScheme B S hS W).isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((U ⊓ φ ⁻¹ᵁ O : (etaleChartScheme B S hS W).Opens) : Set _) from ⟨hx, hxO⟩)
        (U ⊓ φ ⁻¹ᵁ O).2
    have hle : O' ≤ U ⊓ φ ⁻¹ᵁ O := hO'le
    exact ⟨O', ⟨⟨(O, O'), hO, hO', hle.trans inf_le_right⟩, rfl⟩, hxO', hle.trans inf_le_left⟩
  let c := chartRestrictionPullbackComparison B S hS a V W g hg G
  let M' : TopCat.Sheaf AddCommGrpCat (etaleChartScheme B S hS W) :=
    ⟨((Scheme.Modules.pullback φ).obj (chartRestrictionSheaf B S hS Z G V)).presheaf,
      ((Scheme.Modules.pullback φ).obj (chartRestrictionSheaf B S hS Z G V)).isSheaf⟩
  let N' : TopCat.Sheaf AddCommGrpCat (etaleChartScheme B S hS W) :=
    ⟨(chartRestrictionSheaf B S hS X ((modulePullback B S hS a).obj G) W).presheaf,
      (chartRestrictionSheaf B S hS X ((modulePullback B S hS a).obj G) W).isSheaf⟩
  let c' : M' ⟶ N' := ⟨c.mapPresheaf⟩
  have hc' : IsIso c' := TopCat.Sheaf.isIso_iff_isIso_basis hbasis (fun p =>
    (ConcreteCategory.isIso_iff_bijective _).2
      (bijective_chartRestrictionPullbackComparison_app B S hS a V W g hg G hG p.1.1 p.2.1 p.1.2
        p.2.2.1 p.2.2.2))
  have : IsIso ((Scheme.Modules.toPresheaf (etaleChartScheme B S hS W)).map c) :=
    (TopCat.Sheaf.forget AddCommGrpCat (etaleChartScheme B S hS W)).map_isIso c'
  exact isIso_of_reflects_iso c (Scheme.Modules.toPresheaf (etaleChartScheme B S hS W))

end Comparison

end AlgebraicGeometry.Space

end
