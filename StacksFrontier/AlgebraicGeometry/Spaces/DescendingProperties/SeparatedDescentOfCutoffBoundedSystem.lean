module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.CutoffBoundedSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentBounded

/-!
# Separatedness descends to a stage of a system bounded by the cutoff

Stacks 086X says: if `X = lim X_i` is a directed limit over a quasi-separated algebraic space `Y`
of quasi-compact quasi-separated algebraic spaces with affine transition morphisms, and `X ⟶ Y` is
separated, then `X_i ⟶ Y` is separated for `i` large. The library proves it as
`AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_system_app` for an index set smaller
than the cofinality of the site's cutoff. This file proves it for a descent situation whose
system is bounded by the cutoff (`AlgebraicGeometry.Space.IsCutoffBoundedSystem`), with no
condition on the cofinality, and in particular for a system with monomorphic transition morphisms
and fewer stages than the cutoff.

The proof is the library's
(`StacksFrontier/AlgebraicGeometry/Spaces/DescendingProperties/SeparatedDescent.lean`). The bound by
the cofinality entered it only in the proof of Stacks 084T over an affine base, in two places:

* the limit of the affine charts of the stages:
  `AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBaseChangeSizeBounded` in place of
  `AlgebraicGeometry.Space.AffineChartSystem.limitBridge`;
* the preservation by the underlying scheme functor of the limits of the products of those
  charts with one fixed chart, in Stacks 081B and Stacks 01ZP: the products are bounded by one
  cardinal below the cutoff, and
  `AlgebraicGeometry.BigFppfOver.preservesLimit_toScheme_of_size_le` replaces
  `AlgebraicGeometry.BigFppfOver.preservesLimit_toScheme`.

The two reductions of the library's proof, to an affine base by viewing the situation over the
terminal scheme and to a base change along a chart of `Y`, keep the system bounded by the cutoff:
`AlgebraicGeometry.Space.baseChangeSizeBounded_relocalize` and
`AlgebraicGeometry.Space.baseChangeSizeBounded_baseChangeOverSystem`. Every other step is the
library's, used as it stands.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isCutoffBoundedSystem`:
  Stacks 084T for a system bounded by the cutoff.
* `DescentSituation.exists_isSeparated_system_app_of_isCutoffBoundedSystem`:
  Stacks 086X for a system bounded by the cutoff.
* `DescentSituation.exists_isSeparated_system_app_of_mono` and
  `DescentSituation.exists_isSeparated_system_app_of_isClosedImmersion`:
  Stacks 086X for a system with fewer stages than the cutoff and monomorphic, respectively
  closed immersion, transition morphisms.

Nothing here is registered: Stacks 084T and Stacks 086X carry their tags on the library's forms.

## References

* [Stacks Project, Tag 084T](https://stacks.math.columbia.edu/tag/084T)
* [Stacks Project, Tag 086X](https://stacks.math.columbia.edu/tag/086X)
* [Stacks Project, Tag 081B](https://stacks.math.columbia.edu/tag/081B)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Descending a closed immersion into a product of charts -/

section ProductDiagrams

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))

include hSaff hVaff in
/-- **Stacks 081B** for the products of a cofiltered limit of affine charts with the charts of
the stages, for fewer charts than the cutoff of uniformly bounded size. A closed immersion into
`U ×_S U`, where `U` is the limit of the charts, whose composite with the first projection is
locally of finite type, is already a closed immersion into `U ×_S U_k` for all sufficiently late
stages `k`.

This is `AlgebraicGeometry.Space.exists_isClosedImmersion_comp_prodMap_π` with the bound by the
cofinality of the cutoff traded for a uniform bound on the sizes of the charts. -/
theorem exists_isClosedImmersion_comp_prodMap_π_of_size_le
    (hK : #K < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hVsize : ∀ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size ≤ μ)
    {c : Cone V} (hc : IsLimit c)
    (hcaff : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    {R : Scheme.{u}} (g : R ⟶ (BigFppfOver.toScheme B S hS).obj (c.pt ⨯ c.pt))
    (hg : _root_.AlgebraicGeometry.IsClosedImmersion g) (k₀ : K)
    (hft : LocallyOfFiniteType (g ≫ (BigFppfOver.toScheme B S hS).map prod.fst)) :
    ∃ k₁ : K, ∀ (k : K) (_ : k ⟶ k₁),
      _root_.AlgebraicGeometry.IsClosedImmersion
        (g ≫ (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k))) := by
  have hconn : IsConnected K := IsCofiltered.isConnected K
  have hpres := prod_preservesConnectedLimits (J := K) c.pt
  have hprodlim : IsLimit ((prod.functor.obj c.pt).mapCone c) := isLimitOfPreserves _ hc
  have hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.obj c.pt).obj j)) := fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ hcaff (hVaff j)
  have hsize : ∀ j, ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.obj c.pt).obj j)).size ≤
        max ((BigFppfOver.toScheme B S hS).obj c.pt).size μ := fun j =>
    (size_toScheme_obj_prod_le B S hS c.pt (V.obj j)).trans (max_le_max le_rfl (hVsize j))
  have := BigFppfOver.preservesLimit_toScheme_of_size_le (V ⋙ prod.functor.obj c.pt) hpaff hK
    (max_lt c.pt.left.property hμ) hsize
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.obj c.pt).mapCone c)) := isLimitOfPreserves _ hprodlim
  have hEaff : ∀ j, IsAffine
      (((V ⋙ prod.functor.obj c.pt) ⋙ BigFppfOver.toScheme B S hS).obj j) := hpaff
  have hπ : ∀ k : K, ((BigFppfOver.toScheme B S hS).mapCone
        ((prod.functor.obj c.pt).mapCone c)).π.app k
      = (BigFppfOver.toScheme B S hS).map (prod.map (𝟙 c.pt) (c.π.app k)) := fun k => rfl
  have hgft : LocallyOfFiniteType (g ≫
      ((BigFppfOver.toScheme B S hS).mapCone ((prod.functor.obj c.pt).mapCone c)).π.app k₀) := by
    have hcomp2 : LocallyOfFiniteType ((g ≫ (BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 c.pt) (c.π.app k₀))) ≫
        (BigFppfOver.toScheme B S hS).map prod.fst) := by
      rw [Category.assoc, ← Functor.map_comp,
        show prod.map (𝟙 c.pt) (c.π.app k₀) ≫ (prod.fst : c.pt ⨯ V.obj k₀ ⟶ c.pt)
          = (prod.fst : c.pt ⨯ c.pt ⟶ c.pt) by simp]
      exact hft
    rw [hπ k₀]
    exact @locallyOfFiniteType_of_comp _ _ _ _
      ((BigFppfOver.toScheme B S hS).map prod.fst) hcomp2
  obtain ⟨k₁, hk₁⟩ := EventualLimit.exists_isClosedImmersion_comp_π_app_of_isAffine
    ((V ⋙ prod.functor.obj c.pt) ⋙ BigFppfOver.toScheme B S hS) _ he g hg k₀ hgft
  exact ⟨k₁, fun k hk => hk₁ k hk⟩

include hSaff hVaff in
/-- **Stacks 01ZP** for the products of the charts of the stages with the chart of one stage,
for fewer charts than the cutoff of uniformly bounded size. A morphism to `U_k ×_S U_k` whose
source is quasi-compact and quasi-separated and which is locally of finite type becomes a closed
immersion after base change to `U_j ×_S U_k` for some `j`, as soon as it is one after base
change to `U ×_S U_k`, where `U` is the limit of the charts.

This is `AlgebraicGeometry.Space.exists_isClosedImmersion_pullback_snd_prodMap` with the bound
by the cofinality of the cutoff traded for a uniform bound on the sizes of the charts. -/
theorem exists_isClosedImmersion_pullback_snd_prodMap_of_size_le
    (hK : #K < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hVsize : ∀ j, ((BigFppfOver.toScheme B S hS).obj (V.obj j)).size ≤ μ)
    {c : Cone V} (hc : IsLimit c) (k : K) {T : BigFppfOver B S hS} (m : T ⟶ V.obj k ⨯ V.obj k)
    (hmft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map m))
    (hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj T))
    (hlim : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (c.π.app k) (𝟙 (V.obj k)))))) :
    ∃ (i : K) (hi : i ⟶ k), _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map m)
        ((BigFppfOver.toScheme B S hS).map (prod.map (V.map hi) (𝟙 (V.obj k))))) := by
  have hconn : IsConnected K := IsCofiltered.isConnected K
  have hiso : prod.functor.obj (V.obj k) ≅ prod.functor.flip.obj (V.obj k) :=
    NatIso.ofComponents (fun W => prod.braiding (V.obj k) W)
      (fun {W W'} f => braid_natural (𝟙 (V.obj k)) f)
  have h1 := prod_preservesConnectedLimits (J := K) (V.obj k)
  have h2 : PreservesLimitsOfShape K (prod.functor.flip.obj (V.obj k)) :=
    @preservesLimitsOfShape_of_natIso _ _ _ _ _ _ _ _ hiso h1
  have hprodlim : IsLimit ((prod.functor.flip.obj (V.obj k)).mapCone c) :=
    isLimitOfPreserves _ hc
  have hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.flip.obj (V.obj k)).obj j)) := fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hVaff j) (hVaff k)
  have hsize : ∀ j, ((BigFppfOver.toScheme B S hS).obj
      ((V ⋙ prod.functor.flip.obj (V.obj k)).obj j)).size ≤ μ := fun j =>
    (size_toScheme_obj_prod_le B S hS (V.obj j) (V.obj k)).trans (max_le (hVsize j) (hVsize k))
  have := BigFppfOver.preservesLimit_toScheme_of_size_le
    (V ⋙ prod.functor.flip.obj (V.obj k)) hpaff hK hμ hsize
  have he : IsLimit ((BigFppfOver.toScheme B S hS).mapCone
      ((prod.functor.flip.obj (V.obj k)).mapCone c)) := isLimitOfPreserves _ hprodlim
  set E := (V ⋙ prod.functor.flip.obj (V.obj k)) ⋙ BigFppfOver.toScheme B S hS with hE
  have hEaff : ∀ j, IsAffine (E.obj j) := hpaff
  have hEhom : ∀ {i j : K} (g : i ⟶ j), _root_.AlgebraicGeometry.IsAffineHom (E.map g) := by
    intro i j g
    have := hEaff i
    have := hEaff j
    exact isAffineHom_of_isAffine _
  have hk₀ : IsAffine (E.obj k) := hEaff k
  have hkc : CompactSpace (E.obj k) := Scheme.compactSpace_of_isAffine _
  have hkqs : QuasiSeparatedSpace (E.obj k) := inferInstance
  have hX₀c : CompactSpace
      ((Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k))).left := hmqc
  have hX₀qs : QuasiSeparatedSpace
      ((Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k))).left := hmqs
  have hY₀c : CompactSpace (Over.mk (𝟙 (E.obj k))).left := hkc
  have hY₀qs : QuasiSeparatedSpace (Over.mk (𝟙 (E.obj k))).left := hkqs
  have hf₀ft : LocallyOfFiniteType
      (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _) :
        (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) ⟶
          Over.mk (𝟙 (E.obj k))).left := hmft
  have hci : _root_.AlgebraicGeometry.IsClosedImmersion
      ((Over.pullback (((BigFppfOver.toScheme B S hS).mapCone
        ((prod.functor.flip.obj (V.obj k)).mapCone c)).π.app k)).map
        (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _) :
          (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) ⟶
            Over.mk (𝟙 (E.obj k)))).left :=
    (prop_overPullback_map_left_iff_pullback_snd
      (@_root_.AlgebraicGeometry.IsClosedImmersion) _ _).mpr hlim
  obtain ⟨i, hi, hres⟩ := exists_isClosedImmersion_baseChange_of_isLimit E _ he k
    (Over.mk ((BigFppfOver.toScheme B S hS).map m) : Over (E.obj k)) (Over.mk (𝟙 (E.obj k)))
    (Over.homMk ((BigFppfOver.toScheme B S hS).map m) (Category.comp_id _))
  exact ⟨i, hi, (prop_overPullback_map_left_iff_pullback_snd
    (@_root_.AlgebraicGeometry.IsClosedImmersion) _ _).mp hres⟩

end ProductDiagrams

/-! ### The bound passes to the two reductions of the proof -/

/-- **Uniformly bounded base changes pass to a relocalization.** Let `D` be a system of
algebraic spaces over `S` with affine transition morphisms and uniformly bounded base changes,
and let `k : S ⟶ S'` be a morphism of the site. Then the system of relocalizations of the stages
along `k` again has uniformly bounded base changes: a morphism from a representable presheaf into
a relocalization is the relocalization of a morphism from a representable presheaf with the same
underlying scheme, and a represented base change of a relocalized transition morphism is then
the relocalization of a represented base change of the transition morphism itself, with the same
underlying scheme. -/
theorem baseChangeSizeBounded_relocalize {J : Type u} [Category.{u} J] {S' : Scheme.{u}}
    (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hD : ∀ j, IsAlgebraicSpace B S hS (D.obj j))
    (hAffine : ∀ {i j : J} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    (hB : BaseChangeSizeBounded B S hS D) :
    BaseChangeSizeBounded B S' hS' (D ⋙ OverShriek.relocalizePresheafFunctor k) := by
  intro i₀ Z g
  obtain ⟨ψ, hψ, σ, hg⟩ := OverShriek.exists_eq_relocalizeYonedaFactorIso_comp k g
  obtain ⟨μ, hμ, hb⟩ := hB i₀ (Over.mk ψ) σ
  refine ⟨μ, hμ, fun k' W p q hpq => ?_⟩
  have hrep : yoneda.relativelyRepresentable (D.map k'.hom) :=
    (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS
      (hD k'.left) (hD i₀) (hAffine k'.hom)).1
  have hpb₀ := hrep.isPullback σ
  have hsize := hb k' (hrep.pullback σ) (hrep.fst σ) (yoneda.map (hrep.snd σ)) hpb₀
  have hpb₁ := OverShriek.isPullback_map_relocalize_of_factor k hψ hg hpb₀
  let e := yoneda.preimageIso (hpq.isoIsPullback _ _ hpb₁)
  rw [Scheme.size_congr ((BigFppfOver.toScheme B S' hS').mapIso e)]
  exact hsize

/-- **Uniformly bounded base changes pass to a base change over `Y`.** For an inverse system of
presheaves over `Y` with uniformly bounded base changes, the system of its base changes along
`u : T ⟶ Y` again has uniformly bounded base changes: a base change of a transition morphism of
the new system along a test morphism is, by pasting, a base change of the corresponding
transition morphism of the old one. -/
theorem baseChangeSizeBounded_baseChangeOverSystem {I : Type u} [Preorder I]
    {T Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (Dsys : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (t : Dsys ⟶ (Functor.const Iᵒᵖ).obj Y) (u : T ⟶ Y)
    (hB : BaseChangeSizeBounded B S hS Dsys) :
    BaseChangeSizeBounded B S hS (baseChangeOverSystem B S hS Dsys t u) := by
  intro i₀ Z g
  obtain ⟨μ, hμ, hb⟩ := hB i₀ Z (g ≫ pullback.fst (t.app i₀) u)
  refine ⟨μ, hμ, fun k W p q hpq => hb k W (p ≫ pullback.fst (t.app k.left) u) q ?_⟩
  exact hpq.paste_horiz (isPullback_baseChangeOverMap B S hS (t.app k.left) (t.app i₀)
    (Dsys.map k.hom) (by simp) u).flip

/-! ### Separatedness descends to a stage -/

/-- A quasi-compact algebraic space has an affine chart which is surjective and étale, both in
the sense of morphisms of presheaves on the underlying schemes. -/
private theorem exists_affine_chart_presheaf_etale_surjective
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hFqc : IsQuasiCompactSpace B S hS F) :
    ∃ (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q ∧
        (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q := by
  obtain ⟨U, q, hU, hqS, hqE⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).mp hFqc
  exact ⟨U, q, hU, hqS, (isEtale_iff_presheaf_of_yoneda B S hS q).mp hqE⟩

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))

namespace DescentSituation

/-- **Stacks 084T over an affine base scheme, for a system bounded by the cutoff.** In the
situation of Stacks 084R over an affine base scheme, with the system bounded by the cutoff, if
the limit `X` of the inverse system is separated then some stage `X_i` is separated.

This is `DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isAffine` with the bound by
the cofinality of the cutoff replaced by `AlgebraicGeometry.Space.IsCutoffBoundedSystem`: the
limit of the affine charts is
`AlgebraicGeometry.Space.AffineChartSystem.limitBridgeOfBaseChangeSizeBounded`, and the charts are
uniformly bounded, being base changes of the stages along one chart of the distinguished stage,
which is what Stacks 081B and Stacks 01ZP need in the forms
`AlgebraicGeometry.Space.exists_isClosedImmersion_comp_prodMap_π_of_size_le` and
`AlgebraicGeometry.Space.exists_isClosedImmersion_pullback_snd_prodMap_of_size_le`. -/
theorem exists_isAbsolutelySeparated_system_obj_of_isAffine_of_isCutoffBoundedSystem
    (hSaff : IsAffine S) {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hDc : IsCutoffBoundedSystem B S hS D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  have : Nonempty I := ⟨D.base⟩
  have : IsDirectedOrder I := inferInstance
  have : IsFiltered I := inferInstance
  have : IsCofiltered Iᵒᵖ := inferInstance
  obtain ⟨hSize, ⟨ν, hν, hHom⟩, hB⟩ := hDc
  -- separatedness of the canonical limit presheaf
  have e : D.limitCone.pt ≅ limit D.system :=
    D.isLimit.conePointUniqueUpToIso (limit.isLimit _)
  have hlimAS : IsAlgebraicSpace B S hS (limit D.system) := D.limitAlgebraicSpace.of_iso e
  have hlimSep : IsSeparatedOver B S hS (limit D.system) :=
    (isAbsolutelySeparated_iff_isSeparatedOver B S hS hZ hSaff hlimAS).mp
      (isAbsolutelySeparated_of_isSeparated B S hS hZ hX (isSeparated_of_isIso B S hS e.inv))
  -- an affine étale surjective chart of the distinguished stage
  obtain ⟨U₀, chart, hU₀, hchartS, hchartE'⟩ := exists_affine_chart_presheaf_etale_surjective B S hS
    (D.system.obj (op D.base)) (D.algebraicSpace D.base) (D.quasiCompact D.base)
  set C := affineChartSystem B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart
    (fun {_ _} g ↦ D.transition_affine g) with hC
  set L : AffineChartSystem.LimitBridge C :=
    C.limitBridgeOfBaseChangeSizeBounded hSize hν hHom hB with hL
  have hKsize : #(Over (op D.base)) < B.cutoff :=
    mk_over_lt_of_mk_hom_le B.aleph0_lt_cutoff hSize hν hHom (op D.base)
  obtain ⟨μ, hμ, hb⟩ := hB (op D.base) _ chart
  have hCsize : ∀ j : Over (op D.base),
      ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)).size ≤ μ := fun j =>
    hb j _ (C.stageMap j) (C.baseMap j) (C.isPullback j)
  set j₀ : Over (op D.base) := Over.mk (𝟙 (op D.base)) with hj₀
  -- the charts of the stages and of the limit, with their properties
  have hq : ∀ j : Over (op D.base), yoneda.relativelyRepresentable (C.stageMap j) := fun j =>
    (D.algebraicSpace j.left.unop).diagonal_representable.of_diag (C.stageMap j)
  have hqE : ∀ j : Over (op D.base), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (C.stageMap j) := fun j =>
    presheaf_of_isPullback B S hS (C.isPullback j).flip hchartE'
  have hqS : ∀ j : Over (op D.base), (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (C.stageMap j) := fun j =>
    presheaf_of_isPullback B S hS (C.isPullback j).flip hchartS
  have hqLim : yoneda.relativelyRepresentable L.toLimit :=
    hlimAS.diagonal_representable.of_diag L.toLimit
  have hqLimE : (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) L.toLimit :=
    presheaf_of_isPullback B S hS (L.isPullback_stage j₀).flip (hqE j₀)
  -- the kernel pair of the limit chart is a closed immersion into `U ×_S U`
  have hkpLim : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqLim)) :=
    isClosedImmersion_kernelPairToProd_of_isSeparatedOver B S hS hlimSep hqLim
  have hUaff : ∀ j : Over (op D.base),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj j)) := fun j =>
    C.isAffine_obj j
  have hmono : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) ≤
      (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) := by
    intro Vv Ww g hg
    have hgE : Etale ((BigFppfOver.toScheme B S hS).map g) := hg
    exact (inferInstance : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g))
  have hfstLim : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (hqLim.fst' L.toLimit)) := by
    refine property_kernelPair_fst B S hS (@LocallyOfFiniteType.{u}) hqLim ?_
    exact MorphismProperty.relative_monotone hmono _ (presheaf_of_isPullback B S hS
      (IsPullback.of_hasPullback L.toLimit L.toLimit).flip hqLimE)
  have hftLim : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hqLim) ≫
        (BigFppfOver.toScheme B S hS).map prod.fst) := by
    rw [← Functor.map_comp,
      show kernelPairToProd B S hS hqLim ≫ prod.fst = hqLim.fst' L.toLimit from by
        simp [kernelPairToProd]]
    exact hfstLim
  -- Stacks 081B: the closed immersion already lands in a product with a stage
  obtain ⟨k₁, hk₁⟩ := exists_isClosedImmersion_comp_prodMap_π_of_size_le B S hS hSaff
    C.siteDiagram hUaff hKsize hμ hCsize L.isLimit L.isAffine_pt _ hkpLim j₀ hftLim
  have hRespects : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨ρ, hρ⟩ := exists_isPullback_kernelPairToProd_prodMap B S hS
    (limit.π D.system k₁.left) (hq k₁) hqLim (L.cone.π.app k₁) (L.isPullback_stage k₁)
  have hlimci : _root_.AlgebraicGeometry.IsClosedImmersion
      (pullback.snd ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
        ((BigFppfOver.toScheme B S hS).map
          (prod.map (L.cone.π.app k₁) (𝟙 (C.siteDiagram.obj k₁))))) := by
    refine (prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (hρ.map (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)).mp ?_
    rw [Functor.map_comp]
    exact hk₁ k₁ (𝟙 k₁)
  -- quasi-compactness and quasi-separatedness of the kernel pair at the stage
  have hUc : CompactSpace ((BigFppfOver.toScheme B S hS).obj (C.siteDiagram.obj k₁)) :=
    have := hUaff k₁; Scheme.compactSpace_of_isAffine _
  have hmqc : CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((hq k₁).pullback (C.stageMap k₁))) :=
    compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ (D.quasiSeparated k₁.left.unop)
      ((hq k₁).isPullback' (C.stageMap k₁)) hUc hUc
  have hmft : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁))) :=
    (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (C.stageMap k₁) (hqE k₁)).1
  have hmqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj
      ((hq k₁).pullback (C.stageMap k₁))) := by
    have hmm : Mono ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁))) :=
      (locallyOfFiniteType_and_mono_toScheme_kernelPairToProd B S hS (C.stageMap k₁)
        (hqE k₁)).2
    have := isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj k₁)
      (C.isAffine_obj k₁)
    exact quasiSeparatedSpace_of_quasiSeparated
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq k₁)))
  -- Stacks 01ZP: the closed immersion descends to a stage
  obtain ⟨i, hi, hires⟩ := exists_isClosedImmersion_pullback_snd_prodMap_of_size_le B S hS hSaff
    C.siteDiagram hUaff hKsize hμ hCsize L.isLimit k₁
    (kernelPairToProd B S hS (hq k₁)) hmft hmqc hmqs hlimci
  obtain ⟨ρ', hρ'⟩ := exists_isPullback_kernelPairToProd_prodMap B S hS
    (D.system.map hi.left) (hq k₁) (hq i) (C.siteDiagram.map hi)
    (AffineChartSystem.isPullback_map B S hS (op D.base) D.system ⟨U₀, hU₀⟩ chart C hi)
  have hcomp : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i) ≫
        prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) :=
    (prop_snd_iff_of_isPullback (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (hρ'.map (BigFppfOver.toScheme B S hS)) (IsPullback.of_hasPullback _ _)).mpr hires
  -- cancel the separated morphism `U_i ×_S U_i ⟶ U_i ×_S U_{k₁}`
  have hsep : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map
      (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) := by
    have := isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj i)
      (C.isAffine_obj i)
    have := isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (C.isAffine_obj i)
      (C.isAffine_obj k₁)
    have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi))) :=
      isAffineHom_of_isAffine _
    exact _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom _
  have hkpi : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i))) := by
    rw [Functor.map_comp] at hcomp
    exact _root_.AlgebraicGeometry.IsClosedImmersion.of_comp
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS (hq i)))
      ((BigFppfOver.toScheme B S hS).map
        (prod.map (𝟙 (C.siteDiagram.obj i)) (C.siteDiagram.map hi)))
  refine ⟨i.left.unop, leOfHom i.hom.unop, ?_⟩
  refine (isAbsolutelySeparated_iff_isSeparatedOver B S hS hZ hSaff
    (D.algebraicSpace i.left.unop)).mpr ?_
  exact isSeparatedOver_of_isClosedImmersion_kernelPairToProd B S hS
    (D.algebraicSpace i.left.unop) (hqS i) (hqE i) hkpi

/-- The view over the terminal scheme of a descent situation whose system is bounded by the
cutoff has its system bounded by the cutoff: the index is the same, and the base changes stay
uniformly bounded by `AlgebraicGeometry.Space.baseChangeSizeBounded_relocalize`. -/
theorem isCutoffBoundedSystem_viewOverIntegers {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hDc : IsCutoffBoundedSystem B S hS D.system) :
    IsCutoffBoundedSystem B (⊤_ Scheme.{u}) hZ (D.viewOverIntegers B S hS hZ).system :=
  ⟨hDc.1, hDc.2.1, baseChangeSizeBounded_relocalize B S hS hZ (integersMap B S hS hZ) D.system
    (fun j => D.algebraicSpace j.unop) D.transition_affine hDc.2.2⟩

/-- **Stacks 084T for a system bounded by the cutoff.** In the situation of Stacks 084R, over an
arbitrary base scheme and with the system bounded by the cutoff, if the limit `X` of the inverse
system is separated then some stage `X_i` is separated.

As for `AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj`, the
descent is read over the terminal scheme, which is affine; the system stays bounded by the cutoff
there. -/
theorem exists_isAbsolutelySeparated_system_obj_of_isCutoffBoundedSystem {I : Type u}
    [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hDc : IsCutoffBoundedSystem B S hS D.system)
    (hX : IsAbsolutelySeparated B S hS hZ D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) := by
  obtain ⟨i, hi, hres⟩ :=
    exists_isAbsolutelySeparated_system_obj_of_isAffine_of_isCutoffBoundedSystem
      B (⊤_ Scheme.{u}) hZ hZ inferInstance (D.viewOverIntegers B S hS hZ)
      (isCutoffBoundedSystem_viewOverIntegers B S hS hZ D hDc)
      ((isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ D.limitCone.pt).2 hX)
  exact ⟨i, hi, (isAbsolutelySeparated_viewOverIntegers_iff B S hS hZ
    (D.system.obj (op i))).1 hres⟩

end DescentSituation

end Descent

/-! ### Separatedness over a base algebraic space at a late stage -/

section SeparatedOverBase

variable (hZ : B.Contains (⊤_ Scheme.{u})) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]

/-- **Stacks 086X for a system bounded by the cutoff.** Let `Y` be a quasi-separated algebraic
space over `S` and let `X = lim X_i` be a directed limit, over `Y` and with affine transition
morphisms, of quasi-compact and quasi-separated algebraic spaces over `S`, as in the standing
situation of Stacks 084R, with the system bounded by the cutoff. If `X ⟶ Y` is separated then
`X_i ⟶ Y` is separated for all `i` large enough.

The proof is that of `AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_system_app`:
the situation is base changed along an affine étale chart of the distinguished stage composed
with the structure morphism to `Y`, which keeps the system bounded by the cutoff
(`AlgebraicGeometry.Space.baseChangeSizeBounded_baseChangeOverSystem`), and Stacks 084T in the
form `DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isCutoffBoundedSystem` gives
a separated stage of the base change, from which separatedness of `X_i ⟶ Y` descends. -/
theorem DescentSituation.exists_isSeparated_system_app_of_isCutoffBoundedSystem
    (D : DescentSituation B S hS hZ I) (hDc : IsCutoffBoundedSystem B S hS D.system)
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (hsep : IsSeparated B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)) := by
  have : Nonempty I := ⟨D.base⟩
  -- an affine étale surjective chart of the distinguished stage, and its image point of `Y`
  obtain ⟨U₀, q₀, hU₀, hq₀S, hq₀E'⟩ := exists_affine_chart_presheaf_etale_surjective B S hS
    (D.system.obj (op D.base)) (D.algebraicSpace D.base) (D.quasiCompact D.base)
  -- the base changed descent situation, its bound and the separatedness of its limit
  have hlim : IsAbsolutelySeparated B S hS hZ
      (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))).limitCone.pt :=
    isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ U₀ hU₀
      (pullback.snd f (q₀ ≫ t.app (op D.base)))
      (isSeparated_pullbackSnd B S hS (q₀ ≫ t.app (op D.base)) hsep)
  have hbc : IsCutoffBoundedSystem B S hS
      (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))).system :=
    ⟨hDc.1, hDc.2.1, baseChangeSizeBounded_baseChangeOverSystem B S hS D.system t
      (q₀ ≫ t.app (op D.base)) hDc.2.2⟩
  obtain ⟨i, hbi₀, hi⟩ :=
    DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isCutoffBoundedSystem B S hS hZ
      (D.baseChangeOver B S hS hZ hY hYqs t f hf U₀ hU₀ (q₀ ≫ t.app (op D.base))) hbc hlim
  have hbi : D.base ≤ i := hbi₀
  -- the base change of the stage along the chart of `Y` is separated
  have hsepi : IsSeparated B S hS (pullback.snd (t.app (op i)) (q₀ ≫ t.app (op D.base))) :=
    (isSeparated_pullbackSnd_iff_isAbsolutelySeparated B S hS hZ (D.algebraicSpace i)
      (t.app (op i)) U₀ hU₀ (q₀ ≫ t.app (op D.base))).mpr hi
  -- the chart of the distinguished stage, base changed to the stage `i` along the affine
  -- transition morphism
  have hτ : D.system.map (homOfLE hbi).op ≫ t.app (op D.base) = t.app (op i) := by simp
  obtain ⟨W, v, wq, hpb⟩ :=
    D.transition_affine (homOfLE hbi).op ⟨U₀, hU₀⟩ q₀
  -- descend separatedness to the stage itself
  have hstage : IsSeparated B S hS (t.app (op i)) := by
    refine isSeparated_of_isSeparated_pullbackSnd_of_etaleChart_factorization B S hS
      (D.algebraicSpace i) (t.app (op i))
      (presheaf_of_isPullback B S hS hpb.flip hq₀S)
      (presheaf_of_isPullback B S hS hpb.flip hq₀E') (yoneda.map wq) ?_ hsepi
    rw [← hτ]
    simp only [← Category.assoc, hpb.w]
  -- and propagate it to all later stages along the affine transition morphisms
  refine ⟨i, hbi, fun k hik => ?_⟩
  have hk : D.system.map (homOfLE hik).op ≫ t.app (op i) = t.app (op k) := by simp
  rw [← hk]
  exact isSeparated_comp B S hS _ _
    (isSeparated_of_isAffineHom B S hS (D.system.map (homOfLE hik).op)
      (D.algebraicSpace k) (D.algebraicSpace i) (D.transition_affine _)) hstage

/-- **Stacks 086X for a system with monomorphic transition morphisms.** In the situation of
Stacks 084R over a quasi-separated algebraic space `Y`, with fewer stages than the cutoff of the
site and monomorphic transition morphisms, if `X ⟶ Y` is separated then `X_i ⟶ Y` is separated
for all `i` large enough. No condition on the cofinality of the cutoff is involved: monomorphic
transition morphisms give uniformly bounded base changes
(`AlgebraicGeometry.Space.baseChangeSizeBounded_of_mono`). -/
theorem DescentSituation.exists_isSeparated_system_app_of_mono
    (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff)
    (hmono : ∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), Mono (D.system.map g))
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (hsep : IsSeparated B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)) :=
  D.exists_isSeparated_system_app_of_isCutoffBoundedSystem B S hS hZ
    (isCutoffBoundedSystem_of_preorder B S hS hI
      (baseChangeSizeBounded_of_mono B S hS D.system fun g => hmono g))
    hY hYqs t f hf hsep

/-- **Stacks 086X for a system of closed immersions.** In the situation of Stacks 084R over a
quasi-separated algebraic space `Y`, with fewer stages than the cutoff of the site and closed
immersions as transition morphisms, if `X ⟶ Y` is separated then `X_i ⟶ Y` is separated for all
`i` large enough. Closed immersions are monomorphisms, so this is
`AlgebraicGeometry.Space.DescentSituation.exists_isSeparated_system_app_of_mono`. -/
theorem DescentSituation.exists_isSeparated_system_app_of_isClosedImmersion
    (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff)
    (hci : ∀ ⦃i j : Iᵒᵖ⦄ (g : i ⟶ j), IsClosedImmersion B S hS (D.system.map g))
    (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (f : D.limitCone.pt ⟶ Y)
    (hf : ∀ j, D.limitCone.π.app j ≫ t.app j = f) (hsep : IsSeparated B S hS f) :
    ∃ i, D.base ≤ i ∧ ∀ k, i ≤ k → IsSeparated B S hS (t.app (op k)) :=
  D.exists_isSeparated_system_app_of_mono B S hS hZ hI
    (fun _ _ g => mono_of_isClosedImmersion B S hS _ (hci g)) hY hYqs t f hf hsep

end SeparatedOverBase

end AlgebraicGeometry.Space

end
