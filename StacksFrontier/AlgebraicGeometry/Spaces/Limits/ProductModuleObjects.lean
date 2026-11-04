module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModuleOfReindexComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductChartGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.RepresentedChartModuleLimit

/-!
# Modules along a limit of base changes of an algebraic space

Let `X₀` be an algebraic space over `S` and `T : I ⥤ (Sch/S)` a cofiltered system of affine
schemes whose underlying schemes have a limit `c`, with `h_{T i₀} ⨯ X₀` quasi-compact and
quasi-separated. A quasi-coherent module of finite presentation on `h_{c.pt} ⨯ X₀` is the inverse
image of a quasi-coherent module of finite presentation on some `h_{T j} ⨯ X₀`: the object clause
of Limits of Spaces, Lemma 70.7.2 (Stacks 07V7).

## Main results

* `AlgebraicGeometry.Space.exists_modulePullback_productSpaceConeMap_iso`: the object clause.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X₀ : AlgebraicSpaces B S hS}
  {I : Type u} [Category.{u} I] {T : I ⥤ BigFppfOver B S hS} {i₀ : I}

@[deprecated schemeSpaceMap_comp (since := "2026-10-27")]
alias schemeSpaceMap_comp' := schemeSpaceMap_comp

/-- Solving `X = t₁ ≫ x ≫ t₂` for `x`. -/
theorem eq_sandwich_of_eq {C : Type*} [Category C] {A A' D D' : C} {t₁ : A ⟶ A'} {s₁ : A' ⟶ A}
    {t₂ : D ⟶ D'} {s₂ : D' ⟶ D} (h₁ : s₁ ≫ t₁ = 𝟙 A') (h₂ : t₂ ≫ s₂ = 𝟙 D) {x : A' ⟶ D}
    {X : A ⟶ D'} (h : X = t₁ ≫ x ≫ t₂) : x = s₁ ≫ X ≫ s₂ := by
  rw [h, ← Category.assoc, ← Category.assoc, h₁, Category.id_comp, Category.assoc, h₂,
    Category.comp_id]

/-- A morphism sandwiched between two pairs of mutually inverse morphisms is itself. -/
theorem sandwich_cancel' {C : Type*} [Category C] {A A' D D' : C} {t₁ : A ⟶ A'} {s₁ : A' ⟶ A}
    {t₂ : D ⟶ D'} {s₂ : D' ⟶ D} (h₁ : s₁ ≫ t₁ = 𝟙 A') (h₂ : t₂ ≫ s₂ = 𝟙 D) (x : A' ⟶ D) :
    s₁ ≫ (t₁ ≫ x ≫ t₂) ≫ s₂ = x := by
  rw [Category.assoc, Category.assoc, h₂, Category.comp_id, ← Category.assoc, h₁,
    Category.id_comp]

/-- Two reindexings of morphisms of modules that agree on the limit already agree at some stage. -/
private theorem exists_modulePullbackReindex_eq_of_isLimit [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))] {c : Cone T}
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) {U₀ : BigFppfOver B S hS}
    (a₀ : yoneda.obj U₀ ⟶ (productSpace X₀ (T.obj i₀)).1) (n : Over i₀)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj ((productChartSystem X₀ T i₀ a₀).obj n))]
    {Z : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS Z.1 Z.2} (hM : M.IsQuasicoherentOnSite)
    (hMfp : M.IsFinitePresentationOnSite)
    {p q : schemeSpace ((productChartSystem X₀ T i₀ a₀).obj n) ⟶ Z}
    {α β : (modulePullback B S hS p).obj M ⟶ (modulePullback B S hS q).obj M}
    (h : modulePullbackReindex (productChartConeπ X₀ T i₀ a₀ c n) α =
      modulePullbackReindex (productChartConeπ X₀ T i₀ a₀ c n) β) :
    ∃ (n' : Over i₀) (e : n' ⟶ n),
      modulePullbackReindex (schemeSpaceMap ((productChartSystem X₀ T i₀ a₀).map e)) α =
        modulePullbackReindex (schemeSpaceMap ((productChartSystem X₀ T i₀ a₀).map e)) β := by
  obtain ⟨n', e, he⟩ := exists_modulePullback_map_eq_of_isLimit_pt
    (productChartSystem X₀ T i₀ a₀) (productChartCone X₀ T i₀ a₀ c)
    (isLimitProductChartCone X₀ T i₀ a₀ c hc) n
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM)
    (isFinitePresentationOnSite_modulePullback B S hS _ M hMfp)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM)
    (isFinitePresentationOnSite_modulePullback B S hS _ M hMfp) α β
    ((modulePullbackReindex_eq_iff _ _ _).1 h)
  exact ⟨n', e, (modulePullbackReindex_eq_iff _ _ _).2 he⟩

namespace ProductChartData

variable (D : ProductChartData X₀ T i₀) (c : Cone T)

/-! ### The presentation of the limit -/

/-- The chart of the limit. -/
abbrev chartc := productChartConeSpaceMap X₀ T i₀ D.a₀ c

/-- The target of the arrows of the limit. -/
abbrev tArrc := productChartConeSpacePairMap X₀ T i₀ D.a₀ D.t₀ D.a₁ rfl c

/-- The source of the arrows of the limit. -/
abbrev sArrc := productChartConeSpacePairMap X₀ T i₀ D.a₀ D.s₀ D.a₁ D.s_a₁ c

/-- The arrow applied second, at the limit. -/
abbrev pArrc := productChartConeSpacePairMap X₀ T i₀ D.a₁ D.p₀ D.a₂ rfl c

/-- The arrow applied first, at the limit. -/
abbrev qArrc := productChartConeSpacePairMap X₀ T i₀ D.a₁ D.q₀ D.a₂ D.q_a₂ c

/-- The composite arrow, at the limit. -/
abbrev cArrc := productChartConeSpacePairMap X₀ T i₀ D.a₁ D.c₀ D.a₂ D.c_a₂ c

/-- The projection of the chart of the limit to the chart of a stage. -/
abbrev πU (k : Over i₀) := productChartConeπ X₀ T i₀ D.a₀ c k

/-- The projection of the arrows of the limit to the arrows of a stage. -/
abbrev πR (k : Over i₀) := productChartConeπ X₀ T i₀ D.a₁ c k

/-- The projection of the composable pairs of the limit to those of a stage. -/
abbrev πK (k : Over i₀) := productChartConeπ X₀ T i₀ D.a₂ c k

/-- The transition morphisms of the charts. -/
abbrev mapU {k k' : Over i₀} (f : k ⟶ k') :=
  schemeSpaceMap ((productChartSystem X₀ T i₀ D.a₀).map f)

/-- The transition morphisms of the arrows. -/
abbrev mapR {k k' : Over i₀} (f : k ⟶ k') :=
  schemeSpaceMap ((productChartSystem X₀ T i₀ D.a₁).map f)

/-- The transition morphisms of the composable pairs. -/
abbrev mapK {k k' : Over i₀} (f : k ⟶ k') :=
  schemeSpaceMap ((productChartSystem X₀ T i₀ D.a₂).map f)

/-- The arrows of the limit form the kernel pair of its chart, as morphisms of presheaves. -/
theorem isPullback_tArrc :
    IsPullback (D.tArrc c).hom (D.sArrc c).hom (D.chartc c).hom (D.chartc c).hom :=
  isPullback_productChartKernelPair X₀ D.a₀ D.isPullback D.a₁ rfl D.s_a₁ (V := c.pt) (c.π.app i₀)

/-- The arrows of the limit form the kernel pair of its chart. -/
theorem isPullback_tArrc' : IsPullback (D.tArrc c) (D.sArrc c) (D.chartc c) (D.chartc c) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) (D.isPullback_tArrc c)

/-- The target and the source of the arrows of the limit agree after the chart. -/
theorem tArrc_comp_chartc : D.tArrc c ≫ D.chartc c = D.sArrc c ≫ D.chartc c :=
  (D.isPullback_tArrc' c).w

/-- Morphisms of the site with equal composites have equal composites as algebraic spaces. -/
private theorem schemeSpaceMap_comp_eq_comp {U V W Z : BigFppfOver B S hS} {a : U ⟶ V}
    {b : V ⟶ Z} {c : U ⟶ W} {d : W ⟶ Z} (h : a ≫ b = c ≫ d) :
    schemeSpaceMap a ≫ schemeSpaceMap b = schemeSpaceMap c ≫ schemeSpaceMap d := by
  rw [← schemeSpaceMap_comp, ← schemeSpaceMap_comp, h]

/-- At the limit, the composite arrow has the target of the arrow applied second. -/
theorem cArrc_comp_tArrc : D.cArrc c ≫ D.tArrc c = D.pArrc c ≫ D.tArrc c :=
  schemeSpaceMap_comp_eq_comp ((productChartPairMap_comp_productChartPairMap X₀ D.a₀ D.t₀ D.a₁ rfl
    D.c₀ D.a₂ D.c_a₂ D.ct_a₂ (c.π.app i₀)).trans
    ((productChartPairMap_congr X₀ D.a₀ D.c₀_t D.a₂ D.ct_a₂ D.pt_a₂ (c.π.app i₀)).trans
      (productChartPairMap_comp_productChartPairMap X₀ D.a₀ D.t₀ D.a₁ rfl
        D.p₀ D.a₂ rfl D.pt_a₂ (c.π.app i₀)).symm))

/-- At the limit, the composite arrow has the source of the arrow applied first. -/
theorem cArrc_comp_sArrc : D.cArrc c ≫ D.sArrc c = D.qArrc c ≫ D.sArrc c :=
  schemeSpaceMap_comp_eq_comp ((productChartPairMap_comp_productChartPairMap X₀ D.a₀ D.s₀ D.a₁
    D.s_a₁ D.c₀ D.a₂ D.c_a₂ D.cs_a₂ (c.π.app i₀)).trans
    ((productChartPairMap_congr X₀ D.a₀ D.c₀_s D.a₂ D.cs_a₂ D.qs_a₂ (c.π.app i₀)).trans
      (productChartPairMap_comp_productChartPairMap X₀ D.a₀ D.s₀ D.a₁ D.s_a₁
        D.q₀ D.a₂ D.q_a₂ D.qs_a₂ (c.π.app i₀)).symm))

/-- At the limit, the source of the arrow applied second is the target of the arrow applied
first. -/
theorem pArrc_comp_sArrc : D.pArrc c ≫ D.sArrc c = D.qArrc c ≫ D.tArrc c :=
  schemeSpaceMap_comp_eq_comp (isPullback_productChartPairMap_of_isPullback X₀ D.a₀ D.isPullbackK
    D.a₁ D.s_a₁ D.a₁ rfl D.a₂ rfl D.q_a₂ (V := c.pt) (c.π.app i₀)).w

/-- The unit arrows of the limit. -/
def diagc : schemeSpace (productChartCone X₀ T i₀ D.a₀ c).pt ⟶
    schemeSpace (productChartCone X₀ T i₀ D.a₁ c).pt :=
  (D.isPullback_tArrc' c).lift (𝟙 _) (𝟙 _) rfl

/-- The target of the unit arrows of the limit is the identity. -/
theorem diagc_tArrc : D.diagc c ≫ D.tArrc c = 𝟙 _ := (D.isPullback_tArrc' c).lift_fst _ _ _

/-- The source of the unit arrows of the limit is the identity. -/
theorem diagc_sArrc : D.diagc c ≫ D.sArrc c = 𝟙 _ := (D.isPullback_tArrc' c).lift_snd _ _ _

/-! ### Compatibilities with the stages -/

/-- The projections of the limit to a stage commute with the targets of the arrows. -/
theorem πR_tArr (k : Over i₀) : D.πR c k ≫ D.tArr k = D.tArrc c ≫ D.πU c k :=
  productChartConeπ_comp_productChartSpacePairMap X₀ T i₀ D.a₀ D.t₀ D.a₁ rfl c k

/-- The projections of the limit to a stage commute with the sources of the arrows. -/
theorem πR_sArr (k : Over i₀) : D.πR c k ≫ D.sArr k = D.sArrc c ≫ D.πU c k :=
  productChartConeπ_comp_productChartSpacePairMap X₀ T i₀ D.a₀ D.s₀ D.a₁ D.s_a₁ c k

/-- The projections of the limit to a stage commute with the arrow applied second. -/
theorem πK_pArr (k : Over i₀) : D.πK c k ≫ D.pArr k = D.pArrc c ≫ D.πR c k :=
  productChartConeπ_comp_productChartSpacePairMap X₀ T i₀ D.a₁ D.p₀ D.a₂ rfl c k

/-- The projections of the limit to a stage commute with the arrow applied first. -/
theorem πK_qArr (k : Over i₀) : D.πK c k ≫ D.qArr k = D.qArrc c ≫ D.πR c k :=
  productChartConeπ_comp_productChartSpacePairMap X₀ T i₀ D.a₁ D.q₀ D.a₂ D.q_a₂ c k

/-- The projections of the limit to a stage commute with the composite arrow. -/
theorem πK_cArr (k : Over i₀) : D.πK c k ≫ D.cArr k = D.cArrc c ≫ D.πR c k :=
  productChartConeπ_comp_productChartSpacePairMap X₀ T i₀ D.a₁ D.c₀ D.a₂ D.c_a₂ c k

/-- The projection of the chart of the limit to a stage commutes with the charts and the
projection of the limit space to that stage. -/
theorem πU_chart (k : Over i₀) :
    D.πU c k ≫ D.chart T i₀ k = D.chartc c ≫ productSpaceConeMap X₀ T c k.left :=
  (productChartConeSpaceMap_comp_productSpaceMap X₀ T i₀ D.a₀ c k).symm

/-- The projections of the chart of the limit commute with the transition morphisms. -/
theorem πU_mapU {k k' : Over i₀} (f : k ⟶ k') : D.πU c k ≫ D.mapU f = D.πU c k' :=
  (schemeSpaceMap_comp _ _).symm.trans (congrArg _ ((productChartCone X₀ T i₀ _ c).w f))

/-- The projections of the arrows of the limit commute with the transition morphisms. -/
theorem πR_mapR {k k' : Over i₀} (f : k ⟶ k') : D.πR c k ≫ D.mapR f = D.πR c k' :=
  (schemeSpaceMap_comp _ _).symm.trans (congrArg _ ((productChartCone X₀ T i₀ _ c).w f))

/-- The projections of the composable pairs of the limit commute with the transition morphisms. -/
theorem πK_mapK {k k' : Over i₀} (f : k ⟶ k') : D.πK c k ≫ D.mapK f = D.πK c k' :=
  (schemeSpaceMap_comp _ _).symm.trans (congrArg _ ((productChartCone X₀ T i₀ _ c).w f))

/-- The transition morphisms commute with the targets of the arrows. -/
theorem mapR_tArr {k k' : Over i₀} (f : k ⟶ k') : D.mapR f ≫ D.tArr k' = D.tArr k ≫ D.mapU f :=
  schemeSpaceMap_comp_productChartSpacePairMap X₀ T i₀ D.a₀ D.t₀ D.a₁ rfl f

/-- The transition morphisms commute with the sources of the arrows. -/
theorem mapR_sArr {k k' : Over i₀} (f : k ⟶ k') : D.mapR f ≫ D.sArr k' = D.sArr k ≫ D.mapU f :=
  schemeSpaceMap_comp_productChartSpacePairMap X₀ T i₀ D.a₀ D.s₀ D.a₁ D.s_a₁ f

/-- The transition morphisms commute with the arrow applied second. -/
theorem mapK_pArr {k k' : Over i₀} (f : k ⟶ k') : D.mapK f ≫ D.pArr k' = D.pArr k ≫ D.mapR f :=
  schemeSpaceMap_comp_productChartSpacePairMap X₀ T i₀ D.a₁ D.p₀ D.a₂ rfl f

/-- The transition morphisms commute with the arrow applied first. -/
theorem mapK_qArr {k k' : Over i₀} (f : k ⟶ k') : D.mapK f ≫ D.qArr k' = D.qArr k ≫ D.mapR f :=
  schemeSpaceMap_comp_productChartSpacePairMap X₀ T i₀ D.a₁ D.q₀ D.a₂ D.q_a₂ f

/-- The transition morphisms commute with the composite arrow. -/
theorem mapK_cArr {k k' : Over i₀} (f : k ⟶ k') : D.mapK f ≫ D.cArr k' = D.cArr k ≫ D.mapR f :=
  schemeSpaceMap_comp_productChartSpacePairMap X₀ T i₀ D.a₁ D.c₀ D.a₂ D.c_a₂ f

/-- The transition morphisms of the charts respect composition. -/
theorem mapU_comp {k k' k'' : Over i₀} (f : k ⟶ k') (g : k' ⟶ k'') :
    D.mapU (f ≫ g) = D.mapU f ≫ D.mapU g := by
  rw [mapU, Functor.map_comp, schemeSpaceMap_comp]

/-- The transition morphisms of the arrows respect composition. -/
theorem mapR_comp {k k' k'' : Over i₀} (f : k ⟶ k') (g : k' ⟶ k'') :
    D.mapR (f ≫ g) = D.mapR f ≫ D.mapR g := by
  rw [mapR, Functor.map_comp, schemeSpaceMap_comp]

/-- The transition morphisms of the composable pairs respect composition. -/
theorem mapK_comp {k k' k'' : Over i₀} (f : k ⟶ k') (g : k' ⟶ k'') :
    D.mapK (f ≫ g) = D.mapK f ≫ D.mapK g := by
  rw [mapK, Functor.map_comp, schemeSpaceMap_comp]

/-- The transition morphisms commute with the unit arrows. -/
theorem mapU_diag {k k' : Over i₀} (f : k ⟶ k') : D.mapU f ≫ D.diag k' = D.diag k ≫ D.mapR f := by
  apply (D.isPullback_tArr' k').hom_ext
  · rw [Category.assoc, diag_tArr, Category.comp_id, Category.assoc, mapR_tArr, ← Category.assoc,
      diag_tArr, Category.id_comp]
  · rw [Category.assoc, diag_sArr, Category.comp_id, Category.assoc, mapR_sArr, ← Category.assoc,
      diag_sArr, Category.id_comp]

/-- The projections of the limit to a stage commute with the unit arrows. -/
theorem πU_diag (k : Over i₀) : D.πU c k ≫ D.diag k = D.diagc c ≫ D.πR c k := by
  apply (D.isPullback_tArr' k).hom_ext
  · rw [Category.assoc, diag_tArr, Category.comp_id, Category.assoc, πR_tArr, ← Category.assoc,
      diagc_tArrc, Category.id_comp]
  · rw [Category.assoc, diag_sArr, Category.comp_id, Category.assoc, πR_sArr, ← Category.assoc,
      diagc_sArrc, Category.id_comp]

/-! ### The descended transition -/

/-- The target of the arrows of the limit, projected to the stage `k`, is the projection to an
earlier stage `n`, followed by the transition `f : n ⟶ k` and the target. -/
theorem tArrc_πU {n k : Over i₀} (f : n ⟶ k) :
    D.tArrc c ≫ D.πU c k = D.πR c n ≫ D.mapR f ≫ D.tArr k := by
  rw [← Category.assoc, πR_mapR, πR_tArr]

/-- The source of the arrows of the limit, projected to the stage `k`, is the projection to an
earlier stage `n`, followed by the transition `f : n ⟶ k` and the source. -/
theorem sArrc_πU {n k : Over i₀} (f : n ⟶ k) :
    D.sArrc c ≫ D.πU c k = D.πR c n ≫ D.mapR f ≫ D.sArr k := by
  rw [← Category.assoc, πR_mapR, πR_sArr]

/-- The arrows of each stage form an absolutely quasi-separated algebraic space. -/
theorem isAbsolutelyQuasiSeparated_arrows (hZ : B.Contains (⊤_ Scheme.{u}))
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))] (k : Over i₀) :
    IsAbsolutelyQuasiSeparated B S hS hZ
      (schemeSpace ((productChartSystem X₀ T i₀ D.a₁).obj k)).1 := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj D.U₀) := D.isAffine
  have hU : IsAffineSpace B S hS (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k)).1 :=
    isAffineSpace_yoneda B S hS _ inferInstance
  refine isAbsolutelyQuasiSeparated_of_isQuasiSeparated_hom_of_isAffineSpace B S hS hZ (D.tArr k)
    ?_ hU
  exact isQuasiSeparated_of_isPullback B S hS (D.isPullback_tArr k).flip
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ
      (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k)).2
      (isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ hU) _)

/-- **The descent datum of a module on the limit descends to a stage**: a quasi-coherent module
`ℳ` of finite presentation on a chart `U_{k₁}` with `π^*ℳ ≅ u^*𝒢` on the chart of the limit
(Stacks 01ZR (1)), and a morphism `α` on the arrows `R_n` of a later stage whose inverse image to
the arrows of the limit is the descent datum of `𝒢` transported to `ℳ` (Stacks 01ZR (2)). -/
theorem exists_descentTransport [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (hZ : B.Contains (⊤_ Scheme.{u}))
    (G : Modules.{u, u} B S hS (productSpace X₀ c.pt).1 (productSpace X₀ c.pt).2)
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite) :
    ∃ (k₁ : Over i₀) (M : Modules.{u, u} B S hS
        (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k₁)).1
        (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k₁)).2)
      (_ : M.IsQuasicoherentOnSite) (_ : M.IsFinitePresentationOnSite)
      (ι : (modulePullback B S hS (D.πU c k₁)).obj M ≅
        (modulePullback B S hS (D.chartc c)).obj G) (n : Over i₀) (f : n ⟶ k₁)
      (α : (modulePullback B S hS (D.mapR f ≫ D.tArr k₁)).obj M ⟶
        (modulePullback B S hS (D.mapR f ≫ D.sArr k₁)).obj M),
      modulePullbackReindex (D.πR c n) α = descentTransport (D.πU c k₁) (D.chartc c) ι
        (D.tArrc_πU c f) (D.sArrc_πU c f) (D.tArrc_comp_chartc c) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj D.U₀) := D.isAffine
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj D.R₀) := D.compactR
  obtain ⟨k₁, M, hM, hMfp, ⟨ι⟩⟩ := exists_modulePullback_iso_of_isLimit_pt
    (productChartSystem X₀ T i₀ D.a₀) (productChartCone X₀ T i₀ D.a₀ c)
    (isLimitProductChartCone X₀ T i₀ D.a₀ c hc) ((modulePullback B S hS (D.chartc c)).obj G)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ G hG)
    (isFinitePresentationOnSite_modulePullback B S hS _ G hGfp)
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = descentTransport (D.πU c k₁) (D.chartc c) ι (D.πR_tArr c k₁).symm
    (D.πR_sArr c k₁).symm (D.tArrc_comp_chartc c) := ⟨_, rfl⟩
  obtain ⟨k, ψ, hψ⟩ := exists_homTransport_schemeSpaceMap_eq_of_isLimit
    (productChartSystem X₀ T i₀ D.a₁) k₁ hZ (productChartCone X₀ T i₀ D.a₁ c)
    (isLimitProductChartCone X₀ T i₀ D.a₁ c hc)
    (isQuasiCompactSpace_yoneda_of_compactSpace B S hS _ inferInstance)
    (D.isAbsolutelyQuasiSeparated_arrows hZ k₁)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM)
    (isFinitePresentationOnSite_modulePullback B S hS _ M hMfp)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ M hM)
    (isFinitePresentationOnSite_modulePullback B S hS _ M hMfp)
    (modulePullbackUnflattenHom (D.πR c k₁) θ)
  refine ⟨k₁, M, hM, hMfp, ι, k.left, k.hom, modulePullbackFlattenHom (D.mapR k.hom) ψ, ?_⟩
  have e₁ : D.πR c k₁ ≫ D.tArr k₁ = D.πR c k.left ≫ D.mapR k.hom ≫ D.tArr k₁ := by
    rw [← Category.assoc, πR_mapR]
  have e₂ : D.πR c k.left ≫ D.mapR k.hom ≫ D.sArr k₁ = D.πR c k₁ ≫ D.sArr k₁ := by
    rw [← Category.assoc, πR_mapR]
  have hψ' : QuasiCoherentDescent.homTransport ((modulePullback B S hS (D.tArr k₁)).obj M)
      ((modulePullback B S hS (D.sArr k₁)).obj M) (D.πR c k.left) (D.πR_mapR c k.hom) ψ =
      modulePullbackUnflattenHom (D.πR c k₁) θ := hψ
  have key := modulePullbackFlattenHom_homTransport (D.tArr k₁) (D.sArr k₁) (M := M) (N := M)
    (D.πR c k.left) (D.mapR k.hom) (D.πR_mapR c k.hom) ψ e₁ e₂
  rw [hψ', modulePullbackFlattenHom_unflattenHom, hθ] at key
  have k2 : pullbackTransport M e₁.symm ≫ descentTransport (D.πU c k₁) (D.chartc c) ι
      (D.πR_tArr c k₁).symm (D.πR_sArr c k₁).symm (D.tArrc_comp_chartc c) ≫
        pullbackTransport M e₂.symm =
      modulePullbackReindexHom (D.πR c k.left) (modulePullbackFlattenHom (D.mapR k.hom) ψ) := by
    rw [key, ← Category.assoc (pullbackTransport M e₁.symm),
      ← Category.assoc (pullbackTransport M e₁.symm), pullbackTransport_comp_self M e₁.symm e₁,
      Category.id_comp, Category.assoc _ (pullbackTransport M e₂),
      pullbackTransport_comp_self M e₂ e₂.symm, Category.comp_id]
  refine (modulePullbackReindexHom_eq _ _).symm.trans ?_
  refine k2.symm.trans ?_
  exact pullbackTransport_comp_descentTransport_comp (π := D.πU c k₁) (u := D.chartc c)
    (x := D.tArrc c) (y := D.sArrc c) ι (D.πR_tArr c k₁).symm
    (D.πR_sArr c k₁).symm (D.tArrc_comp_chartc c) e₁.symm e₂.symm (D.tArrc_πU c k.hom)
    (D.sArrc_πU c k.hom)

/-! ### The unit and cocycle conditions at a stage -/

/-- The unit arrows of the stage `n`, followed by the transition `f : n ⟶ k` and the target, are
the transition morphism of the charts. -/
theorem diag_tArr_mapU {n k : Over i₀} (f : n ⟶ k) :
    D.diag n ≫ D.mapR f ≫ D.tArr k = D.mapU f := by
  rw [mapR_tArr, ← Category.assoc, diag_tArr, Category.id_comp]

/-- The unit arrows of the stage `n`, followed by the transition `f : n ⟶ k` and the source, are
the transition morphism of the charts. -/
theorem diag_sArr_mapU {n k : Over i₀} (f : n ⟶ k) :
    D.diag n ≫ D.mapR f ≫ D.sArr k = D.mapU f := by
  rw [mapR_sArr, ← Category.assoc, diag_sArr, Category.id_comp]

/-- **The unit condition holds at a stage** (Stacks 01ZR (3)): a morphism on the arrows of a
stage whose inverse image to the arrows of the limit is a transported descent datum satisfies
the unit condition after passing to a later stage. -/
theorem exists_transitionUnit [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    {G : Modules.{u, u} B S hS (productSpace X₀ c.pt).1 (productSpace X₀ c.pt).2} {k₁ : Over i₀}
    {M : Modules.{u, u} B S hS (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k₁)).1
      (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k₁)).2}
    (hM : M.IsQuasicoherentOnSite) (hMfp : M.IsFinitePresentationOnSite)
    (ι : (modulePullback B S hS (D.πU c k₁)).obj M ≅ (modulePullback B S hS (D.chartc c)).obj G)
    {n : Over i₀} (f : n ⟶ k₁)
    (α : (modulePullback B S hS (D.mapR f ≫ D.tArr k₁)).obj M ⟶
      (modulePullback B S hS (D.mapR f ≫ D.sArr k₁)).obj M)
    (hα : modulePullbackReindex (D.πR c n) α = descentTransport (D.πU c k₁) (D.chartc c) ι
      (D.tArrc_πU c f) (D.sArrc_πU c f) (D.tArrc_comp_chartc c)) :
    ∃ (n' : Over i₀) (e : n' ⟶ n), TransitionUnit B S hS M α (D.mapU e ≫ D.diag n) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj D.U₀) := D.isAffine
  have hd : D.diag n ≫ D.mapR f ≫ D.tArr k₁ = D.diag n ≫ D.mapR f ≫ D.sArr k₁ :=
    (D.diag_tArr_mapU f).trans (D.diag_sArr_mapU f).symm
  have E₁ : D.πU c n ≫ D.diag n ≫ D.mapR f ≫ D.tArr k₁ =
      (D.πU c n ≫ D.diag n) ≫ D.mapR f ≫ D.tArr k₁ := (Category.assoc _ _ _).symm
  have E₂ : (D.πU c n ≫ D.diag n) ≫ D.mapR f ≫ D.sArr k₁ =
      D.πU c n ≫ D.diag n ≫ D.mapR f ≫ D.sArr k₁ := Category.assoc _ _ _
  have hab : (D.πU c n ≫ D.diag n) ≫ D.mapR f ≫ D.tArr k₁ =
      (D.πU c n ≫ D.diag n) ≫ D.mapR f ≫ D.sArr k₁ := E₁.symm.trans ((congrArg _ hd).trans E₂.symm)
  have hx : (D.diagc c ≫ D.tArrc c) ≫ D.πU c k₁ = (D.πU c n ≫ D.diag n) ≫ D.mapR f ≫ D.tArr k₁ := by
    rw [diagc_tArrc, Category.id_comp, Category.assoc, D.diag_tArr_mapU f, πU_mapU]
  have hy : (D.diagc c ≫ D.sArrc c) ≫ D.πU c k₁ = (D.πU c n ≫ D.diag n) ≫ D.mapR f ≫ D.sArr k₁ := by
    rw [diagc_sArrc, Category.id_comp, Category.assoc, D.diag_sArr_mapU f, πU_mapU]
  have hxy : (D.diagc c ≫ D.tArrc c) ≫ D.chartc c = (D.diagc c ≫ D.sArrc c) ≫ D.chartc c := by
    rw [Category.assoc, Category.assoc, tArrc_comp_chartc]
  have hlim := modulePullbackReindex_eq_descentTransport_of (π := D.πU c k₁) (u := D.chartc c)
    (x := D.tArrc c) (y := D.sArrc c) (x' := D.diagc c ≫ D.tArrc c)
    (y' := D.diagc c ≫ D.sArrc c) ι α (D.πR c n) (D.tArrc_πU c f)
    (D.sArrc_πU c f) (D.tArrc_comp_chartc c) hα (D.diagc c) (D.πU c n ≫ D.diag n)
    (D.πU_diag c n).symm rfl rfl hx hy hxy
  rw [descentTransport_eq_pullbackTransport (π := D.πU c k₁) (u := D.chartc c)
    (x := D.diagc c ≫ D.tArrc c) (y := D.diagc c ≫ D.sArrc c) ι hx hy hxy
    ((D.diagc_tArrc c).trans (D.diagc_sArrc c).symm) hab] at hlim
  have h₁ := modulePullbackReindex_comp' (modulePullbackCompIsoAssoc B S hS) (D.πU c n) (D.diag n)
    (D.πU c n ≫ D.diag n) rfl α E₁ E₂
  rw [hlim, pullbackTransport_comp₃ B S hS M E₁ hab E₂ (congrArg (D.πU c n ≫ ·) hd)] at h₁
  have h₂ := modulePullbackReindex_pullbackTransport (D.πU c n) hd M (congrArg (D.πU c n ≫ ·) hd)
  obtain ⟨n', e, he⟩ := exists_modulePullbackReindex_eq_of_isLimit hc D.a₀ n hM hMfp
    (h₁.trans h₂.symm)
  refine ⟨n', e, TransitionUnit.of_transitionReindex_eq M α hd (D.mapU e) ?_⟩
  rw [transitionReindex_eq_modulePullbackReindex, transitionReindex_eq_modulePullbackReindex,
    transitionReindex_eq_modulePullbackReindex]
  exact he

/-- Two morphisms into the arrows of a stage with the same target still have the same target
after a transition morphism. -/
theorem comp_mapR_tArr {W : AlgebraicSpaces B S hS} {n k : Over i₀} (f : n ⟶ k)
    {g g' : W ⟶ schemeSpace ((productChartSystem X₀ T i₀ D.a₁).obj n)}
    (h : g ≫ D.tArr n = g' ≫ D.tArr n) :
    g ≫ D.mapR f ≫ D.tArr k = g' ≫ D.mapR f ≫ D.tArr k := by
  rw [mapR_tArr, ← Category.assoc, h, Category.assoc]

/-- Two morphisms into the arrows of a stage with the same source still have the same source
after a transition morphism. -/
theorem comp_mapR_sArr {W : AlgebraicSpaces B S hS} {n k : Over i₀} (f : n ⟶ k)
    {g g' : W ⟶ schemeSpace ((productChartSystem X₀ T i₀ D.a₁).obj n)}
    (h : g ≫ D.sArr n = g' ≫ D.sArr n) :
    g ≫ D.mapR f ≫ D.sArr k = g' ≫ D.mapR f ≫ D.sArr k := by
  rw [mapR_sArr, ← Category.assoc, h, Category.assoc]

/-- If the source of `g` is the target of `g'` in the arrows of a stage, this persists after a
transition morphism. -/
theorem comp_mapR_sArr_tArr {W : AlgebraicSpaces B S hS} {n k : Over i₀} (f : n ⟶ k)
    {g g' : W ⟶ schemeSpace ((productChartSystem X₀ T i₀ D.a₁).obj n)}
    (h : g ≫ D.sArr n = g' ≫ D.tArr n) :
    g ≫ D.mapR f ≫ D.sArr k = g' ≫ D.mapR f ≫ D.tArr k := by
  rw [mapR_sArr, mapR_tArr, ← Category.assoc, h, Category.assoc]

/-- After a transition morphism, the composite arrow has the target of the arrow applied second. -/
theorem cArr_tArr_mapR {n k : Over i₀} (f : n ⟶ k) :
    D.cArr n ≫ D.mapR f ≫ D.tArr k = D.pArr n ≫ D.mapR f ≫ D.tArr k :=
  D.comp_mapR_tArr f (D.cArr_comp_tArr n)

/-- After a transition morphism, the source of the arrow applied second is the target of the
arrow applied first. -/
theorem pArr_sArr_mapR {n k : Over i₀} (f : n ⟶ k) :
    D.pArr n ≫ D.mapR f ≫ D.sArr k = D.qArr n ≫ D.mapR f ≫ D.tArr k :=
  D.comp_mapR_sArr_tArr f (D.isPullback_pArr' n).w

/-- After a transition morphism, the composite arrow has the source of the arrow applied first. -/
theorem cArr_sArr_mapR {n k : Over i₀} (f : n ⟶ k) :
    D.cArr n ≫ D.mapR f ≫ D.sArr k = D.qArr n ≫ D.mapR f ≫ D.sArr k :=
  D.comp_mapR_sArr f (D.cArr_comp_sArr n)

/-- For `g` at the limit lying over `g'` at the stage `n`, the target of `g`, projected to the
stage `k`, is the target of `g'` transported along `f : n ⟶ k`. -/
theorem arrc_πU_t {n k : Over i₀} (f : n ⟶ k)
    {g : schemeSpace (productChartCone X₀ T i₀ D.a₂ c).pt ⟶
      schemeSpace (productChartCone X₀ T i₀ D.a₁ c).pt}
    {g' : schemeSpace ((productChartSystem X₀ T i₀ D.a₂).obj n) ⟶
      schemeSpace ((productChartSystem X₀ T i₀ D.a₁).obj n)}
    (hg : D.πK c n ≫ g' = g ≫ D.πR c n) :
    (g ≫ D.tArrc c) ≫ D.πU c k = (D.πK c n ≫ g') ≫ D.mapR f ≫ D.tArr k := by
  rw [Category.assoc, D.tArrc_πU c f, hg, Category.assoc]

/-- For `g` at the limit lying over `g'` at the stage `n`, the source of `g`, projected to the
stage `k`, is the source of `g'` transported along `f : n ⟶ k`. -/
theorem arrc_πU_s {n k : Over i₀} (f : n ⟶ k)
    {g : schemeSpace (productChartCone X₀ T i₀ D.a₂ c).pt ⟶
      schemeSpace (productChartCone X₀ T i₀ D.a₁ c).pt}
    {g' : schemeSpace ((productChartSystem X₀ T i₀ D.a₂).obj n) ⟶
      schemeSpace ((productChartSystem X₀ T i₀ D.a₁).obj n)}
    (hg : D.πK c n ≫ g' = g ≫ D.πR c n) :
    (g ≫ D.sArrc c) ≫ D.πU c k = (D.πK c n ≫ g') ≫ D.mapR f ≫ D.sArr k := by
  rw [Category.assoc, D.sArrc_πU c f, hg, Category.assoc]

/-- The target and the source of a morphism into the arrows of the limit agree after the chart. -/
theorem arrc_chartc (g : schemeSpace (productChartCone X₀ T i₀ D.a₂ c).pt ⟶
      schemeSpace (productChartCone X₀ T i₀ D.a₁ c).pt) :
    (g ≫ D.tArrc c) ≫ D.chartc c = (g ≫ D.sArrc c) ≫ D.chartc c := by
  rw [Category.assoc, Category.assoc, tArrc_comp_chartc]

/-- **The cocycle condition holds at a stage** (Stacks 01ZR (3)): a morphism on the arrows of a
stage whose inverse image to the arrows of the limit is a transported descent datum satisfies
the cocycle condition at the composable pairs of a later stage. -/
theorem exists_transitionCocycle [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    {G : Modules.{u, u} B S hS (productSpace X₀ c.pt).1 (productSpace X₀ c.pt).2} {k₁ : Over i₀}
    {M : Modules.{u, u} B S hS (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k₁)).1
      (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k₁)).2}
    (hM : M.IsQuasicoherentOnSite) (hMfp : M.IsFinitePresentationOnSite)
    (ι : (modulePullback B S hS (D.πU c k₁)).obj M ≅ (modulePullback B S hS (D.chartc c)).obj G)
    {n : Over i₀} (f : n ⟶ k₁)
    (α : (modulePullback B S hS (D.mapR f ≫ D.tArr k₁)).obj M ⟶
      (modulePullback B S hS (D.mapR f ≫ D.sArr k₁)).obj M)
    (hα : modulePullbackReindex (D.πR c n) α = descentTransport (D.πU c k₁) (D.chartc c) ι
      (D.tArrc_πU c f) (D.sArrc_πU c f) (D.tArrc_comp_chartc c)) :
    ∃ (n' : Over i₀) (e : n' ⟶ n), TransitionCocycle B S hS M α (D.mapK e ≫ D.pArr n)
      (D.mapK e ≫ D.qArr n) (D.mapK e ≫ D.cArr n) := by
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj D.K₀) := D.compactK
  have hlim : ∀ (g : schemeSpace (productChartCone X₀ T i₀ D.a₂ c).pt ⟶
      schemeSpace (productChartCone X₀ T i₀ D.a₁ c).pt)
      (g' : schemeSpace ((productChartSystem X₀ T i₀ D.a₂).obj n) ⟶
        schemeSpace ((productChartSystem X₀ T i₀ D.a₁).obj n))
      (hg : D.πK c n ≫ g' = g ≫ D.πR c n),
      modulePullbackReindex (D.πK c n ≫ g') α = descentTransport (D.πU c k₁) (D.chartc c) ι
        (D.arrc_πU_t c f hg) (D.arrc_πU_s c f hg) (D.arrc_chartc c g) := fun g g' hg =>
    modulePullbackReindex_eq_descentTransport_of (π := D.πU c k₁) (u := D.chartc c)
      (x := D.tArrc c) (y := D.sArrc c) (x' := g ≫ D.tArrc c) (y' := g ≫ D.sArrc c) ι α
      (D.πR c n) (D.tArrc_πU c f) (D.sArrc_πU c f) (D.tArrc_comp_chartc c) hα g
      (D.πK c n ≫ g') hg.symm rfl rfl (D.arrc_πU_t c f hg) (D.arrc_πU_s c f hg) (D.arrc_chartc c g)
  have hcoc := transitionCocycle_of_descentTransport (π := D.πU c k₁) (u := D.chartc c) ι α
    (D.πK c n ≫ D.pArr n) (D.πK c n ≫ D.qArr n) (D.πK c n ≫ D.cArr n)
    (D.arrc_πU_t c f (D.πK_pArr c n)) (D.arrc_πU_s c f (D.πK_pArr c n)) (D.arrc_chartc c _)
    (D.arrc_πU_t c f (D.πK_qArr c n)) (D.arrc_πU_s c f (D.πK_qArr c n)) (D.arrc_chartc c _)
    (D.arrc_πU_t c f (D.πK_cArr c n)) (D.arrc_πU_s c f (D.πK_cArr c n)) (D.arrc_chartc c _)
    (hlim _ _ (D.πK_pArr c n)) (hlim _ _ (D.πK_qArr c n)) (hlim _ _ (D.πK_cArr c n))
    (D.cArrc_comp_tArrc c) (D.pArrc_comp_sArrc c) (D.cArrc_comp_sArrc c)
  have hK := TransitionCocycle.transitionReindex_eq M α (D.cArr_tArr_mapR f) (D.pArr_sArr_mapR f)
    (D.cArr_sArr_mapR f) (D.πK c n) hcoc
  obtain ⟨n', e, he⟩ := exists_modulePullbackReindex_eq_of_isLimit hc D.a₂ n hM hMfp
    ((transitionReindex_eq_modulePullbackReindex M _ (D.πK c n)).symm.trans
      (hK.trans (transitionReindex_eq_modulePullbackReindex M _ (D.πK c n))))
  refine ⟨n', e, TransitionCocycle.of_transitionReindex_eq M α (D.cArr_tArr_mapR f)
    (D.pArr_sArr_mapR f) (D.cArr_sArr_mapR f) (D.mapK e) ?_⟩
  exact (transitionReindex_eq_modulePullbackReindex M _ (D.mapK e)).trans
    (he.trans (transitionReindex_eq_modulePullbackReindex M _ (D.mapK e)).symm)

/-! ### Comparison at the limit -/

/-- The chart of the limit is étale. -/
theorem isEtale_chartc : IsEtale B S hS (D.chartc c).hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS _).2 (productChartMap_etale X₀ D.etale (V := c.pt)
    (c.π.app i₀))

/-- **The module at a stage descends the module on the limit**: if `𝒩` on `h_{T F} ⨯ X₀` has, on
the chart `U_F`, the descent datum of `ℳ` given by `α`, then the inverse image of `𝒩` to the limit
is isomorphic to `𝒢` (Stacks 04W6, 04W5). -/
theorem nonempty_modulePullback_iso_of_descentTransport
    {G : Modules.{u, u} B S hS (productSpace X₀ c.pt).1 (productSpace X₀ c.pt).2} {k₁ : Over i₀}
    {M : Modules.{u, u} B S hS (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k₁)).1
      (schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k₁)).2}
    (ι : (modulePullback B S hS (D.πU c k₁)).obj M ≅ (modulePullback B S hS (D.chartc c)).obj G)
    {n : Over i₀} (f : n ⟶ k₁)
    (α : (modulePullback B S hS (D.mapR f ≫ D.tArr k₁)).obj M ⟶
      (modulePullback B S hS (D.mapR f ≫ D.sArr k₁)).obj M)
    (hα : modulePullbackReindex (D.πR c n) α = descentTransport (D.πU c k₁) (D.chartc c) ι
      (D.tArrc_πU c f) (D.sArrc_πU c f) (D.tArrc_comp_chartc c))
    {F : Over i₀} (μ : F ⟶ n)
    {N : Modules.{u, u} B S hS (productSpace X₀ (T.obj F.left)).1
      (productSpace X₀ (T.obj F.left)).2}
    (ιF : (modulePullback B S hS (D.mapU (μ ≫ f))).obj M ≅
      (modulePullback B S hS (D.chart T i₀ F)).obj N)
    (haF : D.tArr F ≫ D.mapU (μ ≫ f) = D.mapR μ ≫ D.mapR f ≫ D.tArr k₁)
    (hbF : D.sArr F ≫ D.mapU (μ ≫ f) = D.mapR μ ≫ D.mapR f ≫ D.sArr k₁)
    (hF : modulePullbackReindex (D.mapR μ) α = descentTransport (D.mapU (μ ≫ f))
      (D.chart T i₀ F) ιF haF hbF (D.isPullback_tArr' F).w) :
    Nonempty ((modulePullback B S hS (productSpaceConeMap X₀ T c F.left)).obj N ≅ G) := by
  have ha₁ : (D.πR c F ≫ D.tArr F) ≫ D.mapU (μ ≫ f) = D.πR c n ≫ D.mapR f ≫ D.tArr k₁ := by
    rw [Category.assoc, haF, ← Category.assoc, πR_mapR]
  have hb₁ : (D.πR c F ≫ D.sArr F) ≫ D.mapU (μ ≫ f) = D.πR c n ≫ D.mapR f ≫ D.sArr k₁ := by
    rw [Category.assoc, hbF, ← Category.assoc, πR_mapR]
  have h₁ : (D.πR c F ≫ D.tArr F) ≫ D.chart T i₀ F = (D.πR c F ≫ D.sArr F) ≫ D.chart T i₀ F := by
    rw [Category.assoc, Category.assoc, (D.isPullback_tArr' F).w]
  have hR := modulePullbackReindex_eq_descentTransport_of (π := D.mapU (μ ≫ f))
    (u := D.chart T i₀ F) (x := D.tArr F) (y := D.sArr F) (x' := D.πR c F ≫ D.tArr F)
    (y' := D.πR c F ≫ D.sArr F) ιF α (D.mapR μ) haF hbF (D.isPullback_tArr' F).w hF
    (D.πR c F) (D.πR c n) (D.πR_mapR c μ) rfl rfl ha₁ hb₁ h₁
  have ha₂ : (D.tArrc c ≫ D.πU c F) ≫ D.mapU (μ ≫ f) = D.πR c n ≫ D.mapR f ≫ D.tArr k₁ := by
    rw [← D.πR_tArr c F, ha₁]
  have hb₂ : (D.sArrc c ≫ D.πU c F) ≫ D.mapU (μ ≫ f) = D.πR c n ≫ D.mapR f ≫ D.sArr k₁ := by
    rw [← D.πR_sArr c F, hb₁]
  have h₂ : (D.tArrc c ≫ D.πU c F) ≫ D.chart T i₀ F = (D.sArrc c ≫ D.πU c F) ≫ D.chart T i₀ F := by
    rw [← D.πR_tArr c F, ← D.πR_sArr c F, h₁]
  rw [descentTransport_congr (π := D.mapU (μ ≫ f)) (u := D.chart T i₀ F) ιF ha₁ hb₁ h₁
    (D.πR_tArr c F) (D.πR_sArr c F) ha₂ hb₂ h₂] at hR
  have ha₃ : D.tArrc c ≫ D.πU c F ≫ D.mapU (μ ≫ f) = D.πR c n ≫ D.mapR f ≫ D.tArr k₁ := by
    rw [← Category.assoc, ha₂]
  have hb₃ : D.sArrc c ≫ D.πU c F ≫ D.mapU (μ ≫ f) = D.πR c n ≫ D.mapR f ≫ D.sArr k₁ := by
    rw [← Category.assoc, hb₂]
  have h₃ : D.tArrc c ≫ D.πU c F ≫ D.chart T i₀ F = D.sArrc c ≫ D.πU c F ≫ D.chart T i₀ F := by
    rw [← Category.assoc, h₂, Category.assoc]
  rw [descentTransport_comp_left (π := D.mapU (μ ≫ f)) (u := D.chart T i₀ F) ιF (D.πU c F)
    (x₁ := D.tArrc c) (y₁ := D.sArrc c) rfl rfl ha₂ hb₂ h₂ ha₃ hb₃ h₃] at hR
  have hπ : D.πU c F ≫ D.mapU (μ ≫ f) = D.πU c k₁ := D.πU_mapU c (μ ≫ f)
  rw [descentTransport_congr_left (π := D.πU c F ≫ D.mapU (μ ≫ f)) (π' := D.πU c k₁)
    (u := D.πU c F ≫ D.chart T i₀ F) hπ hπ.symm (modulePullbackReindexIso (D.πU c F) ιF) ha₃ hb₃ h₃
    (D.tArrc_πU c f) (D.sArrc_πU c f)
    (congrArg (D.tArrc c ≫ ·) hπ.symm) (congrArg (D.sArrc c ≫ ·) hπ)] at hR
  have hu : D.πU c F ≫ D.chart T i₀ F = D.chartc c ≫ productSpaceConeMap X₀ T c F.left :=
    D.πU_chart c F
  have h₅ : D.tArrc c ≫ D.chartc c ≫ productSpaceConeMap X₀ T c F.left =
      D.sArrc c ≫ D.chartc c ≫ productSpaceConeMap X₀ T c F.left := by
    rw [← Category.assoc, tArrc_comp_chartc, Category.assoc]
  rw [descentTransport_congr_right (π := D.πU c k₁) (u := D.πU c F ≫ D.chart T i₀ F)
    (u' := D.chartc c ≫ productSpaceConeMap X₀ T c F.left) hu hu.symm
    (pullbackTransportIso M hπ.symm ≪≫ modulePullbackReindexIso (D.πU c F) ιF) (D.tArrc_πU c f)
    (D.sArrc_πU c f) h₃ h₅ (congrArg (D.tArrc c ≫ ·) hu) (congrArg (D.sArrc c ≫ ·) hu.symm)] at hR
  rw [descentTransport_comp_right (π := D.πU c k₁) (D.chartc c) (productSpaceConeMap X₀ T c F.left)
    ((pullbackTransportIso M hπ.symm ≪≫ modulePullbackReindexIso (D.πU c F) ιF) ≪≫
      pullbackTransportIso N hu) (D.tArrc_πU c f) (D.sArrc_πU c f) h₅ (D.tArrc_comp_chartc c)
    (by rw [tArrc_comp_chartc]) (Category.assoc _ _ _).symm
    (Category.assoc _ _ _)] at hR
  obtain ⟨e⟩ := nonempty_iso_of_descentTransportCore_eq (D.chartc c) (D.isEtale_chartc c)
    (relativelyRepresentable_of_isAlgebraicSpace B S hS (productSpace X₀ c.pt).2 _)
    (isEtaleCovering_productChartConeSpaceMap X₀ T i₀ D.a₀ c D.etale D.surjective)
    (D.isPullback_tArrc c) (D.πU c k₁) ι _ (D.tArrc_comp_chartc c)
    (descentTransportCore_eq_of_descentTransport_eq (D.πU c k₁) (D.chartc c) _ _
      (D.tArrc_πU c f) (D.sArrc_πU c f) (D.tArrc_comp_chartc c) (hα.symm.trans hR))
  exact ⟨e.symm⟩

/-! ### Assembly -/

/-- The target of the arrows of the stage `F` followed by the transition `μ ≫ f` of the charts
is the transition `μ`, then `f`, of the arrows, followed by the target. -/
theorem tArr_mapU_comp {F n k : Over i₀} (μ : F ⟶ n) (f : n ⟶ k) :
    D.tArr F ≫ D.mapU (μ ≫ f) = D.mapR μ ≫ D.mapR f ≫ D.tArr k := by
  rw [← mapR_tArr, mapR_comp, Category.assoc]

/-- The source of the arrows of the stage `F` followed by the transition `μ ≫ f` of the charts
is the transition `μ`, then `f`, of the arrows, followed by the source. -/
theorem sArr_mapU_comp {F n k : Over i₀} (μ : F ⟶ n) (f : n ⟶ k) :
    D.sArr F ≫ D.mapU (μ ≫ f) = D.mapR μ ≫ D.mapR f ≫ D.sArr k := by
  rw [← mapR_sArr, mapR_comp, Category.assoc]

include D in
/-- **Stacks 07V7, objects, for a presentation**: a quasi-coherent module of finite presentation
on the limit `h_{c.pt} ⨯ X₀` is the inverse image of a quasi-coherent module of finite
presentation on some stage `h_{T j} ⨯ X₀`. -/
theorem exists_modulePullback_iso [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))]
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (hZ : B.Contains (⊤_ Scheme.{u}))
    (G : Modules.{u, u} B S hS (productSpace X₀ c.pt).1 (productSpace X₀ c.pt).2)
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite) :
    ∃ (F : Over i₀) (N : Modules.{u, u} B S hS (productSpace X₀ (T.obj F.left)).1
        (productSpace X₀ (T.obj F.left)).2),
      N.IsQuasicoherentOnSite ∧ N.IsFinitePresentationOnSite ∧
        Nonempty ((modulePullback B S hS (productSpaceConeMap X₀ T c F.left)).obj N ≅ G) := by
  obtain ⟨k₁, M, hM, hMfp, ι, n, f, α, hα⟩ := D.exists_descentTransport c hc hZ G hG hGfp
  obtain ⟨n', e', hunit⟩ := D.exists_transitionUnit c hc hM hMfp ι f α hα
  obtain ⟨n'', e'', hcoc⟩ := D.exists_transitionCocycle c hc hM hMfp ι f α hα
  obtain ⟨F, g₁, g₂, hg⟩ := IsCofiltered.cospan e' e''
  have ht := kernelPairGroupoid_target (D.chart T i₀ F) (D.isPullback_tArr F)
  have hs := kernelPairGroupoid_source (D.chart T i₀ F) (D.isPullback_tArr F)
  have ha : (D.groupoid F).target ≫ D.mapU ((g₁ ≫ e') ≫ f) =
      D.mapR (g₁ ≫ e') ≫ D.mapR f ≫ D.tArr k₁ :=
    (congrArg (· ≫ D.mapU ((g₁ ≫ e') ≫ f)) ht).trans (D.tArr_mapU_comp (g₁ ≫ e') f)
  have hb : D.mapR (g₁ ≫ e') ≫ D.mapR f ≫ D.sArr k₁ =
      (D.groupoid F).source ≫ D.mapU ((g₁ ≫ e') ≫ f) :=
    (D.sArr_mapU_comp (g₁ ≫ e') f).symm.trans (congrArg (· ≫ D.mapU ((g₁ ≫ e') ≫ f)) hs.symm)
  have hcocΓ : TransitionCocycle B S hS M α
      (firstArrow (D.groupoid F) ≫ D.mapR (g₁ ≫ e'))
      (secondArrow (D.groupoid F) ≫ D.mapR (g₁ ≫ e'))
      ((D.groupoid F).comp ≫ D.mapR (g₁ ≫ e')) := by
    refine TransitionCocycle.comp B S hS M α ?_ ?_ ?_ hcoc (D.composableSection F ≫ D.mapK g₂)
      ?_ ?_ ?_
    · rw [Category.assoc, Category.assoc, D.cArr_tArr_mapR f]
    · rw [Category.assoc, Category.assoc, D.pArr_sArr_mapR f]
    · rw [Category.assoc, Category.assoc, D.cArr_sArr_mapR f]
    · rw [Category.assoc, ← Category.assoc (D.mapK g₂), ← mapK_comp, ← hg, mapK_pArr,
        ← Category.assoc, composableSection_pArr]
      rfl
    · rw [Category.assoc, ← Category.assoc (D.mapK g₂), ← mapK_comp, ← hg, mapK_qArr,
        ← Category.assoc, composableSection_qArr]
      rfl
    · rw [Category.assoc, ← Category.assoc (D.mapK g₂), ← mapK_comp, ← hg, mapK_cArr,
        ← Category.assoc, composableSection_cArr]
      rfl
  have hunitΓ : TransitionUnit B S hS M α (identityArrow (D.groupoid F) ≫ D.mapR (g₁ ≫ e')) := by
    refine TransitionUnit.comp B S hS M α ?_ hunit (D.mapU g₁) ?_
    · rw [Category.assoc, Category.assoc, D.diag_tArr_mapU f, D.diag_sArr_mapU f]
    · rw [← Category.assoc, ← mapU_comp, mapU_diag, identityArrow_groupoid]
      rfl
  have hφet := isEtale_productChartSpaceMap X₀ T i₀ D.a₀ D.etale F
  have hcov := isEtaleCovering_productChartSpaceMap X₀ T i₀ D.a₀ D.etale D.surjective F
  have hφ := kernelPairGroupoid_target_comp_source (D.chart T i₀ F) (D.isPullback_tArr F)
  obtain ⟨𝓕, ⟨eF⟩⟩ := exists_spaceBaseObj_iso B S hS (D.groupoid F) (D.chart T i₀ F) hφet hφ hcov
    (relativelyRepresentable_of_isAlgebraicSpace B S hS (productSpace X₀ (T.obj F.left)).2 _)
    (isPullback_kernelPairGroupoid (D.chart T i₀ F) (D.isPullback_tArr F))
    (quasicoherentModuleOfReindex (D.groupoid F) (D.mapU ((g₁ ≫ e') ≫ f)) M α
      (D.mapR (g₁ ≫ e')) ha hb hM hcocΓ hunitΓ)
  let ιF := reindexSpaceBaseIso (D.groupoid F) (D.chart T i₀ F) hφ 𝓕.obj 𝓕.property
    (D.mapU ((g₁ ≫ e') ≫ f)) M hM α (D.mapR (g₁ ≫ e')) ha hb hcocΓ hunitΓ eF
  have hF₀ := modulePullbackReindex_eq_descentTransport_of_iso (D.groupoid F) (D.chart T i₀ F)
    hφ 𝓕.obj 𝓕.property (D.mapU ((g₁ ≫ e') ≫ f)) M hM α (D.mapR (g₁ ≫ e')) ha hb hcocΓ
    hunitΓ eF hb.symm
  have hF : modulePullbackReindex (D.mapR (g₁ ≫ e')) α = descentTransport
      (D.mapU ((g₁ ≫ e') ≫ f)) (D.chart T i₀ F) ιF (D.tArr_mapU_comp (g₁ ≫ e') f)
      (D.sArr_mapU_comp (g₁ ≫ e') f) (D.isPullback_tArr' F).w :=
    hF₀.trans (descentTransport_congr (π := D.mapU ((g₁ ≫ e') ≫ f)) (u := D.chart T i₀ F) ιF ha
      hb.symm hφ ht hs (D.tArr_mapU_comp (g₁ ≫ e') f) (D.sArr_mapU_comp (g₁ ≫ e') f)
      (D.isPullback_tArr' F).w)
  refine ⟨F, 𝓕.obj, 𝓕.property, ?_,
    D.nonempty_modulePullback_iso_of_descentTransport c ι f α hα (g₁ ≫ e') ιF
      (D.tArr_mapU_comp (g₁ ≫ e') f) (D.sArr_mapU_comp (g₁ ≫ e') f) hF⟩
  exact isFinitePresentationOnSite_of_modulePullback B S hS (D.chart T i₀ F) hφet
    (isSurjective_of_isEtaleCovering_single B S hS (D.groupoid F) (D.chart T i₀ F) hcov) 𝓕.obj
    (SheafOfModules.IsFinitePresentationOnSite.of_iso ιF
      (isFinitePresentationOnSite_modulePullback B S hS _ M hMfp))

end ProductChartData

/-- **Stacks 07V7, objects**, for the limit situation `h_{T j} ⨯ X₀`: for a cofiltered system `T`
of affine schemes over `S` whose underlying schemes have the limit `c`, and `h_{T i₀} ⨯ X₀`
quasi-compact and quasi-separated, a quasi-coherent module of finite presentation on
`h_{c.pt} ⨯ X₀` is the inverse image of a quasi-coherent module of finite presentation on some
`h_{T j} ⨯ X₀`, `j ⟶ i₀`. -/
theorem exists_modulePullback_productSpaceConeMap_iso [IsCofiltered I]
    [∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T.obj i))] (X₀ : AlgebraicSpaces B S hS)
    (c : Cone T) (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c)) (i₀ : I)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS (productSpace X₀ (T.obj i₀)).1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (productSpace X₀ (T.obj i₀)).1)
    (G : Modules.{u, u} B S hS (productSpace X₀ c.pt).1 (productSpace X₀ c.pt).2)
    (hG : G.IsQuasicoherentOnSite) (hGfp : G.IsFinitePresentationOnSite) :
    ∃ (j : I) (_ : j ⟶ i₀) (N : Modules.{u, u} B S hS (productSpace X₀ (T.obj j)).1
        (productSpace X₀ (T.obj j)).2),
      N.IsQuasicoherentOnSite ∧ N.IsFinitePresentationOnSite ∧
        Nonempty ((modulePullback B S hS (productSpaceConeMap X₀ T c j)).obj N ≅ G) := by
  obtain ⟨D⟩ := nonempty_productChartData X₀ T i₀ hZ hqc hqs
  obtain ⟨F, N, hN, hNfp, hiso⟩ := D.exists_modulePullback_iso c hc hZ G hG hGfp
  exact ⟨F.left, F.hom, N, hN, hNfp, hiso⟩

end AlgebraicGeometry.Space

end
