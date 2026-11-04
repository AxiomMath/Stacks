module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.KernelPairGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductChartPresentation

/-!
# The groupoids of the presentations of base changes along a limit

Given presentation data `(U₀, R₀, K₀)` of `h_{T i₀} ⨯ X₀`
(`AlgebraicGeometry.Space.ProductChartData`), their base changes along `T j ⟶ T i₀` present
`h_{T j} ⨯ X₀`: the chart `U_j ⟶ h_{T j} ⨯ X₀` has kernel pair `R_j`, the groupoid of that
kernel pair (Stacks 043Y) has composable pairs `K_j`, and the composite of a composable pair is
the base change of the composite at `i₀`.

## Main definitions

* `AlgebraicGeometry.Space.ProductChartData.groupoid`: the kernel-pair groupoid at a stage.
* `AlgebraicGeometry.Space.ProductChartData.composableSection`: the composable pairs of the
  groupoid, read in the scheme `K_j`.

## Main results

* `AlgebraicGeometry.Space.ProductChartData.composableSection_cArr`: read in `K_j`, the
  composition of the groupoid is the base change of the composite at `i₀`.
* `AlgebraicGeometry.Space.ProductChartData.identityArrow_groupoid`: the identity arrows of the
  groupoid are the diagonal of the kernel pair.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X₀ : AlgebraicSpaces B S hS)

/-- `productChartPairMap` is unchanged when `g` is replaced by an equal morphism. -/
theorem productChartPairMap_congr {T₀ U₀ R₀ : BigFppfOver B S hS}
    (a₀ : yoneda.obj U₀ ⟶ (productSpace X₀ T₀).1) {g g' : R₀ ⟶ U₀} (hgg : g = g')
    (a₁ : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (h : yoneda.map g ≫ a₀ = a₁)
    (h' : yoneda.map g' ≫ a₀ = a₁) {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    productChartPairMap X₀ a₀ g a₁ h k = productChartPairMap X₀ a₀ g' a₁ h' k := by
  subst hgg
  rfl

/-- The morphisms of base changes induced by `g₁` and by `g₀` compose to the one induced by
`g₁ ≫ g₀`. -/
theorem productChartPairMap_comp_productChartPairMap {T₀ U₀ R₀ K₀ : BigFppfOver B S hS}
    (a₀ : yoneda.obj U₀ ⟶ (productSpace X₀ T₀).1) (g₀ : R₀ ⟶ U₀)
    (a₁ : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (h₀ : yoneda.map g₀ ≫ a₀ = a₁) (g₁ : K₀ ⟶ R₀)
    (a₂ : yoneda.obj K₀ ⟶ (productSpace X₀ T₀).1) (h₁ : yoneda.map g₁ ≫ a₁ = a₂)
    (h : yoneda.map (g₁ ≫ g₀) ≫ a₀ = a₂) {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    productChartPairMap X₀ a₁ g₁ a₂ h₁ k ≫ productChartPairMap X₀ a₀ g₀ a₁ h₀ k =
      productChartPairMap X₀ a₀ (g₁ ≫ g₀) a₂ h k := by
  apply pullback.hom_ext
  · simp only [productChartPairMap, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [productChartPairMap, Category.assoc, pullback.lift_snd, Category.comp_id]

namespace ProductChartData

variable {X₀} {I : Type u} [Category.{u} I] {T : I ⥤ BigFppfOver B S hS} {i₀ : I}
  (D : ProductChartData X₀ T i₀)

/-- The base of the kernel pair. -/
abbrev a₁ : yoneda.obj D.R₀ ⟶ (productSpace X₀ (T.obj i₀)).1 := yoneda.map D.t₀ ≫ D.a₀

/-- The chart composed with the source of the kernel pair is also `a₁`. -/
theorem s_a₁ : yoneda.map D.s₀ ≫ D.a₀ = D.a₁ := D.isPullback.w.symm

/-- The base of the composable pairs. -/
abbrev a₂ : yoneda.obj D.K₀ ⟶ (productSpace X₀ (T.obj i₀)).1 := yoneda.map D.p₀ ≫ D.a₁

/-- The chart composed with `p₀ ≫ t₀` is `a₂`. -/
theorem pt_a₂ : yoneda.map (D.p₀ ≫ D.t₀) ≫ D.a₀ = D.a₂ :=
  (congrArg (· ≫ D.a₀) (yoneda.map_comp D.p₀ D.t₀)).trans (Category.assoc _ _ _)

/-- The arrow applied first, followed by `a₁`, is also `a₂`. -/
theorem q_a₂ : yoneda.map D.q₀ ≫ D.a₁ = D.a₂ := by
  simp only [a₂, a₁, ← Category.assoc, ← Functor.map_comp]
  rw [← D.isPullbackK.w, Functor.map_comp, Category.assoc, D.s_a₁]
  exact D.pt_a₂.symm

/-- The composite arrow, followed by `a₁`, is also `a₂`. -/
theorem c_a₂ : yoneda.map D.c₀ ≫ D.a₁ = D.a₂ := by
  simp only [a₂, a₁, ← Category.assoc, ← Functor.map_comp, D.c₀_t]

/-- The chart composed with `c₀ ≫ t₀` is `a₂`. -/
theorem ct_a₂ : yoneda.map (D.c₀ ≫ D.t₀) ≫ D.a₀ = D.a₂ := by
  rw [D.c₀_t, D.pt_a₂]

/-- The chart composed with `c₀ ≫ s₀` is `a₂`. -/
theorem cs_a₂ : yoneda.map (D.c₀ ≫ D.s₀) ≫ D.a₀ = D.a₂ := by
  rw [Functor.map_comp, Category.assoc, D.s_a₁, D.c_a₂]

/-- The chart composed with `q₀ ≫ s₀` is `a₂`. -/
theorem qs_a₂ : yoneda.map (D.q₀ ≫ D.s₀) ≫ D.a₀ = D.a₂ := by
  rw [Functor.map_comp, Category.assoc, D.s_a₁, D.q_a₂]

variable (T i₀) in
/-- The chart of a stage. -/
abbrev chart (k : Over i₀) := productChartSpaceMap X₀ T i₀ D.a₀ k

/-- The target of the arrows at a stage. -/
abbrev tArr (k : Over i₀) := productChartSpacePairMap X₀ T i₀ D.a₀ D.t₀ D.a₁ rfl k

/-- The source of the arrows at a stage. -/
abbrev sArr (k : Over i₀) := productChartSpacePairMap X₀ T i₀ D.a₀ D.s₀ D.a₁ D.s_a₁ k

/-- The arrow applied second, at a stage. -/
abbrev pArr (k : Over i₀) := productChartSpacePairMap X₀ T i₀ D.a₁ D.p₀ D.a₂ rfl k

/-- The arrow applied first, at a stage. -/
abbrev qArr (k : Over i₀) := productChartSpacePairMap X₀ T i₀ D.a₁ D.q₀ D.a₂ D.q_a₂ k

/-- The composite arrow, at a stage. -/
abbrev cArr (k : Over i₀) := productChartSpacePairMap X₀ T i₀ D.a₁ D.c₀ D.a₂ D.c_a₂ k

/-- At every stage the target and source arrows form a kernel pair of the chart, on the underlying
presheaves. -/
theorem isPullback_tArr (k : Over i₀) :
    IsPullback (D.tArr k).hom (D.sArr k).hom (D.chart T i₀ k).hom (D.chart T i₀ k).hom :=
  isPullback_productChartSpacePairMap X₀ T i₀ D.a₀ D.a₁ D.isPullback rfl D.s_a₁ k

/-- At every stage the composable pairs are the fibre product of the source and the target arrows,
on the underlying presheaves. -/
theorem isPullback_pArr (k : Over i₀) :
    IsPullback (D.pArr k).hom (D.qArr k).hom (D.sArr k).hom (D.tArr k).hom :=
  (isPullback_productChartPairMap_of_isPullback X₀ D.a₀ D.isPullbackK D.a₁ D.s_a₁ D.a₁ rfl
    D.a₂ rfl D.q_a₂ (T.map k.hom)).map yoneda

/-- At every stage the target and source arrows form a kernel pair of the chart. -/
theorem isPullback_tArr' (k : Over i₀) :
    IsPullback (D.tArr k) (D.sArr k) (D.chart T i₀ k) (D.chart T i₀ k) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) (D.isPullback_tArr k)

/-- At every stage the composable pairs are the fibre product of the source and the target
arrows. -/
theorem isPullback_pArr' (k : Over i₀) :
    IsPullback (D.pArr k) (D.qArr k) (D.sArr k) (D.tArr k) :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) (D.isPullback_pArr k)

/-- Two arrows into `R₀` with the same composite with `g₀` induce the same composite of morphisms
of charts. -/
private theorem pairMap_comp_eq (g₀ : D.R₀ ⟶ D.U₀) (hg₀ : yoneda.map g₀ ≫ D.a₀ = D.a₁)
    (g₁ g₁' : D.K₀ ⟶ D.R₀) (h₁ : yoneda.map g₁ ≫ D.a₁ = D.a₂)
    (h₁' : yoneda.map g₁' ≫ D.a₁ = D.a₂) (e : g₁ ≫ g₀ = g₁' ≫ g₀) (k : Over i₀) :
    productChartSpacePairMap X₀ T i₀ D.a₁ g₁ D.a₂ h₁ k ≫
        productChartSpacePairMap X₀ T i₀ D.a₀ g₀ D.a₁ hg₀ k =
      productChartSpacePairMap X₀ T i₀ D.a₁ g₁' D.a₂ h₁' k ≫
        productChartSpacePairMap X₀ T i₀ D.a₀ g₀ D.a₁ hg₀ k := by
  have h : yoneda.map (g₁ ≫ g₀) ≫ D.a₀ = D.a₂ := by rw [Functor.map_comp, Category.assoc, hg₀, h₁]
  have h' : yoneda.map (g₁' ≫ g₀) ≫ D.a₀ = D.a₂ := by
    rw [Functor.map_comp, Category.assoc, hg₀, h₁']
  exact ObjectProperty.hom_ext _ ((yoneda.map_comp _ _).symm.trans
    ((congrArg yoneda.map ((productChartPairMap_comp_productChartPairMap X₀ D.a₀ g₀ D.a₁ hg₀
      g₁ D.a₂ h₁ h (T.map k.hom)).trans
      ((productChartPairMap_congr X₀ D.a₀ e D.a₂ h h' (T.map k.hom)).trans
        (productChartPairMap_comp_productChartPairMap X₀ D.a₀ g₀ D.a₁ hg₀
          g₁' D.a₂ h₁' h' (T.map k.hom)).symm))).trans (yoneda.map_comp _ _)))

/-- The composite arrow has the target of the arrow applied second. -/
theorem cArr_comp_tArr (k : Over i₀) : D.cArr k ≫ D.tArr k = D.pArr k ≫ D.tArr k :=
  D.pairMap_comp_eq D.t₀ rfl D.c₀ D.p₀ D.c_a₂ rfl D.c₀_t k

/-- The composite arrow has the source of the arrow applied first. -/
theorem cArr_comp_sArr (k : Over i₀) : D.cArr k ≫ D.sArr k = D.qArr k ≫ D.sArr k :=
  D.pairMap_comp_eq D.s₀ D.s_a₁ D.c₀ D.q₀ D.c_a₂ D.q_a₂ D.c₀_s k

/-- The kernel-pair groupoid of the chart of a stage (Stacks 043Y). -/
abbrev groupoid (k : Over i₀) : GroupoidInAlgebraicSpaces B S hS (productSpace X₀ (T.obj k.left)) :=
  kernelPairGroupoid (D.chart T i₀ k) (D.isPullback_tArr k)

/-- In a composable pair of the groupoid of a stage, the source of the first arrow is the target
of the second. -/
theorem firstArrow_comp_sArr (k : Over i₀) :
    GroupoidInAlgebraicSpaces.firstArrow (D.groupoid k) ≫ D.sArr k =
      GroupoidInAlgebraicSpaces.secondArrow (D.groupoid k) ≫ D.tArr k :=
  (congrArg (GroupoidInAlgebraicSpaces.firstArrow (D.groupoid k) ≫ ·)
    (kernelPairGroupoid_source (D.chart T i₀ k) (D.isPullback_tArr k)).symm).trans
    ((GroupoidInAlgebraicSpaces.firstArrow_comp_source (D.groupoid k)).trans
      (congrArg (GroupoidInAlgebraicSpaces.secondArrow (D.groupoid k) ≫ ·)
        (kernelPairGroupoid_target (D.chart T i₀ k) (D.isPullback_tArr k))))

/-- The composable pairs of the groupoid of a stage, read in `K_j`. -/
def composableSection (k : Over i₀) :
    AlgebraicSpaces.fiberProduct B S hS (D.groupoid k).source (D.groupoid k).target ⟶
      schemeSpace ((productChartSystem X₀ T i₀ D.a₂).obj k) :=
  (D.isPullback_pArr' k).lift (GroupoidInAlgebraicSpaces.firstArrow (D.groupoid k))
    (GroupoidInAlgebraicSpaces.secondArrow (D.groupoid k)) (D.firstArrow_comp_sArr k)

/-- `composableSection` followed by `pArr` is the first arrow of a composable pair. -/
theorem composableSection_pArr (k : Over i₀) :
    D.composableSection k ≫ D.pArr k = GroupoidInAlgebraicSpaces.firstArrow (D.groupoid k) :=
  (D.isPullback_pArr' k).lift_fst _ _ _

/-- `composableSection` followed by `qArr` is the second arrow of a composable pair. -/
theorem composableSection_qArr (k : Over i₀) :
    D.composableSection k ≫ D.qArr k = GroupoidInAlgebraicSpaces.secondArrow (D.groupoid k) :=
  (D.isPullback_pArr' k).lift_snd _ _ _

/-- `composableSection` followed by `cArr` is the composition of the groupoid of a stage. -/
theorem composableSection_cArr (k : Over i₀) :
    D.composableSection k ≫ D.cArr k = (D.groupoid k).comp := by
  have ht := kernelPairGroupoid_target (D.chart T i₀ k) (D.isPullback_tArr k)
  have hs := kernelPairGroupoid_source (D.chart T i₀ k) (D.isPullback_tArr k)
  apply (D.isPullback_tArr' k).hom_ext
  · refine ((Category.assoc _ _ _).trans ((congrArg (D.composableSection k ≫ ·)
      (D.cArr_comp_tArr k)).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ D.tArr k) (D.composableSection_pArr k))).trans ?_)))
    refine ((congrArg (GroupoidInAlgebraicSpaces.firstArrow (D.groupoid k) ≫ ·) ht.symm).trans
      ((GroupoidInAlgebraicSpaces.comp_comp_target (D.groupoid k)).symm.trans
        (congrArg ((D.groupoid k).comp ≫ ·) ht)))
  · refine ((Category.assoc _ _ _).trans ((congrArg (D.composableSection k ≫ ·)
      (D.cArr_comp_sArr k)).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ D.sArr k) (D.composableSection_qArr k))).trans ?_)))
    refine ((congrArg (GroupoidInAlgebraicSpaces.secondArrow (D.groupoid k) ≫ ·) hs.symm).trans
      ((GroupoidInAlgebraicSpaces.comp_comp_source (D.groupoid k)).symm.trans
        (congrArg ((D.groupoid k).comp ≫ ·) hs)))

/-- The diagonal of the kernel pair at a stage: the unit arrows. -/
def diag (k : Over i₀) :
    schemeSpace ((productChartSystem X₀ T i₀ D.a₀).obj k) ⟶
      schemeSpace ((productChartSystem X₀ T i₀ D.a₁).obj k) :=
  (D.isPullback_tArr' k).lift (𝟙 _) (𝟙 _) rfl

/-- The diagonal followed by the target arrow is the identity. -/
theorem diag_tArr (k : Over i₀) : D.diag k ≫ D.tArr k = 𝟙 _ :=
  (D.isPullback_tArr' k).lift_fst _ _ _

/-- The diagonal followed by the source arrow is the identity. -/
theorem diag_sArr (k : Over i₀) : D.diag k ≫ D.sArr k = 𝟙 _ :=
  (D.isPullback_tArr' k).lift_snd _ _ _

/-- The identity arrows of the groupoid of a stage are the diagonal of the kernel pair. -/
theorem identityArrow_groupoid (k : Over i₀) :
    GroupoidInAlgebraicSpaces.identityArrow (D.groupoid k) = D.diag k := by
  have ht := kernelPairGroupoid_target (D.chart T i₀ k) (D.isPullback_tArr k)
  have hs := kernelPairGroupoid_source (D.chart T i₀ k) (D.isPullback_tArr k)
  exact (D.isPullback_tArr' k).hom_ext
    (((congrArg (GroupoidInAlgebraicSpaces.identityArrow (D.groupoid k) ≫ ·) ht.symm).trans
      (GroupoidInAlgebraicSpaces.identityArrow_comp_target (D.groupoid k))).trans
        (D.diag_tArr k).symm)
    (((congrArg (GroupoidInAlgebraicSpaces.identityArrow (D.groupoid k) ≫ ·) hs.symm).trans
      (GroupoidInAlgebraicSpaces.identityArrow_comp_source (D.groupoid k))).trans
        (D.diag_sArr k).symm)

end ProductChartData

end AlgebraicGeometry.Space

end
