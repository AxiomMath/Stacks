module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeDoubledLine

/-!
# Hilbert families on the affine line with doubled points

Let `X` be two copies of `𝔸¹_S` glued along `𝔸¹_W` for an open `W ⊆ S`
(`Stacks.Hilbert.DoubledLine.doubledLine`). This file relates Hilbert families in `X` to
Hilbert families in the affine line over the two kinds of bases on which the charts of `X` are
well behaved.

* Over a base landing in `W` either chart is an isomorphism, so pulling back along the first chart
  identifies families in `X` with families in `𝔸¹`: `Stacks.Hilbert.DoubledLine.familyToLine`.
* Over a base landing outside `W` the charts are open and closed with complementary images, so a
  closed subscheme of `X` splits into its two chart pieces. Its degree is the sum of the degrees
  of the pieces over an affine base, `isFiniteLocallyFreeOfRank_of_charts`, and the pieces are
  finite, flat and of finite presentation as soon as the whole is,
  `finite_flat_lfp_of_isFiniteLocallyFreeOfRank`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Morphisms

universe u

namespace Stacks.Hilbert.DoubledLine

open AffineLine

variable {S : Scheme.{u}} (W : S.Opens)

/-- Pulling back along an isomorphism of ambient schemes preserves and reflects finite local
freeness of closed subschemes. -/
theorem isFiniteLocallyFreeOfRank_comap_iff_of_isIso {A B T : Scheme.{u}} (e : A ⟶ B) [IsIso e]
    (pA : A ⟶ T) (pB : B ⟶ T) (h : e ≫ pB = pA) (I : B.IdealSheafData) (d : ℕ) :
    IsFiniteLocallyFreeOfRank ((I.comap e).subschemeι ≫ pA) d ↔
      IsFiniteLocallyFreeOfRank (I.subschemeι ≫ pB) d := by
  have hfac : (I.comap e).subschemeι ≫ pA =
      (I.comapIso e).hom ≫ pullback.snd e I.subschemeι ≫ I.subschemeι ≫ pB := by
    rw [← Scheme.IdealSheafData.comapIso_hom_fst, ← h, Category.assoc,
      ← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc]
  rw [hfac, ← IsFiniteLocallyFreeOfRank.property_iff, ← IsFiniteLocallyFreeOfRank.property_iff,
    MorphismProperty.cancel_left_of_respectsIso (IsFiniteLocallyFreeOfRank.property d)
      (I.comapIso e).hom,
    MorphismProperty.cancel_left_of_respectsIso (IsFiniteLocallyFreeOfRank.property d)
      (pullback.snd e I.subschemeι)]

/-! ### Over a base landing in `W` -/

/-- **Over a base landing in `W`, families in `X` are families in the affine line**, by pulling
back along the first chart. -/
def familyToLine {V : Over S} (hV : ∀ v, V.hom v ∈ W) {d : ℕ}
    (D : HilbertFamily (doubledLine W) V d) : HilbertFamily (line S) V d where
  ideal := D.ideal.comap (chartT W V true)
  isFiniteLocallyFreeOfRank := by
    have := isIso_chartT W V hV true
    exact (isFiniteLocallyFreeOfRank_comap_iff_of_isIso _ _ _ (chartT_hom W V true) _ d).mpr
      D.isFiniteLocallyFreeOfRank

/-! ### Over a base landing outside `W` -/

variable (V : Over S)

/-- Over a base landing outside `W`, the image of the second chart is the complement of the image
of the first. -/
theorem range_chartT_false_eq_compl (hV : ∀ v, V.hom v ∉ W) :
    Set.range (chartT W V false) = (Set.range (chartT W V true))ᶜ := by
  have hc := isCompl_opensRange_chartT W V hV
  ext p
  refine ⟨fun hp hp' ↦ ?_, fun hp ↦ ?_⟩
  · have : p ∈ ((chartT W V true).opensRange ⊓ (chartT W V false).opensRange : (total W V).Opens) :=
      ⟨hp', hp⟩
    rwa [hc.inf_eq_bot] at this
  · have : p ∈ ((chartT W V true).opensRange ⊔ (chartT W V false).opensRange :
        (total W V).Opens) := by
      rw [hc.sup_eq_top]
      trivial
    rcases this with h | h
    exacts [absurd h hp, h]

/-- **Over a base landing outside `W` the charts are closed immersions.** -/
theorem isClosedImmersion_chartT (hV : ∀ v, V.hom v ∉ W) (b : Bool) :
    IsClosedImmersion (chartT W V b) := by
  refine isClosedImmersion_of_isOpenImmersion _ ?_
  have h := range_chartT_false_eq_compl W V hV
  cases b
  · rw [h]
    exact (chartT W V true).isOpenEmbedding.isOpen_range.isClosed_compl
  · rw [← compl_compl (Set.range (chartT W V true)), ← h]
    exact (chartT W V false).isOpenEmbedding.isOpen_range.isClosed_compl

variable {W V}

/-- The chart pieces of a closed subscheme of `X ×_S V`. -/
def subschemeChart (I : (total W V).IdealSheafData) (b : Bool) :
    (I.comap (chartT W V b)).subscheme ⟶ I.subscheme :=
  (I.comapIso (chartT W V b)).hom ≫ pullback.snd _ _

/-- The chart piece `subschemeChart I b` followed by the inclusion of `I.subscheme` is the
inclusion of the pulled-back subscheme followed by the chart `chartT W V b`. -/
theorem subschemeChart_subschemeι (I : (total W V).IdealSheafData) (b : Bool) :
    subschemeChart I b ≫ I.subschemeι = (I.comap (chartT W V b)).subschemeι ≫ chartT W V b := by
  rw [subschemeChart, Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- The chart piece `subschemeChart I b`, restricted to a larger closed subscheme `J`, followed by
the inclusion of `I.subscheme` is the inclusion of `J` followed by the chart `chartT W V b`. -/
private theorem inclusion_subschemeChart_subschemeι {I : (total W V).IdealSheafData}
    {J : (ambient V).IdealSheafData} {b : Bool}
    (hle : I.comap (chartT W V b) ≤ J) :
    (Scheme.IdealSheafData.inclusion hle ≫ subschemeChart I b) ≫ I.subschemeι =
      J.subschemeι ≫ chartT W V b := by
  rw [Category.assoc, subschemeChart_subschemeι, ← Category.assoc,
    Scheme.IdealSheafData.inclusion_subschemeι]

/-- The chart pieces of a closed subscheme are open immersions. -/
instance (I : (total W V).IdealSheafData) (b : Bool) : IsOpenImmersion (subschemeChart I b) := by
  unfold subschemeChart
  infer_instance

/-- The chart pieces of a closed subscheme are compatible with the structure morphisms to `V`. -/
theorem subschemeChart_hom (I : (total W V).IdealSheafData) (b : Bool) :
    subschemeChart I b ≫ I.subschemeι ≫ ((Over.pullback V.hom).obj (doubledLine W)).hom =
      (I.comap (chartT W V b)).subschemeι ≫ proj V := by
  rw [← Category.assoc, subschemeChart_subschemeι, Category.assoc, chartT_hom]

/-- The image of the chart piece `subschemeChart I b` is the inverse image in `I.subscheme` of the
image of the chart `chartT W V b`. -/
theorem range_subschemeChart (I : (total W V).IdealSheafData) (b : Bool) :
    Set.range (subschemeChart I b) = I.subschemeι ⁻¹' Set.range (chartT W V b) := by
  rw [subschemeChart, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    (ConcreteCategory.bijective_of_isIso (I.comapIso (chartT W V b)).hom.base).2.range_eq,
    Set.image_univ, Scheme.Pullback.range_snd]

/-- Over a base landing outside `W`, the images of the two chart pieces of a closed subscheme are
complementary opens. -/
theorem isCompl_opensRange_subschemeChart (hV : ∀ v, V.hom v ∉ W)
    (I : (total W V).IdealSheafData) :
    IsCompl (subschemeChart I true).opensRange (subschemeChart I false).opensRange := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff, ← TopologicalSpace.Opens.coe_inj,
    ← TopologicalSpace.Opens.coe_inj]
  simp only [TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_sup,
    Scheme.Hom.coe_opensRange, range_subschemeChart, range_chartT_false_eq_compl W V hV,
    Set.preimage_compl,
    Set.inter_compl_self, Set.union_compl_self, TopologicalSpace.Opens.coe_bot,
    TopologicalSpace.Opens.coe_top, and_self]

/-- Over a base landing outside `W`, the chart pieces of a closed subscheme are closed
immersions. -/
theorem isClosedImmersion_subschemeChart (hV : ∀ v, V.hom v ∉ W)
    (I : (total W V).IdealSheafData) (b : Bool) : IsClosedImmersion (subschemeChart I b) := by
  refine isClosedImmersion_of_isOpenImmersion _ ?_
  rw [range_subschemeChart]
  have := isClosedImmersion_chartT W V hV b
  exact (chartT W V b).isClosedEmbedding.isClosed_range.preimage I.subschemeι.continuous

/-- **The chart pieces of a family are finite, flat and of finite presentation.** -/
theorem finite_flat_lfp_of_isFiniteLocallyFreeOfRank (hV : ∀ v, V.hom v ∉ W)
    (I : (total W V).IdealSheafData) {d : ℕ}
    (hI : IsFiniteLocallyFreeOfRank (I.subschemeι ≫
      ((Over.pullback V.hom).obj (doubledLine W)).hom) d) (b : Bool) :
    IsFinite ((I.comap (chartT W V b)).subschemeι ≫ proj V) ∧
      Flat ((I.comap (chartT W V b)).subschemeι ≫ proj V) ∧
        LocallyOfFinitePresentation ((I.comap (chartT W V b)).subschemeι ≫ proj V) := by
  obtain ⟨hfin, hflat, hlfp⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mp
      (@IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ _ _ d hI)
  have := isClosedImmersion_subschemeChart hV I b
  rw [← subschemeChart_hom]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Degrees add up over the two charts.** Over an affine base landing outside `W`, a closed
subscheme of `X ×_S V` whose two chart pieces are finite locally free of ranks `r₁` and `r₂` is
finite locally free of rank `r₁ + r₂`. -/
theorem isFiniteLocallyFreeOfRank_of_charts (hV : ∀ v, V.hom v ∉ W) [IsAffine V.left]
    (I : (total W V).IdealSheafData) {r₁ r₂ : ℕ}
    (h₁ : IsFiniteLocallyFreeOfRank ((I.comap (chartT W V true)).subschemeι ≫ proj V) r₁)
    (h₂ : IsFiniteLocallyFreeOfRank ((I.comap (chartT W V false)).subschemeι ≫ proj V) r₂) :
    IsFiniteLocallyFreeOfRank (I.subschemeι ≫ ((Over.pullback V.hom).obj (doubledLine W)).hom)
      (r₁ + r₂) := by
  set κ := I.subschemeι ≫ ((Over.pullback V.hom).obj (doubledLine W)).hom with hκ
  set κ₁ := (I.comap (chartT W V true)).subschemeι ≫ proj V
  set κ₂ := (I.comap (chartT W V false)).subschemeι ≫ proj V
  have := isIso_coprod_desc_of_isCompl (subschemeChart I true) (subschemeChart I false)
    (isCompl_opensRange_subschemeChart hV I)
  have : IsAffine (I.comap (chartT W V true)).subscheme := isAffine_of_isAffineHom κ₁
  have : IsAffine (I.comap (chartT W V false)).subscheme := isAffine_of_isAffineHom κ₂
  have : IsAffine I.subscheme :=
    .of_isIso (inv (coprod.desc (subschemeChart I true) (subschemeChart I false)))
  have : IsAffineHom κ := isAffineHom_of_isAffine _
  let := κ.appTop.hom.toAlgebra
  let := κ₁.appTop.hom.toAlgebra
  let := κ₂.appTop.hom.toAlgebra
  have m₁ := (isFiniteLocallyFreeOfRank_iff_module_of_isAffine κ₁ r₁ rfl).mp h₁
  have m₂ := (isFiniteLocallyFreeOfRank_iff_module_of_isAffine κ₂ r₂ rfl).mp h₂
  have hcomp (b : Bool) : (subschemeChart I b).appTop.hom.comp κ.appTop.hom =
      ((I.comap (chartT W V b)).subschemeι ≫ proj V).appTop.hom := by
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hκ, subschemeChart_hom]
  let L : Γ(I.subscheme, ⊤) →ₗ[Γ(V.left, ⊤)]
      Γ((I.comap (chartT W V true)).subscheme, ⊤) × Γ((I.comap (chartT W V false)).subscheme, ⊤) :=
    { toFun := RingHom.prod (subschemeChart I true).appTop.hom (subschemeChart I false).appTop.hom
      map_add' := map_add _
      map_smul' := fun r x ↦ by
        simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
        ext
        · show _ * _ = κ₁.appTop r * _
          congr 1
          exact RingHom.congr_fun (hcomp true) r
        · show _ * _ = κ₂.appTop r * _
          congr 1
          exact RingHom.congr_fun (hcomp false) r }
  rw [isFiniteLocallyFreeOfRank_iff_module_of_isAffine κ (r₁ + r₂) rfl]
  exact (isFiniteLocallyFreeOfRank_prod m₁ m₂).of_linearEquiv (LinearEquiv.ofBijective L
    (bijective_prod_appTop (subschemeChart I true) (subschemeChart I false))).symm

end Stacks.Hilbert.DoubledLine

namespace Stacks.Hilbert.DoubledLine

open AffineLine

variable {S : Scheme.{u}} {W : S.Opens}

/-- **The charts agree over `W`**, for any two of them. -/
theorem comp_chartT_eq' {T : Over S} {V : Scheme.{u}} (h : V ⟶ ambient T)
    (hW : ∀ v, T.hom (proj T (h v)) ∈ W) (b b' : Bool) : h ≫ chartT W T b = h ≫ chartT W T b' := by
  have := comp_chartT_eq W T h hW
  cases b <;> cases b' <;> simp_all

/-- Over the inverse image of `W`, the two charts agree pointwise. -/
theorem chartT_apply_eq {T : Over S} (a : ambient T) (ha : T.hom (proj T a) ∈ W) (b b' : Bool) :
    chartT W T b a = chartT W T b' a := by
  let O : (ambient T).Opens := (proj T ≫ T.hom) ⁻¹ᵁ W
  exact congrArg (fun f ↦ f (⟨a, ha⟩ : O)) (comp_chartT_eq' O.ι (fun v ↦ v.2) b b')

/-- If two morphisms over `X` agree on an open `U`, then the induced map to the fibre product
sends `U` into the diagonal. -/
private theorem subset_preimage_range_diagonal {Z Y X : Scheme.{u}} {π : Y ⟶ X} {f g : Z ⟶ Y}
    (h : f ≫ π = g ≫ π) (U : Z.Opens) (hU : U.ι ≫ f = U.ι ≫ g) :
    (U : Set Z) ⊆ pullback.lift f g h ⁻¹' Set.range (pullback.diagonal π) := by
  intro z hz
  have hΨ : U.ι ≫ pullback.lift f g h = U.ι ≫ f ≫ pullback.diagonal π :=
    pullback.hom_ext (by simp [pullback.lift_fst]) (by simp [pullback.lift_snd, hU])
  exact ⟨f z, (congrArg (fun φ ↦ φ (⟨z, hz⟩ : U)) hΨ).symm⟩

/-- Two morphisms over `X` agree at a point which the induced map to the fibre product sends into
the diagonal. -/
private theorem apply_eq_of_mem_preimage_range_diagonal {Z Y X : Scheme.{u}} {π : Y ⟶ X}
    {f g : Z ⟶ Y} (h : f ≫ π = g ≫ π) {z : Z}
    (hz : z ∈ pullback.lift f g h ⁻¹' Set.range (pullback.diagonal π)) : f z = g z := by
  obtain ⟨k, hk⟩ := hz
  have e1 := congrArg (pullback.fst π π) hk
  have e2 := congrArg (pullback.snd π π) hk
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_fst,
    pullback.lift_fst] at e1
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.diagonal_snd,
    pullback.lift_snd] at e2
  exact e1.symm.trans e2

/-- For a closed subscheme of `X ×_S T` affine over `T`, the points of the union of two chart
pieces lying over `W` form a closed subset. -/
private theorem isClosed_setOf_mem_sup_comap_chartT {T : Over S} (I : (total W T).IdealSheafData)
    (b : Bool) [IsAffineHom (I.subschemeι ≫ ((Over.pullback T.hom).obj (doubledLine W)).hom)] :
    IsClosed {w : (I.comap (chartT W T b) ⊔ I.comap (chartT W T (!b))).subscheme |
      T.hom (proj T ((I.comap (chartT W T b) ⊔ I.comap (chartT W T (!b))).subschemeι w)) ∈ W} := by
  obtain ⟨π, hπdef⟩ : ∃ π, π = I.subschemeι ≫ ((Over.pullback T.hom).obj (doubledLine W)).hom :=
    ⟨_, rfl⟩
  have : IsAffineHom π := hπdef ▸ inferInstance
  set J := I.comap (chartT W T b) ⊔ I.comap (chartT W T (!b))
  have hψ (c : Bool) (hle : I.comap (chartT W T c) ≤ J) : ∃ ψ : J.subscheme ⟶ I.subscheme,
      ψ ≫ I.subschemeι = J.subschemeι ≫ chartT W T c :=
    ⟨_, inclusion_subschemeChart_subschemeι hle⟩
  obtain ⟨ψ₁, hψ₁⟩ := hψ b le_sup_left
  obtain ⟨ψ₂, hψ₂⟩ := hψ (!b) le_sup_right
  have hπ : ψ₁ ≫ π = ψ₂ ≫ π := by
    rw [hπdef, ← Category.assoc, hψ₁, ← Category.assoc, hψ₂, Category.assoc, Category.assoc,
      chartT_hom, chartT_hom]
  have hE : {w : J.subscheme | T.hom (proj T (J.subschemeι w)) ∈ W} =
      pullback.lift ψ₁ ψ₂ hπ ⁻¹' Set.range (pullback.diagonal π) := by
    ext w
    refine ⟨fun hw ↦ ?_, fun hw ↦ ?_⟩
    · let O : J.subscheme.Opens := (J.subschemeι ≫ proj T ≫ T.hom) ⁻¹ᵁ W
      have hO : O.ι ≫ ψ₁ = O.ι ≫ ψ₂ := by
        rw [← cancel_mono I.subschemeι, Category.assoc, Category.assoc, hψ₁, hψ₂,
          ← Category.assoc, ← Category.assoc]
        exact comp_chartT_eq' (T := T) (O.ι ≫ J.subschemeι) (fun v ↦ v.2) b (!b)
      exact subset_preimage_range_diagonal hπ O hO hw
    · have h₂ : chartT W T b (J.subschemeι w) = chartT W T (!b) (J.subschemeι w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hψ₁, ← hψ₂,
          Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
          apply_eq_of_mem_preimage_range_diagonal hπ hw]
      exact mem_of_chartT_eq W T (by cases b <;> decide) h₂
  rw [hE]
  exact (pullback.diagonal π).isClosedEmbedding.isClosed_range.preimage
    (pullback.lift ψ₁ ψ₂ hπ).continuous

/-- The points of a chart piece lying over `W` have the same image in `X ×_S T` as the points of
the union of the two chart pieces lying over `W`. -/
private theorem image_setOf_mem_comap_chartT_eq_sup {T : Over S} (I : (total W T).IdealSheafData)
    (b : Bool) :
    (I.comap (chartT W T b)).subschemeι ''
        {x | T.hom (proj T ((I.comap (chartT W T b)).subschemeι x)) ∈ W} =
      (I.comap (chartT W T b) ⊔ I.comap (chartT W T (!b))).subschemeι ''
        {w | T.hom (proj T
          ((I.comap (chartT W T b) ⊔ I.comap (chartT W T (!b))).subschemeι w)) ∈ W} := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hsupp₁ : (I.comap (chartT W T b)).subschemeι x ∈ (I.comap (chartT W T b)).support := by
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    have hsupp : (I.comap (chartT W T b)).subschemeι x ∈
        (I.comap (chartT W T b) ⊔ I.comap (chartT W T (!b))).support := by
      rw [Scheme.IdealSheafData.support_sup]
      refine ⟨hsupp₁, ?_⟩
      rw [Scheme.IdealSheafData.support_comap] at hsupp₁ ⊢
      show chartT W T (!b) _ ∈ I.support
      rwa [chartT_apply_eq _ hx (!b) b]
    rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι] at hsupp
    obtain ⟨w, hw⟩ := hsupp
    exact ⟨w, by rwa [Set.mem_ofPred_eq, hw], hw⟩
  · rintro ⟨w, hw, rfl⟩
    have hle₁ : I.comap (chartT W T b) ≤ I.comap (chartT W T b) ⊔ I.comap (chartT W T (!b)) :=
      le_sup_left
    have := Scheme.IdealSheafData.inclusion_subschemeι hle₁
    refine ⟨Scheme.IdealSheafData.inclusion hle₁ w, ?_, ?_⟩
    · show T.hom (proj T ((Scheme.IdealSheafData.inclusion hle₁ ≫
        (I.comap (chartT W T b)).subschemeι) w)) ∈ W
      rwa [this]
    · rw [← Scheme.Hom.comp_apply, this]

/-- For a finite locally free closed subscheme of `X ×_S T`, the points of a chart piece lying
over `W` form a closed subset. -/
theorem isClosed_subschemeChart_preimage {T : Over S} {d : ℕ}
    (I : (total W T).IdealSheafData) (b : Bool)
    (hI : IsFiniteLocallyFreeOfRank (I.subschemeι ≫
      ((Over.pullback T.hom).obj (doubledLine W)).hom) d) :
    IsClosed {x : (I.comap (chartT W T b)).subscheme |
      T.hom (proj T ((I.comap (chartT W T b)).subschemeι x)) ∈ W} := by
  have hclosed := (I.comap (chartT W T b) ⊔ I.comap (chartT W T (!b))).subschemeι.isClosedEmbedding
    |>.isClosedMap _ (isClosed_setOf_mem_sup_comap_chartT I b)
  rw [← image_setOf_mem_comap_chartT_eq_sup I b] at hclosed
  exact (I.comap (chartT W T b)).subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
    hclosed

end Stacks.Hilbert.DoubledLine

namespace Stacks.Hilbert.DoubledLine

open AffineLine

variable {S : Scheme.{u}} {W : S.Opens}

/-- A finite locally free morphism of positive rank is open and surjective. -/
theorem isOpenMap_surjective_of_isFiniteLocallyFreeOfRank {A T : Scheme.{u}} (p : A ⟶ T) {d : ℕ}
    (hd : 0 < d) [hp : IsFiniteLocallyFreeOfRank p d] :
    IsOpenMap p ∧ Function.Surjective p := by
  obtain ⟨hfin, hflat, hlfp⟩ :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).mp
      (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p d)
  refine ⟨p.isOpenMap, ?_⟩
  have hrank := (isFiniteLocallyFreeOfRank_iff_forall_finrank_eq p d).mp hp
  exact ((Scheme.Hom.one_le_finrank_iff_surjective p).mp fun t ↦ hrank t ▸ hd).surj

/-- **Families of positive degree split the base.** If a degree-`d` family in the doubled line
with `d ≥ 1` exists over an `S`-scheme `T`, then the inverse image of `W` in `T` is closed (it is
always open). -/
theorem isClosed_preimage_of_family {T : Over S} {d : ℕ} (hd : 0 < d)
    (D : HilbertFamily (doubledLine W) T d) : IsClosed (T.hom ⁻¹' (W : Set S)) := by
  have := D.isFiniteLocallyFreeOfRank
  obtain ⟨hopen, hsurj⟩ := isOpenMap_surjective_of_isFiniteLocallyFreeOfRank
    (D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj (doubledLine W)).hom) hd
  rw [← closure_subset_iff_isClosed]
  intro t ht
  obtain ⟨z, rfl⟩ := hsurj t
  obtain ⟨b, a, ha⟩ := exists_chartT_eq W T (D.ideal.subschemeι z)
  obtain ⟨y, rfl⟩ : z ∈ Set.range (subschemeChart D.ideal b) := by
    rw [range_subschemeChart]
    exact ⟨a, ha⟩
  have hcl := IsOpenMap.preimage_closure_subset_closure_preimage
    (subschemeChart D.ideal b).isOpenEmbedding.isOpenMap
    (hopen.preimage_closure_subset_closure_preimage ht)
  have hset : (subschemeChart D.ideal b) ⁻¹'
      ((D.ideal.subschemeι ≫ ((Over.pullback T.hom).obj (doubledLine W)).hom) ⁻¹'
        (T.hom ⁻¹' (W : Set S))) =
      {x | T.hom (proj T ((D.ideal.comap (chartT W T b)).subschemeι x)) ∈ W} := by
    ext x
    show T.hom ((subschemeChart D.ideal b ≫ D.ideal.subschemeι ≫
      ((Over.pullback T.hom).obj (doubledLine W)).hom) x) ∈ W ↔ _
    rw [subschemeChart_hom D.ideal b]
    rfl
  rwa [hset, (isClosed_subschemeChart_preimage D.ideal b D.isFiniteLocallyFreeOfRank).closure_eq,
    ← hset] at hcl

end Stacks.Hilbert.DoubledLine

end
