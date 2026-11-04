module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupEtaleChartTransfer
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.IdealSheafLocallyFiniteProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ProjHyperplane
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism

/-!
# The codimension of a smooth centre, and the twisting divisor `Σ (c - 1) E_c`

Let `i : Z ⟶ X` be a closed immersion of schemes smooth over `S` and `b : X' ⟶ X` the blowup of
`X` along `Z`. The centre decomposes as `Z = ∐ Z_c`, where `Z_c` is the open and closed part on
which `Z` has codimension `c` in `X`. We define the codimension function and the divisor
`Σ (c - 1) E_c` of `X'`, where `E_c = b⁻¹(Z_c)`.

## Main definitions

* `Stacks.DeRham.centreCodim f i : Z → ℕ`: the codimension of `Z` in `X` at a point, which is
  the codimension `n` of any étale chart through it.
* `Stacks.DeRham.centrePiece f i c`: the open and closed piece `Z_c ⊆ Z` of codimension `c`, and
  `Stacks.DeRham.centrePieceIdeal f i c` its ideal sheaf on `X`.
* `Stacks.DeRham.blowupTwistDivisor f i`: the twisting divisor `Σ_c (c - 1)E_c` on the blowup,
  the locally finite product of the ideal sheaves `(ℐ_{Z_c}^{c-1})·𝒪_{X'}`.

## Main results

* `Stacks.DeRham.BlowupEtaleChart.fiberDimension_eq` and
  `Stacks.DeRham.BlowupEtaleChart.centreFiberDimension_eq`: on a chart the fibres of `X` and of
  `Z` over `S` have local dimensions `m + n` and `m`.
* `Stacks.DeRham.BlowupEtaleChart.centreCodim_eq`: the codimension is the `n` of every chart.
* `Stacks.DeRham.isEffectiveCartierDivisor_blowupTwistDivisor`: the twisting divisor is an
  effective Cartier divisor.
* `Stacks.DeRham.BlowupEtaleChart.comap_blowupTwistDivisor`: on a chart the twisting divisor is
  the pullback of `(n - 1)E` from the coordinate blowup.
* `Stacks.DeRham.comap_blowupTwistDivisor_of_disjoint`: off the centre the twisting divisor is
  empty.

## References

* [Stacks Project, Tag 0G5J](https://stacks.math.columbia.edu/tag/0G5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DeRham

/-- The coordinate affine space `𝐀^{m+n}_R ⟶ Spec R` is smooth of relative dimension `m + n`. -/
theorem smoothOfRelativeDimension_coordinateAmbientToBase (R : Type u) [CommRing R] (m n : ℕ) :
    SmoothOfRelativeDimension (m + n) (coordinateAmbientToBase R m n) := by
  let e : MvPolynomial (Fin (m + n)) R ≃ₐ[R] MvPolynomial (Fin m ⊕ Fin n) R :=
    MvPolynomial.renameEquiv R finSumFinEquiv.symm
  have h := smoothOfRelativeDimension_specMap_C R (m + n)
  have he : coordinateAmbientToBase R m n =
      Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin (m + n)) (R := R))) := by
    rw [← Spec.map_comp]
    change Spec.map _ = _
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
    simp [e]
  rw [he]
  have : IsIso (Spec.map (CommRingCat.ofHom e.toRingEquiv.toRingHom)) :=
    inferInstanceAs (IsIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom))
  exact SmoothOfRelativeDimension.etale_comp (m + n) _ _

variable {S X Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

namespace BlowupEtaleChart

variable (c : BlowupEtaleChart f i)

/-- On a chart, `U ⟶ S` is smooth of relative dimension `m + n`. -/
theorem smoothOfRelativeDimension_ι_comp :
    SmoothOfRelativeDimension (c.m + c.n) (c.U.ι ≫ f) := by
  rw [← c.comm]
  have := smoothOfRelativeDimension_coordinateAmbientToBase c.R c.m c.n
  have : SmoothOfRelativeDimension (c.m + c.n) (coordinateAmbientToBase c.R c.m c.n ≫ c.base) :=
    SmoothOfRelativeDimension.comp_relativeDimension_zero _ _ _
  exact SmoothOfRelativeDimension.etale_comp _ _ _

/-- **On a chart the fibre of `X ⟶ S` has local dimension `m + n`.** -/
theorem fiberDimension_eq {x : X} (hx : x ∈ c.U) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = ((c.m + c.n : ℕ) : WithBot ℕ∞) := by
  have := c.smoothOfRelativeDimension_ι_comp
  exact (fiberDimensionAt_comp_openImmersion c.U.ι f ⟨x, hx⟩).symm.trans
    (fiberDimensionAt_eq_of_smoothOfRelativeDimension (c.U.ι ≫ f) (c.m + c.n) ⟨x, hx⟩)

/-- The coordinate subspace maps to the base as relative affine `m`-space. -/
theorem coordinateEmbedding_comp_toBase :
    Stacks.MoreMorphisms.coordinateEmbedding c.R c.m c.n ≫ coordinateAmbientToBase c.R c.m c.n =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin c.m) (R := c.R))) := by
  rw [Stacks.MoreMorphisms.coordinateEmbedding, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun r ↦ ?_)
  simp [Stacks.MoreMorphisms.coordinateProjection]

/-- **On a chart the fibre of `Z ⟶ S` has local dimension `m`.** -/
theorem centreFiberDimension_eq [IsClosedImmersion i] {z : Z} (hz : i z ∈ c.U) :
    topologicalKrullDimAt ((i ≫ f).fiber ((i ≫ f) z)) ((i ≫ f).asFiber z) =
      ((c.m : ℕ) : WithBot ℕ∞) := by
  have hcomp : (i ⁻¹ᵁ c.U).ι ≫ i ≫ f = c.centreMap ≫
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin c.m) (R := c.R))) ≫ c.base) := by
    rw [← c.coordinateEmbedding_comp_toBase]
    calc (i ⁻¹ᵁ c.U).ι ≫ i ≫ f = ((i ∣_ c.U) ≫ c.U.ι) ≫ f := by
          rw [morphismRestrict_ι, Category.assoc]
      _ = (i ∣_ c.U) ≫ (c.g ≫ coordinateAmbientToBase c.R c.m c.n ≫ c.base) := by
          rw [c.comm, Category.assoc]
      _ = _ := by rw [← Category.assoc _ c.g, ← c.centreMap_comm]; simp only [Category.assoc]
  have := smoothOfRelativeDimension_specMap_C c.R c.m
  have : SmoothOfRelativeDimension c.m
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin c.m) (R := c.R))) ≫ c.base) :=
    SmoothOfRelativeDimension.comp_relativeDimension_zero _ _ _
  have : SmoothOfRelativeDimension c.m ((i ⁻¹ᵁ c.U).ι ≫ i ≫ f) := by
    rw [hcomp]
    exact SmoothOfRelativeDimension.etale_comp _ _ _
  exact (fiberDimensionAt_comp_openImmersion (i ⁻¹ᵁ c.U).ι (i ≫ f) ⟨z, hz⟩).symm.trans
    (fiberDimensionAt_eq_of_smoothOfRelativeDimension ((i ⁻¹ᵁ c.U).ι ≫ i ≫ f) c.m ⟨z, hz⟩)

end BlowupEtaleChart

open Classical in
/-- The codimension of the centre at a point `z`: the codimension `n` of an étale chart through
`i z`, and `0` if there is none. -/
def centreCodim (f : X ⟶ S) (i : Z ⟶ X) (z : Z) : ℕ :=
  if h : ∃ c : BlowupEtaleChart f i, i z ∈ c.U then h.choose.n else 0

/-- The codimension of the centre at a point is the `n` of every chart through it. -/
theorem BlowupEtaleChart.centreCodim_eq [IsClosedImmersion i] (c : BlowupEtaleChart f i) {z : Z}
    (hz : i z ∈ c.U) : centreCodim f i z = c.n := by
  have h : ∃ c : BlowupEtaleChart f i, i z ∈ c.U := ⟨c, hz⟩
  rw [centreCodim, dite_eq_left h]
  have h₁ := (h.choose.fiberDimension_eq h.choose_spec).symm.trans (c.fiberDimension_eq hz)
  have h₂ := (h.choose.centreFiberDimension_eq h.choose_spec).symm.trans
    (c.centreFiberDimension_eq hz)
  have e₁ : h.choose.m + h.choose.n = c.m + c.n := by exact_mod_cast h₁
  have e₂ : h.choose.m = c.m := by exact_mod_cast h₂
  omega

/-! ### The pieces `Z_c` of the centre of fixed codimension -/

section Pieces

variable (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)]

/-- The codimension of the centre is locally constant. -/
theorem isOpen_setOf_centreCodim (p : ℕ → Prop) : IsOpen {z : Z | p (centreCodim f i z)} := by
  refine isOpen_iff_forall_mem_open.mpr fun z hz ↦ ?_
  obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
  refine ⟨i ⁻¹ᵁ c.U, fun w hw ↦ ?_, (i ⁻¹ᵁ c.U).isOpen, hzc⟩
  change p (centreCodim f i w)
  rw [c.centreCodim_eq hw, ← c.centreCodim_eq hzc]
  exact hz

/-- The piece `Z_c ⊆ Z` on which the centre has codimension `c`, an open and closed subscheme. -/
def centrePiece (k : ℕ) : Z.Opens :=
  ⟨{z | centreCodim f i z = k}, isOpen_setOf_centreCodim f i (· = k)⟩

/-- The piece `Z_c` of the centre is closed in `Z`. -/
theorem isClosed_centrePiece (k : ℕ) : IsClosed (centrePiece f i k : Set Z) :=
  isOpen_compl_iff.mp (isOpen_setOf_centreCodim f i (· ≠ k))

/-- The inclusion of the piece `Z_c` into `Z` is a closed immersion. -/
instance isClosedImmersion_centrePiece_ι (k : ℕ) : IsClosedImmersion (centrePiece f i k).ι :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_centrePiece f i k)

/-- The ideal sheaf on `X` of the piece `Z_c` of the centre of codimension `c`. -/
def centrePieceIdeal (k : ℕ) : X.IdealSheafData :=
  ((centrePiece f i k).ι ≫ i).ker

/-- On an affine open whose trace on `Z` lies in `Z_c`, the ideal of `Z_c` is that of `Z`. -/
theorem ideal_centrePieceIdeal_of_le {k : ℕ} (U : X.affineOpens)
    (hU : i ⁻¹ᵁ (U : X.Opens) ≤ centrePiece f i k) :
    (centrePieceIdeal f i k).ideal U = i.ker.ideal U := by
  rw [centrePieceIdeal, Scheme.Hom.ker_apply, Scheme.Hom.ker_apply]
  change RingHom.ker (((centrePiece f i k).ι.app (i ⁻¹ᵁ (U : X.Opens))).hom.comp
    (i.app U).hom) = _
  refine RingHom.ker_comp_of_injective _ ?_
  rw [Scheme.Opens.ι_app]
  have himg : (centrePiece f i k).ι ''ᵁ (centrePiece f i k).ι ⁻¹ᵁ (i ⁻¹ᵁ (U : X.Opens)) =
      i ⁻¹ᵁ (U : X.Opens) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hU
  have key : ∀ {A B : Z.Opens} (h : A ≤ B), A = B →
      Function.Injective (Z.presheaf.map (homOfLE h).op).hom := by
    rintro A B h rfl
    rw [show (homOfLE h).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    exact fun a b hab ↦ hab
  exact key _ himg

/-- Off the piece `Z_c` its ideal sheaf is the unit ideal. -/
theorem comap_centrePieceIdeal_eq_top {k : ℕ} (V : X.Opens)
    (hV : i ⁻¹ᵁ V ⊓ centrePiece f i k = ⊥) :
    (centrePieceIdeal f i k).comap V.ι = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_comap]
  ext x
  simp only [TopologicalSpace.Closeds.coe_preimage, Set.mem_preimage,
    TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hx
  have hx' : V.ι x ∈ ((centrePieceIdeal f i k).support : Set X) := hx
  rw [centrePieceIdeal, Scheme.Hom.support_ker,
    ((centrePiece f i k).ι ≫ i).isClosedEmbedding.isClosed_range.closure_eq] at hx'
  obtain ⟨w, hw⟩ := hx'
  have hmem : ((centrePiece f i k).ι w : Z) ∈ (i ⁻¹ᵁ V ⊓ centrePiece f i k : Z.Opens) := by
    refine ⟨?_, ?_⟩
    · change ((centrePiece f i k).ι ≫ i) w ∈ V
      rw [hw]
      exact x.2
    · rw [← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
  rwa [hV] at hmem

/-- On an open whose trace on `Z` lies in `Z_c`, the ideal of `Z_c` is that of `Z`. -/
theorem comap_centrePieceIdeal_of_le {k : ℕ} (V : X.Opens) (hV : i ⁻¹ᵁ V ≤ centrePiece f i k) :
    (centrePieceIdeal f i k).comap V.ι = i.ker.comap V.ι := by
  ext W : 2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, ideal_centrePieceIdeal_of_le]
  exact (Scheme.Hom.preimage_mono i (V.ι.image_le_opensRange W |>.trans
    (by rw [Scheme.Opens.opensRange_ι]))).trans hV

/-- The summand `(c - 1)E_c` of the twisting divisor, as an ideal sheaf on the blowup: the inverse
image of the `(c - 1)`-st power of the ideal of `Z_c`. -/
def twistSummand (k : ℕ) : (blowUp i.ker).IdealSheafData :=
  (centrePieceIdeal f i k ^ (k - 1)).comap (blowUpToBase i.ker)

/-- Over an open of `X`, the summand is computed from the ideal of `Z_c` restricted there. -/
theorem comap_twistSummand (k : ℕ) (V : X.Opens) :
    (twistSummand f i k).comap (blowUpToBase i.ker ⁻¹ᵁ V).ι =
      (((centrePieceIdeal f i k).comap V.ι) ^ (k - 1)).comap (blowUpToBase i.ker ∣_ V) := by
  rw [twistSummand, ← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι,
    Scheme.IdealSheafData.comap_comp, Stacks.IdealSheaf.comap_pow]

/-- Over an open of `X` whose trace on `Z` misses `Z_c`, the summand `(c - 1)E_c` is the unit
ideal. -/
theorem comap_twistSummand_eq_top {k : ℕ} (V : X.Opens) (hV : i ⁻¹ᵁ V ⊓ centrePiece f i k = ⊥) :
    (twistSummand f i k).comap (blowUpToBase i.ker ⁻¹ᵁ V).ι = ⊤ := by
  rw [comap_twistSummand, comap_centrePieceIdeal_eq_top f i V hV,
    ← Scheme.IdealSheafData.one_eq_top, one_pow, Scheme.IdealSheafData.one_eq_top,
    Scheme.IdealSheafData.comap_top]

/-- A point whose image lies in the support of an ideal sheaf cannot have the inverse image of that
ideal sheaf equal to the unit ideal. -/
private theorem not_mem_support_of_comap_eq_top {Y W : Scheme.{u}} {I : Y.IdealSheafData}
    (g : W ⟶ Y) (h : I.comap g = ⊤) (w : W) : g w ∉ (I.support : Set Y) := fun hw ↦ by
  have hw' : w ∈ (((I.comap g).support : TopologicalSpace.Closeds W) : Set W) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hw
  rw [h, Scheme.IdealSheafData.support_top] at hw'
  exact hw'

/-- An ideal sheaf whose inverse image along an open immersion is the unit ideal has support
disjoint from the open. -/
theorem disjoint_support_of_comap_ι_eq_top {Y : Scheme.{u}} {I : Y.IdealSheafData} {W : Y.Opens}
    (h : I.comap W.ι = ⊤) : Disjoint (W : Set Y) (I.support : Set Y) :=
  Set.disjoint_left.mpr fun y hyW ↦ not_mem_support_of_comap_eq_top W.ι h ⟨y, hyW⟩

/-- Every point of `X` has an open neighbourhood whose trace on `Z` meets at most one piece
`Z_c`. -/
theorem exists_open_inf_centrePiece_eq_bot (x : X) :
    ∃ (V : X.Opens) (k₀ : ℕ), x ∈ V ∧ ∀ k ≠ k₀, i ⁻¹ᵁ V ⊓ centrePiece f i k = ⊥ := by
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
    exact ⟨c.U, c.n, hzc, fun k hk ↦ eq_bot_iff.mpr fun w hw ↦
      hk ((hw.2 : centreCodim f i w = k).symm.trans (c.centreCodim_eq hw.1))⟩
  · refine ⟨⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩, 0, hx,
      fun k _ ↦ eq_bot_iff.mpr fun w hw ↦ hw.1 ⟨w, rfl⟩⟩

/-- The supports of the summands `(c - 1)E_c` form a locally finite family in the blowup. -/
theorem locallyFinite_support_twistSummand :
    LocallyFinite fun k => ((twistSummand f i k).support : Set (blowUp i.ker)) := by
  intro y
  obtain ⟨V, k₀, hxV, hV⟩ := exists_open_inf_centrePiece_eq_bot f i (blowUpToBase i.ker y)
  refine ⟨blowUpToBase i.ker ⁻¹ᵁ V, ((blowUpToBase i.ker ⁻¹ᵁ V).isOpen.mem_nhds hxV),
    (Set.finite_singleton k₀).subset fun k hk ↦ ?_⟩
  by_contra hne
  obtain ⟨w, hw, hwV⟩ := hk
  exact Set.disjoint_left.mp (disjoint_support_of_comap_ι_eq_top
    (comap_twistSummand_eq_top f i V (hV k hne))) hwV hw

/-- The twisting divisor `𝒟 = Σ_c (c - 1)E_c` on the blowup `X'` of `X` along `Z`, where
`E_c = b⁻¹(Z_c)` is the part of the exceptional divisor over the piece `Z_c` of the centre of
codimension `c`. It is the locally finite product of the ideal sheaves `(ℐ_{Z_c}^{c-1})·𝒪_{X'}`. -/
def blowupTwistDivisor : (blowUp i.ker).IdealSheafData :=
  Scheme.IdealSheafData.locallyFiniteProd (twistSummand f i)
    (locallyFinite_support_twistSummand f i)

/-- The product of a locally finite family whose members all pull back to the unit ideal pulls
back to the unit ideal. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_locallyFiniteProd_eq_top
    {Y W : Scheme.{u}} {ι : Type*} (F : ι → Y.IdealSheafData)
    (hF : LocallyFinite fun k => ((F k).support : Set Y)) (g : W ⟶ Y)
    (h : ∀ k, (F k).comap g = ⊤) :
    (Scheme.IdealSheafData.locallyFiniteProd F hF).comap g = ⊤ := by
  rw [← Scheme.IdealSheafData.support_eq_bot_iff]
  ext w
  simp only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Set.mem_preimage, TopologicalSpace.Closeds.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hw
  have hw' : g w ∈ ((Scheme.IdealSheafData.locallyFiniteProd F hF).support : Set Y) := hw
  rw [Scheme.IdealSheafData.coe_support_locallyFiniteProd, Set.mem_iUnion] at hw'
  obtain ⟨k, hk⟩ := hw'
  exact not_mem_support_of_comap_eq_top g (h k) w hk

/-- The product of a locally finite family pulls back to the pullback of one member, if all the
others pull back to the unit ideal. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.comap_locallyFiniteProd_of_eq_top
    {Y W : Scheme.{u}} {ι : Type*} (F : ι → Y.IdealSheafData)
    (hF : LocallyFinite fun k => ((F k).support : Set Y)) (g : W ⟶ Y) (k₀ : ι)
    (h : ∀ k ≠ k₀, (F k).comap g = ⊤) :
    (Scheme.IdealSheafData.locallyFiniteProd F hF).comap g = (F k₀).comap g := by
  classical
  rw [Scheme.IdealSheafData.locallyFiniteProd_eq_mul F hF k₀, Stacks.IdealSheaf.comap_mul,
    Scheme.IdealSheafData.comap_locallyFiniteProd_eq_top _ _ g fun k ↦ ?_,
    ← Scheme.IdealSheafData.one_eq_top, mul_one]
  by_cases hk : k = k₀
  · subst hk
    rw [Function.update_self, Scheme.IdealSheafData.comap_top]
  · rw [Function.update_of_ne hk, h k hk]

/-- Over an open of `X` disjoint from the centre, the twisting divisor is empty. -/
theorem comap_blowupTwistDivisor_of_disjoint (V : X.Opens) (hV : i ⁻¹ᵁ V = ⊥) :
    (blowupTwistDivisor f i).comap (blowUpToBase i.ker ⁻¹ᵁ V).ι = ⊤ :=
  Scheme.IdealSheafData.comap_locallyFiniteProd_eq_top _ _ _ fun k ↦
    comap_twistSummand_eq_top f i V (by rw [hV, bot_inf_eq])

variable {f i} in
/-- On a chart, the twisting divisor is `(n - 1)` times the exceptional divisor of the coordinate
blowup, pulled back along the chart. -/
theorem BlowupEtaleChart.comap_blowupTwistDivisor (c : BlowupEtaleChart f i) :
    (blowupTwistDivisor f i).comap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι =
      (coordinateExceptional c.R c.m c.n ^ (c.n - 1)).comap c.blowupMap := by
  have hle : i ⁻¹ᵁ c.U ≤ centrePiece f i c.n := fun w hw ↦ c.centreCodim_eq hw
  rw [blowupTwistDivisor, Scheme.IdealSheafData.comap_locallyFiniteProd_of_eq_top _ _ _ c.n
      fun k hk ↦ comap_twistSummand_eq_top f i c.U (eq_bot_iff.mpr fun w hw ↦ hk ?_),
    comap_twistSummand, comap_centrePieceIdeal_of_le f i c.U hle, c.ker_comap,
    ← Stacks.IdealSheaf.comap_pow, ← Scheme.IdealSheafData.comap_comp, c.blowupMap_comm,
    Scheme.IdealSheafData.comap_comp, Stacks.IdealSheaf.comap_pow]
  exact (hw.2 : centreCodim f i w = k).symm.trans (c.centreCodim_eq hw.1)

variable {f i} in
/-- On a chart, the twisting divisor is `(n - 1)` times the exceptional divisor of `b`. -/
theorem BlowupEtaleChart.comap_blowupTwistDivisor_eq_exceptionalIdeal_pow
    (c : BlowupEtaleChart f i) :
    (blowupTwistDivisor f i).comap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι =
      (exceptionalIdeal i.ker ^ (c.n - 1)).comap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι := by
  rw [c.comap_blowupTwistDivisor, Stacks.IdealSheaf.comap_pow, Stacks.IdealSheaf.comap_pow,
    c.comap_exceptionalIdeal]

/-- The twisting divisor is an effective Cartier divisor. -/
instance isEffectiveCartierDivisor_blowupTwistDivisor :
    Stacks.Divisors.IsEffectiveCartierDivisor (blowupTwistDivisor f i) := by
  let V₀ : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  let W : Option (BlowupEtaleChart f i) → (blowUp i.ker).Opens := fun
    | none => blowUpToBase i.ker ⁻¹ᵁ V₀
    | some c => blowUpToBase i.ker ⁻¹ᵁ c.U
  refine Stacks.Chow.GenuineChern.isEffectiveCartierDivisor_of_comap (fun o ↦ (W o).ι) ?_ _
    fun o ↦ ?_
  · refine eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ?_
    by_cases hx : blowUpToBase i.ker y ∈ Set.range i.base
    · obtain ⟨z, hz⟩ := hx
      obtain ⟨c, hzc, -⟩ := exists_blowupEtaleChart f i z ⊤ trivial
      refine ⟨some c, ?_⟩
      change y ∈ (blowUpToBase i.ker ⁻¹ᵁ c.U).ι.opensRange
      rw [Scheme.Opens.opensRange_ι]
      change blowUpToBase i.ker y ∈ c.U
      rwa [← hz]
    · refine ⟨none, ?_⟩
      change y ∈ (blowUpToBase i.ker ⁻¹ᵁ V₀).ι.opensRange
      rw [Scheme.Opens.opensRange_ι]
      exact hx
  · cases o with
    | none =>
      change Stacks.Divisors.IsEffectiveCartierDivisor
        ((blowupTwistDivisor f i).comap (blowUpToBase i.ker ⁻¹ᵁ V₀).ι)
      rw [comap_blowupTwistDivisor_of_disjoint f i V₀
        (eq_bot_iff.mpr fun w hw ↦ hw ⟨w, rfl⟩)]
      exact Stacks.Divisors.isEffectiveCartierDivisor_top
    | some c =>
      change Stacks.Divisors.IsEffectiveCartierDivisor
        ((blowupTwistDivisor f i).comap (blowUpToBase i.ker ⁻¹ᵁ c.U).ι)
      rw [c.comap_blowupTwistDivisor_eq_exceptionalIdeal_pow]
      exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
        (Stacks.Divisors.isEffectiveCartierDivisor_pow
          (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) _) _

end Pieces

end Stacks.DeRham

end
