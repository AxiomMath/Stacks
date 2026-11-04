module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.DoubledOriginNotSeparated

/-!
# Base changes of the coordinate morphism of affine space with doubled origin

Let `X` be affine `n`-space over a field with its origin doubled, `Y` affine `n`-space, and
`f : X ⟶ Y` the coordinate morphism, which restricts to the identity on each of the two charts.
This file studies the base changes `P = U ×_Y X` of `f` along a morphism `h : U ⟶ Y`, presented
by an arbitrary pullback square, together with the two sections `U ⟶ P` determined by the two
charts.

## Main definitions

* `AlgebraicGeometry.chartSectionOfIsPullback`: the section of a base change of `f` determined
  by a chart.

## Main results

* `AlgebraicGeometry.coordinateMorphism_preimage_affineOrigin`: the fibre of `f` over the origin
  is exactly the pair of chart origins (Stacks 04QI).
* `AlgebraicGeometry.isPullback_chartSectionOfIsPullback`: each chart section is the base change
  of its chart inclusion, hence an open immersion, whose image is computed by
  `AlgebraicGeometry.range_chartSectionOfIsPullback`.
* `AlgebraicGeometry.isFinite_of_isPullback_of_forall_notMem`: if `h` maps every point to the
  origin, then `P ⟶ U` is finite, the two chart sections exhibiting `P` as two copies of `U`.
* `AlgebraicGeometry.exists_opens_forall_notMem_puncturedAffineSpace`: if an open subscheme of
  `P` finite over `U` contains the values of both chart sections at a point `u` over the origin,
  then a whole neighbourhood of `u` lies over the origin.

## Implementation notes

Everything is stated for an arbitrary pullback square rather than for Mathlib's chosen pullback.

## References

* [Stacks Project, Tag 04QI](https://stacks.math.columbia.edu/tag/04QI)
* [Stacks Project, Tag 01JD](https://stacks.math.columbia.edu/tag/01JD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (n : ℕ)

/-- The coordinate morphism restricted to a chart is the identity, read pointwise. -/
theorem coordinateMorphism_chartInclusion (i : Fin 2)
    (y : Spec (.of (MvPolynomial (Fin n) k))) :
    coordinateMorphism k n (chartInclusion k n i y) = y :=
  congrArg (fun g => g y) ((coordinateMorphismData k n).property i)

/-- The fibre of the coordinate morphism over the origin of affine space consists of exactly the
two chart origins. -/
theorem coordinateMorphism_preimage_affineOrigin :
    (coordinateMorphism k n).base ⁻¹' {affineOrigin k n} =
      {chartInclusion k n 0 (affineOrigin k n),
        chartInclusion k n 1 (affineOrigin k n)} := by
  refine subset_antisymm (fun x hx => ?_) ?_
  · obtain ⟨⟨i⟩, y, rfl⟩ := (doubledZeroGlueData k n).ι_jointly_surjective x
    have hy : y = affineOrigin k n := by
      have := coordinateMorphism_chartInclusion k n i y
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      exact this.symm.trans hx
    subst hy
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro x (rfl | rfl) <;>
      simpa [Set.mem_preimage] using coordinateMorphism_chartInclusion k n _ (affineOrigin k n)

/-- The complement of the origin in affine space is nonempty in positive dimension. -/
theorem puncturedAffineSpace_nonempty (hn : 0 < n) :
    (↑(puncturedAffineSpace k n) : Set (Spec (.of (MvPolynomial (Fin n) k)))).Nonempty := by
  refine ⟨⟨⊥, by simpa using (inferInstance : (⊥ : Ideal (MvPolynomial (Fin n) k)).IsPrime)⟩, ?_⟩
  refine Opens.mem_iSup.mpr ⟨⟨0, hn⟩, ?_⟩
  exact (PrimeSpectrum.mem_basicOpen _ _).mpr (by simp)

/-- The complement of the origin is dense in affine space in positive dimension. -/
theorem dense_puncturedAffineSpace (hn : 0 < n) :
    Dense (↑(puncturedAffineSpace k n) : Set (Spec (.of (MvPolynomial (Fin n) k)))) :=
  (puncturedAffineSpace k n).2.dense (puncturedAffineSpace_nonempty k n hn)

/-- In positive dimension every point of a scheme mapped to affine space by a universally open
morphism lies in the closure of the preimage of the complement of the origin. -/
theorem mem_closure_preimage_puncturedAffineSpace (hn : 0 < n) {U : Scheme.{u}}
    (h : U ⟶ Spec (.of (MvPolynomial (Fin n) k))) [UniversallyOpen h] (u : U) :
    u ∈ closure (h ⁻¹' (puncturedAffineSpace k n : Set _)) := by
  rw [mem_closure_iff]
  intro O hO huO
  obtain ⟨y, hy, ⟨x, hxO, rfl⟩⟩ := (dense_puncturedAffineSpace k n hn).exists_mem_open
    (h.isOpenMap _ hO) ⟨h u, u, huO, rfl⟩
  exact ⟨x, hxO, hy⟩

/-- If the first chart inclusion at `y` agrees with the second at `y'`, then `y` lies in the
complement of the origin. -/
theorem mem_puncturedAffineSpace_of_chartInclusion_eq
    {y y' : Spec (.of (MvPolynomial (Fin n) k))}
    (hy : chartInclusion k n 0 y = chartInclusion k n 1 y') : y ∈ puncturedAffineSpace k n := by
  have hne : (ULift.up (0 : Fin 2) : ULift.{u} (Fin 2)) ≠ ULift.up 1 := by decide
  obtain ⟨z, hz, -⟩ :=
    ((doubledZeroGlueData k n).ι_eq_iff (ULift.up 0) (ULift.up 1) _ _).mp hy
  rw [← opensRange_glueData_f k n hne]
  exact ⟨z, hz⟩

section OverOrigin

/-! ### Base changes of the coordinate morphism, presented by a pullback square

The results of this section are stated for an arbitrary pullback square `P ⟶ U`, `P ⟶ X` over
`h : U ⟶ Y` and the coordinate morphism, rather than for Mathlib's chosen pullback. -/

variable {k n} {U P : Scheme.{u}} {h : U ⟶ Spec (.of (MvPolynomial (Fin n) k))}
  {π : P ⟶ U} {g : P ⟶ affineSpaceWithDoubledZero k n}

/-- The section of a base change `P` of the coordinate morphism along `h : U ⟶ Y` determined by
the `i`-th chart: its component in `U` is the identity and its component in `X` is `h` followed
by the `i`-th chart inclusion. -/
noncomputable def chartSectionOfIsPullback (hP : IsPullback π g h (coordinateMorphism k n))
    (i : Fin 2) : U ⟶ P :=
  hP.lift (𝟙 U) (h ≫ chartInclusion k n i) (by
    rw [Category.id_comp, Category.assoc, (coordinateMorphismData k n).property i,
      Category.comp_id])

/-- The component in `U` of a chart section is the identity. -/
@[reassoc (attr := simp)]
theorem chartSectionOfIsPullback_fst (hP : IsPullback π g h (coordinateMorphism k n))
    (i : Fin 2) : chartSectionOfIsPullback hP i ≫ π = 𝟙 U :=
  hP.lift_fst _ _ _

/-- The component in `X` of the `i`-th chart section is `h` followed by the `i`-th chart
inclusion. -/
@[reassoc (attr := simp)]
theorem chartSectionOfIsPullback_snd (hP : IsPullback π g h (coordinateMorphism k n))
    (i : Fin 2) : chartSectionOfIsPullback hP i ≫ g = h ≫ chartInclusion k n i :=
  hP.lift_snd _ _ _

/-- Over a point of `U` lying off the complement of the origin the two chart sections take
distinct values. -/
theorem chartSectionOfIsPullback_apply_ne (hP : IsPullback π g h (coordinateMorphism k n))
    (x : U) (hx : h x ∉ puncturedAffineSpace k n) :
    chartSectionOfIsPullback hP 0 x ≠ chartSectionOfIsPullback hP 1 x := by
  intro heq
  refine hx (mem_puncturedAffineSpace_of_chartInclusion_eq k n (y' := h x) ?_)
  have key : ∀ i : Fin 2, g (chartSectionOfIsPullback hP i x) = chartInclusion k n i (h x) := by
    intro i
    rw [← Scheme.Hom.comp_apply, chartSectionOfIsPullback_snd, Scheme.Hom.comp_apply]
  rw [← key 0, ← key 1, heq]

/-- The `i`-th chart section of a base change of the coordinate morphism is the base change of
the `i`-th chart inclusion along the projection to `X`: the square it forms with `h`, the
projection and the chart inclusion is a pullback. -/
theorem isPullback_chartSectionOfIsPullback (hP : IsPullback π g h (coordinateMorphism k n))
    (i : Fin 2) :
    IsPullback (chartSectionOfIsPullback hP i) h g (chartInclusion k n i) := by
  refine IsPullback.of_right ?_ (chartSectionOfIsPullback_snd hP i) hP
  rw [chartSectionOfIsPullback_fst, (coordinateMorphismData k n).property i]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Each chart section of a base change of the coordinate morphism is an open immersion. -/
instance isOpenImmersion_chartSectionOfIsPullback
    (hP : IsPullback π g h (coordinateMorphism k n)) (i : Fin 2) :
    IsOpenImmersion (chartSectionOfIsPullback hP i) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_chartSectionOfIsPullback hP i).flip inferInstance

/-- The image of the `i`-th chart section is the preimage of the `i`-th chart. -/
theorem range_chartSectionOfIsPullback (hP : IsPullback π g h (coordinateMorphism k n))
    (i : Fin 2) :
    Set.range (chartSectionOfIsPullback hP i) = g ⁻¹' Set.range (chartInclusion k n i) := by
  have hpb := isPullback_chartSectionOfIsPullback hP i
  rw [← Scheme.Pullback.range_fst, ← hpb.isoPullback_hom_fst, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
  exact (ConcreteCategory.bijective_of_isIso (hpb.isoPullback.hom.base)).2

/-- If `h : U ⟶ Y` maps every point off the complement of the origin, then the base change
`P ⟶ U` of the coordinate morphism is finite. -/
theorem isFinite_of_isPullback_of_forall_notMem
    (hP : IsPullback π g h (coordinateMorphism k n))
    (hh : ∀ x : U, h x ∉ puncturedAffineSpace k n) : IsFinite π := by
  set s := fun i : Fin 2 => chartSectionOfIsPullback hP i with hs
  have hdisj : Pairwise (Function.onFun Disjoint fun i => Set.range (s i)) := by
    have key : ∀ x : P, x ∈ Set.range (s 0) → x ∉ Set.range (s 1) := by
      rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
      have hab : b = a := by
        simpa [hs, ← Scheme.Hom.comp_apply] using congrArg π hb
      subst hab
      exact chartSectionOfIsPullback_apply_ne hP b (hh b) hb.symm
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro x hi hj
    fin_cases i <;> fin_cases j
    · exact hij rfl
    · exact key x hi hj
    · exact key x hj hi
    · exact hij rfl
  have hcov : ⋃ i, Set.range (s i) = Set.univ := by
    refine Set.eq_univ_of_forall (fun x => ?_)
    obtain ⟨⟨i⟩, y, hy⟩ := (doubledZeroGlueData k n).ι_jointly_surjective (g x)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    rw [hs, range_chartSectionOfIsPullback]
    exact ⟨y, hy⟩
  have : IsOpenImmersion (Sigma.desc s) := isOpenImmersion_sigmaDesc (fun _ : Fin 2 => U) s hdisj
  have : Surjective (Sigma.desc s) := Surjective.sigmaDesc_of_union_range_eq_univ hcov
  have : IsIso (Sigma.desc s) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have hdesc : Sigma.desc s ≫ π = Sigma.desc (fun _ : Fin 2 => 𝟙 U) := by
    ext i
    simp [hs]
  have hπ : π = inv (Sigma.desc s) ≫ Sigma.desc (fun _ : Fin 2 => 𝟙 U) := by
    rw [← hdesc, IsIso.inv_hom_id_assoc]
  rw [hπ]
  infer_instance

/-- Let `W` be an open subscheme of a base change `P` of the coordinate morphism along
`h : U ⟶ Y`, finite over `U`, and let `u` be a point of `U` mapped off the complement of the
origin such that both chart sections pass through `W` at `u`. Then a whole open neighbourhood of
`u` is mapped off the complement of the origin. -/
theorem exists_opens_forall_notMem_puncturedAffineSpace
    (hP : IsPullback π g h (coordinateMorphism k n)) (W : P.Opens)
    (hW : IsFinite (W.ι ≫ π)) (u : U) (hu : h u ∉ puncturedAffineSpace k n)
    (hu0 : chartSectionOfIsPullback hP 0 u ∈ W) (hu1 : chartSectionOfIsPullback hP 1 u ∈ W) :
    ∃ O : U.Opens, u ∈ O ∧ ∀ x ∈ O, h x ∉ puncturedAffineSpace k n := by
  set s := fun i : Fin 2 => chartSectionOfIsPullback hP i with hs
  set q := W.ι ≫ π with hq
  have := hW
  have : IsSeparated q := IsSeparated.of_isAffineHom q
  set V : U.Opens := (s 0 ⁻¹ᵁ W) ⊓ (s 1 ⁻¹ᵁ W) with hV
  have huV : u ∈ V := ⟨hu0, hu1⟩
  have hmemV : ∀ (A : U.Opens) (v : A.toScheme), A.ι v ∈ A := by
    intro A v
    have hmem : A.ι v ∈ Set.range A.ι := ⟨v, rfl⟩
    rwa [Scheme.Opens.range_ι] at hmem
  have hrange : ∀ i : Fin 2, Set.range (V.ι ≫ s i) ⊆ Set.range W.ι := by
    intro i
    rw [Scheme.Opens.range_ι]
    rintro x ⟨v, rfl⟩
    rw [Scheme.Hom.comp_apply]
    have hvv := hmemV V v
    fin_cases i
    · exact hvv.1
    · exact hvv.2
  set t := fun i : Fin 2 => IsOpenImmersion.lift W.ι (V.ι ≫ s i) (hrange i) with ht
  have ht_fac : ∀ i : Fin 2, t i ≫ W.ι = V.ι ≫ s i := fun i => IsOpenImmersion.lift_fac _ _ _
  have ht_q : ∀ i : Fin 2, t i ≫ q = V.ι := by
    intro i
    rw [hq, ← Category.assoc, ht_fac i, Category.assoc, hs, chartSectionOfIsPullback_fst,
      Category.comp_id]
  have hsame : t 0 ≫ q = t 1 ≫ q := by rw [ht_q 0, ht_q 1]
  set j := pullback.lift (t 0) (t 1) hsame with hj
  have hjfst : j ≫ pullback.fst q q = t 0 := by rw [hj]; exact pullback.lift_fst _ _ _
  have hjsnd : j ≫ pullback.snd q q = t 1 := by rw [hj]; exact pullback.lift_snd _ _ _
  set c := pullback.fst j (pullback.diagonal q) with hc
  set d := pullback.snd j (pullback.diagonal q) with hd
  have : IsClosedImmersion c := by rw [hc]; infer_instance
  have hcond : c ≫ j = d ≫ pullback.diagonal q := by rw [hc, hd]; exact pullback.condition
  have hc_t : c ≫ t 0 = c ≫ t 1 := by
    rw [← hjfst, ← hjsnd, reassoc_of% hcond, reassoc_of% hcond, pullback.diagonal_fst,
      pullback.diagonal_snd]
  have hb : ∀ y : V.toScheme, y ∈ Set.range c → h (V.ι y) ∈ puncturedAffineSpace k n := by
    rintro y ⟨e, rfl⟩
    by_contra hy
    refine chartSectionOfIsPullback_apply_ne hP (V.ι (c e)) hy ?_
    have key : ∀ i : Fin 2, W.ι (t i (c e)) = s i (V.ι (c e)) := by
      intro i
      rw [← Scheme.Hom.comp_apply, ht_fac i, Scheme.Hom.comp_apply]
    have hvt : t 0 (c e) = t 1 (c e) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hc_t]
    rw [← key 0, ← key 1, hvt]
  have ha : ∀ y : V.toScheme, h (V.ι y) ∈ puncturedAffineSpace k n → y ∈ Set.range c := by
    intro y hy
    set V' : U.Opens := V ⊓ (h ⁻¹ᵁ puncturedAffineSpace k n) with hV'
    have hle : V' ≤ V := inf_le_left
    have hagree : U.homOfLE hle ≫ t 0 = U.homOfLE hle ≫ t 1 := by
      rw [← cancel_mono W.ι, Category.assoc, Category.assoc, ht_fac 0, ht_fac 1,
        ← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι]
      refine hP.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hs, chartSectionOfIsPullback_fst,
          chartSectionOfIsPullback_fst]
      · rw [Category.assoc, Category.assoc, hs, chartSectionOfIsPullback_snd,
          chartSectionOfIsPullback_snd, ← Category.assoc, ← Category.assoc]
        refine comp_chartInclusion_eq k n (V'.ι ≫ h) ?_
        rintro x ⟨v, rfl⟩
        exact (hmemV V' v).2
    have hlift : U.homOfLE hle ≫ j = (U.homOfLE hle ≫ t 0) ≫ pullback.diagonal q := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hjfst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, hjsnd, Category.assoc, pullback.diagonal_snd, Category.comp_id,
          hagree]
    obtain ⟨w, hw⟩ : V.ι y ∈ Set.range V'.ι := by
      rw [Scheme.Opens.range_ι]; exact ⟨hmemV V y, hy⟩
    have hwy : U.homOfLE hle w = y := by
      refine V.ι.isOpenEmbedding.injective ?_
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact hw
    refine ⟨pullback.lift (U.homOfLE hle) (U.homOfLE hle ≫ t 0) hlift w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hc, pullback.lift_fst, hwy]
  have hclosed : IsClosed (Set.range c) := c.isClosedEmbedding.isClosed_range
  refine ⟨⟨V.ι '' (Set.range c)ᶜ, V.ι.isOpenEmbedding.isOpenMap _ hclosed.isOpen_compl⟩,
    ?_, ?_⟩
  · obtain ⟨v, hv⟩ : u ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact huV
    refine ⟨v, fun hvc => hu ?_, hv⟩
    rw [← hv]
    exact hb v hvc
  · rintro x ⟨y, hy, rfl⟩ hx
    exact hy (ha y hx)

end OverOrigin

end AlgebraicGeometry

end
