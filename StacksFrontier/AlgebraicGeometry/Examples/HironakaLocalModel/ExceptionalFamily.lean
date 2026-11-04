module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.FirstBlowupStrictCentreLine
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaConicChart
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalDivisorProjectiveLineFibres
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalProjectiveLine
public import StacksFrontier.AlgebraicGeometry.Perfect.InvertibleFibreEulerConstant
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.FlatStratificationFieldPoints
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.AffineSpaceSmooth
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# The exceptional family of the second blow-up of the local model of Hironaka's example

Let `A = k[x, y, z]`, `I = (x, y)`, `J = (x - y², z)` on `Spec A`, `b₁ : B₁ = Bl_I Spec A ⟶ Spec A`
the first blow-up, `J' = AlgebraicGeometry.TwoStepTower.strictCentre I J` the ideal of the strict
transform of `V(J)` on `B₁`, `b₂ : T = Bl_{J'} B₁ ⟶ B₁` the second blow-up and
`p : E₂ ⟶ V(J')` the exceptional divisor of `b₂` over its centre
(`Stacks.AlgebraicGeometry.exceptionalSubschemeMap`).

This file shows that the Euler characteristic of an invertible module on `T` along the fibre of
`T ⟶ Spec A` over a `k`-point `d = (t², t, 0)` of `V(J) ∖ V(I)` (`t ≠ 0`) equals its Euler
characteristic along any fibre of `p` over a `k`-point of `V(J')`, for instance the point `o'` over
the origin. The argument:

* `B₁` is smooth of relative dimension `3` over `k` (its two charts are affine `3`-spaces) and
  `V(J') ≅ 𝔸¹_k` is smooth of relative dimension `1`, so the conormal sheaf of `V(J')` is locally
  free of rank `2` and `p` is a flat proper family of projective lines
  (`Stacks.AlgebraicGeometry.smooth_blowUp_exceptionalSubschemeMap_projectiveLineFamily`);
* `V(J')` is connected, so the Euler characteristic of an invertible module is constant on the
  fibres of `p`
  (`ProperFlatFibreEulerCharacteristic.eulerSum_eq_of_isPullback_of_isInvertible`);
* `b₁` is an isomorphism off `V(I)`, so the fibre of `b₁` over `d` is the `k`-point `d'` of `V(J')`
  with chart coordinates `x₁ = y = t, z = 0`; hence the fibre of `T ⟶ Spec A` over `d` is the
  fibre of `b₂` over `d'`, which is the fibre of `p` over `d'`
  (`Stacks.AlgebraicGeometry.isPullback_blowUpToBase_comp_subschemeι_iff`).

## Main definitions

* `Stacks.Examples.HironakaLocalModel.ambientToBase`, `firstBlowupToBase`: the structure
  morphisms of `Spec A` and of `B₁` to `Spec k`.
* `Stacks.Examples.HironakaLocalModel.strictLinePoint`: the `k`-point of `V(J')` with chart
  coordinates `x₁ = y = t, z = 0` on `U₂`, lying over `(t², t, 0)`; `strictLinePoint k 0` is the
  point `o'` over the origin.

## Main results

* `Stacks.Examples.HironakaLocalModel.smoothOfRelativeDimension_firstBlowupToBase`,
  `Stacks.Examples.HironakaLocalModel.smoothOfRelativeDimension_strictCentre_subschemeι_comp`:
  the relative dimensions `3` and `1`.
* `Stacks.Examples.HironakaLocalModel.isFiniteLocallyFreeOfRank_two_conormal_strictCentre`: the
  conormal sheaf of `V(J')` in `B₁` has rank two.
* `Stacks.Examples.HironakaLocalModel.isProper_exceptionalSubschemeMap_strictCentre` and its
  siblings: `p` is proper, flat and locally of finite presentation.
* `Stacks.Examples.HironakaLocalModel.isPullback_strictLinePoint_blowUpToBase`: the fibre of `b₁`
  over `(t², t, 0)`, `t ≠ 0`, is the point `strictLinePoint k t`.
* `Stacks.Examples.HironakaLocalModel.eulerSum_fibre_strictTower_eq_exceptionalFibre`: the
  equality of Euler characteristics.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AlgebraicGeometry.TwoStepTower AlgebraicGeometry.ProperFlatFibreEulerCharacteristic
open Stacks.Examples.HironakaConicChart

universe u

namespace Stacks.Examples.HironakaLocalModel

/-! ### Smoothness of relative dimension `n` -/

private instance smoothOfRelativeDimensionIsZariskiLocalAtSource (n : ℕ) :
    IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
  HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} n)

/-- Smoothness of relative dimension `n` can be read after an isomorphism of the source. -/
theorem smoothOfRelativeDimension_of_isIso_comp {X Y Z : Scheme.{u}} (n : ℕ) (e : X ⟶ Y)
    [IsIso e] (g : Y ⟶ Z) (h : SmoothOfRelativeDimension n (e ≫ g)) :
    SmoothOfRelativeDimension n g := by
  have := SmoothOfRelativeDimension.etale_comp n (inv e) (e ≫ g)
  rwa [IsIso.inv_hom_id_assoc] at this

variable (k : Type u) [Field k]

/-! ### The model's two ideal sheaves, in the two spellings -/

/-- The first centre of `StacksFrontier/AlgebraicGeometry/Examples/HironakaConicChart.lean` is the
first centre of the local model files. -/
theorem modelIdealSheafI_eq_centreIdeal : modelIdealSheafI k = centreIdeal k := rfl

/-- The second curve of `StacksFrontier/AlgebraicGeometry/Examples/HironakaConicChart.lean` is the
second curve of the local model files. -/
theorem modelIdealSheafJ_eq_curveIdeal : modelIdealSheafJ k = curveIdeal k := rfl

/-! ### Structure morphisms to `Spec k` -/

/-- The structure morphism `Spec k[x, y, z] ⟶ Spec k`. -/
abbrev ambientToBase : ambient k ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Ring3 k)))

/-- The structure morphism `B₁ = Bl_I Spec A ⟶ Spec k` of the first blow-up. -/
abbrev firstBlowupToBase : blowUp (centreIdeal k) ⟶ Spec (.of k) :=
  blowUpToBase (centreIdeal k) ≫ ambientToBase k

/-- Each chart of the first blow-up is an affine `3`-space over `k`. -/
theorem chartι_comp_firstBlowupToBase (i : Fin 2) :
    chartι k i ≫ firstBlowupToBase k = ambientToBase k := by
  rw [← Category.assoc, chartι_comp_blowUpToBase, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun a ↦ (chartHom k i).commutes a

/-- `Spec k[x, y, z]` is smooth of relative dimension `3` over `k`. -/
theorem smoothOfRelativeDimension_ambientToBase : SmoothOfRelativeDimension 3 (ambientToBase k) :=
  AlgebraicGeometry.smoothOfRelativeDimension_specMap_C k 3

/-- **The first blow-up is smooth of relative dimension `3` over `k`**: it is covered by two
affine `3`-spaces. -/
theorem smoothOfRelativeDimension_firstBlowupToBase :
    SmoothOfRelativeDimension 3 (firstBlowupToBase k) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SmoothOfRelativeDimension 3) (chartCover k)]
  change ∀ i : Fin 2, SmoothOfRelativeDimension 3 (chartι k i ≫ firstBlowupToBase k)
  intro i
  rw [chartι_comp_firstBlowupToBase]
  exact smoothOfRelativeDimension_ambientToBase k

/-! ### `V(J')` is smooth of relative dimension one -/

/-- The parametrization `k[x₁, y, z]/(x₁ - y, z) ≅ k[t]`, as an isomorphism of `k`-algebras. -/
def lineQuotientAlgEquiv :
    (Ring3 k ⧸ Ideal.span {X 0 - X 1, (X 2 : Ring3 k)}) ≃ₐ[k] Polynomial k :=
  (Ideal.quotientEquivAlgOfEq k (ker_lineParam k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (lineParam_surjective k))

/-- `V(x₁ - y, z) ⊆ Spec k[x₁, y, z]` is smooth of relative dimension `1` over `k`. -/
theorem smoothOfRelativeDimension_lineSubscheme :
    SmoothOfRelativeDimension 1
      ((idealSheafOf k (Ideal.span {X 0 - X 1, (X 2 : Ring3 k)})).subschemeι ≫
        ambientToBase k) := by
  set 𝔞 : Ideal (Ring3 k) := Ideal.span {X 0 - X 1, (X 2 : Ring3 k)}
  have hI : idealSheafOf k 𝔞 = Scheme.IdealSheafData.ofIdealTop
      (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of (Ring3 k))).hom.hom 𝔞) := by
    rw [AlgebraicGeometry.Ideal.comap_hom_eq_map_inv]
  rw [hI]
  refine smoothOfRelativeDimension_of_isIso_comp 1
    (Stacks.Blowup.specQuotientIsoSubscheme 𝔞).hom _ ?_
  rw [Stacks.Blowup.specQuotientIsoSubscheme_hom_comp_subschemeι_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  change (algebraMap k (Ring3 k ⧸ 𝔞)).IsStandardSmoothOfRelativeDimension 1
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact .of_algEquiv 1 ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).trans
    (lineQuotientAlgEquiv k).symm)

/-- The base change of `V(J') ⟶ B₁` along the chart `U₂ ⟶ B₁` is an isomorphism, since `V(J')`
lies in `U₂`. -/
instance isIso_pullbackSnd_chartι_one_strictCentre :
    IsIso (pullback.snd (chartι k 1) (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι) := by
  set K := strictCentre (centreIdeal k) (curveIdeal k)
  have hsurj : Function.Surjective (pullback.snd (chartι k 1) K.subschemeι) := by
    intro x
    have hx : K.subschemeι x ∈ (K.support : Set (blowUp (centreIdeal k))) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := support_strictCentre_subset_range_chartι_one k hx
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨z, hz⟩
  have : Surjective (pullback.snd (chartι k 1) K.subschemeι) := ⟨hsurj⟩
  exact (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩

/-- **`V(J')` is smooth of relative dimension `1` over `k`.** -/
theorem smoothOfRelativeDimension_strictCentre_subschemeι_comp :
    SmoothOfRelativeDimension 1
      ((strictCentre (centreIdeal k) (curveIdeal k)).subschemeι ≫ firstBlowupToBase k) := by
  set K := strictCentre (centreIdeal k) (curveIdeal k)
  let ψ : (K.comap (chartι k 1)).subscheme ⟶ K.subscheme :=
    (K.comapIso (chartι k 1)).hom ≫ pullback.snd (chartι k 1) K.subschemeι
  have : IsIso ψ := by
    dsimp only [ψ]
    infer_instance
  have hψ : ψ ≫ K.subschemeι = (K.comap (chartι k 1)).subschemeι ≫ chartι k 1 := by
    simp only [ψ, Category.assoc, ← pullback.condition,
      Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  refine smoothOfRelativeDimension_of_isIso_comp 1 ψ _ ?_
  rw [← Category.assoc, hψ, Category.assoc, chartι_comp_firstBlowupToBase,
    comap_chartι_one_strictCentre k]
  exact smoothOfRelativeDimension_lineSubscheme k

/-! ### The hypotheses of the exceptional-divisor theorem -/

/-- The first blow-up is smooth over `k`. -/
instance smooth_firstBlowupToBase : Smooth (firstBlowupToBase k) :=
  haveI := smoothOfRelativeDimension_firstBlowupToBase k
  SmoothOfRelativeDimension.smooth 3 _

/-- `V(J')` is smooth over `k`. -/
instance smooth_strictCentre_subschemeι_comp :
    Smooth ((strictCentre (centreIdeal k) (curveIdeal k)).subschemeι ≫ firstBlowupToBase k) :=
  haveI := smoothOfRelativeDimension_strictCentre_subschemeι_comp k
  SmoothOfRelativeDimension.smooth 1 _

/-- **The conormal sheaf of `V(J')` in `B₁` is locally free of rank two**: `B₁` and `V(J')` have
relative dimensions `3` and `1` over `k`. -/
instance isFiniteLocallyFreeOfRank_two_conormal_strictCentre :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne
        (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι) 2 :=
  haveI : SmoothOfRelativeDimension (1 + 2) (firstBlowupToBase k) :=
    smoothOfRelativeDimension_firstBlowupToBase k
  haveI := smoothOfRelativeDimension_strictCentre_subschemeι_comp k
  Stacks.AlgebraicGeometry.isFiniteLocallyFreeOfRank_two_conormalSheafDegreeOne
    (firstBlowupToBase k) _ 1

/-- The exceptional divisor of the second blow-up is proper over `V(J')`. -/
instance isProper_exceptionalSubschemeMap_strictCentre :
    IsProper (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
      (strictCentre (centreIdeal k) (curveIdeal k))) :=
  Stacks.AlgebraicGeometry.isProper_exceptionalSubschemeMap (firstBlowupToBase k) _

/-- The exceptional divisor of the second blow-up is flat over `V(J')`. -/
instance flat_exceptionalSubschemeMap_strictCentre :
    Flat (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
      (strictCentre (centreIdeal k) (curveIdeal k))) :=
  Stacks.AlgebraicGeometry.flat_exceptionalSubschemeMap (firstBlowupToBase k) _

/-- The exceptional divisor of the second blow-up is locally of finite presentation over
`V(J')`. -/
instance locallyOfFinitePresentation_exceptionalSubschemeMap_strictCentre :
    LocallyOfFinitePresentation (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
      (strictCentre (centreIdeal k) (curveIdeal k))) :=
  Stacks.AlgebraicGeometry.locallyOfFinitePresentation_exceptionalSubschemeMap
    (firstBlowupToBase k) _

/-- `V(J')` is connected. -/
instance preconnectedSpace_strictCentre_subscheme :
    PreconnectedSpace (strictCentre (centreIdeal k) (curveIdeal k)).subscheme :=
  haveI := connectedSpace_strictCentre_subscheme k
  inferInstance

/-! ### The `k`-points of `V(J')` -/

/-- The `k`-point `x₁ = y = t, z = 0` of the chart `U₂` of the first blow-up. -/
abbrev chartLinePoint (t : k) : Spec (.of k) ⟶ blowUp (centreIdeal k) :=
  modelKPoint k ![t, t, 0] ≫ chartι k 1

/-- The chart point `x₁ = y = t, z = 0` lies on `V(J')`. -/
theorem chartLinePoint_mem_support (t : k) (x : Spec (.of k)) :
    chartLinePoint k t x ∈ (strictCentre (centreIdeal k) (curveIdeal k)).support := by
  have hx : chartLinePoint k t x = chartι k 1 (kPoint k ![t, t, 0]) := by
    rw [Scheme.Hom.comp_apply, modelKPoint_apply]
    rfl
  rw [hx, chartι_mem_support_strictCentre_iff, comap_chartι_one_strictCentre]
  refine (mem_support_idealSheafOf_iff k _ (kPoint k ![t, t, 0])).mpr ?_
  rw [Ideal.span_le]
  rintro _ (rfl | rfl) <;> simp [kPoint_asIdeal]

/-- **The `k`-point of `V(J')` with chart coordinates `x₁ = y = t, z = 0`** (on `U₂`), lying over
`(t², t, 0)`. `strictLinePoint k 0` is the point `o'` of `V(J')` over the origin. -/
def strictLinePoint (t : k) :
    Spec (.of k) ⟶ (strictCentre (centreIdeal k) (curveIdeal k)).subscheme :=
  (exists_lift_subschemeι_of_mem_support _ k (chartLinePoint k t)
    (IsLocalRing.closedPoint k) (chartLinePoint_mem_support k t _)).choose

/-- `strictLinePoint k t` is the chart point `x₁ = y = t, z = 0` of `B₁`. -/
@[reassoc]
theorem strictLinePoint_subschemeι (t : k) :
    strictLinePoint k t ≫ (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι =
      chartLinePoint k t :=
  (exists_lift_subschemeι_of_mem_support _ k (chartLinePoint k t)
    (IsLocalRing.closedPoint k) (chartLinePoint_mem_support k t _)).choose_spec

/-- The chart point `x₁ = y = t, z = 0` lies over `(t², t, 0)`. -/
theorem chartLinePoint_comp_blowUpToBase (t : k) (d : Fin 3 → k) (hd0 : d 0 = t ^ 2)
    (hd1 : d 1 = t) (hd2 : d 2 = 0) :
    chartLinePoint k t ≫ blowUpToBase (centreIdeal k) = modelKPoint k d := by
  rw [Category.assoc, chartι_comp_blowUpToBase, modelKPoint, modelKPoint, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
  · simp only [RingHom.comp_apply, eval_C]
    rw [show (C a : Ring3 k) = algebraMap k (Ring3 k) a from rfl, AlgHom.coe_toRingHom,
      AlgHom.commutes]
    simp
  · simp only [RingHom.comp_apply, chartHom_one_eq, AlgHom.coe_toRingHom, aeval_X, eval_X]
    fin_cases i
    · simp [hd0, pow_two]
    · simp [hd1]
    · simp [hd2]

/-- `strictLinePoint k t` lies over `(t², t, 0)`. -/
theorem strictLinePoint_comp (t : k) (d : Fin 3 → k) (hd0 : d 0 = t ^ 2) (hd1 : d 1 = t)
    (hd2 : d 2 = 0) :
    strictLinePoint k t ≫ (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι ≫
      blowUpToBase (centreIdeal k) = modelKPoint k d :=
  (strictLinePoint_subschemeι_assoc k t _).trans
    (chartLinePoint_comp_blowUpToBase k t d hd0 hd1 hd2)

/-! ### The fibre of the first blow-up off the centre -/

/-- **Off the centre, a section of the blow-up is its fibre.** If `x : T ⟶ W` misses the support
of `I` and `s : T ⟶ Bl_I W` lifts it, then `s` exhibits `T` as the fibre of the blow-up over `x`:
the blow-up is an isomorphism over the complement of `V(I)` ([Stacks, Tag 02OS]). -/
theorem isPullback_id_blowUpToBase_of_not_mem {W T : Scheme.{u}} (I : W.IdealSheafData)
    (x : T ⟶ W) (hx : ∀ t, x t ∉ I.support) (s : T ⟶ blowUp I)
    (hs : s ≫ blowUpToBase I = x) :
    IsPullback s (𝟙 T) (blowUpToBase I) x := by
  let U : W.Opens := I.support.compl
  have hxU : Set.range x ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hx t
  let p : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι x hxU
  have hp : p ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  let r := blowUpToBase I ∣_ U
  have sq1 : IsPullback (p ≫ inv r) (𝟙 T) r p :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have sq := sq1.paste_horiz (isPullback_morphismRestrict (blowUpToBase I) U).flip
  rw [hp] at sq
  have hl := sq.lift_snd s (𝟙 T) (by rw [hs, Category.id_comp])
  have hf := sq.lift_fst s (𝟙 T) (by rw [hs, Category.id_comp])
  rw [Category.comp_id] at hl
  rw [hl, Category.id_comp] at hf
  rwa [hf] at sq

/-- **The fibre of `b₁` over `(t², t, 0)`, `t ≠ 0`, is the point `strictLinePoint k t` of
`V(J')`.** -/
theorem isPullback_strictLinePoint_blowUpToBase (d : Fin 3 → k) (hd0 : d 0 = d 1 ^ 2)
    (hd2 : d 2 = 0) (hd1 : d 1 ≠ 0) :
    IsPullback (strictLinePoint k (d 1) ≫ (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι)
      (𝟙 _) (blowUpToBase (centreIdeal k)) (modelKPoint k d) := by
  refine isPullback_id_blowUpToBase_of_not_mem _ _ (fun x hx ↦ ?_) _
    (by rw [Category.assoc, strictLinePoint_comp k (d 1) d hd0 rfl hd2])
  rw [modelKPoint_apply] at hx
  have := (mem_support_idealSheafOf_iff k _ (kPoint k d)).mp hx
    (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  exact hd1 (by simpa [kPoint_asIdeal] using this)

/-! ### The Euler characteristics -/

/-- The restriction of an invertible module along any morphism is invertible. -/
theorem isInvertible_pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [hL : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((Scheme.Modules.pullback f).obj L) :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp
    (@Stacks.Modules.isInvertible_pullback _ _ f L
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        _ _ _).mpr hL))

/-- `Stacks.Examples.HironakaLocalModel.eulerSum_fibre_strictTower_eq_exceptionalFibre`, in the
spelling `centreIdeal`, `curveIdeal` of the two ideal sheaves. -/
theorem eulerSum_fibre_strictTower_eq_exceptionalFibre_of_centreIdeal
    (H : (blowUp (strictCentre (centreIdeal k) (curveIdeal k))).Modules)
    (hH : AlgebraicGeometry.SheafOfModules.IsInvertible
      (blowUp (strictCentre (centreIdeal k) (curveIdeal k))).presheaf
      (blowUp (strictCentre (centreIdeal k) (curveIdeal k))).ringCatSheaf.2 H)
    (d : Fin 3 → k) (hd0 : d 0 = d 1 ^ 2) (hd2 : d 2 = 0) (hd1 : d 1 ≠ 0)
    {F : Scheme.{u}} (q : F ⟶ blowUp (strictCentre (centreIdeal k) (curveIdeal k)))
    (g : F ⟶ Spec (.of k))
    (hq : IsPullback q g (strictTower (centreIdeal k) (curveIdeal k))
      (modelKPoint k d))
    (o' : Spec (.of k) ⟶ (strictCentre (centreIdeal k) (curveIdeal k)).subscheme)
    {F' : Scheme.{u}}
    (q' : F' ⟶ exceptionalDivisor (strictCentre (centreIdeal k) (curveIdeal k)))
    (g' : F' ⟶ Spec (.of k))
    (hq' : IsPullback q' g'
      (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
        (strictCentre (centreIdeal k) (curveIdeal k))) o') :
    eulerSum k g ((Scheme.Modules.pullback q).obj H) =
      eulerSum k g' ((Scheme.Modules.pullback
        (q' ≫ (exceptionalIdeal (strictCentre (centreIdeal k)
          (curveIdeal k))).subschemeι)).obj H) := by
  have hbot := isPullback_strictLinePoint_blowUpToBase k d hd0 hd2 hd1
  have hc : (q ≫ blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k))) ≫
      blowUpToBase (centreIdeal k) = g ≫ modelKPoint k d := by
    rw [Category.assoc]
    exact hq.w
  have hw : q ≫ blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k)) =
      g ≫ strictLinePoint k (d 1) ≫ (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι := by
    have hl := hbot.lift_snd _ g hc
    have hf := hbot.lift_fst _ g hc
    rw [Category.comp_id] at hl
    rw [← hf, hl]
  have htop : IsPullback q g (blowUpToBase (strictCentre (centreIdeal k) (curveIdeal k)))
      (strictLinePoint k (d 1) ≫ (strictCentre (centreIdeal k) (curveIdeal k)).subschemeι) :=
    IsPullback.of_bot (by rw [Category.comp_id]; exact hq) hw hbot
  obtain ⟨q₁, hq₁, hpb⟩ :=
    Stacks.AlgebraicGeometry.exists_isPullback_exceptionalSubschemeMap_of_isPullback_blowUpToBase
      _ _ htop
  have := hH
  have := isInvertible_pullback_obj
    (exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι H
  rw [← hq₁, eulerSum_pullback_comp, eulerSum_pullback_comp]
  exact eulerSum_eq_of_isPullback_of_isInvertible
    (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
      (strictCentre (centreIdeal k) (curveIdeal k)))
    ((Scheme.Modules.pullback
      (exceptionalIdeal (strictCentre (centreIdeal k) (curveIdeal k))).subschemeι).obj H)
    (strictLinePoint k (d 1)) o' q₁ g hpb q' g' hq'

/-- **The fibre of the tower over `d = (t², t, 0)` and the fibres of the exceptional family have
the same Euler characteristic.** Let `T = Bl_{J'} Bl_I Spec A ⟶ Spec A` be the strict tower of the
local model, `p : E₂ ⟶ V(J')` the exceptional divisor of the second blow-up and `ℋ` an invertible
module on `Bl_{J'} B₁`. For `d = (d₀, d₁, d₂)` with `d₀ = d₁²`, `d₂ = 0`, `d₁ ≠ 0` (a `k`-point of
`V(J) ∖ V(I)`), every fibre `F` of `T` over `d` and every fibre `F'` of `p` over a `k`-point `o'`
of `V(J')` (for instance the point over the origin, `strictLinePoint k 0`), the Euler
characteristics `χ(F, ℋ|_F)` and `χ(F', ℋ|_{F'})` agree. -/
theorem eulerSum_fibre_strictTower_eq_exceptionalFibre
    (H : (blowUp (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (blowUp (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))).presheaf
      (blowUp (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))).ringCatSheaf.2 H]
    (d : Fin 3 → k) (hd0 : d 0 = d 1 ^ 2) (hd2 : d 2 = 0) (hd1 : d 1 ≠ 0)
    {F : Scheme.{u}} (q : F ⟶ blowUp (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)))
    (g : F ⟶ Spec (.of k))
    (hq : IsPullback q g (strictTower (modelIdealSheafI k) (modelIdealSheafJ k))
      (modelKPoint k d))
    (o' : Spec (.of k) ⟶ (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)).subscheme)
    {F' : Scheme.{u}}
    (q' : F' ⟶ exceptionalDivisor (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k)))
    (g' : F' ⟶ Spec (.of k))
    (hq' : IsPullback q' g'
      (Stacks.AlgebraicGeometry.exceptionalSubschemeMap
        (strictCentre (modelIdealSheafI k) (modelIdealSheafJ k))) o') :
    eulerSum k g ((Scheme.Modules.pullback q).obj H) =
      eulerSum k g' ((Scheme.Modules.pullback
        (q' ≫ (exceptionalIdeal (strictCentre (modelIdealSheafI k)
          (modelIdealSheafJ k))).subschemeι)).obj H) :=
  eulerSum_fibre_strictTower_eq_exceptionalFibre_of_centreIdeal k H (by assumption) d hd0 hd2
    hd1 q g hq o' q' g' hq'

end Stacks.Examples.HironakaLocalModel

end
