module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Curves.RelativeCurveEtaleDivisorPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinMorphism
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IotaRealizableSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageRealizable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLisseLocus
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseKernelTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PointwiseMixedInverseImage
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The Gysin input of the top higher direct image, from the Gysin morphism

Let `g : U ⟶ W` be smooth of relative dimension one and affine over a finite field `k`, with `W`
reduced and irreducible and `U` nonempty. On an affine chart of `W` there is an étale divisor
(`AlgebraicGeometry.exists_etale_divisor_pullback_of_smoothOfRelativeDimension_one`): a set
`S ⊆ U` with finite fibres over `W` which, over every open `V'` of a nonempty open `W_a ⊆ W`, is
the underlying set of a closed subscheme `Z' = V(f') ⊆ U'` finite étale over `V'` and meeting every
positive-dimensional irreducible component of every geometric fibre. Its fibre over `w` gives the
finite set `Z w` of closed points of `U` over `w`, with degrees `d z = [κ(z) : κ(g z)]`.

For a lisse `G`, let `V ⊆ W_a` be the part of the lisse locus of the `Rʳ g_! G`
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageLisseLocusInput`) where `W` is smooth over
`k`. Over an open `V' ⊆ V`, the Gysin morphism
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinMorphismInput`) gives a lisse `A` and
`φ : A ⟶ R² g'_! G` surjective on the rational stalks at closed points, with
`Tr(π_w ^ m | A) = #κ(w) ^ m · Tr(π_w ^ m | π'_* i'⁻¹ G)`. The kernel of `φ` is lisse, with
`Tr A = Tr R² + Tr K`
(`Stacks.EtaleCohomology.LAdicSheaf.exists_isLisse_trace_rationalStalkFrobenius_pow_eq_add`, `V'`
being irreducible), and the trace formula for the finite étale direct image
(`Stacks.EtaleCohomology.LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_eq_sum`) writes
the trace on `π'_* i'⁻¹ G` as `∑_{x ↦ w, d_x ∣ m} d_x · Tr(π_x ^ (m / d_x) | i'⁻¹ G)`; the points
`x` of `Z'` over `w` are the points of `Z (w)`, with the same residue fields, so this is the sum of
the Gysin input (`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

All names below are in the namespace `Stacks.EtaleCohomology`.

* `LAdicSheaf.higherDirectImageTopGysinInput_of_gysinMorphismInput`.
* `LAdicSheaf.higherDirectImageTopGysinInput_higherDirectImageShriekFamily`: the Gysin input for
  `Rʳ g_!`, from its Gysin morphism and the constructibility of `Rf_!`.
* `LAdicSheaf.higherDirectImageTopRealizableInput_higherDirectImageShriekFamily`: the
  realizability of `R² g_!`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

/-- A field extension of finite residue fields has `#κ(x) = #κ(f x) ^ [κ(x) : κ(f x)]`. -/
private lemma natCard_residueField_eq_pow_liftResidueDegree {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : X) (hx : Finite (X.residueField x)) :
    Nat.card (X.residueField x) =
      Nat.card (Y.residueField (f.base x)) ^ liftResidueDegree f x := by
  let : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  have : Module.Finite (Y.residueField (f.base x)) (X.residueField x) := Module.Finite.of_finite
  exact Module.natCard_eq_pow_finrank

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The Gysin input of `R² g_!` from its Gysin morphism** (Weil II 1.5 and 3.3, for the
reduction of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): if a family `R` in the role of
`Rʳ g_!` has the lisse locus (`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageLisseLocusInput`)
and the Gysin morphism of `R²` along étale divisors
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinMorphismInput`), then it has the
Gysin input (`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinInput`): the divisor is
the étale divisor of a chart of `W`
(`AlgebraicGeometry.exists_etale_divisor_pullback_of_smoothOfRelativeDimension_one`), the kernel
of the Gysin morphism is lisse with additive traces, and the trace on the finite étale direct
image is the sum over the points of the divisor. -/
theorem LAdicSheaf.higherDirectImageTopGysinInput_of_gysinMorphismInput
    (R : LAdicSheaf.HigherDirectImageFamily B ℓ)
    (hL : LAdicSheaf.HigherDirectImageLisseLocusInput R)
    (hM : LAdicSheaf.HigherDirectImageTopGysinMorphismInput R) :
    LAdicSheaf.HigherDirectImageTopGysinInput R := by
  classical
  intro k _ _ p n _ _ hcard hℓ U W _ _ _ g _ _ _ _ _ fW _ _ _ hW hU
  have : IrreducibleSpace (B.inclusion.obj W) := hW
  have : IsReduced (B.inclusion.obj W) := ‹IsReduced W.1›
  have : AlgebraicGeometry.IsIntegral (B.inclusion.obj W) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  have : AlgebraicGeometry.IsIntegral W.1 := ‹AlgebraicGeometry.IsIntegral (B.inclusion.obj W)›
  have hNW : IsNoetherian (B.inclusion.obj W) := ‹IsNoetherian W.1›
  have : IsLocallyNoetherian (B.inclusion.obj W) := hNW.toIsLocallyNoetherian
  obtain ⟨Wa, S, hWa, hSfin, hdiv⟩ := exists_etale_divisor_pullback_of_smoothOfRelativeDimension_one
    (B.inclusion.map g) k p fW (Classical.arbitrary U.1)
  -- the divisor over each point, and the residue degrees
  let Zs : W.1 → Set (closedPoints U.1) := fun w =>
    {z | z.1 ∈ S ∧ (B.inclusion.map g).base z.1 = w}
  have hZs : ∀ w, (Zs w).Finite := fun w =>
    Set.Finite.preimage Subtype.val_injective.injOn (hSfin w)
  refine ⟨fun w => (hZs w).toFinset, fun z => liftResidueDegree (B.inclusion.map g) z.1,
    fun w z hz => ((hZs w).mem_toFinset.mp hz).2, fun G hG => ?_⟩
  -- the open `V`: the divisor's open, the smooth locus of `W` over `k`, and the lisse locus
  obtain ⟨V₃, j₃, ho₃, hn₃, h₃⟩ :=
    hL U W g G hG ⟨(B.inclusion.map g).base (Classical.arbitrary U.1)⟩
  let O : (B.inclusion.obj W).Opens :=
    Wa ⊓ fW.smoothLocus ⊓ (B.inclusion.map j₃).opensRange
  have hOB : B.Contains O.toScheme := (Scheme.size_le_of_isOpenImmersion O.ι).trans_lt W.2
  let V : B.Scheme := B.obj O.toScheme hOB
  let jV : V ⟶ W := ObjectProperty.homMk O.ι
  have hjV : B.inclusion.map jV = O.ι := rfl
  have hVne : Nonempty V.1 := by
    have hsm : (fW.smoothLocus : Set W.1).Nonempty :=
      ⟨_, fW.genericPoint_mem_smoothLocus_of_perfectField⟩
    obtain ⟨w, hw⟩ := nonempty_preirreducible_inter
      ((Wa ⊓ fW.smoothLocus).isOpen) ((B.inclusion.map j₃).opensRange.isOpen)
      (nonempty_preirreducible_inter Wa.isOpen fW.smoothLocus.isOpen hWa hsm)
      ⟨_, (Classical.arbitrary V₃.1), rfl⟩
    exact ⟨⟨w, hw⟩⟩
  refine ⟨V, jV, inferInstanceAs (IsOpenImmersion O.ι), hVne, ?_⟩
  intro V' U' _ _ jV' jU g' _ _ _ jg' hjV' hpb fV' _
  -- the open immersion `V' ⟶ W` lands in `O`
  have : IsOpenImmersion (B.inclusion.map (jV' ≫ jV)) := by
    rw [Functor.map_comp, hjV]; infer_instance
  have hrangeO : Set.range (B.inclusion.map (jV' ≫ jV)).base ⊆ (O : Set (B.inclusion.obj W)) := by
    rintro _ ⟨x, rfl⟩
    rw [Functor.map_comp, hjV, Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι O]
    exact ⟨_, rfl⟩
  -- the factorization through the lisse locus
  have hr₃ : Set.range (B.inclusion.map (jV' ≫ jV)) ⊆ Set.range (B.inclusion.map j₃) :=
    fun _ hx => (hrangeO hx).2
  have hfac₃ := IsOpenImmersion.lift_fac (B.inclusion.map j₃) (B.inclusion.map (jV' ≫ jV)) hr₃
  let i₃ : V' ⟶ V₃ := ObjectProperty.homMk (IsOpenImmersion.lift (B.inclusion.map j₃)
    (B.inclusion.map (jV' ≫ jV)) hr₃)
  have hi₃ : IsOpenImmersion (B.inclusion.map i₃) := by
    have : IsOpenImmersion (IsOpenImmersion.lift (B.inclusion.map j₃)
        (B.inclusion.map (jV' ≫ jV)) hr₃ ≫ B.inclusion.map j₃) := by
      rw [hfac₃]; infer_instance
    exact IsOpenImmersion.of_comp (IsOpenImmersion.lift (B.inclusion.map j₃)
      (B.inclusion.map (jV' ≫ jV)) hr₃) (B.inclusion.map j₃)
  have hf₃ : i₃ ≫ j₃ = jV' ≫ jV := B.inclusion.map_injective (by rw [Functor.map_comp]; exact hfac₃)
  have hR2 : (R g' jg' (LAdicSheaf.inverseImage jU G) 2).IsLisse :=
    h₃ V' U' i₃ jU g' jg' hi₃ (hf₃ ▸ hpb) 2
  -- the divisor over `V'`
  obtain ⟨Z', i', f, hcl, hfin, het, hZf, hZS, hfib⟩ := hdiv (B.inclusion.map (jV' ≫ jV))
    (B.inclusion.map jU) (B.inclusion.map g') (fun _ hx => (hrangeO hx).1.1) hpb
  have := hcl
  have hZB : B.Contains Z' :=
    (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact i').trans_lt U'.2
  let ZB : B.Scheme := B.obj Z' hZB
  let iB : ZB ⟶ U' := ObjectProperty.homMk i'
  have : IsClosedImmersion (B.inclusion.map iB) := hcl
  have : IsFinite (B.inclusion.map (iB ≫ g')) := hfin
  have : AlgebraicGeometry.Etale (B.inclusion.map (iB ≫ g')) := het
  have : IsNoetherian ZB.1 := by
    have hNU' : IsNoetherian (B.inclusion.obj U') := ‹IsNoetherian U'.1›
    have : IsLocallyNoetherian (B.inclusion.obj U') := hNU'.toIsLocallyNoetherian
    have : CompactSpace (B.inclusion.obj U') := hNU'.toCompactSpace
    have : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian i'
    have : CompactSpace Z' := i'.isClosedEmbedding.compactSpace
    exact { }
  have : SmoothOfRelativeDimension 1 (B.inclusion.map g') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hpb inferInstance
  have : IsOpenImmersion (B.inclusion.map jU) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb.flip inferInstance
  have : IsAffineHom (B.inclusion.map g') :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hpb inferInstance
  -- `V'` is smooth over `k`
  let fVs : V'.1 ⟶ Spec (.of k) := B.inclusion.map (jV' ≫ jV) ≫ fW
  have : Smooth fVs := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    refine top_le_iff.mp fun x _ => ?_
    exact (hrangeO ⟨x, rfl⟩).1.2
  -- the Gysin morphism
  have hGl : (LAdicSheaf.inverseImage jU G).IsLisse := LAdicSheaf.IsLisse.inverseImage jU hG
  have hF := LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse _
    (LAdicSheaf.IsLisse.inverseImage iB hGl)
  obtain ⟨A, φ, hA, hsurj, htr⟩ := hM k p n hcard hℓ U' V' ZB g' jg' iB (iB ≫ g') rfl f hZf
    (fun Ω _ _ w C hC hxy => hfib Ω w C hC hxy) fVs (LAdicSheaf.inverseImage jU G) hGl hR2
  -- the kernel
  by_cases hV' : Nonempty V'.1
  swap
  · exact ⟨_, hR2, fun w => (hV' ⟨w.1⟩).elim⟩
  have : Nonempty (B.inclusion.obj V') := hV'
  have : IrreducibleSpace V'.1 :=
    (B.inclusion.map (jV' ≫ jV)).isOpenEmbedding.irreducibleSpace
  obtain ⟨K, hK, hKtr⟩ := LAdicSheaf.exists_isLisse_trace_rationalStalkFrobenius_pow_eq_add
    B V' ℓ fVs hA hR2 φ hsurj
  refine ⟨K, hK, fun w m hm => ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, m = e + 1 := ⟨m - 1, by omega⟩
  have hwfin : Finite (V'.1.residueField w.1) := finite_residueField fVs w.1 w.2
  have : Finite ((B.inclusion.obj V').residueField w.1) := hwfin
  -- the points of `Z'` over `w` are those of the divisor over the image of `w`
  have : JacobsonSpace (B.inclusion.obj U) :=
    LocallyOfFiniteType.jacobsonSpace (B.inclusion.map g ≫ fW)
  have hclosed : ∀ x : ZB.1, (B.inclusion.map (iB ≫ g')).base x = w.1 →
      (B.inclusion.map jU).base (i'.base x) ∈ closedPoints U.1 := by
    intro x hx
    have h1 : IsClosed ({x} : Set ZB.1) :=
      Stacks.Curves.isClosed_singleton_of_quasiFinite_preimage (B.inclusion.map (iB ≫ g')) x
        (by rw [hx]; exact w.2)
    have h2 : IsClosed ({i'.base x} : Set (B.inclusion.obj U')) := by
      have := i'.isClosedEmbedding.isClosedMap _ h1
      rwa [Set.image_singleton] at this
    have h3 := (B.inclusion.map jU).isOpenEmbedding.preimage_closedPoints
    have h4 : i'.base x ∈ closedPoints (B.inclusion.obj U') := h2
    rw [← h3] at h4
    exact h4
  have hcardw : Nat.card ((B.inclusion.obj V').residueField w.1) =
      Nat.card ((B.inclusion.obj W).residueField ((B.inclusion.map (jV' ≫ jV)).base w.1)) :=
    (Nat.card_eq_of_bijective _
      (ConcreteCategory.bijective_of_isIso ((B.inclusion.map (jV' ≫ jV)).residueFieldMap w.1))).symm
  have hone : 1 < Nat.card ((B.inclusion.obj V').residueField w.1) := Finite.one_lt_card
  have hKw := hKtr w (e + 1)
  have hAw := htr hF w (e + 1) (by omega)
  rw [LAdicSheaf.trace_rationalStalkFrobenius_directImage_pow_eq_sum (iB ≫ g') w.1 _ hF e]
    at hAw
  refine hKw.symm.trans (hAw.trans ?_)
  congr 1
  refine Finset.sum_bij (fun x hx => ⟨(B.inclusion.map jU).base (i'.base x),
      hclosed x ((mem_geometricLiftPoints_iff (iB ≫ g') w.1 x).1 hx)⟩) ?_ ?_ ?_ ?_
  · -- the image lies in the divisor over the image of `w`
    intro x hx
    have hxw := (mem_geometricLiftPoints_iff (iB ≫ g') w.1 x).1 hx
    refine (hZs _).mem_toFinset.mpr ⟨?_, ?_⟩
    · show (B.inclusion.map jU).base (i'.base x) ∈ S
      have : i'.base x ∈ Set.range i'.base := ⟨x, rfl⟩
      rw [hZS] at this
      exact this
    · show (B.inclusion.map g).base ((B.inclusion.map jU).base (i'.base x)) = _
      rw [← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply]
      congr 1
  · -- injectivity
    intro x₁ _ x₂ _ h12
    have h := congrArg Subtype.val h12
    exact i'.isClosedEmbedding.injective ((B.inclusion.map jU).isOpenEmbedding.injective h)
  · -- surjectivity
    intro z hz
    obtain ⟨hzS, hzw⟩ := (hZs _).mem_toFinset.mp hz
    have : HasPullback (B.inclusion.map g) (B.inclusion.map (jV' ≫ jV)) := inferInstance
    obtain ⟨y₀, hy₀1, hy₀2⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.inclusion.map g)
      (g := B.inclusion.map (jV' ≫ jV)) z.1 w.1 hzw
    let y : B.inclusion.obj U' := hpb.isoPullback.inv.base y₀
    have hy1 : (B.inclusion.map jU).base y = z.1 := by
      rw [← hy₀1, ← hpb.isoPullback_inv_fst]
      rfl
    have hy2 : (B.inclusion.map g').base y = w.1 := by
      rw [← hy₀2, ← hpb.isoPullback_inv_snd]
      rfl
    have hyS : y ∈ (B.inclusion.map jU).base ⁻¹' S := by
      rw [Set.mem_preimage, hy1]; exact hzS
    rw [← hZS] at hyS
    obtain ⟨x, hxy⟩ := hyS
    refine ⟨x, (mem_geometricLiftPoints_iff (iB ≫ g') w.1 x).2 ?_, Subtype.ext ?_⟩
    · show (B.inclusion.map g').base (i'.base x) = w.1
      rw [hxy]; exact hy2
    · show (B.inclusion.map jU).base (i'.base x) = z.1
      rw [hxy]; exact hy1
  · -- the summands agree
    intro x hx
    have hxw := (mem_geometricLiftPoints_iff (iB ≫ g') w.1 x).1 hx
    rw [dite_eq_left hxw]
    have hxfin : Finite ((B.inclusion.obj ZB).residueField x) :=
      finite_residueField_of_base_eq (iB ≫ g') x hxw
    have hyfin : Finite ((B.inclusion.obj U').residueField (i'.base x)) :=
      @Finite.of_injective _ _ hxfin _ (i'.residueFieldMap x).hom.injective
    have hzfin :
        Finite ((B.inclusion.obj U).residueField ((B.inclusion.map jU).base (i'.base x))) :=
      @Finite.of_injective _ _ hyfin _
        ((B.inclusion.map jU).residueFieldMap (i'.base x)).hom.injective
    have hc1 : Nat.card ((B.inclusion.obj ZB).residueField x) =
        Nat.card ((B.inclusion.obj U').residueField (i'.base x)) :=
      (Nat.card_eq_of_bijective _
        (Stacks.Chow.bijective_residueFieldMap_of_isClosedImmersion i' x)).symm
    have hc2 : Nat.card ((B.inclusion.obj U').residueField (i'.base x)) =
        Nat.card ((B.inclusion.obj U).residueField ((B.inclusion.map jU).base (i'.base x))) :=
      (Nat.card_eq_of_bijective _ (ConcreteCategory.bijective_of_isIso
        ((B.inclusion.map jU).residueFieldMap (i'.base x)))).symm
    -- the residue degrees agree
    have hd : liftResidueDegree (B.inclusion.map (iB ≫ g')) x =
        liftResidueDegree (B.inclusion.map g) ((B.inclusion.map jU).base (i'.base x)) := by
      have e1 := natCard_residueField_eq_pow_liftResidueDegree (B.inclusion.map (iB ≫ g')) x
        hxfin
      have e2 := natCard_residueField_eq_pow_liftResidueDegree (B.inclusion.map g)
        ((B.inclusion.map jU).base (i'.base x)) hzfin
      have hgz : (B.inclusion.map g).base ((B.inclusion.map jU).base (i'.base x)) =
          (B.inclusion.map (jV' ≫ jV)).base w.1 := by
        rw [← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply, ← hxw]
        rfl
      rw [hxw] at e1
      rw [hgz] at e2
      have key : Nat.card ((B.inclusion.obj V').residueField w.1) ^
            liftResidueDegree (B.inclusion.map (iB ≫ g')) x =
          Nat.card ((B.inclusion.obj V').residueField w.1) ^
            liftResidueDegree (B.inclusion.map g) ((B.inclusion.map jU).base (i'.base x)) := by
        refine e1.symm.trans (hc1.trans (hc2.trans (e2.trans ?_)))
        rw [hcardw]
      exact Nat.pow_right_injective hone key
    -- the traces agree
    have htrx : ∀ N : ℕ, 1 ≤ N →
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B ZB ℓ
          (LAdicSheaf.inverseImage iB (LAdicSheaf.inverseImage jU G)) x
          (finite_residueField_of_base_eq (iB ≫ g') x hxw) ^ N) =
        LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B U ℓ G
          ((B.inclusion.map jU).base (i'.base x))
          (finite_residueField (B.inclusion.map g ≫ fW)
            ((B.inclusion.map jU).base (i'.base x))
            (hclosed x hxw)) ^ N) := by
      intro N hN
      rw [LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow U' ℓ iB
        (LAdicSheaf.inverseImage jU G) x hxfin hyfin 0 (by rw [zero_add, pow_one]; exact hc1) hN,
        zero_add, one_mul]
      exact LAdicSheaf.trace_rationalStalkFrobenius_inverseImage_pow U ℓ jU G (i'.base x) hyfin
        hzfin 0 (by rw [zero_add, pow_one]; exact hc2) hN |>.trans (by rw [zero_add, one_mul])
    show (if liftResidueDegree (B.inclusion.map (iB ≫ g')) x ∣ e + 1 then _ else _) =
      if liftResidueDegree (B.inclusion.map g) ((B.inclusion.map jU).base (i'.base x)) ∣ e + 1
      then _ else _
    rw [hd]
    split_ifs with hdvd
    · congr 1
      have hpos : 0 < liftResidueDegree (B.inclusion.map g)
          ((B.inclusion.map jU).base (i'.base x)) := by
        rw [← hd]
        have : Finite (V'.1.residueField ((B.inclusion.map (iB ≫ g')).base x)) := by
          rw [hxw]; exact hwfin
        exact liftResidueDegree_pos (iB ≫ g') x
      exact htrx _ (Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hpos)
    · rfl

/-- **The Gysin input of `R² g_!`** for the family of the ℓ-adic sheaves `Rʳ g_! G`
(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekFamily`), granted the constructibility
of `Rf_!` (Tag 0GL0, `Stacks.EtaleCohomology.LowerShriekConstructibilityInput`, for its lisse
locus) and the Gysin morphism of `R² g_!` along étale divisors
(`Stacks.EtaleCohomology.LAdicSheaf.HigherDirectImageTopGysinMorphismInput`). -/
theorem LAdicSheaf.higherDirectImageTopGysinInput_higherDirectImageShriekFamily
    (hC : LowerShriekConstructibilityInput B)
    (hM : LAdicSheaf.HigherDirectImageTopGysinMorphismInput
      (LAdicSheaf.higherDirectImageShriekFamily B ℓ)) :
    LAdicSheaf.HigherDirectImageTopGysinInput (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
  LAdicSheaf.higherDirectImageTopGysinInput_of_gysinMorphismInput _
    (LAdicSheaf.higherDirectImageLisseLocusInput_higherDirectImageShriek B ℓ hC) hM

/-- **Realizability of `R² g_!`** (Weil II 1.5 and 3.3, for the reduction of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) for the family of the ℓ-adic sheaves
`Rʳ g_! G`, granted the constructibility of `Rf_!` (Tag 0GL0) and the Gysin morphism of `R² g_!`
along étale divisors. -/
theorem LAdicSheaf.higherDirectImageTopRealizableInput_higherDirectImageShriekFamily
    (hC : LowerShriekConstructibilityInput B)
    (hM : LAdicSheaf.HigherDirectImageTopGysinMorphismInput
      (LAdicSheaf.higherDirectImageShriekFamily B ℓ)) :
    LAdicSheaf.HigherDirectImageTopRealizableInput (LAdicSheaf.higherDirectImageShriekFamily B ℓ) :=
  LAdicSheaf.higherDirectImageTopRealizableInput_of_gysinInput _
    (LAdicSheaf.higherDirectImageLisseLocusInput_higherDirectImageShriek B ℓ hC)
    (LAdicSheaf.higherDirectImageTopGysinInput_higherDirectImageShriekFamily hC hM)

end Stacks.EtaleCohomology

end
