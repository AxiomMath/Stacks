module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PicardSchemeRepresentable
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal

/-!
# The rank-one locus as a chart of a scheme representing the Picard functor of a curve

Let `X` be a smooth projective curve of genus `g` over a separably closed field `k`, let `P`
represent its Picard functor `Pic_{X/k}` on a big fppf site, and let `H` represent `Hilb^g_{X/k}`.
The subfunctor `F` of [Stacks, Tag 0B9V] (the classes `ℒ` with `Rf_{T,*}ℒ` an invertible module
in degree zero), read on `Pic_{X/k}` through `Pic_{X/k, σ} ≅ Pic_{X/k}`, is open, is represented
by an open `W` of `H` ([Stacks, Tag 0B9X]) through the universal class, and every field-valued
point of `P` is carried into it by a `k`-point ([Stacks, Tag 0B9Y]). These are exactly the inputs
of `Stacks.PicardFunctor.smoothOfRelativeDimension_of_representsOpen`.

## Main results

* `Stacks.PicardFunctor.exists_rankOneChart`.

## References

* [Stacks Project, Tag 0B9V](https://stacks.math.columbia.edu/tag/0B9V)
* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0B9Y](https://stacks.math.columbia.edu/tag/0B9Y)
* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.PicardFunctor

open AlgebraicGeometry.RigidifiedPicard

/-- A morphism factors through an open subscheme exactly when its image lies in it. -/
theorem exists_comp_ι_eq_iff_range_subset {Y Z : Scheme.{u}} (U : Z.Opens) (φ : Y ⟶ Z) :
    (∃ h : Y ⟶ U.toScheme, h ≫ U.ι = φ) ↔ Set.range φ ⊆ (U : Set Z) := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact (Set.image_subset_range _ _).trans_eq U.range_ι
  · intro hφ
    exact ⟨IsOpenImmersion.lift U.ι φ (by rwa [U.range_ι]),
      IsOpenImmersion.lift_fac _ _ _⟩

variable (B : BigFppfSite.{u}) {k : Type u} [Field k] {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : X ⟶ Spec (.of k))

/-- **The rank-one locus of [Stacks, Tag 0B9V] is a represented open chart of the Picard scheme,
and its translates by `k`-points cover** ([Stacks, Tag 0B9X], [Stacks, Tag 0B9Y]). Let `P`
represent `Pic_{X/k}` on the big fppf site and `H` represent `Hilb^g_{X/k}`. There are a subset
`F` of `Pic_{X/k}`, open in the sense of [Stacks, Tag 0B9V], an open `i : W ⟶ H` and
`j : W ⟶ P` such that `j` represents `F`, and such that every point of `P` lies on a field-valued
point whose class is carried into `F` by adding a `k`-point. -/
theorem exists_rankOneChart
    [IsSepClosed k] [IsCurve k f] [IsProjectiveVariety k f] [Smooth f]
    {P H : BigFppfOver B (Spec (.of k)) hk}
    (R : (picardFunctor B hX hk (ObjectProperty.homMk f)).RepresentableBy P)
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f)
      ((BigFppfOver.toOver B (Spec (.of k)) hk).obj H) (genus f)) :
    ∃ (F : ∀ T : BigFppfOver B (Spec (.of k)) hk,
        Set ((picardFunctor B hX hk (ObjectProperty.homMk f)).obj (op T)))
      (W : BigFppfOver B (Spec (.of k)) hk) (i : W ⟶ H) (j : W ⟶ P),
      IsOpenImmersion ((BigFppfOver.toScheme B (Spec (.of k)) hk).map i) ∧
      (∀ (T : BigFppfOver B (Spec (.of k)) hk)
          (c : (picardFunctor B hX hk (ObjectProperty.homMk f)).obj (op T)),
        ∃ U : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).Opens,
          ∀ {T' : BigFppfOver B (Spec (.of k)) hk} (h : T' ⟶ T),
            (picardFunctor B hX hk (ObjectProperty.homMk f)).map h.op c ∈ F T' ↔
              Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map h) ⊆ (U : Set _)) ∧
      R.homEquiv j ∈ F W ∧
      (∀ {T : BigFppfOver B (Spec (.of k)) hk}
          (c : (picardFunctor B hX hk (ObjectProperty.homMk f)).obj (op T)), c ∈ F T →
        ∃ t : T ⟶ W, R.homEquiv (t ≫ j) = c) ∧
      (∀ {T : BigFppfOver B (Spec (.of k)) hk} (t t' : T ⟶ W), t ≫ j = t' ≫ j → t = t') ∧
      (∀ p : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj P,
        ∃ (T : BigFppfOver B (Spec (.of k)) hk) (x : T ⟶ P)
          (t : ((BigFppfOver.toOver B (Spec (.of k)) hk).obj T).left)
          (r : Over.mk (𝟙 (B.obj hk)) ⟶ P),
          ((BigFppfOver.toOver B (Spec (.of k)) hk).map x).left t = p ∧
            ∀ v : T ⟶ Over.mk (𝟙 (B.obj hk)),
              R.homEquiv x + (picardFunctor B hX hk (ObjectProperty.homMk f)).map v.op
                (R.homEquiv r) ∈ F T) := by
  classical
  have hPerfBC := fun {X S : Scheme.{u}} (f : X ⟶ S) hf E hE G hG =>
    isPerfect_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap f hf E hE G hG
  have hRankOpen := fun {Z : Scheme.{u}} (E : DerivedCategory Z.Modules) hE i r {Y : Scheme.{u}}
      (h : Y ⟶ Z) =>
    Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff_derivedPullback E i r hE h
  have : IsProper f := inferInstance
  have : Nonempty X := (inferInstance : IsIntegral X).nonempty
  obtain ⟨σ, hσ, -⟩ := exists_section_of_isSepClosed f
  let Φ := BigFppfOver.toOver B (Spec (.of k)) hk
  let κ := fun T => kernelToPicardFunctor B hX hk f σ hσ T
  have hκ : ∀ T, Function.Bijective (κ T) := bijective_kernelToPicardFunctor B hX hk f σ hσ
  have hnat : ∀ {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U) (c : kernelAt f σ hσ (Φ.obj U)),
      (picardFunctor B hX hk (ObjectProperty.homMk f)).map g.op (κ U c) =
        κ T (kernelMap f σ hσ (Φ.map g) c) := fun g c =>
    (kernelToPicardFunctor_naturality B hX hk f σ hσ g c).symm
  let F : ∀ T : BigFppfOver B (Spec (.of k)) hk,
      Set ((picardFunctor B hX hk (ObjectProperty.homMk f)).obj (op T)) :=
    fun T => κ T '' rankOneLocus f σ hσ (Φ.obj T)
  have hmemF : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (c : kernelAt f σ hσ (Φ.obj T)),
      κ T c ∈ F T ↔ c ∈ rankOneLocus f σ hσ (Φ.obj T) := fun _ =>
    (hκ _).1.mem_set_image
  obtain ⟨-, hopenr⟩ := rankOneLocus_isSubfunctor_and_representable f σ hσ hPerfBC hRankOpen
  obtain ⟨Wo, hW⟩ := rankOneLocus_representable_by_open_of_hilbert f σ hσ hPerfBC hRankOpen hH
  obtain ⟨Wb, i, hio, hir, hilift⟩ := exists_restrict_bigFppfOver H Wo
  have := hio
  have : Mono i := (BigFppfOver.toScheme B (Spec (.of k)) hk).mono_of_mono_map inferInstance
  let u₀ := universalClass f σ hσ hH
  -- classes of morphisms into `H` factoring through `W` lie in the rank-one locus
  have hfac : ∀ {T : Over (Spec (.of k))} (m : T ⟶ Φ.obj H),
      (∃ h : T.left ⟶ Wo.toScheme, h ≫ Wo.ι = m.left) →
        kernelMap f σ hσ m u₀ ∈ rankOneLocus f σ hσ T := by
    intro T m hm
    obtain ⟨e, he⟩ := hW T
    have h := (e ⟨m, hm⟩).2
    rwa [he] at h
  obtain ⟨j, hjdef⟩ := R.homEquiv.surjective (κ Wb (kernelMap f σ hσ (Φ.map i) u₀))
  have hj : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ Wb),
      R.homEquiv (t ≫ j) = κ T (kernelMap f σ hσ (Φ.map (t ≫ i)) u₀) := by
    intro T t
    have e2 : kernelMap f σ hσ (Φ.map (t ≫ i)) u₀ =
        kernelMap f σ hσ (Φ.map t) (kernelMap f σ hσ (Φ.map i) u₀) :=
      (congrArg (fun m => kernelMap f σ hσ m u₀) (Φ.map_comp t i)).trans
        (kernelMap_comp f σ hσ _ _ _)
    exact (R.homEquiv_comp t j).trans
      ((congrArg _ hjdef).trans ((hnat t _).trans (congrArg (κ T) e2.symm)))
  obtain ⟨l, hl⟩ := (exists_comp_ι_eq_iff_range_subset Wo (Φ.map i).left).2 hir.le
  have hiW : ∀ {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ Wb),
      ∃ h : (Φ.obj T).left ⟶ Wo.toScheme, h ≫ Wo.ι = (Φ.map (t ≫ i)).left := by
    intro T t
    refine ⟨(Φ.map t).left ≫ l, ?_⟩
    rw [Category.assoc, hl, ← Over.comp_left, ← Φ.map_comp]
  refine ⟨F, Wb, i, j, hio, ?_, ?_, ?_, ?_, ?_⟩
  · -- `F` is open
    intro T c
    obtain ⟨c', rfl⟩ := (hκ T).2 c
    obtain ⟨U, hU⟩ := hopenr (Φ.obj T) c'
    refine ⟨U, fun {T'} h => ?_⟩
    rw [hnat, hmemF]
    exact (hU (Φ.map h)).trans (exists_comp_ι_eq_iff_range_subset U _)
  · -- the class of `j` is in `F`
    rw [hjdef, hmemF]
    exact hfac (Φ.map i) ⟨l, hl⟩
  · -- every class in `F` comes from `W`
    intro T c hc
    obtain ⟨c', hc', hcc⟩ := hc
    obtain ⟨e, he⟩ := hW (Φ.obj T)
    obtain ⟨⟨m, hm⟩, hme⟩ := e.surjective ⟨c', hc'⟩
    obtain ⟨m', hm'⟩ : ∃ m' : T ⟶ H, Φ.map m' = m :=
      ⟨_, (BigFppfOver.fullyFaithfulToOver B (Spec (.of k)) hk).map_preimage m⟩
    have hrm : Set.range ((BigFppfOver.toScheme B (Spec (.of k)) hk).map m') ⊆
        (Wo : Set (Φ.obj H).left) := by
      have h2 : (BigFppfOver.toScheme B (Spec (.of k)) hk).map m' = m.left :=
        congrArg Over.Hom.left hm'
      rw [h2]
      exact (exists_comp_ι_eq_iff_range_subset Wo m.left).1 hm
    obtain ⟨t, ht⟩ := hilift m' hrm
    have htm : Φ.map (t ≫ i) = m := by rw [ht, hm']
    exact ⟨t, (hj t).trans ((congrArg (fun m => κ T (kernelMap f σ hσ m u₀)) htm).trans
      ((congrArg (κ T) ((he ⟨m, hm⟩).symm.trans (congrArg Subtype.val hme))).trans hcc))⟩
  · -- uniqueness
    intro T t t' htt
    have h1 := (hκ T).1 ((hj t).symm.trans ((congrArg R.homEquiv htt).trans (hj t')))
    obtain ⟨e, he⟩ := hW (Φ.obj T)
    have h2 : e ⟨Φ.map (t ≫ i), hiW t⟩ = e ⟨Φ.map (t' ≫ i), hiW t'⟩ :=
      Subtype.ext (by rwa [he ⟨Φ.map (t ≫ i), hiW t⟩, he ⟨Φ.map (t' ≫ i), hiW t'⟩])
    exact (cancel_mono i).1 ((BigFppfOver.fullyFaithfulToOver B (Spec (.of k)) hk).map_injective
      (congrArg Subtype.val (e.injective h2)))
  · -- the translates cover
    intro p
    let Y := (BigFppfOver.toScheme B (Spec (.of k)) hk).obj P
    have hK := BigFppfSite.residueField_spec_contains B P.left.property p
    let α : Spec (.of (Y.residueField p)) ⟶ Spec (.of k) :=
      Y.fromSpecResidueField p ≫ B.inclusion.map P.hom
    let T : BigFppfOver B (Spec (.of k)) hk :=
      Over.mk (ObjectProperty.homMk α : B.obj hK ⟶ B.obj hk)
    let x : T ⟶ P := Over.homMk (ObjectProperty.homMk (Y.fromSpecResidueField p)) rfl
    obtain ⟨c', hc'⟩ := (hκ T).2 (R.homEquiv x)
    obtain ⟨r₀, hr₀⟩ := exists_add_mem_rankOneLocus f σ hσ (Y.residueField p) α c'
    obtain ⟨r, hr⟩ := R.homEquiv.surjective (κ (Over.mk (𝟙 (B.obj hk))) r₀)
    refine ⟨T, x, IsLocalRing.closedPoint _, r, Y.fromSpecResidueField_apply p _, fun v => ?_⟩
    have hv : Φ.map v = (Over.homMk α (Category.comp_id α) :
        Over.mk α ⟶ Over.mk (𝟙 (Spec (.of k)))) := by
      ext
      have hw : v.left = T.hom := by simpa using Over.w v
      exact congrArg B.inclusion.map hw
    have key : R.homEquiv x + (picardFunctor B hX hk (ObjectProperty.homMk f)).map v.op
        (R.homEquiv r) = κ T (kernelMap f σ hσ (Φ.map v) r₀ + c') := by
      have e1 := congrArg ((picardFunctor B hX hk (ObjectProperty.homMk f)).map v.op) hr
      have e3 := map_add (κ T) (kernelMap f σ hσ (Φ.map v) r₀) c'
      exact (add_comm _ _).trans
        (e3.trans (congrArg₂ (· + ·) ((hnat v r₀).symm.trans e1.symm) hc')).symm
    refine key ▸ (hmemF _).2 ?_
    have e4 : kernelMap f σ hσ (Φ.map v) r₀ =
        (RigidifiedPicard.picardFunctor f σ hσ).map
          (Over.homMk α (Category.comp_id α) : Over.mk α ⟶ Over.mk (𝟙 (Spec (.of k)))).op r₀ :=
      congrArg (fun m => kernelMap f σ hσ m r₀) hv
    rwa [e4]

end Stacks.PicardFunctor

end
