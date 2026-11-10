module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatDimensionKeyCase

/-!
# The locus `F_n` is represented over every quasi-finite test scheme

In Situation 0CWU, assume `f` and `F` of finite presentation and `F` pure relative to `Y`. Then
for every test scheme `V` over `Y` whose structure morphism is locally quasi-finite, the locus
`F_n` over `V` is cut out by a monomorphism of finite presentation `Z_n ⟶ V`. This is the middle
of the source's proof of Stacks 0CX1: the question is Zariski local on `V`, so `V` may be taken
affine; then the fibre dimensions are bounded, `F_n` is everything for `n` large, and a
descending induction on `n` reduces to the key case of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatDimensionKeyCase.lean`, applied over `Z_{n+1}`, which
is quasi-finite over `V` as a monomorphism of finite presentation, so that purity still applies.

## Main results

* `AlgebraicGeometry.Space.FlatDimensionSituation.isRepresentedOver_of_isFlat`: the key case over
  an arbitrary quasi-finite test scheme.
* `AlgebraicGeometry.Space.FlatDimensionSituation.isRepresentedOver_of_isAffine`: the descending
  induction over an affine quasi-finite test scheme.
* `AlgebraicGeometry.Space.FlatDimensionSituation.isRepresentedOver`: the result over an arbitrary
  quasi-finite test scheme.

## References

* [Stacks Project, Tag 0CX1](https://stacks.math.columbia.edu/tag/0CX1)
* [Stacks Project, Tag 0CT8](https://stacks.math.columbia.edu/tag/0CT8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Flatness

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace FlatDimensionSituation

variable (D : FlatDimensionSituation.{u} B S hS)

/-- **Representability is Zariski local on the test scheme.** If the locus is represented over
every affine open of `V`, regarded as a test scheme, then it is represented over `V`. -/
theorem isRepresentedOver_of_affine_local (n : ℕ) (V : SchemesOver D.Y)
    (hqf : IsLocallyQuasiFinite B S hS V.hom.hom)
    (h : ∀ V' : SchemesOver D.Y, IsAffine ((BigFppfOver.toScheme B S hS).obj V'.left) →
      IsLocallyQuasiFinite B S hS V'.hom.hom → (V' ⟶ V) → D.IsRepresentedOver n V') :
    D.IsRepresentedOver n V := by
  refine D.isRepresentedOver_of_etale_local n V fun t ↦ ?_
  let C := ((BigFppfOver.toScheme B S hS).obj V.left).affineCover
  obtain ⟨a, t', ht'⟩ := C.exists_eq t
  have hc : B.Contains (C.X a) := B.contains_of_locallyOfFinitePresentation (C.f a) V.left.left.2
  refine ⟨schemesOverOfContained V hc (C.f a), schemesOverOfContainedMap V hc (C.f a),
    inferInstanceAs (Etale (C.f a)), ⟨t', ht'⟩,
    h _ (inferInstanceAs (IsAffine (C.X a)))
      (D.isLocallyQuasiFinite_schemesOverOfContained V hqf hc (C.f a))
      (schemesOverOfContainedMap V hc (C.f a))⟩

/-- Flatness in dimensions `≥ n` of `F_V` over `V` passes to a test scheme over `V`. -/
theorem presented_id_of_hom (n : ℕ) {V' V : SchemesOver D.Y} (β : V' ⟶ V)
    (h : D.Presented n V (Over.mk (𝟙 _))) : D.Presented n V' (Over.mk (𝟙 _)) := by
  rw [D.presented_baseChange_iff n β]
  exact D.presented_of_hom n V
    (Over.homMk ((BigFppfOver.toScheme B S hS).map β.left) (by simp) :
      (Over.map ((BigFppfOver.toScheme B S hS).map β.left)).obj (Over.mk (𝟙 _)) ⟶
        Over.mk (𝟙 _)) h

/-- **The key case over an arbitrary quasi-finite test scheme.** -/
theorem isRepresentedOver_of_isFlat (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hpure : ∀ y, IsPureAbove (D.fpPrePureSituation hf y)) (n : ℕ) (V : SchemesOver D.Y)
    (hqf : IsLocallyQuasiFinite B S hS V.hom.hom)
    (hflat : D.Presented (n + 1) V (Over.mk (𝟙 _))) : D.IsRepresentedOver n V :=
  D.isRepresentedOver_of_affine_local n V hqf fun V' hV' hqf' β ↦
    D.isRepresentedOver_of_isAffine_of_isFlat hf hF hpure n V' hV' hqf'
      (D.presented_id_of_hom (n + 1) β hflat)

attribute [local instance] _root_.AlgebraicGeometry.isQuasicoherent_pullback_obj'
  _root_.AlgebraicGeometry.isFiniteType_pullback_obj'

/-- **The descending induction over an affine quasi-finite test scheme.** -/
theorem isRepresentedOver_of_isAffine (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hpure : ∀ y, IsPureAbove (D.fpPrePureSituation hf y)) (V : SchemesOver D.Y)
    (hVaff : IsAffine ((BigFppfOver.toScheme B S hS).obj V.left))
    (hqf : IsLocallyQuasiFinite B S hS V.hom.hom) (n : ℕ) : D.IsRepresentedOver n V := by
  obtain ⟨U, hUaff, hUs⟩ :=
    exists_isAffine_isSurjective_chart_baseChangeSpace B S hS D.f hf.2.1 V hVaff
  have : CompactSpace (D.stageSituation B S hS 0 V U).S :=
    inferInstanceAs (CompactSpace ((BigFppfOver.toScheme B S hS).obj V.left))
  have : QuasiCompact (D.stageSituation B S hS 0 V U).f :=
    D.quasiCompact_stageSituation_f B S hS 0 V hVaff U hUaff
  obtain ⟨N, hN⟩ := exists_topologicalKrullDim_fiber_le (D.stageSituation B S hS 0 V U).f
  -- for `m` large the locus is everything
  have hbig (m : ℕ) (hm : N + 1 ≤ m) : D.IsRepresentedOver m V := by
    refine IsCutOutByMonoFP.of_forall fun T ↦ (D.presented_iff m V U hUs T).2 ?_
    exact (D.stageSituation B S hS m V U).isFlat_of_isFlatOverInDimensionsGE
      ((_root_.AlgebraicGeometry.isFlatOverInDimensionsGE_of_fiber_le
        (D.stageSituation B S hS m V U).f (D.stageSituation B S hS m V U).F hN).mono hm) T
  -- the induction step
  have hstep (m : ℕ) (h : D.IsRepresentedOver (m + 1) V) : D.IsRepresentedOver m V := by
    obtain ⟨Z, hZm, hZfp, hZ⟩ := h
    have := hZm
    obtain ⟨h1, h2, h3⟩ := hZfp
    have hZc : B.Contains Z.left :=
      (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact Z.hom).trans_lt V.left.left.2
    have : LocallyQuasiFinite Z.hom := (isSeparated_and_locallyQuasiFinite_of_mono Z.hom).2
    let VZ := schemesOverOfContained V hZc Z.hom
    let βZ : VZ ⟶ V := schemesOverOfContainedMap V hZc Z.hom
    have hqfZ : IsLocallyQuasiFinite B S hS VZ.hom.hom :=
      D.isLocallyQuasiFinite_schemesOverOfContained V hqf hZc Z.hom
    have hflatZ : D.Presented (m + 1) VZ (Over.mk (𝟙 _)) := by
      rw [D.presented_baseChange_iff (m + 1) βZ]
      exact (hZ _).2 ⟨Over.homMk (𝟙 _) rfl⟩
    have hrepZ := D.isRepresentedOver_of_isFlat hf hF hpure m VZ hqfZ hflatZ
    refine IsCutOutByMonoFP.comp (fun g h ↦ D.presented_of_hom m V g h) (fun T hT ↦ ?_) hZm
      ⟨h1, h2, h3⟩ hZ (hrepZ.of_iff fun T ↦ D.presented_baseChange_iff m βZ T)
    rw [D.presented_iff m V U hUs] at hT
    rw [D.presented_iff (m + 1) V U hUs]
    exact (D.stageSituation B S hS m V U).isFlat_withN_mono (Nat.le_succ m) T hT
  have hind : ∀ k m, N + 1 ≤ m + k → D.IsRepresentedOver m V := by
    intro k
    induction k with
    | zero => exact fun m hm ↦ hbig m (by omega)
    | succ k ih => exact fun m hm ↦ hstep m (ih (m + 1) (by omega))
  exact hind (N + 1 - n) n (by omega)

/-- **The locus `F_n` is represented over every quasi-finite test scheme.** In Situation 0CWU
with `f` and `F` of finite presentation and `F` pure relative to `Y`, for every test scheme `V`
over `Y` whose structure morphism is locally quasi-finite, `F_n` over `V` is cut out by a
monomorphism of finite presentation. -/
theorem isRepresentedOver (hf : IsFinitePresentation B S hS D.f.hom)
    (hF : SheafOfModules.IsFinitePresentationOnSite D.F)
    (hpure : ∀ y, IsPureAbove (D.fpPrePureSituation hf y)) (n : ℕ) (V : SchemesOver D.Y)
    (hqf : IsLocallyQuasiFinite B S hS V.hom.hom) : D.IsRepresentedOver n V :=
  D.isRepresentedOver_of_affine_local n V hqf fun V' hV' hqf' _ ↦
    D.isRepresentedOver_of_isAffine hf hF hpure V' hV' hqf' n

end FlatDimensionSituation

end AlgebraicGeometry.Space

end
