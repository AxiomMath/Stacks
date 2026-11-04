module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SeparablyClosed

/-!
# Local charts of the Picard scheme of a curve

Let `P` represent a presheaf `F` on the big fppf site over `S`, and let `G ⊂ F` be a subfunctor
whose pullback along `T ⟶ P` is cut out by an open `U ⊂ P` (an *open subfunctor*). If `G` is
represented by `W`, then `W` is the open subscheme `U` of `P`
(`AlgebraicGeometry.BigFppfOver.subfunctorOpenIso`).

For the Picard scheme `Pic_{X/k}` of a pointed smooth projective curve `X` over a separably
closed field `k`, the translates `F_g` of the normalized subfunctor `F` by rational points are
open subfunctors, each represented by the open `W` of the Hilbert scheme `Hilb^g_{X/k}` which
represents `F` ([Stacks, Tag 0B9X], fibrewise form), and they cover `Pic_{X/k}` (proof of
[Stacks, Tag 0B9Z]). So `Pic_{X/k}` is covered by opens isomorphic to `W`; since `Hilb^g_{X/k}`
is smooth of dimension `g` ([Stacks, Tag 0B9I]), `Pic_{X/k}` is smooth of relative dimension `g`
over `k`. This is the smoothness statement in the proof of [Stacks, Tag 0BA0].

## Main results

* `AlgebraicGeometry.BigFppfOver.subfunctorOpenIso`.
* `Stacks.PicardFunctor.smoothOfRelativeDimension_picardScheme`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w} {P : BigFppfOver B S hS} (R : F.RepresentableBy P)
  (G : Subfunctor F) {W : BigFppfOver B S hS} (RW : G.toFunctor.RepresentableBy W)
  (U : P.left.obj.Opens)
  (hU : ∀ {T : BigFppfOver B S hS} (h : T ⟶ P), R.homEquiv h ∈ G.obj (op T) ↔
    Set.range ⇑((BigFppfOver.toScheme B S hS).map h) ⊆ (U : Set P.left.obj))

/-- The morphism `W ⟶ P` classifying the universal point of the subfunctor `G`. -/
abbrev subfunctorHom : W ⟶ P := R.homEquiv.symm (RW.homEquiv (𝟙 W)).1

include hU in
/-- The image of the morphism `W ⟶ P` classifying the universal point of `G` lies in `U`. -/
theorem range_subfunctorHom_subset :
    Set.range ⇑((BigFppfOver.toScheme B S hS).map (subfunctorHom B S hS R G RW)) ⊆
      (U : Set P.left.obj) :=
  (hU _).1 (by rw [Equiv.apply_symm_apply]; exact (RW.homEquiv (𝟙 W)).2)

include hU in
/-- The point of `F` over the open `U` given by the inclusion `U ⟶ P` lies in `G`. -/
theorem homEquiv_openSubHom_mem :
    R.homEquiv (openSubHom B S hS P U) ∈ G.obj (op (openSubObj B S hS P U)) :=
  (hU _).2 (by rw [AlgebraicGeometry.Space.openSubHom_toScheme, Scheme.Opens.range_ι])

/-- The lift of `W ⟶ P` to the open `U`. -/
def subfunctorOpenHom : W ⟶ openSubObj B S hS P U :=
  AlgebraicGeometry.Space.openSubObjLift B S hS P U (subfunctorHom B S hS R G RW)
    (range_subfunctorHom_subset B S hS R G RW U hU)

/-- The morphism `U ⟶ W` classifying the restriction of the universal point to `U`. -/
def subfunctorOpenInv : openSubObj B S hS P U ⟶ W :=
  RW.homEquiv.symm ⟨_, homEquiv_openSubHom_mem B S hS R G U hU⟩

/-- The lift `W ⟶ U` composed with the inclusion `U ⟶ P` is the morphism `W ⟶ P`. -/
theorem subfunctorOpenHom_comp :
    subfunctorOpenHom B S hS R G RW U hU ≫ openSubHom B S hS P U =
      subfunctorHom B S hS R G RW :=
  AlgebraicGeometry.Space.openSubObjLift_comp_openSubHom B S hS P U _ _

/-- The point of `G` classified by `U ⟶ W` is the point of `F` given by the inclusion `U ⟶ P`. -/
theorem homEquiv_subfunctorOpenInv :
    (RW.homEquiv (subfunctorOpenInv B S hS R G RW U hU)).1 =
      R.homEquiv (openSubHom B S hS P U) :=
  congrArg Subtype.val (Equiv.apply_symm_apply RW.homEquiv _)

/-- **An open subfunctor represented by `W` is the open subscheme it is cut out by**: `W` is
isomorphic, over `P`, to the open `U` of `P`. -/
def subfunctorOpenIso : W ≅ openSubObj B S hS P U where
  hom := subfunctorOpenHom B S hS R G RW U hU
  inv := subfunctorOpenInv B S hS R G RW U hU
  hom_inv_id := by
    refine RW.homEquiv.injective (Subtype.ext ?_)
    have h1 := congrArg Subtype.val (RW.homEquiv_comp (subfunctorOpenHom B S hS R G RW U hU)
      (subfunctorOpenInv B S hS R G RW U hU))
    have h2 := R.homEquiv_comp (subfunctorOpenHom B S hS R G RW U hU) (openSubHom B S hS P U)
    rw [subfunctorOpenHom_comp, Equiv.apply_symm_apply] at h2
    refine h1.trans ?_
    change F.map _ (RW.homEquiv (subfunctorOpenInv B S hS R G RW U hU)).1 = _
    rw [homEquiv_subfunctorOpenInv, ← h2]
  inv_hom_id := by
    apply (AlgebraicGeometry.Space.mono_openSubHom B S hS P U).right_cancellation
    rw [Category.assoc, subfunctorOpenHom_comp, Category.id_comp]
    apply R.homEquiv.injective
    have h1 := R.homEquiv_comp (subfunctorOpenInv B S hS R G RW U hU) (subfunctorHom B S hS R G RW)
    rw [Equiv.apply_symm_apply] at h1
    have h2 := congrArg Subtype.val (RW.homEquiv_comp
      (subfunctorOpenInv B S hS R G RW U hU) (𝟙 W))
    rw [Category.comp_id] at h2
    refine h1.trans ?_
    rw [← homEquiv_subfunctorOpenInv B S hS R G RW U hU, h2]
    rfl

/-- The isomorphism `W ≅ U` composed with the inclusion `U ⟶ P` is the morphism `W ⟶ P`. -/
theorem subfunctorOpenIso_hom_comp :
    (subfunctorOpenIso B S hS R G RW U hU).hom ≫ openSubHom B S hS P U =
      subfunctorHom B S hS R G RW :=
  subfunctorOpenHom_comp B S hS R G RW U hU

end AlgebraicGeometry.BigFppfOver

namespace Stacks.PicardFunctor

/-- Smoothness of a given relative dimension is local on the source. -/
theorem isZariskiLocalAtSource_smoothOfRelativeDimension (n : ℕ) :
    IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
  HasRingHomProperty.instIsZariskiLocalAtSource
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))

attribute [local instance] isZariskiLocalAtSource_smoothOfRelativeDimension

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)

/-- The translate `F_g` of the normalized subfunctor, for a pointed smooth projective curve. -/
abbrev curveTranslate (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) :
    Subfunctor (picardFunctor B hX hk f) :=
  (curveNormalized B hX hk f σ hσ).preimage (translate B hX hk f g).hom

/-- Translation identifies `F_g` with `F`. -/
def curveTranslateIso (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) :
    (curveTranslate B hX hk f σ hσ g).toFunctor ≅ (curveNormalized B hX hk f σ hσ).toFunctor :=
  NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := fun x => ⟨(translate B hX hk f g).hom.app T x.1, x.2⟩
        invFun := fun y => ⟨(translate B hX hk f g).inv.app T y.1, by
          change (translate B hX hk f g).hom.app T ((translate B hX hk f g).inv.app T y.1) ∈
            (curveNormalized B hX hk f σ hσ).obj T
          rw [Iso.inv_hom_id_app_apply]
          exact y.2⟩
        left_inv := fun x => Subtype.ext (Iso.hom_inv_id_app_apply _ _ _)
        right_inv := fun y => Subtype.ext (Iso.inv_hom_id_app_apply _ _ _) })
    (fun {T T'} φ => by
      ext x
      apply Subtype.ext
      change (translate B hX hk f g).hom.app T' ((picardFunctor B hX hk f).map φ x.1) =
        (picardFunctor B hX hk f).map φ ((translate B hX hk f g).hom.app T x.1)
      exact NatTrans.naturality_apply (translate B hX hk f g).hom φ x.1)

variable (H : BigFppfOver B (Spec (.of k)) hk)
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map H.hom)) (genus (B.inclusion.map f)))

/-- `F_g` is represented by the open `W` of the Hilbert scheme. -/
def curveTranslateRepresentableBy (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) :
    (curveTranslate B hX hk f σ hσ g).toFunctor.RepresentableBy
      (normalizedHilbertOpen B hX hk f σ hσ H hH) :=
  (normalizedRepresentableBy B hX hk f σ hσ H hH).ofIso (curveTranslateIso B hX hk f σ hσ g).symm

variable [(picardFunctor B hX hk f).IsRepresentable]

omit [GeometricallyIrreducible (B.inclusion.map f)] in
/-- The open-locus property of `F_g` on the Picard scheme. -/
theorem homEquiv_mem_curveTranslate_iff (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    {T : BigFppfOver B (Spec (.of k)) hk} (h : T ⟶ picardSchemeOver B hX hk f) :
    (picardFunctor B hX hk f).representableBy.homEquiv h ∈
        (curveTranslate B hX hk f σ hσ g).obj (op T) ↔
      Set.range ⇑((BigFppfOver.toScheme B (Spec (.of k)) hk).map h) ⊆
        (curveNormalizedLocus B hX hk f σ hσ (picardSchemeOver B hX hk f)
          ((translate B hX hk f g).hom.app (op (picardSchemeOver B hX hk f))
            (universalPoint B hX hk f)) : Set (picardSchemeOver B hX hk f).left.obj) := by
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  change picardHomEquiv B hX hk f h ∈ _ ↔ _
  rw [picardHomEquiv_eq_map]
  refine (map_mem_translateSubfunctor_iff B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
    (topologicalKrullDim_le_one_of_isCurve B hX hk f) g h _).trans ?_
  exact ⟨fun h' _ ⟨t, ht⟩ => ht ▸ h' t, fun h' t => h' ⟨t, rfl⟩⟩

/-- **Every translate `F_g` is the open subscheme of the Picard scheme over which the translate
of the universal point is normalized, and that open is isomorphic to `W ⊂ Hilb^g_{X/k}`.** -/
def translateChartIso (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) :
    normalizedHilbertOpen B hX hk f σ hσ H hH ≅
      BigFppfOver.openSubObj B _ hk (picardSchemeOver B hX hk f)
        (curveNormalizedLocus B hX hk f σ hσ (picardSchemeOver B hX hk f)
          ((translate B hX hk f g).hom.app (op (picardSchemeOver B hX hk f))
            (universalPoint B hX hk f))) :=
  BigFppfOver.subfunctorOpenIso B _ hk (picardFunctor B hX hk f).representableBy
    (curveTranslate B hX hk f σ hσ g) (curveTranslateRepresentableBy B hX hk f σ hσ H hH g) _
    (homEquiv_mem_curveTranslate_iff B hX hk f σ hσ g)

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable] in
include σ hσ in
/-- **The open `W ⊂ Hilb^g_{X/k}` representing the normalized subfunctor is smooth of relative
dimension `g` over `k`** ([Stacks, Tag 0B9I]). -/
theorem smoothOfRelativeDimension_normalizedHilbertOpen :
    SmoothOfRelativeDimension (genus (B.inclusion.map f))
      (B.inclusion.map (normalizedHilbertOpen B hX hk f σ hσ H hH).hom) :=
  IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension (genus (B.inclusion.map f)))
    (Stacks.Hilbert.smoothOfRelativeDimension_and_isProper_of_isCurve k
      (B.inclusion.map f) _ _ hH).1 (normalizedOpen B hX hk f σ hσ H hH).ι

variable [IsSepClosed k]

include σ hσ in
/-- **The Picard scheme of a smooth projective curve over a separably closed field is smooth of
relative dimension `g` over `k`.** It is covered by the translates of the normalized open, each
isomorphic to the open `W` of `Hilb^g_{X/k}`. -/
theorem smoothOfRelativeDimension_picardScheme :
    SmoothOfRelativeDimension (genus (B.inclusion.map f))
      (B.inclusion.map (picardSchemeOver B hX hk f).hom) := by
  obtain ⟨H, ⟨hH⟩⟩ := exists_hilbertScheme B hX hk f
  let U : (picardFunctor B hX hk f).obj (op (baseObj B hk)) → (picardScheme B hX hk f).Opens :=
    fun g => curveNormalizedLocus B hX hk f σ hσ (picardSchemeOver B hX hk f)
      ((translate B hX hk f g).hom.app (op (picardSchemeOver B hX hk f))
        (universalPoint B hX hk f))
  refine IsZariskiLocalAtSource.of_iSup_eq_top U ?_ fun g => ?_
  · exact top_unique fun t _ => TopologicalSpace.Opens.mem_iSup.2
      (exists_translate_mem_curveNormalizedLocus B hX hk f σ hσ
        (twistToNormalized_of_isSepClosed B hX hk f
          ((isProjectiveVariety_iff_isProjective k _).1 inferInstance)) _
        (universalPoint B hX hk f) t)
  · let e := translateChartIso B hX hk f σ hσ H hH g
    have he : B.inclusion.map e.inv.left ≫
        B.inclusion.map (normalizedHilbertOpen B hX hk f σ hσ H hH).hom =
        (U g).ι ≫ B.inclusion.map (picardSchemeOver B hX hk f).hom := by
      rw [← Functor.map_comp, Over.w e.inv]
      rfl
    rw [← he]
    have : IsIso (B.inclusion.map e.inv.left) :=
      inferInstanceAs (IsIso ((Over.forget _ ⋙ B.inclusion).mapIso e).inv)
    exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension (genus (B.inclusion.map f)))
      (smoothOfRelativeDimension_normalizedHilbertOpen B hX hk f σ hσ H hH)
      (B.inclusion.map e.inv.left)

end Stacks.PicardFunctor

end
