module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.HilbertChartFull
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardZeroCurve

/-!
# `Pic_{X/k,σ}` of a curve is a group scheme (Stacks 0B9Z)

The proof of [Stacks, Tag 0B9Z]: the group-scheme criterion ([Stacks, Tag 0B9Q]) applied to the
rigidified Picard functor `Pic_{X/k,σ}` of a proper smooth curve with a rational point, with the
open chart `W ⊆ Hilb^g` of [Stacks, Tag 0B9X] for the subfunctor of [Stacks, Tag 0B9V], and
condition (2)(c) from [Stacks, Tag 0B9Y]. The claim of [Stacks, Tag 0B9X] (`hexists`, `huniq`)
and [Stacks, Tag 0B9Y] (`h0B9Y`) are hypotheses.

## Main results

* `Stacks.RigidifiedPicard.exists_translate_mem_cohomologySubfunctor` — condition (2)(c).
* `Stacks.RigidifiedPicard.exists_smooth_grp_iso_functor` — the group scheme, smooth over `k`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
  [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
  (hdimX : topologicalKrullDim X ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- The Picard class of `X_T` of an element of `Pic_{X/k,σ}(T)`. -/
def classOf {T : Over (Spec (.of k))} (x : (functor f σ hσ ⋙ forget GrpCat).obj (op T)) :
    Stacks.Picard.ofScheme (bc f T) :=
  smallEquiv _ ((Multiplicative.toAdd x : group f σ hσ T) : Stacks.Picard.smallOfScheme (bc f T))

omit [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f] in
include hdimX in
/-- **Condition (2)(c) of [Stacks, Tag 0B9Q] for `Pic_{X/k,σ}`, from [Stacks, Tag 0B9Y].** -/
theorem exists_translate_mem_cohomologySubfunctor
    (h0B9Y : ∀ (K : Type u) [Field K] [Algebra k K]
      (c : Stacks.Picard.ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      ∃ c₀ : Stacks.Picard.ofScheme X,
        Module.finrank K (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀)).obj 0) = 1 ∧
        IsZero (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀)).obj 1))
    (K : Type u) [Field K] [Algebra k K]
    (x : (functor f σ hσ ⋙ forget GrpCat).obj (op (fieldExtensionPoint k K))) :
    ∃ r : (functor f σ hσ ⋙ forget GrpCat).obj (op (Over.mk (𝟙 (Spec (.of k))))),
      (functor f σ hσ).map (Over.homMk (fieldExtensionPoint k K).hom).op r * x ∈
        (cohomologySubfunctor f σ hσ
          (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
          baseChangeDerivedPushforward 0).obj (op (fieldExtensionPoint k K)) := by
  set c := classOf f σ hσ x with hcdef
  obtain ⟨c₀, h0, h1⟩ := h0B9Y K c
  let r := Multiplicative.ofAdd (mkGroup f σ hσ (normalize f σ hσ (Over.mk (𝟙 (Spec (.of k))))
    (Stacks.Picard.schemePullbackClass (pullback.fst f (Over.mk (𝟙 (Spec (.of k)))).hom) c₀))
    (schemePullbackClass_bcSection_normalize f σ hσ _ _))
  refine ⟨r, ?_⟩
  have hT0 : ∀ n : Stacks.Picard.ofScheme (fieldExtensionPoint k K).left, n = 0 :=
    Stacks.Picard.eq_zero_of_isField K
  have hcl : classOf f σ hσ
      ((functor f σ hσ).map (Over.homMk (fieldExtensionPoint k K).hom).op r * x) =
      c + Stacks.Picard.schemePullbackClass (pullback.fst f (fieldExtensionPoint k K).hom) c₀ := by
    show smallEquiv (bc f (fieldExtensionPoint k K)) ((groupMap f σ hσ
      (Over.homMk (fieldExtensionPoint k K).hom : fieldExtensionPoint k K ⟶ Over.mk (𝟙 _))
        (mkGroup f σ hσ _ (schemePullbackClass_bcSection_normalize f σ hσ _ _)) +
        (Multiplicative.toAdd x : group f σ hσ (fieldExtensionPoint k K)) :
        group f σ hσ (fieldExtensionPoint k K)) :
          Stacks.Picard.smallOfScheme (bc f (fieldExtensionPoint k K))) = _
    rw [AddSubgroup.coe_add, map_add, coe_groupMap, smallEquiv_smallSchemePullbackClassHom,
      smallEquiv_mkGroup, normalize_bcMap, Stacks.Picard.schemePullbackClass_comp, bcMap_fst,
      normalize_eq_self f σ hσ _ _ (hT0 _), add_comm]
    rfl
  show IsCohomologyClass f 0 (fieldExtensionPoint k K) (classOf f σ hσ _)
  rw [hcl, isCohomologyClass_zero_iff]
  set P := Stacks.Picard.picardRepresentative (bc f (fieldExtensionPoint k K)).toRingedSpace
    (c + Stacks.Picard.schemePullbackClass (pullback.fst f (fieldExtensionPoint k K).hom) c₀)
  have hz : ∀ n, IsZero (cohomologyOverField K (bcProj f (fieldExtensionPoint k K)) P.obj n) →
      Module.finrank K (cohomologyOverField K (bcProj f (fieldExtensionPoint k K)) P.obj n) = 0 :=
    fun n h => have := ModuleCat.subsingleton_of_isZero h; Module.finrank_zero_of_subsingleton
  obtain ⟨hF, hflat⟩ := isFinitePresentation_and_isFlatOver_of_isInvertible
    (bcProj f (fieldExtensionPoint k K)) _ P.property
  refine hasDerivedPushforwardRank_of_finrank K (bcProj f (fieldExtensionPoint k K))
    (finitePresentation_bcProj f (fieldExtensionPoint k K)) _ hF hflat 0 1 h0 fun j hj => ?_
  rcases j with _ | _ | j
  · exact absurd rfl hj
  · exact hz 1 h1
  · exact hz _ (isZero_cohomologyOverField_of_topologicalKrullDim_le K
      (bcProj f (fieldExtensionPoint k K)) P.obj (d := 1)
      (by exact_mod_cast topologicalKrullDim_bc_fieldExtensionPoint_le f hdimX K)
      (by omega : 1 < j + 2))

include hdimX in
/-- **[Stacks, Tag 0B9Z] for `Pic_{X/k,σ}`, given the claim of [Stacks, Tag 0B9X] and
[Stacks, Tag 0B9Y].** The rigidified Picard functor of a proper smooth curve with a rational point
is represented by a group scheme over `k`, smooth over `k`. -/
theorem exists_smooth_grp_iso_functor (H : ℕ → Over (Spec (.of k)))
    (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d)
    (hexists : ∀ (T : Over (Spec (.of k))) (c : Stacks.Picard.ofScheme (bc f T)),
      HasInvertibleDirectImage f T c →
        ∃ (Z : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f))
          (n : Stacks.Picard.ofScheme T.left),
          abelClass f Z = c + Stacks.Picard.schemePullbackClass (bcProj f T) n)
    (huniq : ∀ (T : Over (Spec (.of k)))
      (Z Z' : Stacks.Hilbert.HilbertFamily (Over.mk f) T (genus f)),
      HasInvertibleDirectImage f T (abelClass f Z) →
        (∃ n : Stacks.Picard.ofScheme T.left,
          abelClass f Z' = abelClass f Z + Stacks.Picard.schemePullbackClass (bcProj f T) n) →
          Z = Z')
    (h0B9Y : ∀ (K : Type u) [Field K] [Algebra k K]
      (c : Stacks.Picard.ofScheme (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
      ∃ c₀ : Stacks.Picard.ofScheme X,
        Module.finrank K (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀)).obj 0) = 1 ∧
        IsZero (cohomologyOverField K
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (Stacks.Picard.picardRepresentative _ (c +
            Stacks.Picard.schemePullbackClass
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) c₀)).obj 1)) :
    ∃ A : Grp (Over (Spec (.of k))), Nonempty (yonedaGrp.obj A ≅ functor f σ hσ) ∧
      SmoothOfRelativeDimension (genus f) A.X.hom := by
  have : IsIntegral X := isIntegral_of_smooth_geometricallyIrreducible f
  obtain ⟨W, ⟨R⟩⟩ := exists_representableBy_cohomologySubfunctor f σ hσ
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward 0 (hH (genus f)) hexists huniq
  have hopen := (isOpenSubfunctor_cohomologySubfunctor f σ hσ
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward 0).isOpenImmersion_presheaf_ι
  have hfield := exists_translate_mem_cohomologySubfunctor f hdimX σ hσ h0B9Y
  obtain ⟨A, ⟨e⟩⟩ := exists_grp_iso_of_representable_openSubfunctor k (functor f σ hσ)
    (isSheaf_functor f σ hσ (isIso_bcProj_c f σ hσ)) _ ⟨_, ⟨R⟩⟩ hopen hfield
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (genus f)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have hH' : SmoothOfRelativeDimension (genus f) (H (genus f)).hom :=
    have : IsSeparated (Over.mk f).hom := (inferInstance : IsSeparated f)
    have : SmoothOfRelativeDimension 1 (Over.mk f).hom := ‹SmoothOfRelativeDimension 1 f›
    Stacks.Hilbert.smoothOfRelativeDimension_of_represents H hH (genus f)
  have hPW : SmoothOfRelativeDimension (genus f) (Over.mk (W.ι ≫ (H (genus f)).hom)).hom :=
    IsZariskiLocalAtSource.comp hH' W.ι
  exact ⟨A, ⟨e⟩, of_chart_of_isZariskiLocalAtSource A e _ _ _
    (Functor.representableByEquiv R) hopen hfield hPW⟩

end Stacks.RigidifiedPicard

end
