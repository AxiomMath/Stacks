module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.NormalizedRepresentable
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.RepresentabilityReduction
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.CardinalBound
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurve
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyBaseChange

/-!
# Representability of the Picard functor of a pointed curve, from the translation property

Let `X` be a geometrically irreducible smooth projective curve over a field `k` with a rational
point. The normalized subfunctor of `Pic_{X/k}` is an open of the Hilbert scheme `Hilb^g_{X/k}`
([Stacks, Tag 0B9X], `Stacks.PicardFunctor.normalizedRepresentableBy`), the Picard group of `X`
is bounded below the cutoff of the site, and so the gluing step of [Stacks, Tag 0B9Q]
(`Stacks.PicardFunctor.isRepresentable_picardFunctor_of_normalized`) represents `Pic_{X/k}` as
soon as every point is translated into the normalized subfunctor by a rational point near every
point of its base — the family form of [Stacks, Tag 0B9Y].

## Main results

* `Stacks.PicardFunctor.contains_hilbertScheme`: the Hilbert scheme lies in the site.
* `Stacks.PicardFunctor.isRepresentable_picardFunctor_of_translates`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Cardinal
open Stacks.PicardCurve

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]

include hk in
/-- **A scheme of finite type over `k` lies in the site.** -/
theorem contains_of_isProper {Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsProper g] :
    B.Contains Y :=
  lt_of_le_of_lt (Scheme.size_le_of_locallyOfFiniteType_of_quasiCompact g) hk

omit [GeometricallyIrreducible (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- **The degree-`g` Hilbert scheme of the curve, as an object of the site, with its universal
property** ([Stacks, Tag 0B9I]). -/
theorem exists_hilbertScheme : ∃ (H : BigFppfOver B (Spec (.of k)) hk),
    Nonempty (Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map H.hom)) (genus (B.inclusion.map f))) := by
  obtain ⟨⟨H₀, hH₀⟩⟩ := Stacks.Hilbert.nonempty_representsHilbertFunctorOfRank_of_isCurve k
    (B.inclusion.map f) (genus (B.inclusion.map f))
  have : IsProper H₀.hom := (Stacks.Hilbert.smoothOfRelativeDimension_and_isProper_of_isCurve k
    (B.inclusion.map f) _ H₀ hH₀).2
  exact ⟨Over.mk (ObjectProperty.homMk (X := B.obj (contains_of_isProper B hk H₀.hom))
    (Y := B.obj hk) H₀.hom), ⟨hH₀⟩⟩

/-- The base change `X_k = X ×_k k` of the curve to the base object of the site. -/
abbrev baseCurve : Scheme.{u} := baseChange B hX hk f (baseObj B hk)

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The first projection `X ×_k k ⟶ X` of the base change of the curve along the identity of
`Spec k` is an isomorphism. -/
theorem isIso_baseCurve_fst : IsIso (pullback.fst (B.inclusion.map f)
    (B.inclusion.map (baseObj B hk).hom)) := by
  change IsIso (pullback.fst (B.inclusion.map f) (𝟙 _))
  infer_instance

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The base change `X ×_k k` has the same size as the curve `X`. -/
theorem size_baseCurve : (baseCurve B hX hk f).size = X.size :=
  have := isIso_baseCurve_fst B hX hk f
  Scheme.size_congr (asIso (pullback.fst (B.inclusion.map f) (B.inclusion.map (baseObj B hk).hom)))

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The base change `X ×_k k` is the pullback of the structure morphism `X ⟶ Spec k` along the
morphism `Spec k ⟶ Spec k` induced by `algebraMap k k`. -/
theorem isPullback_baseCurve : IsPullback
    (pullback.fst (B.inclusion.map f) (B.inclusion.map (baseObj B hk).hom))
    (baseChangeProj B hX hk f (baseObj B hk)) (B.inclusion.map f)
    (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
  have h : Spec.map (CommRingCat.ofHom (algebraMap k k)) = B.inclusion.map (baseObj B hk).hom := by
    change Spec.map (CommRingCat.ofHom (RingHom.id k)) = 𝟙 _
    rw [← Spec.map_id]
    rfl
  rw [h]
  exact IsPullback.of_hasPullback _ _

omit [IsCurve k (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The base change `X ×_k k` of the curve is an integral scheme. -/
theorem isIntegral_baseCurve : IsIntegral (baseCurve B hX hk f) :=
  Stacks.AbelMap.isIntegral_of_isPullback (K := k) (B.inclusion.map f) _ _
    (isPullback_baseCurve B hX hk f)

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [IsProper (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The base change `X ×_k k` of the curve is locally Noetherian. -/
theorem isLocallyNoetherian_baseCurve : IsLocallyNoetherian (baseCurve B hX hk f) := by
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B _ hk).obj (baseObj B hk)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))
  exact LocallyOfFiniteType.isLocallyNoetherian (baseChangeProj B hX hk f (baseObj B hk))

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [IsProper (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The base change `X ×_k k` of the curve is a normal scheme. -/
theorem isNormal_baseCurve : IsNormal (baseCurve B hX hk f) :=
  have : IsNormal ((BigFppfOver.toScheme B _ hk).obj (baseObj B hk)) :=
    isNormal_spec_of_isNormalRing (R := k) (IsNormalRing.of_isIntegrallyClosed k)
  isNormal_of_smooth (baseChangeProj B hX hk f (baseObj B hk))

variable (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)

omit [IsProper (B.inclusion.map f)] in
include σ hσ in
/-- **The `k`-points of the Picard functor of the curve are bounded below the cutoff.** -/
theorem mk_picardFunctor_baseObj_le :
    #((picardFunctor B hX hk f).obj (op (baseObj B hk))) ≤
      Cardinal.lift.{u + 1} ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ X.size) := by
  have := isIntegral_baseCurve B hX hk f
  have := isLocallyNoetherian_baseCurve B hX hk f
  have := isNormal_baseCurve B hX hk f
  refine (Cardinal.mk_le_of_surjective (surjective_toPicardFunctorHom B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) (baseObj B hk))).trans ?_
  have h := Stacks.Picard.lift_mk_ofScheme_le (baseCurve B hX hk f)
  rwa [size_baseCurve] at h

/-- The open of a test scheme over which a point of the Picard functor of the curve is
normalized. -/
def curveNormalizedLocus (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T)) : T.left.obj.Opens :=
  haveI := isSeparated_of_isCurve B hX hk f
  haveI := isNoetherian_of_isCurve B hX hk f
  normalizedLocus B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ)
    (topologicalKrullDim_le_one_of_isCurve B hX hk f) T ξ

include σ hσ in
/-- **Representability of the Picard functor of a pointed curve from the translation property**
(the gluing of [Stacks, Tag 0B9Q] in the proof of [Stacks, Tag 0B9Z]): if every point of
`Pic_{X/k}` is, near every point of its base, translated into the normalized subfunctor by a
`k`-rational point, then `Pic_{X/k}` is representable. -/
theorem isRepresentable_picardFunctor_of_translates
    (htrans : ∀ (T : BigFppfOver B (Spec (.of k)) hk)
      (ξ : (picardFunctor B hX hk f).obj (op T)) (t : (BigFppfOver.toScheme B _ hk).obj T),
      ∃ g, t ∈ curveNormalizedLocus B hX hk f σ hσ T ((translate B hX hk f g).hom.app (op T) ξ)) :
    (picardFunctor B hX hk f).IsRepresentable := by
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  obtain ⟨H, ⟨hH⟩⟩ := exists_hilbertScheme B hX hk f
  let W := normalizedHilbertOpen B hX hk f σ hσ H hH
  let c : Cardinal.{u} :=
    max ((2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^ X.size)
      ((BigFppfOver.toScheme B _ hk).obj W).size
  have hc : c < B.cutoff := max_lt (B.cutoff_isStrongPrelimit (B.cutoff_isStrongPrelimit hX))
    W.left.property
  exact isRepresentable_picardFunctor_of_normalized B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) (topologicalKrullDim_le_one_of_isCurve B hX hk f) W
    (normalizedRepresentableBy B hX hk f σ hσ H hH) htrans c hc
    ((mk_picardFunctor_baseObj_le B hX hk f σ hσ).trans (Cardinal.lift_le.2 (le_max_left _ _)))
    (le_max_right _ _)

/-- **The conclusion of [Stacks, Tag 0B9Y]** for the curve `X`: every invertible module on a base
change `X_K` to a field extension is twisted, by an invertible module on `X`, to one with
`dim H⁰ = 1` and `H¹ = 0`. -/
def TwistToNormalized : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] {X' : Scheme.{u}} (f' : X' ⟶ Spec (.of K))
    (p : X' ⟶ X), IsPullback p f' (B.inclusion.map f)
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) →
    ∀ (L : X'.Modules), Stacks.Ample.IsInvertibleModule X' L →
      ∃ L₀ : X.Modules, Stacks.Ample.IsInvertibleModule X L₀ ∧
        Module.finrank K (cohomologyOverField K f' (baseChangeTwist p L L₀) 0) = 1 ∧
        Module.finrank K (cohomologyOverField K f' (baseChangeTwist p L L₀) 1) = 0

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- Translation by the class of a point `x₀` of `Pic(X_k)` sends the class of `x ∈ Pic(X_T)` to
the class of the sum of `x` and the pullback of `x₀`. -/
theorem translate_toPicardFunctorHom (T : BigFppfOver B (Spec (.of k)) hk)
    (x₀ : picardAt B hX hk f (baseObj B hk)) (x : picardAt B hX hk f T) :
    (translate B hX hk f (toPicardFunctorHom B hX hk f (baseObj B hk) x₀)).hom.app (op T)
      (toPicardFunctorHom B hX hk f T x) =
      toPicardFunctorHom B hX hk f T (picardMap B hX hk f (toBaseObj B hk T) x₀ + x) := by
  rw [translate_hom_app, map_add]
  congr 1
  exact (toPicardFunctor_app_naturality B hX hk f (toBaseObj B hk T) x₀).symm

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- The restriction to the fibre of `X_T` at `t` of the pullback to `T` of the class of `L₀`
on `X_k` is the class of the pullback of `L₀` to that fibre. -/
theorem schemePullbackClass_fiberι_picardMap (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B _ hk).obj T) (L₀ : X.Modules)
    (hL₀q : Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback
      (pullback.fst (B.inclusion.map f) (B.inclusion.map (baseObj B hk).hom))).obj L₀))
    (hpL₀ : Stacks.SheafOfModules.IsInvertible ((baseChangeProj B hX hk f T).fiber t).presheaf
      (Stacks.RingedSpace.structureIsSheaf ((baseChangeProj B hX hk f T).fiber t).toRingedSpace)
      ((Scheme.Modules.pullback ((baseChangeProj B hX hk f T).fiberι t ≫
        pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom))).obj L₀)) :
    Stacks.Picard.schemePullbackClass ((baseChangeProj B hX hk f T).fiberι t)
      (picardMap B hX hk f (toBaseObj B hk T)
        (Stacks.SheafOfModules.picardClass _ _ ((Scheme.Modules.pullback
          (pullback.fst (B.inclusion.map f) (B.inclusion.map (baseObj B hk).hom))).obj L₀) hL₀q)) =
      Stacks.SheafOfModules.picardClass _ _ ((Scheme.Modules.pullback
        ((baseChangeProj B hX hk f T).fiberι t ≫
          pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom))).obj L₀) hpL₀ := by
  set fT := baseChangeProj B hX hk f T
  set p := fT.fiberι t ≫ pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom)
  set q := pullback.fst (B.inclusion.map f) (B.inclusion.map (baseObj B hk).hom)
  have hpq : (fT.fiberι t ≫ baseChangeMap B hX hk f (toBaseObj B hk T)) ≫ q = p := by
    rw [Category.assoc]
    congr 1
    simp [q, baseChangeMap]
  change Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ _) = _
  rw [Stacks.Picard.schemePullbackClass_comp]
  refine (Stacks.Picard.pullbackClass_classOf _ _ hL₀q).trans ?_
  refine (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨?_⟩
  set g := fT.fiberι t ≫ baseChangeMap B hX hk f (toBaseObj B hk T)
  let e₁ : (Stacks.RingedSpace.pullbackFunctor g.toLRSHom.toShHom).obj
      ((Scheme.Modules.pullback q).obj L₀) ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj L₀) :=
    ((Stacks.ProjectiveBundleQuotients.pullbackIso g).app _).symm
  let e₂ : (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback q).obj L₀) ≅
      (Scheme.Modules.pullback p).obj L₀ :=
    (Scheme.Modules.pullbackComp g q).app L₀ ≪≫ (Scheme.Modules.pullbackCongr hpq).app L₀
  exact e₁ ≪≫ e₂

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)] in
include σ hσ in
/-- The fibre ranks at `t` of the class of `y ∈ Pic(X_T)` are the cohomology dimensions of any
invertible module representing its restriction to the fibre at `t`. -/
theorem fibreRank_eq_finrank_of_schemePullbackClass_eq (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B _ hk).obj T) {y : picardAt B hX hk f T}
    {M : ((baseChangeProj B hX hk f T).fiber t).Modules}
    (hM : Stacks.SheafOfModules.IsInvertible ((baseChangeProj B hX hk f T).fiber t).presheaf
      (Stacks.RingedSpace.structureIsSheaf ((baseChangeProj B hX hk f T).fiber t).toRingedSpace) M)
    (h : Stacks.Picard.schemePullbackClass ((baseChangeProj B hX hk f T).fiberι t) y =
      Stacks.SheafOfModules.picardClass _ _ M hM) (n : ℕ) :
    fibreRank B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ) T
      (toPicardFunctorHom B hX hk f T y) t n =
      Module.finrank ((B.inclusion.obj T.left).residueField t)
        (cohomologyOverField ((B.inclusion.obj T.left).residueField t)
          ((baseChangeProj B hX hk f T).fiberToSpecResidueField t) M n) := by
  rw [fibreRank_eq, classFibreRank_eq_fibre]
  have h' : Stacks.Picard.schemePullbackClass
      (Stacks.FibreCohomology.fibreAtMap (baseChangeProj B hX hk f T) t) y =
      Stacks.SheafOfModules.picardClass _ _ M hM := h
  rw [h']
  exact LinearEquiv.finrank_eq (Stacks.FibreCohomology.cohomologyOverFieldMapIso _ _
    (nonempty_rep_picardClass_iso _ _).some n).toLinearEquiv

omit [GeometricallyIrreducible (B.inclusion.map f)] in
include σ hσ in
/-- **[Stacks, Tag 0B9Y] gives the translation property of the proof of [Stacks, Tag 0B9Z]**:
near every point of its base, every point of `Pic_{X/k}` is translated into the normalized
subfunctor by a `k`-rational point. -/
theorem exists_translate_mem_curveNormalizedLocus (htw : TwistToNormalized B hX hk f)
    (T : BigFppfOver B (Spec (.of k)) hk) (ξ : (picardFunctor B hX hk f).obj (op T))
    (t : (BigFppfOver.toScheme B _ hk).obj T) :
    ∃ g, t ∈ curveNormalizedLocus B hX hk f σ hσ T ((translate B hX hk f g).hom.app (op T) ξ) := by
  have := isSeparated_of_isCurve B hX hk f
  have := isNoetherian_of_isCurve B hX hk f
  obtain ⟨x, rfl⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ
    (isIso_c_of_isCurve B hX hk f σ hσ) T ξ
  set fT := baseChangeProj B hX hk f T
  let := residueAlgebra (B.inclusion.map T.hom) t
  have hZ := isPullback_fiber (B.inclusion.map f) (B.inclusion.map T.hom)
    (pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom)) fT
    (IsPullback.of_hasPullback _ _) t
  set p := fT.fiberι t ≫ pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom)
  set L := rep (Stacks.Picard.schemePullbackClass (fT.fiberι t) x)
  obtain ⟨L₀, hL₀, h0, h1⟩ := htw ((B.inclusion.obj T.left).residueField t)
    (fT.fiberToSpecResidueField t) p hZ L inferInstance
  set q := pullback.fst (B.inclusion.map f) (B.inclusion.map (baseObj B hk).hom)
  have hL₀q : Stacks.Ample.IsInvertibleModule _ ((Scheme.Modules.pullback q).obj L₀) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback q L₀
  set x₀ : picardAt B hX hk f (baseObj B hk) :=
    Stacks.SheafOfModules.picardClass _ _ ((Scheme.Modules.pullback q).obj L₀) hL₀q
  refine ⟨toPicardFunctorHom B hX hk f (baseObj B hk) x₀, ?_⟩
  have hpL₀ : Stacks.SheafOfModules.IsInvertible (fT.fiber t).presheaf
      (Stacks.RingedSpace.structureIsSheaf (fT.fiber t).toRingedSpace)
      ((Scheme.Modules.pullback p).obj L₀) :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mpr
      (Stacks.InvertiblePullback.isInvertibleModule_pullback p L₀)
  have hLinv : Stacks.SheafOfModules.IsInvertible (fT.fiber t).presheaf
      (Stacks.RingedSpace.structureIsSheaf (fT.fiber t).toRingedSpace) L :=
    (Stacks.Picard.picardRepresentative _ _).property
  have hTw : Stacks.SheafOfModules.IsInvertible (fT.fiber t).presheaf
      (Stacks.RingedSpace.structureIsSheaf (fT.fiber t).toRingedSpace) (baseChangeTwist p L L₀) :=
    @Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ (fT.fiber t).presheaf
      (Stacks.RingedSpace.structureIsSheaf (fT.fiber t).toRingedSpace) _ _ _ _ hLinv hpL₀
  have hcls : Stacks.Picard.schemePullbackClass (fT.fiberι t)
      (picardMap B hX hk f (toBaseObj B hk T) x₀ + x) =
      Stacks.SheafOfModules.picardClass _ _ (baseChangeTwist p L L₀) hTw := by
    rw [Stacks.Picard.schemePullbackClass_add, add_comm]
    have hB : Stacks.Picard.schemePullbackClass (fT.fiberι t) x =
        Stacks.SheafOfModules.picardClass _ _ L hLinv :=
      (Stacks.Picard.classOf_picardRepresentative _ _).symm
    rw [schemePullbackClass_fiberι_picardMap B hX hk f T t L₀ hL₀q hpL₀, hB]
    exact Stacks.SheafOfModules.picardClass_tensorSheaf _ _ L _ hLinv hpL₀ hTw
  have hfib := fibreRank_eq_finrank_of_schemePullbackClass_eq B hX hk f σ hσ T t hTw hcls
  change fibreRank B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ) T _ t 1 = 0 ∧
    fibreRank B hX hk f σ hσ (isIso_c_of_isCurve B hX hk f σ hσ) T _ t 0 = 1
  rw [translate_toPicardFunctorHom, hfib, hfib]
  exact ⟨h1, h0⟩

include σ hσ in
/-- **The Picard functor of a pointed curve is representable once [Stacks, Tag 0B9Y] holds for
it.** -/
theorem isRepresentable_picardFunctor_of_twistToNormalized (htw : TwistToNormalized B hX hk f) :
    (picardFunctor B hX hk f).IsRepresentable :=
  isRepresentable_picardFunctor_of_translates B hX hk f σ hσ
    (exists_translate_mem_curveNormalizedLocus B hX hk f σ hσ htw)

end Stacks.PicardFunctor
