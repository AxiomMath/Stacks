module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFinal
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegree
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.GroupScheme
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.AbelianVariety.AbelMapCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SectionDivisor
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardBasePoints
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.FibreDegreeAdditive
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree components of the Picard scheme of a curve

Clause (1) of [Stacks, Tag 0BA0]: for a smooth projective curve `X` of genus `g` over a separably
closed field `k`, the Picard scheme is the disjoint union of its degree components `Pic^d_{X/k}`,
each a smooth proper variety of dimension `g`.

## Main results

* `Stacks.PicardFunctor.degreePointsEquiv'`: clause (2) at a rational point.
* `Stacks.PicardFunctor.picardDegreeComponent_smooth_proper_variety`: clause (1) for the degree
  components.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.PicardFunctor Stacks.PicardCurve

universe u


namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))

section Translate

variable [(picardFunctor B hX hk f).IsRepresentable]

/-- The base point of `Spec k`. -/
abbrev basePoint : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseObj B hk) :=
  Classical.arbitrary (Spec (.of k))

/-- **The degree of a `k`-point of the Picard functor.** -/
abbrev rationalPointDegree (g : (picardFunctor B hX hk f).obj (op (baseObj B hk))) : ℤ :=
  curveFibreDegree B hX hk f σ hσ (baseObj B hk) g (basePoint B hk)

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable] in
/-- The fibre degree of a `k`-point of the Picard functor at any point of `Spec k` is its degree
`rationalPointDegree`. -/
theorem curveFibreDegree_baseObj (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseObj B hk)) :
    curveFibreDegree B hX hk f σ hσ (baseObj B hk) g t = rationalPointDegree B hX hk f σ hσ g := by
  have : Subsingleton ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseObj B hk)) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  rw [Subsingleton.elim t (basePoint B hk)]

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable] in
/-- The fibre degree of the restriction of a `k`-point of the Picard functor to `T` is, at every
point of `T`, the degree of the `k`-point. -/
theorem curveFibreDegree_restrictBase (g : (picardFunctor B hX hk f).obj (op (baseObj B hk)))
    (T : BigFppfOver B (Spec (.of k)) hk) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    curveFibreDegree B hX hk f σ hσ T (restrictBase B hX hk f g T) t =
      rationalPointDegree B hX hk f σ hσ g := by
  rw [curveFibreDegree, restrictBase, fibreDegree_map]
  exact curveFibreDegree_baseObj B hX hk f σ hσ g _

end Translate

section BasePoints

variable [(picardFunctor B hX hk f).IsRepresentable]

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable] in
/-- `picardBaseAddEquiv` sends a class on `X` to the image under `toPicardFunctorHom` of its
pullback along the inverse of `baseChangeBaseOverIso`. -/
theorem picardBaseAddEquiv_apply' (x : Stacks.Picard.ofScheme X) :
    picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) x =
      toPicardFunctorHom B hX hk f (baseOver B hk)
        (Stacks.Picard.schemePullbackClass (baseChangeBaseOverIso B hX hk f).inv x) :=
  rfl

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)]
  [(picardFunctor B hX hk f).IsRepresentable] in
/-- The inverse of `baseChangeBaseOverIso` is the first projection of the pullback of `f` along the
structure morphism of `baseOver B hk`. -/
theorem baseChangeBaseOverIso_inv :
    (baseChangeBaseOverIso B hX hk f).inv =
      pullback.fst (B.inclusion.map f) (B.inclusion.map (baseOver B hk).hom) :=
  pullbackRightIdIso_inv _

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable] in
/-- **The fibre Euler characteristic of a `k`-point is the Euler characteristic on `X`.** -/
theorem fibreEuler_picardBaseAddEquiv (x : Stacks.Picard.ofScheme X)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseOver B hk)) :
    fibreEuler B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) (baseOver B hk)
        (picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) x)
        t =
      (Module.finrank k (cohomologyOverField k (B.inclusion.map f) (rep x) 0) : ℤ) -
        Module.finrank k (cohomologyOverField k (B.inclusion.map f) (rep x) 1) := by
  have : IsProper (B.inclusion.map f) := inferInstance
  let fT := baseChangeProj B hX hk f (baseOver B hk)
  let g := pullback.fst (B.inclusion.map f) (B.inclusion.map (baseOver B hk).hom)
  have hId : Spec.map (CommRingCat.ofHom (algebraMap k k)) =
      B.inclusion.map (baseOver B hk).hom := by
    rw [Algebra.algebraMap_self]
    exact Spec.map_id _
  have hsq :
      IsPullback g fT (B.inclusion.map f) (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [hId]
    exact IsPullback.of_hasPullback _ _
  have : (rep x).IsQuasicoherent := inferInstance
  obtain ⟨e⟩ := nonempty_rep_schemePullbackClass_iso g x
  have hrank : ∀ n, fibreRank B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
      (baseOver B hk)
      (picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) x)
      t n = Module.finrank k (cohomologyOverField k (B.inclusion.map f) (rep x) n) := by
    intro n
    have : IsProper fT := inferInstance
    rw [picardBaseAddEquiv_apply', baseChangeBaseOverIso_inv, fibreRank_toPicardFunctorHom]
    refine (Stacks.AbelMap.finrank_cohomologyOverField_eq_fibreCohomology fT
      (rep (Stacks.Picard.schemePullbackClass g x)) t n).symm.trans ?_
    rw [finrank_cohomologyOverField_eq_of_iso k fT e n]
    exact finrank_cohomologyOverField_baseChange_field k k g fT _ hsq (rep x) n
  rw [fibreEuler, hrank, hrank]

omit [GeometricallyIrreducible (B.inclusion.map f)] [(picardFunctor B hX hk f).IsRepresentable] in
include σ hσ in
/-- **The degree of a `k`-point of the Picard functor is the degree of its invertible module.** -/
theorem curveFibreDegree_picardBaseAddEquiv (x : Stacks.Picard.ofScheme X)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj (baseOver B hk)) :
    curveFibreDegree B hX hk f σ hσ (baseOver B hk)
        (picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) x)
        t =
      @invertibleCurveDegree k _ X (B.inclusion.map f) _
        (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le (rep x)
        (Stacks.Picard.picardRepresentative X.toRingedSpace x).property := by
  have : IsProper (B.inclusion.map f) := inferInstance
  refine Eq.trans ?_ (classDegree_eq k (B.inclusion.map f) x)
  rw [classDegree_eq_euler_sub, curveFibreDegree,
    fibreDegree, fibreEuler_picardBaseAddEquiv,
    show (0 : (picardFunctor B hX hk f).obj (op (baseOver B hk))) =
      picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) 0 from
      (map_zero _).symm, fibreEuler_picardBaseAddEquiv]

include σ hσ in
/-- **Stacks Project, Tag 0BA0, clause (2), at a rational point**: the `k`-points of `Pic^d_{X/k}`
correspond to the invertible `𝒪_X`-modules of degree `d`, up to isomorphism. -/
def degreePointsEquiv' (d : ℤ) :
    (baseOver B hk ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d) ≃
      {x : Stacks.Picard.ofScheme X //
        @invertibleCurveDegree k _ X (B.inclusion.map f) _
          (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le (rep x)
          (Stacks.Picard.picardRepresentative X.toRingedSpace x).property = d} := by
  have : IsProper (B.inclusion.map f) := inferInstance
  let E := picardPointsEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
  have hdeg : ∀ p : baseOver B hk ⟶ picardSchemeOver B hX hk f,
      (∃ q : baseOver B hk ⟶ picardSchemeDegreeComponent B hX hk f σ hσ d,
          q ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d = p) ↔
        @invertibleCurveDegree k _ X (B.inclusion.map f) _
          (IsCurve.topologicalKrullDim_eq_one (k := k) (f := B.inclusion.map f)).le (rep (E p))
          (Stacks.Picard.picardRepresentative X.toRingedSpace (E p)).property = d := by
    intro p
    rw [exists_comp_picardSchemeDegreeComponentι_iff]
    have hp : picardHomEquiv B hX hk f p =
        picardBaseAddEquiv B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ)
          (E p) := by
      simp [E, picardPointsEquiv]
    rw [hp]
    exact ⟨fun h =>
        (curveFibreDegree_picardBaseAddEquiv B hX hk f σ hσ (E p) (basePoint B hk)).symm.trans
          (h _),
      fun h t => (curveFibreDegree_picardBaseAddEquiv B hX hk f σ hσ (E p) t).trans h⟩
  exact Equiv.ofBijective
    (fun q => ⟨E (q ≫ picardSchemeDegreeComponentι B hX hk f σ hσ d), (hdeg _).1 ⟨q, rfl⟩⟩)
    ⟨fun q₁ q₂ h => (cancel_mono (picardSchemeDegreeComponentι B hX hk f σ hσ d)).1
        (E.injective (Subtype.ext_iff.1 h)),
      fun L => by
        obtain ⟨q, hq⟩ := (hdeg (E.symm L.1)).2 (by rw [Equiv.apply_symm_apply]; exact L.2)
        exact ⟨q, Subtype.ext ((congrArg E hq).trans (E.apply_symm_apply L.1))⟩⟩

end BasePoints

include hk in
/-- **The degree-`d` Hilbert scheme of the curve, as an object of the site**
([Stacks, Tag 0B9I]). -/
theorem exists_hilbertScheme_of_degree (d : ℕ) : ∃ (H : BigFppfOver B (Spec (.of k)) hk),
    Nonempty (Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map H.hom)) d) := by
  have : IsProper (B.inclusion.map f) := inferInstance
  have hg := Stacks.Hilbert.Curve.hilbertScheme_geometry (B.inclusion.map f) d
  obtain ⟨⟨H₀, hH₀⟩⟩ := hg.1
  have : IsProper H₀.hom := (hg.2 H₀ hH₀).2.1
  exact ⟨Over.mk (ObjectProperty.homMk (X := B.obj (contains_of_isProper B hk H₀.hom))
    (Y := B.obj hk) H₀.hom), ⟨hH₀⟩⟩

/-- The image under the inclusion of an isomorphism of objects over `Spec k` is an isomorphism. -/
private theorem isIso_inclusion_map_left_of_iso {A A' : BigFppfOver B (Spec (.of k)) hk}
    (e : A ≅ A') : IsIso (B.inclusion.map e.hom.left) :=
  inferInstanceAs (IsIso (B.inclusion.mapIso ((Over.forget _).mapIso e)).hom)

/-- A morphism over `Spec k` is compatible with the structure morphisms after applying the
inclusion. -/
private theorem inclusion_map_left_comp_hom {A A' : BigFppfOver B (Spec (.of k)) hk} (e : A ⟶ A') :
    B.inclusion.map e.left ≫ B.inclusion.map A'.hom = B.inclusion.map A.hom := by
  rw [← Functor.map_comp, Over.w]

section Points

variable [IsSepClosed k] [(picardFunctor B hX hk f).IsRepresentable]

/-- **There are `k`-points of the Picard functor of every degree** over a separably closed field:
for `d ≥ 0` the image under `γ_d` of a `k`-point of the smooth variety `Hilb^d_{X/k}`
([Stacks, Tag 056U]), and for `d < 0` the negative of one of degree `-d`. -/
theorem exists_rationalPointDegree_eq (e : ℤ) :
    ∃ g : (picardFunctor B hX hk f).obj (op (baseObj B hk)),
      rationalPointDegree B hX hk f σ hσ g = e := by
  have key : ∀ d : ℕ, ∃ g, rationalPointDegree B hX hk f σ hσ g = d := by
    intro d
    obtain ⟨H, ⟨hH⟩⟩ := exists_hilbertScheme_of_degree B hX hk f d
    have hgeo := (Stacks.Hilbert.Curve.hilbertScheme_geometry (B.inclusion.map f) d).2 _ hH
    have : Smooth (B.inclusion.map H.hom) := hgeo.1
    have : IsVariety k (B.inclusion.map H.hom) := hgeo.2.2.1
    have : Nonempty (B.inclusion.obj H.left) := inferInstance
    obtain ⟨s, hs⟩ := Stacks.AbelMap.exists_section_of_isSepClosed (B.inclusion.map H.hom)
    let a : baseObj B hk ⟶ H := Over.homMk (B.inclusion.preimage s) <|
      B.inclusion.map_injective <| by
        rw [Functor.map_comp, Functor.map_preimage, hs]
        exact (B.inclusion.map_id (B.obj hk)).symm
    let ζ := (Stacks.AbelMap.degreeComponentRepresentableBy B hX hk f σ hσ d).homEquiv
      (a ≫ Stacks.AbelMap.curveAbelMap B hX hk f σ hσ H hH)
    exact ⟨ζ.1, ζ.2 (basePoint B hk)⟩
  rcases Int.eq_nat_or_neg e with ⟨d, rfl | rfl⟩
  · exact key d
  · obtain ⟨g, hg⟩ := key d
    exact ⟨-g, curveFibreDegree_neg_of_eq B hX hk f σ hσ g d
      (fun t => (curveFibreDegree_baseObj B hX hk f σ hσ g t).trans hg) _⟩

/-- **Any two degree components of the Picard scheme are isomorphic** (by translation). -/
theorem nonempty_picardDegreeComponent_iso (d d' : ℤ) :
    Nonempty (picardSchemeDegreeComponent B hX hk f σ hσ d ≅
      picardSchemeDegreeComponent B hX hk f σ hσ d') := by
  obtain ⟨g, hg⟩ := exists_rationalPointDegree_eq B hX hk f σ hσ (d' - d)
  exact ⟨picardDegreeComponentTranslateIso B hX hk f σ hσ g (d' - d)
    (fun t => (curveFibreDegree_baseObj B hX hk f σ hσ g t).trans hg) d d' (by omega)⟩

end Points

section Components

variable [IsSepClosed k] [(picardFunctor B hX hk f).IsRepresentable]

/-- The structure morphism of `Pic^d_{X/k}`, as a morphism of schemes. -/
abbrev picardDegreeComponentHom (d : ℤ) :=
  B.inclusion.map (picardSchemeDegreeComponent B hX hk f σ hσ d).hom

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsSepClosed k] in
/-- The structure morphism of `Pic^d_{X/k}` is the inclusion of the degree locus followed by the
structure morphism of the Picard scheme. -/
theorem picardDegreeComponentHom_eq (d : ℤ) :
    picardDegreeComponentHom B hX hk f σ hσ d =
      (picardDegreeLocus B hX hk f σ hσ d).ι ≫
        B.inclusion.map (picardSchemeOver B hX hk f).hom := by
  change B.inclusion.map (degreeLocusHom B hX hk f σ hσ d ≫ (picardSchemeOver B hX hk f).hom) = _
  rw [Functor.map_comp, inclusion_map_degreeLocusHom]

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProjectiveVariety k (B.inclusion.map f)] [IsSepClosed k] in
/-- **The Picard scheme is separated over `k`**, being a group scheme over a field
([Stacks, Tag 047L]). -/
@[sga "6 XII 1.2" "special case"]
theorem isSeparated_picardScheme :
    IsSeparated (B.inclusion.map (picardSchemeOver B hX hk f).hom) :=
  isSeparated_hom_of_groupScheme_over_field (k := k) (picardGrp B hX hk f)

include σ hσ in
/-- A property stable under composition with isomorphisms holds for every degree component as
soon as it holds for one. -/
theorem picardDegreeComponentHom_of_iso (Q : MorphismProperty Scheme.{u}) [Q.RespectsIso]
    (d d' : ℤ) (h : Q (picardDegreeComponentHom B hX hk f σ hσ d)) :
    Q (picardDegreeComponentHom B hX hk f σ hσ d') := by
  obtain ⟨e⟩ := nonempty_picardDegreeComponent_iso B hX hk f σ hσ d' d
  have := isIso_inclusion_map_left_of_iso B hk e
  unfold picardDegreeComponentHom at h ⊢
  rw [← inclusion_map_left_comp_hom B hk e.hom]
  exact (Q.cancel_left_of_respectsIso _ _).2 h

include σ hσ in
/-- **Stacks Project, Tag 0BA0, clause (1), for the degree components**: over a separably closed
field, every degree component `Pic^d_{X/k}` of the Picard scheme of a smooth projective curve of
genus `g` is a smooth proper variety of dimension `g` (smooth of relative dimension `g`, proper,
integral, separated and of finite type over `k`). The conclusion of [Stacks, Tag 0B9Y] is `htw`. -/
@[sga "6 XII 1.2" "special case"]
theorem picardDegreeComponent_smooth_proper_variety (htw : TwistToNormalized B hX hk f) (d : ℤ) :
    SmoothOfRelativeDimension (genus (B.inclusion.map f))
        (picardDegreeComponentHom B hX hk f σ hσ d) ∧
      IsProper (picardDegreeComponentHom B hX hk f σ hσ d) ∧
      IsVariety k (picardDegreeComponentHom B hX hk f σ hσ d) ∧
      topologicalKrullDim (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ d).left) =
        (genus (B.inclusion.map f) : WithBot ℕ∞) := by
  have hSepP : IsSeparated (B.inclusion.map (picardSchemeOver B hX hk f).hom) :=
    isSeparated_picardScheme B hX hk f
  have hSmP : SmoothOfRelativeDimension (genus (B.inclusion.map f))
      (B.inclusion.map (picardSchemeOver B hX hk f).hom) :=
    Stacks.AbelMap.smoothOfRelativeDimension_picardScheme B hX hk f σ hσ htw
  have hsm : ∀ e : ℤ, SmoothOfRelativeDimension (genus (B.inclusion.map f))
      (picardDegreeComponentHom B hX hk f σ hσ e) := fun e => by
    have h : SmoothOfRelativeDimension (genus (B.inclusion.map f))
        ((picardDegreeLocus B hX hk f σ hσ e).ι ≫
          B.inclusion.map (picardSchemeOver B hX hk f).hom) := by
      simpa using smoothOfRelativeDimension_comp (n := 0) (m := genus (B.inclusion.map f))
        (picardDegreeLocus B hX hk f σ hσ e).ι (B.inclusion.map (picardSchemeOver B hX hk f).hom)
    rw [picardDegreeComponentHom_eq]
    exact h
  have hsep : ∀ e : ℤ, IsSeparated (picardDegreeComponentHom B hX hk f σ hσ e) := fun e => by
    have h : IsSeparated ((picardDegreeLocus B hX hk f σ hσ e).ι ≫
        B.inclusion.map (picardSchemeOver B hX hk f).hom) :=
      have : IsSeparated (picardDegreeLocus B hX hk f σ hσ e).ι :=
        AlgebraicGeometry.IsSeparated.isSeparated_of_mono _
      inferInstance
    rw [picardDegreeComponentHom_eq]
    exact h
  have hlft : ∀ e : ℤ, LocallyOfFiniteType (picardDegreeComponentHom B hX hk f σ hσ e) :=
    fun e => Stacks.AbelMap.locallyOfFiniteType_picardDegreeComponent B hX hk f σ hσ htw e
  -- the component of degree `g`, image of `Hilb^g_{X/k}`
  obtain ⟨H, ⟨hH⟩⟩ := exists_hilbertScheme_of_degree B hX hk f (genus (B.inclusion.map f))
  have hgeo := (Stacks.Hilbert.Curve.hilbertScheme_geometry (B.inclusion.map f) _).2 _ hH
  have : IsProper (B.inclusion.map H.hom) := hgeo.2.1
  have : IsVariety k (B.inclusion.map H.hom) := hgeo.2.2.1
  have : IsProper (B.inclusion.map f) := inferInstance
  have hsurj := Stacks.AbelMap.surjective_curveAbelMap B hX hk f σ hσ H hH le_rfl
  let γ := B.inclusion.map (Stacks.AbelMap.curveAbelMap B hX hk f σ hσ H hH).left
  have hγ : γ ≫ picardDegreeComponentHom B hX hk f σ hσ (genus (B.inclusion.map f) : ℕ) =
      B.inclusion.map H.hom :=
    inclusion_map_left_comp_hom B hk _
  have hprg :
      IsProper (picardDegreeComponentHom B hX hk f σ hσ (genus (B.inclusion.map f) : ℕ)) :=
    have := hsep (genus (B.inclusion.map f) : ℕ)
    have := hlft (genus (B.inclusion.map f) : ℕ)
    isProper_of_isProper_of_surjective γ _ _ hγ
  have hirr : IrreducibleSpace (B.inclusion.obj
      (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f) : ℕ)).left) :=
    Function.Surjective.irreducibleSpace γ.continuous hsurj.surj
  have hint : IsIntegral (B.inclusion.obj
      (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f) : ℕ)).left) := by
    have := hsm (genus (B.inclusion.map f) : ℕ)
    have := SmoothOfRelativeDimension.smooth (genus (B.inclusion.map f))
      (picardDegreeComponentHom B hX hk f σ hσ (genus (B.inclusion.map f) : ℕ))
    have : IsReduced (B.inclusion.obj (B.obj hk)) := inferInstanceAs (IsReduced (Spec (.of k)))
    have : IsReduced (B.inclusion.obj
      (picardSchemeDegreeComponent B hX hk f σ hσ (genus (B.inclusion.map f) : ℕ)).left) :=
      AlgebraicGeometry.isReduced_of_smooth
        (picardDegreeComponentHom B hX hk f σ hσ (genus (B.inclusion.map f) : ℕ))
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  -- transport to every degree
  have hpr : IsProper (picardDegreeComponentHom B hX hk f σ hσ d) :=
    picardDegreeComponentHom_of_iso B hX hk f σ hσ @IsProper _ d hprg
  have hintd :
      IsIntegral (B.inclusion.obj (picardSchemeDegreeComponent B hX hk f σ hσ d).left) := by
    obtain ⟨e⟩ := nonempty_picardDegreeComponent_iso B hX hk f σ hσ
      (genus (B.inclusion.map f) : ℕ) d
    have := isIso_inclusion_map_left_of_iso B hk e
    exact IsIntegral.of_isIso (B.inclusion.map e.hom.left)
  have := hsm d
  have := hintd
  have := hsep d
  have := hlft d
  refine ⟨hsm d, hpr, { }, ?_⟩
  exact Stacks.Hilbert.Curve.topologicalKrullDim_eq_of_smoothOfRelativeDimension
    (picardDegreeComponentHom B hX hk f σ hσ d) _

end Components

end Stacks.PicardFunctor

end
