module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleTypesUnderIso
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.TerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.SeparableDegreeFibres
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesSemistableOpen
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.GlobalFunctionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.NodalOverField
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.RationalTailIso

/-!
# `Curves^{semistable}` over a field (Stacks 0E70, part (2))

Let `X` be a proper scheme of dimension at most one over a field `k`, and `x₀ : Spec k → Curves`
its classifying morphism, the point of `Curves` given by the family of curves
`AlgebraicGeometry.curveFamilyOfScheme X`. Part (2) of Stacks 0E70 says that `x₀` factors through
`Curves^{semistable}` exactly when

* (b) `X` is at-worst-nodal, `dim X = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is at least one,
  and `X` has no rational tail; equivalently
* (c) `X` is at-worst-nodal, `dim X = 1`, `k = H⁰(X, 𝒪_X)`, and `ω_X^{⊗ m}` is globally generated
  for every `m ≥ 2`.

By part (1) (`AlgebraicGeometry.C1590Private.factors_curvesSemistable_iff`) this is the
semistability (Stacks 0E6Z) of the family of curves of `X`, which this file reads on `X`:

* the family is at-worst-nodal of relative dimension one exactly when `X ⟶ Spec k` is, that is,
  when `X` is equidimensional of dimension one with at-worst-nodal singularities (Stacks 0C59 over
  a field, `AlgebraicGeometry.C1590Private.isAtWorstNodalOfRelativeDimensionOne_iff_of_field`);
  equidimensionality is automatic once `k = H⁰(X, 𝒪_X)` and `dim X = 1`;
* `f_*𝒪_X = 𝒪_S` universally exactly when `k = H⁰(X, 𝒪_X)`, by
  `AlgebraicGeometry.C1590Private.hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff`;
* the fibre at a field-valued point `Spec K → Spec k` is the base change `X_K`, of the genus of
  `X` (Stacks 0BY9), and without rational tail when `X` has none, by the compatibility of Stacks
  0E3L with ground field extensions (`AlgebraicGeometry.forall_not_isRationalTail_baseChange`);
  at the point `Spec k → Spec k` itself the fibre is `X`, and rational tails are invariant under
  isomorphism (`AlgebraicGeometry.C1590Private.forall_not_isRationalTail_iff_of_isIso`).

Conditions (2)(b) and (2)(c) are equivalent by Algebraic Curves, Lemma 0E3L, through Stacks 0E3K:
without rational tails `ω_X ≅ 𝒪_X` in genus one and `ω_X^{⊗ m}` is globally generated in genus at
least two; conversely a globally generated power of `ω_X` has nonnegative degree on every rational
tail and on `X` itself when `X` is irreducible, whereas `ω_X` has negative degree on a rational
tail (Stacks 0E63) and degree `2g - 2 = -2` on an irreducible curve of genus zero (Stacks 0C19).

## Main results

* `AlgebraicGeometry.C1590Private.isSemistableCurveFamily_curveFamilyOfScheme_iff`: the family of
  curves of `X` is semistable exactly when condition (2)(b) holds.
* `AlgebraicGeometry.C1590Private.factors_curvesSemistable_over_field_iff`: **Stacks 0E70, part
  (2), (a) ⟺ (b).**
* `AlgebraicGeometry.C1590Private.hasPositiveGenusNoRationalTail_iff_isGeneratedByGlobalSections`:
  the equivalence of (2)(b) and (2)(c), Algebraic Curves, Lemma 0E3L.
* `C1590Private.isSemistableCurveFamily_curveFamilyOfScheme_iff_globallyGenerated` and
  `AlgebraicGeometry.C1590Private.factors_curvesSemistable_over_field_iff_globallyGenerated`:
  **Stacks 0E70, part (2), (a) ⟺ (c).**

## References

* [Stacks Project, Tag 0E70](https://stacks.math.columbia.edu/tag/0E70)
* [Stacks Project, Tag 0E6Z](https://stacks.math.columbia.edu/tag/0E6Z)
* [Stacks Project, Tag 0E3L](https://stacks.math.columbia.edu/tag/0E3L)
* [Stacks Project, Tag 0E3K](https://stacks.math.columbia.edu/tag/0E3K)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
  {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
  (hk : B.Contains (Spec (.of k))) (hdim : topologicalKrullDim X.left ≤ 1)

/-! ### Nodality -/

/-- The family of curves of a proper scheme `X` over a field is at-worst-nodal of relative
dimension one exactly when `X ⟶ Spec k` is: the property is local in the étale topology on source
and target, so it may be read on the identity chart. -/
theorem isAtWorstNodal_curveFamilyOfScheme_iff :
    Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ
        (curveFamilyOfScheme X B hZ hk hdim).toBase.hom ↔
      IsAtWorstNodalOfRelativeDimensionOne X.hom :=
  Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk
      X.hom)

/-! ### The fibres -/

/-- A scheme presenting the fibre of the family of curves of `X` at a field-valued point `p` is
the base change of `X` along the morphism `Spec K ⟶ Spec k` of `p`, as a cartesian square of
schemes. -/
theorem isPullback_of_isPullback_curveFamilyOfScheme
    (p : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj)
    {V : BigFppfOver B integerBase hZ} (v : V ⟶ p.siteObject)
    (q : yoneda.obj V ⟶ (curveFamilyOfScheme X B hZ hk hdim).total.obj)
    (hV : IsPullback q (yoneda.map v) (curveFamilyOfScheme X B hZ hk hdim).toBase.hom
      (yonedaEquiv.symm p.value)) :
    IsPullback ((BigFppfOver.toScheme B integerBase hZ).map (Yoneda.fullyFaithful.preimage q))
      ((BigFppfOver.toScheme B integerBase hZ).map v) X.hom
      ((BigFppfOver.toScheme B integerBase hZ).map p.value) := by
  have hsq : IsPullback (Yoneda.fullyFaithful.preimage q) v
      (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk
        X.hom) p.value :=
    IsPullback.of_map_of_faithful yoneda (by rwa [Yoneda.fullyFaithful.map_preimage q])
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B integerBase hZ) := by
    dsimp [BigFppfOver.toScheme]
    infer_instance
  exact hsq.map (BigFppfOver.toScheme B integerBase hZ)

/-- The field-valued point `Spec k ⟶ Spec k` of the base of the family of curves of `X`, given by
the identity. -/
def selfPoint : Space.FieldValuedPoint B integerBase hZ
    (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj where
  carrier := k
  contained := hk
  toBase := specULiftZIsTerminal.from _
  value := 𝟙 _

/-- **The fibres of the family of curves of `X`.** Let `X` be at-worst-nodal of dimension one
with `k = H⁰(X, 𝒪_X)`. Every fibre of its family of curves, presented by a scheme at a
field-valued point, has genus at least one and no rational tail exactly when `X` does. -/
theorem forall_hasPositiveGenusNoRationalTail_iff (hdim1 : topologicalKrullDim X.left = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)]
    (hnodal : letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X.left) :
    (∀ p : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ (curveFamilyOfScheme X B hZ hk hdim).total.obj),
        IsPullback q (yoneda.map v) (curveFamilyOfScheme X B hZ hk hdim).toBase.hom
            (yonedaEquiv.symm p.value) ∧
          HasPositiveGenusNoRationalTail p.carrier
            ((BigFppfOver.toScheme B integerBase hZ).map v)) ↔
      1 ≤ genus X.hom ∧ ∀ C : X.left.IdealSheafData, ¬ @IsRationalTail k _ X.left ⟨X.hom⟩ C := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
  constructor
  · intro h
    obtain ⟨V, v, q, hV, hg, htail⟩ := h (selfPoint X hk hdim)
    have hS := isPullback_of_isPullback_curveFamilyOfScheme X hk hdim _ v q hV
    let a : (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ X.left :=
      (BigFppfOver.toScheme B integerBase hZ).map (Yoneda.fullyFaithful.preimage q)
    have : IsIso a :=
      hS.isIso_fst_of_isIso (inferInstanceAs (IsIso (𝟙 (Spec (.of k)))))
    have hw : a ≫ X.hom = (BigFppfOver.toScheme B integerBase hZ).map v :=
      hS.w.trans (Category.comp_id _)
    let : ((BigFppfOver.toScheme B integerBase hZ).obj V).Over (Spec (.of k)) :=
      ⟨(BigFppfOver.toScheme B integerBase hZ).map v⟩
    refine ⟨?_, (forall_not_isRationalTail_iff_of_isIso (k := k) (X := X.left)
      (Y := (BigFppfOver.toScheme B integerBase hZ).obj V) a hw).2 htail⟩
    have hgen := genus_comp_iso_eq k X.hom (asIso a)
    rw [asIso_hom, hw] at hgen
    rwa [← hgen]
  · rintro ⟨hg, htail⟩ p
    let g := integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk)
      hk X.hom
    let v := pullback.snd g p.value
    let q : yoneda.obj (pullback g p.value) ⟶ (curveFamilyOfScheme X B hZ hk hdim).total.obj :=
      yoneda.map (pullback.fst g p.value)
    have hV : IsPullback q (yoneda.map v) (curveFamilyOfScheme X B hZ hk hdim).toBase.hom
        (yonedaEquiv.symm p.value) :=
      (IsPullback.of_hasPullback g p.value).map yoneda
    refine ⟨_, v, q, hV, ?_⟩
    have hS := isPullback_of_isPullback_curveFamilyOfScheme X hk hdim p v q hV
    let pv : Spec (.of p.carrier) ⟶ Spec (.of k) :=
      (BigFppfOver.toScheme B integerBase hZ).map p.value
    obtain ⟨φ, hφ⟩ : ∃ φ : k →+* p.carrier, Spec.map (CommRingCat.ofHom φ) = pv :=
      ⟨(Spec.preimage pv).hom, by simp⟩
    let a : (BigFppfOver.toScheme B integerBase hZ).obj (pullback g p.value) ⟶ X.left :=
      (BigFppfOver.toScheme B integerBase hZ).map (Yoneda.fullyFaithful.preimage q)
    let w : (BigFppfOver.toScheme B integerBase hZ).obj (pullback g p.value) ⟶
        Spec (.of p.carrier) :=
      (BigFppfOver.toScheme B integerBase hZ).map v
    have hS0 : IsPullback a w X.hom (Spec.map (CommRingCat.ofHom φ)) := by rwa [hφ]
    let : Algebra k p.carrier := φ.toAlgebra
    have hS' : IsPullback a w X.hom (Spec.map (CommRingCat.ofHom (algebraMap k p.carrier))) := hS0
    refine ⟨?_, ?_⟩
    · change 1 ≤ genus w
      rwa [genus_eq_of_isPullback k p.carrier φ a w X.hom hS0]
    · have hK := forall_not_isRationalTail_baseChange k p.carrier X.hom hdim1 hnodal htail hg
      let : ((BigFppfOver.toScheme B integerBase hZ).obj (pullback g p.value)).Over
          (Spec (.of p.carrier)) := ⟨w⟩
      let : (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)))).Over
          (Spec (.of p.carrier)) := ⟨pullback.snd _ _⟩
      have : IsProper (pullback X.hom (Spec.map (CommRingCat.ofHom (algebraMap k p.carrier))) ↘
          Spec (.of p.carrier)) :=
        MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) (inferInstanceAs
          (IsProper X.hom))
      exact (forall_not_isRationalTail_iff_of_isIso (k := p.carrier) hS'.isoPullback.hom
        hS'.isoPullback_hom_snd).1 hK

/-! ### Part (2): (a) ⟺ (b) -/

/-- **Semistability of the family of curves of a proper scheme over a field.** For a proper
scheme `X` of dimension at most one over a field `k`, its family of curves is semistable
(Stacks 0E6Z) exactly when `X` has at-worst-nodal singularities, `dim X = 1`, `k = H⁰(X, 𝒪_X)`,
the genus of `X` is at least one, and `X` has no rational tail. -/
theorem isSemistableCurveFamily_curveFamilyOfScheme_iff :
    IsSemistableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ 1 ≤ genus X.hom ∧
          ∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  rw [isSemistableCurveFamily_iff]
  constructor
  · rintro ⟨⟨hnod, hU⟩, hfib⟩
    have hΓ := (hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff X B hZ hk hdim).1 hU
    have : Nonempty X.left :=
      (connectedSpace_of_isIso_globalSections k X.hom).toNonempty
    obtain ⟨-, hdim1, hnodal⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_of_field k X.hom).1
      ((isAtWorstNodal_curveFamilyOfScheme_iff X hk hdim).1 hnod)
    obtain ⟨hg, htail⟩ := (forall_hasPositiveGenusNoRationalTail_iff X hk hdim hdim1 hnodal).1 hfib
    exact ⟨hnodal, hdim1, hΓ, hg, htail⟩
  · rintro ⟨hnodal, hdim1, hΓ, hg, htail⟩
    have : Nonempty X.left :=
      (connectedSpace_of_isIso_globalSections k X.hom).toNonempty
    exact ⟨⟨(isAtWorstNodal_curveFamilyOfScheme_iff X hk hdim).2
      ((isAtWorstNodalOfRelativeDimensionOne_iff_of_field k X.hom).2
        ⟨equidimensional_of_isIso_globalSections_of_dimension_one k X.hom hdim1, hdim1, hnodal⟩),
      (hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff X B hZ hk hdim).2 hΓ⟩,
      (forall_hasPositiveGenusNoRationalTail_iff X hk hdim hdim1 hnodal).2 ⟨hg, htail⟩⟩

/-- A scheme-valued point `y` of `Curves` whose family is identified with the family of curves of
`X` factors through `Curves^{semistable}` exactly when the family of curves of `X` is semistable. -/
private theorem factors_curvesSemistable_iff_isSemistableCurveFamily_curveFamilyOfScheme
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamily B hZ) = y) ↔
      IsSemistableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) :=
  (factors_curvesSemistable_iff B hZ U y hy).trans
    (Iff.intro (CurveFamily.isSemistableCurveFamily_of_hom B hZ e.inv)
      (CurveFamily.isSemistableCurveFamily_of_hom B hZ e.hom))

/-- **Stacks 0E70, part (2), (a) ⟺ (b).** Let `X` be a proper scheme of dimension at most one
over a field `k`. The classifying morphism `Spec k → Curves` of `X` factors through
`Curves^{semistable}` exactly when `X` has at-worst-nodal singularities, `dim X = 1`,
`k = H⁰(X, 𝒪_X)`, the genus of `X` is at least one, and `X` has no rational tail. Here the
classifying morphism is any scheme-valued point `y` of `Curves` whose family is identified with
the family of curves of `X`, as in part (2) of Stacks 0E0E. -/
theorem factors_curvesSemistable_over_field_iff (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamily B hZ) = y) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ 1 ≤ genus X.hom ∧
          ∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C :=
  (factors_curvesSemistable_iff_isSemistableCurveFamily_curveFamilyOfScheme X hk hdim U y hy
    e).trans (isSemistableCurveFamily_curveFamilyOfScheme_iff X hk hdim)

/-! ### Part (2): (b) ⟺ (c) -/

section GloballyGenerated

open Stacks.SheafOfModules.Invertible (tensorPower)

/-- **Algebraic Curves, Lemma 0E3L, the equivalence of (2)(b) and (2)(c) of Stacks 0E70.** Let
`Y` be a proper scheme of dimension one over `k` with `k = H⁰(Y, 𝒪_Y)` and at-worst-nodal
singularities. Then `Y` has genus at least one and no rational tail exactly when `ω_Y^{⊗ m}` is
globally generated for every `m ≥ 2`.

Without rational tails, `ω_Y ≅ 𝒪_Y` in genus one and `ω_Y^{⊗ m}` is globally generated in genus at
least two (Stacks 0E3K). Conversely, `ω_Y^{⊗ 2}` globally generated gives `ω_Y` nonnegative degree
on every proper integral curve mapping to `Y`; it has negative degree on a rational tail
(Stacks 0E63), so there is none, and in genus zero `Y` would be an irreducible conic
(Stacks 0E3L, part (1)) on which `ω_Y` has degree `2g - 2 = -2` (Stacks 0C19). -/
theorem hasPositiveGenusNoRationalTail_iff_isGeneratedByGlobalSections {Y : Scheme.{u}}
    [Y.Over (Spec (.of k))] [IsProper (Y ↘ Spec (.of k))] (hdim : topologicalKrullDim Y = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y ↘ Spec (.of k)).appTop)]
    (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k Y) :
    (1 ≤ genus (Y ↘ Spec (.of k)) ∧ ∀ C : Y.IdealSheafData, ¬ IsRationalTail k Y C) ↔
      haveI := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
      letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
      ∀ m : ℕ, 2 ≤ m → SheafOfModules.IsGeneratedByGlobalSections
        (tensorPower Y.presheaf Y.ringCatSheaf.2
          (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) m) := by
  have := connectedSpace_of_isIso_globalSections k (Y ↘ Spec (.of k))
  let hω := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k Y hdim hnodal
  constructor
  · rintro ⟨hg, htail⟩ m hm
    by_cases h1 : genus (Y ↘ Spec (.of k)) = 1
    · obtain ⟨φ⟩ := nonempty_dualizingSheafOverField_iso_unit_of_forall_not_isRationalTail hdim
        hnodal htail h1
      have := AlgebraicGeometry.SheafOfModules.isInvertible_unit Y.presheaf Y.ringCatSheaf.2
      let e := Stacks.SheafOfModules.Invertible.tensorPowerCongr Y.presheaf Y.ringCatSheaf.2 _ _
        φ m ≪≫ Stacks.SheafOfModules.Invertible.tensorPowerUnitIso Y.presheaf Y.ringCatSheaf.2 m
      exact Stacks.SheafOfModules.Intrinsic.isGeneratedByGlobalSections_of_iso e.symm
        ⟨Stacks.AlgebraicGeometry.CoherenceCriteria.unitGeneratingSections⟩
    · exact
        isGeneratedByGlobalSections_tensorPower_dualizingSheafOverField_of_forall_not_isRationalTail
        hdim hnodal htail (by omega) m hm
  · intro h
    have h2 := h 2 le_rfl
    have htail : ∀ C : Y.IdealSheafData, ¬ IsRationalTail k Y C := by
      intro C hC
      have hneg := invertibleCurveDegree_pullback_dualizingSheafOverField_neg_of_isRationalTail
        hdim hnodal C hC
      have : IsIntegral C.subscheme := hC.isIntegral
      have hnn := invertibleCurveDegree_pullback_nonneg_of_isGeneratedByGlobalSections k
        (C.subschemeι ≫ (Y ↘ Spec (.of k)))
        (Stacks.Curves.topologicalKrullDim_subscheme_eq_one_of_isRationalTail k Y hdim C hC).le
        C.subschemeι _ 2 (by norm_num) h2
      exact not_lt.mpr hnn hneg
    refine ⟨?_, htail⟩
    by_contra hg
    have hg0 : genus (Y ↘ Spec (.of k)) = 0 := by omega
    obtain ⟨Q, -, hirr, e, -⟩ :=
      (exists_planeCurveData_deg_two_of_forall_not_isRationalTail hdim hnodal htail hg0).1
    have := hirr
    have : IrreducibleSpace Y :=
      (Scheme.homeoOfIso e.symm).surjective.irreducibleSpace (Scheme.homeoOfIso e.symm).continuous
    have : IsReduced Y := Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities k Y hnodal
    have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
    have hnn := invertibleCurveDegree_pullback_nonneg_of_isGeneratedByGlobalSections k
      (Y ↘ Spec (.of k)) hdim.le (𝟙 Y) _ 2 (by norm_num) h2
    let : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        ((Scheme.Modules.pullback (𝟙 Y)).obj
          (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k)))) :=
      Stacks.Modules.isInvertible_pullback _ _
    let : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
        ((𝟭 Y.Modules).obj (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k)))) := hω
    rw [invertibleCurveDegree_eq_of_iso (k := k) (Y ↘ Spec (.of k)) hdim.le
      ((Scheme.Modules.pullbackId Y).app _)] at hnn
    change 0 ≤ invertibleCurveDegree k (Y ↘ Spec (.of k)) hdim.le
      (Stacks.Duality.dualizingSheafOverField (Y ↘ Spec (.of k))) at hnn
    rw [invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k (Y ↘ Spec (.of k)) hdim.le,
      hg0] at hnn
    norm_num at hnn

/-- **Semistability of the family of curves of a proper scheme over a field, by global
generation.** For a proper scheme `X` of dimension at most one over a field `k`, its family of
curves is semistable exactly when `X` has at-worst-nodal singularities, `dim X = 1`,
`k = H⁰(X, 𝒪_X)`, and `ω_X^{⊗ m}` is globally generated for every `m ≥ 2`. -/
theorem isSemistableCurveFamily_curveFamilyOfScheme_iff_globallyGenerated :
    IsSemistableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
      ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X.left)
        (hdim1 : topologicalKrullDim X.left = 1)
        (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)),
        haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hΓ
        haveI := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
        letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left
          hdim1 hnodal
        ∀ m : ℕ, 2 ≤ m → SheafOfModules.IsGeneratedByGlobalSections
          (tensorPower X.left.presheaf X.left.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField (X.left ↘ Spec (.of k))) m) := by
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  have : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
  rw [isSemistableCurveFamily_curveFamilyOfScheme_iff]
  constructor
  · rintro ⟨hnodal, hdim1, hΓ, hg, htail⟩
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hΓ
    exact ⟨hnodal, hdim1, hΓ,
      (hasPositiveGenusNoRationalTail_iff_isGeneratedByGlobalSections hdim1 hnodal).1 ⟨hg, htail⟩⟩
  · rintro ⟨hnodal, hdim1, hΓ, hgg⟩
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hΓ
    exact ⟨hnodal, hdim1, hΓ,
      (hasPositiveGenusNoRationalTail_iff_isGeneratedByGlobalSections hdim1 hnodal).2 hgg⟩

/-- **Stacks 0E70, part (2), (a) ⟺ (c).** Let `X` be a proper scheme of dimension at most one
over a field `k`. The classifying morphism `Spec k → Curves` of `X` factors through
`Curves^{semistable}` exactly when `X` has at-worst-nodal singularities, `dim X = 1`,
`k = H⁰(X, 𝒪_X)`, and `ω_X^{⊗ m}` is globally generated for every `m ≥ 2`. The classifying
morphism is any scheme-valued point `y` of `Curves` whose family is identified with the family of
curves of `X`, as in `AlgebraicGeometry.C1590Private.factors_curvesSemistable_over_field_iff`. -/
theorem factors_curvesSemistable_over_field_iff_globallyGenerated
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom)
    (e : y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) :
    (∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
        ObjectProperty.FullSubcategory (IsSemistableCurveFamily B hZ),
        z ⋙ ObjectProperty.ι (IsSemistableCurveFamily B hZ) = y) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
      ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X.left)
        (hdim1 : topologicalKrullDim X.left = 1)
        (hΓ : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)),
        haveI : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hΓ
        haveI := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
        letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left
          hdim1 hnodal
        ∀ m : ℕ, 2 ≤ m → SheafOfModules.IsGeneratedByGlobalSections
          (tensorPower X.left.presheaf X.left.ringCatSheaf.2
            (Stacks.Duality.dualizingSheafOverField (X.left ↘ Spec (.of k))) m) :=
  (factors_curvesSemistable_iff_isSemistableCurveFamily_curveFamilyOfScheme X hk hdim U y hy
    e).trans
    (isSemistableCurveFamily_curveFamilyOfScheme_iff_globallyGenerated X hk hdim)

end GloballyGenerated

end AlgebraicGeometry.C1590Private

end
