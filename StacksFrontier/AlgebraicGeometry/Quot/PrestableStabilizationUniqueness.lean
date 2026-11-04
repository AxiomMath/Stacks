module

public import StacksFrontier.AlgebraicGeometry.Quot.PrestableStabilizationFibreIso
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionDescentAlongCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringOfOpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Quot.ExtendsFibreIsoNearPoint
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessNearPointFamilies

/-!
# Uniqueness of the stabilization of a prestable family

Let `X ⟶ S` be a prestable family of curves whose fibres have genus `g ≥ 2`, and let
`cᵢ : X ⟶ Yᵢ`, `i = 1, 2`, be morphisms to families of curves over `S` satisfying conditions (1)
and (2) of Stacks 0E8A. Then there is a unique isomorphism `e : Y₁ ≅ Y₂` with `c₁ ≫ e = c₂`.

The proof is the source's. At a point `s ∈ S` the fibres `Y₁,s` and `Y₂,s` are related by a unique
isomorphism under `X_s`, both being the stable contraction of `X_s` (Stacks 0E7Q). By Stacks 0E89
this isomorphism extends to an open neighbourhood of `s`; these local morphisms glue along the
open covering of `S` they live on, because morphisms out of `Y₁` are determined after `c₁`
(the scheme-theoretic image of `c₁` is `Y₁`), and the same argument shows the glued morphisms are
inverse to each other and unique.

Stacks 0E89 enters as `AlgebraicGeometry.CurveFamily.extendsFibreIsoNearPoint`, the statement
`AlgebraicGeometry.CurveFamily.ExtendsFibreIsoNearPoint` of that lemma for families of curves over
a scheme of the site, at the residue field of a point.

## Main statements

* `AlgebraicGeometry.CurveFamily.exists_hom_of_hasStableContractionFibres`: a morphism between two
  stabilizations under `X`, over the base.
* `AlgebraicGeometry.CurveFamily.existsUnique_iso_of_hasStableContractionFibres`: the uniqueness in
  Stacks 0E8A.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The fibre of a family of curves over a field-valued point of a base equal to its own is
presented by a scheme of the site. -/
theorem exists_isPullback_fieldValuedPoint_of_base_eq (Y : CurveFamily B hZ)
    {Q : BigFppfOver B integerBase hZ} (hb : Y.base = Q)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace Q).obj) :
    ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject) (q : schemeSpace V ⟶ Y.total),
      IsPullback q (schemeSpaceMap v) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb))
        (schemeSpaceMap p.value) := by
  subst hb
  simpa only [eqToHom_refl, Category.comp_id] using exists_isPullback_fieldValuedPoint B hZ Y p

/-- The structure morphism of a family of curves, transported to an equal base, is separated. -/
theorem isSeparated_toBase_comp_eqToHom (Y : CurveFamily B hZ) {Q : BigFppfOver B integerBase hZ}
    (hb : Y.base = Q) :
    Space.IsSeparated B integerBase hZ (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom := by
  subst hb
  simpa only [eqToHom_refl, Category.comp_id] using Y.proper.1

/-- Condition (1) of Stacks 0E8A makes the structure map of every base change of the
contraction along a scheme of the site an isomorphism. -/
theorem isIso_structureSharp_of_isUniversalStructureContraction {X Y : CurveFamily B hZ}
    {hb : Y.base = X.base} {c : X.total ⟶ Y.total}
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
    (h : X.IsUniversalStructureContraction B hZ Y hb c) (T : BigFppfOver B integerBase hZ)
    (t : T ⟶ X.base) :
    IsIso (Space.structureSharp B integerBase hZ
      (Space.structureContractionBaseChange B integerBase hZ c hc (schemeSpaceMap t))) :=
  (h T t _ _ _ _ _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase _)
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ _ _)
    (Space.structureContractionBaseChange_fst B integerBase hZ c hc _)
    (Space.structureContractionBaseChange_snd B integerBase hZ c hc _)).1

/-- The contraction itself has structure map an isomorphism. -/
theorem isIso_structureSharp_of_isUniversalStructureContraction_self {X Y : CurveFamily B hZ}
    {hb : Y.base = X.base} {c : X.total ⟶ Y.total}
    (hc : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
    (h : X.IsUniversalStructureContraction B hZ Y hb c) :
    IsIso (Space.structureSharp B integerBase hZ c) := by
  have hid : schemeSpaceMap (𝟙 X.base) = 𝟙 _ := ObjectProperty.hom_ext _ (yoneda.map_id _)
  refine (h X.base (𝟙 _) X.total Y.total (𝟙 _) X.toBase (𝟙 _)
    (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) c ?_ ?_ (by simp) hc).1
  · rw [hid]
    exact IsPullback.id_horiz X.toBase
  · rw [hid]
    exact IsPullback.id_horiz _

/-- Two morphisms between stabilizations, compatible with the contractions and the structure
morphisms, compose to the identity. -/
private theorem comp_eq_id_of_comp_eq {X Y₁ Y₂ : CurveFamily B hZ}
    (hb₁ : Y₁.base = X.base) (hb₂ : Y₂.base = X.base) {c₁ : X.total ⟶ Y₁.total}
    {c₂ : X.total ⟶ Y₂.total} [IsIso (Space.structureSharp B integerBase hZ c₁)]
    {Ψ : Y₁.total ⟶ Y₂.total} {Φ : Y₂.total ⟶ Y₁.total}
    (hΨb : Ψ ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) =
      Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁))
    (hΦb : Φ ≫ Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) =
      Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂))
    (hΨc : c₁ ≫ Ψ = c₂) (hΦc : c₂ ≫ Φ = c₁) : Ψ ≫ Φ = 𝟙 _ :=
  Space.eq_of_comp_eq_of_isIso_structureSharp B integerBase hZ c₁ _
    (isSeparated_toBase_comp_eqToHom Y₁ hb₁) (by rw [Category.assoc, hΦb, hΨb, Category.id_comp])
    (by rw [reassoc_of% hΨc, hΦc, Category.comp_id])

/-- **A morphism between two stabilizations**. If `cᵢ : X ⟶ Yᵢ` satisfy
conditions (1) (for `c₁`) and (2) (for both) of Stacks 0E8A, there is a morphism `Ψ : Y₁ ⟶ Y₂`
over the base with `c₁ ≫ Ψ = c₂`. -/
theorem exists_hom_of_hasStableContractionFibres {X Y₁ Y₂ : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) {g : ℕ} (hg : 2 ≤ g)
    (hgen : X.HasFibresOfGenus g) {hb₁ : Y₁.base = X.base}
    {hb₂ : Y₂.base = X.base} {c₁ : X.total ⟶ Y₁.total} {c₂ : X.total ⟶ Y₂.total}
    (hc₁ : c₁ ≫ Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) = X.toBase)
    (hc₂ : c₂ ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) = X.toBase)
    (h1₁ : X.IsUniversalStructureContraction B hZ Y₁ hb₁ c₁)
    (h2₁ : X.HasStableContractionFibres B hZ Y₁ hb₁ c₁)
    (h2₂ : X.HasStableContractionFibres B hZ Y₂ hb₂ c₂) :
    ∃ Ψ : Y₁.total ⟶ Y₂.total, Ψ ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) =
      Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) ∧ c₁ ≫ Ψ = c₂ := by
  set g₁ := Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) with hg₁
  set g₂ := Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) with hg₂
  let F := schemeSpaceFunctorFullyFaithful B (S := integerBase) hZ
  have hloc : ∀ s : X.base.left.1, ∃ (W : BigFppfOver B integerBase hZ) (j : W ⟶ X.base),
      IsOpenImmersion ((𝒯).map j) ∧ s ∈ Set.range ((𝒯).map j) ∧
      ∃ ψ : AlgebraicSpaces.fiberProduct B integerBase hZ g₁ (schemeSpaceMap j) ⟶ Y₂.total,
        ψ ≫ g₂ = ObjectProperty.homMk (pullback.snd g₁.hom (schemeSpaceMap j).hom) ≫
          schemeSpaceMap j ∧
        Space.structureContractionBaseChange B integerBase hZ c₁ hc₁ (schemeSpaceMap j) ≫ ψ =
          ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap j).hom) ≫ c₂ := by
    intro s
    let p := residueFieldValuedPoint B hZ X.base s
    obtain ⟨VX, vX, qX, hqX⟩ := exists_isPullback_fieldValuedPoint B hZ X p
    obtain ⟨V₁, v₁, q₁, hq₁⟩ := exists_isPullback_fieldValuedPoint_of_base_eq Y₁ hb₁ p
    obtain ⟨V₂, v₂, q₂, hq₂⟩ := exists_isPullback_fieldValuedPoint_of_base_eq Y₂ hb₂ p
    -- the fibres of the contractions
    have hfib : ∀ {Y : CurveFamily B hZ} (hb : Y.base = X.base) {c : X.total ⟶ Y.total}
        (_ : c ≫ Y.toBase ≫ eqToHom (congrArg schemeSpace hb) = X.toBase)
        {V : BigFppfOver B integerBase hZ} {v : V ⟶ p.siteObject} {q : schemeSpace V ⟶ Y.total}
        (_ : IsPullback q (schemeSpaceMap v) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb))
          (schemeSpaceMap p.value)),
        ∃ a : VX ⟶ V, a ≫ v = vX ∧ qX ≫ c = schemeSpaceMap a ≫ q := by
      intro Y hb c hc V v q hq
      let a' := hq.lift (qX ≫ c) (schemeSpaceMap vX) (by rw [Category.assoc, hc]; exact hqX.w)
      refine ⟨F.preimage a', F.map_injective ?_, ?_⟩
      · change schemeSpaceMap (F.preimage a' ≫ v) = schemeSpaceMap vX
        rw [schemeSpaceMap_comp]
        exact (congrArg (· ≫ schemeSpaceMap v) (F.map_preimage a')).trans (hq.lift_snd _ _ _)
      · exact (hq.lift_fst _ _ _).symm.trans
          (congrArg (· ≫ q) (F.map_preimage a').symm)
    obtain ⟨a₁, ha₁, hqa₁⟩ := hfib hb₁ hc₁ hq₁
    obtain ⟨a₂, ha₂, hqa₂⟩ := hfib hb₂ hc₂ hq₂
    have hqX' := isPullback_yoneda_of_isPullback_schemeSpace X.toBase p hqX
    have hq₁' := isPullback_yoneda_of_isPullback_schemeSpace g₁ p hq₁
    have hq₂' := isPullback_yoneda_of_isPullback_schemeSpace g₂ p hq₂
    have hqa₁' : qX.hom ≫ c₁.hom = yoneda.map a₁ ≫ q₁.hom := congrArg (fun m => m.hom) hqa₁
    have hqa₂' : qX.hom ≫ c₂.hom = yoneda.map a₂ ≫ q₂.hom := congrArg (fun m => m.hom) hqa₂
    have hst₁ := h2₁ p VX V₁ vX v₁ qX.hom q₁.hom a₁ hqX' hq₁' ha₁ hqa₁'
    obtain ⟨φ, hφa, hφ, -⟩ := existsUnique_fibreIso_of_hasStableContractionFibres hX hg hgen h2₁ h2₂
      p hqX' hq₁' hq₂' ha₁ ha₂ hqa₁' hqa₂'
    obtain ⟨W, j, hj, hs, ψ, hψ₁, hψ₂⟩ :=
      extendsFibreIsoNearPoint X Y₁ Y₂ hb₁ hb₂ c₁ c₂ hc₁ hc₂ s VX V₁ V₂ vX v₁ v₂
      qX q₁ q₂ hqX hq₁ hq₂ a₁ a₂ ha₁ ha₂ hqa₁ hqa₂ φ hφ hφa
      hst₁.isIso_unitToPushforwardObjUnit hst₁.isZero_rightDerived_one
    refine ⟨W, j, hj, hs, ψ.hom ≫ ObjectProperty.homMk (pullback.fst g₂.hom (schemeSpaceMap j).hom),
      ?_, ?_⟩
    · rw [Category.assoc, (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ g₂ _).w,
        ← Category.assoc, hψ₁]
    · rw [← Category.assoc, hψ₂, Space.structureContractionBaseChange_fst]
  choose W j hj hs ψ hψg hψc using hloc
  have hcov := Space.isFppfCovering_yoneda_of_openCover B integerBase hZ W j hj
    (fun x => ⟨x, hs x⟩)
  have hφ : Space.IsFpqcCovering B integerBase hZ (fun s => (schemeSpaceMap (j s)).hom) :=
    Space.isFpqcCovering_of_isFppfCovering B integerBase hZ _ _ hcov
  obtain ⟨Ψ, h₁, h₂, -⟩ := Space.exists_desc_of_isFpqcCovering_of_isIso_structureSharp
    (X := X.total) (Y₁ := Y₁.total) (Y₂ := Y₂.total)
    (X' := fun s => AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase (schemeSpaceMap (j s)))
    (Y' := fun s => AlgebraicSpaces.fiberProduct B integerBase hZ g₁ (schemeSpaceMap (j s))) j hφ
    X.toBase g₁ g₂ (isSeparated_toBase_comp_eqToHom Y₂ hb₂) c₁ c₂ hc₁ hc₂
    (isIso_structureSharp_of_isUniversalStructureContraction hc₁ h1₁)
    (fun s => ObjectProperty.homMk (pullback.fst X.toBase.hom (schemeSpaceMap (j s)).hom))
    (fun s => ObjectProperty.homMk (pullback.snd X.toBase.hom (schemeSpaceMap (j s)).hom))
    (fun s => AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase _)
    (fun s => ObjectProperty.homMk (pullback.fst g₁.hom (schemeSpaceMap (j s)).hom))
    (fun s => ObjectProperty.homMk (pullback.snd g₁.hom (schemeSpaceMap (j s)).hom))
    (fun s => AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ g₁ _)
    (fun s => Space.structureContractionBaseChange B integerBase hZ c₁ hc₁ (schemeSpaceMap (j s)))
    (fun s => Space.structureContractionBaseChange_fst B integerBase hZ c₁ hc₁ _)
    (fun s => Space.structureContractionBaseChange_snd B integerBase hZ c₁ hc₁ _) ψ hψg hψc
  exact ⟨Ψ, h₁, h₂⟩

/-- **The uniqueness in Stacks 0E8A**. If `cᵢ : X ⟶ Yᵢ`, `i = 1, 2`, both
satisfy conditions (1) and (2) of Stacks 0E8A, there is exactly one isomorphism `e : Y₁ ≅ Y₂`
over the base with `c₁ ≫ e = c₂`. -/
theorem existsUnique_iso_of_hasStableContractionFibres {X Y₁ Y₂ : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) {g : ℕ} (hg : 2 ≤ g)
    (hgen : X.HasFibresOfGenus g) {hb₁ : Y₁.base = X.base}
    {hb₂ : Y₂.base = X.base} {c₁ : X.total ⟶ Y₁.total} {c₂ : X.total ⟶ Y₂.total}
    (hc₁ : c₁ ≫ Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) = X.toBase)
    (hc₂ : c₂ ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) = X.toBase)
    (h1₁ : X.IsUniversalStructureContraction B hZ Y₁ hb₁ c₁)
    (h1₂ : X.IsUniversalStructureContraction B hZ Y₂ hb₂ c₂)
    (h2₁ : X.HasStableContractionFibres B hZ Y₁ hb₁ c₁)
    (h2₂ : X.HasStableContractionFibres B hZ Y₂ hb₂ c₂) :
    ∃ e : Y₁.total ≅ Y₂.total, c₁ ≫ e.hom = c₂ ∧
      e.hom ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) =
        Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) ∧
      ∀ e' : Y₁.total ≅ Y₂.total, c₁ ≫ e'.hom = c₂ →
        e'.hom ≫ Y₂.toBase ≫ eqToHom (congrArg schemeSpace hb₂) =
          Y₁.toBase ≫ eqToHom (congrArg schemeSpace hb₁) → e' = e := by
  obtain ⟨Ψ, hΨb, hΨc⟩ := exists_hom_of_hasStableContractionFibres hX hg hgen hc₁ hc₂ h1₁ h2₁
    h2₂
  obtain ⟨Φ, hΦb, hΦc⟩ := exists_hom_of_hasStableContractionFibres hX hg hgen hc₂ hc₁ h1₂ h2₂
    h2₁
  have := isIso_structureSharp_of_isUniversalStructureContraction_self hc₁ h1₁
  have := isIso_structureSharp_of_isUniversalStructureContraction_self hc₂ h1₂
  have h₁ : Ψ ≫ Φ = 𝟙 _ := comp_eq_id_of_comp_eq hb₁ hb₂ hΨb hΦb hΨc hΦc
  have h₂ : Φ ≫ Ψ = 𝟙 _ := comp_eq_id_of_comp_eq hb₂ hb₁ hΦb hΨb hΦc hΨc
  exact ⟨⟨Ψ, Φ, h₁, h₂⟩, hΨc, hΨb, fun e' he' hb' => Iso.ext <|
    Space.eq_of_comp_eq_of_isIso_structureSharp B integerBase hZ c₁ _
      (isSeparated_toBase_comp_eqToHom Y₂ hb₂) (hb'.trans hΨb.symm) (he'.trans hΨc.symm)⟩

end CurveFamily

end AlgebraicGeometry

end
