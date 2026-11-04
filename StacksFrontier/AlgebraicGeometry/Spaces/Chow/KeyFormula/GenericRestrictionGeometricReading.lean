module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericFieldChartRatio

/-!
# The reading of a meromorphic section of `ℒ|_Z` at a field point of a chart of `Spec κ(u)`

Let `X`, `Z`, `ℒ`, `V`, `e`, `W' = V ×_X Z` be as in
`StacksFrontier/AlgebraicGeometry/Spaces/Chow/KeyFormula/GenericFieldChartRatio.lean` and let `q'`
be a point of `W'` with `𝒪_{W', q'}` a field.  On an étale chart `P` of `Spec κ(u)` over `W'`,
the inverse image of `e|_Z` is `w` times the image of the generator `s_ξ`, and the pullback of
the coefficient of a meromorphic section `σ` of `ℒ|_Z` times `w` is the value of `σ`.  Evaluating
this at a field point `t : Spec K → P` which lies over `q'` (through `ψ' : κ(q') → K`) and over
`Spec κ(u)` (through `φ : κ(u) → K`) gives **the reading of `σ` at `q'`, read in `K`, times the
value of `w` at `t`, is the value of `σ` at the generic point, read in `K`.**

The chart `P` used in the proof of Stacks 0EQV is the base change
`Spec κ(u) ×_{Spec 𝒪_{U, u}} Q` of an étale chart `Q` of `Spec 𝒪_{U, u}` over the base change of
`V`; this file constructs it and its morphism to `W'`.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldStalkBaseChangeChart`: the chart
  `Spec κ(u) ×_{Spec 𝒪_{U, u}} Q`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericFieldStalkBaseChangeToChart`: its morphism to
  `W'` over `ρ_Z`.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.baseChangeChartSectionReading_mul_eq_of_point`: the
  evaluation of the comparison at a field point.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 0EQV](https://stacks.math.columbia.edu/tag/0EQV)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (V : SmallEtale B S hS X) (q' : chartScheme (Z.baseChangeChart B S hS hX V))
    (hq' : chartSchemeToPoints B S hS X V (Z.baseChangeChartProj B S hS hX V q') =
      Z.genericPoint B S hS X)

/-! ### Evaluating the comparison on `P` at a field point -/

section Evaluation

attribute [local instance] chartMeromorphicAlgebra chartMeromorphicFunctionAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (e : (W' : SmallEtale B S hS X) → (W' ⟶ V) → L.val.obj (op W'))
    (hcompat : ∀ (W₁ W₂ : SmallEtale B S hS X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))
    (hfree : ∀ (W₁ : SmallEtale B S hS X) (k : W₁ ⟶ V),
      Function.Bijective fun r : chartRing B S hS X hX W₁ ↦ r • e W₁ k)
    (hW : IsAffine (chartScheme (Z.baseChangeChart B S hS hX V)))
    (hK : @IsFractionRing ((structurePresheaf B S hS (Z.space B S hS).1).obj
        (op (Z.baseChangeChart B S hS hX V))) _
      ((meromorphicFunctionSheaf B S hS (Z.space B S hS).1 (Z.space B S hS).2).obj.obj
        (op (Z.baseChangeChart B S hS hX V))) _
      (chartMeromorphicFunctionAlgebra B S hS (X := Z.space B S hS)
        (Z.baseChangeChart B S hS hX V)))
    (hz : IsField ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.stalk q'))
    (P : SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1)
    (g : (SmallEtale.toOver B S hS _).obj P ⟶
      (SmallEtale.toOver B S hS Z.subspace.toFunctor).obj (Z.baseChangeChart B S hS hX V))
    (hg : P.1.hom ≫ (Z.genericFieldMorphism B S hS hX hdec).hom =
      yoneda.map g ≫ (Z.baseChangeChart B S hS hX V).1.hom)

/-- **Evaluating the comparison on `P` at a field point.**  Let `p` be a field-valued point of
`X` with a lift `t : Spec K → P` whose composite to `Spec κ(u)` is `Spec φ`
and whose composite to `W'` is `Spec ψ'` followed by `Spec κ(q') → W'`.  Then the reading at `q'`
of a meromorphic section `σ` of `ℒ|_Z` against `e|_Z`, read in `K` through `ψ'`, times the value
at `t` of the ratio of `e|_Z` to `s_ξ`, is the value of `σ` at the generic point read in `K`
through `φ`. -/
theorem PrimeDivisor.baseChangeChartSectionReading_mul_eq_of_point
    (σ : MeromorphicSection.{u, u} B S hS Z.subspace.toFunctor Z.closed.1
      (Z.restrictModule B S hS hX L))
    (p : FieldValuedPoint B S hS X)
    (t : p.siteObject B S hS X ⟶ P.obj.left)
    (φ : Z.genericResidueField B S hS hX hdec →+* p.carrier)
    (hφ : (BigFppfOver.toScheme B S hS).map (t ≫ (SmallEtale.toOver B S hS _).map
        (chartToIdEtaleChart B S hS
          P)) =
      Spec.map (CommRingCat.ofHom φ))
    (ψ' : (chartScheme (Z.baseChangeChart B S hS hX V)).residueField q' ⟶ .of p.carrier)
    (hψ' : (BigFppfOver.toScheme B S hS).map (t ≫
        g) =
      Spec.map ψ' ≫ (chartScheme (Z.baseChangeChart B S hS hX V)).fromSpecResidueField q') :
    ψ' (Z.baseChangeChartSectionReading B S hS hX L hL V e hcompat hfree hW hK q' hz σ) *
        (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op).hom
            (Z.genericFieldChartRatio B S hS hX hdec L hL V e P g hg)) =
      φ (Z.genericFieldValue B S hS hX hdec L hL σ) := by
  have := hW
  let := chartMeromorphicFunctionAlgebra B S hS (X := Z.space B S hS)
    (Z.baseChangeChart B S hS hX V)
  have := hK
  set c := Z.baseChangeChartSectionCoefficient B S hS hX L hL V e hcompat hfree σ with hc
  obtain ⟨⟨c₁, c₂⟩, hc₁₂⟩ := IsLocalization.mk'_surjective
    ((structurePresheaf B S hS (Z.space B S hS).1).obj (op (Z.baseChangeChart B S hS hX V)))⁰ c
  have hspec : c * chartToMeromorphic (X := Z.space B S hS) (Z.baseChangeChart B S hS hX V) c₂.1 =
      chartToMeromorphic (X := Z.space B S hS) (Z.baseChangeChart B S hS hX V) c₁ := by
    rw [← hc₁₂]
    exact IsLocalization.mk'_spec _ c₁ c₂
  have hrel := Z.chartDiagramRestrict_mul_genericFieldChartRatio B S hS hX hdec L hL V e
    hcompat hfree P g hg σ c₁ c₂.1 hspec
  -- evaluation at `t`
  set ev : chartRing B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (Z.genericFieldSpace B S hS hX hdec).2
      P →+*
        p.carrier :=
    (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom.comp
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op).hom with hev
  have hev_d : ∀ a : (structurePresheaf B S hS (Z.space B S hS).1).obj
      (op (Z.baseChangeChart B S hS hX V)),
      ev (chartDiagramRestrict B S hS (Z.genericFieldMorphism B S hS hX hdec)
        (Z.genericFieldChartDiagram B S hS hX hdec V P g hg) a) =
      ψ' ((chartScheme (Z.baseChangeChart B S hS hX V)).residue q'
        ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.germ ⊤ q' trivial a)) := by
    intro a
    have hle : (⊤ : ((BigFppfOver.toScheme B S hS).obj (p.siteObject B S hS X)).Opens) ≤
        (BigFppfOver.toScheme B S hS).map (t ≫
          g) ⁻¹ᵁ ⊤ :=
      fun _ _ ↦ trivial
    have h := Scheme.ΓSpecIso_appLE_eq_residue ((BigFppfOver.toScheme B S hS).map (t ≫
      g)) q' ψ'
      hψ' ⊤ trivial hle a
    refine Eq.trans ?_ h
    have hΓ : ((BigFppfOver.toScheme B S hS).map (t ≫
        g)).appLE
          ⊤ ⊤ hle = Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            g).op ≫
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op := by
      rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp, Scheme.Γ_map_op]
      simp only [Scheme.Hom.appLE]
      exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
    exact congrArg (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom
      (ConcreteCategory.congr_hom hΓ a).symm
  have hev_k : ev (((structurePresheaf B S hS (Z.genericFieldSpace B S hS hX hdec).1).map
        (chartToIdEtaleChart B S hS
          P).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom
          (Z.genericFieldValue B S hS hX hdec L hL σ))) =
      φ (Z.genericFieldValue B S hS hX hdec L hL σ) := by
    have hΓ : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS _).map
          (chartToIdEtaleChart B S hS
            P))).op ≫
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map t).op =
        (Spec.map (CommRingCat.ofHom φ)).appTop := by
      rw [← Functor.map_comp, ← op_comp, ← Functor.map_comp, hφ]
      rfl
    have hnat := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
      ((Scheme.ΓSpecIso (CommRingCat.of (Z.genericResidueField B S hS hX hdec))).inv.hom
        (Z.genericFieldValue B S hS hX hdec L hL σ))
    refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of p.carrier)).hom.hom
      (ConcreteCategory.congr_hom hΓ _)).trans (hnat.trans ?_)
    exact congrArg φ (CommRingCat.inv_hom_apply _ _)
  have hread : Z.baseChangeChartSectionReading B S hS hX L hL V e hcompat hfree hW hK q' hz σ *
      (chartScheme (Z.baseChangeChart B S hS hX V)).residue q'
        ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.germ ⊤ q' trivial c₂.1) =
      (chartScheme (Z.baseChangeChart B S hS hX V)).residue q'
        ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.germ ⊤ q' trivial c₁) := by
    have h := congrArg (chartPointResidueReading B S hS (Z.space B S hS)
      (Z.baseChangeChart B S hS hX V) hW hK q' hz) hspec
    have hr := chartPointResidueReading_algebraMap B S hS (Z.space B S hS)
      (Z.baseChangeChart B S hS hX V) hW hK q' hz
    exact (congrArg (_ * ·) (hr c₂.1).symm).trans (((map_mul _ _ _).symm.trans h).trans (hr c₁))
  have hne : ψ' ((chartScheme (Z.baseChangeChart B S hS hX V)).residue q'
      ((chartScheme (Z.baseChangeChart B S hS hX V)).presheaf.germ ⊤ q' trivial c₂.1)) ≠ 0 :=
    (map_ne_zero ψ'.hom).2 (Scheme.isUnit_residue_germ_of_mem_nonZeroDivisors
      (T := chartScheme (Z.baseChangeChart B S hS hX V)) q' hz c₂.2).ne_zero
  have h1 := congrArg ev hrel
  rw [map_mul, map_mul, hev_d, hev_d, hev_k, ← hread, map_mul] at h1
  refine mul_right_cancel₀ hne ?_
  rw [mul_right_comm]
  exact h1

end Evaluation

/-! ### The base change `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q` of a chart of `Spec 𝒪_{U, u}` -/

section BaseChange

attribute [local instance] chartMeromorphicAlgebra chartMeromorphicFunctionAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

/-- The closed point `c : Spec κ(u) → Spec 𝒪_{U, u}` is representable. -/
theorem PrimeDivisor.representable_genericFieldToStalk :
    yoneda.relativelyRepresentable (Z.genericFieldToStalk B S hS hX hdec).hom :=
  relativelyRepresentable_yoneda_map B S hS (Z.genericFieldToStalkSpec B S hS hX hdec)

/-- **The base change `Spec κ(u) ×_{Spec 𝒪_{U, u}} Q`** of an étale chart `Q` of `Spec 𝒪_{U, u}`
along the closed point, an étale chart of `Spec κ(u)`. -/
abbrev PrimeDivisor.genericFieldStalkBaseChangeChart
    (Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1) :
    SmallEtale B S hS (Z.genericFieldSpace B S hS hX hdec).1 :=
  (smallBaseChange B S hS (Z.genericFieldToStalk B S hS hX hdec)
    (Z.representable_genericFieldToStalk B S hS hX hdec)).obj Q

/-- The cartesian square of charts over the closed point at the base change of a chart `Q`. -/
abbrev PrimeDivisor.genericFieldStalkBaseChangeDiagram
    (Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1) :
    ChartDiagram B S hS (Z.genericFieldSpace B S hS hX hdec).1
      (Z.genericStalkSpace B S hS hX hdec).1 (Z.genericFieldToStalk B S hS hX hdec).hom :=
  ⟨Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q, Q,
    (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom,
    ((Z.representable_genericFieldToStalk B S hS hX hdec).isPullback Q.obj.hom).w⟩

variable (V : SmallEtale B S hS X) (Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V)

/-- A chart `Q` of `Spec 𝒪_{U, u}` over the base change of `V` maps to `V` over `X`. -/
theorem PrimeDivisor.genericStalkBaseChangeChart_comm :
    Q.obj.hom ≫ (Z.genericStalkMorphism B S hS hX hdec).hom =
      yoneda.map ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) ≫ V.obj.hom := by
  refine ((congrArg (· ≫ (Z.genericStalkMorphism B S hS hX hdec).hom)
    (CostructuredArrow.w ι.hom).symm).trans (Category.assoc _ _ _)).trans ?_
  refine (congrArg (yoneda.map ι.hom.left ≫ ·)
    (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).comm).trans ?_
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ V.obj.hom)
    (yoneda.map_comp _ _).symm)

/-- The square defining the morphism `P → W'` from the base change `P` of `Q` to the
base-change chart `W' = V ×_X Z`. -/
theorem PrimeDivisor.genericFieldStalkBaseChange_lift_cond :
    ((Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).obj.hom ≫
        (Z.genericFieldMorphism B S hS hX hdec).hom) ≫ (Z.inclusionHom B S hS hX).hom =
      yoneda.map ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom ≫
        (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) ≫ V.obj.hom := by
  have h1 : (Z.genericFieldMorphism B S hS hX hdec).hom ≫ (Z.inclusionHom B S hS hX).hom =
      (Z.genericFieldToStalk B S hS hX hdec).hom ≫ (Z.genericStalkMorphism B S hS hX hdec).hom :=
    congrArg (fun f ↦ f.hom) (Z.genericFieldMorphism_comp_inclusion B S hS hX hdec)
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h1).trans ?_)
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ (Z.genericStalkMorphism B S hS hX hdec).hom)
    ((Z.representable_genericFieldToStalk B S hS hX hdec).isPullback Q.obj.hom).w).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Z.genericStalkBaseChangeChart_comm B S hS hX hdec V Q ι)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ V.obj.hom) (yoneda.map_comp _ _).symm

/-- **The morphism `P → W'`** from the base change `P` of `Q` to the base-change chart
`W' = V ×_X Z`, over `ρ_Z`. -/
def PrimeDivisor.genericFieldStalkBaseChangeToChart :
    (SmallEtale.toOver B S hS _).obj (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q) ⟶
      (SmallEtale.toOver B S hS Z.subspace.toFunctor).obj (Z.baseChangeChart B S hS hX V) :=
  (Z.isClosedImmersion_inclusionHom B S hS hX).rep.lift
    ((Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).obj.hom ≫
      (Z.genericFieldMorphism B S hS hX hdec).hom)
    ((Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom ≫
      (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g)
    (Z.genericFieldStalkBaseChange_lift_cond B S hS hX hdec V Q ι)

/-- The morphism `P → W'` lies over `ρ_Z`. -/
theorem PrimeDivisor.genericFieldStalkBaseChangeToChart_comm :
    (Z.genericFieldStalkBaseChangeChart B S hS hX hdec Q).1.hom ≫
        (Z.genericFieldMorphism B S hS hX hdec).hom =
      yoneda.map (Z.genericFieldStalkBaseChangeToChart B S hS hX hdec V Q ι) ≫
        (Z.baseChangeChart B S hS hX V).1.hom :=
  ((Z.isClosedImmersion_inclusionHom B S hS hX).rep.lift_fst _ _ _).symm

/-- The morphism `P → W'` followed by `W' → V` is `P → Q → V`. -/
theorem PrimeDivisor.genericFieldStalkBaseChangeToChart_comp_g :
    Z.genericFieldStalkBaseChangeToChart B S hS hX hdec V Q ι ≫
        (Z.baseChangeChartDiagram B S hS hX V).g =
      (Z.representable_genericFieldToStalk B S hS hX hdec).snd Q.obj.hom ≫
        (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g :=
  (Z.isClosedImmersion_inclusionHom B S hS hX).rep.lift_snd _ _ _

end BaseChange

end AlgebraicGeometry.Space

end
