module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableContractionDescent
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelDescent
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.StableModelLocality

/-!
# Stable models glue along an étale cover

Let `X ⟶ S` be a prestable family of curves of genus `g ≥ 2`. Suppose that every point of `S` lies
in the image of the base of some morphism of families `X' ⟶ X` whose base map is étale and such
that `X'` has a stable model in the sense of Stacks 0E8A, and that stable models of a prestable
family are related by a morphism of families compatible with the contractions. Then `X` has a
stable model. This is the gluing step in the proof of Stacks 0E8A: the local models form a
descent datum for the stack of curves (Stacks 0D52), which is effective; the glued family is
prestable, condition (1) of Stacks 0E8A holds étale locally hence globally, and condition (2) and
stability are checked on the fibres.

## Main results

* `AlgebraicGeometry.C1590Private.isModelRelation_isStableModel_of_exists_hom`: stable models of
  genus `g` of prestable families form a model relation as soon as any two stable models of a
  prestable family are related.
* `AlgebraicGeometry.C1590Private.exists_isStableModel_of_locally`: a prestable family of genus
  `g ≥ 2` has a stable model when it has one étale locally on the base.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0D52](https://stacks.math.columbia.edu/tag/0D52)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **Stable models of prestable families of genus `g` form a model relation** as soon as any two
stable models of a prestable family are related by a morphism of families compatible with the base
maps and with the contractions: such a morphism is unique
(`AlgebraicGeometry.C1590Private.IsStableModel.hom_ext`), and stable models lie over their base map
and are stable under base change (`AlgebraicGeometry.C1590Private.IsStableModel.of_hom`), as is
prestability of the source. -/
theorem isModelRelation_isStableModel_of_exists_hom {g : ℕ}
    (huniq : ∀ {X Y₁ Y₂ : CurveFamily B hZ} {b₁ : X.base ⟶ Y₁.base} {c₁ : X.total ⟶ Y₁.total}
      {b₂ : X.base ⟶ Y₂.base} {c₂ : X.total ⟶ Y₂.total},
      IsPrestableCurveFamily B hZ X → IsStableModel B hZ g b₁ c₁ → IsStableModel B hZ g b₂ c₂ →
        ∃ e : Y₁ ⟶ Y₂, b₁ ≫ e.baseMap = b₂ ∧ c₁ ≫ e.totalMap = c₂) :
    IsModelRelation (fun X Y (b : X.base ⟶ Y.base) c =>
      IsPrestableCurveFamily B hZ X ∧ IsStableModel B hZ g b c) where
  w h := h.2.comp_toBase
  exists_hom h₁ h₂ := huniq h₁.1 h₁.2 h₂.2
  hom_ext h₁ h₂ _ _ he hc he' hc' := IsStableModel.hom_ext h₁.2 h₂.2 he hc he' hc'
  baseChange := by
    intro _ _ _ _ φ ψ _ _ b' c' h hb' hb hc hc'
    have := hb'
    exact ⟨CurveFamily.isPrestableCurveFamily_of_hom φ h.1, h.2.of_hom φ ψ b' c' hb hc hc'⟩

/-- **Stable models glue along an étale cover.** Let `X` be a prestable family of curves with
fibres of genus `g ≥ 2`. Suppose that every point `s` of the base lies in the image of the base
map of a morphism of families `φ : X' ⟶ X` which is étale on bases and such that `X'` has a
stable model of genus `g`, and that any two stable models of a prestable family are related by a
morphism of families compatible with the base maps and the contractions. Then `X` has a stable
model of genus `g`. -/
theorem exists_isStableModel_of_locally {g : ℕ} (hg : 2 ≤ g) {X : CurveFamily B hZ}
    (hX : IsPrestableCurveFamily B hZ X) (hgen : X.HasFibresOfGenus g)
    (huniq : ∀ {X Y₁ Y₂ : CurveFamily B hZ} {b₁ : X.base ⟶ Y₁.base} {c₁ : X.total ⟶ Y₁.total}
      {b₂ : X.base ⟶ Y₂.base} {c₂ : X.total ⟶ Y₂.total},
      IsPrestableCurveFamily B hZ X → IsStableModel B hZ g b₁ c₁ → IsStableModel B hZ g b₂ c₂ →
        ∃ e : Y₁ ⟶ Y₂, b₁ ≫ e.baseMap = b₂ ∧ c₁ ≫ e.totalMap = c₂)
    (hloc : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
      ∃ (X' : CurveFamily B hZ) (φ : X' ⟶ X),
        Etale ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧
        s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map φ.baseMap) ∧
        ∃ (Y' : CurveFamily B hZ) (b' : X'.base ⟶ Y'.base) (c' : X'.total ⟶ Y'.total),
          IsStableModel B hZ g b' c') :
    ∃ (Y : CurveFamily B hZ) (b : X.base ⟶ Y.base) (c : X.total ⟶ Y.total),
      IsStableModel B hZ g b c := by
  have hR := isModelRelation_isStableModel_of_exists_hom huniq
  choose Xi φ hφ hs Y' b' c' hi using hloc
  choose m _ _ using fun s => exists_model_of_exists hR
    ⟨CurveFamily.isPrestableCurveFamily_of_hom (φ s) hX, hi s⟩
  have hsurj : ∀ s : (BigFppfOver.toScheme B integerBase hZ).obj X.base,
      ∃ i, s ∈ Set.range ((BigFppfOver.toScheme B integerBase hZ).map (φ i).baseMap) :=
    fun s => ⟨s, hs s⟩
  have hcov : Sieve.ofArrows (fun i => (Xi i).base) (fun i => (φ i).baseMap) ∈
      BigFppfOver.topology B integerBase hZ X.base := by
    simpa only [Category.comp_id] using
      ofArrows_comp_mem_topology (𝟙 X.base) (fun i => (Xi i).base) (fun i => (φ i).baseMap) hφ hsurj
  obtain ⟨x, hx, c, ψ, hc, hψ⟩ := exists_descent_of_models Xi φ m hR hcov
  let bi := fun i => eqToHom (m i).base_eq.symm
  have hmi : ∀ i, IsStableModel B hZ g (bi i) (m i).contraction := fun i => (m i).isModel.2
  have hψb : ∀ i, bi i ≫ (ψ i).baseMap = (φ i).baseMap ≫ eqToHom hx.symm := fun i => by
    rw [(hψ i).1, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hψc := fun i => (hψ i).2
  have hpre := isPrestableCurveFamily_of_cover hx hc φ hφ hsurj hmi ψ hψb hψc hX
  have hF := isFibrewiseStableContraction_of_cover hX hpre (eqToHom hx.symm) c hc φ hsurj bi
    (fun i => (m i).contraction) hmi ψ hψb hψc
  have hst := isStableCurveFamily_of_isFibrewiseStableContraction hX hgen hg hpre
    (eqToHom hx.symm) c hc hF
  exact ⟨x, eqToHom hx.symm, c,
    { isIso_base := inferInstance
      comp_toBase := hc
      isStable := hst.1
      hasFibresOfGenus := hst.2
      universallyAcyclic := isUniversallyAcyclic_of_cover hx hc φ hφ hsurj hmi ψ hψb hψc
      fibrewiseStable := hF }⟩

end AlgebraicGeometry.C1590Private

end
