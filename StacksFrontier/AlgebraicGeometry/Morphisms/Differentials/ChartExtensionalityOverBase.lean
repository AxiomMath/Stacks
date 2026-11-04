module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBaseChange

/-!
# Extensionality for differential operators on a fibre product relative to the base

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes. An affine chart of `X ×_S Y` is the
spectrum of a tensor product `A ⊗_R B`, where `R = Γ(S, W)`, `A = Γ(X, U)` and `B = Γ(Y, V)`, and
the composite `X ×_S Y ⟶ X ⟶ S` restricts on the chart to `Spec` of the algebra map
`R ⟶ A ⊗_R B` followed by the open immersion `Spec R ⟶ S`. Since the order of a differential
operator is unchanged when the relative base is replaced by an open subscheme of itself through
which the morphism factors, the differential operators of order at most `k` on `X ×_S Y / S`
defined over the opens of such a chart are exactly the differential operators of order at most `k`
relative to `R ⟶ A ⊗_R B` between the modules of sections on the chart. Consequently a
differential operator of order at most `k` on `X ×_S Y / S` out of a quasi-coherent module is
determined by its action on the sections over each affine chart.

This is the `S`-relative mirror of
`AlgebraicGeometry.globalDiffOp_ext_of_chart_sections` and of the chart machinery it rests on,
which are stated for the order relative to the second projection `X ×_S Y ⟶ Y`. The `S`-relative
form is what a composite such as `(1 ⊠ E) ∘ (D ⊠ 1)` satisfies: the two factors have finite order
relative to the two projections separately, and their composite only relative to `S`.

## Main definitions

* `Stacks.FibreProductAffineChart.Chart.diffOpEquivOverBase`: the differential operators of order
  at most `k` on `X ×_S Y / S` over the opens of a chart, identified with the differential
  operators of order at most `k` relative to `R ⟶ A ⊗_R B` on the chart's modules of sections.

## Main results

* `Stacks.FibreProductAffineChart.Chart.specIso_inv_ι_comp_fst_comp`: the chart, read as the
  spectrum of a tensor product, maps to `S` by `Spec` of the algebra map `R ⟶ A ⊗_R B` followed by
  the open immersion `Spec R ⟶ S`.
* `Stacks.FibreProductAffineChart.Chart.diffOpEquivOverBase_apply_coe_apply`: the linear map
  attached to a differential operator is its action on the sections over the chart.
* `Stacks.FibreProductAffineChart.Chart.rawOp_ext_of_chart_sections_overBase`: two differential
  operators of order at most `k` on `X ×_S Y / S` over the opens of one chart which agree on the
  sections over the chart are equal.
* `AlgebraicGeometry.globalDiffOp_ext_of_chart_sections_overBase`: two differential operators of
  order at most `k` on `X ×_S Y / S` out of a quasi-coherent module which agree on the sections
  over every affine chart are equal.

## Implementation notes

The `Γ(S, W)`-algebra structure on `A ⊗_R B` used here is the canonical one, so unlike the
`Y`-relative development no local instance for the right factor is needed. The chart equivalence is
assembled from `AlgebraicGeometry.diffOpEquivGlobalDiffOpRestrictOfIso`, which moves an operator
defined over the opens of the chart to the spectrum of the tensor product, and
`AlgebraicGeometry.AffineDiffOp.globalDiffOpEquiv` (Tag 0G44) on that affine scheme, taken with
`R = Γ(S, W)`: the identification of Tag 0G44 does not care which subring the linearity is read
over.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat

universe u

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry RingHomClass

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

section SpecIso

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)

/-- **A chart lies over `S` through its base.** Read as the spectrum of a tensor product, a chart
maps to `S` by `Spec` of the algebra map `Γ(S, W) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` followed by the
open immersion `Spec Γ(S, W) ⟶ S`. -/
theorem specIso_inv_ι_comp_fst_comp :
    ((c.specIso hl hr).inv ≫ c.ι) ≫ (pullback.fst a b ≫ a) =
      Spec.map (ofHom (algebraMap Γ(S, c.base)
        (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))) ≫ c.fromSpecBase := by
  rw [Category.assoc, ι_fst_assoc, specIso_inv_fst_assoc, ← specMap_leftHom_fromSpec,
    ← Category.assoc, ← Spec.map_comp, ← hl, ← ofHom_comp]

/-- **Differential operators on an affine chart of a fibre product, relative to the base.** The
differential operators of order at most `k` on `X ×_S Y / S` between two modules on `X ×_S Y`,
defined over the opens contained in a chart, are the differential operators of order at most `k`
relative to `Γ(S, W) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` between the two modules of sections on the
chart. -/
noncomputable def diffOpEquivOverBase (M M' : (pullback a b).Modules)
    [(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι)).IsQuasicoherent] (k : ℕ) :
    letI _modAF : Module (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso
        (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).inv.hom
    letI _modAG : Module (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso
        (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).inv.hom
    letI _modRF : Module Γ(S, c.base)
        Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      Module.compHom _ (algebraMap Γ(S, c.base)
        (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))
    letI _modRG : Module Γ(S, c.base)
        Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      Module.compHom _ (algebraMap Γ(S, c.base)
        (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))
    letI _towerF : IsScalarTower Γ(S, c.base) (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      IsScalarTower.of_compHom _ _ _
    letI _towerG : IsScalarTower Γ(S, c.base) (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      IsScalarTower.of_compHom _ _ _
    {D : DiffOp.RawOp M M' c.ι.opensRange //
        DiffOp.IsDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap k D} ≃
      {D : Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) →ₗ[Γ(S, c.base)]
          Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) //
        D.IsDifferentialOperatorOfOrderLE
          (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)) k} := by
  haveI : IsOpenImmersion c.fromSpecBase := c.isAffineOpen_base.isOpenImmersion_fromSpec
  refine (diffOpEquivGlobalDiffOpRestrictOfIso (c.specIso hl hr).inv c.ι
      (pullback.fst a b ≫ a) M M' k).trans
    ((Equiv.subtypeEquivRight ?_).trans
      (AffineDiffOp.globalDiffOpEquiv (R := Γ(S, c.base))
        (Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι))
        (Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι)) k).1)
  rw [specIso_inv_ι_comp_fst_comp c hl hr]
  exact fun E ↦ isGlobalDiffOpOfOrder_comp_isOpenImmersion_iff _ c.fromSpecBase k E

/-- The linear map attached to a differential operator on `X ×_S Y / S` over the opens of a chart
is the operator's action on the sections over the chart. -/
theorem diffOpEquivOverBase_apply_coe_apply (M M' : (pullback a b).Modules)
    [(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι)).IsQuasicoherent] (k : ℕ)
    (D : {D : DiffOp.RawOp M M' c.ι.opensRange //
      DiffOp.IsDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap k D})
    (x : Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤))
    (hV : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤ ≤ c.ι.opensRange) :
    (diffOpEquivOverBase c hl hr M M' k D).1 x = D.1 (Over.mk (homOfLE hV)) x :=
  ((AffineDiffOp.globalDiffOpEquiv
      (R := Γ(S, c.base)) (Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι))
      (Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι)) k).2 _ x).trans
    (congrArg (fun z ↦ z x)
      (diffOpEquivGlobalDiffOpRestrictOfIso_coe_apply (c.specIso hl hr).inv c.ι
        (pullback.fst a b ≫ a) M M' k D ⊤ hV))

/-- **Two differential operators on `X ×_S Y / S` over a chart which agree on the sections over
the chart are equal.** Both are differential operators of order at most `k` relative to `S`
defined over the opens contained in the chart, and agreement is only required at the chart
itself. -/
theorem rawOp_ext_of_chart_sections_overBase (M M' : (pullback a b).Modules)
    [(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι)).IsQuasicoherent] (k : ℕ)
    (D E : {D : DiffOp.RawOp M M' c.ι.opensRange //
      DiffOp.IsDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap k D})
    (hV : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤ ≤ c.ι.opensRange)
    (h : ∀ x, D.1 (Over.mk (homOfLE hV)) x = E.1 (Over.mk (homOfLE hV)) x) : D.1 = E.1 := by
  let _modA (N : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).Modules) :
      Module (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)) Γ(N, ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso
      (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).inv.hom
  let _modR (N : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).Modules) :
      Module Γ(S, c.base) Γ(N, ⊤) :=
    Module.compHom _ (algebraMap Γ(S, c.base)
      (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))
  refine congrArg Subtype.val
    ((diffOpEquivOverBase c hl hr M M' k).injective (Subtype.ext (LinearMap.ext fun x ↦ ?_)))
  exact (diffOpEquivOverBase_apply_coe_apply c hl hr M M' k D x hV).trans
    ((h x).trans (diffOpEquivOverBase_apply_coe_apply c hl hr M M' k E x hV).symm)

end SpecIso

end Chart

end Stacks.FibreProductAffineChart

namespace AlgebraicGeometry

open Stacks.FibreProductAffineChart

/-- **A differential operator on `X ×_S Y` relative to `S` is determined by its action on the
affine charts.** Two differential operators of order at most `k` on `X ×_S Y / S`, out of a
quasi-coherent module, which agree on the sections over every affine chart of `X ×_S Y`, are
equal. -/
theorem globalDiffOp_ext_of_chart_sections_overBase {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (k : ℕ) {M M' : (pullback a b).Modules} [M.IsQuasicoherent] (D E : DiffOp.GlobalOp M M')
    (hD : DiffOp.IsGlobalDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap k D)
    (hE : DiffOp.IsGlobalDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap k E)
    (hagree : ∀ (c : Chart a b) (s : Γ(M, c.ι.opensRange)),
      D (op c.ι.opensRange) s = E (op c.ι.opensRange) s) :
    D = E := by
  refine DiffOp.globalOp_ext_of_cover (fun c : Chart a b ↦ (Chart.ι c).opensRange)
    (fun z ↦ (exists_chart_mem a b z).imp fun _ ↦ id) D E
    (DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k _ (hD ⊤))
    (DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k _ (hE ⊤)) fun c ↦ ?_
  let := c.algebraLeft
  let := c.algebraRight
  have heq : ((c.specIso (Chart.ofHom_algebraMap_left c)
      (Chart.ofHom_algebraMap_right c)).inv ≫ c.ι) ''ᵁ ⊤ = c.ι.opensRange := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso]
  have htrans : ∀ (V V' : (pullback a b).Opens), V = V' →
      (∀ s, D (op V') s = E (op V') s) → ∀ s, D (op V) s = E (op V) s := by
    rintro V V' rfl h
    exact h
  exact Chart.rawOp_ext_of_chart_sections_overBase c (Chart.ofHom_algebraMap_left c)
    (Chart.ofHom_algebraMap_right c) M M' k ⟨D.restrict (Chart.ι c).opensRange, hD _⟩
    ⟨E.restrict (Chart.ι c).opensRange, hE _⟩ heq.le (htrans _ _ heq (hagree c))

end AlgebraicGeometry

end
