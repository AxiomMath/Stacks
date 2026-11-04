module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.BoxProductPureTensors
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProductQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.OperatorTransportIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.AffineDifferentialOperators

/-!
# Differential operators on an affine chart of a fibre product

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes. An affine chart of the fibre product
`X ×_S Y` is the spectrum of a tensor product `A ⊗_R B`, where `R = Γ(S, W)`, `A = Γ(X, U)` and
`B = Γ(Y, V)` for affine opens `W ⊆ S`, `U ⊆ a⁻¹(W)`, `V ⊆ b⁻¹(W)`, and the second projection of
the fibre product restricts on the chart to `Spec` of the algebra map `B ⟶ A ⊗_R B` followed by
the open immersion `Spec B ⟶ Y`. Since the order of a differential operator is unchanged when the
relative base is replaced by an open subscheme of itself through which the morphism factors, the
differential operators of order at most `k` on `X ×_S Y / Y` defined over the opens of such a
chart are exactly the differential operators of order at most `k` relative to `B ⟶ A ⊗_R B`
between the modules of sections on the chart. Consequently a differential operator of order at
most `k` on `X ×_S Y / Y` out of a quasi-coherent module is determined by its action on the
sections over each affine chart.

## Main definitions

* `Stacks.FibreProductAffineChart.Chart.algebraLeft` and
  `Stacks.FibreProductAffineChart.Chart.algebraRight`: the algebra structures a chart carries
  through its two structure maps.
* `Stacks.FibreProductAffineChart.Chart.diffOpEquiv`: the differential operators of order at most
  `k` on `X ×_S Y / Y` over the opens of a chart, identified with the differential operators of
  order at most `k` relative to `B ⟶ A ⊗_R B` on the chart's modules of sections.

## Main results

* `DiffOp.RawOp.isBaseLinear_comp` and `DiffOp.RawOp.isBaseLinear_of_comp_isOpenImmersion`:
  linearity over the relative base is unchanged when the base is replaced by an open subscheme of
  itself through which the morphism factors.
* `AlgebraicGeometry.isDiffOpOfOrder_comp_isOpenImmersion_iff` and
  `AlgebraicGeometry.isGlobalDiffOpOfOrder_comp_isOpenImmersion_iff`: the same for the order
  predicates.
* `Stacks.FibreProductAffineChart.Chart.specIso_inv_ι_comp_snd`: the chart, read as the spectrum
  of a tensor product, maps to `Y` by `Spec` of the algebra map `B ⟶ A ⊗_R B` followed by the open
  immersion `Spec B ⟶ Y`.
* `Stacks.FibreProductAffineChart.Chart.diffOpEquiv_apply_coe_apply`: the linear map attached to a
  differential operator is its action on the sections over the chart.
* `Stacks.FibreProductAffineChart.Chart.rawOp_ext_of_chart_sections`: two differential operators
  of order at most `k` on `X ×_S Y / Y` over the opens of one chart which agree on the sections
  over the chart are equal.
* `AlgebraicGeometry.iSup_opensRange_chart_ι`: the affine charts cover the fibre product.
* `AlgebraicGeometry.existsUnique_globalDiffOp_of_charts`: a chart-indexed family of differential
  operators of order at most `k` on `X ×_S Y / Y` agreeing on overlaps glues uniquely.
* `AlgebraicGeometry.globalDiffOp_ext_of_chart_sections`: two differential operators of order at
  most `k` on `X ×_S Y / Y` out of a quasi-coherent module which agree on the sections over every
  affine chart are equal.

## Implementation notes

The order predicate on `W/Y` splits, by `AlgebraicGeometry.isDiffOpOfOrder_iff_sections`, into two
clauses that do not mention the relative base at all and the clause
`DiffOp.RawOp.IsBaseLinear`, which refers to the base only through the maps
`AlgebraicGeometry.Scheme.Hom.appLE` of the structure morphism. Changing the base along an open
immersion therefore only has to be checked on that clause, where it is the surjectivity of
`AlgebraicGeometry.Scheme.Hom.appIso`.

The chart equivalence is assembled from
`AlgebraicGeometry.diffOpEquivGlobalDiffOpRestrictOfIso`, which moves an operator defined over the
opens of the chart to the spectrum of the tensor product, and
`AlgebraicGeometry.AffineDiffOp.globalDiffOpEquiv` (Tag 0G44) on that affine scheme. The algebra
structure on `A ⊗_R B` over `B` is `Algebra.TensorProduct.rightAlgebra`, installed as a local
instance; Mathlib has no global such instance.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat

universe u

namespace DiffOp.RawOp

open AlgebraicGeometry

variable {W Z Y : Scheme.{u}} (g : W ⟶ Z) (h : Z ⟶ Y) {M M' : W.Modules} {U : W.Opens}

/-- An operator linear over the relative base `g : W ⟶ Z` is linear over any further base
`Z ⟶ Y`: a section of the structure sheaf of `Y` restricts to `W` through `Z`. -/
theorem isBaseLinear_comp (D : DiffOp.RawOp M M' U) (hD : D.IsBaseLinear g) :
    D.IsBaseLinear (g ≫ h) := by
  intro T V hV s
  have h₂ : T.left ≤ g ⁻¹ᵁ (h ⁻¹ᵁ V) := by rwa [← Scheme.Hom.comp_preimage]
  have key : ∀ x, g.appLE (h ⁻¹ᵁ V) T.left h₂ (h.app V x) = (g ≫ h).appLE V T.left hV x := by
    rw [Scheme.Hom.comp_appLE]
    exact fun _ ↦ rfl
  rw [← key]
  exact hD T (h ⁻¹ᵁ V) h₂ (h.app V s)

/-- An operator linear over the relative base `g ≫ h : W ⟶ Y` is linear over `g : W ⟶ Z` when
`h : Z ⟶ Y` is an open immersion: every section of the structure sheaf of `Z` comes from a section
of the structure sheaf of `Y` over the image open. -/
theorem isBaseLinear_of_comp_isOpenImmersion [IsOpenImmersion h] (D : DiffOp.RawOp M M' U)
    (hD : D.IsBaseLinear (g ≫ h)) : D.IsBaseLinear g := by
  intro T V hV r s
  have h₂ : T.left ≤ (g ≫ h) ⁻¹ᵁ (h ''ᵁ V) := by
    rw [Scheme.Hom.comp_preimage]
    exact hV.trans (g.preimage_mono (h.preimage_image_eq V).ge)
  have key : (g ≫ h).appLE (h ''ᵁ V) T.left h₂ ((h.appIso V).inv r) = g.appLE V T.left hV r := by
    rw [← Scheme.Hom.appLE_comp_appLE g h (h ''ᵁ V) V T.left (h.preimage_image_eq V).ge hV]
    simp only [CommRingCat.comp_apply, (Scheme.Hom.appIso_hom' h V).symm]
    exact congrArg _ (ConcreteCategory.congr_hom (h.appIso V).inv_hom_id r)
  rw [← key]
  exact hD T (h ''ᵁ V) h₂ ((h.appIso V).inv r) s

end DiffOp.RawOp

namespace AlgebraicGeometry

variable {W Z Y : Scheme.{u}} (g : W ⟶ Z) (h : Z ⟶ Y) [IsOpenImmersion h] (k : ℕ)

/-- **The order of a differential operator is insensitive to shrinking the relative base to an
open subscheme.** For `g : W ⟶ Z` and an open immersion `h : Z ⟶ Y`, an operator on the local
sections of modules on `W` is a differential operator of order at most `k` on `W/Y` exactly when it
is one of order at most `k` on `W/Z`. -/
theorem isDiffOpOfOrder_comp_isOpenImmersion_iff {M M' : W.Modules} {U : W.Opens}
    (D : DiffOp.RawOp M M' U) :
    DiffOp.IsDiffOpOfOrder (g ≫ h).relativeStructureSheafMap k D ↔
      DiffOp.IsDiffOpOfOrder g.relativeStructureSheafMap k D := by
  rw [isDiffOpOfOrder_iff_sections, isDiffOpOfOrder_iff_sections]
  exact and_congr_right fun _ ↦ and_congr_left fun _ ↦
    ⟨DiffOp.RawOp.isBaseLinear_of_comp_isOpenImmersion g h D,
      DiffOp.RawOp.isBaseLinear_comp g h D⟩

/-- **The order of a global differential operator is insensitive to shrinking the relative base to
an open subscheme.** For `g : W ⟶ Z` and an open immersion `h : Z ⟶ Y`, a global operator on the
local sections of modules on `W` is a differential operator of order at most `k` on `W/Y` exactly
when it is one of order at most `k` on `W/Z`. -/
theorem isGlobalDiffOpOfOrder_comp_isOpenImmersion_iff {M M' : W.Modules}
    (E : DiffOp.GlobalOp M M') :
    DiffOp.IsGlobalDiffOpOfOrder (g ≫ h).relativeStructureSheafMap k E ↔
      DiffOp.IsGlobalDiffOpOfOrder g.relativeStructureSheafMap k E :=
  forall_congr' fun V ↦ isDiffOpOfOrder_comp_isOpenImmersion_iff g h k (E.restrict V)

end AlgebraicGeometry

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry RingHomClass

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

/-- The algebra structure on the sections over the first factor of a chart given by the chart's
first structure map. -/
@[instance_reducible]
noncomputable def algebraLeft : Algebra Γ(S, c.base) Γ(X, c.left) := c.leftHom.hom.toAlgebra

/-- The algebra structure on the sections over the second factor of a chart given by the chart's
second structure map. -/
@[instance_reducible]
noncomputable def algebraRight : Algebra Γ(S, c.base) Γ(Y, c.right) := c.rightHom.hom.toAlgebra

attribute [local instance] algebraLeft algebraRight

/-- The first structure map of a chart is the algebra map of
`Stacks.FibreProductAffineChart.Chart.algebraLeft`. -/
theorem ofHom_algebraMap_left :
    ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom := rfl

/-- The second structure map of a chart is the algebra map of
`Stacks.FibreProductAffineChart.Chart.algebraRight`. -/
theorem ofHom_algebraMap_right :
    ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom := rfl

section SpecIso

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)

/-- **A chart lies over `Y` through its second factor.** Read as the spectrum of a tensor product,
a chart maps to `Y` by `Spec` of the algebra map `Γ(Y, V) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` followed
by the open immersion `Spec Γ(Y, V) ⟶ Y`. -/
theorem specIso_inv_ι_comp_snd :
    ((c.specIso hl hr).inv ≫ c.ι) ≫ pullback.snd a b =
      Spec.map (ofHom (algebraMap Γ(Y, c.right)
        (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))) ≫ c.fromSpecRight := by
  rw [specIso_inv_ι, affineChart_snd]
  rfl

/-- **Differential operators on an affine chart of a fibre product.** The differential operators
of order at most `k` on `X ×_S Y / Y` between two modules on `X ×_S Y`, defined over the opens
contained in a chart, are the differential operators of order at most `k` relative to
`Γ(Y, V) ⟶ Γ(X, U) ⊗_{Γ(S, W)} Γ(Y, V)` between the two modules of sections on the chart. -/
@[stacks 0G45 "the affine-chart reduction step of the proof: over an affine chart of `X ×_S Y`, \
the differential operators of order at most `k` on `X ×_S Y / Y` are the differential operators \
of order at most `k` relative to `B ⟶ A ⊗_R B` on the chart's sections. Neither the construction \
of `D'` nor its characterisation on pure tensors is included"]
noncomputable def diffOpEquiv (M M' : (pullback a b).Modules)
    [(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι)).IsQuasicoherent] (k : ℕ) :
    letI _modAF : Module (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso
        (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).inv.hom
    letI _modAG : Module (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      Module.compHom _ (Scheme.ΓSpecIso
        (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).inv.hom
    letI _modRF : Module Γ(Y, c.right)
        Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      Module.compHom _ (algebraMap Γ(Y, c.right)
        (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))
    letI _modRG : Module Γ(Y, c.right)
        Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      Module.compHom _ (algebraMap Γ(Y, c.right)
        (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))
    letI _towerF : IsScalarTower Γ(Y, c.right) (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      IsScalarTower.of_compHom _ _ _
    letI _towerG : IsScalarTower Γ(Y, c.right) (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
        Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
      IsScalarTower.of_compHom _ _ _
    {D : DiffOp.RawOp M M' c.ι.opensRange //
        DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k D} ≃
      {D : Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) →ₗ[Γ(Y, c.right)]
          Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) //
        D.IsDifferentialOperatorOfOrderLE
          (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)) k} := by
  haveI : IsOpenImmersion c.fromSpecRight := c.isAffineOpen_right.isOpenImmersion_fromSpec
  refine (diffOpEquivGlobalDiffOpRestrictOfIso (c.specIso hl hr).inv c.ι
      (pullback.snd a b) M M' k).trans
    ((Equiv.subtypeEquivRight ?_).trans
      (AffineDiffOp.globalDiffOpEquiv (R := Γ(Y, c.right))
        (Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι))
        (Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι)) k).1)
  rw [specIso_inv_ι_comp_snd c hl hr]
  exact isGlobalDiffOpOfOrder_comp_isOpenImmersion_iff _ c.fromSpecRight k

/-- The linear map attached to a differential operator on a chart is the operator's action on the
sections over the chart. -/
theorem diffOpEquiv_apply_coe_apply (M M' : (pullback a b).Modules)
    [(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι)).IsQuasicoherent] (k : ℕ)
    (D : {D : DiffOp.RawOp M M' c.ι.opensRange //
      DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k D})
    (x : Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤))
    (hV : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤ ≤ c.ι.opensRange) :
    (diffOpEquiv c hl hr M M' k D).1 x = D.1 (Over.mk (homOfLE hV)) x :=
  ((AffineDiffOp.globalDiffOpEquiv
      (R := Γ(Y, c.right)) (Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι))
      (Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι)) k).2 _ x).trans
    (congrArg (fun z ↦ z x)
      (diffOpEquivGlobalDiffOpRestrictOfIso_coe_apply (c.specIso hl hr).inv c.ι
        (pullback.snd a b) M M' k D ⊤ hV))

/-- **Two differential operators on a chart which agree on the sections over the chart are
equal.** Both are differential operators of order at most `k` on `X ×_S Y / Y` defined over the
opens contained in the chart, and agreement is only required at the chart itself. -/
theorem rawOp_ext_of_chart_sections (M M' : (pullback a b).Modules)
    [(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι)).IsQuasicoherent] (k : ℕ)
    (D E : {D : DiffOp.RawOp M M' c.ι.opensRange //
      DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k D})
    (hV : ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤ ≤ c.ι.opensRange)
    (h : ∀ x, D.1 (Over.mk (homOfLE hV)) x = E.1 (Over.mk (homOfLE hV)) x) : D.1 = E.1 := by
  let _modAF : Module (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
      Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso
      (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).inv.hom
  let _modAG : Module (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right))
      Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
    Module.compHom _ (Scheme.ΓSpecIso
      (.of (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))).inv.hom
  let _modRF : Module Γ(Y, c.right)
      Γ(Scheme.Modules.restrict M ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
    Module.compHom _ (algebraMap Γ(Y, c.right)
      (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))
  let _modRG : Module Γ(Y, c.right)
      Γ(Scheme.Modules.restrict M' ((c.specIso hl hr).inv ≫ c.ι), ⊤) :=
    Module.compHom _ (algebraMap Γ(Y, c.right)
      (Γ(X, c.left) ⊗[Γ(S, c.base)] Γ(Y, c.right)))
  exact congrArg Subtype.val ((diffOpEquiv c hl hr M M' k).injective
    (Subtype.ext (LinearMap.ext fun x ↦ (diffOpEquiv_apply_coe_apply c hl hr M M' k D x hV).trans
      ((h x).trans (diffOpEquiv_apply_coe_apply c hl hr M M' k E x hV).symm))))

end SpecIso

end Chart

end Stacks.FibreProductAffineChart

namespace AlgebraicGeometry

open Stacks.FibreProductAffineChart

/-- The affine charts of a fibre product cover it. -/
theorem iSup_opensRange_chart_ι {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    ⨆ c : Chart a b, (Chart.ι c).opensRange = ⊤ :=
  eq_top_iff.2 fun z _ ↦ Opens.mem_iSup.2 ((exists_chart_mem a b z).imp fun _ hc ↦ hc)

/-- **Gluing differential operators along the affine chart cover of a fibre product.** A family of
differential operators of order at most `k` on `X ×_S Y / Y`, one over the opens of each affine
chart, agreeing on the opens contained in two charts, glues to a unique differential operator of
order at most `k` on `X ×_S Y / Y`. -/
theorem existsUnique_globalDiffOp_of_charts {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (k : ℕ)
    {M M' : (pullback a b).Modules} (D : ∀ c : Chart a b, DiffOp.RawOp M M' (Chart.ι c).opensRange)
    (hD : ∀ c, DiffOp.IsDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k (D c))
    (hagree : DiffOp.AgreeOnCover (fun c : Chart a b ↦ (Chart.ι c).opensRange) D) :
    ∃! E : DiffOp.GlobalOp M M',
      DiffOp.IsGlobalDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k E ∧
        ∀ c, E.restrict (Chart.ι c).opensRange = D c :=
  existsUnique_globalDiffOp_of_cover (pullback.snd a b) k
    (fun c : Chart a b ↦ (Chart.ι c).opensRange) (iSup_opensRange_chart_ι a b) D hD hagree

/-- **A differential operator on a fibre product is determined by its action on the affine
charts.** Two differential operators of order at most `k` on `X ×_S Y / Y`, out of a
quasi-coherent module, which agree on the sections over every affine chart of `X ×_S Y`, are
equal. -/
@[stacks 0G45 "the local-global step of the proof: a differential operator of order at most `k` \
on `X ×_S Y / Y` out of a quasi-coherent module is determined by its action on the sections over \
the affine charts. This is not the uniqueness clause of the tag, which is uniqueness among the \
operators satisfying the characterisation on pure tensors"]
theorem globalDiffOp_ext_of_chart_sections {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (k : ℕ)
    {M M' : (pullback a b).Modules} [M.IsQuasicoherent] (D E : DiffOp.GlobalOp M M')
    (hD : DiffOp.IsGlobalDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k D)
    (hE : DiffOp.IsGlobalDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k E)
    (hagree : ∀ (c : Chart a b) (s : Γ(M, c.ι.opensRange)),
      D (op c.ι.opensRange) s = E (op c.ι.opensRange) s) :
    D = E := by
  refine DiffOp.globalOp_ext_of_cover (fun c : Chart a b ↦ (Chart.ι c).opensRange)
    (fun z ↦ (exists_chart_mem a b z).imp fun _ hc ↦ hc) D E
    (DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k _ (hD ⊤))
    (DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k _ (hE ⊤)) fun c ↦ ?_
  let _instL := c.algebraLeft
  let _instR := c.algebraRight
  have heq : ((c.specIso (Chart.ofHom_algebraMap_left c)
      (Chart.ofHom_algebraMap_right c)).inv ≫ c.ι) ''ᵁ ⊤ = c.ι.opensRange := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso]
  exact Chart.rawOp_ext_of_chart_sections c (Chart.ofHom_algebraMap_left c)
    (Chart.ofHom_algebraMap_right c) M M' k ⟨D.restrict (Chart.ι c).opensRange, hD _⟩
    ⟨E.restrict (Chart.ι c).opensRange, hE _⟩ heq.le (by rintro s; exact (heq ▸ hagree c) s)

end AlgebraicGeometry

end
