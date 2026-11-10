module

public import StacksFrontier.AlgebraicGeometry.FibreProductAffineChart.ChartBoxSectionGeneration
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductFunctor

/-!
# The affine description of the box-product bifunctor

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes and let `c` be an affine chart of the
fibre product, with `R = Γ(S, W)`, `A = Γ(X, U)`, `B = Γ(Y, V)`. On the chart the sections of a
box product `F ⊠ G` are the tensor product `M ⊗_R N` of the sections of `F` on `Spec A` and of
`G` on `Spec B`, by `Stacks.FibreProductAffineChart.Chart.boxSectionsEquiv`. This file computes
the box product `D ⊠ E` of two finite-order differential operators through that identification:
it is `D ⊗ E`, the operator carrying `s ⊗ t` to `D s ⊗ E t`.

Taking the chart whose three opens are everything, this is the affine description of the remark:
for `X = Spec A`, `Y = Spec B` and `S = Spec R`, the box-product bifunctor is
`(M, N) ↦ M ⊗_R N` on objects and `(D, D') ↦ D ⊗ D'` on morphisms.

## Main definitions

* `Stacks.FibreProductAffineChart.Chart.rightDiffOpEquiv`: the differential operators of order at
  most `k` on `Y/S` over the opens contained in the second factor of a chart, identified with the
  differential operators of order at most `k` relative to `Γ(S, W) ⟶ Γ(Y, V)` between the two
  modules of sections on `Spec Γ(Y, V)`. This is the mirror image of
  `Stacks.FibreProductAffineChart.Chart.leftDiffOpEquiv`.
* `Stacks.FibreProductAffineChart.affineTopChart`: the chart of a fibre product of affine schemes
  over an affine base whose three opens are everything — the chart at which the statements of
  this file are the remark's affine description, by
  `Stacks.FibreProductAffineChart.opensRange_ι_affineTopChart`.

## Main results

* `Stacks.FibreProductAffineChart.Chart.rightOrder_iff` and
  `Stacks.FibreProductAffineChart.Chart.rightDiffOpEquiv_apply`: the mirror images of
  `Stacks.FibreProductAffineChart.Chart.leftOrder_iff` and
  `Stacks.FibreProductAffineChart.Chart.leftDiffOpEquiv_apply`.
* `Stacks.FibreProductAffineChart.Chart.rightDiffOpEquiv_apply_modulesPullbackUnitTop`: the
  operator on `Γ(Spec Γ(Y, V), G)` attached to a differential operator on `Y/S` carries the
  global section of the inverse image coming from a section `t` of `G` over `V'` to the one
  coming from `E t`.
* `Stacks.FibreProductAffineChart.Chart.boxHom_boxSectionOfTensor`: **the affine description of
  the box product on morphisms.** The operator `D ⊠ E`, read on the sections of `F ⊠ G` over a
  chart through the identification of those sections with `M ⊗_R N`, is the tensor product
  `D ⊗ E` of the two operators on `M` and on `N`.
* `Stacks.FibreProductAffineChart.Chart.boxHom_boxSectionOfTensor_tmul`: the same on a pure
  tensor, which is where `D ⊗ E` is visible: `D ⊠ E` carries the section attached to `s ⊗ t` to
  the one attached to `D s ⊗ E t`.
* `Stacks.FibreProductAffineChart.Chart.boxHom_boxSectionOfTensor_algebraMap`: the same with the
  two algebra structures taken to be the ones the chart's own structure maps define, so that no
  hypothesis is left beyond an order bound for each of the two operators.

## Implementation notes

The identification of the sections of `F ⊠ G` over the chart with `M ⊗_R N` is used in the
direction `Stacks.FibreProductAffineChart.Chart.boxSectionOfTensor`, which is a map into the
sections over the *image* of the chart rather than over its spectrum spelling; this is the form
in which the pure tensors are already known to be the sections attached to a pair of local
sections (`Chart.boxSectionOfTensor_tmul`) and to generate (`Chart.boxSectionOfTensor_add`,
`Chart.boxSectionOfTensor_surjective`), and it is the form in which `D ⊠ E` can be applied
without first transporting it across the chart.

`Stacks.FibreProductAffineChart.Chart.leftDiffOpEquiv` reads an operator on `X/S` on the sections
over the chart's first factor. Its mirror image on the second factor is not in the tree — the
second factor carries only the module and tower instances, not the operator comparison — so it is
built here; nothing of it is new beyond exchanging the roles of the two factors.

The order bounds `k` and `l` are taken as arguments together with the two order hypotheses rather
than extracted from the two morphisms: the underlying linear map of `Chart.leftDiffOpEquiv` does
not depend on the bound, so the statement is the same for every choice, and quantifying over the
bound avoids `Exists.choose` in the statement.

A pure tensor is reduced to one of sections coming from the chart's two factors by
`Chart.surjective_modulesPullbackUnitTop_left` and `..._right`, and that reduction is taken as a
term, `Exists.elim ... fun s hs ↦ ...`: destructuring the two surjectivity witnesses with `obtain`
exhausts the heartbeat budget in these goals, in each of its forms — the `rfl` pattern, `subst`,
and `rw [← hs]` — while the same step as a term costs nothing. The equation is then moved across
the statement by `congrArg`, in `Chart.boxHom_boxSectionOfTensor_tmul_of_eq`.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct TopologicalSpace
open CommRingCat
open Stacks.Tag01VSPullbackTensor

universe u

attribute [local instance] Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback

namespace Stacks.FibreProductAffineChart

open _root_.AlgebraicGeometry RingHomClass

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Chart

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S} (c : Chart a b)

attribute [local instance] leftModuleAlg leftModuleBase leftTower
attribute [local instance] rightModuleAlg rightModuleBase rightTower

/-! ### Differential operators on the second factor of a chart -/

section Right

variable [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
  (G G' : Y.Modules) [G.IsQuasicoherent] (k : ℕ)

omit [G.IsQuasicoherent] in
include hr in
/-- The order of an operator on the inverse images along the second factor of a chart may be read
relative to `Γ(S, W) ⟶ Γ(Y, V)` instead of relative to `S`. -/
theorem rightOrder_iff
    (E : DiffOp.GlobalOp ((Scheme.Modules.pullback c.fromSpecRight).obj G)
      ((Scheme.Modules.pullback c.fromSpecRight).obj G')) :
    DiffOp.IsGlobalDiffOpOfOrder (c.fromSpecRight ≫ b).relativeStructureSheafMap k E ↔
      DiffOp.IsGlobalDiffOpOfOrder
        (Spec.map (ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)))).relativeStructureSheafMap k E :=
  have : IsOpenImmersion c.fromSpecBase := c.isAffineOpen_base.isOpenImmersion_fromSpec
  (Iff.of_eq (congrArg (fun m ↦ DiffOp.IsGlobalDiffOpOfOrder
      (Scheme.Hom.relativeStructureSheafMap m) k E) (c.fromSpecRight_comp_eq hr))).trans
    (isGlobalDiffOpOfOrder_comp_isOpenImmersion_iff
      (Spec.map (ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)))) c.fromSpecBase k E)

include hr in
/-- **Differential operators on the second factor of an affine chart.** The differential operators
of order at most `k` on `Y/S` between two modules on `Y`, defined over the opens contained in the
second factor of a chart, are the differential operators of order at most `k` relative to
`Γ(S, W) ⟶ Γ(Y, V)` between the two modules of sections on `Spec Γ(Y, V)`. -/
noncomputable def rightDiffOpEquiv :
    {E : DiffOp.RawOp G G' c.fromSpecRight.opensRange //
        DiffOp.IsDiffOpOfOrder b.relativeStructureSheafMap k E} ≃
      {E : Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤) →ₗ[Γ(S, c.base)]
          Γ((Scheme.Modules.pullback c.fromSpecRight).obj G', ⊤) //
        E.IsDifferentialOperatorOfOrderLE Γ(Y, c.right) k} :=
  (diffOpEquivGlobalDiffOpPullback c.fromSpecRight b G G' k).trans
    ((Equiv.subtypeEquivRight (c.rightOrder_iff hr G G' k)).trans
      (AffineDiffOp.globalDiffOpEquiv (R := Γ(S, c.base))
        ((Scheme.Modules.pullback c.fromSpecRight).obj G)
        ((Scheme.Modules.pullback c.fromSpecRight).obj G') k).1)

include hr in
/-- The operator on the sections over the second factor of a chart attached to a differential
operator on `Y/S` is the operator's action on those sections, read through the comparison of the
restriction with the inverse image. -/
theorem rightDiffOpEquiv_apply
    (E : {E : DiffOp.RawOp G G' c.fromSpecRight.opensRange //
        DiffOp.IsDiffOpOfOrder b.relativeStructureSheafMap k E})
    (x : Γ((Scheme.Modules.pullback c.fromSpecRight).obj G, ⊤)) :
    (rightDiffOpEquiv c hr G G' k E).1 x =
      Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecRight).app G').hom ⊤
        (E.1 (AlgebraicGeometry.imageOver c.fromSpecRight ⊤)
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecRight).app G).inv ⊤ x)) :=
  ((AffineDiffOp.globalDiffOpEquiv (R := Γ(S, c.base))
      ((Scheme.Modules.pullback c.fromSpecRight).obj G)
      ((Scheme.Modules.pullback c.fromSpecRight).obj G') k).2
    (Equiv.subtypeEquivRight (c.rightOrder_iff hr G G' k)
      (diffOpEquivGlobalDiffOpPullback c.fromSpecRight b G G' k E)) x).trans
    (diffOpEquivGlobalDiffOpPullback_coe_apply c.fromSpecRight b G G' k E ⊤ x)

include hr in
/-- **A differential operator on the second factor of a chart, on the section coming from an open
containing that factor.** For a differential operator `E` of order at most `k` on `Y/S` and a
section `t` of `G` over an open `V'` of `Y` whose preimage in the chart's second factor is
everything, the operator on `Γ(Spec Γ(Y, V), G)` attached to `E` carries the global section of
the inverse image coming from `t` to the one coming from `E t`. -/
theorem rightDiffOpEquiv_apply_modulesPullbackUnitTop (E : DiffOp.GlobalOp G G')
    (hE : DiffOp.IsGlobalDiffOpOfOrder b.relativeStructureSheafMap k E)
    (V' : Y.Opens) (hV : c.fromSpecRight ⁻¹ᵁ V' = ⊤) (t : Γ(G, V')) :
    (c.rightDiffOpEquiv hr G G' k
          ⟨E.restrict c.fromSpecRight.opensRange, hE c.fromSpecRight.opensRange⟩).1
        (modulesPullbackUnitTop c.fromSpecRight G V' hV t)
      = modulesPullbackUnitTop c.fromSpecRight G' V' hV (E (op V') t) := by
  have hle : c.fromSpecRight ''ᵁ (⊤ : (Spec Γ(Y, c.right)).Opens) ≤ V' := by
    rw [← hV]
    exact c.fromSpecRight.image_preimage_le V'
  have hsrc := modulesPullbackUnitTop_restrictFunctorIsoPullback c.fromSpecRight G V' hV t hle
  have htgt := modulesPullbackUnitTop_restrictFunctorIsoPullback c.fromSpecRight G' V' hV
    (E (op V') t) hle
  have hinv : Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecRight).app G).inv ⊤
        (modulesPullbackUnitTop c.fromSpecRight G V' hV t)
      = G.presheaf.map (homOfLE hle).op t := by
    rw [modulesPullbackUnitTop, hsrc]
    exact congrArg
      (fun φ : Scheme.Modules.restrict G c.fromSpecRight ⟶
          Scheme.Modules.restrict G c.fromSpecRight ↦
        Scheme.Modules.Hom.app φ ⊤ (G.presheaf.map (homOfLE hle).op t))
      ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecRight).app G).hom_inv_id
  have hnat := DiffOp.RawOp.isNatural_of_isDiffOpOfOrder b.relativeStructureSheafMap k _ (hE ⊤)
    (Over.mk (homOfLE (le_top : c.fromSpecRight ''ᵁ (⊤ : (Spec Γ(Y, c.right)).Opens) ≤ ⊤)))
    (Over.mk (homOfLE (le_top : V' ≤ ⊤))) (Over.homMk (homOfLE hle) (Subsingleton.elim _ _)) t
  refine (c.rightDiffOpEquiv_apply hr G G' k _ _).trans (Eq.trans ?_ htgt.symm)
  exact congrArg
    (fun z ↦ Scheme.Modules.Hom.app
      ((Scheme.Modules.restrictFunctorIsoPullback c.fromSpecRight).app G').hom ⊤ z)
    ((congrArg (fun z ↦ E (op (c.fromSpecRight ''ᵁ (⊤ : (Spec Γ(Y, c.right)).Opens))) z)
      hinv).trans hnat)

end Right

/-! ### The box product of two operators on the sections over a chart -/

section Box

attribute [local instance] Stacks.TensorProductPushout.rightModule
  Stacks.TensorProductPushout.rightModule_isScalarTower
  Stacks.TensorProductPushout.smulCommClass_right
  Stacks.TensorProductPushout.pushoutModule
  Stacks.TensorProductPushout.pushoutModule_isScalarTower
attribute [local instance] boxModuleAlg boxModuleBase boxTower

variable [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)]
  (hl : ofHom (algebraMap Γ(S, c.base) Γ(X, c.left)) = c.leftHom)
  (hr : ofHom (algebraMap Γ(S, c.base) Γ(Y, c.right)) = c.rightHom)
  {F F' : AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory a}
  {G G' : AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory b}
  (D : F ⟶ F') (E : G ⟶ G') (k l : ℕ)
  (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D.1)
  (hE : DiffOp.IsGlobalDiffOpOfOrder b.relativeStructureSheafMap l E.1)

/-- The chart lies inside the preimage of its first factor under the first projection. -/
theorem image_specIso_inv_ι_le_preimage_fst :
    ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.fst a b ⁻¹ᵁ c.left :=
  (c.image_specIso_inv_ι_top hl hr).le.trans
    (c.opensRange_ι_le_preimage_fst c.left c.preimage_fromSpecLeft_left)

/-- The chart lies inside the preimage of its second factor under the second projection. -/
theorem image_specIso_inv_ι_le_preimage_snd :
    ((c.specIso hl hr).inv ≫ c.ι) ''ᵁ (⊤ : (Spec (.of (Γ(X, c.left) ⊗[Γ(S, c.base)]
        Γ(Y, c.right)))).Opens) ≤ pullback.snd a b ⁻¹ᵁ c.right :=
  (c.image_specIso_inv_ι_top hl hr).le.trans
    (c.opensRange_ι_le_preimage_snd c.right c.preimage_fromSpecRight_right)

include hD hE in
/-- The target side of the affine description on a pure tensor: the section attached to the pure
tensor `D s ⊗ E t` of the operators' values is the section of `F' ⊠ G'` attached to `D s` and
`E t`. -/
theorem boxSectionOfTensor_tmul_diffOp (s : Γ(F.module, c.left))
    (t : Γ(G.module, c.right)) :
    c.boxSectionOfTensor hl hr F'.module G'.module
        ((c.leftDiffOpEquiv hl F.module F'.module k
              ⟨D.1.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1
            (modulesPullbackUnitTop c.fromSpecLeft F.module c.left
              c.preimage_fromSpecLeft_left s)
          ⊗ₜ[Γ(S, c.base)]
          (c.rightDiffOpEquiv hr G.module G'.module l
              ⟨E.1.restrict c.fromSpecRight.opensRange, hE c.fromSpecRight.opensRange⟩).1
            (modulesPullbackUnitTop c.fromSpecRight G.module c.right
              c.preimage_fromSpecRight_right t)) =
      externalTensorSection a b F'.module G'.module (D.1 (op c.left) s) (E.1 (op c.right) t)
        (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) (c.image_specIso_inv_ι_le_preimage_fst hl hr)
        (c.image_specIso_inv_ι_le_preimage_snd hl hr) :=
  (congrArg (c.boxSectionOfTensor hl hr F'.module G'.module)
    (congrArg₂ (fun u v ↦ u ⊗ₜ[Γ(S, c.base)] v)
      (c.leftDiffOpEquiv_apply_modulesPullbackUnitTop hl F.module F'.module k D.1 hD
        c.left c.preimage_fromSpecLeft_left s)
      (c.rightDiffOpEquiv_apply_modulesPullbackUnitTop hr G.module G'.module l E.1 hE
        c.right c.preimage_fromSpecRight_right t))).trans
    (c.boxSectionOfTensor_tmul hl hr F'.module G'.module
      (c.image_specIso_inv_ι_le_preimage_fst hl hr)
      (c.image_specIso_inv_ι_le_preimage_snd hl hr) (D.1 (op c.left) s) (E.1 (op c.right) t))

/-- The source side of the affine description on a pure tensor: `D ⊠ E` carries the section of
`F ⊠ G` attached to the pure tensor of the sections coming from `s` and `t` to the section of
`F' ⊠ G'` attached to `D s` and `E t`. -/
theorem boxHom_boxSectionOfTensor_unit (s : Γ(F.module, c.left)) (t : Γ(G.module, c.right)) :
    (AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom D E).1
        (op (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤))
        (c.boxSectionOfTensor hl hr F.module G.module
          (modulesPullbackUnitTop c.fromSpecLeft F.module c.left c.preimage_fromSpecLeft_left s
            ⊗ₜ[Γ(S, c.base)]
            modulesPullbackUnitTop c.fromSpecRight G.module c.right
              c.preimage_fromSpecRight_right t)) =
      externalTensorSection a b F'.module G'.module (D.1 (op c.left) s) (E.1 (op c.right) t)
        (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤) (c.image_specIso_inv_ι_le_preimage_fst hl hr)
        (c.image_specIso_inv_ι_le_preimage_snd hl hr) :=
  (congrArg
    ((AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom D E).1
      (op (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤)))
    (c.boxSectionOfTensor_tmul hl hr F.module G.module
      (c.image_specIso_inv_ι_le_preimage_fst hl hr)
      (c.image_specIso_inv_ι_le_preimage_snd hl hr) s t)).trans
    (AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom_externalTensorSection
      D E s t (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤)
      (c.image_specIso_inv_ι_le_preimage_fst hl hr)
      (c.image_specIso_inv_ι_le_preimage_snd hl hr))

include hD hE in
/-- **The affine description of the box product, on the sections coming from a pair of sections
over the chart's two factors.** The operator `D ⊠ E`, read on the sections of `F ⊠ G` over the
image of a chart, carries the section attached to the pure tensor of the sections coming from `s`
and from `t` to the section attached to the pure tensor of the values of the two transported
operators on them. -/
theorem boxHom_boxSectionOfTensor_unit_tmul (s : Γ(F.module, c.left))
    (t : Γ(G.module, c.right)) :
    (AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom D E).1
        (op (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤))
        (c.boxSectionOfTensor hl hr F.module G.module
          (modulesPullbackUnitTop c.fromSpecLeft F.module c.left c.preimage_fromSpecLeft_left s
            ⊗ₜ[Γ(S, c.base)]
            modulesPullbackUnitTop c.fromSpecRight G.module c.right
              c.preimage_fromSpecRight_right t)) =
      c.boxSectionOfTensor hl hr F'.module G'.module
        ((c.leftDiffOpEquiv hl F.module F'.module k
              ⟨D.1.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1
            (modulesPullbackUnitTop c.fromSpecLeft F.module c.left
              c.preimage_fromSpecLeft_left s)
          ⊗ₜ[Γ(S, c.base)]
          (c.rightDiffOpEquiv hr G.module G'.module l
              ⟨E.1.restrict c.fromSpecRight.opensRange, hE c.fromSpecRight.opensRange⟩).1
            (modulesPullbackUnitTop c.fromSpecRight G.module c.right
              c.preimage_fromSpecRight_right t)) :=
  (c.boxHom_boxSectionOfTensor_unit hl hr D E s t).trans
    (c.boxSectionOfTensor_tmul_diffOp hl hr D E k l hD hE s t).symm

include hD hE in
/-- **The affine description of the box product on a pure tensor, for sections presented as
coming from the chart's two factors.** -/
theorem boxHom_boxSectionOfTensor_tmul_of_eq
    (ms : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F.module, ⊤))
    (mt : Γ((Scheme.Modules.pullback c.fromSpecRight).obj G.module, ⊤))
    (s : Γ(F.module, c.left)) (t : Γ(G.module, c.right))
    (hs : modulesPullbackUnitTop c.fromSpecLeft F.module c.left c.preimage_fromSpecLeft_left s
      = ms)
    (ht : modulesPullbackUnitTop c.fromSpecRight G.module c.right
      c.preimage_fromSpecRight_right t = mt) :
    (AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom D E).1
        (op (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤))
        (c.boxSectionOfTensor hl hr F.module G.module (ms ⊗ₜ[Γ(S, c.base)] mt)) =
      c.boxSectionOfTensor hl hr F'.module G'.module
        ((c.leftDiffOpEquiv hl F.module F'.module k
              ⟨D.1.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1 ms
          ⊗ₜ[Γ(S, c.base)]
          (c.rightDiffOpEquiv hr G.module G'.module l
              ⟨E.1.restrict c.fromSpecRight.opensRange, hE c.fromSpecRight.opensRange⟩).1 mt) :=
  (congrArg
    (fun z ↦ (AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom D E).1
      (op (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤))
      (c.boxSectionOfTensor hl hr F.module G.module z))
    (congrArg₂ (fun u v ↦ u ⊗ₜ[Γ(S, c.base)] v) hs.symm ht.symm)).trans
    ((c.boxHom_boxSectionOfTensor_unit_tmul hl hr D E k l hD hE s t).trans
      (congrArg (c.boxSectionOfTensor hl hr F'.module G'.module)
        (congrArg₂ (fun u v ↦ u ⊗ₜ[Γ(S, c.base)] v)
          (congrArg (c.leftDiffOpEquiv hl F.module F'.module k
            ⟨D.1.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1 hs)
          (congrArg (c.rightDiffOpEquiv hr G.module G'.module l
            ⟨E.1.restrict c.fromSpecRight.opensRange, hE c.fromSpecRight.opensRange⟩).1 ht))))

include hD hE in
/-- **The affine description of the box product on a pure tensor.** The operator `D ⊠ E`, read on
the sections of `F ⊠ G` over the image of a chart, carries the section attached to a pure tensor
`ms ⊗ mt` of `Γ(Spec A, F) ⊗_R Γ(Spec B, G)` to the section attached to the pure tensor of the
values of the two transported operators on `ms` and on `mt`. -/
theorem boxHom_boxSectionOfTensor_tmul
    (ms : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F.module, ⊤))
    (mt : Γ((Scheme.Modules.pullback c.fromSpecRight).obj G.module, ⊤)) :
    (AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom D E).1
        (op (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤))
        (c.boxSectionOfTensor hl hr F.module G.module (ms ⊗ₜ[Γ(S, c.base)] mt)) =
      c.boxSectionOfTensor hl hr F'.module G'.module
        ((c.leftDiffOpEquiv hl F.module F'.module k
              ⟨D.1.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1 ms
          ⊗ₜ[Γ(S, c.base)]
          (c.rightDiffOpEquiv hr G.module G'.module l
              ⟨E.1.restrict c.fromSpecRight.opensRange, hE c.fromSpecRight.opensRange⟩).1 mt) :=
  Exists.elim (c.surjective_modulesPullbackUnitTop_left F.module ms) fun s hs ↦
    Exists.elim (c.surjective_modulesPullbackUnitTop_right G.module mt) fun t ht ↦
      c.boxHom_boxSectionOfTensor_tmul_of_eq hl hr D E k l hD hE ms mt s t hs ht

include hD hE in
/-- **The affine description of the box product on morphisms.** Read on the sections of `F ⊠ G`
over the image of a chart, through the identification of those sections with
`Γ(Spec A, F) ⊗_R Γ(Spec B, G)`, the operator `D ⊠ E` is the tensor product `D ⊗ E` of the
operator attached to `D` on `Γ(Spec A, F)` and the operator attached to `E` on
`Γ(Spec B, G)`. -/
@[stacks 0G46 "the MORPHISM half of the affine description of the remark: on an affine chart of \
`X ×_S Y`, and so in particular for `X = Spec A`, `Y = Spec B`, `S = Spec R` and the chart whose \
three opens are everything, the operator `D ⊠ E` read on the sections of `F ⊠ G` through the \
identification of those sections with `M ⊗_R N` is `D ⊗ E`. Carries a chosen order bound for \
each of the two operators (`hD`, `hE`), which exists for every morphism of the category. The \
OBJECT half `(M, N) ↦ M ⊗_R N` is `Chart.boxSectionsEquiv`"]
theorem boxHom_boxSectionOfTensor
    (z : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F.module, ⊤) ⊗[Γ(S, c.base)]
      Γ((Scheme.Modules.pullback c.fromSpecRight).obj G.module, ⊤)) :
    (AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom D E).1
        (op (((c.specIso hl hr).inv ≫ c.ι) ''ᵁ ⊤))
        (c.boxSectionOfTensor hl hr F.module G.module z) =
      c.boxSectionOfTensor hl hr F'.module G'.module
        (TensorProduct.map
          (c.leftDiffOpEquiv hl F.module F'.module k
            ⟨D.1.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1
          (c.rightDiffOpEquiv hr G.module G'.module l
            ⟨E.1.restrict c.fromSpecRight.opensRange, hE c.fromSpecRight.opensRange⟩).1 z) := by
  induction z using TensorProduct.inductionOn with
  | tmul ms mt => exact c.boxHom_boxSectionOfTensor_tmul hl hr D E k l hD hE ms mt
  | add z₁ z₂ ih₁ ih₂ =>
      simp only [map_add, c.boxSectionOfTensor_add]
      exact (map_add _ _ _).trans (congrArg₂ (· + ·) ih₁ ih₂)

/-! ### The affine description at a chart's own algebra structure -/

section Canonical

variable {F F' : AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory a}
  {G G' : AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory b}
  (D : F ⟶ F') (E : G ⟶ G') (k l : ℕ)
  (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D.1)
  (hE : DiffOp.IsGlobalDiffOpOfOrder b.relativeStructureSheafMap l E.1)

omit [Algebra Γ(S, c.base) Γ(X, c.left)] [Algebra Γ(S, c.base) Γ(Y, c.right)] in
/-- **The affine description of the box product on morphisms, at the chart's own algebra
structure.** This is `Chart.boxHom_boxSectionOfTensor` with the two algebra structures taken to be
the ones the chart's structure maps define, so that it carries no hypothesis beyond an order bound
for each of the two operators: every chart satisfies the hypotheses of that statement. -/
theorem boxHom_boxSectionOfTensor_algebraMap :
    letI := c.algebraLeft
    letI := c.algebraRight
    ∀ z : Γ((Scheme.Modules.pullback c.fromSpecLeft).obj F.module, ⊤) ⊗[Γ(S, c.base)]
      Γ((Scheme.Modules.pullback c.fromSpecRight).obj G.module, ⊤),
      (AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHom D E).1
          (op (((c.specIso (ofHom_algebraMap_left c) (ofHom_algebraMap_right c)).inv ≫ c.ι)
            ''ᵁ ⊤))
          (c.boxSectionOfTensor (ofHom_algebraMap_left c) (ofHom_algebraMap_right c)
            F.module G.module z) =
        c.boxSectionOfTensor (ofHom_algebraMap_left c) (ofHom_algebraMap_right c)
          F'.module G'.module
          (TensorProduct.map
            (c.leftDiffOpEquiv (ofHom_algebraMap_left c) F.module F'.module k
              ⟨D.1.restrict c.fromSpecLeft.opensRange, hD c.fromSpecLeft.opensRange⟩).1
            (c.rightDiffOpEquiv (ofHom_algebraMap_right c) G.module G'.module l
              ⟨E.1.restrict c.fromSpecRight.opensRange, hE c.fromSpecRight.opensRange⟩).1 z) :=
  let := c.algebraLeft
  let := c.algebraRight
  c.boxHom_boxSectionOfTensor (ofHom_algebraMap_left c) (ofHom_algebraMap_right c) D E k l hD hE

end Canonical

end Box

end Chart

/-! ### The chart of a fibre product of affine schemes -/

/-- **The chart of a fibre product of affine schemes over an affine base whose three opens are
everything.** For `X = Spec A`, `Y = Spec B` and `S = Spec R` this is the chart at which the
statements above are the remark's affine description: `A = Γ(X, ⊤)`, `B = Γ(Y, ⊤)` and
`R = Γ(S, ⊤)`, and the chart covers the whole fibre product. -/
def affineTopChart {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S] (a : X ⟶ S)
    (b : Y ⟶ S) : Chart a b where
  base := ⊤
  left := ⊤
  right := ⊤
  isAffineOpen_base := isAffineOpen_top S
  isAffineOpen_left := isAffineOpen_top X
  isAffineOpen_right := isAffineOpen_top Y
  le_left := (Scheme.Hom.preimage_top a).ge
  le_right := (Scheme.Hom.preimage_top b).ge

/-- The chart of a fibre product of affine schemes whose three opens are everything covers the
whole fibre product. -/
theorem opensRange_ι_affineTopChart {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S]
    (a : X ⟶ S) (b : Y ⟶ S) : (affineTopChart a b).ι.opensRange = ⊤ :=
  ((affineTopChart a b).opensRange_ι).trans
    (le_antisymm le_top (le_inf (Scheme.Hom.preimage_top (pullback.fst a b)).ge
      (Scheme.Hom.preimage_top (pullback.snd a b)).ge))



end Stacks.FibreProductAffineChart

end
