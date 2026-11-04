module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ChartBoxOperatorGluing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.ExternalTensorProductQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.RelativeOrderComposition

/-!
# The box product of a differential operator with the identity

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `F`, `F'` be quasi-coherent
`𝒪_X`-modules, let `G` be a quasi-coherent `𝒪_Y`-module and let `D : F ⟶ F'` be a differential
operator of order at most `k` on `X/S`. The operator `D ⊠ 1` from `F ⊠ G` to `F' ⊠ G` is the
chart-indexed family of affine base changes of `D`, glued along the affine chart cover of
`X ×_S Y`. It is a differential operator of order at most `k` on `X ×_S Y / Y`, hence also on
`X ×_S Y / S`, and it does not depend on the order bound `k` used to build it.

## Main definitions

* `AlgebraicGeometry.boxOpLeft`: the operator `D ⊠ 1`, as a global operator on local sections.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHomLeft`: `D ⊠ 1` as a morphism
  of the category of finite-order differential operators on `X ×_S Y / S`.

## Main results

* `AlgebraicGeometry.isGlobalDiffOpOfOrder_boxOpLeft`: `D ⊠ 1` is a differential operator of
  order at most `k` on `X ×_S Y / Y`.
* `AlgebraicGeometry.boxOpLeft_externalTensorSection`: `D ⊠ 1` carries the section of `F ⊠ G`
  attached to a pair of local sections `s` of `F` and `t` of `G` to the section of `F' ⊠ G`
  attached to `D s` and `t`.
* `AlgebraicGeometry.boxOpLeft_eq_of_order`: `D ⊠ 1` does not depend on the order bound used to
  construct it.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxHomLeft_externalTensorSection`:
  the characterisation of `D ⊠ 1` read on the morphism of the category.

## References

* [Stacks Project, Tag 0G44](https://stacks.math.columbia.edu/tag/0G44)
* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.FibreProductAffineChart
open Stacks.Tag01VSPullbackTensor

universe u

namespace AlgebraicGeometry

/-- The order of a differential operator on `X/Y` may be enlarged. -/
theorem isGlobalDiffOpOfOrder_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' : X.Modules}
    {k l : ℕ} (hkl : k ≤ l) (D : DiffOp.GlobalOp M M')
    (hD : DiffOp.IsGlobalDiffOpOfOrder f.relativeStructureSheafMap k D) :
    DiffOp.IsGlobalDiffOpOfOrder f.relativeStructureSheafMap l D := by
  induction l, hkl using Nat.le_induction with
  | base => exact hD
  | succ l _ ih =>
      exact fun U ↦ DiffOp.RawOp.isDiffOpOfOrder_succ_of_isDiffOpOfOrder
        f.relativeStructureSheafMap l (D.restrict U) (ih U)

section

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (F F' : X.Modules) (G : Y.Modules)
  [F.IsQuasicoherent] [F'.IsQuasicoherent] [G.IsQuasicoherent] (k : ℕ)
  (D : DiffOp.GlobalOp F F')
  (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D)

/-- **The box product `D ⊠ 1` of a differential operator with the identity.** For a differential
operator `D : F ⟶ F'` of order at most `k` on `X/S` and a quasi-coherent `𝒪_Y`-module `G`, the
affine base changes of `D` on the charts of `X ×_S Y`, glued along the chart cover. -/
def boxOpLeft :
    DiffOp.GlobalOp (externalTensorProduct a b F G) (externalTensorProduct a b F' G) :=
  DiffOp.coverGlue (fun c : Chart a b ↦ c.ι.opensRange)
    (fun p ↦ (exists_chart_mem a b p).imp fun _ hc ↦ hc)
    (fun c ↦ (c.boxOp F F' G k D hD).1)
    (fun c ↦ DiffOp.RawOp.isNatural_of_isDiffOpOfOrder _ k _ (c.boxOp F F' G k D hD).2)
    (Chart.agreeOnCover_boxOp F F' G k D hD)

/-- `D ⊠ 1` restricts on the opens of an affine chart to the affine base change of `D` there. -/
theorem boxOpLeft_restrict (c : Chart a b) :
    (boxOpLeft a b F F' G k D hD).restrict c.ι.opensRange = (c.boxOp F F' G k D hD).1 :=
  DiffOp.coverGlue_restrict _ _ _ _ _ c

/-- `D ⊠ 1` is compatible with restriction of sections. -/
theorem isNatural_boxOpLeft : ((boxOpLeft a b F F' G k D hD).restrict ⊤).IsNatural :=
  DiffOp.coverGlue_isNatural _ _ _ _ _ ⊤

/-- **`D ⊠ 1` is a differential operator of order at most `k` on `X ×_S Y / Y`.** -/
theorem isGlobalDiffOpOfOrder_boxOpLeft :
    DiffOp.IsGlobalDiffOpOfOrder (pullback.snd a b).relativeStructureSheafMap k
      (boxOpLeft a b F F' G k D hD) :=
  isGlobalDiffOpOfOrder_of_cover (pullback.snd a b) k
    (fun c : Chart a b ↦ c.ι.opensRange) (iSup_opensRange_chart_ι a b) _
    (isNatural_boxOpLeft a b F F' G k D hD) fun c ↦
      (boxOpLeft_restrict a b F F' G k D hD c).symm ▸ (c.boxOp F F' G k D hD).2

/-- **`D ⊠ 1` is a differential operator of order at most `k` on `X ×_S Y / S`.** -/
theorem isGlobalDiffOpOfOrder_boxOpLeft_base :
    DiffOp.IsGlobalDiffOpOfOrder (pullback.fst a b ≫ a).relativeStructureSheafMap k
      (boxOpLeft a b F F' G k D hD) :=
  isGlobalDiffOpOfOrder_pullbackSnd a b k _ (isGlobalDiffOpOfOrder_boxOpLeft a b F F' G k D hD)

/-- **`D ⊠ 1` on the section attached to a pair of local sections.** It carries the section of
`F ⊠ G` attached to a section `s` of `F` over `U'` and a section `t` of `G` over `V'`, over any
open `W` of `X ×_S Y` inside `pr₁⁻¹U' ⊓ pr₂⁻¹V'`, to the section of `F' ⊠ G` attached to `D s`
and `t`. -/
theorem boxOpLeft_externalTensorSection {U' : X.Opens} {V' : Y.Opens} (s : Γ(F, U'))
    (t : Γ(G, V')) (W : (pullback a b).Opens) (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U')
    (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    boxOpLeft a b F F' G k D hD (op W) (externalTensorSection a b F G s t W hW₁ hW₂) =
      externalTensorSection a b F' G (D (op U') s) t W hW₁ hW₂ :=
  Chart.apply_externalTensorSection_of_restrict F F' G k D hD _
    (isNatural_boxOpLeft a b F F' G k D hD) (boxOpLeft_restrict a b F F' G k D hD) s t W hW₁ hW₂

end

section

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) (F F' : X.Modules) (G : Y.Modules)
  [F.IsQuasicoherent] [F'.IsQuasicoherent] [G.IsQuasicoherent]
  (D : DiffOp.GlobalOp F F')

/-- **`D ⊠ 1` does not depend on the order bound used to build it.** Two order bounds for the
same differential operator `D` give the same box product with the identity. -/
theorem boxOpLeft_eq_of_order {k l : ℕ}
    (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D)
    (hD' : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap l D) :
    boxOpLeft a b F F' G k D hD = boxOpLeft a b F F' G l D hD' := by
  refine globalDiffOp_ext_of_chart_sections a b (max k l) _ _
    (isGlobalDiffOpOfOrder_of_le (pullback.snd a b) (Nat.le_max_left k l) _
      (isGlobalDiffOpOfOrder_boxOpLeft a b F F' G k D hD))
    (isGlobalDiffOpOfOrder_of_le (pullback.snd a b) (Nat.le_max_right k l) _
      (isGlobalDiffOpOfOrder_boxOpLeft a b F F' G l D hD')) fun c₀ x ↦ ?_
  have h₁ : c₀.ι.opensRange ≤ pullback.fst a b ⁻¹ᵁ c₀.left :=
    c₀.opensRange_ι.le.trans inf_le_left
  have h₂ : c₀.ι.opensRange ≤ pullback.snd a b ⁻¹ᵁ c₀.right :=
    c₀.opensRange_ι.le.trans inf_le_right
  refine c₀.ext_of_externalTensorSection_of_eq F G
    (by rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_comp_of_isIso]) h₁ h₂
    (boxOpLeft a b F F' G k D hD (op c₀.ι.opensRange))
    (boxOpLeft a b F F' G l D hD' (op c₀.ι.opensRange)) (fun s t ↦ ?_) x
  exact (boxOpLeft_externalTensorSection a b F F' G k D hD s t c₀.ι.opensRange h₁ h₂).trans
    (boxOpLeft_externalTensorSection a b F F' G l D hD' s t c₀.ι.opensRange h₁ h₂).symm

end

namespace FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} {a : X ⟶ S} {b : Y ⟶ S}

/-- **The box product of a finite-order differential operator with the identity.** For a morphism
`D : F ⟶ F'` of the category of finite-order differential operators on `X/S` and an object `G` of
the category on `Y/S`, the operator `D ⊠ 1 : F ⊠ G ⟶ F' ⊠ G` of the category of finite-order
differential operators on `X ×_S Y / S`. -/
def boxHomLeft {F F' : FiniteOrderDifferentialOperatorCategory a}
    (G : FiniteOrderDifferentialOperatorCategory b) (D : F ⟶ F') :
    boxProductObj F G ⟶ boxProductObj F' G :=
  homOfPullbackSnd _ _
    (boxOpLeft a b F.module F'.module G.module D.2.choose D.1 D.2.choose_spec)
    ⟨D.2.choose, isGlobalDiffOpOfOrder_boxOpLeft a b F.module F'.module G.module
      D.2.choose D.1 D.2.choose_spec⟩

/-- The underlying operator of `D ⊠ 1` is the glued box product of `D` with the identity, for any
order bound of `D`. -/
theorem boxHomLeft_coe {F F' : FiniteOrderDifferentialOperatorCategory a}
    (G : FiniteOrderDifferentialOperatorCategory b) (D : F ⟶ F') {k : ℕ}
    (hD : DiffOp.IsGlobalDiffOpOfOrder a.relativeStructureSheafMap k D.1) :
    (boxHomLeft G D).1 = boxOpLeft a b F.module F'.module G.module k D.1 hD :=
  boxOpLeft_eq_of_order a b F.module F'.module G.module D.1 D.2.choose_spec hD

/-- **`D ⊠ 1` on the section attached to a pair of local sections.** -/
theorem boxHomLeft_externalTensorSection {F F' : FiniteOrderDifferentialOperatorCategory a}
    (G : FiniteOrderDifferentialOperatorCategory b) (D : F ⟶ F') {U' : X.Opens} {V' : Y.Opens}
    (s : Γ(F.module, U')) (t : Γ(G.module, V')) (W : (pullback a b).Opens)
    (hW₁ : W ≤ pullback.fst a b ⁻¹ᵁ U') (hW₂ : W ≤ pullback.snd a b ⁻¹ᵁ V') :
    (boxHomLeft G D).1 (op W)
        (externalTensorSection a b F.module G.module s t W hW₁ hW₂) =
      externalTensorSection a b F'.module G.module (D.1 (op U') s) t W hW₁ hW₂ :=
  boxOpLeft_externalTensorSection a b F.module F'.module G.module D.2.choose D.1 D.2.choose_spec
    s t W hW₁ hW₂

end FiniteOrderDifferentialOperatorCategory

end AlgebraicGeometry

end
