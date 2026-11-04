module

public import StacksFrontier.AlgebraicGeometry.Cohomology.CechKunneth.KunnethFormula

/-!
# The Künneth isomorphism does not depend on the coverings

The Künneth isomorphism `Stacks.CechKunneth.kunnethIsoOfCovers` of [Stacks, Tag 0BED] is built
from finite affine coverings `𝒰` of `X` and `𝒱` of `Y`. This file proves that it does not depend
on them: a refinement of the coverings ([Stacks, Tag 01FD]) changes neither the classes of Čech
cocycles nor the Alexander–Whitney product of two cocycles, read as sections of `ℱ ⊠ 𝒢`, and any
two finite affine coverings of a scheme with affine diagonal have a common finite affine
refinement, the pairwise intersections.

## Main results

* `Stacks.CechKunneth.kunnethIsoOfCovers_eq_of_refines`: refining the coverings does not change
  the isomorphism.
* `Stacks.CechKunneth.kunnethIsoOfCovers_eq`: any two pairs of finite affine coverings give the
  same isomorphism.
* `Stacks.CechKunneth.kunnethIsoOfAffineDiagonal_eq`: the Künneth isomorphism is the one of any
  pair of finite affine coverings; it is canonical.

## References

* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 01FD](https://stacks.math.columbia.edu/tag/01FD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry TensorProduct

universe u

namespace Stacks.CechKunneth

/-- **The common refinement of two finite affine coverings** of a scheme with affine diagonal:
the pairwise intersections. -/
def FiniteAffineCover.inf {X : Scheme.{u}} [IsAffineHom (pullback.diagonal (terminal.from X))]
    (C C' : FiniteAffineCover X) : FiniteAffineCover X where
  I := C.I × C'.I
  U ij := C.U ij.1 ⊓ C'.U ij.2
  isAffineOpen ij := (C.isAffineOpen ij.1).inf (C'.isAffineOpen ij.2)
  iSup_eq := by
    refine (eq_top_iff.2 fun x _ => ?_).symm
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (C.iSup_eq ▸ trivial : x ∈ ⨆ i, C.U i)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (C'.iSup_eq ▸ trivial : x ∈ ⨆ j, C'.U j)
    exact Opens.mem_iSup.2 ⟨(i, j), ⟨hi, hj⟩⟩

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))]
  (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
  (CX CX' : FiniteAffineCover X) (CY CY' : FiniteAffineCover Y)
  (rX : CX'.I → CX.I) (hrX : ∀ i, CX'.U i ≤ CX.U (rX i))
  (rY : CY'.I → CY.I) (hrY : ∀ j, CY'.U j ≤ CY.U (rY j))

/-- Refining a finite affine covering of `X` does not change the cohomology class of a Čech
cocycle: the class of the restricted cocycle under `cechEquivX` is that of the original. -/
theorem cechEquivX_refCochain {p : ℕ} (c : Cochain (sectionsK X (structureRingHom f) F) CX.U p)
    (hc : d _ CX.U p c = 0) :
    cechEquivX f CX' F p (Hmk _ _ (refCochain _ CX.U CX'.U rX hrX p c)
        (by rw [refCochain_d, hc, map_zero])) = cechEquivX f CX F p (Hmk _ _ c hc) :=
  cechEquiv_refCochain X _ F CX.U CX.iSup_eq CX'.U CX'.iSup_eq rX hrX _ _ c hc

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] in
include hrX hrY in
/-- If `CX'` refines `CX` along `rX` and `CY'` refines `CY` along `rY`, then the product covering
of `X ×ₖ Y` by `CX'` and `CY'` refines the one by `CX` and `CY` along `Prod.map rX rY`. -/
theorem prodCover_refines (ij : CX'.I × CY'.I) :
    ((boxOpen f g).obj ∘ prodCover CX'.U CY'.U) ij ≤
      ((boxOpen f g).obj ∘ prodCover CX.U CY.U) (Prod.map rX rY ij) :=
  (boxOpen f g).monotone (LatProd.le_mk (hrX ij.1) (hrY ij.2))

/-- Refining the product covering of `X ×ₖ Y` does not change the cohomology class of a Čech
cocycle of `ℱ ⊠ 𝒢`: the class of the restricted cocycle under `cechEquivProd` is that of the
original. -/
theorem cechEquivProd_refCochain {n : ℕ} (z : Cochain (sectionsK (pullback f g)
      (structureRingHom (pullback.fst f g ≫ f)) (externalTensorProduct f g F G))
      ((boxOpen f g).obj ∘ prodCover CX.U CY.U) n) (hz : d _ _ n z = 0) :
    cechEquivProd f g CX' CY' F G n (Hmk _ _ (refCochain _ _ _ (Prod.map rX rY)
        (prodCover_refines f g CX CX' CY CY' rX hrX rY hrY) n z)
        (by rw [refCochain_d, hz, map_zero])) = cechEquivProd f g CX CY F G n (Hmk _ _ z hz) :=
  cechEquiv_refCochain (pullback f g) _ _ _ _ _ _ _ _ _ _ z hz

omit [IsAffineHom (pullback.diagonal (terminal.from X))]
  [IsAffineHom (pullback.diagonal (terminal.from Y))] [F.IsQuasicoherent] [G.IsQuasicoherent] in
/-- **The Alexander–Whitney product commutes with refinement**: restricting `boxCup` of two Čech
cochains to the refined product covering gives `boxCup` of their restrictions. -/
theorem refCochain_boxCup {n : ℕ} (pq : Idx n)
    (c : Cochain (sectionsK X (structureRingHom f) F) CX.U pq.1.1)
    (e : Cochain (sectionsK Y (structureRingHom g) G) CY.U pq.1.2) :
    refCochain _ _ _ (Prod.map rX rY) (prodCover_refines f g CX CX' CY CY' rX hrX rY hrY) n
        (boxCup f g CX CY F G pq c e) =
      boxCup f g CX' CY' F G pq (refCochain _ CX.U CX'.U rX hrX _ c)
        (refCochain _ CY.U CY'.U rY hrY _ e) := by
  funext σ
  rw [refCochain_apply, boxCup_apply, boxCup_apply]
  exact
    (Stacks.Tag01VSPullbackTensor.externalTensorSection_presheaf_map f g F G _ _ _ _ _ _ _).trans
      (externalTensorSection_res f g F G _ _ _ _ _ _ _).symm

include hrX hrY in
/-- **Refining the coverings does not change the Künneth isomorphism.** -/
theorem kunnethIsoOfCovers_eq_of_refines (n : ℕ) :
    kunnethIsoOfCovers f g CX' CY' F G n = kunnethIsoOfCovers f g CX CY F G n := by
  refine LinearEquiv.symm_bijective.injective (LinearEquiv.toLinearMap_injective
    (DirectSum.linearMap_ext k fun pq => TensorProduct.ext' fun a b => ?_))
  obtain ⟨α, rfl⟩ := (cechEquivX f CX F pq.1.1).surjective a
  obtain ⟨β, rfl⟩ := (cechEquivX g CY G pq.1.2).surjective b
  obtain ⟨c, hc, rfl⟩ := Hmk_surjective _ _ α
  obtain ⟨e, he, rfl⟩ := Hmk_surjective _ _ β
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← cechEquivX_refCochain f F CX CX' rX hrX c hc,
    ← cechEquivX_refCochain g G CY CY' rY hrY e he, kunnethIsoOfCovers_symm_lof_tmul,
    cechEquivX_refCochain f F CX CX' rX hrX c hc, cechEquivX_refCochain g G CY CY' rY hrY e he,
    kunnethIsoOfCovers_symm_lof_tmul,
    ← cechEquivProd_refCochain f g F G CX CX' CY CY' rX hrX rY hrY]
  exact congrArg (cechEquivProd f g CX' CY' F G n)
    (Hmk_congr _ _ (refCochain_boxCup f g F G CX CX' CY CY' rX hrX rY hrY pq c e).symm _ _)

/-- **The Künneth isomorphism does not depend on the finite affine coverings.** -/
theorem kunnethIsoOfCovers_eq (n : ℕ) :
    kunnethIsoOfCovers f g CX CY F G n = kunnethIsoOfCovers f g CX' CY' F G n :=
  (kunnethIsoOfCovers_eq_of_refines f g F G CX (CX.inf CX') CY (CY.inf CY') Prod.fst
      (fun _ => inf_le_left) Prod.fst (fun _ => inf_le_left) n).symm.trans
    (kunnethIsoOfCovers_eq_of_refines f g F G CX' (CX.inf CX') CY' (CY.inf CY') Prod.snd
      (fun _ => inf_le_right) Prod.snd (fun _ => inf_le_right) n)

variable (k) in
/-- **The Künneth isomorphism is canonical**: it is the isomorphism
`Stacks.CechKunneth.kunnethIsoOfCovers` of *any* pair of finite affine coverings of `X` and `Y`,
which on Čech classes is the Alexander–Whitney product of the pulled-back cocycles
(`Stacks.CechKunneth.kunnethIsoOfCovers_symm_lof_tmul`). -/
@[stacks 0BED "the isomorphism is canonical: independent of the chosen finite affine covers, and \
on Cech classes given by the cup product of the pulled-back cocycles"]
theorem kunnethIsoOfAffineDiagonal_eq [CompactSpace X] [CompactSpace Y] (n : ℕ) :
    kunnethIsoOfAffineDiagonal k f g F G n = kunnethIsoOfCovers f g CX CY F G n :=
  kunnethIsoOfCovers_eq f g F G _ CX _ CY n

end Stacks.CechKunneth

end
