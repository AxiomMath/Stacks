module

public import StacksFrontier.Deformation.Examples.Linear.NodalCubicHlocal

/-!
# The `Q'`-side lift: `N = Q ⊗_P M` does lift

In the counterexample to `Deformation.FlatModuleLiftBaseChangeStatement`, the module
`N = Q ⊗_P M` has an `A'`-flat `Q'`-module lift, namely `N' = Q' ⧸ (x − t·z)`. This is the
*positive* half of the negated conclusion of Stacks 0DZ2 for the counterexample.

Here `z` is the adjoined Artin–Schreier root of `Q'`. The element `Z/Y` does not exist in `Q'`:
`Y = z·(z + 1)` with `z + 1` invertible and `z` not, so `Y` is not a unit in `Q'`.

The image of `x − t·z` in `Q = Q'/t·Q'` is `x`, which generates the kernel of `P → M`, so the
comparison `Q ⊗_{Q'} N' ≃ₗ[Q] Q ⊗_P M` is an equality of ideals of `Q`. The module `N'` is flat
over `A'` because `Q' ⧸ (x − t·z)` is isomorphic, as an `A'`-algebra, to
`(A'[α]/(α² + α − Y))_{α+1}`.

## Main definitions

* `Deformation.Examples.ArtinSchreier.vElt`: the element `x − t·z` of `Q'`.
* `Deformation.Examples.ArtinSchreier.QLift`: `N' = Q' ⧸ (x − t·z)`.
* `Deformation.Examples.ArtinSchreier.qLiftAlgEquivNMod`: `Q' ⧸ (x − t·z) ≃ₐ[A'] (N'₁)_{α+1}`.

## Main results

* `Deformation.Examples.ArtinSchreier.flat_QLift`: **`Module.Flat A' N'`**.
* `Deformation.Examples.ArtinSchreier.map_vIdeal_eq`: the image of `x − t·z` in `Q` generates
  `ker(P → M)·Q`, which is the whole content of the comparison.
* `Deformation.Examples.ArtinSchreier.qRedComparison`: the comparison equivalence
  `Q ⊗_{Q'} N' ≃ Q ⊗_P M`.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
-/

@[expose] public noncomputable section

open Polynomial
open Deformation.Examples.MaurerCartanWindow
open scoped TensorProduct

universe u

namespace Deformation.Examples.ArtinSchreier

/-! ### The element `x − t·z` of `Q'` -/

/-- The image of the thickening coordinate `x` in `Q'`. -/
def xQBase : QBase := algebraMap PBase QBase (AdjoinRoot.root pPoly)

/-- **`x − t·z`**, the element of `Q'` cutting out the `Q'`-side lift. On this side the
Artin–Schreier root is the adjoined `z`, not `Z/Y`: `Y = z·(z + 1)` is not a unit in `Q'`. -/
def vElt : QBase := xQBase - tauQBase * zQ

/-- The ideal `(x − t·z)` of `Q'`. -/
abbrev vIdeal : Ideal QBase := Ideal.span {vElt}

/-- `N' = Q' ⧸ (x − t·z)`, the `A'`-flat `Q'`-module lift of `N = Q ⊗_P M`. -/
abbrev QLift : Type := QBase ⧸ vIdeal

/-- The image of the adjoined root `z` of `Q₁` in `Q'` is `zQ`. -/
private theorem algebraMap_zRoot_eq : algebraMap QOne QBase zRoot = zQ := rfl

/-- `z² + z = Y` in `Q'`, the relation of `Q₁` pushed down. -/
theorem zQ_relation : zQ * zQ + zQ = algebraMap ABase QBase (cst NC ncY) := by
  have h := congrArg (algebraMap QOne QBase) qRelation
  rw [map_add, map_mul] at h
  rw [algebraMap_zRoot_eq] at h
  rw [h, ← IsScalarTower.algebraMap_apply PBase QOne QBase, omegaP,
    ← IsScalarTower.algebraMap_apply ABase PBase QBase]

/-- `x = t·z` in `N'`, which is the relation the quotient imposes. -/
theorem algebraMap_vElt_eq_zero : algebraMap QBase QLift vElt = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)

/-! ### The structure maps of the three `AdjoinRoot`s, named -/

/-- The structure map `A' → P'` of `AdjoinRoot pPoly` is `algebraMap A' P'`. -/
theorem of_pPoly_eq (a : ABase) : AdjoinRoot.of pPoly a = algebraMap ABase PBase a := rfl

/-- The structure map `P' → Q₁` of `AdjoinRoot qPoly` is `algebraMap P' Q₁`. -/
theorem of_qPoly_eq (p : PBase) : AdjoinRoot.of qPoly p = algebraMap PBase QOne p := rfl

/-- The structure map `A' → N'₁` of `AdjoinRoot asPolyA` is `algebraMap A' N'₁`. -/
theorem of_asPolyA_eq (a : ABase) : AdjoinRoot.of asPolyA a = algebraMap ABase NOne a := rfl

/-- The adjoined root of `Q₁ = P'[z]/(z² + z − Y)` is `z`. -/
theorem root_qPoly_eq : AdjoinRoot.root qPoly = zRoot := rfl

/-- The adjoined root of `N'₁ = A'[α]/(α² + α − Y)` is `α`. -/
theorem root_asPolyA_eq : AdjoinRoot.root asPolyA = alphaRoot := rfl

/-- The quotient map `Q' → N'` is `algebraMap Q' N'`. -/
theorem mk_vIdeal_eq (b : QBase) :
    Ideal.Quotient.mk vIdeal b = algebraMap QBase QLift b := rfl

/-! ### `Q' ↠ N'₁` computed on generators -/

/-- On the image of `Q₁`, the map `Q' ↠ (N'₁)_{α+1}` is `qOneToNOne` followed by the
localization map. -/
theorem qBaseToNMod_algebraMap_QOne (b : QOne) :
    qBaseToNMod (algebraMap QOne QBase b) = algebraMap NOne NMod (qOneToNOne b) :=
  IsLocalization.lift_eq _ b

/-- The map `Q' ↠ (N'₁)_{α+1}` sends `z` to `α`. -/
theorem qBaseToNMod_zQ : qBaseToNMod zQ = algebraMap NOne NMod alphaRoot := by
  rw [← algebraMap_zRoot_eq, qBaseToNMod_algebraMap_QOne]
  congr 1
  exact AdjoinRoot.lift_root _

/-- On the image of `P'`, the map `Q' ↠ (N'₁)_{α+1}` is `pBaseToNOne` followed by the
localization map. -/
theorem qBaseToNMod_algebraMap_PBase (p : PBase) :
    qBaseToNMod (algebraMap PBase QBase p) = algebraMap NOne NMod (pBaseToNOne p) := by
  rw [IsScalarTower.algebraMap_apply PBase QOne QBase, qBaseToNMod_algebraMap_QOne]
  congr 1
  exact AdjoinRoot.lift_of _

/-- The map `Q' ↠ (N'₁)_{α+1}` sends `x` to `t·α`. -/
theorem qBaseToNMod_xQBase :
    qBaseToNMod xQBase =
      algebraMap NOne NMod (algebraMap ABase NOne (tau NC) * alphaRoot) := by
  rw [xQBase, qBaseToNMod_algebraMap_PBase]
  congr 1
  exact AdjoinRoot.lift_root _

/-- The map `Q' ↠ (N'₁)_{α+1}` commutes with the structure maps from `A'`. -/
theorem qBaseToNMod_algebraMap_ABase (a : ABase) :
    qBaseToNMod (algebraMap ABase QBase a) = algebraMap ABase NMod a := by
  rw [IsScalarTower.algebraMap_apply ABase PBase QBase, qBaseToNMod_algebraMap_PBase,
    show pBaseToNOne (algebraMap ABase PBase a) = algebraMap ABase NOne a from
      AdjoinRoot.lift_of _,
    ← IsScalarTower.algebraMap_apply ABase NOne NMod]

/-- `Q' ↠ N'₁` kills `x − t·z`: both `x` and `t·z` go to `t·α`. -/
theorem qBaseToNMod_vElt : qBaseToNMod vElt = 0 := by
  rw [vElt, map_sub, map_mul, qBaseToNMod_xQBase, qBaseToNMod_zQ, tauQBase,
    qBaseToNMod_algebraMap_ABase, IsScalarTower.algebraMap_apply ABase NOne NMod,
    ← map_mul, sub_self]

/-! ### The identification `N' = Q' ⧸ (x − t·z)` -/

/-- `Q' ⧸ (x − t·z) → (N'₁)_{α+1}`, induced by the surjection `qBaseToNMod`, which kills
`x − t·z`. -/
def qLiftToNMod : QLift →+* NMod :=
  Ideal.Quotient.lift _ qBaseToNMod (by
    have hle : vIdeal ≤ RingHom.ker qBaseToNMod := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact qBaseToNMod_vElt
    exact fun y hy => hle hy)

/-- The map `N' → (N'₁)_{α+1}` sends the class of `b ∈ Q'` to `qBaseToNMod b`. -/
theorem qLiftToNMod_mk (b : QBase) :
    qLiftToNMod (algebraMap QBase QLift b) = qBaseToNMod b :=
  Ideal.Quotient.lift_mk _ _ _

/-- The map `N' → (N'₁)_{α+1}` commutes with the structure maps from `A'`. -/
theorem qLiftToNMod_algebraMap_ABase (a : ABase) :
    qLiftToNMod (algebraMap ABase QLift a) = algebraMap ABase NMod a := by
  rw [IsScalarTower.algebraMap_apply ABase QBase QLift, qLiftToNMod_mk,
    qBaseToNMod_algebraMap_ABase]

/-- The image of `z` in `N'`. -/
def zQLift : QLift := algebraMap QBase QLift zQ

/-- `N'₁ = A'[α]/(α² + α − Y) → N'`, sending `α ↦ z`. Well defined because `z² + z = Y` holds in
`Q'` already. -/
def nOneToQLift : NOne →+* QLift :=
  AdjoinRoot.lift (algebraMap ABase QLift) zQLift (by
    change Polynomial.eval₂ (algebraMap ABase QLift) zQLift asPolyA = 0
    rw [show asPolyA = X ^ 2 + (X - C (cst NC ncY)) from rfl]
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    have h := congrArg (algebraMap QBase QLift) zQ_relation
    rw [map_add, map_mul, ← IsScalarTower.algebraMap_apply ABase QBase QLift] at h
    rw [zQLift]
    linear_combination h)

/-- The map `N'₁ → N'` sends `α` to `z`. -/
theorem nOneToQLift_root : nOneToQLift alphaRoot = zQLift :=
  AdjoinRoot.lift_root _

/-- The map `N'₁ → N'` commutes with the structure maps from `A'`. -/
theorem nOneToQLift_algebraMap (a : ABase) :
    nOneToQLift (algebraMap ABase NOne a) = algebraMap ABase QLift a :=
  AdjoinRoot.lift_of _

/-- `α + 1` goes to the unit `z + 1`. -/
theorem isUnit_nOneToQLift_alpha_add_one : IsUnit (nOneToQLift (alphaRoot + 1)) := by
  rw [map_add, map_one, nOneToQLift_root, zQLift]
  have h := isUnit_zQ_add_one
  rw [map_add, map_one, algebraMap_zRoot_eq] at h
  have h2 := h.map (algebraMap QBase QLift)
  rwa [map_add, map_one] at h2

/-- `(N'₁)_{α+1} → N'`, the extension of `nOneToQLift` across the localization. -/
def nModToQLift : NMod →+* QLift :=
  IsLocalization.lift (M := Submonoid.powers (alphaRoot + 1)) (g := nOneToQLift) (by
    intro y
    obtain ⟨k, hk⟩ := y.2
    rw [← hk, map_pow]
    exact IsUnit.pow _ isUnit_nOneToQLift_alpha_add_one)

/-- On the image of `N'₁`, the map `(N'₁)_{α+1} → N'` is `nOneToQLift`. -/
theorem nModToQLift_algebraMap (b : NOne) :
    nModToQLift (algebraMap NOne NMod b) = nOneToQLift b :=
  IsLocalization.lift_eq _ b

/-- `nModToQLift` is a right inverse of `qLiftToNMod`. -/
theorem qLiftToNMod_nModToQLift (n : NMod) : qLiftToNMod (nModToQLift n) = n := by
  have hring : qLiftToNMod.comp nModToQLift = RingHom.id NMod := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (alphaRoot + 1)) ?_
    refine AdjoinRoot.ringHom_ext (RingHom.ext fun a => ?_) ?_
    · simp only [RingHom.comp_apply, RingHom.id_apply, of_asPolyA_eq]
      rw [nModToQLift_algebraMap, nOneToQLift_algebraMap, qLiftToNMod_algebraMap_ABase,
        ← IsScalarTower.algebraMap_apply ABase NOne NMod]
    · simp only [RingHom.comp_apply, RingHom.id_apply, root_asPolyA_eq]
      rw [nModToQLift_algebraMap, nOneToQLift_root, zQLift, qLiftToNMod_mk, qBaseToNMod_zQ]
  exact RingHom.congr_fun hring n

/-- `nModToQLift` is a left inverse of `qLiftToNMod`. -/
theorem nModToQLift_qLiftToNMod (y : QLift) : nModToQLift (qLiftToNMod y) = y := by
  have hring : (nModToQLift.comp qLiftToNMod).comp
        (Ideal.Quotient.mk vIdeal) = (Ideal.Quotient.mk vIdeal : QBase →+* QLift) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (zRoot + 1)) ?_
    refine AdjoinRoot.ringHom_ext ?_ ?_
    · refine AdjoinRoot.ringHom_ext (RingHom.ext fun a => ?_) ?_
      · simp only [RingHom.comp_apply, of_pPoly_eq, of_qPoly_eq, mk_vIdeal_eq]
        rw [← IsScalarTower.algebraMap_apply ABase PBase QOne,
          ← IsScalarTower.algebraMap_apply ABase QOne QBase,
          ← IsScalarTower.algebraMap_apply ABase QBase QLift,
          qLiftToNMod_algebraMap_ABase,
          IsScalarTower.algebraMap_apply ABase NOne NMod a, nModToQLift_algebraMap,
          nOneToQLift_algebraMap]
      · simp only [RingHom.comp_apply, of_qPoly_eq, mk_vIdeal_eq]
        rw [← IsScalarTower.algebraMap_apply PBase QOne QBase,
          show algebraMap PBase QBase (AdjoinRoot.root pPoly) = xQBase from rfl,
          qLiftToNMod_mk, qBaseToNMod_xQBase, nModToQLift_algebraMap, map_mul,
          nOneToQLift_algebraMap, nOneToQLift_root]
        have h := algebraMap_vElt_eq_zero
        rw [vElt, map_sub, map_mul, sub_eq_zero, tauQBase,
          ← IsScalarTower.algebraMap_apply ABase QBase QLift] at h
        rw [zQLift, ← h]
    · simp only [RingHom.comp_apply, root_qPoly_eq, mk_vIdeal_eq]
      rw [algebraMap_zRoot_eq, qLiftToNMod_mk, qBaseToNMod_zQ,
        nModToQLift_algebraMap, nOneToQLift_root, zQLift]
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact RingHom.congr_fun hring b

/-- **`N' = Q' ⧸ (x − t·z)` is `(N'₁)_{α+1}`**, as `A'`-algebras: the relation `x = t·z`
eliminates `x`. -/
def qLiftAlgEquivNMod : QLift ≃ₐ[ABase] NMod :=
  AlgEquiv.ofRingEquiv
    (f := { toFun := qLiftToNMod
            invFun := nModToQLift
            left_inv := nModToQLift_qLiftToNMod
            right_inv := qLiftToNMod_nModToQLift
            map_mul' := qLiftToNMod.map_mul
            map_add' := qLiftToNMod.map_add })
    (fun a => qLiftToNMod_algebraMap_ABase a)

/-- **`Module.Flat A' N'`**: the lift `N' = Q' ⧸ (x − t·z)` is flat over `A'`. -/
theorem flat_QLift : Module.Flat ABase QLift := by
  have := flat_NMod
  exact Module.Flat.of_linearEquiv qLiftAlgEquivNMod.toLinearEquiv

/-! ### The comparison, and the lift -/

/-- The image of `x − t·z` in `Q` is `x`, so the ideal it generates there is the kernel of
`P → M` extended to `Q`. -/
theorem map_vIdeal_eq :
    vIdeal.map (algebraMap QBase QRed) =
      (Ideal.span {xRed}).map (algebraMap PRed QRed) := by
  have hv : algebraMap QBase QRed vElt = algebraMap PRed QRed xRed := by
    rw [vElt, map_sub, map_mul, algebraMap_tauQBase_eq_zero, zero_mul, sub_zero, xQBase,
      ← IsScalarTower.algebraMap_apply PBase QBase QRed, xRed,
      ← IsScalarTower.algebraMap_apply PBase PRed QRed]
  rw [Ideal.map_span (algebraMap QBase QRed) {vElt},
    Ideal.map_span (algebraMap PRed QRed) {xRed}, Set.image_singleton, Set.image_singleton]
  exact congrArg Ideal.span (congrArg (fun z => ({z} : Set QRed)) hv)

/- The type of `qRedComparison` is left to be inferred. Written out as `QRed ⊗[PRed] NC`,
instance search finds `Submodule.Quotient.module'` for `Module PRed QRed` and
`Ideal.Quotient.commSemiring` for `CommSemiring PRed`, while the equivalences below carry
`Algebra.toModule` and `CommRing.toCommSemiring`; deciding that these agree requires unfolding
`OreLocalization.instAdd`, which the module system does not expose. The inferred type uses
`Algebra.toModule`, the only `Module P Q` available to
`Deformation.FlatModuleLiftBaseChangeStatement`. -/
/-- **The `Q'`-side comparison** `Q ⊗_{Q'} N' ≃ Q ⊗_P M`, as the composite of Mathlib's quotient
base-change equivalences: `Q ⊗_{Q'} (Q' ⧸ (x − t·z)) ≃ Q ⧸ (x) ≃ Q ⊗_P (P ⧸ (x)) ≃ Q ⊗_P M`. -/
def qRedComparison :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot QRed vIdeal).symm.trans
    ((Ideal.quotientEquivAlgOfEq QRed map_vIdeal_eq).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot QRed (Ideal.span {xRed})).trans
        (Algebra.TensorProduct.congr (AlgEquiv.refl : QRed ≃ₐ[QRed] QRed)
          ncAlgEquivQuotXRed)))

end Deformation.Examples.ArtinSchreier

end
