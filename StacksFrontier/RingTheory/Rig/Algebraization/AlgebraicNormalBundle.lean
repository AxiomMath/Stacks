module

public import StacksFrontier.RingTheory.AdicCompletion.IteratedMvPolynomial
public import StacksFrontier.RingTheory.Rig.Algebraization.NormalBundle
public import StacksFrontier.RingTheory.Rig.Algebraization.RigEtaleAlgebraizationAux

/-!
# An algebraic model of the completed normal bundle

Let `D : Rig.NormalBundle.Data B Pres` be the data of a completed normal bundle, with
`N = Pres.variableCount` variables, and suppose that the generators `fₗ` of `J` and the
quasi-idempotent `Ẽ` are *polynomials*, `fₗ = fPₗ` and `Ẽ = EP` in `A[x] ⊆ A⟨x⟩`. Then the
equations of the normal bundle are polynomials in `A[X][x', T]`, and

`W = A[X][x', T] / (fP(x'), (aᶜ − EP(x')) T, X − x' − aᵏ T)`

is a finite type `A[X]`-algebra whose `(a)`-adic completion is the completed normal bundle
`Ĉ = D.obj`. Hence `W^` is rig-étale over `(A[X], (a))`, and there is `g ∈ 1 + aW` with `W_g`
étale over `Spec A[X] ∖ V(a)` and `W_g^ ≅ Ĉ`.

## Main definitions

* `Rig.NormalBundle.Data.PolynomialLift`: polynomial lifts `fP`, `EP` of `D.f` and `D.Et`.
* `Rig.NormalBundle.Data.PolynomialLift.W`: the algebraic normal bundle `W`.

## Main results

* `Rig.NormalBundle.Data.PolynomialLift.completionEquiv`: `W^ ≅ Ĉ` as `A[X]`-algebras.
* `Rig.NormalBundle.Data.PolynomialLift.isRigEtale_adicCompletionObj`: `W^` is rig-étale.
* `Rig.NormalBundle.Data.PolynomialLift.exists_isEtaleOutside_away`: a localization `W_g` with
  `g ∈ 1 + aW`, étale off `V(a)`, together with `W_g^ ≅ Ĉ` compatible with `W → W_g`.

## References

* [Stacks Project, Tag 0GAF](https://stacks.math.columbia.edu/tag/0GAF)
* [Stacks Project, Tag 0ALQ](https://stacks.math.columbia.edu/tag/0ALQ)
-/

@[expose] public noncomputable section

open MvPolynomial

universe u v

namespace Rig

namespace NormalBundle

namespace Data

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {a : A}
  {B : AdicFiniteTypeAlgebra.{u, v} A (Ideal.span {a})}
  {Pres : CompletedPolynomialPresentation (Ideal.span {a}) B}

/-- Polynomial lifts of the data of a normal bundle: polynomials `fP` and `EP` in
`A[x₁, …, x_N]` whose images in `A⟨x⟩` are the generators `D.f` of `J` and the
quasi-idempotent `D.Et`. -/
structure PolynomialLift (D : Data B Pres) where
  /-- Polynomial lifts of the generators of `J`. -/
  fP : Fin D.m → MvPolynomial (Fin Pres.variableCount) A
  /-- A polynomial lift of the quasi-idempotent `Ẽ`. -/
  EP : Matrix (Fin Pres.variableCount) (Fin Pres.variableCount)
    (MvPolynomial (Fin Pres.variableCount) A)
  f_eq : ∀ l, D.f l = algebraMap _ Pres.completedPolynomialRing (fP l)
  Et_eq : ∀ i j, D.Et i j = algebraMap _ Pres.completedPolynomialRing (EP i j)

/-- The polynomial ring `A[X][x', T]` in which the algebraic normal bundle is cut out. -/
abbrev Poly (N : ℕ) := MvPolynomial (Fin (N + N)) (Base (A := A) N)

/-- The polynomial equations `Xᵢ − xᵢ' − aᵏ Tᵢ`. -/
def gPoly (D : Data B Pres) (i : Fin Pres.variableCount) : Poly (A := A) Pres.variableCount :=
  C (X i) - X (Fin.castAdd Pres.variableCount i) -
    algebraMap A (Poly (A := A) Pres.variableCount) (a ^ D.k) *
      X (Fin.natAdd Pres.variableCount i)

namespace PolynomialLift

variable {D : Data B Pres} (L : D.PolynomialLift)

/-- The polynomial equations `fₗ(x')`. -/
def fPoly (l : Fin D.m) : Poly (A := A) Pres.variableCount :=
  inclPoly Pres.variableCount (L.fP l)

/-- The polynomial equations `((aᶜ − EP(x')) T)ᵢ`. -/
def lPoly (i : Fin Pres.variableCount) : Poly (A := A) Pres.variableCount :=
  ∑ j, ((1 : Matrix (Fin Pres.variableCount) (Fin Pres.variableCount)
      (Poly (A := A) Pres.variableCount)) i j *
        algebraMap A (Poly (A := A) Pres.variableCount) (a ^ D.c) -
      inclPoly Pres.variableCount (L.EP i j)) * X (Fin.natAdd Pres.variableCount j)

/-- All the polynomial equations, indexed as `Rig.NormalBundle.Data.gens`. -/
def gensPoly : Fin D.m ⊕ (Fin Pres.variableCount ⊕ Fin Pres.variableCount) →
    Poly (A := A) Pres.variableCount :=
  Sum.elim L.fPoly (Sum.elim L.lPoly D.gPoly)

/-- The ideal `K` of the algebraic normal bundle in `A[X][x', T]`. -/
def idealPoly : Ideal (Poly (A := A) Pres.variableCount) := Ideal.span (Set.range L.gensPoly)

/-- The algebraic normal bundle `W = A[X][x', T] / K`. -/
abbrev W := Poly (A := A) Pres.variableCount ⧸ L.idealPoly

/-- `W` is of finite type over `A[X]`. -/
instance : Algebra.FiniteType (Base (A := A) Pres.variableCount) L.W :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ (Base (A := A) Pres.variableCount) L.idealPoly)
    (Ideal.Quotient.mkₐ_surjective _ _)

/-- The completion map `A[X][x', T] → A[X]⟨x', T⟩`. -/
local notation "φ" => algebraMap (Poly (A := A) Pres.variableCount) (Amb a Pres.variableCount)

omit [IsNoetherianRing A] in
/-- The completion map is compatible with the structure maps from `A`. -/
theorem algebraMap_A_poly (r : A) :
    φ (algebraMap A (Poly (A := A) Pres.variableCount) r) =
      algebraMap A (Amb a Pres.variableCount) r :=
  (IsScalarTower.algebraMap_apply A (Poly (A := A) Pres.variableCount)
    (Amb a Pres.variableCount) r).symm

/-- The image of `fP(x')` in `A[X]⟨x', T⟩` is the equation `D.fGen`. -/
theorem algebraMap_fPoly (l : Fin D.m) : φ (L.fPoly l) = D.fGen l := by
  rw [fPoly, fGen, L.f_eq, incl_algebraMap]

/-- The image of `((aᶜ − EP(x')) T)ᵢ` in `A[X]⟨x', T⟩` is the equation `D.lGen`. -/
theorem algebraMap_lPoly (i : Fin Pres.variableCount) : φ (L.lPoly i) = D.lGen i := by
  classical
  rw [lPoly, lGen, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul, map_sub, map_mul, algebraMap_A_poly, ambE, Matrix.map_apply, L.Et_eq,
    incl_algebraMap, tv]
  congr 3
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  exacts [map_one _, map_zero _]

/-- The image of `Xᵢ − xᵢ' − aᵏ Tᵢ` in `A[X]⟨x', T⟩` is the equation `D.gGen`. -/
theorem algebraMap_gPoly (i : Fin Pres.variableCount) : φ (D.gPoly i) = D.gGen i := by
  have hC : φ (C (X i)) = bv a Pres.variableCount i :=
    (IsScalarTower.algebraMap_apply (Base (A := A) Pres.variableCount)
      (Poly (A := A) Pres.variableCount) (Amb a Pres.variableCount) (X i)).symm
  rw [gPoly, gGen, map_sub, map_sub, map_mul, algebraMap_A_poly, hC, xv, tv]

/-- The images of the polynomial equations are the equations `D.gens` of the bundle. -/
theorem algebraMap_gensPoly :
    (φ ∘ L.gensPoly) = D.gens := by
  funext x
  rcases x with l | i | i
  exacts [L.algebraMap_fPoly l, L.algebraMap_lPoly i, algebraMap_gPoly i]

/-- The ideal `K` generates the ideal of the completed normal bundle: `K^ = 𝔎`. -/
theorem map_idealPoly : L.idealPoly.map φ = D.ideal := by
  rw [idealPoly, Ideal.map_span, ← Set.range_comp, algebraMap_gensPoly, ideal]

/-- The presenting surjection `A[X][x', T] → W`. -/
abbrev mkW : Poly (A := A) Pres.variableCount →ₐ[Base (A := A) Pres.variableCount] L.W :=
  Ideal.Quotient.mkₐ _ L.idealPoly

/-- The extension of `ker(A[X][x', T] → W)` to `A[X][x', T]^` is the ideal of the bundle. -/
theorem ker_mkW_map :
    (RingHom.ker L.mkW.toRingHom).map
        (algebraMap (Poly (A := A) Pres.variableCount)
          (adicCompletionMvPolynomial (baseIdeal a Pres.variableCount)
            (Pres.variableCount + Pres.variableCount))) = D.ideal := by
  rw [show RingHom.ker L.mkW.toRingHom = L.idealPoly from Ideal.mk_ker]
  exact L.map_idealPoly

/-- The presentation `W^ = A[X][x', T]^ / K^` of the completion of `W`. -/
def completedQuotientEquiv :
    (adicCompletionMvPolynomial (baseIdeal a Pres.variableCount)
        (Pres.variableCount + Pres.variableCount) ⧸ (RingHom.ker L.mkW.toRingHom).map
          (algebraMap (Poly (A := A) Pres.variableCount)
            (adicCompletionMvPolynomial (baseIdeal a Pres.variableCount)
              (Pres.variableCount + Pres.variableCount)))) ≃ₐ[Base (A := A) Pres.variableCount]
      (adicCompletionObj (baseIdeal a Pres.variableCount) (B := L.W)).carrier :=
  (completedPresentation (baseIdeal a Pres.variableCount) L.mkW
    (Ideal.Quotient.mkₐ_surjective _ _)).quotientEquiv

/-- The completion of the algebraic normal bundle is the completed normal bundle:
`W^ ≅ A[X]⟨x', T⟩ / K^ = Ĉ` as `A[X]`-algebras. -/
def completionEquiv :
    (adicCompletionObj (baseIdeal a Pres.variableCount) (B := L.W)).carrier ≃ₐ[Base (A := A)
      Pres.variableCount] D.obj.carrier :=
  L.completedQuotientEquiv.symm.trans
    ((Ideal.quotientEquivAlgOfEq (Base (A := A) Pres.variableCount)
      (A := adicCompletionMvPolynomial (baseIdeal a Pres.variableCount)
        (Pres.variableCount + Pres.variableCount)) L.ker_mkW_map).trans D.pres.quotientEquiv)

/-- The isomorphism `W^ ≅ Ĉ` sends the class of a polynomial `p` to the class of `p`. -/
theorem completionEquiv_algebraMap_mk (p : Poly (A := A) Pres.variableCount) :
    L.completionEquiv (algebraMap L.W _ (Ideal.Quotient.mk L.idealPoly p)) = D.π (φ p) := by
  have h : algebraMap L.W (adicCompletionObj (baseIdeal a Pres.variableCount) (B := L.W)).carrier
      (Ideal.Quotient.mk L.idealPoly p) =
      L.completedQuotientEquiv
        (Ideal.Quotient.mk _ (algebraMap (Poly (A := A) Pres.variableCount)
          (adicCompletionMvPolynomial (baseIdeal a Pres.variableCount)
            (Pres.variableCount + Pres.variableCount)) p)) :=
    (completedPresentationMap_algebraMap (baseIdeal a Pres.variableCount) L.mkW p).symm
  rw [h]
  change D.pres.quotientEquiv (Ideal.quotientEquivAlgOfEq _ L.ker_mkW_map
    (L.completedQuotientEquiv.symm (L.completedQuotientEquiv _))) = _
  rw [AlgEquiv.symm_apply_apply, Ideal.quotientEquivAlgOfEq_mk]
  rfl

/-- The completion of the algebraic normal bundle is rig-étale over `(A[X], (a))`. -/
theorem isRigEtale_adicCompletionObj :
    IsRigEtale (adicCompletionObj (baseIdeal a Pres.variableCount) (B := L.W)) :=
  isRigEtale_of_algEquiv L.completionEquiv D.isRigEtale

/-- There is `g ∈ 1 + aW` such that `W_g` is étale over `Spec A[X] ∖ V(a)`, together with an
isomorphism `W_g^ ≅ Ĉ` of `A[X]`-algebras sending the image of the class of a polynomial `p` to
the class of `p`; in particular it is compatible with `W → W_g` and `W^ ≅ Ĉ`. -/
theorem exists_isEtaleOutside_away :
    ∃ g : L.W, g - 1 ∈ (baseIdeal a Pres.variableCount).map
        (algebraMap (Base (A := A) Pres.variableCount) L.W) ∧
      IsEtaleOutside (baseIdeal a Pres.variableCount) (Localization.Away g) ∧
      ∃ e : AdicCompletion ((baseIdeal a Pres.variableCount).map
          (algebraMap (Base (A := A) Pres.variableCount) (Localization.Away g)))
          (Localization.Away g) ≃ₐ[Base (A := A) Pres.variableCount] D.obj.carrier,
        (∀ w : L.W, e (algebraMap (Localization.Away g) _ (algebraMap L.W _ w)) =
          L.completionEquiv (algebraMap L.W _ w)) ∧
        ∀ p : Poly (A := A) Pres.variableCount,
          e (algebraMap (Localization.Away g) _
            (algebraMap L.W _ (Ideal.Quotient.mk L.idealPoly p))) = D.π (φ p) := by
  obtain ⟨g, hg, hgEt⟩ := exists_isEtaleOutside_localization_of_isRigEtale_adicCompletionObj
    (baseIdeal a Pres.variableCount) L.isRigEtale_adicCompletionObj
  obtain ⟨E, hE⟩ := exists_adicCompletion_algEquiv_away
    ((baseIdeal a Pres.variableCount).map (algebraMap (Base (A := A) Pres.variableCount) L.W)) hg
  have hJ : ((baseIdeal a Pres.variableCount).map
      (algebraMap (Base (A := A) Pres.variableCount) L.W)).map
        (algebraMap L.W (Localization.Away g)) =
      (baseIdeal a Pres.variableCount).map
        (algebraMap (Base (A := A) Pres.variableCount) (Localization.Away g)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let Wg := Localization.Away g
  let J₁ := ((baseIdeal a Pres.variableCount).map
    (algebraMap (Base (A := A) Pres.variableCount) L.W)).map (algebraMap L.W Wg)
  let J₂ := (baseIdeal a Pres.variableCount).map
    (algebraMap (Base (A := A) Pres.variableCount) Wg)
  have hIJ : J₂ = J₁.map ((AlgEquiv.refl : Wg ≃ₐ[Base (A := A) Pres.variableCount] Wg) :
      Wg →+* Wg) := by
    rw [AlgEquiv.refl_toRingHom, Ideal.map_id]
    exact hJ.symm
  obtain ⟨F, hF⟩ : ∃ F : AdicCompletion J₁ Wg ≃ₐ[Base (A := A) Pres.variableCount]
      AdicCompletion J₂ Wg, ∀ y : Wg, F.symm (algebraMap Wg (AdicCompletion J₂ Wg) y) =
        algebraMap Wg (AdicCompletion J₁ Wg) y := by
    refine ⟨AdicCompletion.congrAlgEquiv AlgEquiv.refl hIJ, fun y ↦ ?_⟩
    rw [AlgEquiv.symm_apply_eq]
    exact (AdicCompletion.congrAlgEquiv_of AlgEquiv.refl hIJ y).symm
  let e := (F.symm.trans (E.restrictScalars (Base (A := A) Pres.variableCount)).symm).trans
    L.completionEquiv
  have he : ∀ w : L.W, e (algebraMap Wg _ (algebraMap L.W Wg w)) =
      L.completionEquiv (algebraMap L.W _ w) := by
    intro w
    have hE' : (E.restrictScalars (Base (A := A) Pres.variableCount)).symm
        (algebraMap Wg (AdicCompletion J₁ Wg) (algebraMap L.W Wg w)) =
        algebraMap L.W _ w := by
      rw [AlgEquiv.symm_apply_eq]
      exact (hE w).symm
    change L.completionEquiv ((E.restrictScalars _).symm (F.symm _)) = _
    rw [hF, hE']
    rfl
  exact ⟨g, hg, hgEt, e, he, fun p ↦ by rw [he, completionEquiv_algebraMap_mk]⟩

end PolynomialLift

end Data

end NormalBundle

end Rig

end
