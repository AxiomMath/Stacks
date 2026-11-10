module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChartSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence
public import StacksFrontier.RingTheory.MvPolynomial.VariablesRegular
public import StacksFrontier.RingTheory.Koszul.Regular
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.RingTheory.Flat.Localization

/-!
# The coordinate ring of the chart `D₊(T)` of the projective completion

Let `E = Proj_X(Sym^*(𝒞)[T])` and let `V` be an affine open of `X` with `R = Γ(X, V)` and
`M = Γ(𝒞, V)`. The image `W ⊆ E` of the standard open `D₊(T)` of the chart over `V` has ring of
functions `Γ(E, W) ≅ (Sym_R(M)[T])_{(T)} ≅ Sym_R(M)`, the function `y_m = m / T` going to `m`.
When `M` is free with basis `b₁, …, b_r` this is the polynomial ring `R[y_{b₁}, …, y_{b_r}]`, so
the germs of the coordinates `y_{b_j}` at a point of `W` form a Koszul-regular sequence.

## Main definitions

* `Stacks.Chow.ProjectiveCompletion.coordRingEquiv`: `Γ(E, W) ≅ Sym_R(M)`.

## Main results

* `Stacks.Chow.ProjectiveCompletion.coordRingEquiv_coordY`: `y_m ↦ m`.
* `Stacks.Chow.ProjectiveCompletion.isKoszulRegular_germ_coordY`: the germs of the coordinates
  form a Koszul-regular sequence.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SymGraded Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.Chow.ProjectiveCompletion

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] {V : X.Opens}
  (hV : IsAffineOpen V)

/-- **The ring of functions on `W = D₊(T)` is `Sym_R(M)`.** -/
def coordRingEquiv : Γ(space 𝒞, openW 𝒞 hV) ≃+* SymmetricAlgebra Γ(X, V) Γ(𝒞, V) :=
  ((chart 𝒞 V hV).appIso (chartD 𝒞 (V := V))).commRingCatIsoToRingEquiv.trans
    ((AlgebraicGeometry.Proj.basicOpenIsoAway ((symAlg 𝒞).grading V)
        ((chartT 𝒞 V : (symAlg 𝒞).grading V 1) : (symAlg 𝒞).sectionRing V)
        (chartT 𝒞 V).2 one_pos).commRingCatIsoToRingEquiv.symm.trans
      (chartAwayEquiv 𝒞 hV))

/-- The function `y_m = m / T` goes to `m`. -/
theorem coordRingEquiv_coordY (m : Γ(𝒞, V)) :
    coordRingEquiv 𝒞 hV (coordY 𝒞 hV m) = SymmetricAlgebra.ι Γ(X, V) Γ(𝒞, V) m := by
  rw [← (chartAwayEquiv 𝒞 hV).apply_symm_apply (SymmetricAlgebra.ι Γ(X, V) Γ(𝒞, V) m),
    chartAwayEquiv_symm_ι]
  change chartAwayEquiv 𝒞 hV ((AlgebraicGeometry.Proj.basicOpenIsoAway _ _ (chartT 𝒞 V).2
    one_pos).inv (((chart 𝒞 V hV).appIso (chartD 𝒞 (V := V))).hom
      (((chart 𝒞 V hV).appIso (chartD 𝒞 (V := V))).inv (chartY 𝒞 m)))) = _
  rw [Iso.inv_hom_id_apply]
  congr 1
  exact Iso.hom_inv_id_apply (AlgebraicGeometry.Proj.basicOpenIsoAway _ _ (chartT 𝒞 V).2
    one_pos) _

/-- The open `W = D₊(T)` is affine. -/
theorem isAffineOpen_openW : IsAffineOpen (openW 𝒞 hV) :=
  (AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _ (chartT 𝒞 V).2
    one_pos).image_of_isOpenImmersion (chart 𝒞 V hV)

/-- **The coordinates of `W` form a weakly regular sequence** of `Γ(E, W)`, for a basis of `M`. -/
theorem isWeaklyRegular_coordY {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V)) :
    RingTheory.Sequence.IsWeaklyRegular Γ(space 𝒞, openW 𝒞 hV)
      (List.ofFn fun j => coordY 𝒞 hV (b j)) := by
  set e : Γ(space 𝒞, openW 𝒞 hV) ≃+* MvPolynomial (Fin r) Γ(X, V) :=
    (coordRingEquiv 𝒞 hV).trans (SymmetricAlgebra.equivMvPolynomial b).toRingEquiv with he
  have hX : RingTheory.Sequence.IsWeaklyRegular (MvPolynomial (Fin r) Γ(X, V))
      (List.ofFn (MvPolynomial.X : Fin r → MvPolynomial (Fin r) Γ(X, V))) := by
    rcases r with _ | n
    · simp only [List.ofFn_zero]
      exact RingTheory.Sequence.IsWeaklyRegular.nil _ _
    · exact MvPolynomial.isWeaklyRegular_ofFn_X n
  convert Stacks.AlgebraicGeometry.isWeaklyRegular_ofFn_map_of_flat e.symm.toRingHom
    (RingHom.Flat.of_bijective e.symm.bijective) _ hX using 2
  funext j
  change coordY 𝒞 hV (b j) = e.symm (MvPolynomial.X j)
  rw [RingEquiv.eq_symm_apply, he, RingEquiv.trans_apply, coordRingEquiv_coordY]
  exact SymmetricAlgebra.equivMvPolynomial_ι_apply b j

/-- **The germs of the coordinates at a point of `W` form a Koszul-regular sequence.** -/
theorem isKoszulRegular_germ_coordY {r : ℕ} (b : Module.Basis (Fin r) Γ(X, V) Γ(𝒞, V))
    (ξ : space 𝒞) (hξ : ξ ∈ openW 𝒞 hV) :
    Koszul.IsKoszulRegular fun j =>
      (space 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ (coordY 𝒞 hV (b j)) := by
  let : Algebra Γ(space 𝒞, openW 𝒞 hV) ((space 𝒞).presheaf.stalk ξ) :=
    ((space 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ).hom.toAlgebra
  have := (isAffineOpen_openW 𝒞 hV).isLocalization_stalk ⟨ξ, hξ⟩
  have hflat : ((space 𝒞).presheaf.germ (openW 𝒞 hV) ξ hξ).hom.Flat :=
    IsLocalization.flat _ ((isAffineOpen_openW 𝒞 hV).primeIdealOf ⟨ξ, hξ⟩).asIdeal.primeCompl
  exact (Koszul.isKoszulRegularOn_self_iff _).mp
    ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular).1
      (Stacks.AlgebraicGeometry.isWeaklyRegular_ofFn_map_of_flat _ hflat _
        (isWeaklyRegular_coordY 𝒞 hV b)))

end Stacks.Chow.ProjectiveCompletion
