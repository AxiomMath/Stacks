module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Properties
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.ChartRingRegular
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute

/-!
# The cyclic cover over `k[[π]]` is regular

Let `Z` be smooth over a field `k`, let `n` be invertible in `k`, and let `X ⟶ Z_R` be the cyclic
cover `Spec_{Z_R}(Sym(L_R)/(φ - π))` over `R = k[[π]]` of [Stacks, Tag 0CEH]. Over an affine open
`U = Spec A` of `Z` trivializing `L`, `X` is `Spec (A ⊗_k R)[x]/(xⁿ - π f)` with `f` a unit, and
that ring is regular (`Stacks.CyclicCover.isRegularRing_chartRing`). Hence **`X` is regular**, as
the source reads off "by the local equation above".

## Main results

* `Stacks.CyclicCover.smooth_sections`: the functions on an affine open of `Z` are a smooth
  `k`-algebra.
* `Stacks.CyclicCover.isRegular_cover`: **`X` is a regular scheme.**

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Polynomial
open scoped TensorProduct

universe u

namespace Stacks.CyclicCover

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)

/-- **The functions on an affine open of a smooth `k`-scheme form a smooth `k`-algebra.** -/
theorem smooth_sections [Smooth f] (U : Z.affineOpens) :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    Algebra.Smooth k Γ(Z, U.1) := by
  have h := HasRingHomProperty.appLE (P := @Smooth) f ‹_› ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  have h' : (sectionsStructure f U.1).hom.Smooth :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)) h
  exact h'

/-- **The cyclic cover `X` over `k[[π]]` is regular.** -/
theorem isRegular_cover [Smooth f] (hn : (n : k) ≠ 0) :
    IsRegular (cover f φ (PowerSeries k) PowerSeries.X) := by
  intro x
  obtain ⟨U, ⟨hU, -, ⟨b⟩⟩, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 (situation f L).isBasis_chartOpens
    (show baseChangeFst f (PowerSeries k) (coverMap f φ _ PowerSeries.X x) ∈ (⊤ : Z.Opens) from
      trivial)
  let U' : Z.affineOpens := ⟨U, hU⟩
  let := (sectionsStructure f U).hom.toAlgebra
  have := smooth_sections f U'
  let e := coverOpenIso f φ U' b (PowerSeries k) PowerSeries.X
  set W := coverOpen f φ U' (PowerSeries k) PowerSeries.X
  have hW : IsAffineOpen W := IsAffine.of_isIso e.hom
  have hf : IsUnit (chartCoeff f φ U' b) :=
    IsUnit.of_mul_eq_one_right _ (rootCoeff_mul_chartCoeff f φ U' b)
  have := isRegularRing_chartRing (A := Γ(Z, U)) (k := k) hn hf
  have hx : x ∈ W := by
    rw [show W = _ from (preimage_baseChangeOpen f φ U' (PowerSeries k) PowerSeries.X).symm]
    exact hxU
  exact ⟨⟨W, hW⟩, hx, IsRegularRing.of_ringEquiv ((Scheme.ΓSpecIso _).symm ≪≫
    Scheme.Γ.mapIso e.op ≪≫ W.topIso).commRingCatIsoToRingEquiv⟩

end Stacks.CyclicCover

end
