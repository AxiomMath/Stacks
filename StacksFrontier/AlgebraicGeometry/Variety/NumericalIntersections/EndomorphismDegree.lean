module

public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.ZPowFiniteLocallyFree

/-!
# The degree of a finite endomorphism pulling an ample module back to a tensor power

Let `X` be a proper variety of dimension `d` over a field `k`, let `f : X ⟶ X` be a finite
dominant morphism over `k` and let `𝓝` be an ample invertible `𝒪_X`-module with
`f^*𝓝 ≅ 𝓝^{⊗ m}`. Then `deg(f) = m ^ d`.

This is the computation in the last paragraph of the proof of [Stacks, Tag 0BFG], where `X` is an
abelian variety, `f = [n]` and `m = n²` (by [Stacks, Tag 0BFF] for a symmetric ample `𝓝`): by
[Stacks, Tag 0BEX], `deg_{f^*𝓝}(X) = deg(f) deg_𝓝(X)`; the left side is `deg_{𝓝^{⊗ m}}(X)`,
which is `m ^ d deg_𝓝(X)` because the intersection number is additive in each of its `d` slots
([Stacks, Tag 0BER]); and `deg_𝓝(X) > 0` ([Stacks, Tag 0BEV]). The source reads the two degrees
as leading coefficients of `n ↦ χ(X, 𝓝^{⊗ n m})` and `n ↦ χ(X, 𝓝^{⊗ n})`; here the degree is by
definition the self-intersection number, and multilinearity replaces the comparison of leading
coefficients.

## Main results

* `AlgebraicGeometry.selfIntersectionNumber_tensorPower`: `((𝓛^{⊗ m})^d · Z) = m ^ d (𝓛^d · Z)`.
* `AlgebraicGeometry.degreeOver_eq_pow_of_pullback_iso_tensorPower`: `deg(f) = m ^ d`.

## References

* [Stacks Project, Tag 0BFG](https://stacks.math.columbia.edu/tag/0BFG)
* [Stacks Project, Tag 0BEX](https://stacks.math.columbia.edu/tag/0BEX)
* [Stacks Project, Tag 0BER](https://stacks.math.columbia.edu/tag/0BER)
* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.SheafOfModules.Invertible (tensorPower)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X Z : Scheme.{u}}

/-- The intersection number transported along an equality of structure morphisms. -/
theorem intersectionNumber_congr_base {f f' : X ⟶ Spec (.of k)} [IsProper f] [IsProper f']
    (h : f = f') (i : Z ⟶ X) [IsClosedImmersion i] (d : ℕ) (hd : topologicalKrullDim Z ≤ d)
    (L : Fin d → X.Modules) [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)] :
    intersectionNumber k f i d hd L = intersectionNumber k f' i d hd L := by
  subst h
  rfl

/-- The family that is `M` on `S` and `L` off `S`. -/
def mixFamily {d : ℕ} (S : Finset (Fin d)) (M L : Fin d → X.Modules) : Fin d → X.Modules :=
  fun q => if q ∈ S then M q else L q

/-- If every member of `M` and of `L` is invertible, so is every member of `mixFamily S M L`. -/
theorem isInvertible_mixFamily {d : ℕ} (S : Finset (Fin d)) (M L : Fin d → X.Modules)
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
    [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)] (q : Fin d) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (mixFamily S M L q) := by
  by_cases hq : q ∈ S
  · have h : mixFamily S M L q = M q := ite_eq_left hq
    rw [h]; infer_instance
  · have h : mixFamily S M L q = L q := ite_eq_right hq
    rw [h]; infer_instance

attribute [local instance] isInvertible_mixFamily isInvertible_update

/-- The family that is `M` on `∅` and `L` elsewhere is `L`. -/
theorem mixFamily_empty {d : ℕ} (M L : Fin d → X.Modules) : mixFamily ∅ M L = L :=
  funext fun q => ite_eq_right (Finset.notMem_empty q)

/-- The family that is `M` on all of `Fin d` is `M`. -/
theorem mixFamily_univ {d : ℕ} (M L : Fin d → X.Modules) : mixFamily Finset.univ M L = M :=
  funext fun q => ite_eq_left (Finset.mem_univ q)

/-- Off `S`, the family `mixFamily S M L` agrees with `L`. -/
theorem mixFamily_apply_of_notMem {d : ℕ} {S : Finset (Fin d)} (M L : Fin d → X.Modules)
    {j : Fin d} (hj : j ∉ S) : mixFamily S M L j = L j := ite_eq_right hj

/-- For `j ∉ S`, the family that is `M` on `insert j S` is obtained from the one that is `M` on `S`
by replacing its value at `j` with `M j`. -/
theorem mixFamily_insert {d : ℕ} {S : Finset (Fin d)} (M L : Fin d → X.Modules) {j : Fin d}
    (hj : j ∉ S) :
    mixFamily (insert j S) M L = Function.update (mixFamily S M L) j (M j) := by
  funext q
  by_cases hq : q = j
  · subst hq
    simp [mixFamily]
  · simp [mixFamily, hq]

/-- **The degree of a finite endomorphism pulling an ample module back to its `m`-th tensor
power is `m ^ dim X`.** Let `X` be a proper variety of dimension `d` over `k`, `f : X ⟶ X` a
finite dominant morphism over `k`, and `𝓝` an ample invertible module with `f^*𝓝 ≅ 𝓝^{⊗ m}`.
Then `deg(f) = m ^ d`.

This is the degree computation of [Stacks, Tag 0BFG]: [Stacks, Tag 0BEX] gives
`deg_{f^*𝓝}(X) = deg(f) deg_𝓝(X)`, the left side is `m ^ d deg_𝓝(X)`, and `deg_𝓝(X) > 0` by
[Stacks, Tag 0BEV]. -/
theorem degreeOver_eq_pow_of_pullback_iso_tensorPower (p : X ⟶ Spec (.of k)) [IsVariety k p]
    [IsProper p] (f : X ⟶ X) [IsFinite f] [IsDominant f] (hf : f ≫ p = p) (d : ℕ)
    (hd : topologicalKrullDim X = d) (N : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N]
    (hN : Scheme.Modules.IsAmple X N) (m : ℕ)
    (e : (Scheme.Modules.pullback f).obj N ≅ tensorPower X.presheaf X.ringCatSheaf.2 N (m : ℤ)) :
    degreeOver f = m ^ d := by
  have : IsVariety k (f ≫ p) := by rw [hf]; infer_instance
  -- the intersection number only depends on the isomorphism classes of the modules, by
  -- `AlgebraicGeometry.intersectionNumber_eq_of_iso_at` one slot at a time
  have hiso : ∀ (L M : Fin d → X.Modules)
      [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L q)]
      [∀ q, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (M q)],
      (∀ q, L q ≅ M q) →
        intersectionNumber k p (𝟙 X) d hd.le L = intersectionNumber k p (𝟙 X) d hd.le M := by
    intro L M _ _ eLM
    classical
    have key : ∀ s : Finset (Fin d), intersectionNumber k p (𝟙 X) d hd.le L =
        intersectionNumber k p (𝟙 X) d hd.le (mixFamily s M L) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact intersectionNumber_congr_family k p (𝟙 X) d hd.le (mixFamily_empty M L).symm
      | insert j s hj ih =>
        rw [ih, intersectionNumber_congr_family k p (𝟙 X) d hd.le (mixFamily_insert M L hj)]
        exact intersectionNumber_eq_of_iso_at k p (𝟙 X) d hd.le _ _ j
          (fun q hq => Function.update_of_ne hq _ _)
          ((eqToIso (mixFamily_apply_of_notMem M L hj)) ≪≫ eLM j ≪≫
            eqToIso (by simp))
    rw [key Finset.univ]
    exact intersectionNumber_congr_family k p (𝟙 X) d hd.le (mixFamily_univ M L)
  have h0BEX := degreeWithRespectTo_pullback_of_isFinite k p f d hd N hN
  rw [degreeWithRespectTo_eq_selfIntersectionNumber,
    degreeWithRespectTo_eq_selfIntersectionNumber] at h0BEX
  have h1 : selfIntersectionNumber k (f ≫ p) (𝟙 X) d hd.le ((Scheme.Modules.pullback f).obj N) =
      selfIntersectionNumber k p (𝟙 X) d hd.le
        (tensorPower X.presheaf X.ringCatSheaf.2 N (m : ℤ)) :=
    (intersectionNumber_congr_base k hf (𝟙 X) d hd.le _).trans
      (hiso _ _ fun _ => e)
  rw [h1, selfIntersectionNumber_tensorPower] at h0BEX
  have hpos := selfIntersectionNumber_pos k p (𝟙 X) d hd N hN
  have : ((m ^ d : ℕ) : ℤ) = (degreeOver f : ℤ) := by
    push_cast
    exact mul_right_cancel₀ hpos.ne' h0BEX
  exact_mod_cast this.symm

end AlgebraicGeometry
