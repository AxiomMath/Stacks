module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.FormallySmooth.Topological
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of adic formal smoothness

Formal smoothness for an adic topology is preserved by arbitrary base change.  The
base-changed algebra is represented by `S ⊗[R] R'`; its structural map from `R'` is
`Algebra.TensorProduct.includeRight`, and the extended ideal is the image along
`Algebra.TensorProduct.includeLeft`.

## Main results

* `RingHom.FormallySmoothNAdic.baseChange`: arbitrary base change preserves formal
  smoothness for an adic topology.

## References

* [Stacks Project, Tag 07EG](https://stacks.math.columbia.edu/tag/07EG)
-/

@[expose] public section

namespace RingHom.FormallySmoothNAdic

/-- Formal smoothness for the `n`-adic topology is preserved by arbitrary base change from
`R` to `R'`; on `S ⊗[R] R'`, the adic ideal is the extension of `n`. -/
@[stacks 07EG, ega "0 19.3.5" "(iii)", ega "0 19.9.3" "adic topology case"]
theorem baseChange.{u, v, w, z}
    {R : Type v} {S : Type w} {R' : Type z}
    [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
    (n : Ideal S) (h : RingHom.FormallySmoothNAdic.{u, v, w} (algebraMap R S) n) :
    RingHom.FormallySmoothNAdic.{u, z, max w z}
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := R')).toRingHom
      (n.map (Algebra.TensorProduct.includeLeft (R := R) (S := R)
        (A := S) (B := R')).toRingHom) := by
  intro A _ J hJ f ψ hcomm hk
  let ψS : S →+* A ⧸ J := ψ.comp
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := R')).toRingHom
  let fR : R →+* A := f.comp (algebraMap R R')
  have hcommS : ψS.comp (algebraMap R S) = (Ideal.Quotient.mk J).comp fR := by
    ext r
    simpa [ψS, fR] using DFunLike.congr_fun hcomm (algebraMap R R' r)
  have hkS : ∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker ψS := by
    obtain ⟨k, hk, hpow⟩ := hk
    exact ⟨k, hk, fun x hx ↦ hpow (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx)⟩
  obtain ⟨gS, hgSquot, hgSR⟩ := h A J hJ fR ψS hcommS hkS
  let : Algebra R A := fR.toAlgebra
  let gS' : S →ₐ[R] A := { gS with commutes' := fun r ↦ DFunLike.congr_fun hgSR r }
  let f' : R' →ₐ[R] A := { f with commutes' := fun _ ↦ rfl }
  let g := (Algebra.TensorProduct.lift gS' f' (fun _ _ ↦ Commute.all _ _)).toRingHom
  refine ⟨g, ?_, ?_⟩
  · ext s
    · simpa [g, gS', ψS] using DFunLike.congr_fun hgSquot s
    · simpa [g, f'] using (DFunLike.congr_fun hcomm s).symm
  · ext r
    simp [g, f']

end RingHom.FormallySmoothNAdic
