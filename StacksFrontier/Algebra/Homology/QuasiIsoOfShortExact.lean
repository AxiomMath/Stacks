module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# A monomorphism of complexes with acyclic cokernel is a quasi-isomorphism

Let `0 → K → L → N → 0` be a short exact sequence of cochain complexes in an abelian category.
If every cohomology object of `N` vanishes then `K → L` is a quasi-isomorphism: in the long
exact cohomology sequence the two neighbours of `H^i(K) → H^i(L)` are `H^{i-1}(N)` and `H^i(N)`,
so that map is both a monomorphism and an epimorphism.

## Main results

* `CategoryTheory.quasiIso_of_shortExact_of_isZero_homology`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A monomorphism of complexes with acyclic cokernel is a quasi-isomorphism. -/
lemma quasiIso_of_shortExact_of_isZero_homology {C : Type*} [Category C] [Abelian C]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    (hQ : ∀ i, IsZero (S.X₃.homology i)) : QuasiIso S.f := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₁ (i - 1) i (by change i - 1 + 1 = i; omega)).mono_g
      ((hQ (i - 1)).eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.f i) :=
    (hS.homology_exact₂ i).epi_f ((hQ i).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end CategoryTheory
