module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import StacksFrontier.Algebra.Homology.Resolution.Existence
public import StacksFrontier.Homology.KFlat.Flat

@[expose] public section

/-!
# K-flat resolutions by free modules

Let `R` be a commutative ring and `M` an `R`-module. Covering `M` by a free module and then
iterating the construction on the kernels produces an exact complex `… → F₁ → F₀ → M → 0` of
free `R`-modules (Stacks 00LP). Placing `Fₙ` in cohomological degree `-n` turns it into a
cochain complex of free modules concentrated in degrees `≤ 0` together with a quasi-isomorphism
onto `M` viewed in degree `0`. A bounded above complex of flat modules is K-flat (Stacks 064K),
and free modules are flat, so this complex is a K-flat resolution of `M`.

## Main results

* `CochainComplex.KFlat.exists_free_kFlat_resolution`: every `R`-module `M` receives a
  quasi-isomorphism from a K-flat cochain complex of free `R`-modules concentrated in degrees
  `≤ 0`.

## References

* [Stacks Project, Tag 00LP](https://stacks.math.columbia.edu/tag/00LP)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

open CategoryTheory Limits

noncomputable section

universe u

namespace CochainComplex.KFlat

variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R}

/-- The chain complex `… → F₁ → F₀` underlying an exact free resolution datum of `M`. -/
private def freeChain (D : FreeResolutionData R M) (hD : D.IsExact) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (D.F n))
    (fun n ↦ ModuleCat.ofHom (D.d n))
    (fun n ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦ (hD.2.2 n).le ⟨x, rfl⟩)

/-- The augmentation `F_• → M[0]` of an exact free resolution datum of `M`. -/
private def freeChainAug (D : FreeResolutionData R M) (hD : D.IsExact) :
    freeChain D hD ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M :=
  (ChainComplex.toSingle₀Equiv (freeChain D hD) M).symm
    ⟨ModuleCat.ofHom D.ε, ModuleCat.hom_ext <| LinearMap.ext fun x ↦ hD.2.1.le ⟨x, rfl⟩⟩

/-- An exact free resolution datum is exact in every positive degree. -/
private theorem freeChain_exactAt_succ (D : FreeResolutionData R M) (hD : D.IsExact) (n : ℕ) :
    (freeChain D hD).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
  change LinearMap.range (((freeChain D hD).d (n + 2) (n + 1)).hom) =
    LinearMap.ker (((freeChain D hD).d (n + 1) n).hom)
  simp only [freeChain, ChainComplex.of.d, dite_true,
    show n + 2 = (n + 1) + 1 by omega]
  convert hD.2.2 n using 1
  rfl

/-- Exactness of `… → F₁ → F₀ → M → 0` says that the augmentation is a quasi-isomorphism. -/
private theorem freeChainAug_quasiIso (D : FreeResolutionData R M) (hD : D.IsExact) :
    QuasiIso (freeChainAug D hD) := by
  constructor
  intro n
  cases n with
  | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by rfl) (by rfl) (by rfl)]
      refine ⟨?_, ?_⟩
      · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
        change LinearMap.range (((freeChain D hD).d 1 0).hom) =
          LinearMap.ker ((freeChainAug D hD).f 0).hom
        simp only [freeChain, freeChainAug]
        exact hD.2.1
      · apply (ModuleCat.epi_iff_surjective _).2
        convert hD.1 using 1 <;> rfl
  | succ n =>
      exact (quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj M n)).2
        (freeChain_exactAt_succ D hD n)

/-- An exact free resolution datum of `M` with free terms, read as a projective resolution. -/
private def freeProjectiveResolution (D : FreeResolutionData R M) (hD : D.IsExact)
    (hFree : D.IsFree) : ProjectiveResolution M where
  complex := freeChain D hD
  π := freeChainAug D hD
  projective n :=
    have := hFree n
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (D.F n))
  quasiIso := freeChainAug_quasiIso D hD

/-- Every term of the associated cochain complex is a free `R`-module: in degree `-n` it is
`Fₙ`, and in the positive degrees it is the zero module. -/
private theorem freeCochain_terms (D : FreeResolutionData R M) (hD : D.IsExact)
    (hFree : D.IsFree) (i : ℤ) :
    Module.Free R ((freeProjectiveResolution D hD hFree).cochainComplex.X i) := by
  let Q := freeProjectiveResolution D hD hFree
  by_cases hi : i ≤ 0
  · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hi
    have : Module.Free R (Q.complex.X k) := hFree k
    exact Module.Free.of_equiv (Q.cochainComplexXIso (-k) k).symm.toLinearEquiv
  · have : Subsingleton (Q.cochainComplex.X i) := ModuleCat.isZero_iff_subsingleton.mp
      (CochainComplex.isZero_of_isStrictlyLE Q.cochainComplex 0 i (by omega))
    exact Module.Free.of_subsingleton R _

/-- **Stacks 064K.** Every `R`-module `M` receives a quasi-isomorphism from a K-flat cochain
complex of free `R`-modules concentrated in cohomological degrees `≤ 0`: a free resolution of
`M` read in cohomological indexing is bounded above with flat terms, hence K-flat. -/
theorem exists_free_kFlat_resolution {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ)
      (f : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M),
      P.KFlat ∧ P.IsStrictlyLE 0 ∧ (∀ n : ℤ, Module.Free R (P.X n)) ∧ QuasiIso f := by
  obtain ⟨D, hD, hFree⟩ := exists_free_resolution R (M : Type u)
  let Q := freeProjectiveResolution D hD hFree
  have hfree : ∀ n : ℤ, Module.Free R (Q.cochainComplex.X n) :=
    freeCochain_terms D hD hFree
  have _ : ∀ n : ℤ, Module.Flat R (Q.cochainComplex.X n) := fun n ↦
    have := hfree n
    inferInstance
  exact ⟨Q.cochainComplex, Q.π', kFlat_of_flat.{u, u} Q.cochainComplex 0, inferInstance,
    hfree, inferInstance⟩

end CochainComplex.KFlat

end

end
