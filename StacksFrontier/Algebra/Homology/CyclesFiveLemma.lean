module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# A five lemma for the cocycles in degree one

Let `φ : K ⟶ L` be a morphism of cochain complexes in an abelian category. In low degrees there
is an exact sequence, natural in the complex,

`Z⁰(K) ⟶ K⁰ ⟶ Z¹(K) ⟶ H¹(K) ⟶ 0`,

whose maps are the inclusion of the cocycles, the corestriction `K⁰ ⟶ Z¹(K)` of the
differential, and the projection onto cohomology. The four lemma applied to it shows that `φ`
induces an isomorphism `Z¹(K) ≅ Z¹(L)` as soon as it induces an epimorphism on `Z⁰`, an
isomorphism in degree `0`, and an isomorphism on `H¹`. When nothing maps into degree `0` the
cocycles `Z⁰` are the cohomology `H⁰`, so it suffices that `φ` is a quasi-isomorphism in degrees
`0` and `1` and an isomorphism in degree `0`.

## Main results

* `HomologicalComplex.isIso_cyclesMap_one_of_epi_of_isIso`: `Z¹(φ)` is an isomorphism when
  `Z⁰(φ)` is an epimorphism and `φ⁰` and `H¹(φ)` are isomorphisms.
* `HomologicalComplex.isIso_cyclesMap_one_of_isIso_homologyMap`: the same with `H⁰(φ)` in place
  of `Z⁰(φ)`, when the differentials into degree `0` vanish.

## References

* [Stacks Project, Tag 0EIF](https://stacks.math.columbia.edu/tag/0EIF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- The corestriction `K⁰ ⟶ Z¹(K)` of the differential commutes with the maps a morphism of
complexes induces. -/
theorem comp_toCycles_zero_one :
    φ.f 0 ≫ L.toCycles 0 1 = K.toCycles 0 1 ≫ cyclesMap φ 1 := by
  rw [← cancel_mono (L.iCycles 1), Category.assoc, Category.assoc, toCycles_i, cyclesMap_i,
    toCycles_i_assoc, Hom.comm]

/-- The inclusion of the cocycles in degree `0`, followed by the corestriction `K⁰ ⟶ Z¹(K)` of
the differential, vanishes. -/
@[reassoc (attr := simp)]
theorem iCycles_zero_comp_toCycles_zero_one (K : CochainComplex C ℤ) :
    K.iCycles 0 ≫ K.toCycles 0 1 = 0 := by
  rw [← cancel_mono (K.iCycles 1), Category.assoc, toCycles_i, iCycles_d, zero_comp]

/-- The cocycles in degree `0` are the kernel of the corestriction `K⁰ ⟶ Z¹(K)` of the
differential. -/
theorem exact_iCycles_zero_toCycles_zero_one (K : CochainComplex C ℤ) :
    (ShortComplex.mk (K.iCycles 0) (K.toCycles 0 1)
      (iCycles_zero_comp_toCycles_zero_one K)).Exact := by
  refine ShortComplex.exact_of_f_is_kernel _ ?_
  refine KernelFork.IsLimit.ofι' _ _ fun {A} k hk => ?_
  have hk' : k ≫ K.d 0 1 = 0 := by
    rw [← toCycles_i, ← Category.assoc, hk, zero_comp]
  exact ⟨K.liftCycles k 1 (by simp) hk', by simp⟩

/-- The corestriction `K⁰ ⟶ Z¹(K)` of the differential and the projection `Z¹(K) ⟶ H¹(K)` form
an exact sequence: cohomology is cocycles modulo coboundaries. -/
theorem exact_toCycles_zero_one_homologyπ_one (K : CochainComplex C ℤ) :
    (ShortComplex.mk (K.toCycles 0 1) (K.homologyπ 1) (K.toCycles_comp_homologyπ 0 1)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel 0 1 (by simp))

/-- **The five lemma for the degree-one cocycles.** Let `φ : K ⟶ L` be a morphism of cochain
complexes in an abelian category which induces an epimorphism on the cocycles in degree `0`, and
isomorphisms in degree `0` and on the cohomology in degree `1`. Then it induces an isomorphism
on the cocycles in degree `1`. -/
theorem isIso_cyclesMap_one_of_epi_of_isIso [Epi (cyclesMap φ 0)] [IsIso (φ.f 0)]
    [IsIso (homologyMap φ 1)] : IsIso (cyclesMap φ 1) := by
  have hmono : Mono (cyclesMap φ 1) := by
    let R₁ := ComposableArrows.mk₃ (K.iCycles 0) (K.toCycles 0 1) (K.homologyπ 1)
    let R₂ := ComposableArrows.mk₃ (L.iCycles 0) (L.toCycles 0 1) (L.homologyπ 1)
    let ψ : R₁ ⟶ R₂ := ComposableArrows.homMk₃ (cyclesMap φ 0) (φ.f 0) (cyclesMap φ 1)
      (homologyMap φ 1) (cyclesMap_i φ 0).symm (comp_toCycles_zero_one φ).symm
      (homologyπ_naturality φ 1)
    refine Abelian.mono_of_epi_of_mono_of_mono' ψ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [R₁.map'_comp 0 1 2]
      exact iCycles_zero_comp_toCycles_zero_one K
    · exact ComposableArrows.exact₂_mk _ _ (exact_toCycles_zero_one_homologyπ_one K)
    · exact ComposableArrows.exact₂_mk _ _ (exact_iCycles_zero_toCycles_zero_one L)
    · exact (inferInstance : Epi (cyclesMap φ 0))
    · exact (inferInstance : Mono (φ.f 0))
    · exact (inferInstance : Mono (homologyMap φ 1))
  have hepi : Epi (cyclesMap φ 1) := by
    let R₁ := ComposableArrows.mk₃ (K.toCycles 0 1) (K.homologyπ 1)
      (0 : K.homology 1 ⟶ 0)
    let R₂ := ComposableArrows.mk₃ (L.toCycles 0 1) (L.homologyπ 1)
      (0 : L.homology 1 ⟶ 0)
    let ψ : R₁ ⟶ R₂ := ComposableArrows.homMk₃ (φ.f 0) (cyclesMap φ 1) (homologyMap φ 1)
      (𝟙 0) (comp_toCycles_zero_one φ).symm (homologyπ_naturality φ 1)
      (by
        show (0 : K.homology 1 ⟶ 0) ≫ 𝟙 0 = homologyMap φ 1 ≫ (0 : L.homology 1 ⟶ 0)
        simp)
    refine Abelian.epi_of_epi_of_epi_of_mono' ψ ?_ ?_ ?_ ?_ ?_ ?_
    · refine ComposableArrows.exact₂_mk _ (by exact comp_zero) ?_
      exact (ShortComplex.exact_iff_epi _ rfl).2 (inferInstanceAs (Epi (K.homologyπ 1)))
    · exact ComposableArrows.exact₂_mk _ _ (exact_toCycles_zero_one_homologyπ_one L)
    · rw [R₂.map'_comp 1 2 3]
      exact comp_zero
    · exact (inferInstance : Epi (φ.f 0))
    · exact (inferInstance : Epi (homologyMap φ 1))
    · exact (inferInstance : Mono (𝟙 (0 : C)))
  exact isIso_of_mono_of_epi _

/-- **The five lemma for the degree-one cocycles, read on cohomology.** Let `φ : K ⟶ L` be a
morphism of cochain complexes in an abelian category whose differentials into degree `0` vanish.
If `φ` is an isomorphism in degree `0` and induces isomorphisms on cohomology in degrees `0` and
`1`, then it induces an isomorphism on the cocycles in degree `1`. -/
theorem isIso_cyclesMap_one_of_isIso_homologyMap (hK : K.d (-1) 0 = 0) (hL : L.d (-1) 0 = 0)
    [IsIso (φ.f 0)] [IsIso (homologyMap φ 0)] [IsIso (homologyMap φ 1)] :
    IsIso (cyclesMap φ 1) := by
  have := K.isIso_homologyπ (-1) 0 (by simp) hK
  have := L.isIso_homologyπ (-1) 0 (by simp) hL
  have hc : cyclesMap φ 0 = K.homologyπ 0 ≫ homologyMap φ 0 ≫ inv (L.homologyπ 0) := by
    rw [← Category.assoc, homologyπ_naturality, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have : IsIso (cyclesMap φ 0) := by rw [hc]; infer_instance
  exact isIso_cyclesMap_one_of_epi_of_isIso φ

end HomologicalComplex

end
