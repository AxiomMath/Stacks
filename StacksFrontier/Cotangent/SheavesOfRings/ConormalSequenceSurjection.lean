module

public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTrivialPresentation

/-!
# `H^{-1}` of the naive cotangent complex of a locally surjective homomorphism

Let `a : A ⟶ B` be a locally surjective homomorphism of sheaves of commutative rings on a
topological space, with conormal sheaf `𝒞 = I/I²`.  The naive cotangent complex `NL_{B/A}` of
Stacks 08TW is formed with the canonical polynomial presentation `A[B] ⟶ B`, so its degree `-1`
term is the conormal sheaf of that presentation and not `𝒞`.  This file proves that the map
`𝒞 ⟶ NL_{B/A}.X (-1)` induced by the coefficient inclusion `A ⟶ A[B]` (a morphism of
presentations of `B` over `A`) and the differential of `NL_{B/A}` form a short exact sequence

`0 ⟶ 𝒞 ⟶ NL_{B/A}.X (-1) ⟶ NL_{B/A}.X 0 ⟶ 0`,

that is, `H^0(NL_{B/A}) = Ω_{B/A} = 0` and `H^{-1}(NL_{B/A}) = 𝒞` through that map.

Extension of scalars along any `B ⟶ D` keeps this sequence short exact, its third term being
flat (`Stacks.SheafOfModules.isFlat_naiveCotangentComplex_X_zero`,
`CategoryTheory.Sheaf.shortExact_map_towerExtendScalars`), which computes `H^{-1}` of
`NL_{B/A} ⊗_B D`.

## Main results

* `CochainComplex.shortExact_of_quasiIsoAt_of_isZero`: a quasi-isomorphism `φ : K ⟶ L` of
  cochain complexes concentrated in degrees `[-1, 0]`, with `K.X 0 = 0`, makes
  `K.X (-1) ⟶ L.X (-1) ⟶ L.X 0` short exact.
* `Stacks.SheafOfModules.shortExact_conormalSheaf_naiveCotangentComplex`: **the conormal sheaf of
  a locally surjective `a : A ⟶ B` is `H^{-1}(NL_{B/A})`, and `H^0(NL_{B/A}) = 0`**, as short
  exactness of `𝒞 ⟶ NL_{B/A}.X (-1) ⟶ NL_{B/A}.X 0`.

## Implementation notes

The main result is read off Stacks 08TL for the trivial presentation,
`Stacks.SheafOfModules.quasiIso_trivialNaiveCotangentComplexComparison`: the naive cotangent
complex of `a` itself is `𝒞 ⟶ 0`, so the comparison quasi-isomorphism identifies `𝒞` with the
cycles of `NL_{B/A}` in degree `-1` and kills its degree `0` cohomology.

## References

* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW)
* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

noncomputable section

namespace CochainComplex

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {K L : CochainComplex 𝒜 ℤ} (φ : K ⟶ L)

/-- The degree `-1` component of a chain map `φ : K ⟶ L` followed by the differential of `L`
vanishes when `K.X 0 = 0`. -/
theorem f_negOne_comp_d_eq_zero (hK₀ : IsZero (K.X 0)) : φ.f (-1) ≫ L.d (-1) 0 = 0 := by
  rw [φ.comm, hK₀.eq_of_tgt (K.d (-1) 0) 0, zero_comp]

/-- **A quasi-isomorphism out of a complex concentrated in degree `-1`.**  If `φ : K ⟶ L` is a
quasi-isomorphism in degrees `-1` and `0` between cochain complexes with `K.X (-2) = K.X 0 = 0`
and `L.X (-2) = L.X 1 = 0`, then `K.X (-1) ⟶ L.X (-1) ⟶ L.X 0` is short exact: `φ.f (-1)` is a
kernel of the differential of `L`, which is an epimorphism. -/
theorem shortExact_of_quasiIsoAt_of_isZero [QuasiIsoAt φ (-1)] [QuasiIsoAt φ 0]
    (hK₂ : IsZero (K.X (-2))) (hK₀ : IsZero (K.X 0)) (hL₂ : IsZero (L.X (-2)))
    (hL₁ : IsZero (L.X 1)) :
    (ShortComplex.mk (φ.f (-1)) (L.d (-1) 0) (f_negOne_comp_d_eq_zero φ hK₀)).ShortExact := by
  have : IsIso (K.iCycles (-1)) := K.isIso_iCycles (-1) 0 (by simp) (hK₀.eq_of_tgt _ _)
  have : IsIso (K.homologyπ (-1)) := K.isIso_homologyπ (-2) (-1) (by simp) (hK₂.eq_of_src _ _)
  have : IsIso (L.homologyπ (-1)) := L.isIso_homologyπ (-2) (-1) (by simp) (hL₂.eq_of_src _ _)
  have : IsIso (HomologicalComplex.cyclesMap φ (-1)) := by
    have : IsIso (HomologicalComplex.cyclesMap φ (-1) ≫ L.homologyπ (-1)) := by
      rw [← HomologicalComplex.homologyπ_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (L.homologyπ (-1))
  let e : L.cycles (-1) ≅ K.X (-1) :=
    (asIso (HomologicalComplex.cyclesMap φ (-1))).symm ≪≫ asIso (K.iCycles (-1))
  have he : e.hom ≫ φ.f (-1) = L.iCycles (-1) := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc,
      ← HomologicalComplex.cyclesMap_i, IsIso.inv_hom_id_assoc]
  have hker : IsLimit (KernelFork.ofι (φ.f (-1)) (f_negOne_comp_d_eq_zero φ hK₀)) :=
    IsLimit.ofIsoLimit (L.cyclesIsKernel (-1) 0 (by simp)) (Fork.ext e (by simpa using he))
  have hH : IsZero (L.homology 0) :=
    (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc 0) hK₀).of_iso
      (asIso (HomologicalComplex.homologyMap φ 0)).symm
  have hepi : Epi (L.d (-1) 0) :=
    (ShortComplex.exact_iff_epi _ (hL₁.eq_of_tgt _ _)).mp
      ((L.exactAt_iff' (-1) 0 1 (by simp) (by simp)).mp
        ((L.exactAt_iff_isZero_homology 0).mpr hH))
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ hker
      mono_f := Fork.IsLimit.mono hker
      epi_g := hepi }

end CochainComplex

namespace Stacks.SheafOfModules

open Stacks.Sites.Conormal

variable {X : TopCat.{u}} (A B : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  (a : A ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) a.hom]

/-- The map `𝒞 ⟶ NL_{B/A}.X (-1)` from the conormal sheaf of `a` to the degree `-1` term of the
naive cotangent complex, induced by the coefficient inclusion `A ⟶ A[B]`, followed by the
differential of `NL_{B/A}`, vanishes. -/
theorem trivialConormalMap_comp_naiveCotangentComplex_d :
    (trivialConormalMap A B a ≫ eqToHom
          (naiveCotangentComplex_X_negOne (Opens.grothendieckTopology X) A B a).symm) ≫
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X) A B a).d (-1) 0 =
      0 := by
  rw [trivialConormalMap_comm, trivialConormalSequence_f_eq_zero, zero_comp]
  rfl

/-- **The conormal sheaf of a locally surjective homomorphism is `H^{-1}` of its naive cotangent
complex, and `H^0` vanishes.**  Let `a : A ⟶ B` be a locally surjective homomorphism of sheaves
of commutative rings on a topological space and `𝒞` its conormal sheaf
(`Stacks.Sites.Conormal.conormalSheaf` for the presentation `a`).  Then the map
`𝒞 ⟶ NL_{B/A}.X (-1)` induced by the coefficient inclusion `A ⟶ A[B]`, a morphism of
presentations of `B` over `A`, and the differential of `NL_{B/A}` form a short exact sequence
`0 ⟶ 𝒞 ⟶ NL_{B/A}.X (-1) ⟶ NL_{B/A}.X 0 ⟶ 0`.

This is Stacks 08TL for the trivial presentation
(`Stacks.SheafOfModules.quasiIso_trivialNaiveCotangentComplexComparison`): the naive cotangent
complex of `a` itself is `𝒞 ⟶ 0`, and the comparison map to `NL_{B/A}` is a quasi-isomorphism. -/
theorem shortExact_conormalSheaf_naiveCotangentComplex :
    (ShortComplex.mk _ _ (trivialConormalMap_comp_naiveCotangentComplex_d A B a)).ShortExact := by
  have := quasiIso_trivialNaiveCotangentComplexComparison A B a
  have h := CochainComplex.shortExact_of_quasiIsoAt_of_isZero
    (trivialNaiveCotangentComplexComparison A B a)
    (isZero_trivialNaiveCotangentComplex_X_of_ne A B a (-2) (by decide))
    (isZero_trivialNaiveCotangentComplex_X_of_ne A B a 0 (by decide))
    (naiveCotangentComplex_isZero_X _ A B a (-2) (by decide) (by decide))
    (naiveCotangentComplex_isZero_X _ A B a 1 (by decide) (by decide))
  refine ShortComplex.shortExact_of_iso ?_ h
  refine ShortComplex.isoMk (eqToIso (trivialNaiveCotangentComplex_X_negOne A B a))
    (Iso.refl _) (Iso.refl _) ?_ ?_
  · simp only [trivialNaiveCotangentComplexComparison_f_negOne, Iso.refl_hom, Category.comp_id]
    rfl
  · simp

end Stacks.SheafOfModules

end
