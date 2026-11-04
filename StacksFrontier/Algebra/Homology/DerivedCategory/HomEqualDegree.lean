module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Maps of the derived category from `D^{≤ n}` to `D^{≥ n}` are detected by `Hⁿ`

Let `C` be an abelian category and let `X` and `Y` be objects of `D(C)` with `X` in `D^{≤ n}` and
`Y` in `D^{≥ n}` for one and the same integer `n`.  The map

`Hom_{D(C)}(X, Y) ⟶ Hom_C(Hⁿ X, Hⁿ Y)`

is then injective: a morphism `X ⟶ Y` killed by `Hⁿ` is zero.

## Main results

* `DerivedCategory.eq_zero_of_isLE_of_isGE_of_homologyFunctor_map_eq_zero`: a morphism from an
  object of `D^{≤ n}` to an object of `D^{≥ n}` whose image under `Hⁿ` vanishes is zero.
* `DerivedCategory.eq_of_isLE_of_isGE_of_homologyFunctor_map_eq` and
  `DerivedCategory.injective_homologyFunctor_map_of_isLE_of_isGE`: the same, as a cancellation
  rule and as injectivity of `Hⁿ` on that `Hom`-group.

## Implementation notes

Mathlib's `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE` is the case of a *strict*
gap `n₀ < n₁`, where no hypothesis on `Hⁿ` is needed; the statements here are the remaining case
`n₀ = n₁`, where the hypothesis is exactly the vanishing of the induced map on `Hⁿ`.

The proof follows `DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE`, which is how
Mathlib proves the strict-gap case: replace `X` and `Y` by strictly bounded complexes, write the
morphism as `inv (Q.map s) ≫ Q.map g` by `DerivedCategory.right_fac_of_isStrictlyLE`, and show
that the cochain map `g` vanishes degreewise.  Away from `n` one of its two terms is a zero
object.  In degree `n` the differential of the source out of `n` and the differential of the
target into `n` both vanish, so `HomologicalComplex.iCycles` of the source and
`HomologicalComplex.homologyπ` of the target are isomorphisms there, and the hypothesis on `Hⁿ`
says precisely that `HomologicalComplex.cyclesMap g n` is zero.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

omit [HasDerivedCategory C] in
/-- A cochain map from a complex strictly supported in degrees `≤ n` to a complex strictly
supported in degrees `≥ n` is zero as soon as it is zero on `Hⁿ`: it has one possibly nonzero
component, in degree `n`, and there the hypothesis forces it to vanish. -/
theorem eq_zero_of_isStrictlyLE_of_isStrictlyGE_of_homologyMap_eq_zero
    {K L : CochainComplex C ℤ} (n : ℤ) [K.IsStrictlyLE n] [L.IsStrictlyGE n] (g : K ⟶ L)
    (hg : HomologicalComplex.homologyMap g n = 0) : g = 0 := by
  ext i
  simp only [HomologicalComplex.zero_f]
  by_cases hi : i = n
  · rw [hi]
    have hdK : K.d n (n + 1) = 0 :=
      (K.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _
    have hdL : L.d (n - 1) n = 0 :=
      (L.isZero_of_isStrictlyGE n (n - 1) (by omega)).eq_of_src _ _
    have h1 : IsIso (K.iCycles n) := K.isIso_iCycles n (n + 1) (by simp) hdK
    have h2 : IsIso (L.homologyπ n) := L.isIso_homologyπ (n - 1) n (by simp) hdL
    have h3 : HomologicalComplex.cyclesMap g n = 0 := by
      rw [← cancel_mono (L.homologyπ n), zero_comp, ← HomologicalComplex.homologyπ_naturality,
        hg, comp_zero]
    have h4 := HomologicalComplex.cyclesMap_i g n
    rw [h3, zero_comp] at h4
    rw [← cancel_epi (K.iCycles n), comp_zero, ← h4]
  · rcases lt_or_gt_of_ne hi with h | h
    · exact (L.isZero_of_isStrictlyGE n i h).eq_of_tgt _ _
    · exact (K.isZero_of_isStrictlyLE n i h).eq_of_src _ _

/-- **A morphism of `D(C)` from an object of `D^{≤ n}` to an object of `D^{≥ n}` which vanishes
on `Hⁿ` is zero.**  Mathlib's `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`
covers the case of a strict gap `n₀ < n₁`; this is the equal-degree case, where the vanishing on
`Hⁿ` is exactly what is needed. -/
theorem eq_zero_of_isLE_of_isGE_of_homologyFunctor_map_eq_zero
    {X Y : DerivedCategory C} (n : ℤ) [X.IsLE n] [Y.IsGE n] (f : X ⟶ Y)
    (hf : (homologyFunctor C n).map f = 0) : f = 0 := by
  obtain ⟨K, hK, ⟨eX⟩⟩ := X.exists_iso_Q_obj_of_isLE n
  obtain ⟨L, hL, ⟨eY⟩⟩ := Y.exists_iso_Q_obj_of_isGE n
  have := hK
  have := hL
  have key : eX.inv ≫ f ≫ eY.hom = 0 := by
    obtain ⟨K', hK', s, hs, g, hfac⟩ := right_fac_of_isStrictlyLE (eX.inv ≫ f ≫ eY.hom) n
    have := hK'
    have := hs
    have hQg : Q.map g = Q.map s ≫ eX.inv ≫ f ≫ eY.hom := by
      rw [hfac, IsIso.hom_inv_id_assoc]
    have h1 : (homologyFunctor C n).map (Q.map g) = 0 := by
      rw [hQg, Functor.map_comp, Functor.map_comp, Functor.map_comp, hf]
      simp
    have h2 := homologyFunctorFactors_hom_naturality g n
    rw [h1, zero_comp] at h2
    have hg : HomologicalComplex.homologyMap g n = 0 :=
      (cancel_epi ((homologyFunctorFactors C n).hom.app K')).1
        (h2.symm.trans comp_zero.symm)
    rw [hfac, eq_zero_of_isStrictlyLE_of_isStrictlyGE_of_homologyMap_eq_zero n g hg,
      Functor.map_zero, comp_zero]
  have hexp : f = eX.hom ≫ (eX.inv ≫ f ≫ eY.hom) ≫ eY.inv := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hexp, key, zero_comp, comp_zero]

/-- Two morphisms of `D(C)` from an object of `D^{≤ n}` to an object of `D^{≥ n}` which agree on
`Hⁿ` are equal. -/
theorem eq_of_isLE_of_isGE_of_homologyFunctor_map_eq
    {X Y : DerivedCategory C} (n : ℤ) [X.IsLE n] [Y.IsGE n] (f g : X ⟶ Y)
    (h : (homologyFunctor C n).map f = (homologyFunctor C n).map g) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_isLE_of_isGE_of_homologyFunctor_map_eq_zero n _ ?_
  rw [Functor.map_sub, h, sub_self]

/-- **`Hⁿ` is injective on morphisms from `D^{≤ n}` to `D^{≥ n}`.** -/
theorem injective_homologyFunctor_map_of_isLE_of_isGE
    (X Y : DerivedCategory C) (n : ℤ) [X.IsLE n] [Y.IsGE n] :
    Function.Injective fun f : X ⟶ Y => (homologyFunctor C n).map f :=
  fun _ _ h => eq_of_isLE_of_isGE_of_homologyFunctor_map_eq n _ _ h

end DerivedCategory

end
