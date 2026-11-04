module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Homology.TwoTermComplex.Ext
public import StacksFrontier.Homology.TwoTermComplex.ExtAnnihilationFactorization
public import StacksFrontier.Homology.TwoTermComplex.Morphisms

/-!
# A scalar acting by zero on a two-term complex in the derived category

Let `R` be a commutative ring and let `L = (L⁻¹ --d--> L⁰)` be a cochain complex of
`R`-modules concentrated in degrees `-1` and `0`.  For a scalar `f : R` the condition

`f • 𝟙 L = 0 in D(R)`

is strictly stronger than annihilation of `Ext¹_R(L, -)` by `f`: the latter asks only that
multiplication by `f` on `L⁻¹` factor through `d` (Stacks 0G9F, recorded in
`TwoTermComplex.smul_ext_one_eq_zero_iff_exists_factorization`), whereas the former asks that
the chain map `f • 𝟙 L` be null-homotopic.  For `L` with projective degree-zero term this file
shows that the two conditions differ by exactly the second half of the homotopy relation:
`f • 𝟙 L` vanishes in `D(R)` precisely when there is a single map `s : L⁰ → L⁻¹` with

`d ≫ s = f • 𝟙 L⁻¹`  and  `s ≫ d = f • 𝟙 L⁰`.

That `L⁰` is projective is what makes the derived statement detect a homotopy: morphisms out of
`L` in `D(R)` are then homotopy classes of chain maps, which is Stacks 0ALN part (1), used here
through its part (4).

The criterion is what makes `f • 𝟙 L = 0` *transportable*.  Being the existence of concrete
module maps it survives any construction applied termwise — base change along a ring map, in
particular — and the sufficiency direction needs no projectivity, so the transported data
proves the transported statement.  This is the derived-category half of Stacks 0AK2 and 0GB2,
and it is the form in which the hypothesis of rig-étaleness (Stacks 0GAY) is usable.

## Main results

* `TwoTermComplex.smul_id_Q_obj_eq_zero_iff_exists_factorization`: the criterion.
* `TwoTermComplex.smul_id_Q_obj_eq_zero_of_factorization`: its sufficiency half, which needs no
  projectivity and is therefore the half that consumes transported data.
* `TwoTermComplex.smul_id_eq_zero_of_comparison`: the criterion through a comparison morphism
  which is an `H⁰`-isomorphism and an `H⁻¹`-epimorphism, by Stacks 0G9I.
* `TwoTermComplex.nonempty_homotopy_of_twoTerm_components`: a homotopy between two chain maps
  out of a two-term complex from its single surviving component.

## References

* [The Stacks Project, Lemma 15.86.4 (0ALN)](https://stacks.math.columbia.edu/tag/0ALN)
* [The Stacks Project, Lemma 15.86.8 (0G9I)](https://stacks.math.columbia.edu/tag/0G9I)
* [Stacks Project, Tag 0AK2](https://stacks.math.columbia.edu/tag/0AK2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace TwoTermComplex

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- A homotopy between two chain maps out of a complex concentrated in degrees `-1` and `0`
from its one surviving component `h : K⁰ → L⁻¹`: the homotopy relation in degree `-1` reads
`f⁻¹ = d_K ≫ h + g⁻¹` and in degree `0` it reads `f⁰ = h ≫ d_L + g⁰`, and in every other
degree the source vanishes. -/
public theorem nonempty_homotopy_of_twoTerm_components
    {K L : CochainComplex (ModuleCat.{v} R) ℤ}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    {f g : K ⟶ L} (h : K.X 0 ⟶ L.X (-1))
    (hneg : f.f (-1) = K.d (-1) 0 ≫ h + g.f (-1))
    (hzero : f.f 0 = h ≫ L.d (-1) 0 + g.f 0) :
    Nonempty (Homotopy f g) := by
  classical
  let H : ∀ i j, K.X i ⟶ L.X j := fun i j =>
    if hi : i = 0 then if hj : j = -1 then
      eqToHom (congrArg K.X hi) ≫ h ≫ eqToHom (congrArg L.X hj.symm)
    else 0 else 0
  refine ⟨{ hom := H, zero := ?_, comm := ?_ }⟩
  · intro i j hij
    dsimp [H]
    split_ifs with hi hj
    · subst i; subst j
      exact (hij (by decide)).elim
    all_goals rfl
  · intro i
    by_cases hi1 : i = -1
    · subst i
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-2) (-1) by decide)]
      simpa [H] using hneg
    by_cases hi0 : i = 0
    · subst i
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel 0 1 by decide),
        prevD_eq _ (show (ComplexShape.up ℤ).Rel (-1) 0 by decide)]
      simpa [H] using hzero
    have hzK : IsZero (K.X i) := by
      rcases lt_or_gt_of_ne hi0 with hi | hi
      · exact K.isZero_of_isStrictlyGE (-1) i (by omega)
      · exact K.isZero_of_isStrictlyLE 0 i hi
    exact hzK.eq_of_src _ _

/-- A map `s : L⁰ → L⁻¹` with `d ≫ s = f • 𝟙 L⁻¹` and `s ≫ d = f • 𝟙 L⁰` is a null-homotopy of
`f • 𝟙 L`, so `f` acts by zero on `L` in the derived category.

No projectivity is needed for this direction, which is why it is the half that applies to data
transported from another ring. -/
public theorem smul_id_Q_obj_eq_zero_of_factorization (f : R)
    (L : CochainComplex (ModuleCat.{v} R) ℤ) [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    (s : L.X 0 ⟶ L.X (-1))
    (hneg : L.d (-1) 0 ≫ s = f • 𝟙 (L.X (-1)))
    (hzero : s ≫ L.d (-1) 0 = f • 𝟙 (L.X 0)) :
    f • 𝟙 (DerivedCategory.Q.obj L) = 0 := by
  obtain ⟨H⟩ := nonempty_homotopy_of_twoTerm_components (f := f • 𝟙 L) (g := 0) s
    (by simpa using hneg.symm) (by simpa using hzero.symm)
  simpa using DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{v} R) H

variable [Small.{v} R]

/-- If `f` acts by zero on a two-term complex `L` with projective degree-zero term in the
derived category, then the chain map `f • 𝟙 L` is null-homotopic, and its homotopy is a single
map `s : L⁰ → L⁻¹` satisfying both halves of the homotopy relation.

Morphisms out of `L` in `D(R)` are homotopy classes of chain maps because `L⁰` is projective
and `L` vanishes below degree `-1`; this is **Stacks 0ALN**, applied in the form of its part
(4) to the two representatives `f • 𝟙 L` and `0` of the zero morphism. -/
public theorem exists_factorization_of_smul_id_Q_obj_eq_zero (f : R)
    (L : CochainComplex (ModuleCat.{v} R) ℤ) [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Projective (L.X 0)] (h : f • 𝟙 (DerivedCategory.Q.obj L) = 0) :
    ∃ s : L.X 0 ⟶ L.X (-1),
      L.d (-1) 0 ≫ s = f • 𝟙 (L.X (-1)) ∧ s ≫ L.d (-1) 0 = f • 𝟙 (L.X 0) := by
  have hpos : ∀ i : ℤ, 0 < i → IsZero (L.X i) := fun i hi =>
    L.isZero_of_isStrictlyLE 0 i hi
  have hneg3 : ∀ i ≤ (-3 : ℤ), IsZero (L.X i) := fun i hi =>
    L.isZero_of_isStrictlyGE (-1) i (by omega)
  have hm2 : IsZero (L.X (-2)) := L.isZero_of_isStrictlyGE (-1) (-2) (by omega)
  have hQ : DerivedCategory.Q.map (f • 𝟙 L) = 0 := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, h]
  obtain ⟨h0, hm1, -, hrel1, hrel0⟩ :=
    TwoTermComplexExt.exists_homotopy_components_of_Q_map_eq L L hpos ‹_› hneg3
      (0 : TwoTermComplexExt.HomD L L) 0 (f • 𝟙 L) 0 hQ (by simp)
      (hm2.eq_zero_of_tgt _) (by simp)
  have hf : ∀ i, (f • 𝟙 L).f i = f • 𝟙 (L.X i) := by simp
  refine ⟨-h0, ?_, ?_⟩
  · have hrel : (0 : L ⟶ L).f (-1) =
        (f • 𝟙 L).f (-1) + hm1 ≫ L.d (-2) (-1) + L.d (-1) 0 ≫ h0 := hrel1
    rw [hm2.eq_zero_of_tgt hm1, hf] at hrel
    simp only [HomologicalComplex.zero_f, zero_comp, add_zero] at hrel
    rw [Preadditive.comp_neg]
    linear_combination (norm := abel) hrel
  · have hrel : (0 : L ⟶ L).f 0 = (f • 𝟙 L).f 0 + h0 ≫ L.d (-1) 0 := hrel0
    rw [hf] at hrel
    simp only [HomologicalComplex.zero_f] at hrel
    rw [Preadditive.neg_comp]
    linear_combination (norm := abel) hrel

/-- **The criterion.** For a two-term complex `L` of `R`-modules with projective degree-zero
term and a scalar `f : R`, the scalar acts by zero on `L` in the derived category exactly when
multiplication by `f` on both terms of `L` is realized by a single map `s : L⁰ → L⁻¹` against
the differential. -/
public theorem smul_id_Q_obj_eq_zero_iff_exists_factorization (f : R)
    (L : CochainComplex (ModuleCat.{v} R) ℤ) [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Projective (L.X 0)] :
    f • 𝟙 (DerivedCategory.Q.obj L) = 0 ↔
      ∃ s : L.X 0 ⟶ L.X (-1),
        L.d (-1) 0 ≫ s = f • 𝟙 (L.X (-1)) ∧ s ≫ L.d (-1) 0 = f • 𝟙 (L.X 0) :=
  ⟨exists_factorization_of_smul_id_Q_obj_eq_zero f L,
    fun ⟨s, hneg, hzero⟩ ↦ smul_id_Q_obj_eq_zero_of_factorization f L s hneg hzero⟩

omit [Small.{v} R] in
/-- If multiplication by `f` on a two-term complex `L` is realized by a map `s : L⁰ → L⁻¹`
against the differential of `L`, and `L` maps to a two-term object `K` of `D(R)` by a morphism
which is an isomorphism on `H⁰` and an epimorphism on `H⁻¹`, then `f` acts by zero on `K`.

This is the composite of the criterion with **Stacks 0G9I**. -/
public theorem smul_id_eq_zero_of_comparison (f : R) {K : DerivedCategory (ModuleCat.{v} R)}
    (L : CochainComplex (ModuleCat.{v} R) ℤ) [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj K))
    (α : DerivedCategory.Q.obj L ⟶ K)
    [IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map α)]
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) (-1)).map α)]
    (s : L.X 0 ⟶ L.X (-1))
    (hneg : L.d (-1) 0 ≫ s = f • 𝟙 (L.X (-1)))
    (hzero : s ≫ L.d (-1) 0 = f • 𝟙 (L.X 0)) :
    f • 𝟙 K = 0 :=
  smul_id_eq_zero_of_two_term_homology_map α (isZero_homology_Q_obj_of_twoTerm L) hK ‹_› ‹_› f
    (smul_id_Q_obj_eq_zero_of_factorization f L s hneg hzero)

end TwoTermComplex

end
