module

public import StacksFrontier.CategoryTheory.Abelian.PowExact
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
import all StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicObjects

/-!
# Reduction modulo `p^a` of complexes of pow-exact objects

Let `C` be an abelian category.  Reduction modulo `p^a`, `X ↦ X / p^a X`, is a functor, and on
bounded below complexes whose terms are pow-exact and killed by `p^m` it carries acyclic
complexes to acyclic complexes and quasi-isomorphisms to quasi-isomorphisms.

## Main definitions

* `CategoryTheory.Abelian.powReductionFunctor`: the reduction modulo `p^a`.

## Main results

* `CategoryTheory.Abelian.acyclic_map_powReductionFunctor`: it preserves acyclicity of bounded
  below complexes of pow-exact objects killed by `p^m`.
* `CategoryTheory.Abelian.quasiIso_map_powReductionFunctor`: it preserves quasi-isomorphisms
  between such complexes.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Abelian

open CategoryTheory Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C] (p : ℕ)

/-- **Reduction modulo `p^a`**, `X ↦ X / p^a X`, as a functor. -/
def powReductionFunctor (a : ℕ) : C ⥤ C where
  obj X := powReduction (p := p) a X
  map f := powReductionMap (p := p) a f
  map_id X := by
    ext
    simp
  map_comp f g := by
    ext
    simp

/-- Reduction modulo `p^a` is an additive functor. -/
instance (a : ℕ) : (powReductionFunctor (C := C) p a).Additive where
  map_add {X Y f g} := by
    change powReductionMap (p := p) a (f + g) = powReductionMap (p := p) a f +
      powReductionMap (p := p) a g
    ext
    simp

variable {p} {m : ℕ}

/-- **Reduction modulo `p^a` keeps a bounded below acyclic complex of pow-exact objects killed by
`p^m` acyclic.** -/
theorem acyclic_map_powReductionFunctor {a : ℕ} (ha : a ≤ m) (K : CochainComplex C ℤ) (b : ℤ)
    [K.IsStrictlyGE b] (hK : K.Acyclic) (hX : ∀ n, PowExact p m (K.X n))
    (hX' : ∀ n, (p ^ m) • 𝟙 (K.X n) = 0) :
    (((powReductionFunctor (C := C) p a).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic := by
  refine Functor.RightAcyclicCriterion.map_acyclic (powReductionFunctor (C := C) p a)
    (fun X => PowExact p m X ∧ (p ^ m) • 𝟙 X = 0)
    (fun hZ => ⟨PowExact.of_isZero hZ, hZ.eq_of_src _ _⟩)
    (fun S hS h₁ h₂ => ⟨⟨PowExact.of_shortExact hS h₁.1 h₂.1 h₂.2, ?_⟩,
      PowExact.reduction_shortExact hS h₁.1 h₂.2 ha⟩) K b hK (fun n => ⟨hX n, hX' n⟩)
  have := hS.epi_g
  rw [← cancel_epi S.g, comp_zero, ← nsmul_id_comp, h₂.2, zero_comp]

/-- **Reduction modulo `p^a` preserves quasi-isomorphisms between bounded below complexes of
pow-exact objects killed by `p^m`.** -/
theorem quasiIso_map_powReductionFunctor {a : ℕ} (ha : a ≤ m) {K L : CochainComplex C ℤ}
    (φ : K ⟶ L) [QuasiIso φ] (b : ℤ) [K.IsStrictlyGE b] [L.IsStrictlyGE b]
    (hK : ∀ n, PowExact p m (K.X n)) (hL : ∀ n, PowExact p m (L.X n))
    (hK' : ∀ n, (p ^ m) • 𝟙 (K.X n) = 0) (hL' : ∀ n, (p ^ m) • 𝟙 (L.X n) = 0) :
    QuasiIso (((powReductionFunctor (C := C) p a).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) := by
  have : (CochainComplex.mappingCone φ).IsStrictlyGE (b - 1) :=
    CochainComplex.isStrictlyGE_mappingCone φ b b _ (by omega) (by omega)
  have heq : ∀ n, (CochainComplex.mappingCone φ).X n =
      (K.X ((ComplexShape.up ℤ).next n) ⊞ L.X n) := fun n => dite_eq_left (by simp)
  have hc := acyclic_map_powReductionFunctor (C := C) ha (CochainComplex.mappingCone φ) (b - 1)
    (Functor.acyclic_mappingCone φ inferInstance)
    (fun n => by rw [heq n]; exact (hK _).biprod (hL n))
    (fun n => by
      rw [heq n]
      apply biprod.hom_ext
      · rw [nsmul_comp, Category.id_comp, ← Category.comp_id biprod.fst, ← comp_nsmul, hK',
          comp_zero, zero_comp]
      · rw [nsmul_comp, Category.id_comp, ← Category.comp_id biprod.snd, ← comp_nsmul, hL',
          comp_zero, zero_comp])
  apply Functor.quasiIso_of_acyclic_mappingCone
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hc i).isZero_homology.of_iso
    (((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso φ (powReductionFunctor p a))).symm)

end CategoryTheory.Abelian
