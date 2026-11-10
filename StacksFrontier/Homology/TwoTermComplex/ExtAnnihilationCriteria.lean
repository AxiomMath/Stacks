module

public import StacksFrontier.Homology.TwoTermComplex.BaseChange
public import StacksFrontier.Homology.TwoTermComplex.Representative
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

/-!
# Ideal annihilation of `Ext¹` after derived base change

If an ideal annihilates every first Ext group of a two-term object, then its image annihilates
every first Ext group of the truncation of the derived base change.

## Main results

* `TwoTermComplex.ext_one_annihilated_truncGE_derivedBaseChange` (Stacks 0G9H).

## Implementation notes

The factorization criterion of Stacks 0G9F turns the annihilation hypothesis into a
factorization through a two-term representative with free degree-zero term, Stacks 0G9G
identifies the base change of such a representative with the truncation of the derived base
change, and the factorization transports along that identification with the ideal's image acting
on the base-changed module.

Derived base change is quantified over rather than modelled: the statement takes any functor with
a comparison transformation exhibiting it as a total left derived functor of termwise extension of
scalars, exactly as 0G9G does.

Both inputs are cited from conceptual modules — 0G9G from `TwoTermComplex/BaseChange.lean` and
0G9F from `TwoTermComplex/Representative.lean`, both in this cluster.

## References

* [The Stacks Project, Lemma 15.85.8 (0G9H)](https://stacks.math.columbia.edu/tag/0G9H)
-/

open CategoryTheory CategoryTheory.Limits

namespace TwoTermComplex

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0G9H.** If an ideal annihilates every degree-one Ext group from a two-term derived
object, then the extended ideal has the same property for its derived base change truncated in
degrees at least `-1`. -/
@[stacks 0G9H]
public theorem ext_one_annihilated_truncGE_derivedBaseChange
    {R : Type u} {R' : Type v} [CommRing R] [CommRing R']
    (I : Ideal R) (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K))
    (φ : R →+* R')
    (hI : ∀ (N : ModuleCat.{max u v} R) (a : R), a ∈ I →
      ∀ ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj N) 1,
        a • ξ = 0)
    (derivedBaseChange : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} R'))
    (comparison : DerivedCategory.Q ⋙ derivedBaseChange ⟶
      (ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
    [derivedBaseChange.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))] :
    let K' := ((DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R')).truncGE (-1)).obj
      (derivedBaseChange.obj K)
    ∀ (N : ModuleCat.{max u v} R') (a : R'), a ∈ Ideal.map φ I →
      ∀ ξ : DerivedCategory.Ext K'
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R') 0).obj N) 1,
        a • ξ = 0 := by
  let K' := ((DerivedCategory.TStructure.t (C := ModuleCat.{max u v} R')).truncGE (-1)).obj
    (derivedBaseChange.obj K)
  let : Algebra R R' := φ.toAlgebra
  change ∀ (N : ModuleCat.{max u v} R') (a : R'), a ∈ Ideal.map φ I →
    ∀ ξ : DerivedCategory.Ext K'
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R') 0).obj N) 1, a • ξ = 0
  obtain ⟨L, hLge, hLle, hLfree, ⟨e⟩, hfac⟩ :=
    (ext_one_annihilated_iff_twoTerm_factorization I K hK).1.mp hI
  let F := ModuleCat.extendScalars φ
  let L' := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  have hL'ge : CochainComplex.IsStrictlyGE L' (-1) := by
    refine ⟨fun i hi => F.map_isZero (hLge.isZero i hi)⟩
  have hL'le : CochainComplex.IsStrictlyLE L' 0 := by
    refine ⟨fun i hi => F.map_isZero (hLle.isZero i hi)⟩
  have hL'free : Module.Free R' (L'.X 0) := by
    dsimp [L', F]
    let := hLfree
    exact Module.Free.of_basis ((Module.Free.chooseBasis R (L.X 0)).baseChange R')
  obtain ⟨f, _hcomparison, hf⟩ :=
    twoTermBaseChange_iso_truncGE φ K L e hK
      (fun i hi₁ hi₂ => by
        let := hLge
        let := hLle
        rcases lt_or_gt_of_ne hi₂ with hi | hi
        · exact L.isZero_of_isStrictlyGE (-1) i (by omega)
        · exact L.isZero_of_isStrictlyLE 0 i hi)
      (by let := hLfree; infer_instance) derivedBaseChange comparison
  let := hf
  let e' : DerivedCategory.Q.obj L' ≅ K' := (asIso f).symm
  have hK' : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R') i).obj K') := by
    intro i hi₁ hi₂
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor _ i).mapIso e').symm
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors _ i).app L')
    let := hL'ge
    let := hL'le
    rcases lt_or_gt_of_ne hi₂ with hi | hi
    · exact (CochainComplex.exactAt_of_isGE L' (-1) i (by omega)).isZero_homology
    · exact (CochainComplex.exactAt_of_isLE L' 0 i hi).isZero_homology
  apply (ext_one_annihilated_iff_twoTerm_factorization (Ideal.map φ I) K' hK').1.mpr
  refine ⟨L', hL'ge, hL'le, hL'free, ⟨e'⟩, ?_⟩
  intro a ha
  let J : Ideal R' :=
    { carrier := {a | ∃ h : L'.X 0 ⟶ L'.X (-1), L'.d (-1) 0 ≫ h = a • 𝟙 _}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro x y ⟨hx, ehx⟩ ⟨hy, ehy⟩
        refine ⟨hx + hy, ?_⟩
        rw [Preadditive.comp_add, ehx, ehy, add_smul]
      smul_mem' := by
        rintro x y ⟨hy, ehy⟩
        refine ⟨x • hy, ?_⟩
        rw [CategoryTheory.Linear.comp_smul, ehy, smul_smul]
        rfl }
  have hmap : Ideal.map φ I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨h, eh⟩ := hfac b hb
    refine ⟨F.map h, ?_⟩
    change F.map (L.d (-1) 0) ≫ F.map h = φ b • 𝟙 _
    rw [← F.map_comp, eh]
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (1 : R') ⊗ₜ[R] (b • x) = φ b • ((1 : R') ⊗ₜ[R] x)
    rw [TensorProduct.tmul_smul]
    change (φ b * 1) ⊗ₜ[R] x = (φ b * 1) ⊗ₜ[R] x
    rfl
  exact hmap ha

end TwoTermComplex
