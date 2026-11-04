module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldSections
public import StacksFrontier.RingTheory.TotallySplit.FiniteSeparableSplitting
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# A finite locally free étale morphism to the spectrum of a field acquires all its sections

Let `K` be a field and `f : Z ⟶ Spec K` an étale morphism which is finite locally free of rank
`d`. Then there is a finite separable extension `K'/K` over which `f` has `d` pairwise distinct
`K'`-points, that is, `d` pairwise distinct morphisms `Spec K' ⟶ Z` over `Spec K`; equivalently
`d` pairwise distinct sections of the base change `Z ×_{Spec K} Spec K' ⟶ Spec K'`.

Together with `Stacks.Morphisms.exists_eq_of_isFiniteLocallyFreeOfRank`, which says that `d`
distinct sections of a morphism of rank `d` to the spectrum of a field are *all* its sections,
this says that `K'` splits the fibre completely.

The statement is about *morphisms*, not about points of the topological space of `Z`: two
distinct `K'`-points of `Z` over `Spec K` can have the same image in `|Z|`, as they do for
`Z = Spec L` with `L/K` quadratic Galois and `K' = L`.

## Main results

* `Stacks.Morphisms.exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank`: `d`
  pairwise distinct `K'`-points of `Z` over `Spec K`, for some finite separable `K'/K`.
* `Stacks.Morphisms.exists_finiteSeparable_section_of_etale_isFiniteLocallyFreeOfRank`: the same
  read as `d` pairwise distinct sections of the base change of `f` to `Spec K'`.

## References

* [Stacks Project, Tag 00U3](https://stacks.math.columbia.edu/tag/00U3)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Stacks.Morphisms

/-- An étale morphism to the spectrum of a field which is finite locally free of rank `d` has
`d` pairwise distinct `K'`-points over the base, for some finite separable extension `K'/K`. -/
theorem exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank {K : Type u} [Field K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank f d) (hetale : Etale f) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (_ : Algebra.IsSeparable K K') (σ : Fin d → (Spec (CommRingCat.of K') ⟶ Z)),
      Function.Injective σ ∧
        ∀ k, σ k ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K K')) := by
  obtain ⟨haff, hfin, hrank⟩ := (isFiniteLocallyFreeOfRank_iff_finrank_sections_eq f d).1 hf
  have _ : IsAffine Z := isAffine_of_isAffineHom f
  let α : CommRingCat.of K ⟶ Γ(Z, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop
  let _ : Algebra K ↑Γ(Z, ⊤) := (CommRingCat.Hom.hom α).toAlgebra
  have hα : Spec.map α = Z.isoSpec.inv ≫ f := by
    rw [show α = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop from rfl, Spec.map_comp,
      ← Scheme.isoSpec_Spec_inv]
    exact Scheme.isoSpec_inv_naturality f
  have _ : Algebra.Etale K ↑Γ(Z, ⊤) := by
    refine (HasRingHomProperty.Spec_iff (P := @Etale) (φ := α)).1 ?_
    rw [hα]
    infer_instance
  subst hrank
  obtain ⟨K', instK', instAlg, instFin, instSep, w, hw⟩ :=
    Stacks.TotallySplit.exists_finiteSeparable_injective_algHom (K := K) (A := ↑Γ(Z, ⊤))
  let φ : Fin (Module.finrank K ↑Γ(Z, ⊤)) → (↑Γ(Z, ⊤) →ₐ[K] K') := fun k ↦
    (AlgHom.restrictScalars K (w k)).comp Algebra.TensorProduct.includeRight
  have hφ : Function.Injective φ := fun k l hkl ↦
    hw (Algebra.TensorProduct.ext_ring hkl)
  refine ⟨K', instK', instAlg, instFin, instSep,
    fun k ↦ Spec.map (CommRingCat.ofHom (φ k).toRingHom) ≫ Z.isoSpec.inv, ?_, ?_⟩
  · intro k l hkl
    have h1 : CommRingCat.ofHom (φ k).toRingHom = CommRingCat.ofHom (φ l).toRingHom :=
      Spec.map_injective ((cancel_mono Z.isoSpec.inv).1 hkl)
    exact hφ (AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom h1))
  · intro k
    rw [Category.assoc, hα.symm, ← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
    exact (φ k).commutes x

/-- An étale morphism `f : Z ⟶ Spec K` which is finite locally free of rank `d` acquires `d`
pairwise distinct sections of its base change along `Spec K' ⟶ Spec K`, for some finite
separable extension `K'/K`. -/
theorem exists_finiteSeparable_section_of_etale_isFiniteLocallyFreeOfRank {K : Type u} [Field K]
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of K)) (d : ℕ)
    (hf : IsFiniteLocallyFreeOfRank f d) (hetale : Etale f) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (_ : Algebra.IsSeparable K K'),
      ∃ τ : Fin d → (Spec (CommRingCat.of K') ⟶
        pullback f (Spec.map (CommRingCat.ofHom (algebraMap K K')))),
        Function.Injective τ ∧ ∀ k, τ k ≫ pullback.snd _ _ = 𝟙 _ := by
  obtain ⟨K', instK', instAlg, instFin, instSep, σ, hσinj, hσ⟩ :=
    exists_finiteSeparable_hom_of_etale_isFiniteLocallyFreeOfRank f d hf hetale
  refine ⟨K', instK', instAlg, instFin, instSep,
    fun k ↦ pullback.lift (σ k) (𝟙 _) ((hσ k).trans (Category.id_comp _).symm), ?_, ?_⟩
  · intro k l hkl
    exact hσinj ((pullback.lift_fst _ _ _).symm.trans
      ((hkl =≫ pullback.fst _ _).trans (pullback.lift_fst _ _ _)))
  · exact fun k ↦ pullback.lift_snd _ _ _

end Stacks.Morphisms

end
