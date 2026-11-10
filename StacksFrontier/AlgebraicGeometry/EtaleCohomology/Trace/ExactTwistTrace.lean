module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace

/-!
# The twisted endomorphism when the outer functors are exact

Let `P : 𝒞 ⥤ 𝒞`, `F₁ : 𝒞 ⥤ 𝒟` and `F₂ : 𝒟 ⥤ Mod_R` be as in
`CategoryTheory.Functor.derivedTwistEndo`, and suppose that `F₁` and `F₂` are exact.  Then
`RF₂ ∘ RF₁` is computed termwise on every bounded below complex, not only on complexes of
injectives, and the twisted endomorphism of `RF₂(RF₁(K))` attached to a twist `τ : K ⟶ P(K)` is
the termwise endomorphism `F₂(F₁(τ) ≫ θ)` of `F₂(F₁(K))`.  In particular its trace is the trace
of that termwise endomorphism.

This is the situation of Step 2 of the proof of [Stacks, Tag 03UG]: for a scheme `Z` finite over
the finite field `k`, the structure morphism `Z_k̄ ⟶ Spec k̄` is finite, so its direct image is
exact, and global sections over the spectrum of an algebraically closed field are exact; so
`RΓ(Z_k̄, -)` together with the Frobenius acting on it is computed by global sections of the
complex itself.

## Main results

* `CategoryTheory.Functor.isIso_twistComparison_of_exact` — the comparison
  `F₂(F₁(K)) ⟶ RF₂(RF₁(K))` is invertible on every bounded below complex.
* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_exact` — the trace of the
  twisted endomorphism is the trace of the termwise endomorphism.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 2.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard

universe u v u₁ v₁

namespace CategoryTheory.Functor

/-- Perfectness is invariant under isomorphism in the derived category. -/
lemma isPerfect_iff_of_iso {R : Type u} [Ring R] {K L : DerivedCategory (ModuleCat.{v} R)}
    (e : K ≅ L) : StacksDraft.Perfect.IsPerfect K ↔ StacksDraft.Perfect.IsPerfect L := by
  have key : ∀ {K L : DerivedCategory (ModuleCat.{v} R)}, (K ≅ L) →
      StacksDraft.Perfect.IsPerfect K → StacksDraft.Perfect.IsPerfect L := by
    rintro K L e ⟨P, a, b, h₁, h₂, h₃, h₄, ⟨e'⟩⟩
    exact ⟨P, a, b, h₁, h₂, h₃, h₄, ⟨e.symm ≪≫ e'⟩⟩
  exact ⟨key e, key e.symm⟩

section Exact

variable {R : Type u} [Ring R] {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R) [P.Additive] [F₁.Additive]
  [F₂.Additive] [P.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

/-- For exact `F₁` and `F₂` the comparison `F₂(F₁(K)) ⟶ RF₂(RF₁(K))` is invertible on every
bounded below complex: every object is right acyclic for an exact functor, so both units are
invertible by Leray's acyclicity lemma. -/
lemma isIso_twistComparison_of_exact (K : CochainComplex.Plus C) :
    IsIso (twistComparison F₁ F₂ K) := by
  have h₁ : IsIso ((mapCochainComplexPlusDerivedUnit F₁).app K) :=
    Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app F₁ K
      fun n => rightAcyclic_of_exact F₁ _
  have h₂ : IsIso ((mapCochainComplexPlusDerivedUnit F₂).app (F₁.mapCochainComplexPlus.obj K)) :=
    Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app F₂ _
      fun n => rightAcyclic_of_exact F₂ _
  rw [twistComparison]
  infer_instance

/-- The comparison `RF₂(RF₁(K)) ≅ F₂(F₁(K))` for exact `F₁` and `F₂`, in the unbounded derived
category of `R`-modules. -/
def exactTwistIso (K : CochainComplex.Plus C) :
    DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) ≅
      DerivedCategory.Q.obj (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj K)).obj :=
  have := isIso_twistComparison_of_exact F₁ F₂ K
  DerivedCategory.Plus.ι.mapIso (asIso (twistComparison F₁ F₂ K)).symm

/-- The comparison for exact `F₁` and `F₂` intertwines the twisted endomorphism with the
termwise endomorphism `F₂(F₁(τ) ≫ θ)`. -/
lemma exactTwistIso_hom_comp (K : CochainComplex.Plus C)
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) :
    DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ) ≫
        (exactTwistIso F₁ F₂ K).hom =
      (exactTwistIso F₁ F₂ K).hom ≫
        DerivedCategory.Q.map (twistChainEndo P F₁ F₂ θ K τ).hom := by
  have := isIso_twistComparison_of_exact F₁ F₂ K
  have hc := twistComparison_comp_derivedTwistEndo P F₁ F₂ θ K τ
  have hc' : derivedTwistEndo P F₁ F₂ θ K τ ≫ CategoryTheory.inv (twistComparison F₁ F₂ K) =
      CategoryTheory.inv (twistComparison F₁ F₂ K) ≫
        DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ K τ) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hc]
    simp
  change DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ =
    DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ K τ))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- Perfectness of `RF₂(RF₁(K))` is perfectness of the termwise complex `F₂(F₁(K))`, for exact
`F₁` and `F₂`. -/
lemma isPerfect_twist_iff_of_exact (K : CochainComplex.Plus C) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))) ↔
      StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Q.obj
          (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj K)).obj) :=
  isPerfect_iff_of_iso (exactTwistIso F₁ F₂ K)

/-- **The trace of the twisted endomorphism for exact `F₁` and `F₂`** is the trace of the termwise
endomorphism `F₂(F₁(τ) ≫ θ)` of `F₂(F₁(K))`. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq_of_exact (K : CochainComplex.Plus C)
    (τ : K ⟶ P.mapCochainComplexPlus.obj K)
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))))) :
    perfectDerivedTrace R ⟨_, hK⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ)) =
      perfectDerivedTrace R ⟨_, (isPerfect_twist_iff_of_exact F₁ F₂ K).1 hK⟩
        (DerivedCategory.Q.map (twistChainEndo P F₁ F₂ θ K τ).hom) :=
  perfectDerivedTrace_congr R _ _ (exactTwistIso F₁ F₂ K) _ _
    (exactTwistIso_hom_comp P F₁ F₂ θ K τ)

end Exact

end CategoryTheory.Functor

end
