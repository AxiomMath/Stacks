module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AcyclicTwistResolution

/-!
# Twisted traces computed on acyclic resolutions

Let `P : 𝒞 ⥤ 𝒞`, `F₁ : 𝒞 ⥤ 𝒟` and `F₂ : 𝒟 ⥤ Mod_R` be as in
`CategoryTheory.Functor.derivedTwistEndo`. The trace of the derived endomorphism of
`RF₂(RF₁(K))` attached to a twist `τ : K ⟶ P(K)` is computed by
`CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_eq` on a resolution of `K` by a
bounded below complex of injectives. The same holds for a quasi-isomorphism `ψ : K ⟶ T` into any
bounded below complex on which the comparison `F₂(F₁(T)) ⟶ RF₂(RF₁(T))` is invertible, for
instance one whose terms are `F₁`-acyclic with `F₂`-acyclic images.

This is needed when the resolution is the image of an injective resolution under a functor which
does not preserve injectives, as in Step 7 of the proof of [Stacks, Tag 03UG], where the
resolution of `Hom_{A[G]}(M^*, L)` is `Hom_{A[G]}(M^*, I^•)` for an injective resolution `I^•`
of `L`.

## Main results

* `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_isIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u v u₁ v₁

namespace CategoryTheory.Functor

section Twist

variable {C D : Type u₁} {E : Type*} [Category.{v₁} C] [Category.{v₁} D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) [P.Additive] [F₁.Additive] [F₂.Additive]
  [P.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

/-- The comparison `RF₂(RF₁(K)) ≅ F₂(F₁(T))` attached to a quasi-isomorphism `K ⟶ T` into a
bounded below complex on which `F₂(F₁(T)) ⟶ RF₂(RF₁(T))` is invertible. -/
def twistResolutionIsoOfIsIso {K T : CochainComplex.Plus C} (ψ : K ⟶ T) [QuasiIso ψ.hom]
    [IsIso (twistComparison F₁ F₂ T)] :
    DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) ≅
      DerivedCategory.Q.obj (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj T)).obj :=
  haveI : IsIso (DerivedCategory.Plus.Q.map ψ) :=
    haveI : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ψ)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 ‹_›
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  DerivedCategory.Plus.ι.mapIso
    (F₂.rightDerivedFunctorPlus.mapIso
        (F₁.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ψ))) ≪≫
      (asIso (twistComparison F₁ F₂ T)).symm)

/-- **The resolution comparison intertwines the twisted endomorphism with its chain model.** -/
lemma twistResolutionIsoOfIsIso_hom_comp {K T : CochainComplex.Plus C} (ψ : K ⟶ T)
    [QuasiIso ψ.hom] [IsIso (twistComparison F₁ F₂ T)]
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) (g : T ⟶ P.mapCochainComplexPlus.obj T)
    (h : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ g)) :
    DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ) ≫
        (twistResolutionIsoOfIsIso F₁ F₂ ψ).hom =
      (twistResolutionIsoOfIsIso F₁ F₂ ψ).hom ≫
        DerivedCategory.Q.map (twistChainEndo P F₁ F₂ θ T g).hom := by
  have hn := derivedTwistEndo_naturality P F₁ F₂ θ ψ τ g h
  have hc := twistComparison_comp_derivedTwistEndo P F₁ F₂ θ T g
  have hc' : derivedTwistEndo P F₁ F₂ θ T g ≫ CategoryTheory.inv (twistComparison F₁ F₂ T) =
      CategoryTheory.inv (twistComparison F₁ F₂ T) ≫
        DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  show DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ =
    DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  show derivedTwistEndo P F₁ F₂ θ K τ ≫ (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T)) =
    (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T)) ≫
      DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g)
  rw [reassoc_of% hn, hc', Category.assoc]

end Twist

section Trace

variable {R : Type u} [Ring R] {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
  [Abelian C] [Abelian D] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ ModuleCat.{max u v} R) [P.Additive] [F₁.Additive]
  [F₂.Additive] [P.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

/-- **The trace of a twisted endomorphism is computed on any resolution on which the
derived functors are computed termwise.** For a quasi-isomorphism `ψ : K ⟶ T` with
`F₂(F₁(T)) ⟶ RF₂(RF₁(T))` invertible and twists `τ` of `K` and `g` of `T` compatible along `ψ` in
the derived category, the trace of the derived endomorphism of `RF₂(RF₁(K))` attached to `τ` is
the trace of the componentwise endomorphism `F₂(F₁(g) ≫ θ)` of `F₂(F₁(T))`. -/
theorem perfectDerivedTrace_derivedTwistEndo_eq_of_isIso {K T : CochainComplex.Plus C}
    (ψ : K ⟶ T) [QuasiIso ψ.hom] [IsIso (twistComparison F₁ F₂ T)]
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) (g : T ⟶ P.mapCochainComplexPlus.obj T)
    (h : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ g))
    (hK : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)))))
    (hT : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj T)).obj)) :
    perfectDerivedTrace R ⟨_, hK⟩
        (DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ)) =
      perfectDerivedTrace R ⟨_, hT⟩
        (DerivedCategory.Q.map (twistChainEndo P F₁ F₂ θ T g).hom) :=
  perfectDerivedTrace_congr R _ _ (twistResolutionIsoOfIsIso F₁ F₂ ψ) _ _
    (twistResolutionIsoOfIsIso_hom_comp P F₁ F₂ θ ψ τ g h)

end Trace

end CategoryTheory.Functor

end
