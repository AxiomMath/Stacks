module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ExistenceChowReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Grothendieck's existence theorem for algebraic spaces

In Situation 08B7 — `A` a Noetherian ring complete with respect to an ideal `I`,
`f : X ⟶ Spec A` a separated morphism of finite type of algebraic spaces — the completion functor
`Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, I𝒪_X)` of Stacks 08B8 is an
equivalence (`AlgebraicGeometry.Space.C1573.isEquivalence_completionFunctorProperOver`, Stacks
08BE).

Full faithfulness is Stacks 08B9.  Essential surjectivity is proved by Noetherian induction on
the closed set of points of a closed subspace of `X`: on an empty space every coherent adic system
is zero, and otherwise the Chow reduction
`AlgebraicGeometry.Space.C1573.essImage_completionFunctorProperOver_of_essSurj_closedSubspaces`
reduces to closed subspaces with strictly fewer points.  This is the source's induction over the
maximal quasi-coherent sheaf of ideals for which the statement fails, carried out on the closed
subsets of the Noetherian space `|X|` instead.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.C1573 _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.C1573 _root_.CategoryTheory.Limits.C1573
attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {A : Type u} [CommRing A] {hA : B.Contains (Spec (.of A))}

/-- **On an algebraic space with no points, completion is essentially surjective**: every module
vanishes. -/
theorem C1573.essSurj_completionFunctorProperOver_of_isEmpty [IsNoetherianRing A] (I : Ideal A)
    (X : AlgebraicSpaces B (Spec (.of A)) hA) (f : X ⟶ schemeSpace (baseObject A B hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f.hom)
    (hX : IsEmpty (points B (Spec (.of A)) hA X.1)) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).EssSurj := by
  let := fact_isLocallyNoetherian_of_baseObject X f hf
  have hz : ∀ M : Modules.{u, u} B (Spec (.of A)) hA X.1 X.2, IsZero M := fun M =>
    isZero_of_supportOfSheaf_eq_empty B (Spec (.of A)) hA X M (Set.eq_empty_of_isEmpty _)
  refine ⟨fun E => ⟨⟨⟨E.obj.obj.obj (op 0), E.obj.property.1 0⟩, E.property⟩, ⟨?_⟩⟩⟩
  refine (ObjectProperty.fullyFaithfulι _).preimageIso
    ((ObjectProperty.fullyFaithfulι _).preimageIso ?_)
  exact (Functor.isZero _ fun _ => hz _).iso (Functor.isZero _ fun _ => hz _)

/-- Two morphisms of algebraic spaces into the base are equal. -/
theorem C1573.eq_of_baseObject {X : AlgebraicSpaces B (Spec (.of A)) hA}
    (g g' : X ⟶ schemeSpace (baseObject A B hA)) : g = g' :=
  ObjectProperty.hom_ext _ ((isTerminal_yoneda_obj_base B (Spec (.of A)) hA).hom_ext _ _)

/-- **Essential surjectivity of completion on the closed subspaces of `X`**, by Noetherian
induction on their sets of points. -/
theorem C1573.essSurj_completionFunctorProperOver_of_isClosedImmersion [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsep : IsSeparated B (Spec (.of A)) hA f.hom) :
    ∀ (W : AlgebraicSpaces B (Spec (.of A)) hA) (i : W ⟶ X),
      IsClosedImmersion B (Spec (.of A)) hA i.hom →
      ∀ (g : W ⟶ schemeSpace (baseObject A B hA))
        (hg : IsLocallyOfFiniteType B (Spec (.of A)) hA g.hom),
      letI := fact_isLocallyNoetherian_of_baseObject W g hg
      (completionFunctorProperOver B (Spec (.of A)) hA W.1 (schemeSpace (baseObject A B hA)).1
        W.2 (schemeSpace (baseObject A B hA)).2 g.hom hg (baseIdealSubmodule W.1 W.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I)).EssSurj := by
  have hXN := isNoetherian_of_isFiniteType_baseObject X f hf hsep
  have : TopologicalSpace.NoetherianSpace (points B (Spec (.of A)) hA X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B (Spec (.of A)) hA X.1 X.2 hXN.1
      hXN.2.2
  let P : TopologicalSpace.Closeds (points B (Spec (.of A)) hA X.1) → Prop := fun T =>
    ∀ (W : AlgebraicSpaces B (Spec (.of A)) hA) (i : W ⟶ X),
      IsClosedImmersion B (Spec (.of A)) hA i.hom →
      Set.range (pointsMap B (Spec (.of A)) hA W.1 i.hom) ⊆ T →
      ∀ (g : W ⟶ schemeSpace (baseObject A B hA))
        (hg : IsLocallyOfFiniteType B (Spec (.of A)) hA g.hom),
      let := fact_isLocallyNoetherian_of_baseObject W g hg
      (completionFunctorProperOver B (Spec (.of A)) hA W.1 (schemeSpace (baseObject A B hA)).1
        W.2 (schemeSpace (baseObject A B hA)).2 g.hom hg (baseIdealSubmodule W.1 W.2 I)
        (isQuasicoherentOnSite_baseIdealSubmodule (X := W.1) (hX := W.2) I)).EssSurj
  have key : ∀ T, P T := by
    intro T
    induction T using WellFoundedLT.induction with
    | _ T IH =>
    intro W i hi hT g hg
    let := fact_isLocallyNoetherian_of_baseObject W g hg
    by_cases hW : IsEmpty (points B (Spec (.of A)) hA W.1)
    · exact essSurj_completionFunctorProperOver_of_isEmpty I W g hg hW
    · have hne : Nonempty (points B (Spec (.of A)) hA W.1) := not_isEmpty_iff.1 hW
      have hgi : g = i ≫ f := eq_of_baseObject _ _
      have hgf : IsFiniteType B (Spec (.of A)) hA g.hom := by
        rw [hgi]
        exact isFiniteType_comp' B (Spec (.of A)) hA i.hom f.hom X.2
          (schemeSpace (baseObject A B hA)).2
          (isFiniteType_of_isClosedImmersion B (Spec (.of A)) hA i.hom hi) hf
      have hgs : IsSeparated B (Spec (.of A)) hA g.hom := by
        rw [hgi]
        exact isSeparated_comp B (Spec (.of A)) hA i.hom f.hom
          (isSeparated_of_isClosedImmersion B (Spec (.of A)) hA i.hom hi) hsep
      have hinj := injective_pointsMap_of_isImmersion B (Spec (.of A)) hA X.2 i.hom
        (isImmersion_of_isClosedImmersion B (Spec (.of A)) hA hi)
      refine ⟨fun E => essImage_completionFunctorProperOver_of_essSurj_closedSubspaces I W g hgf hgs
        hne (fun W' j hj hj' => ?_) E⟩
      have hji : IsClosedImmersion B (Spec (.of A)) hA (j ≫ i).hom :=
        isClosedImmersion_comp B (Spec (.of A)) hA j.hom i.hom hj hi
      let T' : TopologicalSpace.Closeds (points B (Spec (.of A)) hA X.1) :=
        ⟨_, isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of A)) hA X.2 _ hji⟩
      have hle : T' ≤ T := by
        rintro _ ⟨w, rfl⟩
        refine hT ⟨pointsMap B (Spec (.of A)) hA _ j.hom w, ?_⟩
        show _ = pointsMap B (Spec (.of A)) hA _ (j.hom ≫ i.hom) w
        rw [pointsMap_comp]
        rfl
      have hlt : T' < T := by
        refine lt_of_le_of_ne hle fun heq => hj' (Set.eq_univ_of_forall fun w => ?_)
        have hw : pointsMap B (Spec (.of A)) hA _ i.hom w ∈ (T' : Set _) :=
          heq ▸ hT ⟨w, rfl⟩
        obtain ⟨w', hw'⟩ := hw
        refine ⟨w', hinj ?_⟩
        change pointsMap B (Spec (.of A)) hA _ (j.hom ≫ i.hom) w' = _ at hw'
        rw [pointsMap_comp] at hw'
        exact hw'
      exact IH T' hlt W' (j ≫ i) hji le_rfl _ _
  intro W i hi g hg
  exact key ⊤ W i hi (Set.subset_univ _) g hg

/-- **Stacks 08BE, Grothendieck's existence theorem for algebraic spaces.**  Let `A` be a
Noetherian ring complete with respect to an ideal `I`, and let `f : X ⟶ Spec A` be a separated
morphism of finite type of algebraic spaces (Situation 08B7, with `𝓘 = I 𝒪_X`).  Then the
completion functor

`Coh_{support proper over A}(𝒪_X) ⟶ Coh_{support proper over A}(X, 𝓘)`

of Stacks 08B8 is an equivalence of categories. -/
theorem C1573.isEquivalence_completionFunctorProperOver [IsNoetherianRing A] (I : Ideal A)
    [IsAdicComplete I A] (X : AlgebraicSpaces B (Spec (.of A)) hA)
    (f : X ⟶ schemeSpace (baseObject A B hA)) (hf : IsFiniteType B (Spec (.of A)) hA f.hom)
    (hsep : IsSeparated B (Spec (.of A)) hA f.hom) :
    letI := fact_isLocallyNoetherian_of_baseObject X f hf.1
    (completionFunctorProperOver B (Spec (.of A)) hA X.1 (schemeSpace (baseObject A B hA)).1 X.2
      (schemeSpace (baseObject A B hA)).2 f.hom hf.1 (baseIdealSubmodule X.1 X.2 I)
      (isQuasicoherentOnSite_baseIdealSubmodule (X := X.1) (hX := X.2) I)).IsEquivalence := by
  let := fact_isLocallyNoetherian_of_baseObject X f hf.1
  have hFF := completionFunctorProperOverFullyFaithful (X := X) I f hf.1
  have := hFF.full
  have := hFF.faithful
  have := essSurj_completionFunctorProperOver_of_isClosedImmersion I X f hf hsep X (𝟙 X)
    (isClosedImmersion_of_isIso B (Spec (.of A)) hA (𝟙 X.1)) f hf.1
  exact { }

end AlgebraicGeometry.Space

end
