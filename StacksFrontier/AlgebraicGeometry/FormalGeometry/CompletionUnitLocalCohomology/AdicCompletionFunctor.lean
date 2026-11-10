module

public import StacksFrontier.AlgebraicGeometry.Algebraization.AnnihilatorCompletedLocalCohomology
public import StacksFrontier.Homology.DerivedComplete.PseudoCoherentComplete
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.CompletedLocalCohomologyDegreeZero
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.UliftAdicQuotient

/-!
# The completion unit on local cohomology: derived completion as a reflection

Derived `I`-adic completion as an endofunctor of `D(A)`, namely `Dualizing.derivedCompletion`
followed by the inclusion of the derived `I`-complete objects, together with its unit, its
linearity, and the identification of the completion with the Koszul derived limit of
Stacks 0920.

## Main definitions

* `Stacks.Algebraization.adicCompletionFunctor` — derived `I`-adic completion as an endofunctor
  of `D(A)`.
* `Stacks.Algebraization.adicCompletionUnit` — the unit of that reflection.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-! ### Formal lemmas on units of reflections -/

/-- A map between two objects both identified with the same `P`, normalized by a monomorphism
out of `P`, is invertible. -/
private theorem isIso_of_normalized_comparisons
    {C : Type*} [Category C] {X Y P V W : C}
    (f : X ⟶ Y) (e : X ≅ P) (e' : Y ≅ P)
    (inc : P ⟶ V) (u : V ⟶ W) [Mono inc] [Mono u]
    {a : X ⟶ V} {b : Y ⟶ W}
    (he : e.hom ≫ inc = a) (he' : e'.hom ≫ inc ≫ u = b)
    (hn : f ≫ b = a ≫ u) : IsIso f := by
  have h : f ≫ e'.hom = e.hom := by
    apply (cancel_mono inc).1
    apply (cancel_mono u).1
    simpa only [Category.assoc, he', he] using hn
  exact IsIso.of_isIso_fac_right h

/-- Naturality of a unit transfers invertibility along an arrow inverted by the two functors. -/
public theorem isIso_map_unit_of_naturality
    {C D : Type*} [Category C] [Category D]
    (H : C ⥤ D) (T : C ⥤ C) (η : 𝟭 C ⟶ T)
    {X Y : C} (g : X ⟶ Y)
    [IsIso (H.map g)] [IsIso (H.map (T.map g))] [IsIso (H.map (η.app X))] :
    IsIso (H.map (η.app Y)) := by
  have h : H.map g ≫ H.map (η.app Y) = H.map (η.app X) ≫ H.map (T.map g) := by
    rw [← H.map_comp, ← H.map_comp]
    exact congrArg H.map (η.naturality g)
  exact IsIso.of_isIso_fac_left h

/-- Composing with the unit is a bijection on maps into a derived-complete target, provided the
unit is invertible there and the functor inverts the unit at the source. -/
private theorem completion_hom_bijective
    {C : Type*} [Category C]
    (completion : C ⥤ C) (unit : 𝟭 C ⟶ completion)
    (source target : C) [IsIso (unit.app target)]
    [Epi (completion.map (unit.app source))] :
    Function.Bijective (fun map : completion.obj source ⟶ target => unit.app source ≫ map) := by
  refine ⟨fun g h equality => ?_, fun map => ⟨completion.map map ≫ inv (unit.app target), ?_⟩⟩
  · have mapEquality : completion.map g = completion.map h := by
      apply (cancel_epi (completion.map (unit.app source))).1
      simpa only [Functor.map_comp] using congrArg completion.map equality
    have hg : g ≫ unit.app target =
        unit.app (completion.obj source) ≫ completion.map g := by
      simpa using unit.naturality g
    have hh : h ≫ unit.app target =
        unit.app (completion.obj source) ≫ completion.map h := by
      simpa using unit.naturality h
    apply (cancel_mono (unit.app target)).1
    rw [hg, hh, mapEquality]
  · change unit.app source ≫ (completion.map map ≫ inv (unit.app target)) = map
    rw [← Category.assoc]
    have hm : unit.app source ≫ completion.map map = map ≫ unit.app target := by
      simpa using (unit.naturality map).symm
    rw [hm]
    simp

/-- A functor whose unit admits a left inverse after composing is linear. -/
private theorem map_smul_of_unit_hom_injective
    {R : Type*} [Semiring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (F : C ⥤ C) (η : 𝟭 C ⟶ F) {X Y : C}
    (hη : Function.Injective (fun g : F.obj X ⟶ F.obj Y => η.app X ≫ g))
    (a : R) (f : X ⟶ Y) : F.map (a • f) = a • F.map f := by
  apply hη
  change η.app X ≫ F.map (a • f) = η.app X ≫ (a • F.map f)
  rw [← η.naturality, Functor.id_map]
  simpa only [Functor.id_map, Linear.smul_comp, Linear.comp_smul] using
    congrArg (fun g => a • g) (η.naturality f)

/-! ### Derived completion as a reflection -/

section Completion

variable {A : Type u} [CommRing A]

/-- Derived `I`-adic completion as an endofunctor of `D(A)`: the reflection onto the derived
`I`-complete objects, followed by the inclusion of that subcategory. -/
abbrev adicCompletionFunctor (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Dualizing.derivedCompletion A I hI ⋙ (Dualizing.derivedCompleteProperty A I).ι

/-- The adjunction presenting derived `I`-adic completion as a reflection. -/
abbrev adicCompletionAdjunction (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Dualizing.derivedCompletion.{u, u} A I hI ⊣ (Dualizing.derivedCompleteProperty A I).ι :=
  (Dualizing.derivedCompletionReflection A I hI).2

/-- The unit `K ⟶ K^∧` of derived `I`-adic completion. -/
abbrev adicCompletionUnit (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    𝟭 (DerivedCategory (ModuleCat.{u} A)) ⟶ adicCompletionFunctor A I hI :=
  (adicCompletionAdjunction A I hI).unit

/-- The counit of the reflection is invertible, the inclusion of the derived complete objects
being fully faithful. -/
private theorem isIso_completionAdjunction_counit (I : Ideal A) (hI : I.FG)
    (Y : Dualizing.DerivedCompleteDerivedCategory.{u, u} A I) :
    IsIso ((adicCompletionAdjunction A I hI).counit.app Y) := by
  let := (Dualizing.derivedCompleteProperty.{u, u} A I).fullyFaithfulι
  infer_instance

/-- The unit of derived completion is invertible at a derived complete object. -/
theorem isIso_completionUnit_of_derivedComplete (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{u} A)) (hX : IsDerivedComplete I X) :
    IsIso ((adicCompletionUnit A I hI).app X) := by
  let Y : Dualizing.DerivedCompleteDerivedCategory.{u, u} A I := ⟨X, hX⟩
  have hc := isIso_completionAdjunction_counit I hI Y
  set g : (adicCompletionFunctor A I hI).obj X ⟶ X :=
    (Dualizing.derivedCompleteProperty A I).ι.map
      ((adicCompletionAdjunction A I hI).counit.app Y) with hg
  have hmap : IsIso g := by
    rw [hg]
    infer_instance
  have htri : (adicCompletionUnit A I hI).app X ≫ g = 𝟙 X :=
    (adicCompletionAdjunction A I hI).right_triangle_components Y
  have := IsIso.id X
  exact IsIso.of_isIso_fac_right htri

/-- Derived completion inverts its own unit. -/
theorem isIso_completionFunctor_map_completionUnit (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((adicCompletionFunctor A I hI).map ((adicCompletionUnit A I hI).app X)) := by
  have hc := isIso_completionAdjunction_counit I hI ((Dualizing.derivedCompletion A I hI).obj X)
  have htri := (adicCompletionAdjunction A I hI).left_triangle_components X
  have := IsIso.id ((Dualizing.derivedCompletion A I hI).obj X)
  have hL : IsIso ((Dualizing.derivedCompletion A I hI).map ((adicCompletionUnit A I hI).app X)) :=
    IsIso.of_isIso_fac_right htri
  change IsIso ((Dualizing.derivedCompleteProperty A I).ι.map
    ((Dualizing.derivedCompletion A I hI).map ((adicCompletionUnit A I hI).app X)))
  infer_instance

/-- Composing with the unit identifies maps out of the completion with maps out of the object,
for every derived complete target. -/
theorem completionUnit_comp_bijective (I : Ideal A) (hI : I.FG)
    (X E : DerivedCategory (ModuleCat.{u} A)) (hE : IsDerivedComplete I E) :
    Function.Bijective (fun g : (adicCompletionFunctor A I hI).obj X ⟶ E =>
      (adicCompletionUnit A I hI).app X ≫ g) := by
  have h₁ : IsIso ((adicCompletionUnit A I hI).app E) :=
    isIso_completionUnit_of_derivedComplete I hI _ hE
  have h₂ : IsIso ((adicCompletionFunctor A I hI).map ((adicCompletionUnit A I hI).app X)) :=
    isIso_completionFunctor_map_completionUnit I hI X
  exact completion_hom_bijective (adicCompletionFunctor A I hI) (adicCompletionUnit A I hI) X E

/-- Two reflections onto the same full subcategory agree, compatibly with their units. -/
theorem exists_iso_of_reflections {C : Type*} [Category C]
    (P : ObjectProperty C) (F G : C ⥤ C) (ηF : 𝟭 C ⟶ F) (ηG : 𝟭 C ⟶ G)
    (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X))
    (bF : ∀ X E, P E → Function.Bijective (fun g : F.obj X ⟶ E => ηF.app X ≫ g))
    (bG : ∀ X E, P E → Function.Bijective (fun g : G.obj X ⟶ E => ηG.app X ≫ g))
    (X : C) : ∃ e : F.obj X ≅ G.obj X, ηF.app X ≫ e.hom = ηG.app X := by
  obtain ⟨α, hα⟩ := (bF X (G.obj X) (hG X)).2 (ηG.app X)
  obtain ⟨β, hβ⟩ := (bG X (F.obj X) (hF X)).2 (ηF.app X)
  change ηF.app X ≫ α = ηG.app X at hα
  change ηG.app X ≫ β = ηF.app X at hβ
  refine ⟨⟨α, β, ?_, ?_⟩, hα⟩
  · refine (bF X (F.obj X) (hF X)).1 (a₁ := α ≫ β) (a₂ := 𝟙 _) ?_
    change ηF.app X ≫ α ≫ β = ηF.app X ≫ 𝟙 _
    rw [← Category.assoc, hα, hβ, Category.comp_id]
  · refine (bG X (G.obj X) (hG X)).1 (a₁ := β ≫ α) (a₂ := 𝟙 _) ?_
    change ηG.app X ≫ β ≫ α = ηG.app X ≫ 𝟙 _
    rw [← Category.assoc, hβ, hα, Category.comp_id]

/-- **The Čech model of derived completion agrees with the reflection model.** Both are
reflections of `D(A)` onto the derived `I`-complete objects, so they are isomorphic. -/
theorem exists_iso_derivedCompletionFunctor_completionFunctor
    (I : Ideal A) (hI : I.FG) {r : ℕ} (gen : Fin r → A)
    (hgen : Ideal.span (Set.range gen) = I) (X : DerivedCategory (ModuleCat.{u} A)) :
    ∃ e : (DerivedCompletion.derivedCompletionFunctor A gen).obj X ≅
      (adicCompletionFunctor A I hI).obj X,
      (DerivedCompletion.derivedCompletionUnit A gen).app X ≫ e.hom =
        (adicCompletionUnit A I hI).app X := by
  obtain ⟨hcech, bcech⟩ := DerivedCompletion.derivedCompletion_isReflection A gen
  refine exists_iso_of_reflections (Dualizing.derivedCompleteProperty A I)
    (DerivedCompletion.derivedCompletionFunctor A gen) (adicCompletionFunctor A I hI)
    (DerivedCompletion.derivedCompletionUnit A gen) (adicCompletionUnit A I hI)
    (fun Y => by rw [← hgen]; exact hcech Y)
    (fun Y => ((Dualizing.derivedCompletion A I hI).obj Y).property)
    (fun Y E hE => bcech Y E (by rw [hgen]; exact hE))
    (fun Y E hE => completionUnit_comp_bijective I hI Y E hE) X

/-- Derived completion is `A`-linear. -/
theorem completionFunctor_map_smul (I : Ideal A) (hI : I.FG)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (a : A) (f : X ⟶ Y) :
    (adicCompletionFunctor A I hI).map (a • f) = a • (adicCompletionFunctor A I hI).map f :=
  map_smul_of_unit_hom_injective (adicCompletionFunctor A I hI) (adicCompletionUnit A I hI)
    (completionUnit_comp_bijective I hI X ((adicCompletionFunctor A I hI).obj Y)
      ((Dualizing.derivedCompletion A I hI).obj Y).property).1 a f

section KoszulDerivedLimit

attribute [local instance] Dualizing.AdicQuotientComparison.derivedCategoryHasProductsNat

open CategoryTheory.Pretriangulated in
/-- **Derived `I`-adic completion is the Koszul derived limit of Stacks 0920.** For every finite
family `f` generating `I`, every derived tensor product `T` and every `K` in `D(A)`, the
completion `K^∧` is a derived limit of the tower `n ↦ K ⊗ᴸ K(A, fⁿ)` of derived tensor products
of `K` with the Koszul complexes on the powers of `f`.

Stacks 0920, `AdicKoszulAdjunction.koszulPowerDerivedLimit_isLeftAdjoint`, produces *some* left
adjoint of the inclusion of the derived `I`-complete objects satisfying this clause, while
`Dualizing.derivedCompletionReflection` chooses such an adjoint and keeps only the adjunction.
Left adjoints of one functor are isomorphic, so the discarded clause transports onto the chosen
reflector `adicCompletionFunctor`, and it transports for *every* generating family and derived
tensor product, not only for the ones the choice was made with. -/
theorem isDerivedLimit_adicCompletionFunctor (I : Ideal A) (hI : I.FG)
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct (ULift.{u} A))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDerivedLimit (AdicKoszul.tensorKoszulPowerSystem f T K)
      ((AdicKoszul.derivedUniverseLift A).obj ((adicCompletionFunctor A I hI).obj K)) := by
  subst hf
  obtain ⟨L, ⟨adjL⟩, hL⟩ := AdicKoszulAdjunction.koszulPowerDerivedLimit_isLeftAdjoint A f T
  exact Dualizing.AdicQuotientComparison.isDerivedLimit_of_iso
    ((AdicKoszul.derivedUniverseLift A).mapIso
      ((Dualizing.derivedCompleteProperty A (Ideal.span (Set.range f))).ι.mapIso
        ((adjL.leftAdjointUniq (adicCompletionAdjunction A _ hI)).app K))) (hL K)

end KoszulDerivedLimit

end Completion

end Stacks.Algebraization

end
