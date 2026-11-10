module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectImageSectionsRestrictScalarsUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveHomotopy
public import StacksFrontier.Homology.HomComplex.DerivedAdjunctionResolution
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.FunctorTrace

/-!
# Twisted endomorphisms on acyclic resolutions, and traces along a non-exact functor

Two complements to `CategoryTheory.Functor.twistResolutionIso`.

* The chain model of the twisted endomorphism of `RF₂(RF₁(K))` (see
  `CategoryTheory.Functor.derivedTwistEndo`) may be computed on any quasi-isomorphism `K ⟶ T`
  into a bounded below complex whose terms are `F₁`-acyclic with `F₁`-images `F₂`-acyclic, not
  only on an injective resolution.
* Let `Φ : Mod_R ⥤ Mod_S` be an additive functor carrying finite projective modules to finite
  projective modules, and `J` a bounded below complex of injective `R`-modules which is perfect,
  over a ring all of whose finite projective modules are injective (a quasi-Frobenius ring such
  as `(ℤ/ℓⁿ)[H]`). Then `Φ(J)` is perfect and `Tr_S(Φ(t) | Φ(J)) = Φ♮(Tr_R(t | J))` for every
  endomorphism `t` of `J`, although `Φ` need not be exact: a bounded complex `P` of finite
  projective modules representing `J` is again a bounded below complex of injectives, so
  `P ⟶ J` is a homotopy equivalence and `Φ` preserves homotopies.

These are used in Step 7 of the proof of [Stacks, Tag 03UG], with `Φ = Hom_{A[H]}(N^∨, -)`.

## Main results

* `CategoryTheory.Functor.twistAcyclicResolutionIso` and
  `CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_rightAcyclic`.
* `CategoryTheory.FilteredDerived.isPerfect_map_of_injective` and
  `CategoryTheory.FilteredDerived.perfectDerivedTrace_map_of_injective`.

## Implementation notes

The statements involve `CategoryTheory.Functor.derivedTwistEndo` and
`CategoryTheory.FilteredDerived.perfectDerivedTrace`, which are defined in the model
`HasDerivedCategory.standard`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u₁ v₁ w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.Functor

section Twist

variable {C D : Type u₁} {E : Type*} [Category.{v₁} C] [Category.{v₁} D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) [P.Additive] [F₁.Additive] [F₂.Additive]
  [P.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

/-- The comparison `F₂(F₁(K)) ⟶ RF₂(RF₁(K))` is invertible on a bounded below complex of
`F₁`-acyclic objects whose images are `F₂`-acyclic (Leray's acyclicity lemma, twice). -/
lemma isIso_twistComparison_of_rightAcyclic (K : CochainComplex.Plus C)
    (h₁ : ∀ n, F₁.rightAcyclic (K.obj.X n)) (h₂ : ∀ n, F₂.rightAcyclic (F₁.obj (K.obj.X n))) :
    IsIso (twistComparison F₁ F₂ K) := by
  have := Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic F₁ K h₁
  have := Stacks.EtaleCohomology.isIso_mapCochainComplexPlusDerivedUnit_app_of_rightAcyclic F₂
    (F₁.mapCochainComplexPlus.obj K) h₂
  rw [twistComparison]
  infer_instance

/-- The comparison `RF₂(RF₁(K)) ≅ F₂(F₁(T))` attached to a quasi-isomorphism `K ⟶ T` into a
bounded below complex of `F₁`-acyclic objects with `F₂`-acyclic images. -/
def twistAcyclicResolutionIso {K T : CochainComplex.Plus C} (ψ : K ⟶ T) [QuasiIso ψ.hom]
    (h₁ : ∀ n, F₁.rightAcyclic (T.obj.X n)) (h₂ : ∀ n, F₂.rightAcyclic (F₁.obj (T.obj.X n))) :
    DerivedCategory.Plus.ι.obj (F₂.rightDerivedFunctorPlus.obj
        (F₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))) ≅
      DerivedCategory.Q.obj (F₂.mapCochainComplexPlus.obj (F₁.mapCochainComplexPlus.obj T)).obj :=
  haveI : IsIso (DerivedCategory.Plus.Q.map ψ) :=
    haveI : IsIso (DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map ψ)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ ψ.hom).2 ‹_›
    isIso_of_fully_faithful DerivedCategory.Plus.ι _
  haveI := isIso_twistComparison_of_rightAcyclic F₁ F₂ T h₁ h₂
  DerivedCategory.Plus.ι.mapIso
    (F₂.rightDerivedFunctorPlus.mapIso
        (F₁.rightDerivedFunctorPlus.mapIso (asIso (DerivedCategory.Plus.Q.map ψ))) ≪≫
      (asIso (twistComparison F₁ F₂ T)).symm)

/-- **The acyclic resolution comparison intertwines the twisted endomorphism with its chain
model.** -/
lemma twistAcyclicResolutionIso_hom_comp {K T : CochainComplex.Plus C} (ψ : K ⟶ T)
    [QuasiIso ψ.hom] (h₁ : ∀ n, F₁.rightAcyclic (T.obj.X n))
    (h₂ : ∀ n, F₂.rightAcyclic (F₁.obj (T.obj.X n)))
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) (g : T ⟶ P.mapCochainComplexPlus.obj T)
    (h : DerivedCategory.Plus.Q.map (τ ≫ P.mapCochainComplexPlus.map ψ) =
      DerivedCategory.Plus.Q.map (ψ ≫ g)) :
    DerivedCategory.Plus.ι.map (derivedTwistEndo P F₁ F₂ θ K τ) ≫
        (twistAcyclicResolutionIso F₁ F₂ ψ h₁ h₂).hom =
      (twistAcyclicResolutionIso F₁ F₂ ψ h₁ h₂).hom ≫
        DerivedCategory.Q.map (twistChainEndo P F₁ F₂ θ T g).hom := by
  have := isIso_twistComparison_of_rightAcyclic F₁ F₂ T h₁ h₂
  have hn := derivedTwistEndo_naturality P F₁ F₂ θ ψ τ g h
  have hc := twistComparison_comp_derivedTwistEndo P F₁ F₂ θ T g
  have hc' : derivedTwistEndo P F₁ F₂ θ T g ≫ CategoryTheory.inv (twistComparison F₁ F₂ T) =
      CategoryTheory.inv (twistComparison F₁ F₂ T) ≫
        DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, hc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  change DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map _ =
    DerivedCategory.Plus.ι.map _ ≫ DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  change derivedTwistEndo P F₁ F₂ θ K τ ≫ (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T)) =
    (F₂.rightDerivedFunctorPlus.map
      (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) ≫
        CategoryTheory.inv (twistComparison F₁ F₂ T)) ≫
      DerivedCategory.Plus.Q.map (twistChainEndo P F₁ F₂ θ T g)
  rw [reassoc_of% hn, hc', Category.assoc]

end Twist

end CategoryTheory.Functor

namespace CategoryTheory.FilteredDerived

variable {R : Type} [Ring R] {S : Type} [Ring S] (Φ : ModuleCat.{w} R ⥤ ModuleCat.{w} S)
  [Φ.Additive] (hΦ : PreservesFiniteProjective Φ)
  (hinj : ∀ M : ModuleCat.{w} R, Module.Finite R M → Module.Projective R M → Injective M)
  (J : CochainComplex (ModuleCat.{w} R) ℤ) (a : ℤ) [J.IsStrictlyGE a]
  (hJ : ∀ i, Injective (J.X i)) (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Q.obj J))

include hinj hJ hperf a in
/-- A perfect bounded below complex of injective modules over a ring whose finite projective
modules are injective is homotopy equivalent to a bounded complex `P` of finite projective
modules. -/
theorem exists_homotopyEquiv_of_injective :
    ∃ (P : CochainComplex (ModuleCat.{w} R) ℤ) (_ : finiteProjectiveComplex.{0, w} R P)
      (α : J ⟶ P) (β : P ⟶ J), Nonempty (Homotopy (α ≫ β) (𝟙 J)) ∧
        Nonempty (Homotopy (β ≫ α) (𝟙 P)) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := (isPerfect_iff R _).1 hperf
  obtain ⟨⟨⟨b, hb⟩, hle⟩, hterms⟩ := hP
  have : ∀ i, Injective (J.X i) := hJ
  have : ∀ i, Injective (P.X i) := fun i => hinj _ (hterms i).2 (hterms i).1
  have := CochainComplex.isKInjective_of_injective J a
  have := CochainComplex.isKInjective_of_injective P b
  obtain ⟨α, hα⟩ := StacksDraft.DerivedHom.exists_eq_Q_map_of_isKInjective J P e.inv
  obtain ⟨β, hβ⟩ := StacksDraft.DerivedHom.exists_eq_Q_map_of_isKInjective P J e.hom
  refine ⟨P, ⟨⟨⟨b, hb⟩, hle⟩, hterms⟩, α, β, ⟨CochainComplex.homotopyOfQMapEq ?_⟩,
    ⟨CochainComplex.homotopyOfQMapEq ?_⟩⟩
  · rw [DerivedCategory.Q.map_comp, hα, hβ, e.inv_hom_id, DerivedCategory.Q.map_id]
  · rw [DerivedCategory.Q.map_comp, hα, hβ, e.hom_inv_id, DerivedCategory.Q.map_id]

/-- The image under an additive functor of a homotopy equivalence `α : J ⟶ P`, `β : P ⟶ J` is an
isomorphism in the derived category. -/
def mapHomotopyEquivIso {J P : CochainComplex (ModuleCat.{w} R) ℤ} (α : J ⟶ P) (β : P ⟶ J)
    (h₁ : Homotopy (α ≫ β) (𝟙 J)) (h₂ : Homotopy (β ≫ α) (𝟙 P)) :
    DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅
      DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J) where
  hom := DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map β)
  inv := DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map α)
  hom_inv_id := by
    rw [← DerivedCategory.Q.map_comp, ← Functor.map_comp, ← DerivedCategory.Q.map_id,
      ← Functor.map_id (Φ.mapHomologicalComplex (ComplexShape.up ℤ))]
    exact DerivedCategory.Q_map_eq_of_homotopy _ (Φ.mapHomotopy h₂)
  inv_hom_id := by
    rw [← DerivedCategory.Q.map_comp, ← Functor.map_comp, ← DerivedCategory.Q.map_id,
      ← Functor.map_id (Φ.mapHomologicalComplex (ComplexShape.up ℤ))]
    exact DerivedCategory.Q_map_eq_of_homotopy _ (Φ.mapHomotopy h₁)

include hΦ hinj hJ hperf a in
/-- **Perfectness along a functor preserving finite projective modules**, for a perfect bounded
below complex of injectives over a ring whose finite projective modules are injective. -/
theorem isPerfect_map_of_injective :
    StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) := by
  obtain ⟨P, hP, α, β, ⟨h₁⟩, ⟨h₂⟩⟩ := exists_homotopyEquiv_of_injective hinj J a hJ hperf
  exact (isPerfect_iff S _).2 ⟨_, finiteProjectiveComplex_map Φ hΦ P hP,
    ⟨mapHomotopyEquivIso Φ α β h₁ h₂⟩⟩

include hinj hJ hperf a in
/-- **The trace along a functor preserving finite projective modules** of an endomorphism of a
perfect bounded below complex of injectives: `Tr_S(Φ(t) | Φ(J)) = Φ♮(Tr_R(t | J))`. -/
theorem perfectDerivedTrace_map_of_injective (t : J ⟶ J)
    (hperf' : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj J))) :
    perfectDerivedTrace S ⟨_, hperf'⟩
        (DerivedCategory.Q.map ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).map t)) =
      functorTraceMap Φ (𝟙 _) hΦ (perfectDerivedTrace R ⟨_, hperf⟩ (DerivedCategory.Q.map t)) := by
  obtain ⟨P, hP, α, β, ⟨h₁⟩, ⟨h₂⟩⟩ := exists_homotopyEquiv_of_injective hinj J a hJ hperf
  let eP : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj J :=
    mapHomotopyEquivIso (𝟭 _) α β h₁ h₂
  refine perfectDerivedTrace_functor Φ (𝟙 _) hΦ ⟨_, hperf⟩ (DerivedCategory.Q.map t) P hP
    eP (β ≫ t ≫ α) ?_ ⟨_, hperf'⟩ _ (mapHomotopyEquivIso Φ α β h₁ h₂) ?_
  · simp only [Functor.map_comp]; rfl
  · simp [mapHomotopyEquivIso, NatTrans.mapHomologicalComplex_id]

end CategoryTheory.FilteredDerived
