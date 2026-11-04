module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Coreflection
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.RightAdjoint
public import StacksFrontier.RingTheory.Dualizing.PowerTorsionComparison.LocalCohomologyFunctor
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.Complete

/-!
# Derived completion after local cohomology

Let `I` be a finitely generated ideal of a commutative ring `A` and `Z = V(I)`. The counit
`RΓ_Z(K) ⟶ K` of the adjunction defining local cohomology becomes an isomorphism after derived
`I`-completion: completing the local cohomology of `K` gives the completion of `K` itself.

The proof replaces `RΓ_Z(K) ⟶ K` by the coreflection of `K` onto the common kernel of the
derived localizations at the powers of a finite generating family of `I`. That kernel is exactly
the objects with `I`-power-torsion cohomology, so the two maps agree up to a unique isomorphism;
and the coreflection is built from fibres whose cones are derived localizations, each of which is
killed by derived completion because the inverted element acts invertibly on it.

The statement is for an arbitrary reflection of `D(A)` onto the derived `I`-complete objects, so
it applies to every model of derived completion, and the module universe stays independent of the
ring universe.

## Main results

* `Dualizing.Coreflection.exists_finite_localization_coreflection_isIso_map` — a triangulated
  functor annihilating the image of each localization inverts the structure map of the
  coreflection onto their common kernel.
* `Dualizing.isIso_derivedCompletion_map_localCohomologyCounit` — Stacks 0A6W, the half asserting
  `RΓ_Z(K)^∧ = K^∧`.

That the inverted element acts invertibly on a derived localization, which is what makes derived
completion kill the cones, is `Dualizing.isIso_smul_mapDerivedCategory_smallLocalization` of
`StacksFrontier/RingTheory/Dualizing/TorsionComplete/SmallLocalization.lean`.

## References

* [Stacks Project, Tag 0A6W](https://stacks.math.columbia.edu/tag/0A6W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace Dualizing

namespace Coreflection

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The coreflection onto the common kernel of a finite family of localizations is inverted by
any triangulated functor killing that family.** This refines
`Dualizing.Coreflection.exists_finite_localization_coreflection` by recording, alongside the
coreflection, that its structure map becomes invertible under such a functor: the map is a
composite of fibre inclusions whose cones are values of the family. -/
theorem exists_finite_localization_coreflection_isIso_map
    {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    {ι : Type*} (F : ι → C ⥤ C) [∀ i, (F i).Additive]
    [∀ i, (F i).CommShift ℤ] [∀ i, (F i).IsTriangulated]
    (η : ∀ i, 𝟭 C ⟶ F i)
    (hη : ∀ i X, IsIso ((η i).app ((F i).obj X)))
    (hFη : ∀ i X, IsIso ((F i).map ((η i).app X)))
    (hpres : ∀ i j X, IsZero ((F j).obj X) → IsZero ((F j).obj ((F i).obj X)))
    (s : Finset ι) (G : C ⥤ D) [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    (hG : ∀ i ∈ s, ∀ X, IsZero (G.obj ((F i).obj X))) (X : C) :
    ∃ (Y : C) (a : Y ⟶ X), (∀ i ∈ s, IsZero ((F i).obj Y)) ∧ IsIso (G.map a) ∧
      ∀ W, (∀ i ∈ s, IsZero ((F i).obj W)) →
        Function.Bijective (fun g : W ⟶ Y => g ≫ a) := by
  classical
  revert hG X
  induction s using Finset.induction_on with
  | empty =>
    intro _ X
    refine ⟨X, 𝟙 X, by simp, inferInstance, ?_⟩
    intro W _
    exact ⟨fun _ _ h => by simpa using h,
      fun g => ⟨g, Category.comp_id g⟩⟩
  | @insert i s hi ih =>
    intro hG X
    obtain ⟨U, b, hU, hGb, hb⟩ := ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)) X
    obtain ⟨T, hT, h₂, h₃, hFT, ha⟩ :=
      exists_fiber_localization (F i) (η i) (hη i) (hFη i) U
    let e : T.obj₂ ≅ U := eqToIso h₂
    refine ⟨T.obj₁, T.mor₁ ≫ e.hom ≫ b, ?_, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hFT
      · apply Triangle.isZero₁_of_isZero₂₃ _ ((F j).map_distinguished _ hT)
        · exact (hU j hj).of_iso ((F j).mapIso e)
        · rw [show ((F j).mapTriangle.obj T).obj₃ = (F j).obj T.obj₃ from rfl, h₃]
          exact hpres i j U (hU j hj)
    · have : IsIso (G.map T.mor₁) :=
        (Triangle.isZero₃_iff_isIso₁ _ (G.map_distinguished _ hT)).mp (by
          show IsZero (G.obj T.obj₃)
          rw [h₃]
          exact hG i (Finset.mem_insert_self _ _) U)
      simp only [Functor.map_comp]
      infer_instance
    · intro W hW
      have h₂' : Function.Bijective (fun g : W ⟶ T.obj₂ => g ≫ e.hom) :=
        ⟨fun _ _ h => (cancel_mono e.hom).1 h, fun g => ⟨g ≫ e.inv, by simp⟩⟩
      simpa only [Function.comp_def, Category.assoc] using
        (hb W fun j hj => hW j (Finset.mem_insert_of_mem hj)).comp
          (h₂'.comp (ha W (hW i (Finset.mem_insert_self _ _))))

end Coreflection

section

attribute [local instance] HasDerivedCategory.standard hasProductsOfShape_nat_derivedCategory

/-- **An exact triangulated functor killing every derived localization at the powers of a
generating family inverts the local-cohomology counit.** Such a functor inverts the structure map
of the coreflection onto the common kernel of those localizations, and that kernel is the
subcategory of objects with `I`-power-torsion cohomology, so the coreflection and the counit
differ by an isomorphism. -/
theorem map_localCohomologyCounit_isIso_of_isZero_mapDerivedCategory
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (s : Finset A) (hs : Ideal.span (s : Set A) = I)
    (G : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A))
    [G.Additive] [G.CommShift ℤ] [G.IsTriangulated]
    (hG : ∀ x ∈ s, ∀ X, IsZero (G.obj
      ((smallLocalizationFunctor (Submonoid.powers x)).mapDerivedCategory.obj X)))
    (K : DerivedCategory (ModuleCat.{v} A)) :
    IsIso (G.map ((localCohomologyAdjunction A I hI).counit.app K)) := by
  classical
  let F : A → DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCategory (ModuleCat.{v} A) :=
    fun x => (smallLocalizationFunctor (Submonoid.powers x)).mapDerivedCategory
  let η : ∀ x, 𝟭 (DerivedCategory (ModuleCat.{v} A)) ⟶ F x := fun x =>
    Coreflection.derivedUnit (smallLocalizationFunctor (Submonoid.powers x))
      (smallLocalizationUnit (Submonoid.powers x))
  have hη (x : A) (X : DerivedCategory (ModuleCat.{v} A)) :
      IsIso ((η x).app ((F x).obj X)) :=
    Coreflection.derivedUnit_obj_isIso _ _
      (isIso_smallLocalizationUnit_app_obj (Submonoid.powers x)) X
  have hFη (x : A) (X : DerivedCategory (ModuleCat.{v} A)) :
      IsIso ((F x).map ((η x).app X)) :=
    Coreflection.derivedUnit_map_isIso _ _
      (isIso_smallLocalizationFunctor_map_smallLocalizationUnit_app (Submonoid.powers x)) X
  have hpres (x y : A) (X : DerivedCategory (ModuleCat.{v} A))
      (h : IsZero ((F y).obj X)) : IsZero ((F y).obj ((F x).obj X)) :=
    isZero_mapDerivedCategory_smallLocalization_comp (Submonoid.powers y) (Submonoid.powers x) X h
  obtain ⟨Y, a, hY, hGa, ha⟩ :=
    Coreflection.exists_finite_localization_coreflection_isIso_map F η hη hFη hpres s G hG K
  let P := derivedPowerTorsionProperty A I hI
  let Y' : P.FullSubcategory :=
    ⟨Y, (derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory I hI s hs Y).mpr hY⟩
  let adj := localCohomologyAdjunction A I hI
  let φ : Y' ⟶ (localCohomologyRightAdjoint A I hI).1.obj K := adj.homEquiv Y' K a
  have hφ : P.ι.map φ ≫ adj.counit.app K = a := (adj.homEquiv Y' K).symm_apply_apply a
  have : IsIso φ := by
    apply isIso_of_yoneda_map_bijective
    intro W
    have hbW := (ha W.obj
      ((derivedPowerTorsionProperty_iff_isZero_mapDerivedCategory I hI s hs W.obj).mp
        W.property)).comp (P.fullyFaithfulι.homEquiv (X := W) (Y := Y')).bijective
    have heq : (fun g : W ⟶ Y' => g ≫ φ) =
        (adj.homEquiv W K) ∘ (fun g : W ⟶ Y' => P.ι.map g ≫ a) := by
      funext g
      apply (adj.homEquiv W K).symm.injective
      simp only [Function.comp_apply, Equiv.symm_apply_apply, Adjunction.homEquiv_counit,
        Functor.map_comp, Category.assoc]
      exact congrArg (fun k => P.ι.map g ≫ k) hφ
    rw [heq]
    exact (adj.homEquiv W K).bijective.comp hbW
  have : IsIso (G.map (P.ι.map φ) ≫ G.map (adj.counit.app K)) := by
    rwa [← G.map_comp, hφ]
  exact IsIso.of_isIso_comp_left (G.map (P.ι.map φ)) _

/-- **Stacks 0A6W, completion after local cohomology.** For a finitely generated ideal `I` of a
commutative ring `A` and `Z = V(I)`, the counit `RΓ_Z(K) ⟶ K` of the adjunction defining local
cohomology becomes an isomorphism after derived `I`-completion; equivalently
`RΓ_Z(K)^∧ = K^∧` in `D(A)`, naturally in `K`.

The statement holds for every reflection `C` of `D(A)` onto the derived `I`-complete objects, so
it is independent of the chosen model of derived completion. -/
@[stacks 0A6W "completion_after_local"]
theorem isIso_derivedCompletion_map_localCohomologyCounit
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (C : DerivedCategory (ModuleCat.{v} A) ⥤ DerivedCompleteDerivedCategory A I)
    (hC : C ⊣ (derivedCompleteProperty A I).ι) (K : DerivedCategory (ModuleCat.{v} A)) :
    IsIso ((C ⋙ (derivedCompleteProperty A I).ι).map
      ((localCohomologyAdjunction A I hI).counit.app K)) := by
  let P := derivedCompleteProperty.{u, v} A I
  let := hC.leftAdjointCommShift ℤ
  have := hC.commShift_of_rightAdjoint ℤ
  have : C.IsTriangulated := hC.isTriangulated_leftAdjoint
  have : C.Additive := hC.left_adjoint_additive
  obtain ⟨s, hs⟩ := id hI
  apply map_localCohomologyCounit_isIso_of_isZero_mapDerivedCategory A I hI s hs (C ⋙ P.ι) _ K
  intro x hx X
  have := isIso_smul_mapDerivedCategory_smallLocalization x X
  exact P.ι.map_isZero (isZero_reflector_obj_of_isIso_smul A I P C hC _ x
    (hs ▸ Ideal.subset_span hx) fun E => E.property)

end

end Dualizing

end
