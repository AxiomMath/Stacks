module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BoundedBelowComparisonEquivalence
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The unit of a derived adjunction on bounded below derived categories

Let `L ⊣ R` be an adjunction between abelian categories with `L` exact, so that it descends to
`L ⊣ R⁺` on bounded below derived categories
(`Stacks.ComparingTopologies.derivedPlusAdjunction`), and let `P : 𝒜 ⥤ A` be an exact functor.
If for every object `X` of `𝒜` the unit `P X ⟶ R(L(P X))` is an isomorphism and `L(P X)` is
acyclic for `R`, then the derived unit `P K ⟶ R⁺(L(P K))` is an isomorphism for every `K` in
`D⁺(𝒜)`. This is the reduction to a single object in the proof of Stacks 0DGG, through Leray's
acyclicity lemma (Stacks 015E).

## Main results

* `Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app_mapDerivedCategoryPlus`: the
  statement above.
* `Stacks.ComparingTopologies.isIso_derivedPlusAdjunction_unit_app`: the case `P = 𝟭`.

## Implementation notes

An object of `D⁺(𝒜)` is the image of a bounded below complex `K'`; at its image the derived unit
is, by `CategoryTheory.Adjunction.derivedη_fac_app`, the degreewise unit at `P K'` followed by the
unit of right derivation of `R` at `L(P K')`. The first is invertible termwise, the second by
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0DGG](https://stacks.math.columbia.edu/tag/0DGG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ComparingTopologies

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {𝒜 A B : Type*} [Category 𝒜] [Category A] [Category B]
  [Abelian 𝒜] [Abelian A] [Abelian B]
  [HasDerivedCategory 𝒜] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives B]
  {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

omit [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives B]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- The unit of the degreewise adjunction on bounded below homotopy categories is invertible at a
complex at each of whose terms the unit of the adjunction is invertible. -/
theorem isIso_mapHomotopyCategoryPlus_unit_app (adj : L ⊣ R) (M : HomotopyCategory.Plus A)
    (hM : ∀ n : ℤ, IsIso (adj.unit.app (M.obj.as.X n))) :
    IsIso (adj.mapHomotopyCategoryPlus.unit.app M) := by
  have : ∀ n : ℤ, IsIso
      (((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app M.obj.as).f n) :=
    fun n ↦ hM n
  have : IsIso ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app M.obj.as) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((HomotopyCategory.Plus.ι A).map (adj.mapHomotopyCategoryPlus.unit.app M)) := by
    have e := Adjunction.map_restrictFullyFaithful_unit_app (L := L.mapHomotopyCategoryPlus)
      (R := R.mapHomotopyCategoryPlus) (adj.mapHomotopyCategory (ComplexShape.up ℤ))
      (HomotopyCategory.Plus.fullyFaithfulι A) (HomotopyCategory.Plus.fullyFaithfulι B)
      (Iso.refl _) (Iso.refl _) M
    rw [Adjunction.mapHomotopyCategoryPlus, e, Adjunction.mapHomotopyCategory_unit_app]
    have h₁ : IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app
          ((HomotopyCategory.Plus.ι A).obj M).as)) :=
      (Functor.mapIso (HomotopyCategory.quotient A (ComplexShape.up ℤ))
        (asIso ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app
          M.obj.as))).isIso_hom
    exact (@asIso _ _ _ _ _ h₁ ≪≫ (R.mapHomotopyCategory (ComplexShape.up ℤ)).mapIso
      ((Iso.refl (HomotopyCategory.Plus.ι A ⋙ L.mapHomotopyCategory (ComplexShape.up ℤ))).app M) ≪≫
      (Iso.refl (HomotopyCategory.Plus.ι B ⋙ R.mapHomotopyCategory (ComplexShape.up ℤ))).app
        (L.mapHomotopyCategoryPlus.obj M)).isIso_hom
  exact isIso_of_fully_faithful (HomotopyCategory.Plus.ι A) _

/-- The derived unit at the image of a bounded below complex is invertible if the degreewise unit
is invertible and the terms of its image under `L` are right acyclic. -/
private theorem isIso_derivedPlusAdjunction_unit_app_qh_obj (adj : L ⊣ R)
    (M : HomotopyCategory.Plus A) (hu : ∀ n : ℤ, IsIso (adj.unit.app (M.obj.as.X n)))
    (hac : ∀ n : ℤ, R.rightAcyclic (L.obj (M.obj.as.X n))) :
    IsIso ((derivedPlusAdjunction adj).unit.app (DerivedCategory.Plus.Qh.obj M)) := by
  have : L.mapDerivedCategoryPlus.IsLeftDerivedFunctor
      L.mapDerivedCategoryPlusFactorsh.hom (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
      L.mapDerivedCategoryPlusFactorsh
  have : (L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
        L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
      (HomotopyCategory.Plus.quasiIso A) :=
    Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
        L.mapDerivedCategoryPlusFactorsh R.rightDerivedFunctorPlus)
  have hη := adj.mapHomotopyCategoryPlus.derivedη_fac_app (HomotopyCategory.Plus.quasiIso A)
    L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnith M
  have h₁ : IsIso (adj.mapHomotopyCategoryPlus.unit.app M) :=
    isIso_mapHomotopyCategoryPlus_unit_app adj M hu
  have h₂ : IsIso (R.rightDerivedFunctorPlusUnith.app (L.mapHomotopyCategoryPlus.obj M)) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic R _ hac
  have : IsIso ((derivedPlusAdjunction adj).unit.app (DerivedCategory.Plus.Qh.obj M) ≫
      R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app M)) := by
    have hu' : (derivedPlusAdjunction adj).unit =
        adj.mapHomotopyCategoryPlus.derivedη (HomotopyCategory.Plus.quasiIso A)
          L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnith := by
      have : (R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus).IsRightDerivedFunctor
          (Functor.whiskerRight R.rightDerivedFunctorPlusUnith L.mapDerivedCategoryPlus ≫
            (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B) := by
        apply (HomotopyCategory.Plus.localizerMorphism_derives
          ((R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
            L.mapDerivedCategoryPlus)).isRightDerivedFunctor_of_isIso
        intro K
        dsimp
        infer_instance
      dsimp only [derivedPlusAdjunction]
      exact Adjunction.derived_unit ..
    rw [hu', hη]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app M))

/-- **The derived unit at the image of an exact functor.** Let `L ⊣ R` with `L` exact and
`P : 𝒜 ⥤ A` exact. If the unit `P X ⟶ R(L(P X))` is invertible and `L(P X)` is right acyclic
for `R` for every object `X` of `𝒜`, then the unit `P K ⟶ R⁺(L(P K))` of the derived adjunction
is invertible for every `K` in `D⁺(𝒜)`. -/
theorem isIso_derivedPlusAdjunction_unit_app_mapDerivedCategoryPlus
    (P : 𝒜 ⥤ A) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (adj : L ⊣ R) (hu : ∀ X : 𝒜, IsIso (adj.unit.app (P.obj X)))
    (hac : ∀ X : 𝒜, R.rightAcyclic (L.obj (P.obj X))) (K : DerivedCategory.Plus 𝒜) :
    IsIso ((derivedPlusAdjunction adj).unit.app (P.mapDerivedCategoryPlus.obj K)) := by
  let K' := DerivedCategory.Plus.Qh.objPreimage K
  let eK : DerivedCategory.Plus.Qh.obj K' ≅ K := DerivedCategory.Plus.Qh.objObjPreimageIso K
  let M := P.mapHomotopyCategoryPlus.obj K'
  let eM : P.mapDerivedCategoryPlus.obj K ≅ DerivedCategory.Plus.Qh.obj M :=
    P.mapDerivedCategoryPlus.mapIso eK.symm ≪≫ P.mapDerivedCategoryPlusFactorsh.app K'
  rw [NatTrans.isIso_app_iff_of_iso _ eM]
  exact isIso_derivedPlusAdjunction_unit_app_qh_obj adj M (fun n ↦ hu _) fun n ↦ hac _

/-- **The derived unit, from the unit and acyclicity on objects.** Let `L ⊣ R` with `L` exact.
If the unit `X ⟶ R(L X)` is invertible and `L X` is right acyclic for `R` for every object `X`,
then the unit `K ⟶ R⁺(L K)` of the derived adjunction is invertible for every `K` in `D⁺(A)`. -/
theorem isIso_derivedPlusAdjunction_unit_app
    (adj : L ⊣ R) (hu : ∀ X : A, IsIso (adj.unit.app X))
    (hac : ∀ X : A, R.rightAcyclic (L.obj X)) (K : DerivedCategory.Plus A) :
    IsIso ((derivedPlusAdjunction adj).unit.app K) := by
  let M := DerivedCategory.Plus.Qh.objPreimage K
  let eM : K ≅ DerivedCategory.Plus.Qh.obj M := (DerivedCategory.Plus.Qh.objObjPreimageIso K).symm
  rw [NatTrans.isIso_app_iff_of_iso _ eM]
  exact isIso_derivedPlusAdjunction_unit_app_qh_obj adj M (fun n ↦ hu _) fun n ↦ hac _

/-- **The counit of `derivedPlusAdjunction` is invertible when `R` is fully faithful.** Every
object of `D⁺(B)` is the image of a bounded below complex of injectives `N`, at which the unit of
right derivation of `R` is invertible; by `CategoryTheory.Adjunction.derivedε_fac_app` the derived
counit at `N` is then the counit of the degreewise adjunction, invertible because `R` is fully
faithful. (The same argument is a private lemma of the module
`BoundedBelowComparisonEquivalence`.) -/
theorem isIso_derivedPlusAdjunction_counit_app_of_fullyFaithful [R.Full] [R.Faithful]
    (adj : L ⊣ R) (Y : DerivedCategory.Plus B) :
    IsIso ((derivedPlusAdjunction adj).counit.app Y) := by
  obtain ⟨a, ha⟩ := Y.property
  have : Y.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Y a).1 ha
  obtain ⟨I, _, ⟨eY⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso Y a
  let M := (InjectiveObject.ι B).mapCochainComplexPlus.obj I
  let N := (HomotopyCategory.Plus.quotient B).obj M
  have : ∀ i : ℤ, Injective (N.obj.as.X i) := fun _ => inferInstance
  have : IsIso (R.rightDerivedFunctorPlusUnith.app N) := inferInstance
  have : (R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorPlusUnith L.mapDerivedCategoryPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso B) := by
    apply (HomotopyCategory.Plus.localizerMorphism_derives
      ((R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        L.mapDerivedCategoryPlus)).isRightDerivedFunctor_of_isIso
    intro K
    dsimp
    infer_instance
  have hfac := adj.mapHomotopyCategoryPlus.derivedε_fac_app
    (HomotopyCategory.Plus.quasiIso B) L.mapDerivedCategoryPlusFactorsh.hom
    R.rightDerivedFunctorPlusUnith N
  have hc' : (derivedPlusAdjunction adj).counit =
      adj.mapHomotopyCategoryPlus.derivedε (HomotopyCategory.Plus.quasiIso B)
        L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlusUnith := by
    have : L.mapDerivedCategoryPlus.IsLeftDerivedFunctor
        L.mapDerivedCategoryPlusFactorsh.hom (HomotopyCategory.Plus.quasiIso A) :=
      Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
        L.mapDerivedCategoryPlusFactorsh
    have : (L.mapDerivedCategoryPlus ⋙ R.rightDerivedFunctorPlus).IsLeftDerivedFunctor
        ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight
          L.mapDerivedCategoryPlusFactorsh.hom R.rightDerivedFunctorPlus)
        (HomotopyCategory.Plus.quasiIso A) :=
      Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso A) _
        ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight
          L.mapDerivedCategoryPlusFactorsh R.rightDerivedFunctorPlus)
    dsimp only [derivedPlusAdjunction]
    exact Adjunction.derived_counit ..
  rw [← hc'] at hfac
  have : IsIso ((derivedPlusAdjunction adj).counit.app (DerivedCategory.Plus.Qh.obj N)) := by
    have : IsIso (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app N) ≫
        (derivedPlusAdjunction adj).counit.app (DerivedCategory.Plus.Qh.obj N)) := by
      rw [hfac]
      infer_instance
    exact IsIso.of_isIso_comp_left
      (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlusUnith.app N)) _
  exact (NatTrans.isIso_app_iff_of_iso _ ((ObjectProperty.isoMk _
    ((DerivedCategory.quotientCompQhIso B).app M.obj) :
      DerivedCategory.Plus.Qh.obj N ≅ DerivedCategory.Plus.Q.obj M) ≪≫ eY)).1 inferInstance

section Mates

variable {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂} {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}

/-- **A base-change map whose square of right adjoints is invertible is invertible, when both left
adjoints are fully faithful and the target lies in the essential image.** Let `L₁ ⊣ R₁` and
`L₂ ⊣ R₂` have invertible units, and let `α : R₁ ⋙ G ⟶ H ⋙ R₂` be invertible. Then the mate
`β : G ⋙ L₂ ⟶ L₁ ⋙ H` of `α` is invertible at every `c` for which `H (L₁ c)` is isomorphic to an
object `L₂ e`: `R₂ (β c)` is invertible by the unit identity of the mates correspondence, and the
counit of `L₂ ⊣ R₂` is invertible on the essential image of the fully faithful `L₂`. -/
theorem isIso_mateEquiv_symm_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare R₁ H G R₂) [IsIso α]
    (h₁ : ∀ c, IsIso (adj₁.unit.app c)) (h₂ : ∀ e, IsIso (adj₂.unit.app e)) (c : C₁)
    {e : C₂} (φ : L₂.obj e ≅ H.obj (L₁.obj c)) :
    IsIso (((mateEquiv adj₁ adj₂).symm α).app c) := by
  let β := ((mateEquiv adj₁ adj₂).symm α).app c
  have hR : IsIso (R₂.map β) := by
    have : IsIso (α.app (L₁.obj c)) := inferInstanceAs (IsIso (α.app _))
    have : IsIso (G.map (adj₁.unit.app c) ≫ α.app (L₁.obj c)) := inferInstance
    rw [unit_mateEquiv_symm adj₁ adj₂ α c] at this
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ (h₂ _) this
  have : IsIso adj₂.unit := NatIso.isIso_of_isIso_app _
  have hff := adj₂.fullyFaithfulLOfIsIsoUnit
  have : L₂.Full := hff.full
  have : L₂.Faithful := hff.faithful
  have hs : IsIso (adj₂.counit.app (L₂.obj (G.obj c))) :=
    adj₂.isIso_counit_app_iff_mem_essImage.2 ⟨_, ⟨Iso.refl _⟩⟩
  have ht : IsIso (adj₂.counit.app (H.obj (L₁.obj c))) :=
    adj₂.isIso_counit_app_iff_mem_essImage.2 ⟨_, ⟨φ⟩⟩
  have : IsIso (L₂.map (R₂.map β) ≫ adj₂.counit.app (H.obj (L₁.obj c))) := inferInstance
  rw [show L₂.map (R₂.map β) ≫ adj₂.counit.app (H.obj (L₁.obj c)) =
    adj₂.counit.app (L₂.obj (G.obj c)) ≫ β from adj₂.counit.naturality β] at this
  exact IsIso.of_isIso_comp_left (adj₂.counit.app (L₂.obj (G.obj c))) β

end Mates

end Stacks.ComparingTopologies

end
