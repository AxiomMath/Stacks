module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionUnitLocalCohomology.AdicCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.StabilizationReduction

/-!
# The completion unit on local cohomology: the inductive steps

Formal criteria for the unit `RΓ_J(M) ⟶ RΓ_J(M)^∧` of derived `I`-adic completion to be
invertible on cohomology: the two inductive steps of Stacks 0EFL (along a short exact sequence
and along a regular element), criteria for `RΓ_J(M)` to be already derived complete, and the
statement that completion inverts the comparison `RΓ_J(K) ⟶ RΓ_{J'}(K)` attached to a shrinking
with the same trace on `V(I)`.

## Main results

* `Stacks.Algebraization.completionUnit_localCohomology_isIso_of_regular_annihilator`
* `Stacks.Algebraization.completionUnit_localCohomology_isIso_of_shortExact`
* `Stacks.Algebraization.isIso_completionFunctor_map_localCohomologyComparison`

## References

* [Stacks Project, Tag 0EFL](https://stacks.math.columbia.edu/tag/0EFL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Stacks.Algebraization

/-! ### Formal lemmas on homology of distinguished triangles -/

/-- In a map of short complexes whose target is exact and whose two outer maps are invertible,
with both second maps epimorphisms, the third map is invertible. -/
private theorem isIso_third_of_exact_of_epi
    {C : Type*} [Category C] [Abelian C]
    {S T : ShortComplex C} (φ : S ⟶ T)
    (hT : T.Exact)
    [Epi S.g] [Epi T.g] [IsIso φ.τ₁] [IsIso φ.τ₂] : IsIso φ.τ₃ := by
  have hw : T.f ≫ (inv φ.τ₂ ≫ S.g) = 0 := by
    apply (cancel_epi φ.τ₁).1
    rw [← Category.assoc, φ.comm₁₂]
    simp [Category.assoc]
  obtain ⟨ψ, hψ⟩ := hT.desc' (inv φ.τ₂ ≫ S.g) hw
  have hleft : φ.τ₃ ≫ ψ = 𝟙 S.X₃ := by
    apply (cancel_epi S.g).1
    rw [← Category.assoc, ← φ.comm₂₃, Category.assoc, hψ]
    simp
  have hright : ψ ≫ φ.τ₃ = 𝟙 T.X₃ := by
    apply (cancel_epi T.g).1
    rw [← Category.assoc, hψ, Category.assoc, ← φ.comm₂₃]
    simp
  exact ⟨⟨ψ, hleft, hright⟩⟩

open CategoryTheory.Pretriangulated in
/-- Let `φ` be a map of distinguished triangles for which the first map of each triangle induces
zero in degree `j = i + 1`. If `φ` is invertible on `H^i` of the second and third vertices, it is
invertible on `H^j` of the first vertex. -/
private theorem isIso_homologyMap_first_of_zero_first_maps
    {C : Type*} [Category C] [Abelian C]
    {T T' : CategoryTheory.Pretriangulated.Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang _)
    (hT' : T' ∈ distTriang _)
    (φ : T ⟶ T') (i j : ℤ) (hij : i + 1 = j)
    (hz : (DerivedCategory.homologyFunctor C j).map T.mor₁ = 0)
    (hz' : (DerivedCategory.homologyFunctor C j).map T'.mor₁ = 0)
    [IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₂)]
    [IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₃)] :
    IsIso ((DerivedCategory.homologyFunctor C j).map φ.hom₁) := by
  let S := ShortComplex.mk _ _ (DerivedCategory.HomologySequence.comp_δ T hT i j hij)
  let S' := ShortComplex.mk _ _ (DerivedCategory.HomologySequence.comp_δ T' hT' i j hij)
  let ψ : S ⟶ S' :=
    { τ₁ := (DerivedCategory.homologyFunctor C i).map φ.hom₂
      τ₂ := (DerivedCategory.homologyFunctor C i).map φ.hom₃
      τ₃ := (DerivedCategory.homologyFunctor C j).map φ.hom₁
      comm₁₂ := by
        dsimp [S, S']
        rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂]
      comm₂₃ := (DerivedCategory.homologyFunctor C 0).homologySequenceδ_naturality
        φ i j hij }
  have he := DerivedCategory.HomologySequence.exact₁ T hT i j hij
  have he' := DerivedCategory.HomologySequence.exact₁ T' hT' i j hij
  have : Epi S.g := he.epi_f hz
  have : Epi S'.g := he'.epi_f hz'
  exact isIso_third_of_exact_of_epi ψ
    (DerivedCategory.HomologySequence.exact₃ T' hT' i j hij)

/-- The map from a triangle to its image under `F` given by the components of a natural
transformation `η` from the identity to a triangulated functor `F`. -/
private def triangleHomOfNatTrans
    {C : Type*} [Category C] [Abelian C]
    (F : DerivedCategory C ⥤ DerivedCategory C) [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 _ ⟶ F) [NatTrans.CommShift η ℤ]
    (T : CategoryTheory.Pretriangulated.Triangle (DerivedCategory C)) :
    T ⟶ F.mapTriangle.obj T :=
  { hom₁ := η.app T.obj₁
    hom₂ := η.app T.obj₂
    hom₃ := η.app T.obj₃
    comm₁ := η.naturality T.mor₁
    comm₂ := η.naturality T.mor₂
    comm₃ := by
      show T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map (η.app T.obj₁) =
        η.app T.obj₃ ≫ F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁
      rw [← Category.assoc, ← η.naturality T.mor₃, Functor.id_map,
        Category.assoc, ← η.shift_app_comm]
      simp }

open CategoryTheory.Pretriangulated in
/-- The previous lemma for the map of triangles given by a natural transformation `η` to a
triangulated functor. -/
private theorem isIso_homology_unit_of_zero_first_maps
    {C : Type*} [Category C] [Abelian C]
    (F : DerivedCategory C ⥤ DerivedCategory C) [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 _ ⟶ F) [NatTrans.CommShift η ℤ]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (i j : ℤ) (hij : i + 1 = j)
    (hz : (DerivedCategory.homologyFunctor C j).map T.mor₁ = 0)
    (hz' : (DerivedCategory.homologyFunctor C j).map (F.map T.mor₁) = 0)
    [IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₂))]
    [IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₃))] :
    IsIso ((DerivedCategory.homologyFunctor C j).map (η.app T.obj₁)) := by
  let φ := triangleHomOfNatTrans F η T
  have : IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₂) := by
    show IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₂))
    infer_instance
  have : IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₃) := by
    show IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₃))
    infer_instance
  exact isIso_homologyMap_first_of_zero_first_maps hT (F.map_distinguished T hT) φ i j hij hz hz'

open CategoryTheory.Pretriangulated in
/-- A five-lemma for the second vertices of a map of distinguished triangles which is invertible
on the first vertex and in two consecutive degrees on the third. -/
private theorem isIso_homologyMap_second_of_isIso_first
    {C : Type*} [Category C] [Abelian C]
    {T T' : Triangle (DerivedCategory C)}
    (hT : T ∈ distTriang _) (hT' : T' ∈ distTriang _)
    (φ : T ⟶ T') (i : ℤ) [IsIso φ.hom₁]
    [IsIso ((DerivedCategory.homologyFunctor C (i - 1)).map φ.hom₃)]
    [IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₃)] :
    IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₂) := by
  let H := DerivedCategory.homologyFunctor C
  let R := fun (T : Triangle (DerivedCategory C)) => ComposableArrows.mk₄
    (DerivedCategory.HomologySequence.δ T (i - 1) i (by omega))
    ((H i).map T.mor₁) ((H i).map T.mor₂)
    (DerivedCategory.HomologySequence.δ T i (i + 1))
  have he : ∀ T, T ∈ distTriang _ → (R T).Exact := by
    intro T hT
    exact ComposableArrows.exact_of_δ₀
      (DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega)).exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀
        (DerivedCategory.HomologySequence.exact₂ T hT i).exact_toComposableArrows
        (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1)).exact_toComposableArrows)
  let ψ : R T ⟶ R T' := ComposableArrows.homMk₄
    ((H (i - 1)).map φ.hom₃) ((H i).map φ.hom₁) ((H i).map φ.hom₂)
    ((H i).map φ.hom₃) ((H (i + 1)).map φ.hom₁)
    ((H 0).homologySequenceδ_naturality φ (i - 1) i (by omega)).symm
    (by
      show (H i).map T.mor₁ ≫ _ = _ ≫ (H i).map T'.mor₁
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₁])
    (by
      show (H i).map T.mor₂ ≫ _ = _ ≫ (H i).map T'.mor₂
      rw [← Functor.map_comp, ← Functor.map_comp, φ.comm₂])
    ((H 0).homologySequenceδ_naturality φ i (i + 1) rfl).symm
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (he T hT) (he T' hT') ψ
    (by change Epi ((H (i - 1)).map φ.hom₃); infer_instance)
    (by change IsIso ((H i).map φ.hom₁); infer_instance)
    (by change IsIso ((H i).map φ.hom₃); infer_instance)
    (by change Mono ((H (i + 1)).map φ.hom₁); infer_instance)

open CategoryTheory.Pretriangulated in
/-- The previous five-lemma for the map of triangles given by a natural transformation. -/
private theorem isIso_homology_unit_second_of_isIso_first
    {C : Type*} [Category C] [Abelian C]
    (F : DerivedCategory C ⥤ DerivedCategory C) [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 _ ⟶ F) [NatTrans.CommShift η ℤ]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (i : ℤ) [IsIso (η.app T.obj₁)]
    [IsIso ((DerivedCategory.homologyFunctor C (i - 1)).map (η.app T.obj₃))]
    [IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₃))] :
    IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₂)) := by
  let φ := triangleHomOfNatTrans F η T
  have : IsIso φ.hom₁ := by
    show IsIso (η.app T.obj₁)
    infer_instance
  have : IsIso ((DerivedCategory.homologyFunctor C (i - 1)).map φ.hom₃) := by
    show IsIso ((DerivedCategory.homologyFunctor C (i - 1)).map (η.app T.obj₃))
    infer_instance
  have : IsIso ((DerivedCategory.homologyFunctor C i).map φ.hom₃) := by
    show IsIso ((DerivedCategory.homologyFunctor C i).map (η.app T.obj₃))
    infer_instance
  exact isIso_homologyMap_second_of_isIso_first hT (F.map_distinguished T hT) φ i

/-! ### Formal lemmas on counits and annihilators -/

/-- If a functor `C` inverts `F.map g` and the two components of a counit `ε : F ⟶ 𝟭` at the
endpoints of `g`, then it inverts `g`. -/
private theorem completion_map_isIso_of_localization_map_isIso
    {D : Type*} [Category D] (C F : D ⥤ D) (ε : F ⟶ 𝟭 D)
    {X Y : D} (g : X ⟶ Y)
    (hmap : IsIso (C.map (F.map g)))
    (hX : IsIso (C.map (ε.app X))) (hY : IsIso (C.map (ε.app Y))) :
    IsIso (C.map g) := by
  have hnatural : C.map (F.map g) ≫ C.map (ε.app Y) =
      C.map (ε.app X) ≫ C.map g := by
    rw [← Functor.map_comp, ← Functor.map_comp, ε.naturality]
    simp
  have : IsIso (C.map (ε.app X) ≫ C.map g) := by
    rw [← hnatural]
    infer_instance
  exact IsIso.of_isIso_comp_left (C.map (ε.app X)) _

/-- Two coreflection-like normalizations of the same object are related by an isomorphism. -/
private theorem isIso_of_coreflections
    {C : Type*} [Category C] {X Y K : C}
    (a : X ⟶ K) (b : Y ⟶ K) (g : X ⟶ Y) (hg : g ≫ b = a)
    (haX : Function.Injective (fun f : X ⟶ X => f ≫ a))
    (haY : Function.Surjective (fun f : Y ⟶ X => f ≫ a))
    (hbY : Function.Injective (fun f : Y ⟶ Y => f ≫ b)) : IsIso g := by
  obtain ⟨h, hh⟩ := haY b
  change h ≫ a = b at hh
  refine ⟨⟨h, ?_, ?_⟩⟩
  · apply haX
    show (g ≫ h) ≫ a = (𝟙 X) ≫ a
    rw [Category.assoc, hh, hg, Category.id_comp]
  · apply hbY
    show (h ≫ g) ≫ b = (𝟙 Y) ≫ b
    rw [Category.assoc, hg, hh, Category.id_comp]

/-- A functor whose counit admits a right inverse after composing is linear. -/
private theorem map_smul_of_counit_hom_injective
    {R : Type*} [Semiring R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (F : C ⥤ C) (ε : F ⟶ 𝟭 C) {X Y : C}
    (hε : Function.Injective (fun g : F.obj X ⟶ F.obj Y => g ≫ ε.app Y))
    (a : R) (f : X ⟶ Y) : F.map (a • f) = a • F.map f := by
  apply hε
  show F.map (a • f) ≫ ε.app Y = (a • F.map f) ≫ ε.app Y
  rw [ε.naturality, Functor.id_map]
  simpa only [Functor.id_map, Linear.smul_comp, Linear.comp_smul] using
    congrArg (fun g => a • g) (ε.naturality f).symm

/-- Scaling the identity of an object of the derived category by an element of the annihilator of
one of its cohomology modules is zero in that degree. -/
private theorem homology_map_smul_id_eq_zero
    {A : Type u} [CommRing A] (X : DerivedCategory (ModuleCat.{u} A))
    (i : ℤ) (a : A)
    (ha : a ∈ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (a • 𝟙 X) = 0 := by
  have : Functor.Linear A (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) :=
    derivedHomologyFunctorLinear i
  rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  ext m
  exact Module.mem_annihilator.mp ha m

/-! ### The completion unit on distinguished triangles -/

section Completion

variable {A : Type u} [CommRing A]

/-- Derived completion commutes with the shift. -/
private instance completionFunctor_commShift (I : Ideal A) (hI : I.FG) :
    (adicCompletionFunctor A I hI).CommShift ℤ := by
  let adj := adicCompletionAdjunction A I hI
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  infer_instance

/-- Derived completion is triangulated. -/
private instance completionFunctor_isTriangulated (I : Ideal A) (hI : I.FG) :
    (adicCompletionFunctor A I hI).IsTriangulated := by
  let adj := adicCompletionAdjunction A I hI
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : (Dualizing.derivedCompletion.{u, u} A I hI).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  infer_instance

open CategoryTheory.Pretriangulated in
/-- **The degree-raising step.** If the first map of a distinguished triangle induces zero on
`H^j` before and after completion, and the unit is invertible on `H^i` at the second and third
vertices, then it is invertible on `H^j` at the first. -/
private theorem completionUnit_isIso_homology_of_zero_first_maps (I : Ideal A) (hI : I.FG)
    (T : Triangle (DerivedCategory (ModuleCat.{u} A))) (hT : T ∈ distTriang _)
    (i j : ℤ) (hij : i + 1 = j)
    (hz : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map T.mor₁ = 0)
    (hz' : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      ((adicCompletionFunctor A I hI).map T.mor₁) = 0)
    [IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app T.obj₂))]
    [IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app T.obj₃))] :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      ((adicCompletionUnit A I hI).app T.obj₁)) := by
  let adj := adicCompletionAdjunction A I hI
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  exact isIso_homology_unit_of_zero_first_maps
    (adicCompletionFunctor A I hI) (adicCompletionUnit A I hI) T hT i j hij hz hz'

open CategoryTheory.Pretriangulated in
/-- **The short-exact reduction step.** If the first vertex of a distinguished triangle is
already derived complete and the unit is invertible on `H^{i-1}` and `H^i` at the third vertex,
then it is invertible on `H^i` at the second. -/
private theorem completionUnit_isIso_homology_second_of_complete_first (I : Ideal A) (hI : I.FG)
    (T : Triangle (DerivedCategory (ModuleCat.{u} A))) (hT : T ∈ distTriang _)
    (i : ℤ) (h₁ : IsDerivedComplete I T.obj₁)
    [IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i - 1)).map
      ((adicCompletionUnit A I hI).app T.obj₃))]
    [IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app T.obj₃))] :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app T.obj₂)) := by
  let adj := adicCompletionAdjunction A I hI
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : IsIso ((adicCompletionUnit A I hI).app T.obj₁) :=
    isIso_completionUnit_of_derivedComplete I hI _ h₁
  exact isIso_homology_unit_second_of_isIso_first
    (adicCompletionFunctor A I hI) (adicCompletionUnit A I hI) T hT i

end Completion

/-! ### Local cohomology: linearity, annihilators and the comparison maps -/

section LocalCohomology

variable {A : Type u} [CommRing A]

/-- Local cohomology commutes with the shift. -/
private instance localCohomologyFunctor_commShift (J : Ideal A) (hJ : J.FG) :
    (Dualizing.localCohomologyFunctor.{u, u} A J hJ).CommShift ℤ :=
  let adj : (Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ).ι ⊣
    Dualizing.localCohomologyFunctor A J hJ := Dualizing.localCohomologyAdjunction A J hJ
  adj.rightAdjointCommShift ℤ

/-- Local cohomology is triangulated. -/
private instance localCohomologyFunctor_isTriangulated (J : Ideal A) (hJ : J.FG) :
    (Dualizing.localCohomologyFunctor.{u, u} A J hJ).IsTriangulated := by
  let adj : (Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ).ι ⊣
    Dualizing.localCohomologyFunctor A J hJ := Dualizing.localCohomologyAdjunction A J hJ
  have := adj.commShift_of_leftAdjoint ℤ
  exact adj.isTriangulated_rightAdjoint

/-- **The universal property of local cohomology.** Composing with the counit identifies maps
from a `J`-power-torsion object into `RΓ_{V(J)}(K)` with maps into `K`. -/
private theorem localCohomology_counit_bijective (J : Ideal A) (hJ : J.FG)
    (K W : DerivedCategory (ModuleCat.{u} A))
    (hW : Dualizing.derivedPowerTorsionProperty A J hJ W) :
    Function.Bijective (fun f : W ⟶ ((Dualizing.localCohomologyFunctor A J hJ).obj K).obj =>
      f ≫ (Dualizing.localCohomologyAdjunction A J hJ).counit.app K) :=
  Stacks.LocalCohomology.bijective_comp_localCohomologyCounit.{u, u} J hJ K W hW

/-- Local cohomology is `A`-linear. -/
private theorem localCohomology_map_smul (J : Ideal A) (hJ : J.FG)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (a : A) (f : X ⟶ Y) :
    ((Dualizing.localCohomologyFunctor A J hJ).map (a • f)).hom =
      a • ((Dualizing.localCohomologyFunctor A J hJ).map f).hom := by
  let F := Dualizing.localCohomologyFunctor A J hJ ⋙
    (Dualizing.derivedPowerTorsionProperty A J hJ).ι
  let ε := (Dualizing.localCohomologyAdjunction A J hJ).counit
  exact map_smul_of_counit_hom_injective F ε
    (localCohomology_counit_bijective J hJ Y (F.obj X)
      ((Dualizing.localCohomologyFunctor A J hJ).obj X).property).1 a f

/-- **Local cohomology is `A`-linear**: on each morphism of `D(A)`, the local cohomology functor
`RΓ_{V(J)}` commutes with multiplication by a scalar. -/
alias localCohomologyFunctor_map_smul := localCohomology_map_smul

/-- The annihilator of a module annihilates each of its local cohomology modules. -/
private theorem annihilator_le_localCohomology_homology (J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (i : ℤ) :
    Module.annihilator A M ≤ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) := by
  intro a ha
  have hz : a • 𝟙 M = 0 := by
    ext m
    exact Module.mem_annihilator.mp ha m
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let R := Dualizing.localCohomologyFunctor A J hJ
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  have : Functor.Linear A H := derivedHomologyFunctorLinear i
  have hz' : a • 𝟙 (H.obj (R.obj (S.obj M)).obj) = 0 := by
    have h := congrArg (fun f : M ⟶ M => H.map (R.map (S.map f)).hom) hz
    have hr0 : (R.map (0 : S.obj M ⟶ S.obj M)).hom = 0 := by
      simpa only [zero_smul] using
        (localCohomology_map_smul J hJ (0 : A) (𝟙 (S.obj M)))
    dsimp only [S, R] at h hr0
    rw [Functor.map_smul, CategoryTheory.Functor.map_id, localCohomology_map_smul,
      CategoryTheory.Functor.map_id, Functor.map_zero, hr0] at h
    simp only [ObjectProperty.FullSubcategory.id_hom] at h
    rwa [Functor.map_smul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  exact Module.mem_annihilator.mpr fun m => congrArg (fun f => f.hom m) hz'

/-- A module annihilated by a power of `I` is derived `I`-complete: the recurrence operator of
each element of `I` is invertible because that element acts nilpotently. -/
private theorem isDerivedCompleteModule_of_pow_le_annihilator (I : Ideal A) (n : ℕ)
    (N : ModuleCat.{u} A) (h : (I ^ n : Ideal A) ≤ Module.annihilator A N) :
    IsDerivedCompleteModule I N := by
  intro a ha
  rw [isDerivedCompleteAt_single_iff_isIso_oneSubSmulShift,
    ← isDerivedCompleteAt_iff_isIso]
  refine isDerivedCompleteAt_of_isNilpotent ⟨n, ?_⟩
  ext1
  rw [smul_id_pow, End.zero_asHom]
  exact (smul_id_eq_zero_iff_mem_annihilator N (a ^ n)).2 (h (Ideal.pow_mem_pow ha n))

/-- If a power of `I` annihilates `M`, then `RΓ_{V(J)}(M)` is derived `I`-complete. -/
theorem isDerivedComplete_localCohomology_of_pow_le_annihilator (I J : Ideal A) (hJ : J.FG)
    (n : ℕ) (M : ModuleCat.{u} A) (h : (I ^ n : Ideal A) ≤ Module.annihilator A M) :
    IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj := by
  rw [isDerivedComplete_iff_forall_isDerivedCompleteModule_homology]
  intro i
  exact isDerivedCompleteModule_of_pow_le_annihilator I n _
    (h.trans (annihilator_le_localCohomology_homology J hJ M i))

/-- If `I` annihilates `M`, then `RΓ_{V(J)}(M)` is derived `I`-complete. -/
theorem isDerivedComplete_localCohomology_of_le_annihilator (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A) (h : I ≤ Module.annihilator A M) :
    IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj :=
  isDerivedComplete_localCohomology_of_pow_le_annihilator I J hJ 1 M (by simpa using h)

/-- If the support of `M` misses `V(J)` then every local cohomology module of `M` with support
in `V(J)` vanishes, so `RΓ_{V(J)}(M)` is derived `I`-complete for any `I`. -/
theorem isDerivedComplete_localCohomology_of_disjoint_support (I J : Ideal A) (hJ : J.FG)
    (M : ModuleCat.{u} A)
    (hM : PrimeSpectrum.zeroLocus (Module.annihilator A M : Set A) ∩
      PrimeSpectrum.zeroLocus (J : Set A) = ∅) :
    IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj := by
  rw [isDerivedComplete_iff_forall_isDerivedCompleteModule_homology]
  intro i
  let X := (Dualizing.localCohomologyFunctor A J hJ).obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj X.obj
  have hN : Module.support A N = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    have hpa : Module.annihilator A M ≤ p.asIdeal :=
      (annihilator_le_localCohomology_homology J hJ M i).trans
        (Module.annihilator_le_of_mem_support hp)
    have hpJ := support_subset_zeroLocus_of_isIPowerTorsion (X.property i) hp
    have h : p ∈ PrimeSpectrum.zeroLocus (Module.annihilator A M : Set A) ∩
        PrimeSpectrum.zeroLocus (J : Set A) := ⟨hpa, hpJ⟩
    simp only [hM, Set.mem_empty_iff_false] at h
  have : Subsingleton N := Module.support_eq_empty_iff.mp hN
  exact isDerivedCompleteModule_of_pow_le_annihilator I 1 N fun _ _ =>
    Module.mem_annihilator.mpr fun _ => Subsingleton.elim _ _

end LocalCohomology

/-! ### Derived completeness along short exact sequences -/

section Complete

variable {A : Type u} [CommRing A]

open CategoryTheory.Pretriangulated in
/-- Derived completeness of `RΓ_{V(J)}` of the outer terms of a short exact sequence of modules
passes to the middle term. -/
theorem isDerivedComplete_localCohomology_of_shortExact (I J : Ideal A) (hJ : J.FG)
    (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
    (h₁ : IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj S.X₁)).obj)
    (h₃ : IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj S.X₃)).obj) :
    IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj S.X₂)).obj := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ
  let R := Dualizing.localCohomologyFunctor.{u, u} A J hJ
  exact (Dualizing.derivedCompleteProperty A I).ext_of_isTriangulatedClosed₂
    ((R ⋙ P.ι).mapTriangle.obj hS.singleTriangle)
    ((R ⋙ P.ι).map_distinguished _ hS.singleTriangle_distinguished) h₁ h₃

/-- The unit of derived completion is invertible on a finite module over a ring complete along
`I`, that module being `I`-adically complete. -/
theorem isIso_completionUnit_single [IsNoetherianRing A] (I : Ideal A) (hI : I.FG)
    [IsAdicComplete I A] (M : ModuleCat.{u} A) [Module.Finite A M] :
    IsIso ((adicCompletionUnit A I hI).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) := by
  have hM : IsAdicComplete I (M : Type u) :=
    AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I (M : Type u)
  exact isIso_completionUnit_of_derivedComplete I hI _
    ((isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective A I
      (M : Type u)).1 hM)

/-- Local cohomology of an `I`-power-torsion module over a ring complete along `I` is derived
complete: the counit of the local cohomology adjunction is invertible there, and the module,
placed in degree zero, is derived complete. -/
theorem isDerivedComplete_localCohomology_of_isIPowerTorsion [IsNoetherianRing A]
    (I J : Ideal A) [IsAdicComplete I A]
    (M : ModuleCat.{u} A) [Module.Finite A M] (hM : IsIPowerTorsion A M J) :
    IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J
      J.fg_of_isNoetherianRing).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  have hprop : Dualizing.derivedPowerTorsionProperty A J J.fg_of_isNoetherianRing K :=
    Dualizing.PowerTorsionBaseChange.derivedPowerTorsionProperty_singleFunctor J
      J.fg_of_isNoetherianRing M hM
  have hε : IsIso ((Dualizing.localCohomologyAdjunction A J
      J.fg_of_isNoetherianRing).counit.app K) :=
    Dualizing.isIso_localCohomologyAdjunction_counit A J J.fg_of_isNoetherianRing ⟨K, hprop⟩
  have hK : IsDerivedComplete I K := by
    have hMc : IsAdicComplete I (M : Type u) :=
      AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I (M : Type u)
    exact (isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective A I
      (M : Type u)).1 hMc
  exact DerivedCompleteRecurrence.isDerivedComplete_of_iso
    (asIso ((Dualizing.localCohomologyAdjunction A J
      J.fg_of_isNoetherianRing).counit.app K)).symm hK

end Complete

/-! ### Completion inverts the shrinking comparison -/

section Comparison

variable {A : Type u} [CommRing A]

/-- Local cohomology with support in `V(I)` inverts the comparison
`RΓ_{V(J)}(K) ⟶ RΓ_{V(J')}(K)` attached to a shrinking with the same trace on `V(I)`: both
sides are the coreflection of `K` onto the objects with `(J + I)`-power-torsion cohomology. -/
theorem isIso_localCohomologyDerived_map_localCohomologyComparison
    (I J J' : Ideal A) (hI : I.FG) (hJ : J.FG) (hJ' : J'.FG) (hle : J' ≤ J)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    IsIso ((Dualizing.localCohomologyFunctor A I hI ⋙
        (Dualizing.derivedPowerTorsionProperty A I hI).ι).map
      (localCohomologyComparison A J J' hJ hJ' hle K)) := by
  classical
  let F := Dualizing.localCohomologyFunctor A I hI ⋙
    (Dualizing.derivedPowerTorsionProperty A I hI).ι
  let X₀ := ((Dualizing.localCohomologyFunctor A J hJ).obj K).obj
  let Y₀ := ((Dualizing.localCohomologyFunctor A J' hJ').obj K).obj
  let X := F.obj X₀
  let Y := F.obj Y₀
  let g := localCohomologyComparison A J J' hJ hJ' hle K
  let εI := (Dualizing.localCohomologyAdjunction A I hI).counit
  let εJ := (Dualizing.localCohomologyAdjunction A J hJ).counit
  let εJ' := (Dualizing.localCohomologyAdjunction A J' hJ').counit
  have hXI : Dualizing.derivedPowerTorsionProperty A I hI X :=
    ((Dualizing.localCohomologyFunctor A I hI).obj X₀).property
  have hYI : Dualizing.derivedPowerTorsionProperty A I hI Y :=
    ((Dualizing.localCohomologyFunctor A I hI).obj Y₀).property
  have hJtors : ∀ (J₀ : Ideal A) (hJ₀ : J₀.FG),
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) ⊆
        PrimeSpectrum.zeroLocus (J : Set A) →
      Dualizing.derivedPowerTorsionProperty A J hJ
        (F.obj ((Dualizing.localCohomologyFunctor A J₀ hJ₀).obj K).obj) := by
    intro J₀ hJ₀ hsub i
    refine isIPowerTorsion_of_support_subset hJ ?_
    have hs := support_subset_zeroLocus_of_isIPowerTorsion
      (Dualizing.localCohomology_comp_torsion A J₀ I hJ₀ hI
        ((Dualizing.localCohomologyFunctor A J₀ hJ₀).obj K) i)
    rw [Ideal.add_eq_sup, PrimeSpectrum.zeroLocus_sup] at hs
    exact fun p hp => hsub (hs hp)
  have hXJ := hJtors J hJ Set.inter_subset_left
  have hYJ := hJtors J' hJ' (hV.subset.trans Set.inter_subset_left)
  have hYJ' : Dualizing.derivedPowerTorsionProperty A J' hJ' Y := by
    intro i m
    obtain ⟨n, hn, hm⟩ := hYJ i m
    exact ⟨n, hn, fun a ha => hm a (pow_le_pow_left' hle n ha)⟩
  have hbij : ∀ (J₀ : Ideal A) (hJ₀ : J₀.FG) (W : DerivedCategory (ModuleCat.{u} A)),
      Dualizing.derivedPowerTorsionProperty A I hI W →
      Dualizing.derivedPowerTorsionProperty A J₀ hJ₀ W →
      Function.Bijective
        (fun f : W ⟶ F.obj ((Dualizing.localCohomologyFunctor A J₀ hJ₀).obj K).obj =>
          f ≫ (εI.app ((Dualizing.localCohomologyFunctor A J₀ hJ₀).obj K).obj ≫
            (Dualizing.localCohomologyAdjunction A J₀ hJ₀).counit.app K)) := by
    intro J₀ hJ₀ W hWI hWJ
    convert (localCohomology_counit_bijective J₀ hJ₀ K W hWJ).comp
      (localCohomology_counit_bijective I hI _ W hWI) using 2
    exact (Category.assoc _ _ _).symm
  have hg : g ≫ εJ'.app K = εJ.app K :=
    localCohomologyComparison_comp_counit J J' hJ hJ' hle K
  refine isIso_of_coreflections _ _ (F.map g) ?_ (hbij J hJ X hXI hXJ).1
    (hbij J hJ Y hYI hYJ).2 (hbij J' hJ' Y hYI hYJ').1
  have hnat : F.map g ≫ εI.app Y₀ = εI.app X₀ ≫ g := εI.naturality g
  exact ((Category.assoc (F.map g) (εI.app Y₀) (εJ'.app K)).symm.trans
      (congrArg (fun t => t ≫ εJ'.app K) hnat)).trans
    ((Category.assoc (εI.app X₀) g (εJ'.app K)).trans
      (congrArg (fun t => εI.app X₀ ≫ t) hg))

/-- **Derived `I`-adic completion inverts the shrinking comparison.** -/
theorem isIso_completionFunctor_map_localCohomologyComparison
    (I J J' : Ideal A) (hI : I.FG) (hJ : J.FG) (hJ' : J'.FG) (hle : J' ≤ J)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hV : PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    IsIso ((adicCompletionFunctor A I hI).map
      (localCohomologyComparison A J J' hJ hJ' hle K)) := by
  have hF := isIso_localCohomologyDerived_map_localCohomologyComparison I J J' hI hJ hJ' hle K hV
  have hmap : IsIso ((adicCompletionFunctor A I hI).map
      ((Dualizing.localCohomologyFunctor A I hI ⋙
        (Dualizing.derivedPowerTorsionProperty A I hI).ι).map
        (localCohomologyComparison A J J' hJ hJ' hle K))) := by
    infer_instance
  exact completion_map_isIso_of_localization_map_isIso (adicCompletionFunctor A I hI)
    (Dualizing.localCohomologyFunctor A I hI ⋙
      (Dualizing.derivedPowerTorsionProperty A I hI).ι)
    (Dualizing.localCohomologyAdjunction A I hI).counit _ hmap
    (Dualizing.isIso_derivedCompletion_map_localCohomologyCounit A I hI
      (Dualizing.derivedCompletion A I hI) (adicCompletionAdjunction A I hI) _)
    (Dualizing.isIso_derivedCompletion_map_localCohomologyCounit A I hI
      (Dualizing.derivedCompletion A I hI) (adicCompletionAdjunction A I hI) _)

/-- The completion unit is invertible on cohomology in negative degrees, both sides vanishing
there. -/
theorem isIso_homology_completionUnit_localCohomology_of_neg [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG)
    (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℤ) (hi : i < 0) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)) :=
  IsZero.isIso
    (Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg A J hJ M i hi)
    (Dualizing.isZero_homology_completedLocalCohomology_of_neg A I J hI hJ M
      (Dualizing.isDerivedLimit_completedLocalCohomology A I J hI hJ M) i hi) _

end Comparison

/-! ### The two inductive steps -/

section Steps

variable {A : Type u} [CommRing A]

open CategoryTheory.Pretriangulated in
/-- **The reduction along a short exact sequence.** If `RΓ_{V(J)}` of the sub is already derived
complete and the completion unit is invertible on `H^{i-1}` and `H^i` of `RΓ_{V(J)}` of the
quotient, then it is invertible on `H^i` of `RΓ_{V(J)}` of the middle term. -/
theorem completionUnit_localCohomology_isIso_of_shortExact (I J : Ideal A) (hI : I.FG)
    (hJ : J.FG) (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
    (h₁ : IsDerivedComplete I ((Dualizing.localCohomologyFunctor A J hJ).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj S.X₁)).obj)
    (i : ℤ)
    (h₃ : ∀ j ∈ ({i - 1, i} : Set ℤ),
      IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
        ((adicCompletionUnit A I hI).app
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj S.X₃)).obj))) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj S.X₂)).obj)) := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ
  let R := Dualizing.localCohomologyFunctor.{u, u} A J hJ
  let T := (R ⋙ P.ι).mapTriangle.obj hS.singleTriangle
  have hT₃ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i - 1)).map
      ((adicCompletionUnit A I hI).app T.obj₃)) := h₃ (i - 1) (by simp)
  have hT₃' : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app T.obj₃)) := h₃ i (by simp)
  exact completionUnit_isIso_homology_second_of_complete_first I hI T
    ((R ⋙ P.ι).map_distinguished _ hS.singleTriangle_distinguished) i h₁

open CategoryTheory.Pretriangulated in
/-- **The degree-raising step.** Let `a` be a nonzerodivisor on `M` annihilating `H^j_{V(J)}(M)`
and `H^j(RΓ_{V(J)}(M)^∧)`. If the completion unit is invertible on `H^{j-1}` for `M` and for
`M/aM`, it is invertible on `H^j` for `M`. -/
theorem completionUnit_localCohomology_isIso_of_regular_annihilator (I J : Ideal A) (hI : I.FG)
    (hJ : J.FG) (M : ModuleCat.{u} A) (a : A) (ha : IsSMulRegular M a)
    (i j : ℤ) (hij : i + 1 = j)
    (hann : a ∈ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj))
    (hcomplete : a ∈ Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((adicCompletionFunctor A I hI).obj
          ((Dualizing.localCohomologyFunctor A J hJ).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)))
    (hM : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)))
    (hN : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (QuotSMulTop a M)))).obj))) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      ((adicCompletionUnit A I hI).app
        ((Dualizing.localCohomologyFunctor A J hJ).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj)) := by
  let P := Dualizing.derivedPowerTorsionProperty.{u, u} A J hJ
  let R := Dualizing.localCohomologyFunctor.{u, u} A J hJ
  let L := R ⋙ P.ι
  let T := L.mapTriangle.obj ha.smulShortComplex_shortExact.singleTriangle
  have hT : T ∈ distTriang _ := L.map_distinguished _
    ha.smulShortComplex_shortExact.singleTriangle_distinguished
  have hid : ((Dualizing.localCohomologyFunctor A J hJ).map
      (𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))).hom =
      𝟙 (((Dualizing.localCohomologyFunctor A J hJ).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)).obj) := by
    simp
  have hsingle : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
      ((ModuleCat.smulShortComplex M a).f) =
      a • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) :=
    (congrArg (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.smulShortComplex_f_eq_smul_id M a)).trans
      (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map_smul a (𝟙 M)).trans
        (congrArg (fun t => a • t)
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map_id M)))
  have hmor : T.mor₁ = a • 𝟙 T.obj₁ :=
    (congrArg (fun g => ((Dualizing.localCohomologyFunctor A J hJ).map g).hom) hsingle).trans
      ((localCohomology_map_smul J hJ a
        (𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M))).trans
        (congrArg (fun t => a • t) hid))
  have hz : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map T.mor₁ = 0 :=
    (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map hmor).trans
      (homology_map_smul_id_eq_zero _ _ _ hann)
  have hcmor : (adicCompletionFunctor A I hI).map T.mor₁ =
      a • 𝟙 ((adicCompletionFunctor A I hI).obj T.obj₁) :=
    (congrArg (adicCompletionFunctor A I hI).map hmor).trans
      ((completionFunctor_map_smul I hI a (𝟙 T.obj₁)).trans
        (congrArg (fun t => a • t) ((adicCompletionFunctor A I hI).map_id T.obj₁)))
  have hz' : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map
      ((adicCompletionFunctor A I hI).map T.mor₁) = 0 :=
    (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).map hcmor).trans
      (homology_map_smul_id_eq_zero _ _ _ hcomplete)
  have h₂ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app T.obj₂)) := hM
  have h₃ : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
      ((adicCompletionUnit A I hI).app T.obj₃)) := hN
  exact completionUnit_isIso_homology_of_zero_first_maps I hI T hT i j hij hz hz'

end Steps

end Stacks.Algebraization

end
