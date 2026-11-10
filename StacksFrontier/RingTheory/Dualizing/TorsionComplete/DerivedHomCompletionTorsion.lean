module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.CechCompletion
import all StacksFrontier.Homology.DerivedComplete.CechCompletion
public import StacksFrontier.Homology.DerivedComplete.CechReflection
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionHom
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.Equivalence
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.LocalCohomologyAfterCompletion
import all StacksFrontier.RingTheory.Dualizing.TorsionComplete.LocalCohomologyAfterCompletion
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.TensorCompatibility

/-!
# Derived Hom between completions and between local cohomologies

Let `A` be a commutative ring, let `I = (f₁, …, f_r) ⊆ A` be a finitely generated ideal and let
`Z = V(I)`. Write `(-)^∧` for derived `I`-adic completion and `RΓ_Z` for local cohomology with
support in `Z`. For objects `K, L` of `D(A)` there is a canonical isomorphism

`RHom_A(K^∧, L^∧) ≅ RHom_A(RΓ_Z(K), RΓ_Z(L))`

in `D(A)`, together with its naturality in `K`. Both functors are computed from the extended
alternating Čech complex `Č(f)`: completion as `RHom_A(Č(f), -)` and local cohomology as
`- ⊗ᴸ_A Č(f)`.

## Main definitions

* `Dualizing.reflectionAdjunctionOfUniversal` — a unit with a universal property presents its
  functor as the left adjoint of the inclusion of a full subcategory.
* `Dualizing.cechTorsionFunctor`, `Dualizing.cechTorsionCounit` — the Čech model `- ⊗ᴸ_A Č(f)`
  of `RΓ_Z` and its comparison map to the identity.
* `Dualizing.localCohomologyCechTensorIso` — the Čech formula `RΓ_Z ≅ - ⊗ᴸ_A Č(f)` in this
  tensor product, normalized by the counit.
* `Dualizing.derivedHomCompletionUnitIso`, `Dualizing.derivedHomCompletionCounitIso`,
  `Dualizing.cechCurryIso`, `Dualizing.derivedHomCechTensorIso` — the four isomorphisms whose
  composite is `Dualizing.derivedHomCompletionTorsionIso`.
* `Dualizing.derivedHomCompletionTorsionIso` — the isomorphism
  `RHom_A(K^∧, L^∧) ≅ RHom_A(RΓ_Z(K), RΓ_Z(L))`.
* `Dualizing.derivedHomInto`, `Dualizing.derivedHomIntoMapIso` — derived Hom into a fixed
  object as a contravariant functor of its source, and the functor isomorphism induced by an
  isomorphism of that object.
* `Dualizing.derivedCompletionDerivedHomTorsionNatIso` — the isomorphism
  `RHom_A(-, L)^∧ ≅ RHom_A(RΓ_Z(-), RΓ_Z(L))` of contravariant functors on `D(A)`.

## Main results

* `Dualizing.derivedPowerTorsion_derivedTensor` — the derived tensor product of the
  tensor--Hom adjunction preserves `I`-power-torsion cohomology in its second variable.
* `Dualizing.isIso_cechTorsionFunctor_map_cechTorsionCounit` — the Čech model inverts its own
  comparison map.
* `Dualizing.exists_localCohomologyCechTensorIso` and
  `Dualizing.localCohomologyCechTensorIso_comp_counit` — the normalized Čech formula.
* `Dualizing.isIso_derivedHom_map_derivedCompletionUnit` — precomposition with the completion
  unit is invertible on derived Hom with derived complete target.
* `Dualizing.isIso_derivedCompletion_map_cechTorsionCounit` — the Čech comparison map becomes
  invertible after derived completion.
* `Dualizing.derivedHomCompletionTorsionIso_hom_comp` — the normalization of the isomorphism.
* `Dualizing.derivedHomCompletionTorsionIso_naturality_left` — the isomorphism is natural in its
  source variable.

## References

* [Stacks Project, Tag 0A6Y](https://stacks.math.columbia.edu/tag/0A6Y)
* [Stacks Project, Tag 0A6W](https://stacks.math.columbia.edu/tag/0A6W)
* [Stacks Project, Tag 0A6X](https://stacks.math.columbia.edu/tag/0A6X)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0A65](https://stacks.math.columbia.edu/tag/0A65)
* [Stacks Project, Tag 0A6B](https://stacks.math.columbia.edu/tag/0A6B)
* [Stacks Project, Tag 0A6E](https://stacks.math.columbia.edu/tag/0A6E)
* [Stacks Project, Tag 091V](https://stacks.math.columbia.edu/tag/091V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor Stacks.LocalCohomology Stacks.LocalCohomology.CechFormula

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

section Reflection

variable {C : Type*} [Category C] (P : ObjectProperty C)
    (F : C ⥤ C) (η : 𝟭 C ⟶ F) (hF : ∀ X, P (F.obj X))
    (hη : ∀ X E, P E → Function.Bijective (fun g : F.obj X ⟶ E ↦ η.app X ≫ g))

/-- Composition with a universal unit, as a bijection of morphism sets in the full subcategory
cut out by `P`. -/
def reflectionHomEquivOfUniversal (X : C) (E : P.FullSubcategory) :
    ((P.lift F hF).obj X ⟶ E) ≃ (X ⟶ P.ι.obj E) :=
  Equiv.ofBijective (fun g ↦ η.app X ≫ g.hom) (by
    refine ⟨fun g g' h ↦ ?_, fun g ↦ ?_⟩
    · exact P.ι.map_injective ((hη X E.obj E.property).injective h)
    · obtain ⟨h, hh⟩ := (hη X E.obj E.property).surjective g
      exact ⟨ObjectProperty.homMk h, hh⟩)

/-- If `η : 𝟭 C ⟶ F` takes values in the objects satisfying `P` and its components are universal
among maps into such objects, then `F` corestricted to `P` is left adjoint to the inclusion. -/
def reflectionAdjunctionOfUniversal : P.lift F hF ⊣ P.ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := reflectionHomEquivOfUniversal P F η hF hη
      homEquiv_naturality_left_symm := fun {X' X E} f g ↦ by
        apply (reflectionHomEquivOfUniversal P F η hF hη X' E).injective
        rw [Equiv.apply_symm_apply]
        have hn : η.app X' ≫ F.map f = f ≫ η.app X := (η.naturality f).symm
        change f ≫ g = η.app X' ≫ ((P.lift F hF).map f ≫
          (reflectionHomEquivOfUniversal P F η hF hη X E).symm g).hom
        rw [ObjectProperty.FullSubcategory.comp_hom, ← Category.assoc]
        change f ≫ g = (η.app X' ≫ F.map f) ≫ _
        rw [hn, Category.assoc]
        exact (congrArg (fun k ↦ f ≫ k)
          ((reflectionHomEquivOfUniversal P F η hF hη X E).apply_symm_apply g)).symm
      homEquiv_naturality_right := fun {X E E'} f g ↦ by
        change η.app X ≫ (f ≫ g).hom = (η.app X ≫ f.hom) ≫ g.hom
        rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc] }

end Reflection

section CechModel

variable (A : Type u) [CommRing A] {r : ℕ}

/-- Derived Hom into a fixed object, as a contravariant functor of its source:
`K ↦ RHom_A(K, L)`. -/
abbrev derivedHomInto (L : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCategory (ModuleCat.{u} A))ᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Functor.prod' (Functor.id _) ((Functor.const _).obj L) ⋙
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom

/-- An isomorphism of the target object of derived Hom, read as an isomorphism of the
contravariant functors of the source that the two objects define. -/
def derivedHomIntoMapIso {N N' : DerivedCategory (ModuleCat.{u} A)} (e : N ≅ N') :
    derivedHomInto A N ≅ derivedHomInto A N' :=
  NatIso.ofComponents
    (fun K ↦ (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
      ((Iso.refl K).prod e))
    (by
      intro X Y g
      let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
      change d.hom.map (show (X, N) ⟶ (Y, N) from (g, 𝟙 N)) ≫
          d.hom.map (show (Y, N) ⟶ (Y, N') from (𝟙 Y, e.hom)) =
        d.hom.map (show (X, N) ⟶ (X, N') from (𝟙 X, e.hom)) ≫
          d.hom.map (show (X, N') ⟶ (Y, N') from (g, 𝟙 N'))
      rw [← d.hom.map_comp, ← d.hom.map_comp]
      congr 1
      refine Prod.ext ?_ ?_ <;> simp)

/-- Derived tensor product with the extended alternating Čech complex of `f`, as an endofunctor
of `D(A)`: the Čech model of local cohomology with support in `V(f₁, …, f_r)`. -/
def cechTorsionFunctor (f : Fin r → A) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (Functor.id (DerivedCategory (ModuleCat.{u} A))).prod'
      ((Functor.const (DerivedCategory (ModuleCat.{u} A))).obj
        (CechCompletion.extendedCechObject A f)) ⋙
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor

/-- The Čech augmentation `Č(f) ⟶ A[0]`, tensored on the right: the natural map
`K ⊗ᴸ_A Č(f) ⟶ K`. -/
@[no_expose]
def cechTorsionCounit (f : Fin r → A) : cechTorsionFunctor A f ⟶ 𝟭 _ where
  app X := (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor.map
      (show (X, CechCompletion.extendedCechObject A f) ⟶
        (X, DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ))) from
        (𝟙 X, DerivedCategory.Q.map (CechCompletion.cechAugmentation f (ModuleCat.of A A)))) ≫
    (CechCompletion.tensorUnitRight (StacksDraft.DerivedHom.derivedHomAdjunction (R := A))
      StacksDraft.DerivedHom.derivedHomCurrying X).hom
  naturality := by
    intro X Y g
    let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
    let c := StacksDraft.DerivedHom.derivedHomCurrying (R := A)
    let B := CechCompletion.extendedCechObject A f
    let a : B ⟶ DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ)) :=
      DerivedCategory.Q.map (CechCompletion.cechAugmentation f (ModuleCat.of A A))
    change d.tensor.map (show (X, B) ⟶ (Y, B) from (g, 𝟙 B)) ≫
        (d.tensor.map (show (Y, B) ⟶
          (Y, DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ))) from (𝟙 Y, a)) ≫
          (CechCompletion.tensorUnitRight d c Y).hom) =
      (d.tensor.map (show (X, B) ⟶
        (X, DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ))) from (𝟙 X, a)) ≫
        (CechCompletion.tensorUnitRight d c X).hom) ≫ g
    rw [← Category.assoc, d.tensor_map_comp, Category.assoc,
      ← CechCompletion.tensorUnitRight_naturality d c g, ← Category.assoc, d.tensor_map_comp]
    simp

/-- The Čech comparison map `K ⊗ᴸ_A Č(f) ⟶ K` is invertible on complexes with
`I`-power-torsion cohomology. -/
theorem isIso_cechTorsionCounit_app (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (X : DerivedCategory (ModuleCat.{u} A))
    (hX : derivedPowerTorsionProperty A I hI X) :
    IsIso ((cechTorsionCounit A f).app X) :=
  isIso_tensor_cechAugmentation_of_powerTorsion A I hI f hf X hX

/-- The derived tensor product of the tensor--Hom adjunction preserves `I`-power-torsion
cohomology in the second variable. -/
theorem derivedPowerTorsion_derivedTensor (I : Ideal A) (hI : I.FG)
    (X Y : DerivedCategory (ModuleCat.{u} A)) (hY : derivedPowerTorsionProperty A I hI Y) :
    derivedPowerTorsionProperty A I hI
      ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor.obj (X, Y)) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := exists_kFlat_representative X
  obtain ⟨N, hN, ⟨eN⟩⟩ := exists_kFlat_representative Y
  have hYN : derivedPowerTorsionProperty A I hI (DerivedCategory.Q.obj N) :=
    (derivedPowerTorsionProperty A I hI).prop_of_iso eN.symm hY
  refine (derivedPowerTorsionProperty A I hI).prop_of_iso ?_
    (derivedTensorProduct_mem_powerTorsion_right A I hI
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) hYN)
  exact (canonicalDerivedTensorProduct A).comparison P N hP hN ≪≫
    ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensorIso P N hN).symm ≪≫
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor.mapIso (eP.prod eN)

/-- The extended alternating Čech complex of the ring has `I`-power-torsion cohomology. -/
theorem derivedPowerTorsion_extendedCechObject (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    derivedPowerTorsionProperty A I hI (CechCompletion.extendedCechObject A f) :=
  (derivedPowerTorsionProperty A I hI).prop_of_iso
    (DerivedCategory.Q.mapIso (extendedCechComplexULiftIso A f))
    (cechRegular_derivedPowerTorsion.{u, u} f I hI hf)

/-- Tensoring the Čech augmentation with the Čech complex is invertible. -/
private theorem isIso_tensor_cechAugmentation_left (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    IsIso ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor.map
      (show (CechCompletion.extendedCechObject A f, CechCompletion.extendedCechObject A f) ⟶
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ)),
          CechCompletion.extendedCechObject A f) from
        (DerivedCategory.Q.map (CechCompletion.cechAugmentation f (ModuleCat.of A A)),
          𝟙 (CechCompletion.extendedCechObject A f)))) := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let c := StacksDraft.DerivedHom.derivedHomCurrying (R := A)
  let B := CechCompletion.extendedCechObject A f
  let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ))
  let a : B ⟶ U := DerivedCategory.Q.map (CechCompletion.cechAugmentation f (ModuleCat.of A A))
  have : IsIso (d.tensor.map (show (B, B) ⟶ (B, U) from (𝟙 B, a)) ≫
      (CechCompletion.tensorUnitRight d c B).hom) :=
    isIso_cechTorsionCounit_app A I hI f hf B (derivedPowerTorsion_extendedCechObject A I hI f hf)
  exact (isIso_iff_of_commSq _ _ (d.tensorSwap B B) (d.tensorSwap U B)
    (d.tensorSwap_naturality a (𝟙 B))).mpr
    (IsIso.of_isIso_comp_right _ (CechCompletion.tensorUnitRight d c B).hom)

/-- The Čech model of `RΓ_Z` inverts its own comparison map. -/
theorem isIso_cechTorsionFunctor_map_cechTorsionCounit (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (X : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((cechTorsionFunctor A f).map ((cechTorsionCounit A f).app X)) := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let c := StacksDraft.DerivedHom.derivedHomCurrying (R := A)
  let B := CechCompletion.extendedCechObject A f
  let U := DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ))
  let a : B ⟶ U := DerivedCategory.Q.map (CechCompletion.cechAugmentation f (ModuleCat.of A A))
  have hsplit : (cechTorsionFunctor A f).map ((cechTorsionCounit A f).app X) =
      d.tensor.map (show (d.tensor.obj (X, B), B) ⟶ (d.tensor.obj (X, U), B) from
          (d.tensor.map (show (X, B) ⟶ (X, U) from (𝟙 X, a)), 𝟙 B)) ≫
        d.tensor.map (show (d.tensor.obj (X, U), B) ⟶ (X, B) from
          ((CechCompletion.tensorUnitRight d c X).hom, 𝟙 B)) := by
    rw [d.tensor_map_comp, Category.comp_id]
    rfl
  rw [hsplit]
  have h2 : IsIso (d.tensor.map (show (d.tensor.obj (X, U), B) ⟶ (X, B) from
      ((CechCompletion.tensorUnitRight d c X).hom, 𝟙 B))) := by
    have : IsIso (show (d.tensor.obj (X, U), B) ⟶ (X, B) from
        ((CechCompletion.tensorUnitRight d c X).hom, 𝟙 B)) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    infer_instance
  have h3 : IsIso (d.tensor.map (show (X, d.tensor.obj (B, B)) ⟶ (X, d.tensor.obj (U, B)) from
      (𝟙 X, d.tensor.map (show (B, B) ⟶ (U, B) from (a, 𝟙 B))))) := by
    have : IsIso (show (X, d.tensor.obj (B, B)) ⟶ (X, d.tensor.obj (U, B)) from
        (𝟙 X, d.tensor.map (show (B, B) ⟶ (U, B) from (a, 𝟙 B)))) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, isIso_tensor_cechAugmentation_left A I hI f hf⟩
    infer_instance
  have h1 := (isIso_iff_of_commSq _ _ (d.tensorAssoc X B B) (d.tensorAssoc X U B)
    (d.tensorAssoc_naturality (𝟙 X) a (𝟙 B))).mpr h3
  exact IsIso.comp_isIso' h1 h2

/-- Local cohomology with support in `V(I)` is derived tensor product with the extended
alternating Čech complex of a finite generating family, by an isomorphism carrying the Čech
comparison map to the counit of the adjunction defining `RΓ_Z`. -/
theorem exists_localCohomologyCechTensorIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    ∃ e : localCohomologyEndofunctor A I hI ≅ cechTorsionFunctor A f,
      e.hom ≫ cechTorsionCounit A f = (localCohomologyAdjunction A I hI).counit :=
  exists_normalized_coreflectionIso (derivedPowerTorsionProperty A I hI)
    (localCohomologyFunctor A I hI) (localCohomologyAdjunction A I hI)
    (cechTorsionFunctor A f) (cechTorsionCounit A f)
    (fun X ↦ derivedPowerTorsion_derivedTensor A I hI X _
      (derivedPowerTorsion_extendedCechObject A I hI f hf))
    (fun Y hY ↦ isIso_cechTorsionCounit_app A I hI f hf Y hY)
    (fun X ↦ isIso_cechTorsionFunctor_map_cechTorsionCounit A I hI f hf X)

/-- The Čech formula `RΓ_Z ≅ - ⊗ᴸ_A Č(f)`, as a chosen isomorphism carrying the Čech comparison
map to the counit of the adjunction defining `RΓ_Z`. -/
def localCohomologyCechTensorIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    localCohomologyEndofunctor A I hI ≅ cechTorsionFunctor A f :=
  Classical.choose
    (p := fun e ↦ e.hom ≫ cechTorsionCounit A f = (localCohomologyAdjunction A I hI).counit)
    (exists_localCohomologyCechTensorIso A I hI f hf)

/-- The Čech formula is normalized: it carries the Čech comparison map to the counit of the
adjunction that defines `RΓ_Z`. -/
theorem localCohomologyCechTensorIso_comp_counit (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) :
    (localCohomologyCechTensorIso A I hI f hf).hom ≫ cechTorsionCounit A f =
      (localCohomologyAdjunction A I hI).counit :=
  (exists_localCohomologyCechTensorIso A I hI f hf).choose_spec

end CechModel

section Completion

variable (A : Type u) [CommRing A] {r : ℕ}

attribute [local instance] hasProductsOfShape_nat_derivedCategory

/-- Precomposition with the derived-completion unit is invertible on derived
Hom with derived complete target: `RHom_A(K^∧, M^∧) ⟶ RHom_A(K, M^∧)` is an isomorphism. -/
theorem isIso_derivedHom_map_derivedCompletionUnit (f : Fin r → A)
    (K M : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
      (show (Opposite.op ((DerivedCompletion.derivedCompletionFunctor A f).obj K),
            (DerivedCompletion.derivedCompletionFunctor A f).obj M) ⟶
          (Opposite.op K, (DerivedCompletion.derivedCompletionFunctor A f).obj M) from
        (((DerivedCompletion.derivedCompletionUnit A f).app K).op,
          𝟙 ((DerivedCompletion.derivedCompletionFunctor A f).obj M)))) := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let F := DerivedCompletion.derivedCompletionFunctor A f
  let ε := DerivedCompletion.derivedCompletionUnit A f
  have hε := DerivedCompletion.derivedCompletion_isReflection A f
  obtain ⟨η, hFc, hηc, -, e₀, he₀⟩ := DerivedHomCechCompletion.derivedHom_cechCompletion A f
  obtain ⟨w, hw⟩ := exists_iso_of_bijective_precomp (ε.app K) (η.app K)
    (hε.2 K _ (hε.1 K)) (hηc K _ (hε.1 K))
  have hiso : IsIso (e₀.hom.app (Opposite.op K, M)) :=
    (e₀.app (Opposite.op K, M)).isIso_hom
  rw [he₀ K M] at hiso
  have hprod : (show (Opposite.op (F.obj K), F.obj M) ⟶ (Opposite.op K, F.obj M) from
        ((η.app K).op, 𝟙 (F.obj M))) =
      (show (Opposite.op (F.obj K), F.obj M) ⟶ (Opposite.op (F.obj K), F.obj M) from
        (w.hom.op, 𝟙 (F.obj M))) ≫
      (show (Opposite.op (F.obj K), F.obj M) ⟶ (Opposite.op K, F.obj M) from
        ((ε.app K).op, 𝟙 (F.obj M))) := by
    apply Prod.ext
    · change (η.app K).op = w.hom.op ≫ (ε.app K).op
      rw [← op_comp, hw]
    · simp
  have hpi : IsIso (show (Opposite.op (F.obj K), F.obj M) ⟶
      (Opposite.op (F.obj K), F.obj M) from (w.hom.op, 𝟙 (F.obj M))) :=
    (isIso_prod_iff _ _).mpr ⟨w.op.isIso_hom, inferInstance⟩
  rw [hprod, d.hom.map_comp] at hiso
  exact IsIso.of_isIso_comp_left (d.hom.map
    (show (Opposite.op (F.obj K), F.obj M) ⟶ (Opposite.op (F.obj K), F.obj M) from
      (w.hom.op, 𝟙 (F.obj M)))) _

/-- The isomorphism `RHom_A(K^∧, M^∧) ≅ RHom_A(K, M^∧)` given by precomposition with the
derived-completion unit `K ⟶ K^∧`. -/
def derivedHomCompletionUnitIso (f : Fin r → A) (K M : DerivedCategory (ModuleCat.{u} A)) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((DerivedCompletion.derivedCompletionFunctor A f).obj K),
          (DerivedCompletion.derivedCompletionFunctor A f).obj M) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op K, (DerivedCompletion.derivedCompletionFunctor A f).obj M) :=
  letI := isIso_derivedHom_map_derivedCompletionUnit A f K M
  asIso ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.map
    (show (Opposite.op ((DerivedCompletion.derivedCompletionFunctor A f).obj K),
          (DerivedCompletion.derivedCompletionFunctor A f).obj M) ⟶
        (Opposite.op K, (DerivedCompletion.derivedCompletionFunctor A f).obj M) from
      (((DerivedCompletion.derivedCompletionUnit A f).app K).op,
        𝟙 ((DerivedCompletion.derivedCompletionFunctor A f).obj M))))

/-- The Čech comparison map `L ⊗ᴸ_A Č(f) ⟶ L` becomes invertible after derived `I`-adic
completion. -/
theorem isIso_derivedCompletion_map_cechTorsionCounit (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (L : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((DerivedCompletion.derivedCompletionFunctor A f).map
      ((cechTorsionCounit A f).app L)) := by
  let F := DerivedCompletion.derivedCompletionFunctor A f
  let ε := DerivedCompletion.derivedCompletionUnit A f
  have hε := DerivedCompletion.derivedCompletion_isReflection A f
  have hFc : ∀ X, derivedCompleteProperty A I (F.obj X) := fun X ↦ hf ▸ hε.1 X
  have hb : ∀ X E, derivedCompleteProperty A I E →
      Function.Bijective (fun g : F.obj X ⟶ E ↦ ε.app X ≫ g) := fun X E hE ↦
    hε.2 X E (by rwa [hf])
  have : IsIso (F.map ((localCohomologyAdjunction A I hI).counit.app L)) :=
    isIso_derivedCompletion_map_localCohomologyCounit A I hI
      ((derivedCompleteProperty A I).lift F hFc)
      (reflectionAdjunctionOfUniversal (derivedCompleteProperty A I) F ε hFc hb) L
  have happ : (localCohomologyCechTensorIso A I hI f hf).hom.app L ≫
      (cechTorsionCounit A f).app L = (localCohomologyAdjunction A I hI).counit.app L :=
    NatTrans.congr_app (localCohomologyCechTensorIso_comp_counit A I hI f hf) L
  have : IsIso (F.map ((localCohomologyCechTensorIso A I hI f hf).hom.app L) ≫
      F.map ((cechTorsionCounit A f).app L)) := by
    rwa [← F.map_comp, happ]
  exact IsIso.of_isIso_comp_left
    (F.map ((localCohomologyCechTensorIso A I hI f hf).hom.app L)) _

/-- The isomorphism `RHom_A(K, (L ⊗ᴸ_A Č(f))^∧) ≅ RHom_A(K, L^∧)` induced by the completed Čech
comparison map. -/
def derivedHomCompletionCounitIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (K L : DerivedCategory (ModuleCat.{u} A)) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op K, (DerivedCompletion.derivedCompletionFunctor A f).obj
          ((cechTorsionFunctor A f).obj L)) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op K, (DerivedCompletion.derivedCompletionFunctor A f).obj L) :=
  letI := isIso_derivedCompletion_map_cechTorsionCounit A I hI f hf L
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
    ((Iso.refl (Opposite.op K)).prod
      (asIso ((DerivedCompletion.derivedCompletionFunctor A f).map
        ((cechTorsionCounit A f).app L))))

/-- Currying: `RHom_A(K, RHom_A(Č(f), M)) ≅ RHom_A(K ⊗ᴸ_A Č(f), M)`. -/
def cechCurryIso (f : Fin r → A) (K M : DerivedCategory (ModuleCat.{u} A)) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op K, (DerivedCompletion.derivedCompletionFunctor A f).obj M) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((cechTorsionFunctor A f).obj K), M) :=
  StacksDraft.DerivedHom.derivedHomCurrying.iso K (CechCompletion.extendedCechObject A f) M

/-- The Čech formula for `RΓ_Z`, transported into derived Hom:
`RHom_A(K ⊗ᴸ_A Č(f), L ⊗ᴸ_A Č(f)) ≅ RHom_A(RΓ_Z(K), RΓ_Z(L))`. -/
def derivedHomCechTensorIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (K L : DerivedCategory (ModuleCat.{u} A)) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((cechTorsionFunctor A f).obj K), (cechTorsionFunctor A f).obj L) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((localCohomologyEndofunctor A I hI).obj K),
          (localCohomologyEndofunctor A I hI).obj L) :=
  (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.mapIso
    (((localCohomologyCechTensorIso A I hI f hf).app K).op.prod
      ((localCohomologyCechTensorIso A I hI f hf).app L).symm)

/-- For `A` a commutative ring, `I` a finitely generated ideal, `Z = V(I)`, `(-)^∧` derived
`I`-adic completion and `RΓ_Z` local cohomology, the canonical isomorphism
`RHom_A(K^∧, L^∧) ≅ RHom_A(RΓ_Z(K), RΓ_Z(L))` in `D(A)`. -/
@[stacks 0A6Y]
def derivedHomCompletionTorsionIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (K L : DerivedCategory (ModuleCat.{u} A)) :
    (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((DerivedCompletion.derivedCompletionFunctor A f).obj K),
          (DerivedCompletion.derivedCompletionFunctor A f).obj L) ≅
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((localCohomologyEndofunctor A I hI).obj K),
          (localCohomologyEndofunctor A I hI).obj L) :=
  derivedHomCompletionUnitIso A f K L ≪≫
    (derivedHomCompletionCounitIso A I hI f hf K L).symm ≪≫
    cechCurryIso A f K ((cechTorsionFunctor A f).obj L) ≪≫
    derivedHomCechTensorIso A I hI f hf K L

/-- Transporting `Dualizing.derivedHomCompletionTorsionIso` back along the Čech formula,
uncurrying, and completing the Čech comparison map recovers precomposition with the
derived-completion unit. -/
theorem derivedHomCompletionTorsionIso_hom_comp (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (K L : DerivedCategory (ModuleCat.{u} A)) :
    (derivedHomCompletionTorsionIso A I hI f hf K L).hom ≫
        (derivedHomCechTensorIso A I hI f hf K L).inv ≫
        (cechCurryIso A f K ((cechTorsionFunctor A f).obj L)).inv ≫
        (derivedHomCompletionCounitIso A I hI f hf K L).hom =
      (derivedHomCompletionUnitIso A f K L).hom := by
  simp [derivedHomCompletionTorsionIso]

/-- `RHom_A(-, -)` takes a commuting square in the first variable, with a fixed map `v` in the
second, to a commuting square. -/
private theorem derivedHom_map_comm_square {X X' Y Y' N N' : DerivedCategory (ModuleCat.{u} A)}
    (a : X' ⟶ X) (b : Y' ⟶ X') (b' : Y ⟶ X) (a' : Y' ⟶ Y) (v : N ⟶ N') (h : b ≫ a = a' ≫ b') :
    let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
    d.hom.map ((a.op, 𝟙 N) : (Opposite.op X, N) ⟶ (Opposite.op X', N)) ≫
        d.hom.map ((b.op, v) : (Opposite.op X', N) ⟶ (Opposite.op Y', N')) =
      d.hom.map ((b'.op, v) : (Opposite.op X, N) ⟶ (Opposite.op Y, N')) ≫
        d.hom.map ((a'.op, 𝟙 N') : (Opposite.op Y, N') ⟶ (Opposite.op Y', N')) := by
  intro d
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact Prod.ext (congrArg Quiver.Hom.op h) (by simp)

/-- `Dualizing.derivedHomCompletionUnitIso` is natural in its source variable. -/
theorem derivedHomCompletionUnitIso_naturality_left (f : Fin r → A)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    ((DerivedCompletion.derivedCompletionFunctor A f).op ⋙
          derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L)).map g.op ≫
        (derivedHomCompletionUnitIso A f K' L).hom =
      (derivedHomCompletionUnitIso A f K L).hom ≫
        (derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L)).map g.op := by
  exact derivedHom_map_comm_square A _ _ _ _ _
    ((DerivedCompletion.derivedCompletionUnit A f).naturality g).symm

/-- `Dualizing.derivedHomCompletionCounitIso` is natural in its source variable. -/
theorem derivedHomCompletionCounitIso_naturality_left (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    (derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj
            ((cechTorsionFunctor A f).obj L))).map g.op ≫
        (derivedHomCompletionCounitIso A I hI f hf K' L).hom =
      (derivedHomCompletionCounitIso A I hI f hf K L).hom ≫
        (derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L)).map g.op := by
  exact derivedHom_map_comm_square A _ _ _ _ _ (by simp)

/-- `Dualizing.cechCurryIso` is natural in its source variable. -/
theorem cechCurryIso_naturality_left (f : Fin r → A)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K)
    (M : DerivedCategory (ModuleCat.{u} A)) :
    (derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj M)).map g.op ≫
        (cechCurryIso A f K' M).hom =
      (cechCurryIso A f K M).hom ≫
        ((cechTorsionFunctor A f).op ⋙ derivedHomInto A M).map g.op :=
  (StacksDraft.DerivedHom.derivedHomCurrying (R := A)).naturality_left g

/-- `Dualizing.derivedHomCechTensorIso` is natural in its source variable. -/
theorem derivedHomCechTensorIso_naturality_left (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    ((cechTorsionFunctor A f).op ⋙
          derivedHomInto A ((cechTorsionFunctor A f).obj L)).map g.op ≫
        (derivedHomCechTensorIso A I hI f hf K' L).hom =
      (derivedHomCechTensorIso A I hI f hf K L).hom ≫
        ((localCohomologyEndofunctor A I hI).op ⋙
          derivedHomInto A ((localCohomologyEndofunctor A I hI).obj L)).map g.op := by
  exact derivedHom_map_comm_square A _ _ _ _ _
    ((localCohomologyCechTensorIso A I hI f hf).hom.naturality g).symm

/-- `Dualizing.derivedHomCompletionTorsionIso` is natural in its source variable. -/
theorem derivedHomCompletionTorsionIso_naturality_left (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I)
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K' ⟶ K)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    ((DerivedCompletion.derivedCompletionFunctor A f).op ⋙
          derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L)).map g.op ≫
        (derivedHomCompletionTorsionIso A I hI f hf K' L).hom =
      (derivedHomCompletionTorsionIso A I hI f hf K L).hom ≫
        ((localCohomologyEndofunctor A I hI).op ⋙
          derivedHomInto A ((localCohomologyEndofunctor A I hI).obj L)).map g.op := by
  have hu := derivedHomCompletionUnitIso_naturality_left A f g L
  have hc := derivedHomCompletionCounitIso_naturality_left A I hI f hf g L
  have hk := cechCurryIso_naturality_left A f g ((cechTorsionFunctor A f).obj L)
  have ht := derivedHomCechTensorIso_naturality_left A I hI f hf g L
  have hc' : (derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L)).map g.op ≫
      (derivedHomCompletionCounitIso A I hI f hf K' L).inv =
      (derivedHomCompletionCounitIso A I hI f hf K L).inv ≫
        (derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj
          ((cechTorsionFunctor A f).obj L))).map g.op := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [derivedHomCompletionTorsionIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, hu, Category.assoc]
  congr 1
  rw [← Category.assoc, hc', Category.assoc]
  congr 1
  rw [← Category.assoc, hk, Category.assoc, ht]

/-- Derived completion of derived Hom is derived Hom into the derived completion:
`RHom_A(K, L)^∧ ≅ RHom_A(K, L^∧)`, naturally in `K`. -/
theorem nonempty_derivedCompletionDerivedHomNatIso (f : Fin r → A)
    (L : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty (derivedHomInto A L ⋙ DerivedCompletion.derivedCompletionFunctor A f ≅
      derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L)) := by
  obtain ⟨-, -, -, ⟨e⟩, -, -⟩ := DerivedHomCechCompletion.derivedHom_cechCompletion A f
  refine ⟨NatIso.ofComponents (fun K ↦ e.app (K, L)) fun {X Y} g ↦ ?_⟩
  simpa using e.hom.naturality (show ((X, L) : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ ×
    DerivedCategory (ModuleCat.{u} A)) ⟶ (Y, L) from (g, 𝟙 L))

/-- The natural isomorphism of `Dualizing.nonempty_derivedCompletionDerivedHomNatIso`, as a
chosen isomorphism of functors. -/
def derivedCompletionDerivedHomNatIso (f : Fin r → A) (L : DerivedCategory (ModuleCat.{u} A)) :
    derivedHomInto A L ⋙ DerivedCompletion.derivedCompletionFunctor A f ≅
      derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L) :=
  (nonempty_derivedCompletionDerivedHomNatIso A f L).some

/-- Precomposition with the derived-completion unit, `RHom_A(K^∧, L^∧) ≅ RHom_A(K, L^∧)`,
naturally in `K`. -/
def derivedHomCompletionUnitNatIso (f : Fin r → A) (L : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCompletion.derivedCompletionFunctor A f).op ⋙
        derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L) ≅
      derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L) :=
  NatIso.ofComponents (fun K ↦ derivedHomCompletionUnitIso A f K.unop L)
    (fun g ↦ derivedHomCompletionUnitIso_naturality_left A f g.unop L)

/-- `RHom_A(K^∧, L^∧) ≅ RHom_A(RΓ_Z K, RΓ_Z L)`, naturally in `K`. -/
def derivedHomCompletionTorsionNatIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (L : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCompletion.derivedCompletionFunctor A f).op ⋙
        derivedHomInto A ((DerivedCompletion.derivedCompletionFunctor A f).obj L) ≅
      (localCohomologyEndofunctor A I hI).op ⋙
        derivedHomInto A ((localCohomologyEndofunctor A I hI).obj L) :=
  NatIso.ofComponents (fun K ↦ derivedHomCompletionTorsionIso A I hI f hf K.unop L)
    (fun g ↦ derivedHomCompletionTorsionIso_naturality_left A I hI f hf g.unop L)

/-- For a finite family `f` generating an ideal `I` of a commutative ring `A`, with `Z = V(I)`,
there is an isomorphism `RHom_A(-, L)^∧ ≅ RHom_A(RΓ_Z(-), RΓ_Z(L))` of contravariant functors
on `D(A)`. -/
@[stacks 0A6Y "natural in the source object"]
def derivedCompletionDerivedHomTorsionNatIso (I : Ideal A) (hI : I.FG) (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = I) (L : DerivedCategory (ModuleCat.{u} A)) :
    derivedHomInto A L ⋙ DerivedCompletion.derivedCompletionFunctor A f ≅
      (localCohomologyEndofunctor A I hI).op ⋙
        derivedHomInto A ((localCohomologyEndofunctor A I hI).obj L) :=
  derivedCompletionDerivedHomNatIso A f L ≪≫
    (derivedHomCompletionUnitNatIso A f L).symm ≪≫
    derivedHomCompletionTorsionNatIso A I hI f hf L

end Completion

end Dualizing

end
