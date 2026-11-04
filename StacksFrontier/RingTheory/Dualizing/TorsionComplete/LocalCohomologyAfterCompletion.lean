module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.DerivedComplete.CechCompletion
import all StacksFrontier.Homology.DerivedComplete.CechCompletion
public import StacksFrontier.Homology.DerivedComplete.CechReflection
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.Complete
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.Basic

/-!
# Local cohomology after derived completion

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a commutative ring `A` and `Z = V(I)`.
Local cohomology with support in `Z` does not change under derived `I`-completion: the unit
`K ⟶ K^∧` of derived completion induces an isomorphism `RΓ_Z(K) ⟶ RΓ_Z(K^∧)`.

Both functors are computed from the extended alternating Čech complex `C(f)`: local cohomology is
`C(f) ⊗^L_A -` by the Čech formula of Stacks 0A6R, and derived completion is `RHom_A(C(f), -)` by
Stacks 091V. Since `RΓ_Z` is a coreflection onto the complexes with `I`-power-torsion cohomology,
it suffices to show that `K ⟶ K^∧` induces a bijection on maps out of every such complex `X`. By
tensor–Hom adjunction those maps are maps `X ⊗^L_A C(f) ⟶ K`, and the Čech augmentation
`C(f) ⟶ A` becomes invertible after tensoring with a power-torsion complex, which is the content
of the Čech formula.

The remaining work is bookkeeping between the two models of the Čech complex: the Čech formula
uses the complex of the regular module lifted into the module universe, while derived completion
uses the complex of `A` itself, and the two derived tensor products involved are the canonical
one and the one underlying the tensor–Hom adjunction. The module universe equals the ring
universe throughout, which is where both models live.

## Main results

* `Dualizing.isIso_tensor_map_app_iff` — the canonical derived tensor product and the one
  underlying the tensor–Hom adjunction invert the same maps of K-flat complexes.
* `Dualizing.isIso_localCohomology_map_derivedCompletionUnit` — Stacks 0A6W, the half asserting
  `RΓ_Z(K) = RΓ_Z(K^∧)`.

## References

* [Stacks Project, Tag 0A6W](https://stacks.math.columbia.edu/tag/0A6W)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 091V](https://stacks.math.columbia.edu/tag/091V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor Stacks.LocalCohomology Stacks.LocalCohomology.CechFormula

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

section General

/-- Invertibility transports across a commutative square whose vertical maps are
isomorphisms. -/
theorem isIso_iff_of_commSq {C : Type*} [Category C] {X Y X' Y' : C}
    (a : X ⟶ Y) (b : X' ⟶ Y') (e : X ≅ X') (e' : Y ≅ Y') (h : a ≫ e'.hom = e.hom ≫ b) :
    IsIso a ↔ IsIso b := by
  rw [← isIso_comp_right_iff a e'.hom, h, isIso_comp_left_iff]

/-- Invertibility of `F.map (a, a')` for a functor on a product category transports across
squares whose vertical maps are isomorphisms in both components. -/
private theorem isIso_map_prod_iff_of_commSq {C D E : Type*} [Category C] [Category D]
    [Category E] (F : C × D ⥤ E) {L M N P : C} {L' M' N' P' : D} (a : L ⟶ M) (a' : L' ⟶ M')
    (b : N ⟶ P) (b' : N' ⟶ P') (e : L ≅ N) (e' : M ≅ P) (g : L' ≅ N') (g' : M' ≅ P')
    (h : a ≫ e'.hom = e.hom ≫ b) (h' : a' ≫ g'.hom = g.hom ≫ b') :
    IsIso (F.map ((a, a') : (L, L') ⟶ (M, M'))) ↔ IsIso (F.map ((b, b') : (N, N') ⟶ (P, P'))) :=
  isIso_iff_of_commSq _ _ (F.mapIso (e.prod g)) (F.mapIso (e'.prod g')) <| by
    simp only [Functor.mapIso_hom, Iso.prod_hom, ← Functor.map_comp]
    exact congrArg F.map (Prod.ext h h')

/-- Two maps out of `X` into `Y` that are both universal among maps out of `X` differ by an
automorphism of `Y`. -/
theorem exists_iso_of_bijective_precomp {C : Type*} [Category C] {X Y : C} (a b : X ⟶ Y)
    (ha : Function.Bijective (fun g : Y ⟶ Y => a ≫ g))
    (hb : Function.Bijective (fun g : Y ⟶ Y => b ≫ g)) : ∃ e : Y ≅ Y, a ≫ e.hom = b := by
  obtain ⟨α, hα⟩ := ha.surjective b
  obtain ⟨β, hβ⟩ := hb.surjective a
  have hαβ : α ≫ β = 𝟙 Y := by
    apply ha.injective
    simp only [← Category.assoc, hα, hβ, Category.comp_id]
  have hβα : β ≫ α = 𝟙 Y := by
    apply hb.injective
    simp only [← Category.assoc, hβ, hα, Category.comp_id]
  exact ⟨⟨α, β, hαβ, hβα⟩, hα⟩

/-- Every object of `D(A)` is represented by a K-flat complex. -/
theorem exists_kFlat_representative {A : Type u} [CommRing A]
    (X : DerivedCategory (ModuleCat.{u} A)) :
    ∃ K : CochainComplex (ModuleCat.{u} A) ℤ,
      K.KFlat ∧ Nonempty (DerivedCategory.Q.obj K ≅ X) := by
  obtain ⟨K, p, hK, -, hp, -⟩ :=
    CochainComplex.KFlat.exists_kFlat_resolution (DerivedCategory.Q.objPreimage X)
  exact ⟨K, hK, ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso X⟩⟩

/-- **The two derived tensor products agree on invertibility.** For a map of K-flat complexes,
the canonical derived tensor product inverts it on an object exactly when the tensor product
underlying the tensor–Hom adjunction does: both are computed by the total tensor product of
K-flat representatives. -/
theorem isIso_tensor_map_app_iff {A : Type u} [CommRing A] (T : DerivedTensorProduct A)
    {L M : CochainComplex (ModuleCat.{u} A) ℤ} (a : L ⟶ M) (hL : L.KFlat) (hM : M.KFlat)
    (X : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((T.tensor.map (DerivedCategory.Q.map a)).app X) ↔
      IsIso ((StacksDraft.DerivedHom.derivedHomAdjunction (R := A)).tensor.map
        (show (DerivedCategory.Q.obj L, X) ⟶ (DerivedCategory.Q.obj M, X) from
          (DerivedCategory.Q.map a, 𝟙 X))) := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_representative X
  have h₁ := isIso_iff_of_commSq ((T.tensor.map (Q.map a)).app (Q.obj P))
    ((T.tensor.map (Q.map a)).app X) ((T.tensor.obj (Q.obj L)).mapIso e)
    ((T.tensor.obj (Q.obj M)).mapIso e) ((T.tensor.map (Q.map a)).naturality e.hom).symm
  have hn := T.comparison_naturality a (𝟙 P) hL hM hP hP
  rw [Q.map_id P, (T.tensor.obj (DerivedCategory.Q.obj M)).map_id (DerivedCategory.Q.obj P),
    Category.id_comp] at hn
  have h₂ := isIso_iff_of_commSq _ _ (T.comparison L P hL hP) (T.comparison M P hM hP) hn
  have hn' := d.tensorIso_naturality a (𝟙 P) hP hP
  simp only [CategoryTheory.Functor.map_id] at hn'
  have h₃ := isIso_iff_of_commSq _ _ (d.tensorIso L P hP) (d.tensorIso M P hP) hn'
  have h₄ := isIso_map_prod_iff_of_commSq d.tensor (Q.map a) (𝟙 (Q.obj P)) (Q.map a) (𝟙 X)
    (Iso.refl _) (Iso.refl _) e e (by simp) (by simp)
  exact h₁.symm.trans (h₂.trans (h₃.symm.trans h₄))

end General

section Cech

variable (A : Type u) [CommRing A] {r : ℕ}

/-- **The Čech complex of the lifted regular module and of the ring agree.** Both compute the
Čech complex of the tensor unit, so the comparison is the tensor identification of the Čech
complex followed by the left unitor. -/
private def extendedCechComplexULiftIso (f : Fin r → A) :
    extendedCechComplex f (regularModule.{u, u} A) ≅
      extendedCechComplex f (ModuleCat.of A A) := by
  let e : ModuleCat.of A (ULift.{u} A) ≅ 𝟙_ (ModuleCat.{u} A) := ULift.moduleEquiv.toModuleIso
  let t : tensorLeft (ModuleCat.of A (ULift.{u} A)) ≅ 𝟭 (ModuleCat.{u} A) :=
    (curriedTensor _).mapIso e ≪≫ leftUnitorNatIso _
  let eC : Cech.cechComplex f (ULift.{u} A) ≅ Cech.cechComplex f A :=
    CechCompletion.cechTensorIso f (ModuleCat.of A (ULift.{u} A)) ≪≫
      (NatIso.mapHomologicalComplex t (ComplexShape.up ℕ)).app _ ≪≫
        (Functor.mapHomologicalComplexIdIso _ _).app _
  exact (ComplexShape.embeddingUpNat.extendFunctor _).mapIso eC

/-- The two Čech augmentations agree up to the comparison of the two Čech complexes and an
isomorphism of their degree-zero targets: both are invertible in degree zero and zero
elsewhere. -/
private theorem exists_singleIso_extendedCechAugmentation (f : Fin r → A) :
    ∃ e : (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (ULift.{u} A)) ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A),
      extendedCechAugmentation f (regularModule.{u, u} A) ≫ e.hom =
        (extendedCechComplexULiftIso A f).hom ≫
          CechCompletion.cechAugmentation f (ModuleCat.of A A) := by
  let a := extendedCechAugmentation f (regularModule.{u, u} A)
  let b := CechCompletion.cechAugmentation f (ModuleCat.of A A)
  let c := extendedCechComplexULiftIso A f
  have : IsIso (a.f 0) := isIso_extendedCechAugmentation_f_zero f (regularModule.{u, u} A)
  have : IsIso (b.f 0) := CechCompletion.isIso_cechAugmentation_f_zero f (ModuleCat.of A A)
  let e₀ : ModuleCat.of A (ULift.{u} A) ≅ ModuleCat.of A A :=
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).symm ≪≫
      (asIso (a.f 0)).symm ≪≫ HomologicalComplex.Hom.isoApp c 0 ≪≫
        asIso (b.f 0) ≪≫ HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _
  refine ⟨(CochainComplex.singleFunctor (ModuleCat.{u} A) 0).mapIso e₀, ?_⟩
  apply HomologicalComplex.to_single_hom_ext
  show a.f 0 ≫ ((HomologicalComplex.single (ModuleCat A) (.up ℤ) 0).map e₀.hom).f 0 =
    c.hom.f 0 ≫ b.f 0
  rw [HomologicalComplex.single_map_f_self]
  simp only [e₀, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc, asIso_inv, asIso_hom,
    Category.assoc]
  simp

/-- If the Čech comparison map is invertible at `X`, then so is the derived tensor product with
the Čech augmentation of the lifted regular module. -/
private theorem isIso_tensor_map_extendedCechAugmentation_app (f : Fin r → A)
    (X : DerivedCategory (ModuleCat.{u} A)) (hcech : IsIso ((cechTensorToId A f).app X)) :
    IsIso (((canonicalDerivedTensorProduct A).tensor.map (DerivedCategory.Q.map
      (extendedCechAugmentation f (regularModule.{u, u} A)))).app X) := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let T := canonicalDerivedTensorProduct A
  let a := extendedCechAugmentation f (regularModule.{u, u} A)
  let sIso : Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
      (regularModule.{u, u} A)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
        (regularModule.{u, u} A)).symm ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
        (ULift.moduleEquiv (R := A) (M := A)).toModuleIso
  have hfac : CechFormula.cechAugmentation A f = Q.map a ≫ sIso.hom := by
    dsimp only [CechFormula.cechAugmentation, extendedCechAugmentationHom, sIso, a,
      Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [Category.assoc]
  have hrw : (cechTensorToId A f).app X =
      (T.tensor.map (Q.map a)).app X ≫
        ((T.tensor.map sIso.hom).app X ≫ (derivedTensorLeftUnitor A).hom.app X) := by
    dsimp only [cechTensorToId, T]
    rw [hfac, Functor.map_comp]
    simp
  have h₁ : IsIso ((T.tensor.map sIso.hom).app X) :=
    ((T.tensor.mapIso sIso).app X).isIso_hom
  have h₂ : IsIso ((derivedTensorLeftUnitor A).hom.app X) :=
    ((derivedTensorLeftUnitor A).app X).isIso_hom
  rw [hrw] at hcech
  exact IsIso.of_isIso_comp_right ((T.tensor.map (Q.map a)).app X)
    ((T.tensor.map sIso.hom).app X ≫ (derivedTensorLeftUnitor A).hom.app X)

/-- **Tensoring the Čech augmentation with a power-torsion complex gives an isomorphism.** By the
Čech formula the canonical derived tensor product with the Čech complex of the lifted regular
module is local cohomology, whose counit is invertible on the power-torsion subcategory; the
statement is then transported to the Čech complex of the ring and to the tensor product
underlying the tensor–Hom adjunction. -/
private theorem isIso_tensor_cechAugmentation_of_powerTorsion (I : Ideal A) (hI : I.FG)
    (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (X : DerivedCategory (ModuleCat.{u} A)) (hX : derivedPowerTorsionProperty A I hI X) :
    IsIso (let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
      d.tensor.map (show (X, CechCompletion.extendedCechObject A f) ⟶
        (X, DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ))) from
          (𝟙 X, DerivedCategory.Q.map
            (CechCompletion.cechAugmentation f (ModuleCat.of A A)))) ≫
        (CechCompletion.tensorUnitRight d StacksDraft.DerivedHom.derivedHomCurrying X).hom) := by
  let Q := DerivedCategory.Q (C := ModuleCat.{u} A)
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let T := canonicalDerivedTensorProduct A
  let a := extendedCechAugmentation f (regularModule.{u, u} A)
  let b := CechCompletion.cechAugmentation f (ModuleCat.of A A)
  have hflat : Module.Flat A (ULift.{u} A) := Module.Flat.of_linearEquiv ULift.moduleEquiv
  have hL : (extendedCechComplex f (regularModule.{u, u} A)).KFlat :=
    cechRegular_isKFlat.{u, u} f
  have hM : ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (ULift.{u} A))).KFlat :=
    single_isKFlat.{u, u} (ModuleCat.of A (ULift.{u} A)) 0
  have ha : IsIso ((T.tensor.map (Q.map a)).app X) :=
    isIso_tensor_map_extendedCechAugmentation_app A f X
      (isIso_cechTensorToId_app A f I hI hf X hX)
  have ha' := (isIso_tensor_map_app_iff T a hL hM X).mp ha
  obtain ⟨e, he⟩ := exists_singleIso_extendedCechAugmentation A f
  let c := extendedCechComplexULiftIso A f
  have hb := (isIso_map_prod_iff_of_commSq d.tensor (Q.map a) (𝟙 X) (Q.map b) (𝟙 X)
    (Q.mapIso c) (Q.mapIso e) (Iso.refl X) (Iso.refl X)
    (by simpa only [Functor.mapIso_hom, ← Q.map_comp] using congrArg Q.map he) (by simp)).mp ha'
  have hswap := d.tensorSwap_naturality (𝟙 X) (Q.map b)
  have hb' : IsIso (d.tensor.map (show (X, Q.obj _) ⟶ (X, Q.obj _) from (𝟙 X, Q.map b))) :=
    (isIso_iff_of_commSq _ _ (d.tensorSwap X (Q.obj _)) (d.tensorSwap X (Q.obj _)) hswap).mpr hb
  exact IsIso.comp_isIso' hb' (by infer_instance)

end Cech

section Reflection

variable (A : Type u) [CommRing A] {r : ℕ}

/-- For a power-torsion complex `X`, postcomposition with the Čech completion unit is bijective
on maps out of `X`: under tensor–Hom adjunction it becomes composition with the tensor product of
the Čech augmentation, which is invertible by
`Dualizing.isIso_tensor_cechAugmentation_of_powerTorsion`. -/
private theorem bijective_postcomp_cechCompletionUnit_of_powerTorsion (I : Ideal A) (hI : I.FG)
    (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (X K : DerivedCategory (ModuleCat.{u} A)) (hX : derivedPowerTorsionProperty A I hI X) :
    Function.Bijective
      (fun g : X ⟶ K => g ≫ (CechCompletion.cechCompletionUnit A f).app K) := by
  let d := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let c := StacksDraft.DerivedHom.derivedHomCurrying (R := A)
  let a := d.tensor.map (show (X, CechCompletion.extendedCechObject A f) ⟶
      (X, DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat A) ℤ))) from
        (𝟙 X, DerivedCategory.Q.map
          (CechCompletion.cechAugmentation f (ModuleCat.of A A)))) ≫
      (CechCompletion.tensorUnitRight d c X).hom
  have : IsIso a := isIso_tensor_cechAugmentation_of_powerTorsion A I hI f hf X hX
  apply CechCompletion.bijective_postcomp_homUnitOfAugmentation d c
  simp only [← Category.assoc]
  show Function.Bijective (fun g : X ⟶ K => a ≫ g)
  exact ⟨fun _ _ hgg' => (cancel_epi a).mp hgg', fun g => ⟨inv a ≫ g, by simp⟩⟩

/-- **Local cohomology inverts the Čech completion unit.** Local cohomology is a coreflection onto
the power-torsion subcategory, so this is tested on maps out of power-torsion complexes, where it
is `Dualizing.bijective_postcomp_cechCompletionUnit_of_powerTorsion`. -/
private theorem isIso_localCohomology_map_cechCompletionUnit (I : Ideal A) (hI : I.FG)
    (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso ((localCohomologyRightAdjoint A I hI).1.map
      ((CechCompletion.cechCompletionUnit A f).app K)) := by
  let adj := localCohomologyAdjunction A I hI
  apply isIso_of_yoneda_map_bijective
  intro X
  have h := bijective_postcomp_cechCompletionUnit_of_powerTorsion A I hI f hf X.obj K X.property
  have hb := (adj.homEquiv X _).bijective.comp (h.comp (adj.homEquiv X K).symm.bijective)
  convert hb using 1
  funext g
  dsimp only [Function.comp_apply]
  rw [adj.homEquiv_naturality_right]
  simp

section Unit

attribute [local instance] hasProductsOfShape_nat_derivedCategory

/-- The Čech completion unit is a reflection unit: it lands in the derived-complete objects and is
universal among maps into them. -/
private theorem cechCompletionUnit_isReflection (f : Fin r → A) :
    (∀ K, IsDerivedComplete (Ideal.span (Set.range f))
      ((CechCompletion.cechCompletionFunctor A f).obj K)) ∧
    ∀ (K E : DerivedCategory (ModuleCat.{u} A)),
      IsDerivedComplete (Ideal.span (Set.range f)) E →
        Function.Bijective
          (fun g : (CechCompletion.cechCompletionFunctor A f).obj K ⟶ E =>
            (CechCompletion.cechCompletionUnit A f).app K ≫ g) := by
  refine ⟨CechCompletion.cechCompletion_isDerivedComplete A f, ?_⟩
  intro K E hE
  have := CechCompletion.isIso_cechCompletionUnit_of_complete A f E hE
  have hK := CechCompletion.isIso_cechCompletionUnit_of_complete A f
    ((CechCompletion.cechCompletionFunctor A f).obj K)
    (CechCompletion.cechCompletion_isDerivedComplete A f K)
  have : IsIso ((CechCompletion.cechCompletionFunctor A f).map
      ((CechCompletion.cechCompletionUnit A f).app K)) :=
    CechCompletion.isIso_map_homUnitOfAugmentation
      (StacksDraft.DerivedHom.derivedHomAdjunction (R := A))
      StacksDraft.DerivedHom.derivedHomCurrying (CechCompletion.extendedCechObject A f) K
      (DerivedCategory.Q.map (CechCompletion.cechAugmentation f (ModuleCat.of A A))) hK
  exact CechCompletion.bijective_precomp_unit (CechCompletion.cechCompletionFunctor A f)
    (CechCompletion.cechCompletionUnit A f) K E

/-- **Stacks 0A6W, local cohomology after completion.** For a finitely generated ideal
`I = (f₁, …, f_r)` of a commutative ring `A` and `Z = V(I)`, the derived-completion unit
`K ⟶ K^∧` induces an isomorphism `RΓ_Z(K) ⟶ RΓ_Z(K^∧)` in `D(A)`, naturally in `K`. -/
@[stacks 0A6W "local_after_completion"]
theorem isIso_localCohomology_map_derivedCompletionUnit (I : Ideal A) (hI : I.FG)
    (f : Fin r → A) (hf : Ideal.span (Set.range f) = I)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (((localCohomologyRightAdjoint A I hI).1 ⋙
      (derivedPowerTorsionProperty A I hI).ι).map
        ((DerivedCompletion.derivedCompletionUnit A f).app K)) := by
  let R := (localCohomologyRightAdjoint A I hI).1
  let j := (derivedPowerTorsionProperty.{u, u} A I hI).ι
  let η := DerivedCompletion.derivedCompletionUnit A f
  let ε := CechCompletion.cechCompletionUnit A f
  have hε := cechCompletionUnit_isReflection A f
  have hη := DerivedCompletion.derivedCompletion_isReflection A f
  obtain ⟨e, he⟩ := exists_iso_of_bijective_precomp (ε.app K) (η.app K)
    (hε.2 K _ (hε.1 K)) (hη.2 K _ (hε.1 K))
  have hR : IsIso (R.map (ε.app K)) :=
    isIso_localCohomology_map_cechCompletionUnit A I hI f hf K
  show IsIso ((R ⋙ j).map (η.app K))
  rw [← he, Functor.map_comp]
  exact IsIso.comp_isIso' (j.map_isIso (R.map (ε.app K))) (by infer_instance)

end Unit

end Reflection

end Dualizing

end
