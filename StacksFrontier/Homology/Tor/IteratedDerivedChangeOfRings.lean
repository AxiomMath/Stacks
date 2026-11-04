module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.BifunctorAssociator
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Homology.KFlat.ChosenResolution
public import StacksFrontier.Homology.KFlat.Iso
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.KFlat.ScalarBaseChange
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse
public import StacksCore.Tactic.StacksAttribute

@[expose] public noncomputable section

/-!
# Iterated derived change of rings

Let `A → B → C` be ring maps, let `N` be a complex of `B`-modules and `K` a complex of
`C`-modules. A complex of `A`-modules can be tensored with `N` over `A` and the result then
tensored with `K` over `B`; it can also be tensored in one step against the single right factor
`N ⊗_B K`; and the two right factors can be interchanged, at the cost of the Koszul sign. This
file proves that all three derived constructions agree, that each comparison is the *unique*
one compatible with the specified counits of the derived change-of-rings construction, and that
the resulting identification factors as derived extension of scalars followed by derived
tensoring over `C`.

This is the mathematics of `StacksFrontier.Homology.Tor.DerivedChangeOfRings` one step further out:
that file builds, for a single ring map, the derived tensor-total functor with its counit and its
change-of-rings factorization; here two such constructions are composed.

As in the source argument the two right factors are replaced by K-flat complexes before any
ordinary triple tensor product is formed, so no derived triple tensor product of possibly
nonflat factors is ever needed. The replacements are the chosen ones of
`CochainComplex.KFlat.chosenResolution`, and the ordinary associator and interchange are pinned
down on homogeneous tensor generators through the `tensorElement` projections of the two
constructions. The derived comparisons are then characterized by commuting with the counits, and
that characterization is what makes them canonical rather than merely existent.

The three ring universes are independent, and the common module universe, which holds the
modules of all three rings, is independent of them as well. K-flatness at that generality is
`CochainComplex.KFlat`.

## Main definitions

* `CochainComplex.DerivedTensor.IteratedChangeOfRings.compositeCounit`: the counit of an
  iterated derived tensor product, as an explicit composite of the two specified counits.
* `CochainComplex.DerivedTensor.IteratedChangeOfRings.doubleBaseChangeIso`: the associativity
  isomorphism `(- ⊗ᴸ_A N) ⋙ (- ⊗ᴸ_B K) ≅ - ⊗ᴸ_A (N ⊗ᴸ_B K)`.

## Main results

* `CochainComplex.DerivedTensor.IteratedChangeOfRings.derivedTensorProduct_doubleBaseChange`:
  the canonical associativity, base-change and signed interchange isomorphisms of an iterated
  derived tensor product, each unique subject to its counit normalization.

## Implementation notes

Mathlib's monoidal structure on `ModuleCat` requires the module universe to agree with the
ring's, and instance search reaches it before the lifted structure of
`StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse`. A universe unification failure
there is not read as "this instance does not apply", so the search does not fall through to the
lifted one; the lifted instances are therefore installed by hand at every point where a tensor
product of large-universe modules is formed.

The declarations between `compositeCounit` and the main theorem are private auxiliaries of its
proof: the ordinary associator and interchange of the tensor-total complex, their element-level
normalizations, and the two left-derived-functor recognition principles. The flip isomorphism of
the tensor-total complex and the preservation of quasi-isomorphisms by `TleftCochain` come from
`StacksFrontier.Homology.Tor.DerivedTensorLargeUniverse` rather than being rebuilt here.

## References

* [The Stacks Project, Tag 08YU](https://stacks.math.columbia.edu/tag/08YU)
-/

open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe uA uB uC v uR uS w

namespace CochainComplex.DerivedTensor.IteratedChangeOfRings


attribute [local instance] HasDerivedCategory.standard

/-- The counit of an iterated derived tensor product: the composite of the two specified counits
of the constructions being iterated, whiskered into place. It is an actual composite of named
counits, not an abstract comparison, and it is what pins the iterated comparison down. -/
public def compositeCounit
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    {N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ}
    {K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ}
    (S : DerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N)
    (T : DerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K) :
    DerivedCategory.Q ⋙ (S.F ⋙ T.F) ⟶
      (S.directTensor ⋙ T.directTensor) ⋙ DerivedCategory.Q :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight S.alphaF T.F ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft S.directTensor T.alphaF ≫
    (Functor.associator _ _ _).inv

private lemma isIso_of_isIso_app_kFlat
    {R : Type uA} [CommRing R] {D : Type*} [Category* D]
    {F G : DerivedCategory (ModuleCat.{max v uA} R) ⥤ D} (t : F ⟶ G)
    (ht : ∀ M : CochainComplex (ModuleCat.{max v uA} R) ℤ,
      CochainComplex.KFlat.{uA, v} M → IsIso (t.app (DerivedCategory.Q.obj M))) : IsIso t := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [← NatTrans.isIso_app_iff_of_iso t (DerivedCategory.Q.objObjPreimageIso X)]
  let M := DerivedCategory.Q.objPreimage X
  let P := CochainComplex.KFlat.chosenResolution M
  have : QuasiIso P.π := P.quasiIso
  have : IsIso (DerivedCategory.Q.map P.π) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  have := ht P.complex P.kFlat
  rw [← isIso_comp_left_iff (F.map (DerivedCategory.Q.map P.π)), t.naturality]
  infer_instance

private lemma isLeftDerivedFunctor_of_isIso_app_kFlat
    {R : Type uA} [CommRing R] {D : Type*} [Category* D]
    (T : CochainComplex (ModuleCat.{max v uA} R) ℤ ⥤ D)
    (F G : DerivedCategory (ModuleCat.{max v uA} R) ⥤ D)
    (α : DerivedCategory.Q ⋙ F ⟶ T) (β : DerivedCategory.Q ⋙ G ⟶ T)
    [F.IsLeftDerivedFunctor α
      (HomologicalComplex.quasiIso (ModuleCat.{max v uA} R) (ComplexShape.up ℤ))]
    (hα : ∀ M : CochainComplex (ModuleCat.{max v uA} R) ℤ,
      CochainComplex.KFlat.{uA, v} M → IsIso (α.app M))
    (hβ : ∀ M : CochainComplex (ModuleCat.{max v uA} R) ℤ,
      CochainComplex.KFlat.{uA, v} M → IsIso (β.app M)) :
    G.IsLeftDerivedFunctor β
      (HomologicalComplex.quasiIso (ModuleCat.{max v uA} R) (ComplexShape.up ℤ)) := by
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v uA} R) (ComplexShape.up ℤ)
  apply (F.isLeftDerivedFunctor_iff_isIso_leftDerivedLift α W G β).2
  apply isIso_of_isIso_app_kFlat
  intro M hM
  have := hα M hM
  have := hβ M hM
  have : IsIso ((F.leftDerivedLift α W G β).app (DerivedCategory.Q.obj M) ≫ α.app M) := by
    rw [Functor.leftDerived_fac_app]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (α.app M)

private def extendScalarsComp
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    ModuleCat.extendScalars.{uA, uC, max v uA uB uC} (g.comp f) ≅
      ModuleCat.extendScalars.{uA, uB, max v uA uB uC} f ⋙
        ModuleCat.extendScalars.{uB, uC, max v uA uB uC} g :=
  (conjugateIsoEquiv
    ((ModuleCat.extendRestrictScalarsAdj.{max v uA uB uC, uA, uB} f).comp
      (ModuleCat.extendRestrictScalarsAdj.{max v uA uB uC, uB, uC} g))
    (ModuleCat.extendRestrictScalarsAdj.{max v uA uB uC, uA, uC} (g.comp f))).symm
      (ModuleCat.restrictScalarsComp f g).symm

private def moduleTensorChange
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B) :
    ModuleCat.{max v uA uB} A ⥤ ModuleCat.{max v uA uB} B ⥤
      ModuleCat.{max v uA uB} B := by
  letI := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
  letI := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
  exact ModuleCat.extendScalars f ⋙ curriedTensor (ModuleCat.{max v uA uB} B)

private def extendScalarsTensorIso
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (M N : ModuleCat.{max v uA uB} A) :
    letI := ModuleCat.liftedModuleMonoidalStruct.{uA, max v uB} (R := A)
    letI := ModuleCat.liftedModuleMonoidal.{uA, max v uB} (R := A)
    letI := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
    letI := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
    (ModuleCat.extendScalars f).obj (M ⊗ N) ≅
      (ModuleCat.extendScalars f).obj M ⊗ (ModuleCat.extendScalars f).obj N := by
  letI := ModuleCat.liftedModuleMonoidalStruct.{uA, max v uB} (R := A)
  letI := ModuleCat.liftedModuleMonoidal.{uA, max v uB} (R := A)
  letI := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
  letI := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
  letI := f.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange A B M N).toModuleIso


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private lemma homEquiv_extendScalarsComp
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (M : ModuleCat.{max v uA uB uC} A) :
    (ModuleCat.extendRestrictScalarsAdj.{max v uA uB uC, uA, uC} (g.comp f)).homEquiv _ _
      ((extendScalarsComp.{uA, uB, uC, v} f g).hom.app M) =
      (ModuleCat.extendRestrictScalarsAdj.{max v uA uB uC, uA, uB} f).unit.app M ≫
        (ModuleCat.restrictScalars f).map
          ((ModuleCat.extendRestrictScalarsAdj.{max v uA uB uC, uB, uC} g).unit.app _) ≫
        (ModuleCat.restrictScalarsComp f g).inv.app _ := by
  dsimp [extendScalarsComp, conjugateIsoEquiv, conjugateEquiv]
  simp only [Functor.comp_obj, Category.assoc, Category.id_comp,
    Category.comp_id, Adjunction.comp_unit_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Adjunction.unit_naturality_assoc,
    Adjunction.right_triangle_components]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma extendScalarsComp_hom_one_tmul
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (M : ModuleCat.{max v uA uB uC} A) (x : M) :
    (extendScalarsComp f g).hom.app M ((1 : C) ⊗ₜ[A,g.comp f] x) =
      (1 : C) ⊗ₜ[B,g] ((1 : B) ⊗ₜ[A,f] x) := by
  rw [← ModuleCat.extendRestrictScalarsAdj_homEquiv_apply.{max v uA uB uC, uA, uC},
    homEquiv_extendScalarsComp]
  rfl

private def moduleTensorChangeAssociator
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (M : ModuleCat.{max v uA uB uC} A) (N : ModuleCat.{max v uA uB uC} B)
    (K : ModuleCat.{max v uA uB uC} C) :
    ((moduleTensorChange.{uB, uC, max v uA} g).obj
        (((moduleTensorChange.{uA, uB, max v uC} f).obj M).obj N)).obj K ≅
      ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M).obj
        (((moduleTensorChange.{uB, uC, max v uA} g).obj N).obj K) := by
  letI := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA uC} (R := B)
  letI := ModuleCat.liftedModuleMonoidal.{uB, max v uA uC} (R := B)
  letI := ModuleCat.liftedModuleMonoidalStruct.{uC, max v uA uB} (R := C)
  letI := ModuleCat.liftedModuleMonoidal.{uC, max v uA uB} (R := C)
  exact tensorIso (extendScalarsTensorIso.{uB, uC, max v uA} g _ _) (Iso.refl K) ≪≫
    tensorIso (tensorIso ((extendScalarsComp.{uA, uB, uC, v} f g).symm.app M) (Iso.refl _))
      (Iso.refl K) ≪≫
      α_ _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma extendScalarsComp_inv_one_tmul
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) (M : ModuleCat.{max v uA uB uC} A) (x : M) :
    (extendScalarsComp.{uA, uB, uC, v} f g).inv.app M
      ((1 : C) ⊗ₜ[B,g] ((1 : B) ⊗ₜ[A,f] x)) = (1 : C) ⊗ₜ[A,g.comp f] x := by
  rw [← extendScalarsComp_hom_one_tmul f g M x, ← ModuleCat.comp_apply]
  simp

private abbrev moduleTensorElement
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (M : ModuleCat.{max v uA uB} A) (N : ModuleCat.{max v uA uB} B) (x : M) (n : N) :
    ((moduleTensorChange.{uA, uB, v} f).obj M).obj N :=
  ((1 : B) ⊗ₜ[A,f] x) ⊗ₜ[B] n

set_option backward.isDefEq.respectTransparency false in
private lemma moduleTensorChangeAssociator_hom_tmul
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (M : ModuleCat.{max v uA uB uC} A) (N : ModuleCat.{max v uA uB uC} B)
    (K : ModuleCat.{max v uA uB uC} C) (x : M) (n : N) (k : K) :
    (moduleTensorChangeAssociator f g M N K).hom
      (moduleTensorElement.{uB, uC, max v uA} g _ K
        (moduleTensorElement.{uA, uB, max v uC} f M N x n) k) =
      moduleTensorElement.{uA, uC, max v uB} (g.comp f) M _ x
        (moduleTensorElement.{uB, uC, max v uA} g N K n k) := by
  change TensorProduct.tmul C (M := (ModuleCat.extendScalars (g.comp f)).obj M)
      (N := (((moduleTensorChange.{uB, uC, max v uA} g).obj N).obj K))
      ((extendScalarsComp.{uA, uB, uC, v} f g).inv.app M
        ((1 : C) ⊗ₜ[B,g] ((1 : B) ⊗ₜ[A,f] x)))
      (moduleTensorElement.{uB, uC, max v uA} g N K n k) = _
  rw [extendScalarsComp_inv_one_tmul]

private lemma extendScalarsTensorIso_naturality
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    {M M' N N' : ModuleCat.{max v uA uB} A} (m : M ⟶ M') (n : N ⟶ N') :
    letI := ModuleCat.liftedModuleMonoidalStruct.{uA, max v uB} (R := A)
    letI := ModuleCat.liftedModuleMonoidal.{uA, max v uB} (R := A)
    letI := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
    letI := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
    (ModuleCat.extendScalars f).map (m ⊗ₘ n) ≫ (extendScalarsTensorIso f M' N').hom =
      (extendScalarsTensorIso f M N).hom ≫
        ((ModuleCat.extendScalars f).map m ⊗ₘ (ModuleCat.extendScalars f).map n) := by
  let := ModuleCat.liftedModuleMonoidalStruct.{uA, max v uB} (R := A)
  let := ModuleCat.liftedModuleMonoidal.{uA, max v uB} (R := A)
  let := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
  apply ((ModuleCat.extendRestrictScalarsAdj.{max v uA uB, uA, uB} f).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  rfl

private lemma moduleTensorChangeAssociator_naturality
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    {M M' : ModuleCat.{max v uA uB uC} A} {N N' : ModuleCat.{max v uA uB uC} B}
    {K K' : ModuleCat.{max v uA uB uC} C} (m : M ⟶ M') (n : N ⟶ N') (k : K ⟶ K') :
    letI := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA uC} (R := B)
    letI := ModuleCat.liftedModuleMonoidal.{uB, max v uA uC} (R := B)
    letI := ModuleCat.liftedModuleMonoidalStruct.{uC, max v uA uB} (R := C)
    letI := ModuleCat.liftedModuleMonoidal.{uC, max v uA uB} (R := C)
    ((ModuleCat.extendScalars g).map ((ModuleCat.extendScalars f).map m ⊗ₘ n) ⊗ₘ k) ≫
        (moduleTensorChangeAssociator f g M' N' K').hom =
      (moduleTensorChangeAssociator f g M N K).hom ≫
        ((ModuleCat.extendScalars (g.comp f)).map m ⊗ₘ
          ((ModuleCat.extendScalars g).map n ⊗ₘ k)) := by
  let := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA uC} (R := B)
  let := ModuleCat.liftedModuleMonoidal.{uB, max v uA uC} (R := B)
  let := ModuleCat.liftedModuleMonoidalStruct.{uC, max v uA uB} (R := C)
  let := ModuleCat.liftedModuleMonoidal.{uC, max v uA uB} (R := C)
  dsimp only [moduleTensorChange] at *
  simp only [moduleTensorChangeAssociator, moduleTensorChange, Iso.trans_hom, tensorIso,
    Iso.refl_hom, Iso.app_hom, Iso.symm_hom]
  simp only [Category.assoc]
  rw [← associator_naturality]
  simp only [← Category.assoc, tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp]
  rw [extendScalarsTensorIso_naturality]
  simp only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
  rw [← Functor.comp_map, (extendScalarsComp.{uA, uB, uC, v} f g).inv.naturality m]

set_option backward.isDefEq.respectTransparency false in
-- Nested natural isomorphisms require comparing three functor categories.
private def moduleTensorChangeAssociatorNatIso
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    bifunctorComp₁₂ (moduleTensorChange.{uA, uB, max v uC} f)
        (moduleTensorChange.{uB, uC, max v uA} g) ≅
      bifunctorComp₂₃ (moduleTensorChange.{uA, uC, max v uB} (g.comp f))
        (moduleTensorChange.{uB, uC, max v uA} g) := by
  letI := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA uC} (R := B)
  letI := ModuleCat.liftedModuleMonoidal.{uB, max v uA uC} (R := B)
  letI := ModuleCat.liftedModuleMonoidalStruct.{uC, max v uA uB} (R := C)
  letI := ModuleCat.liftedModuleMonoidal.{uC, max v uA uB} (R := C)
  refine NatIso.ofComponents (fun M : ModuleCat.{max v uA uB uC} A =>
    NatIso.ofComponents (fun N : ModuleCat.{max v uA uB uC} B =>
      NatIso.ofComponents (fun K : ModuleCat.{max v uA uB uC} C =>
        moduleTensorChangeAssociator.{uA, uB, uC, v} f g M N K) ?_) ?_) ?_
  · intro K K' k
    simpa [moduleTensorChange, bifunctorComp₁₂, bifunctorComp₁₂Obj,
      bifunctorComp₂₃, bifunctorComp₂₃Obj] using
      moduleTensorChangeAssociator_naturality.{uA, uB, uC, v} f g (𝟙 M) (𝟙 N) k
  · intro N N' n
    apply NatTrans.ext
    funext K
    simpa [moduleTensorChange, bifunctorComp₁₂, bifunctorComp₁₂Obj,
      bifunctorComp₂₃, bifunctorComp₂₃Obj] using
      moduleTensorChangeAssociator_naturality.{uA, uB, uC, v} f g (𝟙 M) n (𝟙 K)
  · intro M M' m
    apply NatTrans.ext
    funext N
    apply NatTrans.ext
    funext K
    simpa [moduleTensorChange, bifunctorComp₁₂, bifunctorComp₁₂Obj,
      bifunctorComp₂₃, bifunctorComp₂₃Obj] using
      moduleTensorChangeAssociator_naturality.{uA, uB, uC, v} f g m (𝟙 N) (𝟙 K)

private lemma moduleTensorChangeAssociatorNatIso_hom_app
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (M : ModuleCat.{max v uA uB uC} A) (N : ModuleCat.{max v uA uB uC} B)
    (K : ModuleCat.{max v uA uB uC} C) :
    (((moduleTensorChangeAssociatorNatIso.{uA, uB, uC, v} f g).hom.app M).app N).app K =
      (moduleTensorChangeAssociator.{uA, uB, uC, v} f g M N K).hom := rfl

private lemma moduleTensorChange_additive
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B) :
    (moduleTensorChange.{uA, uB, v} f).Additive := by
  let := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidalPreadditive.{uB, max v uA} (R := B)
  let := (ModuleCat.extendRestrictScalarsAdj.{max v uA uB, uA, uB} f).left_adjoint_additive
  change (ModuleCat.extendScalars f ⋙ curriedTensor (ModuleCat.{max v uA uB} B)).Additive
  infer_instance

private lemma moduleTensorChange_obj_additive
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (M : ModuleCat.{max v uA uB} A) :
    ((moduleTensorChange.{uA, uB, v} f).obj M).Additive := by
  let := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidalPreadditive.{uB, max v uA} (R := B)
  exact inferInstanceAs (((curriedTensor (ModuleCat.{max v uA uB} B)).obj
    ((ModuleCat.extendScalars f).obj M)).Additive)

private lemma moduleTensorChange_preservesColimits
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (M : ModuleCat.{max v uA uB} A) :
    CategoryTheory.Limits.PreservesColimits ((moduleTensorChange.{uA, uB, v} f).obj M) := by
  let := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidalClosed.{uB, max v uA} (R := B)
  exact inferInstanceAs (CategoryTheory.Limits.PreservesColimits
    ((curriedTensor (ModuleCat.{max v uA uB} B)).obj ((ModuleCat.extendScalars f).obj M)))

private lemma moduleTensorChange_flip_preservesColimits
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (N : ModuleCat.{max v uA uB} B) :
    CategoryTheory.Limits.PreservesColimits ((moduleTensorChange.{uA, uB, v} f).flip.obj N) := by
  let := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
  let := ModuleCat.liftedModuleMonoidalClosed.{uB, max v uA} (R := B)
  let := (ModuleCat.extendRestrictScalarsAdj.{max v uA uB, uA, uB} f).isLeftAdjoint
  let e : ((moduleTensorChange.{uA, uB, v} f).flip.obj N) ≅
      ModuleCat.extendScalars f ⋙ MonoidalCategory.tensorLeft N :=
    NatIso.ofComponents
      (fun M => (TensorProduct.comm B ((ModuleCat.extendScalars f).obj M) N).toModuleIso)
      (by
        intro M M' m
        apply ModuleCat.hom_ext
        apply TensorProduct.ext'
        intro x n
        rfl)
  exact CategoryTheory.Limits.preservesColimits_of_natIso e.symm

attribute [local instance] moduleTensorChange_additive moduleTensorChange_obj_additive
  moduleTensorChange_preservesColimits moduleTensorChange_flip_preservesColimits

private lemma tensorChange_obj
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (M : CochainComplex (ModuleCat.{max v uA uB} A) ℤ)
    (N : CochainComplex (ModuleCat.{max v uA uB} B) ℤ) :
    letI := ModuleCat.liftedModuleMonoidalStruct.{uB, max v uA} (R := B)
    letI := ModuleCat.liftedModuleMonoidal.{uB, max v uA} (R := B)
    letI := ModuleCat.liftedModuleMonoidalPreadditive.{uB, max v uA} (R := B)
    letI := (ModuleCat.extendRestrictScalarsAdj.{max v uA uB, uA, uB} f).left_adjoint_additive
    letI : ∀ X, ((moduleTensorChange.{uA, uB, v} f).obj X).PreservesZeroMorphisms :=
      fun X => inferInstanceAs (((curriedTensor (ModuleCat.{max v uA uB} B)).obj
        ((ModuleCat.extendScalars f).obj X)).PreservesZeroMorphisms)
    ((moduleTensorChange.{uA, uB, v} f).map₂CochainComplex.obj M).obj N =
      (tensorRightLarge.{uB, max v uA} N).obj ((extendScalarsLarge.{v, uA, uB} f).obj M) := by
  rfl

private abbrev tensorChange
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B) :
    CochainComplex (ModuleCat.{max v uA uB} A) ℤ ⥤
      CochainComplex (ModuleCat.{max v uA uB} B) ℤ ⥤
        CochainComplex (ModuleCat.{max v uA uB} B) ℤ := by
  letI : (moduleTensorChange.{uA, uB, v} f).Additive := moduleTensorChange_additive.{uA, uB, v} f
  letI : ∀ M, ((moduleTensorChange.{uA, uB, v} f).obj M).Additive :=
    moduleTensorChange_obj_additive.{uA, uB, v} f
  exact (moduleTensorChange.{uA, uB, v} f).map₂CochainComplex

private def tensorChangeAssociator
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
    (N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ)
    (K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ) :
    ((tensorChange.{uB, uC, max v uA} g).obj
      (((tensorChange.{uA, uB, max v uC} f).obj M).obj N)).obj K ≅
    ((tensorChange.{uA, uC, max v uB} (g.comp f)).obj M).obj
      (((tensorChange.{uB, uC, max v uA} g).obj N).obj K) :=
  by
  letI : (moduleTensorChange.{uA, uB, max v uC} f).Additive :=
    moduleTensorChange_additive.{uA, uB, max v uC} f
  letI : (moduleTensorChange.{uB, uC, max v uA} g).Additive :=
    moduleTensorChange_additive.{uB, uC, max v uA} g
  letI : (moduleTensorChange.{uA, uC, max v uB} (g.comp f)).Additive :=
    moduleTensorChange_additive.{uA, uC, max v uB} _
  letI : ∀ M, ((moduleTensorChange.{uA, uB, max v uC} f).obj M).Additive :=
    moduleTensorChange_obj_additive.{uA, uB, max v uC} f
  letI : ∀ M, ((moduleTensorChange.{uB, uC, max v uA} g).obj M).Additive :=
    moduleTensorChange_obj_additive.{uB, uC, max v uA} g
  letI : ∀ M, ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M).Additive :=
    moduleTensorChange_obj_additive.{uA, uC, max v uB} _
  letI : ∀ M, Limits.PreservesColimits ((moduleTensorChange.{uB, uC, max v uA} g).flip.obj M) :=
    moduleTensorChange_flip_preservesColimits.{uB, uC, max v uA} g
  letI : ∀ M, Limits.PreservesColimits ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M) :=
    moduleTensorChange_preservesColimits.{uA, uC, max v uB} _
  letI : ∀ M, Limits.PreservesColimitsOfSize.{0, 0}
      ((moduleTensorChange.{uB, uC, max v uA} g).flip.obj M) := fun M =>
    Limits.preservesSmallestColimits_of_preservesColimits _
  letI : ∀ M, Limits.PreservesColimitsOfSize.{0, 0}
      ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M) := fun M =>
    Limits.preservesSmallestColimits_of_preservesColimits _
  letI : HomologicalComplex.HasGoodTrifunctor₁₂Obj
      (moduleTensorChange.{uA, uB, max v uC} f) (moduleTensorChange.{uB, uC, max v uA} g)
      M N K (.up ℤ) (.up ℤ) := fun i j => by infer_instance
  letI : HomologicalComplex.HasGoodTrifunctor₂₃Obj
      (moduleTensorChange.{uA, uC, max v uB} (g.comp f)) (moduleTensorChange.{uB, uC, max v uA} g)
      M N K (.up ℤ) (.up ℤ) (.up ℤ) := fun i j => by infer_instance
  exact HomologicalComplex.mapBifunctorAssociator
    (moduleTensorChangeAssociatorNatIso.{uA, uB, uC, v} f g) M N K (.up ℤ) (.up ℤ) (.up ℤ)

private abbrev tensorChangeElement
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (M : CochainComplex (ModuleCat.{max v uA uB} A) ℤ)
    (N : CochainComplex (ModuleCat.{max v uA uB} B) ℤ)
    (i j q : ℤ) (h : i + j = q) (x : M.X i) (n : N.X j) :
    (((tensorChange.{uA, uB, v} f).obj M).obj N).X q :=
  HomologicalComplex.ιMapBifunctor M N (moduleTensorChange.{uA, uB, v} f) (.up ℤ)
    i j q h (moduleTensorElement.{uA, uB, v} f (M.X i) (N.X j) x n)

set_option backward.isDefEq.respectTransparency false in
private lemma tensorChangeAssociator_hom_element
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
    (N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ)
    (K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ)
    (i j k q : ℤ) (h : (i + j) + k = q) (x : M.X i) (n : N.X j) (l : K.X k) :
    ((tensorChangeAssociator.{uA, uB, uC, v} f g M N K).hom.f q)
      (tensorChangeElement.{uB, uC, max v uA} g _ K (i + j) k q h
        (tensorChangeElement.{uA, uB, max v uC} f M N i j (i + j) rfl x n) l) =
    tensorChangeElement.{uA, uC, max v uB} (g.comp f) M _ i (j + k) q (by omega) x
      (tensorChangeElement.{uB, uC, max v uA} g N K j k (j + k) rfl n l) := by
  let : (moduleTensorChange.{uA, uB, max v uC} f).Additive :=
    moduleTensorChange_additive.{uA, uB, max v uC} f
  let : (moduleTensorChange.{uB, uC, max v uA} g).Additive :=
    moduleTensorChange_additive.{uB, uC, max v uA} g
  let : (moduleTensorChange.{uA, uC, max v uB} (g.comp f)).Additive :=
    moduleTensorChange_additive.{uA, uC, max v uB} _
  let : ∀ M, ((moduleTensorChange.{uA, uB, max v uC} f).obj M).Additive :=
    moduleTensorChange_obj_additive.{uA, uB, max v uC} f
  let : ∀ M, ((moduleTensorChange.{uB, uC, max v uA} g).obj M).Additive :=
    moduleTensorChange_obj_additive.{uB, uC, max v uA} g
  let : ∀ M, ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M).Additive :=
    moduleTensorChange_obj_additive.{uA, uC, max v uB} _
  let : ∀ M, Limits.PreservesColimits ((moduleTensorChange.{uB, uC, max v uA} g).flip.obj M) :=
    moduleTensorChange_flip_preservesColimits.{uB, uC, max v uA} g
  let : ∀ M, Limits.PreservesColimits ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M) :=
    moduleTensorChange_preservesColimits.{uA, uC, max v uB} _
  let : ∀ M, Limits.PreservesColimitsOfSize.{0, 0}
      ((moduleTensorChange.{uB, uC, max v uA} g).flip.obj M) := fun M =>
    Limits.preservesSmallestColimits_of_preservesColimits _
  let : ∀ M, Limits.PreservesColimitsOfSize.{0, 0}
      ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M) := fun M =>
    Limits.preservesSmallestColimits_of_preservesColimits _
  let : HomologicalComplex.HasGoodTrifunctor₁₂Obj
      (moduleTensorChange.{uA, uB, max v uC} f) (moduleTensorChange.{uB, uC, max v uA} g)
      M N K (.up ℤ) (.up ℤ) := fun i j => by infer_instance
  let : HomologicalComplex.HasGoodTrifunctor₂₃Obj
      (moduleTensorChange.{uA, uC, max v uB} (g.comp f)) (moduleTensorChange.{uB, uC, max v uA} g)
      M N K (.up ℤ) (.up ℤ) (.up ℤ) := fun i j => by infer_instance
  change (HomologicalComplex.mapBifunctor₁₂.ι
    (moduleTensorChange.{uA, uB, max v uC} f) (moduleTensorChange.{uB, uC, max v uA} g)
    M N K (.up ℤ) (.up ℤ) i j k q h ≫
      (HomologicalComplex.mapBifunctorAssociatorX
        (moduleTensorChangeAssociatorNatIso.{uA, uB, uC, v} f g)
        M N K (.up ℤ) (.up ℤ) (.up ℤ) q).hom)
    (moduleTensorElement.{uB, uC, max v uA} g _ _
      (moduleTensorElement.{uA, uB, max v uC} f _ _ x n) l) = _
  rw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom]
  change (HomologicalComplex.mapBifunctor₂₃.ι
    (moduleTensorChange.{uA, uC, max v uB} (g.comp f)) (moduleTensorChange.{uB, uC, max v uA} g)
    M N K (.up ℤ) (.up ℤ) (.up ℤ) i j k q h)
    ((moduleTensorChangeAssociator.{uA, uB, uC, v} f g (M.X i) (N.X j) (K.X k)).hom
      (moduleTensorElement.{uB, uC, max v uA} g _ _
        (moduleTensorElement.{uA, uB, max v uC} f _ _ x n) l)) = _
  rw [moduleTensorChangeAssociator_hom_tmul]
  rfl

set_option backward.isDefEq.respectTransparency false in
private def tensorChangeComparison
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (N : CochainComplex (ModuleCat.{max v uA uB} B) ℤ) :
    (tensorChange.{uA, uB, v} f).flip.obj N ≅
      extendScalarsLarge.{v, uA, uB} f ⋙ tensorRightLarge.{uB, max v uA} N :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
private lemma tensorChange_map_element
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    {M M' : CochainComplex (ModuleCat.{max v uA uB} A) ℤ}
    {N N' : CochainComplex (ModuleCat.{max v uA uB} B) ℤ}
    (m : M ⟶ M') (n : N ⟶ N') (i j q : ℤ) (h : i + j = q)
    (x : M.X i) (y : N.X j) :
    (HomologicalComplex.mapBifunctorMap m n (moduleTensorChange.{uA, uB, v} f) (.up ℤ)).f q
      (tensorChangeElement.{uA, uB, v} f M N i j q h x y) =
    tensorChangeElement.{uA, uB, v} f M' N' i j q h (m.f i x) (n.f j y) := by
  change (HomologicalComplex.ιMapBifunctor M N (moduleTensorChange.{uA, uB, v} f) (.up ℤ) i j q h ≫
    (HomologicalComplex.mapBifunctorMap m n (moduleTensorChange.{uA, uB, v} f) (.up ℤ)).f q)
    (moduleTensorElement.{uA, uB, v} f _ _ x y) = _
  rw [HomologicalComplex.ι_mapBifunctorMap]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma directTensorComparison_tensorElement
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] {f : A →+* B}
    {N : CochainComplex (ModuleCat.{max v uA uB} B) ℤ}
    (T : DerivedTensorChangeOfRings.{uA, uB, v} f N)
    (M : CochainComplex (ModuleCat.{max v uA uB} A) ℤ)
    (i j q : ℤ) (h : i + j = q) (x : M.X i) (y : N.X j) :
    (T.directTensorComparison.hom.app M).f q (T.tensorElement M i j q h x y) =
      tensorChangeElement.{uA, uB, v} f M N i j q h x y := by
  unfold DerivedTensorChangeOfRings.tensorElement
  rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f]
  simp
  rfl

private lemma existsUnique_leftDerivedNatIso
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {F G : C ⥤ E} (LF LG : D ⥤ E)
    (α : L ⋙ LF ⟶ F) (β : L ⋙ LG ⟶ G)
    [LF.IsLeftDerivedFunctor α W] [LG.IsLeftDerivedFunctor β W] (e : F ≅ G) :
    ∃! comparison : LF ≅ LG,
      Functor.whiskerLeft L comparison.hom ≫ β = α ≫ e.hom :=
  ⟨Functor.leftDerivedNatIso LF LG α β W e, Functor.leftDerivedNatTrans_fac LF LG α β W e.hom,
    fun _ h => Iso.ext <| Functor.leftDerived_ext LG β W LF _ _
      (h.trans (Functor.leftDerivedNatTrans_fac LF LG α β W e.hom).symm)⟩

section AssociatorNaturality

open HomologicalComplex Category Limits

variable {C₁ C₂ C₁₂ C₂₃ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] [Category* C₁₂] [Category* C₂₃]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [HasZeroMorphisms C₃]
  [Preadditive C₁₂] [Preadditive C₂₃] [Preadditive C₄]
  {F₁₂ : C₁ ⥤ C₂ ⥤ C₁₂} {G : C₁₂ ⥤ C₃ ⥤ C₄}
  {F : C₁ ⥤ C₂₃ ⥤ C₄} {G₂₃ : C₂ ⥤ C₃ ⥤ C₂₃}
  [F₁₂.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F₁₂.obj X₁).PreservesZeroMorphisms]
  [G.Additive] [∀ (X₁₂ : C₁₂), (G.obj X₁₂).PreservesZeroMorphisms]
  [G₂₃.PreservesZeroMorphisms] [∀ (X₂ : C₂), (G₂₃.obj X₂).PreservesZeroMorphisms]
  [F.PreservesZeroMorphisms] [∀ (X₁ : C₁), (F.obj X₁).Additive]
  (associator : bifunctorComp₁₂ F₁₂ G ≅ bifunctorComp₂₃ F G₂₃)
  {ι₁ ι₂ ι₃ ι₁₂ ι₂₃ ι₄ : Type*} [DecidableEq ι₄] [DecidableEq ι₁₂] [DecidableEq ι₂₃]
  {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂} {c₃ : ComplexShape ι₃}
  {K₁ L₁ : HomologicalComplex C₁ c₁} (φ : K₁ ⟶ L₁) (K₂ : HomologicalComplex C₂ c₂)
  (K₃ : HomologicalComplex C₃ c₃)
  (c₁₂ : ComplexShape ι₁₂) (c₂₃ : ComplexShape ι₂₃) (c₄ : ComplexShape ι₄)
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c₄]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c₄]
  [HomologicalComplex.HasMapBifunctor K₁ K₂ F₁₂ c₁₂]
  [HomologicalComplex.HasMapBifunctor K₂ K₃ G₂₃ c₂₃]
  [HomologicalComplex.HasMapBifunctor L₁ K₂ F₁₂ c₁₂]
  [ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c₄]
  [HomologicalComplex.HasMapBifunctor
    (HomologicalComplex.mapBifunctor K₁ K₂ F₁₂ c₁₂) K₃ G c₄]
  [HomologicalComplex.HasMapBifunctor K₁
    (HomologicalComplex.mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄]
  [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]
  [HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄]
  [HomologicalComplex.HasMapBifunctor
    (HomologicalComplex.mapBifunctor L₁ K₂ F₁₂ c₁₂) K₃ G c₄]
  [HomologicalComplex.HasMapBifunctor L₁
    (HomologicalComplex.mapBifunctor K₂ K₃ G₂₃ c₂₃) F c₄]
  [HasGoodTrifunctor₁₂Obj F₁₂ G L₁ K₂ K₃ c₁₂ c₄]
  [HasGoodTrifunctor₂₃Obj F G₂₃ L₁ K₂ K₃ c₁₂ c₂₃ c₄]

omit [HasGoodTrifunctor₁₂Obj F₁₂ G K₁ K₂ K₃ c₁₂ c₄]
  [HasGoodTrifunctor₁₂Obj F₁₂ G L₁ K₂ K₃ c₁₂ c₄] in
set_option backward.isDefEq.respectTransparency false in
private lemma ι₁₂_map (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j) :
    mapBifunctor₁₂.ι F₁₂ G K₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h ≫
      (mapBifunctorMap (mapBifunctorMap φ (𝟙 K₂) F₁₂ c₁₂) (𝟙 K₃) G c₄).f j =
    ((G.map ((F₁₂.map (φ.f i₁)).app (K₂.X i₂))).app (K₃.X i₃)) ≫
      mapBifunctor₁₂.ι F₁₂ G L₁ K₂ K₃ c₁₂ c₄ i₁ i₂ i₃ j h := by
  rw [mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ i₁ i₂ i₃ _ j rfl h,
    mapBifunctor₁₂.ι_eq _ _ _ _ _ _ _ i₁ i₂ i₃ _ j rfl h]
  simp only [assoc, ι_mapBifunctorMap, id_f]
  simp only [← assoc, ← NatTrans.comp_app, ← Functor.map_comp, ι_mapBifunctorMap]
  simp

omit [DecidableEq ι₁₂] [HasGoodTrifunctor₂₃Obj F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄]
  [HasGoodTrifunctor₂₃Obj F G₂₃ L₁ K₂ K₃ c₁₂ c₂₃ c₄] in
set_option backward.isDefEq.respectTransparency false in
private lemma ι₂₃_map (i₁ : ι₁) (i₂ : ι₂) (i₃ : ι₃) (j : ι₄)
    (h : ComplexShape.r c₁ c₂ c₃ c₁₂ c₄ (i₁, i₂, i₃) = j) :
    mapBifunctor₂₃.ι F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ j h ≫
      (mapBifunctorMap φ (𝟙 (HomologicalComplex.mapBifunctor K₂ K₃ G₂₃ c₂₃)) F c₄).f j =
    (F.map (φ.f i₁)).app _ ≫
      mapBifunctor₂₃.ι F G₂₃ L₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ j h := by
  have h' : ComplexShape.π c₁ c₂₃ c₄ (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j := by
    rw [← h, ComplexShape.r, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c₄]
  have e₁ := mapBifunctor₂₃.ι_eq F G₂₃ K₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ _ j rfl h'
  have e₂ := mapBifunctor₂₃.ι_eq F G₂₃ L₁ K₂ K₃ c₁₂ c₂₃ c₄ i₁ i₂ i₃ _ j rfl h'
  rw [e₁, e₂]
  simp only [assoc, ι_mapBifunctorMap, id_f]
  simp only [← assoc, NatTrans.naturality]
  rw [CategoryTheory.Functor.map_id, comp_id]

set_option backward.isDefEq.respectTransparency false in
private lemma mapBifunctorAssociator_hom_naturality₁ :
    mapBifunctorMap (mapBifunctorMap φ (𝟙 K₂) F₁₂ c₁₂) (𝟙 K₃) G c₄ ≫
      (mapBifunctorAssociator associator L₁ K₂ K₃ c₁₂ c₂₃ c₄).hom =
    (mapBifunctorAssociator associator K₁ K₂ K₃ c₁₂ c₂₃ c₄).hom ≫
      mapBifunctorMap φ (𝟙 _) F c₄ := by
  ext j i₁ i₂ i₃ h
  dsimp [mapBifunctorAssociator]
  rw [reassoc_of% ι₁₂_map, ι_mapBifunctorAssociatorX_hom, ι_mapBifunctorAssociatorX_hom_assoc,
    ι₂₃_map]
  have := NatTrans.naturality_app_app associator.hom (φ.f i₁) (K₂.X i₂) (K₃.X i₃)
  exact (reassoc_of% this) _
end AssociatorNaturality

set_option backward.isDefEq.respectTransparency false in
private lemma tensorChangeAssociator_naturality
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    {M M' : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ} (m : M ⟶ M')
    (N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ)
    (K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ) :
    ((tensorChange.{uB, uC, max v uA} g).map
      (((tensorChange.{uA, uB, max v uC} f).map m).app N)).app K ≫
      (tensorChangeAssociator.{uA, uB, uC, v} f g M' N K).hom =
    (tensorChangeAssociator.{uA, uB, uC, v} f g M N K).hom ≫
      ((tensorChange.{uA, uC, max v uB} (g.comp f)).map m).app
        (((tensorChange.{uB, uC, max v uA} g).obj N).obj K) := by
  let : (moduleTensorChange.{uA, uB, max v uC} f).Additive :=
    moduleTensorChange_additive.{uA, uB, max v uC} f
  let : (moduleTensorChange.{uB, uC, max v uA} g).Additive :=
    moduleTensorChange_additive.{uB, uC, max v uA} g
  let : (moduleTensorChange.{uA, uC, max v uB} (g.comp f)).Additive :=
    moduleTensorChange_additive.{uA, uC, max v uB} _
  let : ∀ M, ((moduleTensorChange.{uA, uB, max v uC} f).obj M).Additive :=
    moduleTensorChange_obj_additive.{uA, uB, max v uC} f
  let : ∀ M, ((moduleTensorChange.{uB, uC, max v uA} g).obj M).Additive :=
    moduleTensorChange_obj_additive.{uB, uC, max v uA} g
  let : ∀ M, ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M).Additive :=
    moduleTensorChange_obj_additive.{uA, uC, max v uB} _
  let : ∀ M, Limits.PreservesColimits ((moduleTensorChange.{uB, uC, max v uA} g).flip.obj M) :=
    moduleTensorChange_flip_preservesColimits.{uB, uC, max v uA} g
  let : ∀ M, Limits.PreservesColimits ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M) :=
    moduleTensorChange_preservesColimits.{uA, uC, max v uB} _
  let : ∀ M, Limits.PreservesColimitsOfSize.{0, 0}
      ((moduleTensorChange.{uB, uC, max v uA} g).flip.obj M) := fun M =>
    Limits.preservesSmallestColimits_of_preservesColimits _
  let : ∀ M, Limits.PreservesColimitsOfSize.{0, 0}
      ((moduleTensorChange.{uA, uC, max v uB} (g.comp f)).obj M) := fun M =>
    Limits.preservesSmallestColimits_of_preservesColimits _
  let : HomologicalComplex.HasGoodTrifunctor₁₂Obj
      (moduleTensorChange.{uA, uB, max v uC} f) (moduleTensorChange.{uB, uC, max v uA} g)
      M' N K (.up ℤ) (.up ℤ) := fun i j => by infer_instance
  let : HomologicalComplex.HasGoodTrifunctor₂₃Obj
      (moduleTensorChange.{uA, uC, max v uB} (g.comp f)) (moduleTensorChange.{uB, uC, max v uA} g)
      M' N K (.up ℤ) (.up ℤ) (.up ℤ) := fun i j => by infer_instance
  let : HomologicalComplex.HasGoodTrifunctor₁₂Obj
      (moduleTensorChange.{uA, uB, max v uC} f) (moduleTensorChange.{uB, uC, max v uA} g)
      M N K (.up ℤ) (.up ℤ) := fun i j => by infer_instance
  let : HomologicalComplex.HasGoodTrifunctor₂₃Obj
      (moduleTensorChange.{uA, uC, max v uB} (g.comp f)) (moduleTensorChange.{uB, uC, max v uA} g)
      M N K (.up ℤ) (.up ℤ) (.up ℤ) := fun i j => by infer_instance
  exact mapBifunctorAssociator_hom_naturality₁ _ m N K _ _ _

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_map_of_quasiIso {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    {f : R →+* S}
    {L N : CochainComplex (ModuleCat.{max w uR uS} S) ℤ}
    (X : DerivedTensorChangeOfRings.{uR, uS, w} f L)
    (Y : DerivedTensorChangeOfRings.{uR, uS, w} f N) (r : L ⟶ N) [QuasiIso r] :
    IsIso (X.map Y r) := by
  apply isIso_of_isIso_app_kFlat.{uR, max w uS}
  intro M hM
  have hX := X.isIso_alphaF M hM
  have hY := Y.isIso_alphaF M hM
  have hE := CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uR, uS, w} f M hM
  have hq : QuasiIso ((TleftCochain ((extendScalarsLarge.{w, uR, uS} f).obj M)).map r) :=
    quasiIso_tleft_map_of_kFlat.{uS, max w uR} _ hE r
  have hfac := NatTrans.congr_app (X.map_fac Y r) M
  simp only [Functor.comp_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hfac
  have : IsIso (DerivedCategory.Q.map ((X.directTensorMap Y r).app M)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    simp only [DerivedTensorChangeOfRings.directTensorMap, NatTrans.comp_app,
      Functor.whiskerLeft_app]
    exact quasiIso_comp (hφ := quasiIso_of_isIso _)
      (hφ' := quasiIso_comp (hφ := hq) (hφ' := quasiIso_of_isIso _) _ _) _ _
  have : IsIso ((X.map Y r).app (DerivedCategory.Q.obj M) ≫ Y.alphaF.app M) := by
    rw [hfac]; infer_instance
  exact IsIso.of_isIso_comp_right _ (Y.alphaF.app M)


set_option backward.isDefEq.respectTransparency false in
private lemma directTensorComparison_inv_element
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] {f : A →+* B}
    {N : CochainComplex (ModuleCat.{max v uA uB} B) ℤ}
    (T : DerivedTensorChangeOfRings.{uA, uB, v} f N)
    (M : CochainComplex (ModuleCat.{max v uA uB} A) ℤ)
    (i j q : ℤ) (h : i + j = q) (x : M.X i) (y : N.X j) :
    (T.directTensorComparison.inv.app M).f q (tensorChangeElement.{uA, uB, v} f M N i j q h x y) =
      T.tensorElement M i j q h x y := by
  rw [← directTensorComparison_tensorElement, ← ModuleCat.comp_apply,
    ← HomologicalComplex.comp_f, ← NatTrans.comp_app, Iso.hom_inv_id]
  rfl

private def directTensorIso
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] {f : A →+* B}
    {N : CochainComplex (ModuleCat.{max v uA uB} B) ℤ}
    (T : DerivedTensorChangeOfRings.{uA, uB, v} f N) :
    T.directTensor ≅ (tensorChange.{uA, uB, v} f).flip.obj N :=
  T.directTensorComparison ≪≫ (tensorChangeComparison.{uA, uB, v} f N).symm

private def tensorChangeAssociatorNatIso
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ)
    (K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ) :
    (tensorChange.{uA, uB, max v uC} f).flip.obj N ⋙
        (tensorChange.{uB, uC, max v uA} g).flip.obj K ≅
      (tensorChange.{uA, uC, max v uB} (g.comp f)).flip.obj
        (((tensorChange.{uB, uC, max v uA} g).obj N).obj K) :=
  NatIso.ofComponents (fun M => tensorChangeAssociator.{uA, uB, uC, v} f g M N K)
    (fun m => tensorChangeAssociator_naturality.{uA, uB, uC, v} f g m N K)

/-- The two direct tensor functors composed, identified with one tensor against `N ⊗ K`. -/
private def iteratedDirectTensorIso
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    {N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ}
    {K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ}
    (S : DerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N)
    (T : DerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K) :
    S.directTensor ⋙ T.directTensor ≅
      (tensorChange.{uA, uC, max v uB} (g.comp f)).flip.obj
        (((tensorChange.{uB, uC, max v uA} g).obj N).obj K) :=
  Functor.isoWhiskerLeft S.directTensor (directTensorIso.{uB, uC, max v uA uB uC} T) ≪≫
    Functor.isoWhiskerRight (directTensorIso.{uA, uB, max v uA uB uC} S) _ ≪≫
    tensorChangeAssociatorNatIso.{uA, uB, uC, v} f g N K

private def ordinaryAssociatorIso
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    {N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ}
    {K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ}
    (S : DerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N)
    (T : DerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K)
    (U : DerivedTensorChangeOfRings.{uA, uC, max v uA uB uC} (g.comp f)
      (T.directTensor.obj N)) :
    S.directTensor ⋙ T.directTensor ≅ U.directTensor :=
  iteratedDirectTensorIso.{uA, uB, uC, v} S T ≪≫
    (tensorChange.{uA, uC, max v uB} (g.comp f)).flip.mapIso
      ((directTensorIso.{uB, uC, max v uA uB uC} T).app N).symm ≪≫
    (directTensorIso.{uA, uC, max v uA uB uC} U).symm

private lemma iteratedDirectTensorIso_hom_element
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    {N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ}
    {K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ}
    (S : DerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N)
    (T : DerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K)
    (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
    (i j k : ℤ) (x : M.X i) (n : N.X j) (l : K.X k) :
    ((iteratedDirectTensorIso.{uA, uB, uC, v} S T).hom.app M).f ((i + j) + k)
        (T.tensorElement (S.directTensor.obj M) (i + j) k ((i + j) + k) rfl
          (S.tensorElement M i j (i + j) rfl x n) l) =
      tensorChangeElement.{uA, uC, max v uB} (g.comp f) M _ i (j + k) ((i + j) + k) (by omega) x
        (tensorChangeElement.{uB, uC, max v uA} g N K j k (j + k) rfl n l) := by
  set_option backward.isDefEq.respectTransparency false in
  simp only [iteratedDirectTensorIso, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    ModuleCat.comp_apply]
  have h1 : ((S.directTensor.isoWhiskerLeft
        (directTensorIso.{uB, uC, max v uA uB uC} T)).hom.app M).f (i + j + k)
      (T.tensorElement (S.directTensor.obj M) (i + j) k (i + j + k) rfl
        (S.tensorElement M i j (i + j) rfl x n) l) =
      tensorChangeElement.{uB, uC, max v uA} g _ K (i + j) k (i + j + k) rfl
        (S.tensorElement M i j (i + j) rfl x n) l :=
    directTensorComparison_tensorElement T _ _ _ _ _ _ _
  rw [h1]
  have h2 := tensorChange_map_element.{uB, uC, max v uA} g
    ((directTensorIso.{uA, uB, max v uA uB uC} S).hom.app M)
    (𝟙 K) (i + j) k (i + j + k) rfl (S.tensorElement M i j (i + j) rfl x n) l
  erw [h2]
  have h3 : ((directTensorIso.{uA, uB, max v uA uB uC} S).hom.app M).f (i + j)
        (S.tensorElement M i j (i + j) rfl x n) =
      tensorChangeElement.{uA, uB, max v uC} f M N i j (i + j) rfl x n :=
    directTensorComparison_tensorElement S _ _ _ _ _ _ _
  rw [h3]
  exact tensorChangeAssociator_hom_element.{uA, uB, uC, v} f g M N K i j k (i + j + k) rfl x n l

set_option backward.isDefEq.respectTransparency false in
private lemma ordinaryAssociatorIso_hom_element
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    {N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ}
    {K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ}
    (S : DerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N)
    (T : DerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K)
    (U : DerivedTensorChangeOfRings.{uA, uC, max v uA uB uC} (g.comp f)
      (T.directTensor.obj N))
    (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
    (i j k : ℤ) (x : M.X i) (n : N.X j) (l : K.X k) :
    ((ordinaryAssociatorIso.{uA, uB, uC, v} S T U).hom.app M).f ((i + j) + k)
        (T.tensorElement (S.directTensor.obj M) (i + j) k ((i + j) + k) rfl
          (S.tensorElement M i j (i + j) rfl x n) l) =
      U.tensorElement M i (j + k) ((i + j) + k) (by omega) x
        (T.tensorElement N j k (j + k) rfl n l) := by
  simp only [ordinaryAssociatorIso, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    ModuleCat.comp_apply]
  rw [iteratedDirectTensorIso_hom_element]
  have h4 := tensorChange_map_element.{uA, uC, max v uB} (g.comp f) (𝟙 M)
    ((directTensorIso.{uB, uC, max v uA uB uC} T).inv.app N) i (j + k) (i + j + k) (by omega) x
    (tensorChangeElement.{uB, uC, max v uA} g N K j k (j + k) rfl n l)
  erw [h4]
  have h5 : ((directTensorIso.{uB, uC, max v uA uB uC} T).inv.app N).f (j + k)
      (tensorChangeElement.{uB, uC, max v uA} g N K j k (j + k) rfl n l) =
      T.tensorElement N j k (j + k) rfl n l :=
    directTensorComparison_inv_element T _ _ _ _ _ _ _
  rw [h5]
  exact directTensorComparison_inv_element U _ _ _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
private def extendScalarsIdIso {C : Type uC} [CommRing C]
    (L : CochainComplex (ModuleCat.{max v uC} C) ℤ) :
    L ≅ (extendScalarsLarge.{v, uC, uC} (RingHom.id C)).obj L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k => ((ModuleCat.extendScalarsId.{uC, v} C).app (L.X k)).symm)
    (fun k k' _ => ((ModuleCat.extendScalarsId.{uC, v} C).inv.naturality (L.d k k')).symm)

set_option backward.isDefEq.respectTransparency false in
private def tensorChangeSwap {B : Type uB} {C : Type uC} [CommRing B] [CommRing C] (g : B →+* C)
    (P : CochainComplex (ModuleCat.{max v uB uC} B) ℤ)
    (L : CochainComplex (ModuleCat.{max v uB uC} C) ℤ) :
    ((tensorChange.{uB, uC, v} g).obj P).obj L ≅
      ((tensorChange.{uC, uC, max v uB} (RingHom.id C)).obj L).obj
        ((extendScalarsLarge.{v, uB, uC} g).obj P) := by
  letI := ModuleCat.liftedModuleMonoidalStruct.{uC, max v uB} (R := C)
  letI := ModuleCat.liftedModuleMonoidal.{uC, max v uB} (R := C)
  letI := ModuleCat.liftedModuleMonoidalPreadditive.{uC, max v uB} (R := C)
  let E := (extendScalarsLarge.{v, uB, uC} g).obj P
  let L' := (extendScalarsLarge.{max v uB, uC, uC} (RingHom.id C)).obj L
  let e₁ : ((tensorChange.{uB, uC, v} g).obj P).obj L ≅ (TleftCochain E).obj L :=
    Iso.refl _
  let e₂ : (TleftCochain E).obj L ≅ (TrightCochain E).obj L :=
    tensorFlipIso.{uC, max v uB} E L
  let e₃ : (TrightCochain E).obj L ≅ (TrightCochain E).obj L' :=
    (TrightCochain E).mapIso (extendScalarsIdIso.{uC, max v uB} L)
  let e₄ : (TrightCochain E).obj L' ≅
      ((tensorChange.{uC, uC, max v uB} (RingHom.id C)).obj L).obj E :=
    Iso.refl _
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

set_option backward.isDefEq.respectTransparency false in
private lemma ι_tensorFlipIso_hom {R : Type uA} [CommRing R]
    (K L : CochainComplex (ModuleCat.{max v uA} R) ℤ) (j k q : ℤ) (h : j + k = q) :
    letI := ModuleCat.liftedModuleMonoidalStruct.{uA, v} (R := R)
    letI := ModuleCat.liftedModuleMonoidal.{uA, v} (R := R)
    HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat.{max v uA} R)) (.up ℤ)
        j k q h ≫ (tensorFlipIso.{uA, v} K L).hom.f q =
      (k * j).negOnePow • ((TensorProduct.comm R (K.X j) (L.X k)).toModuleIso.hom ≫
        HomologicalComplex.ιMapBifunctor L K (curriedTensor (ModuleCat.{max v uA} R)) (.up ℤ)
          k j q (by rw [← h]; exact add_comm k j)) := by
  let := ModuleCat.liftedModuleMonoidalStruct.{uA, v} (R := R)
  let := ModuleCat.liftedModuleMonoidal.{uA, v} (R := R)
  simp only [tensorFlipIso, Iso.trans_hom, HomologicalComplex.comp_f]
  erw [HomologicalComplex₂.ιTotal_map_assoc]
  rw [HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  rw [Linear.comp_units_smul]
  rfl


private lemma units_smul_apply {R : Type*} [Ring R] {X Y : ModuleCat.{v} R} (u : ℤˣ)
    (φ : X ⟶ Y) (x : X) : (u • φ) x = (u : ℤ) • φ x := rfl

private lemma negOnePow_mul_cast {C : Type*} [CommRing C] (j k : ℤ) :
    (((k * j).negOnePow : ℤ) : C) = (-1 : C) ^ (j * k).natAbs := by
  rw [mul_comm, Int.coe_negOnePow C (j * k)]

set_option backward.isDefEq.respectTransparency false in
private lemma tensorChangeSwap_hom_element {B : Type uB} {C : Type uC} [CommRing B] [CommRing C]
    (g : B →+* C)
    (P : CochainComplex (ModuleCat.{max v uB uC} B) ℤ)
    (L : CochainComplex (ModuleCat.{max v uB uC} C) ℤ) (j k q : ℤ) (h : j + k = q)
    (n : P.X j) (l : L.X k) :
    ((tensorChangeSwap.{uB, uC, v} g P L).hom.f q)
        (tensorChangeElement.{uB, uC, v} g P L j k q h n l) =
      ((-1 : C) ^ (j * k).natAbs) •
        tensorChangeElement.{uC, uC, max v uB} (RingHom.id C) L
          ((extendScalarsLarge.{v, uB, uC} g).obj P) k j q (by omega) l
          ((1 : C) ⊗ₜ[B,g] n) := by
  let := ModuleCat.liftedModuleMonoidalStruct.{uC, max v uB} (R := C)
  let := ModuleCat.liftedModuleMonoidal.{uC, max v uB} (R := C)
  let E := (extendScalarsLarge.{v, uB, uC} g).obj P
  change ((HomologicalComplex.ιMapBifunctor E L (curriedTensor (ModuleCat.{max v uB uC} C))
      (.up ℤ) j k q h ≫ (tensorFlipIso.{uC, max v uB} E L).hom.f q) ≫
      ((TrightCochain E).map (extendScalarsIdIso.{uC, max v uB} L).hom).f q)
      (((1 : C) ⊗ₜ[B,g] n) ⊗ₜ[C] l) = _
  rw [ι_tensorFlipIso_hom, Linear.units_smul_comp, Category.assoc]
  rw [units_smul_apply]
  rw [← negOnePow_mul_cast, Int.cast_smul_eq_zsmul]
  congr 1
  change (HomologicalComplex.ιMapBifunctor L E (curriedTensor (ModuleCat.{max v uB uC} C))
      (.up ℤ) k j q _ ≫ ((TrightCochain E).map (extendScalarsIdIso.{uC, max v uB} L).hom).f q)
      (l ⊗ₜ[C] ((1 : C) ⊗ₜ[B,g] n)) = _
  erw [HomologicalComplex.ι_mapBifunctorMap]
  rfl

private def ordinaryInterchangeIso
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    {N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ}
    {K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ}
    (S : DerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N)
    (T : DerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K)
    (U : DerivedTensorChangeOfRings.{uA, uC, max v uA uB uC} (g.comp f) K)
    (V : DerivedTensorChangeOfRings.{uC, uC, max v uA uB uC} (RingHom.id C)
      ((extendScalarsLarge.{max v uA uB uC, uB, uC} g).obj N)) :
    S.directTensor ⋙ T.directTensor ≅ U.directTensor ⋙ V.directTensor :=
  iteratedDirectTensorIso.{uA, uB, uC, v} S T ≪≫
    (tensorChange.{uA, uC, max v uB} (g.comp f)).flip.mapIso
      (tensorChangeSwap.{uB, uC, max v uA} g N K) ≪≫
    (tensorChangeAssociatorNatIso.{uA, uC, uC, max v uB} (g.comp f) (RingHom.id C) K
      ((extendScalarsLarge.{max v uA uB uC, uB, uC} g).obj N)).symm ≪≫
    Functor.isoWhiskerRight (directTensorIso.{uA, uC, max v uA uB uC} U).symm _ ≪≫
    Functor.isoWhiskerLeft U.directTensor (directTensorIso.{uC, uC, max v uA uB uC} V).symm

section KFlatTensor

open Limits
variable {R : Type uA} [CommRing R]
attribute [local instance] ModuleCat.liftedModuleMonoidalStruct
  ModuleCat.liftedModuleMonoidal ModuleCat.liftedModuleMonoidalPreadditive
  ModuleCat.liftedModuleMonoidalClosed

set_option backward.isDefEq.respectTransparency false in
private lemma kFlat_tensorObj (X Y : CochainComplex (ModuleCat.{max v uA} R) ℤ)
    (hX : CochainComplex.KFlat.{uA, v} X)
    (hY : CochainComplex.KFlat.{uA, v} Y) :
    CochainComplex.KFlat.{uA, v} (HomologicalComplex.tensorObj X Y) := by
  intro M hM
  have hflip : ∀ N : ModuleCat.{max v uA} R,
      PreservesColimits ((curriedTensor (ModuleCat.{max v uA} R)).flip.obj N) := fun N =>
    preservesColimits_of_natIso (NatIso.ofComponents
      (fun P => (TensorProduct.comm R N P).toModuleIso)
      (by intro P P' p; apply ModuleCat.hom_ext; apply TensorProduct.ext'; intro x n; rfl) :
        MonoidalCategory.tensorLeft N ≅ (curriedTensor (ModuleCat.{max v uA} R)).flip.obj N)
  let : ∀ M : ModuleCat.{max v uA} R, PreservesColimitsOfSize.{0, 0}
      ((curriedTensor (ModuleCat.{max v uA} R)).flip.obj M) := fun M =>
    have := hflip M
    preservesSmallestColimits_of_preservesColimits _
  let : ∀ M : ModuleCat.{max v uA} R, PreservesColimitsOfSize.{0, 0}
      ((curriedTensor (ModuleCat.{max v uA} R)).obj M) := fun M =>
    preservesSmallestColimits_of_preservesColimits _
  let : HomologicalComplex.HasGoodTensor₁₂ M X Y := fun i j => by infer_instance
  let : HomologicalComplex.HasGoodTensor₂₃ M X Y := fun i j => by infer_instance
  exact HomologicalComplex.Acyclic.of_iso (HomologicalComplex.associator M X Y)
    (hY _ (hX M hM))
end KFlatTensor

set_option backward.isDefEq.respectTransparency false in
private lemma tensorChangeAssociator_hom_element'
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
    (N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ)
    (K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ)
    (i j k p q : ℤ) (h : (i + j) + k = q) (h₁ : j + k = p) (h₂ : i + p = q)
    (x : M.X i) (n : N.X j) (l : K.X k) :
    ((tensorChangeAssociator.{uA, uB, uC, v} f g M N K).hom.f q)
      (tensorChangeElement.{uB, uC, max v uA} g _ K (i + j) k q h
        (tensorChangeElement.{uA, uB, max v uC} f M N i j (i + j) rfl x n) l) =
    tensorChangeElement.{uA, uC, max v uB} (g.comp f) M _ i p q h₂ x
      (tensorChangeElement.{uB, uC, max v uA} g N K j k p h₁ n l) := by
  subst h₁
  exact tensorChangeAssociator_hom_element.{uA, uB, uC, v} f g M N K i j k q h x n l

set_option backward.isDefEq.respectTransparency false in
private lemma tensorChangeAssociator_inv_element
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
    (N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ)
    (K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ)
    (i j k p q : ℤ) (h : (i + j) + k = q) (h₁ : j + k = p) (h₂ : i + p = q)
    (x : M.X i) (n : N.X j) (l : K.X k) :
    ((tensorChangeAssociator.{uA, uB, uC, v} f g M N K).inv.f q)
      (tensorChangeElement.{uA, uC, max v uB} (g.comp f) M _ i p q h₂ x
        (tensorChangeElement.{uB, uC, max v uA} g N K j k p h₁ n l)) =
    tensorChangeElement.{uB, uC, max v uA} g _ K (i + j) k q h
        (tensorChangeElement.{uA, uB, max v uC} f M N i j (i + j) rfl x n) l := by
  rw [← tensorChangeAssociator_hom_element'.{uA, uB, uC, v} f g M N K i j k p q h h₁ h₂,
    ← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, Iso.hom_inv_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma tensorChangeElement_smul
    {A : Type uA} {B : Type uB} [CommRing A] [CommRing B] (f : A →+* B)
    (M : CochainComplex (ModuleCat.{max v uA uB} A) ℤ)
    (N : CochainComplex (ModuleCat.{max v uA uB} B) ℤ)
    (i j q : ℤ) (h : i + j = q) (x : M.X i) (c : B) (n : N.X j) :
    tensorChangeElement.{uA, uB, v} f M N i j q h x (c • n) =
      c • tensorChangeElement.{uA, uB, v} f M N i j q h x n := by
  unfold tensorChangeElement moduleTensorElement
  rw [TensorProduct.tmul_smul]
  exact LinearMap.map_smul _ _ _


set_option backward.isDefEq.respectTransparency false in
private lemma ordinaryInterchangeIso_hom_element
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    {N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ}
    {K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ}
    (S : DerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N)
    (T : DerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K)
    (U : DerivedTensorChangeOfRings.{uA, uC, max v uA uB uC} (g.comp f) K)
    (V : DerivedTensorChangeOfRings.{uC, uC, max v uA uB uC} (RingHom.id C)
      ((extendScalarsLarge.{max v uA uB uC, uB, uC} g).obj N))
    (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
    (i j k : ℤ) (x : M.X i) (n : N.X j) (l : K.X k) :
    ((ordinaryInterchangeIso.{uA, uB, uC, v} S T U V).hom.app M).f ((i + j) + k)
        (T.tensorElement (S.directTensor.obj M) (i + j) k ((i + j) + k) rfl
          (S.tensorElement M i j (i + j) rfl x n) l) =
      (-1 : C) ^ (j * k).natAbs •
        V.tensorElement (U.directTensor.obj M) (i + k) j ((i + j) + k)
          (by omega) (U.tensorElement M i k (i + k) rfl x l)
          ((1 : C) ⊗ₜ[B,g] n) := by
  simp only [ordinaryInterchangeIso, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    ModuleCat.comp_apply]
  rw [iteratedDirectTensorIso_hom_element]
  have h4 := tensorChange_map_element.{uA, uC, max v uB} (g.comp f) (𝟙 M)
    (tensorChangeSwap.{uB, uC, max v uA} g N K).hom i (j + k) (i + j + k) (by omega) x
    (tensorChangeElement.{uB, uC, max v uA} g N K j k (j + k) rfl n l)
  erw [h4]
  rw [tensorChangeSwap_hom_element.{uB, uC, max v uA} g N K j k (j + k) rfl n l]
  rw [tensorChangeElement_smul]
  rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
  congr 1
  erw [tensorChangeAssociator_inv_element.{uA, uC, uC, max v uB} (g.comp f) (RingHom.id C) M K
    ((extendScalarsLarge.{max v uA uB uC, uB, uC} g).obj N) i k j (j + k) (i + j + k)
    (by omega) (by omega) (by omega) x l ((1 : C) ⊗ₜ[B,g] n)]
  have h6 := tensorChange_map_element.{uC, uC, max v uA uB} (RingHom.id C)
    ((directTensorIso.{uA, uC, max v uA uB uC} U).inv.app M)
    (𝟙 ((extendScalarsLarge.{max v uA uB uC, uB, uC} g).obj N)) (i + k) j (i + j + k) (by omega)
    (tensorChangeElement.{uA, uC, max v uB} (g.comp f) M K i k (i + k) rfl x l) ((1 : C) ⊗ₜ[B,g] n)
  erw [h6]
  have h7 : ((directTensorIso.{uA, uC, max v uA uB uC} U).inv.app M).f (i + k)
      (tensorChangeElement.{uA, uC, max v uB} (g.comp f) M K i k (i + k) rfl x l) =
      U.tensorElement M i k (i + k) rfl x l :=
    directTensorComparison_inv_element U _ _ _ _ _ _ _
  rw [h7]
  exact directTensorComparison_inv_element V _ _ _ _ _ _ _


set_option backward.isDefEq.respectTransparency false in
private lemma kFlat_directTensor_obj {A : Type uA} {B : Type uB} [CommRing A] [CommRing B]
    {f : A →+* B} {N : CochainComplex (ModuleCat.{max w uA uB} B) ℤ}
    (T : DerivedTensorChangeOfRings.{uA, uB, w} f N)
    (hN : CochainComplex.KFlat.{uB, max w uA} N)
    (M : CochainComplex (ModuleCat.{max w uA uB} A) ℤ)
    (hM : CochainComplex.KFlat.{uA, max w uB} M) :
    CochainComplex.KFlat.{uB, max w uA} (T.directTensor.obj M) :=
  CochainComplex.KFlat.of_iso.{uB, max w uA} (T.directTensorComparison.app M).symm
    (kFlat_tensorObj.{uB, max w uA} _ N
      (CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars.{uA, uB, w} f M hM) hN)

private lemma isIso_compositeCounit_app
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C}
    {N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ}
    {K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ}
    (S : DerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N)
    (T : DerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K)
    (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
    [IsIso (S.alphaF.app M)] [IsIso (T.alphaF.app (S.directTensor.obj M))] :
    IsIso ((compositeCounit.{uA, uB, uC, v} S T).app M) := by
  simp only [compositeCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Category.id_comp, Category.comp_id]
  infer_instance

private lemma isLeftDerivedFunctor_comp_iso {C D H : Type*} [Category C] [Category D] [Category H]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    {T T' : C ⥤ H} (F : D ⥤ H) (α : L ⋙ F ⟶ T) [F.IsLeftDerivedFunctor α W] (e : T ≅ T') :
    F.IsLeftDerivedFunctor (α ≫ e.hom) W := by
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  rw [← Functor.isRightKanExtension_iff_of_iso₂ α (α ≫ e.hom) e (Iso.refl F) (by simp)]
  exact Functor.IsLeftDerivedFunctor.isRightKanExtension F α W


set_option backward.isDefEq.respectTransparency false in
-- The statement is a deep nest of `let`s and existential quantifiers, and the
-- default transparency setting makes the elaborator refuse the projections of
-- the two iterated constructions.
/-- Canonical associativity of derived change of rings, with its signed interchange. The
ordinary maps send `(x ⊗ n) ⊗ k` to `x ⊗ (n ⊗ k)` and to `(-1)^(deg n * deg k) (x ⊗ k) ⊗ n`,
respectively. These equations and the specified counits of `DerivedTensorChangeOfRings` fix the
derived comparisons, including for nonflat `N` and `K`.

`rightFactor` identifies the complex used by `together` with `N ⊗ᴸ_B K`;
`baseFactor` identifies the second signed factor with `N ⊗ᴸ_B C`. The final isomorphism
to extension of scalars followed by tensoring is exactly the change-of-rings projection.
All comparisons are natural in the object of `D(A)`. -/
@[stacks 08YU]
public theorem derivedTensorProduct_doubleBaseChange
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ)
    (K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ) :
    let Q_A := DerivedCategory.Q (C := ModuleCat.{max v uA uB uC} A)
    let Q_B := DerivedCategory.Q (C := ModuleCat.{max v uA uB uC} B)
    let Q_C := DerivedCategory.Q (C := ModuleCat.{max v uA uB uC} C)
    let W_A := HomologicalComplex.quasiIso
      (ModuleCat.{max v uA uB uC} A) (ComplexShape.up ℤ)
    let PN := CochainComplex.KFlat.chosenResolution.{uB, max v uA uC} N
    let LK := CochainComplex.KFlat.chosenResolution.{uC, max v uA uB} K
    let AN := canonicalDerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N
    let AP := canonicalDerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f PN.complex
    let BK := canonicalDerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K
    let BL := canonicalDerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g LK.complex
    let AC := canonicalDerivedTensorChangeOfRings.{uA, uC, max v uA uB uC}
      (g.comp f) (BL.directTensor.obj PN.complex)
    let AL := canonicalDerivedTensorChangeOfRings.{uA, uC, max v uA uB uC}
      (g.comp f) LK.complex
    let AK := canonicalDerivedTensorChangeOfRings.{uA, uC, max v uA uB uC} (g.comp f) K
    let CP := canonicalDerivedTensorChangeOfRings.{uC, uC, max v uA uB uC}
      (RingHom.id C)
      ((extendScalarsLarge.{max v uA uB uC, uB, uC} g).obj PN.complex)
    let iterated := AN.F ⋙ BK.F
    let together := AC.F
    let signed := AK.F ⋙ CP.F
    ∃ (replaceN : AP.F ≅ AN.F) (replaceK : BL.F ≅ BK.F) (replaceAK : AL.F ≅ AK.F),
      replaceN.hom = AP.map AN PN.π ∧
      replaceK.hom = BL.map BK LK.π ∧
      replaceAK.hom = AL.map AK LK.π ∧
      ∃ (rightFactor : BK.F.obj (Q_B.obj N) ≅ Q_C.obj (BL.directTensor.obj PN.complex))
        (baseFactor : BK.B.obj (Q_B.obj N) ≅
          Q_C.obj ((extendScalarsLarge.{max v uA uB uC, uB, uC} g).obj PN.complex)),
        BL.F.map (Q_B.map PN.π) ≫ replaceK.hom.app (Q_B.obj N) ≫ rightFactor.hom =
          BL.alphaF.app PN.complex ∧
        BK.B.map (Q_B.map PN.π) ≫ baseFactor.hom = BK.alphaB.app PN.complex ∧
        ∃ (ordinaryAssociator : AP.directTensor ⋙ BL.directTensor ≅ AC.directTensor)
          (ordinaryInterchange : AP.directTensor ⋙ BL.directTensor ≅
            AL.directTensor ⋙ CP.directTensor),
          (∀ (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
              (i j k : ℤ) (x : M.X i) (n : PN.complex.X j) (l : LK.complex.X k),
            (ordinaryAssociator.hom.app M).f ((i + j) + k)
                (BL.tensorElement (AP.directTensor.obj M) (i + j) k ((i + j) + k) rfl
                  (AP.tensorElement M i j (i + j) rfl x n) l) =
              AC.tensorElement M i (j + k) ((i + j) + k) (by omega) x
                (BL.tensorElement PN.complex j k (j + k) rfl n l)) ∧
          (∀ (M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ)
              (i j k : ℤ) (x : M.X i) (n : PN.complex.X j) (l : LK.complex.X k),
            (ordinaryInterchange.hom.app M).f ((i + j) + k)
                (BL.tensorElement (AP.directTensor.obj M) (i + j) k ((i + j) + k) rfl
                  (AP.tensorElement M i j (i + j) rfl x n) l) =
              (-1 : C) ^ (j * k).natAbs •
                CP.tensorElement (AL.directTensor.obj M) (i + k) j ((i + j) + k)
                  (by omega) (AL.tensorElement M i k (i + k) rfl x l)
                  ((1 : C) ⊗ₜ[B,g] n)) ∧
          let replaceIterated := Functor.isoWhiskerRight replaceN BL.F ≪≫
            Functor.isoWhiskerLeft AN.F replaceK
          let replaceSigned := Functor.isoWhiskerRight replaceAK CP.F
          let direct := (AP.directTensor ⋙ BL.directTensor) ⋙ Q_C
          let iteratedComparison : Q_A ⋙ iterated ⟶ direct :=
            Functor.whiskerLeft Q_A replaceIterated.inv ≫ compositeCounit.{uA, uB, uC, v} AP BL
          let togetherComparison : Q_A ⋙ together ⟶ direct :=
            AC.alphaF ≫ Functor.whiskerRight ordinaryAssociator.inv Q_C
          let signedCounit := Functor.whiskerLeft Q_A replaceSigned.inv ≫
            compositeCounit.{uA, uC, uC, max v uB} AL CP
          iterated.IsLeftDerivedFunctor iteratedComparison W_A ∧
          together.IsLeftDerivedFunctor togetherComparison W_A ∧
          ∃ (doubleBaseChange : iterated ≅ together)
            (signedComparison : iterated ≅ signed)
            (baseChangeComparison : iterated ≅ AC.B ⋙ AC.G),
            Functor.whiskerLeft Q_A doubleBaseChange.hom ≫ togetherComparison =
              iteratedComparison ∧
            (∀ e : iterated ≅ together,
              Functor.whiskerLeft Q_A e.hom ≫ togetherComparison = iteratedComparison →
                e = doubleBaseChange) ∧
            Functor.whiskerLeft Q_A signedComparison.hom ≫ signedCounit =
              iteratedComparison ≫ Functor.whiskerRight ordinaryInterchange.hom Q_C ∧
            (∀ e : iterated ≅ signed,
              Functor.whiskerLeft Q_A e.hom ≫ signedCounit =
                iteratedComparison ≫ Functor.whiskerRight ordinaryInterchange.hom Q_C →
                  e = signedComparison) ∧
            baseChangeComparison = doubleBaseChange ≪≫ AC.changeOfRings := by
  intro Q_A Q_B Q_C W_A PN LK AN AP BK BL AC AL AK CP iterated together signed
  have := PN.quasiIso
  have := LK.quasiIso
  have hN : IsIso (AP.map AN PN.π) := isIso_map_of_quasiIso AP AN PN.π
  have hK : IsIso (BL.map BK LK.π) := isIso_map_of_quasiIso BL BK LK.π
  have hAK : IsIso (AL.map AK LK.π) := isIso_map_of_quasiIso AL AK LK.π
  refine ⟨asIso (AP.map AN PN.π), asIso (BL.map BK LK.π), asIso (AL.map AK LK.π),
    rfl, rfl, rfl, ?_⟩
  have hQπ : IsIso (Q_B.map PN.π) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; infer_instance
  have := BL.isIso_alphaF PN.complex PN.kFlat
  have := KFlatDerived.isIso_extensionCounit_app_of_kFlat g BK.B BK.alphaB
    PN.complex PN.kFlat
  let a := BL.F.map (Q_B.map PN.π) ≫ (asIso (BL.map BK LK.π)).hom.app (Q_B.obj N)
  refine ⟨(asIso a).symm ≪≫ asIso (BL.alphaF.app PN.complex),
    (asIso (BK.B.map (Q_B.map PN.π))).symm ≪≫ asIso (BK.alphaB.app PN.complex), ?_, ?_, ?_⟩
  · simp [a]
  · simp
  refine ⟨ordinaryAssociatorIso.{uA, uB, uC, v} AP BL AC,
    ordinaryInterchangeIso.{uA, uB, uC, v} AP BL AL CP,
    ordinaryAssociatorIso_hom_element.{uA, uB, uC, v} AP BL AC,
    ordinaryInterchangeIso_hom_element.{uA, uB, uC, v} AP BL AL CP, ?_⟩
  intro replaceIterated replaceSigned direct iteratedComparison togetherComparison signedCounit
  have hT : together.IsLeftDerivedFunctor togetherComparison W_A :=
    isLeftDerivedFunctor_comp_iso Q_A W_A AC.F AC.alphaF
      (Functor.isoWhiskerRight (ordinaryAssociatorIso.{uA, uB, uC, v} AP BL AC).symm Q_C)
  have hTiso : ∀ M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ,
      CochainComplex.KFlat.{uA, max v uB uC} M → IsIso (togetherComparison.app M) := by
    intro M hM
    have := AC.isIso_alphaF M hM
    simp only [togetherComparison, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have hIiso : ∀ M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ,
      CochainComplex.KFlat.{uA, max v uB uC} M → IsIso (iteratedComparison.app M) := by
    intro M hM
    have := AP.isIso_alphaF M hM
    have := BL.isIso_alphaF (AP.directTensor.obj M)
      (kFlat_directTensor_obj.{uA, uB, max v uA uB uC} AP PN.kFlat M hM)
    have := isIso_compositeCounit_app.{uA, uB, uC, v} AP BL M
    simp only [iteratedComparison, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have hI : iterated.IsLeftDerivedFunctor iteratedComparison W_A :=
    isLeftDerivedFunctor_of_isIso_app_kFlat.{uA, max v uB uC} _ together iterated
      togetherComparison iteratedComparison hTiso hIiso
  refine ⟨hI, hT, ?_⟩
  let interchange :=
    Functor.isoWhiskerRight (ordinaryInterchangeIso.{uA, uB, uC, v} AP BL AL CP) Q_C
  have hI' : iterated.IsLeftDerivedFunctor (iteratedComparison ≫ interchange.hom) W_A :=
    isLeftDerivedFunctor_comp_iso Q_A W_A iterated iteratedComparison interchange
  have hSiso : ∀ M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ,
      CochainComplex.KFlat.{uA, max v uB uC} M → IsIso (signedCounit.app M) := by
    intro M hM
    have := AL.isIso_alphaF M hM
    have := CP.isIso_alphaF (AL.directTensor.obj M)
      (kFlat_directTensor_obj.{uA, uC, max v uA uB uC} AL LK.kFlat M hM)
    have := isIso_compositeCounit_app.{uA, uC, uC, max v uB} AL CP M
    simp only [signedCounit, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have hIiso' : ∀ M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ,
      CochainComplex.KFlat.{uA, max v uB uC} M →
        IsIso ((iteratedComparison ≫ interchange.hom).app M) := by
    intro M hM
    have := hIiso M hM
    rw [NatTrans.comp_app]
    infer_instance
  have hS : signed.IsLeftDerivedFunctor signedCounit W_A :=
    isLeftDerivedFunctor_of_isIso_app_kFlat.{uA, max v uB uC} _ iterated signed
      _ signedCounit hIiso' hSiso
  obtain ⟨d, hd, hdu⟩ := existsUnique_leftDerivedNatIso Q_A W_A iterated together
    iteratedComparison togetherComparison (Iso.refl direct)
  obtain ⟨s, hs, hsu⟩ := existsUnique_leftDerivedNatIso Q_A W_A iterated signed
    (iteratedComparison ≫ interchange.hom) signedCounit (Iso.refl _)
  simp only [Iso.refl_hom, Category.comp_id] at hd hdu hs hsu
  exact ⟨d, s, d ≪≫ AC.changeOfRings, hd, hdu, hs, hsu, rfl⟩

/-- The associativity isomorphism `(- ⊗ᴸ_A N) ⋙ (- ⊗ᴸ_B K) ≅ - ⊗ᴸ_A (N ⊗ᴸ_B K)` of
`CochainComplex.DerivedTensor.IteratedChangeOfRings.derivedTensorProduct_doubleBaseChange`,
built rather than quantified over.

It is the same isomorphism: both are `CategoryTheory.Functor.leftDerivedNatIso` at the iterated
and at the composed comparison, and that theorem pins its `doubleBaseChange` uniquely by the very
equation `CategoryTheory.Functor.leftDerivedNatTrans_fac` supplies here. The witnesses it
quantifies over are all constructions: the two K-flat replacements are `asIso` of the maps
induced by the chosen K-flat resolutions, and the ordinary associator is
`CochainComplex.DerivedTensor.IteratedChangeOfRings.ordinaryAssociatorIso`. -/
@[no_expose]
public def doubleBaseChangeIso
    {A : Type uA} {B : Type uB} {C : Type uC} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (N : CochainComplex (ModuleCat.{max v uA uB uC} B) ℤ)
    (K : CochainComplex (ModuleCat.{max v uA uB uC} C) ℤ) :
    (canonicalDerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N).F ⋙
        (canonicalDerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K).F ≅
      (canonicalDerivedTensorChangeOfRings.{uA, uC, max v uA uB uC} (g.comp f)
        ((canonicalDerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g
            (CochainComplex.KFlat.chosenResolution.{uC, max v uA uB} K).complex).directTensor.obj
          (CochainComplex.KFlat.chosenResolution.{uB, max v uA uC} N).complex)).F := by
  let PN := CochainComplex.KFlat.chosenResolution.{uB, max v uA uC} N
  let LK := CochainComplex.KFlat.chosenResolution.{uC, max v uA uB} K
  let AN := canonicalDerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f N
  let BK := canonicalDerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g K
  let BL := canonicalDerivedTensorChangeOfRings.{uB, uC, max v uA uB uC} g LK.complex
  let AC := canonicalDerivedTensorChangeOfRings.{uA, uC, max v uA uB uC}
    (g.comp f) (BL.directTensor.obj PN.complex)
  change AN.F ⋙ BK.F ≅ AC.F
  let Q_A := DerivedCategory.Q (C := ModuleCat.{max v uA uB uC} A)
  let Q_C := DerivedCategory.Q (C := ModuleCat.{max v uA uB uC} C)
  let W_A := HomologicalComplex.quasiIso (ModuleCat.{max v uA uB uC} A) (ComplexShape.up ℤ)
  let AP := canonicalDerivedTensorChangeOfRings.{uA, uB, max v uA uB uC} f PN.complex
  have := PN.quasiIso
  have := LK.quasiIso
  have hN : IsIso (AP.map AN PN.π) := isIso_map_of_quasiIso AP AN PN.π
  have hK : IsIso (BL.map BK LK.π) := isIso_map_of_quasiIso BL BK LK.π
  let iterated := AN.F ⋙ BK.F
  let together := AC.F
  let replaceIterated := Functor.isoWhiskerRight (asIso (AP.map AN PN.π)) BL.F ≪≫
    Functor.isoWhiskerLeft AN.F (asIso (BL.map BK LK.π))
  let direct := (AP.directTensor ⋙ BL.directTensor) ⋙ Q_C
  let iteratedComparison : Q_A ⋙ iterated ⟶ direct :=
    Functor.whiskerLeft Q_A replaceIterated.inv ≫ compositeCounit.{uA, uB, uC, v} AP BL
  let togetherComparison : Q_A ⋙ together ⟶ direct :=
    AC.alphaF ≫ Functor.whiskerRight (ordinaryAssociatorIso.{uA, uB, uC, v} AP BL AC).inv Q_C
  have hT : together.IsLeftDerivedFunctor togetherComparison W_A :=
    isLeftDerivedFunctor_comp_iso Q_A W_A AC.F AC.alphaF
      (Functor.isoWhiskerRight (ordinaryAssociatorIso.{uA, uB, uC, v} AP BL AC).symm Q_C)
  have hTiso : ∀ M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ,
      CochainComplex.KFlat.{uA, max v uB uC} M → IsIso (togetherComparison.app M) := by
    intro M hM
    have := AC.isIso_alphaF M hM
    simp only [togetherComparison, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  have hIiso : ∀ M : CochainComplex (ModuleCat.{max v uA uB uC} A) ℤ,
      CochainComplex.KFlat.{uA, max v uB uC} M → IsIso (iteratedComparison.app M) := by
    intro M hM
    have := AP.isIso_alphaF M hM
    have := BL.isIso_alphaF (AP.directTensor.obj M)
      (kFlat_directTensor_obj.{uA, uB, max v uA uB uC} AP PN.kFlat M hM)
    have := isIso_compositeCounit_app.{uA, uB, uC, v} AP BL M
    simp only [iteratedComparison, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  have hI : iterated.IsLeftDerivedFunctor iteratedComparison W_A :=
    isLeftDerivedFunctor_of_isIso_app_kFlat.{uA, max v uB uC} _ together iterated
      togetherComparison iteratedComparison hTiso hIiso
  exact Functor.leftDerivedNatIso iterated together iteratedComparison togetherComparison W_A
    (Iso.refl direct)

end CochainComplex.DerivedTensor.IteratedChangeOfRings

end
