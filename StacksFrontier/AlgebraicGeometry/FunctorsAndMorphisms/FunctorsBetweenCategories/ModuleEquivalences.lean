module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Center.Localization
public import Mathlib.RingTheory.PicardGroup
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.LinearTensorEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Equivalences between categories of modules

An equivalence between the categories of modules over two commutative rings is extension of
scalars along an isomorphism of the rings, followed by tensoring with an invertible module.

## Main definitions

* `ModuleCat.extensionTensorFunctor` is extension of scalars along a ring isomorphism followed
  by tensoring with a fixed module.

## Main results

* `ModuleCat.exists_ringEquiv_invertible_iso_extensionTensorFunctor` describes every equivalence
  between categories of modules in this form.

## Implementation notes

The isomorphism of rings is a `RingEquiv`, invertibility of the module is Mathlib's
`Module.Invertible`, and isomorphism of functors is a nonempty natural isomorphism. Mathlib's
extension-of-scalars functor uses `B ⊗[A] M`; symmetry of the tensor product identifies this
canonically with the `M ⊗[A] B` of the source.

The ring isomorphism is produced from the centre of the category: for a commutative ring `R`
the canonical map from `R` to the centre of `ModuleCat R` is bijective, and an additive
equivalence of categories induces an isomorphism of centres. Linearity of the equivalence over
the resulting `A`-algebra structure on `B` then puts it in the range of
`ModuleCat.moduleTensorFunctor`, and the bimodule that appears is invertible because tensoring
with it is an equivalence.

## References

* [Stacks Project, Tag 0GP0](https://stacks.math.columbia.edu/tag/0GP0)
-/

@[expose] public section

namespace ModuleCat

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra ChangeOfRings TensorProduct

/-- Extension of scalars along a ring isomorphism, followed by tensoring with a module over the
target ring. -/
public noncomputable def extensionTensorFunctor
    (A B : Type u) [CommRing A] [CommRing B] (e : A ≃+* B) (L : ModuleCat.{u} B) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} B :=
  ModuleCat.extendScalars e.toRingHom ⋙
    (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L

private theorem exists_tensor_representation
    (A B : Type u) [CommRing A] [CommRing B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence] :
    ∃ K : ModuleCat.{u} (A ⊗[ℤ] B),
      Nonempty (tensorFunctorOverInt A B K ≅ F) := by
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let : F.Linear ℤ := inferInstance
  have hfinite : PreservesFiniteColimits F := inferInstance
  have hcoprod : ∀ J : Type u, PreservesColimitsOfShape (Discrete J) F := fun _ => inferInstance
  have h :=
    (tfae_iso_tensorFunctor_preserves_colimits_isLeftAdjoint A B F).out 2 1
  rcases h.mp ⟨hfinite, hcoprod⟩ with ⟨K, hK⟩
  exact ⟨K, hK⟩

private def centerEval (R : Type u) [CommRing R]
    (z : CategoryTheory.CatCenter (ModuleCat.{u} R)) : R :=
  (z.app (ModuleCat.of R R)).hom (1 : R)

private theorem center_apply (R : Type u) [CommRing R]
    (z : CategoryTheory.CatCenter (ModuleCat.{u} R))
    (M : ModuleCat.{u} R) (x : M) :
    (z.app M).hom x = centerEval R z • x := by
  let f : ModuleCat.of R R ⟶ M :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)
  have h := congrArg (fun g : ModuleCat.of R R ⟶ M => g.hom (1 : R))
    (CategoryTheory.CatCenter.naturality z f)
  simpa [centerEval, f, LinearMap.toSpanSingleton_apply, ModuleCat.hom_comp] using h

/-- The canonical ring morphism `R →+* CatCenter (ModuleCat R)` is bijective, for `R` a
commutative ring. -/
public theorem center_toCatCenter_bijective (R : Type u) [CommRing R] :
    Function.Bijective (CategoryTheory.Linear.toCatCenter R (ModuleCat.{u} R)) := by
  constructor
  · intro a b h
    simpa [centerEval, CategoryTheory.Linear.toCatCenter_apply_asHom_app,
      CategoryTheory.CatCenter.app] using
      congrArg (centerEval R) h
  · intro z
    refine ⟨centerEval R z, ?_⟩
    apply CategoryTheory.CatCenter.ext
    intro M
    apply ModuleCat.hom_ext
    ext x
    simp [CategoryTheory.Linear.toCatCenter_apply_asHom_app, CategoryTheory.CatCenter.app,
      center_apply]

/-- **The centre of `ModuleCat R` is `R`**, for `R` a commutative ring: the canonical ring
morphism `R →+* CatCenter (ModuleCat R)`, which sends `r` to the natural endomorphism
`r • 𝟙 (-)` of the identity functor, is bijective. -/
public noncomputable def centerRingEquiv (R : Type u) [CommRing R] :
    R ≃+* CategoryTheory.CatCenter (ModuleCat.{u} R) :=
  RingEquiv.ofBijective (CategoryTheory.Linear.toCatCenter R (ModuleCat.{u} R))
    (center_toCatCenter_bijective R)

private theorem centerLoc_bijective {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (W : MorphismProperty C) [F.IsLocalization W] [F.Full] [F.Faithful] :
    Function.Bijective (CategoryTheory.CatCenter.localizationRingHom F W) := by
  let FF := Functor.FullyFaithful.ofFullyFaithful F
  constructor
  · intro a b h
    apply CategoryTheory.CatCenter.ext
    intro X
    apply F.map_injective
    simpa [CategoryTheory.CatCenter.localizationRingHom,
      CategoryTheory.CatCenter.localization_app] using
      congrArg (fun z : CategoryTheory.CatCenter D => z.app (F.obj X)) h
  · intro b
    let α : CategoryTheory.CatCenter C := .of {
      app := fun X => FF.preimage (b.app (F.obj X))
      naturality := by
        intro X Y f
        apply F.map_injective
        simp only [Functor.map_comp, FF.map_preimage]
        exact b.naturality (F.map f)
    }
    refine ⟨α, ?_⟩
    apply CategoryTheory.CatCenter.ext_of_localization F W
    intro X
    simp [α, CategoryTheory.CatCenter.localization_app,
      CategoryTheory.CatCenter.localizationRingHom, FF.map_preimage]

private noncomputable def centerLocEquiv {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (W : MorphismProperty C) [F.IsLocalization W] [F.Full] [F.Faithful] :
    CategoryTheory.CatCenter C ≃+* CategoryTheory.CatCenter D :=
  RingEquiv.ofBijective (CategoryTheory.CatCenter.localizationRingHom F W)
    (centerLoc_bijective F W)

private noncomputable def centerEquivOfEquivalence {C D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] [F.IsEquivalence] :
    CategoryTheory.CatCenter C ≃+* CategoryTheory.CatCenter D := by
  let W := MorphismProperty.isomorphisms C
  letI : F.IsLocalization W := Functor.IsLocalization.of_isEquivalence F W le_rfl
  exact centerLocEquiv F W

/-- **The canonical ring isomorphism attached to an equivalence of module categories.**  An
additive equivalence `F : ModuleCat A ⥤ ModuleCat B` between the categories of modules over two
commutative rings induces an isomorphism of the centres of those categories, and the centre of
`ModuleCat R` is canonically `R` (`ModuleCat.centerRingEquiv`); composing gives a ring
isomorphism `A ≃+* B` that depends on nothing but `F`.

This is the ring isomorphism produced by
`ModuleCat.exists_ringEquiv_invertible_iso_extensionTensorFunctor` (Tag 0GP0).  It is
characterised by `ModuleCat.map_regular_scalar`, hence depends on `F` only through its
isomorphism class (`ModuleCat.ringEquivOfEquivalence_congr`), and it inverts
`ModuleCat.extensionTensorFunctor` (`ModuleCat.ringEquivOfEquivalence_extensionTensorFunctor`). -/
@[no_expose]
public noncomputable def ringEquivOfEquivalence
    (A B : Type u) [CommRing A] [CommRing B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence] [F.Additive] :
    A ≃+* B :=
  (centerRingEquiv A).trans <|
    (centerEquivOfEquivalence F).trans (centerRingEquiv B).symm

/-- **`ModuleCat.ringEquivOfEquivalence` transports the central scalars along `F`.**  The
natural endomorphism `a • 𝟙 (-)` of the identity functor of `ModuleCat A` is carried by `F` to
the natural endomorphism `ringEquivOfEquivalence A B F a • 𝟙 (-)` of the identity functor of
`ModuleCat B`, read at the objects in the image of `F`. -/
public theorem map_regular_scalar
    (A B : Type u) [CommRing A] [CommRing B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence] [F.Additive]
    (a : A) (X : ModuleCat.{u} A) :
    F.map ((centerRingEquiv A a).app X) =
      (centerRingEquiv B (ringEquivOfEquivalence A B F a)).app (F.obj X) := by
  let W := MorphismProperty.isomorphisms (ModuleCat.{u} A)
  let : F.IsLocalization W := Functor.IsLocalization.of_isEquivalence F W le_rfl
  simp [ringEquivOfEquivalence, centerEquivOfEquivalence, centerLocEquiv,
    CategoryTheory.CatCenter.localizationRingHom, CategoryTheory.CatCenter.localization_app]

private theorem exists_relative_tensor_representation
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence] [F.Linear R] :
    ∃ K : ModuleCat.{u} (A ⊗[R] B),
      Nonempty ((moduleTensorFunctor R A B).obj K ≅ F) := by
  let P := IsLinearRightExactAndPreservesDirectSums R A B
  let E := tensorFunctorEquivalence R A B
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let X : P.FullSubcategory := ⟨F, ⟨inferInstance, inferInstance, fun _ => inferInstance⟩⟩
  obtain ⟨K, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage E.functor X
  obtain ⟨i'⟩ := tensorFunctorEquivalence_functorIso R A B
  exact ⟨K, ⟨P.ι.mapIso ((i'.app K).symm ≪≫ i :
    (moduleTensorFunctorLift R A B).obj K ≅ X)⟩⟩

/-- The central element `r` acts on a morphism of `ModuleCat R` by scalar multiplication. -/
private theorem centerRingEquiv_app_comp (R : Type u) [CommRing R] (r : R)
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) : (centerRingEquiv R r).app X ≫ f = r • f := by
  have hs : (centerRingEquiv R r).app X = r • (𝟙 X) := by
    change (CategoryTheory.Linear.toCatCenter R (ModuleCat.{u} R) r).app X = _
    simp [CategoryTheory.Linear.toCatCenter_apply_asHom_app, CategoryTheory.CatCenter.app]
  simp [hs]

private theorem functor_linear_of_centers
    (A B : Type u) [CommRing A] [CommRing B]
    (e : A ≃+* B) (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence]
    [F.Additive]
    (h : ∀ a X, F.map ((centerRingEquiv A a).app X) =
      (centerRingEquiv B (e a)).app (F.obj X)) :
    letI : Algebra A B := e.toRingHom.toAlgebra
    F.Linear A := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let : CategoryTheory.Linear A (ModuleCat.{u} B) := ModuleCat.Algebra.instLinear
  constructor
  intro X Y f a
  rw [← centerRingEquiv_app_comp A a f, Functor.map_comp, h]
  exact centerRingEquiv_app_comp B (e a) (F.map f)

private theorem inverse_linear
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence]
    (h : F.Linear A) : F.asEquivalence.inverse.Linear A := by
  let : F.asEquivalence.functor.Linear A := by
    dsimp [Functor.asEquivalence]
    exact h
  exact F.asEquivalence.inverseLinear A

private theorem invertible_of_tensoringRight_equivalence
    (B : Type u) [CommRing B] (L : ModuleCat.{u} B)
    (T : ModuleCat.{u} B ⥤ ModuleCat.{u} B) [T.IsEquivalence]
    (hT : Nonempty
      (T ≅ (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L)) :
    Module.Invertible B L := by
  let N := T.asEquivalence.inverse.obj (ModuleCat.of B B)
  obtain ⟨α⟩ := hT
  let j : ModuleCat.of B (N ⊗[B] L) ≅ ModuleCat.of B B :=
    (α.app N).symm ≪≫ T.asEquivalence.counitIso.app (ModuleCat.of B B)
  exact Module.Invertible.right j.toLinearEquiv

/-- The algebra map `A ⊗[A] B →ₐ[A] B` induced by the identity has underlying map `lid`. -/
private theorem liftEquiv_id_toLinearMap
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (AlgHom.liftEquiv A A B B (AlgHom.id A B)).toLinearMap = TensorProduct.lid A B := by
  ext a
  simp

private noncomputable def regularAlgEquiv
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (A ⊗[A] B) ≃ₐ[A] B := by
  let q : A ⊗[A] B →ₐ[A] B := AlgHom.liftEquiv A A B B (AlgHom.id A B)
  refine AlgEquiv.ofBijective q ?_
  change Function.Bijective q.toLinearMap
  rw [liftEquiv_id_toLinearMap]
  exact (TensorProduct.lid A B).bijective

private instance regularAlgEquiv_invPair
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    RingHomInvPair (regularAlgEquiv A B).toRingEquiv.toRingHom
      (regularAlgEquiv A B).toRingEquiv.symm.toRingHom :=
  ⟨(regularAlgEquiv A B).toRingEquiv.symm_toRingHom_comp_toRingHom,
    (regularAlgEquiv A B).toRingEquiv.toRingHom_comp_symm_toRingHom⟩

private instance regularAlgEquiv_invPair_symm
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    RingHomInvPair (regularAlgEquiv A B).toRingEquiv.symm.toRingHom
      (regularAlgEquiv A B).toRingEquiv.toRingHom :=
  ⟨(regularAlgEquiv A B).toRingEquiv.toRingHom_comp_symm_toRingHom,
    (regularAlgEquiv A B).toRingEquiv.symm_toRingHom_comp_toRingHom⟩

private theorem regularAlgEquiv_apply
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (a : A ⊗[A] B) :
    regularAlgEquiv A B a = TensorProduct.lid A B a := by
  exact LinearMap.congr_fun (liftEquiv_id_toLinearMap A B) a

private theorem regularAlgEquiv_left
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    (regularAlgEquiv A B).toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)) =
        algebraMap A B := by
  ext a
  change regularAlgEquiv A B (algebraMap A (A ⊗[A] B) a) = algebraMap A B a
  exact (regularAlgEquiv A B).commutes a

/-- The regular `A ⊗[A] B`-module and the regular `B`-module, both restricted to `A`, identified
along `q`. This is the coefficient isomorphism that the two scalar-extension comparisons below
are built from. -/
private noncomputable def extendScalarsRegularIso
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (q : (A ⊗[A] B) ≃ₐ[A] B)
    [RingHomInvPair q.toRingEquiv.toRingHom q.toRingEquiv.symm.toRingHom]
    [RingHomInvPair q.toRingEquiv.symm.toRingHom q.toRingEquiv.toRingHom]
    (hleft : q.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)) =
        algebraMap A B)
    :
    (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).obj
          (ModuleCat.of (A ⊗[A] B) (A ⊗[A] B)) ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) :=
  (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).mapIso
    (ModuleCat.restrictScalarsIsoOfEquiv q.toRingEquiv).symm ≪≫
  (ModuleCat.restrictScalarsComp'App
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))
      q.toRingEquiv.toRingHom
      (q.toRingEquiv.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))) rfl
      (ModuleCat.of B B)).symm ≪≫
  (ModuleCat.restrictScalarsCongr hleft).app (ModuleCat.of B B)

/-- On elements the coefficient isomorphism is `q` itself. -/
private theorem extendScalarsRegularIso_apply
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (q : (A ⊗[A] B) ≃ₐ[A] B)
    [RingHomInvPair q.toRingEquiv.toRingHom q.toRingEquiv.symm.toRingHom]
    [RingHomInvPair q.toRingEquiv.symm.toRingHom q.toRingEquiv.toRingHom]
    (hleft : q.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)) =
        algebraMap A B)
    (x : (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).obj
        (ModuleCat.of (A ⊗[A] B) (A ⊗[A] B))) :
    (extendScalarsRegularIso A B q hleft).hom x = q.toRingEquiv.toRingHom x := by
  change (ModuleCat.restrictScalarsIsoOfEquiv q.toRingEquiv).inv x = _
  exact ModuleCat.restrictScalarsIsoOfEquiv_inv_apply q.toRingEquiv x

private noncomputable def extendScalarsTensorLinearEquiv
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (q : (A ⊗[A] B) ≃ₐ[A] B)
    [RingHomInvPair q.toRingEquiv.toRingHom q.toRingEquiv.symm.toRingHom]
    [RingHomInvPair q.toRingEquiv.symm.toRingHom q.toRingEquiv.toRingHom]
    (hleft : q.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)) =
        algebraMap A B)
    (M : ModuleCat.{u} A) :
    ((ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).obj M) ≃ₗ[A]
      ((ModuleCat.extendScalars (algebraMap A B)).obj M) := by
  let iL := Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)
  let X := ModuleCat.ExtendScalars.obj' iL M
  let Y := ModuleCat.ExtendScalars.obj' (algebraMap A B) M
  letI : Module A (↑X) := Module.compHom X iL
  letI : Module A (↑Y) := Module.compHom Y (algebraMap A B)
  exact TensorProduct.congr (extendScalarsRegularIso A B q hleft).toLinearEquiv
    (LinearEquiv.refl A M)

private theorem extendScalarsTensorLinearEquiv_tmul
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (q : (A ⊗[A] B) ≃ₐ[A] B)
    [RingHomInvPair q.toRingEquiv.toRingHom q.toRingEquiv.symm.toRingHom]
    [RingHomInvPair q.toRingEquiv.symm.toRingHom q.toRingEquiv.toRingHom]
    (hleft : q.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)) =
        algebraMap A B)
    (M : ModuleCat.{u} A)
    (t : (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).obj
        (ModuleCat.of (A ⊗[A] B) (A ⊗[A] B))) (m : M) :
    extendScalarsTensorLinearEquiv A B q hleft M (t ⊗ₜ[A] m) =
      q.toRingEquiv.toRingHom t ⊗ₜ[A, algebraMap A B] m := by
  change (TensorProduct.congr (extendScalarsRegularIso A B q hleft).toLinearEquiv
    (LinearEquiv.refl A M)) (t ⊗ₜ[A] m) = _
  have ht : (extendScalarsRegularIso A B q hleft).toLinearEquiv t =
      q.toRingEquiv.toRingHom t := by
    simpa using extendScalarsRegularIso_apply A B q hleft t
  rw [TensorProduct.congr_tmul, ht]
  rfl

private noncomputable def extendScalarsTensorEquiv
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (q : (A ⊗[A] B) ≃ₐ[A] B)
    [RingHomInvPair q.toRingEquiv.toRingHom q.toRingEquiv.symm.toRingHom]
    [RingHomInvPair q.toRingEquiv.symm.toRingHom q.toRingEquiv.toRingHom]
    (hleft : q.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)) =
        algebraMap A B)
    (M : ModuleCat.{u} A) :
    ((ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).obj M) ≃ₛₗ[
        q.toRingEquiv.toRingHom]
      ((ModuleCat.extendScalars (algebraMap A B)).obj M) := by
  let a := extendScalarsTensorLinearEquiv A B q hleft M
  refine { toEquiv := a.toEquiv, map_add' := a.map_add, map_smul' := ?_ }
  intro s x
  -- Name the two module structures the goal uses: typeclass search cannot rediscover them on
  -- the unfolded carriers, so without these every `•` written below is stuck.
  let : Module (A ⊗[A] B) (↑((ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).obj
        (ModuleCat.of (A ⊗[A] B) (A ⊗[A] B))) ⊗[A] ↑M) :=
    ((ModuleCat.extendScalars (Algebra.TensorProduct.includeLeftRingHom
      (R := A) (A := A) (B := B))).obj M).isModule
  let : Module B (↑((ModuleCat.restrictScalars (algebraMap A B)).obj
      (ModuleCat.of B B)) ⊗[A] ↑M) :=
    ((ModuleCat.extendScalars (algebraMap A B)).obj M).isModule
  change a (s • x) = _
  -- Each step is applied as a term rather than by `rw`/`simp`: the two sides live over
  -- different coefficient rings, so the semilinear `•` on the target carries an instance those
  -- tactics cannot match against the one in the pure tensors.
  induction x using TensorProduct.inductionOn with
  | tmul t m =>
      refine (congrArg a
        (ModuleCat.ExtendScalars.smul_tmul _ s t m)).trans ?_
      refine (extendScalarsTensorLinearEquiv_tmul A B q hleft M _ m).trans ?_
      refine (congrArg (fun z => z ⊗ₜ[A, algebraMap A B] m)
        (map_mul q.toRingEquiv.toRingHom s t)).trans ?_
      refine (ModuleCat.ExtendScalars.smul_tmul (algebraMap A B)
        (q.toRingEquiv.toRingHom s) (q.toRingEquiv.toRingHom t) m).symm.trans ?_
      exact congrArg (fun z : ↑((ModuleCat.extendScalars (algebraMap A B)).obj M) =>
          q.toRingEquiv.toRingHom s • z)
        (extendScalarsTensorLinearEquiv_tmul A B q hleft M t m).symm
  | add x y hx hy =>
      refine (congrArg a (smul_add s x y)).trans ?_
      refine (map_add a _ _).trans ?_
      refine (congrArg₂ (· + ·) hx hy).trans ?_
      refine (smul_add (q.toRingEquiv.toRingHom s) _ _).symm.trans ?_
      exact congrArg (fun z => q.toRingEquiv.toRingHom s • z) (map_add a x y).symm

private theorem extendScalarsTensorEquiv_natural
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (q : (A ⊗[A] B) ≃ₐ[A] B)
    [RingHomInvPair q.toRingEquiv.toRingHom q.toRingEquiv.symm.toRingHom]
    [RingHomInvPair q.toRingEquiv.symm.toRingHom q.toRingEquiv.toRingHom]
    (hleft : q.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)) =
        algebraMap A B)
    {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (x : (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).obj M) :
    extendScalarsTensorEquiv A B q hleft N
        ((ModuleCat.extendScalars
          (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).map f x) =
      (ModuleCat.extendScalars (algebraMap A B)).map f
        (extendScalarsTensorEquiv A B q hleft M x) := by
  change (extendScalarsTensorLinearEquiv A B q hleft N)
      ((ModuleCat.extendScalars
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).map f x) =
    (ModuleCat.extendScalars (algebraMap A B)).map f
      ((extendScalarsTensorLinearEquiv A B q hleft M) x)
  let FL := ((ModuleCat.extendScalars
    (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).map f).hom
  let FR := ((ModuleCat.extendScalars (algebraMap A B)).map f).hom
  let eM := extendScalarsTensorLinearEquiv A B q hleft M
  let eN := extendScalarsTensorLinearEquiv A B q hleft N
  -- `rw` cannot rewrite with `ExtendScalars.map_tmul` here: the `Module A (A ⊗[A] B)` instance
  -- in the goal comes from `ModuleCat.restrictScalars` rather than from instance search. Each
  -- step is therefore applied as a term.
  induction x using TensorProduct.inductionOn with
  | tmul t m =>
      refine (congrArg eN (ModuleCat.ExtendScalars.map_tmul
        (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))
        f t m)).trans ?_
      refine (extendScalarsTensorLinearEquiv_tmul A B q hleft N t (f m)).trans ?_
      refine (ModuleCat.ExtendScalars.map_tmul (algebraMap A B) f
        (q.toRingEquiv.toRingHom t) m).symm.trans ?_
      exact congrArg FR
        (extendScalarsTensorLinearEquiv_tmul A B q hleft M t m).symm
  | add x y hx hy =>
      refine (congrArg eN (map_add FL x y)).trans ?_
      refine (map_add eN _ _).trans ?_
      refine (congrArg₂ (· + ·) hx hy).trans ?_
      refine (map_add FR _ _).symm.trans ?_
      exact congrArg FR (map_add eM x y).symm

private noncomputable def restrictSemilinear
    {S B : Type u} [CommRing S] [CommRing B]
    (q : S ≃+* B) [RingHomInvPair q.toRingHom q.symm.toRingHom]
    [RingHomInvPair q.symm.toRingHom q.toRingHom]
    (K : ModuleCat S) : K ≃ₛₗ[q.toRingHom]
      (ModuleCat.restrictScalars q.symm.toRingHom).obj K := {
  toEquiv := Equiv.refl K
  map_add' _ _ := rfl
  map_smul' := by
    intro s x
    change s • x = q.symm.toRingHom (q.toRingHom s) • x
    have hs : q.symm.toRingHom (q.toRingHom s) = s :=
      DFunLike.congr_fun q.symm_toRingHom_comp_toRingHom s
    rw [hs] }

private noncomputable def transportTensor
    {S B : Type u} [CommRing S] [CommRing B]
    (q : S ≃+* B) [RingHomInvPair q.toRingHom q.symm.toRingHom]
    [RingHomInvPair q.symm.toRingHom q.toRingHom]
    {X : ModuleCat S} {Y : ModuleCat B}
    (f : X ≃ₛₗ[q.toRingHom] Y) (K : ModuleCat S)
    (L : ModuleCat B) (g : K ≃ₛₗ[q.toRingHom] L) :
    (ModuleCat.restrictScalars q.symm.toRingHom).obj
      (ModuleCat.of S (X ⊗[S] K)) ≃ₗ[B]
    (ModuleCat.of B (Y ⊗[B] L)) := by
  let c := TensorProduct.congr f g
  refine {
    toFun := c
    invFun := c.symm
    left_inv := c.left_inv
    right_inv := c.right_inv
    map_add' := c.map_add
    map_smul' := ?_ }
  intro b x
  change c (q.symm.toRingHom b • x) = b • c x
  let xt : (↑X) ⊗[S] (↑K) := x
  calc
    c (q.symm.toRingHom b • x) = c (q.symm.toRingHom b • xt) := rfl
    _ = q.toRingHom (q.symm.toRingHom b) • c xt := c.map_smulₛₗ _ _
    _ = b • c x := by simp [xt]

private theorem transportTensor_tmul
    {S B : Type u} [CommRing S] [CommRing B]
    (q : S ≃+* B) [RingHomInvPair q.toRingHom q.symm.toRingHom]
    [RingHomInvPair q.symm.toRingHom q.toRingHom]
    {X : ModuleCat S} {Y : ModuleCat B}
    (f : X ≃ₛₗ[q.toRingHom] Y) (K : ModuleCat S)
    (L : ModuleCat B) (g : K ≃ₛₗ[q.toRingHom] L) (x : X) (k : K) :
    transportTensor q f K L g (x ⊗ₜ[S] k) = f x ⊗ₜ[B] g k := by
  change (TensorProduct.congr f g) (x ⊗ₜ[S] k) = _
  rw [TensorProduct.congr_tmul]

private noncomputable def bridgeComponent
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{u} A) (K : ModuleCat.{u} (A ⊗[A] B)) :
    (((moduleTensorFunctor A A B).obj K).obj M) ≅
      ((ModuleCat.extendScalars (algebraMap A B) ⋙
        (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj
          ((ModuleCat.restrictScalars
            (regularAlgEquiv A B).toRingEquiv.symm.toRingHom).obj K)).obj M) := by
  let q := regularAlgEquiv A B
  let iL := Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B)
  let iR := (Algebra.TensorProduct.includeRight (R := A) (A := A) (B := B)).toRingHom
  have hright : q.toRingEquiv.symm.toRingHom = iR := by
    ext b
    apply q.toRingEquiv.injective
    calc
      q.toRingEquiv (q.toRingEquiv.symm b) = b := q.toRingEquiv.apply_symm_apply b
      _ = q.toRingEquiv (iR b) := by
        change b = regularAlgEquiv A B (iR b)
        rw [regularAlgEquiv_apply]
        simp [iR, TensorProduct.lid_tmul]
  let X := ((ModuleCat.extendScalars iL).obj M)
  let f := extendScalarsTensorEquiv A B q (regularAlgEquiv_left A B) M
  let L := (ModuleCat.restrictScalars q.toRingEquiv.symm.toRingHom).obj K
  let g := restrictSemilinear q.toRingEquiv K
  let c := transportTensor q.toRingEquiv f K L g
  let r := (ModuleCat.restrictScalarsCongr hright).app
    (ModuleCat.of (A ⊗[A] B) ((↑X) ⊗[A ⊗[A] B] (↑K)))
  exact r.symm ≪≫ c.toModuleIso

private theorem bridgeComponent_tmul
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{u} A) (K : ModuleCat.{u} (A ⊗[A] B))
    (x : (ModuleCat.extendScalars
      (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).obj M)
    (k : K) :
    (bridgeComponent A B M K).hom (x ⊗ₜ[A ⊗[A] B] k) =
      (extendScalarsTensorEquiv A B (regularAlgEquiv A B)
        (regularAlgEquiv_left A B) M x) ⊗ₜ[B]
          (restrictSemilinear (regularAlgEquiv A B).toRingEquiv K k) := by
  let q := regularAlgEquiv A B
  dsimp [bridgeComponent, moduleTensorFunctor,
    ModuleCat.restrictScalarsCongr, LinearEquiv.toModuleIso]
  exact transportTensor_tmul q.toRingEquiv
    (extendScalarsTensorEquiv A B q (regularAlgEquiv_left A B) M) K
    ((ModuleCat.restrictScalars q.toRingEquiv.symm.toRingHom).obj K)
    (restrictSemilinear q.toRingEquiv K) x k

private noncomputable def moduleTensorBridge
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (K : ModuleCat.{u} (A ⊗[A] B)) :
    (moduleTensorFunctor A A B).obj K ≅
      ModuleCat.extendScalars (algebraMap A B) ⋙
        (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj
          ((ModuleCat.restrictScalars
            (regularAlgEquiv A B).toRingEquiv.symm.toRingHom).obj K) := by
  refine NatIso.ofComponents (fun M => bridgeComponent A B M K) ?_
  intro M N f
  let q := regularAlgEquiv A B
  apply ModuleCat.hom_ext
  ext x
  -- Name the two sides as linear maps. `simp only [LinearMap.map_zero]` and
  -- `simp only [LinearMap.map_add]` make no progress on this goal, whose objects are spelled
  -- through `bridgeComponent`; applied as terms the additivity steps go through.
  let L := ModuleCat.Hom.hom (((moduleTensorFunctor A A B).obj K).map f ≫
    (bridgeComponent A B N K).hom)
  let R := ModuleCat.Hom.hom ((bridgeComponent A B M K).hom ≫
    (ModuleCat.extendScalars (algebraMap A B) ⋙
      (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj
        ((ModuleCat.restrictScalars q.toRingEquiv.symm.toRingHom).obj K)).map f)
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
      change (bridgeComponent A B N K).hom
          ((((ModuleCat.extendScalars
            (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A) (B := B))).map f) s) ⊗ₜ m) =
        (ModuleCat.extendScalars (algebraMap A B) ⋙
          (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj
            ((ModuleCat.restrictScalars q.toRingEquiv.symm.toRingHom).obj K)).map f
          ((bridgeComponent A B M K).hom (s ⊗ₜ[A ⊗[A] B] m))
      rw [bridgeComponent_tmul, bridgeComponent_tmul]
      simp only [Functor.comp_map, MonoidalCategory.tensoringRight,
        MonoidalCategory.curriedTensor]
      rw [extendScalarsTensorEquiv_natural A B q
        (regularAlgEquiv_left A B) f s]
      rfl
  | add x y hx hy =>
      exact (map_add L x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add R x y).symm)

/-- **Stacks Project, Tag 0GP0.** Every equivalence between categories of modules is extension
of scalars along an isomorphism of the rings, followed by tensoring with an invertible module. -/
@[stacks 0GP0]
public lemma exists_ringEquiv_invertible_iso_extensionTensorFunctor
    (A B : Type u) [CommRing A] [CommRing B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence] :
    ∃ (e : A ≃+* B) (L : ModuleCat.{u} B),
      Module.Invertible B L ∧ Nonempty (F ≅ extensionTensorFunctor A B e L) := by
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let e := ringEquivOfEquivalence A B F
  let : Algebra A B := e.toRingHom.toAlgebra
  let : F.Linear A := functor_linear_of_centers A B e F (map_regular_scalar A B F)
  obtain ⟨K, ⟨iF⟩⟩ := exists_relative_tensor_representation A A B F
  let L : ModuleCat.{u} B :=
    (ModuleCat.restrictScalars
      (regularAlgEquiv A B).toRingEquiv.symm.toRingHom).obj K
  have hF : F ≅ extensionTensorFunctor A B e L := by
    dsimp [extensionTensorFunctor]
    exact iF.symm ≪≫ moduleTensorBridge A B K
  let X := ModuleCat.extendScalars e.toRingHom
  have : X.IsEquivalence :=
    have := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
    (ModuleCat.extendRestrictScalarsAdj e.toRingHom).isEquivalence_left_of_isEquivalence_right
  let T := X.asEquivalence.inverse ⋙ F
  have hT : T ≅ (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L := by
    calc
      T ≅ X.asEquivalence.inverse ⋙
          (X ⋙ (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L) :=
        Functor.isoWhiskerLeft X.asEquivalence.inverse hF
      _ ≅ (X.asEquivalence.inverse ⋙ X) ⋙
          (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L :=
        (Functor.associator _ _ _).symm
      _ ≅ (𝟭 (ModuleCat.{u} B)) ⋙
          (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L :=
        Functor.isoWhiskerRight X.asEquivalence.counitIso _
      _ ≅ (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L :=
        Functor.leftUnitor _
  exact ⟨e, L, invertible_of_tensoringRight_equivalence B L T ⟨hT⟩, ⟨hF⟩⟩

end ModuleCat
