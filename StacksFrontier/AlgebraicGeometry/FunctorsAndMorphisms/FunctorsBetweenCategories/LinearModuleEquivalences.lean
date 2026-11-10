module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Monoidal.Linear
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.ModuleEquivalences
public import StacksCore.Tactic.StacksAttribute

/-!
# Linear equivalences between categories of modules

An equivalence between the categories of modules over two algebras over a commutative ring, if
it is linear over the base ring, comes from an isomorphism of algebras followed by tensoring
with an invertible module.

## Main results

* `ModuleCat.exists_algEquiv_invertible_iso_extensionTensorFunctor` describes a base-linear
  equivalence of module categories by extension of scalars along an algebra isomorphism and
  tensoring with an invertible module.

## References

* [Stacks Project, Tag 0GP1](https://stacks.math.columbia.edu/tag/0GP1)
-/

@[expose] public section

namespace ModuleCat

open CategoryTheory
open scoped ModuleCat.Algebra ChangeOfRings

universe u v

private lemma moduleCat_smul_eq_algebra_smul
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat S) (f : M ⟶ M) (r : R) :
    r • f = (algebraMap R S r) • f := by
  ext x; simp [Algebra.smul_def]

private theorem tensorRight_map_injective
    {B : Type u} [CommRing B] (L : ModuleCat.{u} B) [Module.Invertible B L]
    {X Y : ModuleCat.{u} B} :
    Function.Injective
      (((MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L).map : (X ⟶ Y) → _) := by
  intro f g h; apply ModuleCat.hom_ext
  let e : TensorProduct B L (Module.Dual B L) ≃ₗ[B] B :=
    TensorProduct.comm B L (Module.Dual B L) ≪≫ₗ Module.Invertible.linearEquiv B L
  have hh := congrArg (fun t => t.hom) h
  change f.hom.rTensor L = g.hom.rTensor L at hh
  apply (Module.Invertible.rTensorEquiv X Y e).injective
  change (LinearMap.rTensorHom L) f.hom = (LinearMap.rTensorHom L) g.hom
  simpa only [← LinearMap.coe_rTensorHom] using hh

private theorem ringEquiv_apply_eq_of_extensionScalars_map
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) (a : A) (b : B)
    (h : (ModuleCat.extendScalars e.toRingHom).map
      (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) a)) =
      b • 𝟙 ((ModuleCat.extendScalars e.toRingHom).obj (ModuleCat.of A A))) :
    e a = b := by
  let : Algebra A B := e.toRingHom.toAlgebra
  let E := (ModuleCat.extendScalars e.toRingHom).obj (ModuleCat.of A A)
  let v : E := (1 : B) ⊗ₜ[A,e.toRingHom] (1 : A)
  let φ : TensorProduct A B A ≃ₗ[A] B :=
    TensorProduct.comm A B A ≪≫ₗ TensorProduct.lid A B
  have hevalL : ((ModuleCat.extendScalars e.toRingHom).map
      (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) a))).hom v =
      (1 : B) ⊗ₜ[A,e.toRingHom] a := by
    change ((ModuleCat.extendScalars e.toRingHom).map
      (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) a)))
        ((1 : B) ⊗ₜ[A,e.toRingHom] (1 : A)) = _
    rw [ModuleCat.ExtendScalars.map_tmul]
    change (1 : B) ⊗ₜ[A,e.toRingHom]
      ((LinearMap.lsmul A (ModuleCat.of A A) a) 1) = _
    simp [LinearMap.lsmul_apply]
  have hevalR : (b • (𝟙 E)).hom v = b • ((1 : B) ⊗ₜ[A,e.toRingHom] (1 : A)) := rfl
  have hv := congrArg (fun f : E ⟶ E => f.hom v) h
  rw [hevalL, hevalR] at hv
  have hleft : φ ((1 : B) ⊗ₜ[A,e.toRingHom] a) = e a := by
    simp [φ, Algebra.smul_def]; rfl
  have hright : φ (b • ((1 : B) ⊗ₜ[A,e.toRingHom] (1 : A))) = b := by
    rw [← TensorProduct.tmul_eq_smul_one_tmul b (1 : A)]; simp [φ, Algebra.smul_def]
  simpa only [hleft, hright] using congrArg φ hv

/-- **Stacks Project, Tag 0GP1.** An equivalence of module categories linear over the base
ring is extension of scalars along an algebra isomorphism, followed by tensoring with an
invertible module. -/
@[stacks 0GP1]
public theorem exists_algEquiv_invertible_iso_extensionTensorFunctor
    (R : Type v) (A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    (F : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [F.IsEquivalence]
    [F.Linear R] :
    ∃ (e : A ≃ₐ[R] B) (L : ModuleCat.{u} B),
      Module.Invertible B L ∧
        Nonempty (F ≅ extensionTensorFunctor A B e.toRingEquiv L) := by
  obtain ⟨e, L, hL, ⟨η⟩⟩ :=
    exists_ringEquiv_invertible_iso_extensionTensorFunctor A B F
  have he : ∀ r : R, e (algebraMap R A r) = algebraMap R B r := by
    intro r
    let X : ModuleCat.{u} A := ModuleCat.of A A
    let E := (ModuleCat.extendScalars e.toRingHom).obj X
    let T := (MonoidalCategory.tensoringRight (ModuleCat.{u} B)).obj L
    let G := extensionTensorFunctor A B e L
    have h := (Functor.linear_iff (R := R) G).mp (Functor.linear_of_iso R η) X r
    rw [moduleCat_smul_eq_algebra_smul (R := R) (S := A) X (𝟙 X) r,
      moduleCat_smul_eq_algebra_smul (R := R) (S := B) (G.obj X) (𝟙 (G.obj X)) r] at h
    have hE : (ModuleCat.extendScalars e.toRingHom).map
        ((algebraMap R A r) • 𝟙 X) =
        (algebraMap R B r) • 𝟙 E := by
      apply tensorRight_map_injective L
      change T.map ((ModuleCat.extendScalars e.toRingHom).map
        ((algebraMap R A r) • 𝟙 X)) = T.map ((algebraMap R B r) • 𝟙 E)
      have hT : T.map ((algebraMap R B r) • 𝟙 E) =
          (algebraMap R B r) • 𝟙 (T.obj E) := by
        rw [Functor.map_smul (F := T), T.map_id]
      exact h.trans hT.symm
    exact ringEquiv_apply_eq_of_extensionScalars_map e
      (algebraMap R A r) (algebraMap R B r) hE
  exact ⟨{ toRingEquiv := e, commutes' := he }, L, hL, ⟨η⟩⟩

end ModuleCat
