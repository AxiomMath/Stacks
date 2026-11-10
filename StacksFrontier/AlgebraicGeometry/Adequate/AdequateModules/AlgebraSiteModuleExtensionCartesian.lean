module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AlgebraSiteCartesianBase

/-!
# The module extensions are cartesian

A presheaf of modules is *cartesian* when every restriction map is a base-change isomorphism,
`Stacks.PresheafOfModules.restrictionBaseChange`.  The module extension `C ↦ C ⊗[A] M` of an
`A`-module `M` is cartesian for a reason with no geometry in it: its restriction along an
`A`-algebra map `C ⟶ D` is `D ⊗[C] (C ⊗[A] M) ⟶ D ⊗[A] M`, and that is the cancellation
isomorphism of the tower of base changes `A ⟶ C ⟶ D`,
`TensorProduct.AlgebraTensorModule.cancelBaseChange`.

Nothing here relates the universe of `M` to the universe of the algebras: the cancellation
isomorphism is polymorphic in both, and so is this file.  That is why the sheaf condition for
the module extensions can be routed through the cartesian criterion at a value universe the
site knows nothing about.

## Main definitions

* `Stacks.Adequate.algebraMapCancelBaseChange` — the base change of a module extension along a
  map of `A`-algebras, computed as the cancellation isomorphism of the tower.  The ring map is
  an explicit argument together with the equation identifying it on `A`, so that the `Algebra`
  instance on the target is the one the base-change comparison uses rather than a
  propositionally equal copy.

## Main results

* `Stacks.Adequate.isScalarTower_of_commutes` — a ring map between two `A`-algebras which fixes
  the image of `A` makes the three into a tower of scalars.  This is the one instance the
  cancellation isomorphism needs and does not get for free.
* `Stacks.Adequate.isIso_restrictionBaseChange_moduleExtension` — **the module extensions are
  cartesian over every morphism of the algebra site.**
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w m

namespace Stacks.Adequate

open scoped ChangeOfRings

/-- A ring map between the underlying rings of two `A`-algebras which agrees with the two
structure maps on `A` makes `A`, the source and the target into a tower of scalars, when the
target is given the algebra structure the ring map defines. -/
public theorem isScalarTower_of_commutes {A : CommRingCat.{u}} (C D : CommAlgCat.{u} A)
    (ψ : CommRingCat.of (C : Type u) ⟶ CommRingCat.of (D : Type u))
    (hψ : ∀ a : (A : Type u),
      ψ.hom (algebraMap (A : Type u) (C : Type u) a) =
        algebraMap (A : Type u) (D : Type u) a) :
    letI : Algebra (C : Type u) (D : Type u) := ψ.hom.toAlgebra
    IsScalarTower (A : Type u) (C : Type u) (D : Type u) := by
  let : Algebra (C : Type u) (D : Type u) := ψ.hom.toAlgebra
  refine ⟨fun a c d => ?_⟩
  change ψ.hom (a • c) * d = a • (ψ.hom c * d)
  rw [Algebra.smul_def a c, map_mul, hψ, mul_assoc, ← Algebra.smul_def]

/-- **The base change of a module extension along a map of `A`-algebras, computed.**  Base
changing `C ⊗[A] M` from `C` to `D` gives `D ⊗[C] (C ⊗[A] M)`, and cancelling the intermediate
base change leaves `D ⊗[A] M`, which is the module extension at `D`. -/
public noncomputable def algebraMapCancelBaseChange {A : CommRingCat.{u}}
    (C D : CommAlgCat.{u} A)
    (ψ : CommRingCat.of (C : Type u) ⟶ CommRingCat.of (D : Type u))
    (hψ : ∀ a : (A : Type u),
      ψ.hom (algebraMap (A : Type u) (C : Type u) a) =
        algebraMap (A : Type u) (D : Type u) a)
    (M : ModuleCat.{w} A) :
    letI : Algebra (C : Type u) (D : Type u) := ψ.hom.toAlgebra
    TensorProduct (C : Type u) (D : Type u) (TensorProduct (A : Type u) (C : Type u) M)
      ≃ₗ[(D : Type u)] TensorProduct (A : Type u) (D : Type u) M := by
  letI : Algebra (C : Type u) (D : Type u) := ψ.hom.toAlgebra
  letI := isScalarTower_of_commutes C D ψ hψ
  exact TensorProduct.AlgebraTensorModule.cancelBaseChange (A : Type u) (C : Type u)
    (D : Type u) (D : Type u) M

/-- `Stacks.Adequate.algebraMapCancelBaseChange` on a pure tensor. -/
public theorem algebraMapCancelBaseChange_tmul {A : CommRingCat.{u}}
    (C D : CommAlgCat.{u} A)
    (ψ : CommRingCat.of (C : Type u) ⟶ CommRingCat.of (D : Type u))
    (hψ : ∀ a : (A : Type u),
      ψ.hom (algebraMap (A : Type u) (C : Type u) a) =
        algebraMap (A : Type u) (D : Type u) a)
    (M : ModuleCat.{w} A) (d : (D : Type u)) (c : (C : Type u)) (x : M) :
    letI : Algebra (C : Type u) (D : Type u) := ψ.hom.toAlgebra
    algebraMapCancelBaseChange.{u, w} C D ψ hψ M
        (d ⊗ₜ[(C : Type u)] (c ⊗ₜ[(A : Type u)] x)) =
      (d * ψ.hom c) ⊗ₜ[(A : Type u)] x := by
  let : Algebra (C : Type u) (D : Type u) := ψ.hom.toAlgebra
  let := isScalarTower_of_commutes C D ψ hψ
  refine Eq.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul (A : Type u)
    (C : Type u) (D : Type u) d x c) ?_
  refine congrArg (fun z => z ⊗ₜ[(A : Type u)] x) ?_
  rw [Algebra.smul_def c d]
  exact mul_comm _ _

/-- Additive maps out of a tensor product agreeing on pure tensors are equal. -/
private theorem addMonoidHom_tensor_ext {R S W T : Type*} [CommSemiring R] [AddCommMonoid S]
    [AddCommMonoid W] [Module R S] [Module R W] [AddCommMonoid T]
    (f g : TensorProduct R S W →+ T) (h : ∀ s w, f (s ⊗ₜ[R] w) = g (s ⊗ₜ[R] w)) : f = g :=
  AddMonoidHom.ext fun z => by
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => rw [map_add, map_add, hz, hz']
    | tmul s w => exact h s w

/-- An `S`-linear map out of a base change `S ⊗[R] W` is determined on pure tensors by its
values on `1 ⊗ₜ w`. -/
private theorem map_tmul_eq_smul_of_map_one_tmul {R S W T : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup W] [Module R W] [AddCommGroup T] [Module S T]
    (e : TensorProduct R S W →ₗ[S] T) (s : S) (w : W) (t : T) (h : e (1 ⊗ₜ[R] w) = t) :
    e (s ⊗ₜ[R] w) = s • t := by
  rw [← h, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The restriction maps of the presheaf of rings of the algebra site agree with the structure
maps of `A` on `A`: they are the underlying ring maps of morphisms of `A`-algebras. -/
public theorem algebraSiteRings_map_commutes {X Y : (algebraSite B)ᵒᵖ} (f : X ⟶ Y)
    (a : (A : Type u)) :
    ((algebraSiteRings B).map f).hom
        (algebraMap (A : Type u)
          (((AdequateFunctor.siteAlgebraInclusion (A : Type u)
            (schemeSizeBelow B.cutoff)).obj X.unop.unop : CommAlgCat.{u} A) : Type u) a) =
      algebraMap (A : Type u)
        (((AdequateFunctor.siteAlgebraInclusion (A : Type u)
          (schemeSizeBelow B.cutoff)).obj Y.unop.unop : CommAlgCat.{u} A) : Type u) a :=
  ((AdequateFunctor.siteAlgebraInclusion (A : Type u)
    (schemeSizeBelow B.cutoff)).map f.unop.unop).hom.commutes a

/-- **The module extensions are cartesian.**  The base-change comparison agrees on pure tensors
with the cancellation isomorphism `Stacks.Adequate.algebraMapCancelBaseChange` of the tower
`A ⟶ C ⟶ D`, and both are additive, so they agree. -/
public theorem isIso_restrictionBaseChange_moduleExtension (M : ModuleCat.{max u m} A)
    {X Y : (algebraSite B)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, max u m}
      (R := algebraSiteRings B)
      ((AdequateFunctor.moduleExtensionFunctorOn
        (AdequateFunctor.siteAlgebraInclusion (A : Type u)
          (schemeSizeBelow B.cutoff))).obj M) f) := by
  set ι := AdequateFunctor.siteAlgebraInclusion (A : Type u) (schemeSizeBelow B.cutoff)
  let : Algebra ((ι.obj X.unop.unop : CommAlgCat.{u} A) : Type u)
      ((ι.obj Y.unop.unop : CommAlgCat.{u} A) : Type u) :=
    ((algebraSiteRings B).map f).hom.toAlgebra
  set e := algebraMapCancelBaseChange.{u, max u m} (ι.obj X.unop.unop) (ι.obj Y.unop.unop)
    ((algebraSiteRings B).map f) (algebraSiteRings_map_commutes B f) M with he
  set N := (AdequateFunctor.moduleExtensionFunctorOn ι).obj M
  have h : Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, max u m}
      (R := algebraSiteRings B) N f = ModuleCat.ofHom e.toLinearMap := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
    refine DFunLike.congr_fun (addMonoidHom_tensor_ext
      (Stacks.PresheafOfModules.restrictionBaseChange.{u + 1, u, u, max u m}
        (R := algebraSiteRings B) N f).hom.toAddMonoidHom e.toLinearMap.toAddMonoidHom
      fun d y => ?_) z
    refine (Stacks.PresheafOfModules.restrictionBaseChange_tmul
      (R := algebraSiteRings B) N f d y).trans ?_
    have hone : ∀ w : TensorProduct (A : Type u)
        ((ι.obj X.unop.unop : CommAlgCat.{u} A) : Type u) M,
        e ((1 : ((ι.obj Y.unop.unop : CommAlgCat.{u} A) : Type u)) ⊗ₜ[
          ((ι.obj X.unop.unop : CommAlgCat.{u} A) : Type u)] w) = (N.map f) w := fun w =>
      DFunLike.congr_fun (addMonoidHom_tensor_ext
        (e.toLinearMap.toAddMonoidHom.comp (TensorProduct.mk _ _ _ 1).toAddMonoidHom)
        (N.map f).hom.toAddMonoidHom fun c x => by
          change e (1 ⊗ₜ[_] (c ⊗ₜ[(A : Type u)] x)) = _
          rw [he, algebraMapCancelBaseChange_tmul.{u, max u m}, one_mul]
          change _ = ((AdequateFunctor.moduleExtension (A : Type u) M).map
            (ι.op.op.map f)) (c ⊗ₜ[(A : Type u)] x)
          rw [AdequateFunctor.moduleExtension_map_tmul]
          rfl) w
    exact (map_tmul_eq_smul_of_map_one_tmul e.toLinearMap d y _ (hone y)).symm
  rw [h]
  exact (LinearEquiv.toModuleIso e).isIso_hom

end Stacks.Adequate

end
