module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.BaseRingLinear
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.EventualExtVanishing
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Restriction along an open immersion is linear over a base ring

Let `f : X ⟶ Y` be an open immersion of schemes and let `A` be a commutative ring equipped with
a ring map `φ : A ⟶ Γ(Y, 𝒪_Y)`. Composing `φ` with the restriction `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`
makes `X.Modules` an `A`-linear category as well, by
`AlgebraicGeometry.Scheme.linearOfRingHom`, and restriction of modules along `f` is then an
`A`-linear functor.  The same holds for the functor it induces on the unbounded derived
categories.

Carrying one fixed scalar ring `A` across all the open subschemes of a scheme is what makes a
statement such as "this morphism of `D(𝒪_X)` is killed by a power of `f ∈ Γ(X, 𝒪_X)`" restrict
to the same statement on an open subscheme: the scalar does not have to be renamed, only the
ring map changes.

## Main results

* `Stacks.DerivedQCoh.restrictFunctor_linear`: restriction of modules along an open immersion
  is `A`-linear.
* `Stacks.DerivedQCoh.derivedRestrict_linear`: the induced functor on the unbounded derived
  categories is `A`-linear.

## Implementation notes

A scalar `a` acts on a morphism of `𝒪_Y`-modules by multiplication by the restriction of the
global section `φ a`, which is `Stacks.SheafOfModules.smul_val_app`. On the restricted module
the sections over an open `U ⊆ X` are the sections of the original module over `f(U)`, and the
`Γ(X, U)`-module structure is the one transported along `(f.appIso U).inv`. The content of the
first result is therefore the identity

`(f.appIso U).inv (res^⊤_U (f^♯ s)) = res^⊤_{f(U)} s`

for a global section `s` of `𝒪_Y`, which is `Stacks.DerivedQCoh.appTop_res_appIso_inv`: both
sides are the restriction of `s` to `f(U)`, read through the isomorphism `Γ(Y, f(U)) ≅ Γ(X, U)`
of the open immersion. It is proved from `AlgebraicGeometry.Scheme.Hom.appLE_appIso_inv` in
term mode, because the goal is not type-correct at `implicit` transparency -- `f ⁻¹ᵁ ⊤` and `⊤`
are equal only by unfolding -- so `rw` refuses it.

The derived statement is `CategoryTheory.Localization.functor_linear_iff` at the localization
`DerivedCategory.Q`, for which `Functor.mapDerivedCategory` is a lift of
`F.mapHomologicalComplex _ ⋙ DerivedCategory.Q`; that composite is `A`-linear because
`CategoryTheory.Functor.mapHomologicalComplex_linear` and `DerivedCategory.Q` are.

The `A`-linear structures are `letI`-local, `AlgebraicGeometry.Scheme.linearOfRingHom` being a
definition and not an instance: the ring `A` is not determined by the scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Duality.OpenImmersion (derivedRestrict)

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- **Restricting a global section of `𝒪_Y` to an open `U` of `X` through an open immersion
`f : X ⟶ Y` is restricting it to `f(U)`.** The two readings are compared by the isomorphism
`Γ(Y, f(U)) ≅ Γ(X, U)` attached to the open immersion. -/
theorem appTop_res_appIso_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    f.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ (f.appIso U).inv =
      Y.presheaf.map (homOfLE (le_top : f ''ᵁ U ≤ ⊤)).op :=
  have h1 : f.appTop ≫ X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op =
      f.appLE ⊤ U (by simp) := rfl
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (f.appIso U).inv) h1).trans
      (AlgebraicGeometry.Scheme.Hom.appLE_appIso_inv f _))

/-- `Stacks.DerivedQCoh.appTop_res_appIso_inv` read on a global section. -/
theorem appTop_res_appIso_inv_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) (s : Γ(Y, ⊤)) :
    (f.appIso U).inv (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop s)) =
      Y.presheaf.map (homOfLE (le_top : f ''ᵁ U ≤ ⊤)).op s := by
  have := ConcreteCategory.congr_hom (appTop_res_appIso_inv f U) s
  simpa only [CommRingCat.comp_apply] using this

/-- **Restriction of modules along an open immersion `f : X ⟶ Y` is `A`-linear**, for the
`A`-linear structures attached to a ring map `φ : A ⟶ Γ(Y, 𝒪_Y)` and to its composite with
the restriction `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)`. -/
theorem restrictFunctor_linear {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (φ : A →+* Γ(Y, ⊤)) :
    letI : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
    letI : Linear A X.Modules := Scheme.linearOfRingHom X A ((f.appTop).hom.comp φ)
    Functor.Linear A (Scheme.Modules.restrictFunctor f) := by
  let : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
  let : Linear A X.Modules := Scheme.linearOfRingHom X A ((f.appTop).hom.comp φ)
  refine { map_smul := ?_ }
  intro M N g a
  ext U x
  have hL : (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor f).map (a • g)) U).hom x =
      (Scheme.Modules.Hom.app (a • g) (f ''ᵁ U)).hom x := rfl
  have hLs : (Scheme.Modules.Hom.app (a • g) (f ''ᵁ U)).hom x =
      (Y.presheaf.map (homOfLE (le_top : f ''ᵁ U ≤ ⊤)).op (φ a)) •
        (Scheme.Modules.Hom.app g (f ''ᵁ U)).hom x :=
    Stacks.SheafOfModules.smul_val_app Y.ringCatSheaf A ⊤ isTerminalTop φ a g
      (op (f ''ᵁ U)) x
  have hR : (Scheme.Modules.Hom.app (a • (Scheme.Modules.restrictFunctor f).map g) U).hom x =
      (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (((f.appTop).hom.comp φ) a)) •
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor f).map g) U).hom x :=
    Stacks.SheafOfModules.smul_val_app X.ringCatSheaf A ⊤ isTerminalTop
      ((f.appTop).hom.comp φ) a ((Scheme.Modules.restrictFunctor f).map g) (op U) x
  have hsm : ∀ (r : Γ(X, U)) (y : Γ(N, f ''ᵁ U)),
      (((Scheme.Modules.restrictFunctor f).obj N).smul (U := U) r).hom y =
        ((f.appIso U).inv r) • y := fun _ _ => rfl
  have hsm' : (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (((f.appTop).hom.comp φ) a)) •
        (Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctor f).map g) U).hom x =
      ((f.appIso U).inv (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f.appTop (φ a)))) •
        (Scheme.Modules.Hom.app g (f ''ᵁ U)).hom x := hsm _ _
  exact hL.trans (hLs.trans (Eq.trans
    ((congrArg (fun r => r • (Scheme.Modules.Hom.app g (f ''ᵁ U)).hom x)
      (appTop_res_appIso_inv_apply f U (φ a))).symm.trans hsm'.symm) hR.symm))

/-- **Restriction of unbounded derived modules along an open immersion is `A`-linear.** -/
theorem derivedRestrict_linear {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (φ : A →+* Γ(Y, ⊤)) :
    letI : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
    letI : Linear A X.Modules := Scheme.linearOfRingHom X A ((f.appTop).hom.comp φ)
    Functor.Linear A (derivedRestrict f) := by
  let : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
  let : Linear A X.Modules := Scheme.linearOfRingHom X A ((f.appTop).hom.comp φ)
  let : Functor.Linear A (Scheme.Modules.restrictFunctor f) := restrictFunctor_linear f φ
  let : PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
    preservesFiniteLimits_restrictFunctor f
  refine (Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso Y.Modules (ComplexShape.up ℤ)) A
    ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q)
    (Scheme.Modules.restrictFunctor f).mapDerivedCategory).1 ?_
  infer_instance

end Stacks.DerivedQCoh

end
