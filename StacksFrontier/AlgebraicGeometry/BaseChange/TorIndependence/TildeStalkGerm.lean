module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedTildeStalk
public import StacksFrontier.RingTheory.MilnorPatching.ModuleProperties
import all StacksFrontier.RingTheory.MilnorPatching.ModuleProperties

/-!
# The stalk of an associated sheaf, computed on the germ of a global section

`AlgebraicGeometry.tildeModulesStalkIso` identifies the stalk at `y` of the sheaf associated to
an `A`-module `M` with `𝒪_{Spec A, y} ⊗_A M`, but it is produced by comparing right adjoints and
carries no description of what it does to an element. This file supplies that description, at the
only elements a consumer needs: the germ at `y` of the global section of `M̃` attached to `m : M`
goes to `1 ⊗ m`.

That single equation pins the isomorphism down. Both sides of
`AlgebraicGeometry.tildeModulesStalkIso` are left adjoints, so a morphism out of the left-hand
side is determined by its composite with the unit of the adjunction, and the unit *is*
`m ↦ germ_y (toOpen M ⊤ m)`.

## The route

`tildeModulesStalkIso` is a five-fold composite: the crossing between the two spellings of the
stalk functor, Stacks 01HV over the `RingCat`-valued stalk, and the three factors of
`AlgebraicGeometry.tildeStalkBaseChangeIso`. Each factor is computed separately.

* The crossing `AlgebraicGeometry.restrictScalarsStalkFunctorIso` is the identity on underlying
  abelian groups, so it moves a germ to itself.
* `Stacks.TildeStalk.tildeStalkFunctorIso` is
  `CategoryTheory.Adjunction.leftAdjointUniq`, so `unit_leftAdjointUniq_hom_app` computes it
  against the unit of the tilde–skyscraper adjunction, and that unit is the germ of `toOpen`.
* `ModuleCat.restrictScalarsIsoExtendScalarsOfRingEquiv` is again a `leftAdjointUniq`, over the
  unit of an equivalence, which is the identity on carriers; so it is `n ↦ 1 ⊗ n`.
* The two extension-of-scalars factors are Mathlib's `ModuleCat.extendScalarsComp`, computed by
  `ModuleCat.extendScalarsComp_hom_app_one_tmul`, and a transport along an equality of ring
  homomorphisms.

## Main results

* `Stacks.TildeStalk.tildeStalkAdjunction_ofNatIsoRight_unit_apply`: the unit of the adjunction
  that presents `~ ⋙ (-)_y` as a left adjoint of restriction of scalars is `m ↦ germ_y (toOpen
  M ⊤ m)`.
* `Stacks.TildeStalk.tildeStalkFunctorIso_hom_app_germ_toOpen`: **Stacks 01HV on a germ**, over
  the `RingCat`-valued stalk.
* `AlgebraicGeometry.tildeModulesStalkIso_hom_app_germ_toOpen`: **Stacks 01HV on a germ**, over
  the local ring `𝒪_{Spec A, y}`. This is the form every consumer uses.

## Implementation notes

The five-fold splitting of `tildeModulesStalkIso` is stated as a `have` proved by `rfl`, with the
identity component of the associator written out and the composite parenthesised to the right.
Reaching it by `dsimp only [tildeModulesStalkIso]` instead fails: unfolding the definition
presents the category of modules on `Spec A` as `SheafOfModules (Spec A).ringCatSheaf`, and the
resulting goal is not type-correct at the implicit transparency at which `simp` checks its
output.

No tag attribute is placed here. Stacks 01HV is the identification itself, which the development
already carries; what is added is a computation of it on one family of elements.

## References

* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped ChangeOfRings

universe u

namespace ModuleCat

/-- **Restriction of scalars along the inverse of a ring isomorphism, on an element.** The
comparison of `ModuleCat.restrictScalarsIsoExtendScalarsOfRingEquiv` sends `n` to `1 ⊗ n`.

Both functors are left adjoints of restriction of scalars along `e`, and the comparison is
`CategoryTheory.Adjunction.leftAdjointUniq`; the unit on the restriction side is the unit of an
equivalence, which is the identity on carriers, so
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` is the statement. -/
public theorem restrictScalarsIsoExtendScalarsOfRingEquiv_hom_app_apply {T O : Type u}
    [CommRing T] [CommRing O] (e : T ≃+* O) (N : ModuleCat.{u} T) (n : N) :
    ((ModuleCat.restrictScalarsIsoExtendScalarsOfRingEquiv.{u} e).hom.app N).hom n =
      (1 : O) ⊗ₜ[T, e.toRingHom] n :=
  congr($(CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u} e.symm).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} e.toRingHom) N).hom n)

/-- **The transport along an equality of ring homomorphisms, on a unital tensor.** It fixes
`1 ⊗ m`. -/
public theorem extendScalarsFunctorCongr_hom_app_one_tmul {R S : Type u} [CommRing R]
    [CommRing S] {f g : R →+* S} (h : f = g) (M : ModuleCat.{u} R) (m : M) :
    ((ModuleCat.extendScalarsFunctorCongr.{u} h).hom.app M).hom ((1 : S) ⊗ₜ[R, f] m) =
      (1 : S) ⊗ₜ[R, g] m := by
  subst h
  rfl

/-- **A five-fold composite of morphisms of modules evaluated on an element, step by step.** An
identity is inserted after the first factor, which is the shape the splitting of
`AlgebraicGeometry.tildeModulesStalkIso` has, and each step's value is given as a hypothesis.

Every object and morphism is a variable. The concrete composite this is applied to mixes two
spellings of the category of modules on `Spec A` and two spellings of the stalk ring, and a `rw`
on it is rejected as producing a goal that is not type-correct at the implicit transparency; with
variables there is nothing to unfold and the chase is five rewrites. -/
public theorem comp5_id_apply_of_eq {O : Type u} [Ring O] {N₀ N₁ N₂ N₃ N₄ N₅ : ModuleCat.{u} O}
    (f₁ : N₀ ⟶ N₁) (f₂ : N₁ ⟶ N₂) (f₃ : N₂ ⟶ N₃) (f₄ : N₃ ⟶ N₄) (f₅ : N₄ ⟶ N₅)
    (z : N₀) (a₁ : N₁) (a₂ : N₂) (a₃ : N₃) (a₄ : N₄) (a₅ : N₅)
    (h₁ : f₁.hom z = a₁) (h₂ : f₂.hom a₁ = a₂) (h₃ : f₃.hom a₂ = a₃)
    (h₄ : f₄.hom a₃ = a₄) (h₅ : f₅.hom a₄ = a₅) :
    (f₁ ≫ 𝟙 N₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅).hom z = a₅ := by
  have hpeel : (f₁ ≫ 𝟙 N₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅).hom z =
      f₅.hom (f₄.hom (f₃.hom (f₂.hom (f₁.hom z)))) := by simp
  rw [hpeel, h₁, h₂, h₃, h₄, h₅]

end ModuleCat

namespace Stacks.TildeStalk

open AlgebraicGeometry

variable (A : CommRingCat.{u}) (y : (Spec A).carrier) (M : ModuleCat.{u} A)

/-- **The unit of the tilde–skyscraper adjunction on an element.** The adjunction presenting
`~ ⋙ (-)_y` as a left adjoint of restriction of scalars along the germ map has unit
`m ↦ germ_y (toOpen M ⊤ m)`: the global section of `M̃` attached to `m`, read as a germ at `y`.

The three factors are the unit of `AlgebraicGeometry.tilde.adjunction`, which is
`AlgebraicGeometry.tilde.toOpen` at `⊤`, the unit of the stalk–skyscraper adjunction, which is
the germ map, and the evaluation of a section of a skyscraper at the unique proof that `y` lies
in `⊤`. -/
public theorem tildeStalkAdjunction_ofNatIsoRight_unit_apply (m : M) :
    (((tildeStalkAdjunction A y).ofNatIsoRight (specSkyscraperSectionsIso A y)).unit.app M).hom m =
      (TopCat.Presheaf.germ ((tilde.functor A).obj M).val.presheaf ⊤ y trivial).hom
        ((tilde.toOpen M ⊤).hom m) := by
  have h1 : ((tildeStalkAdjunction A y).ofNatIsoRight
        (specSkyscraperSectionsIso A y)).unit.app M =
      (tildeStalkAdjunction A y).unit.app M ≫
        (specSkyscraperSectionsIso A y).hom.app
          ((tilde.functor A ⋙ specStalkFunctor A y).obj M) := by
    rw [Adjunction.ofNatIsoRight_unit]; rfl
  have h2 : (tildeStalkAdjunction A y).unit.app M =
      (tilde.adjunction (R := A)).unit.app M ≫
        moduleSpecΓFunctor.map ((AlgebraicGeometry.SheafOfModules.stalkSkyscraperAdjunction
          (structureSheafRing (Spec A).toRingedSpace) y).unit.app ((tilde.functor A).obj M)) :=
    Adjunction.comp_unit_app _ _ M
  rw [h1, h2]
  rfl

/-- **Stacks 01HV on a germ, over the `RingCat`-valued stalk.** The identification of the stalk
at `y` of `M̃` with `𝒪_{Spec A,y} ⊗_A M` sends the germ of the global section attached to `m` to
`1 ⊗ m`.

`Stacks.TildeStalk.tildeStalkFunctorIso` is `CategoryTheory.Adjunction.leftAdjointUniq`, so
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` compares it with the unit of
`ModuleCat.extendRestrictScalarsAdj`, which is `m ↦ 1 ⊗ m`; the unit on the other side is
`tildeStalkAdjunction_ofNatIsoRight_unit_apply`. -/
public theorem tildeStalkFunctorIso_hom_app_germ_toOpen (m : M) :
    letI := Stacks.RingedSpace.structureStalkCommRing (Spec A).toRingedSpace y
    ((tildeStalkFunctorIso A y).hom.app M).hom
        ((TopCat.Presheaf.germ ((tilde.functor A).obj M).val.presheaf ⊤ y trivial).hom
          ((tilde.toOpen M ⊤).hom m)) =
      (1 : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (structureSheafRing (Spec A).toRingedSpace).obj y)) ⊗ₜ[A, specStalkRingHom A y] m := by
  rw [← tildeStalkAdjunction_ofNatIsoRight_unit_apply A y M m]
  exact congr($(CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
    ((tildeStalkAdjunction A y).ofNatIsoRight (specSkyscraperSectionsIso A y))
    (tildeStalkBaseChangeAdjunction A y) M).hom m)

end Stacks.TildeStalk

namespace AlgebraicGeometry

variable (A : CommRingCat.{u}) (y : (Spec A).carrier) (M : ModuleCat.{u} A)

/-- **Stacks 01HV on a germ, over the local ring.** `AlgebraicGeometry.tildeModulesStalkIso`
sends the germ at `y` of the global section of `M̃` attached to `m : M` to `1 ⊗ m` in
`𝒪_{Spec A, y} ⊗_A M`.

This is the computation the comparison of Stacks 01HV with the affine pullback isomorphism of
Stacks 01I9 and the stalk formula of Stacks 0098 rests on: it says that the identification of
Stacks 01HV is the one normalised against the unit of `AlgebraicGeometry.tilde.adjunction`. -/
public theorem tildeModulesStalkIso_hom_app_germ_toOpen (m : M) :
    ((tildeModulesStalkIso A y).hom.app M).hom
        ((TopCat.Presheaf.germ ((tilde.functor A).obj M).val.presheaf ⊤ y trivial).hom
          ((tilde.toOpen M ⊤).hom m)) =
      (1 : ToType ((Spec A).presheaf.stalk y)) ⊗ₜ[A, specGermRingHom A y] m := by
  let := Stacks.RingedSpace.structureStalkCommRing (Spec A).toRingedSpace y
  have hsplit : (tildeModulesStalkIso A y).hom.app M =
      (restrictScalarsStalkFunctorIso (X := Spec A) y).inv.app ((tilde.functor A).obj M) ≫
      𝟙 _ ≫
      ((ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv y).symm.toRingHom).map
        ((Stacks.TildeStalk.tildeStalkFunctorIso A y).hom.app M) ≫
      ((ModuleCat.restrictScalarsIsoExtendScalarsOfRingEquiv.{u}
          (ringCatStalkRingEquiv y)).hom.app
        ((Stacks.TildeStalk.tildeStalkBaseChange A y).obj M) ≫
      ((ModuleCat.extendScalarsComp.{u, u} (Stacks.TildeStalk.specStalkRingHom A y)
        (ringCatStalkRingEquiv y).toRingHom).inv.app M ≫
      (ModuleCat.extendScalarsFunctorCongr.{u}
        (ringCatStalkRingEquiv_comp_specStalkRingHom A y)).hom.app M))) := rfl
  exact Eq.trans
    (congrArg
      (fun u : (tilde.functor A ⋙ Stacks.ModuleSkyscraper.modulesStalkFunctor (Spec A) y).obj M ⟶
          (ModuleCat.extendScalars.{u, u, u} (specGermRingHom A y)).obj M =>
        u.hom ((TopCat.Presheaf.germ ((tilde.functor A).obj M).val.presheaf ⊤ y trivial).hom
          ((tilde.toOpen M ⊤).hom m)))
      hsplit)
    (ModuleCat.comp5_id_apply_of_eq _ _ _ _ _ _ _ _ _ _ _ rfl
      (Stacks.TildeStalk.tildeStalkFunctorIso_hom_app_germ_toOpen A y M m)
      (ModuleCat.restrictScalarsIsoExtendScalarsOfRingEquiv_hom_app_apply _ _ _)
      (by
        have h := MilnorPatching.comp_inv_tmul (Stacks.TildeStalk.specStalkRingHom A y)
          (ringCatStalkRingEquiv y).toRingHom M 1 1 m
        simp only [map_one, one_mul] at h
        exact h)
      (ModuleCat.extendScalarsFunctorCongr_hom_app_one_tmul _ _ _))

end AlgebraicGeometry

end
