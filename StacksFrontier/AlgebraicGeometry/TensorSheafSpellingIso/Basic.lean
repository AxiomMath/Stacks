module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.AlgebraicGeometry.SheafInternalHom.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction

/-!
# The monoidal product of sheaves of modules is the tensor product sheaf

The canonical tensor product of sheaves of modules (Stacks Tag 01CA) is
`Stacks.SheafOfModules.Tensor.sheafTensor`: sheafify the root
`PresheafOfModules.tensorObj` of the underlying presheaves. Its action on a pair of morphisms
is sheafification of `PresheafOfModules.tensorHom`.

This file compares that tensor product with the monoidal product of
`Stacks.SheafOfModules.monoidalCategory`, naturally in both arguments, and specializes the
comparison to `Stacks.SheafInternalHom.schemeMonoidalCategory`. The comparison is substantive:
the latter monoidal structures are obtained by localization, whose tensor product is supplied
by a universal property rather than by the native tensor definition. The comparison uses the
monoidal structure isomorphism of the sheafification functor and its invertible counit.

## Main results

* `Stacks.TensorSheafSpellingIso.tensorSheafIsoMonoidal`: for a sheaf of commutative rings on
  any site, the monoidal product of `Stacks.SheafOfModules.monoidalCategory` is the tensor
  product sheaf defined by `Stacks.SheafOfModules.Tensor.sheafTensor`, with
  `tensorSheafIsoMonoidal_naturality` its naturality in both arguments.
* `Stacks.TensorSheafSpellingIso.monoidalTensorIso`: the consequence for a scheme, in the
  vocabulary the ampleness and twisting files are written over.  For `A B : X.Modules` with
  `Stacks.SheafInternalHom.schemeMonoidalCategory` active,
  it identifies `A ⊗ B` with the canonical tensor product of `A` and `B`, naturally in both
  arguments against the action of the native bifunctor.

## Implementation notes

`tensorSheafIsoMonoidal` reuses `Stacks.SheafOfModules.tensorObjIso`, and its naturality reuses
the shared `Stacks.SheafOfModules.tensorObjIso_naturality`. The explicit right-adjoint
comparison `tensorObjIsoOver` and its naturality remain available for computations through
`forgetRestrict`. The scheme-level computation uses `sheafTensor_uncurry_map` to pass from
sheafification of the presheaf tensor map to the action of the native bifunctor.

`sheafifyMonoidal` must be `instance_reducible`: as a semireducible definition of class type it
makes the scheme-level unification of `tensorObjIsoOver`'s type exhaust the unifier's budget.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [The Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry

universe v u w

namespace Stacks.TensorSheafSpellingIso

/-! ### The monoidal product is the tensor product sheaf -/

section Monoidal

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  PresheafOfModules.toPresheaf PresheafOfModulesOfCommRing.Monoidal.tensorObj

/-- The right adjoint of module sheafification — forget the sheaf condition, then restrict
scalars along the identity — written as a functor whose codomain is spelled over
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf`, which is the domain spelling of
`Stacks.SheafOfModules.sheafifyFunctor`.  Writing `F.val` instead leaves goals that are not
type-correct at `implicit` transparency; see the implementation notes. -/
abbrev forgetRestrict : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⥤
    PresheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪) :=
  SheafOfModules.forget (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪) ⋙
    PresheafOfModules.restrictScalars (𝟙 (Stacks.SheafOfModules.TensorSheafification.structureSheaf
      𝒪 h𝒪).obj)

/-- Sheafifying the underlying presheaf of a sheaf of modules returns it: the counit of the
sheafification adjunction, as an isomorphism.  This is
`Stacks.SheafOfModules.sheafifyValIso` with its source written through `forgetRestrict`. -/
def valIso (F : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪))
  :
    (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj ((forgetRestrict 𝒪 h𝒪).obj F) ≅ F :=
  (asIso (Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction 𝒪 h𝒪).counit).app F

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Naturality of `valIso` in the form the comparison needs, with the inverse on the left. -/
theorem valIso_inv_naturality
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)} (p :
      A ⟶ B) :
    p ≫ (valIso 𝒪 h𝒪 B).inv
      = (valIso 𝒪 h𝒪 A).inv
          ≫ (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).map ((forgetRestrict 𝒪 h𝒪).map p) := by
  exact Stacks.SheafOfModules.comp_sheafifyValIso_inv 𝒪 h𝒪 p

/-- Module sheafification is a monoidal functor for `Stacks.SheafOfModules.monoidalCategory`.
This is Mathlib's instance for the localizing functor of a localized monoidal category, with
the functor spelled as `Stacks.SheafOfModules.sheafifyFunctor`; its structure isomorphism is
`Stacks.SheafOfModules.sheafifyTensorIso`. -/
@[instance_reducible]
noncomputable def sheafifyMonoidal : (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).Monoidal := by
  change (Localization.Monoidal.toMonoidalCategory
    (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪)
    (Stacks.SheafOfModules.localIso (J := J) 𝒪)
    (Stacks.SheafOfModules.sheafifyUnitIso 𝒪 h𝒪)).Monoidal
  infer_instance

attribute [local instance] sheafifyMonoidal

/-- The monoidal product of two sheaves of modules is the sheafification of the objectwise
tensor product of their underlying presheaves — the comparison written entirely through
`forgetRestrict`, so that `tensorObjIsoOver_naturality` can be proved by rewriting. -/
def tensorObjIsoOver (F G : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    F ⊗ G ≅ (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).obj
      ((forgetRestrict 𝒪 h𝒪).obj F ⊗ (forgetRestrict 𝒪 h𝒪).obj G) :=
  ((valIso 𝒪 h𝒪 F).symm ⊗ᵢ (valIso 𝒪 h𝒪 G).symm) ≪≫
    Functor.Monoidal.μIso (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪) _ _

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `tensorObjIsoOver` is natural in both module arguments.  Three steps: the two tensored
morphisms are composed by `tensorHom_comp_tensorHom`, each factor is moved across the
sheafification counit by `valIso_inv_naturality`, and the result is carried through the
structure isomorphism by `Functor.LaxMonoidal.μ_natural`. -/
theorem tensorObjIsoOver_naturality
    {F F' G G' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (f ⊗ₘ g) ≫ (tensorObjIsoOver 𝒪 h𝒪 F' G').hom
      = (tensorObjIsoOver 𝒪 h𝒪 F G).hom
          ≫ (Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪).map
              ((forgetRestrict 𝒪 h𝒪).map f ⊗ₘ (forgetRestrict 𝒪 h𝒪).map g) := by
  simp only [tensorObjIsoOver, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
    Functor.Monoidal.μIso_hom]
  conv_lhs => rw [← Category.assoc, tensorHom_comp_tensorHom, valIso_inv_naturality,
    valIso_inv_naturality, ← tensorHom_comp_tensorHom, Category.assoc,
    Functor.LaxMonoidal.μ_natural]
  rw [Category.assoc]

/-- **The monoidal product of sheaves of modules is the tensor product sheaf of Tag 01CA.**
This is the shared comparison `Stacks.SheafOfModules.tensorObjIso`, with the canonical native
tensor product as its target. -/
def tensorSheafIsoMonoidal (F G : SheafOfModules.{w}
  (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) :
    F ⊗ G ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj G :=
  Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 F G

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `tensorSheafIsoMonoidal` is natural in both module arguments against the native bifunctor. -/
theorem tensorSheafIsoMonoidal_naturality
    {F F' G G' : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪
      h𝒪)}
    (f : F ⟶ F') (g : G ⟶ G') :
    (f ⊗ₘ g) ≫ (tensorSheafIsoMonoidal 𝒪 h𝒪 F' G').hom
      = (tensorSheafIsoMonoidal 𝒪 h𝒪 F G).hom
          ≫ (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩)).map
                (X := (F, G)) (Y := (F', G')) (f, g) := by
  unfold tensorSheafIsoMonoidal
  have naturality := Stacks.SheafOfModules.tensorObjIso_naturality 𝒪 h𝒪
    (M := F) (M' := F') (N := G) (N' := G') f g
  have mapEquality := Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩
    (left := F) (left' := F') (right := G) (right' := G') f g
  exact naturality.trans
    (congrArg (fun morphism => (Stacks.SheafOfModules.tensorObjIso 𝒪 h𝒪 F G).hom ≫ morphism)
      mapEquality.symm)

end Monoidal

/-! ### The consequence for a scheme -/

section Scheme

variable (X : Scheme.{u})

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory
attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf TopCat.Sheaf

/-- **The monoidal product on `X.Modules` is the canonical sheaf tensor.** This identifies
the native bifunctor with the monoidal `⊗` of `Stacks.SheafInternalHom.schemeMonoidalCategory`,
as needed for the tensor powers of Tag 01CU. -/
def monoidalTensorIso (A B : X.Modules) :
    A ⊗ B ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj A).obj B :=
  tensorSheafIsoMonoidal X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) A B

/-- `monoidalTensorIso` is natural in both module arguments against the native bifunctor. -/
theorem monoidalTensorIso_naturality {A A' B B' : X.Modules} (f : A ⟶ A') (g : B ⟶ B') :
    (f ⊗ₘ g) ≫ (monoidalTensorIso X A' B').hom
      = (monoidalTensorIso X A B).hom ≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
              (X := (A, B)) (Y := (A', B')) (f, g) :=
  tensorSheafIsoMonoidal_naturality X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
    (F := A) (F' := A') (G := B) (G' := B') f g

/-- The structure sheaf of rings of a scheme in Tag 01CB's packaging is Mathlib's
`AlgebraicGeometry.Scheme.ringCatSheaf`, so `X.Modules` is already the category Tag 01CB's
tensor product is defined on.  This is the half of the earlier diagnosis that was *not* the
obstruction. An alias of
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.structureSheafRing_eq_ringCatSheaf`. -/
alias structureSheafRing_eq_ringCatSheaf :=
  Stacks.AlgebraicGeometry.SchemeHigherDirectImage.structureSheafRing_eq_ringCatSheaf

end Scheme

end Stacks.TensorSheafSpellingIso

end
