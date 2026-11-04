module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormula
public import StacksFrontier.AlgebraicGeometry.TensorSheafSpellingIso.Basic

/-!
# The section-level tensor comparison in its first variable

`StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormula.lean` proves that the section-level
tensor comparison `Stacks.SectionTensorFormula.toTensorSection` is natural in its **second**
variable, and that was all its consumer — the formula for multiplication by a global section —
needed. The twist-transport statements of [Stacks, Tag 0BQR] need the **first** variable as well,
and on sections rather than as an equality of morphisms of presheaves. This file is that mirror
image:

  `(f ▷ G)(tensorSection F G m n) = tensorSection F' G (f(m)) n`,

together with the two sheaf-level statements it is assembled from, at the generality of an
arbitrary ringed site.

The same consumer needs the monoidal product `A ⊗ B` of `X.Modules` written as a value of the
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`, which is the spelling the tensor product of
complexes of sheaves of modules is stated over. That bridge, and its naturality in the first
variable, are the last two declarations here. They are cheap:
`Stacks.TensorSheafSpellingIso.monoidalTensorIso` is already that isomorphism, only with the
structure sheaf of `X` written `⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩` instead of
`X.toRingedSpace.sheaf`; the two spellings are **equal**, so the bridge is that isomorphism with
its target restated.

## Main definitions

* `Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso`: the monoidal product of
  `X.Modules` as a value of the bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`.

## Main results

* `Stacks.SectionTensorFormula.tensorSheafIsoTensorObj_hom_whiskerRight`: **naturality of
  `tensorSheafIsoTensorObj` in its first variable.** For `f : F ⟶ F'`,
  `(tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom ≫ f ▷ G` is
  `(sheafify 𝒪 h𝒪).map (f.val ▷ G.val) ≫ (tensorSheafIsoTensorObj 𝒪 h𝒪 F' G).hom`.
* `Stacks.SectionTensorFormula.toTensorSection_comp_whiskerRight_val`: **naturality of the
  section comparison in its first variable**, as an equality of morphisms of presheaves of
  modules.
* `Stacks.SectionTensorFormula.tensorSection_whiskerRight`: **the payload**, the previous
  statement read on an elementary tensor of sections over an open of a scheme.
* `Stacks.TensorSheafSpellingIso.monoidalTensorSheafTensorIso_naturality_left`: naturality of
  the bridge in its first variable, against `Stacks.SheafOfModules.Tensor.sheafTensor`'s own
  action on morphisms.

## Implementation notes

**Why the sheaf-level proofs are terms and not rewrites.** The reason is the one recorded in the
implementation notes of `StacksFrontier/AlgebraicGeometry/SectionProduct/MulSecFormula.lean`: three
spellings of one object occur unavoidably —
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf 𝒪 h𝒪 F G` versus
`(sheafify 𝒪 h𝒪).obj (F.val ⊗ G.val)`, and `(structureSheaf 𝒪 h𝒪).obj` versus
`structureRingPresheaf 𝒪`, at which `toSheafify` is declared — and each pair is definitionally
equal at default transparency but not at the *reducible* transparency at which `rw`, `simp only`
and `conv` check their motives. So `tensorSheafIsoTensorObj_hom_whiskerRight` is a `calc` chain of
`exact`s whose steps are `CategoryTheory.whisker_eq`, `CategoryTheory.eq_whisker` and
`CategoryTheory.Category.assoc`, each of which fixes its own spelling, and
`toTensorSection_comp_whiskerRight_val` is an `Eq.trans` of two such whiskerings. Re-bracketing is
free, composition of morphisms of presheaves of modules and `SheafOfModules.Hom.val` of a
composite being `rfl` here.

**The scheme-level statement is one `congrArg`.** The whiskering `f.val ▷ G.val` of presheaves of
modules is Mathlib's, the monoidal structure being
`Stacks.SheafOfModules.monoidalCategoryPresheafOfModules`, which is `inferInstance` for it; so by
`PresheafOfModules.Monoidal.whiskerRight_app` and
`ModuleCat.MonoidalCategory.whiskerRight_apply`, both `rfl`, it sends `m ⊗ₜ n` to
`f.val.app U m ⊗ₜ n`. And `Stacks.SectionTensorFormula.tensorSection F G m n` is by definition
`((toTensorSection X.presheaf _ F G).app (op U)).hom (m ⊗ₜ n)`. So evaluating
`toTensorSection_comp_whiskerRight_val` at `Opposite.op U` and at `m ⊗ₜ n` *is* the statement, and
no rewriting of the elementwise formula is needed. The `congrArg` motive must be ascribed in the
`Stacks.SectionProduct.forgetFun` spelling rather than the `.val` one: `F.val ⊗ G.val`
fails to elaborate there, because `F.val` has type `PresheafOfModules X.ringCatSheaf.obj` and the
monoidal structure on presheaves of modules is declared at `(structureSheaf 𝒪 h𝒪).obj`, which
instance search does not unfold to it — so the `⊗` falls through to `TensorProduct`'s. This is the
same spelling problem the implementation notes of
`StacksFrontier/AlgebraicGeometry/TensorSheafSpellingIso/Basic.lean` record, and `forgetFun` is that
right adjoint written as a functor, whose codomain carries the spelling the instance is keyed on.

**The bridge needs no comparison morphism.** `Stacks.SheafOfModules.Tensor.sheafTensor` is the
sheafification of `PresheafOfModules.tensorObj` of the underlying presheaves, which is the same
tensor product as the hand-built presheaf the ringed-space theory once used — see
`Stacks.TensorSheafDedup.presheafTensor_eq_monoidalTensorObj`. What is *not* an identity is the
monoidal `⊗` of `Stacks.SheafInternalHom.schemeMonoidalCategory`, which is a localization; that
difference is exactly `Stacks.TensorSheafSpellingIso.monoidalTensorIso`, and the bridge below is
that isomorphism with its target's ring-sheaf argument restated.

**Why the naturality is not `monoidalTensorIso_naturality` verbatim.**
`Stacks.TensorSheafSpellingIso.monoidalTensorIso_naturality` is stated against
`CategoryTheory.Functor.uncurry` of the bifunctor, whose action on `(f, 𝟙 B)` is
`((sheafTensor _).map f).app B ≫ ((sheafTensor _).obj A').map (𝟙 B)`. The trailing factor is the
functorial image of an identity, which is *not* an identity by `rfl`; collapsing it is one
`CategoryTheory.Functor.map_id` and one `CategoryTheory.Category.comp_id`, done below as a term
so that no motive has to be checked at reducible transparency.

## References

* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)

## What is not done

No `@[stacks]` attribute is attached: this is infrastructure, and nothing here is an assertion of
a Stacks tag. Naturality of the bridge in its *second* variable is not stated, only in the first, which
is what the consumer needs; and no statement here says that the section comparison is injective or
surjective over any particular open.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite Stacks.SheafOfModules.TensorSheafification
open Stacks.SheafOfModules (sheafifyValIso)
open scoped TensorProduct

universe w v u

namespace Stacks.SectionTensorFormula

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-! ### Naturality in the first variable -/

section Left

variable {F F' : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
  (G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- **Naturality of `tensorSheafIsoTensorObj` in its first variable**, which is the sheaf-level
half of the naturality of the comparison on sections. It is the naturality of the tensorator
together with the naturality of the counit; no coherence of the localized monoidal structure is
used. This is the mirror image of
`Stacks.SectionTensorFormula.tensorSheafIsoTensorObj_hom_whiskerLeft`. -/
theorem tensorSheafIsoTensorObj_hom_whiskerRight (f : F ⟶ F') :
    (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom ≫ f ▷ G =
      ((sheafify 𝒪 h𝒪).map (f.val ▷ G.val) :
          ((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
                (forget₂ CommRingCat RingCat) h𝒪⟩).obj F).obj G ⟶
            ((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪
                (forget₂ CommRingCat RingCat) h𝒪⟩).obj F').obj G) ≫
        (tensorSheafIsoTensorObj 𝒪 h𝒪 F' G).hom := by
  have hmid : ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) ≫ f ▷ G =
      ((sheafify 𝒪 h𝒪).map f.val ▷ (sheafify 𝒪 h𝒪).obj G.val) ≫
        ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) := by
    rw [← MonoidalCategory.tensorHom_id, ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, sheafifyCounit_naturality]
  exact calc Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) ≫ f ▷ G
      = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafify 𝒪 h𝒪).map f.val ▷ (sheafify 𝒪 h𝒪).obj G.val) ≫
            ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) :=
        whisker_eq (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val) hmid
    _ = (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafify 𝒪 h𝒪).map f.val ▷ (sheafify 𝒪 h𝒪).obj G.val)) ≫
            ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) :=
        (Category.assoc _ _ _).symm
    _ = ((sheafify 𝒪 h𝒪).map (f.val ▷ G.val) ≫
          Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F'.val G.val) ≫
            ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) :=
        eq_whisker (Functor.OplaxMonoidal.δ_natural_left (sheafify 𝒪 h𝒪) f.val G.val)
          ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom)
    _ = (sheafify 𝒪 h𝒪).map (f.val ▷ G.val) ≫
          Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F'.val G.val ≫
            ((sheafifyValIso 𝒪 h𝒪 F').hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) := Category.assoc _ _ _

/-- **Naturality of the section comparison in its first variable**, the mirror image of
`Stacks.SectionTensorFormula.toTensorSection_comp_whiskerLeft_val`. -/
theorem toTensorSection_comp_whiskerRight_val (f : F ⟶ F') :
    toTensorSection 𝒪 h𝒪 F G ≫ (f ▷ G).val =
      (f.val ▷ G.val) ≫ toTensorSection 𝒪 h𝒪 F' G :=
  have hunit : toSheafify 𝒪 h𝒪 (F.val ⊗ G.val) ≫ ((sheafify 𝒪 h𝒪).map (f.val ▷ G.val)).val =
      (f.val ▷ G.val) ≫ toSheafify 𝒪 h𝒪 (F'.val ⊗ G.val) :=
    ((sheafifyAdjunction 𝒪 h𝒪).unit.naturality (f.val ▷ G.val)).symm
  have hstep : (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom.val ≫ (f ▷ G).val =
      ((sheafify 𝒪 h𝒪).map (f.val ▷ G.val)).val ≫
        (tensorSheafIsoTensorObj 𝒪 h𝒪 F' G).hom.val :=
    congrArg SheafOfModules.Hom.val (tensorSheafIsoTensorObj_hom_whiskerRight 𝒪 h𝒪 G f)
  (whisker_eq (toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)) hstep).trans
    (eq_whisker hunit (tensorSheafIsoTensorObj 𝒪 h𝒪 F' G).hom.val)

end Left

end Stacks.SectionTensorFormula

/-! ### Naturality on sections, over a scheme -/

namespace Stacks.SectionTensorFormula

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open Stacks.SectionProduct (forgetFun)

variable {X : Scheme.{u}}

/-- **The product of sections is natural in its first factor.** For `f : F ⟶ F'` a morphism of
`𝒪_X`-modules, the image under `f ▷ G` of the product of a section `m` of `F` over `U` with a
section `n` of `G` over `U` is the product of `f(m)` with `n`.

This is `Stacks.SectionTensorFormula.toTensorSection_comp_whiskerRight_val` evaluated at
`Opposite.op U` and at the elementary tensor `m ⊗ₜ n`; the presheaf-level whiskering sends
`m ⊗ₜ n` to `f.val.app U m ⊗ₜ n` by `rfl`, the monoidal structure on presheaves of modules being
Mathlib's. -/
theorem tensorSection_whiskerRight {F F' G : X.Modules} (f : F ⟶ F') {U : X.Opens}
    (m : Γ(F, U)) (n : Γ(G, U)) :
    (f ▷ G).app U (tensorSection F G m n) = tensorSection F' G (f.app U m) n :=
  congrArg
    (fun α : (forgetFun X).obj F ⊗ (forgetFun X).obj G ⟶ (forgetFun X).obj (F' ⊗ G) =>
      α.app (op U) (m ⊗ₜ[Γ(X, U)] n))
    (toTensorSection_comp_whiskerRight_val X.presheaf (schemeSheafCondition X) G f)

end Stacks.SectionTensorFormula

/-! ### The monoidal product as a value of `sheafTensor` -/

namespace Stacks.TensorSheafSpellingIso

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable (X : Scheme.{u})

/-- **The monoidal product of `X.Modules` is a value of the bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`.** This is
`Stacks.TensorSheafSpellingIso.monoidalTensorIso` with the ring sheaf of its target written
`X.toRingedSpace.sheaf` rather than `⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩`, which
is the spelling the tensor product of complexes of sheaves of modules is written over. The two
are equal, so this is a restatement rather than a construction. -/
def monoidalTensorSheafTensorIso (A B : X.Modules) :
    A ⊗ B ≅ ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).obj A).obj B :=
  monoidalTensorIso X A B

/-- **`monoidalTensorSheafTensorIso` is natural in its first variable**, against the action of
`Stacks.SheafOfModules.Tensor.sheafTensor` on morphisms. This is
`Stacks.TensorSheafSpellingIso.monoidalTensorIso_naturality` at `(f, 𝟙 B)`, with
`MonoidalCategory.tensorHom_id` turning the tensor product of morphisms into the whiskering on
the left, and `huncurry` below — `Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` against
`Stacks.SheafOfModules.Tensor.sheafTensor_map_app` — collapsing the uncurried bifunctor's action
on `(f, 𝟙 B)` to the whiskering on the right. -/
theorem monoidalTensorSheafTensorIso_naturality_left {A A' : X.Modules} (f : A ⟶ A')
    (B : X.Modules) :
    (f ▷ B) ≫ (monoidalTensorSheafTensorIso X A' B).hom =
      (monoidalTensorSheafTensorIso X A B).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf).map f).app B :=
  have huncurry := (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
      X.toRingedSpace.sheaf f (𝟙 B)).trans
    (Stacks.SheafOfModules.Tensor.sheafTensor_map_app X.toRingedSpace.sheaf f B).symm
  ((eq_whisker (MonoidalCategory.tensorHom_id f B)
        (monoidalTensorSheafTensorIso X A' B).hom).symm.trans
      (monoidalTensorIso_naturality X f (𝟙 B))).trans
    (whisker_eq (monoidalTensorSheafTensorIso X A B).hom huncurry)

end Stacks.TensorSheafSpellingIso

end
