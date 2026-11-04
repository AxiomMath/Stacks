module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import StacksFrontier.AlgebraicGeometry.SectionTensorFormula.Scheme
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalTensorBridge

/-!
# A section-level formula for multiplication by a global section

For `F` and `G` two `𝒪_X`-modules on a scheme and `f : 𝟙_ X.Modules ⟶ G` a global section of `G`,
`Stacks.TensorSectionNonvanishing.mulSec F f m` is the product of a section `m` of `F` over an
open `U` with that global section, built by whiskering `f` by `F` and reading the right unitor; and
`Stacks.SectionTensorFormula.tensorSection F G m n` is the image of the elementary tensor
`m ⊗ₜ n` under `Stacks.SectionTensorFormula.toTensorSection`. **The two were not related.** This
file relates them:

  `mulSec F f m = tensorSection F G m (f|_U)`.

The "What is not done" of `StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/Basic.lean`
names exactly the two missing inputs — *"naturality of `toTensorSection` in its second variable,
and the formula for it against the right unitor at `G = 𝟙_ X.Modules`"* — and the "Why this does
not need a formula for the monoidal comparison" of
`StacksFrontier/AlgebraicGeometry/SectionProduct/BijStalk.lean` records the same two. Both are proved
here, at the generality of an arbitrary ringed site, and then composed on a scheme.

## Main definitions

* `Stacks.SectionProduct.monoidalUnitSection`: the canonical section of `𝟙_ X.Modules` over an
  open, the image of `1` under the sheafification unit.

## Main results

* `Stacks.SectionTensorFormula.toTensorSection_comp_whiskerLeft_val`: **naturality of the
  comparison in its second variable.** For `g : G ⟶ H`,
  `toTensorSection 𝒪 h𝒪 F G ≫ (F ◁ g).val = (F.val ◁ g.val) ≫ toTensorSection 𝒪 h𝒪 F H`.
* `Stacks.SectionTensorFormula.toTensorSection_unit_comp_rightUnitor_val`: **the value against
  the right unitor.** Composing the comparison at `G = 𝟙_` with the sheaf right unitor, after
  tensoring on the left with the sheafification unit of the presheaf unit, is the *presheaf* right
  unitor.
* `Stacks.SectionTensorFormula.toTensorSection_whiskerLeft_toSheafify`: the comparison against a
  sheafified second variable, which is what the unitor statement is the `𝟙_` case of.
* `Stacks.SectionTensorFormula.rightUnitor_inv_val_eq` and
  `Stacks.SectionTensorFormula.mulRight_val_eq`: **the section-level formula for the twisted
  multiplication map** as an equality of morphisms of presheaves of modules.
* `Stacks.SectionProduct.mulSec_eq_tensorSection` and
  `Stacks.SectionProduct.mulSec_eq_tensorSection_globalSection`: **the identification**, with the
  second factor written first as the value of `f` on the unit section over `U` and then as the
  restriction to `U` of the global section of `f`.

## Implementation notes

**Why the proofs are terms and not rewrites.** Three spellings of one object occur unavoidably:
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf 𝒪 h𝒪 F G` versus
`(sheafify 𝒪 h𝒪).obj (F.val ⊗ G.val)`, `(structureSheaf 𝒪 h𝒪).obj` versus
`structureRingPresheaf 𝒪` — `Stacks.SheafOfModules.TensorSheafification.toSheafify` is declared at
the second — and `𝟙_ (SheafOfModules _)` versus `(sheafify 𝒪 h𝒪).obj (𝟙_ (PresheafOfModules _))`.
Each pair is definitionally equal at default transparency and none is equal at the *reducible*
transparency at which `rw`, `simp only` and `conv` check their motives; for instance `rw
[Category.assoc]` against a goal that plainly contains `(f ≫ g) ≫ h` reports "Did not find an
occurrence of the pattern", with the explanation that the argument `P` "has type
`PresheafOfModules (structureSheaf 𝒪 h𝒪).obj` but is expected to have type
`PresheafOfModules (structureRingPresheaf 𝒪)`". So every step below is an `exact` of a declaration
whose own type fixes the spelling, chained with `Eq.trans`, `CategoryTheory.whisker_eq` and
`CategoryTheory.eq_whisker`. This is the technique of
`StacksFrontier/AlgebraicGeometry/SectionProduct/MonoidalUnitBridge.lean`.

**Re-bracketing is free.** Composition of morphisms of presheaves of modules, of sheaves of
modules, and `SheafOfModules.Hom.val` of a composite are all equal by `rfl` here, so
the chains below never need an associativity step, and a `calc` whose two sides differ only in
bracketing is discharged by the next lemma in line.

**The counit is taken in the `Stacks.SheafOfModules.sheafifyValIso` spelling.** The counit of
sheafification at a sheaf of modules is `(Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).app F`,
whose source is written through the composite functor
`SheafOfModules.forget ⋙ PresheafOfModules.restrictScalars (𝟙 _)`, and it is the same morphism as
`(Stacks.SheafOfModules.sheafifyValIso 𝒪 h𝒪 F).hom`, whose type writes that source as
`(sheafify 𝒪 h𝒪).obj F.val` instead. The second is the spelling used below, because it is what
makes `tensorSheafIsoTensorObj_hom_eq` a single-spelling statement and hence `rfl`.

**The monoidal unit of the sheaves is the sheafification of the presheaf unit by `rfl`**, the
monoidal structure being a localization with `ε = Iso.refl`; and for the same reason
`Functor.OplaxMonoidal.η (sheafify 𝒪 h𝒪)` is the identity by `rfl`. Those two facts are what let
`Functor.OplaxMonoidal.right_unitality_hom` be used at `𝟙_`, in `δ_comp_rightUnitor_hom`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)

## What is not done

No `@[stacks]` attribute is attached: this is infrastructure, and nothing here is an assertion of
a tagged statement. The comparison is still not claimed to be injective or surjective over any particular
open — `mulSec_eq_tensorSection` identifies two maps, it does not say that either is onto
`Γ(F ⊗ G, U)`.

**Multiplication by a *local* trivialising section is not shown to be surjective on sections over
a fixed open**, and that — not either of the two facts proved here — is what generalising
`Stacks.Tag0C6KZeroSchemeAnnihilation.ker_annihilates` to a non-invertible source needs. The
missing statement is `(F ⊗ G)|_U ≅ F|_U ⊗ G|_U`, recorded as unproved and "not cheap" in the "What
is not done" of `StacksFrontier/AlgebraicGeometry/SectionTensorFormula/Scheme.lean`, equivalently the
monoidal structure on `SheafOfModules.overFunctor` recorded in
`StacksFrontier/AlgebraicGeometry/TwistTensor/Basic.lean`.
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

/-! ### The counit of sheafification -/

/-- The counit of sheafification is natural. -/
theorem sheafifyCounit_naturality {G H : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (g : G ⟶ H) :
    (sheafify 𝒪 h𝒪).map g.val ≫ (sheafifyValIso 𝒪 h𝒪 H).hom = (sheafifyValIso 𝒪 h𝒪 G).hom ≫ g :=
  (Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).hom.naturality g

/-- **The right triangle identity**: the sheafification unit at the underlying presheaf of a
sheaf, followed by the counit, is the identity. -/
theorem toSheafify_comp_sheafifyCounit_val (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    toSheafify 𝒪 h𝒪 F.val ≫ (sheafifyValIso 𝒪 h𝒪 F).hom.val = 𝟙 F.val :=
  (sheafifyAdjunction 𝒪 h𝒪).right_triangle_components F

/-- **The left triangle identity**: the sheafification of the unit at a presheaf, followed by the
counit at its sheafification, is the identity. -/
theorem map_toSheafify_comp_sheafifyCounit
    (P : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj) :
    (sheafify 𝒪 h𝒪).map (toSheafify 𝒪 h𝒪 P) ≫
        (sheafifyValIso 𝒪 h𝒪 ((sheafify 𝒪 h𝒪).obj P)).hom = 𝟙 ((sheafify 𝒪 h𝒪).obj P) :=
  (sheafifyAdjunction 𝒪 h𝒪).left_triangle_components P

/-- `Stacks.SectionTensorFormula.tensorSheafIsoTensorObj` unfolded: the comparison of the
sheafified sectionwise tensor product with the localized monoidal product is the inverse
tensorator of sheafification followed by the two counits. True by `rfl`, the whole point being
that both sides are written in one spelling. -/
theorem tensorSheafIsoTensorObj_hom_eq (F G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom =
      Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
        ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) := rfl

/-- **The inverse tensorator of sheafification against the right unitor.** This is Mathlib's
`Functor.OplaxMonoidal.right_unitality_hom` at `sheafify 𝒪 h𝒪`, with the whiskered
`Functor.OplaxMonoidal.η` deleted: the monoidal structure on sheaves of modules is a localization
with `ε = Iso.refl`, so that `η` is the identity. -/
theorem δ_comp_rightUnitor_hom (P : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj) :
    Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) P
          (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
        (ρ_ ((sheafify 𝒪 h𝒪).obj P)).hom = (sheafify 𝒪 h𝒪).map (ρ_ P).hom :=
  calc Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) P
          (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
        (ρ_ ((sheafify 𝒪 h𝒪).obj P)).hom
      = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) P
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
          𝟙 ((sheafify 𝒪 h𝒪).obj P ⊗
              𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) ≫
            (ρ_ ((sheafify 𝒪 h𝒪).obj P)).hom :=
        (whisker_eq _ (Category.id_comp (ρ_ ((sheafify 𝒪 h𝒪).obj P)).hom)).symm
    _ = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) P
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
          ((sheafify 𝒪 h𝒪).obj P ◁ Functor.OplaxMonoidal.η (sheafify 𝒪 h𝒪)) ≫
            (ρ_ ((sheafify 𝒪 h𝒪).obj P)).hom :=
        whisker_eq _ (eq_whisker (MonoidalCategory.whiskerLeft_id
          ((sheafify 𝒪 h𝒪).obj P) (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)))).symm
            (ρ_ ((sheafify 𝒪 h𝒪).obj P)).hom)
    _ = (sheafify 𝒪 h𝒪).map (ρ_ P).hom :=
        Functor.OplaxMonoidal.right_unitality_hom (sheafify 𝒪 h𝒪) P

/-- **The inverse of the sheafification counit on underlying presheaves is the sheafification
unit.** Both are maps `F.val ⟶ ((sheafify 𝒪 h𝒪).obj F.val).val`, and the two triangle identities
of the adjunction identify them. -/
theorem sheafifyCounit_inv_val (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    ((Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).app F).inv.val = toSheafify 𝒪 h𝒪 F.val :=
  have hiv : (sheafifyValIso 𝒪 h𝒪 F).hom.val ≫
      ((Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).app F).inv.val =
      𝟙 ((sheafify 𝒪 h𝒪).obj F.val).val :=
    congrArg SheafOfModules.Hom.val
      ((Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).app F).hom_inv_id
  ((Category.id_comp _).symm.trans
      (eq_whisker (toSheafify_comp_sheafifyCounit_val 𝒪 h𝒪 F).symm
        ((Stacks.SheafInternalHom.sheafifyCounitIso 𝒪 h𝒪).app F).inv.val)).trans
    ((whisker_eq (toSheafify 𝒪 h𝒪 F.val) hiv).trans (Category.comp_id _))

/-! ### Naturality in the second variable -/

/-- The sheafification unit is natural, on underlying presheaves. -/
private theorem toSheafify_comp_map_val {P Q : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj}
    (g : P ⟶ Q) :
    toSheafify 𝒪 h𝒪 P ≫ ((sheafify 𝒪 h𝒪).map g).val = g ≫ toSheafify 𝒪 h𝒪 Q :=
  ((sheafifyAdjunction 𝒪 h𝒪).unit.naturality g).symm

section Right

variable (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  {G H : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}

/-- **Naturality of `tensorSheafIsoTensorObj` in its second variable**, which is the sheaf-level
half of the naturality of the comparison on sections. It is the naturality of the tensorator
together with the naturality of the counit; no coherence of the localized monoidal structure is
used. -/
theorem tensorSheafIsoTensorObj_hom_whiskerLeft (g : G ⟶ H) :
    (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom ≫ F ◁ g =
      ((sheafify 𝒪 h𝒪).map (F.val ◁ g.val) :
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
            (F)).obj (G)) ⟶
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
            (F)).obj (H))) ≫
        (tensorSheafIsoTensorObj 𝒪 h𝒪 F H).hom := by
  have hmid : ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) ≫ F ◁ g =
      ((sheafify 𝒪 h𝒪).obj F.val ◁ (sheafify 𝒪 h𝒪).map g.val) ≫
        ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 H).hom) := by
    rw [tensorHom_comp_whiskerLeft, whiskerLeft_comp_tensorHom, sheafifyCounit_naturality]
  exact calc Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 G).hom) ≫ F ◁ g
      = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafify 𝒪 h𝒪).obj F.val ◁ (sheafify 𝒪 h𝒪).map g.val) ≫
            ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 H).hom) :=
        whisker_eq (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val) hmid
    _ = (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val G.val ≫
          ((sheafify 𝒪 h𝒪).obj F.val ◁ (sheafify 𝒪 h𝒪).map g.val)) ≫
            ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 H).hom) :=
        (Category.assoc _ _ _).symm
    _ = ((sheafify 𝒪 h𝒪).map (F.val ◁ g.val) ≫
          Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val H.val) ≫
            ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 H).hom) :=
        eq_whisker (Functor.OplaxMonoidal.δ_natural_right (sheafify 𝒪 h𝒪) F.val g.val)
          ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 H).hom)
    _ = (sheafify 𝒪 h𝒪).map (F.val ◁ g.val) ≫
          Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val H.val ≫
            ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 H).hom) := Category.assoc _ _ _

/-- **Naturality of the section comparison in its second variable.** -/
theorem toTensorSection_comp_whiskerLeft_val (g : G ⟶ H) :
    toTensorSection 𝒪 h𝒪 F G ≫ (F ◁ g).val =
      (F.val ◁ g.val) ≫ toTensorSection 𝒪 h𝒪 F H :=
  have hstep : (tensorSheafIsoTensorObj 𝒪 h𝒪 F G).hom.val ≫ (F ◁ g).val =
      ((sheafify 𝒪 h𝒪).map (F.val ◁ g.val)).val ≫
        (tensorSheafIsoTensorObj 𝒪 h𝒪 F H).hom.val :=
    congrArg SheafOfModules.Hom.val (tensorSheafIsoTensorObj_hom_whiskerLeft 𝒪 h𝒪 F g)
  (whisker_eq (toSheafify 𝒪 h𝒪 (F.val ⊗ G.val)) hstep).trans
    (eq_whisker (toSheafify_comp_map_val 𝒪 h𝒪 (F.val ◁ g.val))
      (tensorSheafIsoTensorObj 𝒪 h𝒪 F H).hom.val)

end Right

/-! ### The second variable a sheafification -/

section Sheafify

variable (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  (P : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)

/-- **`tensorSheafIsoTensorObj` against a sheafified second variable.** The left triangle
identity collapses the second counit, leaving a whiskering. -/
theorem map_whiskerLeft_toSheafify_comp_tensorSheafIsoTensorObj_hom :
    ((sheafify 𝒪 h𝒪).map (F.val ◁ toSheafify 𝒪 h𝒪 P) :
        (sheafify 𝒪 h𝒪).obj (F.val ⊗ P) ⟶
          (((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
            (F)).obj (((sheafify 𝒪 h𝒪).obj P)))) ≫
        (tensorSheafIsoTensorObj 𝒪 h𝒪 F ((sheafify 𝒪 h𝒪).obj P)).hom =
      Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val P ≫
        ((sheafifyValIso 𝒪 h𝒪 F).hom ▷ (sheafify 𝒪 h𝒪).obj P) :=
  have hmid : ((sheafify 𝒪 h𝒪).obj F.val ◁ (sheafify 𝒪 h𝒪).map (toSheafify 𝒪 h𝒪 P)) ≫
      ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 ((sheafify 𝒪 h𝒪).obj P)).hom) =
      (sheafifyValIso 𝒪 h𝒪 F).hom ▷ (sheafify 𝒪 h𝒪).obj P :=
    (whiskerLeft_comp_tensorHom _ _ _).trans
      ((congrArg ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ ·)
        (map_toSheafify_comp_sheafifyCounit 𝒪 h𝒪 P)).trans (tensorHom_id _ _))
  calc (sheafify 𝒪 h𝒪).map (F.val ◁ toSheafify 𝒪 h𝒪 P) ≫
          Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val ((sheafify 𝒪 h𝒪).obj P).val ≫
            ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 ((sheafify 𝒪 h𝒪).obj P)).hom)
      = ((sheafify 𝒪 h𝒪).map (F.val ◁ toSheafify 𝒪 h𝒪 P) ≫
          Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val ((sheafify 𝒪 h𝒪).obj P).val) ≫
            ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 ((sheafify 𝒪 h𝒪).obj P)).hom) :=
        (Category.assoc _ _ _).symm
    _ = (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val P ≫
          ((sheafify 𝒪 h𝒪).obj F.val ◁ (sheafify 𝒪 h𝒪).map (toSheafify 𝒪 h𝒪 P))) ≫
            ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 ((sheafify 𝒪 h𝒪).obj P)).hom) :=
        eq_whisker (Functor.OplaxMonoidal.δ_natural_right (sheafify 𝒪 h𝒪) F.val
            (toSheafify 𝒪 h𝒪 P)).symm
          ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 ((sheafify 𝒪 h𝒪).obj P)).hom)
    _ = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val P ≫
          ((sheafify 𝒪 h𝒪).obj F.val ◁ (sheafify 𝒪 h𝒪).map (toSheafify 𝒪 h𝒪 P)) ≫
            ((sheafifyValIso 𝒪 h𝒪 F).hom ⊗ₘ (sheafifyValIso 𝒪 h𝒪 ((sheafify 𝒪 h𝒪).obj P)).hom) :=
        Category.assoc _ _ _
    _ = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val P ≫
          ((sheafifyValIso 𝒪 h𝒪 F).hom ▷ (sheafify 𝒪 h𝒪).obj P) :=
        whisker_eq (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val P) hmid

/-- **The section comparison against a sheafified second variable.** -/
theorem toTensorSection_whiskerLeft_toSheafify :
    (F.val ◁ toSheafify 𝒪 h𝒪 P) ≫ toTensorSection 𝒪 h𝒪 F ((sheafify 𝒪 h𝒪).obj P) =
      toSheafify 𝒪 h𝒪 (F.val ⊗ P) ≫
        (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val P ≫
          ((sheafifyValIso 𝒪 h𝒪 F).hom ▷ (sheafify 𝒪 h𝒪).obj P)).val :=
  have hstep : ((sheafify 𝒪 h𝒪).map (F.val ◁ toSheafify 𝒪 h𝒪 P) :
          (sheafify 𝒪 h𝒪).obj (F.val ⊗ P) ⟶
            (((Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ (𝒪) (forget₂ CommRingCat RingCat) (h𝒪)⟩).obj
              (F)).obj (((sheafify 𝒪 h𝒪).obj P)))).val ≫
        (tensorSheafIsoTensorObj 𝒪 h𝒪 F ((sheafify 𝒪 h𝒪).obj P)).hom.val =
      (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val P ≫
        ((sheafifyValIso 𝒪 h𝒪 F).hom ▷ (sheafify 𝒪 h𝒪).obj P)).val :=
    (SheafOfModules.comp_val _ _).symm.trans
      (congrArg SheafOfModules.Hom.val
        (map_whiskerLeft_toSheafify_comp_tensorSheafIsoTensorObj_hom 𝒪 h𝒪 F P))
  (eq_whisker (toSheafify_comp_map_val 𝒪 h𝒪 (F.val ◁ toSheafify 𝒪 h𝒪 P)).symm
      (tensorSheafIsoTensorObj 𝒪 h𝒪 F ((sheafify 𝒪 h𝒪).obj P)).hom.val).trans
    (whisker_eq (toSheafify 𝒪 h𝒪 (F.val ⊗ P)) hstep)

end Sheafify

/-! ### The value against the right unitor -/

section Unit

variable (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- The sheaf-level half of the value against the right unitor: naturality of the right unitor
moves the counit past it, and `δ_comp_rightUnitor_hom` finishes. -/
theorem δ_comp_whiskerRight_counit_comp_rightUnitor :
    (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val
          (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
        ((sheafifyValIso 𝒪 h𝒪 F).hom ▷ (sheafify 𝒪 h𝒪).obj
          (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)))) ≫ (ρ_ F).hom =
      (sheafify 𝒪 h𝒪).map (ρ_ F.val).hom ≫ (sheafifyValIso 𝒪 h𝒪 F).hom :=
  calc (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
          ((sheafifyValIso 𝒪 h𝒪 F).hom ▷ (sheafify 𝒪 h𝒪).obj
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)))) ≫ (ρ_ F).hom
      = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
          ((sheafifyValIso 𝒪 h𝒪 F).hom ▷ (sheafify 𝒪 h𝒪).obj
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj))) ≫ (ρ_ F).hom :=
        Category.assoc _ _ _
    _ = Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
          (ρ_ ((sheafify 𝒪 h𝒪).obj F.val)).hom ≫ (sheafifyValIso 𝒪 h𝒪 F).hom :=
        whisker_eq _ (MonoidalCategory.rightUnitor_naturality ((sheafifyValIso 𝒪 h𝒪 F).hom))
    _ = (Functor.OplaxMonoidal.δ (sheafify 𝒪 h𝒪) F.val
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫
          (ρ_ ((sheafify 𝒪 h𝒪).obj F.val)).hom) ≫ (sheafifyValIso 𝒪 h𝒪 F).hom :=
        (Category.assoc _ _ _).symm
    _ = (sheafify 𝒪 h𝒪).map (ρ_ F.val).hom ≫ (sheafifyValIso 𝒪 h𝒪 F).hom :=
        eq_whisker (δ_comp_rightUnitor_hom 𝒪 h𝒪 F.val) ((sheafifyValIso 𝒪 h𝒪 F).hom)

/-- **The value of the section comparison against the right unitor.** -/
theorem toTensorSection_unit_comp_rightUnitor_val :
    (F.val ◁ toSheafify 𝒪 h𝒪 (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj))) ≫
        toTensorSection 𝒪 h𝒪 F (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) ≫
          (ρ_ F).hom.val = (ρ_ F.val).hom :=
  (eq_whisker (toTensorSection_whiskerLeft_toSheafify 𝒪 h𝒪 F
          (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj))) (ρ_ F).hom.val).trans
    ((whisker_eq (toSheafify 𝒪 h𝒪
          (F.val ⊗ 𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)))
        (congrArg SheafOfModules.Hom.val
          (δ_comp_whiskerRight_counit_comp_rightUnitor 𝒪 h𝒪 F))).trans
      ((eq_whisker (toSheafify_comp_map_val 𝒪 h𝒪 (ρ_ F.val).hom)
          (sheafifyValIso 𝒪 h𝒪 F).hom.val).trans
        ((whisker_eq (ρ_ F.val).hom (toSheafify_comp_sheafifyCounit_val 𝒪 h𝒪 F)).trans
          (Category.comp_id (ρ_ F.val).hom))))

end Unit

/-! ### Multiplication by a global section, on underlying presheaves -/

section MulRight

variable (F : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))

/-- **The inverse right unitor of `SheafOfModules` on underlying presheaves.** -/
theorem rightUnitor_inv_val_eq :
    (ρ_ F).inv.val =
      (ρ_ F.val).inv ≫
        (F.val ◁ toSheafify 𝒪 h𝒪 (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj))) ≫
          toTensorSection 𝒪 h𝒪 F (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) :=
  have h1 : (ρ_ F.val).inv ≫
      (F.val ◁ toSheafify 𝒪 h𝒪 (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj))) ≫
        toTensorSection 𝒪 h𝒪 F (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))) ≫
          (ρ_ F).hom.val = 𝟙 F.val :=
    (whisker_eq (ρ_ F.val).inv
      (toTensorSection_unit_comp_rightUnitor_val 𝒪 h𝒪 F)).trans (ρ_ F.val).inv_hom_id
  have hinv : (ρ_ F).hom.val ≫ (ρ_ F).inv.val =
      𝟙 (F ⊗ 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))).val :=
    congrArg SheafOfModules.Hom.val (ρ_ F).hom_inv_id
  (((Category.comp_id _).symm.trans (whisker_eq _ hinv.symm)).trans
    ((eq_whisker h1 (ρ_ F).inv.val).trans (Category.id_comp (ρ_ F).inv.val))).symm

/-- **The section-level formula for the twisted multiplication map.** Multiplication by a
morphism `f` out of the monoidal unit is, on underlying presheaves, the inverse presheaf right
unitor followed by tensoring on the left with `f` read through the sheafification unit, followed
by the section comparison. -/
theorem mulRight_val_eq {G : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)}
    (f : 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ G) :
    ((ρ_ F).inv ≫ F ◁ f).val =
      (ρ_ F.val).inv ≫
        (F.val ◁ (toSheafify 𝒪 h𝒪
            (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫ f.val)) ≫
          toTensorSection 𝒪 h𝒪 F G :=
  have hlast : (F.val ◁ toSheafify 𝒪 h𝒪
          (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj))) ≫
        (F.val ◁ f.val) ≫ toTensorSection 𝒪 h𝒪 F G =
      (F.val ◁ (toSheafify 𝒪 h𝒪
          (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)) ≫ f.val)) ≫
        toTensorSection 𝒪 h𝒪 F G :=
    eq_whisker (MonoidalCategory.whiskerLeft_comp F.val
      (toSheafify 𝒪 h𝒪 (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj))) f.val).symm
        (toTensorSection 𝒪 h𝒪 F G)
  (eq_whisker (rightUnitor_inv_val_eq 𝒪 h𝒪 F) (F ◁ f).val).trans
    (whisker_eq (ρ_ F.val).inv
      ((whisker_eq (F.val ◁ toSheafify 𝒪 h𝒪
          (𝟙_ (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj)))
        (toTensorSection_comp_whiskerLeft_val 𝒪 h𝒪 F f)).trans hlast))

end MulRight

end Stacks.SectionTensorFormula

/-! ### The formula on sections, over a scheme -/

namespace Stacks.SectionProduct

open Stacks.SectionTensorFormula

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {X : Scheme.{u}}

/-- **The canonical section of the monoidal unit over an open.** The monoidal unit of `X.Modules`
is the sheafification of the presheaf unit, whose sections over `U` are `Γ(X, U)`; this is the
image of `1` under the sheafification unit. -/
def monoidalUnitSection (X : Scheme.{u}) (U : X.Opens) : Γ(𝟙_ X.Modules, U) :=
  (toSheafify X.presheaf (schemeSheafCondition X)
    (𝟙_ (PresheafOfModules.{u}
      (structureSheaf X.presheaf (schemeSheafCondition X)).obj))).app (op U) (1 : Γ(X, U))

/-- **The product of a section with a global section is the sectionwise tensor product.**
`Stacks.TensorSectionNonvanishing.mulSec F f m` — the section of `F ⊗ G` obtained by multiplying
a section `m` of `F` over `U` by a global section `f` of `G` — is
`Stacks.SectionTensorFormula.tensorSection` of `m` with the section of `G` over `U` carried by
`f`. This is the identification the "What is not done" of
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/Basic.lean` records as missing, and the
two inputs it names are `Stacks.SectionTensorFormula.toTensorSection_comp_whiskerLeft_val` and
`Stacks.SectionTensorFormula.toTensorSection_unit_comp_rightUnitor_val`. -/
theorem mulSec_eq_tensorSection (F G : X.Modules) (f : 𝟙_ X.Modules ⟶ G) {U : X.Opens}
    (m : Γ(F, U)) :
    Stacks.TensorSectionNonvanishing.mulSec F f m =
      tensorSection F G m (f.app U (monoidalUnitSection X U)) :=
  have hval : Stacks.TensorSectionNonvanishing.mulSec F f m =
      (toTensorSection X.presheaf (schemeSheafCondition X) F G).app (op U)
        (((forgetFun X).obj F ◁ (toSheafify X.presheaf (schemeSheafCondition X)
          (𝟙_ (PresheafOfModules.{u}
            (structureSheaf X.presheaf (schemeSheafCondition X)).obj)) ≫ f.val)).app (op U)
          ((ρ_ ((forgetFun X).obj F)).inv.app (op U) m)) :=
    congrArg
      (fun α : (forgetFun X).obj F ⟶ (forgetFun X).obj (F ⊗ G) => α.app (op U) m)
      (mulRight_val_eq X.presheaf (schemeSheafCondition X) F f)
  have hrho : (ρ_ ((forgetFun X).obj F)).inv.app (op U) m =
      (m ⊗ₜ[Γ(X, U)] (1 : Γ(X, U)) : TensorProduct Γ(X, U) Γ(F, U) Γ(X, U)) :=
    ModuleCat.MonoidalCategory.rightUnitor_inv_apply (R := Γ(X, U)) m
  hval.trans (congrArg
    (fun t : TensorProduct Γ(X, U) Γ(F, U) Γ(X, U) =>
      (toTensorSection X.presheaf (schemeSheafCondition X) F G).app (op U)
        (((forgetFun X).obj F ◁ (toSheafify X.presheaf (schemeSheafCondition X)
          (𝟙_ (PresheafOfModules.{u}
            (structureSheaf X.presheaf (schemeSheafCondition X)).obj)) ≫ f.val)).app (op U) t))
    hrho)


/-- The section of the monoidal unit over `U` is the restriction of the one over `V ≤ U`'s
container: the unit section is compatible with restriction, since the sheafification unit is
natural and the structure sheaf's restriction maps are ring maps. -/
theorem map_monoidalUnitSection {U V : X.Opens} (i : V ⟶ U) :
    (𝟙_ X.Modules).presheaf.map i.op (monoidalUnitSection X U) = monoidalUnitSection X V :=
  have hnat := PresheafOfModules.naturality_apply
    (toSheafify X.presheaf (schemeSheafCondition X)
      (𝟙_ (PresheafOfModules.{u}
        (structureSheaf X.presheaf (schemeSheafCondition X)).obj))) i.op (1 : Γ(X, U))
  hnat.symm.trans (congrArg
    (fun r : Γ(X, V) =>
      (toSheafify X.presheaf (schemeSheafCondition X)
        (𝟙_ (PresheafOfModules.{u}
          (structureSheaf X.presheaf (schemeSheafCondition X)).obj))).app (op V) r)
    (map_one (CommRingCat.Hom.hom (X.presheaf.map i.op))))

/-- **The global section carried by a morphism out of the monoidal unit** is the value of that
morphism on the unit section over `⊤`. -/
theorem globalSection_eq_app_monoidalUnitSection (G : X.Modules) (f : 𝟙_ X.Modules ⟶ G) :
    globalSection X G f = f.app ⊤ (monoidalUnitSection X ⊤) :=
  congrArg
    (fun α : (𝟙_ (PresheafOfModules.{u}
          (structureSheaf X.presheaf (schemeSheafCondition X)).obj)) ⟶
        ((sheafify X.presheaf (schemeSheafCondition X)).obj
          (𝟙_ (PresheafOfModules.{u}
            (structureSheaf X.presheaf (schemeSheafCondition X)).obj))).val =>
      f.val.app (op ⊤) (α.app (op ⊤) (1 : Γ(X, ⊤))))
    (sheafifyCounit_inv_val X.presheaf (schemeSheafCondition X)
      (_root_.SheafOfModules.unit (structureSheaf X.presheaf (schemeSheafCondition X))))

/-- The section of `G` over `U` carried by a morphism out of the monoidal unit is the restriction
of its global section. -/
theorem app_monoidalUnitSection_eq_map_globalSection (G : X.Modules)
    (f : 𝟙_ X.Modules ⟶ G) (U : X.Opens) :
    f.app U (monoidalUnitSection X U) =
      G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (globalSection X G f) :=
  have hnat := PresheafOfModules.naturality_apply ((forgetFun X).map f)
    (homOfLE (le_top : U ≤ ⊤)).op (monoidalUnitSection X ⊤)
  (congrArg (fun t : Γ(𝟙_ X.Modules, U) => f.app U t)
      (map_monoidalUnitSection (homOfLE (le_top : U ≤ ⊤))).symm).trans
    (hnat.trans (congrArg
      (fun t : Γ(G, ⊤) => G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t)
      (globalSection_eq_app_monoidalUnitSection G f).symm))

/-- **The product of a section with a global section, written with that global section.** -/
theorem mulSec_eq_tensorSection_globalSection (F G : X.Modules) (f : 𝟙_ X.Modules ⟶ G)
    {U : X.Opens} (m : Γ(F, U)) :
    Stacks.TensorSectionNonvanishing.mulSec F f m =
      tensorSection F G m
        (G.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (globalSection X G f)) :=
  (mulSec_eq_tensorSection F G f m).trans
    (congrArg (fun n : Γ(G, U) => tensorSection F G m n)
      (app_monoidalUnitSection_eq_map_globalSection G f U))

end Stacks.SectionProduct

namespace Stacks.SectionTensorFormula

end Stacks.SectionTensorFormula

end
