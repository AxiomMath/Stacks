module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced

/-!
# The tensorator of the inverse image along a continuous functor of sites, on local sections

`Stacks.PullbackMonoidalSite.pullbackStrictMonoidal` makes the inverse image `f⁻¹` of sheaves of
modules along a continuous functor of sites a monoidal functor for the monoidal structure of
Tag 01CA, by transporting a monoidal structure obtained from the localization of presheaves of
modules along sheafification. Its tensorator was given by no formula. This file computes it on
local sections, and uses the computation to discharge the two hypotheses carried by
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackUnit`.

The outcome is that **the localization tensorator cancels**: the oplax tensorator of
`pullbackStrictMonoidal` is the comparison of pullback with sheafification followed by the
sheafification of a morphism of presheaves of modules, and every ingredient of the latter has a
section formula. Nothing about the localized monoidal structure survives.

## Main definitions

* `Stacks.PullbackTensorSectionsSite.shDelta`, `shMu`, `preDelta`, `pullDelta`, `lift`: the two
  tensorators of sheafification, the oplax tensorator of the presheaf-level inverse image, the
  oplax tensorator of the presheaf-level inverse image followed by sheafification, and the
  component of `Stacks.PullbackMonoidalSite.liftingIso`.
* `Stacks.PullbackTensorSectionsSite.pullbackLeg`: **the canonical map
  `f⁻¹_pre(A.val) ⟶ (f⁻¹A).val`** from the presheaf-level inverse image of the underlying
  presheaf of `A` to the underlying presheaf of the sheaf-level inverse image.
* `Stacks.PullbackTensorSectionsSite.shSec`, `preSec`, `pullSec`: a local section read in a
  sheafification, in the presheaf-level inverse image, and in the sheaf-level inverse image.

## Main results

* `Stacks.PullbackTensorSectionsSite.delta_pullbackStrictMonoidal_eq`: **the oplax tensorator of
  the monoidal structure of Tag 01CA on `f⁻¹`, computed**, with no localized tensorator left
  in it.
* `Stacks.PullbackTensorSectionsSite.delta_pullbackStrictMonoidal_pullSec_tmul`: **the oplax
  tensorator of `pullbackStrictMonoidal` on a local pure tensor**: it carries the unit image of
  `a ⊗ b` to the pure tensor of the two unit images.
* `Stacks.DifferentialGradedPullbackConstruction.mu_pushforwardLaxMonoidal`: the tensorator of
  the direct image as the adjoint transpose of the oplax tensorator of the inverse image.
* `Stacks.DifferentialGradedPullbackConstruction.isPushforwardMuSections` and
  `isPushforwardEpsilonSections`: **the two hypotheses of
  `...DifferentialGradedPullbackUnit`, discharged.**

## Implementation notes

**The unit morphism is deduced from the tensorator.** The section formula for
`Functor.LaxMonoidal.ε` of the direct image is not a second computation of the same shape: the
left unitality law of a lax monoidal functor expresses `(λ_ (f_*X)).hom` through `ε`, the
tensorator and `f_*((λ_ X).hom)`, and all three of the other players have section formulas — the
tensorator by `isPushforwardMuSections` and the two unitors by
`Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit`. Reading that law at `X = 𝟙_`
on the section `1` gives `ε(1) = 1`.

**No composite morphism occurs as the argument of a section-evaluation map in a statement**, and
each intermediate step takes the morphism it evaluates as a binder: this keeps the elaborator from
having to reduce a four-fold composite under `PresheafOfModules.Hom.app`.

**Universes.** Everything is at a single universe `u` with both sites small, as forced by
`Stacks.PullbackTensor.pullbackTensorIso`, the comparison of Tag 01CD at a functor of sites.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Functor PresheafOfModules
open Stacks.SheafOfModules.TensorSheafification Stacks.PullbackMonoidalSite
open Stacks.SheafOfModules.SliceRestriction Stacks.PullbackColimit
open CategoryTheory.Sheaf Stacks.DifferentialGradedInverseImage

open scoped TensorProduct

universe u

namespace Stacks.PullbackTensorSectionsSite

/-! ### The data of the localized monoidal structure on sheaves of modules -/

section Sheafify

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{u}) (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
attribute [local instance] Stacks.SheafOfModules.sheafifyFunctor_monoidal

/-- The underlying presheaf of modules of a sheaf of modules, with its type ascribed at the
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf` spelling of the structure ring
presheaf, which is the spelling sheafification and the localized monoidal structure carry.

The two spellings — this one and `(structureSheaf O hO).obj` — agree by `rfl` and are not
syntactically equal, and a term mixing them is not type-correct at `implicit` transparency, so
`rw` refuses any goal containing it. Every statement below is therefore written with `valp`, and
the crossing happens inside a proof given by `:=`. -/
abbrev valp (M : SheafOfModules.{u} (structureSheaf O hO)) :
    PresheafOfModules.{u} (structureRingPresheaf O) :=
  M.val

/-- The sheafification unit of a presheaf of modules, with its target written as the underlying
presheaf of the sheafification. -/
noncomputable def shUnitHom (Pp : PresheafOfModules.{u} (structureRingPresheaf O)) :
    Pp ⟶ valp O hO ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp) :=
  Stacks.SheafOfModules.TensorSheafification.toSheafify O hO Pp

/-- The sheafification of the underlying presheaf of a sheaf of modules is that sheaf: the counit
of the sheafification adjunction, ascribed at the spelling of `valp`. -/
noncomputable def valIso (M : SheafOfModules.{u} (structureSheaf O hO)) :
    (Stacks.SheafOfModules.sheafifyFunctor O hO).obj (valp O hO M) ≅ M :=
  Stacks.SheafOfModules.sheafifyValIso O hO M

/-- A morphism of sheaves of modules, read on underlying presheaves at the spelling of
`valp`. -/
abbrev valHom {M N : SheafOfModules.{u} (structureSheaf O hO)} (g : M ⟶ N) :
    valp O hO M ⟶ valp O hO N :=
  g.val

/-- The tensorator of sheafification of presheaves of modules. -/
noncomputable def shMu (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    (Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp ⊗
        (Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq ⟶
      (Stacks.SheafOfModules.sheafifyFunctor O hO).obj (Pp ⊗ Qq) :=
  Functor.LaxMonoidal.μ (Stacks.SheafOfModules.sheafifyFunctor O hO) Pp Qq

/-- The oplax tensorator of sheafification of presheaves of modules. -/
noncomputable def shDelta (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    (Stacks.SheafOfModules.sheafifyFunctor O hO).obj (Pp ⊗ Qq) ⟶
      (Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp ⊗
        (Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq :=
  Functor.OplaxMonoidal.δ (Stacks.SheafOfModules.sheafifyFunctor O hO) Pp Qq

/-- The two tensorators of sheafification cancel inside a composite. -/
theorem shDelta_shMu_assoc {Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)}
    {W : SheafOfModules.{u} (structureSheaf O hO)}
    (k : (Stacks.SheafOfModules.sheafifyFunctor O hO).obj (Pp ⊗ Qq) ⟶ W) :
    shDelta O hO Pp Qq ≫ shMu O hO Pp Qq ≫ k = k := by
  exact Functor.Monoidal.δ_μ_assoc (Stacks.SheafOfModules.sheafifyFunctor O hO) Pp Qq k

/-- The two tensorators of sheafification cancel inside a composite, the other way round. -/
theorem shMu_shDelta_assoc {Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)}
    {W : SheafOfModules.{u} (structureSheaf O hO)}
    (k : (Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp ⊗
      (Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq ⟶ W) :
    shMu O hO Pp Qq ≫ shDelta O hO Pp Qq ≫ k = k := by
  exact Functor.Monoidal.μ_δ_assoc (Stacks.SheafOfModules.sheafifyFunctor O hO) Pp Qq k

/-- A two-sided inverse is unique. -/
theorem eq_of_comp_id_comp {E : Type*} [Category E] {V W : E} {a : W ⟶ V} {k : V ⟶ W}
    {b : W ⟶ V} (h1 : a ≫ k = CategoryStruct.id W)
    (h2 : k ≫ b = CategoryStruct.id V) : a = b := by
  rw [← Category.comp_id a, ← h2, ← Category.assoc, h1, Category.id_comp]

/-- **The localized tensor product of two sheaves of modules is the tensor product sheaf of Tag
01CA**: `Stacks.SheafOfModules.tensorObjIso`, with its target written as a sheafification of an
objectwise tensor product at the spelling of `valp`. -/
noncomputable def tensorComparisonIso (M N : SheafOfModules.{u} (structureSheaf O hO)) :
    M ⊗ N ≅
      (Stacks.SheafOfModules.sheafifyFunctor O hO).obj (valp O hO M ⊗ valp O hO N) :=
  Stacks.SheafOfModules.tensorObjIso O hO M N

/-- `tensorComparisonIso` is the tensorator of sheafification, precomposed with the two
sheafification counit isomorphisms. -/
theorem tensorComparisonIso_hom (M N : SheafOfModules.{u} (structureSheaf O hO)) :
    (tensorComparisonIso O hO M N).hom =
      ((valIso O hO M).inv ⊗ₘ (valIso O hO N).inv) ≫ shMu O hO (valp O hO M) (valp O hO N) :=
  rfl

/-- The inverse of `Stacks.SheafOfModules.tensorObjIso` is the oplax tensorator of
sheafification followed by the two sheafification counits. -/
theorem tensorComparisonIso_inv (M N : SheafOfModules.{u} (structureSheaf O hO)) :
    (tensorComparisonIso O hO M N).inv =
      shDelta O hO (valp O hO M) (valp O hO N) ≫
        ((valIso O hO M).hom ⊗ₘ (valIso O hO N).hom) := by
  refine eq_of_comp_id_comp (k := (tensorComparisonIso O hO M N).hom)
    (Iso.inv_hom_id _) ?_
  rw [tensorComparisonIso_hom, Category.assoc, shMu_shDelta_assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.inv_hom_id, Iso.inv_hom_id,
    MonoidalCategory.id_tensorHom_id]

/-- The sheafification counit at a sheafified presheaf is the sheafification of the unit. -/
theorem valIso_inv_sheafify (Pp : PresheafOfModules.{u} (structureRingPresheaf O)) :
    (valIso O hO ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp)).inv =
      (Stacks.SheafOfModules.sheafifyFunctor O hO).map (shUnitHom O hO Pp) :=
  Stacks.SheafOfModules.sheafifyValIso_inv_sheafify O hO Pp

/-- Naturality of the tensorator of sheafification. -/
theorem shMu_natural {Pp Pp' Qq Qq' : PresheafOfModules.{u} (structureRingPresheaf O)}
    (g : Pp ⟶ Pp') (h : Qq ⟶ Qq') :
    ((Stacks.SheafOfModules.sheafifyFunctor O hO).map g ⊗ₘ
          (Stacks.SheafOfModules.sheafifyFunctor O hO).map h) ≫ shMu O hO Pp' Qq' =
      shMu O hO Pp Qq ≫ (Stacks.SheafOfModules.sheafifyFunctor O hO).map (g ⊗ₘ h) :=
  Functor.LaxMonoidal.μ_natural (Stacks.SheafOfModules.sheafifyFunctor O hO) g h

/-- Naturality of `tensorComparisonIso`. -/
theorem tensorComparisonIso_naturality {M M' N N' : SheafOfModules.{u} (structureSheaf O hO)}
    (g : M ⟶ M') (h : N ⟶ N') :
    (g ⊗ₘ h) ≫ (tensorComparisonIso O hO M' N').hom =
      (tensorComparisonIso O hO M N).hom ≫
        (Stacks.SheafOfModules.sheafifyFunctor O hO).map (valHom O hO g ⊗ₘ valHom O hO h) :=
  Stacks.SheafOfModules.tensorObjIso_naturality O hO g h

/-- **The tensorator of the localized monoidal structure on sheaves of modules, computed.** The
oplax tensorator of sheafification, followed by the comparison of the localized tensor product
with the tensor product sheaf of Tag 01CA, is the sheafification of the tensor product of the two
sheafification units. -/
theorem shDelta_comp_tensorComparisonIso_hom
    (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    shDelta O hO Pp Qq ≫ (tensorComparisonIso O hO
          ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp)
          ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq)).hom =
      (Stacks.SheafOfModules.sheafifyFunctor O hO).map
        (shUnitHom O hO Pp ⊗ₘ shUnitHom O hO Qq) := by
  rw [tensorComparisonIso_hom, valIso_inv_sheafify, valIso_inv_sheafify, shMu_natural,
    shDelta_shMu_assoc]

/-! #### Local sections through the sheafification unit -/

/-- A local section of a presheaf of modules, read in its sheafification through the
sheafification unit. -/
noncomputable def shSec (Pp : PresheafOfModules.{u} (structureRingPresheaf O)) (V : Cᵒᵖ)
    (p : Pp.obj V) :
    (valp O hO ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp)).obj V :=
  Hom.app (shUnitHom O hO Pp) V p

/-- The sheafification of a morphism of presheaves of modules, on a unit image. -/
theorem map_shSec {Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)} (g : Pp ⟶ Qq)
    (V : Cᵒᵖ) (p : Pp.obj V) :
    Hom.app (valHom O hO ((Stacks.SheafOfModules.sheafifyFunctor O hO).map g)) V
        (shSec O hO Pp V p) =
      shSec O hO Qq V (Hom.app g V p) :=
  PresheafOfModules.unit_naturality_apply
    (α := CategoryStruct.id (structureSheaf O hO).obj) g V p

/-- The sheafification counit undoes the sheafification unit on local sections: the triangle
identity of the sheafification adjunction, read at `shSec`. -/
theorem valIso_hom_shSec (M : SheafOfModules.{u} (structureSheaf O hO)) (V : Cᵒᵖ)
    (x : (valp O hO M).obj V) :
    Hom.app (valHom O hO (valIso O hO M).hom) V (shSec O hO (valp O hO M) V x) = x :=
  PresheafOfModules.hom_congr_apply'
    ((PresheafOfModules.sheafificationAdjunction
      (CategoryStruct.id (structureSheaf O hO).obj)).right_triangle_components M) V x

/-- The tensor product of two morphisms of presheaves of modules, on a pure tensor of local
sections. -/
theorem presheafTensorHom_tmul {Pp Pp' Qq Qq' : PresheafOfModules.{u} (structureRingPresheaf O)}
    (uu : Pp ⟶ Pp') (vv : Qq ⟶ Qq') (V : Cᵒᵖ) (p : Pp.obj V) (q : Qq.obj V) :
    Hom.app (uu ⊗ₘ vv) V (p ⊗ₜ q) =
      (Hom.app uu V p ⊗ₜ Hom.app vv V q : (Pp' ⊗ Qq').obj V) :=
  rfl

end Sheafify

/-! ### The identity functors between the two spellings of the monoidal structure -/

section Spellings

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{u}) (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
attribute [local instance] Stacks.SheafOfModules.sheafifyFunctor_monoidal

/-- The oplax tensorator of the identity functor into the localized spelling is the inverse of
`tensorComparisonIso`. -/
theorem delta_toLoc (M N : SheafOfModules.{u} (structureSheaf O hO)) :
    Functor.OplaxMonoidal.δ (self := (toLocalizedMonoidalMonoidal O hO).toOplaxMonoidal)
        (Stacks.SheafOfModules.Strict.toLocalizedMonoidal O hO) M N =
      (tensorComparisonIso O hO M N).inv :=
  rfl

/-- The lax tensorator of the identity functor out of the localized spelling is the inverse of
`tensorComparisonIso`: the two identity functors are inverse monoidal functors. -/
theorem mu_fromLoc (M N : SheafOfModules.{u} (structureSheaf O hO)) :
    Functor.LaxMonoidal.μ (self := (fromLocalizedMonoidalMonoidal O hO).toLaxMonoidal)
        (fromLocalizedMonoidal O hO) M N =
      (tensorComparisonIso O hO M N).inv := by
  have h : Functor.LaxMonoidal.μ (self := (fromLocalizedMonoidalMonoidal O hO).toLaxMonoidal)
        (fromLocalizedMonoidal O hO) M N =
      CategoryStruct.id _ ≫ (Functor.OplaxMonoidal.δ
            (self := (toLocalizedMonoidalMonoidal O hO).toOplaxMonoidal)
            (Stacks.SheafOfModules.Strict.toLocalizedMonoidal O hO) M N ≫
          (CategoryStruct.id ((Stacks.SheafOfModules.Strict.toLocalizedMonoidal O hO).obj M) ⊗ₘ
            CategoryStruct.id
              ((Stacks.SheafOfModules.Strict.toLocalizedMonoidal O hO).obj N))) := rfl
  rw [h, delta_toLoc, MonoidalCategory.id_tensorHom_id, Category.id_comp]
  exact Category.comp_id _

/-- The oplax tensorator of the identity functor out of the localized spelling is
`tensorComparisonIso`. -/
theorem delta_fromLoc (M N : SheafOfModules.{u} (structureSheaf O hO)) :
    Functor.OplaxMonoidal.δ (self := (fromLocalizedMonoidalMonoidal O hO).toOplaxMonoidal)
        (fromLocalizedMonoidal O hO) M N =
      (tensorComparisonIso O hO M N).hom := by
  have h := Functor.Monoidal.μ_δ (self := fromLocalizedMonoidalMonoidal O hO)
    (fromLocalizedMonoidal O hO) M N
  rw [mu_fromLoc] at h
  exact (Iso.inv_comp_eq_id _).mp h

end Spellings

/-! ### The tensorator of the inverse image -/

section Pullback

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  {O : Cᵒᵖ ⥤ CommRingCat.{u}} {P : Dᵒᵖ ⥤ CommRingCat.{u}} (α : O ⟶ F.op ⋙ P)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf O))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf P))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [(SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).IsRightAdjoint]

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
attribute [local instance] Stacks.SheafOfModules.sheafifyFunctor_monoidal
attribute [local instance] sheafifiedPresheafPullbackMonoidal

/-- The inverse image of sheaves of modules along `α`. -/
noncomputable abbrev pull :
    SheafOfModules.{u} (structureSheaf O hO) ⥤ SheafOfModules.{u} (structureSheaf P hP) :=
  SheafOfModules.pullback.{u} (sheafRingHom α hO hP)

/-- The inverse image of presheaves of modules along `α`. -/
noncomputable abbrev prePull :
    PresheafOfModules.{u} (structureRingPresheaf O) ⥤
      PresheafOfModules.{u} (structureRingPresheaf P) :=
  PresheafOfModules.pullback.{u} (toRingCatPullback α)

/-- The oplax tensorator of the presheaf-level inverse image. -/
noncomputable def preDelta (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    (prePull α).obj (Pp ⊗ Qq) ⟶ (prePull α).obj Pp ⊗ (prePull α).obj Qq :=
  Functor.OplaxMonoidal.δ (self := (presheafPullbackMonoidal α).toOplaxMonoidal)
    (prePull α) Pp Qq

/-- **Pullback of modules commutes with sheafification**, at a presheaf of modules: the component
of `Stacks.PullbackMonoidalSite.liftingIso`. -/
noncomputable def lift (Pp : PresheafOfModules.{u} (structureRingPresheaf O)) :
    (pull α hO hP).obj ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp) ≅
      (Stacks.SheafOfModules.sheafifyFunctor P hP).obj ((prePull α).obj Pp) :=
  (liftingIso α hO hP).app Pp

/-- The oplax tensorator of the presheaf-level inverse image followed by sheafification. -/
noncomputable def pullDelta (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    (Stacks.SheafOfModules.sheafifyFunctor P hP).obj ((prePull α).obj (Pp ⊗ Qq)) ⟶
      (Stacks.SheafOfModules.sheafifyFunctor P hP).obj ((prePull α).obj Pp) ⊗
        (Stacks.SheafOfModules.sheafifyFunctor P hP).obj ((prePull α).obj Qq) :=
  Functor.OplaxMonoidal.δ (self := (sheafifiedPresheafPullbackMonoidal α hP).toOplaxMonoidal)
    (sheafifiedPresheafPullback α hP) Pp Qq

/-- The oplax tensorator of the presheaf-level inverse image followed by sheafification is the
sheafification of the presheaf-level one followed by the one of sheafification. -/
theorem pullDelta_eq (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    pullDelta α hP Pp Qq =
      (Stacks.SheafOfModules.sheafifyFunctor P hP).map (preDelta α Pp Qq) ≫
        shDelta P hP ((prePull α).obj Pp) ((prePull α).obj Qq) :=
  rfl

/-- **Where the structure map of `Stacks.PullbackMonoidalSite.pullbackMonoidal` is pinned**: at a
pair of sheafified presheaves the tensorator is the tensorator of the presheaf-level inverse image
composed with sheafification, conjugated by the lifting isomorphism and by the tensorator of
sheafification on the source site. This is
`CategoryTheory.Localization.Monoidal.functorMonoidalOfComp_μ`, with the lifting isomorphism of
the instance written as `Stacks.PullbackMonoidalSite.liftingIso`. -/
theorem pullbackMonoidal_mu (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    Functor.LaxMonoidal.μ (self := (pullbackMonoidal α hO hP).toLaxMonoidal) (pull α hO hP)
        ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp)
        ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq) =
      (((liftingIso α hO hP).hom.app Pp ⊗ₘ (liftingIso α hO hP).hom.app Qq) ≫
          Functor.LaxMonoidal.μ (self := (sheafifiedPresheafPullbackMonoidal α hP).toLaxMonoidal)
            (sheafifiedPresheafPullback α hP) Pp Qq) ≫
        (liftingIso α hO hP).inv.app (Pp ⊗ Qq) ≫
          (pull α hO hP).map
            (Functor.OplaxMonoidal.δ (Stacks.SheafOfModules.sheafifyFunctor O hO) Pp Qq) :=
  Localization.Monoidal.functorMonoidalOfComp_μ
    (Stacks.SheafOfModules.sheafifyFunctor O hO) (Stacks.SheafOfModules.localIso (J := J) O)
    (pull α hO hP) (sheafifiedPresheafPullback α hP) Pp Qq

/-- **The localization tensorator cancels, at a pair of sheafified presheaves**, with the lifting
isomorphism written as a natural isomorphism. -/
private theorem map_shDelta_comp_delta_aux
    (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    (pull α hO hP).map
            (Functor.OplaxMonoidal.δ (Stacks.SheafOfModules.sheafifyFunctor O hO) Pp Qq) ≫
        Functor.OplaxMonoidal.δ (self := (pullbackMonoidal α hO hP).toOplaxMonoidal)
          (pull α hO hP) ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp)
            ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq) =
      (liftingIso α hO hP).hom.app (Pp ⊗ Qq) ≫
        Functor.OplaxMonoidal.δ (self := (sheafifiedPresheafPullbackMonoidal α hP).toOplaxMonoidal)
            (sheafifiedPresheafPullback α hP) Pp Qq ≫
          ((liftingIso α hO hP).inv.app Pp ⊗ₘ (liftingIso α hO hP).inv.app Qq) := by
  refine eq_of_comp_id_comp (k := Functor.LaxMonoidal.μ
      (self := (pullbackMonoidal α hO hP).toLaxMonoidal) (pull α hO hP)
        ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp)
        ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq) ≫
      (pull α hO hP).map
        (Functor.LaxMonoidal.μ (Stacks.SheafOfModules.sheafifyFunctor O hO) Pp Qq)) ?_ ?_
  · rw [Category.assoc, ← Category.assoc
        (Functor.OplaxMonoidal.δ (self := (pullbackMonoidal α hO hP).toOplaxMonoidal)
          (pull α hO hP) ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp)
            ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq)),
      Functor.Monoidal.δ_μ, Category.id_comp]
    exact Functor.Monoidal.map_δ_μ (Stacks.SheafOfModules.sheafifyFunctor O hO)
      (pull α hO hP) Pp Qq
  · rw [pullbackMonoidal_mu]
    simp only [Category.assoc, Functor.Monoidal.map_δ_μ_assoc, Iso.inv_hom_id_app_assoc,
      Functor.Monoidal.μ_δ_assoc, MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app,
      MonoidalCategory.id_tensorHom_id]
    rfl

/-- **The localization tensorator cancels, at a pair of sheafified presheaves.** The oplax
tensorator of `Stacks.PullbackMonoidalSite.pullbackMonoidal`, precomposed with the inverse image
of the oplax tensorator of sheafification, is the lifting isomorphism followed by the oplax
tensorator of the presheaf-level inverse image composed with sheafification: no tensorator of the
localized monoidal structure survives. -/
theorem map_shDelta_comp_delta (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) :
    (pull α hO hP).map (shDelta O hO Pp Qq) ≫
        Functor.OplaxMonoidal.δ (self := (pullbackMonoidal α hO hP).toOplaxMonoidal)
          (pull α hO hP) ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp)
            ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Qq) =
      (lift α hO hP (Pp ⊗ Qq)).hom ≫
        pullDelta α hP Pp Qq ≫ ((lift α hO hP Pp).inv ⊗ₘ (lift α hO hP Qq).inv) :=
  map_shDelta_comp_delta_aux α hO hP Pp Qq

/-- **The localization tensorator cancels, at an arbitrary pair of sheaves of modules.** -/
theorem map_tensorComparisonIso_inv_comp_delta
    (A B : SheafOfModules.{u} (structureSheaf O hO)) :
    (pull α hO hP).map (tensorComparisonIso O hO A B).inv ≫
        Functor.OplaxMonoidal.δ (self := (pullbackMonoidal α hO hP).toOplaxMonoidal)
          (pull α hO hP) A B =
      (lift α hO hP (valp O hO A ⊗ valp O hO B)).hom ≫
        pullDelta α hP (valp O hO A) (valp O hO B) ≫
          (((lift α hO hP (valp O hO A)).inv ≫
              (pull α hO hP).map (valIso O hO A).hom) ⊗ₘ
            ((lift α hO hP (valp O hO B)).inv ≫
              (pull α hO hP).map (valIso O hO B).hom)) := by
  rw [tensorComparisonIso_inv, Functor.map_comp, Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural, ← Category.assoc, map_shDelta_comp_delta,
    Category.assoc, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]

/-- **The canonical map from the presheaf-level inverse image into the sheaf-level inverse
image.** It is the sheafification unit followed by the comparison of the two constructions of the
inverse image. -/
noncomputable def pullbackLeg (A : SheafOfModules.{u} (structureSheaf O hO)) :
    (prePull α).obj (valp O hO A) ⟶ valp P hP ((pull α hO hP).obj A) :=
  shUnitHom P hP ((prePull α).obj (valp O hO A)) ≫
    valHom P hP ((lift α hO hP (valp O hO A)).inv ≫ (pull α hO hP).map (valIso O hO A).hom)

/-- The sheafification of the presheaf-level oplax tensorator, followed by the comparison of the
localized tensor product with the tensor product sheaf and by the sheafification of a tensor
product of morphisms, is a single sheafification. -/
theorem map_preDelta_comp (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O))
    {M N : SheafOfModules.{u} (structureSheaf P hP)}
    (gA : (Stacks.SheafOfModules.sheafifyFunctor P hP).obj ((prePull α).obj Pp) ⟶ M)
    (gB : (Stacks.SheafOfModules.sheafifyFunctor P hP).obj ((prePull α).obj Qq) ⟶ N) :
    (Stacks.SheafOfModules.sheafifyFunctor P hP).map (preDelta α Pp Qq) ≫
        (shDelta P hP ((prePull α).obj Pp) ((prePull α).obj Qq) ≫
          (tensorComparisonIso P hP
              ((Stacks.SheafOfModules.sheafifyFunctor P hP).obj ((prePull α).obj Pp))
              ((Stacks.SheafOfModules.sheafifyFunctor P hP).obj
                ((prePull α).obj Qq))).hom ≫
            (Stacks.SheafOfModules.sheafifyFunctor P hP).map
              (valHom P hP gA ⊗ₘ valHom P hP gB)) =
      (Stacks.SheafOfModules.sheafifyFunctor P hP).map (preDelta α Pp Qq ≫
        ((shUnitHom P hP ((prePull α).obj Pp) ≫ valHom P hP gA) ⊗ₘ
          (shUnitHom P hP ((prePull α).obj Qq) ≫ valHom P hP gB))) := by
  rw [← Category.assoc (shDelta P hP ((prePull α).obj Pp) ((prePull α).obj Qq)),
    shDelta_comp_tensorComparisonIso_hom, ← Functor.map_comp,
    MonoidalCategory.tensorHom_comp_tensorHom, ← Functor.map_comp]

/-! #### The three ingredients of the tensorator, on local sections -/

/-- A local section of a presheaf of modules, read in the presheaf-level inverse image through
the unit of the adjunction. -/
noncomputable def preSec (Pp : PresheafOfModules.{u} (structureRingPresheaf O)) (U : Cᵒᵖ)
    (m : Pp.obj U) : ((prePull α).obj Pp).obj (F.op.obj U) :=
  PresheafOfModules.pullbackAdjUnit (toRingCatPullback α) Pp U m

/-- A local section of a sheaf of modules over `U`, read in the sheaf-level inverse image over
`F U` through the unit of the adjunction. -/
noncomputable def pullSec (M : SheafOfModules.{u} (structureSheaf O hO)) (U : Cᵒᵖ)
    (x : (valp O hO M).obj U) :
    (valp P hP ((pull α hO hP).obj M)).obj (F.op.obj U) :=
  Hom.app (valHom O hO
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).unit.app M)) U x

omit [RepresentablyFlat F] [F.Final] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] in
/-- Naturality of the sheaf-level unit, on local sections. -/
theorem pullSec_naturality {M M' : SheafOfModules.{u} (structureSheaf O hO)} (φ : M ⟶ M')
    (U : Cᵒᵖ) (x : (valp O hO M).obj U) :
    Hom.app (valHom P hP ((pull α hO hP).map φ)) (F.op.obj U) (pullSec α hO hP M U x) =
      pullSec α hO hP M' U (Hom.app (valHom O hO φ) U x) :=
  (PresheafOfModules.hom_congr_apply' (congrArg (fun h : M ⟶
      (SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).obj ((pull α hO hP).obj M') ↦
        SheafOfModules.Hom.val h)
    ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (sheafRingHom α hO hP)).unit.naturality φ)) U x).symm

omit [RepresentablyFlat F] [F.Final] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] in
/-- The adjoint transpose, read on sections: it is the morphism applied to the unit image. -/
theorem homEquiv_val_app (M : SheafOfModules.{u} (structureSheaf O hO))
    (N : SheafOfModules.{u} (structureSheaf P hP)) (θ : (pull α hO hP).obj M ⟶ N) (U : Cᵒᵖ)
    (z : (valp O hO M).obj U) :
    Hom.app (valHom O hO ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (sheafRingHom α hO hP)).homEquiv M N θ)) U z =
      Hom.app (valHom P hP θ) (F.op.obj U) (pullSec α hO hP M U z) := by
  rw [Adjunction.homEquiv_unit]
  rfl

omit [RepresentablyFlat F] [F.Final] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] in
/-- The counit of the adjunction undoes the unit on local sections: the triangle identity, read
on sections. -/
theorem counit_pullSec (M : SheafOfModules.{u} (structureSheaf P hP)) (U : Cᵒᵖ)
    (x : (valp O hO
      ((SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).obj M)).obj U) :
    Hom.app (valHom P hP ((SheafOfModules.pullbackPushforwardAdjunction.{u}
          (sheafRingHom α hO hP)).counit.app M)) (F.op.obj U)
        (pullSec α hO hP ((SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).obj M) U x) =
      x :=
  SheafOfModules.hom_congr_app_apply ((SheafOfModules.pullbackPushforwardAdjunction.{u}
    (sheafRingHom α hO hP)).right_triangle_components M) U x

omit [RepresentablyFlat F] [F.Final] in
/-- **The comparison of the inverse image with sheafification, on a unit image.** It carries the
sheaf-level unit image of the sheafification unit of `m` to the sheafification unit of the
presheaf-level unit image of `m`. -/
theorem lift_hom_pullSec_shSec (Pp : PresheafOfModules.{u} (structureRingPresheaf O)) (U : Cᵒᵖ)
    (m : Pp.obj U) :
    Hom.app (valHom P hP (lift α hO hP Pp).hom) (F.op.obj U)
        (pullSec α hO hP ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp) U
          (shSec O hO Pp U m)) =
      shSec P hP ((prePull α).obj Pp) (F.op.obj U) (preSec α Pp U m) :=
  PresheafOfModules.hom_congr_apply'
    (Adjunction.unit_leftAdjointUniq_hom_app
      ((PresheafOfModules.sheafificationAdjunction
          (CategoryStruct.id (structureSheaf O hO).obj)).comp
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)))
      ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (toRingCatPullback α)).comp
        (PresheafOfModules.sheafificationAdjunction
          (CategoryStruct.id (structureSheaf P hP).obj))) Pp) U m

omit [RepresentablyFlat F] [F.Final] in
/-- The inverse of the comparison of the inverse image with sheafification, on a unit image. -/
theorem lift_inv_shSec_preSec (Pp : PresheafOfModules.{u} (structureRingPresheaf O)) (U : Cᵒᵖ)
    (m : Pp.obj U) :
    Hom.app (valHom P hP (lift α hO hP Pp).inv) (F.op.obj U)
        (shSec P hP ((prePull α).obj Pp) (F.op.obj U) (preSec α Pp U m)) =
      pullSec α hO hP ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp) U
        (shSec O hO Pp U m) :=
  (congrArg (Hom.app (valHom P hP (lift α hO hP Pp).inv) (F.op.obj U))
      (lift_hom_pullSec_shSec α hO hP Pp U m).symm).trans
    (SheafOfModules.iso_inv_hom_app_apply (lift α hO hP Pp) (F.op.obj U)
      (pullSec α hO hP ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp) U
        (shSec O hO Pp U m)))

omit [RepresentablyFlat F] [F.Final] in
/-- The comparison of the inverse image with sheafification followed by the sheafification of a
morphism of presheaves of modules, on a unit image. The morphism is a binder, so that no
composite occurs under a section-evaluation map. -/
theorem map_lift_hom_pullSec_shSec (Pp : PresheafOfModules.{u} (structureRingPresheaf O))
    {W : PresheafOfModules.{u} (structureRingPresheaf P)} (g : (prePull α).obj Pp ⟶ W)
    (U : Cᵒᵖ) (m : Pp.obj U) :
    Hom.app (valHom P hP ((Stacks.SheafOfModules.sheafifyFunctor P hP).map g)) (F.op.obj U)
        (Hom.app (valHom P hP (lift α hO hP Pp).hom) (F.op.obj U)
          (pullSec α hO hP ((Stacks.SheafOfModules.sheafifyFunctor O hO).obj Pp) U
            (shSec O hO Pp U m))) =
      shSec P hP W (F.op.obj U) (Hom.app g (F.op.obj U) (preSec α Pp U m)) :=
  (congrArg (Hom.app (valHom P hP ((Stacks.SheafOfModules.sheafifyFunctor P hP).map g))
        (F.op.obj U))
      (lift_hom_pullSec_shSec α hO hP Pp U m)).trans
    (map_shSec P hP g (F.op.obj U) (preSec α Pp U m))

/-- **The oplax tensorator of the presheaf-level inverse image on a unit image of a pure
tensor**: it carries the unit image of `x ⊗ y` to the pure tensor of the two unit images. -/
theorem preDelta_preSec_tmul (Pp Qq : PresheafOfModules.{u} (structureRingPresheaf O)) (U : Cᵒᵖ)
    (x : Pp.obj U) (y : Qq.obj U) :
    Hom.app (preDelta α Pp Qq) (F.op.obj U) (preSec α (Pp ⊗ Qq) U (x ⊗ₜ y)) =
      (preSec α Pp U x ⊗ₜ preSec α Qq U y :
        ((prePull α).obj Pp ⊗ (prePull α).obj Qq).obj (F.op.obj U)) :=
  PresheafOfModules.delta_pullbackAdjUnit_tmul (toRingCatPullback α) Pp Qq U x y

omit [RepresentablyFlat F] [F.Final] in
/-- **The canonical map from the presheaf-level inverse image into the sheaf-level inverse image,
on a unit image**: it carries the presheaf-level unit image of `x` to the sheaf-level unit image
of `x`. -/
theorem pullbackLeg_preSec (A : SheafOfModules.{u} (structureSheaf O hO)) (U : Cᵒᵖ)
    (x : (valp O hO A).obj U) :
    Hom.app (pullbackLeg α hO hP A) (F.op.obj U) (preSec α (valp O hO A) U x) =
      pullSec α hO hP A U x := by
  refine Eq.trans (SheafOfModules.comp_val_app_apply (lift α hO hP (valp O hO A)).inv
    ((pull α hO hP).map (valIso O hO A).hom) (F.op.obj U)
    (shSec P hP ((prePull α).obj (valp O hO A)) (F.op.obj U)
      (preSec α (valp O hO A) U x))) ?_
  refine Eq.trans (congrArg (Hom.app (valHom P hP ((pull α hO hP).map (valIso O hO A).hom))
    (F.op.obj U)) (lift_inv_shSec_preSec α hO hP (valp O hO A) U x)) ?_
  exact (pullSec_naturality α hO hP (valIso O hO A).hom U (shSec O hO (valp O hO A) U x)).trans
    (congrArg (pullSec α hO hP A U) (valIso_hom_shSec O hO A U x))

section Strict

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory

/-- **The oplax tensorator of the monoidal structure of Tag 01CA on the inverse image** is the
tensorator of the localized monoidal structure conjugated by `tensorComparisonIso`. -/
theorem delta_pullbackStrictMonoidal (A B : SheafOfModules.{u} (structureSheaf O hO)) :
    Functor.OplaxMonoidal.δ (self := (pullbackStrictMonoidal α hO hP).toOplaxMonoidal)
        (pullbackStrict α hO hP) A B =
      (pull α hO hP).map (tensorComparisonIso O hO A B).inv ≫
        (Functor.OplaxMonoidal.δ (self := (pullbackMonoidal α hO hP).toOplaxMonoidal)
            (pull α hO hP) A B ≫
          (tensorComparisonIso P hP ((pull α hO hP).obj A) ((pull α hO hP).obj B)).hom) := by
  have h : Functor.OplaxMonoidal.δ (self := (pullbackStrictMonoidal α hO hP).toOplaxMonoidal)
        (pullbackStrict α hO hP) A B =
      (pull α hO hP).map (tensorComparisonIso O hO A B).inv ≫
        (Functor.OplaxMonoidal.δ (self := (pullbackMonoidal α hO hP).toOplaxMonoidal)
            (pull α hO hP) A B ≫
          Functor.OplaxMonoidal.δ
            (self := (fromLocalizedMonoidalMonoidal P hP).toOplaxMonoidal)
            (fromLocalizedMonoidal P hP) ((pull α hO hP).obj A)
              ((pull α hO hP).obj B)) := rfl
  rw [h, delta_fromLoc]
  rfl

/-- **The oplax tensorator of the monoidal structure of Tag 01CA on the inverse image,
computed.** It is the lifting isomorphism of the localization followed by the sheafification of a
morphism of presheaves of modules: the oplax tensorator of the *presheaf*-level inverse image —
the comparison of Tag 01CD at the presheaf level — followed by the tensor product of the two
canonical maps `pullbackLeg`. No tensorator of the localized monoidal structure appears. -/
theorem delta_pullbackStrictMonoidal_eq (A B : SheafOfModules.{u} (structureSheaf O hO)) :
    Functor.OplaxMonoidal.δ (self := (pullbackStrictMonoidal α hO hP).toOplaxMonoidal)
        (pullbackStrict α hO hP) A B =
      (lift α hO hP (valp O hO A ⊗ valp O hO B)).hom ≫
        (Stacks.SheafOfModules.sheafifyFunctor P hP).map
          (preDelta α (valp O hO A) (valp O hO B) ≫
            (pullbackLeg α hO hP A ⊗ₘ pullbackLeg α hO hP B)) := by
  rw [delta_pullbackStrictMonoidal, ← Category.assoc, map_tensorComparisonIso_inv_comp_delta,
    Category.assoc, Category.assoc, tensorComparisonIso_naturality, pullDelta_eq,
    Category.assoc]
  exact congrArg (fun z => (lift α hO hP (valp O hO A ⊗ valp O hO B)).hom ≫ z)
    (map_preDelta_comp α hP (valp O hO A) (valp O hO B) _ _)

/-- **The oplax tensorator of the monoidal structure of Tag 01CA on the inverse image, on a local
pure tensor.** It carries the unit image of `a ⊗ b` to the pure tensor of the two unit images —
the defining property of the comparison of Tag 01CD. -/
theorem delta_pullbackStrictMonoidal_pullSec_tmul
    (A B : SheafOfModules.{u} (structureSheaf O hO)) (U : Cᵒᵖ) (a : (valp O hO A).obj U)
    (b : (valp O hO B).obj U) :
    Hom.app (valHom P hP (Functor.OplaxMonoidal.δ
          (self := (pullbackStrictMonoidal α hO hP).toOplaxMonoidal)
          (pullbackStrict α hO hP) A B)) (F.op.obj U)
        (pullSec α hO hP (A ⊗ B) U
          (shSec O hO (valp O hO A ⊗ valp O hO B) U (a ⊗ₜ b))) =
      shSec P hP (valp P hP ((pull α hO hP).obj A) ⊗ valp P hP ((pull α hO hP).obj B))
        (F.op.obj U) (pullSec α hO hP A U a ⊗ₜ pullSec α hO hP B U b) := by
  refine Eq.trans (SheafOfModules.hom_congr_app_apply
    (delta_pullbackStrictMonoidal_eq α hO hP A B) (F.op.obj U)
    (pullSec α hO hP (A ⊗ B) U
      (shSec O hO (valp O hO A ⊗ valp O hO B) U (a ⊗ₜ b)))) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (lift α hO hP (valp O hO A ⊗ valp O hO B)).hom
    ((Stacks.SheafOfModules.sheafifyFunctor P hP).map
      (preDelta α (valp O hO A) (valp O hO B) ≫
        (pullbackLeg α hO hP A ⊗ₘ pullbackLeg α hO hP B))) (F.op.obj U)
    (pullSec α hO hP (A ⊗ B) U
      (shSec O hO (valp O hO A ⊗ valp O hO B) U (a ⊗ₜ b)))) ?_
  refine Eq.trans (map_lift_hom_pullSec_shSec α hO hP (valp O hO A ⊗ valp O hO B)
    (preDelta α (valp O hO A) (valp O hO B) ≫
      (pullbackLeg α hO hP A ⊗ₘ pullbackLeg α hO hP B)) U (a ⊗ₜ b)) ?_
  refine congrArg (shSec P hP
    (valp P hP ((pull α hO hP).obj A) ⊗ valp P hP ((pull α hO hP).obj B)) (F.op.obj U)) ?_
  refine Eq.trans (PresheafOfModules.comp_app_apply
    (preDelta α (valp O hO A) (valp O hO B))
    (pullbackLeg α hO hP A ⊗ₘ pullbackLeg α hO hP B) (F.op.obj U)
    (preSec α (valp O hO A ⊗ valp O hO B) U (a ⊗ₜ b))) ?_
  refine Eq.trans (congrArg (Hom.app (pullbackLeg α hO hP A ⊗ₘ pullbackLeg α hO hP B)
    (F.op.obj U)) (preDelta_preSec_tmul α (valp O hO A) (valp O hO B) U a b)) ?_
  exact (presheafTensorHom_tmul P (pullbackLeg α hO hP A) (pullbackLeg α hO hP B)
    (F.op.obj U) (preSec α (valp O hO A) U a) (preSec α (valp O hO B) U b)).trans
    (congrArg₂ _ (pullbackLeg_preSec α hO hP A U a) (pullbackLeg_preSec α hO hP B U b))

end Strict

end Pullback

end Stacks.PullbackTensorSectionsSite

/-! ### The two sections formulas for the direct image -/

open Stacks.PullbackTensorSectionsSite

namespace Stacks.DifferentialGradedPullbackConstruction

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K] [RepresentablyFlat F] [F.Final]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  {Osharp : Sheaf J CommRingCat.{u}} {Psharp : Sheaf K CommRingCat.{u}}
  (α : Osharp.obj ⟶ F.op ⋙ Psharp.obj)
  (hO : Presheaf.IsSheaf J (structureRingPresheaf Osharp.obj))
  (hP : Presheaf.IsSheaf K (structureRingPresheaf Psharp.obj))
  [radj : (SheafOfModules.pushforward.{u} (sheafRingHom α hO hP)).IsRightAdjoint]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory
attribute [local instance] Stacks.SheafOfModules.Strict.monoidalCategory
attribute [local instance] inverseImageMonoidal
attribute [local instance] pushforward_additive
attribute [local instance] pushforwardLaxMonoidal

include radj in
/-- The tensorator of the direct image is the adjoint transpose of the oplax tensorator of the
inverse image followed by the two counits, by construction. -/
theorem mu_pushforwardLaxMonoidal (X Y : SheafOfModules.{u} (toRingCat K Psharp)) :
    Functor.LaxMonoidal.μ (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) X Y =
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).homEquiv _ _
        (Functor.OplaxMonoidal.δ (self := (pullbackStrictMonoidal α hO hP).toOplaxMonoidal)
            (pullbackStrict α hO hP)
            ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj X)
            ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj Y) ≫
          ((SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).counit.app X ⊗ₘ
            (SheafOfModules.pullbackPushforwardAdjunction.{u}
              (sheafRingHom α hO hP)).counit.app Y)) := rfl


include radj in
/-- **The sections formula for the tensorator of the direct image of sheaves of modules along a
continuous functor of sites**, which `IsPushforwardMuSections` carried as a hypothesis: on the
image of a pure tensor of two local sections over `V` the tensorator is the image of the pure
tensor of the same two sections, read over `F V`. -/
theorem isPushforwardMuSections : IsPushforwardMuSections α hO hP := by
  intro X Y V x y
  refine Eq.trans (SheafOfModules.hom_congr_app_apply (mu_pushforwardLaxMonoidal α hO hP X Y) V
    ((tensorSheafUnit ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj X)
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj Y)).app V
        (x ⊗ₜ y))) ?_
  refine Eq.trans (homEquiv_val_app α hO hP _ _
    (Functor.OplaxMonoidal.δ (self := (pullbackStrictMonoidal α hO hP).toOplaxMonoidal)
        (pullbackStrict α hO hP)
        ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj X)
        ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj Y) ≫
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).counit.app X ⊗ₘ
        (SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).counit.app Y))
    V _) ?_
  refine Eq.trans (SheafOfModules.comp_val_app_apply
    (Functor.OplaxMonoidal.δ (self := (pullbackStrictMonoidal α hO hP).toOplaxMonoidal)
      (pullbackStrict α hO hP)
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj X)
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj Y))
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).counit.app X ⊗ₘ
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).counit.app Y)
    (F.op.obj V) _) ?_
  refine Eq.trans (congrArg (Hom.app (valHom Psharp.obj hP
      ((SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).counit.app X ⊗ₘ
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (sheafRingHom α hO hP)).counit.app Y)) (F.op.obj V))
    (delta_pullbackStrictMonoidal_pullSec_tmul α hO hP
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj X)
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj Y) V x y)) ?_
  refine Eq.trans (Stacks.TensorSheafWorld.tensorHom_val_app_tensorSheafUnit Psharp hP
    (F.op.obj V)
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).counit.app X)
    ((SheafOfModules.pullbackPushforwardAdjunction.{u} (sheafRingHom α hO hP)).counit.app Y)
    (pullSec α hO hP ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj X) V x)
    (pullSec α hO hP ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj Y) V
      y)) ?_
  exact congrArg₂ (fun p q => (tensorSheafUnit X Y).app (F.op.obj V) (p ⊗ₜ q))
    (counit_pullSec α hO hP X V x) (counit_pullSec α hO hP Y V y)


include radj in
/-- **The sections formula for the unit morphism of the lax monoidal direct image of sheaves of
modules**, which `IsPushforwardEpsilonSections` carried as a hypothesis: it carries the unit
section of the structure sheaf over `V` to the unit section over `F V`.

This is deduced from the sections formula for the tensorator: the left unitality law of a lax
monoidal functor expresses the left unitor of `f_*(𝟙_)` through `ε`, the tensorator and
`f_*` of the left unitor, and the other three players have section formulas. -/
theorem isPushforwardEpsilonSections : IsPushforwardEpsilonSections α hO hP := by
  intro V
  have hsm : ∀ r : (toRingCat K Psharp).obj.obj (F.op.obj V),
      r • (1 : (toRingCat K Psharp).obj.obj (F.op.obj V)) = r := fun r => by simp
  have hA : (λ_ ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
          (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))))).hom.val.app V
        ((tensorSheafUnit (𝟙_ (SheafOfModules.{u} (toRingCat J Osharp)))
            ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
              (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))))).app V
          (oneSec V ⊗ₜ (1 : (toRingCat K Psharp).obj.obj (F.op.obj V)))) =
      (1 : (toRingCat K Psharp).obj.obj (F.op.obj V)) :=
    (Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit Osharp hO
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
        (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))) V (oneSec V)
      (1 : (toRingCat K Psharp).obj.obj (F.op.obj V))).trans (one_smul _ _)
  have hB : (Functor.LaxMonoidal.ε
            (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) ▷
          (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
            (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))) ≫
        Functor.LaxMonoidal.μ (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
            (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))
            (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))) ≫
          (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
            (λ_ (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))).hom).val.app V
        ((tensorSheafUnit (𝟙_ (SheafOfModules.{u} (toRingCat J Osharp)))
            ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
              (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))))).app V
          (oneSec V ⊗ₜ (1 : (toRingCat K Psharp).obj.obj (F.op.obj V)))) =
      (Functor.LaxMonoidal.ε
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))).val.app V (oneSec V) := by
    refine Eq.trans (SheafOfModules.comp_val_app_apply
      (Functor.LaxMonoidal.ε (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)) ▷
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
          (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))))
      (Functor.LaxMonoidal.μ (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
          (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))
          (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))) ≫
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
          (λ_ (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))).hom) V _) ?_
    refine Eq.trans (congrArg _ (Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit
      Osharp hO V
      (Functor.LaxMonoidal.ε (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)))
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).obj
        (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))) (oneSec V)
      (1 : (toRingCat K Psharp).obj.obj (F.op.obj V)))) ?_
    refine Eq.trans (SheafOfModules.comp_val_app_apply
      (Functor.LaxMonoidal.μ (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
        (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))
        (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))))
      ((SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP)).map
        (λ_ (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))).hom) V _) ?_
    refine Eq.trans (congrArg _ (isPushforwardMuSections α hO hP
      (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))
      (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))) V
      ((Functor.LaxMonoidal.ε
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))).val.app V (oneSec V))
      (1 : (toRingCat K Psharp).obj.obj (F.op.obj V)))) ?_
    refine Eq.trans (Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit Psharp hP
      (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp))) (F.op.obj V)
      ((Functor.LaxMonoidal.ε
        (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))).val.app V (oneSec V))
      (1 : (toRingCat K Psharp).obj.obj (F.op.obj V))) ?_
    exact hsm _
  exact hB.symm.trans ((SheafOfModules.hom_congr_app_apply
    (Functor.LaxMonoidal.left_unitality
      (SheafOfModules.pushforward.{u} (inverseImageRingHom α hO hP))
      (𝟙_ (SheafOfModules.{u} (toRingCat K Psharp)))) V _).symm.trans hA)

end Stacks.DifferentialGradedPullbackConstruction

end
