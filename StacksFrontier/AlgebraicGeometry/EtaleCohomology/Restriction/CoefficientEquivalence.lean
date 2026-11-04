module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Changing the coefficient category of a sheaf along an equivalence

An equivalence `e : A ≌ B` of coefficient categories induces an equivalence
`Sheaf J A ≌ Sheaf J B` on sheaves for any site, by postcomposition with `e.functor` and
`e.inverse`: the sheaf condition is a limit condition on sections, which both functors preserve.

That equivalence transports every structure a sheaf category carries along with it. Three
transports are recorded here: existence of sheafification, right adjointness of the direct image
along a continuous functor of sites — i.e. existence of the inverse image — and the compatibility
of the inverse image and of the constant sheaf with the change of coefficients. The last two are
*not* extra data: both sides of each comparison are left adjoint to the same functor, so the
isomorphism is the uniqueness of a left adjoint.

The motivating instance is `AddCommGrpCat.moduleCatIntEquivalence`, the equivalence between
abelian groups and `ℤ`-modules. Under it, a statement about sheaves of abelian groups and a
statement about sheaves of `ℤ`-modules are interchangeable; for instance the abelian case of
[Stacks, Tag 09Z4] follows from its module case.

## Main definitions

* `CategoryTheory.Sheaf.coefficientEquivalence` — the induced equivalence of sheaf categories.
* `CategoryTheory.Sheaf.sheafPullbackCoefficientIso` — inverse image commutes with the change of
  coefficients.
* `CategoryTheory.Sheaf.constantSheafCoefficientIso` — the constant sheaf commutes with it.
* `AddCommGrpCat.moduleCatIntEquivalence` — abelian groups are `ℤ`-modules.

## Main results

* `CategoryTheory.Sheaf.hasWeakSheafify_of_coefficientEquivalence` — sheafification transports.
* `CategoryTheory.Sheaf.isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence` —
  so does the existence of the inverse image.

## Implementation notes

The equivalence is built by hand from `CategoryTheory.sheafCompose` rather than obtained from
`CategoryTheory.Equivalence.congrRight` on presheaves, because its two functors must be the
sheaf-level ones: it is those that the adjunction arguments below compose with. The unit and
counit are the unit and counit of `e` whiskered into the sheaves, and the triangle identity is
the one of `e` evaluated at sections.

## References

* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe va vb a b v u v' u'

namespace CategoryTheory.Sheaf

/-- An equivalence `e : A ≌ B` of coefficient categories induces an equivalence
`Sheaf J A ≌ Sheaf J B`: postcompose the underlying presheaf with `e.functor` or with
`e.inverse`, and whisker the unit and counit of `e` into it. -/
public def coefficientEquivalence {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {A : Type a} [Category.{va} A]
    {B : Type b} [Category.{vb} B] (e : A ≌ B)
    [J.HasSheafCompose e.functor] [J.HasSheafCompose e.inverse] :
    Sheaf J A ≌ Sheaf J B where
  functor := sheafCompose J e.functor
  inverse := sheafCompose J e.inverse
  unitIso := NatIso.ofComponents (fun F =>
    { hom := ⟨Functor.whiskerLeft F.obj e.unitIso.hom⟩
      inv := ⟨Functor.whiskerLeft F.obj e.unitIso.inv⟩
      hom_inv_id := by ext V; exact e.unitIso.hom_inv_id_app _
      inv_hom_id := by ext V; exact e.unitIso.inv_hom_id_app _ })
    (by intro F G f; ext V; exact e.unitIso.hom.naturality (f.hom.app V))
  counitIso := NatIso.ofComponents (fun F =>
    { hom := ⟨Functor.whiskerLeft F.obj e.counitIso.hom⟩
      inv := ⟨Functor.whiskerLeft F.obj e.counitIso.inv⟩
      hom_inv_id := by ext V; exact e.counitIso.hom_inv_id_app _
      inv_hom_id := by ext V; exact e.counitIso.inv_hom_id_app _ })
    (by intro F G f; ext V; exact e.counitIso.hom.naturality (f.hom.app V))
  functor_unitIso_comp F := by ext V; exact e.functor_unitIso_comp (F.obj.obj V)

/-- Sheafification transports along a change of coefficients: if presheaves valued in `A` have
sheafification and `A ≌ B`, then presheaves valued in `B` do. -/
public theorem hasWeakSheafify_of_coefficientEquivalence
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B] (e : A ≌ B)
    [J.HasSheafCompose e.functor] [J.HasSheafCompose e.inverse]
    [HasWeakSheafify J A] : HasWeakSheafify J B := by
  let eJ := coefficientEquivalence J e
  apply (Functor.isRightAdjoint_comp_iff_right eJ.functor (sheafToPresheaf J B)).1
  show (sheafToPresheaf J A ⋙ e.congrRight.functor).IsRightAdjoint
  infer_instance

/-- The existence of the inverse image along a continuous functor of sites transports along a
change of coefficients: the direct image on `B`-valued sheaves is a right adjoint as soon as the
one on `A`-valued sheaves is. -/
public theorem isRightAdjoint_sheafPushforwardContinuous_of_coefficientEquivalence
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (f : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B] (e : A ≌ B)
    [J.HasSheafCompose e.functor] [J.HasSheafCompose e.inverse]
    [K.HasSheafCompose e.functor] [K.HasSheafCompose e.inverse]
    [f.IsContinuous J K]
    [(f.sheafPushforwardContinuous A J K).IsRightAdjoint] :
    (f.sheafPushforwardContinuous B J K).IsRightAdjoint := by
  let eJ := coefficientEquivalence J e
  let eK := coefficientEquivalence K e
  apply (Functor.isRightAdjoint_comp_iff_right eK.functor
    (f.sheafPushforwardContinuous B J K)).1
  show (f.sheafPushforwardContinuous A J K ⋙ eJ.functor).IsRightAdjoint
  infer_instance

/-- Inverse image along a continuous functor of sites commutes with a change of coefficients.
Both composites are left adjoint to the composite of the direct image with the inverse change of
coefficients, so the isomorphism is the uniqueness of a left adjoint. -/
public def sheafPullbackCoefficientIso
    {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (f : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B] (e : A ≌ B)
    [J.HasSheafCompose e.functor] [J.HasSheafCompose e.inverse]
    [K.HasSheafCompose e.functor] [K.HasSheafCompose e.inverse]
    [f.IsContinuous J K]
    [(f.sheafPushforwardContinuous A J K).IsRightAdjoint]
    [(f.sheafPushforwardContinuous B J K).IsRightAdjoint] :
    f.sheafPullback A J K ⋙ sheafCompose K e.functor ≅
      sheafCompose J e.functor ⋙ f.sheafPullback B J K :=
  ((f.sheafAdjunctionContinuous A J K).comp
      (coefficientEquivalence K e).toAdjunction).leftAdjointUniq
    (((coefficientEquivalence J e).toAdjunction.comp
      (f.sheafAdjunctionContinuous B J K)).ofNatIsoRight (Iso.refl _))

/-- The constant sheaf commutes with a change of coefficients. Both composites are left adjoint
to evaluation at the final object followed by the inverse change of coefficients. -/
public def constantSheafCoefficientIso {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [HasTerminal C]
    {A : Type a} [Category.{va} A] {B : Type b} [Category.{vb} B] (e : A ≌ B)
    [J.HasSheafCompose e.functor] [J.HasSheafCompose e.inverse]
    [HasWeakSheafify J A] [HasWeakSheafify J B] :
    constantSheaf J A ⋙ sheafCompose J e.functor ≅ e.functor ⋙ constantSheaf J B :=
  ((constantSheafAdj J A terminalIsTerminal).comp
      (coefficientEquivalence J e).toAdjunction).leftAdjointUniq
    ((e.toAdjunction.comp (constantSheafAdj J B terminalIsTerminal)).ofNatIsoRight (Iso.refl _))

end CategoryTheory.Sheaf

namespace AddCommGrpCat

/-- Abelian groups are the same thing as `ℤ`-modules: the forgetful functor from `ℤ`-modules is
an equivalence, and this is its inverse direction. -/
public abbrev moduleCatIntEquivalence : AddCommGrpCat.{a} ≌ ModuleCat.{a} ℤ :=
  (forget₂ (ModuleCat.{a} ℤ) AddCommGrpCat).asEquivalence.symm

/-- A finite abelian group is a module-finite `ℤ`-module. -/
public theorem moduleFinite_moduleCatIntEquivalence_obj (A : AddCommGrpCat.{a}) [Finite A] :
    Module.Finite ℤ (moduleCatIntEquivalence.functor.obj A) := by
  have : Finite ((𝟭 AddCommGrpCat.{a}).obj A) := ‹Finite A›
  have : Finite (moduleCatIntEquivalence.functor.obj A) :=
    Finite.of_injective (moduleCatIntEquivalence.unitIso.inv.app A).hom
      (ConcreteCategory.bijective_of_isIso (moduleCatIntEquivalence.unitIso.inv.app A)).1
  infer_instance

end AddCommGrpCat

end
