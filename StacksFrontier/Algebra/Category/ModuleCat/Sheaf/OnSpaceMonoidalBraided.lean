module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections

/-!
# The monoidal structure of Tag 01CA on a ringed space is symmetric

`Stacks.SheafOfModules.OnSpace.monoidal` is the monoidal structure on sheaves of `O_X`-modules
whose tensor product is the sheafified tensor product `Stacks.SheafOfModules.Tensor.sheafTensor`
of [Stacks, Tag 01CA] *on the
nose*.  It carried no braiding, and this file supplies one: the symmetry constraint
`Stacks.SheafOfModules.tensorSheafBraiding` of the tensor product sheaf.

Nothing about the braiding is reproved.  The structure is transported along the identity functor
`Stacks.SheafOfModules.OnSpace.sheafModuleToLocalized` into the localized monoidal category, by
`CategoryTheory.BraidedCategory.ofFaithful`, whose hypothesis is
`Stacks.SheafOfModules.braiding_hom_eq` — the compatibility of the localized braiding with
`Stacks.SheafOfModules.tensorObjIso`, proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence`.  The same transport
expresses the associator of `monoidal` as the localized associator conjugated by
`Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso`.

## Main definitions

* `Stacks.SheafOfModules.OnSpace.braided` and `Stacks.SheafOfModules.OnSpace.symmetric`: **the
  braiding and its symmetry for `monoidal`**, with braiding
  `Stacks.SheafOfModules.tensorSheafBraiding`.
* `Stacks.SheafOfModules.OnSpace.sheafModuleLocalizedBraided` and
  `…sheafModuleLocalizedSymmetric`: the braiding and the symmetry of the localized structure
  `Stacks.SheafOfModules.OnSpace.sheafModuleLocalizedMonoidal`, which is what is transported.

## Main results

* `Stacks.SheafOfModules.OnSpace.braiding_eq_tensorSheafBraiding`: the braiding of `braided`
  **is** `Stacks.SheafOfModules.tensorSheafBraiding`, by `rfl`.
* `Stacks.SheafOfModules.OnSpace.associator_hom_eq`: **the associator of `monoidal` is the
  localized associator conjugated by the comparison isomorphism.**  This is the handle a
  downstream identification of the associator with a hand-built one needs.
* `Stacks.SheafOfModules.OnSpace.sheafModuleUnitIso_eq`: the unit comparison chosen by
  `OnSpace` is the one chosen by `Stacks.SheafOfModules.sheafifyUnitIso`.  This is what
  identifies the two localizations.
* `Stacks.SheafOfModules.OnSpace.sheafModuleTensorCompareIso_eq`: the comparison isomorphism of
  `OnSpace` is `Stacks.SheafOfModules.tensorObjIso`.

## Implementation notes

**Why the two localizations have to be identified at all.** `OnSpace.monoidal` localizes
sheafification at the unit comparison `OnSpace.sheafModuleUnitIso`, while
`Stacks.SheafOfModules.monoidalCategory` localizes the same functor at the same class of
morphisms but at `Stacks.SheafOfModules.sheafifyUnitIso`.  The two comparisons are equal —
`sheafModuleUnitIso_eq` — but not definitionally: one of them carries a `Functor.map` of an
`eqToHom`, and `CategoryTheory.inv` is not an exposed definition, so the two localized monoidal
structures are not `rfl`-equal and the braiding of one is not usable for the other.

The repair is to make the unit comparison a *variable*: `localizedMonoidalOfUnit` and
`localizedBraidedOfUnit` take it as an argument, so that the two instantiations can be compared
by `subst` rather than by unfolding — `localizedBraidedOfUnit_congr`.  Each instantiation is the
corresponding named structure by `rfl`, since neither tensor product nor braiding of the
localization mentions the unit comparison; only the unitors do.

**The associator.** The associator of `monoidal` is not compared with the localized one by
unfolding either: `monoidal` is `CategoryTheory.Monoidal.transport`ed along a `ULift`
equivalence, so its associator carries that equivalence's unit isomorphisms. What is used
instead is that `sheafModuleToLocalized` is a monoidal functor, whose associativity axiom
`CategoryTheory.Functor.LaxMonoidal.associativity` *is* the statement that the associator of
`monoidal` is the localized one conjugated by the tensorator — and the tensorator is
`sheafModuleTensorCompareIso` by `rfl`.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace Stacks.SheafOfModules.OnSpace

open Stacks.SheafOfModules.TensorStalkRingedSpace

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-! ### The localized structure, with its unit comparison as a variable -/

/-- The type of the unit-object comparison which parametrises the monoidal localization of
sheafification. -/
abbrev localizedUnitIsoType :=
  (Stacks.SheafOfModules.sheafifyFunctor X.presheaf (structureSheafRing X).property).obj
      (𝟙_ (PresheafOfModules.{u}
        (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf))) ≅
    SheafOfModules.unit (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.presheaf
      (structureSheafRing X).property)

/-- The localized monoidal structure, as a function of the chosen unit comparison. -/
@[instance_reducible]
def localizedMonoidalOfUnit (e : localizedUnitIsoType X) :
    MonoidalCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (L := Stacks.SheafOfModules.sheafifyFunctor X.presheaf (structureSheafRing X).property)
    (W := Stacks.SheafOfModules.localIso (J := JX X) X.presheaf) e))

/-- The braiding of the localized monoidal structure, as a function of the chosen unit
comparison. -/
@[instance_reducible]
def localizedBraidedOfUnit (e : localizedUnitIsoType X) :
    @BraidedCategory _ _ (localizedMonoidalOfUnit X e) :=
  inferInstanceAs (BraidedCategory (LocalizedMonoidal
    (L := Stacks.SheafOfModules.sheafifyFunctor X.presheaf (structureSheafRing X).property)
    (W := Stacks.SheafOfModules.localIso (J := JX X) X.presheaf) e))

/-- The symmetry of the localized monoidal structure, as a function of the chosen unit
comparison. -/
@[instance_reducible]
def localizedSymmetricOfUnit (e : localizedUnitIsoType X) :
    @SymmetricCategory _ _ (localizedMonoidalOfUnit X e) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (L := Stacks.SheafOfModules.sheafifyFunctor X.presheaf (structureSheafRing X).property)
    (W := Stacks.SheafOfModules.localIso (J := JX X) X.presheaf) e))

/-- **The braiding of the localized monoidal structure does not depend on the unit
comparison.**  Only the unitors of the localization do, so this is `subst` and `rfl`; it is
stated because the two unit comparisons in play are equal but not definitionally equal. -/
theorem localizedBraidedOfUnit_congr (e₁ e₂ : localizedUnitIsoType X) (h : e₁ = e₂)
    (A B : SheafOfModules.{u} (structureSheafRing X)) :
    BraidedCategory.braiding (self := localizedBraidedOfUnit X e₁) A B =
      BraidedCategory.braiding (self := localizedBraidedOfUnit X e₂) A B := by
  subst h; rfl

/-- **The braiding of the localized monoidal structure of `OnSpace`.** -/
abbrev sheafModuleLocalizedBraided : @BraidedCategory _ _ (sheafModuleLocalizedMonoidal X) :=
  localizedBraidedOfUnit X (sheafModuleUnitIso X)

/-- **The symmetry of the localized monoidal structure of `OnSpace`.** -/
abbrev sheafModuleLocalizedSymmetric :
    @SymmetricCategory _ _ (sheafModuleLocalizedMonoidal X) :=
  localizedSymmetricOfUnit X (sheafModuleUnitIso X)

/-! ### The two localizations agree -/

/-- **The unit comparison chosen by `OnSpace` is the one chosen by
`Stacks.SheafOfModules.sheafifyUnitIso`.**  `OnSpace`'s carries one extra factor, the
sheafification of an `eqToHom` between two spellings of the presheaf tensor unit; that `eqToHom`
is an identity. -/
theorem sheafModuleUnitIso_eq : sheafModuleUnitIso X =
    Stacks.SheafOfModules.sheafifyUnitIso X.presheaf (structureSheafRing X).property := by
  apply Iso.ext
  show (sheafModuleSheafification X).map (eqToHom rfl) ≫ _ = _
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- **The comparison isomorphism of `OnSpace` is `Stacks.SheafOfModules.tensorObjIso`.**  The
two are the same composite; they are compared on inverses because `CategoryTheory.inv`, which
both `.hom`s contain, is not an exposed definition. -/
theorem sheafModuleTensorCompareIso_eq (A B : SheafOfModules.{u} (structureSheafRing X)) :
    sheafModuleTensorCompareIso X A B =
      Stacks.SheafOfModules.tensorObjIso X.presheaf (structureSheafRing X).property A B :=
  Iso.ext ((Iso.inv_eq_inv _ _).mp rfl)

/-- **The braiding of `OnSpace`'s localized structure is the braiding of
`Stacks.SheafOfModules.braidedCategory`.** -/
theorem sheafModuleLocalizedBraiding_eq (A B : SheafOfModules.{u} (structureSheafRing X)) :
    BraidedCategory.braiding (self := sheafModuleLocalizedBraided X) A B =
      BraidedCategory.braiding
        (self := Stacks.SheafOfModules.braidedCategory X.presheaf
          (structureSheafRing X).property) A B :=
  localizedBraidedOfUnit_congr X _ _ (sheafModuleUnitIso_eq X) A B

/-- **The comparison isomorphism carries the localized braiding to the symmetry constraint of
the tensor product sheaf.**  This is `Stacks.SheafOfModules.braiding_hom_eq` read at `OnSpace`'s
localization, and it is the hypothesis of `CategoryTheory.BraidedCategory.ofFaithful`. -/
theorem compareIso_hom_comp_tensorSheafBraiding
    (A B : SheafOfModules.{u} (structureSheafRing X)) :
    (sheafModuleTensorCompareIso X A B).hom ≫
        (Stacks.SheafOfModules.tensorSheafBraiding X.presheaf (structureSheafRing X).property
          A B).hom =
      (BraidedCategory.braiding (self := sheafModuleLocalizedBraided X) A B).hom ≫
        (sheafModuleTensorCompareIso X B A).hom := by
  rw [sheafModuleTensorCompareIso_eq, sheafModuleTensorCompareIso_eq,
    sheafModuleLocalizedBraiding_eq]
  exact (Stacks.SheafOfModules.braiding_hom_eq X.presheaf (structureSheafRing X).property
    A B).symm

/-! ### The braiding and the symmetry -/

section Braided

attribute [local instance] monoidal sheafModuleToLocalizedMonoidal

/-- The identity functor from sheaves of modules to the localized monoidal category is
faithful. -/
theorem sheafModuleToLocalized_faithful : (sheafModuleToLocalized X).Faithful := ⟨fun h => h⟩

attribute [local instance] sheafModuleToLocalized_faithful

/-- The tensorator of `Stacks.SheafOfModules.OnSpace.sheafModuleToLocalized` is the comparison
isomorphism. -/
theorem sheafModuleToLocalized_mu (A B : SheafOfModules.{u} (structureSheafRing X)) :
    Functor.LaxMonoidal.μ (sheafModuleToLocalized X) A B =
      (sheafModuleTensorCompareIso X A B).hom := rfl

/-- **The monoidal structure of [Stacks, Tag 01CA] on a ringed space is braided**, the braiding
being the symmetry constraint `Stacks.SheafOfModules.tensorSheafBraiding` of the tensor product
sheaf.

Like `Stacks.SheafOfModules.OnSpace.monoidal` itself this is not a global instance: the modules
on a ringed space carry several monoidal structures with the same isomorphism class and
different terms, so a file that wants this one asks for it with `attribute [local instance]`. -/
@[instance_reducible]
def braided : @BraidedCategory _ _ (monoidal X) :=
  letI : BraidedCategory (localizedSheafModules X) := sheafModuleLocalizedBraided X
  BraidedCategory.ofFaithful (sheafModuleToLocalized X)
    (fun A B => Stacks.SheafOfModules.tensorSheafBraiding X.presheaf
      (structureSheafRing X).property A B)
    (fun A B => compareIso_hom_comp_tensorSheafBraiding X A B)

/-- **The braiding of `braided` is the symmetry constraint of the tensor product sheaf**, on the
nose. -/
theorem braiding_eq_tensorSheafBraiding (A B : SheafOfModules.{u} (structureSheafRing X)) :
    BraidedCategory.braiding (self := braided X) A B =
      Stacks.SheafOfModules.tensorSheafBraiding X.presheaf (structureSheafRing X).property A B :=
  rfl

/-- **The braiding is a symmetry**: `Stacks.SheafOfModules.tensorSheafBraiding` twice is the
identity. -/
@[instance_reducible]
def symmetric : @SymmetricCategory _ _ (monoidal X) :=
  letI : SymmetricCategory (localizedSheafModules X) := sheafModuleLocalizedSymmetric X
  letI := braided X
  letI : (sheafModuleToLocalized X).Braided :=
    { braided := fun A B => compareIso_hom_comp_tensorSheafBraiding X A B }
  SymmetricCategory.ofFaithful (sheafModuleToLocalized X)

/-- **The braiding of `braided` is a symmetry**: `tensorSheafBraiding` twice is the identity.
This is `Stacks.SheafOfModules.tensorSheafBraiding_trans_self`, and it is the symmetry axiom of
`Stacks.SheafOfModules.OnSpace.symmetric` stated as an equation of morphisms. -/
theorem braiding_symmetry (A B : SheafOfModules.{u} (structureSheafRing X)) :
    (BraidedCategory.braiding (self := braided X) A B).hom ≫
        (BraidedCategory.braiding (self := braided X) B A).hom = 𝟙 _ :=
  congrArg Iso.hom (Stacks.SheafOfModules.tensorSheafBraiding_trans_self X.presheaf
    (structureSheafRing X).property A B)

/-! ### The associator -/

/-- **The associator of `monoidal` is the localized associator conjugated by the comparison
isomorphism.**  This is the associativity axiom of the monoidal functor
`Stacks.SheafOfModules.OnSpace.sheafModuleToLocalized`, solved for the associator. -/
theorem compareIso_comp_associator (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    MonoidalCategoryStruct.whiskerRight
          (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct)
          (sheafModuleTensorCompareIso X A B).hom C ≫
        (sheafModuleTensorCompareIso X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B))) C).hom ≫
          (α_ A B C).hom =
      (MonoidalCategoryStruct.associator
            (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct) A B C).hom ≫
          MonoidalCategoryStruct.whiskerLeft
              (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct) A
              (sheafModuleTensorCompareIso X B C).hom ≫
            (sheafModuleTensorCompareIso X A
              ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (B)).obj (C)))).hom :=
  Functor.LaxMonoidal.associativity (sheafModuleToLocalized X) A B C

/-- `Stacks.SheafOfModules.OnSpace.compareIso_comp_associator` solved for the associator of
`monoidal`. -/
theorem associator_hom_eq (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    (α_ A B C).hom =
      (sheafModuleTensorCompareIso X ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B))) C).inv ≫
        MonoidalCategoryStruct.whiskerRight
            (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct)
            (sheafModuleTensorCompareIso X A B).inv C ≫
          (MonoidalCategoryStruct.associator
                (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct) A B C).hom ≫
            MonoidalCategoryStruct.whiskerLeft
                (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct) A
                (sheafModuleTensorCompareIso X B C).hom ≫
              (sheafModuleTensorCompareIso X A
                ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (B)).obj (C)))).hom :=
  Functor.Monoidal.map_associator (sheafModuleToLocalized X) A B C

/-- The inverse associator of `monoidal`, as the localized one conjugated by the comparison
isomorphism. -/
theorem associator_inv_eq (A B C : SheafOfModules.{u} (structureSheafRing X)) :
    (α_ A B C).inv =
      (sheafModuleTensorCompareIso X A ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (B)).obj (C)))).inv ≫
        MonoidalCategoryStruct.whiskerLeft
            (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct) A
            (sheafModuleTensorCompareIso X B C).inv ≫
          (MonoidalCategoryStruct.associator
                (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct) A B C).inv ≫
            MonoidalCategoryStruct.whiskerRight
                (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct)
                (sheafModuleTensorCompareIso X A B).hom C ≫
              (sheafModuleTensorCompareIso X
                ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj (A)).obj (B))) C).hom :=
  Functor.Monoidal.map_associator_inv (sheafModuleToLocalized X) A B C

/-- Left whiskering in `monoidal` is left whiskering in the localized structure conjugated by
the comparison isomorphism. -/
theorem whiskerLeft_eq (A : SheafOfModules.{u} (structureSheafRing X))
    {B₁ B₂ : SheafOfModules.{u} (structureSheafRing X)} (f : B₁ ⟶ B₂) :
    A ◁ f =
      (sheafModuleTensorCompareIso X A B₁).inv ≫
        MonoidalCategoryStruct.whiskerLeft
            (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct) A f ≫
          (sheafModuleTensorCompareIso X A B₂).hom :=
  Functor.Monoidal.map_whiskerLeft (sheafModuleToLocalized X) A f

/-- Right whiskering in `monoidal` is right whiskering in the localized structure conjugated by
the comparison isomorphism. -/
theorem whiskerRight_eq {A₁ A₂ : SheafOfModules.{u} (structureSheafRing X)} (f : A₁ ⟶ A₂)
    (B : SheafOfModules.{u} (structureSheafRing X)) :
    f ▷ B =
      (sheafModuleTensorCompareIso X A₁ B).inv ≫
        MonoidalCategoryStruct.whiskerRight
            (self := (sheafModuleLocalizedMonoidal X).toMonoidalCategoryStruct) f B ≫
          (sheafModuleTensorCompareIso X A₂ B).hom :=
  Functor.Monoidal.map_whiskerRight (sheafModuleToLocalized X) f B

/-- The braiding of `braided` is the localized braiding conjugated by the comparison
isomorphism. -/
theorem braiding_hom_eq_localized (A B : SheafOfModules.{u} (structureSheafRing X)) :
    (BraidedCategory.braiding (self := braided X) A B).hom =
      (sheafModuleTensorCompareIso X A B).inv ≫
        (BraidedCategory.braiding (self := sheafModuleLocalizedBraided X) A B).hom ≫
          (sheafModuleTensorCompareIso X B A).hom :=
  let : BraidedCategory (localizedSheafModules X) := sheafModuleLocalizedBraided X
  let := braided X
  let : (sheafModuleToLocalized X).Braided :=
    { braided := fun A B => compareIso_hom_comp_tensorSheafBraiding X A B }
  Functor.map_braiding (sheafModuleToLocalized X) A B

end Braided

end Stacks.SheafOfModules.OnSpace

end
