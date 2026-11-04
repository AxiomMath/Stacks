module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
public import StacksFrontier.AlgebraicGeometry.InternalHom.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The internal hom for sheaves of modules

Let `𝒪` be a sheaf of commutative rings on a site `(C, J)`. This file equips the category
`SheafOfModules` of sheaves of `𝒪`-modules with a symmetric monoidal structure and with an
internal hom, and identifies the internal hom explicitly. It discharges the one hypothesis that
`StacksFrontier/AlgebraicGeometry/InternalHom/Basic.lean` had to leave open, namely
`Stacks.InternalHom.sheafOfModulesMonoidalClosed`'s monoidal structure on `SheafOfModules`.

**The route taken, and why it is not the expected one.** The sibling file predicted that the
sheaf level would be blocked by a circularity: the monoidal structure on sheaves reduces to
"tensoring a local isomorphism by a fixed module is again a local isomorphism", and Mathlib
proves the corresponding statement for presheaves valued in a closed monoidal category
(`CategoryTheory.GrothendieckTopology.W.whiskerLeft`) *through* the internal hom in explicit end
form (`CategoryTheory.Presheaf.isSheaf_functorEnrichedHom`), so the abstract adjoint of the
sibling file could not be used to get it. **That circularity does not arise here, because this
repository already proves the whiskering statement for presheaves of modules by a completely
different, elementary route.** `Stacks.SheafOfModules.TensorSheafification.W_whiskerRight` — the
  "Helper B" of Stacks Tag 05NA —
proves stability of `J.W` under right whiskering directly, by decomposing an element of the
kernel of a tensored map locally (`Stacks.SheafOfModules.TensorSheafification.rTensor_ker_decomp`,
`Stacks.SheafOfModules.TensorSheafification.exists_locally_ker_decomp`), with no internal hom
  anywhere. Left whiskering follows by
the braiding. So no end form is constructed in this file, and none is needed: the whole sheaf
level follows from facts already present.

Given that one input, the rest is Mathlib's localization and reflection machinery.
`PresheafOfModules.sheafification` is a localization functor at the local isomorphisms (the
`Functor.IsLocalization` instance of `Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean`,
proved there from `PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`), so
`CategoryTheory.Localization.Monoidal` transports the monoidal structure of presheaves of modules
to sheaves of modules; and sheaves of modules are a reflective subcategory with a monoidal
reflector, so `CategoryTheory.Monoidal.Reflective.monoidalClosed` — the construction Mathlib's own
`Mathlib/CategoryTheory/Sites/Monoidal.lean` points to in its TODO — turns the internal hom for
presheaves of modules of the sibling file into an internal hom for sheaves of modules.

## Main definitions

* `Stacks.SheafInternalHom.localIso`: the local isomorphisms of presheaves of modules, i.e. the
  morphisms inverted by sheafification, as a `MorphismProperty`.
* `Stacks.SheafInternalHom.monoidalCategory`: the monoidal structure on `SheafOfModules`,
  obtained by localizing the one on presheaves of modules. Its tensor product is the
  sheafification of the sectionwise tensor product, and its unit is the sheafification of the
  presheaf unit.
* `Stacks.SheafInternalHom.braidedCategory` and `Stacks.SheafInternalHom.symmetricCategory`: that
  monoidal structure is symmetric.
* `Stacks.SheafInternalHom.sheafifyMonoidal`: sheafification is a monoidal functor from
  presheaves of modules to sheaves of modules.
* `Stacks.SheafInternalHom.monoidalClosed`: **the internal hom for sheaves of modules.**
* `Stacks.SheafInternalHom.sheafifyCounitIso`, `Stacks.SheafInternalHom.tensorSheafifyIso` and
  `Stacks.SheafInternalHom.tensorLeftIso`: the comparison isomorphisms between the sheaf tensor
  product and the sheafified objectwise tensor product `PresheafOfModules.tensorBifunctor`.
* `Stacks.SheafInternalHom.schemeMonoidalCategory` and
  `Stacks.SheafInternalHom.schemeMonoidalClosed`: both structures on the sheaves of modules over
  a scheme, in Mathlib's own `AlgebraicGeometry.Scheme.Modules` spelling.

## Main results

* `Stacks.SheafInternalHom.isMonoidal_localIso`: the local isomorphisms of presheaves of modules
  are stable under tensoring on either side. This is the single input the sheaf level needs, and
  it comes from Stacks Tag 05NA.
* `Stacks.SheafInternalHom.ihom_obj`: the internal hom of two sheaves of modules is the
  sheafification of the internal hom of their underlying presheaves of modules. This holds by
  `rfl`, which is what makes the next two statements usable.
* `Stacks.SheafInternalHom.isSheaf_ihom`: **no sheafification is needed.** The internal hom of
  presheaves of modules whose target is (the underlying presheaf of) a sheaf is already a sheaf.
  Together with `ihom_obj` this says that the sheafification in the formula for the sheaf
  internal hom is an isomorphism, so the sheaf internal hom *is* the presheaf internal hom.
* `Stacks.SheafInternalHom.preservesColimitsOfSize_tensorLeft`: tensoring on the left in
  `SheafOfModules` preserves colimits, being a left adjoint.
* `Stacks.SheafInternalHom.monoidalClosedOfInternalHom`: both hypotheses of
  `Stacks.InternalHom.sheafOfModulesMonoidalClosed` discharged, so that the sibling file's
  statement is now an unconditional theorem.
* `Stacks.SheafInternalHom.tensorLeftIso`: the monoidal `tensorLeft` of a sheaf of modules is
  isomorphic to "forget, tensor sectionwise, sheafify", which is the canonical tensor functor
  `Stacks.SheafOfModules.Tensor.sheafTensor` at that sheaf.

## Implementation notes

**Which of the three planned steps were reached.** All three, but step 1 was reached in a
different and stronger form than planned: rather than constructing the internal hom as an end
and then proving the end is a sheaf, the internal hom is obtained abstractly and *then* proved to
need no sheafification (`isSheaf_ihom`), via Mathlib's reflection instance
`CategoryTheory.Monoidal.Reflective.instIsIsoAppUnitObjIhom`. The explicit end has therefore not
been built, and nothing here depends on one; see "What is not done".

**Transparency.** `Stacks.SheafOfModules.TensorSheafification.structureSheaf` and
  `Stacks.SheafOfModules.TensorSheafification.sheafify` are plain `def`s, so
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj` reduces to
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪` only at
default transparency, and instance search does not see it. Every Mathlib fact about
`PresheafOfModules.sheafification α` is stated with `α : R₀ ⟶ R.obj`, so it matches only when the
index is spelled `(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj`; but the
  monoidal structure on presheaves
of modules is found only when the index is spelled
  `Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪`. The two
requirements are reconciled exactly as the sibling file
`StacksFrontier/AlgebraicGeometry/InvertibleLocallyFree/Basic.lean` does it: the index is always
`(Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).obj`, and the monoidal, symmetric
  and closed structures on
presheaves of modules over it are introduced as `local instance`s whose bodies are `change`
followed by `infer_instance`. Replacing `Stacks.SheafOfModules.TensorSheafification.structureSheaf`
  by a reducible packaging
instead was tried and does *not* work: with the sheaf of rings an `abbrev`, the fullness and
faithfulness instances for `SheafOfModules.forget ⋙ PresheafOfModules.restrictScalars` are no
longer found, which kills the reflection argument. No compiler option is switched anywhere in
this file, and the `local instance`s are confined to the sections that need them.

**Universes.** Sections 1 and 2 are polymorphic in the site universes `u v` and the module
universe `w` independently. Section 3 is not: `Stacks.InternalHom.instMonoidalClosed`, the
internal hom for presheaves of modules, needs `C : Type u`, `[SmallCategory C]` and
`𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}` — site and sections in one universe — because the special adjoint
functor theorem is applied at the universe of the module sections. That constraint is inherited
verbatim: the monoidal structure on `SheafOfModules` is universe-polymorphic, the internal hom on
it is not. It is not a real restriction for the intended consumers, since `Opens X` is a
`SmallCategory`; section 4 is the instance of it that schemes need. The prediction in the sibling
file that the module universe would be forced to `max u v w`, as in
`StacksFrontier/AlgebraicGeometry/SheafDescent/Basic.lean`, did not materialise, because that
constraint comes from writing the internal hom out as an end over the slice category and nothing
here does.

**Where the content actually lives.** `isMonoidal_localIso` is four lines and is the only
mathematical step in this file; everything else is transport. The content it transports is
`Stacks.SheafOfModules.TensorSheafification.W_whiskerRight`, roughly five hundred lines
of local kernel decomposition proved with [Stacks, Tag 05NA].

## What is not done

The internal hom is **not** written out as an end. No analogue of
`CategoryTheory.Enriched.FunctorCategory.functorEnrichedHom` or of
`CategoryTheory.Presheaf.isSheaf_functorEnrichedHom` is built for presheaves of modules, and the
TODO in `Mathlib/CategoryTheory/Sites/Monoidal.lean` asking for exactly that is not addressed.
`Stacks.SheafInternalHom.isSheaf_ihom` settles the *mathematical* question that the end form was
wanted for — no sheafification is needed — but it does so abstractly, so the sections of the
internal hom over an object of the site still have no formula here. Unwinding them to the
restriction-compatible families of `𝒪`-linear maps of Stacks Tag 0B8K would need the end, or the
generalisation of `Stacks.SheafDescent.DualSection` from the unit to an arbitrary target.

Clause 2 of Stacks Tag 0B8M is **not** carried from its presheaf form
(`Stacks.InvertibleRankOne.exists_cover_trivialization_of_tensorLeft`) to the sheaf form. The
comparison isomorphisms asked for are here — `tensorSheafifyIso` and `tensorLeftIso` — but they
are not sufficient, and this is a genuine finding rather than a shortfall of effort: the presheaf
form hypothesises `(MonoidalCategory.tensorLeft L).IsEquivalence` for `L` a *presheaf* of modules,
whereas a sheaf of modules invertible in the monoidal structure built here satisfies only that
`tensorLeft L` is an equivalence of *sheaves*, i.e. that `tensorLeft L.val` becomes an equivalence
after sheafification. Those are not the same hypothesis and the second does not imply the first,
since the presheaf tensor product of two sheaves is not a sheaf. The way forward is either to
reprove the clause-2 argument with the sheaf-level hypothesis, taking stalks as the source does,
or route through `Stacks.SheafDescent.isInvertible_of_trivialization`, which already works at the
sheaf level.

No monoidal structure is placed on the slice sites `J.over X`, and no compatibility of the tensor
product with restriction to a slice is proved. No instance is declared globally: every result is a
`def` or a `local instance`, as in the sibling file, so that nothing conflicts with a monoidal
structure coming from chosen finite products. No Stacks attribute is attached to anything here;
the relevant tags are carried elsewhere in the repository.

## References

* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public section

universe v u w

open CategoryTheory MonoidalCategory Limits Stacks.SheafOfModules.TensorSheafification

namespace Stacks.SheafInternalHom

section LocalIsomorphisms

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w}) [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Local isomorphisms of presheaves of modules are stable under tensoring on the left. This is
`Stacks.SheafOfModules.TensorSheafification.W_whiskerRight` conjugated by the braiding; the
  braiding exists because the ring
presheaf factors through `CommRingCat`. -/
theorem W_whiskerLeft (X : PresheafOfModules.{w} (structureRingPresheaf 𝒪))
    {A B : PresheafOfModules.{w} (structureRingPresheaf 𝒪)} (f : A ⟶ B)
    (hf : J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map f)) :
    J.W ((PresheafOfModules.toPresheaf (structureRingPresheaf 𝒪)).map (X ◁ f)) := by
  have h := W_whiskerRight 𝒪 f X hf
  have hnat : X ◁ f = (β_ X A).hom ≫ (f ▷ X) ≫ (β_ X B).inv := by
    rw [← Category.assoc, ← BraidedCategory.braiding_naturality_right X f,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hnat, Functor.map_comp, Functor.map_comp]
  exact MorphismProperty.RespectsIso.precomp _ _ _
    (MorphismProperty.RespectsIso.postcomp _ _ _ h)

end LocalIsomorphisms

section MonoidalStructure

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules

/-- The local isomorphisms of presheaves of modules: the morphisms whose underlying morphism of
presheaves of abelian groups is locally bijective, equivalently those inverted by sheafification
(`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`). -/
abbrev localIso : MorphismProperty (PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf (structureSheaf 𝒪 h𝒪).obj)

/-- **The local isomorphisms of presheaves of modules form a monoidal class of morphisms.** This
is the single input that the monoidal structure on sheaves of modules needs, and the only
mathematical step in this file. Both halves come from Stacks Tag 05NA: right whiskering is
`Stacks.SheafOfModules.TensorSheafification.W_whiskerRight`, proved there by decomposing an element
  of the kernel of a tensored
map locally, and left whiskering is `W_whiskerLeft`. Multiplicativity is inherited from `J.W`. -/
local instance isMonoidal_localIso : (localIso 𝒪 h𝒪).IsMonoidal where
  whiskerLeft X _ _ g hg := W_whiskerLeft 𝒪 X g hg
  whiskerRight f hf Y := W_whiskerRight 𝒪 f Y hf

/-- Sheafification of presheaves of modules is a localization functor at the local isomorphisms.
Mathlib knows this; the `inferInstanceAs` unfolds the `def`
  `Stacks.SheafOfModules.TensorSheafification.sheafify`. -/
local instance isLocalization_sheafify : (sheafify 𝒪 h𝒪).IsLocalization (localIso 𝒪 h𝒪) :=
  inferInstanceAs ((PresheafOfModules.sheafification
    (𝟙 (structureSheaf 𝒪 h𝒪).obj)).IsLocalization _)

/-- **The monoidal structure on sheaves of modules.** Obtained by localizing the sectionwise
monoidal structure on presheaves of modules at the local isomorphisms, which is legitimate by
`isMonoidal_localIso`. Concretely the tensor product of two sheaves of modules is the
sheafification of the sectionwise tensor product of their underlying presheaves, and the unit is
the sheafification of the presheaf unit; see `tensorLeftIso`. Not an instance, since on some
sites it would conflict with a monoidal structure deduced from chosen finite products. -/
@[instance_reducible]
noncomputable def monoidalCategory :
    MonoidalCategory (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (sheafify 𝒪 h𝒪) (localIso 𝒪 h𝒪) (Iso.refl _)))

attribute [local instance] monoidalCategory

/-- **Sheafification is a monoidal functor.** This is the statement that the sheafification of a
tensor product of presheaves of modules is the tensor product of the sheafifications, coherently;
its structure isomorphism is `tensorSheafifyIso`. -/
@[instance_reducible]
noncomputable def sheafifyMonoidal : (sheafify 𝒪 h𝒪).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (sheafify 𝒪 h𝒪) (localIso 𝒪 h𝒪) (Iso.refl _)).Monoidal

attribute [local instance] sheafifyMonoidal

/-- The monoidal structure of `monoidalCategory` is braided. -/
@[instance_reducible]
noncomputable def braidedCategory :
    BraidedCategory (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  inferInstanceAs (BraidedCategory
    (LocalizedMonoidal (sheafify 𝒪 h𝒪) (localIso 𝒪 h𝒪) (Iso.refl _)))

/-- The monoidal structure of `monoidalCategory` is symmetric, the structure sheaf of rings being
commutative. -/
@[instance_reducible]
noncomputable def symmetricCategory :
    SymmetricCategory (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (sheafify 𝒪 h𝒪) (localIso 𝒪 h𝒪) (Iso.refl _)))

/-- **The comparison isomorphism: tensoring commutes with sheafification.** For a fixed presheaf
of modules `M`, the sheafification of the objectwise tensor product `M ⊗ -`
(`PresheafOfModules.tensorBifunctor`) is the sheaf tensor product of the sheafification of `M`
with the sheafification of `-`, naturally. This is the monoidality isomorphism of
`sheafifyMonoidal`, read as a natural isomorphism of functors. -/
noncomputable def tensorSheafifyIso (M : PresheafOfModules.{w} (structureSheaf 𝒪 h𝒪).obj) :
    sheafify 𝒪 h𝒪 ⋙ tensorLeft ((sheafify 𝒪 h𝒪).obj M) ≅
      (PresheafOfModules.tensorBifunctor.{v, u, w, w, w} 𝒪).obj M ⋙ sheafify 𝒪 h𝒪 :=
  NatIso.ofComponents (fun N ↦ Functor.Monoidal.μIso (sheafify 𝒪 h𝒪) M N)
    (fun f ↦ Functor.LaxMonoidal.μ_natural_right (sheafify 𝒪 h𝒪) M f)

/-- Sheafifying the underlying presheaf of a sheaf of modules returns it: the counit of the
sheafification adjunction is an isomorphism, sheaves of modules being reflective. -/
noncomputable def sheafifyCounitIso :
    (SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
      PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)) ⋙
        sheafify 𝒪 h𝒪 ≅ 𝟭 _ :=
  asIso (sheafifyAdjunction 𝒪 h𝒪).counit

/-- **The monoidal `tensorLeft` on sheaves of modules is the sheafified objectwise tensor
product.** This identifies the abstract localized tensor product with the canonical tensor
functor of this repository, `Stacks.SheafOfModules.Tensor.sheafTensor`: forget to presheaves,
tensor sectionwise with `PresheafOfModules.tensorBifunctor`, sheafify. -/
noncomputable def tensorLeftIso (A : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :
    tensorLeft A ≅ (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w}
      ⟨𝒪, Presheaf.isSheaf_of_isSheaf_comp _ 𝒪 (forget₂ CommRingCat RingCat) h𝒪⟩).obj A :=
  ((curriedTensor _).mapIso ((sheafifyCounitIso 𝒪 h𝒪).app A)).symm ≪≫
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (sheafifyCounitIso 𝒪 h𝒪).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (tensorSheafifyIso 𝒪 h𝒪 _)

end MonoidalStructure

section MonoidalClosedStructure

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  isMonoidal_localIso isLocalization_sheafify monoidalCategory sheafifyMonoidal

/-- Presheaves of modules over the structure sheaf of rings are monoidal closed. Transported by
hand from `Stacks.InternalHom.instMonoidalClosed`, for the same transparency reason as
`Stacks.SheafOfModules.monoidalCategoryPresheafOfModules`; this is where the universe constraint
`[SmallCategory C]` and
`𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}` enters. -/
noncomputable local instance presheafMonoidalClosed :
    MonoidalClosed (PresheafOfModules.{u} (structureSheaf 𝒪 h𝒪).obj) := by
  change MonoidalClosed (PresheafOfModulesOfCommRing.{u} 𝒪)
  infer_instance

/-- **The internal hom for sheaves of modules.** Sheaves of modules are a reflective subcategory
of presheaves of modules whose reflector `sheafifyMonoidal` is monoidal, and presheaves of
modules are symmetric monoidal closed by `Stacks.InternalHom.instMonoidalClosed`; so
`CategoryTheory.Monoidal.Reflective.monoidalClosed` applies. This is the construction that
`Mathlib/CategoryTheory/Sites/Monoidal.lean` points to in its TODO. For the resulting formula see
`ihom_obj`, and for the fact that its sheafification is redundant see `isSheaf_ihom`. -/
@[instance_reducible]
noncomputable def monoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :=
  Monoidal.Reflective.monoidalClosed (sheafifyAdjunction 𝒪 h𝒪)

attribute [local instance] monoidalClosed

/-- **The internal hom of two sheaves of modules is the sheafification of the internal hom of
their underlying presheaves of modules.** True by `rfl`: the right adjoint produced by the
reflection argument is literally `forget ⋙ ihom ⋙ sheafify`. By `isSheaf_ihom` the
sheafification here is an isomorphism, so the sheaf internal hom is the presheaf internal hom. -/
theorem ihom_obj (M N : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    (ihom M).obj N = (sheafify 𝒪 h𝒪).obj ((ihom
      ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj M)).obj
      ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj N)) :=
  rfl

/-- **No sheafification is needed: the internal hom into a sheaf is already a sheaf.** For any
presheaf of modules `M` and any sheaf of modules `N`, the presheaf of modules `(ihom M).obj N` is
a sheaf. With `ihom_obj` this says that the sheaf internal hom agrees with the presheaf internal
hom, which is the expected answer and the reason an explicit end form was wanted. -/
theorem isSheaf_ihom (M : PresheafOfModules.{u} (structureSheaf 𝒪 h𝒪).obj)
    (N : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    Presheaf.IsSheaf J (((ihom M).obj
      ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj N)).presheaf) := by
  have : IsIso ((sheafifyAdjunction 𝒪 h𝒪).unit.app ((ihom M).obj
      ((SheafOfModules.forget (structureSheaf 𝒪 h𝒪) ⋙
        PresheafOfModules.restrictScalars (𝟙 (structureSheaf 𝒪 h𝒪).obj)).obj N))) :=
    inferInstance
  refine (Presheaf.isSheaf_of_iso_iff
    ((PresheafOfModules.toPresheaf _).mapIso (asIso ((sheafifyAdjunction 𝒪 h𝒪).unit.app _)))).2 ?_
  exact ((sheafify 𝒪 h𝒪).obj _).isSheaf

/-- Tensoring on the left in `SheafOfModules` preserves colimits of every size, being a left
adjoint once the internal hom exists. -/
theorem preservesColimitsOfSize_tensorLeft
    (M : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :
    PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
  (ihom.adjunction M).leftAdjoint_preservesColimits

/-- **Both hypotheses of `Stacks.InternalHom.sheafOfModulesMonoidalClosed` discharged.** The
sibling file reduced the internal hom for sheaves of modules to a monoidal structure on
`SheafOfModules` whose `tensorLeft` preserves colimits; `monoidalCategory` supplies the first and
`preservesColimitsOfSize_tensorLeft` the second, so that statement is now unconditional. Note
that this is a *second* construction of the internal hom, through the special adjoint functor
theorem rather than through reflection; `monoidalClosed` is the one to use. -/
@[instance_reducible]
noncomputable def monoidalClosedOfInternalHom :
    MonoidalClosed (SheafOfModules.{u} (structureSheaf 𝒪 h𝒪)) :=
  haveI : ∀ M : SheafOfModules.{u} (structureSheaf 𝒪 h𝒪),
      PreservesColimitsOfSize.{u, u} (tensorLeft M) :=
    preservesColimitsOfSize_tensorLeft 𝒪 h𝒪
  Stacks.InternalHom.sheafOfModulesMonoidalClosed (structureSheaf 𝒪 h𝒪)

end MonoidalClosedStructure

section Scheme

open AlgebraicGeometry

/-- The underlying presheaf of rings of the structure sheaf of a scheme is a sheaf. -/
theorem isSheaf_structureRingPresheaf (X : Scheme.{u}) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (structureRingPresheaf X.presheaf) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ X.sheaf.property

/-- The structure sheaf of rings of a scheme in the `Stacks.SheafOfModules.TensorSheafification`
  packaging is Mathlib's
`AlgebraicGeometry.Scheme.ringCatSheaf`. An equality, not merely an isomorphism: the underlying
presheaves are the same composite and the sheaf condition is a proposition. -/
theorem structureSheaf_eq_ringCatSheaf (X : Scheme.{u}) :
    structureSheaf X.presheaf (isSheaf_structureRingPresheaf X) = X.ringCatSheaf :=
  rfl

/-- **The monoidal structure on the sheaves of modules over a scheme**, in Mathlib's
`AlgebraicGeometry.Scheme.Modules` spelling. Deliberately a `def` and not an instance, for the
same reason as `monoidalCategory`. -/
@[instance_reducible]
noncomputable def schemeMonoidalCategory (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  monoidalCategory X.presheaf (isSheaf_structureRingPresheaf X)

/-- **The internal hom for the sheaves of modules over a scheme**, in Mathlib's
`AlgebraicGeometry.Scheme.Modules` spelling. The monoidal structure is carried in the type as a
`letI` rather than by an attribute, as `Stacks.InternalHom.schemeMonoidalClosed` does. -/
@[instance_reducible, ega "0 4.1.5" "special case"]
noncomputable def schemeMonoidalClosed (X : Scheme.{u}) :
    letI := schemeMonoidalCategory X
    MonoidalClosed X.Modules :=
  monoidalClosed X.presheaf (isSheaf_structureRingPresheaf X)

end Scheme

end Stacks.SheafInternalHom

end
