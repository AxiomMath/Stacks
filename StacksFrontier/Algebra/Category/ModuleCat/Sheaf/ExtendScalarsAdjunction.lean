module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension of scalars for sheaves of modules

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site `(C, J)`. Mathlib's
`SheafOfModules.restrictScalars α : SheafOfModules R' ⥤ SheafOfModules R` reads a sheaf of
`R'`-modules as a sheaf of `R`-modules. This file constructs its left adjoint, *extension of
scalars* `R' ⊗_R -`, and the adjunction

`Hom_{R'}(R' ⊗_R G, F) = Hom_R(G, F_R)`

which is Stacks 03CZ.

The construction is the composite of three steps: forget that a sheaf of `R`-modules is a
sheaf, extend scalars at the level of presheaves of modules, and sheafify. Only the middle
step has content, and it is taken as an instance hypothesis
`(PresheafOfModules.restrictScalars α.hom).IsRightAdjoint`; it is discharged here, with no
commutativity assumption on the sheaves of rings, whenever the site is small and its
universes agree with the universe of the sheaves of rings and modules.

## Main definitions

* `extendScalars α : SheafOfModules.{v} R ⥤ SheafOfModules.{v} R'`: extension of scalars
  along `α`, as the sheafification of the presheaf-level extension of scalars.
* `overId β` and `structureMap α`: a morphism of presheaves of rings, respectively of sheaves
  of rings, read as a structure map over the identity functor of the site, which is the shape
  `PresheafOfModules.pushforward` and `SheafOfModules.pushforward` expect. The lemmas
  `pushforward_overId` and `pushforward_structureMap` say that pushforward along the identity
  functor *is* restriction of scalars, so no comparison isomorphism is involved anywhere
  below.

## Main results

* `extendRestrictScalarsAdjunction α` (**Stacks 03CZ**): `extendScalars α` is left adjoint to
  `SheafOfModules.restrictScalars α`, together with the instances
  `(SheafOfModules.restrictScalars α).IsRightAdjoint` and `(extendScalars α).IsLeftAdjoint`,
  so that the left adjoint is available to instance resolution.
* `extendScalarsCompToSheaf`: the underlying sheaf of abelian groups of `extendScalars α` is
  the sheafification of the underlying presheaf of the presheaf-level extension of scalars.
* `full_restrictScalars_iff_isIso_counit`: restriction of scalars along `α` is full — hence
  fully faithful, since it is always faithful — if and only if the counit of the adjunction
  is an isomorphism. This is the route to Stacks 0930: see the implementation notes.
* `epi_counit_app`: every component `R' ⊗_R F_R ⟶ F` of the counit is an epimorphism, with no
  hypothesis on `α`, and `full_restrictScalars_of_mono_counit_app`: when sheaves of modules
  are abelian, restriction of scalars is full as soon as those components are monomorphisms.
  Together these say that what Stacks 0930 still needs is injectivity of the counit.
* `presheafRestrictScalars_isRightAdjoint`: for a small site in a single universe, extension
  of scalars for presheaves of modules exists along an arbitrary morphism of presheaves of
  (not necessarily commutative) rings.
* `extendScalarsIsoPullback`: `extendScalars α` is canonically isomorphic to Mathlib's
  `SheafOfModules.pullback` along the identity functor of the site, so this functor is the
  expected one and inherits anything proved about `SheafOfModules.pullback`.
* `extendScalarsIdIso`: extension of scalars along `𝟙 R` is the identity functor.

## Implementation notes

All four universes are independent, as in `SheafOfModules.restrictScalars` itself: the site
is `C : Type u'` with `Category.{v'} C`, the sheaves of rings are `RingCat.{u}`-valued and
the module universe is `v`. Nothing in the transfer from presheaves to sheaves couples them.
What does couple them is the presheaf-level hypothesis. That hypothesis is stated as a
typeclass rather than proved for two reasons:

* Mathlib's only unconditional source for it is
  `PresheafOfModules.pullbackObjIsDefined_eq_top`, whose proof resolves a presheaf of modules
  into free modules on representables, and so needs `C : Type u` with `SmallCategory C`,
  sheaves of rings in `RingCat.{u}` and modules in universe `u`. That is what
  `presheafRestrictScalars_isRightAdjoint` below records, for an arbitrary morphism of
  presheaves of rings.
* The construction that needs no smallness at all is the objectwise one,
  `M ↦ (X ↦ R'(X) ⊗_{R(X)} M(X))`. It is available in this repository only for presheaves of
  *commutative* rings (`Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`, and
  `Stacks.PullbackModel.extendScalars`), because `ModuleCat.extendScalars` is stated for
  `CommRing`. Sections of a `RingCat`-valued sheaf need not commute, so the objectwise
  construction is not available at the generality of this file; see the report accompanying
  this module.

Taking the hypothesis as a typeclass keeps those two sources interchangeable and lets the
sheaf-level statement be about an arbitrary morphism `α : R ⟶ R'` in `Sheaf J RingCat.{u}`,
rather than about one of the special shapes (a morphism induced by a map of presheaves of
commutative rings, or a structure map over a continuous functor) that the existing
constructions in this repository are tied to.

The adjunction is obtained from the presheaf-level one by
`CategoryTheory.Adjunction.restrictFullyFaithful` along the fully faithful
`SheafOfModules.forget`, with the second inclusion taken to be the identity functor — the
same device as `Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`. Both
comparison isomorphisms it asks for are `eqToIso` of a unitor, because `extendScalars α` is
*defined* as the composite that appears there and because
`SheafOfModules.restrictScalars α ⋙ SheafOfModules.forget R` is *literally*
`SheafOfModules.forget R' ⋙ PresheafOfModules.restrictScalars α.hom`, with
`PresheafOfModules.restrictScalars (𝟙 R'.obj)` literally the identity functor.

Stacks 0930 (restriction of scalars along an *epimorphism* of sheaves of rings is fully
faithful) is **not** proved here. `full_restrictScalars_iff_isIso_counit` reduces it to
invertibility of the counit of this adjunction, and `epi_counit_app` together with
`full_restrictScalars_of_mono_counit_app` reduce it further to the counit being a
monomorphism. That is the sheaf form of the implication "`R → R'` epi ⟹ `R' ⊗_R R' ≅ R'`" of
Stacks 04VN; proving it needs a tensor product of sheaves of rings over a sheaf of rings,
which does not exist in this repository. The variant
of 0930 with `Sheaf.IsLocallySurjective α` in place of `Epi α` is
`Stacks.SheafOfModules.ChangeOfRings.fullyFaithfulOfIsLocallySurjective`; combined with the
criterion here it gives `isIso_counit_of_isLocallySurjective`, so extension of scalars along
a locally surjective morphism of sheaves of rings is a left inverse of restriction of
scalars.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
-/

@[expose] public section

open CategoryTheory

universe v v' u u'

namespace Stacks.SheafOfModules.ChangeOfRings

section SmallSite

variable {C : Type u} [SmallCategory C] {R₀ R₀' : Cᵒᵖ ⥤ RingCat.{u}}

/-- `β` read as a morphism of presheaves of rings over the identity functor of the site,
which is the shape `PresheafOfModules.pushforward` expects. -/
def overId (β : R₀ ⟶ R₀') : R₀ ⟶ (𝟭 C).op ⋙ R₀' := β

/-- Restriction of scalars for presheaves of modules is the pushforward along the identity
functor of the site. -/
lemma pushforward_overId (β : R₀ ⟶ R₀') :
    PresheafOfModules.pushforward.{u} (overId β) = PresheafOfModules.restrictScalars.{u} β :=
  rfl

/-- On a small site whose universe is that of the presheaves of rings and of the modules,
restriction of scalars for presheaves of modules has a left adjoint — extension of scalars —
along an arbitrary morphism of presheaves of not necessarily commutative rings. This is
Mathlib's `PresheafOfModules.pullbackObjIsDefined_eq_top`, read through
`pushforward_overId`. -/
instance presheafRestrictScalars_isRightAdjoint (β : R₀ ⟶ R₀') :
    (PresheafOfModules.restrictScalars.{u} β).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top (overId β))

end SmallSite

section StructureMap

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- `α` read as a structure map over the identity functor of the site, which is the shape
`SheafOfModules.pushforward` and `SheafOfModules.pullback` expect. -/
def structureMap : R ⟶ ((𝟭 C).sheafPushforwardContinuous RingCat.{u} J J).obj R' := α

/-- Pushforward of sheaves of modules along the identity functor of the site is restriction
of scalars. -/
lemma pushforward_structureMap :
    SheafOfModules.pushforward.{v} (structureMap α) = SheafOfModules.restrictScalars.{v} α :=
  rfl

end StructureMap

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [(PresheafOfModules.restrictScalars.{v} α.hom).IsRightAdjoint]

/-- Extension of scalars along a morphism `α : R ⟶ R'` of sheaves of rings: a sheaf of
`R`-modules is read as a presheaf, scalars are extended along `α` at the level of presheaves
of modules, and the result is sheafified. Informally this is `G ↦ R' ⊗_R G`. -/
noncomputable def extendScalars : SheafOfModules.{v} R ⥤ SheafOfModules.{v} R' :=
  SheafOfModules.forget R ⋙ (PresheafOfModules.restrictScalars.{v} α.hom).leftAdjoint ⋙
    PresheafOfModules.sheafification (R := R') (𝟙 R'.obj)

/-- **Stacks 03CZ**: extension of scalars along a morphism `α : R ⟶ R'` of sheaves of rings
is left adjoint to restriction of scalars along `α`. Concretely, for a sheaf of `R`-modules
`G` and a sheaf of `R'`-modules `F` there is a bijection
`Hom_{R'}(R' ⊗_R G, F) = Hom_R(G, F_R)`, natural in `G` and `F`. -/
@[stacks 03CZ]
noncomputable def extendRestrictScalarsAdjunction :
    extendScalars.{v} α ⊣ SheafOfModules.restrictScalars.{v} α :=
  Adjunction.restrictFullyFaithful
    ((Adjunction.ofIsRightAdjoint (PresheafOfModules.restrictScalars.{v} α.hom)).comp
      (PresheafOfModules.sheafificationAdjunction (R := R') (𝟙 R'.obj)))
    (SheafOfModules.fullyFaithfulForget R) (Functor.FullyFaithful.id _)
    (eqToIso (Functor.comp_id _).symm) (eqToIso (Functor.id_comp _))

/-- Restriction of scalars along `α` has a left adjoint, namely `extendScalars α`. -/
instance isRightAdjoint_restrictScalars :
    (SheafOfModules.restrictScalars.{v} α).IsRightAdjoint :=
  (extendRestrictScalarsAdjunction.{v} α).isRightAdjoint

/-- Extension of scalars along `α` has a right adjoint, namely restriction of scalars. -/
instance isLeftAdjoint_extendScalars : (extendScalars.{v} α).IsLeftAdjoint :=
  (extendRestrictScalarsAdjunction.{v} α).isLeftAdjoint

/-- The underlying sheaf of abelian groups of `extendScalars α` is the sheafification of the
underlying presheaf of abelian groups of the presheaf-level extension of scalars: extension
of scalars does not change the additive structure beyond sheafifying it. -/
noncomputable def extendScalarsCompToSheaf :
    extendScalars.{v} α ⋙ SheafOfModules.toSheaf R' ≅
      SheafOfModules.forget R ⋙ (PresheafOfModules.restrictScalars.{v} α.hom).leftAdjoint ⋙
        PresheafOfModules.toPresheaf R'.obj ⋙ presheafToSheaf J AddCommGrpCat.{v} :=
  Iso.refl _

/-- The pushforward of sheaves of modules along `structureMap α` has a left adjoint. -/
instance isRightAdjoint_pushforward_structureMap :
    (SheafOfModules.pushforward.{v} (structureMap α)).IsRightAdjoint :=
  inferInstanceAs (SheafOfModules.restrictScalars.{v} α).IsRightAdjoint

/-- `extendScalars α` is canonically isomorphic to Mathlib's pullback of sheaves of modules
along the identity functor of the site and the structure map `α`, both being left adjoints
of `SheafOfModules.restrictScalars α`. -/
noncomputable def extendScalarsIsoPullback :
    extendScalars.{v} α ≅ SheafOfModules.pullback.{v} (structureMap α) :=
  Adjunction.leftAdjointUniq (extendRestrictScalarsAdjunction.{v} α)
    (SheafOfModules.pullbackPushforwardAdjunction.{v} (structureMap α))

/-! ### Full faithfulness of restriction of scalars -/

/-- If the counit of the adjunction is an isomorphism — that is, if the canonical map
`R' ⊗_R F_R ⟶ F` is an isomorphism for every sheaf of `R'`-modules `F` — then restriction of
scalars along `α` is fully faithful. -/
noncomputable def fullyFaithfulRestrictScalarsOfIsIsoCounit
    [IsIso (extendRestrictScalarsAdjunction.{v} α).counit] :
    (SheafOfModules.restrictScalars.{v} α).FullyFaithful :=
  (extendRestrictScalarsAdjunction.{v} α).fullyFaithfulROfIsIsoCounit

/-- Restriction of scalars along `α` is full if and only if the counit
`R' ⊗_R F_R ⟶ F` of the adjunction is an isomorphism. Since restriction of scalars is always
faithful, this is the criterion for it to be fully faithful, and so the shape in which
Stacks 0930 reduces to a statement about the counit. -/
theorem full_restrictScalars_iff_isIso_counit :
    (SheafOfModules.restrictScalars.{v} α).Full ↔
      IsIso (extendRestrictScalarsAdjunction.{v} α).counit where
  mp _ := inferInstance
  mpr _ := (fullyFaithfulRestrictScalarsOfIsIsoCounit.{v} α).full

/-- If `α` is locally surjective then the counit of the adjunction is an isomorphism: the
canonical map `R' ⊗_R F_R ⟶ F` is an isomorphism for every sheaf of `R'`-modules `F`. This
is the locally surjective half of Stacks 0930, read through the adjunction. -/
instance isIso_counit_of_isLocallySurjective [Sheaf.IsLocallySurjective α] :
    IsIso (extendRestrictScalarsAdjunction.{v} α).counit :=
  have := (fullyFaithfulOfIsLocallySurjective.{v} α).full
  inferInstance

/-- The counit `R' ⊗_R F_R ⟶ F` is always an epimorphism, with no hypothesis on `α`: its
restriction of scalars is split by the unit, by the triangle identity, and restriction of
scalars reflects epimorphisms because it is faithful. -/
instance epi_counit_app (F : SheafOfModules.{v} R') :
    Epi ((extendRestrictScalarsAdjunction.{v} α).counit.app F) :=
  have : IsSplitEpi ((SheafOfModules.restrictScalars.{v} α).map
      ((extendRestrictScalarsAdjunction.{v} α).counit.app F)) :=
    ⟨⟨_, (extendRestrictScalarsAdjunction.{v} α).right_triangle_components F⟩⟩
  (SheafOfModules.restrictScalars.{v} α).epi_of_epi_map inferInstance

section Balanced

variable [HasSheafify J AddCommGrpCat.{v}]

/-- With sheafification available, so that sheaves of modules form an abelian — hence
balanced — category, restriction of scalars along `α` is full as soon as every component of
the counit `R' ⊗_R F_R ⟶ F` is a monomorphism, the components being epimorphisms already.
This is the sharpest form in which Stacks 0930 is reduced here: what is missing is injectivity
of the counit, not its surjectivity. -/
theorem full_restrictScalars_of_mono_counit_app
    (h : ∀ F : SheafOfModules.{v} R',
      Mono ((extendRestrictScalarsAdjunction.{v} α).counit.app F)) :
    (SheafOfModules.restrictScalars.{v} α).Full :=
  have : ∀ F, IsIso ((extendRestrictScalarsAdjunction.{v} α).counit.app F) :=
    fun F ↦ have := h F; isIso_of_mono_of_epi _
  have : IsIso (extendRestrictScalarsAdjunction.{v} α).counit :=
    NatIso.isIso_of_isIso_app _
  (fullyFaithfulRestrictScalarsOfIsIsoCounit.{v} α).full

end Balanced

/-! ### Extension of scalars along the identity -/

section Identity

variable (R)

/-- Restriction of scalars for presheaves of modules along the identity of a presheaf of
rings is the identity functor, so it trivially has a left adjoint. -/
instance presheafRestrictScalarsId_isRightAdjoint :
    (PresheafOfModules.restrictScalars.{v} (𝟙 R : R ⟶ R).hom).IsRightAdjoint :=
  inferInstanceAs (𝟭 (PresheafOfModules.{v} R.obj)).IsRightAdjoint

/-- Extension of scalars along the identity of a sheaf of rings is the identity functor. -/
noncomputable def extendScalarsIdIso : extendScalars.{v} (𝟙 R) ≅ 𝟭 _ :=
  Adjunction.leftAdjointUniq (extendRestrictScalarsAdjunction.{v} (𝟙 R)) Adjunction.id

end Identity

end Stacks.SheafOfModules.ChangeOfRings

end
