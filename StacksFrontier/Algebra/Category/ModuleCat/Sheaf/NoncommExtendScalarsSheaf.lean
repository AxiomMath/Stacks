module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.NoncommBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsAdjunction

/-!
# Extension of scalars for sheaves of modules over a sheaf of noncommutative rings

Let `α : R ⟶ R'` be a morphism of sheaves of rings on a site `(C, J)`. Mathlib's
`SheafOfModules.restrictScalars α : SheafOfModules R' ⥤ SheafOfModules R` reads a sheaf of
`R'`-modules as a sheaf of `R`-modules. This file constructs its left adjoint, *extension of
scalars* `R' ⊗_R -`, for an arbitrary site and an arbitrary morphism `α` in
`Sheaf J RingCat.{u}`, with no commutativity assumption on the sections and no smallness
assumption on `C`.

Extension of scalars is the composite of three steps: forget that a sheaf of `R`-modules is a
sheaf, extend scalars objectwise at the level of presheaves of modules
(`Stacks.NoncommChangeOfRings.Presheaf.extendScalars`, built from the relative tensor product
`R'(V) ⊗_{R(V)} M(V)`), and sheafify.

The file also gives criteria for restriction of scalars to be fully faithful.

## Main definitions

* `extendScalars α : SheafOfModules.{max u v} R ⥤ SheafOfModules.{max u v} R'`: extension of
  scalars along `α`, the sheafification of the objectwise extension of scalars.
* `extendScalarsCompToSheaf`: its underlying sheaf of abelian groups is the sheafification of
  the objectwise tensor product.
* `extendScalarsIsoPullback` and `isoChangeOfRingsExtendScalars`: comparisons with Mathlib's
  `SheafOfModules.pullback` along the identity functor of the site and with
  `Stacks.SheafOfModules.ChangeOfRings.extendScalars`.
* `fullyFaithfulRestrictScalarsOfIsIsoCounit`, `fullyFaithfulRestrictScalarsOfForallFull`: the
  `Functor.FullyFaithful` data for restriction of scalars obtained from an invertible counit,
  respectively from objectwise fullness.

## Main results

* `extendRestrictScalarsAdjunction α`: `extendScalars α ⊣ SheafOfModules.restrictScalars α`,
  together with the instances `(SheafOfModules.restrictScalars α).IsRightAdjoint`,
  `(extendScalars α).IsLeftAdjoint` and
  `(SheafOfModules.pushforward (structureMap α)).IsRightAdjoint`. This is the statement of
  Stacks 03CZ.
* `fullyFaithful_restrictScalars_iff_isIso_counit`: restriction of scalars along `α` is fully
  faithful if and only if the counit `R' ⊗_R F_R ⟶ F` of any adjunction exhibiting it as a
  right adjoint is an isomorphism.
* `epi_counit_app`: every component of such a counit is an epimorphism, with no hypothesis on
  `α`, and `fullyFaithful_restrictScalars_of_mono_counit_app`: when sheaves of modules are
  abelian, restriction of scalars is fully faithful as soon as those components are
  monomorphisms.
* `full_presheafRestrictScalars` and `full_restrictScalars`: restriction of scalars is full
  for presheaves of modules as soon as it is full for each ring homomorphism of sections, and
  full for sheaves of modules as soon as it is full for presheaves of modules.

## Implementation notes

**Universes.** The site is `C : Type u'` with `Category.{v'} C`, the sheaves of rings are
`RingCat.{u}`-valued, and the module universe is `max u v`: the sections `R'(V) ⊗_{R(V)} G(V)`
of the objectwise extension of scalars, a tensor product of a `Type u` and a `Type (max u v)`,
lie in `Type (max u v)`. The universes `u'` and `v'` are free. The statements in the `Counit`
and `Pointwise` sections involve no tensor product and are stated with the module universe `v`
free.

**Sheafification hypotheses.** The only hypotheses are `HasWeakSheafify J AddCommGrpCat` and
`J.WEqualsLocallyBijective AddCommGrpCat` in the module universe, those of Mathlib's
`PresheafOfModules.sheafification`; no presheaf of rings is sheafified.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930)
* [Stacks Project, Tag 08YS](https://stacks.math.columbia.edu/tag/08YS)
-/

@[expose] public section

open CategoryTheory

universe v u v' u'

namespace Stacks.NoncommChangeOfRings.Sheaf

/-! ### Extension of scalars for sheaves of modules -/

section Adjunction

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Extension of scalars along a morphism `α : R ⟶ R'` of sheaves of (not necessarily
commutative) rings: a sheaf of `R`-modules is read as a presheaf, scalars are extended
objectwise, and the result is sheafified. Informally `G ↦ (V ↦ R'(V) ⊗_{R(V)} G(V))^#`. -/
noncomputable def extendScalars : SheafOfModules.{max u v} R ⥤ SheafOfModules.{max u v} R' :=
  SheafOfModules.forget R ⋙ Presheaf.extendScalars.{v} α.hom ⋙
    PresheafOfModules.sheafification (R := R') (𝟙 R'.obj)

/-- The underlying sheaf of abelian groups of `extendScalars α` is the sheafification of the
objectwise tensor product `V ↦ R'(V) ⊗_{R(V)} G(V)`. -/
noncomputable def extendScalarsCompToSheaf :
    extendScalars.{v} α ⋙ SheafOfModules.toSheaf R' ≅
      SheafOfModules.forget R ⋙ Presheaf.extendScalars.{v} α.hom ⋙
        PresheafOfModules.toPresheaf R'.obj ⋙ presheafToSheaf J AddCommGrpCat.{max u v} :=
  Iso.refl _

/-- **Extension of scalars is left adjoint to restriction of scalars** for sheaves of modules
over sheaves of not necessarily commutative rings, with no smallness hypothesis on the site:
for a sheaf of `R`-modules `G` and a sheaf of `R'`-modules `F` there is a bijection
`Hom_{R'}(R' ⊗_R G, F) = Hom_R(G, F_R)`, natural in `G` and `F` (Stacks 03CZ). -/
noncomputable def extendRestrictScalarsAdjunction :
    extendScalars.{v} α ⊣ SheafOfModules.restrictScalars.{max u v} α :=
  Adjunction.restrictFullyFaithful
    ((Presheaf.extendScalarsAdjunction.{v} α.hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := R') (𝟙 R'.obj)))
    (SheafOfModules.fullyFaithfulForget R) (Functor.FullyFaithful.id _)
    (eqToIso (Functor.comp_id _).symm) (eqToIso (Functor.id_comp _))

/-- Extension of scalars is a left adjoint. -/
instance isLeftAdjoint_extendScalars : (extendScalars.{v} α).IsLeftAdjoint :=
  (extendRestrictScalarsAdjunction.{v} α).isLeftAdjoint

/-- **Restriction of scalars for sheaves of modules has a left adjoint**, along an arbitrary
morphism of sheaves of not necessarily commutative rings and over an arbitrary site. -/
instance isRightAdjoint_restrictScalars :
    (SheafOfModules.restrictScalars.{max u v} α).IsRightAdjoint :=
  (extendRestrictScalarsAdjunction.{v} α).isRightAdjoint

/-- Pushforward of sheaves of modules along the identity functor of the site *is* restriction
of scalars, so it too has a left adjoint. -/
instance isRightAdjoint_pushforward_structureMap :
    (SheafOfModules.pushforward.{max u v}
      (Stacks.SheafOfModules.ChangeOfRings.structureMap α)).IsRightAdjoint :=
  (extendRestrictScalarsAdjunction.{v} α).isRightAdjoint

/-- `extendScalars α` is canonically isomorphic to Mathlib's pullback of sheaves of modules
along the identity functor of the site. -/
noncomputable def extendScalarsIsoPullback :
    extendScalars.{v} α ≅
      SheafOfModules.pullback.{max u v} (Stacks.SheafOfModules.ChangeOfRings.structureMap α) :=
  Adjunction.leftAdjointUniq (extendRestrictScalarsAdjunction.{v} α)
    (SheafOfModules.pullbackPushforwardAdjunction.{max u v}
      (Stacks.SheafOfModules.ChangeOfRings.structureMap α))

/-- The objectwise construction agrees with
`Stacks.SheafOfModules.ChangeOfRings.extendScalars`, the composite that uses an abstract left
adjoint at the level of presheaves of modules. -/
noncomputable def isoChangeOfRingsExtendScalars :
    extendScalars.{v} α ≅ Stacks.SheafOfModules.ChangeOfRings.extendScalars.{max u v} α :=
  Adjunction.leftAdjointUniq (extendRestrictScalarsAdjunction.{v} α)
    (Stacks.SheafOfModules.ChangeOfRings.extendRestrictScalarsAdjunction.{max u v} α)

end Adjunction

/-! ### Full faithfulness of restriction of scalars, through the counit -/

section Counit

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
  {L : SheafOfModules.{v} R ⥤ SheafOfModules.{v} R'}

/-- Restriction of scalars along `α` is fully faithful if and only if the counit
`R' ⊗_R F_R ⟶ F` of *any* adjunction exhibiting it as a right adjoint is an isomorphism. -/
theorem fullyFaithful_restrictScalars_iff_isIso_counit
    (adj : L ⊣ SheafOfModules.restrictScalars.{v} α) :
    Nonempty (SheafOfModules.restrictScalars.{v} α).FullyFaithful ↔ IsIso adj.counit where
  mp h := have := h.some.full; inferInstance
  mpr _ := ⟨adj.fullyFaithfulROfIsIsoCounit⟩

/-- If the counit of an adjunction `L ⊣ SheafOfModules.restrictScalars α` is an isomorphism
then restriction of scalars along `α` is fully faithful. -/
noncomputable def fullyFaithfulRestrictScalarsOfIsIsoCounit
    (adj : L ⊣ SheafOfModules.restrictScalars.{v} α) [IsIso adj.counit] :
    (SheafOfModules.restrictScalars.{v} α).FullyFaithful :=
  adj.fullyFaithfulROfIsIsoCounit

/-- Every component of the counit of an adjunction `L ⊣ SheafOfModules.restrictScalars α` is an
epimorphism, with no hypothesis on `α`. -/
theorem epi_counit_app (adj : L ⊣ SheafOfModules.restrictScalars.{v} α)
    (F : SheafOfModules.{v} R') : Epi (adj.counit.app F) :=
  have : IsSplitEpi ((SheafOfModules.restrictScalars.{v} α).map (adj.counit.app F)) :=
    ⟨⟨_, adj.right_triangle_components F⟩⟩
  (SheafOfModules.restrictScalars.{v} α).epi_of_epi_map inferInstance

/-- With sheafification available, restriction of scalars along `α` is fully faithful as soon as
every component of the counit of an adjunction `L ⊣ SheafOfModules.restrictScalars α` is a
monomorphism. -/
theorem fullyFaithful_restrictScalars_of_mono_counit_app
    [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    (adj : L ⊣ SheafOfModules.restrictScalars.{v} α)
    (h : ∀ F : SheafOfModules.{v} R', Mono (adj.counit.app F)) :
    Nonempty (SheafOfModules.restrictScalars.{v} α).FullyFaithful :=
  have : ∀ F, IsIso (adj.counit.app F) := fun F ↦
    have := h F
    have := epi_counit_app α adj F
    isIso_of_mono_of_epi _
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  ⟨adj.fullyFaithfulROfIsIsoCounit⟩

end Counit

/-! ### Full faithfulness from objectwise full faithfulness -/

section Pointwise

variable {C : Type u'} [Category.{v'} C] {R₀ R₀' : Cᵒᵖ ⥤ RingCat.{u}} (α₀ : R₀ ⟶ R₀')

/-- Restriction of scalars for presheaves of modules along `α₀` is full as soon as
restriction of scalars along each ring homomorphism `α₀(V) : R₀(V) ⟶ R₀'(V)` is full. -/
theorem full_presheafRestrictScalars
    (h : ∀ X : Cᵒᵖ, (ModuleCat.restrictScalars.{v} (α₀.app X).hom).Full) :
    (PresheafOfModules.restrictScalars.{v} α₀).Full where
  map_surjective {M₁ M₂} g := by
    refine ⟨PresheafOfModules.homMk ((PresheafOfModules.toPresheaf R₀).map g) ?_, ?_⟩
    · intro X r m
      obtain ⟨ψ, hψ⟩ := (h X).map_surjective (PresheafOfModules.Hom.app g X)
      have h₁ : ∀ x : M₁.obj X, ψ x = PresheafOfModules.Hom.app g X x :=
        fun x ↦ ConcreteCategory.congr_hom hψ x
      exact (h₁ (r • m)).symm.trans ((map_smul ψ.hom r m).trans (congrArg (r • ·) (h₁ m)))
    · exact PresheafOfModules.hom_ext fun _ ↦ ModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

end Pointwise

section PointwiseSheaf

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- Restriction of scalars for sheaves of modules is full as soon as it is full for the
underlying presheaves of modules. -/
theorem full_restrictScalars [(PresheafOfModules.restrictScalars.{v} α.hom).Full] :
    (SheafOfModules.restrictScalars.{v} α).Full where
  map_surjective {_G₁ _G₂} g :=
    ⟨⟨(PresheafOfModules.restrictScalars α.hom).preimage g.val⟩,
      SheafOfModules.hom_ext ((PresheafOfModules.restrictScalars α.hom).map_preimage g.val)⟩

/-- If restriction of scalars along each ring homomorphism `α(V) : R(V) ⟶ R'(V)` of sections is
full, then restriction of scalars `SheafOfModules R' ⥤ SheafOfModules R` is fully faithful. -/
noncomputable def fullyFaithfulRestrictScalarsOfForallFull
    (h : ∀ X : Cᵒᵖ, (ModuleCat.restrictScalars.{v} (α.hom.app X).hom).Full) :
    (SheafOfModules.restrictScalars.{v} α).FullyFaithful :=
  have := full_presheafRestrictScalars.{v} α.hom h
  have := full_restrictScalars.{v} α
  .ofFullyFaithful _

end PointwiseSheaf

end Stacks.NoncommChangeOfRings.Sheaf

end
