module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import StacksFrontier.AlgebraicGeometry.QcohOverAlgebra.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.RestrictScalarsColimits.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules

/-!
# Exactness of restriction of scalars, and the two extensions of scalars

Two pieces of packaging for change of rings of sheaves of modules on a site.

**Restriction of scalars is exact.**  Both halves are already in the tree, but in two
different namespaces and with no statement tying them together:
`Stacks.AlgebraicGeometry.QcohOverAlgebra.preservesFiniteLimits_restrictScalars` and
`Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesFiniteColimits_restrictScalars`.
This file records the `CategoryTheory.exactFunctor` statement they amount to, and the two
consequences a consumer actually reaches for: that restriction of scalars carries a short
exact sequence to a short exact sequence, and — the direction that is not formal — that it
*reflects* short exactness, so a sequence of sheaves of `O'`-modules which becomes short exact
over `O` was short exact to begin with.

**The two extensions of scalars agree.**  The tree builds extension of scalars twice: once
abstractly, as the left adjoint of restriction of scalars
(`Stacks.Sheaves.ModuleAdjunction.extendScalars`, which is `SheafOfModules.pullback` along the
identity functor of the site), and once concretely, as the sheafified sectionwise tensor
product `A₂ ⊗[A₁] -` (`Stacks.Sheaves.RingedToposModules.extendScalars`, Stacks 03CZ).  Both
carry an adjunction to the *same* restriction of scalars, so uniqueness of left adjoints
identifies them.  Without that identification the abstract one cannot be fed to any result
stated for the concrete tensor product — in particular not to Stacks 03EX.

## Main results

* `Stacks.SheafOfModules.ChangeOfRings.exactFunctor_restrictScalars`: restriction of scalars
  is an exact functor.
* `Stacks.SheafOfModules.ChangeOfRings.shortExact_map_restrictScalars`: it preserves short
  exactness.
* `Stacks.SheafOfModules.ChangeOfRings.shortExact_of_shortExact_map_restrictScalars` and
  `shortExact_map_restrictScalars_iff`: it reflects short exactness.
* `Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor`: the abstract and concrete
  extensions of scalars are isomorphic.

## Implementation notes

**Reflection is not formal and is not proved by hand here.**  It is
`CategoryTheory.ShortComplex.exact_map_iff_of_faithful` for the exactness component, together
with faithfulness for the mono and epi components.  The faithfulness hypothesis is what makes
it work: restriction of scalars does not change the underlying morphism of sheaves of abelian
groups, so it loses no information.  Note that `exact_map_iff_of_faithful` needs
`ShortComplex.HasHomology` of the *source* complex, which is why the statements below carry
`HasSheafify` rather than the weaker `HasWeakSheafify` of the two instance files: the
`Abelian (SheafOfModules R)` instance of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian` is stated with `HasSheafify`, and that
instance is what supplies the homology.

**Universes.**  `RestrictScalarsColimits` keeps the module universe and the ring universe
independent, but `QcohOverAlgebra` — which carries the finite-limits half — identifies them.
The `exactFunctor` statement therefore inherits that identification: the sections of the
modules and of the sheaves of rings are in one universe `u`, while the object and morphism
universes of the site stay independent.  The narrowing comes down the chain from
`QcohOverAlgebra.preservesFiniteLimits_restrictScalars` and is not chosen here.

`extendScalarsIsoTensor` is narrower still, at `SmallCategory` with every universe collapsed:
`Stacks.Sheaves.ModuleAdjunction` is stated for `{C : Type u} [SmallCategory C]` with the ring
sheaves in the same universe `u`, while `Stacks.Sheaves.RingedToposModules.extendScalars` is
stated for an independent `Category.{v}` and section universe `w`.  Taking both forces
`v = w = u`.  Again inherited, not chosen.

**A docstring in the tree overclaims here, and this file deliberately does not route through
it.**  `Stacks.Sheaves.ModuleAdjunction.extendScalarsIso` is documented as exhibiting
extension of scalars as a sectionwise tensor product `R₂(U) ⊗[R₁(U)] -`, but its Lean content
is Mathlib's `SheafOfModules.pullbackIso`, in which no tensor product occurs — it decomposes
the pullback into `PresheafOfModules.pullback` followed by sheafification, and
`PresheafOfModules.pullback` is itself an abstract left adjoint.  So that iso does *not*
supply the identification proved below, and `extendScalarsIsoTensor` is built from the two
adjunctions instead.

## References

* [The Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [The Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v' u' u

namespace Stacks.SheafOfModules.ChangeOfRings

section Exactness

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- **Restriction of scalars is exact.**  This is the two halves already in the tree, put
together: it preserves finite limits by
`Stacks.AlgebraicGeometry.QcohOverAlgebra.preservesFiniteLimits_restrictScalars` and finite
colimits by
`Stacks.AlgebraicGeometry.RestrictScalarsColimits.preservesFiniteColimits_restrictScalars`. -/
theorem exactFunctor_restrictScalars :
    exactFunctor (_root_.SheafOfModules.{u} R') (_root_.SheafOfModules.{u} R)
      (_root_.SheafOfModules.restrictScalars.{u} α) :=
  (exactFunctor_iff _).mpr ⟨inferInstance, inferInstance⟩

variable {S : ShortComplex (_root_.SheafOfModules.{u} R')}

/-- Restriction of scalars carries a short exact sequence of sheaves of `R'`-modules to a
short exact sequence of sheaves of `R`-modules. -/
theorem shortExact_map_restrictScalars (hS : S.ShortExact) :
    (S.map (_root_.SheafOfModules.restrictScalars.{u} α)).ShortExact :=
  hS.map_of_exact _

/-- **Restriction of scalars reflects short exactness.**  A short complex of sheaves of
`R'`-modules which becomes short exact over `R` was short exact already, because restriction
of scalars is faithful: it does not change the underlying morphisms of sheaves of abelian
groups, so it loses no information.

This is the direction that is not formal, and it is the one a change-of-rings argument needs:
a tensor-product computation naturally produces exactness over the *smaller* ring. -/
theorem shortExact_of_shortExact_map_restrictScalars
    (hS : (S.map (_root_.SheafOfModules.restrictScalars.{u} α)).ShortExact) : S.ShortExact where
  exact := (S.exact_map_iff_of_faithful (_root_.SheafOfModules.restrictScalars.{u} α)).mp hS.exact
  mono_f := (_root_.SheafOfModules.restrictScalars.{u} α).mono_of_mono_map hS.mono_f
  epi_g := (_root_.SheafOfModules.restrictScalars.{u} α).epi_of_epi_map hS.epi_g

/-- Short exactness over `R'` and over `R` agree, by `shortExact_map_restrictScalars` and
`shortExact_of_shortExact_map_restrictScalars`. -/
theorem shortExact_map_restrictScalars_iff :
    (S.map (_root_.SheafOfModules.restrictScalars.{u} α)).ShortExact ↔ S.ShortExact :=
  ⟨shortExact_of_shortExact_map_restrictScalars α, shortExact_map_restrictScalars α⟩

end Exactness

section ExtendScalars

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{u}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The abstract and the concrete extension of scalars agree.**  On the left,
`Stacks.Sheaves.ModuleAdjunction.extendScalars` is `SheafOfModules.pullback` along the identity
functor of the site, defined as a left adjoint; on the right,
`Stacks.Sheaves.RingedToposModules.extendScalars` is the sheafified sectionwise tensor product
`A₂ ⊗[A₁] -` of Stacks 03CZ.  Both are left adjoint to restriction of scalars along the same
morphism of sheaves of rings, so they are isomorphic by uniqueness of left adjoints.

This is what lets the abstract extension of scalars be fed to a result stated for the concrete
tensor product, such as Stacks 03EX. -/
def extendScalarsIsoTensor :
    Stacks.Sheaves.ModuleAdjunction.extendScalars
        (Stacks.Sheaves.RingedToposModules.commRingSheafMap J θ h₁ h₂)
      ≅ Stacks.Sheaves.RingedToposModules.extendScalars J θ h₁ h₂ :=
  Adjunction.leftAdjointUniq
    (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction _)
    (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction J θ h₁ h₂)

/-- **The identification of the two extensions of scalars carries one unit to the other.**
`extendScalarsIsoTensor` is an isomorphism of *functors*, which on its own says nothing about
the two base-change units `M ⟶ (A₂ ⊗_{A₁} M)_{A₁}`: the abstract one belongs to
`Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction` and the concrete one, whose
sections are computable
(`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`), to
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction`.  The triangle

`η₁ ≫ restrictScalars(extendScalarsIsoTensor) = η₂`

says they agree, and it is the compatibility that lets an argument begun with the computable
unit be finished with a result stated for the abstract functor.  It holds because the
identification *is* `CategoryTheory.Adjunction.leftAdjointUniq`, whose defining property this
is.

The same statement for
`Stacks.Sheaves.DerivedPullback.FlatExtendScalars.extendScalarsIsoChangeOfRings` is this lemma:
that isomorphism is `extendScalarsIsoTensor` at `θ := α.hom` with the two sheaf conditions read
off `Stacks.commRingSheafToRingSheaf`. -/
lemma unit_comp_restrictScalars_map_extendScalarsIsoTensor_hom_app
    (M : _root_.SheafOfModules.{u}
      (Stacks.Sheaves.RingedToposModules.commRingSheaf J A₁ h₁)) :
    (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction
          (Stacks.Sheaves.RingedToposModules.commRingSheafMap J θ h₁ h₂)).unit.app M ≫
        (_root_.SheafOfModules.restrictScalars
            (Stacks.Sheaves.RingedToposModules.commRingSheafMap J θ h₁ h₂)).map
          ((extendScalarsIsoTensor θ h₁ h₂).hom.app M) =
      (Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction J θ h₁ h₂).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

end ExtendScalars

end Stacks.SheafOfModules.ChangeOfRings
