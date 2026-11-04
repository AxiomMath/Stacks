module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension by zero of sheaves of modules from a slice site

Let `C` be a site, `J` a topology on it, `O` a sheaf of rings on `C` and `U : C`. The
restriction functor `j_U^* = SheafOfModules.overFunctor O U` sends a sheaf of `O`-modules to
its restriction to the slice site over `U`, a sheaf of `O.over U`-modules. This file
produces its *left* adjoint `j_{U!}`, the extension by zero.

Restriction `j_U^*` is already known to be a *left* adjoint
(`SheafOfModules.overFunctor_isLeftAdjoint` in
`StacksFrontier/CategoryTheory/Sites/Modules/OverFunctorExact.lean`, which is what makes it
exact). What is produced here is the other half of the triple `j_{U!} ⊣ j_U^* ⊣ j_{U*}`.

## Main results

* `SheafOfModules.pushforwardIdIso`: pushforward along the identity morphism of
  `(Over.forget U).op ⋙ O` is the universe-free `PresheafOfModules.pushforward₀`.
* `SheafOfModules.presheafOverRestriction`: the presheaf-level pushforward along
  `Over.forget U` is a right adjoint.
* `SheafOfModules.sheafOverRestriction` and `SheafOfModules.overFunctor_isRightAdjoint`:
  the same at sheaf level, for `SheafOfModules.pushforward (𝟙 (O.over U))` and for
  `SheafOfModules.overFunctor O U`, which is a plain `def` whose body is that pushforward.
* `SheafOfModules.extensionByZero`: `j_{U!}`.
* `SheafOfModules.extensionByZeroAdjunction`: the adjunction `j_{U!} ⊣ j_U^*`, which is the
  entire content of `j_{U!}`, and determines it up to isomorphism.

## Implementation notes

The site universes `u` and `v`, the universe `w` of the sections of `O` and the extra module
universe `m` are independent; the module universe is `max u v m`, which is forced by the
extension functor itself, since a section of `j_{U!}M` over `V` is assembled from the
morphisms `V ⟶ U` of the site.

Freeing those universes is the reason the presheaf-level step does not use Mathlib's
`PresheafOfModules.instIsRightAdjointPushforward`. That instance builds the left adjoint from
the presentation of a presheaf of modules as a colimit of free presheaves of modules on
representables, which Mathlib states only for a functor between **small** categories, so it
forces the ring, module and site universes to collapse to a single universe. The adjoint is
taken instead from `Stacks.Sites.OverModules.restriction_isRightAdjoint`, the right-adjoint
half of the Stacks 03EJ adjunction bundle, which is constructed directly from the extension
formula and so puts no bound on the ring universe. That instance is stated for
`PresheafOfModules.pushforward₀`, and `pushforwardIdIso` identifies it with the
`PresheafOfModules.pushforward` of an identity morphism of presheaves of rings; the
identification is `Iso.refl`, because `PresheafOfModules.restrictScalars (𝟙 R)` is the
identity functor definitionally.

The sheaf-level step is Mathlib's `SheafOfModules.instIsRightAdjointPushforward`, which
builds the left adjoint as "pull back as presheaves, then sheafify"; it is universe-free.

Neither sheaf-level instance fires by synthesis here, for the same reason in both cases: the
hypothesis is stated for `φ.hom`, and recognising the resulting morphism requires knowing
that `(O.over U).obj` is `(Over.forget U).op ⋙ O.obj`, which holds only after unfolding
`Functor.sheafPushforwardContinuous`, a plain `def`. Instance search works at `instances`
transparency and so cannot unfold it. Writing `𝟙 (O.over U)` with an explicit type
ascription lets `.hom` elaborate at all, and then naming each instance and seating it with
`have` performs the remaining check at default transparency, where it succeeds.
`overFunctor` is a milder case of the same difficulty — a plain `def` whose body is
`pushforward (𝟙 _)` — and is bridged by `inferInstanceAs`, as in `OverFunctorExact.lean`.

## References

* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
-/

@[expose] public section

universe m w v u

open CategoryTheory CategoryTheory.Limits

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]

/-- **Pushforward along the identity is `pushforward₀`.** For a presheaf of rings `O` on `C`
and `U : C`, the pushforward of presheaves of modules along `Over.forget U` induced by the
identity morphism of `(Over.forget U).op ⋙ O` is the pushforward that takes no morphism of
presheaves of rings at all. The two agree definitionally, because `restrictScalars (𝟙 R)` is
the identity functor; stating the identification with the universes written out is what lets
the universe-free `Stacks.Sites.OverModules.restriction_isRightAdjoint` be transported to the
spelling Mathlib's sheaf-level API consumes. -/
noncomputable def pushforwardIdIso (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    pushforward.{max u v m} (F := Over.forget U)
        (R := O) (S := (Over.forget U).op ⋙ O) (𝟙 ((Over.forget U).op ⋙ O)) ≅
      pushforward₀.{max u v m} (Over.forget U) O :=
  Iso.refl _

/-- **Restriction of presheaves of modules to the slice over `U` is a right adjoint**, in the
spelling that takes the identity morphism of presheaves of rings. The ring, module and site
universes are independent. -/
instance pushforwardId_isRightAdjoint (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) :
    (pushforward.{max u v m} (F := Over.forget U)
      (R := O) (S := (Over.forget U).op ⋙ O)
      (𝟙 ((Over.forget U).op ⋙ O))).IsRightAdjoint :=
  letI : (pushforward₀.{max u v m} (Over.forget U) O).IsRightAdjoint :=
    Stacks.Sites.OverModules.restriction_isRightAdjoint.{v, u, w, m} O U
  Functor.isRightAdjoint_of_iso (pushforwardIdIso.{m, w, v, u} O U).symm

end PresheafOfModules

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v m}]

/-- **The presheaf-level pushforward along `Over.forget U` is a right adjoint**, so the
presheaf-level extension by zero exists. This is
`PresheafOfModules.pushforwardId_isRightAdjoint` at the spelling `φ.hom` in which Mathlib's
sheaf-level API states its hypothesis. -/
instance presheafOverRestriction (O : Sheaf J RingCat.{w}) (U : C) :
    (PresheafOfModules.pushforward.{max u v m} (F := Over.forget U)
      (𝟙 (O.over U) : O.over U ⟶ O.over U).hom).IsRightAdjoint :=
  PresheafOfModules.pushforwardId_isRightAdjoint.{m, w, v, u} O.obj U

/-- **Restriction to the slice site over `U` is a right adjoint**, so the extension by zero
`j_{U!}` exists. The left adjoint is "pull back as presheaves of modules, then sheafify". -/
instance sheafOverRestriction (O : Sheaf J RingCat.{w}) (U : C) :
    (pushforward.{max u v m} (F := Over.forget U)
      (𝟙 (O.over U) : O.over U ⟶ O.over U)).IsRightAdjoint :=
  have := presheafOverRestriction.{m, w, v, u} O U
  (PullbackConstruction.adjunction.{max u v m} (F := Over.forget U)
    (𝟙 (O.over U))).isRightAdjoint

/-- Restriction to the slice over `U` is a right adjoint, stated at `overFunctor`, which is
a plain `def` whose body is `pushforward (𝟙 _)`. -/
instance overFunctor_isRightAdjoint (O : Sheaf J RingCat.{w}) (U : C) :
    (overFunctor.{max u v m} O U).IsRightAdjoint :=
  sheafOverRestriction.{m, w, v, u} O U

/-- **`j_{U!}`, the extension by zero of a sheaf of modules from the slice site over `U`.**
It is the left adjoint of restriction `j_U^* = overFunctor O U`. -/
@[sga "2 VI 1.4" "Z open", sga "4 IV 11.3.1", sga "4 IV 11.3.3" "partial"]
noncomputable def extensionByZero (O : Sheaf J RingCat.{w}) (U : C) :
    SheafOfModules.{max u v m} (O.over U) ⥤ SheafOfModules.{max u v m} O :=
  letI := sheafOverRestriction.{m, w, v, u} O U
  pullback.{max u v m} (F := Over.forget U) (𝟙 (O.over U))

/-- **The adjunction `j_{U!} ⊣ j_U^*`.** This is the entire content of `j_{U!}`: it
determines the functor up to isomorphism. -/
@[sga "4 IV 14.2" "more general"]
noncomputable def extensionByZeroAdjunction (O : Sheaf J RingCat.{w}) (U : C) :
    extensionByZero.{m, w, v, u} O U ⊣ overFunctor.{max u v m} O U :=
  letI := sheafOverRestriction.{m, w, v, u} O U
  pullbackPushforwardAdjunction.{max u v m} (F := Over.forget U) (𝟙 (O.over U))

/-- `j_{U!}` is a left adjoint, hence preserves all colimits that exist. -/
instance extensionByZero_isLeftAdjoint (O : Sheaf J RingCat.{w}) (U : C) :
    (extensionByZero.{m, w, v, u} O U).IsLeftAdjoint :=
  (extensionByZeroAdjunction.{m, w, v, u} O U).isLeftAdjoint

end SheafOfModules

end
