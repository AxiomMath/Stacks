module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingInternalHomNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# Dinaturality of the tensor–internal-hom bijection of Tag 08DI on a ringed space

Let `(Z, 𝒪_Z)` be a ringed space.  Tag 08DI provides the bijection

`Hom(A, R𝓗om_{𝒪_Z}(B, C)) ≃ Hom(A ⊗^L_{𝒪_Z} B, C)`

on `D(𝒪_Z)`, and Tag 08J8 asserts it functorial in the three objects.  The clause in the *source*
variable `A` is
`Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivNaturalLeft_ringedSpace` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility`.
This file proves the clause in the variable `B`, which occurs contravariantly inside the internal
hom on the left of the bijection and covariantly as a tensor factor on the right, so that the
clause is a *dinaturality* identity rather than a naturality square: postcomposing
`ψ : A ⟶ R𝓗om(B, C)` with the map induced by `φ : B' ⟶ B` corresponds to precomposing the
transpose of `ψ` with `1 ⊗ φ`.

## Main definitions

* `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.TensorHomEquivDinatural`: dinaturality
  of a tensor–internal-hom bijection in its internal-hom variable, over the abstract data of the
  construction of Tag 08I3 — one category with an internal hom, a tensor product on pairs and a
  bijection between them.  It is the companion of
  `Stacks.Cohomology.DerivedInternalHomPullback.Transpose.TensorHomEquivNaturalLeft`, the clause
  in the source variable.

## Main results

* `Stacks.Cohomology.DerivedInternalHomPullback.uncurry_map_id_mkHom`: the uncurrying of a
  bifunctor at an identity paired with a morphism.
* `Stacks.Cohomology.DerivedInternalHomPullback.derivedCurryHomEquiv_dinaturality_uncurried` and
  `…_toEquiv`: Tag 08J8 in its internal-hom variable on a ringed space, at the uncurried spelling
  of the derived tensor product, with the bijection read as an additive equivalence and as a
  bijection respectively.
* `Stacks.Cohomology.DerivedInternalHomPullback.tensorHomEquivDinatural_ringedSpace`: **the
  bijection of Tag 08DI on a ringed space is dinatural in its internal-hom variable**, which is
  `Transpose.TensorHomEquivDinatural` for it.

## Why this clause is wanted

Over a ring the tensor–internal-hom bijection is bundled as an adjunction,
`StacksDraft.DerivedHom.DerivedHomAdjunction`, which carries naturality in the source,
dinaturality in the internal-hom variable and naturality in the target together, and consumers
use all three.  On a ringed space `Stacks.SheafOfModules.derivedSheafHomTensorEquiv` is a family
of additive equivalences and not a bundled adjunction, so each clause has to be proved
separately; until now only the source one was.  Two consumers ask for this one.

* The implementation notes of
  `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomStalk` record the
  dinaturality clause of Tag 08DI on a ringed space as the one new input the assembly of the
  derived internal hom of a one-point ringed space into `RHom` over the local ring is waiting on:
  that assembly turns the derived tensor comparison
  `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedTensorIso` into
  `Stacks.Cohomology.DerivedInternalHomStalk.InternalHomComparison` by uniqueness of right
  adjoints, which needs Tag 08DI on `Y` and Tag 0A63 over `𝒪_{X,x}` with their dinaturality
  clauses.
* The source's reduction of Tag 0GM7 at a general perfect `K` to the unit case needs the same
  clause, the dévissage being carried out one tensor factor at a time.

## Implementation notes

*Why the proofs are terms and not tactic scripts,* and why the bijection is presented as the
site-level `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` of
`Stacks.SheafOfModules.ringedSite Z.sheaf` rather than as
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf`: both are the disciplines the source
clause is proved under, and the implementation notes of
`…DerivedPushforward.InternalHomPullbackInvertibility` record the measurements behind them.  The
two families of additive equivalences are equal by `rfl` unapplied and are not interchangeable
within the elaborator's budget once a coercion is applied to them, so the family is written at the
spelling Tag 08J8 is proved at; and every step below is applied at its arguments, a `rw` or a
`simp only` with any of them having to match a pattern against terms of this size.

*The uncurrying is affordable only in the abstract,* exactly as for the source clause:
`uncurry_map_id_mkHom` is stated over three arbitrary categories, where both sides are small, and
is never asked for inside a statement about derived categories of module sheaves.

*Three declarations, not one.*  The dinaturality clause has one crossing more than the source
clause: its argument contains the induced map `((derivedSheafHom Z.sheaf).map φ.op).app C`, whose
spelling meets the site-level one of the theorem being applied *inside* the composite, and whose
`φ.op` adds the `Category` instance of an opposite derived category to the identifications the
elaborator must settle.  Carried out in a single declaration — the shape the source clause uses —
that exhausts `maxRecDepth`, and raising the limit is not available.  So the crossings are paid
one declaration at a time:

1. `derivedCurryHomEquiv_dinaturality_uncurried` pays the object-spelling and uncurrying
   crossings, by `convert … using 1`;
2. `derivedCurryHomEquiv_dinaturality_uncurried_toEquiv` pays the `AddEquiv`-versus-`Equiv`
   coercion, by `AddEquiv.coe_toEquiv` applied at its argument at each end;
3. `tensorHomEquivDinatural_ringedSpace` pays the beta-reduction of the predicate's bijection
   family, by `convert … using 1`.

This is the "state the identification once, at the level where it is cheapest" discipline applied
to a chain of three identifications rather than to one.

## References

* [Stacks Project, Tag 08DI](https://stacks.math.columbia.edu/tag/08DI)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 0GM8](https://stacks.math.columbia.edu/tag/0GM8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance] HasDerivedCategory.standard

-- The derived pullback and the derived internal hom name the structure sheaf of a ringed space
-- differently, by `structureSheafRing` and by
-- `Stacks.SheafOfModules.Tensor.ringSheaf`; the two are the same sheaf of rings by `rfl`, and
-- the statements below mix them.  `structureSheafRing` is `@[instance_reducible]`, so it is
-- already unfolded both by instance search and at `implicit` transparency, but its reduct stops
-- at an explicit-constructor projection while `Tensor.ringSheaf Z.sheaf` reduces to
-- `(sheafCompose _ _).obj Z.sheaf`; the last two Mathlib definitions are the gap between them,
-- and they are the list
-- `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackInvertibility`
-- carries for the statements this file applies.
--
-- The list is set per section rather than once for the file, because the two groups of
-- declarations below need the crossing at two *different* transparencies, and a name can carry
-- only one reducibility setting at a time.  `implicit` transparency is strictly above
-- `instances`, so `implicit_reducible` is the setting that keeps a definition opaque to type
-- class *search* while unfolding it for implicit-argument unification, and `instance_reducible`
-- is the one that does both.  See each section.

namespace Transpose

/-- **Dinaturality of a tensor–internal-hom bijection in its internal-hom variable:** the
transpose of a morphism postcomposed with the map induced by `φ : B' ⟶ B` is the transpose
precomposed with `1 ⊗ φ`.

The variable occurs contravariantly on the left of the bijection and covariantly on the right, so
this is a dinaturality identity and not a naturality square.  It is the companion of
`TensorHomEquivNaturalLeft`, the clause in the source variable. -/
def TensorHomEquivDinatural {D : Type*} [Category D] (H : Dᵒᵖ ⥤ D ⥤ D) (T : D × D ⥤ D)
    (e : ∀ A B C : D, (A ⟶ (H.obj (op B)).obj C) ≃ (T.obj (A, B) ⟶ C)) : Prop :=
  ∀ (A B B' C : D) (φ : B' ⟶ B) (ψ : A ⟶ (H.obj (op B)).obj C),
    e A B' C (ψ ≫ (H.map φ.op).app C) = T.map (𝟙 A ×ₘ φ) ≫ e A B C ψ

end Transpose

/-! ### Tag 08J8 in its internal-hom variable, at a ringed space -/

section Dinaturality

/-- **The uncurrying of a bifunctor at an identity paired with a morphism.**  For a bifunctor `F`
and `φ : B' ⟶ B` the functor on pairs `Functor.uncurry.obj F` sends `𝟙 A ×ₘ φ` to
`(F.obj A).map φ`: the first leg is an identity, so only the second survives.

It is stated over three arbitrary categories, and that is what makes it affordable, for the reason
recorded on its companion
`CategoryTheory.uncurry_map_mkHom_id`: the identity is exactly the
difference between the uncurried spelling of the derived tensor product that the abstract
transpose construction is stated at and the curried spelling that Tag 08J8 is stated at, and
carried out inside a statement about derived categories of module sheaves it exhausts the
elaborator's budget, whereas here both sides are small. -/
theorem uncurry_map_id_mkHom {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D ⥤ E) (A : C) {B B' : D} (φ : B' ⟶ B) :
    (Functor.uncurry.obj F).map ((𝟙 A) ×ₘ φ) = (F.obj A).map φ := by
  simp [Functor.uncurry]

variable (Z : RingedSpace.{u, u})

section Crossing

-- The two identities of this section meet the crossing only in implicit and instance-implicit
-- arguments, where `implicit` transparency is what is used, and they are the largest terms in
-- the file: unfolding these three for instance search as well sends the congruence `convert`
-- builds for `derivedCurryHomEquiv_dinaturality_uncurried` past `maxRecDepth`.
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **Tag 08J8 in its internal-hom variable, read on a ringed space at the uncurried spelling of
the derived tensor product.**  Postcomposing `ψ : A ⟶ R𝓗om(B, C)` with the map
`R𝓗om(B, C) ⟶ R𝓗om(B', C)` induced by `φ : B' ⟶ B` corresponds, under the bijection of Tag 08DI,
to precomposing the transpose of `ψ` with `1 ⊗ φ`.

This is `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality` at
`Stacks.SheafOfModules.ringedSite Z.sheaf`, with the curried spelling of the derived tensor
product traded for the uncurried one by `uncurry_map_id_mkHom`.

`convert … using 1` rather than `exact`: the two statements differ in the spelling of the
category of module sheaves — `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z`
against `SheafOfModules (Stacks.SheafOfModules.ringedSite Z.sheaf).ringSheaf` — and of the derived
internal hom, and the congruence `convert` builds settles those argument by argument, whereas
`exact` asks for one `isDefEq` on the whole equation and exhausts `maxRecDepth`.  See the
implementation notes of this file for why the remaining crossings are paid in separate
declarations. -/
theorem derivedCurryHomEquiv_dinaturality_uncurried
    (A B B' C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    (φ : B' ⟶ B)
    (ψ : A ⟶ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).obj C) :
    RingedSite.derivedCurryHomEquiv (Stacks.SheafOfModules.ringedSite Z.sheaf) A B' C
        (ψ ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).map φ.op).app C) =
      (internalHomTensorUncurried Z).map ((𝟙 A) ×ₘ φ) ≫
        RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C ψ := by
  convert (RingedSite.derivedCurryHomEquiv_dinaturality
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A C φ ψ).trans
      (congrArg (· ≫ RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C ψ)
        (uncurry_map_id_mkHom (internalHomTensorProduct Z).tensor A φ)).symm using 2
  -- What `using 2` leaves is the induced map written at the two spellings of the derived
  -- internal hom, `Stacks.SheafOfModules.derivedSheafHom Z.sheaf` against the
  -- `derivedSheafHomBifunctor` of the same ringed site, which is the abbreviation for it.  The
  -- congruence `convert` builds closes its leaves at `reducible` transparency, and the two
  -- differ in instance arguments carrying the sheaf of rings, so settling them needs `implicit`
  -- transparency — which is what this file's reducibility list is for, and what `rfl` uses.
  rfl

/-- `derivedCurryHomEquiv_dinaturality_uncurried` with the additive equivalence of Tag 08DI read
as a bijection, which is the shape `Transpose.TensorHomEquivDinatural` is stated at.

The coercion is traded at each end by `AddEquiv.coe_toEquiv` applied at its argument: the
unapplied equality of the two coercions costs nothing, whereas asking for the applied equality by
`rfl` exceeds `maxRecDepth`, as the implementation notes of
`…DerivedPushforward.InternalHomPullbackInvertibility` record for the same trade on the source
clause. -/
theorem derivedCurryHomEquiv_dinaturality_uncurried_toEquiv
    (A B B' C : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z))
    (φ : B' ⟶ B)
    (ψ : A ⟶ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).obj (op B)).obj C) :
    (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B' C).toEquiv
        (ψ ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).map φ.op).app C) =
      (internalHomTensorUncurried Z).map ((𝟙 A) ×ₘ φ) ≫
        (RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv ψ :=
  (congrFun (AddEquiv.coe_toEquiv (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B' C))
      (ψ ≫ ((Stacks.SheafOfModules.derivedSheafHom Z.sheaf).map φ.op).app C)).trans
    ((derivedCurryHomEquiv_dinaturality_uncurried Z A B B' C φ ψ).trans
      (congrArg ((internalHomTensorUncurried Z).map ((𝟙 A) ×ₘ φ) ≫ ·)
        (congrFun (AddEquiv.coe_toEquiv (RingedSite.derivedCurryHomEquiv
          (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C)) ψ).symm))

end Crossing

section Predicate

-- The predicate below fixes its category from the derived internal hom, so its three bound
-- objects arrive at the `Tensor.ringSheaf` spelling, and writing the bijection of Tag 08DI at
-- them asks *instance search* for the additive structure of a group of morphisms of `D(𝒪_Z)` —
-- the bijection is an `AddEquiv`.  `Tensor.ringSheaf` is a plain `def` and `SheafedSpace.sheaf`
-- is what exposes the presheaf its constructor shares with `structureSheafRing`, so search
-- reaches `Preadditive` only with these two unfolded at `instances` transparency.
-- `structureSheafRing` is left at its own `@[instance_reducible]`: listing it as
-- `implicit_reducible`, as the section above does, would move it *up* to the level at which
-- instance search stops seeing it, which is the other half of the same gap.
attribute [local implicit_reducible] CategoryTheory.sheafCompose
attribute [local instance_reducible] Stacks.SheafOfModules.Tensor.ringSheaf
  AlgebraicGeometry.SheafedSpace.sheaf

/-- **The bijection of Tag 08DI on a ringed space is dinatural in its internal-hom variable.**
This is `Transpose.TensorHomEquivDinatural` for the bijection of Tag 08DI, the companion of
`tensorHomEquivNaturalLeft_ringedSpace`, and it is the clause the assembly of
`Stacks.Cohomology.DerivedInternalHomStalk.InternalHomComparison` and the dévissage of Tag 0GM7
in the perfect variable both ask for.

The bijection is presented as the site-level `RingedSite.derivedCurryHomEquiv` of
`Stacks.SheafOfModules.ringedSite Z.sheaf` rather than as
`Stacks.SheafOfModules.derivedSheafHomTensorEquiv Z.sheaf`, which is the same family of additive
equivalences; see the implementation notes of this file.  `convert … using 1` rather than `exact`
for the reason recorded on `tensorHomEquivNaturalLeft_ringedSpace`: what is left to settle lives
inside the `FunLike` instance of the coercion, where the two spellings of the derived tensor
product and of the derived internal hom appear as instance arguments, and the congruence `convert`
builds settles those argument by argument. -/
@[stacks 08J8 "dinaturality of the bijection of morphism groups of Tag 08DI in its internal-hom \
variable, read on a ringed space at the uncurried spelling of the derived tensor product; the \
companion clause in the source variable is tensorHomEquivNaturalLeft_ringedSpace"]
theorem tensorHomEquivDinatural_ringedSpace :
    Transpose.TensorHomEquivDinatural (Stacks.SheafOfModules.derivedSheafHom Z.sheaf)
      (internalHomTensorUncurried Z)
      (fun A B C => (RingedSite.derivedCurryHomEquiv
        (Stacks.SheafOfModules.ringedSite Z.sheaf) A B C).toEquiv) := by
  intro A B B' C φ ψ
  convert derivedCurryHomEquiv_dinaturality_uncurried_toEquiv Z A B B' C φ ψ using 1

end Predicate

end Dinaturality

end Stacks.Cohomology.DerivedInternalHomPullback

end
