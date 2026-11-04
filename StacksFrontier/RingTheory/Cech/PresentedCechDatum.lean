module

public import StacksFrontier.Algebra.Homology.KFlatStrictReplacement
public import StacksFrontier.RingTheory.Cech.PairCategory
public import StacksFrontier.RingTheory.DerivedCompletion.FunctorialCechComplex

/-!
# A Čech datum on the category of presented pairs

[Stacks, Tag 099D] asks for a complex `K(A, I)` of `A`-modules for every pair of a ring and a
finitely generated ideal, with an augmentation onto `A` and maps `K(A, I) → K(B, IB)` composing
on the nose, satisfying the base-change condition (c) and the Čech comparison (d). The source
produces it in two steps: first for the *presented* pairs — the objects of
`Stacks.PairSite.Pair` — and then for arbitrary pairs by a filtered colimit.

This file states the first step's output. A `Stacks.PairSite.PresentedCechDatum` is **one**
complex `𝒦•` of presheaves of modules on the category of pairs together with an augmentation
`𝒦• ⟶ 𝒪[0]`, such that the complexes of sections `𝒦•(P)` satisfy conditions (c) and (d) of the
tag at every presented pair `P`. Conditions (a) and (b) are not fields: they are *theorems*
about an arbitrary complex of pair-modules
(`Stacks.PairSite.sectionsMap_augmentation` and
`Stacks.PairSite.sectionsMap_comp`), because the maps `𝒦•(P) → 𝒦•(Q)` are the restriction maps
of a presheaf and therefore compose strictly. That is the whole reason the construction runs
over a category of pairs instead of over pairs with a chosen generating family, for which (b)
is only available up to isomorphism in the derived category
(`Stacks.FunctorialCechFamily.isEmpty_functorialGenerators`).

## Main definitions

* `Stacks.PairSite.sectionsComplex` — the complex of sections `𝒦•(P)` of a complex of
  pair-modules at a presented pair, a complex of `P.ring`-modules.
* `Stacks.PairSite.sectionsMap` — its restriction map `𝒦•(P) ⟶ 𝒦•(Q)` along a morphism of
  pairs, a map of `P.ring`-modules into restriction of scalars; this is datum (3) of the tag.
* `Stacks.PairSite.structureSingle` — the structure pair-module `𝒪` placed in degree zero.
* `Stacks.PairSite.sectionsAugmentation` — the augmentation `𝒦•(P) ⟶ P.ring[0]` obtained from an
  augmentation `𝒦• ⟶ 𝒪[0]` by taking sections; this is datum (2) of the tag.
* `Stacks.PairSite.PresentedCechDatum` — the structure: the complex, the augmentation, and
  conditions (c) and (d) at presented pairs.

## Main results

* `Stacks.PairSite.sectionsMap_comp` — **condition (b) at presented pairs**, on the nose, for an
  arbitrary complex of pair-modules, in the shape
  `Stacks.LocalCohomology.FunctorialCechData.map_map` demands.
* `Stacks.PairSite.sectionsMap_augmentation` — **condition (a) at presented pairs**, on the nose,
  in the shape `Stacks.LocalCohomology.FunctorialCechData.map_augmentation` demands.

## Implementation notes

The conditions are stated in exactly the shapes of the corresponding fields of
`Stacks.LocalCohomology.FunctorialCechData`, with `A := P.ring`, `I := P.ideal` and
`φ := f.toRingHom`, so that a datum here feeds the filtered-colimit step with no further
translation. In particular (b) is spelled with
`Stacks.LocalCohomology.restrictScalarsCompComplexIso` and not with
`Stacks.StrictReplacement.restrictScalarsComplexComp`: the two differ by
`ModuleCat.restrictScalarsComp` versus `ModuleCat.restrictScalarsComp'`, and the first is what
the target structure uses.

The ideal of a presented pair is finitely generated automatically (`Pair.ideal_fg`), so no
finiteness hypothesis occurs.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.PairSite

/-! ### The sections of a complex of pair-modules at a presented pair -/

/-- **The complex of sections at a presented pair.** A complex of pair-modules has, at every
presented pair `P`, a complex of `P.ring`-modules: this is `K(A₀, I₀)` for `P = (A₀, I₀)`. -/
abbrev sectionsComplex (K : CochainComplex PairModule.{u} ℤ) (P : Pair.{u}) :
    CochainComplex (ModuleCat.{u} P.ring) ℤ :=
  (StrictReplacement.sectionsFunctor structureRings.{u} P.ix).obj K

/-- **The restriction map between the complexes of sections**, along a morphism of pairs: a map
of complexes of `P.ring`-modules from the sections at `P` to the sections at `Q` read over
`P.ring`. This is datum (3) of [Stacks, Tag 099D] at presented pairs. -/
abbrev sectionsMap (K : CochainComplex PairModule.{u} ℤ) {P Q : Pair.{u}} (f : P ⟶ Q) :
    sectionsComplex K P ⟶
      (CochainComplex.restrictScalars f.toRingHom).obj (sectionsComplex K Q) :=
  StrictReplacement.sectionsRestrict K (Pair.Hom.ix f)

/-- In degree `n`, the restriction map between complexes of sections is the restriction map
of the pair-module `K.X n` along `f`. -/
@[simp]
theorem sectionsMap_f (K : CochainComplex PairModule.{u} ℤ) {P Q : Pair.{u}} (f : P ⟶ Q)
    (n : ℤ) : (sectionsMap K f).f n = (K.X n).restriction f :=
  rfl

/-- **Condition (b) of [Stacks, Tag 099D] at presented pairs, on the nose.** The restriction maps
between the complexes of sections of a complex of pair-modules compose, with no comparison in a
derived category intervening: this is `PresheafOfModules.map_comp` in every degree. The shape is
the one `Stacks.LocalCohomology.FunctorialCechData.map_map` demands. -/
theorem sectionsMap_comp (K : CochainComplex PairModule.{u} ℤ) {P Q R : Pair.{u}} (f : P ⟶ Q)
    (g : Q ⟶ R) :
    sectionsMap K (f ≫ g) =
      sectionsMap K f ≫
        (CochainComplex.restrictScalars f.toRingHom).map (sectionsMap K g) ≫
          (LocalCohomology.restrictScalarsCompComplexIso f.toRingHom g.toRingHom).hom.app
            (sectionsComplex K R) :=
  StrictReplacement.sectionsRestrict_comp K (Pair.Hom.ix f) (Pair.Hom.ix g)

/-! ### The structure pair-module in degree zero, and augmentations -/

/-- **The structure presheaf of pairs, placed in degree zero**: the complex `𝒪[0]` of
pair-modules that an augmentation of a complex of pair-modules lands in. -/
abbrev structureSingle : CochainComplex PairModule.{u} ℤ :=
  (CochainComplex.singleFunctor PairModule.{u} 0).obj structureModule.{u}

/-- **The sections of `𝒪[0]` at a pair are the pair's ring in degree zero.** -/
def sectionsStructureSingleIso (P : Pair.{u}) :
    sectionsComplex structureSingle.{u} P ≅
      (CochainComplex.singleFunctor (ModuleCat.{u} P.ring) 0).obj (ModuleCat.of P.ring P.ring) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (PresheafOfModules.evaluation.{u} structureRings.{u} P.ix) (ComplexShape.up ℤ) 0).app
      structureModule.{u}

/-- **The augmentation at a pair.** An augmentation `𝒦• ⟶ 𝒪[0]` of a complex of pair-modules
gives, at every presented pair, a map of complexes of `P.ring`-modules from the sections onto
`P.ring` in degree zero. This is datum (2) of [Stacks, Tag 099D] at presented pairs. -/
def sectionsAugmentation {K : CochainComplex PairModule.{u} ℤ} (α : K ⟶ structureSingle.{u})
    (P : Pair.{u}) :
    sectionsComplex K P ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} P.ring) 0).obj (ModuleCat.of P.ring P.ring) :=
  (StrictReplacement.sectionsFunctor structureRings.{u} P.ix).map α ≫
    (sectionsStructureSingleIso P).hom

/-- The augmentation at `P` is the map induced by `α` on sections at `P`, followed by the
identification `sectionsStructureSingleIso P`. -/
theorem sectionsAugmentation_eq {K : CochainComplex PairModule.{u} ℤ}
    (α : K ⟶ structureSingle.{u}) (P : Pair.{u}) :
    sectionsAugmentation α P =
      (StrictReplacement.sectionsFunctor structureRings.{u} P.ix).map α ≫
        (sectionsStructureSingleIso P).hom :=
  rfl

/-- **A morphism of complexes of pair-modules commutes with the restriction maps on sections**,
on the nose, in the spelling the conditions of [Stacks, Tag 099D] use. -/
theorem sectionsMap_naturality {K L : CochainComplex PairModule.{u} ℤ} (α : K ⟶ L)
    {P Q : Pair.{u}} (f : P ⟶ Q) :
    sectionsMap K f ≫ (CochainComplex.restrictScalars f.toRingHom).map
        ((StrictReplacement.sectionsFunctor structureRings.{u} Q.ix).map α) =
      (StrictReplacement.sectionsFunctor structureRings.{u} P.ix).map α ≫ sectionsMap L f :=
  StrictReplacement.sectionsRestrict_naturality α (Pair.Hom.ix f)

/-- Two maps into the restriction of scalars of a ring placed in degree zero agree once they
agree in degree zero. -/
private theorem hom_eq_of_f_zero_eq {P Q : Pair.{u}} (f : P ⟶ Q)
    {X : CochainComplex (ModuleCat.{u} P.ring) ℤ}
    (a b : X ⟶ (CochainComplex.restrictScalars f.toRingHom).obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} Q.ring) 0).obj (ModuleCat.of Q.ring Q.ring)))
    (h : a.f 0 = b.f 0) : a = b := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  by_cases hn : n = 0
  · subst hn
    exact h
  · exact (Functor.map_isZero (ModuleCat.restrictScalars f.toRingHom)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
        (ModuleCat.of Q.ring Q.ring) n hn)).eq_of_tgt _ _

/-- **The identification of the sections of `𝒪[0]` is compatible with the restriction maps.**
Restricting a section of `𝒪` along a morphism of pairs is applying the underlying ring map, in
degree zero and trivially elsewhere; this is the degreewise content of condition (a). -/
theorem sectionsStructureSingleIso_naturality {P Q : Pair.{u}} (f : P ⟶ Q) :
    sectionsMap structureSingle.{u} f ≫
        (CochainComplex.restrictScalars f.toRingHom).map (sectionsStructureSingleIso Q).hom =
      (sectionsStructureSingleIso P).hom ≫ LocalCohomology.singleRingHom f.toRingHom := by
  exact hom_eq_of_f_zero_eq f _ _ rfl

/-- **Condition (a) of [Stacks, Tag 099D] at presented pairs, on the nose.** The restriction maps
between the complexes of sections are compatible with the augmentations, with no comparison in a
derived category intervening: this is the naturality of a morphism of presheaves of modules. The
shape is the one `Stacks.LocalCohomology.FunctorialCechData.map_augmentation` demands. -/
theorem sectionsMap_augmentation {K : CochainComplex PairModule.{u} ℤ}
    (α : K ⟶ structureSingle.{u}) {P Q : Pair.{u}} (f : P ⟶ Q) :
    sectionsMap K f ≫
        (CochainComplex.restrictScalars f.toRingHom).map (sectionsAugmentation α Q) =
      sectionsAugmentation α P ≫ LocalCohomology.singleRingHom f.toRingHom := by
  exact hom_eq_of_f_zero_eq f _ _ ((α.f 0).naturality (Pair.Hom.ix f))

/-! ### The datum -/

/-- **A Čech datum on the category of presented pairs.** One complex `𝒦•` of presheaves of
modules on the category of pairs, with an augmentation onto the structure presheaf in degree
zero, whose complexes of sections satisfy conditions (c) and (d) of [Stacks, Tag 099D] at every
presented pair.

Conditions (a) and (b) are absent on purpose: they are theorems about any complex of
pair-modules, proved in this file, because the maps of datum (3) are the restriction maps of a
presheaf. -/
structure PresentedCechDatum where
  /-- (1) The complex `𝒦•` of pair-modules; its sections at `P = (A₀, I₀)` are `K(A₀, I₀)`. -/
  complex : CochainComplex PairModule.{u} ℤ
  /-- (2) The augmentation `𝒦• ⟶ 𝒪[0]`. -/
  augmentation : complex ⟶ structureSingle.{u}
  /-- (c) For a morphism of pairs `f : P ⟶ Q`, the induced map
  `K(P) ⊗^L_{P.ring} Q.ring → K(Q)` is an isomorphism in `D(Q.ring)`. -/
  isIso_derivedBaseChange {P Q : Pair.{u}} (f : P ⟶ Q) :
    IsIso (LocalCohomology.derivedBaseChange f.toRingHom (sectionsMap complex f))
  /-- (d) For a finite family generating the ideal of `P` there is an isomorphism in
  `D(P.ring)` from the extended alternating Čech complex on that family to `K(P)`, over the
  identity of `P.ring`. -/
  exists_cech_iso (P : Pair.{u}) {r : ℕ} (g : Fin r → P.ring)
      (hg : Ideal.span (Set.range g) = P.ideal) :
    ∃ e : LocalCohomology.extendedCechObject g (ModuleCat.of P.ring P.ring) ≅
        DerivedCategory.Q.obj (sectionsComplex complex P),
      e.hom ≫ DerivedCategory.Q.map (sectionsAugmentation augmentation P) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} P.ring) 0).app
            (ModuleCat.of P.ring P.ring)).inv =
        LocalCohomology.extendedCechAugmentationHom g (ModuleCat.of P.ring P.ring)

end Stacks.PairSite

end
