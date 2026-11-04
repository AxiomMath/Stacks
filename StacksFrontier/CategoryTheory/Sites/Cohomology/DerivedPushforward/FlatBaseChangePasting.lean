module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.FlatBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangePasting

/-!
# Horizontal pasting of the flat base change map on bounded below derived categories

Let

```
        h'        g'
  C'' ———→ C' ———→ C
   | f''     | f'    | f
   v         v       v
  D'' ———→ D' ———→ D
         h         g
```

be two commutative squares of ringed topoi sharing a vertical edge, with all six horizontal
morphisms flat, and let `g₀ : D'' ⟶ D` and `g'₀ : C'' ⟶ C` be the two composite horizontal legs
of the pasted rectangle, presented not as literal composites but through comparisons
`cU : g^* ∘ h^* ≅ g₀^*` and `cV : (g')^* ∘ (h')^* ≅ (g'₀)^*` of the inverse images.

This file proves that **the base change map of `Stacks 0736` for the rectangle is the composite
of the base change maps of the two squares**, read through the comparisons of the derived inverse
images along the two composite legs.  That is the pasting law of **Stacks 0E47** at the seating
`Stacks.Cohomology.ToposBaseChange.baseChangeMap` lives at — `AlgebraicGeometry.RingedToposHom`
on `DerivedCategory.Plus` — and therefore in *every* degree, not only in degree zero.

The one hypothesis about the squares is `hτ`, the **degree-zero** pasting identity for the three
underived base change maps `Stacks.Cohomology.ToposBaseChange.moduleBaseChange`.  Nothing else is
assumed: the three commutativity comparisons of composite direct images are arbitrary, as they
are for the base change map itself, and no acyclicity enters, flatness of the horizontal
morphisms being enough for every object to be right acyclic for their inverse images.

## Main definitions

* `Stacks.Cohomology.ToposBaseChange.flatPullbackCompIso`: the comparison
  `Rg^* ⋙ Rh^* ≅ Rg₀^*` of the derived inverse images along two composable flat morphisms with
  the derived inverse image along a flat composite, from a comparison of the underived ones.

## Main results

* `Stacks.Cohomology.ToposBaseChange.baseChangeMap_horizontal`: **the pasting law**, evaluated at
  an object of `D⁺(Mod(O_C))`.

## Implementation notes

*Where the content comes from.*  `Stacks.Cohomology.ToposBaseChange.baseChangeMap` is by
definition `Stacks.Cohomology.BaseChange.derived` of the underived base change map
`moduleBaseChange`, with the derived-functor unit of the inverse image along the flat `g` as its
comparison — that unit is invertible because a flat inverse image is exact, which is
`Stacks.Cohomology.ToposBaseChange.flatPullbackComparison`.  The generic law
`Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app` descends a degree-zero pasting
identity to the bounded below right derived functors for arbitrary additive functors with exact
horizontal legs.  So the statement below is that generic law instantiated at the direct and
inverse images of sheaves of modules on ringed topoi, with exactness of the four inverse images
it asks for supplied by `Stacks.Sheaves.pullbackModules_exact_of_isFlatMap`, **Stacks 04JC**.

*Why the exactness instances are installed inside the proof rather than assumed.*  Exactness of
a flat inverse image is a consequence of flatness, so assuming it would be an extra hypothesis.
The four `PreservesFiniteLimits`/`PreservesFiniteColimits` instances the generic law needs are
therefore derived from the flatness hypotheses by `have` at the start of the proof, and the two
inside `flatPullbackCompIso` likewise.  They are propositions, so the instances the statement
elaborates with and the ones the proof installs are identified by proof irrelevance and no
transport is needed.

*What this does not supply.*  The hypothesis `hτ` is the degree-zero pasting identity at *this*
seating, for `moduleBaseChange` of the three squares.  For a square of algebraic spaces the
degree-zero law is available at the module spelling,
`AlgebraicGeometry.Space.moduleBaseChangeMap_horizontal`
(`StacksFrontier/AlgebraicGeometry/Spaces/ModuleBaseChangeMapHorizontal.lean`), and at the site
spelling, `AlgebraicGeometry.Space.siteBaseChangeMap_horizontal`;  carrying either across the
comparisons `AlgebraicGeometry.Space.modulePushforwardIso` and
`AlgebraicGeometry.Space.modulePullbackIso` to the direct and inverse images of the small étale
*ringed topoi*, which is the spelling `hτ` wants, is not done here.

*No `@[stacks 0E47]` attribute.*  The statement carries the degree-zero pasting identity of its
three squares as the named hypothesis `hτ`, so it is the descent step of **Stacks 0E47** and not
the tag's assertion;  the unconditional registration of 0E47 in this development is
`Stacks.Cohomology.DerivedBaseChangePasting.derivedBaseChangeMap_horizontal`
(`BaseChangePastingOnRingedTopoi.lean`, beside this file), at the
`RingedToposSiteHom`-on-unbounded-`DerivedCategory` seating.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

namespace Stacks.Cohomology.ToposBaseChange

attribute [local instance] HasDerivedCategory.standard

universe w v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

/-! ### The comparison of derived inverse images along a flat composite -/

section CompIso

variable {E : RingedTopos.{v₁, u₁, w}} {E' : RingedTopos.{v₂, u₂, w}}
  {E'' : RingedTopos.{v₃, u₃, w}}
  [E.J.HasSheafCompose (forget RingCat.{w})] [E'.J.HasSheafCompose (forget RingCat.{w})]
  [E''.J.HasSheafCompose (forget RingCat.{w})]
  [E.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [E'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [E''.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [E.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [E'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [E''.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify E.J AddCommGrpCat.{w}] [HasSheafify E'.J AddCommGrpCat.{w}]
  [HasSheafify E''.J AddCommGrpCat.{w}]
  [E.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [E'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [E''.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf E.O))]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf E'.O))]

/-- **The comparison `Ra^* ⋙ Rb^* ≅ Rc^*` of derived inverse images along a flat composite.**
Given two composable flat morphisms of ringed topoi, a third flat morphism `c` standing for
their composite, and a comparison `e` of the underived inverse images, this is the induced
comparison of the inverse images on bounded below derived categories.

Flatness is what makes it exist with no acyclicity hypothesis: a flat inverse image is exact by
**Stacks 04JC**, so every object is right acyclic for it and the comparison of
**Stacks 015M** applies to any first factor. -/
def flatPullbackCompIso (a : AlgebraicGeometry.RingedToposHom E' E) (ha : a.IsFlat)
    (b : AlgebraicGeometry.RingedToposHom E'' E') (hb : b.IsFlat)
    (c : AlgebraicGeometry.RingedToposHom E'' E) (hc : c.IsFlat)
    (e : pullbackModules a.toRingedToposModulesHom ⋙
      pullbackModules b.toRingedToposModulesHom ≅
        pullbackModules c.toRingedToposModulesHom) :
    flatPullback a ha ⋙ flatPullback b hb ≅ flatPullback c hc :=
  have hexa := (exactFunctor_iff _).mp (pullbackModules_exact_of_isFlatMap a ha)
  have hexb := (exactFunctor_iff _).mp (pullbackModules_exact_of_isFlatMap b hb)
  have hexc := (exactFunctor_iff _).mp (pullbackModules_exact_of_isFlatMap c hc)
  have := hexa.1
  have := hexa.2
  have := hexb.1
  have := hexb.2
  have := hexc.1
  have := hexc.2
  Functor.rightDerivedFunctorPlusCompIsoOfExact _ _ _ e

end CompIso

/-! ### The pasting law -/

/-- The inverse image of modules along a flat morphism preserves finite limits and colimits. -/
private theorem pullbackModules_preservesFinite_of_isFlat
    {X : RingedTopos.{v₁, u₁, w}} {Y : RingedTopos.{v₂, u₂, w}}
    [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (a : AlgebraicGeometry.RingedToposHom X Y) (ha : a.IsFlat) :
    PreservesFiniteLimits (pullbackModules a.toRingedToposModulesHom) ∧
      PreservesFiniteColimits (pullbackModules a.toRingedToposModulesHom) :=
  (exactFunctor_iff _).mp (pullbackModules_exact_of_isFlatMap a ha)

section Paste

variable {C : RingedTopos.{v₁, u₁, w}} {C' : RingedTopos.{v₂, u₂, w}}
  {C'' : RingedTopos.{v₃, u₃, w}} {D : RingedTopos.{v₄, u₄, w}}
  {D' : RingedTopos.{v₅, u₅, w}} {D'' : RingedTopos.{v₆, u₆, w}}
  [C.J.HasSheafCompose (forget RingCat.{w})] [C'.J.HasSheafCompose (forget RingCat.{w})]
  [C''.J.HasSheafCompose (forget RingCat.{w})] [D.J.HasSheafCompose (forget RingCat.{w})]
  [D'.J.HasSheafCompose (forget RingCat.{w})] [D''.J.HasSheafCompose (forget RingCat.{w})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C''.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D''.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [C''.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D''.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify C.J AddCommGrpCat.{w}] [HasSheafify C'.J AddCommGrpCat.{w}]
  [HasSheafify C''.J AddCommGrpCat.{w}] [HasSheafify D.J AddCommGrpCat.{w}]
  [HasSheafify D'.J AddCommGrpCat.{w}] [HasSheafify D''.J AddCommGrpCat.{w}]
  [C.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [C'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [C''.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D''.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf C.O))]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf C'.O))]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf C''.O))]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf D.O))]
  [EnoughInjectives (SheafOfModules.{w} (ringSheaf D'.O))]
  (f : AlgebraicGeometry.RingedToposHom C D)
  (f' : AlgebraicGeometry.RingedToposHom C' D')
  (f'' : AlgebraicGeometry.RingedToposHom C'' D'')
  (g : AlgebraicGeometry.RingedToposHom D' D)
  (g' : AlgebraicGeometry.RingedToposHom C' C)
  (h : AlgebraicGeometry.RingedToposHom D'' D')
  (h' : AlgebraicGeometry.RingedToposHom C'' C')
  (g₀ : AlgebraicGeometry.RingedToposHom D'' D)
  (g'₀ : AlgebraicGeometry.RingedToposHom C'' C)
  (comm : pushforwardModules g'.toRingedToposModulesHom ⋙
      pushforwardModules f.toRingedToposModulesHom ≅
    pushforwardModules f'.toRingedToposModulesHom ⋙
      pushforwardModules g.toRingedToposModulesHom)
  (comm₂ : pushforwardModules h'.toRingedToposModulesHom ⋙
      pushforwardModules f'.toRingedToposModulesHom ≅
    pushforwardModules f''.toRingedToposModulesHom ⋙
      pushforwardModules h.toRingedToposModulesHom)
  (comm₀ : pushforwardModules g'₀.toRingedToposModulesHom ⋙
      pushforwardModules f.toRingedToposModulesHom ≅
    pushforwardModules f''.toRingedToposModulesHom ⋙
      pushforwardModules g₀.toRingedToposModulesHom)
  (hg : g.IsFlat) (hg' : g'.IsFlat) (hh : h.IsFlat) (hh' : h'.IsFlat)
  (hg₀ : g₀.IsFlat) (hg'₀ : g'₀.IsFlat)
  (cU : pullbackModules g.toRingedToposModulesHom ⋙
      pullbackModules h.toRingedToposModulesHom ≅
    pullbackModules g₀.toRingedToposModulesHom)
  (cV : pullbackModules g'.toRingedToposModulesHom ⋙
      pullbackModules h'.toRingedToposModulesHom ≅
    pullbackModules g'₀.toRingedToposModulesHom)

/-- **Horizontal pasting of the base change map of Stacks 0736, in every degree.**  For two
commutative squares of ringed topoi sharing a vertical edge, all six horizontal morphisms flat,
the base change map `g₀^* Rf_* ⟶ R(f'')_* (g'₀)^*` of the pasted rectangle is the composite of
the base change maps of the two squares, read through the comparisons
`Stacks.Cohomology.ToposBaseChange.flatPullbackCompIso` of the derived inverse images along the
two composite horizontal legs.

The hypothesis `hτ` is exactly the **degree-zero** pasting identity, for the three underived
base change maps `Stacks.Cohomology.ToposBaseChange.moduleBaseChange`, evaluated at each sheaf of
modules.  Since each of the three derived base change maps is the descent of its underived one
along the derived-functor unit of the corresponding `Rf_*`, and `Rf_* ⋙ Rg^*` is a right derived
functor of `f_* ⋙ g^*` with that unit, the degree-zero identity determines the derived one;  that
descent is the generic `Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app`, whose four
exactness hypotheses are supplied here by flatness through **Stacks 04JC**.

This is the shape **Stacks 073K**, part (1) needs in order to restrict the base change map of a
cartesian square to a localization of its base:  pasting the square onto the cartesian square of
a localization composes the two *bottom* arrows, so the law that identifies the restricted base
change map with the base change map of the restricted square is this horizontal one. -/
theorem baseChangeMap_horizontal
    (hτ : ∀ M, (moduleBaseChange f f'' g₀ g'₀ comm₀).app M =
      cU.inv.app ((pushforwardModules f.toRingedToposModulesHom).obj M) ≫
        (pullbackModules h.toRingedToposModulesHom).map
          ((moduleBaseChange f f' g g' comm).app M) ≫
        (moduleBaseChange f' f'' h h' comm₂).app
          ((pullbackModules g'.toRingedToposModulesHom).obj M) ≫
        (pushforwardModules f''.toRingedToposModulesHom).map (cV.hom.app M))
    (M : DerivedCategory.Plus (SheafOfModules.{w} (ringSheaf C.O))) :
    (baseChangeMap f f'' g₀ g'₀ comm₀ hg₀ hg'₀).app M =
      (flatPullbackCompIso g hg h hh g₀ hg₀ cU).inv.app
          ((pushforwardModules f.toRingedToposModulesHom).rightDerivedFunctorPlus.obj M) ≫
        (flatPullback h hh).map ((baseChangeMap f f' g g' comm hg hg').app M) ≫
          (baseChangeMap f' f'' h h' comm₂ hh hh').app ((flatPullback g' hg').obj M) ≫
            (pushforwardModules f''.toRingedToposModulesHom).rightDerivedFunctorPlus.map
              ((flatPullbackCompIso g' hg' h' hh' g'₀ hg'₀ cV).hom.app M) := by
  obtain ⟨_, _⟩ := pullbackModules_preservesFinite_of_isFlat g hg
  obtain ⟨_, _⟩ := pullbackModules_preservesFinite_of_isFlat h hh
  obtain ⟨_, _⟩ := pullbackModules_preservesFinite_of_isFlat g₀ hg₀
  obtain ⟨_, _⟩ := pullbackModules_preservesFinite_of_isFlat h' hh'
  exact Stacks.Cohomology.BaseChange.derived_eq_derivedPaste_app
    (pushforwardModules f.toRingedToposModulesHom)
    (pushforwardModules f'.toRingedToposModulesHom)
    (pushforwardModules f''.toRingedToposModulesHom)
    (pullbackModules g.toRingedToposModulesHom)
    (pullbackModules h.toRingedToposModulesHom)
    (pullbackModules g₀.toRingedToposModulesHom)
    (pullbackModules g'.toRingedToposModulesHom)
    (pullbackModules h'.toRingedToposModulesHom)
    (pullbackModules g'₀.toRingedToposModulesHom)
    cU cV
    (moduleBaseChange f f'' g₀ g'₀ comm₀)
    (moduleBaseChange f f' g g' comm)
    (moduleBaseChange f' f'' h h' comm₂)
    hτ M

end Paste

end Stacks.Cohomology.ToposBaseChange

end
