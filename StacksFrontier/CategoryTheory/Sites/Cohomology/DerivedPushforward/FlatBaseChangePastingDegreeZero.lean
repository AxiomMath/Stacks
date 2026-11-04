module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.FlatBaseChangePasting
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.BaseChangeMateHorizontalPasting

/-!
# Horizontal pasting of the degree-zero base change map of ringed topoi

Let

```
        h'        g'
  C'' ———→ C' ———→ C
   | f''     | f'    | f
   v         v       v
  D'' ———→ D' ———→ D
         h         g
```

be two commutative squares of ringed topoi sharing a vertical edge, with `g₀ : D'' ⟶ D` and
`g'₀ : C'' ⟶ C` standing for the two composite horizontal legs through comparisons
`cU : g^* ∘ h^* ≅ g₀^*` and `cV : (g')^* ∘ (h')^* ≅ (g'₀)^*` of the inverse images.

This file proves the **degree-zero** horizontal pasting law of **Stacks 0E47** at this seating:
the underived base change map `Stacks.Cohomology.ToposBaseChange.moduleBaseChange` of the pasted
rectangle is the composite of the base change maps of the two squares.  Its statement is exactly
the hypothesis `hτ` of `Stacks.Cohomology.ToposBaseChange.baseChangeMap_horizontal`, which
descends it to every degree, so the two together give the pasting law on bounded below derived
categories with nothing assumed about the base change maps.

## Main results

* `Stacks.Cohomology.ToposBaseChange.moduleBaseChange_eq_mate`: the base change map of a square
  *is* the base change mate across the two vertical adjunctions of **Stacks 03D7** — true by
  definition, stated so that it can be rewritten with.
* `Stacks.Cohomology.ToposBaseChange.moduleBaseChange_horizontal`: **the degree-zero pasting
  law**, from the pasting law for the comparisons of composite inverse images.

## Implementation notes

*Why the law is proved here, with the topoi as variables.*  Because at a geometric seating — the
six ringed topoi the small étale ringed topoi of six algebraic spaces — it cannot even be
*written*.  Elaborating the statement below at that instance, with the proof stubbed out so
that only the statement is elaborated, is a `(deterministic) timeout at isDefEq` at 200,000
heartbeats (12.0s to fail);  the same statement with each of the three base change maps written
as the named `AlgebraicGeometry.Space.toposModuleBaseChangeMap`, and nothing else changed,
elaborates in 3.8s, and writing the inverse images one way or the other makes no difference.  So
the cost is the three occurrences of `moduleBaseChange` and nothing else.  Proving the law once
with the topoi as variables makes those occurrences free, and `moduleBaseChange_horizontal_of_eq`
below moves each of them into an equation of its own for a consumer that must name its maps.  The
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ToposModuleBaseChangeHorizontal.lean` record what a
geometric instance of the law is still blocked on, which is not this and not any hypothesis of
the engine.

*What the proof needs that the engine does not supply.*  The engine concludes about
`Stacks.Cohomology.BaseChange.mate`, and `moduleBaseChange` is that mate by definition, but the
elaborator does not take the three delta-steps on its own:  with the identification left to
unification the application reaches `maximum recursion depth` (5.9s to
fail, and naming the adjunctions does not change that — the recursion is in the three
`moduleBaseChange`s, not in the nine adjunctions).  Rewriting with
`moduleBaseChange_eq_mate` first, one square at a time, is what makes it go through.

*What the hypotheses are.*  The three squares enter only through their comparisons `α`, `α₂`,
`α₀` of the two composite *inverse* images, each pinned by `hα`, `hα₂`, `hα₀` to the comparison
of composite direct images it is the conjugate of — that is **Stacks 03D8** at a square, and it
is what makes each base change map the mate of its square.  The one hypothesis about the
geometry is then `hs`, the cocycle condition of **Stacks 03LU** expressing the rectangle's
comparison as the pasting of the two squares' through `cU` and `cV`.  Nothing is assumed about
the base change maps themselves;  no flatness and no acyclicity enters, this being the underived
statement.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

namespace Stacks.Cohomology.ToposBaseChange

universe w v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

/-! ### The base change map of a square is a mate -/

section Square

variable {C : RingedTopos.{v₁, u₁, w}} {C' : RingedTopos.{v₂, u₂, w}}
  {D : RingedTopos.{v₃, u₃, w}} {D' : RingedTopos.{v₄, u₄, w}}
  [C.J.HasSheafCompose (forget RingCat.{w})] [C'.J.HasSheafCompose (forget RingCat.{w})]
  [D.J.HasSheafCompose (forget RingCat.{w})] [D'.J.HasSheafCompose (forget RingCat.{w})]
  [C.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [C.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [C'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [D'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasSheafify C'.J AddCommGrpCat.{w}] [HasSheafify D'.J AddCommGrpCat.{w}]
  [C'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposHom C D)
  (f' : AlgebraicGeometry.RingedToposHom C' D')
  (g : AlgebraicGeometry.RingedToposHom D' D)
  (g' : AlgebraicGeometry.RingedToposHom C' C)

/-- **The degree-zero base change map of a square of ringed topoi is the base change mate** of
the comparison of its two composite direct images, across the two adjunctions of **Stacks 03D7**
for its two *vertical* morphisms.

`Stacks.Cohomology.ToposBaseChange.moduleBaseChange` is defined as that mate, so this holds by
`rfl`.  It is stated because the elaborator does not take the step on its own:  the pasting law
below is the engine's conclusion about three mates, and leaving their identification with the
three base change maps to unification reaches `maximum recursion depth`, while rewriting with
this lemma one square at a time is free. -/
theorem moduleBaseChange_eq_mate
    (comm : pushforwardModules g'.toRingedToposModulesHom ⋙
        pushforwardModules f.toRingedToposModulesHom ≅
      pushforwardModules f'.toRingedToposModulesHom ⋙
        pushforwardModules g.toRingedToposModulesHom) :
    moduleBaseChange f f' g g' comm =
      Stacks.Cohomology.BaseChange.mate
        (pullbackAdjPushforwardModules g.toRingedToposModulesHom)
        (pullbackAdjPushforwardModules g'.toRingedToposModulesHom)
        (pushforwardModules f.toRingedToposModulesHom)
        (pushforwardModules f'.toRingedToposModulesHom) comm := rfl

end Square

/-! ### The pasting law in degree zero -/

section PasteDegreeZero

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
  [HasSheafify C''.J AddCommGrpCat.{w}]
  [HasSheafify D'.J AddCommGrpCat.{w}] [HasSheafify D''.J AddCommGrpCat.{w}]
  [C.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [C'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [C''.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [D''.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
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
  (cU : pullbackModules g.toRingedToposModulesHom ⋙
      pullbackModules h.toRingedToposModulesHom ≅
    pullbackModules g₀.toRingedToposModulesHom)
  (cV : pullbackModules g'.toRingedToposModulesHom ⋙
      pullbackModules h'.toRingedToposModulesHom ≅
    pullbackModules g'₀.toRingedToposModulesHom)
  (α : TwoSquare (pullbackModules g.toRingedToposModulesHom)
    (pullbackModules f.toRingedToposModulesHom)
    (pullbackModules f'.toRingedToposModulesHom)
    (pullbackModules g'.toRingedToposModulesHom))
  (α₂ : TwoSquare (pullbackModules h.toRingedToposModulesHom)
    (pullbackModules f'.toRingedToposModulesHom)
    (pullbackModules f''.toRingedToposModulesHom)
    (pullbackModules h'.toRingedToposModulesHom))
  (α₀ : TwoSquare (pullbackModules g₀.toRingedToposModulesHom)
    (pullbackModules f.toRingedToposModulesHom)
    (pullbackModules f''.toRingedToposModulesHom)
    (pullbackModules g'₀.toRingedToposModulesHom))

/-- **Horizontal pasting of the degree-zero base change map of Stacks 0736**, the shape
**Stacks 0E47** takes for `Stacks.Cohomology.ToposBaseChange.moduleBaseChange`:  for two
commutative squares of ringed topoi sharing a vertical edge, the base change map
`g₀^* f_* ⟶ (f'')_* (g'₀)^*` of the pasted rectangle is the composite of the base change maps of
the two squares, read through the comparisons `cU`, `cV` of the inverse images along the two
composite horizontal legs.

This is exactly the hypothesis `hτ` of
`Stacks.Cohomology.ToposBaseChange.baseChangeMap_horizontal`, which descends it to every degree.

Each of the three base change maps is the base change mate of its square across the two vertical
adjunctions of **Stacks 03D7**, by `moduleBaseChange_eq_mate`, so this is the generic engine
`Stacks.Cohomology.BaseChange.mate_horizontal`;  `hα`, `hα₂`, `hα₀` are **Stacks 03D8** at the
three squares and `hs` the cocycle condition of **Stacks 03LU** for their comparisons of
composite inverse images. -/
theorem moduleBaseChange_horizontal
    (hα : conjugateEquiv
        ((pullbackAdjPushforwardModules f.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules g'.toRingedToposModulesHom))
        ((pullbackAdjPushforwardModules g.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules f'.toRingedToposModulesHom)) α = comm.hom)
    (hα₂ : conjugateEquiv
        ((pullbackAdjPushforwardModules f'.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules h'.toRingedToposModulesHom))
        ((pullbackAdjPushforwardModules h.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules f''.toRingedToposModulesHom)) α₂ = comm₂.hom)
    (hα₀ : conjugateEquiv
        ((pullbackAdjPushforwardModules f.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules g'₀.toRingedToposModulesHom))
        ((pullbackAdjPushforwardModules g₀.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules f''.toRingedToposModulesHom)) α₀ = comm₀.hom)
    (hs : ∀ M, (pullbackModules f''.toRingedToposModulesHom).map (cU.inv.app M) ≫
      α₂.app ((pullbackModules g.toRingedToposModulesHom).obj M) ≫
        (pullbackModules h'.toRingedToposModulesHom).map (α.app M) ≫
          cV.hom.app ((pullbackModules f.toRingedToposModulesHom).obj M) = α₀.app M)
    (M : SheafOfModules.{w} (ringSheaf C.O)) :
    (moduleBaseChange f f'' g₀ g'₀ comm₀).app M =
      cU.inv.app ((pushforwardModules f.toRingedToposModulesHom).obj M) ≫
        (pullbackModules h.toRingedToposModulesHom).map
          ((moduleBaseChange f f' g g' comm).app M) ≫
        (moduleBaseChange f' f'' h h' comm₂).app
          ((pullbackModules g'.toRingedToposModulesHom).obj M) ≫
        (pushforwardModules f''.toRingedToposModulesHom).map (cV.hom.app M) := by
  rw [moduleBaseChange_eq_mate f f'' g₀ g'₀ comm₀, moduleBaseChange_eq_mate f f' g g' comm,
    moduleBaseChange_eq_mate f' f'' h h' comm₂]
  exact (Stacks.Cohomology.BaseChange.mate_horizontal
    (pullbackAdjPushforwardModules f.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules f'.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules f''.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules g.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules g'.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules h.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules h'.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules g₀.toRingedToposModulesHom)
    (pullbackAdjPushforwardModules g'₀.toRingedToposModulesHom)
    comm comm₂ comm₀ cU cV α α₂ α₀ hα hα₂ hα₀ hs M).symm

/-- **The degree-zero horizontal pasting law read through three given names for its base change
maps.**  Each of the three maps is supplied as a morphism `τ₀`, `τ`, `τ₂` together with an
equation identifying it with the base change map of its square, and the conclusion is the law of
`moduleBaseChange_horizontal` written with those names.

This is what a geometric instance of the law is proved by, and the generalization is what makes
that possible.  A statement of the law in which the three maps are written as
`moduleBaseChange` itself does not elaborate at a geometric seating:  with the six ringed topoi
the small étale ringed topoi of six algebraic spaces, elaborating such a statement — with no
proof at all — is a `(deterministic) timeout at isDefEq` at 200,000 heartbeats
(12.0s to fail).  The same statement with the three maps named, and
*nothing else changed*, elaborates in 3.8s;  the cost is in the three occurrences of
`moduleBaseChange` and in nothing else, neither in the composite nor in the spelling of the
direct and inverse images.  Taking the three as variables moves each occurrence into its own
equation, where one at a time it is affordable, and leaves the law's statement free. -/
theorem moduleBaseChange_horizontal_of_eq
    (τ₀ : pushforwardModules f.toRingedToposModulesHom ⋙
        pullbackModules g₀.toRingedToposModulesHom ⟶
      pullbackModules g'₀.toRingedToposModulesHom ⋙
        pushforwardModules f''.toRingedToposModulesHom)
    (τ : pushforwardModules f.toRingedToposModulesHom ⋙
        pullbackModules g.toRingedToposModulesHom ⟶
      pullbackModules g'.toRingedToposModulesHom ⋙
        pushforwardModules f'.toRingedToposModulesHom)
    (τ₂ : pushforwardModules f'.toRingedToposModulesHom ⋙
        pullbackModules h.toRingedToposModulesHom ⟶
      pullbackModules h'.toRingedToposModulesHom ⋙
        pushforwardModules f''.toRingedToposModulesHom)
    (hτ₀ : τ₀ = moduleBaseChange f f'' g₀ g'₀ comm₀)
    (hτ : τ = moduleBaseChange f f' g g' comm)
    (hτ₂ : τ₂ = moduleBaseChange f' f'' h h' comm₂)
    (hα : conjugateEquiv
        ((pullbackAdjPushforwardModules f.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules g'.toRingedToposModulesHom))
        ((pullbackAdjPushforwardModules g.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules f'.toRingedToposModulesHom)) α = comm.hom)
    (hα₂ : conjugateEquiv
        ((pullbackAdjPushforwardModules f'.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules h'.toRingedToposModulesHom))
        ((pullbackAdjPushforwardModules h.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules f''.toRingedToposModulesHom)) α₂ = comm₂.hom)
    (hα₀ : conjugateEquiv
        ((pullbackAdjPushforwardModules f.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules g'₀.toRingedToposModulesHom))
        ((pullbackAdjPushforwardModules g₀.toRingedToposModulesHom).comp
          (pullbackAdjPushforwardModules f''.toRingedToposModulesHom)) α₀ = comm₀.hom)
    (hs : ∀ M, (pullbackModules f''.toRingedToposModulesHom).map (cU.inv.app M) ≫
      α₂.app ((pullbackModules g.toRingedToposModulesHom).obj M) ≫
        (pullbackModules h'.toRingedToposModulesHom).map (α.app M) ≫
          cV.hom.app ((pullbackModules f.toRingedToposModulesHom).obj M) = α₀.app M)
    (M : SheafOfModules.{w} (ringSheaf C.O)) :
    τ₀.app M =
      cU.inv.app ((pushforwardModules f.toRingedToposModulesHom).obj M) ≫
        (pullbackModules h.toRingedToposModulesHom).map (τ.app M) ≫
        τ₂.app ((pullbackModules g'.toRingedToposModulesHom).obj M) ≫
        (pushforwardModules f''.toRingedToposModulesHom).map (cV.hom.app M) := by
  subst hτ₀
  subst hτ
  subst hτ₂
  exact moduleBaseChange_horizontal f f' f'' g g' h h' g₀ g'₀ comm comm₂ comm₀ cU cV α α₂ α₀
    hα hα₂ hα₀ hs M

end PasteDegreeZero

end Stacks.Cohomology.ToposBaseChange

end
