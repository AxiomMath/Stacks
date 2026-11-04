module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.MemberSiteComparison

/-!
# The transition of a descent datum, read on a chart

Let `X` be an algebraic space over a scheme `S` and let `(f i : Y i ⟶ X)` be a family of
algebraic spaces étale over `X`.  A descent datum `D` for quasi-coherent modules relative to that
family carries, on every test space `T` equipped with compatible morphisms `vi : T ⟶ Y i` and
`vj : T ⟶ Y j`, an isomorphism of the two inverse images,
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionOn`.  Along an étale morphism the inverse
image is restriction of sections, by Stacks 03LW, so when `vi` and `vj` are étale that
isomorphism becomes a bijection

`D.F i` over the chart `U ≫ vi` of `Y i`  ⟷  `D.F j` over the chart `U ≫ vj` of `Y j`

for every chart `U` of `T`.  That reading is
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect`, and it is the datum from which the
sheaf of modules on the site of the charts of the members of a covering is to be assembled — the
object-level counterpart of `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm`, which is
the same reading for a *morphism* of the inverse images and which the full faithfulness clause of
Stacks 04W6 rests on.

This file supplies the reading and the section calculus it needs.  The two laws that make it a
presheaf on the charts of the members — naturality in the chart and the cocycle across three
members — are in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartLaws.lean`, stated with the
reading written out; the implementation notes below say why they cannot be stated with the names
this file defines.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionHom` is the transition of a descent
  datum on a test space, as a bare morphism of the two inverse images.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSectRaw` reads it on the sections of
  the inverse image over a chart of the test space, and
  `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect` reads both ends as sections of
  the component modules over the induced charts.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSectInv_restrict`: reading a section of an
  étale restriction back as a section of the inverse image commutes with restriction along a
  morphism of charts.  This is `.etaleSect_restrict` in the inverse direction, which the reading
  of the *source* of a transition needs.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect_hom_restrict`: reading the target of a
  morphism into an inverse image commutes with restriction along a morphism of charts.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect_comp_apply`: reading the target of a
  composite of two such morphisms is reading the target of the composite.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.iso_hom_val_app_congr`: equal isomorphisms of
  modules agree on a local section.

The last three are stated on variables, which is what makes each of them cost one definitional
step at a use instead of a search.

## Implementation notes

**Why the section calculus is stated on variables.**  The three lemmas above mention only a
morphism of modules, two charts and a section; none of them mentions a descent datum.  Stated
that way they elaborate in milliseconds.  The same statements with the morphism written out as
`(transitionOn … D.F D.transition …).hom` elaborate too — see the next paragraph for what does
not.

**What the names below cannot appear in.**  The naturality of
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSectRaw` in the chart, namely

```
transitionSectRaw … U' (((modulePullback B S hS vi).obj (D.F i)).val.map c.op m) =
  (D.F j).val.map ((smallEtalePostcomp B S hS vj hvj).map c).op (transitionSectRaw … U m)
```

is exactly `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect_hom_restrict` instantiated at
`ψ := transitionHom …`, and it does not go through: the elaborator exhausts its recursion depth
matching the instantiated conclusion against the statement.  The failure is **not** in either
half separately — the statement elaborates on its own, as does each side of it, and the generic
lemma elaborates on its own; it is in the match.  Making `transitionSectRaw` an `abbrev`, naming
the transition morphism as `transitionHom` so that the unifier meets a constant rather than an
`Iso.hom` of a large term, and driving the match from a tactic rather than from a term: none of the
three changes the outcome.

What does change the outcome is writing the reading out.  The same law stated with
`etaleSect … ((transitionHom …).val.app …)` in place of `transitionSectRaw …` is closed by that
instantiation in milliseconds, and that is how both laws are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/DatumChartLaws.lean`.  What is fatal
is a statement in which one of the two names below has to be *matched against* the written-out
composite: an equation naming `transitionSect` on both sides elaborates, the `rfl` equation
between `transitionSect` and its own definition does not, and neither does an `exact` against the
goal left by `unfold transitionSect transitionSectRaw`, which prints as the written-out
statement.  The rule is the one of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackCompUnit.lean`: never write a statement
mixing two spellings of one object.

Neither law needs
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction`.  Reading at
a chart of a pairwise fibre product, through
`AlgebraicGeometry.Space.QuasiCoherentDescent.PairChartData` as
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/PairChartNaturality.lean` does for
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm`, would make naturality need it; at the
chart of an arbitrary test space, which is the reading below, both laws are free of it, because
the cocycle condition of a descent datum is itself stated at an arbitrary test space.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {C₀ D₀ : AlgebraicSpaces B S hS}

/-! ### The section calculus, on variables -/

/-- Equal isomorphisms of `𝒪_Y`-modules agree on every local section.  Stated on variables, so
that the two isomorphisms never have to be matched against a concrete term. -/
theorem iso_hom_val_app_congr {P Q : Modules.{u, u} B S hS D₀.1 D₀.2} {e e' : P ≅ Q}
    (h : e = e') (U : SmallEtale B S hS D₀.1) (m : P.val.obj (.op U)) :
    e.hom.val.app (.op U) m = e'.hom.val.app (.op U) m := by rw [h]

/-- **Reading a section of an étale restriction back as a section of the inverse image commutes
with restriction along a morphism of charts.**  This is
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleSect_restrict` in the inverse direction, which
is the direction needed to read the *source* of a morphism out of an inverse image. -/
theorem etaleSectInv_restrict (g : D₀ ⟶ C₀) (hg : IsEtale B S hS g.hom)
    (M : Modules.{u, u} B S hS C₀.1 C₀.2) {U U' : SmallEtale B S hS D₀.1} (c : U' ⟶ U)
    (s : ((etaleModulePullback.{u, u} B S hS g hg).obj M).val.obj (.op U)) :
    etaleSectInv B S hS g hg M U'
        (M.val.map ((smallEtalePostcomp B S hS g hg).map c).op s) =
      ((modulePullback B S hS g).obj M).val.map c.op (etaleSectInv B S hS g hg M U s) :=
  ((congrArg (fun z => etaleSectInv B S hS g hg M U' (M.val.map
            ((smallEtalePostcomp B S hS g hg).map c).op z))
        (etaleSect_etaleSectInv B S hS g hg M U s)).symm.trans
      (congrArg (etaleSectInv B S hS g hg M U')
        (etaleSect_restrict B S hS g hg M c (etaleSectInv B S hS g hg M U s)).symm)).trans
    (etaleSectInv_etaleSect B S hS g hg M U'
      (((modulePullback B S hS g).obj M).val.map c.op (etaleSectInv B S hS g hg M U s)))

/-- **Reading the target of a morphism into an inverse image commutes with restriction along a
morphism of charts.**  Stated on variables: the morphism, the two modules and the two charts are
all opaque, so a use is substitution. -/
theorem etaleSect_hom_restrict (w : D₀ ⟶ C₀) (hw : IsEtale B S hS w.hom)
    {P : Modules.{u, u} B S hS D₀.1 D₀.2} {N : Modules.{u, u} B S hS C₀.1 C₀.2}
    (ψ : P ⟶ (modulePullback B S hS w).obj N)
    {U U' : SmallEtale B S hS D₀.1} (c : U' ⟶ U) (m : P.val.obj (.op U)) :
    etaleSect B S hS w hw N U' (ψ.val.app (.op U') (P.val.map c.op m)) =
      N.val.map ((smallEtalePostcomp B S hS w hw).map c).op
        (etaleSect B S hS w hw N U (ψ.val.app (.op U) m)) :=
  (congrArg (etaleSect B S hS w hw N U') (val_app_restrict B S hS ψ c m)).trans
    (etaleSect_restrict B S hS w hw N c (ψ.val.app (.op U) m))

/-- **Reading the target of a composite of two morphisms is reading the target of the
composite.**  Stated on variables, so that the middle module never has to be matched against a
concrete term; this is the step through which the cocycle condition of a descent datum is meant
to reach the sections. -/
theorem etaleSect_comp_apply (w : D₀ ⟶ C₀) (hw : IsEtale B S hS w.hom)
    {P Q : Modules.{u, u} B S hS D₀.1 D₀.2} {N : Modules.{u, u} B S hS C₀.1 C₀.2}
    (α : P ⟶ Q) (β : Q ⟶ (modulePullback B S hS w).obj N) (U : SmallEtale B S hS D₀.1)
    (m : P.val.obj (.op U)) :
    etaleSect B S hS w hw N U (β.val.app (.op U) (α.val.app (.op U) m)) =
      etaleSect B S hS w hw N U ((α ≫ β).val.app (.op U) m) :=
  rfl

/-! ### The transition of a descent datum on a chart -/

variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-- The transition isomorphism of a descent datum, read on a test space `T` equipped with a
morphism to the pairwise fibre product and the two composites to the members, as a bare morphism
of the two inverse images.  Naming it keeps the unifier from meeting an `Iso.hom` of a large term
in the position of a function argument. -/
def transitionHom (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i j : I)
    (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj) :
    (modulePullback B S hS vi).obj (D.F i) ⟶ (modulePullback B S hS vj).obj (D.F j) :=
  (transitionOn B S hS Yi f D.F D.transition i j v vi vj hi hj).hom

/-- The transition of a descent datum, read on the sections of the inverse image over a chart of
the test space: its target is already a section of the `j`-th component module over the induced
chart of `Y j`, its source is not yet read. -/
def transitionSectRaw (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i j : I)
    (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvj : IsEtale B S hS vj.hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (U : SmallEtale B S hS T.1)
    (m : ((modulePullback B S hS vi).obj (D.F i)).val.obj (.op U)) :
    (D.F j).val.obj (.op ((smallEtalePostcomp B S hS vj hvj).obj U)) :=
  etaleSect B S hS vj hvj (D.F j) U
    ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (.op U) m)

/-- **The transition of a descent datum, read on sections over a chart of a test space.**  For a
chart `U` of a test space `T` carrying étale morphisms to the two members, it takes a section of
`D.F i` over the induced chart of `Y i` to a section of `D.F j` over the induced chart of `Y j`.
This is the reading out of which the sheaf of modules on the charts of the members of a covering
is to be built. -/
def transitionSect (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS} (i j : I)
    (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS vi hvi).obj U))) :
    (D.F j).val.obj (.op ((smallEtalePostcomp B S hS vj hvj).obj U)) :=
  transitionSectRaw B S hS Yi f D i j v vi vj hvj hi hj U
    (etaleSectInv B S hS vi hvi (D.F i) U s)

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
