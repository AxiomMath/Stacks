module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DatumChartTransition

/-!
# The two laws of the transition of a descent datum read on a chart

Let `X` be an algebraic space over a scheme `S`, let `(f i : Y i ⟶ X)` be a family of algebraic
spaces over `X`, and let `D` be a descent datum for quasi-coherent modules relative to that
family.  On a test space `T` carrying a morphism `v` to `Y i ×_X Y j` and the two étale
composites `vi`, `vj` to the members, the transition of `D` is read on the sections over a chart
`U` of `T` as a bijection

`D.F i` over the chart `U ≫ vi` of `Y i`  ⟷  `D.F j` over the chart `U ≫ vj` of `Y j`,

namely `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect`.  This file supplies the two
laws that make that reading presheaf data on the charts of the members of the family: it is
**natural in the chart**, and it **composes across three members**.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_restrict`: **naturality in the
  chart.**  Restricting a section along the morphism of charts of `Y i` induced by a morphism `c`
  of charts of the test space and then carrying it across is carrying it across and then
  restricting along the morphism of charts of `Y j` induced by `c`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect_comp`: **the cocycle.**  For three
  members and a test space mapping compatibly to all three, carrying a section from `i` to `j`
  and then from `j` to `k` is carrying it from `i` to `k`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionHom_sect_restrict` and
  `.transitionHom_comp_apply`: the two laws for the bare transition morphism, before the source is
  read back as a section of the inverse image.  These are the halves the two laws above are
  assembled from.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.hom_val_app_comp_congr`: two morphisms of modules
  which are the components of two isomorphisms composing to a third agree, on a section, with the
  component of that third.  Stated on variables.

Neither law needs the compatibility
`AlgebraicGeometry.Space.QuasiCoherentDescent.ModulePullbackCompIsoEtaleRestriction` of the
comparison of Stacks 03LU with étale restriction.  Naturality is the naturality of a morphism of
modules in the chart, and the cocycle is the cocycle condition of the descent datum itself, which
is already stated at an arbitrary test space; the reading of both ends happens over one chart of
one test space, so no comparison of iterated inverse images is crossed.

## Implementation notes

**Every statement below writes the reading out.**  The two laws are *about*
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect`, which is by definition the
composite of `.etaleSectInv`, the transition and `.etaleSect` appearing in them, but none of them
names it.  That is forced, and the measurements are these.  A statement naming `transitionSect`
on both sides of an equation elaborates in milliseconds; a statement in which `transitionSect` or
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSectRaw` has to be matched against the
written-out composite — including the `rfl` equation between the two spellings — exhausts the
elaborator's recursion depth.  So does the same match performed on the goal left by
`unfold transitionSect transitionSectRaw`, even though that goal prints exactly as the
written-out statement: the instances carried by the unfolding and the instances a fresh
elaboration synthesizes are reconciled only by unfolding
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, and that does not terminate.  The
rule this file follows is therefore the one
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackCompUnit.lean` records: never write a
statement mixing two spellings of one object, and let the reading be the written-out one.

For the same reason `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionHom_comp_apply` is
stated with `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionHom` and proved through
`.hom_val_app_comp_congr`, whose three morphisms are variables identified with the components of
the three isomorphisms by separate hypotheses.  That is what crosses from the `transitionOn`
spelling, in which the cocycle condition of a descent datum is stated, to the `transitionHom`
spelling, in which the reading is defined, in one definitional step; asking the unifier to cross
it inside a section type does not terminate either.

No `@[stacks]` attribute is carried: nothing below is an assertion of a numbered result.

## References

* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {I : Type v} {X : AlgebraicSpaces B S hS} (Yi : I → AlgebraicSpaces B S hS)
  (f : ∀ i, Yi i ⟶ X)

/-! ### Naturality in the chart -/

/-- **The transition of a descent datum, read on its target only, is natural in the chart.**
Restricting a section of the inverse image along a morphism `c` of charts of the test space and
then carrying it across the transition is carrying it across and then restricting along the
induced morphism of charts of `Y j`.

The left-hand side is `AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSectRaw` at the
restricted section, written out. -/
theorem transitionHom_sect_restrict (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS}
    (i j : I) (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvj : IsEtale B S hS vj.hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    {U U' : SmallEtale B S hS T.1} (c : U' ⟶ U)
    (m : ((modulePullback B S hS vi).obj (D.F i)).val.obj (.op U)) :
    etaleSect B S hS vj hvj (D.F j) U'
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (.op U')
          (((modulePullback B S hS vi).obj (D.F i)).val.map c.op m)) =
      (D.F j).val.map ((smallEtalePostcomp B S hS vj hvj).map c).op
        (etaleSect B S hS vj hvj (D.F j) U
          ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (.op U) m)) :=
  etaleSect_hom_restrict B S hS vj hvj (transitionHom B S hS Yi f D i j v vi vj hi hj) c m

/-- **The transition of a descent datum, read on sections over a chart, is natural in the
chart.**  This is the first of the two laws that make
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect` presheaf data: restricting a
section of `D.F i` along the morphism of charts of `Y i` induced by a morphism `c` of charts of
the test space, and then carrying it to `D.F j`, is carrying it across and then restricting along
the morphism of charts of `Y j` induced by `c`.

Both sides are written out: the left-hand side is `.transitionSect` over `U'` at the restricted
section, and the right-hand side the restriction of `.transitionSect` over `U`. -/
theorem transitionSect_restrict (D : DescentDatum B S hS Yi f) {T : AlgebraicSpaces B S hS}
    (i j : I) (v : T ⟶ pair B S hS Yi f i j) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom)
    (hi : v ≫ pairFst B S hS Yi f i j = vi) (hj : v ≫ pairSnd B S hS Yi f i j = vj)
    {U U' : SmallEtale B S hS T.1} (c : U' ⟶ U)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS vi hvi).obj U))) :
    etaleSect B S hS vj hvj (D.F j) U'
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (.op U')
          (etaleSectInv B S hS vi hvi (D.F i) U'
            ((D.F i).val.map ((smallEtalePostcomp B S hS vi hvi).map c).op s))) =
      (D.F j).val.map ((smallEtalePostcomp B S hS vj hvj).map c).op
        (etaleSect B S hS vj hvj (D.F j) U
          ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (.op U)
            (etaleSectInv B S hS vi hvi (D.F i) U s))) :=
  (congrArg (fun z => etaleSect B S hS vj hvj (D.F j) U'
        ((transitionHom B S hS Yi f D i j v vi vj hi hj).val.app (.op U') z))
      (etaleSectInv_restrict B S hS vi hvi (D.F i) c s)).trans
    (transitionHom_sect_restrict B S hS Yi f D i j v vi vj hvj hi hj c
      (etaleSectInv B S hS vi hvi (D.F i) U s))

/-! ### The cocycle -/

/-- Two morphisms of modules which are the components of two isomorphisms whose composite is a
third agree, on a section, with the component of that third.  The three morphisms are variables
identified with the three components by hypotheses, which is what lets a consumer state the
conclusion in its own spelling of them. -/
theorem hom_val_app_comp_congr {D₀ : AlgebraicSpaces B S hS}
    {P Q R : Modules.{u, u} B S hS D₀.1 D₀.2} {e : P ≅ Q} {e' : Q ≅ R} {e'' : P ≅ R}
    (h : e ≪≫ e' = e'') (ψ : P ⟶ Q) (ψ' : Q ⟶ R) (ψ'' : P ⟶ R)
    (hψ : ψ = e.hom) (hψ' : ψ' = e'.hom) (hψ'' : ψ'' = e''.hom)
    (U : SmallEtale B S hS D₀.1) (m : P.val.obj (.op U)) :
    ψ'.val.app (.op U) (ψ.val.app (.op U) m) = ψ''.val.app (.op U) m := by
  subst hψ hψ' hψ''
  rw [← h]
  rfl

/-- **The cocycle condition of a descent datum, read on sections over a chart of a test space.**
For three members of the family and a test space mapping compatibly to all three, the transitions
from `i` to `j` and from `j` to `k` compose, on sections of the inverse images over a chart, to
the transition from `i` to `k`.

This is `AlgebraicGeometry.Space.QuasiCoherentDescent.DescentDatum.cocycle` read through
`.hom_val_app_comp_congr`; the condition is already stated at an arbitrary test space, so nothing
has to be transported to reach the chart. -/
theorem transitionHom_comp_apply (D : DescentDatum B S hS Yi f) (i j k : I)
    (T : AlgebraicSpaces B S hS) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j) (vk : T ⟶ Yi k)
    (vij : T ⟶ pair B S hS Yi f i j) (vjk : T ⟶ pair B S hS Yi f j k)
    (vik : T ⟶ pair B S hS Yi f i k)
    (hij₀ : vij ≫ pairFst B S hS Yi f i j = vi) (hij₁ : vij ≫ pairSnd B S hS Yi f i j = vj)
    (hjk₀ : vjk ≫ pairFst B S hS Yi f j k = vj) (hjk₁ : vjk ≫ pairSnd B S hS Yi f j k = vk)
    (hik₀ : vik ≫ pairFst B S hS Yi f i k = vi) (hik₁ : vik ≫ pairSnd B S hS Yi f i k = vk)
    (U : SmallEtale B S hS T.1)
    (m : ((modulePullback B S hS vi).obj (D.F i)).val.obj (.op U)) :
    (transitionHom B S hS Yi f D j k vjk vj vk hjk₀ hjk₁).val.app (.op U)
        ((transitionHom B S hS Yi f D i j vij vi vj hij₀ hij₁).val.app (.op U) m) =
      (transitionHom B S hS Yi f D i k vik vi vk hik₀ hik₁).val.app (.op U) m :=
  hom_val_app_comp_congr B S hS
    (e := transitionOn B S hS Yi f D.F D.transition i j vij vi vj hij₀ hij₁)
    (e' := transitionOn B S hS Yi f D.F D.transition j k vjk vj vk hjk₀ hjk₁)
    (e'' := transitionOn B S hS Yi f D.F D.transition i k vik vi vk hik₀ hik₁)
    (D.cocycle i j k T vi vj vk vij vjk vik hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁)
    (transitionHom B S hS Yi f D i j vij vi vj hij₀ hij₁)
    (transitionHom B S hS Yi f D j k vjk vj vk hjk₀ hjk₁)
    (transitionHom B S hS Yi f D i k vik vi vk hik₀ hik₁) rfl rfl rfl U m

/-- **The transition of a descent datum, read on sections over a chart, composes across three
members.**  This is the second of the two laws that make
`AlgebraicGeometry.Space.QuasiCoherentDescent.transitionSect` presheaf data: over a chart `U` of
a test space mapping compatibly to three members, carrying a section of `D.F i` to `D.F j` and
then to `D.F k` is carrying it to `D.F k` directly.

All three readings are taken over the same chart of the same test space, so the two sides are
sections over literally the same chart of `Y k` and no transport appears.  Both sides are written
out: the left-hand side is `.transitionSect` from `j` to `k` applied to `.transitionSect` from
`i` to `j`, and the right-hand side is `.transitionSect` from `i` to `k`. -/
theorem transitionSect_comp (D : DescentDatum B S hS Yi f) (i j k : I)
    (T : AlgebraicSpaces B S hS) (vi : T ⟶ Yi i) (vj : T ⟶ Yi j) (vk : T ⟶ Yi k)
    (hvi : IsEtale B S hS vi.hom) (hvj : IsEtale B S hS vj.hom) (hvk : IsEtale B S hS vk.hom)
    (vij : T ⟶ pair B S hS Yi f i j) (vjk : T ⟶ pair B S hS Yi f j k)
    (vik : T ⟶ pair B S hS Yi f i k)
    (hij₀ : vij ≫ pairFst B S hS Yi f i j = vi) (hij₁ : vij ≫ pairSnd B S hS Yi f i j = vj)
    (hjk₀ : vjk ≫ pairFst B S hS Yi f j k = vj) (hjk₁ : vjk ≫ pairSnd B S hS Yi f j k = vk)
    (hik₀ : vik ≫ pairFst B S hS Yi f i k = vi) (hik₁ : vik ≫ pairSnd B S hS Yi f i k = vk)
    (U : SmallEtale B S hS T.1)
    (s : (D.F i).val.obj (.op ((smallEtalePostcomp B S hS vi hvi).obj U))) :
    etaleSect B S hS vk hvk (D.F k) U
        ((transitionHom B S hS Yi f D j k vjk vj vk hjk₀ hjk₁).val.app (.op U)
          (etaleSectInv B S hS vj hvj (D.F j) U
            (etaleSect B S hS vj hvj (D.F j) U
              ((transitionHom B S hS Yi f D i j vij vi vj hij₀ hij₁).val.app (.op U)
                (etaleSectInv B S hS vi hvi (D.F i) U s))))) =
      etaleSect B S hS vk hvk (D.F k) U
        ((transitionHom B S hS Yi f D i k vik vi vk hik₀ hik₁).val.app (.op U)
          (etaleSectInv B S hS vi hvi (D.F i) U s)) :=
  (congrArg (fun z => etaleSect B S hS vk hvk (D.F k) U
        ((transitionHom B S hS Yi f D j k vjk vj vk hjk₀ hjk₁).val.app (.op U) z))
      (etaleSectInv_etaleSect B S hS vj hvj (D.F j) U
        ((transitionHom B S hS Yi f D i j vij vi vj hij₀ hij₁).val.app (.op U)
          (etaleSectInv B S hS vi hvi (D.F i) U s)))).trans
    (congrArg (etaleSect B S hS vk hvk (D.F k) U)
      (transitionHom_comp_apply B S hS Yi f D i j k T vi vj vk vij vjk vik
        hij₀ hij₁ hjk₀ hjk₁ hik₀ hik₁ U (etaleSectInv B S hS vi hvi (D.F i) U s)))

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
