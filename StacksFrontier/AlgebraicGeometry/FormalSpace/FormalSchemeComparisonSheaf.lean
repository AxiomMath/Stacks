module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcDescent
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsSheaf
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparison

/-!
# The fppf sheaf condition on the functor of points of a formal scheme

Let `S` be a scheme contained in a big fppf site `B`, and let `𝔛` be a formal scheme à la EGA.
`AlgebraicGeometry.FormalSpace.IsFppfSheafFormalSchemePoints` is the sheaf condition on the
functor of points of `𝔛`, read on the big fppf site of `S` and with its values lifted, and
`StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparison` carries it as a hypothesis:
the comparison of Stacks 0AIR is about the object of
`AlgebraicGeometry.FormalSpace.FppfSheaf B S hS` which that condition produces.

Two things are proved here.

*The condition depends on no base.* A covering sieve of the big fppf site of `S` has fpqc
covering image in the category of all schemes, and the functor `BigFppfOver.toScheme` is
compatible preserving, so the sheaf condition for the fpqc topology on *all* schemes — the
statement of Stacks 0AI2 — already implies the condition on the big fppf site of every base.
So the clause blocked by Stacks 0AHZ has to be discharged only once, on schemes, and not once
per base scheme.

*The condition holds for every formal scheme*, by
`AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints`, the full statement of Stacks 0AI2.
The functor of points of any formal scheme is therefore an honest object of
`AlgebraicGeometry.FormalSpace.FppfSheaf B S hS`, with no hypothesis assumed — which is the
first sentence of Stacks 0AIR.

## Main definitions

* `AlgebraicGeometry.FormalSpace.formalSchemeFppfSheafOfIso` and
  `AlgebraicGeometry.FormalSpace.formalSchemePointsFppfSheaf`: the functor of points of a formal
  scheme — isomorphic to a scheme, respectively arbitrary — as an object of the category in
  which formal algebraic spaces over `S` live.
* `AlgebraicGeometry.FormalSpace.formalSchemePointsFppfSheafFunctor`: that assignment as a
  functor of the formal scheme. It is defined on the whole category of formal schemes, the sheaf
  clause holding with no hypothesis; its full faithfulness is the embedding clause of
  Stacks 0AIR, proved in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparisonAtlas`.

## Main results

* `AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_of_isSheaf_fpqcTopology`: the
  fpqc sheaf condition on all schemes implies the fppf sheaf condition on the big fppf site of
  `S`.
* `AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_of_exists_isAmalgamation_scheme`:
  consequently the condition follows from the existence of amalgamations for fpqc coverings of
  schemes, which is exactly what the gluing clause of Stacks 0AI2 asserts.
* `AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_of_iso`: **Stacks 0AIR**, the
  sheaf clause, for a formal scheme isomorphic to a scheme.
* `AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`: **Stacks 0AIR**,
  the sheaf clause, for an arbitrary formal scheme.

## Implementation notes

The lift of the values is handled by `CategoryTheory.Presieve.isSheaf_of_nat_equiv` rather than
by a transport lemma of its own: `ULift.up` is a bijection commuting with the restriction maps,
which is all that lemma asks for. The restriction of the site is
`Stacks.Sites.isSheafFor_op_comp`, the single-sieve form of the transport of the sheaf condition
along a compatible-preserving functor, used exactly as it is for the structure presheaf of the
big fppf site.

The gluing clause of Stacks 0AI2, which the condition rests on, is proved in
`StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcDescent`; nothing below is
assumed.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIR](https://stacks.math.columbia.edu/tag/0AIR)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fppf sheaf condition on the functor of points of a formal scheme, over any base, follows
from the sheaf condition for the fpqc topology on the category of all schemes, which is the
statement of Stacks 0AI2.

A covering sieve of the big fppf site of `S` has fpqc covering image in the category of all
schemes, and `AlgebraicGeometry.BigFppfOver.toScheme` is compatible preserving, so the sheaf
condition restricts along it; the lift of the values is harmless because `ULift.up` is a
bijection commuting with the restriction maps. -/
theorem isFppfSheafFormalSchemePoints_of_isSheaf_fpqcTopology (X : FormalScheme.{u})
    (hX : Presieve.IsSheaf Scheme.fpqcTopology.{u} (formalSchemePoints X)) :
    IsFppfSheafFormalSchemePoints B S hS X := by
  rw [isFppfSheafFormalSchemePoints_iff]
  refine Presieve.isSheaf_of_nat_equiv
    (P₁ := (BigFppfOver.toScheme B S hS).op ⋙ formalSchemePoints X)
    (fun {_} => Equiv.ulift.symm) (fun _ _ _ _ => rfl) fun _ R hR =>
    Stacks.Sites.isSheafFor_op_comp (BigFppfOver.compatiblePreserving_toScheme B S hS)
      ⟨_, (isSheaf_iff_isSheaf_of_type _ _).2 hX⟩ R
      ((BigFppfOver.coverPreserving_toScheme B S hS).cover_preserve hR)

/-- The fppf sheaf condition on the functor of points of a formal scheme, over any base, follows
from the existence of an amalgamation for every compatible family of points over an fpqc
covering sieve of a scheme.

This is the precise form of what the gluing clause of Stacks 0AI2 still owes: it is a statement
about the category of all schemes alone, so discharging it once gives the condition carried as
a hypothesis in `StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSchemeComparison` for every
base scheme at once. -/
theorem isFppfSheafFormalSchemePoints_of_exists_isAmalgamation_scheme (X : FormalScheme.{u})
    (hglue : ∀ (T : Scheme.{u}) (R : Sieve T), R ∈ Scheme.fpqcTopology.{u} T →
      ∀ x : Presieve.FamilyOfElements (formalSchemePoints X) R.arrows,
        x.Compatible → ∃ t, x.IsAmalgamation t) :
    IsFppfSheafFormalSchemePoints B S hS X :=
  isFppfSheafFormalSchemePoints_of_isSheaf_fpqcTopology B S hS X
    (isSheaf_fpqcTopology_formalSchemePoints_of_exists_isAmalgamation X hglue)

/-- **Stacks 0AIR**, the sheaf clause, for a formal scheme isomorphic to a scheme: its functor
of points satisfies the fppf sheaf condition on the big fppf site of `S`, with no hypothesis
assumed.

The functor of points of a scheme seen as a formal scheme is the presheaf it represents and the
fpqc topology is subcanonical, which is
`AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_of_iso`. -/
@[stacks 0AIR "the functor of points is an fppf sheaf, for a formal scheme that is a scheme"]
theorem isFppfSheafFormalSchemePoints_of_iso {X : FormalScheme.{u}} {Z : Scheme.{u}}
    (e : X ≅ schemeToFormalScheme.obj Z) : IsFppfSheafFormalSchemePoints B S hS X :=
  isFppfSheafFormalSchemePoints_of_isSheaf_fpqcTopology B S hS X
    (isSheaf_fpqcTopology_formalSchemePoints_of_iso e)

/-- For a formal scheme isomorphic to a scheme, its functor of points as an object of
`AlgebraicGeometry.FormalSpace.FppfSheaf B S hS`, the category in which formal algebraic spaces
over `S` live. This is the object the comparison of Stacks 0AIR is about, available here with no
hypothesis assumed. -/
noncomputable def formalSchemeFppfSheafOfIso {X : FormalScheme.{u}} {Z : Scheme.{u}}
    (e : X ≅ schemeToFormalScheme.obj Z) : FppfSheaf B S hS :=
  formalSchemeFppfSheaf B S hS X (isFppfSheafFormalSchemePoints_of_iso B S hS e)

/-- The underlying presheaf of that fppf sheaf is the functor of points. -/
@[simp]
theorem formalSchemeFppfSheafOfIso_obj {X : FormalScheme.{u}} {Z : Scheme.{u}}
    (e : X ≅ schemeToFormalScheme.obj Z) :
    (formalSchemeFppfSheafOfIso B S hS e).obj = formalSchemeFppfPresheaf B S hS X :=
  rfl

/-- **Stacks 0AIR**, the sheaf clause, for an *arbitrary* formal scheme: the functor of points
of a formal scheme à la EGA satisfies the fppf sheaf condition on the big fppf site of `S`, with
no hypothesis assumed.

This is the first sentence of the source's remark, "by Lemma 87.2.2 the functor of points
`h_𝔛` associated to a formal scheme `𝔛` is a sheaf in the fppf topology". It is
`AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints`, the full statement of Stacks 0AI2,
read on the big fppf site of `S` by
`AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_of_isSheaf_fpqcTopology`. -/
@[stacks 0AIR "the functor of points of an arbitrary formal scheme is an fppf sheaf",
  stacks 0AI2 "the fpqc sheaf condition read on the big fppf site of a base scheme"]
theorem isFppfSheafFormalSchemePoints_formalScheme (X : FormalScheme.{u}) :
    IsFppfSheafFormalSchemePoints B S hS X :=
  isFppfSheafFormalSchemePoints_of_isSheaf_fpqcTopology B S hS X
    (isSheaf_fpqcTopology_formalSchemePoints X)

/-- **The object the comparison of Stacks 0AIR is about**, for an arbitrary formal scheme: its
functor of points as an object of `AlgebraicGeometry.FormalSpace.FppfSheaf B S hS`, the category
in which formal algebraic spaces over `S` live. No hypothesis is assumed. -/
noncomputable def formalSchemePointsFppfSheaf (X : FormalScheme.{u}) : FppfSheaf B S hS :=
  formalSchemeFppfSheaf B S hS X (isFppfSheafFormalSchemePoints_formalScheme B S hS X)

/-- The underlying presheaf of that fppf sheaf is the functor of points. -/
@[simp]
theorem formalSchemePointsFppfSheaf_obj (X : FormalScheme.{u}) :
    (formalSchemePointsFppfSheaf B S hS X).obj = formalSchemeFppfPresheaf B S hS X :=
  rfl

/-- **The assignment `𝔛 ↦ h_𝔛` of Stacks 0AIR**, as a functor from formal schemes à la EGA to
the category `AlgebraicGeometry.FormalSpace.FppfSheaf B S hS` in which formal algebraic spaces
over `S` live. No hypothesis is assumed: the sheaf condition on the functor of points holds for
every formal scheme by
`AlgebraicGeometry.FormalSpace.isFppfSheafFormalSchemePoints_formalScheme`, so the assignment is
defined on the whole category. -/
noncomputable def formalSchemePointsFppfSheafFunctor : FormalScheme.{u} ⥤ FppfSheaf B S hS where
  obj X := formalSchemePointsFppfSheaf B S hS X
  map f := ⟨(formalSchemeFppfPresheafFunctor B S hS).map f⟩
  map_id X := Sheaf.hom_ext ((formalSchemeFppfPresheafFunctor B S hS).map_id X)
  map_comp f g := Sheaf.hom_ext ((formalSchemeFppfPresheafFunctor B S hS).map_comp f g)

/-- The underlying morphism of presheaves of the morphism of fppf sheaves induced by a morphism
of formal schemes. -/
theorem hom_map_formalSchemePointsFppfSheafFunctor {X Y : FormalScheme.{u}} (f : X ⟶ Y) :
    ((formalSchemePointsFppfSheafFunctor B S hS).map f).hom
      = (formalSchemeFppfPresheafFunctor B S hS).map f := rfl

end AlgebraicGeometry.FormalSpace

end
