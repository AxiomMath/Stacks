module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# A big étale site contains the finite étale covers of what it contains

`AlgebraicGeometry.BigEtaleSite.Contains X` is the condition `X.size < B.cutoff` that puts a
scheme in the bounded category underlying a big étale site. It is not a closure condition, so it
has to be checked for each scheme a statement names. This file checks it for the source of a
finite étale morphism: a finite étale morphism is locally of finite type and quasi-compact, so
Stacks 000R (5) bounds the size of its source by the size of its target.

The use is Stacks 0DV6, which compares the dictionaries of Stacks 0DV5 over two schemes of one
big étale site. Reading it over a finite étale cover `T → S` needs a single big étale site
containing both, and `AlgebraicGeometry.BigEtaleSite.containing S` is one: by the result below it
contains every finite étale cover of `S` as well.

## Main results

* `AlgebraicGeometry.BigEtaleSite.contains_of_finiteEtale`: the source of a finite étale morphism
  into a contained scheme is contained.
* `AlgebraicGeometry.BigEtaleSite.contains_left_of_finiteEtaleOver`: the same for an object of
  `AlgebraicGeometry.FiniteEtaleOver`.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 0DV6](https://stacks.math.columbia.edu/tag/0DV6)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.BigEtaleSite

variable (B : BigEtaleSite.{u})

/-- **The source of a finite étale morphism into a scheme of a big étale site belongs to that big
étale site.** A finite étale morphism is quasi-compact and locally of finite type, so this is
Stacks 000R (5), `AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact`. -/
theorem contains_of_finiteEtale {T S : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ S)
    (hf : finiteEtale f) (hS : B.Contains S) : B.Contains T :=
  have : IsFinite f := hf.1
  have : Etale f := hf.2
  AlgebraicGeometry.Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact f hS

/-- **A finite étale cover of a scheme of a big étale site belongs to that big étale site.** -/
theorem contains_left_of_finiteEtaleOver {S : AlgebraicGeometry.Scheme.{u}} (T : FiniteEtaleOver S)
    (hS : B.Contains S) : B.Contains T.left :=
  B.contains_of_finiteEtale T.hom T.prop hS

/-- A finite étale cover of a scheme of a big étale site, as an object of that big étale site. -/
noncomputable def schemeOfFiniteEtaleOver {S : AlgebraicGeometry.Scheme.{u}} (T : FiniteEtaleOver S)
    (hS : B.Contains S) : B.Scheme :=
  ⟨T.left, B.contains_left_of_finiteEtaleOver T hS⟩

end AlgebraicGeometry.BigEtaleSite

end
