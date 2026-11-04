module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherent complexes on a ringed site

Let `(C, O)` be a ringed site, let `E` be a complex of `O`-modules and fix `m : ℤ`. The complex
`E` is *`m`-pseudo-coherent* when every object `U` of `C` admits a covering `{V → U}` such that
over each `V` there is a strictly perfect complex `P` of `O|_V`-modules together with a map
`α : P ⟶ E|_V` which is an isomorphism on cohomology in every degree `> m` and an epimorphism
on cohomology in degree `m`. It is *pseudo-coherent* when it is `m`-pseudo-coherent for every
`m`. An object of `D(O)` is (`m`-)pseudo-coherent when it is represented by an
(`m`-)pseudo-coherent complex.

## Main definitions

* `AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom`: `m`-pseudo-coherence of a
  complex of `O`-modules, part (1) of the source definition.
* `AlgebraicGeometry.RingedSite.IsPseudoCoherentComplex`: pseudo-coherence of a complex of
  `O`-modules, part (2).
* `AlgebraicGeometry.RingedSite.IsPseudoCoherentFrom` and
  `AlgebraicGeometry.RingedSite.IsPseudoCoherent`: the two clauses of part (3), the
  corresponding properties of an object of `D(O)`.

## Implementation notes

A covering family `{V → U}` is represented by a presieve on `U` whose generated sieve is a
covering sieve, and the strictly perfect approximation is demanded on the arrows of that
presieve. Strict perfectness is `IsStrictlyPerfect`, the predicate carrying Stacks 08FL, taken
over the
restricted structure sheaf `O|_V`; restriction of complexes is the degreewise
`AlgebraicGeometry.RingedSite.restrictComplex`. No second notion of strict perfectness or of
restriction is introduced.

`IsStrictlyPerfect` carries the universe of the sections of the structure sheaf and that of
the sections of the modules as independent parameters, and this file keeps both free, as it
keeps free the universes of the objects and the morphisms of the site and of the derived
category. The small étale ringed site of an algebraic space over `Scheme.{u}` has its
structure rings in `Type u`, so a ring universe fixed at `Type` would not reach it.

The two derived-category clauses ask for a representative in the strong sense of an
isomorphism in `D(O)` with the image of a complex under the localisation functor, rather than
merely for a quasi-isomorphic complex.

The instances on the slices of the topology are hypothesised in `∀`-form over the objects of
the site, since the predicates range over all objects of `C`; the local instances below make
them available to instance search inside the statements.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w m d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{m}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{m}]
variable [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- **Stacks 08FT, part (1).** A complex `E` of `O`-modules is `m`-*pseudo-coherent* if every
object `U` of the site admits a covering `{V → U}` over each member of which there are a
strictly perfect complex `P` of `O|_V`-modules and a map `P ⟶ E|_V` inducing isomorphisms on
cohomology in every degree `> m` and an epimorphism on cohomology in degree `m`. -/
@[stacks 08FT "part (1)"]
noncomputable def IsPseudoCoherentComplexFrom
    (E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) : Prop :=
  ∀ U : X.C, ∃ S : Presieve U, (Sieve.generate S ∈ X.J U) ∧
    ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ P : CochainComplex
          (SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
        ∃ α : P ⟶ X.restrictComplex E V,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
          Epi (HomologicalComplex.homologyMap α m)

/-- **Stacks 08FT, part (2).** A complex of `O`-modules is *pseudo-coherent* if it is
`m`-pseudo-coherent for every integer `m`. -/
@[stacks 08FT "part (2)"]
noncomputable def IsPseudoCoherentComplex
    (E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Prop :=
  ∀ m : ℤ, X.IsPseudoCoherentComplexFrom E m

variable [HasSheafify X.J AddCommGrpCat.{m}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Stacks 08FT, part (3), first clause.** An object of `D(O)` is `m`-*pseudo-coherent* if
it is isomorphic to the image of an `m`-pseudo-coherent complex. -/
@[stacks 08FT "part (3), m-pseudo-coherent"]
noncomputable def IsPseudoCoherentFrom
    [HasDerivedCategory.{d} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (E : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (m : ℤ) : Prop :=
  ∃ K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
    X.IsPseudoCoherentComplexFrom K m ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

/-- **Stacks 08FT, part (3), second clause.** An object of `D(O)` is *pseudo-coherent* if it
is isomorphic to the image of a pseudo-coherent complex. -/
@[stacks 08FT "part (3), pseudo-coherent"]
noncomputable def IsPseudoCoherent
    [HasDerivedCategory.{d} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (E : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    Prop :=
  ∃ K : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
    X.IsPseudoCoherentComplex K ∧ Nonempty (DerivedCategory.Q.obj K ≅ E)

end AlgebraicGeometry.RingedSite

end
