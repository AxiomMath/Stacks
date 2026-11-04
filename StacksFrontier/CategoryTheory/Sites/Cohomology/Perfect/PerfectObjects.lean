module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Perfect complexes on a ringed site

Let `(C, O)` be a ringed site. A complex `E` of `O`-modules is *perfect* when every object `U`
of `C` admits a covering `{V → U}` such that over each `V` there is a strictly perfect complex
`P` of `O|_V`-modules and a quasi-isomorphism `P ⟶ E|_V`. An object of `D(O)` is *perfect*
when it is represented by a perfect complex.

Unlike pseudo-coherence (Stacks 08FT), where the local models only approximate the complex
above a given degree, here the local models are required to compute the whole cohomology of
the restriction.

## Main definitions

* `AlgebraicGeometry.RingedSite.IsPerfectComplex`: perfectness of a complex of `O`-modules.
* `AlgebraicGeometry.RingedSite.IsPerfect`: perfectness of an object of `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.exists_coversTop_isStrictlyPerfect_of_isPerfectComplex`: the
  per-object local hypothesis produces a single family of objects covering the final object which
  carries the strictly perfect models. This is the form a statement checked locally consumes.

## Implementation notes

As for Stacks 08FT, a covering family `{V → U}` is a presieve on `U` whose generated sieve is
covering, strict perfectness is the `IsStrictlyPerfect` carrying Stacks 08FL, and restriction
of complexes is `AlgebraicGeometry.RingedSite.restrictComplex`.

The universes of the sections of the structure sheaf and of the sections of the modules are
independent parameters and both are kept free, exactly as in
`AlgebraicGeometry.RingedSite.IsPseudoCoherentComplexFrom`: the small étale ringed site of an
algebraic space over `Scheme.{u}` has its structure rings in `Type u`, so a ring universe fixed
at `Type` would not reach it.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
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

/-- **Stacks 08G5, perfect complexes.** A complex `E` of `O`-modules is *perfect* if every
object `U` of the site admits a covering `{V → U}` over each member of which there are a
strictly perfect complex `P` of `O|_V`-modules and a quasi-isomorphism `P ⟶ E|_V`. -/
@[stacks 08G5 "perfect complexes"]
noncomputable def IsPerfectComplex
    (E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    Prop :=
  ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
    ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
      ∃ P : CochainComplex
          (SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
          ∃ q : P ⟶ X.restrictComplex E V, QuasiIso q

omit [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})] in
/-- **The per-object local hypothesis of Stacks 08G5 produces a single family of objects
covering the final object on which the complex has a strictly perfect model.** Perfectness is
stated object by object, each object getting its own covering; a statement which is checked
locally, such as the invertibility of a morphism of `D(O)`, consumes instead one family of
objects covering the final object. This is the passage between the two.

The family is indexed by the pairs of an object and an arrow into it belonging to the chosen
covering presieve of that object, and its value there is the source of the arrow. That family
covers the final object for a direct reason: the chosen presieve of an object already consists
of arrows whose sources are members of the family, so the sieve it generates is contained in the
sieve of arrows factoring through a member; no pullback of sieves and no refinement is
needed. -/
theorem exists_coversTop_isStrictlyPerfect_of_isPerfectComplex
    (E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hE : X.IsPerfectComplex E) :
    ∃ (K : Type (max u v)) (V : K → X.C), X.J.CoversTop V ∧
      ∀ k, ∃ P : CochainComplex
          (SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V k))) ℤ,
        IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (V k)) P ∧
          ∃ q : P ⟶ X.restrictComplex E (V k), QuasiIso q := by
  classical
  choose S hS hP using hE
  refine ⟨Σ U : X.C, Σ V : X.C, { f : V ⟶ U // S U f }, fun k => k.2.1, ?_, ?_⟩
  · intro W
    refine X.J.superset_covering ?_ (hS W)
    rintro Z g ⟨V, a, f, hf, rfl⟩
    exact ⟨⟨W, V, f, hf⟩, ⟨a⟩⟩
  · intro k
    exact hP k.1 k.2.2.1 k.2.2.2

variable [HasSheafify X.J AddCommGrpCat.{m}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Stacks 08G5, perfect objects of the derived category.** An object of `D(O)` is *perfect*
if it is isomorphic to the image of a perfect complex. -/
@[stacks 08G5 "perfect derived-category objects"]
noncomputable def IsPerfect
    [HasDerivedCategory.{d} (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : DerivedCategory (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    Prop :=
  ∃ E : CochainComplex (SheafOfModules.{m} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
    X.IsPerfectComplex E ∧ Nonempty (DerivedCategory.Q.obj E ≅ K)

end AlgebraicGeometry.RingedSite

end
