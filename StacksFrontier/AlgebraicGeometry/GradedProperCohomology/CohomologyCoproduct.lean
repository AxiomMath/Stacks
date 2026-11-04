module

public import Mathlib.Algebra.Category.ModuleCat.Products
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsHypotheses
public import StacksFrontier.Homology.DerivedCategory.ZeroDifferentialCoproduct

/-!
# Cohomology of a `ℤ`-indexed direct sum, and the base ring it is a module over

Let `X` be a quasi-compact quasi-separated scheme and `N : ℤ → X.Modules` a family of
`𝒪_X`-modules.  Cohomology commutes with the direct sum:

`H^p(X, ∐ₙ Nₙ) ≅ ⨁ₙ H^p(X, Nₙ)`.

This is the commutation [Stacks, Tag 0897] part (1) needs, at the `ℤ`-indexed coproduct and in
the `DirectSum` spelling in which `Stacks.AlgebraicGeometry.GradedProperCohomology`
`.gradedCohomologySum` is written.

It is then combined with [Stacks, Tag 089W]: if `π : X' ⟶ X` is affine and `G` is a
quasi-coherent `𝒪_{X'}`-module whose direct image is `∐ₙ Nₙ`, then

`H^p(X', G) ≅ ⨁ₙ H^p(X, Nₙ)`

as `Γ(X, ⊤)`-modules, hence as abelian groups.  For a ring `B` and a morphism `g : X' ⟶ Spec B`
the left-hand side is a `B`-module, and the comparison carries that action — and with it
finiteness over `B` — to `⨁ₙ H^p(X, Nₙ)`.

## Main definitions

* `coprodCohomologyModule`: the `B`-module structure on `⨁ₙ H^p(X, Nₙ)` carried across the
  comparison from `H^p(X', G)`.

## Main results

* `preservesColimitsOfShape_int_rightDerived_moduleGlobalSections`: cohomology of a
  quasi-compact quasi-separated scheme preserves `ℤ`-indexed coproducts.
* `cohomologyCoprodIso`: `H^p(X, ∐ₙ Nₙ) ≅ ⨁ₙ H^p(X, Nₙ)`.
* `cohomologyPushforwardCoprodAddEquiv`: `H^p(X', G) ≃+ ⨁ₙ H^p(X, Nₙ)` for `π` affine with
  `π_* G ≅ ∐ₙ Nₙ`.
* `moduleFinite_coprodCohomology`: `⨁ₙ H^p(X, Nₙ)` is a finite `B`-module as soon as
  `H^p(X', G)` is.

## Implementation notes

The `ℤ`-indexed coproduct preservation is a universe specialization and nothing more: the
qcqs statement for an arbitrary index type in the scheme's own universe is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections`, which rests on
[Stacks, Tag 01FF].  `ℤ` lives in `Type 0`, so the statement is read at `ULift.{u} ℤ` and
transported along `Discrete (ULift.{u} ℤ) ≌ Discrete ℤ` by
`CategoryTheory.Limits.preservesColimitsOfShape_discrete_shrink`.

`coprodCohomologyModule` transports the action rather than building the intrinsic one: the two
sides are compared only as `Γ(X, ⊤)`-modules, because [Stacks, Tag 089W] restricts scalars
along `π^♯` while the `B`-action on `H^p(X', G)` is restriction along `g^♯`, and the comparison
is `B`-linear for the transported structure by construction.  A consumer holding a different
`B`-action together with a `B`-linear comparison obtains the same finiteness from
`Module.Finite.equiv`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.AffineBase (moduleGlobalSections)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GradedProperCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### `ℤ`-indexed coproducts -/

/-- **Cohomology of a quasi-compact quasi-separated scheme commutes with `ℤ`-indexed direct
sums.** This is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections`, whose index type ranges
over the scheme's own universe, read at `ULift.{u} ℤ` and shrunk along the equivalence
`Discrete (ULift.{u} ℤ) ≌ Discrete ℤ`. -/
public theorem preservesColimitsOfShape_int_rightDerived_moduleGlobalSections (X : Scheme.{u})
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)] (q : ℕ) :
    PreservesColimitsOfShape (Discrete ℤ) ((moduleGlobalSections X).rightDerived q) :=
  let := preservesColimitsOfShape_discrete_rightDerived_moduleGlobalSections X q (ULift.{u} ℤ)
  CategoryTheory.Limits.preservesColimitsOfShape_discrete_shrink _ ℤ

/-- **`H^p(X, ∐ₙ Nₙ) ≅ ⨁ₙ H^p(X, Nₙ)` for a `ℤ`-indexed family of `𝒪_X`-modules on a
quasi-compact quasi-separated scheme.** The right-hand side is spelled as a `DirectSum`, which
is how `gradedCohomologySum` writes the graded cohomology of [Stacks, Tag 0897]. -/
public def cohomologyCoprodIso (X : Scheme.{u}) [CompactSpace (X : Type u)]
    [QuasiSeparatedSpace (X : Type u)] (N : ℤ → X.Modules) (p : ℕ) :
    cohomologyOf X p (∐ N) ≅
      ModuleCat.of Γ(X, ⊤) (DirectSum ℤ fun n => ↥(cohomologyOf X p (N n))) :=
  letI := preservesColimitsOfShape_int_rightDerived_moduleGlobalSections X p
  PreservesCoproduct.iso ((moduleGlobalSections X).rightDerived p) N ≪≫
    ModuleCat.coprodIsoDirectSum _

/-! ### The comparison across an affine morphism -/

section Pushforward

variable {X' X : Scheme.{u}} (π : X' ⟶ X) [IsAffineHom π]
  [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
  (N : ℤ → X.Modules) (G : X'.Modules) [G.IsQuasicoherent] (p : ℕ)

/-- **`H^p(X', G) ≅ ⨁ₙ H^p(X, Nₙ)` as `Γ(X, ⊤)`-modules**, for an affine `π : X' ⟶ X` and a
quasi-coherent `G` whose direct image along `π` is `∐ₙ Nₙ`.

[Stacks, Tag 089W] identifies `H^p(X', G)`, its scalars restricted along `π^♯`, with
`H^p(X, π_* G)`; the hypothesis `e` rewrites the argument as the coproduct, and
`cohomologyCoprodIso` splits the coproduct off. -/
public def cohomologyPushforwardCoprodIso
    (e : (Scheme.Modules.pushforward π).obj G ≅ ∐ N) :
    (ModuleCat.restrictScalars π.appTop.hom).obj (cohomologyOf X' p G) ≅
      ModuleCat.of Γ(X, ⊤) (DirectSum ℤ fun n => ↥(cohomologyOf X p (N n))) :=
  Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward π G p ≪≫
    ((moduleGlobalSections X).rightDerived p).mapIso e ≪≫ cohomologyCoprodIso X N p

/-- `cohomologyPushforwardCoprodIso` read on the underlying abelian groups. Restriction of
scalars does not change the underlying group, so this is an isomorphism of the cohomology
upstairs with the direct sum downstairs. -/
public def cohomologyPushforwardCoprodAddEquiv
    (e : (Scheme.Modules.pushforward π).obj G ≅ ∐ N) :
    ↥(cohomologyOf X' p G) ≃+ DirectSum ℤ fun n => ↥(cohomologyOf X p (N n)) :=
  (cohomologyPushforwardCoprodIso π N G p e).toLinearEquiv.toAddEquiv

variable {B : Type u} [CommRing B] (g : X' ⟶ Spec (.of B))

/-- **The `B`-action on `⨁ₙ H^p(X, Nₙ)` carried across the comparison.** For a morphism
`g : X' ⟶ Spec B` the cohomology `H^p(X', G)` is a `B`-module by restriction of scalars along
`g^♯`, and `cohomologyPushforwardCoprodAddEquiv` is an isomorphism of abelian groups, so the
action transports. The comparison is `B`-linear for this structure by construction. -/
@[instance_reducible]
public def coprodCohomologyModule (e : (Scheme.Modules.pushforward π).obj G ≅ ∐ N) :
    Module B (DirectSum ℤ fun n => ↥(cohomologyOf X p (N n))) :=
  letI : Module B ↥(cohomologyOf X' p G) :=
    inferInstanceAs (Module B
      ↥((ModuleCat.restrictScalars (specAlgebraRingHom B g)).obj (cohomologyOf X' p G)))
  letI φ : ↥(cohomologyOf X' p G) ≃+ DirectSum ℤ fun n => ↥(cohomologyOf X p (N n)) :=
    cohomologyPushforwardCoprodAddEquiv π N G p e
  letI : SMul B (DirectSum ℤ fun n => ↥(cohomologyOf X p (N n))) :=
    ⟨fun b x => φ (b • φ.symm x)⟩
  Function.Injective.module B φ.symm.toAddMonoidHom φ.symm.injective fun c x =>
    φ.symm_apply_apply (c • φ.symm x)

/-- **`⨁ₙ H^p(X, Nₙ)` is a finite `B`-module as soon as `H^p(X', G)` is**, for the action of
`coprodCohomologyModule`. The comparison is a `B`-linear surjection from a finite module. -/
public theorem moduleFinite_coprodCohomology
    (e : (Scheme.Modules.pushforward π).obj G ≅ ∐ N)
    (hfin : Module.Finite B ↥((ModuleCat.restrictScalars (specAlgebraRingHom B g)).obj
      (cohomologyOf X' p G))) :
    @Module.Finite B (DirectSum ℤ fun n => ↥(cohomologyOf X p (N n))) _ _
      (coprodCohomologyModule π N G p g e) := by
  let : Module B ↥(cohomologyOf X' p G) :=
    inferInstanceAs (Module B
      ↥((ModuleCat.restrictScalars (specAlgebraRingHom B g)).obj (cohomologyOf X' p G)))
  have : Module.Finite B ↥(cohomologyOf X' p G) := hfin
  let := coprodCohomologyModule π N G p g e
  let φ := cohomologyPushforwardCoprodAddEquiv π N G p e
  exact Module.Finite.of_surjective
    ({ toFun := φ, map_add' := φ.map_add,
       map_smul' := fun c y => congrArg φ (congrArg (c • ·) (φ.symm_apply_apply y).symm) } :
      _ →ₗ[B] _) φ.surjective

end Pushforward

end Stacks.AlgebraicGeometry.GradedProperCohomology

end
