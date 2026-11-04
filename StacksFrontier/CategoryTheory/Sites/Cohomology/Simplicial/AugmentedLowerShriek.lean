module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.SimplicialModulesAbelian
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek along an augmented simplicial sheaf of rings

Let `C` be a site, let `O` be a sheaf of rings on `C` and let `ε : A_• ⟶ O` be an augmentation of
a simplicial sheaf of rings on `C` by `O`, that is, a map from `A_•` to the constant simplicial
sheaf of rings `O`. Writing `π : Δ × C ⟶ C` for the projection, a simplicial module over the
constant simplicial sheaf of rings `O` is a module over `π^{-1}O`, and derived lower shriek
along `π` is defined on `D(A_•)` as the composite

`D(A_•) --(- ⊗^L_{A_•} O)--> D(π^{-1}O) --Lπ_!--> D(O)`.

Being a composite of exact functors of triangulated categories it is again one, which is the
assertion of the source.

## Main definitions

* `Stacks.SimplicialModules.constantRing`: a sheaf of rings read as a constant simplicial sheaf
  of rings.
* `Stacks.SimplicialModules.Augmentation`: an augmentation of a simplicial sheaf of rings, in the
  sense of Simplicial, Definition 018G, in the category of sheaves of rings.
* `Stacks.SimplicialModules.augmentedLowerShriek`: the functor `Lπ_! : D(A_•) ⟶ D(O)`.

## Main results

* `Stacks.SimplicialModules.augmentedLowerShriek_isTriangulated` and
  `Stacks.SimplicialModules.augmentedLowerShriek_commShift`: the functor is exact as a functor
  of triangulated categories.

## Implementation notes

Two inputs of the source are carried as explicit parameters, the library not yet having them.
The first is derived extension of scalars `- ⊗^L_{A_•} O` along the augmentation, which the
source introduces in the untagged prose preceding Lemma 09D2 and which needs the abelian
structure of the category of simplicial modules. The second is the functor
`Lπ_! : D(π^{-1}O) ⟶ D(O)` of Tag 09CY. The abelian structure and the choice of derived category
of each of the two categories of simplicial modules are assumed for the same reason.

**What `proj` actually waits on.** The construction of `Lπ_!` does not rest on parts (2) and (4)
of Tag 08PC, and it does not wait on Tag 0D6X.

*Parts (2) and (4) are not needed to construct `Lπ_!`.* They are the forgetful-square
comparisons `forget ∘ π_! = π_!^{Ab} ∘ forget` and its derived form, which the source uses to
*compute* with `Lπ_!`. Constructing it needs only part (1) on modules — which this library has,
`Stacks.Sites.FibredCategory.MorphismSituation.moduleDiagramInverseImage_isRightAdjoint` — and
the existence of a total left derived functor of `π_!`, which is part (3).

*Tag 0D6X is available.* It is formalized in general form, for an arbitrary continuous functor of
sites, as `Stacks.CechSite.injective_module_sheafCohomology_isZero_of_functor`, with Tag 0D6Y
beside it. So the real obstruction to `proj` is narrower: part (3) for modules is
reduced in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/DerivedAdjunction.lean` to the single
acyclicity statement of Tag 0794 at the class of direct sums of the `j_{U!} O_U`, and
`Stacks.Cohomology.DerivedLowerShriek.lowerShriekAcyclic_of_ext_vanishing` reduces that to the
object-level vanishing of 0D6X read as an `Ext` group. What is owed is the identification of
`Ext^n(j_{U!} O_U, π^* I)` with the cohomology of `π^{-1}I` over `U`, the covering-pullback
condition for `Prod.snd : Δ × C ⥤ C` in the inherited topology, and the transport of the derived
category across `Stacks.SimplicialModules.equivSheafOfModules`.

**`proj` now exists; a consumer should not carry it as a parameter.** Derived lower shriek on
modules is built, unconditionally and with both the instances this file asks of `proj`, in
`StacksFrontier/CategoryTheory/Sites/Cohomology/LowerShriek/AcyclicityUnconditional.lean`, and it
is instantiated at the projection `π : Δ × C ⥤ C` as
`Stacks.SimplicialModules.derivedProjectionLowerShriek` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/ProjectionDerivedLowerShriek.lean`. It
lives on `SheafOfModules (Stacks.SimplicialModules.projectionRing C J O)` rather than on
`SimplicialModule J (constantRing J O)`. The two categories are equivalent, and **either
spelling works**: `CategoryTheory.Functor.mapDerivedCategory` transports an exact functor to the
derived categories with the `CommShift ℤ` and `IsTriangulated` instances Mathlib supplies for
it, which is the route `AugmentationDerivedBaseChange.lean` takes to give `base` in both
spellings. The recommendation recorded with `derivedProjectionLowerShriek` is a *preference*,
that Stacks 09DH be stated against `SheafOfModules (projectionRing C J O)` because that is
where every instance is already supplied; it is not a constraint. The sharp edge on the other
side is one of instance *spelling*, not of mathematics and not of heartbeats: `Abelian` and
`HasDerivedCategory` are arguments of `DerivedCategory`, `⋙` typechecks across two definitionally
equal but differently spelled sheaves of rings while instance search — which unfolds only
reducibles — does not, and pinning every intermediate category to one spelling removes it
entirely. See that file for the detail. Nothing is lost either way: what this file contributes,
that the composite `base ⋙ proj` is exact, is proved for arbitrary parameters.

*The projectives route does not work here*, and is recorded so that it is not tried again: the
chaotic-site construction
`Stacks.ChaoticSite.derivedColimitWithCoefficients` runs Tag 0794 at the projective objects,
which is available there only because on the chaotic topology every presheaf is a sheaf, so that
`PresheafOfModules.enoughProjectives` applies. On `Δ × C` the topology inherited from `C` along
the second projection is not chaotic, a simplicial module is an honest sheaf of modules, and a
category of sheaves of modules on a nontrivial site has no enough projectives. Nor is `π_!`
exact: it is the colimit over `Δᵒᵖ`, whose higher left derived functors are the homotopy groups
of a simplicial object, which is the whole content of Tag 09D2.

What the source adds to the composition is the reading of the composite as lower shriek itself:
the `O`-module structure on `Lπ_!(K)` comes from the identification `Lπ_!(K) = Lπ_!(K ⊗^L_{A_•}
O)` of Tag 09D2, under the hypothesis that the augmentation induce a quasi-isomorphism
`s(A_•) ⟶ O`. That hypothesis is **not** assumed below: the composite functor and its exactness
do not depend on it, so the statements here are stronger than the source's. This is the reading the
chaotic-site case already takes, where `Stacks.ChaoticSite.derivedColimitWithCoefficients` is
built and shown exact for an arbitrary coefficient map. What the hypothesis buys is the
identification of the composite with lower shriek itself, which is Tag 09D2 and a separate
assertion.

## References

* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3)
* [Stacks Project, Tag 09D1](https://stacks.math.columbia.edu/tag/09D1), simplicial modules.
* [Stacks Project, Tag 09CY](https://stacks.math.columbia.edu/tag/09CY), the lower shriek of the
  projection of a fibred category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u r

namespace Stacks.SimplicialModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A sheaf of rings on `C`, read as a constant simplicial sheaf of rings. Its simplicial
modules are the modules over `π^{-1}O` on `Δ × C`. -/
abbrev constantRing (O : Sheaf J RingCat.{r}) : SimplicialObject (Sheaf J RingCat.{r}) :=
  (Functor.const SimplexCategoryᵒᵖ).obj O

/-- An augmentation of a simplicial sheaf of rings `A_•` by a sheaf of rings `O`: a map to the
constant simplicial sheaf of rings `O`. -/
abbrev Augmentation (A : SimplicialObject (Sheaf J RingCat.{r})) (O : Sheaf J RingCat.{r}) :=
  A ⟶ constantRing J O

variable {A : SimplicialObject (Sheaf J RingCat.{r})} {O : Sheaf J RingCat.{r}}

section

variable [Abelian (SimplicialModule.{w, v, u, r} J A)]
  [HasDerivedCategory (SimplicialModule.{w, v, u, r} J A)]
  [Abelian (SimplicialModule.{w, v, u, r} J (constantRing J O))]
  [HasDerivedCategory (SimplicialModule.{w, v, u, r} J (constantRing J O))]
  {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]

/-- **Stacks 09D3.** Derived lower shriek along an augmented simplicial sheaf of rings:
`Lπ_! : D(A_•) ⟶ D(O)`, the composite of derived extension of scalars along the augmentation
with derived lower shriek on modules over `π^{-1}O`. -/
@[stacks 09D3 "the functor Lπ_! : D(A_•) ⟶ D(O). Two inputs of the source are carried as \
explicit parameters, the library not yet having them: `base` is derived extension of scalars \
`- ⊗^L_{A_•} O`, introduced in the untagged prose before Lemma 09D2, and `proj` is the functor \
Lπ_! : D(π^{-1}O) ⟶ D(O) of Tag 09CY, which is Tag 08PC part (3) for modules and is reduced in \
this library to the acyclicity statement of Tag 0794 at the class of direct sums of the \
j_{U!} O_U; see the implementation notes for what that still owes"]
def augmentedLowerShriek (_ε : Augmentation J A O)
    (base : DerivedCategory (SimplicialModule.{w, v, u, r} J A) ⥤
      DerivedCategory (SimplicialModule.{w, v, u, r} J (constantRing J O)))
    (proj : DerivedCategory (SimplicialModule.{w, v, u, r} J (constantRing J O)) ⥤
      DerivedCategory D) :
    DerivedCategory (SimplicialModule.{w, v, u, r} J A) ⥤ DerivedCategory D :=
  base ⋙ proj

/-- **Stacks 09D3.** Derived lower shriek along an augmented simplicial sheaf of rings commutes
with the shift. -/
@[stacks 09D3 "the functor commutes with the shift"]
instance augmentedLowerShriek_commShift (ε : Augmentation J A O)
    (base : DerivedCategory (SimplicialModule.{w, v, u, r} J A) ⥤
      DerivedCategory (SimplicialModule.{w, v, u, r} J (constantRing J O)))
    (proj : DerivedCategory (SimplicialModule.{w, v, u, r} J (constantRing J O)) ⥤
      DerivedCategory D) [base.CommShift ℤ] [proj.CommShift ℤ] :
    (augmentedLowerShriek J ε base proj).CommShift ℤ :=
  inferInstanceAs ((base ⋙ proj).CommShift ℤ)

/-- **Stacks 09D3.** Derived lower shriek along an augmented simplicial sheaf of rings is an
exact functor of triangulated categories. -/
@[stacks 09D3 "the functor is exact"]
instance augmentedLowerShriek_isTriangulated (ε : Augmentation J A O)
    (base : DerivedCategory (SimplicialModule.{w, v, u, r} J A) ⥤
      DerivedCategory (SimplicialModule.{w, v, u, r} J (constantRing J O)))
    (proj : DerivedCategory (SimplicialModule.{w, v, u, r} J (constantRing J O)) ⥤
      DerivedCategory D) [base.CommShift ℤ] [proj.CommShift ℤ]
    [base.IsTriangulated] [proj.IsTriangulated] :
    (augmentedLowerShriek J ε base proj).IsTriangulated :=
  inferInstanceAs ((base ⋙ proj).IsTriangulated)

end

/-! ### The functor at the target the source names -/

section DerivedTarget

attribute [local instance] abelian HasDerivedCategory.standard

/-- **Stacks 09D3.** Derived lower shriek along an augmented simplicial sheaf of rings,
`Lπ_! : D(A_•) ⟶ D(O)` with `D(O)` the derived category of the sheaves of `O`-modules on `C`,
which is the `D(O)` of the source.

Nothing is assumed about either category of simplicial modules: the abelian structure is
`Stacks.SimplicialModules.abelian` and the derived category is `HasDerivedCategory.standard`,
both seated as local instances. That abelian structure is supplied at sections universe
`max u v r w`, which is why the module sections are taken there. -/
@[stacks 09D3 "the functor Lπ_! : D(A_•) ⟶ D(O), at the target D(O) the source names and with \
the abelian structure and the derived category of both categories of simplicial modules \
discharged rather than assumed. Two inputs of the source are carried as explicit parameters, \
the library not yet having them: `base` is derived extension of scalars `- ⊗^L_{A_•} O`, \
introduced in the untagged prose before Lemma 09D2, and `proj` is the functor \
Lπ_! : D(π^{-1}O) ⟶ D(O) of Tag 09CY, whose underived half is \
`Stacks.SimplicialModules.moduleLowerShriek` and whose total left derived functor is part (3) \
of Tag 08PC, open here"]
def augmentedLowerShriek_derivedTarget (_ε : Augmentation J A O)
    (base : DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J A) ⥤
      DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J (constantRing J O)))
    (proj : DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J (constantRing J O)) ⥤
      DerivedCategory (SheafOfModules.{max u v r w} O)) :
    DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J A) ⥤
      DerivedCategory (SheafOfModules.{max u v r w} O) :=
  base ⋙ proj

/-- **Stacks 09D3.** Derived lower shriek along an augmented simplicial sheaf of rings commutes
with the shift, at the target `D(O)`. -/
@[stacks 09D3 "the functor commutes with the shift, at the target D(O) the source names"]
instance augmentedLowerShriek_derivedTarget_commShift (ε : Augmentation J A O)
    (base : DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J A) ⥤
      DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J (constantRing J O)))
    (proj : DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J (constantRing J O)) ⥤
      DerivedCategory (SheafOfModules.{max u v r w} O))
    [base.CommShift ℤ] [proj.CommShift ℤ] :
    (augmentedLowerShriek_derivedTarget.{w} J ε base proj).CommShift ℤ :=
  inferInstanceAs ((base ⋙ proj).CommShift ℤ)

/-- **Stacks 09D3.** Derived lower shriek along an augmented simplicial sheaf of rings is an
exact functor of triangulated categories, at the target `D(O)`. -/
@[stacks 09D3 "the functor is exact, at the target D(O) the source names"]
instance augmentedLowerShriek_derivedTarget_isTriangulated (ε : Augmentation J A O)
    (base : DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J A) ⥤
      DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J (constantRing J O)))
    (proj : DerivedCategory (SimplicialModule.{max u v r w, v, u, r} J (constantRing J O)) ⥤
      DerivedCategory (SheafOfModules.{max u v r w} O))
    [base.CommShift ℤ] [proj.CommShift ℤ]
    [base.IsTriangulated] [proj.IsTriangulated] :
    (augmentedLowerShriek_derivedTarget.{w} J ε base proj).IsTriangulated :=
  inferInstanceAs ((base ⋙ proj).IsTriangulated)

end DerivedTarget

end Stacks.SimplicialModules

end
