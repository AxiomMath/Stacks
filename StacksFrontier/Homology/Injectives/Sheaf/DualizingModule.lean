module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyPresheafLocallyZero

/-!
# The dualizing sheaf of a ringed site

Let `(C, O)` be a ringed site. Section 19.8 of the source fixes an injective abelian sheaf `J`
admitting a monomorphism from the direct sum `⨁ j_{U!}O_U/I`, taken over all objects `U` of the
site and all submodules `I ⊆ j_{U!}O_U`, and dualizes `O`-modules against it.

This file constructs such a sheaf for an arbitrary family `X : C → SheafOfModules R` in place of
`U ↦ j_{U!}O_U`: the quotients `X U / I` form a family indexed by a small type, so their direct
sum exists, and abelian sheaves on a small site have enough injectives, so the underlying
abelian sheaf of that sum admits a monomorphism into an injective one.

## Main definitions

* `Stacks.Injectives.DualEvaluation.cyclicQuotient`: the quotient `X U / I`.
* `Stacks.Injectives.DualEvaluation.dualizingSheaf`: an injective abelian sheaf containing the
  direct sum of all the quotients.

## Main results

* `Stacks.Injectives.DualEvaluation.cyclicQuotientEmbedding`: each quotient `X U / I` embeds, as
  an abelian sheaf, in the dualizing sheaf.

## Implementation notes

The dualizing object is an abelian sheaf, not a module: that is the choice of the source, and it
is the one the exactness of dualization (Tag 01DR) is proved for in
`StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact`.

Smallness of the index type is the only point needing care: `Subobject (X U)` lies a universe
above the site, and is brought back down by well-poweredness of sheaves of modules.

## References

* [Stacks Project, Tag 01DQ](https://stacks.math.columbia.edu/tag/01DQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Injectives.DualEvaluation

universe u

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  (X : C → SheafOfModules.{u} R)

/-- The quotient `X U / I` of a member of the family by a submodule of it. -/
abbrev cyclicQuotient (p : Σ U : C, Subobject (X U)) : SheafOfModules.{u} R :=
  cokernel p.2.arrow

/-- The pairs of an object and a submodule of its member of the family form a small type:
sheaves of modules are well-powered, so each `Subobject (X U)` is small. -/
instance small_sigmaSubobject : Small.{u} (Σ U : C, Subobject (X U)) := by
  have : ∀ U : C, Small.{u} (Subobject (X U)) := fun U => inferInstance
  infer_instance

/-- The direct sum of all the quotients exists, the index type being small. -/
instance hasCoproduct_cyclicQuotient : HasCoproduct (cyclicQuotient R X) := by
  have := small_sigmaSubobject R X
  infer_instance

section

variable [HasSheafify J AddCommGrpCat.{u}]

-- Abelian sheaves on a small site have enough injectives, being a Grothendieck abelian
-- category: `Stacks.Cohomology.Locality.enoughInjectives_sheaf`, imported above.

/-- An injective abelian sheaf admitting a monomorphism from the direct sum of all the quotients
`X U / I`, as in Section 19.8 of the source. -/
def dualizingSheaf : Sheaf J AddCommGrpCat.{u} :=
  Injective.under ((SheafOfModules.toSheaf R).obj (∐ cyclicQuotient R X))

/-- The dualizing sheaf is injective, being an injective object chosen over the direct sum. -/
instance injective_dualizingSheaf : Injective (dualizingSheaf R X) :=
  Injective.injective_under _

/-- The monomorphism from the underlying abelian sheaf of the direct sum of all the quotients
`X U / I` into the dualizing sheaf. -/
def dualizingEmbedding :
    (SheafOfModules.toSheaf R).obj (∐ cyclicQuotient R X) ⟶ dualizingSheaf R X :=
  Injective.ι _

/-- The embedding of the direct sum into the dualizing sheaf is a monomorphism. -/
instance mono_dualizingEmbedding : Mono (dualizingEmbedding R X) :=
  Injective.ι_mono _

/-- Each quotient `X U / I` embeds, as an abelian sheaf, in the dualizing sheaf: compose the
inclusion of the summand with the embedding of the direct sum. -/
def cyclicQuotientEmbedding (p : Σ U : C, Subobject (X U)) :
    (SheafOfModules.toSheaf R).obj (cyclicQuotient R X p) ⟶ dualizingSheaf R X :=
  (SheafOfModules.toSheaf R).map (Sigma.ι (cyclicQuotient R X) p) ≫ dualizingEmbedding R X

/-- The embedding of a single quotient into the dualizing sheaf is a monomorphism, being a
split monomorphism onto its summand followed by the embedding of the direct sum. -/
instance mono_cyclicQuotientEmbedding (p : Σ U : C, Subobject (X U)) :
    Mono (cyclicQuotientEmbedding R X p) :=
  mono_comp ((SheafOfModules.toSheaf R).map (Sigma.ι (cyclicQuotient R X) p))
    (dualizingEmbedding R X)

end

end Stacks.Injectives.DualEvaluation

end
