module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.CategoryTheory.Limits.ColimitAlongRightAdjointOfInvertedUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.SingletonCoveringReflection
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of an object, and its computation from the one-member coverings

Let `J` be a Grothendieck topology on a category `C` with finite limits, let `U` be an object,
and let `ℱ` be an additive presheaf on `C`. For each covering `𝒰` of `U` — a family of morphisms
with target `U` generating a covering sieve — Stacks 03AM gives the Čech complex and the Čech
cohomology groups `Ȟⁿ(𝒰, ℱ)`, and Stacks 03F4 gives the map induced by a refinement. Those maps
are functorial (`Stacks.CechSite.cechComplexMap_id`, `Stacks.CechSite.cechComplexMap_comp`), so
the Čech cohomology groups assemble into a diagram on the opposite of the category of coverings
of `U`, and **Čech cohomology of the object `U`** is its colimit

`Ȟⁿ(U, ℱ) = colim_{𝒰} Ȟⁿ(𝒰, ℱ)`.

Stacks 03P0 observes that the one-member coverings `{V ⟶ U}` are *not* an initial subcategory of
all coverings of `U`, so this colimit is not a colimit over a cofinal subcategory of one-member
coverings — and asserts nonetheless that it can still be computed from the one-member coverings,
"it only works for sheaves". This file proves that assertion. The mechanism is not cofinality
but the reflection of `Stacks.CechSite.coproductCoveringAdjunction`: the one-member coverings are
a *reflective* subcategory, the reflector sending `𝒰 = {Uᵢ ⟶ U}` to `{∐ Uᵢ ⟶ U}`, and a colimit
over a category is computed on a reflective subcategory as soon as the diagram inverts the unit
of the reflection. The sheaf hypothesis the source flags is exactly that unit-inversion: the
refinement `𝒰 ⟶ {∐ Uᵢ ⟶ U}` induces an isomorphism of Čech complexes precisely when `ℱ` turns
the coproduct `∐ Uᵢ` and its iterated fibre powers into products, which is Stacks 03OZ (3).

## Main definitions

* `Stacks.CechSite.cechComplexCoveringFunctor`: the Čech complex of a presheaf, as a functor of
  the covering.
* `Stacks.CechSite.cechCohomologyCoveringFunctor`: the Čech cohomology groups in a fixed degree,
  as a functor of the covering; this is the diagram whose colimit defines `Ȟⁿ(U, ℱ)`.
* `Stacks.CechSite.cechCohomologyOfObject`: `Ȟⁿ(U, ℱ)`, the colimit of that diagram.

## Main results

* `Stacks.CechSite.isIso_cechCohomologyCoveringFunctor_map_unit`: on a category with universal
  coproducts, a presheaf turning coproducts into products inverts the unit of the reflection.
* `Stacks.CechSite.isColimitWhiskerSingletonCovering`: the universal cocone on the Čech
  cohomology groups of all coverings of `U`, restricted to the one-member coverings, is still a
  colimit cocone — so `Ȟⁿ(U, ℱ)` is computed from the one-member coverings alone. Its
  isomorphism form is `Stacks.CechSite.cechCohomologyOfObjectIsoColimitSingleton`, pinned down
  by `Stacks.CechSite.ι_cechCohomologyOfObjectIsoColimitSingleton`.
* For abelian-group-valued presheaves the colimit exists once the coefficient universe is large
  enough to contain the category of coverings: instance search finds it, from Mathlib's colimits
  in `AddCommGrpCat`.

## Implementation notes

**Size.** The objects of `Stacks.CechSite.Covering.{w} J U` carry their index type `I₀ : Type w`
as a field, so that type lives in `Type (max (w + 1) u v)` and the category of coverings is
*large*: it is not `Category.{v, u}`-small for any pair of universes of `C`. Mathlib's
`CategoryTheory.Precoverage.ZeroHypercover.Small` does not help, being about the index type of a
single covering rather than about the collection of coverings. The resolution taken here is to
leave the coefficient category `A` abstract, with the colimit required as a hypothesis; for
abelian groups instance search supplies the colimit once the coefficient universe is
raised to `max (w + 1) u v` — `AddCommGrpCat.{t}` has colimits of shape `K` exactly when the
objects of `K` are `t`-small, and smallness of homs is irrelevant. Raising the coefficient
universe is preferable to re-indexing the coverings by a small type: the deduplication
`CategoryTheory.PreZeroHypercover.shrink` is not functorial in refinements, and cutting the
coverings down to a small skeleton would change the category whose colimit the source's
definition names.

No filteredness of the category of coverings is used or needed: the colimit is an ordinary
colimit over a (possibly large) index category, and the reduction to the one-member coverings
goes through finality of the reflector's opposite, not through a cofinality or filteredness
argument.

## References

* [Stacks Project, Tag 03P0](https://stacks.math.columbia.edu/tag/03P0)
* [Stacks Project, Tag 03OZ](https://stacks.math.columbia.edu/tag/03OZ)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
-/

@[expose] public noncomputable section

universe w v v' u u'

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.CechSite

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] (J : GrothendieckTopology C) (U : C)
  {A : Type u'} [Category.{v'} A]

section Diagram

variable [Preadditive A] [HasProducts.{w} A]

/-- **The Čech complex as a functor of the covering.** A refinement of coverings of `U` acts on
Čech complexes in the opposite direction, by the map of Stacks 03F4; this is functorial by
`Stacks.CechSite.cechComplexMap_id` and `Stacks.CechSite.cechComplexMap_comp`. -/
def cechComplexCoveringFunctor (F : Cᵒᵖ ⥤ A) :
    (Covering.{w} J U)ᵒᵖ ⥤ CochainComplex A ℕ where
  obj X := cechComplex X.unop.toPreZeroHypercover F
  map {X Y} ψ := cechComplexMap Y.unop.toPreZeroHypercover X.unop.toPreZeroHypercover
    ((PreZeroHypercover.homOverIdEquivHom _ _).symm ψ.unop) F
  map_id X := cechComplexMap_id X.unop.toPreZeroHypercover F
  map_comp {X Y Z} ψ₁ ψ₂ :=
    (cechComplexMap_comp Z.unop.toPreZeroHypercover Y.unop.toPreZeroHypercover
      X.unop.toPreZeroHypercover
      ((PreZeroHypercover.homOverIdEquivHom _ _).symm ψ₂.unop)
      ((PreZeroHypercover.homOverIdEquivHom _ _).symm ψ₁.unop)
      (Category.comp_id (𝟙 U)) F).symm

/-- The Čech complex functor sends a covering `X` to the Čech complex of `F` with respect to `X`.
-/
@[simp]
theorem cechComplexCoveringFunctor_obj (F : Cᵒᵖ ⥤ A) (X : (Covering.{w} J U)ᵒᵖ) :
    (cechComplexCoveringFunctor.{w} J U F).obj X =
      cechComplex X.unop.toPreZeroHypercover F :=
  rfl

/-- The Čech complex functor sends a refinement `ψ` to the induced map of Čech complexes
`Stacks.CechSite.cechComplexMap`. -/
theorem cechComplexCoveringFunctor_map (F : Cᵒᵖ ⥤ A) {X Y : (Covering.{w} J U)ᵒᵖ} (ψ : X ⟶ Y) :
    (cechComplexCoveringFunctor.{w} J U F).map ψ =
      cechComplexMap Y.unop.toPreZeroHypercover X.unop.toPreZeroHypercover
        ((PreZeroHypercover.homOverIdEquivHom _ _).symm ψ.unop) F :=
  rfl

end Diagram

section Cohomology

variable [Abelian A] [HasProducts.{w} A]

/-- **Stacks 03AM and 03F4.** The degree-`n` Čech cohomology groups, as a functor of the
covering. This is the diagram whose colimit the source's definition of `Ȟⁿ(U, ℱ)` names. -/
def cechCohomologyCoveringFunctor (F : Cᵒᵖ ⥤ A) (n : ℕ) : (Covering.{w} J U)ᵒᵖ ⥤ A :=
  cechComplexCoveringFunctor.{w} J U F ⋙
    HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n

/-- The degree-`n` Čech cohomology functor sends a covering `X` to the degree-`n` Čech
cohomology of `F` with respect to `X`. -/
@[simp]
theorem cechCohomologyCoveringFunctor_obj (F : Cᵒᵖ ⥤ A) (n : ℕ) (X : (Covering.{w} J U)ᵒᵖ) :
    (cechCohomologyCoveringFunctor.{w} J U F n).obj X =
      cechCohomology X.unop.toPreZeroHypercover F n :=
  rfl

/-- **Stacks 03P0: Čech cohomology of an object.** The colimit, over the opposite of the category
of all coverings of `U`, of the Čech cohomology groups of `ℱ` with respect to each covering. -/
@[stacks 03P0 "`Ȟⁿ(U, ℱ)`, defined as the colimit over the opposite of the category of coverings
  `𝒰` of `U` of the Čech cohomology groups of `ℱ` with respect to `𝒰`"]
def cechCohomologyOfObject (F : Cᵒᵖ ⥤ A) (n : ℕ)
    [HasColimit (cechCohomologyCoveringFunctor.{w} J U F n)] : A :=
  colimit (cechCohomologyCoveringFunctor.{w} J U F n)

end Cohomology

section Reflection

variable [Abelian A] [HasProducts.{w} A] [HasCoproducts.{w} C]

omit [Abelian A] in
/-- The map of Čech complexes attached to the unit of the reflection of all coverings onto the
one-member ones is the comparison of Stacks 03FI (2) for the covering by the coproduct of the
members. -/
theorem cechComplexCoveringFunctor_map_unit [Preadditive A] (F : Cᵒᵖ ⥤ A)
    (E : Covering.{w} J U) :
    (cechComplexCoveringFunctor.{w} J U F).map
        ((coproductCoveringAdjunction.{w} J U).unit.app E).op =
      cechComplexMap E.toPreZeroHypercover
        (PreZeroHypercover.singleton.{w} (Sigma.desc E.f))
        (coproductRefinement E.toPreZeroHypercover) F := by
  rw [cechComplexCoveringFunctor_map, coproductCoveringAdjunction_unit_app]
  rfl

/-- **The sheaf hypothesis of Stacks 03P0, in the form it is used.** On a category whose
`w`-indexed coproducts are universal, a presheaf turning `w`-indexed coproducts into products
inverts the unit of the reflection of all coverings onto the one-member ones. This is the
infinitary form of Stacks 03OZ (3); it is a genuine hypothesis on `ℱ`, and is what the source
means by "it only works for sheaves". -/
theorem isIso_cechCohomologyCoveringFunctor_map_unit
    (huniv : ∀ {I : Type w} {D : Discrete I ⥤ C} {d : Cocone D},
      IsColimit d → IsUniversalColimit d)
    (F : Cᵒᵖ ⥤ A) [∀ I : Type w, PreservesLimitsOfShape (Discrete I) F] (n : ℕ)
    (E : Covering.{w} J U) :
    IsIso ((cechCohomologyCoveringFunctor.{w} J U F n).map
      ((coproductCoveringAdjunction.{w} J U).unit.app E).op) := by
  have h : IsIso ((cechComplexCoveringFunctor.{w} J U F).map
      ((coproductCoveringAdjunction.{w} J U).unit.app E).op) := by
    rw [cechComplexCoveringFunctor_map_unit]
    exact isIso_cechComplexMap_of_preservesProducts huniv E.toPreZeroHypercover F
  exact (inferInstance :
    IsIso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n).map
      ((cechComplexCoveringFunctor.{w} J U F).map
        ((coproductCoveringAdjunction.{w} J U).unit.app E).op)))

/-- **Stacks 03P0, the assertion the source leaves unformulated: Čech cohomology of a sheaf is
computed from the one-member coverings.** For an additive presheaf `ℱ` turning `w`-indexed
coproducts into products, on a category whose `w`-indexed coproducts are universal, the cocone
on the diagram of Čech cohomology groups restricted to the opposite of the full subcategory of
*one-member* coverings `{V ⟶ U}`, obtained by restricting the universal cocone on all coverings,
is still a colimit cocone. That is: `Ȟⁿ(U, ℱ)` is the colimit over the one-member coverings
alone — even though, as the standard Zariski covering of `Spec ℤ` by the basic opens of `2` and
of `3` witnesses, those coverings are not an initial subcategory of all coverings of `U`.

The hypotheses are the source's own. `huniv` is the infinitary extensivity of the site, the
disjointness of the coproducts that the proof of Stacks 03OZ invokes; and
`PreservesLimitsOfShape (Discrete I) ℱ` is the sheaf condition for the covering of a coproduct by
its summands, the equality Stacks 03OZ (3) rests on, which the paragraph before the remark
observes to be "false for a general presheaf". Together they are what the remark means by "it
only works for sheaves".

Because the cocone whose legs are tested is the universal cocone on *all* coverings, the
statement contains its own canonicity: the comparison is the restriction of the identity. -/
@[stacks 03P0 "Čech cohomology `Ȟⁿ(U, ℱ)`, the colimit over all coverings of `U`, can still be
  computed in terms of the coverings `{V ⟶ U}`: the universal cocone restricted to the one-member
  coverings is again a colimit cocone, for a coefficient presheaf turning arbitrary coproducts
  into products, which is the source's \"it only works for sheaves\""]
def isColimitWhiskerSingletonCovering
    (huniv : ∀ {I : Type w} {D : Discrete I ⥤ C} {d : Cocone D},
      IsColimit d → IsUniversalColimit d)
    (F : Cᵒᵖ ⥤ A) [∀ I : Type w, PreservesLimitsOfShape (Discrete I) F] (n : ℕ)
    [HasColimit (cechCohomologyCoveringFunctor.{w} J U F n)] :
    IsColimit ((colimit.cocone (cechCohomologyCoveringFunctor.{w} J U F n)).whisker
      (singletonCoveringInclusion.{w} J U).op) :=
  isColimitWhiskerOfInvertsUnit (coproductCoveringAdjunction.{w} J U) _
    (colimit.isColimit (cechCohomologyCoveringFunctor.{w} J U F n))
    (fun E ↦ isIso_cechCohomologyCoveringFunctor_map_unit J U huniv F n E)

/-- The colimit over the one-member coverings of `U` exists whenever the colimit over all
coverings does: it is computed by the same cocone. -/
theorem hasColimit_whisker_singletonCoveringInclusion
    (huniv : ∀ {I : Type w} {D : Discrete I ⥤ C} {d : Cocone D},
      IsColimit d → IsUniversalColimit d)
    (F : Cᵒᵖ ⥤ A) [∀ I : Type w, PreservesLimitsOfShape (Discrete I) F] (n : ℕ)
    [HasColimit (cechCohomologyCoveringFunctor.{w} J U F n)] :
    HasColimit ((singletonCoveringInclusion.{w} J U).op ⋙
      cechCohomologyCoveringFunctor.{w} J U F n) :=
  hasColimit_whisker_of_invertsUnit (coproductCoveringAdjunction.{w} J U)
    (fun E ↦ isIso_cechCohomologyCoveringFunctor_map_unit J U huniv F n E)

/-- **Stacks 03P0.** The isomorphism form of
`Stacks.CechSite.isColimitWhiskerSingletonCovering`: the colimit of the Čech cohomology groups
over the one-member coverings `{V ⟶ U}` alone is `Ȟⁿ(U, ℱ)`. -/
def cechCohomologyOfObjectIsoColimitSingleton
    (huniv : ∀ {I : Type w} {D : Discrete I ⥤ C} {d : Cocone D},
      IsColimit d → IsUniversalColimit d)
    (F : Cᵒᵖ ⥤ A) [∀ I : Type w, PreservesLimitsOfShape (Discrete I) F] (n : ℕ)
    [HasColimit (cechCohomologyCoveringFunctor.{w} J U F n)]
    [HasColimit ((singletonCoveringInclusion.{w} J U).op ⋙
      cechCohomologyCoveringFunctor.{w} J U F n)] :
    colimit ((singletonCoveringInclusion.{w} J U).op ⋙
        cechCohomologyCoveringFunctor.{w} J U F n) ≅
      cechCohomologyOfObject.{w} J U F n :=
  colimitIsoOfInvertsUnit (coproductCoveringAdjunction.{w} J U)
    (fun E ↦ isIso_cechCohomologyCoveringFunctor_map_unit J U huniv F n E)

/-- **Stacks 03P0.** The comparison of
`Stacks.CechSite.cechCohomologyOfObjectIsoColimitSingleton` is the canonical one: on each
one-member covering `{V ⟶ U}` it is the leg, at that covering, of the colimit over all
coverings. -/
@[stacks 03P0 "the computation of `Ȟⁿ(U, ℱ)` from the coverings `{V ⟶ U}` is the canonical
  comparison: it restricts on each one-member covering to the leg of the colimit over all
  coverings"]
theorem ι_cechCohomologyOfObjectIsoColimitSingleton
    (huniv : ∀ {I : Type w} {D : Discrete I ⥤ C} {d : Cocone D},
      IsColimit d → IsUniversalColimit d)
    (F : Cᵒᵖ ⥤ A) [∀ I : Type w, PreservesLimitsOfShape (Discrete I) F] (n : ℕ)
    [HasColimit (cechCohomologyCoveringFunctor.{w} J U F n)]
    [HasColimit ((singletonCoveringInclusion.{w} J U).op ⋙
      cechCohomologyCoveringFunctor.{w} J U F n)]
    (V : (SingletonCovering J U)ᵒᵖ) :
    colimit.ι ((singletonCoveringInclusion.{w} J U).op ⋙
          cechCohomologyCoveringFunctor.{w} J U F n) V ≫
        (cechCohomologyOfObjectIsoColimitSingleton.{w} J U huniv F n).hom =
      colimit.ι (cechCohomologyCoveringFunctor.{w} J U F n)
        ((singletonCoveringInclusion.{w} J U).op.obj V) :=
  ι_colimitIsoOfInvertsUnit (coproductCoveringAdjunction.{w} J U) _ V

end Reflection

end Stacks.CechSite

end
