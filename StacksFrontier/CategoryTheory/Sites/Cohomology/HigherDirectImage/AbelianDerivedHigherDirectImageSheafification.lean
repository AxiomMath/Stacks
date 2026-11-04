module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cohomology sheaves of the bounded-below derived direct image of abelian sheaves

Let `u : 𝒟 ⥤ 𝒞` be a continuous functor between sites, so that it induces the direct image
`f_* = u^s : Sh(𝒞, 𝒜) ⥤ Sh(𝒟, 𝒜)` on sheaves with values in an abelian category `𝒜`. Let `K` be
an object of the bounded-below derived category `D^+(Sh(𝒞, 𝒜))`. This file proves, for every
`i : ℤ`, the two natural isomorphisms

* `H^i(Rf_* K) ≅ a (V ↦ H^i(u(V), K))` — the `i`-th cohomology sheaf of `Rf_* K` is the
  sheafification of the hypercohomology presheaf, and
* `(V ↦ H^i(u(V), K))(V) ≅ H^i(u(V), K)` — the value of that presheaf at `V` is the
  hypercohomology of `K` over `u(V)`,

where `a` is sheafification of `𝒜`-valued presheaves on `𝒟`. Together these are the two clauses
of [Stacks, Tag 0D6I] that a cohomological argument on `D^+` actually consumes, for sheaves of
abelian groups rather than for sheaves of modules over a ringed site, and for the bounded-below
derived category rather than the unbounded one. They are the bounded-below counterparts of
`Stacks.Cohomology.SheafifiedHigherDirectImage.rightDerivedPushforwardIso` and
`pushforwardCohomologyPresheafEvaluationIso`, which are [Stacks, Tag 072W] in the same generality.

The hypercohomology presheaf is realised, exactly as in the underived case, as the total right
derived functor on `D^+` of the composite `Sh(𝒞, 𝒜) ⥤ PSh(𝒟, 𝒜)` sending a sheaf `F` to the
presheaf `V ↦ F(u(V))`, which is
`Stacks.Cohomology.SheafifiedHigherDirectImage.pushforwardCohomologyPresheaf`. So all objects of
`𝒟` and all restriction maps between them are assembled before deriving, and the restriction maps
of the presheaf are part of the construction rather than something to be checked afterwards.

## Main results

All in the namespace `Stacks.Cohomology.SheafifiedHigherDirectImage`.

* `derivedPushforwardHomologySheafifyIso`: the sheafification clause. The `i`-th cohomology sheaf
  of `Rf_* -` on `D^+` is the sheafification of the `i`-th cohomology presheaf of the derived
  cohomology presheaf, naturally in the bounded-below object.
* `derivedPushforwardCohomologyPresheafEvaluationIso`: the values clause. The value at `V` of
  that cohomology presheaf is `H^i(u(V), -)`, naturally in the bounded-below object.

## Implementation notes

**Both clauses are one application each of an exactness comparison.** The generic input is
`Stacks.Cohomology.HigherDirectImagePresheaf.postcomposeHomologyIso`: for `G` exact, the `i`-th
cohomology of the total right derived functor of `F ⋙ G` on `D^+` is `G` applied to the `i`-th
cohomology of the total right derived functor of `F`. The sheafification clause is that for
`G = a`, after transporting along
`pushforwardCohomologyPresheafCompSheafification : (V ↦ -(u(V))) ⋙ a ≅ f_*` with
`Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso`; the values
clause is that for `G` the evaluation of presheaves at `V`, read backwards. So the two exactness
facts the file rests on are that sheafification preserves homology
(`preservesHomology_presheafToSheaf`, left exact as a left adjoint that is also left exact) and
that evaluation of presheaves at an object preserves homology (it is exact, limits and colimits of
presheaves being computed pointwise).

**How the values clause reads as hypercohomology over `u(V)`.**
`pushforwardCohomologyPresheaf_comp_evaluation` is an equality of functors that holds by `rfl`,
and `CategoryTheory.Functor.Additive` is a `Prop`, so the total right derived functor of the
composite appearing in the statement and the total right derived functor of `Γ(u(V), -)` are
definitionally the same functor: a consumer that has the additivity instance for its own spelling
of `Γ(u(V), -)` may read the statement at that spelling directly. The composite is what is
written here because its additivity follows from the additivity of its two factors with no
further instance.

**Derived categories are hypotheses.** All four categories involved — the two sheaf categories,
the presheaf category on `𝒟` and `𝒜` itself — carry `HasDerivedCategory` as an instance
hypothesis rather than a fixed choice, so a consumer may supply
`CategoryTheory.HasDerivedCategory.standard` or any other.

## References

* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.SheafifiedHigherDirectImage

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology D} {K : GrothendieckTopology C}
  (A : Type*) [Category* A] [Abelian A] [HasSheafify J A] [HasSheafify K A]
  (u : D ⥤ C) [u.IsContinuous J K]

section DerivedPushforward

variable [HasDerivedCategory A] [HasDerivedCategory (Sheaf K A)]
  [HasDerivedCategory (Sheaf J A)] [HasDerivedCategory (Dᵒᵖ ⥤ A)]
  [EnoughInjectives (Sheaf K A)]

attribute [local instance] preservesHomology_presheafToSheaf

/-- **[Stacks, Tag 0D6I] for abelian sheaves on `D^+`, the associated sheaf.** The `i`-th
cohomology sheaf of the bounded-below derived direct image is the sheafification of the `i`-th
cohomology presheaf of the derived cohomology presheaf `V ↦ H^•(u(V), -)`, naturally in the
object of `D^+(Sh(𝒞, 𝒜))`.

Writing `f_*` as `(V ↦ -(u(V))) ⋙ a` by `pushforwardCohomologyPresheafCompSheafification` and
pulling the exact functor `a` out of the cohomology of the total right derived functor with
`postcomposeHomologyIso`. -/
@[ega "0 12.2.1" "more general", sga "4 V 5.1" "special case", sga "4 VIII 5.1" "more general"]
def derivedPushforwardHomologySheafifyIso (i : ℤ) :
    (u.sheafPushforwardContinuous A J K).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (Sheaf J A) i ≅
      (pushforwardCohomologyPresheaf (K := K) A u).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (Dᵒᵖ ⥤ A) i ⋙ presheafToSheaf J A :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso
        (pushforwardCohomologyPresheafCompSheafification A u).symm)
      (DerivedCategory.Plus.homologyFunctor (Sheaf J A) i) ≪≫
    Stacks.Cohomology.HigherDirectImagePresheaf.postcomposeHomologyIso
      (pushforwardCohomologyPresheaf (K := K) A u) (presheafToSheaf J A) i

/-- **[Stacks, Tag 0D6I] for abelian sheaves on `D^+`, values on objects of the target site.**
The value at `V` of the `i`-th cohomology presheaf of the derived cohomology presheaf is the
hypercohomology `H^i(u(V), -)` over `u(V)`, naturally in the object of `D^+(Sh(𝒞, 𝒜))`.

Evaluation of presheaves at `V` is exact, so it comes out of the cohomology of the total right
derived functor by `postcomposeHomologyIso`.

As in the underived `pushforwardCohomologyPresheafEvaluationIso`, the target is spelled as the
total right derived functor of the composite rather than of `(sheafSections K A).obj (op (u V))`;
by `pushforwardCohomologyPresheaf_comp_evaluation` those two functors are equal, and the
composite spelling is the one whose additivity is available from the additivity of its two
factors. -/
@[sga "4 VIII 5.1" "partial"]
def derivedPushforwardCohomologyPresheafEvaluationIso (i : ℤ) (V : D) :
    (pushforwardCohomologyPresheaf (K := K) A u).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor (Dᵒᵖ ⥤ A) i ⋙
        (evaluation Dᵒᵖ A).obj (op V) ≅
      (pushforwardCohomologyPresheaf (K := K) A u ⋙
          (evaluation Dᵒᵖ A).obj (op V)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor A i :=
  letI : ((evaluation Dᵒᵖ A).obj (op V)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  (Stacks.Cohomology.HigherDirectImagePresheaf.postcomposeHomologyIso
    (pushforwardCohomologyPresheaf (K := K) A u) ((evaluation Dᵒᵖ A).obj (op V)) i).symm

end DerivedPushforward

end Stacks.Cohomology.SheafifiedHigherDirectImage

end
