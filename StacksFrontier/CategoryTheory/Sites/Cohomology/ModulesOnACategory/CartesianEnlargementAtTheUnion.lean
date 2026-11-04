module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianEnlargementOfSubcomplexes

/-!
# The base-change condition on sections at the union of an iterated enlargement

Let `C` be a category, regarded as a site with the chaotic topology, and let `O` be a presheaf of
rings on `C` whose section rings are commutative. The enlargement claim behind conclusion (1) of
Stacks 0GYZ enlarges a small subcomplex `S^• ⊆ F^•` in stages `S^• = G_0^• ⊆ G_1^• ⊆ ⋯` and takes
`H^•` to be their union. What has then to be checked of `H^•` is, for every morphism `U → V` of
`C`, the base-change condition on its sections: the comparison
`H^•(V) ⊗^L_{O(V)} O(U) ⟶ H^•(U)` is an isomorphism in `D(O(U))`.

This file carries that condition from the stages to the union. Over `V` and over `U` the complex of
sections of `H^•` is the filtered colimit of those of the stages
(`isColimit_sections_of_stages`), and
`Stacks.SubcomplexEnlargement.isIso_comparison_of_stagewise_union` turns the two stagewise
conditions Stacks 0GYI produces — the kernel of the comparison on cohomology dying at the next
stage, and the image of the next step already being covered — into invertibility at the union.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentEquivalence.isIso_sectionsBaseChange_at_union`: the
  base-change condition on sections holds at the union of an iterated enlargement as soon as it
  holds stagewise in the two-sided form of Stacks 0GYI.

## Implementation notes

The statement is the form of the condition that Stacks 0GYI speaks of: the invertibility of
`α.app (P^•(V)) ≫ Q(b)`, where `α` presents a total left derived functor of termwise extension of
scalars and `b` is the degreewise base-change map of sections. Nothing here chooses that left
derived model; `T` and `α` are binders, so the caller can use the one Stacks 0GYI's own statement
quantifies over. That it agrees with the cartesianness condition of Stacks 0GYV — the invertibility
of `comparison bc a` — is
`Stacks.ModulesOnACategory.CartesianObjects.isIso_comparison_Q_iff_isLeftDerived`, and nothing in
either direction needs flatness.

Commutativity of the two section rings is unavoidable and is not a hypothesis beyond those of the
source: extension of scalars `M ↦ M ⊗_{O(V)} O(U)` requires a commutative `O(V)`, so there is no
base change along a restriction map of `O` without it, and Stacks 0GYI is a lemma of More on
Algebra, where every ring is commutative.

The hypotheses on the chain of stages are the ones
`exists_iterated_enlargement_containing_sections` returns, among them that the inclusions `γ_n`
of the stages are monomorphisms, which `BoundedSubcomplex` carries.

## References

* [Stacks Project, Tag 0GYZ](https://stacks.math.columbia.edu/tag/0GYZ)
* [Stacks Project, Tag 0GYI](https://stacks.math.columbia.edu/tag/0GYI)
* [Stacks Project, Tag 0GYV](https://stacks.math.columbia.edu/tag/0GYV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModulesOnACategory.CartesianObjects (commRingOfComm)
open Stacks.ModulesOnACategory.QuasiCoherentCohomology (sectionsBaseChange)

namespace Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ RingCat.{r}}

/-- **The base-change condition on sections at the union of an iterated enlargement.** Let
`G_0^• ⊆ G_1^• ⊆ ⋯` be a chain of subcomplexes of `F^•` with union `H^•`, and let `a : V ⟶ U` in
`Cᵒᵖ`. If at every stage the kernel of the comparison on cohomology over `V` dies at the next
stage, and the image of the next step over `U` is already covered by the comparison there, then the
comparison at `H^•` is an isomorphism.

Those two stagewise conditions are exactly what Stacks 0GYI returns for the pair of subcomplexes
`G_n^•(V) ⊆ F^•(V)` and `G_n^•(U) ⊆ F^•(U)`, and this is the step that converts them into the
cartesianness of the union. -/
public theorem isIso_sectionsBaseChange_at_union {U V : Cᵒᵖ} (a : V ⟶ U)
    (hV : ∀ x y : O.obj V, x * y = y * x) (hU : ∀ x y : O.obj U, x * y = y * x) :
    letI := commRingOfComm (O.obj V) hV
    letI := commRingOfComm (O.obj U) hU
    letI : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).isLeftAdjoint
    letI : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).Additive :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).left_adjoint_additive
    let bSec : ∀ P : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ,
        ((ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj ((sectionsComplexFunctor.{w} O V).obj P) ⟶
          (sectionsComplexFunctor.{w} O U).obj P :=
      fun P => (NatTrans.mapHomologicalComplex
        (sectionsBaseChange.{w} O a
          (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom))
        (ComplexShape.up ℤ)).app P
    ∀ (T : CategoryTheory.Functor
        (DerivedCategory (ModuleCat.{max u v r w} (O.obj V)))
        (DerivedCategory (ModuleCat.{max u v r w} (O.obj U))))
      (α : DerivedCategory.Q ⋙ T ⟶
        (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      [T.IsLeftDerivedFunctor α
        (HomologicalComplex.quasiIso (ModuleCat.{max u v r w} (O.obj V)) (ComplexShape.up ℤ))]
      {F H : CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
      {G : ℕ → CochainComplex (PresheafOfModules.{max u v r w} O) ℤ}
      (h : H ⟶ F) (γ : ∀ n, G n ⟶ F) (p : ∀ n, G n ⟶ G (n + 1)) (k : ∀ n, G n ⟶ H),
      Mono h → (∀ n, Mono (γ n)) → (∀ n, p n ≫ γ (n + 1) = γ n) → (∀ n, k n ≫ h = γ n) →
      (∀ (i : ℤ) (X : Cᵒᵖ) (x : (H.X i).obj X),
        ∃ (n : ℕ) (y : ((G n).X i).obj X), ((k n).f i).app X y = x) →
      (∀ (n : ℕ) (i : ℤ)
        (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).obj
          (T.obj (DerivedCategory.Q.obj ((sectionsComplexFunctor.{w} O V).obj (G n))))),
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).map
            (α.app ((sectionsComplexFunctor.{w} O V).obj (G n)) ≫
              DerivedCategory.Q.map (bSec (G n)))) x = 0 →
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).map
            (T.map (DerivedCategory.Q.map ((sectionsComplexFunctor.{w} O V).map (p n))))) x = 0) →
      (∀ (n : ℕ) (i : ℤ)
        (y : (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).obj
          (DerivedCategory.Q.obj ((sectionsComplexFunctor.{w} O U).obj (G n)))),
        ∃ x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).obj
          (T.obj (DerivedCategory.Q.obj ((sectionsComplexFunctor.{w} O V).obj (G (n + 1))))),
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).map
              (α.app ((sectionsComplexFunctor.{w} O V).obj (G (n + 1))) ≫
                DerivedCategory.Q.map (bSec (G (n + 1))))) x =
            ((DerivedCategory.homologyFunctor (ModuleCat.{max u v r w} (O.obj U)) i).map
              (DerivedCategory.Q.map ((sectionsComplexFunctor.{w} O U).map (p n)))) y) →
      IsIso (α.app ((sectionsComplexFunctor.{w} O V).obj H) ≫
        DerivedCategory.Q.map (bSec H)) := by
  let := commRingOfComm (O.obj V) hV
  let := commRingOfComm (O.obj U) hU
  let : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).isLeftAdjoint
  let : (ModuleCat.extendScalars.{r, r, max u v r w} (O.map a).hom).Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom).left_adjoint_additive
  intro bSec T α hT F H G h γ p k hmono hγ hp hk hexh hker himg
  have := hT
  have := hmono
  exact Stacks.SubcomplexEnlargement.isIso_comparison_of_stagewise_union.{r, r, max u v r w}
    _ T α
    (fun i =>
      Stacks.SubcomplexEnlargement.derivedBaseChangeHomology_preservesFilteredColimits_ulift.{r,
        r, max u v r w} (O.map a).hom T α (J := ULift.{max u v r w, 0} ℕ) i)
    (bSec H)
    (fun n => (sectionsComplexFunctor.{w} O V).obj (G n))
    (fun n => (sectionsComplexFunctor.{w} O U).obj (G n))
    (fun n => (sectionsComplexFunctor.{w} O V).map (k n))
    (fun n => (sectionsComplexFunctor.{w} O U).map (k n))
    (fun n => (sectionsComplexFunctor.{w} O V).map (p n))
    (fun n => (sectionsComplexFunctor.{w} O U).map (p n))
    (fun n => bSec (G n))
    (mono_unionSectionsMap.{w} h γ k hγ hk V)
    (mono_unionSectionsMap.{w} h γ k hγ hk U)
    (comp_unionSectionsMap_eq.{w} h γ p k hp hk V)
    (comp_unionSectionsMap_eq.{w} h γ p k hp hk U)
    (fun i x => hexh i V x) (fun i x => hexh i U x)
    (fun n => (NatTrans.mapHomologicalComplex
      (sectionsBaseChange.{w} O a
        (ModuleCat.extendRestrictScalarsAdj.{max u v w, r, r} (O.map a).hom))
      (ComplexShape.up ℤ)).naturality (k n))
    hker himg

end Stacks.ModulesOnACategory.QuasiCoherentEquivalence

end
