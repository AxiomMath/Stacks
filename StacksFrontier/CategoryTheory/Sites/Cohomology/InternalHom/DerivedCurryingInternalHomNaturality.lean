module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
import StacksCore.Tactic.StacksAttribute

/-! # Dinaturality of the tensor–internal-Hom bijection in its internal-Hom variable

Let `(C, O)` be a ringed site. Stacks 08J8 asserts that the bijection

`(A ⟶ RSheafHom(B, Z)) ≃ (A ⊗^L_O B ⟶ Z)`

of `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` is functorial in the three objects. The
companion file `…InternalHom.DerivedCurryingSourceNaturality` proves its naturality in the
source variable `A`. This file proves the remaining *contravariant* clause, in the variable `B`
that occurs on the left of the bijection inside the internal Hom and on the right as a tensor
factor: postcomposing `h : A ⟶ RSheafHom(B, Z)` with the map `RSheafHom(B, Z) ⟶ RSheafHom(B', Z)`
induced by `v : B' ⟶ B` corresponds to precomposing the morphism matched with `h` with `1 ⊗ v`.

Because `B` is contravariant on one side of the bijection and covariant on the other, the clause
is a *dinaturality* square rather than a naturality square: the two induced maps run in opposite
directions and the identity relates a composite on each side, with no commuting square of
functors.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryIso_natural_internalHom`: the naturality square of
  Stacks 08J9 in its middle object.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality`: **Stacks 08J8**,
  dinaturality of the bijection in the internal-Hom variable.

## Implementation notes

The proof is the one the source clause uses, with the two ends of the bijection exchanged. The
bijection is the derived currying isomorphism of Stacks 08J9 read on degree-zero global
hypercohomology, with both ends identified with morphism groups by Stacks 08JA
(`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections`). So the clause is the
naturality of Stacks 08J9 in its *middle* object — which is
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural` at the identity of the first object and
of the target — together with Stacks 08JA used once in each variance: in its *covariant*
variable at the left end, where the induced map is postcomposition with
`RSheafHom(B, Z) ⟶ RSheafHom(B', Z)`
(`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_target`), and in its
contravariant variable at the right end, where it is precomposition with `1 ⊗ v`
(`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap`).
The source clause uses the contravariant one at both ends, which is the only difference.

Every hypothesis is instantiated at its arguments before it is rewritten, and the global-sections
image of the Stacks 08J9 square is a separate declaration: the elaborator's budget is spent per
declaration and the two halves do not fit in one. Both disciplines are the ones recorded in
`…InternalHom.DerivedCurryingSourceNaturality`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The derived currying isomorphism of Stacks 08J9 is natural in its middle object.** This is
`AlgebraicGeometry.RingedSite.derivedCurryIso_natural` at the identity of the first object and
of the target. -/
theorem derivedCurryIso_natural_internalHom
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (A Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (v : B' ⟶ B) :
    ((derivedSheafHomBifunctor X).obj (op A)).map
          (((derivedSheafHomBifunctor X).map v.op).app Z) ≫
        (derivedCurryIso X A B' Z).hom =
      (derivedCurryIso X A B Z).hom ≫
        ((derivedSheafHomBifunctor X).map
          ((((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map v).op)).app Z := by
  simpa using derivedCurryIso_natural X (𝟙 A) v (𝟙 Z)

/-- **The derived currying isomorphism of Stacks 08J9 is natural in its middle object on
degree-zero global hypercohomology.** This is `derivedCurryIso_natural_internalHom` read on a
hypercohomology class.

It is a separate declaration rather than a step of `derivedCurryHomEquiv_dinaturality`
below because the elaborator's budget is spent per declaration, and the two halves do not fit
in one. -/
private lemma derivedCurryIso_globalSections_natural_internalHom
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (A Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (v : B' ⟶ B)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op A)).obj
          (((derivedSheafHomBifunctor X).obj (op B)).obj Z))) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map (derivedCurryIso X A B' Z).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).obj (op A)).map
              (((derivedSheafHomBifunctor X).map v.op).app Z))) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map
            ((((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map v).op)).app Z))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedCurryIso X A B Z).hom) x) := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
    derivedCurryIso_natural_internalHom, Functor.map_comp, Functor.map_comp,
    ConcreteCategory.comp_apply]

/-- **Stacks 08J8, dinaturality in the internal-Hom variable.** Postcomposing a morphism
`h : A ⟶ RSheafHom(B, Z)` with the map `RSheafHom(B, Z) ⟶ RSheafHom(B', Z)` induced by
`v : B' ⟶ B` corresponds, under the tensor–internal-Hom bijection, to precomposing the morphism
`A ⊗^L_O B ⟶ Z` matched with `h` with `1 ⊗ v`.

The variable `B` is contravariant on the left of the bijection and covariant on the right, so
this is a dinaturality identity and not a naturality square. -/
@[stacks 08J8 "dinaturality of the bijection of morphism groups in the internal-Hom variable"]
theorem derivedCurryHomEquiv_dinaturality
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (A Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (v : B' ⟶ B)
    (h : A ⟶ ((derivedSheafHomBifunctor X).obj (op B)).obj Z) :
    derivedCurryHomEquiv X A B' Z
        (h ≫ ((derivedSheafHomBifunctor X).map v.op).app Z) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map v ≫
        derivedCurryHomEquiv X A B Z h := by
  obtain ⟨x, hx⟩ : ∃ x, derivedSheafHomGlobalSectionsEquiv X A
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z) x = h :=
    ⟨_, (derivedSheafHomGlobalSectionsEquiv X A
      (((derivedSheafHomBifunctor X).obj (op B)).obj Z)).apply_symm_apply h⟩
  subst hx
  -- Every hypothesis is instantiated at its arguments before it is rewritten: a rewrite that
  -- has to match a pattern with metavariables against terms of this size exhausts the
  -- elaborator's budget.
  have hN := derivedSheafHomGlobalSectionsEquiv_naturality_target X A
    (((derivedSheafHomBifunctor X).map v.op).app Z) x
  have hl := derivedCurryHomEquiv_globalSections_homologyMap X A B' Z
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (((derivedSheafHomBifunctor X).obj (op A)).map
          (((derivedSheafHomBifunctor X).map v.op).app Z))) x)
  have hr := derivedCurryHomEquiv_globalSections_homologyMap X A B Z x
  have hmid := congrArg (fun t => derivedSheafHomGlobalSectionsEquiv X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B') Z t)
    (derivedCurryIso_globalSections_natural_internalHom X A Z v x)
  rw [← hN, hl, hmid, hr]
  exact derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyMap X Z
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map v) _

end AlgebraicGeometry.RingedSite

end
