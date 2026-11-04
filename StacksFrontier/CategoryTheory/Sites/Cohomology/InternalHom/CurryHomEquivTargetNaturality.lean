module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv
import StacksCore.Tactic.StacksAttribute

/-! # Naturality of the cochain-level currying bijection in the target complex

Let `(C, O)` be a ringed site and let `A`, `B` be complexes of `O`-modules.  The currying
bijection of morphism groups of Stacks 0A90,

`(A ⟶ SheafHom(B, D)) ≃ (Tot(A ⊗_O B) ⟶ D)`,

constructed in `StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv` as
`AlgebraicGeometry.RingedSite.curryHomEquiv`, is natural in `D`: for `v : D ⟶ D'` the transpose
of `f` followed by the map `v` induces on the internal Hom complex is the transpose of `f`
followed by `v`.  That is the counterpart, in the remaining variable, of the naturality in the
source complex proved alongside the bijection
(`AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_source`).

## Main results

* `AlgebraicGeometry.RingedSite.curryGlobalIso_natural_target`: the isomorphism of Stacks 0A90,
  read on global sections, is natural in the target complex — postcomposition with
  `homMap (𝟙 B) v` on the iterated side corresponds to postcomposition with `v` on the tensor
  side.
* `AlgebraicGeometry.RingedSite.curryCochainEquiv_homComplexConj_target`: currying of cochains is
  natural in the target complex.
* `AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_target`: **the currying bijection is
  natural in the target complex**,
  `curryHomEquiv (f ≫ homMap (𝟙 B) v) = curryHomEquiv f ≫ v`.

## Nothing here is tagged

Tag 0A90 is the isomorphism of complexes
`AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso`, which already carries the tag, and its
naturality in all three complexes is `AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso_natural`
in the same published statement.  What is proved below is the reading of that naturality on
degree-zero global cocycles, in the single variable the cochain-level bijection was not yet known
to be natural in; it is a step of the proof of Tag 0GM7 and not a clause of a published
statement.  No declaration here carries a tag.

## Implementation notes

*The same four steps as in the source variable.*  The proof is the one
`AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_source` runs, with the variable changed:
the naturality of Stacks 0A90 at `k = 𝟙 A`, `l = 𝟙 B`, `m = v`, pushed to global sections by the
global description of Tag 0A8Z (`AlgebraicGeometry.RingedSite.globalSectionsIso_homMap`), then
read on a degree-`n` cochain, then at a degree-zero cocycle.  Since `curryGlobalIso` is a
conjugation of the global-sections image of the isomorphism of Stacks 0A90 by the two global
descriptions, the global step is a pasting of two conjugation squares, which is stated here over
an abstract category with every object and morphism a variable: at the size the global Hom
complexes have, that is one `isDefEq` instead of a dozen keyed rewrites.

*Collapsing the induced map of total tensor complexes.*  `sheafHomTensorCurryIso_natural` is
stated with the morphism of total tensor complexes induced by `k` and `l` in the general form
`(tensorComplex.map k).app L' ≫ (tensorComplex.obj K).map l`.  At `k = 𝟙 A` and `l = 𝟙 B` that
composite is the identity of `Tot(A ⊗_O B)`, which is what lets the tensor side of the square be
`homMap (𝟙 Tot(A ⊗_O B)) v`, and hence `homComplexConj (𝟙 Tot(A ⊗_O B)) v` after global
sections; `homComplexConj` being contravariant in its first and covariant in its second variable,
that is the postcomposition with `v` the bijection is natural for.

*Why the private copies.*  The pasting lemma and the compatibility of
`globalSectionsComplexMap` with composition are `private` in
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv`, so they cannot be
named from here; they are restated below, unchanged, under their own names.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  ringSheafOverSectionsCommRing

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ### Naturality in the target complex -/

section Target

variable {D D' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The induced map of total tensor complexes at a pair of identities is the identity.**  This
is the collapse that turns the general form of `sheafHomTensorCurryIso_natural` into a statement
about `homMap (𝟙 Tot(A ⊗_O B)) v`. -/
private lemma tensorComplex_map_id_app_comp_map_id
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (𝟙 A)).app B ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (𝟙 B) =
      𝟙 (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) := by
  simp

/-- **Stacks 0A90 in the target variable.**  Postcomposition with `v : D ⟶ D'` on the iterated
internal Hom complex corresponds to postcomposition with `v` on the tensor side; this is the
naturality of `sheafHomTensorCurryIso` at `k = 𝟙 A`, `l = 𝟙 B`, `m = v`, with the induced map of
total tensor complexes collapsed to an identity. -/
theorem sheafHomTensorCurryIso_natural_target
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : D ⟶ D') :
    homMap X (𝟙 A) (homMap X (𝟙 B) v) ≫ (sheafHomTensorCurryIso X A B D').hom =
      (sheafHomTensorCurryIso X A B D).hom ≫
        homMap X (𝟙 (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)) v := by
  have h := sheafHomTensorCurryIso_natural X (𝟙 A) (𝟙 B) v
  rw [tensorComplex_map_id_app_comp_map_id X A B] at h
  exact h

/-- **The isomorphism of Stacks 0A90 is natural in its target complex, after global sections.**
Postcomposition with `homMap (𝟙 B) v` on the iterated side corresponds to postcomposition with
`v` on the tensor side.  The Hom complex is contravariant in its first and covariant in its
second variable, so both sides are written with `homComplexConj` at an identity in the first
argument. -/
theorem curryGlobalIso_natural_target
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : D ⟶ D') :
    (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj (𝟙 A) (homMap X (𝟙 B) v)) ≫
        (curryGlobalIso X A B D').hom =
      (curryGlobalIso X A B D).hom ≫
        (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj
            (𝟙 (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)) v) := by
  have h₃ := globalSectionsComplexMap_comp X (homMap X (𝟙 A) (homMap X (𝟙 B) v))
    (sheafHomTensorCurryIso X A B D').hom
  rw [sheafHomTensorCurryIso_natural_target X A B v,
    ← globalSectionsComplexMap_comp] at h₃
  exact paste_two_conjugations
    (sheafHomComplex X A (sheafHomComplex X B D).obj).globalSectionsIso
    (sheafHomComplex X A (sheafHomComplex X B D').obj).globalSectionsIso
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
      D).globalSectionsIso
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
      D').globalSectionsIso
    _ _ _ _ _ _
    (globalSectionsIso_homMap X (𝟙 A) (homMap X (𝟙 B) v))
    (globalSectionsIso_homMap X
      (𝟙 (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)) v)
    h₃

/-- Currying of cochains is natural in the target complex. -/
theorem curryCochainEquiv_homComplexConj_target
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : D ⟶ D') (n : ℤ)
    (z : Cochain A (sheafHomComplex X B D).obj n) :
    curryCochainEquiv X A B D' n
        (AddCommGrpCat.Hom.hom ((homComplexConj (𝟙 A) (homMap X (𝟙 B) v)).f n) z) =
      AddCommGrpCat.Hom.hom
        ((homComplexConj
          (𝟙 (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)) v).f n)
            (curryCochainEquiv X A B D n z) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n)
      (curryGlobalIso_natural_target X A B v)) (ULift.up z)
  exact congrArg ULift.down h

/-- **The currying bijection is natural in the target complex.**  The transpose of `f` followed
by the map `v : D ⟶ D'` induces on the internal Hom complex is the transpose of `f` followed by
`v`.  Together with
`AlgebraicGeometry.RingedSite.curryHomEquiv_naturality_source` this makes the cochain-level
currying bijection of Stacks 0A90 natural in every variable it has. -/
theorem curryHomEquiv_naturality_target
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (v : D ⟶ D')
    (f : A ⟶ (sheafHomComplex X B D).obj) :
    curryHomEquiv X A B D' (f ≫ homMap X (𝟙 B) v) =
      curryHomEquiv X A B D f ≫ v := by
  have hz : Cochain.ofHom (f ≫ homMap X (𝟙 B) v) =
      AddCommGrpCat.Hom.hom ((homComplexConj (𝟙 A) (homMap X (𝟙 B) v)).f 0)
        (Cochain.ofHom f) := by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    obtain rfl : p = q := by omega
    rw [homComplexConj_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f,
      Category.id_comp, HomologicalComplex.comp_f]
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  rw [curryHomEquiv_f, hz, curryCochainEquiv_homComplexConj_target, homComplexConj_v,
    HomologicalComplex.comp_f, curryHomEquiv_f, HomologicalComplex.id_f, Category.id_comp]

end Target

end AlgebraicGeometry.RingedSite

end
