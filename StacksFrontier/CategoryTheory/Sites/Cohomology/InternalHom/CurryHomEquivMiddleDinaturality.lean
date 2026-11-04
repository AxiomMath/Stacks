module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryingHomEquiv
import StacksCore.Tactic.StacksAttribute

/-! # Dinaturality of the cochain-level currying bijection in the internal-hom complex

Let `(C, O)` be a ringed site and let `A`, `B`, `B'`, `D` be complexes of `O`-modules.  The
currying bijection of morphism groups of Stacks 0A90,

`(A ⟶ SheafHom(B, D)) ≃ (Tot(A ⊗_O B) ⟶ D)`,

`AlgebraicGeometry.RingedSite.curryHomEquiv`, is natural in `A`
(`curryHomEquiv_naturality_source`) and in `D` (`curryHomEquiv_naturality_target`).  This file
supplies the remaining variable, `B`, in which it occurs **contravariantly on the left and
covariantly on the right**, so that what holds is a dinaturality identity rather than a
naturality square: for `φ : B' ⟶ B`,

`cur(f ∘ SheafHom(φ, 1)) = Tot(1 ⊗ φ) ∘ cur(f)`.

## Why it is wanted

This is **Tag 08J8 in its internal-hom variable, read at the cochain level**, and it is the
hypothesis `hdin₁` / `hdin₂` of the abstract transpose construction of Tag 08I3 —
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.TensorHomEquivDinatural`.  Its derived
counterpart, `derivedCurryHomEquiv_dinaturality`, is proved and is what lets the dévissage of
Tag 0GM7 clause (1) run in the derived category; the cochain-level one is what lets the same
dévissage run on the **complexes**, where invertibility of the comparison is quasi-isomorphy and
is therefore local — the shape in which the local-to-global step of Tag 0GM7 clause (1) can be
paid at all.

Together with `curryHomEquiv_naturality_source` it makes all four clauses of Tag 08J8 available at
the cochain level for the comparison
`Stacks.Cohomology.DerivedInternalHomPullback.pullbackHomComplexMap`.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso_natural_middle`: Stacks 0A90 in the
  internal-hom variable, at the level of complexes.
* `AlgebraicGeometry.RingedSite.curryGlobalIso_natural_middle`: the same after global sections.
* `AlgebraicGeometry.RingedSite.curryCochainEquiv_homComplexConj_middle`: the same on cochains.
* `AlgebraicGeometry.RingedSite.curryHomEquiv_dinaturality`: **the dinaturality of the currying
  bijection in the internal-hom complex.**

## Implementation notes

The argument is the one of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CurryHomEquivTargetNaturality`, with the
variable changed: the simultaneous naturality of the currying isomorphism in all three complexes
is `AlgebraicGeometry.RingedSite.sheafHomTensorCurryIso_natural`, read at `k = 𝟙 A`, `l = φ`,
`m = 𝟙 D`, and pushed to global sections by the pasting of two conjugation squares.

*What differs from the target case.*  There the induced map of total tensor complexes collapsed to
an identity and the surviving map was the one on `D`; here it is the other way round — the map on
`D` is an identity and the induced map of total tensor complexes is
`Tot(A ⊗ φ)`, so the conjugation on the tensor side acts in the **contravariant** slot.  That is
why the final rewrite ends with `Category.comp_id` rather than `Category.id_comp`, as in the
source-variable case rather than the target-variable one.

*Why the private copies.*  The pasting lemma and the compatibility of `globalSectionsComplexMap`
with composition are `private` in
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

/-! ### Dinaturality in the internal-hom complex -/

section Middle

variable {B B' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The induced map of total tensor complexes at an identity in the first variable.**  This is
the collapse that turns the general form of `sheafHomTensorCurryIso_natural` into a statement
about `Tot(A ⊗ φ)` alone. -/
private lemma tensorComplex_map_id_app_comp_map_mid
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (φ : B' ⟶ B) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map (𝟙 A)).app B' ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map φ =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map φ := by
  simp

/-- **Stacks 0A90 in the internal-hom variable.**  Precomposition of the inner internal Hom with
`φ : B' ⟶ B` corresponds, on the tensor side, to precomposition with `Tot(A ⊗ φ)`; this is the
naturality of `sheafHomTensorCurryIso` at `k = 𝟙 A`, `l = φ`, `m = 𝟙 D`, with the induced map of
total tensor complexes in the first variable collapsed to an identity. -/
theorem sheafHomTensorCurryIso_natural_middle
    (A D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (φ : B' ⟶ B) :
    homMap X (𝟙 A) (homMap X φ (𝟙 D)) ≫ (sheafHomTensorCurryIso X A B' D).hom =
      (sheafHomTensorCurryIso X A B D).hom ≫
        homMap X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map φ) (𝟙 D) := by
  have h := sheafHomTensorCurryIso_natural X (𝟙 A) φ (𝟙 D)
  rw [tensorComplex_map_id_app_comp_map_mid X A φ] at h
  exact h

/-- **The isomorphism of Stacks 0A90 is dinatural in the internal-hom complex, after global
sections.**  Postcomposition with `homMap φ (𝟙 D)` on the iterated side corresponds to
precomposition with `Tot(A ⊗ φ)` on the tensor side. -/
theorem curryGlobalIso_natural_middle
    (A D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (φ : B' ⟶ B) :
    (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj (𝟙 A) (homMap X φ (𝟙 D))) ≫
        (curryGlobalIso X A B' D).hom =
      (curryGlobalIso X A B D).hom ≫
        (AddCommGrpCat.uliftFunctor.{u}.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (homComplexConj
            (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map φ) (𝟙 D)) := by
  have h₃ := globalSectionsComplexMap_comp X (homMap X (𝟙 A) (homMap X φ (𝟙 D)))
    (sheafHomTensorCurryIso X A B' D).hom
  rw [sheafHomTensorCurryIso_natural_middle X A D φ,
    ← globalSectionsComplexMap_comp] at h₃
  exact paste_two_conjugations
    (sheafHomComplex X A (sheafHomComplex X B D).obj).globalSectionsIso
    (sheafHomComplex X A (sheafHomComplex X B' D).obj).globalSectionsIso
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B)
      D).globalSectionsIso
    (sheafHomComplex X (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B')
      D).globalSectionsIso
    _ _ _ _ _ _
    (globalSectionsIso_homMap X (𝟙 A) (homMap X φ (𝟙 D)))
    (globalSectionsIso_homMap X
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map φ) (𝟙 D))
    h₃

/-- Currying of cochains is dinatural in the internal-hom complex. -/
theorem curryCochainEquiv_homComplexConj_middle
    (A D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (φ : B' ⟶ B) (n : ℤ)
    (z : Cochain A (sheafHomComplex X B D).obj n) :
    curryCochainEquiv X A B' D n
        (AddCommGrpCat.Hom.hom ((homComplexConj (𝟙 A) (homMap X φ (𝟙 D))).f n) z) =
      AddCommGrpCat.Hom.hom
        ((homComplexConj
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map φ) (𝟙 D)).f n)
            (curryCochainEquiv X A B D n z) := by
  have h := ConcreteCategory.congr_hom
    (congrArg (fun ψ => HomologicalComplex.Hom.f ψ n)
      (curryGlobalIso_natural_middle X A D φ)) (ULift.up z)
  exact congrArg ULift.down h

/-- **Tag 08J8 in its internal-hom variable, at the cochain level.**  For `φ : B' ⟶ B` and
`f : A ⟶ SheafHom(B, D)`, the transpose of `f` followed by the map `SheafHom(B, D) ⟶
SheafHom(B', D)` induced by `φ` is the transpose of `f` precomposed with `Tot(A ⊗ φ)`:

`cur(f ≫ SheafHom(φ, 1)) = Tot(1 ⊗ φ) ≫ cur(f)`.

The variable occurs contravariantly on the left of the bijection and covariantly on the right, so
this is a dinaturality identity and not a naturality square.  It is the cochain-level counterpart
of `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_dinaturality`, and together with
`curryHomEquiv_naturality_source` it is the shape
`Stacks.Cohomology.DerivedInternalHomPullback.Transpose.TensorHomEquivDinatural` asks for. -/
theorem curryHomEquiv_dinaturality
    (A D : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (φ : B' ⟶ B)
    (f : A ⟶ (sheafHomComplex X B D).obj) :
    curryHomEquiv X A B' D (f ≫ homMap X φ (𝟙 D)) =
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map φ ≫
        curryHomEquiv X A B D f := by
  have hz : Cochain.ofHom (f ≫ homMap X φ (𝟙 D)) =
      AddCommGrpCat.Hom.hom ((homComplexConj (𝟙 A) (homMap X φ (𝟙 D))).f 0)
        (Cochain.ofHom f) := by
    refine Cochain.ext _ _ fun p q hpq ↦ ?_
    obtain rfl : p = q := by omega
    rw [homComplexConj_v, Cochain.ofHom_v, Cochain.ofHom_v, HomologicalComplex.id_f,
      Category.id_comp, HomologicalComplex.comp_f]
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  rw [curryHomEquiv_f, hz, curryCochainEquiv_homComplexConj_middle, homComplexConj_v,
    HomologicalComplex.comp_f, curryHomEquiv_f, HomologicalComplex.id_f, Category.comp_id]

end Middle

end AlgebraicGeometry.RingedSite

end
