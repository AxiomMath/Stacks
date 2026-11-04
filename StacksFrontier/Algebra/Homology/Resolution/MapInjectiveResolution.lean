module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# The image of an injective resolution under an exact functor preserving injectives

Let `F : A ⥤ B` be an additive functor between abelian categories which preserves homology and
carries injective objects to injective objects. Then the image under `F` of an injective
resolution of `M` is an injective resolution of `F M`: its terms are injective because `F`
preserves injective objects, and its augmentation is a quasi-isomorphism because `F` preserves
homology.

The point of recording this is the **comparison of chosen resolutions**. A statement proved about
`CategoryTheory.Functor.rightDerived` through the chosen injective resolution of an object — such
as `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app` or
`Stacks.Cohomology.HigherDirectImage.higherDirectImageRestrictIso_injectiveResolution` — speaks
about `CategoryTheory.injectiveResolution M` on one category and
`CategoryTheory.injectiveResolution (F.obj M)` on the other, and nothing canonical relates those
two complexes. What does relate them is the uniqueness up to homotopy of injective resolutions,
applied to the resolution built here: `CategoryTheory.InjectiveResolution.desc` at the identity of
`F M` descends the chosen resolution of `F M` into the image of the chosen resolution of `M`, and
the augmentation square it comes with is the hypothesis those statements ask for.

## Main results

* `CategoryTheory.InjectiveResolution.mapOfPreservesInjectives`: **the image of an injective
  resolution.** For `F` additive, homology-preserving and injectives-preserving, and `I` an
  injective resolution of `M`, the image of `I` under `F` is an injective resolution of `F M`.
* `CategoryTheory.InjectiveResolution.mapOfPreservesInjectives_ι_f_zero`: its augmentation in
  degree zero is `F` applied to the augmentation of `I` in degree zero.
* `CategoryTheory.InjectiveResolution.desc_mapOfPreservesInjectives_f_zero`: **the augmentation
  clause of the comparison of resolutions.** For any injective resolution `J` of `F M`, the
  degree-zero component of `CategoryTheory.InjectiveResolution.desc` at the identity, precomposed
  with the augmentation of `J`, is `F` applied to the augmentation of `I`.

Nothing is assumed of `A`, of `B`, of `M` or of `I` beyond what `F` is asked for.

## Implementation notes

*The augmentation is written through `HomologicalComplex.singleMapHomologicalComplex`.* The image
under `F` of the complex `M[0]` is not the complex `(F M)[0]` on the nose — the two agree in every
degree but through a `CategoryTheory.eqToHom` that is an identity only after the `if` of
`HomologicalComplex.single` is reduced — so the comparison is taken from Mathlib's natural
isomorphism and its degree-zero component is computed separately, in
`singleMapHomologicalComplex_inv_app_f_zero`.

*`CategoryTheory.Category.id_comp` is applied as a term, not by `rw`.* On a goal whose two sides
are the same morphism of complexes read in degree zero, the rewrite reports that it cannot find
its own pattern; `exact Category.id_comp _` closes the same goal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology] [F.PreservesInjectiveObjects]

/-- **The image of an injective resolution under an exact functor preserving injective objects.**
For an additive `F : A ⥤ B` which preserves homology and carries injective objects to injective
objects, and an injective resolution `I` of `M`, the image of the resolving complex of `I` under
`F` is an injective resolution of `F M`.

Its terms are injective because `F` preserves injective objects, and its augmentation — the image
of `I`'s augmentation, read through `HomologicalComplex.singleMapHomologicalComplex` — is a
quasi-isomorphism because `F` preserves homology.

**Nothing is assumed** of `A`, of `B`, of `M` or of `I`. -/
def mapOfPreservesInjectives {M : A} (I : InjectiveResolution M) :
    InjectiveResolution (F.obj M) where
  cocomplex := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective n := by
    have := I.injective n
    change Injective (F.obj (I.cocomplex.X n))
    infer_instance
  ι := (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app M ≫
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  quasiIso := by
    have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := inferInstance
    infer_instance

omit [F.PreservesHomology] [F.PreservesInjectiveObjects] in
/-- **The degree-zero component of `HomologicalComplex.singleMapHomologicalComplex` inverted is
the identity.** Both ends are `F M`, and the component is an `eqToHom` between them once the `if`
of `HomologicalComplex.single` has been reduced. -/
theorem singleMapHomologicalComplex_inv_app_f_zero (M : A) :
    ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app M).f 0 =
      𝟙 (F.obj M) := by
  simp only [Functor.comp_obj, CochainComplex.single₀_obj_zero,
    Functor.mapHomologicalComplex_obj_X, HomologicalComplex.singleMapHomologicalComplex,
    NatIso.ofComponents_inv_app, ↓reduceDIte]
  exact eqToHom_refl _ _

/-- **The augmentation of the image resolution in degree zero** is `F` applied to the augmentation
of `I` in degree zero: the comparison of the two readings of `F(M[0])` is the identity there. -/
theorem mapOfPreservesInjectives_ι_f_zero {M : A} (I : InjectiveResolution M) :
    (I.mapOfPreservesInjectives F).ι.f 0 = F.map (I.ι.f 0) := by
  show (((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℕ) 0).inv.app M ≫
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι).f 0) = _
  rw [HomologicalComplex.comp_f, singleMapHomologicalComplex_inv_app_f_zero F M]
  exact Category.id_comp _

/-- **The augmentation clause of the comparison of chosen resolutions.** For an injective
resolution `I` of `M` and **any** injective resolution `J` of `F M`,
`CategoryTheory.InjectiveResolution.desc` at the identity of `F M` descends `J` into the image of
`I`, and its degree-zero component precomposed with the augmentation of `J` is `F` applied to the
augmentation of `I`.

This is the hypothesis that a statement computing a right derived functor on the chosen injective
resolution asks for — `Stacks.Cohomology.HigherDirectImage`
`.higherDirectImageRestrictIso_injectiveResolution`'s `hφ`, for instance — so with this lemma such
a statement can be read at the chosen resolutions on both sides, which is the only place a
comparison between two derived functors built from two different chosen resolutions can be
made. -/
theorem desc_mapOfPreservesInjectives_f_zero {M : A} (I : InjectiveResolution M)
    (J : InjectiveResolution (F.obj M)) :
    J.ι.f 0 ≫ (InjectiveResolution.desc (𝟙 (F.obj M)) (I.mapOfPreservesInjectives F) J).f 0 =
      F.map (I.ι.f 0) := by
  have h := InjectiveResolution.desc_commutes (𝟙 (F.obj M)) (I.mapOfPreservesInjectives F) J
  have h0 : (J.ι ≫ InjectiveResolution.desc (𝟙 (F.obj M))
        (I.mapOfPreservesInjectives F) J).f 0 =
      ((CochainComplex.single₀ B).map (𝟙 (F.obj M)) ≫
        (I.mapOfPreservesInjectives F).ι).f 0 := by rw [h]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at h0
  rw [h0, CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
  rw [mapOfPreservesInjectives_ι_f_zero]
  exact Category.id_comp _

end CategoryTheory.InjectiveResolution

end
