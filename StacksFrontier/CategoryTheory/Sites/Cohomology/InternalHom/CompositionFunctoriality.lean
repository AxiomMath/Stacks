module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EvaluationMorphism
import StacksCore.Tactic.StacksAttribute

/-! # Functoriality of the composition morphism of internal Hom complexes

Let `(C, O)` be a ringed site. The composition morphism of internal Hom complexes of
Stacks 0A91,

`Tot(SheafHom(L, M) ⊗_O SheafHom(K, L)) ⟶ SheafHom(K, M)`,

is contravariant in `K`, covariant in `M` and *dinatural* in the intermediate complex `L`:
the intermediate complex occurs covariantly in the right-hand tensor factor and
contravariantly in the left-hand one, so a morphism `l : L ⟶ L'` can be absorbed into either
factor with the same effect. This file records all three at once, in a single identity for a
triple of morphisms `k : K' ⟶ K`, `l : L ⟶ L'` and `m : M ⟶ M'`, and then specialises it to
the three one-variable statements that the derived composition morphism of Stacks 0A98 needs.

## Main results

* `AlgebraicGeometry.RingedSite.compositionSection_homMap`: the three-variable identity on
  homogeneous local sections.
* `AlgebraicGeometry.RingedSite.compositionMap_natural`: the three-variable identity.
* `AlgebraicGeometry.RingedSite.compositionMap_natural_source`,
  `AlgebraicGeometry.RingedSite.compositionMap_natural_target` and
  `AlgebraicGeometry.RingedSite.compositionMap_dinatural_middle`: its three one-variable
  specialisations.

## Implementation notes

Everything is proved on homogeneous local pure tensors, through
`AlgebraicGeometry.RingedSite.tensorTotal_hom_ext` and
`AlgebraicGeometry.RingedSite.homSection_ext`, from the two characterisations
`AlgebraicGeometry.RingedSite.compositionSection_applyOver` and
`AlgebraicGeometry.RingedSite.applyHomSectionOver_homMap`. No sign enters: composition of
homogeneous local sections carries none, and neither does `homMap`.

The three-variable identity is stated with the identity morphism inserted in the slot of each
tensor factor that the corresponding variable does not touch, which is why the two sides have
the same source `Tot(SheafHom(L', M) ⊗_O SheafHom(K, L))` even though the intermediate complex
is absorbed on different sides.

## References

* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
  curriedTensorPreservesZeroMorphisms curriedTensorObjPreservesZeroMorphisms

variable {K K' L L' M M' :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **Functoriality of composition on homogeneous local sections.** Composing the image of a
section `β` of `SheafHom(L', M)` under `homMap (𝟙 L') m` with the image of a section `γ` of
`SheafHom(K, L)` under `homMap k l` is the image under `homMap k m` of the composite of `γ`
with the image of `β` under `homMap l (𝟙 M)`. -/
lemma compositionSection_homMap (k : K' ⟶ K) (l : L ⟶ L') (m : M ⟶ M') (U : X.C) (p q : ℤ)
    (β : ((sheafHomComplex X L' M).obj.X p).val.obj (op U))
    (γ : ((sheafHomComplex X K L).obj.X q).val.obj (op U)) :
    compositionSection X U p q (p + q) rfl
        (((homMap X (𝟙 L') m).f p).val.app (op U) β)
        (((homMap X k l).f q).val.app (op U) γ) =
      ((homMap X k m).f (p + q)).val.app (op U)
        (compositionSection X U p q (p + q) rfl
          (((homMap X l (𝟙 M)).f p).val.app (op U) β) γ) := by
  refine homSection_ext X (sheafHomComplex X K' M') U (p + q) fun r t hrt V i x ↦ ?_
  rw [compositionSection_applyOver X U V i p q (p + q) r (r + q) t rfl rfl (by omega),
    applyHomSectionOver_homMap X k l U V i q r (r + q) rfl γ x,
    applyHomSectionOver_homMap X (𝟙 L') m U V i p (r + q) t (by omega) β _,
    applyHomSectionOver_homMap X k m U V i (p + q) r t hrt _ x,
    compositionSection_applyOver X U V i p q (p + q) r (r + q) t rfl rfl (by omega),
    applyHomSectionOver_homMap X l (𝟙 M) U V i p (r + q) t (by omega) β _]
  simp

/-- **Functoriality of the composition morphism of Stacks 0A91**, in all three complexes at
once: it is contravariant in the source `K`, covariant in the target `M`, and dinatural in the
intermediate complex `L`, which may be absorbed into either tensor factor. -/
theorem compositionMap_natural (k : K' ⟶ K) (l : L ⟶ L') (m : M ⟶ M') :
    tensorTotalMap X (homMap X (𝟙 L') m) (homMap X k l) ≫ compositionMap X K' L' M' =
      tensorTotalMap X (homMap X l (𝟙 M)) (𝟙 (sheafHomComplex X K L).obj) ≫
        compositionMap X K L M ≫ homMap X k m := by
  refine tensorTotal_hom_ext X fun U p q β γ ↦ ?_
  rw [HomologicalComplex.comp_f, AlgebraicGeometry.RingedSite.comp_val_app_apply',
    tensorTotalMap_tensorTotalSection, compositionMap_tensorTotalSection,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    AlgebraicGeometry.RingedSite.comp_val_app_apply',
    AlgebraicGeometry.RingedSite.comp_val_app_apply', tensorTotalMap_tensorTotalSection,
    compositionMap_tensorTotalSection, compositionSection_homMap]
  simp

/-- The total tensor product of two identities is the identity. -/
lemma tensorTotalMap_id
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotalMap X (𝟙 A) (𝟙 B) = 𝟙 (tensorTotal X A B) := by
  refine tensorTotal_hom_ext X fun U t r a b ↦ ?_
  rw [tensorTotalMap_tensorTotalSection]
  simp

/-- The composition morphism of Stacks 0A91 is contravariant in the source complex. -/
theorem compositionMap_natural_source (k : K' ⟶ K) (L M : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotalMap X (𝟙 (sheafHomComplex X L M).obj) (homMap X k (𝟙 L)) ≫
        compositionMap X K' L M =
      compositionMap X K L M ≫ homMap X k (𝟙 M) := by
  simpa only [homMap_id, tensorTotalMap_id, Category.id_comp] using
    compositionMap_natural X k (𝟙 L) (𝟙 M)

/-- The composition morphism of Stacks 0A91 is covariant in the target complex. -/
theorem compositionMap_natural_target (K L : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : M ⟶ M') :
    tensorTotalMap X (homMap X (𝟙 L) m) (𝟙 (sheafHomComplex X K L).obj) ≫
        compositionMap X K L M' =
      compositionMap X K L M ≫ homMap X (𝟙 K) m := by
  simpa only [homMap_id, tensorTotalMap_id, Category.id_comp] using
    compositionMap_natural X (𝟙 K) (𝟙 L) m

/-- **Dinaturality of the composition morphism of Stacks 0A91 in the intermediate complex.**
A morphism `l : L ⟶ L'` may be absorbed either covariantly into the right-hand factor
`SheafHom(K, L)` or contravariantly into the left-hand factor `SheafHom(L', M)`, with the same
effect on the composite. -/
theorem compositionMap_dinatural_middle (K : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (l : L ⟶ L')
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    tensorTotalMap X (𝟙 (sheafHomComplex X L' M).obj) (homMap X (𝟙 K) l) ≫
        compositionMap X K L' M =
      tensorTotalMap X (homMap X l (𝟙 M)) (𝟙 (sheafHomComplex X K L).obj) ≫
        compositionMap X K L M := by
  simpa only [homMap_id, Category.comp_id] using compositionMap_natural X (𝟙 K) l (𝟙 M)

end AlgebraicGeometry.RingedSite

end
