module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageTensorIso

/-!
# The comparison of Tag 03EL factors through the two factors of the pullback

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The pullback of
sheaves of modules of Stacks 03D6, part (2) is the inverse image of Stacks 03D2 followed by
extension of scalars along `f♯`,

`Stacks.Sheaves.RingedToposModules.pullbackModules f =
inverseImageModules f ⋙ extendScalarsFSharp f`,

and each factor carries a comparison for a tensor product: the inverse image has
`Stacks.SheafOfModules.inverseImageTensorIso` and the extension of scalars has the base change of
**Stacks 03CU**, `Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso`. This file proves that
the comparison of **Stacks 03EL** is the composite of the two:

`f^*(F ⊗_{O_D} G) --f♯_*(α₁)--> O_C ⊗_{f⁻¹O_D} (f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G) --α₂--> f^*F ⊗_{O_C} f^*G`.

## Main results

* `Stacks.SheafOfModules.pullbackTensorIso_hom_app_eq`: the factorization above.

## Implementation notes

The comparison of Stacks 03EL is the preimage of the identity under the chain of six bijections
`Stacks.SheafOfModules.pullbackTensorHomEquiv`, so the factorization is proved by *applying* that
chain to the composite on the right and checking that the result is the identity. The chain
evaluates on it in four moves, each of which is one of the bijections' own naturality:

* the first link splits, by `CategoryTheory.Adjunction.comp_homEquiv`, into the adjunction of
  Stacks 03CZ followed by that of Stacks 03D4, because
  `Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules` is by construction the
  `CategoryTheory.Adjunction.comp` of those two — this is
  `pullbackTensorStep1_eq_inverseImageStep1`;
* the adjunction of Stacks 03CZ carries `f♯_*(α₁) ≫ α₂` to `α₁ ≫ (the transpose of α₂)`, by
  naturality of a hom-equivalence in its source;
* links two to four *are* the last three links of
  `Stacks.SheafOfModules.inverseImageTensorHomEquiv` — this is
  `pullbackTensorStepsTwoThreeFour_eq`, which holds by `rfl` — and that chain carries `α₁ ≫ k` to
  `k`, since it carries `α₁` to the identity;
* the fifth link is the inverse of the adjunction of Stacks 03CZ, undoing the transpose, and the
  sixth composes with the inverse of `extendScalarsTensorIso`, leaving the identity.

`pullbackTensorStepsTwoThreeFour_eq` is where the two chains are seen to share their middle: the
sheaf of values of the three links is `N|_{f⁻¹O_D}` in the one and an arbitrary sheaf of
`f⁻¹O_D`-modules `M` in the other, and
`Stacks.Sheaves.RingedToposModules.pushforwardModules f` restricts scalars before taking the
direct image, so the two agree on the nose at `M = N|_{f⁻¹O_D}`.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
  Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' v u v' u'

section Factorization

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-- The adjunction of Stacks 03CZ between extension and restriction of scalars along the
inverse-image form `f♯ : f⁻¹O_D ⟶ O_C` of the structure map: the second of the two adjunctions
whose composite is the adjunction of Stacks 03D7. -/
abbrev fSharpExtendRestrictAdjunction :
    extendScalarsFSharp f ⊣ SheafOfModules.restrictScalars f.fSharpInverseImage :=
  f.extendRestrictScalarsFSharpAdjunction

variable (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The first link of the chain of Tag 03EL splits.** The adjunction of Stacks 03D7 is by
construction the composite of the adjunction of Stacks 03D4 with the adjunction of Stacks 03CZ,
so step 1 of the chain of Tag 03EL is the transpose along Stacks 03CZ followed by the transpose
along Stacks 03D4, the latter being step 1 of the chain of
`Stacks.SheafOfModules.inverseImageTensorHomEquiv`. -/
lemma pullbackTensorStep1_eq_inverseImageStep1
    (g : (RingedToposHom.pullbackModules f).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ⟶ N) :
    pullbackTensorStep1 f F G N g =
      inverseImageTensorStep1 f F G
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)
        ((fSharpExtendRestrictAdjunction f).homEquiv _ N g) := by
  show ((inverseImageAdjDirectImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).comp
    (fSharpExtendRestrictAdjunction f)).homEquiv _ N g = _
  simp only [Adjunction.comp_homEquiv]
  rfl

/-- **The chain of Tag 03EL, applied through all six of its links.** The composite bijection is
its six links applied in turn; this restates `Stacks.SheafOfModules.pullbackTensorHomEquiv` with
the argument spelled at the composite functor, which is the spelling the comparison of Tag 03EL is
stated at, so that a rewrite by it fires on a goal about the comparison.

`Stacks.SheafOfModules.pullbackTensorHomEquiv_apply` is the same bijection applied, but read
through the *four* links of the regrouping of links three and four, which is the form the base
change of bilinear pairings is stated at. -/
lemma pullbackTensorHomEquiv_apply_steps
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
        RingedToposHom.pullbackModules f).obj (F, G) ⟶ N) :
    pullbackTensorHomEquiv f F G N g =
      pullbackTensorStep6 f F G N (pullbackTensorStep5 f F G N (pullbackTensorStep4 f F G N
        (pullbackTensorStep3 f F G N (pullbackTensorStep2 f F G N
          (pullbackTensorStep1 f F G N g))))) :=
  rfl

/-- **Step 1 of the chain of Tag 03EL on a morphism which is an extension of scalars followed by
anything.** Combining `pullbackTensorStep1_eq_inverseImageStep1` with the naturality of the
hom-equivalence of Stacks 03CZ in its source: step 1 carries `f♯_*(c) ≫ d` to `c` followed by the
transpose of `d`. -/
lemma pullbackTensorStep1_map_comp
    (P : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (c : (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ⟶ P)
    (d : (extendScalarsFSharp f).obj P ⟶ N) :
    pullbackTensorStep1 f F G N ((extendScalarsFSharp f).map c ≫ d) =
      inverseImageTensorStep1 f F G
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N)
        (c ≫ (fSharpExtendRestrictAdjunction f).homEquiv P N d) := by
  rw [pullbackTensorStep1_eq_inverseImageStep1]
  exact congrArg (inverseImageTensorStep1 f F G _)
    ((fSharpExtendRestrictAdjunction f).homEquiv_naturality_left c d)

/-- **Links two to four of the chain of Tag 03EL are links two to four of the chain of
`Stacks.SheafOfModules.inverseImageTensorHomEquiv`.** The sheaf of values is
`N|_{f⁻¹O_D}` on the one side and an arbitrary sheaf of `f⁻¹O_D`-modules on the other, and
`Stacks.Sheaves.RingedToposModules.pushforwardModules f` restricts scalars before taking the
direct image, so the two agree on the nose. -/
lemma pullbackTensorStepsTwoThreeFour_eq
    (h : (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ⟶
      (SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) :
    pullbackTensorStep4 f F G N (pullbackTensorStep3 f F G N (pullbackTensorStep2 f F G N
        (inverseImageTensorStep1 f F G
          ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) h))) =
      inverseImageTensorHomEquiv f F G
        ((SheafOfModules.restrictScalars f.fSharpInverseImage).obj N) h :=
  rfl

/-- **The chain of Tag 03EL evaluated on the comparison composite.** Applied to the extension of
scalars of `Stacks.SheafOfModules.inverseImageTensorIso` followed by any morphism `d`, the chain
of Tag 03EL gives the last two of its six links applied to the transpose of `d`: the first link
splits off the transpose along Stacks 03CZ, links two to four are the last three links of the
chain of `Stacks.SheafOfModules.inverseImageTensorHomEquiv`, and that chain carries the
inverse-image comparison to the identity. -/
lemma pullbackTensorHomEquiv_extendScalarsMap_comparison_comp
    (d : (extendScalarsFSharp f).obj
        ((Functor.prod
              (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          inverseImageTensorBifunctor f).obj (F, G)) ⟶ N) :
    pullbackTensorHomEquiv f F G N
        ((extendScalarsFSharp f).map ((inverseImageTensorIso f).hom.app (F, G)) ≫ d) =
      pullbackTensorStep6 f F G N (pullbackTensorStep5 f F G N
        ((fSharpExtendRestrictAdjunction f).homEquiv _ N d)) := by
  rw [pullbackTensorHomEquiv_apply_steps, pullbackTensorStep1_map_comp,
    pullbackTensorStepsTwoThreeFour_eq, inverseImageTensorHomEquiv_naturality,
    inverseImageTensorIso_hom_app, Equiv.apply_symm_apply, Category.id_comp]
  rfl

/-- **The comparison of Tag 03EL is the inverse-image comparison followed by the base change of
Tag 03CU.** For a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and sheaves of
`O_D`-modules `F` and `G`,

`f^*(F ⊗ G) ⟶ f^*F ⊗ f^*G`

is the extension of scalars along `f♯` of `f⁻¹(F ⊗ G) ⟶ f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G` followed by
`O_C ⊗_{f⁻¹O_D} (f⁻¹F ⊗ f⁻¹G) ⟶ (O_C ⊗_{f⁻¹O_D} f⁻¹F) ⊗_{O_C} (O_C ⊗_{f⁻¹O_D} f⁻¹G)`.

This is the factorization of the comparison into its two factors, the one belonging to the
inverse image of Stacks 03D2 and the one belonging to the extension of scalars. -/
theorem pullbackTensorIso_hom_app_eq :
    (pullbackTensorIso f).hom.app (F, G) =
      (extendScalarsFSharp f).map ((inverseImageTensorIso f).hom.app (F, G)) ≫
        (extendScalarsTensorIso (fSharpCommRing f)
          (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
          ((inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).hom := by
  have key := pullbackTensorHomEquiv_extendScalarsMap_comparison_comp f F G
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))).obj
      ((RingedToposHom.pullbackModules f).obj F, (RingedToposHom.pullbackModules f).obj G))
    (extendScalarsTensorIso (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).hom
  rw [pullbackTensorIso_hom_app]
  refine (Equiv.symm_apply_eq _).mpr (Eq.symm (key.trans ?_))
  refine Eq.trans (congrArg (pullbackTensorStep6 f F G _)
    (((fSharpExtendRestrictAdjunction f).homEquiv _ _).symm_apply_apply _)) ?_
  exact (extendScalarsTensorIso (fSharpCommRing f)
    (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
    ((inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)).inv_hom_id

end Factorization

end Stacks.SheafOfModules

end
