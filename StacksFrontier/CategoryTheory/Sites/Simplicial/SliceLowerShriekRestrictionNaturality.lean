module

public import StacksFrontier.CategoryTheory.Sites.Glueing.LowerShriekObjectNaturality
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.Relocalization
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.ShriekRestrictionTransition
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SliceLowerShriekRestriction

/-!
# Reading off the two projections of Stacks 0D87 part (2)

Let `(C, J)` be a small site and `K` a semi-representable object of `C`.
`CategoryTheory.SemiRepresentable.sheafPushforwardCompSheafPullbackIso` is Stacks 0D87, part (2)
read on the site `C / K`: it identifies `j_{K!} j_K^{-1}` with `G ↦ G ⊗ F(K)^♯`, the target being
Mathlib's `CategoryTheory.toOver (F(K)^♯)` followed by `CategoryTheory.Over.forget`. A map into
`G ⊗ F(K)^♯` is its two projections, so every statement about that isomorphism — in particular
its naturality in `K` — splits into a `CartesianMonoidalCategory.fst` half and a
`CartesianMonoidalCategory.snd` half, exactly as the one-object case Stacks 03EE does in
`StacksFrontier/CategoryTheory/Sites/Glueing/LowerShriekObjectNaturality.lean`.

This module supplies the component form of that isomorphism, both of its projections, and the
naturality in `K` of each of them, hence the naturality square itself.

## Main results

* `CategoryTheory.SemiRepresentable.sheafPushforwardCompSheafPullbackIso_hom_app`: the component
  of the isomorphism, with the six factors of its `Iso.trans` chain evaluated; four of them are
  identities, three outright and the `eqToIso` one by
  `eqToIso_sheafPushforwardContinuous_comp_restrictSheaf_hom_app`.
* `CategoryTheory.SemiRepresentable.sheafPushforwardCompSheafPullbackIso_hom_app_fst`: **the
  `fst` projection is the counit of `j_{K!} ⊣ j_K^{-1}`.** The two ends of the composite are the
  two uniqueness-of-adjoints lemmas
  (`componentwiseRestrictionCompSheafFunctorToOverIso_hom_app_comp_fst` with
  `toOverComparisonAdjunction_counit_app`, and
  `componentOverForget_sheafPullback_iso_hom_app_comp_counit`), joined by
  `componentShriekSigmaCompAdjunction_counit_app`.
* `SemiRepresentable.componentwiseRestrictionCompSheafFunctorToOverIso_hom_app_comp_snd`:
  the `snd` projection of the last factor is the structural map of `j_!`, by the commuting
  triangle of a morphism in the slice.
* `CategoryTheory.SemiRepresentable.tautologicalSection`: the tautological section of `F(K)^♯`
  over the site `C / K`, the semi-representable analogue of
  `CategoryTheory.OverShriek.tautologicalSection`.
* `CategoryTheory.SemiRepresentable.sheafPushforwardCompSheafPullbackIso_hom_app_snd`: **the
  `snd` projection is the adjunct of that tautological section.** Unlike the `fst` projection it
  is not a counit; the tautological section is constant, which is what makes the naturality in
  `K` available.
* `SemiRepresentable.shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso_fst`
  and `.shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso_snd`: **Stacks 0D87
  part (2) is natural in the semi-representable object**, on the sheaf factor and on the
  `F(-)^♯` factor. For a morphism `f : M ⟶ N` the shriek restriction transition is carried by the
  two instances of Stacks 0D87 part (2) to a map which is the identity on the sheaf and `F(f)^♯`
  on the sheafified object.
* `SemiRepresentable.shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso`:
  **the naturality square**, the two halves assembled by
  `CategoryTheory.CartesianMonoidalCategory.hom_ext`, exactly as
  `CategoryTheory.SemiRepresentable.overShriekTransition_comp_overShriekOverPullbackNatIso_app`
  assembles the one-object case from `Limits.prod.hom_ext`.

## Implementation notes

`CategoryTheory.Iso.trans` is `implicit_reducible`, so `(α ≪≫ β).hom` is already in
`simp`-normal form and `CategoryTheory.Iso.trans_hom` never fires on it; the component form is
therefore stated with all six factors written out and proved by `rfl`, and the one place where an
`Iso.trans` component has to be evaluated uses `show`.

The component form cannot be reduced to its two non-identity factors: the `eqToIso` factor is an
`eqToHom` between two *spellings* of one object — `(j_K^{-1} ⋙ restrictSheaf).obj X` and
`(componentwiseRestriction J K).obj X` — so `CategoryTheory.Functor.map_id` and
`CategoryTheory.Category.id_comp` have nothing syntactic to match, and
`CategoryTheory.Limits.Sigma.map` of it is not `rfl`-reducible to the identity because
`CategoryTheory.Limits.getColimitCocone` is not exposed.

Three more frictions, on the `snd` half.

The identity component of `componentShriekSigmaIso` *can* be cancelled, but only in term mode:
the two spellings `(componentShriekSigma J K).obj W` and
`(sheafFunctorToOver J K ⋙ Over.forget _).obj W` are definitionally equal at default
transparency and not at the `reducible` transparency `rw` instantiates its lemmas at, where
`getColimitCocone` stops the unfolding. So `Category.id_comp` is applied as a term, under
`eq_whisker`, and never by `rw`.

The adjunct of the one-object structural map is computed through
`CategoryTheory.Adjunction.homEquiv_unit` rather than
`CategoryTheory.Adjunction.restrictFullyFaithful_homEquiv_apply`, because
`componentShriekAdjunction` cannot be restated: its two `Iso.refl` arguments only elaborate
against the expected type of the original definition, and re-elaborating them with `L` and `R`
supplied gives the two sides of `comm1` at different spellings.

`componentOverMap_comp_componentOverForget` does **not** hold by `rfl`, unlike its one-object
counterpart behind `CategoryTheory.SemiRepresentable.overMapPullbackIso`: both functors are
`CategoryTheory.Sigma.desc`, whose action on morphisms matches on the `SigmaHom` constructor and
so does not reduce for a variable morphism. The component of
`relocalizationForgetPushforwardIso'` is therefore *not* an identity transformation — only its
value at an object with an explicit index is, which is
`relocalizationForgetPushforwardIso'_hom_app_hom_app` and the reason the compatibility along `f`
is proved object by object.

## References

* [Stacks Project, Tag 0D87](https://stacks.math.columbia.edu/tag/0D87)
* [Stacks Project, Tag 00XS](https://stacks.math.columbia.edu/tag/00XS)
* [Stacks Project, Tag 03EE](https://stacks.math.columbia.edu/tag/03EE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
  Opposite

universe u

namespace CategoryTheory.SemiRepresentable

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : FormalCoproduct.{u} C)
  [HasWeakSheafify J (Type u)] [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)]

omit [HasWeakSheafify J (Type u)] [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- The equality of functors behind the `eqToIso` factor of
`sheafPushforwardCompSheafPullbackIso` holds by `rfl`, so its component is the identity. -/
theorem eqToIso_sheafPushforwardContinuous_comp_restrictSheaf_hom_app (X : Sheaf J (Type u)) :
    (eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K)).hom.app X =
      𝟙 ((componentwiseRestriction J K).obj X) :=
  rfl

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- Every component of `componentShriekSigmaIso` is the identity: the two functors agree on
objects and on morphisms. -/
theorem componentShriekSigmaIso_hom_app (F : SheafOverFormalCoproduct J K) :
    (componentShriekSigmaIso J K).hom.app F = 𝟙 ((componentShriekSigma J K).obj F) :=
  rfl

/-- **The component of Stacks 0D87 part (2) on the site `C / K`**, with the six factors of the
`Iso.trans` chain of `sheafPushforwardCompSheafPullbackIso` evaluated. The second, fourth and
fifth factors are identities outright, and the third is one by
`eqToIso_sheafPushforwardContinuous_comp_restrictSheaf_hom_app`, so the content is the first and
the last. -/
theorem sheafPushforwardCompSheafPullbackIso_hom_app (X : Sheaf J (Type u)) :
    (sheafPushforwardCompSheafPullbackIso J K).hom.app X =
      (componentOverForget_sheafPullback_iso J K).hom.app
          (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj X) ≫
        𝟙 _ ≫
        (componentShriekSigma J K).map
            ((eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K)).hom.app X) ≫
          (componentShriekSigmaIso J K).hom.app ((componentwiseRestriction J K).obj X) ≫
            𝟙 _ ≫
            (Over.forget (formalCoproductSheafification J K)).map
              ((componentwiseRestrictionCompSheafFunctorToOverIso J K).hom.app X) :=
  rfl

/-! ### The `fst` projection -/

/-- The adjunction between `Sh(C)` and `Sh(C)/F(K)^♯` whose right adjoint
`componentwiseRestrictionCompSheafFunctorToOverIso` compares with `toOver (F(K)^♯)`: the
equivalence of Stacks 0D87 part (1) composed with Stacks 00XS for `K`. -/
abbrev toOverComparisonAdjunction :
    Over.forget (formalCoproductSheafification J K) ⊣
      componentwiseRestriction J K ⋙ sheafFunctorToOver J K :=
  (((sheafEquivalence J K).symm.toAdjunction.comp
      (sheafFunctorToOverForgetAdjunction J K)).ofNatIsoLeft
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sheafEquivalence J K).counitIso _ ≪≫
      Functor.leftUnitor _))

/-- **The last factor of Stacks 0D87 part (2), followed by the projection onto the sheaf, is a
counit.** The projection `G ⊗ F(K)^♯ ⟶ G` is the counit of `Over.forget ⊣ toOver`
(Mathlib's `CategoryTheory.forgetAdjToOver`), and
`componentwiseRestrictionCompSheafFunctorToOverIso` is uniqueness of right adjoints against it,
so this is `CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`. -/
theorem componentwiseRestrictionCompSheafFunctorToOverIso_hom_app_comp_fst
    (X : Sheaf J (Type u)) :
    (Over.forget (formalCoproductSheafification J K)).map
          ((componentwiseRestrictionCompSheafFunctorToOverIso J K).hom.app X) ≫
        fst X (formalCoproductSheafification J K) =
      (toOverComparisonAdjunction J K).counit.app X :=
  Adjunction.rightAdjointUniq_hom_app_counit (toOverComparisonAdjunction J K)
    (forgetAdjToOver (formalCoproductSheafification J K)) X

/-- The `ofNatIsoLeft` comparison of `toOverComparisonAdjunction` cancels against the inverse
unit of the equivalence of Stacks 0D87 part (1): this is that equivalence's triangle identity,
`CategoryTheory.Equivalence.counitInv_functor_comp`. -/
theorem toOverComparison_counitIso_inv_app_comp (Z : SheafOverFormalCoproduct J K) :
    (Functor.isoWhiskerRight (sheafEquivalence J K).counitIso
            (Over.forget (formalCoproductSheafification J K)) ≪≫
          (Over.forget (formalCoproductSheafification J K)).leftUnitor).inv.app
        ((sheafEquivalence J K).functor.obj Z) ≫
        Over.Hom.left ((sheafFunctorToOver J K).map ((sheafEquivalence J K).unitInv.app Z)) =
      𝟙 ((Over.forget (formalCoproductSheafification J K)).obj
        ((sheafEquivalence J K).functor.obj Z)) := by
  show 𝟙 _ ≫ (Over.forget (formalCoproductSheafification J K)).map
        ((sheafEquivalence J K).counitIso.inv.app ((sheafEquivalence J K).functor.obj Z)) ≫
      (Over.forget (formalCoproductSheafification J K)).map
        ((sheafEquivalence J K).functor.map ((sheafEquivalence J K).unitInv.app Z)) = _
  rw [Category.id_comp, ← Functor.map_comp, Equivalence.counitInv_functor_comp]
  exact (Over.forget (formalCoproductSheafification J K)).map_id _

/-- **The counit of `toOverComparisonAdjunction` is the counit of Stacks 00XS for `K`.** The
equivalence of Stacks 0D87 part (1) enters that adjunction twice, once in the composite and once
in the `ofNatIsoLeft` comparison, and the two cancel by
`toOverComparison_counitIso_inv_app_comp`. -/
theorem toOverComparisonAdjunction_counit_app (X : Sheaf J (Type u)) :
    (toOverComparisonAdjunction J K).counit.app X =
      (sheafFunctorToOverForgetAdjunction J K).counit.app X := by
  simp only [toOverComparisonAdjunction, Adjunction.ofNatIsoLeft, Adjunction.comp_counit_app,
    Equivalence.symm_functor, Equivalence.symm_inverse, Equivalence.toAdjunction_counit,
    NatTrans.comp_app, Functor.comp_map, Functor.whiskerLeft_app]
  exact (eq_whisker (toOverComparison_counitIso_inv_app_comp J K
      ((componentwiseRestriction J K).obj X)) _).trans (Category.id_comp _)

/-! ### The first factor against the counit -/

/-- The second adjunction compared by `componentOverForget_sheafPullback_iso`: the componentwise
lower shrieks, assembled, read through the slice equivalence of `C / K`. -/
abbrev componentShriekSigmaCompAdjunction :
    (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor ⋙
        componentShriekSigma J K ⊣
      (componentOverForget K).sheafPushforwardContinuous (Type u)
        (componentwiseTopology J K) J :=
  ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).toAdjunction.comp
    (componentShriekSigmaAdjunction J K)).ofNatIsoRight
      (componentwiseRestrictionCompInverseIso J K)

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- **The first factor of Stacks 0D87 part (2), followed by the counit of the assembled
componentwise lower shrieks, is the counit of `j_{K!} ⊣ j_K^{-1}`.** This is uniqueness of left
adjoints, `CategoryTheory.Adjunction.leftAdjointUniq_hom_app_counit`. -/
theorem componentOverForget_sheafPullback_iso_hom_app_comp_counit (X : Sheaf J (Type u)) :
    (componentOverForget_sheafPullback_iso J K).hom.app
          (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj X) ≫
        (componentShriekSigmaCompAdjunction J K).counit.app X =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget K)
        (Type u) (componentwiseTopology J K) J).counit.app X :=
  Adjunction.leftAdjointUniq_hom_app_counit _ (componentShriekSigmaCompAdjunction J K) X

/-! ### The two presentations of `j_{K!} j_K^{-1}` have the same counit -/

omit [HasWeakSheafify J (Type u)] [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- The component of `componentwiseRestrictionCompInverseIso`: the unit of the slice equivalence
of `C / K`, followed by the assembling functor applied to the `eqToIso` factor. -/
theorem componentwiseRestrictionCompInverseIso_inv_app (X : Sheaf J (Type u)) :
    (componentwiseRestrictionCompInverseIso J K).inv.app X =
      ((𝟙 _ ≫ (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).unit.app
            (((componentOverForget K).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J K) J).obj X)) ≫ 𝟙 _) ≫
        (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).inverse.map
          ((eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K).symm).inv.app X) :=
  rfl

omit [HasWeakSheafify J (Type u)] [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- **The comparison of `componentwiseRestrictionCompInverseIso` against the counit of the slice
equivalence is the `eqToIso` factor.** Naturality of that counit moves the `eqToHom` past it, and
what is left is the equivalence's triangle identity
`CategoryTheory.Equivalence.functor_unit_comp`. -/
theorem formalCoproductSliceSheaves_counit_comp (X : Sheaf J (Type u)) :
    (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor.map
          ((componentwiseRestrictionCompInverseIso J K).inv.app X) ≫
        (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).counit.app
          ((componentwiseRestriction J K).obj X) =
      (eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K)).hom.app X := by
  rw [componentwiseRestrictionCompInverseIso_inv_app, Category.comp_id, Category.id_comp,
    Functor.map_comp, Category.assoc]
  exact (whisker_eq _
        ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).counit.naturality
          ((eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K).symm).inv.app X))).trans
    ((Category.assoc _ _ _).symm.trans
      ((eq_whisker (Equivalence.functor_unit_comp
          (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)) _) _).trans
        (Category.id_comp _)))

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- **The three middle factors of Stacks 0D87 part (2), against the counit of Stacks 00XS for
`K`, give the counit of `componentShriekSigmaCompAdjunction`.** This is the step that joins the
two uniqueness-of-adjoints halves of
`sheafPushforwardCompSheafPullbackIso_hom_app_fst`: both adjunctions are built from
`componentShriekSigmaAdjunction`, the `componentShriekSigmaIso` factors cancel, and the rest is
`formalCoproductSliceSheaves_counit_comp`. -/
theorem componentShriekSigmaCompAdjunction_counit_app (X : Sheaf J (Type u)) :
    (componentShriekSigma J K).map
          ((eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K)).hom.app X) ≫
        (componentShriekSigmaIso J K).hom.app ((componentwiseRestriction J K).obj X) ≫
          (sheafFunctorToOverForgetAdjunction J K).counit.app X =
      (componentShriekSigmaCompAdjunction J K).counit.app X := by
  have hL : (componentShriekSigmaIso J K).hom.app ((componentwiseRestriction J K).obj X) ≫
        (sheafFunctorToOverForgetAdjunction J K).counit.app X =
      (componentShriekSigmaAdjunction J K).counit.app X := by
    show (componentShriekSigmaIso J K).hom.app ((componentwiseRestriction J K).obj X) ≫
        (componentShriekSigmaIso J K).inv.app ((componentwiseRestriction J K).obj X) ≫
          (componentShriekSigmaAdjunction J K).counit.app X = _
    rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have hR : (componentShriekSigmaCompAdjunction J K).counit.app X =
      (componentShriekSigma J K).map
            ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor.map
              ((componentwiseRestrictionCompInverseIso J K).inv.app X)) ≫
          (componentShriekSigma J K).map
            ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).counit.app
              ((componentwiseRestriction J K).obj X)) ≫
            (componentShriekSigmaAdjunction J K).counit.app X :=
    rfl
  rw [hL, hR, ← Category.assoc, ← Functor.map_comp]
  exact (eq_whisker
    (congrArg
      (fun m : (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor.obj
            (((componentOverForget K).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J K) J).obj X) ⟶ (componentwiseRestriction J K).obj X =>
        (componentShriekSigma J K).map m)
      (formalCoproductSliceSheaves_counit_comp J K X)) _).symm

/-! ### The two projections -/

/-- `sheafPushforwardCompSheafPullbackIso_hom_app` with the three outright identity factors
dropped. The `eqToIso` factor cannot be dropped as well; see the implementation notes. -/
theorem sheafPushforwardCompSheafPullbackIso_hom_app' (X : Sheaf J (Type u)) :
    (sheafPushforwardCompSheafPullbackIso J K).hom.app X =
      (componentOverForget_sheafPullback_iso J K).hom.app
          (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj X) ≫
        (componentShriekSigma J K).map
            ((eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K)).hom.app X) ≫
          (componentShriekSigmaIso J K).hom.app ((componentwiseRestriction J K).obj X) ≫
            (Over.forget (formalCoproductSheafification J K)).map
              ((componentwiseRestrictionCompSheafFunctorToOverIso J K).hom.app X) :=
  rfl

/-- Postcomposing `sheafPushforwardCompSheafPullbackIso_hom_app'` with any map, reassociated. -/
private theorem sheafPushforwardCompSheafPullbackIso_hom_app_comp (X : Sheaf J (Type u))
    {T : Sheaf J (Type u)}
    (g : (Over.forget (formalCoproductSheafification J K)).obj
      ((toOver (formalCoproductSheafification J K)).obj X) ⟶ T) :
    (sheafPushforwardCompSheafPullbackIso J K).hom.app X ≫ g =
      (componentOverForget_sheafPullback_iso J K).hom.app
          (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj X) ≫
        (componentShriekSigma J K).map
            ((eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K)).hom.app X) ≫
          (componentShriekSigmaIso J K).hom.app ((componentwiseRestriction J K).obj X) ≫
            (Over.forget (formalCoproductSheafification J K)).map
              ((componentwiseRestrictionCompSheafFunctorToOverIso J K).hom.app X) ≫ g := by
  rw [sheafPushforwardCompSheafPullbackIso_hom_app']
  simp only [Category.assoc]

/-- **The `fst` projection of Stacks 0D87 part (2) is the counit of `j_{K!} ⊣ j_K^{-1}`.**
Reading `j_{K!} j_K^{-1} G` as `G ⊗ F(K)^♯`, the projection onto `G` is the canonical map. This is
the semi-representable counterpart of
`CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_snd`, where the sheaf factor
sits on the other side of the product.

The two ends of the composite are uniqueness of right adjoints
(`componentwiseRestrictionCompSheafFunctorToOverIso_hom_app_comp_fst`, then
`toOverComparisonAdjunction_counit_app`) and uniqueness of left adjoints
(`componentOverForget_sheafPullback_iso_hom_app_comp_counit`), joined by
`componentShriekSigmaCompAdjunction_counit_app`. -/
theorem sheafPushforwardCompSheafPullbackIso_hom_app_fst (X : Sheaf J (Type u)) :
    (sheafPushforwardCompSheafPullbackIso J K).hom.app X ≫
        fst X (formalCoproductSheafification J K) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget K)
        (Type u) (componentwiseTopology J K) J).counit.app X :=
  (sheafPushforwardCompSheafPullbackIso_hom_app_comp J K X _).trans
    ((whisker_eq _ (whisker_eq _ (whisker_eq _
        ((componentwiseRestrictionCompSheafFunctorToOverIso_hom_app_comp_fst J K X).trans
          (toOverComparisonAdjunction_counit_app J K X))))).trans
      ((whisker_eq _ (componentShriekSigmaCompAdjunction_counit_app J K X)).trans
        (componentOverForget_sheafPullback_iso_hom_app_comp_counit J K X)))

/-- **The `snd` projection of the last factor of Stacks 0D87 part (2) is the structural map of
`j_!`.** The projection onto `F(K)^♯` is the structural map of `toOver (F(K)^♯)`, and
`componentwiseRestrictionCompSheafFunctorToOverIso` is an isomorphism *in the slice*, so this is
just the commuting triangle of a morphism over `F(K)^♯`.

This is the entry point for the `snd` half of the naturality of Stacks 0D87 part (2): it reduces
that half to the first three factors against the structural map of `sheafFunctorToOver`, which is
componentwise the one-object structural map followed by a coproduct injection. -/
theorem componentwiseRestrictionCompSheafFunctorToOverIso_hom_app_comp_snd
    (X : Sheaf J (Type u)) :
    (Over.forget (formalCoproductSheafification J K)).map
          ((componentwiseRestrictionCompSheafFunctorToOverIso J K).hom.app X) ≫
        snd X (formalCoproductSheafification J K) =
      ((componentwiseRestriction J K ⋙ sheafFunctorToOver J K).obj X).hom :=
  Over.w ((componentwiseRestrictionCompSheafFunctorToOverIso J K).hom.app X)

/-! ### The tautological section, and the `snd` projection -/

/-- **The tautological section of `F(K)^♯` over the site `C / K`.** For a sheaf `W` on
`C / K = ∐ i, C / K_i` the map `W ⟶ j_K^{-1}F(K)^♯` which over the object `(i, A →φ K_i)` sends
every section of `W` to the image under the sheafification unit of `φ`, viewed in the `i`-th
summand of `F(K) = ∐ i, h_{K_i}`.

This is the semi-representable counterpart of
`CategoryTheory.OverShriek.tautologicalSection`, and it is the section whose adjunct the `snd`
projection of Stacks 0D87 part (2) is. -/
def tautologicalSection (W : Sheaf (componentwiseTopology J K) (Type u)) :
    W ⟶ ((componentOverForget K).sheafPushforwardContinuous (Type u)
      (componentwiseTopology J K) J).obj (formalCoproductSheafification J K) :=
  ObjectProperty.homMk
    { app := fun A => ↾fun _ =>
        ((sheafificationAdjunction J (Type u)).unit.app
            ((FormalCoproduct.yoneda (C := C)).obj K)).app (op A.unop.2.left)
          ((Limits.Sigma.ι (fun i : K.I => yoneda.obj (K.obj i)) A.unop.1).app
            (op A.unop.2.left) A.unop.2.hom)
      naturality := by
        rintro ⟨⟨i, A⟩⟩ ⟨⟨j, B⟩⟩ h
        cases hh : h.unop with
        | mk g =>
          have hh' : h = Quiver.Hom.op (CategoryTheory.Sigma.SigmaHom.mk
              (C := fun i : K.I => Over (K.obj i)) g) := by
            apply Quiver.Hom.unop_inj
            simpa using hh
          subst h
          ext w
          exact ((congrArg
                (((sheafificationAdjunction J (Type u)).unit.app
                    ((FormalCoproduct.yoneda (C := C)).obj K)).app (op B.left))
                ((congrArg
                    ((Limits.Sigma.ι (fun i : K.I => yoneda.obj (K.obj i)) i).app (op B.left))
                    (Over.w g)).symm.trans
                  (NatTrans.naturality_apply
                    (Limits.Sigma.ι (fun i : K.I => yoneda.obj (K.obj i)) i)
                    g.left.op A.hom))).trans
              (NatTrans.naturality_apply
                ((sheafificationAdjunction J (Type u)).unit.app
                  ((FormalCoproduct.yoneda (C := C)).obj K)) g.left.op
                ((Limits.Sigma.ι (fun i : K.I => yoneda.obj (K.obj i)) i).app
                  (op A.left) A.hom))) }

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- **The tautological section is constant.** It does not depend on the sheaf it is taken on, so
precomposing it with any map of sheaves on `C / K` gives the tautological section again. -/
theorem comp_tautologicalSection {W W' : Sheaf (componentwiseTopology J K) (Type u)}
    (m : W ⟶ W') :
    m ≫ tautologicalSection J K W' = tautologicalSection J K W :=
  rfl

/-- The tautological section read in the componentwise presentation of `Sh(C / K)`: on the
component indexed by `i` it is the one-object tautological section of `h_{K_i}^♯` followed by the
`i`-th sheafified coproduct injection. -/
def componentwiseTautologicalSection (W : SheafOverFormalCoproduct J K) :
    W ⟶ (componentwiseRestriction J K).obj (formalCoproductSheafification J K) :=
  fun i => OverShriek.tautologicalSection (K.obj i) J (W i) ≫
    (J.overPullback (Type u) (K.obj i)).map (formalCoproductSheafificationι J K i)

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- The componentwise tautological section is constant, componentwise by
`CategoryTheory.OverShriek.comp_tautologicalSection`. -/
theorem comp_componentwiseTautologicalSection {W W' : SheafOverFormalCoproduct J K} (m : W ⟶ W') :
    m ≫ componentwiseTautologicalSection J K W' = componentwiseTautologicalSection J K W := by
  funext i
  exact (Category.assoc (m i) (OverShriek.tautologicalSection (K.obj i) J (W' i)) _).symm.trans
    (eq_whisker (OverShriek.comp_tautologicalSection (K.obj i) J (m i)) _)

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- **The structural map of the one-object `j_{i!}` is the adjunct of the tautological section.**
The map `j_{i!}V ⟶ h_{K_i}^♯` carried by `CategoryTheory.OverShriek.sheafFunctorToOver` is, under
Stacks 00XS for the component `K_i`, the transpose of
`CategoryTheory.OverShriek.tautologicalSection`.

Both transposes are computed by the unit of the Stacks 03CD adjunction composed with
sheafification — `componentShriekAdjunction` is that composite restricted to sheaves — so the
content is the naturality of the sheafification unit along
`CategoryTheory.OverShriek.presheafToYoneda`, which is `(φ, s) ↦ φ`. -/
theorem componentShriekAdjunction_homEquiv_sheafFunctorToOver_hom (i : K.I)
    (V : Sheaf (J.over (K.obj i)) (Type u)) :
    (componentShriekAdjunction J K i).homEquiv V
        ((presheafToSheaf J (Type u)).obj (yoneda.obj (K.obj i)))
        ((OverShriek.sheafFunctorToOver (U := K.obj i) J).obj V).hom =
      OverShriek.tautologicalSection (K.obj i) J V := by
  rw [Adjunction.homEquiv_unit]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun A => ?_)
  ext s
  exact (congrArg (fun m => m ⟨A.unop.hom, s⟩)
    (NatTrans.congr_app ((sheafificationAdjunction J (Type u)).unit.naturality
      (OverShriek.presheafToYoneda V.obj)) (op A.unop.left))).symm

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- **The structural map of `j_!` is the adjunct of the componentwise tautological section.** By
`CategoryTheory.SemiRepresentable.sheafCoproductToOver` that structural map is
`CategoryTheory.Limits.Sigma.desc` of the one-object structural maps followed by the sheafified
coproduct injections, and the hom-set bijection of `componentShriekSigmaAdjunction` is
componentwise, so this is
`componentShriekAdjunction_homEquiv_sheafFunctorToOver_hom` on each summand. -/
theorem componentShriekSigmaAdjunction_homEquiv_sheafFunctorToOver_hom
    (W : SheafOverFormalCoproduct J K) :
    (componentShriekSigmaAdjunction J K).homEquiv W (formalCoproductSheafification J K)
        ((componentShriekSigmaIso J K).hom.app W ≫ ((sheafFunctorToOver J K).obj W).hom) =
      componentwiseTautologicalSection J K W := by
  have h : (componentShriekSigmaAdjunction J K).homEquiv W
      (formalCoproductSheafification J K) =
      componentShriekSigmaHomEquiv J K W (formalCoproductSheafification J K) := by
    unfold componentShriekSigmaAdjunction
    rw [Adjunction.mkOfHomEquiv_homEquiv]
  rw [h]
  funext i
  rw [componentShriekSigmaHomEquiv_apply]
  refine Eq.trans (congrArg ((componentShriekAdjunction J K i).homEquiv (W i)
      (formalCoproductSheafification J K))
    ((whisker_eq _
          ((eq_whisker (componentShriekSigmaIso_hom_app J K W) _).trans
            (Category.id_comp _))).trans
      (Limits.Sigma.ι_desc
        (fun j => ((OverShriek.sheafFunctorToOver (U := K.obj j) J).obj (W j)).hom ≫
          formalCoproductSheafificationι J K j) i))) ?_
  rw [Adjunction.homEquiv_naturality_right,
    componentShriekAdjunction_homEquiv_sheafFunctorToOver_hom]
  rfl

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- **Restricting the tautological section to the components is the componentwise tautological
section.** Over `(i, A →φ K_i)` both are the image of `φ` under the sheafification unit followed
by the `i`-th injection; they differ only in the order in which the injection and the unit are
applied, which is the naturality of that unit along `CategoryTheory.Limits.Sigma.ι`. -/
theorem formalCoproductSliceSheaves_map_tautologicalSection
    (W : Sheaf (componentwiseTopology J K) (Type u)) :
    (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor.map
        (tautologicalSection J K W) =
      componentwiseTautologicalSection J K
        ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor.obj W) := by
  funext i
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun A => ?_)
  ext w
  exact congrArg (fun m => m A.unop.hom)
    (NatTrans.congr_app ((sheafificationAdjunction J (Type u)).unit.naturality
      (Limits.Sigma.ι (fun i : K.I => yoneda.obj (K.obj i)) i)) (op A.unop.left))

omit [HasWeakSheafify J (Type u)] [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- The unit of the slice equivalence of `C / K` at a restricted sheaf is the inverse of
`componentwiseRestrictionCompInverseIso`: by `componentwiseRestrictionCompInverseIso_inv_app` the
latter is that unit against the `eqToIso` factor, whose component is the identity. -/
theorem unit_comp_componentwiseRestrictionCompInverseIso_hom (Y : Sheaf J (Type u)) :
    (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).unit.app
          (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj Y) ≫
        (componentwiseRestrictionCompInverseIso J K).hom.app Y =
      𝟙 (((componentOverForget K).sheafPushforwardContinuous (Type u)
        (componentwiseTopology J K) J).obj Y) := by
  have h : (componentwiseRestrictionCompInverseIso J K).inv.app Y =
      (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).unit.app
        (((componentOverForget K).sheafPushforwardContinuous (Type u)
          (componentwiseTopology J K) J).obj Y) := by
    rw [componentwiseRestrictionCompInverseIso_inv_app, Category.comp_id, Category.id_comp,
      show (eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K).symm).inv.app Y =
        𝟙 _ from rfl]
    exact (whisker_eq _
      ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).inverse.map_id _)).trans
        (Category.comp_id _)
  rw [← h]
  exact (componentwiseRestrictionCompInverseIso J K).inv_hom_id_app Y

/-- **The `snd` projection of Stacks 0D87 part (2) is the adjunct of the tautological section.**
Reading `j_{K!}j_K^{-1}G` as `G ⊗ F(K)^♯`, the projection onto `F(K)^♯` is the transpose under
`j_{K!} ⊣ j_K^{-1}` of `tautologicalSection`. This is the semi-representable counterpart of
`CategoryTheory.OverShriek.overShriekOverPullbackNatIso_hom_app_prod_fst`, where the sheaf factor
sits on the other side of the product.

Unlike the `fst` projection this is not a counit, and the right-hand side is the only description
of it that does not mention `G`: the tautological section is constant, which is what makes the
naturality in `K` available.

By `componentwiseRestrictionCompSheafFunctorToOverIso_hom_app_comp_snd` the composite is the
first three factors against the structural map of `sheafFunctorToOver J K`. Transposing,
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` moves the question to
`componentShriekSigmaCompAdjunction`, where
`componentShriekSigmaAdjunction_homEquiv_sheafFunctorToOver_hom` answers it, and the two
transports through the slice equivalence cancel by
`unit_comp_componentwiseRestrictionCompInverseIso_hom`. -/
theorem sheafPushforwardCompSheafPullbackIso_hom_app_snd (X : Sheaf J (Type u)) :
    (sheafPushforwardCompSheafPullbackIso J K).hom.app X ≫
        snd X (formalCoproductSheafification J K) =
      (Functor.sheafPullbackConstruction.sheafPullback (componentOverForget K) (Type u)
            (componentwiseTopology J K) J).map
          (tautologicalSection J K
            (((componentOverForget K).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J K) J).obj X)) ≫
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget K)
          (Type u) (componentwiseTopology J K) J).counit.app
            (formalCoproductSheafification J K) := by
  refine ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget K)
    (Type u) (componentwiseTopology J K) J).homEquiv _ _).injective ?_
  have hL := (sheafPushforwardCompSheafPullbackIso_hom_app_comp J K X
    (snd X (formalCoproductSheafification J K))).trans
    (whisker_eq _ (whisker_eq _ (whisker_eq _
      (componentwiseRestrictionCompSheafFunctorToOverIso_hom_app_comp_snd J K X))))
  rw [hL, Stacks.CategoryTheory.homEquiv_map_comp_counit]
  refine Eq.trans (Adjunction.homEquiv_leftAdjointUniq_hom_app_comp
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget K)
      (Type u) (componentwiseTopology J K) J)
    (componentShriekSigmaCompAdjunction J K) _) ?_
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Stacks.CategoryTheory.comp_homEquiv_apply,
    Equivalence.toAdjunction_unit]
  have h4 : (componentShriekSigmaAdjunction J K).homEquiv
        ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor.obj
          (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj X))
        (formalCoproductSheafification J K)
        ((componentShriekSigma J K).map
            ((eqToIso (sheafPushforwardContinuous_comp_restrictSheaf J K)).hom.app X) ≫
          (componentShriekSigmaIso J K).hom.app ((componentwiseRestriction J K).obj X) ≫
            ((componentwiseRestriction J K ⋙ sheafFunctorToOver J K).obj X).hom) =
      (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor.map
        (tautologicalSection J K (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj X)) :=
    (Adjunction.homEquiv_naturality_left (componentShriekSigmaAdjunction J K) _ _).trans
      (((whisker_eq _
              (componentShriekSigmaAdjunction_homEquiv_sheafFunctorToOver_hom J K _)).trans
            (comp_componentwiseTautologicalSection J K _)).trans
        (formalCoproductSliceSheaves_map_tautologicalSection J K _).symm)
  have h5 : (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).unit.app
          (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj X) ≫
        (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).inverse.map
          ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).functor.map
            (tautologicalSection J K (((componentOverForget K).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J K) J).obj X))) =
      tautologicalSection J K (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj X) ≫
        (formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).unit.app
          (((componentOverForget K).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J K) J).obj (formalCoproductSheafification J K)) :=
    ((formalCoproductSliceSheavesEquivalenceFunctor J K (Type u)).unit.naturality _).symm
  rw [h4]
  exact (eq_whisker h5 _).trans
    ((Category.assoc _ _ _).trans
      ((whisker_eq _ (unit_comp_componentwiseRestrictionCompInverseIso_hom J K
          (formalCoproductSheafification J K))).trans
        (Category.comp_id _)))


section Naturality

variable {M N : FormalCoproduct.{u} C} (f : M ⟶ N)

/-- **Stacks 0D87 part (2) is natural in the semi-representable object, on the sheaf factor.**
For a morphism `f : M ⟶ N` of semi-representable objects, the shriek restriction transition
`j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` is carried by the two instances of Stacks 0D87 part (2) to a
map over the identity of the sheaf: that is, the `fst` halves of the naturality square agree.

This is one of the two halves of the comparison of
`CategoryTheory.SemiRepresentable.shriekRestrictionTransition` with `F(f)^♯`, the half announced
in the docstring of
`CategoryTheory.SemiRepresentable.shriekRestrictionTransition_comp_counit`. Both projections are
the counit of `j_! ⊣ j^{-1}` by `sheafPushforwardCompSheafPullbackIso_hom_app_fst`, and the
transition is a map over the identity. The other half, the `F(-)^♯` factor, is not proved here;
see the module docstring. -/
theorem shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso_fst
    (X : Sheaf J (Type u)) :
    (shriekRestrictionTransition J f (componentwiseTopology J M) (componentwiseTopology J N)
          (Type u)).app X ≫
        (sheafPushforwardCompSheafPullbackIso J N).hom.app X ≫
          fst X (formalCoproductSheafification J N) =
      (sheafPushforwardCompSheafPullbackIso J M).hom.app X ≫
        fst X (formalCoproductSheafification J M) := by
  rw [sheafPushforwardCompSheafPullbackIso_hom_app_fst,
    sheafPushforwardCompSheafPullbackIso_hom_app_fst]
  exact shriekRestrictionTransition_comp_counit J f (componentwiseTopology J M)
    (componentwiseTopology J N) (Type u) X

omit [HasWeakSheafify J (Type u)] [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- The component of the relocalization comparison at an object `(i, A →φ M_i)` of `C / M` is the
identity.

That comparison is `CategoryTheory.Functor.sheafPushforwardContinuousComp'` at
`eqToIso (componentOverMap_comp_componentOverForget f)`, and — unlike its one-object counterpart
behind `CategoryTheory.SemiRepresentable.overMapPullbackIso` — that equality of site functors does
not hold by `rfl`, so the comparison is not an identity transformation. On an object with an
explicit index the two functors do agree definitionally, which is what makes the `eqToHom` an
identity here. -/
theorem relocalizationForgetPushforwardIso'_hom_app_hom_app (Z : Sheaf J (Type u))
    (i : M.I) (A : Over (M.obj i)) :
    ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
          (componentwiseTopology J N) (Type u)).hom.app Z).hom.app (op ⟨i, A⟩) =
      𝟙 (Z.obj.obj (op A.left)) := by
  rw [relocalizationForgetPushforwardIso'_eq]
  show Z.obj.map ((eqToHom (componentOverMap_comp_componentOverForget f).symm).app
      (⟨i, A⟩ : ComponentOver M)).op = 𝟙 (Z.obj.obj (op A.left))
  rw [eqToHom_app, eqToHom_op, eqToHom_map]
  exact eqToHom_refl _ _

omit [HasSheafify J (Type u)] [J.WEqualsLocallyBijective (Type u)] in
/-- **The tautological sections at `M` and at `N` agree along `f : M ⟶ N`.** Restricting the
tautological section of `F(N)^♯` along the componentwise relocalization functor `r_f` and
transporting it by the relocalization comparison gives the tautological section of `F(M)^♯`
followed by `F(f)^♯`: over the object `(i, A →φ M_i)` both are the image of `φ ≫ f.φ i`, in the
summand indexed by `f.f i`, under the sheafification unit of `F(N)` — on the left because `r_f`
sends `(i, A →φ M_i)` to `(f.f i, A →{φ ≫ f.φ i} N_{f.f i})`, on the right by
`CategoryTheory.Limits.Sigma.ι_desc` for `F(f)` and the naturality of that unit along `F(f)`.

This is the only concrete input of the `snd` half of the naturality, and the semi-representable
counterpart of `CategoryTheory.SemiRepresentable.overMapPullback_tautologicalSection`. -/
theorem componentOverMap_tautologicalSection
    (W : Sheaf (componentwiseTopology J N) (Type u)) :
    ((componentOverMap f).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) (componentwiseTopology J N)).map
          (tautologicalSection J N W) ≫
        (relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
          (componentwiseTopology J N) (Type u)).hom.app
            (formalCoproductSheafification J N) =
      tautologicalSection J M
          (((componentOverMap f).sheafPushforwardContinuous (Type u)
            (componentwiseTopology J M) (componentwiseTopology J N)).obj W) ≫
        ((componentOverForget M).sheafPushforwardContinuous (Type u)
          (componentwiseTopology J M) J).map (formalCoproductSheafificationMap J f) := by
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext ?_)
  rintro ⟨⟨i, A⟩⟩
  show (tautologicalSection J N W).hom.app (op ((componentOverMap f).obj ⟨i, A⟩)) ≫
        ((relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
          (componentwiseTopology J N) (Type u)).hom.app
            (formalCoproductSheafification J N)).hom.app (op ⟨i, A⟩) =
      (tautologicalSection J M
            (((componentOverMap f).sheafPushforwardContinuous (Type u)
              (componentwiseTopology J M) (componentwiseTopology J N)).obj W)).hom.app
          (op ⟨i, A⟩) ≫
        (formalCoproductSheafificationMap J f).hom.app
          (op ((componentOverForget M).obj ⟨i, A⟩))
  refine Eq.trans ((whisker_eq _ (relocalizationForgetPushforwardIso'_hom_app_hom_app J f
    (formalCoproductSheafification J N) i A)).trans (Category.comp_id _)) ?_
  ext w
  exact (congrArg
        (((sheafificationAdjunction J (Type u)).unit.app
          ((FormalCoproduct.yoneda (C := C)).obj N)).app (op A.left))
        (congrArg (fun m => m A.hom)
          (NatTrans.congr_app (Sigma.ι_desc (fun j => yoneda.map (f.φ j) ≫
            Sigma.ι (fun j : N.I => yoneda.obj (N.obj j)) (f.f j)) i) (op A.left))).symm).trans
    (congrArg
      (fun m => m ((Limits.Sigma.ι (fun j : M.I => yoneda.obj (M.obj j)) i).app
        (op A.left) A.hom))
      (NatTrans.congr_app ((sheafificationAdjunction J (Type u)).unit.naturality
        ((FormalCoproduct.yoneda (C := C)).map f)) (op A.left)))

/-- **Stacks 0D87 part (2) is natural in the semi-representable object, on the `F(-)^♯` factor.**
For a morphism `f : M ⟶ N` of semi-representable objects the shriek restriction transition
`j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` is carried by the two instances of Stacks 0D87 part (2) to
`F(f)^♯` on the sheafified-object factor: that is, the `snd` halves of the naturality square
agree.

Both projections are adjuncts of tautological sections
(`sheafPushforwardCompSheafPullbackIso_hom_app_snd`), so this is
`Stacks.CategoryTheory.shriekTransition_comp_constant` at the two of them; the hypothesis it needs
is `componentOverMap_tautologicalSection`. -/
theorem shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso_snd
    (X : Sheaf J (Type u)) :
    (shriekRestrictionTransition J f (componentwiseTopology J M) (componentwiseTopology J N)
          (Type u)).app X ≫
        (sheafPushforwardCompSheafPullbackIso J N).hom.app X ≫
          snd X (formalCoproductSheafification J N) =
      ((sheafPushforwardCompSheafPullbackIso J M).hom.app X ≫
          snd X (formalCoproductSheafification J M)) ≫
        formalCoproductSheafificationMap J f := by
  rw [sheafPushforwardCompSheafPullbackIso_hom_app_snd,
    sheafPushforwardCompSheafPullbackIso_hom_app_snd]
  exact Stacks.CategoryTheory.shriekTransition_comp_constant
    (relocalizationForgetPushforwardIso' J f (componentwiseTopology J M)
      (componentwiseTopology J N) (Type u))
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget N)
      (Type u) (componentwiseTopology J N) J)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverForget M)
      (Type u) (componentwiseTopology J M) J)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (componentOverMap f)
      (Type u) (componentwiseTopology J M) (componentwiseTopology J N))
    (formalCoproductSheafificationMap J f)
    (tautologicalSection J N) (tautologicalSection J M)
    (fun {_ _} m => comp_tautologicalSection J N m)
    (fun {_ _} m => comp_tautologicalSection J M m)
    (componentOverMap_tautologicalSection J f) X

/-- **Stacks 0D87 part (2) is natural in the semi-representable object.** For `f : M ⟶ N` the
shriek restriction transition `j_{M!}j_M^{-1} ⟶ j_{N!}j_N^{-1}` is carried by the two instances of
Stacks 0D87 part (2) to `G ⊗ F(f)^♯`.

A map into `G ⊗ F(K)^♯` is its two projections, and those are
`shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso_fst` and
`shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso_snd`, exactly as
`CategoryTheory.SemiRepresentable.overShriekTransition_comp_overShriekOverPullbackNatIso_app`
assembles the one-object case from `CategoryTheory.Limits.prod.hom_ext`. -/
theorem shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso
    (X : Sheaf J (Type u)) :
    (shriekRestrictionTransition J f (componentwiseTopology J M) (componentwiseTopology J N)
          (Type u)).app X ≫
        (sheafPushforwardCompSheafPullbackIso J N).hom.app X =
      (sheafPushforwardCompSheafPullbackIso J M).hom.app X ≫
        X ◁ formalCoproductSheafificationMap J f := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso_fst J f X).trans
        ((congrArg (fun m => (sheafPushforwardCompSheafPullbackIso J M).hom.app X ≫ m)
            (whiskerLeft_fst X (formalCoproductSheafificationMap J f)).symm).trans
          (Category.assoc _ _ _).symm))
  · exact (Category.assoc _ _ _).trans
      ((shriekRestrictionTransition_comp_sheafPushforwardCompSheafPullbackIso_snd J f X).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun m => (sheafPushforwardCompSheafPullbackIso J M).hom.app X ≫ m)
              (whiskerLeft_snd X (formalCoproductSheafificationMap J f)).symm).trans
            (Category.assoc _ _ _).symm)))

end Naturality

end CategoryTheory.SemiRepresentable

end
