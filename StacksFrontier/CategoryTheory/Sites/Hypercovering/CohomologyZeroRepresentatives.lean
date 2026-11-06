module

public import StacksFrontier.CategoryTheory.Limits.FormalCoproductBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.PresheafObjects
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PresheafCohomologyComparison
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence

/-!
# Representing cohomology classes on hypercoverings

Let `C` be a site with fibre products and equalizers and let `F` be an abelian sheaf on `C`.
[Stacks, Tag 09VZ] says that every degree-zero cohomology class of `F` is the image of a Čech
class on some hypercovering of the final presheaf, and that two Čech classes with the same image
agree after passing to a common refinement.  This file contains the ingredients of the degree-zero
case: morphisms of hypercoverings of a presheaf and the Čech pullback they induce, common
refinements by degreewise products, the naturality of the comparison of [Stacks, Tag 01GX] in the
hypercovering, and the degree-zero part of the acyclicity isomorphism of [Stacks, Tag 01GE].

## Main definitions

* `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.Hom`: a morphism of hypercoverings of a
  presheaf, i.e. a morphism of the underlying simplicial semi-representable objects compatible
  with the augmentations.
* `Stacks.CategoryTheory.Hypercovering.HypercoveringOf.Hom.cechCohomologyMap`: the restriction map
  on Čech cohomology induced by a morphism of hypercoverings of a presheaf.
* `Stacks.CategoryTheory.Hypercovering.prodSimplicial`, with `prodSimplicialFst` and
  `prodSimplicialSnd`: the degreewise product of two simplicial semi-representable objects and
  its two projections.
* `Stacks.CategoryTheory.Hypercovering.prodHypercovering`: the degreewise product of two
  hypercoverings of the final presheaf, again a hypercovering.
* `Stacks.CategoryTheory.Hypercovering.homOfSimplicialHom`: a morphism of the underlying
  simplicial objects, read as a morphism of hypercoverings of the final presheaf.

## Main results

* `Stacks.CategoryTheory.Hypercovering.sectionEquiv_map` and
  `Stacks.CategoryTheory.Hypercovering.sectionEquiv_restrict`: read through `sectionEquiv`, the
  map of presheaves induced by a morphism is postcomposition with it, and restriction along a
  morphism of the site is precomposition with it.
* `Stacks.CategoryTheory.Hypercovering.exists_hom_of_prod`: any two hypercoverings of the final
  presheaf are refined by a common one, namely their degreewise product.
* `Stacks.CategoryTheory.Hypercovering.mem_coverings_ofArrows_id`: the identity covering of an
  object, indexed by a one-element type in an arbitrary universe, is a covering.
* `sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees_hom_eq`, in the namespace
  `CategoryTheory.SimplicialObject.Augmented`: the abstract degree-zero isomorphism of
  [Stacks, Tag 01GE] is the one induced by the degree-zero augmentation.

## References

* [Stacks Project, Tag 09VV](https://stacks.math.columbia.edu/tag/09VV)
* [Stacks Project, Tag 09VY](https://stacks.math.columbia.edu/tag/09VY)
* [Stacks Project, Tag 09VZ](https://stacks.math.columbia.edu/tag/09VZ)
* [Stacks Project, Tag 01GI](https://stacks.math.columbia.edu/tag/01GI)
* [Stacks Project, Tag 0DAX](https://stacks.math.columbia.edu/tag/0DAX)
-/

@[expose] public section

universe q w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

/-! ### The degree-zero part of the Tag 01GE isomorphism -/

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- **The abstract degree-zero isomorphism of [Stacks, Tag 01GE] is the one induced by the
augmentation.**  The isomorphism `sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees` is the
degree-zero augmentation `freeAbelianSheafAugZero`, descended through `opcycles` and restricted
along `homologyι`. -/
lemma sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees_hom_eq
    (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type w))
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A)) :
    (sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees J A h₀ h₁).hom =
      ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).homologyι 0 ≫
        ((SimplicialObject.freeAbelianSheafComplexFunctor J).obj A.left).descOpcycles
          (freeAbelianSheafAugZero J A) 1 (by simp)
          (d_comp_freeAbelianSheafAugZero J A 1) := by
  have hLHS : (sheafHomologyZeroIso_of_isLocallySurjective_lowDegrees J A h₀ h₁).hom =
      HomologicalComplex.homologyMap
          ((SimplicialObject.freeAbelianSheafComplexFunctor J).map
            ((SimplicialObject.coskAdj 1).unit.app A.left)) 0 ≫
        HomologicalComplex.homologyMap
            ((SimplicialObject.freeAbelianSheafComplexFunctor J).map
              (coskOneToCechNerve A)) 0 ≫
          Presheaf.cechNerveSheafHomologyZeroAugmentation J
            (A.hom.app (op (SimplexCategory.mk 0))) := rfl
  rw [hLHS, descOpcycles_freeAbelianSheafAugZero_eq J A,
    Presheaf.cechNerveSheafHomologyZeroAugmentation_eq_homologyι_descOpcycles J
      (A.hom.app (op (SimplexCategory.mk 0)))
      (cechNerveSheafAugmentation_f_zero_eq J (A.hom.app (op (SimplexCategory.mk 0)))) 1
      (by simp)
      (Presheaf.d_comp_cechNerveSheafAugmentation_f_zero J
        (A.hom.app (op (SimplexCategory.mk 0)))
        (cechNerveSheafAugmentation_f_zero_eq J
          (A.hom.app (op (SimplexCategory.mk 0)))) 1),
    ← HomologicalComplex.homologyι_naturality_assoc,
    ← HomologicalComplex.homologyι_naturality_assoc]

end CategoryTheory.SimplicialObject.Augmented

namespace Stacks.CategoryTheory.Hypercovering

/-! ### Sections of the presheaf of a semi-representable object -/

section Sections

variable {C : Type u} [Category.{v} C]

/-- `associatedPresheafFunctor` applied to a morphism, read through `sectionEquiv`, is
composition with that morphism. -/
lemma sectionEquiv_map {X Y : FormalCoproduct.{w} C} (U : C) (f : X ⟶ Y)
    (z : ((associatedPresheafFunctor.{v}).obj X).obj (op U)) :
    sectionEquiv Y U (((associatedPresheafFunctor.{v}).map f).app (op U) z) =
      sectionEquiv X U z ≫ f := by
  apply (sectionEquiv Y U).symm.injective
  rw [Equiv.symm_apply_apply, sectionEquiv_symm_postcomp, Equiv.symm_apply_apply]

/-- Restricting a section along a morphism of the site, read through `sectionEquiv`, is
precomposition with that morphism. -/
lemma sectionEquiv_restrict (X : FormalCoproduct.{w} C) {U V : C} (k : V ⟶ U)
    (z : ((associatedPresheafFunctor.{v}).obj X).obj (op U)) :
    sectionEquiv X V (((associatedPresheafFunctor.{v}).obj X).map k.op z) =
      (FormalCoproduct.incl C).map k ≫ sectionEquiv X U z := by
  apply (sectionEquiv X V).symm.injective
  rw [Equiv.symm_apply_apply, sectionEquiv_symm_precomp, Equiv.symm_apply_apply]

/-! ### The degreewise product of two hypercoverings of the final presheaf -/

/-- The augmentation target of a hypercovering of the final presheaf is terminal. -/
noncomputable def isTerminal_liftedTerminal :
    IsTerminal (liftedPresheaf.{v, w} (⊤_ (Cᵒᵖ ⥤ Type v)) : Cᵒᵖ ⥤ Type (max v w)) :=
  terminalIsTerminal.isTerminalObj
    ((Functor.whiskeringRight Cᵒᵖ (Type v) (Type (max v w))).obj uliftFunctor.{max w v, v}) _

/-- Sections of the augmentation target over any object form a subsingleton. -/
lemma subsingleton_liftedTerminal (V : C) :
    Subsingleton ((liftedPresheaf.{v, w} (⊤_ (Cᵒᵖ ⥤ Type v))).obj (op V)) :=
  ((Types.isTerminalEquivUnique
    ((liftedPresheaf.{v, w} (⊤_ (Cᵒᵖ ⥤ Type v))).obj (op V)))
    (IsTerminal.isTerminalObj ((evaluation Cᵒᵖ (Type (max v w))).obj (op V)) _
      isTerminal_liftedTerminal.{w})).instSubsingleton

/-! ### The degreewise product of two simplicial semi-representable objects -/

section Product

variable [HasBinaryProducts C]

/-- The degreewise product of two simplicial semi-representable objects. -/
@[simps]
noncomputable def prodSimplicial (K L : SimplicialObject (FormalCoproduct.{w} C)) :
    SimplicialObject (FormalCoproduct.{w} C) where
  obj n := K.obj n ⨯ L.obj n
  map f := prod.map (K.map f) (L.map f)
  map_id n := by simp
  map_comp f g := by simp

/-- The first projection of the degreewise product. -/
@[simps]
noncomputable def prodSimplicialFst (K L : SimplicialObject (FormalCoproduct.{w} C)) :
    prodSimplicial.{w} K L ⟶ K where
  app _ := prod.fst
  naturality _ _ _ := by simp [prodSimplicial]

/-- The second projection of the degreewise product. -/
@[simps]
noncomputable def prodSimplicialSnd (K L : SimplicialObject (FormalCoproduct.{w} C)) :
    prodSimplicial.{w} K L ⟶ L where
  app _ := prod.snd
  naturality _ _ _ := by simp [prodSimplicial]

open SimplicialObject in
/-- The two coskeleton projections of a degreewise product are jointly monic in every degree. -/
lemma coskeleton_prod_hom_ext (K L : SimplicialObject (FormalCoproduct.{w} C)) (n : ℕ)
    [∀ F : SimplicialObject.Truncated (FormalCoproduct.{w} C) n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (r : SimplexCategoryᵒᵖ) {Z : FormalCoproduct.{w} C}
    {a b : Z ⟶ ((cosk n).obj (prodSimplicial.{w} K L)).obj r}
    (hfst : a ≫ ((cosk n).map (prodSimplicialFst.{w} K L)).app r =
      b ≫ ((cosk n).map (prodSimplicialFst.{w} K L)).app r)
    (hsnd : a ≫ ((cosk n).map (prodSimplicialSnd.{w} K L)).app r =
      b ≫ ((cosk n).map (prodSimplicialSnd.{w} K L)).app r) :
    a = b := by
  refine (matchingIsLimit (prodSimplicial.{w} K L) n r).hom_ext fun j ↦ ?_
  apply prod.hom_ext
  · have e : ∀ c : Z ⟶ ((cosk n).obj (prodSimplicial.{w} K L)).obj r,
        (c ≫ (matchingCone (prodSimplicial.{w} K L) n r).π.app j) ≫ prod.fst =
          c ≫ ((cosk n).map (prodSimplicialFst.{w} K L)).app r ≫
            (matchingCone K n r).π.app j := by
      intro c
      rw [coskeleton_map_comp_matchingCone_π (prodSimplicialFst.{w} K L) n r j,
        ← Category.assoc]
      rfl
    refine (e a).trans (Eq.trans ?_ (e b).symm)
    rw [← Category.assoc, hfst, Category.assoc]
  · have e : ∀ c : Z ⟶ ((cosk n).obj (prodSimplicial.{w} K L)).obj r,
        (c ≫ (matchingCone (prodSimplicial.{w} K L) n r).π.app j) ≫ prod.snd =
          c ≫ ((cosk n).map (prodSimplicialSnd.{w} K L)).app r ≫
            (matchingCone L n r).π.app j := by
      intro c
      rw [coskeleton_map_comp_matchingCone_π (prodSimplicialSnd.{w} K L) n r j,
        ← Category.assoc]
      rfl
    refine (e a).trans (Eq.trans ?_ (e b).symm)
    rw [← Category.assoc, hsnd, Category.assoc]

end Product

end Sections

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]

/-! ### Morphisms of hypercoverings of a presheaf -/

/-- A morphism of hypercoverings of a presheaf `G`: a morphism of the underlying simplicial
semi-representable objects which is compatible with the two augmentations towards `G`. -/
structure HypercoveringOf.Hom {J : Pretopology C} {G : Cᵒᵖ ⥤ Type q}
    (K L : HypercoveringOf.{q, w} J G) where
  /-- The underlying morphism of simplicial semi-representable objects. -/
  simplicialHom : K.toSimplicialObject ⟶ L.toSimplicialObject
  /-- Compatibility of the underlying morphism with the augmentations. -/
  whiskerRight_comp_augmentation :
    Functor.whiskerRight simplicialHom associatedPresheafFunctor.{q} ≫ L.augmentation =
      K.augmentation

/-- The restriction map on Čech cohomology along a morphism of hypercoverings of a presheaf,
Čech cohomology being contravariant in the simplicial semi-representable object. -/
noncomputable def HypercoveringOf.Hom.cechCohomologyMap {J : Pretopology C} {G : Cᵒᵖ ⥤ Type q}
    {K L : HypercoveringOf.{q, w} J G} (ψ : K.Hom L)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (p : ℕ) :
    cechCohomology J G L F p ⟶ cechCohomology J G K F p :=
  HomologicalComplex.homologyMap
    ((cochainComplexFunctorMap.{w} ψ.simplicialHom).app F.obj) p

/-! ### Identity coverings -/

omit [HasEqualizers C] in
/-- The identity covering of an object, indexed by a one-element type in an arbitrary
universe. -/
theorem mem_coverings_ofArrows_id.{t} (J : Pretopology C) (U : C) :
    Presieve.ofArrows (fun _ : PUnit.{t + 1} ↦ U) (fun _ ↦ 𝟙 U) ∈ J U := by
  rw [Presieve.ofArrows_pUnit]
  exact J.has_isos (𝟙 U)

/-! ### Common refinements -/

section CommonRefinement

variable [HasBinaryProducts C]

/-- **Condition (1) for the degreewise product.**  The constituent objects of `K₀ ⨯ L₀` cover the
site as soon as those of `K₀` and of `L₀` do. -/
lemma locallySurjective_zero_prodSimplicial (J : Pretopology C)
    (K L : HypercoveringOfTerminal.{w} J)
    (aug : associatedSimplicialPresheaf.{v}
        (prodSimplicial.{w} K.toSimplicialObject L.toSimplicialObject) ⟶
      (SimplicialObject.const _).obj (liftedPresheaf.{v, w} (⊤_ (Cᵒᵖ ⥤ Type v)))) :
    Presheaf.IsLocallySurjective J.toGrothendieck (aug.app (op (SimplexCategory.mk 0))) := by
  have hK := K.locallySurjective_zero
  have hL := L.locallySurjective_zero
  refine ⟨fun {U} s => ?_⟩
  refine J.toGrothendieck.superset_covering ?_ (J.toGrothendieck.intersection_covering
    (Presheaf.imageSieve_mem J.toGrothendieck
      (K.augmentation.app (op (SimplexCategory.mk 0))) s)
    (Presheaf.imageSieve_mem J.toGrothendieck
      (L.augmentation.app (op (SimplexCategory.mk 0))) s))
  rintro V k ⟨⟨x, -⟩, ⟨y, -⟩⟩
  exact ⟨(sectionEquiv _ V).symm (prod.lift (sectionEquiv _ V x) (sectionEquiv _ V y)),
    @Subsingleton.elim _ (subsingleton_liftedTerminal.{w} (C := C) V) _ _⟩

/-- Postcomposing with the coskeleton of a morphism `Φ` only sees the part of a map into the
coskeleton that is read off after the unit of `Φ`'s target. -/
private lemma comp_cosk_map_eq_of_unit_comp {C : Type u} [Category.{v} C] {n : ℕ}
    {P E : SimplicialObject C} [∀ F : SimplicialObject.Truncated C n,
      (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]
    (Φ : P ⟶ E) (r : SimplexCategoryᵒᵖ) {Z : C} (a : Z ⟶ P.obj r)
    {t : Z ⟶ ((SimplicialObject.cosk n).obj P).obj r}
    (h : (a ≫ Φ.app r) ≫ ((SimplicialObject.coskAdj n).unit.app E).app r =
      t ≫ ((SimplicialObject.cosk n).map Φ).app r) :
    (a ≫ ((SimplicialObject.coskAdj n).unit.app P).app r) ≫
        ((SimplicialObject.cosk n).map Φ).app r =
      t ≫ ((SimplicialObject.cosk n).map Φ).app r := by
  rw [Category.assoc, ← NatTrans.comp_app, ← (SimplicialObject.coskAdj n).unit.naturality Φ,
    NatTrans.comp_app, ← Category.assoc]
  exact h

/-- A morphism into a binary product is determined by its two components, here for a product of
maps. -/
private lemma lift_comp_map_eq_of_comp_eq {D : Type*} [Category D] [HasBinaryProducts D]
    {X A B A' B' : D} (a : X ⟶ A) (b : X ⟶ B) (f : A ⟶ A') (g : B ⟶ B') (u : X ⟶ A' ⨯ B')
    (h₁ : a ≫ f = u ≫ prod.fst) (h₂ : b ≫ g = u ≫ prod.snd) :
    prod.lift a b ≫ prod.map f g = u := by
  ext <;> simp [h₁, h₂]

open SimplicialObject in
/-- **Condition (3) for the degreewise product.**  For `n ≥ 1`, the higher matching map of the
degreewise product of `K` and `L` in degree `n` is locally surjective. -/
lemma locallySurjective_succ_prodSimplicial (J : Pretopology C)
    (K L : HypercoveringOfTerminal.{w} J) (n : ℕ) (hn : 1 ≤ n) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      (higherMatchingMap.{v}
        (prodSimplicial.{w} K.toSimplicialObject L.toSimplicialObject) n hn) := by
  let := hasPositiveCoskeleta.{w} (C := C) n hn
  have hK := K.locallySurjective_succ n hn
  have hL := L.locallySurjective_succ n hn
  rw [higherMatchingMap_eq] at hK hL ⊢
  refine ⟨fun {U} s => ?_⟩
  refine J.toGrothendieck.superset_covering ?_ (J.toGrothendieck.intersection_covering
    (Presheaf.imageSieve_mem J.toGrothendieck
      ((associatedPresheafFunctor.{v}).map (((coskAdj n).unit.app K.toSimplicialObject).app
        (op (SimplexCategory.mk (n + 1)))))
      ((sectionEquiv _ U).symm (sectionEquiv _ U s ≫
        ((cosk n).map (prodSimplicialFst.{w} K.toSimplicialObject
          L.toSimplicialObject)).app (op (SimplexCategory.mk (n + 1))))))
    (Presheaf.imageSieve_mem J.toGrothendieck
      ((associatedPresheafFunctor.{v}).map (((coskAdj n).unit.app L.toSimplicialObject).app
        (op (SimplexCategory.mk (n + 1)))))
      ((sectionEquiv _ U).symm (sectionEquiv _ U s ≫
        ((cosk n).map (prodSimplicialSnd.{w} K.toSimplicialObject
          L.toSimplicialObject)).app (op (SimplexCategory.mk (n + 1)))))))
  rintro V k ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  obtain ⟨z, hz⟩ : ∃ z, sectionEquiv
      ((prodSimplicial.{w} K.toSimplicialObject L.toSimplicialObject).obj
        (op (SimplexCategory.mk (n + 1)))) V z =
      prod.lift (sectionEquiv _ V x) (sectionEquiv _ V y) :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  refine ⟨z, ?_⟩
  apply (sectionEquiv _ V).injective
  refine (sectionEquiv_map V _ _).trans (Eq.trans ?_ (sectionEquiv_restrict _ k s).symm)
  simp only [Functor.id_obj]
  rw [hz]
  have hx' : sectionEquiv _ V x ≫ ((coskAdj n).unit.app K.toSimplicialObject).app
        (op (SimplexCategory.mk (n + 1))) =
      (FormalCoproduct.incl C).map k ≫ sectionEquiv _ U s ≫
        ((cosk n).map (prodSimplicialFst.{w} K.toSimplicialObject
          L.toSimplicialObject)).app (op (SimplexCategory.mk (n + 1))) := by
    have := congrArg (sectionEquiv _ V) hx
    rwa [sectionEquiv_map, sectionEquiv_restrict, Equiv.apply_symm_apply] at this
  have hy' : sectionEquiv _ V y ≫ ((coskAdj n).unit.app L.toSimplicialObject).app
        (op (SimplexCategory.mk (n + 1))) =
      (FormalCoproduct.incl C).map k ≫ sectionEquiv _ U s ≫
        ((cosk n).map (prodSimplicialSnd.{w} K.toSimplicialObject
          L.toSimplicialObject)).app (op (SimplexCategory.mk (n + 1))) := by
    have := congrArg (sectionEquiv _ V) hy
    rwa [sectionEquiv_map, sectionEquiv_restrict, Equiv.apply_symm_apply] at this
  apply coskeleton_prod_hom_ext.{w} K.toSimplicialObject L.toSimplicialObject n
    (op (SimplexCategory.mk (n + 1)))
  · refine comp_cosk_map_eq_of_unit_comp _ _ _ ?_
    refine (congrArg (· ≫ _) (prod.lift_fst _ _)).trans ?_
    exact hx'.trans (Category.assoc _ _ _).symm
  · refine comp_cosk_map_eq_of_unit_comp _ _ _ ?_
    refine (congrArg (· ≫ _) (prod.lift_snd _ _)).trans ?_
    exact hy'.trans (Category.assoc _ _ _).symm

omit [HasBinaryProducts C] in
/-- **Condition (2) of a hypercovering of the final presheaf, in terms of morphisms.**  Two
morphisms out of an object into the degree-zero term are, locally on a covering, the two faces of
a morphism into the degree-one term. -/
lemma exists_sieve_lift_pair (J : Pretopology C) (K : HypercoveringOfTerminal.{w} J) (U : C)
    (α β : (FormalCoproduct.incl C).obj U ⟶
      K.toSimplicialObject.obj (op (SimplexCategory.mk 0))) :
    ∃ S : Sieve U, S ∈ J.toGrothendieck U ∧ ∀ ⦃V : C⦄ (k : V ⟶ U), S k →
      ∃ ξ : (FormalCoproduct.incl C).obj V ⟶
          K.toSimplicialObject.obj (op (SimplexCategory.mk 1)),
        ξ ≫ K.toSimplicialObject.δ 0 = (FormalCoproduct.incl C).map k ≫ α ∧
          ξ ≫ K.toSimplicialObject.δ 1 = (FormalCoproduct.incl C).map k ≫ β := by
  have hone := K.locallySurjective_one
  set f0 := K.augmentation.app (op (SimplexCategory.mk 0)) with hf0
  set a' := uliftYonedaEquiv.{w}.symm ((sectionEquiv _ U).symm α) with ha'
  set b' := uliftYonedaEquiv.{w}.symm ((sectionEquiv _ U).symm β) with hb'
  have hcomm : a' ≫ f0 = b' ≫ f0 := isTerminal_liftedTerminal.{w}.hom_ext _ _
  set t := uliftYonedaEquiv.{w} (pullback.lift a' b' hcomm) with ht
  have htfst : (pullback.fst f0 f0).app (op U) t = (sectionEquiv _ U).symm α := by
    rw [ht, ← uliftYonedaEquiv_comp, pullback.lift_fst, ha', Equiv.apply_symm_apply]
  have htsnd : (pullback.snd f0 f0).app (op U) t = (sectionEquiv _ U).symm β := by
    rw [ht, ← uliftYonedaEquiv_comp, pullback.lift_snd, hb', Equiv.apply_symm_apply]
  refine ⟨Presheaf.imageSieve (oneMatchingMap (associatedSimplicialPresheaf.{v}
      K.toSimplicialObject) (liftedPresheaf.{v, w} (⊤_ (Cᵒᵖ ⥤ Type v)))
      K.augmentation) t, hone.imageSieve_mem t, ?_⟩
  rintro V k ⟨x, hx⟩
  refine ⟨sectionEquiv _ V x, ?_, ?_⟩
  · have h := congrArg ((pullback.fst f0 f0).app (op V)) hx
    rw [← types_comp_apply ((oneMatchingMap _ _ _).app (op V))
        ((pullback.fst f0 f0).app (op V)), ← NatTrans.comp_app, oneMatchingMap_fst] at h
    rw [NatTrans.naturality_apply, htfst] at h
    refine (sectionEquiv_map V _ x).symm.trans (Eq.trans (congrArg (sectionEquiv _ V) h) ?_)
    refine (sectionEquiv_restrict _ k _).trans ?_
    rw [Equiv.apply_symm_apply]
  · have h := congrArg ((pullback.snd f0 f0).app (op V)) hx
    rw [← types_comp_apply ((oneMatchingMap _ _ _).app (op V))
        ((pullback.snd f0 f0).app (op V)), ← NatTrans.comp_app, oneMatchingMap_snd] at h
    rw [NatTrans.naturality_apply, htsnd] at h
    refine (sectionEquiv_map V _ x).symm.trans (Eq.trans (congrArg (sectionEquiv _ V) h) ?_)
    refine (sectionEquiv_restrict _ k _).trans ?_
    rw [Equiv.apply_symm_apply]

/-- **Condition (2) for the degreewise product.**  The one-matching map of the degreewise product
of `K` and `L` is locally surjective. -/
lemma locallySurjective_one_prodSimplicial (J : Pretopology C)
    (K L : HypercoveringOfTerminal.{w} J)
    (aug : associatedSimplicialPresheaf.{v}
        (prodSimplicial.{w} K.toSimplicialObject L.toSimplicialObject) ⟶
      (SimplicialObject.const _).obj (liftedPresheaf.{v, w} (⊤_ (Cᵒᵖ ⥤ Type v)))) :
    Presheaf.IsLocallySurjective J.toGrothendieck
      (oneMatchingMap (associatedSimplicialPresheaf.{v}
        (prodSimplicial.{w} K.toSimplicialObject L.toSimplicialObject))
        (liftedPresheaf.{v, w} (⊤_ (Cᵒᵖ ⥤ Type v))) aug) := by
  refine ⟨fun {U} s => ?_⟩
  set f0 := aug.app (op (SimplexCategory.mk 0)) with hf0
  set α := sectionEquiv ((prodSimplicial.{w} K.toSimplicialObject L.toSimplicialObject).obj
    (op (SimplexCategory.mk 0))) U ((pullback.fst f0 f0).app (op U) s) with hα
  set β := sectionEquiv ((prodSimplicial.{w} K.toSimplicialObject L.toSimplicialObject).obj
    (op (SimplexCategory.mk 0))) U ((pullback.snd f0 f0).app (op U) s) with hβ
  obtain ⟨SK, hSK, hliftK⟩ := exists_sieve_lift_pair.{w} J K U (α ≫ prod.fst) (β ≫ prod.fst)
  obtain ⟨SL, hSL, hliftL⟩ := exists_sieve_lift_pair.{w} J L U (α ≫ prod.snd) (β ≫ prod.snd)
  refine J.toGrothendieck.superset_covering ?_
    (J.toGrothendieck.intersection_covering hSK hSL)
  rintro V k ⟨hk1, hk2⟩
  obtain ⟨ξK, hξK0, hξK1⟩ := hliftK k hk1
  obtain ⟨ξL, hξL0, hξL1⟩ := hliftL k hk2
  obtain ⟨z, hz⟩ : ∃ z, sectionEquiv ((prodSimplicial.{w} K.toSimplicialObject
      L.toSimplicialObject).obj (op (SimplexCategory.mk 1))) V z = prod.lift ξK ξL :=
    ⟨_, Equiv.apply_symm_apply _ _⟩
  refine ⟨z, ?_⟩
  apply presheaf_pullback_section_ext.{w} f0 f0 V
  · rw [← types_comp_apply ((oneMatchingMap _ _ _).app (op V)) ((pullback.fst f0 f0).app (op V)),
      ← NatTrans.comp_app, oneMatchingMap_fst, NatTrans.naturality_apply]
    apply (sectionEquiv _ V).injective
    refine (sectionEquiv_map V _ z).trans (Eq.trans ?_ (sectionEquiv_restrict _ k _).symm)
    rw [hz]
    exact lift_comp_map_eq_of_comp_eq _ _ _ _ _ (hξK0.trans (Category.assoc _ _ _).symm)
      (hξL0.trans (Category.assoc _ _ _).symm)
  · rw [← types_comp_apply ((oneMatchingMap _ _ _).app (op V)) ((pullback.snd f0 f0).app (op V)),
      ← NatTrans.comp_app, oneMatchingMap_snd, NatTrans.naturality_apply]
    apply (sectionEquiv _ V).injective
    refine (sectionEquiv_map V _ z).trans (Eq.trans ?_ (sectionEquiv_restrict _ k _).symm)
    rw [hz]
    exact lift_comp_map_eq_of_comp_eq _ _ _ _ _ (hξK1.trans (Category.assoc _ _ _).symm)
      (hξL1.trans (Category.assoc _ _ _).symm)

/-- **The degreewise product of two hypercoverings of the final presheaf is a hypercovering.**
This is the analogue for hypercoverings of the final presheaf of [Stacks, Tag 01GI]. -/
noncomputable def prodHypercovering (J : Pretopology C) (K L : HypercoveringOfTerminal.{w} J) :
    HypercoveringOfTerminal.{w} J where
  toSimplicialObject := prodSimplicial.{w} K.toSimplicialObject L.toSimplicialObject
  augmentation :=
    (Functor.isTerminalConst SimplexCategoryᵒᵖ isTerminal_liftedTerminal.{w}).from _
  locallySurjective_zero := locallySurjective_zero_prodSimplicial.{w} J K L _
  locallySurjective_one := locallySurjective_one_prodSimplicial.{w} J K L _
  locallySurjective_succ n hn := locallySurjective_succ_prodSimplicial.{w} J K L n hn

omit [HasBinaryProducts C] in
/-- A morphism of the underlying simplicial semi-representable objects is a morphism of
hypercoverings of the final presheaf. -/
def homOfSimplicialHom {J : Pretopology C} {K L : HypercoveringOfTerminal.{w} J}
    (f : K.toSimplicialObject ⟶ L.toSimplicialObject) : K.Hom L where
  simplicialHom := f
  whiskerRight_comp_augmentation :=
    (Functor.isTerminalConst SimplexCategoryᵒᵖ isTerminal_liftedTerminal.{w}).hom_ext _ _

/-- **Any two hypercoverings of the final presheaf admit a common refinement**: their degreewise
product, refining each of them through the corresponding projection. -/
theorem exists_hom_of_prod (J : Pretopology C) (K L : HypercoveringOfTerminal.{w} J) :
    ∃ M : HypercoveringOfTerminal.{w} J, Nonempty (M.Hom K) ∧ Nonempty (M.Hom L) :=
  ⟨prodHypercovering.{w} J K L,
    ⟨homOfSimplicialHom.{w}
      (prodSimplicialFst.{w} K.toSimplicialObject L.toSimplicialObject)⟩,
    ⟨homOfSimplicialHom.{w}
      (prodSimplicialSnd.{w} K.toSimplicialObject L.toSimplicialObject)⟩⟩

end CommonRefinement

end Stacks.CategoryTheory.Hypercovering

/-! ### [Stacks, Tag 01GX] is natural in the simplicial semi-representable object -/

namespace Stacks.CategoryTheory.Hypercovering.SemiRepresentable

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}]

omit [HasSheafify J AddCommGrpCat.{max (max u v) (max q w)}] in
/-- **The Čech pullback on the complexes of sections is restriction along the structure morphisms
of the morphism of simplicial semi-representable objects**, in the vocabulary of
`evalOpProductIso` and `CategoryTheory.Limits.Pi.π` that the comparison of [Stacks, Tag 01GX] is
stated in. -/
theorem pi_cochainComplexFunctorMap
    {E E' : SimplicialObject (FormalCoproduct.{w} C)} (ψ : E ⟶ E')
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (n : ℕ)
    (z : (sectionsComplex.{q, w, v, u} J E' F).X n) (i : (E.obj (op ⦋n⦌)).I) :
    ConcreteCategory.hom (Pi.π (fun l ↦ F.obj.obj (op ((E.obj (op ⦋n⦌)).obj l))) i)
        (ConcreteCategory.hom
          (evalOpProductIso.{q, w, v, u} (C := C) J (E.obj (op ⦋n⦌)) F).hom
          (ConcreteCategory.hom (((cochainComplexFunctorMap.{w} ψ).app F.obj).f n) z)) =
      ConcreteCategory.hom (F.obj.map ((ψ.app (op ⦋n⦌)).φ i).op)
        (ConcreteCategory.hom
          (Pi.π (fun l ↦ F.obj.obj (op ((E'.obj (op ⦋n⦌)).obj l))) ((ψ.app (op ⦋n⦌)).f i))
          (ConcreteCategory.hom
            (evalOpProductIso.{q, w, v, u} (C := C) J (E'.obj (op ⦋n⦌)) F).hom z)) := by
  change ConcreteCategory.hom
      (Pi.π (fun l ↦ F.obj.obj (op ((E.obj (op ⦋n⦌)).obj l))) i)
      (ConcreteCategory.hom (Pi.lift (fun l ↦
        Pi.π (fun m ↦ F.obj.obj (op ((E'.obj (op ⦋n⦌)).obj m))) ((ψ.app (op ⦋n⦌)).f l) ≫
          F.obj.map ((ψ.app (op ⦋n⦌)).φ l).op)) z) =
    ConcreteCategory.hom
      (Pi.π (fun m ↦ F.obj.obj (op ((E'.obj (op ⦋n⦌)).obj m))) ((ψ.app (op ⦋n⦌)).f i) ≫
        F.obj.map ((ψ.app (op ⦋n⦌)).φ i).op) z
  exact ConcreteCategory.congr_hom (Pi.lift_comp_π _ i) z

/-- **The degreewise comparison of [Stacks, Tag 01GX] is natural in the simplicial
semi-representable object**: the Čech pullback on sections corresponds to precomposition with the
free abelian sheaf of the degree-`n` component of the morphism. -/
theorem sectionsDegreeIso_naturality
    {E E' : SimplicialObject (FormalCoproduct.{w} C)} (ψ : E ⟶ E')
    (F : Sheaf J AddCommGrpCat.{max (max u v) (max q w)}) (n : ℕ) :
    ((cochainComplexFunctorMap.{w} ψ).app F.obj).f n ≫
        (sectionsDegreeIso.{q, w, v, u} (C := C) J E F n).hom =
      (sectionsDegreeIso.{q, w, v, u} (C := C) J E' F n).hom ≫
        (preadditiveYoneda.obj F).map
          ((((_root_.CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor J).map
            (Functor.whiskerRight ψ
              associatedPresheafFunctor.{max (max u v) (max q w)})).f n)).op := by
  refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
  have key : ConcreteCategory.hom (sectionsDegreeIso.{q, w, v, u} (C := C) J E F n).hom
        (ConcreteCategory.hom (((cochainComplexFunctorMap.{w} ψ).app F.obj).f n) z) =
      freeAbelianSheafMap.{q, w, v, u} (C := C) J (ψ.app (op ⦋n⦌)) ≫
        ConcreteCategory.hom
          (sectionsDegreeIso.{q, w, v, u} (C := C) J E' F n).hom z := by
    refine (sectionsEquiv.{q, w, v, u} (C := C) J (E.obj (op ⦋n⦌)) F).injective ?_
    refine (Concrete.productEquiv
      (fun l ↦ F.obj.obj (op ((E.obj (op ⦋n⦌)).obj l)))).injective (funext fun i ↦ ?_)
    rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply]
    refine Eq.trans ?_ (sectionsEquiv_naturality.{q, w, v, u} (C := C) J (ψ.app (op ⦋n⦌)) F
      (ConcreteCategory.hom
        (sectionsDegreeIso.{q, w, v, u} (C := C) J E' F n).hom z) i).symm
    refine Eq.trans (congrArg (ConcreteCategory.hom
        (Pi.π (fun l ↦ F.obj.obj (op ((E.obj (op ⦋n⦌)).obj l))) i))
      (sectionsEquiv_sectionsDegreeIso.{q, w, v, u} (C := C) J E F n
        (ConcreteCategory.hom (((cochainComplexFunctorMap.{w} ψ).app F.obj).f n) z))) ?_
    rw [sectionsEquiv_sectionsDegreeIso.{q, w, v, u} (C := C) J E' F n z]
    exact pi_cochainComplexFunctorMap.{q, w, v, u} J ψ F n z i
  exact (ConcreteCategory.comp_apply _ _ z).trans
    (key.trans (Eq.symm (ConcreteCategory.comp_apply _ _ z)))

/-- **[Stacks, Tag 01GX] is natural in the simplicial semi-representable object**, as an identity
of natural transformations of functors of the coefficient sheaf: the Čech pullback on the
complexes of sections corresponds to precomposition with the free abelian sheaves of the
morphism. -/
theorem sectionsComplexFunctorMap_comp_sectionsComplexFunctorIso
    {E E' : SimplicialObject (FormalCoproduct.{w} C)} (ψ : E ⟶ E') :
    Functor.whiskerLeft (sheafToPresheaf J AddCommGrpCat.{max (max u v) (max q w)})
          (cochainComplexFunctorMap.{w} ψ) ≫
        (sectionsComplexFunctorIsoHomComplexFunctor.{q, w, v, u} J E).hom =
      (sectionsComplexFunctorIsoHomComplexFunctor.{q, w, v, u} J E').hom ≫
        ChainComplex.homComplexFunctorPrecomp
          ((_root_.CategoryTheory.SimplicialObject.freeAbelianSheafComplexFunctor J).map
            (Functor.whiskerRight ψ
              associatedPresheafFunctor.{max (max u v) (max q w)})) :=
  NatTrans.ext (funext fun F ↦ HomologicalComplex.hom_ext _ _ fun n ↦
    sectionsDegreeIso_naturality.{q, w, v, u} J ψ F n)

end Stacks.CategoryTheory.Hypercovering.SemiRepresentable

/-! ### A morphism of hypercoverings as a morphism of augmented simplicial presheaves -/

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q)

/-- **A morphism of hypercoverings of `G` is a morphism of the augmented simplicial presheaves**,
with identity component at the augmentation points. -/
noncomputable def HypercoveringOf.Hom.toAugmentedHom {K L : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L) :
    K.toAugmented.{q, w, v, u} J G ⟶ L.toAugmented.{q, w, v, u} J G where
  left := Functor.whiskerRight ψ.simplicialHom associatedPresheafFunctor.{q}
  right := 𝟙 _
  w := ψ.whiskerRight_comp_augmentation.trans
    ((Category.comp_id K.augmentation).symm.trans
      (congrArg (fun t ↦ (K.toAugmented.{q, w, v, u} J G).hom ≫ t)
        (CategoryTheory.Functor.map_id (SimplicialObject.const (Cᵒᵖ ⥤ Type (max q w v)))
          (K.toAugmented.{q, w, v, u} J G).right).symm))

/-- The morphism `HypercoveringOf.Hom.toAugmentedHom` after the universe lift. -/
noncomputable def HypercoveringOf.Hom.toAugmentedULiftHom {K L : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L) :
    K.toAugmentedULift.{q, w, v, u} J G ⟶ L.toAugmentedULift.{q, w, v, u} J G :=
  (SimplicialObject.Augmented.whiskeringObj _ _
    (presheafULiftFunctor.{max q w v, max (max u v) (max q w)} (C := C))).map
      (ψ.toAugmentedHom J G)

/-- **The component of `HypercoveringOf.Hom.toAugmentedULiftHom` at the augmentation points is an
identity.** -/
@[simp]
lemma HypercoveringOf.Hom.toAugmentedULiftHom_right {K L : HypercoveringOf.{q, w} J G}
    (ψ : HypercoveringOf.Hom K L) :
    (ψ.toAugmentedULiftHom J G).right = 𝟙 _ := by
  dsimp only [HypercoveringOf.Hom.toAugmentedULiftHom,
    SimplicialObject.Augmented.whiskeringObj, HypercoveringOf.Hom.toAugmentedHom]
  exact CategoryTheory.Functor.map_id _ _

/-- **The two spellings of the simplicial presheaf of a hypercovering of `G` are identified
compatibly with a morphism of hypercoverings.** -/
theorem HypercoveringOf.Hom.toAugmentedULiftHom_left_comp_toAugmentedULiftLeftIso
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) :
    (ψ.toAugmentedULiftHom J G).left ≫
        (L.toAugmentedULiftLeftIso.{q, w, v, u} J G).hom =
      (K.toAugmentedULiftLeftIso.{q, w, v, u} J G).hom ≫
        Functor.whiskerRight ψ.simplicialHom
          associatedPresheafFunctor.{max (max u v) (max q w)} :=
  NatTrans.ext (funext fun r ↦
    (associatedPresheafFunctorULiftIso.{q, w, v, u} (C := C)).hom.naturality
      (ψ.simplicialHom.app r))

/-- **The map on sections over the augmentation points induced by a morphism of hypercoverings is
the identity.** -/
lemma HypercoveringOf.Hom.freeAbelianSheafSectionsPrecomp_toAugmentedULiftHom
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) :
    SimplicialObject.Augmented.freeAbelianSheafSectionsPrecomp J.toGrothendieck
        (ψ.toAugmentedULiftHom J G) =
      𝟙 (SimplicialObject.Augmented.freeAbelianSheafSections J.toGrothendieck
        (K.toAugmentedULift.{q, w, v, u} J G)) := by
  change preadditiveCoyoneda.map ((Presheaf.freeAbelianSheaf J.toGrothendieck).map
      (𝟙 ((K.toAugmentedULift.{q, w, v, u} J G).right))).op =
    𝟙 (SimplicialObject.Augmented.freeAbelianSheafSections J.toGrothendieck
      (K.toAugmentedULift.{q, w, v, u} J G))
  rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
  rfl

end Stacks.CategoryTheory.Hypercovering

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q)

variable [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]

/-- **[Stacks, Tag 01GX] for a hypercovering of a presheaf is natural in the hypercovering.**  The
Čech pullback along a morphism of hypercoverings corresponds, through the comparison, to
precomposition with the free abelian sheaves of the morphism of augmented simplicial presheaves. -/
theorem HypercoveringOf.Hom.sectionsComplexFunctorMap_comp_sectionsComplexIso
    {K L : HypercoveringOf.{q, w} J G} (ψ : HypercoveringOf.Hom K L) :
    Functor.whiskerLeft
          (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})
          (cochainComplexFunctorMap.{w} ψ.simplicialHom) ≫
        (sectionsComplexIsoFreeAbelianSheafHomCx.{q, w, v, u} J G K).hom =
      (sectionsComplexIsoFreeAbelianSheafHomCx.{q, w, v, u} J G L).hom ≫
        SimplicialObject.Augmented.freeAbelianSheafHomCxPrecomp J.toGrothendieck
          (ψ.toAugmentedULiftHom J G) := by
  have hmap : (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).map
          (ψ.toAugmentedULiftHom J G).left ≫
        (freeAbelianSheafComplexIsoOfToAugmentedULift.{q, w, v, u} J G L).hom =
      (freeAbelianSheafComplexIsoOfToAugmentedULift.{q, w, v, u} J G K).hom ≫
        (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).map
          (Functor.whiskerRight ψ.simplicialHom
            associatedPresheafFunctor.{max (max u v) (max q w)}) :=
    ((SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).map_comp _ _).symm.trans
      ((congrArg
          ((SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).map)
          (ψ.toAugmentedULiftHom_left_comp_toAugmentedULiftLeftIso J G)).trans
        ((SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).map_comp _ _))
  have hsq := ChainComplex.homComplexFunctorPrecomp_comp_homComplexFunctorIsoOfIso
    ((SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).map
      (ψ.toAugmentedULiftHom J G).left)
    ((SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).map
      (Functor.whiskerRight ψ.simplicialHom
        associatedPresheafFunctor.{max (max u v) (max q w)}))
    (freeAbelianSheafComplexIsoOfToAugmentedULift.{q, w, v, u} J G K)
    (freeAbelianSheafComplexIsoOfToAugmentedULift.{q, w, v, u} J G L) hmap
  change Functor.whiskerLeft
          (sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})
          (cochainComplexFunctorMap.{w} ψ.simplicialHom) ≫
      ((SemiRepresentable.sectionsComplexFunctorIsoHomComplexFunctor.{q, w, v, u}
            J.toGrothendieck K.toSimplicialObject).hom ≫
        (ChainComplex.homComplexFunctorIsoOfIso
          (freeAbelianSheafComplexIsoOfToAugmentedULift.{q, w, v, u} J G K)).hom) =
    ((SemiRepresentable.sectionsComplexFunctorIsoHomComplexFunctor.{q, w, v, u}
            J.toGrothendieck L.toSimplicialObject).hom ≫
        (ChainComplex.homComplexFunctorIsoOfIso
          (freeAbelianSheafComplexIsoOfToAugmentedULift.{q, w, v, u} J G L)).hom) ≫
      SimplicialObject.Augmented.freeAbelianSheafHomCxPrecomp J.toGrothendieck
        (ψ.toAugmentedULiftHom J G)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t ↦ t ≫ (ChainComplex.homComplexFunctorIsoOfIso
      (freeAbelianSheafComplexIsoOfToAugmentedULift.{q, w, v, u} J G K)).hom)
    (SemiRepresentable.sectionsComplexFunctorMap_comp_sectionsComplexFunctorIso
      J.toGrothendieck ψ.simplicialHom)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t ↦
    (SemiRepresentable.sectionsComplexFunctorIsoHomComplexFunctor.{q, w, v, u}
      J.toGrothendieck L.toSimplicialObject).hom ≫ t) hsq.symm) ?_
  exact (Category.assoc _ _ _).symm

end Stacks.CategoryTheory.Hypercovering

end
