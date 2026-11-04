module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.InverseImageCoherence

/-!
# The pseudofunctor of component sheaf categories (Stacks 09WF)

Stacks 09WF describes sheaves on the total site of a simplicial site as a lax section of a
pseudofunctor on the locally discrete bicategory `LocallyDiscrete SimplexCategory`, whose value
at `n` is the category of sheaves in simplicial degree `n` and whose value at a simplex map `φ`
is the inverse image of the induced morphism of topoi `f_φ`. The source says only "see the
discussion above": that this assignment *is* a pseudofunctor is the part it leaves implicit.

This file builds it. The three coherence axioms of
`CategoryTheory.LocallyDiscrete.mkPseudofunctor` are discharged from the coherence of the
inverse-image comparisons proved in
`StacksFrontier.CategoryTheory.Sites.Simplicial.InverseImageCoherence`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentPseudofunctor`: the pseudofunctor
  `LocallyDiscrete SimplexCategory ⥤ᵖ Cat.{u + 1, u + 1}` on the transported component sheaf
  categories, with `mapId` and `mapComp` the canonical comparisons `componentCatMapId` and
  `componentCatMapComp`. This is the `diagram` field of a `SimplicialSheafPresentation`.
* `CategoryTheory.SimplicialSiteSituation.componentPseudofunctorEquiv` and
  `.componentPseudofunctorTransitionIso`: the `componentEquivalence` and `transitionIso` fields
  of a `SimplicialSheafPresentation` for that pseudofunctor.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentCatMapComp_comp_id`,
  `_id_comp`, `_assoc`: the three coherence axioms, in the exact form
  `LocallyDiscrete.mkPseudofunctor` asks for.
* `CategoryTheory.SimplicialSiteSituation.componentPseudofunctor_identityComparison_isCanonical`
  and `.componentPseudofunctor_compositionComparison_isCanonical`: the two remaining
  constraints a `SimplicialSheafPresentation` puts on its diagram, namely that the unit and
  compositor of the pseudofunctor are the canonical inverse-image comparisons.

## Implementation notes

`componentCat` is `AsSmall` of the category of sheaves, and `componentCatMap`,
`componentCatMapId`, `componentCatMapComp` are the conjugates by `AsSmall.down`/`AsSmall.up` of
the inverse image and its two comparisons. Each axiom is therefore the conjugate of the
corresponding law of `InverseImageCoherence`, and the proofs all have the same three steps:
descend to a natural transformation with `Cat.Hom₂.ext`, then to a component with
`NatTrans.ext`, then out of `AsSmall` with `ULift.ext`. At that point the goal is
*definitionally* the component of the inverse-image law, so a `change` states it in the
law's own spelling — the conjugation is invisible to the kernel because the round trips of
`AsSmall` are definitional, but it is not syntactic, so `rw` and `simp only` cannot see
through it and `change` is what is needed.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Functor CategoryTheory.Bicategory

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- The right unit axiom of a pseudofunctor for the component sheaf categories. -/
theorem componentCatMapComp_comp_id {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentCatMapComp S φ (𝟙 n)).hom ≫
      componentCatMap S φ ◁ (componentCatMapId S n).hom ≫
        (ρ_ (componentCatMap S φ)).hom = eqToHom (by simp) := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  have hlaw := NatTrans.congr_app
    (congrArg Iso.hom (canonicalCompositionComparison_comp_id S φ)) (ULift.down X)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hlaw
  show (canonicalCompositionComparison S φ (𝟙 n)).hom.app (ULift.down X) ≫
      (canonicalIdentityComparison S n).hom.app
          ((S.transitionMorphism φ).inverseImage.obj (ULift.down X)) ≫
        𝟙 ((S.transitionMorphism φ).inverseImage.obj (ULift.down X)) = _
  rw [← hlaw, Iso.hom_inv_id_app_assoc]
  simp only [inverseImageCongr, eqToIso.hom, eqToHom_app, Cat.eqToHom_app]
  exact (eqToHom_down _).symm

/-- The left unit axiom of a pseudofunctor for the component sheaf categories. -/
theorem componentCatMapComp_id_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentCatMapComp S (𝟙 m) φ).hom ≫
      (componentCatMapId S m).hom ▷ componentCatMap S φ ≫
        (λ_ (componentCatMap S φ)).hom = eqToHom (by simp) := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  have hlaw := NatTrans.congr_app
    (congrArg Iso.hom (canonicalCompositionComparison_id_comp S φ)) (ULift.down X)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hlaw
  show (canonicalCompositionComparison S (𝟙 m) φ).hom.app (ULift.down X) ≫
      (S.transitionMorphism φ).inverseImage.map
          ((canonicalIdentityComparison S m).hom.app (ULift.down X)) ≫
        𝟙 ((S.transitionMorphism φ).inverseImage.obj (ULift.down X)) = _
  rw [← hlaw, Iso.hom_inv_id_app_assoc]
  simp only [inverseImageCongr, eqToIso.hom, eqToHom_app, Cat.eqToHom_app]
  exact (eqToHom_down _).symm

/-- The associativity axiom of a pseudofunctor for the component sheaf categories. -/
theorem componentCatMapComp_assoc {k l m n : SimplexCategory}
    (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n) :
    (componentCatMapComp S (χ ≫ ψ) φ).hom ≫
        (componentCatMapComp S χ ψ).hom ▷ componentCatMap S φ ≫
          (α_ (componentCatMap S χ) (componentCatMap S ψ) (componentCatMap S φ)).hom ≫
            componentCatMap S χ ◁ (componentCatMapComp S ψ φ).inv ≫
              (componentCatMapComp S χ (ψ ≫ φ)).inv = eqToHom (by simp) := by
  apply Cat.Hom₂.ext
  apply NatTrans.ext
  funext X
  apply ULift.ext
  have hlaw := NatTrans.congr_app
    (congrArg Iso.hom (canonicalCompositionComparison_assoc S χ ψ φ)) (ULift.down X)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.id_comp] at hlaw
  show (canonicalCompositionComparison S (χ ≫ ψ) φ).hom.app (ULift.down X) ≫
      (S.transitionMorphism φ).inverseImage.map
          ((canonicalCompositionComparison S χ ψ).hom.app (ULift.down X)) ≫
        𝟙 _ ≫
          (canonicalCompositionComparison S ψ φ).inv.app
              ((S.transitionMorphism χ).inverseImage.obj (ULift.down X)) ≫
            (canonicalCompositionComparison S χ (ψ ≫ φ)).inv.app (ULift.down X) = _
  rw [Category.id_comp, hlaw, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_app_assoc]
  simp only [inverseImageCongr, eqToIso.hom, eqToHom_app, Cat.eqToHom_app]
  exact (eqToHom_down _).symm

/-- **Stacks 09WF**, the pseudofunctoriality the source leaves implicit: the assignment sending
a simplicial degree to its category of sheaves and a simplex map `φ` to the inverse image of
the induced morphism of topoi `f_φ` is a pseudofunctor, with unit and compositor the canonical
comparisons. -/
noncomputable def componentPseudofunctor :
    LocallyDiscrete SimplexCategory ⥤ᵖ Cat.{u + 1, u + 1} :=
  LocallyDiscrete.mkPseudofunctor (componentCat S) (componentCatMap S) (componentCatMapId S)
    (componentCatMapComp S)
    (fun χ ψ φ => componentCatMapComp_assoc S χ ψ φ)
    (fun φ => componentCatMapComp_id_comp S φ)
    (fun φ => componentCatMapComp_comp_id S φ)

/-- The fibre of the pseudofunctor in simplicial degree `n` is the category of sheaves in that
degree. This is the `componentEquivalence` field of `SimplicialSheafPresentation`. -/
noncomputable def componentPseudofunctorEquiv (n : SimplexCategory) :
    (componentPseudofunctor S).obj ⟨n⟩ ≌ Sheaf (S.componentTopology n) (Type u) :=
  componentCatEquiv S n

/-- The transition functor of the pseudofunctor is, under the identification of its fibres with
the categories of sheaves, the inverse image of the induced morphism of topoi. This is the
`transitionIso` field of `SimplicialSheafPresentation`, and it is an identity: the transition
functor is the inverse image conjugated by `AsSmall`, and the identification of the fibres is
`AsSmall.down`. -/
noncomputable def componentPseudofunctorTransitionIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((componentPseudofunctor S).map ⟨φ⟩).toFunctor ⋙ (componentPseudofunctorEquiv S n).functor ≅
      (componentPseudofunctorEquiv S m).functor ⋙ (S.transitionMorphism φ).inverseImage :=
  Iso.refl _

/-- The unit of the pseudofunctor is the canonical inverse-image unit comparison. This is the
`identityComparison_isCanonical` field of `SimplicialSheafPresentation`. -/
theorem componentPseudofunctor_identityComparison_isCanonical (n : SimplexCategory)
    (X : (componentPseudofunctor S).obj ⟨n⟩) :
    (componentPseudofunctorTransitionIso S (𝟙 n)).hom.app X ≫
        (canonicalIdentityComparison S n).hom.app
          ((componentPseudofunctorEquiv S n).functor.obj X) =
      (componentPseudofunctorEquiv S n).functor.map
        (((componentPseudofunctor S).mapId ⟨n⟩).hom.toNatTrans.app X) := by
  simp only [componentPseudofunctorTransitionIso, Iso.refl_hom, NatTrans.id_app]
  rfl

/-- The compositor of the pseudofunctor is the canonical inverse-image compositor. This is the
`compositionComparison_isCanonical` field of `SimplicialSheafPresentation`. -/
theorem componentPseudofunctor_compositionComparison_isCanonical {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) (X : (componentPseudofunctor S).obj ⟨l⟩) :
    (componentPseudofunctorEquiv S n).functor.map
          (((componentPseudofunctor S).mapComp ⟨ψ⟩ ⟨φ⟩).hom.toNatTrans.app X) ≫
        (componentPseudofunctorTransitionIso S φ).hom.app
            (((componentPseudofunctor S).map ⟨ψ⟩).toFunctor.obj X) ≫
          (S.transitionMorphism φ).inverseImage.map
            ((componentPseudofunctorTransitionIso S ψ).hom.app X) =
      (componentPseudofunctorTransitionIso S (ψ ≫ φ)).hom.app X ≫
        (canonicalCompositionComparison S ψ φ).hom.app
          ((componentPseudofunctorEquiv S l).functor.obj X) := by
  show (canonicalCompositionComparison S ψ φ).hom.app (ULift.down X) ≫ 𝟙 _ ≫
      (S.transitionMorphism φ).inverseImage.map (𝟙 _) =
    𝟙 _ ≫ (canonicalCompositionComparison S ψ φ).hom.app (ULift.down X)
  simp

end CategoryTheory.SimplicialSiteSituation

end
