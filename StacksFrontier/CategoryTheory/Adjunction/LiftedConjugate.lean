module

public import StacksFrontier.CategoryTheory.Adjunction.PushedForwardTwistedBaseChange
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.PushPullNaturality

/-!
# Conjugates of adjunctions lifted to full subcategories

An adjunction `L ⊣ R` whose functors carry full subcategories into each other restricts to an
adjunction between them. For four such restricted adjunctions around a square, the comparison of
the composite right adjoints is computed on underlying objects by the ambient conjugate.

## Main results

* `CategoryTheory.ObjectProperty.restrictFullyFaithful_lift_counit_app_hom` — the counit of an
  adjunction restricted to full subcategories has the ambient counit as underlying morphism.
* `CategoryTheory.ObjectProperty.eq_conjugateEquiv_restrict_comp` — a transformation of the
  lifted composite right adjoints whose components are those of the ambient conjugate of `α` is
  the conjugate, for the restricted adjunctions, of the lift of `α`.
* `CategoryTheory.ObjectProperty.map_restrictFullyFaithful_hom` — the base change map of
  adjunctions restricted to full subcategories has the ambient base change map as underlying
  morphism.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.ObjectProperty

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]
  {P₁ : ObjectProperty C₁} {P₂ : ObjectProperty C₂} {P₃ : ObjectProperty C₃}
  {P₄ : ObjectProperty C₄}

/-- The counit of an adjunction restricted to full subcategories along its lifts has the counit
of the ambient adjunction as underlying morphism. -/
theorem restrictFullyFaithful_lift_counit_app_hom {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : L ⊣ R)
    (hL : ∀ X : P₁.FullSubcategory, P₂ ((P₁.ι ⋙ L).obj X))
    (hR : ∀ Y : P₂.FullSubcategory, P₁ ((P₂.ι ⋙ R).obj Y)) (Y : P₂.FullSubcategory) :
    ((adj.restrictFullyFaithful P₁.fullyFaithfulι P₂.fullyFaithfulι
      (P₂.liftCompιIso _ hL).symm (P₁.liftCompιIso _ hR).symm).counit.app Y).hom =
      adj.counit.app Y.obj := by
  have h := Adjunction.map_restrictFullyFaithful_counit_app adj P₁.fullyFaithfulι
    P₂.fullyFaithfulι (P₂.liftCompιIso _ hL).symm (P₁.liftCompιIso _ hR).symm Y
  exact h.trans (by simp [liftCompιIso])

variable {Lf : C₁ ⥤ C₂} {Rf : C₂ ⥤ C₁} {Lf' : C₃ ⥤ C₄} {Rf' : C₄ ⥤ C₃}
  {Lg : C₁ ⥤ C₃} {Rg : C₃ ⥤ C₁} {Lg' : C₂ ⥤ C₄} {Rg' : C₄ ⥤ C₂}
  (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg')
  (hLf : ∀ X : P₁.FullSubcategory, P₂ ((P₁.ι ⋙ Lf).obj X))
  (hRf : ∀ Y : P₂.FullSubcategory, P₁ ((P₂.ι ⋙ Rf).obj Y))
  (hLf' : ∀ X : P₃.FullSubcategory, P₄ ((P₃.ι ⋙ Lf').obj X))
  (hRf' : ∀ Y : P₄.FullSubcategory, P₃ ((P₄.ι ⋙ Rf').obj Y))
  (hLg : ∀ X : P₁.FullSubcategory, P₃ ((P₁.ι ⋙ Lg).obj X))
  (hRg : ∀ Y : P₃.FullSubcategory, P₁ ((P₃.ι ⋙ Rg).obj Y))
  (hLg' : ∀ X : P₂.FullSubcategory, P₄ ((P₂.ι ⋙ Lg').obj X))
  (hRg' : ∀ Y : P₄.FullSubcategory, P₂ ((P₄.ι ⋙ Rg').obj Y))

/-- **Conjugates of four restricted adjunctions around a square.** A transformation `τ` of the
lifted composite right adjoints whose components are those of the ambient conjugate of `α`, for a
lift `β` of `α`, is the conjugate of `β` for the restricted adjunctions. -/
theorem eq_conjugateEquiv_restrict_comp
    (α : Lg ⋙ Lf' ⟶ Lf ⋙ Lg')
    (β : P₃.lift (P₁.ι ⋙ Lg) hLg ⋙ P₄.lift (P₃.ι ⋙ Lf') hLf' ⟶
      P₂.lift (P₁.ι ⋙ Lf) hLf ⋙ P₄.lift (P₂.ι ⋙ Lg') hLg')
    (hβ : ∀ X, (β.app X).hom = α.app X.obj)
    (τ : P₂.lift (P₄.ι ⋙ Rg') hRg' ⋙ P₁.lift (P₂.ι ⋙ Rf) hRf ⟶
      P₃.lift (P₄.ι ⋙ Rf') hRf' ⋙ P₁.lift (P₃.ι ⋙ Rg) hRg)
    (hτ : ∀ d, (τ.app d).hom = (conjugateEquiv (af.comp ag') (ag.comp af') α).app d.obj) :
    τ = conjugateEquiv
      ((af.restrictFullyFaithful P₁.fullyFaithfulι P₂.fullyFaithfulι
          (P₂.liftCompιIso _ hLf).symm (P₁.liftCompιIso _ hRf).symm).comp
        (ag'.restrictFullyFaithful P₂.fullyFaithfulι P₄.fullyFaithfulι
          (P₄.liftCompιIso _ hLg').symm (P₂.liftCompιIso _ hRg').symm))
      ((ag.restrictFullyFaithful P₁.fullyFaithfulι P₃.fullyFaithfulι
          (P₃.liftCompιIso _ hLg).symm (P₁.liftCompιIso _ hRg).symm).comp
        (af'.restrictFullyFaithful P₃.fullyFaithfulι P₄.fullyFaithfulι
          (P₄.liftCompιIso _ hLf').symm (P₃.liftCompιIso _ hRf').symm)) β := by
  refine Stacks.CategoryTheory.eq_conjugateEquiv _ _ _ _ fun d => ?_
  apply ObjectProperty.hom_ext
  have h := conjugateEquiv_counit (af.comp ag') (ag.comp af') α d.obj
  rw [← hτ] at h
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] at h
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj,
    FullSubcategory.comp_hom, hβ]
  change Lf'.map (Lg.map (τ.app d).hom) ≫ Lf'.map ((ag.restrictFullyFaithful P₁.fullyFaithfulι
      P₃.fullyFaithfulι (P₃.liftCompιIso _ hLg).symm (P₁.liftCompιIso _ hRg).symm).counit.app
        ((P₃.lift (P₄.ι ⋙ Rf') hRf').obj d)).hom ≫
      ((af'.restrictFullyFaithful P₃.fullyFaithfulι P₄.fullyFaithfulι
        (P₄.liftCompιIso _ hLf').symm (P₃.liftCompιIso _ hRf').symm).counit.app d).hom =
    α.app _ ≫ Lg'.map ((af.restrictFullyFaithful P₁.fullyFaithfulι P₂.fullyFaithfulι
      (P₂.liftCompιIso _ hLf).symm (P₁.liftCompιIso _ hRf).symm).counit.app
        ((P₂.lift (P₄.ι ⋙ Rg') hRg').obj d)).hom ≫
      ((ag'.restrictFullyFaithful P₂.fullyFaithfulι P₄.fullyFaithfulι
        (P₄.liftCompιIso _ hLg').symm (P₂.liftCompιIso _ hRg').symm).counit.app d).hom
  rw [restrictFullyFaithful_lift_counit_app_hom, restrictFullyFaithful_lift_counit_app_hom,
    restrictFullyFaithful_lift_counit_app_hom, restrictFullyFaithful_lift_counit_app_hom]
  exact h

/-- **The base change map of restricted adjunctions is the ambient one.** For adjunctions
`Lf ⊣ Rf` and `Lf' ⊣ Rf'` restricted to full subcategories, and identifications of the composites
around the square whose comparison has the ambient components, the base change map of the
restricted adjunctions has the underlying morphism of the ambient base change map. -/
theorem map_restrictFullyFaithful_hom {Lc : C₁ ⥤ C₄} (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    {Lc' : P₁.FullSubcategory ⥤ P₄.FullSubcategory}
    (eg' : P₃.lift (P₁.ι ⋙ Lg) hLg ⋙ P₄.lift (P₃.ι ⋙ Lf') hLf' ≅ Lc')
    (ef' : P₂.lift (P₁.ι ⋙ Lf) hLf ⋙ P₄.lift (P₂.ι ⋙ Lg') hLg' ≅ Lc')
    (h : ∀ X, ((eg'.hom ≫ ef'.inv).app X).hom = (eg.hom ≫ ef.inv).app X.obj)
    (K : P₂.FullSubcategory) :
    (Stacks.CategoryTheory.BaseChange.map
      (af.restrictFullyFaithful P₁.fullyFaithfulι P₂.fullyFaithfulι
        (P₂.liftCompιIso _ hLf).symm (P₁.liftCompιIso _ hRf).symm)
      (af'.restrictFullyFaithful P₃.fullyFaithfulι P₄.fullyFaithfulι
        (P₄.liftCompιIso _ hLf').symm (P₃.liftCompιIso _ hRf').symm) eg' ef' K).hom =
      Stacks.CategoryTheory.BaseChange.map af af' eg ef K.obj := by
  have h' := congrArg InducedCategory.Hom.hom
    (Stacks.CategoryTheory.BaseChange.homEquiv_symm_map
      (af.restrictFullyFaithful P₁.fullyFaithfulι P₂.fullyFaithfulι
        (P₂.liftCompιIso _ hLf).symm (P₁.liftCompιIso _ hRf).symm)
      (af'.restrictFullyFaithful P₃.fullyFaithfulι P₄.fullyFaithfulι
        (P₄.liftCompιIso _ hLf').symm (P₃.liftCompιIso _ hRf').symm) eg' ef' K)
  rw [Adjunction.homEquiv_counit] at h'
  rw [Stacks.CategoryTheory.BaseChange.map_eq af af' eg ef K.obj, ← Equiv.symm_apply_eq,
    Adjunction.homEquiv_counit]
  simp only [FullSubcategory.comp_hom, restrictFullyFaithful_lift_counit_app_hom] at h'
  have h₂ : ((eg'.hom ≫ ef'.inv).app ((P₁.lift (P₂.ι ⋙ Rf) hRf).obj K)).hom =
      (eg.hom ≫ ef.inv).app (Rf.obj K.obj) := h _
  rw [← Category.assoc, ← NatTrans.comp_app, ← h₂]
  simp only [NatTrans.comp_app, FullSubcategory.comp_hom, Category.assoc]
  exact h'.trans (congrArg (fun t => _ ≫ _ ≫ t)
    (congrArg Lg'.map (restrictFullyFaithful_lift_counit_app_hom af hLf hRf K)))

end CategoryTheory.ObjectProperty
