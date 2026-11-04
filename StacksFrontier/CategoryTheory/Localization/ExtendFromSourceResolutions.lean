module

public import Mathlib.CategoryTheory.Localization.Predicate

/-!
# Extending an isomorphism of localized functors from resolutions that are not functorial

Let `Q : C ⥤ D` be a localization of `C` at a class `W` of morphisms and let `P` be a property
of objects of `C`. Two functors `F, G : D ⥤ E` are isomorphic as soon as they are isomorphic at
the image of every object satisfying `P`, naturally in the morphisms between such objects,
provided that

* every object receives a morphism from one satisfying `P` which becomes invertible in `D`, and
* every morphism of `D` between the images of two objects satisfying `P` is a *fraction*
  `inv (Q a) ≫ Q b` through an object satisfying `P`.

`CategoryTheory.exists_natIso_of_isoOnResolutions` of
`StacksFrontier.CategoryTheory.Localization.ExtendFromResolutions` proves the same conclusion from
a *functorial* resolution `R : C ⥤ C` with an augmentation `𝟭 C ⟶ R`. The two hypotheses above
are what replace that functor, and they are what a resolution by sources rather than by targets
supplies: a K-injective resolution of a complex is functorial (Stacks 079P) and its augmentation
goes `K ⟶ I`, whereas a K-flat resolution (Stacks 06YS) is a chosen morphism `P ⟶ K` out of a
complex built from a colimit presentation, with no functoriality in `K`. The second hypothesis
is then supplied by the calculus of fractions in the derived category, `DerivedCategory.right_fac`
together with the existence of resolutions: a morphism `Q A ⟶ Q A'` is `inv (Q s) ≫ Q g` through
some complex, and resolving that complex once more makes the intermediate object satisfy `P`.

## Main results

* `CategoryTheory.naturality_of_isoOnSourceResolutions`: naturality for the morphisms of `C`
  between objects satisfying `P` upgrades to naturality for all morphisms of `D` between their
  images, as soon as every such morphism is a fraction through an object satisfying `P`.
* `CategoryTheory.exists_natIso_of_isoOnSourceResolutions`: the isomorphism of functors,
  together with the formula for its components at the objects satisfying `P`.

## Implementation notes

The conclusion records the components at the objects satisfying `P`, which determines the
isomorphism by `CategoryTheory.Localization.natTrans_ext`; that is what makes the extension
canonical rather than chosen, exactly as in `exists_natIso_of_isoOnResolutions`.

The resolution is given as a function `r : C → C` together with the morphisms `ρ c : r c ⟶ c`,
rather than as an existential statement, so that a caller which has made the choice once can
pass it; `Classical.choice` turns the existential into this shape.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/-- **Naturality on a resolving class upgrades to naturality for every localized morphism.**
A family of isomorphisms given at the objects satisfying `P` and natural for the morphisms of
`C` between such objects is natural for every morphism of `D` between their images, provided
every such morphism is a fraction `inv (Q a) ≫ Q b` through an object satisfying `P`.

Writing the morphism as such a fraction, the two instances of the given naturality — at `a` and
at `b` — identify the conjugate of the component at the intermediate object with each of the two
sides. -/
theorem naturality_of_isoOnSourceResolutions
    (Q : C ⥤ D) (P : C → Prop) (F G : D ⥤ E)
    (e : ∀ c, P c → (F.obj (Q.obj c) ≅ G.obj (Q.obj c)))
    (hfrac : ∀ {c c' : C}, P c → P c' → ∀ f : Q.obj c ⟶ Q.obj c',
      ∃ (z : C) (_ : P z) (a : z ⟶ c) (_ : IsIso (Q.map a)) (b : z ⟶ c'),
        f = inv (Q.map a) ≫ Q.map b)
    (he : ∀ {c c' : C} (hc : P c) (hc' : P c') (f : c ⟶ c'),
      F.map (Q.map f) ≫ (e c' hc').hom = (e c hc).hom ≫ G.map (Q.map f)) :
    ∀ ⦃c c' : C⦄ (hc : P c) (hc' : P c') (f : Q.obj c ⟶ Q.obj c'),
      F.map f ≫ (e c' hc').hom = (e c hc).hom ≫ G.map f := by
  intro c c' hc hc' f
  obtain ⟨z, hz, a, ha, b, rfl⟩ := hfrac hc hc' f
  have ha' : IsIso (Q.map a) := ha
  have h1 : F.map (Q.map a) ≫ (e c hc).hom = (e z hz).hom ≫ G.map (Q.map a) := he hz hc a
  have h2 : F.map (Q.map b) ≫ (e c' hc').hom = (e z hz).hom ≫ G.map (Q.map b) := he hz hc' b
  have hL : F.map (Q.map a) ≫ F.map (inv (Q.map a) ≫ Q.map b) ≫ (e c' hc').hom =
      (e z hz).hom ≫ G.map (Q.map b) := by
    simp only [Functor.map_comp, Functor.map_inv, Category.assoc, IsIso.hom_inv_id_assoc]
    exact h2
  have hR : F.map (Q.map a) ≫ (e c hc).hom ≫ G.map (inv (Q.map a) ≫ Q.map b) =
      (e z hz).hom ≫ G.map (Q.map b) := by
    simp only [Functor.map_comp, Functor.map_inv]
    rw [← Category.assoc, h1]
    simp
  exact (cancel_epi (F.map (Q.map a))).mp (hL.trans hR.symm)

/-- **An isomorphism of functors on a localized category, extended from a family of
isomorphisms at a resolving class of objects.** The resolution is not required to be
functorial: what replaces functoriality is that every morphism of `D` between the images of two
objects of the class is a fraction through an object of the class.

The components at the objects of the class are the given ones, which determines the
isomorphism. -/
theorem exists_natIso_of_isoOnSourceResolutions
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W] (P : C → Prop)
    (r : C → C) (ρ : ∀ c, r c ⟶ c) (hrP : ∀ c, P (r c)) (hρ : ∀ c, IsIso (Q.map (ρ c)))
    (hfrac : ∀ {c c' : C}, P c → P c' → ∀ f : Q.obj c ⟶ Q.obj c',
      ∃ (z : C) (_ : P z) (a : z ⟶ c) (_ : IsIso (Q.map a)) (b : z ⟶ c'),
        f = inv (Q.map a) ≫ Q.map b)
    (F G : D ⥤ E) (e : ∀ c, P c → (F.obj (Q.obj c) ≅ G.obj (Q.obj c)))
    (he : ∀ {c c' : C} (hc : P c) (hc' : P c') (f : c ⟶ c'),
      F.map (Q.map f) ≫ (e c' hc').hom = (e c hc).hom ≫ G.map (Q.map f)) :
    ∃ e' : F ≅ G, ∀ c (hc : P c), e'.hom.app (Q.obj c) = (e c hc).hom := by
  have heD := naturality_of_isoOnSourceResolutions Q P F G e hfrac he
  let t : Q ⋙ F ≅ Q ⋙ G := NatIso.ofComponents
    (fun c => (asIso (F.map (Q.map (ρ c)))).symm ≪≫ e (r c) (hrP c) ≪≫
      asIso (G.map (Q.map (ρ c))))
    (by
      intro c c' f
      have hkey := heD (hrP c) (hrP c') (Q.map (ρ c) ≫ Q.map f ≫ inv (Q.map (ρ c')))
      simp only [Functor.map_comp, Functor.map_inv] at hkey
      refine (cancel_epi (F.map (Q.map (ρ c)))).mp ?_
      simp only [Functor.comp_map, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
        Category.assoc, IsIso.hom_inv_id_assoc]
      rw [reassoc_of% hkey]
      simp)
  let ff := Localization.fullyFaithfulWhiskeringLeft Q W E
  refine ⟨ff.preimageIso t, fun c hc => ?_⟩
  have ht := congrArg (fun k => k.app c) (ff.map_preimage t.hom)
  change (ff.preimageIso t).hom.app (Q.obj c) = _ at ht
  rw [ht]
  have hc' := he (hrP c) hc (ρ c)
  change inv (F.map (Q.map (ρ c))) ≫ (e (r c) (hrP c)).hom ≫ G.map (Q.map (ρ c)) = (e c hc).hom
  rw [← hc']
  simp

end CategoryTheory

end
