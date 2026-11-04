module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModificationGlueing
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor

/-!
# Glueing spaces étale over a modification, from glueing sheaves

Let

```
E --j--> Y
|g       |f
v        v
Z --i--> X
```

be a commutative square of algebraic spaces over `S`. Base change along the four sides gives a
functor from the spaces-étale site of `X` to the categorical pullback of the base changes along
`j` and `g`, `V ↦ (V ×_X Y, V ×_X Z, (V ×_X Y) ×_Y E ≅ (V ×_X Z) ×_Z E)`. Stacks 0GG1 asserts
that this functor is an equivalence when `f` is proper, `i` is a closed immersion, the square is
cartesian and `f` is an isomorphism over `X ∖ Z`; its proof deduces this from Stacks 0GFY, the
same statement for sheaves of sets, through the Yoneda embedding.

For an arbitrary commutative square, the Yoneda embeddings of the four spaces-étale sites induce
a fully faithful functor between the two categorical pullbacks (Stacks 02XB), and the
identification `j⁻¹ f⁻¹ ≅ g⁻¹ i⁻¹` of the sheaf-level restriction functor of
`AlgebraicGeometry.Space.spacesModificationRestriction` restricts on representable sheaves to the
base-change identification of the site-level functor (Stacks 04D3 and the composition
comparison of Stacks 03G2). So the site-level functor is an equivalence as soon as the
sheaf-level one is and every sheaf whose restriction is the restriction of a representable
object is itself representable.

## Main definitions

* `AlgebraicGeometry.Space.spacesEtaleModificationSquareIso`: the identification
  `(V ×_X Y) ×_Y E ≅ (V ×_X Z) ×_Z E` of the two iterated base changes.
* `AlgebraicGeometry.Space.spacesEtaleModificationRestriction`: the site-level restriction
  functor of Stacks 0GG1.
* `AlgebraicGeometry.Space.spacesEtaleModificationYoneda`: the functor induced by the Yoneda
  embeddings on the categorical pullbacks.
* `AlgebraicGeometry.Space.spacesEtaleModificationRestrictionYonedaIso`: the site-level
  restriction followed by the Yoneda embedding is the Yoneda embedding followed by the
  sheaf-level restriction.

## Main results

* `CategoryTheory.Functor.isEquivalence_of_compIso_of_isEquivalence`: if `R ⋙ T ≅ y ⋙ R'` with
  `R'` an equivalence, `y` and `T` fully faithful, and every `T d` isomorphic to some `R' (y c)`,
  then `R` is an equivalence.
* `AlgebraicGeometry.Space.inverseImageIso_spacesPushforwardCompSquareIso_hom`: the
  identification `j⁻¹ f⁻¹ ≅ g⁻¹ i⁻¹` of the sheaf-level restriction is the composite of the
  composition comparisons of the inverse images.
* `AlgebraicGeometry.Space.isEquivalence_spacesEtaleModificationRestriction_of_representable`:
  the site-level restriction functor is an equivalence, given that the sheaf-level one is and
  that sheaves with representable restrictions are representable.

## References

* [Stacks Project, Tag 0GG1](https://stacks.math.columbia.edu/tag/0GG1)
* [Stacks Project, Tag 0GFY](https://stacks.math.columbia.edu/tag/0GFY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']

/-- Let `R ⋙ T ≅ y ⋙ R'` with `R'` an equivalence and `y`, `T` fully faithful. If every object
`T d` is isomorphic to some `R' (y c)`, then `R` is an equivalence. -/
theorem isEquivalence_of_compIso_of_isEquivalence (R : C ⥤ D) (R' : C' ⥤ D') (y : C ⥤ C')
    (T : D ⥤ D') (e : R ⋙ T ≅ y ⋙ R') [R'.IsEquivalence] (hy : y.FullyFaithful)
    (hT : T.FullyFaithful)
    (hess : ∀ d : D, ∃ c : C, Nonempty (R'.obj (y.obj c) ≅ T.obj d)) : R.IsEquivalence := by
  have hRT : (R ⋙ T).FullyFaithful :=
    (hy.comp (FullyFaithful.ofFullyFaithful R')).ofIso e.symm
  have := hT.faithful
  have hR : R.FullyFaithful := hRT.ofCompFaithful
  have := hR.full
  have := hR.faithful
  have : R.EssSurj := ⟨fun d => by
    obtain ⟨c, ⟨i⟩⟩ := hess d
    exact ⟨c, ⟨hT.preimageIso (e.app c ≪≫ i)⟩⟩⟩
  exact { }

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Coherence of the identifications on representable sheaves -/

section Coherence

/-- The identification of Stacks 04D3 is compatible with the identification of the inverse
images along two equal morphisms. -/
@[reassoc]
theorem eqToHom_app_comp_baseChangeYonedaIso_hom {T Z : AlgebraicSpaces B S hS} {p q : T ⟶ Z}
    (h : p = q) (V : SpacesEtale B S hS Z) :
    (eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) h)).app
        ((SpacesEtale.topology B S hS Z).yoneda.obj V) ≫ (baseChangeYonedaIso B S hS q V).hom =
      (baseChangeYonedaIso B S hS p V).hom ≫ (SpacesEtale.topology B S hS T).yoneda.map
        ((eqToHom (congrArg (fun k => (spacesBaseChange B S hS k).functor) h)).app V) := by
  subst h
  simp

/-- The adjoint conjugate of the identification of the inverse images along two equal
morphisms is the identification of their direct images. -/
theorem conjugateEquiv_spacesToposAdjunction_eqToHom {T Z : AlgebraicSpaces B S hS}
    {p q : T ⟶ Z} (h : p = q) :
    conjugateEquiv (spacesToposAdjunction B S hS q) (spacesToposAdjunction B S hS p)
        (eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) h)) =
      eqToHom (congrArg (fun k => (spacesBaseChange B S hS k).functor.sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS Z) (SpacesEtale.topology B S hS T))
          h.symm) := by
  subst h
  simp

variable {X Y Z E : AlgebraicSpaces B S hS} (f : Y ⟶ X) (i : Z ⟶ X) (j : E ⟶ Y) (g : E ⟶ Z)
  (w : j ≫ f = g ≫ i)

/-- The identification `f⁻¹ ⋙ j⁻¹ ≅ i⁻¹ ⋙ g⁻¹` of the sheaf-level restriction functor of a
commutative square, conjugate to the comparison of the composite direct images, is the
composite of the composition comparisons of the inverse images along `j ≫ f = g ≫ i`. -/
theorem inverseImageIso_spacesPushforwardCompSquareIso_hom :
    (Adjunction.ModificationGlueing.inverseImageIso (spacesToposAdjunction B S hS f)
        (spacesToposAdjunction B S hS i) (spacesToposAdjunction B S hS j)
        (spacesToposAdjunction B S hS g) (spacesPushforwardCompSquareIso B S hS j g f i w)).hom =
      (spacesEtaleInverseImage_comp B S hS j f).inv ≫
        eqToHom (congrArg (fun k => spacesEtaleInverseImage B S hS k) w) ≫
          (spacesEtaleInverseImage_comp B S hS g i).hom := by
  have e₁ : (spacesEtaleInverseImage_comp B S hS j f).inv =
      (conjugateEquiv (spacesToposAdjunction B S hS (j ≫ f))
        ((spacesToposAdjunction B S hS f).comp (spacesToposAdjunction B S hS j))).symm
          (spacesBaseChange_pushforward_comp B S hS j f).inv := rfl
  have e₃ : (spacesEtaleInverseImage_comp B S hS g i).hom =
      (conjugateEquiv ((spacesToposAdjunction B S hS i).comp (spacesToposAdjunction B S hS g))
        (spacesToposAdjunction B S hS (g ≫ i))).symm
          (spacesBaseChange_pushforward_comp B S hS g i).hom := rfl
  have e₀ : (Adjunction.ModificationGlueing.inverseImageIso (spacesToposAdjunction B S hS f)
        (spacesToposAdjunction B S hS i) (spacesToposAdjunction B S hS j)
        (spacesToposAdjunction B S hS g) (spacesPushforwardCompSquareIso B S hS j g f i w)).hom =
      (conjugateEquiv ((spacesToposAdjunction B S hS i).comp (spacesToposAdjunction B S hS g))
        ((spacesToposAdjunction B S hS f).comp (spacesToposAdjunction B S hS j))).symm
          (spacesPushforwardCompSquareIso B S hS j g f i w).inv := rfl
  apply (conjugateEquiv ((spacesToposAdjunction B S hS i).comp (spacesToposAdjunction B S hS g))
    ((spacesToposAdjunction B S hS f).comp (spacesToposAdjunction B S hS j))).injective
  rw [e₀, e₁, e₃, Equiv.apply_symm_apply,
    ← conjugateEquiv_comp _ (spacesToposAdjunction B S hS (j ≫ f)),
    ← conjugateEquiv_comp _ (spacesToposAdjunction B S hS (g ≫ i)),
    conjugateEquiv_spacesToposAdjunction_eqToHom B S hS w, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  simp [spacesPushforwardCompSquareIso]

/-- The composition comparison of Stacks 04D3 for `k ≫ y`, solved for the iterated
identification. -/
@[reassoc]
theorem map_baseChangeYonedaIso_hom_comp_baseChangeYonedaIso_hom
    {T' T Z' : AlgebraicSpaces B S hS} (k : T' ⟶ T) (y : T ⟶ Z') (V : SpacesEtale B S hS Z') :
    (spacesEtaleInverseImage B S hS k).map (baseChangeYonedaIso B S hS y V).hom ≫
        (baseChangeYonedaIso B S hS k ((spacesBaseChange B S hS y).functor.obj V)).hom =
      (spacesEtaleInverseImage_comp B S hS k y).inv.app
          ((SpacesEtale.topology B S hS Z').yoneda.obj V) ≫
        (baseChangeYonedaIso B S hS (k ≫ y) V).hom ≫
          (SpacesEtale.topology B S hS T').yoneda.map
            ((spacesBaseChange_comp B S hS k y).inv.app V) := by
  rw [← Category.assoc, spacesEtaleInverseImage_comp_inv_app_comp_baseChangeYonedaIso_hom]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  simp

/-- The identification of the base changes `(V ×_X Y) ×_Y E ≅ (V ×_X Z) ×_Z E` of an object of
the spaces-étale site of `X` along the two sides of a commutative square. -/
def spacesEtaleModificationSquareIso :
    (spacesBaseChange B S hS f).functor ⋙ (spacesBaseChange B S hS j).functor ≅
      (spacesBaseChange B S hS i).functor ⋙ (spacesBaseChange B S hS g).functor :=
  spacesBaseChange_comp B S hS j f ≪≫
    eqToIso (congrArg (fun k => (spacesBaseChange B S hS k).functor) w) ≪≫
      (spacesBaseChange_comp B S hS g i).symm

/-- **The identification `j⁻¹ f⁻¹ ≅ g⁻¹ i⁻¹` on a representable sheaf.** Through the
identifications of Stacks 04D3 it is the sheaf represented by the identification
`(V ×_X Y) ×_Y E ≅ (V ×_X Z) ×_Z E` of the iterated base changes. -/
theorem inverseImageIso_hom_app_yoneda (V : SpacesEtale B S hS X) :
    (Adjunction.ModificationGlueing.inverseImageIso (spacesToposAdjunction B S hS f)
        (spacesToposAdjunction B S hS i) (spacesToposAdjunction B S hS j)
        (spacesToposAdjunction B S hS g)
        (spacesPushforwardCompSquareIso B S hS j g f i w)).hom.app
          ((SpacesEtale.topology B S hS X).yoneda.obj V) ≫
        (spacesEtaleInverseImage B S hS g).map (baseChangeYonedaIso B S hS i V).hom ≫
          (baseChangeYonedaIso B S hS g ((spacesBaseChange B S hS i).functor.obj V)).hom =
      (spacesEtaleInverseImage B S hS j).map (baseChangeYonedaIso B S hS f V).hom ≫
        (baseChangeYonedaIso B S hS j ((spacesBaseChange B S hS f).functor.obj V)).hom ≫
          (SpacesEtale.topology B S hS E).yoneda.map
            ((spacesEtaleModificationSquareIso B S hS f i j g w).hom.app V) := by
  rw [inverseImageIso_spacesPushforwardCompSquareIso_hom,
    map_baseChangeYonedaIso_hom_comp_baseChangeYonedaIso_hom,
    map_baseChangeYonedaIso_hom_comp_baseChangeYonedaIso_hom_assoc]
  simp only [NatTrans.comp_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [eqToHom_app_comp_baseChangeYonedaIso_hom_assoc B S hS w]
  simp [spacesEtaleModificationSquareIso]

end Coherence

/-! ### The site-level restriction functor -/

variable {X Y Z E : AlgebraicSpaces B S hS} (f : Y ⟶ X) (i : Z ⟶ X) (j : E ⟶ Y) (g : E ⟶ Z)
  (w : j ≫ f = g ≫ i)

/-- **The restriction functor of Stacks 0GG1**: an algebraic space `V` étale over `X` is sent to
its base changes `V ×_X Y` and `V ×_X Z`, with the identification of their base changes to `E`. -/
def spacesEtaleModificationRestriction :
    SpacesEtale B S hS X ⥤
      CategoricalPullback (spacesBaseChange B S hS j).functor (spacesBaseChange B S hS g).functor :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (spacesBaseChange B S hS j).functor (spacesBaseChange B S hS g).functor
    (SpacesEtale B S hS X)).obj
      { fst := (spacesBaseChange B S hS f).functor
        snd := (spacesBaseChange B S hS i).functor
        iso := spacesEtaleModificationSquareIso B S hS f i j g w }

/-- The first component of the restriction of `V` is `V ×_X Y`. -/
@[simp]
theorem spacesEtaleModificationRestriction_obj_fst (V : SpacesEtale B S hS X) :
    ((spacesEtaleModificationRestriction B S hS f i j g w).obj V).fst =
      (spacesBaseChange B S hS f).functor.obj V := rfl

/-- The second component of the restriction of `V` is `V ×_X Z`. -/
@[simp]
theorem spacesEtaleModificationRestriction_obj_snd (V : SpacesEtale B S hS X) :
    ((spacesEtaleModificationRestriction B S hS f i j g w).obj V).snd =
      (spacesBaseChange B S hS i).functor.obj V := rfl

/-- The identification in the restriction of `V` is `(V ×_X Y) ×_Y E ≅ (V ×_X Z) ×_Z E`. -/
@[simp]
theorem spacesEtaleModificationRestriction_obj_iso_hom (V : SpacesEtale B S hS X) :
    ((spacesEtaleModificationRestriction B S hS f i j g w).obj V).iso.hom =
      (spacesEtaleModificationSquareIso B S hS f i j g w).hom.app V := rfl

/-- The first component of the restriction of a morphism is its base change along `f`. -/
@[simp]
theorem spacesEtaleModificationRestriction_map_fst {V V' : SpacesEtale B S hS X} (a : V ⟶ V') :
    ((spacesEtaleModificationRestriction B S hS f i j g w).map a).fst =
      (spacesBaseChange B S hS f).functor.map a := rfl

/-- The second component of the restriction of a morphism is its base change along `i`. -/
@[simp]
theorem spacesEtaleModificationRestriction_map_snd {V V' : SpacesEtale B S hS X} (a : V ⟶ V') :
    ((spacesEtaleModificationRestriction B S hS f i j g w).map a).snd =
      (spacesBaseChange B S hS i).functor.map a := rfl

/-- The identification of Stacks 04D3, `y⁻¹ h_V ≅ h_{V ×_Z T}`, as a natural isomorphism. -/
def baseChangeYonedaNatIso {T Z' : AlgebraicSpaces B S hS} (y : T ⟶ Z') :
    (SpacesEtale.topology B S hS Z').yoneda ⋙ spacesEtaleInverseImage B S hS y ≅
      (spacesBaseChange B S hS y).functor ⋙ (SpacesEtale.topology B S hS T).yoneda :=
  NatIso.ofComponents (fun V => baseChangeYonedaIso B S hS y V)
    (fun a => Adjunction.map_yoneda_map_comp_yonedaIso_hom _ a)

/-- The functor induced by the Yoneda embeddings of the spaces-étale sites on the categorical
pullbacks, `(V', W, α) ↦ (h_{V'}, h_W, j⁻¹ h_{V'} ≅ h_{V' ×_Y E} ≅ h_{W ×_Z E} ≅ g⁻¹ h_W)`. -/
def spacesEtaleModificationYoneda :
    CategoricalPullback (spacesBaseChange B S hS j).functor (spacesBaseChange B S hS g).functor ⥤
      CategoricalPullback (spacesEtaleInverseImage B S hS j) (spacesEtaleInverseImage B S hS g) :=
  CategoricalPullback.map _ _ (SpacesEtale.topology B S hS Y).yoneda
    (SpacesEtale.topology B S hS Z).yoneda (SpacesEtale.topology B S hS E).yoneda _ _
    (baseChangeYonedaNatIso B S hS g) (baseChangeYonedaNatIso B S hS j).symm

/-- The functor induced by the Yoneda embeddings on the categorical pullbacks is fully faithful
(Stacks 02XB). -/
def spacesEtaleModificationYonedaFullyFaithful :
    (spacesEtaleModificationYoneda B S hS j g).FullyFaithful := by
  have := (SpacesEtale.topology B S hS Y).yonedaFullyFaithful.full
  have := (SpacesEtale.topology B S hS Y).yonedaFullyFaithful.faithful
  have := (SpacesEtale.topology B S hS Z).yonedaFullyFaithful.full
  have := (SpacesEtale.topology B S hS Z).yonedaFullyFaithful.faithful
  have := (SpacesEtale.topology B S hS E).yonedaFullyFaithful.faithful
  obtain ⟨h₁, h₂⟩ := induced_fullyFaithful_of_fullyFaithful
    (H := (spacesBaseChange B S hS j).functor) (I := (spacesBaseChange B S hS g).functor)
    (F := spacesEtaleInverseImage B S hS j) (G := spacesEtaleInverseImage B S hS g)
    (SpacesEtale.topology B S hS Y).yoneda (SpacesEtale.topology B S hS Z).yoneda
    (SpacesEtale.topology B S hS E).yoneda (baseChangeYonedaNatIso B S hS g)
    (baseChangeYonedaNatIso B S hS j).symm
  have : (spacesEtaleModificationYoneda B S hS j g).Faithful := h₁
  have : (spacesEtaleModificationYoneda B S hS j g).Full := h₂
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- **The site-level and sheaf-level restriction functors agree on representable sheaves**: the
site-level restriction functor followed by the Yoneda embedding is the Yoneda embedding followed
by the sheaf-level restriction functor `F ↦ (f⁻¹ F, i⁻¹ F)`. -/
def spacesEtaleModificationRestrictionYonedaIso :
    spacesEtaleModificationRestriction B S hS f i j g w ⋙ spacesEtaleModificationYoneda B S hS j g ≅
      (SpacesEtale.topology B S hS X).yoneda ⋙ spacesModificationRestriction B S hS f i j g w :=
  NatIso.ofComponents
    (fun V => CategoricalPullback.mkIso (baseChangeYonedaIso B S hS f V).symm
      (baseChangeYonedaIso B S hS i V).symm (by
        have h := inverseImageIso_hom_app_yoneda B S hS f i j g w V
        change (spacesEtaleInverseImage B S hS j).map (baseChangeYonedaIso B S hS f V).inv ≫
            (Adjunction.ModificationGlueing.inverseImageIso (spacesToposAdjunction B S hS f)
              (spacesToposAdjunction B S hS i) (spacesToposAdjunction B S hS j)
              (spacesToposAdjunction B S hS g)
              (spacesPushforwardCompSquareIso B S hS j g f i w)).hom.app
                ((SpacesEtale.topology B S hS X).yoneda.obj V) =
          ((baseChangeYonedaIso B S hS j ((spacesBaseChange B S hS f).functor.obj V)).hom ≫
            (SpacesEtale.topology B S hS E).yoneda.map
              ((spacesEtaleModificationSquareIso B S hS f i j g w).hom.app V) ≫
            (baseChangeYonedaIso B S hS g ((spacesBaseChange B S hS i).functor.obj V)).inv) ≫
            (spacesEtaleInverseImage B S hS g).map (baseChangeYonedaIso B S hS i V).inv
        rw [← cancel_epi ((spacesEtaleInverseImage B S hS j).map
          (baseChangeYonedaIso B S hS f V).hom), ← Functor.map_comp_assoc,
          Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
          ← cancel_mono ((spacesEtaleInverseImage B S hS g).map
          (baseChangeYonedaIso B S hS i V).hom ≫
            (baseChangeYonedaIso B S hS g ((spacesBaseChange B S hS i).functor.obj V)).hom), h]
        simp only [Category.assoc]
        rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
          Category.id_comp, Iso.inv_hom_id, Category.comp_id]))
    (fun a => by
      refine CategoricalPullback.hom_ext ?_ ?_
      · rw [CategoricalPullback.comp_fst, CategoricalPullback.comp_fst]
        exact (baseChangeYonedaNatIso B S hS f).inv.naturality a
      · rw [CategoricalPullback.comp_snd, CategoricalPullback.comp_snd]
        exact (baseChangeYonedaNatIso B S hS i).inv.naturality a)

/-- **Stacks 0GG1, granted Stacks 0GFY and the representability of the glued sheaves.** The
restriction functor of the spaces-étale site of `X` to the categorical pullback of the
spaces-étale sites of `Y` and `Z` over that of `E` is an equivalence, provided

* `hR`: the sheaf-level restriction functor `F ↦ (f⁻¹ F, i⁻¹ F)` is an equivalence (the
  conclusion of Stacks 0GFY), and
* `hrep`: every spaces-étale sheaf on `X` whose restriction is isomorphic to the image of an
  object of the site-level categorical pullback under the Yoneda embeddings is representable. -/
theorem isEquivalence_spacesEtaleModificationRestriction_of_representable
    [hR : (spacesModificationRestriction B S hS f i j g w).IsEquivalence]
    (hrep : ∀ (G : Sheaf (SpacesEtale.topology B S hS X) (Type (u + 1)))
      (A : CategoricalPullback (spacesBaseChange B S hS j).functor
        (spacesBaseChange B S hS g).functor),
      Nonempty ((spacesModificationRestriction B S hS f i j g w).obj G ≅
        (spacesEtaleModificationYoneda B S hS j g).obj A) →
      ∃ V : SpacesEtale B S hS X, Nonempty (G ≅ (SpacesEtale.topology B S hS X).yoneda.obj V)) :
    (spacesEtaleModificationRestriction B S hS f i j g w).IsEquivalence := by
  refine Functor.isEquivalence_of_compIso_of_isEquivalence _
    (spacesModificationRestriction B S hS f i j g w) (SpacesEtale.topology B S hS X).yoneda
    (spacesEtaleModificationYoneda B S hS j g)
    (spacesEtaleModificationRestrictionYonedaIso B S hS f i j g w)
    (SpacesEtale.topology B S hS X).yonedaFullyFaithful
    (spacesEtaleModificationYonedaFullyFaithful B S hS j g) fun A => ?_
  let R := spacesModificationRestriction B S hS f i j g w
  obtain ⟨V, ⟨e⟩⟩ := hrep (R.objPreimage ((spacesEtaleModificationYoneda B S hS j g).obj A)) A
    ⟨R.objObjPreimageIso _⟩
  exact ⟨V, ⟨R.mapIso e.symm ≪≫ R.objObjPreimageIso _⟩⟩

end AlgebraicGeometry.Space
