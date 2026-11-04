module

public import StacksFrontier.Deformation.CofiberedPresentation.Existence
public import StacksFrontier.Deformation.ResidueField.GroupoidRestriction
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.Deformation.GroupoidQuotient.MoritaPresentation
public import StacksFrontier.Deformation.ResidueField.SeparableExtension

/-!
# Change of residue field of a presentation

Let `Λ → k → l` be a finite tower of fields over a Noetherian ring (Stacks 07W8) and let `G` be a
groupoid in functors on `𝒞_{Λ,k}` presenting a category `p : ℱ ⥤ 𝒞_{Λ,k}`. Restricting `G`
along the comparison functor `T ↦ T ×_l k` gives a groupoid in functors on `𝒞_{Λ,l}`, and it
presents the change of residue field `ℱ_{l/k}`, the categorical pullback of `p` along the
comparison functor.

The quotient `[G|_{𝒞_{Λ,l}}]` is the Grothendieck construction of the evaluated groupoids of `G`
precomposed with the comparison functor, which maps to the quotient `[G]` by
`CategoryTheory.Grothendieck.pre`; composing with the presentation of `p` and recording the base
gives a functor into the categorical pullback, which is full, faithful and essentially surjective.

## Main results

* `Deformation.GroupoidInFunctors.restrictPresentation`: the presentation of `ℱ_{l/k}`.
* `Deformation.GroupoidInFunctors.twoMul_ringKrullDim_sub_eq_of_changeOfFields`: for a finite
  separable extension `l/k`, the integer `2 dim A - dim B` of a smooth prorepresentable
  presentation of `ℱ` over `𝒞_{Λ,k}` is the integer `2 dim A' - dim B'` of any smooth
  prorepresentable presentation over `𝒞_{Λ,l}` of a category equivalent to `ℱ_{l/k}`. This is
  the change of residue field step in the proof of Stacks 0DSB.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u uF vF uF' vF'

namespace Deformation

namespace GroupoidInFunctors

variable (S : ChangeOfFieldsSituation.{u, u, u})
  (G : GroupoidInFunctors.{_, u, u} (ArtinianLocalAlgCat.{u, u, u} S.Λ S.k))

/-- The evaluated groupoids of a restriction are those of the original groupoid in functors. -/
theorem evaluationFunctor_restrict_comparisonFunctor :
    evaluationFunctor (G.restrict (comparisonFunctor S).functor) =
      (comparisonFunctor S).functor ⋙ evaluationFunctor G := rfl

/-- Two `eqToHom`s that compose to an identity cancel. -/
theorem eqToHom_comp_eqToHom_comp_self {C : Type*} [Category C] {a b c : C} (h₁ : a = b)
    (h₂ : b = a) (x : a ⟶ c) : eqToHom h₁ ≫ eqToHom h₂ ≫ x = x := by
  subst h₁
  simp

/-- The quotient of the restriction maps to the quotient of the groupoid in functors: the
functor `CategoryTheory.Grothendieck.pre` along the comparison functor, written out so that its
values on objects and morphisms are available at reducible transparency. -/
noncomputable def restrictQuotientFunctor :
    Grothendieck (evaluationFunctor (G.restrict (comparisonFunctor S).functor)) ⥤
      Grothendieck (evaluationFunctor G) where
  obj X := ⟨(comparisonFunctor S).functor.obj X.base, X.fiber⟩
  map f := ⟨(comparisonFunctor S).functor.map f.base, f.fiber⟩
  map_id X := (Grothendieck.pre (evaluationFunctor G) (comparisonFunctor S).functor).map_id X
  map_comp f g :=
    (Grothendieck.pre (evaluationFunctor G) (comparisonFunctor S).functor).map_comp f g

/-- The base of the image of an object under `restrictQuotientFunctor` is the image of its base
under the comparison functor. -/
@[simp]
theorem restrictQuotientFunctor_obj_base
    (X : Grothendieck (evaluationFunctor (G.restrict (comparisonFunctor S).functor))) :
    ((restrictQuotientFunctor S G).obj X).base = (comparisonFunctor S).functor.obj X.base := rfl

/-- The base of the image of a morphism under `restrictQuotientFunctor` is the image of its base
under the comparison functor. -/
@[simp]
theorem restrictQuotientFunctor_map_base
    {X Y : Grothendieck (evaluationFunctor (G.restrict (comparisonFunctor S).functor))}
    (f : X ⟶ Y) :
    ((restrictQuotientFunctor S G).map f).base = (comparisonFunctor S).functor.map f.base := rfl

/-- The fiber component of the image of a morphism under `restrictQuotientFunctor` is its fiber
component. -/
theorem restrictQuotientFunctor_map_fiber
    {X Y : Grothendieck (evaluationFunctor (G.restrict (comparisonFunctor S).functor))}
    (f : X ⟶ Y) : ((restrictQuotientFunctor S G).map f).fiber = f.fiber := rfl

variable {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} S.Λ S.k}

/-- The projection to `𝒞_{Λ,k}` of the image of an object under `restrictQuotientFunctor` followed
by a presentation is the image of its base under the comparison functor. -/
theorem restrictPresentation_obj_eq (E : Presentation G p)
    (X : Grothendieck (evaluationFunctor (G.restrict (comparisonFunctor S).functor))) :
    p.obj (E.hom.functor.obj ((restrictQuotientFunctor S G).obj X)) =
      (comparisonFunctor S).functor.obj X.base :=
  Functor.congr_obj E.hom.w ((restrictQuotientFunctor S G).obj X)

/-- The projection of the image of a morphism of the quotient under a presentation. -/
theorem presentation_map_eq (E : Presentation G p) {W W' : Grothendieck (evaluationFunctor G)}
    (g : W ⟶ W') :
    p.map (E.hom.functor.map g) = eqToHom (Functor.congr_obj E.hom.w W) ≫ g.base ≫
      eqToHom (Functor.congr_obj E.hom.w W').symm :=
  Functor.congr_hom E.hom.w g

/-- Cancelling `eqToHom`s on both sides of an equation. -/
theorem eq_of_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {a b c d : C} (h₁ : a = b)
    (h₂ : c = d) (x y : b ⟶ c) (h : eqToHom h₁ ≫ x ≫ eqToHom h₂ = eqToHom h₁ ≫ y ≫ eqToHom h₂) :
    x = y := by
  subst h₁ h₂
  simpa using h

/-- A conjugate of a morphism by `eqToHom`s cancelling in pairs is the morphism. -/
theorem eqToHom_comp_comp_eqToHom_self {C : Type*} [Category C] {a b c d : C} (h₁ : a = b)
    (h₂ : b = a) (x : a ⟶ c) (h₃ : c = d) (h₄ : d = c) :
    eqToHom h₁ ≫ ((eqToHom h₂ ≫ x) ≫ eqToHom h₃) ≫ eqToHom h₄ = x := by
  subst h₁ h₃
  simp

/-- Composing with an `eqToHom` and back is the identity. -/
theorem eq_comp_eqToHom_comp_eqToHom {C : Type*} [Category C] {a b c : C} (x : a ⟶ b)
    (h : b = c) (h' : c = b) : x = (x ≫ eqToHom h) ≫ eqToHom h' := by
  subst h
  simp

/-- The projection to `𝒞_{Λ,k}` of the image of a morphism under `restrictQuotientFunctor` followed
by a presentation is the image of its base under the comparison functor, conjugated by the
identifications of `restrictPresentation_obj_eq`. -/
theorem restrictPresentation_map_eq (E : Presentation G p)
    {X Y : Grothendieck (evaluationFunctor (G.restrict (comparisonFunctor S).functor))}
    (f : X ⟶ Y) :
    p.map (E.hom.functor.map ((restrictQuotientFunctor S G).map f)) =
      eqToHom (restrictPresentation_obj_eq S G E X) ≫ (comparisonFunctor S).functor.map f.base ≫
        eqToHom (restrictPresentation_obj_eq S G E Y).symm := by
  exact presentation_map_eq S G E ((restrictQuotientFunctor S G).map f)

/-- The functor from the quotient of the restriction to the change of residue field of the
presented category. -/
noncomputable def restrictPresentationFunctor (E : Presentation G p) :
    Grothendieck (evaluationFunctor (G.restrict (comparisonFunctor S).functor)) ⥤
      ChangeOfFieldsCategory S p where
  obj X :=
    { fst := E.hom.functor.obj ((restrictQuotientFunctor S G).obj X)
      snd := X.base
      iso := eqToIso (restrictPresentation_obj_eq S G E X) }
  map {X Y} f :=
    { fst := E.hom.functor.map ((restrictQuotientFunctor S G).map f)
      snd := f.base
      w := by
        rw [restrictPresentation_map_eq]
        simp }
  map_id X := by
    ext
    · change E.hom.functor.map ((restrictQuotientFunctor S G).map (𝟙 X)) = 𝟙 _
      rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    · rfl
  map_comp f g := by
    ext
    · change E.hom.functor.map ((restrictQuotientFunctor S G).map (f ≫ g)) =
        E.hom.functor.map ((restrictQuotientFunctor S G).map f) ≫
          E.hom.functor.map ((restrictQuotientFunctor S G).map g)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
    · rfl

/-- The composite of `restrictPresentationFunctor` with the projection of the change of residue
field is the projection of the quotient of the restriction. -/
theorem restrictPresentationFunctor_comp_projection (E : Presentation G p) :
    restrictPresentationFunctor S G E ⋙ changeOfFieldsProjection S p =
      Grothendieck.forget (evaluationFunctor (G.restrict (comparisonFunctor S).functor)) := rfl

/-- The functor `restrictPresentationFunctor` is faithful. -/
instance (E : Presentation G p) : (restrictPresentationFunctor S G E).Faithful where
  map_injective {X Y} f g h := by
    have hf : (restrictQuotientFunctor S G).map f = (restrictQuotientFunctor S G).map g := by
      have := E.isEquivalence_hom_functor
      exact E.hom.functor.map_injective (congrArg CategoricalPullback.Hom.fst h)
    refine Grothendieck.ext _ _ (congrArg CategoricalPullback.Hom.snd h) ?_
    have := Grothendieck.congr hf
    change f.fiber = _ at this
    rw [this, restrictQuotientFunctor_map_fiber]
    exact eqToHom_comp_eqToHom_comp_self _ _ _

/-- The functor `restrictPresentationFunctor` is full. -/
instance (E : Presentation G p) : (restrictPresentationFunctor S G E).Full where
  map_surjective {X Y} φ := by
    have := E.isEquivalence_hom_functor
    let ψ := E.hom.functor.preimage φ.fst
    have hψ : E.hom.functor.map ψ = φ.fst := E.hom.functor.map_preimage _
    have hb : ψ.base = (comparisonFunctor S).functor.map φ.snd := by
      have h1 : p.map φ.fst = eqToHom (restrictPresentation_obj_eq S G E X) ≫ ψ.base ≫
          eqToHom (restrictPresentation_obj_eq S G E Y).symm := by
        rw [← hψ]
        exact presentation_map_eq S G E ψ
      have hw : p.map φ.fst ≫ eqToHom (restrictPresentation_obj_eq S G E Y) =
          eqToHom (restrictPresentation_obj_eq S G E X) ≫
            (comparisonFunctor S).functor.map φ.snd := φ.w
      have h3 : p.map φ.fst = eqToHom (restrictPresentation_obj_eq S G E X) ≫
          (comparisonFunctor S).functor.map φ.snd ≫
            eqToHom (restrictPresentation_obj_eq S G E Y).symm := by
        rw [← Category.assoc, ← hw]
        exact eq_comp_eqToHom_comp_eqToHom _ _ _
      exact eq_of_eqToHom_comp_comp_eqToHom _ _ _ _ (h1.symm.trans h3)
    refine ⟨⟨φ.snd, eqToHom (by rw [hb]; rfl) ≫ ψ.fiber⟩, ?_⟩
    refine CategoricalPullback.hom_ext ?_ rfl
    change E.hom.functor.map ⟨(comparisonFunctor S).functor.map φ.snd, _⟩ = φ.fst
    rw [← hψ]
    congr 1
    exact Grothendieck.ext _ _ hb.symm (eqToHom_comp_eqToHom_comp_self _ _ _)

/-- The functor `restrictPresentationFunctor` is essentially surjective. -/
instance (E : Presentation G p) : (restrictPresentationFunctor S G E).EssSurj where
  mem_essImage z := by
    let y := E.inv.functor.obj z.fst
    have hy : y.base = p.obj z.fst := Functor.congr_obj E.inv.w z.fst
    let b : y.base ≅ (comparisonFunctor S).functor.obj z.snd := eqToIso hy ≪≫ z.iso
    let X : Grothendieck (evaluationFunctor (G.restrict (comparisonFunctor S).functor)) :=
      ⟨z.snd, ((evaluationFunctor G).map b.hom).toFunctor.obj y.fiber⟩
    let m : y ≅ (restrictQuotientFunctor S G).obj X := Grothendieck.isoMk b (Iso.refl _)
    let eₗ : z.fst ≅ E.hom.functor.obj ((restrictQuotientFunctor S G).obj X) :=
      (E.counitIso.app z.fst).symm ≪≫ E.hom.functor.mapIso m
    refine ⟨X, ⟨(CategoricalPullback.mkIso (x := z) (y := (restrictPresentationFunctor S G E).obj X)
      eₗ (Iso.refl z.snd) ?_).symm⟩⟩
    have hc := E.isHomLift_counitIso_inv_app z.fst
    have hc' := IsHomLift.fac' p (𝟙 (p.obj z.fst)) (E.counitIso.inv.app z.fst)
    change p.map (E.counitIso.inv.app z.fst ≫ E.hom.functor.map m.hom) ≫
        eqToHom (restrictPresentation_obj_eq S G E X) =
      z.iso.hom ≫ (comparisonFunctor S).functor.map (𝟙 _)
    have hmb : m.hom.base = eqToHom hy ≫ z.iso.hom := rfl
    rw [CategoryTheory.Functor.map_comp, hc', presentation_map_eq S G E m.hom, hmb]
    simp only [Category.id_comp, Category.assoc, eqToHom_trans_assoc,
      CategoryTheory.Functor.map_id, Category.comp_id]
    exact eqToHom_comp_comp_eqToHom_self _ _ _ _ _

/-- **The restriction of a presentation along the comparison functor.** A presentation of
`p : ℱ ⥤ 𝒞_{Λ,k}` by a groupoid in functors `G` restricts to a presentation of the change of
residue field `ℱ_{l/k}` by the restriction of `G` along `T ↦ T ×_l k`. -/
noncomputable def restrictPresentation (E : Presentation G p) :
    Presentation (G.restrict (comparisonFunctor S).functor) (changeOfFieldsProjection S p) :=
  presentationOfQuotientEquivalence _ _ (restrictPresentationFunctor S G E)
    (restrictPresentationFunctor_comp_projection S G E)

/-- **Change of residue field of the invariant `2 dim A - dim B` (Stacks 0DSB, second step of the
proof).** Let `l/k` be a finite separable extension, let `G` be a smooth groupoid in functors on
`𝒞_{Λ,k}` prorepresented by `(A, B)` presenting `p : ℱ ⥤ 𝒞_{Λ,k}`, and let `H` be a smooth
groupoid in functors on `𝒞_{Λ,l}` prorepresented by `(A', B')` presenting a category
equivalent over `𝒞_{Λ,l}` to the change of residue field `ℱ_{l/k}`. Then
`2 dim A - dim B = 2 dim A' - dim B'`, all four dimensions being finite.

The restriction of `G` along `T ↦ T ×_l k` presents `ℱ_{l/k}`
(`Deformation.GroupoidInFunctors.restrictPresentation`), is smooth, and is prorepresented by the
extensions `A[X]/(F)` and `B[X]/(F)` of `Deformation.SeparableExtension`, which have the
dimensions of `A` and `B`; the invariance under change of presentation
(`Deformation.GroupoidInFunctors.twoMul_ringKrullDim_sub_eq_of_presentations`) concludes. -/
public theorem twoMul_ringKrullDim_sub_eq_of_changeOfFields [Algebra.IsSeparable S.k S.l]
    (hG : GroupoidInFunctors.IsSmooth G)
    (H : GroupoidInFunctors.{_, u, u} (ArtinianLocalAlgCat.{u, u, u} S.Λ S.l))
    (hH : GroupoidInFunctors.IsSmooth H)
    {A B : CompleteLocalAlgCat.{u, u, u} S.Λ S.k} {A' B' : CompleteLocalAlgCat.{u, u, u} S.Λ S.l}
    (eA : G.objects ≅ restrictedCoyoneda A) (eB : G.arrows ≅ restrictedCoyoneda B)
    (eA' : H.objects ≅ restrictedCoyoneda A') (eB' : H.arrows ≅ restrictedCoyoneda B')
    (E : Presentation G p) {F' : Type uF'} [Category.{vF'} F']
    {p' : F' ⥤ ArtinianLocalAlgCat.{u, u, u} S.Λ S.l}
    (PH : Presentation H p')
    (e : StacksRepresentableCFG.EquivalenceOver (changeOfFieldsProjection S p) p') :
    ∃ a b a' b' : ℕ, ringKrullDim A = a ∧ ringKrullDim B = b ∧ ringKrullDim A' = a' ∧
      ringKrullDim B' = b' ∧ 2 * a + b' = 2 * a' + b := by
  obtain ⟨a, b, a', b', ha, hb, ha', hb', h⟩ :=
    twoMul_ringKrullDim_sub_eq_of_presentations.{u, u, u}
      (G.restrict (comparisonFunctor S).functor) H (isSmooth_restrict_comparisonFunctor S G hG) hH
      (Functor.isoWhiskerLeft (comparisonFunctor S).functor eA ≪≫
        SeparableExtension.restrictedCoyonedaIso S A)
      (Functor.isoWhiskerLeft (comparisonFunctor S).functor eB ≪≫
        SeparableExtension.restrictedCoyonedaIso S B)
      eA' eB' ((restrictPresentation S G E).trans e) PH
  exact ⟨a, b, a', b', (SeparableExtension.ringKrullDim_obj S A).symm.trans ha,
    (SeparableExtension.ringKrullDim_obj S B).symm.trans hb, ha', hb', h⟩

end GroupoidInFunctors

end Deformation

end
