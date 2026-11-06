module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.BaseIsoTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentFppfCoveringUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentIntegralSurjectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableBridgePseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentRepresentableCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentRepresentableRefinement

/-!
# Descent of étale sheaves along a representable morphism of algebraic spaces (Stacks 0GFU, 0GFV)

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is representable by
schemes and is surjective and integral, or surjective and proper, or surjective, flat and locally
of finite presentation. Then sheaves on the spaces-étale site of `Y` are equivalent, through the
canonical descent datum, to descent data for `{X ⟶ Y}`: this is Stacks 0GFU. The same holds for
any `f` such that `π ≫ f` is representable with one of these properties for some `π : X' ⟶ X`:
this is Stacks 0GFV.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_toDescentData_schemeSpaceFunctor_map` — effective descent
  of spaces-étale sheaves along the morphism of algebraic spaces represented by a morphism of
  schemes, granted effective descent of small étale sheaves along that morphism of schemes.
* `AlgebraicGeometry.Space.spacesEtaleDescentOverRepresentable_of_smallEtale` — the case of a
  representable target, from the scheme case.
* `AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_relativelyRepresentable` —
  effective descent of spaces-étale sheaves along a representable morphism which is surjective
  and integral, surjective and proper, or surjective, flat and locally of finite presentation.
* `AlgebraicGeometry.Space.isEquivalence_toDescentData_singleton_of_relativelyRepresentable_comp`
  — effective descent of spaces-étale sheaves along `f` as soon as some `π ≫ f` is such a
  morphism.

## References

* [Stacks Project, Tag 0GFU](https://stacks.math.columbia.edu/tag/0GFU)
* [Stacks Project, Tag 0GFV](https://stacks.math.columbia.edu/tag/0GFV)
* [Stacks Project, Tag 0GEZ](https://stacks.math.columbia.edu/tag/0GEZ)
* [Stacks Project, Tag 0GF0](https://stacks.math.columbia.edu/tag/0GF0)
* [Stacks Project, Tag 0GF2](https://stacks.math.columbia.edu/tag/0GF2)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Effective descent along a represented morphism of schemes -/

set_option synthInstance.maxHeartbeats 400000 in
/-- **Effective descent along the morphism of algebraic spaces represented by a morphism of
schemes.** For a morphism `m : W ⟶ V` of the big fppf site of `S`, if small étale sheaves descend
effectively along the underlying morphism of schemes, then spaces-étale sheaves descend
effectively along the represented morphism of algebraic spaces. -/
theorem isEquivalence_toDescentData_schemeSpaceFunctor_map {V W : BigFppfOver B S hS}
    (m : W ⟶ V)
    (h : (smallEtaleSheafInverseImageDescentFunctor (associatedBigEtaleSite B)
      ((Over.forget (B.obj hS)).map m)).IsEquivalence) :
    ((spacesEtalePseudofunctor B S hS).toDescentData
      (fun _ : Unit ↦ (schemeSpaceFunctor B S hS).map m)).IsEquivalence := by
  let g : Unit → (W ⟶ V) := fun _ ↦ m
  have hG' : ((representedSchemesPseudofunctor B S hS).toDescentData g).IsEquivalence :=
    (Pseudofunctor.isEquivalence_toDescentData_restrict_iff
      (smallEtaleSheafInverseImagePseudofunctor (associatedBigEtaleSite B))
      (Over.forget (B.obj hS))
      (fun i j ↦ ChosenPullback.ofHasPullback (g i) (g j))
      (fun i j ↦ (ChosenPullback.ofHasPullback (g i) (g j)).isPullback.map _)
      (fun _ _ _ ↦ ChosenPullback₃.ofHasPullbacks _ _ _)
      (fun i j k ↦ (ChosenPullback₃.ofHasPullbacks
        (ChosenPullback.ofHasPullback (g i) (g j))
        (ChosenPullback.ofHasPullback (g j) (g k))
        (ChosenPullback.ofHasPullback (g i) (g k))).isPullback₂.map _)).2 h
  have hF' : ((representedSpacesPseudofunctor B S hS).toDescentData g).IsEquivalence :=
    ((representedComparison (B := B) (S := S) (hS := hS)).isEquivalence_toDescentData_iff g
      (fun a ↦ (inferInstance : (representedRestriction (B := B) (S := S) (hS := hS)
        a.as.unop (Type (u + 1))).IsEquivalence))).2 hG'
  have hpb : ∀ {P V₁ V₂ Z : BigFppfOver B S hS} {a : P ⟶ V₁} {b : P ⟶ V₂} {c : V₁ ⟶ Z}
      {d : V₂ ⟶ Z}, IsPullback a b c d →
      IsPullback ((schemeSpaceFunctor B S hS).map a) ((schemeSpaceFunctor B S hS).map b)
        ((schemeSpaceFunctor B S hS).map c) ((schemeSpaceFunctor B S hS).map d) :=
    fun hsq ↦ IsPullback.of_map_of_faithful (ObjectProperty.ι _) (hsq.map yoneda)
  exact (Pseudofunctor.isEquivalence_toDescentData_restrict_iff
    (spacesEtalePseudofunctor B S hS) (schemeSpaceFunctor B S hS)
    (fun i j ↦ ChosenPullback.ofHasPullback (g i) (g j))
    (fun i j ↦ hpb (ChosenPullback.ofHasPullback (g i) (g j)).isPullback)
    (fun _ _ _ ↦ ChosenPullback₃.ofHasPullbacks _ _ _)
    (fun i j k ↦ hpb (ChosenPullback₃.ofHasPullbacks
      (ChosenPullback.ofHasPullback (g i) (g j))
      (ChosenPullback.ofHasPullback (g j) (g k))
      (ChosenPullback.ofHasPullback (g i) (g k))).isPullback₂)).1 hF'

/-- **Effective descent along a singleton family transfers along an isomorphism of arrows.** For
a pseudofunctor `F` and morphisms `m : X₁ ⟶ Y₁`, `f : X₂ ⟶ Y₂` with isomorphisms
`eX : X₁ ≅ X₂`, `eY : Y₂ ≅ Y₁` such that `eX.hom ≫ f ≫ eY.hom = m`, effective descent along `m`
gives effective descent along `f`. -/
theorem _root_.CategoryTheory.Pseudofunctor.isEquivalence_toDescentData_singleton_of_arrowIso
    {C : Type*} [Category C] (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat)
    {X₁ Y₁ X₂ Y₂ : C} (m : X₁ ⟶ Y₁) (f : X₂ ⟶ Y₂) (eX : X₁ ≅ X₂) (eY : Y₂ ≅ Y₁)
    (w : eX.hom ≫ f ≫ eY.hom = m)
    (h : (F.toDescentData (fun _ : Unit ↦ m)).IsEquivalence) :
    (F.toDescentData (fun _ : Unit ↦ f)).IsEquivalence := by
  have w₁ : ∀ _ : Unit, eX.inv ≫ m = f ≫ eY.hom := fun _ ↦ by
    rw [← w, Iso.inv_hom_id_assoc]
  have w₂ : ∀ _ : Unit, eX.hom ≫ f = m ≫ eY.inv := fun _ ↦ by
    rw [← w, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let E := Pseudofunctor.DescentData.pullFunctorEquivalence F (X := fun _ : Unit ↦ X₁)
    (f := fun _ : Unit ↦ m) (X' := fun _ : Unit ↦ X₂) (f' := fun _ : Unit ↦ f) eY (α := id)
    (p' := fun _ ↦ eX.inv) w₁ (β := id) (q' := fun _ ↦ eX.hom) w₂
  have : (Pseudofunctor.DescentData.pullFunctor F (X := fun _ : Unit ↦ X₁)
      (f := fun _ : Unit ↦ m) (X' := fun _ : Unit ↦ X₂) (f' := fun _ : Unit ↦ f)
      (p := eY.hom) (α := id) (p' := fun _ ↦ eX.inv) w₁).IsEquivalence :=
    E.isEquivalence_functor
  have : ((F.map eY.hom.op.toLoc).toFunctor ⋙ F.toDescentData (fun _ : Unit ↦ f)).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F (X := fun _ : Unit ↦ X₁)
        (f := fun _ : Unit ↦ m) (X' := fun _ : Unit ↦ X₂) (f' := fun _ : Unit ↦ f)
        (p := eY.hom) (α := id) (p' := fun _ ↦ eX.inv) w₁ :
        F.toDescentData (fun _ : Unit ↦ m) ⋙ E.functor ≅ _)
  exact Functor.isEquivalence_of_comp_left (F.map eY.hom.op.toLoc).toFunctor _

/-- **The case of Stacks 0GFU with a representable target, from the scheme case.** Let `Q` be a
property of morphisms of schemes along which small étale sheaves descend effectively. Then
spaces-étale sheaves descend effectively along every morphism of algebraic spaces with
representable target all of whose represented base changes have `Q`. -/
theorem spacesEtaleDescentOverRepresentable_of_smallEtale (Q : MorphismProperty Scheme.{u})
    (hdesc : ∀ ⦃X Y : (associatedBigEtaleSite B).Scheme⦄ (h : X ⟶ Y),
      Q ((associatedBigEtaleSite B).inclusion.map h) →
      (smallEtaleSheafInverseImageDescentFunctor (associatedBigEtaleSite B) h).IsEquivalence) :
    SpacesEtaleDescentOverRepresentable B S hS
      (MorphismProperty.inverseImage Q (BigFppfOver.toScheme B S hS)).presheaf := by
  intro X' Y' f' hY hQ
  let a : yoneda.obj Y'.1.reprX ≅ Y'.1 := Y'.1.reprW
  have hrep := hQ.rep
  let m : hrep.pullback a.hom ⟶ Y'.1.reprX := hrep.snd a.hom
  have hm : Q ((BigFppfOver.toScheme B S hS).map m) := hQ.property_snd a.hom
  have hsq : IsPullback (hrep.fst a.hom) (yoneda.map m) f'.hom a.hom := hrep.isPullback a.hom
  let eX : (schemeSpaceFunctor B S hS).obj (hrep.pullback a.hom) ≅ X' :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ (hrep.fst a.hom) hsq.isIso_fst_of_isIso)
  let eY : Y' ≅ (schemeSpaceFunctor B S hS).obj Y'.1.reprX := ObjectProperty.isoMk _ a.symm
  refine Pseudofunctor.isEquivalence_toDescentData_singleton_of_arrowIso _
    ((schemeSpaceFunctor B S hS).map m) f' eX eY ?_
    (isEquivalence_toDescentData_schemeSpaceFunctor_map B S hS m (hdesc _ hm))
  apply ObjectProperty.hom_ext
  show hrep.fst a.hom ≫ f'.hom ≫ a.inv = yoneda.map m
  rw [← Category.assoc, hsq.w, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Effective descent of small étale sheaves along a surjective flat morphism locally of finite
presentation (Stacks 0GF2), for the pseudofunctor of small étale sheaves and their inverse
images. -/
@[sga "4 VIII 9.4"]
theorem _root_.AlgebraicGeometry.smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_fppf
    (E : BigEtaleSite.{u}) {X Y : E.Scheme} (f : X ⟶ Y) [Surjective (E.inclusion.map f)]
    [Flat (E.inclusion.map f)] [LocallyOfFinitePresentation (E.inclusion.map f)] :
    (smallEtaleSheafInverseImageDescentFunctor E f).IsEquivalence := by
  have h : ((eqToHom ((smallEtaleSheafPullbackSystemGeneral E).fiber Y).symm).toFunctor ⋙
      smallEtaleSheafInverseImageDescentFunctor E f).IsEquivalence :=
    smallEtaleSheafDescentFunctor_isEquivalence_of_fppf_unconditional E f
  have : (eqToHom ((smallEtaleSheafPullbackSystemGeneral E).fiber Y).symm).toFunctor.IsEquivalence
      := by
    have gen : ∀ {A A' : Cat.{u + 1, u + 2}} (h : A = A'), (eqToHom h).toFunctor.IsEquivalence := by
      rintro A _ rfl
      exact (inferInstance : (𝟭 A).IsEquivalence)
    exact gen _
  exact Functor.isEquivalence_of_comp_left
    (eqToHom ((smallEtaleSheafPullbackSystemGeneral E).fiber Y).symm).toFunctor _

/-! ### Stacks 0GFU and 0GFV -/

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is representable (by
schemes) and is surjective and integral, or surjective and proper, or surjective, flat and locally
of finite presentation. Then the functor from sheaves on the spaces-étale site of `Y` (that is,
`Sh(Y_étale)`, Stacks 03G1) to descent data for étale sheaves with respect to `{X ⟶ Y}` is an
equivalence of categories. -/
@[stacks 0GFU]
theorem isEquivalence_toDescentData_singleton_of_relativelyRepresentable
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (hf : IsSurjectiveIntegralProperOrFlatLfp B S hS f) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence := by
  have hsurj : IsSurjective B S hS f.hom →
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f.hom :=
    presheafSurjective_of_isSurjective B S hS f.hom hrep
  rcases hf with ⟨hs, hi⟩ | ⟨hs, hp⟩ | ⟨hs, hfl, hlfp⟩
  · refine isEquivalence_toDescentData_singleton_of_surjective_integral B S hS
      (spacesEtaleDescentOverRepresentable_of_smallEtale B S hS _ fun _ _ h ⟨_, _⟩ ↦ ?_) f
      (hsurj hs) ((isIntegralHom_iff_representable B S hS f.hom X.property Y.property).1 hi).2
    exact smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_isIntegralHom_of_surjective _ h
  · refine isEquivalence_toDescentData_singleton_of_surjective_proper B S hS
      (spacesEtaleDescentOverRepresentable_of_smallEtale B S hS _ fun _ _ h ⟨_, _⟩ ↦ ?_) f
      (hsurj hs) ((presheaf_isProper_iff B S hS f.hom X.property Y.property hrep).1 hp)
    exact smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_surjective_proper _ h
  · refine isEquivalence_toDescentData_singleton_of_surjective_flat_locallyOfFinitePresentation
      B S hS
      (spacesEtaleDescentOverRepresentable_of_smallEtale B S hS _ fun _ _ h ⟨⟨_, _⟩, _⟩ ↦ ?_) f
      (hsurj hs) ((isFlat_iff_presheaf B S hS X.property Y.property hrep).1 hfl)
      ((isLocallyOfFinitePresentation_iff_presheaf B S hS X.property Y.property hrep).1 hlfp)
    exact smallEtaleSheafInverseImageDescentFunctor_isEquivalence_of_fppf _ h

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` and let `π : X' ⟶ X` be a
morphism of algebraic spaces. Assume that `π ≫ f` is representable (by schemes) and is surjective
and integral, or surjective and proper, or surjective, flat and locally of finite presentation.
Then the functor from sheaves on the spaces-étale site of `Y` to descent data for étale sheaves
with respect to `{X ⟶ Y}` is an equivalence of categories. -/
@[stacks 0GFV]
theorem isEquivalence_toDescentData_singleton_of_relativelyRepresentable_comp
    {X' X Y : AlgebraicSpaces B S hS} (π : X' ⟶ X) (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable (π ≫ f).hom)
    (hcov : IsSurjectiveIntegralProperOrFlatLfp B S hS (π ≫ f)) :
    ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence :=
  isEquivalence_toDescentData_singleton_of_representable_comp B S hS
    (fun f₀ hrep₀ hf₀ ↦ isEquivalence_toDescentData_singleton_of_relativelyRepresentable B S hS f₀
      hrep₀ hf₀) π f hrep hcov

end AlgebraicGeometry.Space

end
