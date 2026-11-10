module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleAugmentation
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphismsTwoSquare

/-!
# Base change and forgetting the degree on constant simplicial algebraic spaces

Let `f : Z₁ ⟶ Z₂` be a morphism of algebraic spaces and `c : const(Z₁) ⟶ const(Z₂)` the induced
morphism of constant simplicial algebraic spaces. Forgetting the simplicial degree commutes with
base change: `constForget Z₁ ∘ c_étale = f_étale ∘ constForget Z₂` on the spaces-étale sites. This
file shows that this square is Guitart exact, so that the direct image `ε_*` of forgetting the
degree (a right Kan extension) commutes with base change:
`f⁻¹ ∘ ε_{Z₁,*} ≅ ε_{Z₂,*} ∘ c⁻¹` on sheaves.

## Main definitions

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.constForgetTwoSquare`: the square
  `c_étale ⋙ constForget Z₁ ⟶ constForget Z₂ ⋙ f_étale`, whose components are identities.
* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.constExchangeIso`: the exchange isomorphism
  of sheaves of sets.

## Main results

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.guitartExact_constForgetTwoSquare`: the square
  is Guitart exact. For `g : U'/Z₁ ⟶ V ×_{Z₂} Z₁` with `U'` in degree `n`, every factorization of
  `g` through an object `W/Z₂` of degree `m` is joined, through the same object placed in degree
  `n`, to the factorization through `V/Z₂` in degree `n`.
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Z₁ Z₂ : AlgebraicSpaces B S hS} (f : Z₁ ⟶ Z₂)

/-! ### The morphism of ringed topoi of a morphism of algebraic spaces -/

/-- The structure map `f♯ : 𝒪_{Z₂} ⟶ f_*𝒪_{Z₁}` of the spaces-étale sites: pullback of global
regular functions along the projections `V ×_{Z₂} Z₁ ⟶ V`. -/
noncomputable def spacesEtaleStructureSharp :
    SpacesEtale.structureSheaf B S hS Z₂ ⟶
      ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous CommRingCat.{u + 1}
        (SpacesEtale.topology B S hS Z₂) (SpacesEtale.topology B S hS Z₁)).obj
        (SpacesEtale.structureSheaf B S hS Z₁) where
  hom := Functor.whiskerRight (NatTrans.op (spacesBaseChange B S hS f).projection)
    (globalFunctionsPresheaf B S hS)

/-- **Stacks 0DE7.** The morphism of ringed topoi
`f : (Sh(Z₁,spaces,étale), 𝒪_{Z₁}) ⟶ (Sh(Z₂,spaces,étale), 𝒪_{Z₂})` of a morphism of algebraic
spaces: the morphism of topoi of base change, with structure map `f♯`. -/
noncomputable def spacesEtaleRingedToposHom :
    RingedToposHom (spacesEtaleRingedTopos B S hS Z₁) (spacesEtaleRingedTopos B S hS Z₂) where
  toToposHom := (spacesBaseChange_isMorphismOfSites B S hS f).morphismOfTopoi
  fSharp := spacesEtaleStructureSharp f ≫ (Stacks.Sheaves.ToposPullback.restrictionCommRingIso
    (SpacesEtale.topology B S hS Z₂) (SpacesEtale.topology B S hS Z₁)
    (spacesBaseChange B S hS f).functor (SpacesEtale.structureSheaf B S hS Z₁)).inv

/-! ### Forgetting the degree commutes with base change -/

/-- On the constant simplicial algebraic spaces, base change along `c = const(f)` followed by
forgetting the degree is base change along `f` of the forgotten object, on morphisms. -/
theorem constForget_map_pullbackFunctor_map
    {V W : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z₂)} (g : V ⟶ W) :
    (constForget Z₁).map ((pullbackFunctor ((Functor.const _).map f)).map g) =
      (spacesBaseChange B S hS f).functor.map ((constForget Z₂).map g) := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · exact ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).trans
      (pullback.lift_snd _ _ _).symm

/-- The square `c_étale ⋙ constForget Z₁ ≅ constForget Z₂ ⋙ f_étale`, with identity
components. -/
noncomputable def constForgetSquareIso :
    pullbackFunctor ((Functor.const _).map f) ⋙ constForget Z₁ ≅
      constForget Z₂ ⋙ (spacesBaseChange B S hS f).functor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun g ↦
    (Category.comp_id _).trans ((constForget_map_pullbackFunctor_map f g).trans
      (Category.id_comp _).symm))

/-- The `2`-square `c_étale ⋙ constForget Z₁ ⟶ constForget Z₂ ⋙ f_étale`. -/
noncomputable abbrev constForgetTwoSquare :
    TwoSquare (pullbackFunctor ((Functor.const _).map f)) (constForget Z₂) (constForget Z₁)
      (spacesBaseChange B S hS f).functor :=
  (constForgetSquareIso f).hom

/-- The components of `constForgetTwoSquare f` are identities. -/
theorem constForgetTwoSquare_app (V : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z₂)) :
    (constForgetTwoSquare f).app V = 𝟙 _ := rfl

section GuitartExact

variable {f} {X₂ : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z₁)}
  {X₃ : SpacesEtale B S hS Z₂}
  (g : (constForget Z₁).obj X₂ ⟶ (spacesBaseChange B S hS f).functor.obj X₃)

/-- The factorization of `g` through `X₃` placed in the degree of `X₂`. -/
noncomputable def canonicalLift :
    X₂ ⟶ (pullbackFunctor ((Functor.const _).map f)).obj ⟨X₂.degree, X₃⟩ :=
  ⟨𝟙 _, g.hom.left, (Over.w g.hom).trans (Category.comp_id _).symm⟩

/-- The lift `canonicalLift g`, followed by the square and by the identity of `X₃`, recovers `g`.
-/
theorem canonicalLift_comm :
    (constForget Z₁).map (canonicalLift g) ≫ (constForgetTwoSquare f).app ⟨X₂.degree, X₃⟩ ≫
      (spacesBaseChange B S hS f).functor.map (𝟙 X₃) = g := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  exact (whisker_eq g.hom.left ((Category.id_comp _).trans (congrArg (fun k ↦ k.hom.left)
    ((spacesBaseChange B S hS f).functor.map_id X₃)))).trans (Category.comp_id _)

/-- The canonical object of `(constForgetTwoSquare f).StructuredArrowRightwards g`. -/
noncomputable abbrev canonicalObj : (constForgetTwoSquare f).StructuredArrowRightwards g :=
  TwoSquare.StructuredArrowRightwards.mk _ g ⟨X₂.degree, X₃⟩ (canonicalLift g) (𝟙 X₃)
    (canonicalLift_comm g)

variable {g}

/-- Every object of `(constForgetTwoSquare f).StructuredArrowRightwards g` is joined by a zigzag
to the canonical one. -/
theorem zigzag_canonicalObj (j : (constForgetTwoSquare f).StructuredArrowRightwards g) :
    Zigzag j (canonicalObj g) := by
  obtain ⟨X₁, a, b, comm, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective j
  let X₁' : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj Z₂) := ⟨X₂.degree, X₁.obj⟩
  let a' : X₂ ⟶ (pullbackFunctor ((Functor.const _).map f)).obj X₁' := ⟨𝟙 _, a.hom, a.w⟩
  let j' : (constForgetTwoSquare f).StructuredArrowRightwards g :=
    TwoSquare.StructuredArrowRightwards.mk _ g X₁' a' b comm
  let m₁ : X₁' ⟶ X₁ := ⟨a.base, 𝟙 _, (Category.id_comp _).trans (Category.comp_id _).symm⟩
  let m₂ : X₁' ⟶ ⟨X₂.degree, X₃⟩ :=
    ⟨𝟙 _, b.hom.left, (Over.w b.hom).trans (Category.comp_id _).symm⟩
  have hm₁ : (constForget Z₂).map m₁ = 𝟙 _ :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl)
  have hm₂ : (constForget Z₂).map m₂ = b :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext rfl)
  have e : ∀ {Y} (m : X₁' ⟶ Y), (a' ≫ (pullbackFunctor ((Functor.const _).map f)).map m).hom =
      a.hom ≫ ((spacesBaseChange B S hS f).functor.map ((constForget Z₂).map m)).hom.left :=
    fun m ↦ congrArg (a.hom ≫ ·) (congrArg (fun k ↦ k.hom.left)
      (constForget_map_pullbackFunctor_map f m))
  have e₁ : a' ≫ (pullbackFunctor ((Functor.const _).map f)).map m₁ = a :=
    Hom.ext (Category.comp_id _) (by
      erw [e, hm₁, (spacesBaseChange B S hS f).functor.map_id]
      exact Category.comp_id _)
  have e₂ : a' ≫ (pullbackFunctor ((Functor.const _).map f)).map m₂ = canonicalLift g :=
    Hom.ext (Category.comp_id _) (by
      rw [e, hm₂]
      have hc := congrArg (fun k ↦ k.hom.left) comm
      change a.hom ≫ (𝟙 _ ≫ ((spacesBaseChange B S hS f).functor.map b).hom.left) =
        g.hom.left at hc
      exact (whisker_eq _ (Category.id_comp _).symm).trans hc)
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.single (b := j') (Or.inr ⟨?_⟩))
    (Or.inl ⟨?_⟩)
  · refine StructuredArrow.homMk (CostructuredArrow.homMk m₁ ?_) ?_
    · exact (eq_whisker hm₁ _).trans (Category.id_comp _)
    · exact CostructuredArrow.hom_ext _ _ e₁
  · refine StructuredArrow.homMk (CostructuredArrow.homMk m₂ ?_) ?_
    · exact (eq_whisker hm₂ _).trans (Category.comp_id _)
    · exact CostructuredArrow.hom_ext _ _ e₂

end GuitartExact

/-- **Stacks 0DE7.** Forgetting the degree commutes with base change in a Guitart exact square:
the categories of factorizations of an arrow `U'/Z₁ ⟶ V ×_{Z₂} Z₁` through the square are
connected. -/
instance guitartExact_constForgetTwoSquare : (constForgetTwoSquare f).GuitartExact := by
  rw [TwoSquare.guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ g
  have : Nonempty ((constForgetTwoSquare f).StructuredArrowRightwards g) := ⟨canonicalObj g⟩
  exact zigzag_isConnected fun j₁ j₂ ↦
    (zigzag_canonicalObj j₁).trans (zigzag_symm.symm _ _ (zigzag_canonicalObj j₂))

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the (co)continuity of the sheaf pushforwards in the statement
/-- **Stacks 0DE7.** The direct image of forgetting the degree commutes with base change:
`ε_{Z₂,*} ∘ c⁻¹ ≅ f⁻¹ ∘ ε_{Z₁,*}` on sheaves of sets, i.e.
`Ran_{ε₂}(F ∘ c_étale) ≅ (Ran_{ε₁} F) ∘ f_étale`. -/
noncomputable def constExchangeIso :
    (pullbackFunctor ((Functor.const _).map f)).sheafPushforwardContinuous (Type (u + 1))
        (topology ((Functor.const _).obj Z₂)) (topology ((Functor.const _).obj Z₁)) ⋙
      (constForget Z₂).sheafPushforwardCocontinuous (Type (u + 1))
        (topology ((Functor.const _).obj Z₂)) (SpacesEtale.topology B S hS Z₂) ≅
    (constForget Z₁).sheafPushforwardCocontinuous (Type (u + 1))
        (topology ((Functor.const _).obj Z₁)) (SpacesEtale.topology B S hS Z₁) ⋙
      (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type (u + 1))
        (SpacesEtale.topology B S hS Z₂) (SpacesEtale.topology B S hS Z₁) :=
  Stacks.Sites.CocontinuousExchange.sheafIsoOfTwoSquareAndMorphismsTwoSquare (Type (u + 1)) _ _ _ _
    (constForgetTwoSquare f)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
