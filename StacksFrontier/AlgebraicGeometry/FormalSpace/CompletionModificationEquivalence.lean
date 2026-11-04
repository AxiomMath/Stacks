module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionEssentialSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Dilatations
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationOutputProper

/-!
# Stacks 0ARB and Stacks 0GDU

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a locally Noetherian algebraic
space over `S`, let `T ⊆ |X|` be closed and let `U ⊂ X` be the open subspace with
`|U| = |X| ∖ T`.

**Stacks 0ARB**: the completion functor of Stacks 0AR5,
`AlgebraicGeometry.FormalSpace.completionModificationFunctor`, is an equivalence. Full
faithfulness is Stacks 0GDR. For essential surjectivity, take an object `g : W ⟶ X_{/T}`. Over
every affine étale chart `Spec R ⟶ X` (`R` Noetherian), the base change
`W ×_{X/T} (Spec R)_{/T}` is an object of the right-hand category for `Spec R`
(`AlgebraicGeometry.FormalSpace.rigEtaleOverCompletionBaseChange`, through Stacks 0GD1). It is
therefore algebraized by Stacks 0ARA
(`AlgebraicGeometry.FormalSpace.exists_finiteTypeModification_completion_iso_of_isRigEtale`), and
the algebraizations glue by 0GDR and 0ADV
(`AlgebraicGeometry.FormalSpace.mem_essImage_completionModificationFunctor_of_affine_charts`).

**Stacks 0GDU** (Artin's theorem on dilatations): every formal modification `𝔣 : 𝔛' ⟶ X_{/T}`
is the completion of a proper morphism `f : X' ⟶ X` which is an isomorphism over `U`, and `f`
is unique up to unique isomorphism. This follows from Stacks 0ARB and Stacks 0ARX
(`AlgebraicGeometry.FormalSpace.isProper_iff_isFormalModification_of_iso`).

## Main results

* `AlgebraicGeometry.FormalSpace.isEquivalence_completionModificationFunctor`: Stacks 0ARB.
* `AlgebraicGeometry.FormalSpace.exists_isProper_completion_iso_of_isFormalModification`: Stacks
  0GDU, existence.
* `AlgebraicGeometry.FormalSpace.existsUnique_completionOverFunctor_map_comp_eq_of_isProper`:
  Stacks 0GDU, uniqueness.

## References

* [Stacks Project, Tag 0ARB](https://stacks.math.columbia.edu/tag/0ARB)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0ARX](https://stacks.math.columbia.edu/tag/0ARX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.pointTopology

/-! ### Stacks 0ARB -/

/-- **Stacks 0ARB.** Let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
closed and let `U ⊂ X` be the open subspace with `|U| = |X| ∖ T`. The completion functor of
Stacks 0AR5 sends `f : X' ⟶ X` to `f_{/T} : X'_{/T'} ⟶ X_{/T}`. Its source is the morphisms of
algebraic spaces which are locally of finite type and an isomorphism over `U`. Its target is the
morphisms `g : W ⟶ X_{/T}` of formal algebraic spaces with `W` locally Noetherian and `g`
rig-étale. This functor is an equivalence.

Full faithfulness is Stacks 0GDR (`completionModificationFunctorFullyFaithful`). For essential
surjectivity, the base change of `W` to each affine étale chart `Spec R ⟶ X`, `R` Noetherian, is
an object of the right-hand category for `Spec R` (`rigEtaleOverCompletionBaseChange`, through
Stacks 0GD1). By Stacks 0ARA
(`exists_finiteTypeModification_completion_iso_of_isRigEtale`) it is the completion of a
finite-type modification of `Spec R`. These glue
(`mem_essImage_completionModificationFunctor_of_affine_charts`). -/
@[stacks 0ARB]
theorem isEquivalence_completionModificationFunctor {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Set (Space.points B S hS X)) (hT : IsClosed T) (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X) :
    (completionModificationFunctor T hT hXsp hX).IsEquivalence := by
  have hff := completionModificationFunctorFullyFaithful T hT hXsp hX
  have := hff.full
  have := hff.faithful
  have : (completionModificationFunctor T hT hXsp hX).EssSurj := ⟨fun W ↦
    mem_essImage_completionModificationFunctor_of_affine_charts T hT hXsp hX W
      fun R _ hRn hR s e he ↦ by
        have := hRn
        let W' := rigEtaleOverCompletionBaseChange hXsp hX hT W
          (isAlgebraicSpace_yoneda B S hS (affineOver B S hS hR s)) e he
        exact exists_finiteTypeModification_completion_iso_of_isRigEtale hR s _
          (hT.preimage (Space.continuous_pointsMap B S hS e)) W'.property.2.1 W'.obj.hom
          W'.property.2.2⟩
  exact { }

/-! ### Stacks 0GDU -/

/-- **Stacks 0GDU, existence.** Let `X` be a locally Noetherian algebraic space over `S`, let
`T ⊆ |X|` be closed, `U ⊂ X` the open subspace with `|U| = |X| ∖ T`, and let
`𝔣 : 𝔛' ⟶ X_{/T}` be a formal modification (Definition 0GDK). Then there is a proper morphism
`f : X' ⟶ X` of algebraic spaces which is an isomorphism over `U` and whose completion `f_{/T}`
is isomorphic to `𝔣` over `X_{/T}`.

By Stacks 0ARB (`isEquivalence_completionModificationFunctor`), `𝔣`, an object of the
right-hand category of Stacks 0AR5, is the completion of a finite-type modification `f`; by
Stacks 0ARX (`isProper_iff_isFormalModification_of_iso`) `f` is proper. -/
@[stacks 0GDU "existence: a proper f : X' ⟶ X, isomorphism over U, with f_{/T} ≅ 𝔣 over X_{/T}"]
theorem exists_isProper_completion_iso_of_isFormalModification
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X) (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    {W : FppfSheaf B S hS} {𝔣 : W ⟶ Space.completionSheaf B S hS X T}
    (h𝔣 : IsFormalModification B S hS 𝔣) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X') (f : X' ⟶ X),
      Space.IsProper B S hS f ∧ IsIso (pullback.snd f (Space.openSubspaceOfPoints B S hS X Tᶜ).ι) ∧
        Nonempty ((Space.completionOverFunctor B S hS T).obj (Over.mk f) ≅ Over.mk 𝔣) := by
  have := isEquivalence_completionModificationFunctor T hT hXsp hX
  let F := completionModificationFunctor T hT hXsp hX
  let P := rigEtaleOverCompletionOfIsFormalModification h𝔣
  let M := F.objPreimage P
  let e : (Space.completionOverFunctor B S hS T).obj M.obj ≅ P.obj :=
    (ObjectProperty.ι _).mapIso (F.objObjPreimageIso P)
  exact ⟨M.obj.left, M.property.1.1, M.obj.hom,
    (isProper_iff_isFormalModification_of_iso hXsp hX T hT M P e).2 h𝔣, M.property.1.2, ⟨e⟩⟩

/-- If `F` is injective on endomorphisms of `A` and `φ : A ⟶ B`, `ψ : B ⟶ A` map to
`e.hom ≫ e'.inv` and `e'.hom ≫ e.inv`, then `φ ≫ ψ = 𝟙 A`. -/
private theorem comp_eq_id_of_map_eq_comp_inv {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {A B : C} {M : D} (hF : Function.Injective (F.map : (A ⟶ A) → _)) (e : F.obj A ≅ M)
    (e' : F.obj B ≅ M) {φ : A ⟶ B} {ψ : B ⟶ A} (hφ : F.map φ = e.hom ≫ e'.inv)
    (hψ : F.map ψ = e'.hom ≫ e.inv) : φ ≫ ψ = 𝟙 A :=
  hF (by rw [F.map_comp, F.map_id, hφ, hψ, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id])

/-- **Stacks 0GDU, uniqueness.** In the situation of
`exists_isProper_completion_iso_of_isFormalModification`, let `f₁ : X₁ ⟶ X` and `f₂ : X₂ ⟶ X`
be proper morphisms of algebraic spaces which are isomorphisms over `U`, with isomorphisms
`e₁ : f₁_{/T} ≅ 𝔣` and `e₂ : f₂_{/T} ≅ 𝔣` over `X_{/T}`. Then there is exactly one morphism
`φ : X₁ ⟶ X₂` over `X` whose completion is compatible with `e₁` and `e₂`, and it is an
isomorphism. So `f` is unique up to unique isomorphism.

This is Stacks 0GDR (`AlgebraicGeometry.Space.completionOverFunctor_map_bijective`), which holds
because a proper morphism is locally of finite type. -/
@[stacks 0GDU "uniqueness: any two such proper f₁, f₂ are isomorphic over X by a unique \
isomorphism compatible with the identifications of f₁_{/T} and f₂_{/T} with 𝔣"]
theorem existsUnique_completionOverFunctor_map_comp_eq_of_isProper
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXsp : IsAlgebraicSpace B S hS X)
    (hX : Space.IsLocallyNoetherian B S hS X) (T : Set (Space.points B S hS X)) (hT : IsClosed T)
    {W : FppfSheaf B S hS} (𝔣 : W ⟶ Space.completionSheaf B S hS X T)
    {X₁ X₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX₁ : IsAlgebraicSpace B S hS X₁)
    (hX₂ : IsAlgebraicSpace B S hS X₂) {f₁ : X₁ ⟶ X} {f₂ : X₂ ⟶ X}
    (hf₁ : Space.IsProper B S hS f₁) (hf₂ : Space.IsProper B S hS f₂)
    (hU₁ : IsIso (pullback.snd f₁ (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hU₂ : IsIso (pullback.snd f₂ (Space.openSubspaceOfPoints B S hS X Tᶜ).ι))
    (e₁ : (Space.completionOverFunctor B S hS T).obj (Over.mk f₁) ≅ Over.mk 𝔣)
    (e₂ : (Space.completionOverFunctor B S hS T).obj (Over.mk f₂) ≅ Over.mk 𝔣) :
    ∃! φ : Over.mk f₁ ⟶ Over.mk f₂,
      (Space.completionOverFunctor B S hS T).map φ ≫ e₂.hom = e₁.hom ∧ IsIso φ := by
  have hN := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyNoetherian hXsp hX
  have hN₁ := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType hX₁ hXsp f₁
    hf₁.2.1.1 hN
  have hN₂ := hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType hX₂ hXsp f₂
    hf₂.2.1.1 hN
  have bij₁₂ := Space.completionOverFunctor_map_bijective hXsp hN hT hX₂ hf₂.2.1.1 hU₂ f₁ hX₁ hN₁
  have bij₂₁ := Space.completionOverFunctor_map_bijective hXsp hN hT hX₁ hf₁.2.1.1 hU₁ f₂ hX₂ hN₂
  have bij₁₁ := Space.completionOverFunctor_map_bijective hXsp hN hT hX₁ hf₁.2.1.1 hU₁ f₁ hX₁ hN₁
  have bij₂₂ := Space.completionOverFunctor_map_bijective hXsp hN hT hX₂ hf₂.2.1.1 hU₂ f₂ hX₂ hN₂
  obtain ⟨φ, hφ⟩ := bij₁₂.2 (e₁.hom ≫ e₂.inv)
  obtain ⟨ψ, hψ⟩ := bij₂₁.2 (e₂.hom ≫ e₁.inv)
  have hφ' : (Space.completionOverFunctor B S hS T).map φ = e₁.hom ≫ e₂.inv := hφ
  have hψ' : (Space.completionOverFunctor B S hS T).map ψ = e₂.hom ≫ e₁.inv := hψ
  have h₁ := comp_eq_id_of_map_eq_comp_inv bij₁₁.1 e₁ e₂ hφ' hψ'
  have h₂ := comp_eq_id_of_map_eq_comp_inv bij₂₂.1 e₂ e₁ hψ' hφ'
  refine ⟨φ, ⟨by rw [hφ', Category.assoc, Iso.inv_hom_id, Category.comp_id], ⟨ψ, h₁, h₂⟩⟩,
    fun φ' hφ'' ↦ bij₁₂.1 ?_⟩
  show (Space.completionOverFunctor B S hS T).map φ' =
    (Space.completionOverFunctor B S hS T).map φ
  rw [hφ', ← hφ''.1, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.FormalSpace

end
