module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Base change of an algebraic space along a system of schemes

Let `X₀` be an algebraic space over `S` and `V` a scheme over `S`. The base change
`X₀ ×_S V` is the product presheaf `h_V ⨯ X₀`, an algebraic space over `S`. A system of schemes
`T : I ⥤ (Sch/S)` with a limit `c` gives the system `h_{T i} ⨯ X₀` of base changes and the base
change `h_{c.pt} ⨯ X₀` to the limit, with the projections induced by `c`.

## Main definitions

* `AlgebraicGeometry.Space.productSpace`: the base change `h_V ⨯ X₀`.
* `AlgebraicGeometry.Space.productSpaceMap`: the morphism of base changes induced by a morphism
  of schemes over `S`.
* `AlgebraicGeometry.Space.productSpaceFst`, `AlgebraicGeometry.Space.productSpaceSnd`: the two
  projections.

## Main results

* `AlgebraicGeometry.Space.isPullback_productSpaceMap`: the base change along a morphism of
  schemes is cartesian over that morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X₀ : AlgebraicSpaces B S hS)

/-- The base change `X₀ ×_S V = h_V ⨯ X₀` of an algebraic space over `S` to a scheme over
`S`. -/
noncomputable def productSpace (V : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj V ⨯ X₀.1, isAlgebraicSpace_prod_yoneda_obj V X₀.2⟩

/-- The morphism of base changes induced by a morphism of schemes over `S`. -/
noncomputable def productSpaceMap {V V' : BigFppfOver B S hS} (k : V ⟶ V') :
    productSpace X₀ V ⟶ productSpace X₀ V' :=
  ObjectProperty.homMk (prod.map (yoneda.map k) (𝟙 X₀.1))

/-- The underlying morphism of presheaves of `productSpaceMap X₀ k` is `yoneda.map k ⨯ 𝟙 X₀`. -/
theorem productSpaceMap_hom {V V' : BigFppfOver B S hS} (k : V ⟶ V') :
    (productSpaceMap X₀ k).hom = prod.map (yoneda.map k) (𝟙 X₀.1) :=
  rfl

/-- The base change of the identity of `V` is the identity. -/
theorem productSpaceMap_id (V : BigFppfOver B S hS) :
    productSpaceMap X₀ (𝟙 V) = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  show prod.map (yoneda.map (𝟙 V)) (𝟙 X₀.1) = 𝟙 _
  rw [yoneda.map_id, prod.map_id_id]

/-- The base change of a composite is the composite of the base changes. -/
theorem productSpaceMap_comp {V V' V'' : BigFppfOver B S hS} (k : V ⟶ V') (k' : V' ⟶ V'') :
    productSpaceMap X₀ (k ≫ k') = productSpaceMap X₀ k ≫ productSpaceMap X₀ k' := by
  apply ObjectProperty.hom_ext
  show prod.map (yoneda.map (k ≫ k')) (𝟙 X₀.1) =
    prod.map (yoneda.map k) (𝟙 X₀.1) ≫ prod.map (yoneda.map k') (𝟙 X₀.1)
  rw [prod.map_map, yoneda.map_comp, Category.comp_id]

/-- The projection of the base change to the scheme. -/
noncomputable def productSpaceFst (V : BigFppfOver B S hS) :
    productSpace X₀ V ⟶ schemeSpace V :=
  ObjectProperty.homMk prod.fst

/-- The projection of the base change to `X₀`. -/
noncomputable def productSpaceSnd (V : BigFppfOver B S hS) : productSpace X₀ V ⟶ X₀ :=
  ObjectProperty.homMk prod.snd

/-- The base change of `k` commutes with the projections to the schemes and with `k`. -/
theorem productSpaceMap_fst {V V' : BigFppfOver B S hS} (k : V ⟶ V') :
    productSpaceMap X₀ k ≫ productSpaceFst X₀ V' = productSpaceFst X₀ V ≫ schemeSpaceMap k :=
  ObjectProperty.hom_ext _ (prod.map_fst _ _)

/-- The base change of `k` commutes with the projections to `X₀`. -/
theorem productSpaceMap_snd {V V' : BigFppfOver B S hS} (k : V ⟶ V') :
    productSpaceMap X₀ k ≫ productSpaceSnd X₀ V' = productSpaceSnd X₀ V :=
  ObjectProperty.hom_ext _ ((prod.map_snd _ _).trans (Category.comp_id _))

/-- The base change along a morphism of schemes is cartesian over it. -/
theorem isPullback_productSpaceMap {V V' : BigFppfOver B S hS} (k : V ⟶ V') :
    IsPullback (prod.map (yoneda.map k) (𝟙 X₀.1)) (prod.fst : yoneda.obj V ⨯ X₀.1 ⟶ _)
      (prod.fst : yoneda.obj V' ⨯ X₀.1 ⟶ _) (yoneda.map k) := by
  refine IsPullback.of_isLimit' ⟨prod.map_fst _ _⟩ ?_
  refine PullbackCone.IsLimit.mk _
    (fun s => prod.lift (PullbackCone.snd s) (PullbackCone.fst s ≫ prod.snd)) ?_ ?_ ?_
  · intro s
    apply prod.hom_ext
    · rw [Category.assoc, prod.map_fst, prod.lift_fst_assoc]
      exact (PullbackCone.condition s).symm
    · rw [Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd]
  · exact fun s => prod.lift_fst _ _
  · intro s m h₁ h₂
    apply prod.hom_ext
    · rwa [prod.lift_fst]
    · rw [prod.lift_snd, ← h₁, Category.assoc, prod.map_snd, Category.comp_id]

/-- The base change along a morphism of schemes is representable. -/
theorem relativelyRepresentable_productSpaceMap {V V' : BigFppfOver B S hS} (k : V ⟶ V') :
    yoneda.relativelyRepresentable (productSpaceMap X₀ k).hom :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange yoneda).of_isPullback
    (isPullback_productSpaceMap X₀ k).flip (Functor.relativelyRepresentable.map yoneda k)

end AlgebraicGeometry.Space

end
