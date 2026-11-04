module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsLift

/-!
# The fibre automorphisms of a deformation of an algebraic space are a group of linear maps

Let `X` be an algebraic space over the field `k`, `i : x₀ ⟶ xε` a pushforward of a point over
`k` of the deformation category of `X` to an object `Aε` of `𝒞_Λ` with a dual-number
coordinate, `X'` the total space of `xε`, `G ⊆ X'` its special fibre and `π : X' ⟶ X` the
retraction given by `i`.  This file proves that `a ↦ a ≫ π` identifies the automorphism group
of `xε` in its fibre with the group

`Hom_{𝒪_G}(e₀^*Ω_{X/k}, 𝒞_{G/X'})`,

`e₀ = π|_G`, under addition: composition of automorphisms is addition of the corresponding
maps.  The lifts of `e₀` over `Spec k` are a torsor under that group
(`AlgebraicGeometry.Space.topLiftsEquiv`, [Stacks Project, Tag 061D]), every lift comes from an
automorphism (the total space of `xε` is the pullback of `X` along `Spec Aε ⟶ Spec k`), and the
precomposition law of the action ([Stacks Project, Tag 0CK6]) together with the triviality of
the conormal map of a self-map over the base ([Stacks Project, Tag 0CK7]) makes composition of
automorphisms correspond to addition.

## Main definitions

* `Deformation.Examples.spaceAutLift`: the lift `a ≫ π` of an automorphism `a`.
* `Deformation.Examples.spaceAutOfHom`: the automorphism of `xε` attached to a map `θ`.
* `Deformation.Examples.spaceAutMulEquivHom`: the isomorphism of groups.

## References

* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 0CK6](https://stacks.math.columbia.edu/tag/0CK6)
* [Stacks Project, Tag 0CK7](https://stacks.math.columbia.edu/tag/0CK7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

variable {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
  {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    (residueFieldObject.{u, u, u} Λ k)}
  {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
  {g : residueFieldObject.{u, u, u} Λ k ⟶ Aε} {e : Aε ⟶ residueFieldObject.{u, u, u} Λ k}
  (hpair : IsCanonicalDualNumberPair g e)
  (i : x₀.1 ⟶ xε.1)

/-- The group `Hom_{𝒪_G}(e₀^*Ω_{X/k}, 𝒞_{G/X'})` acting on the lifts of `e₀ = π|_G`. -/
abbrev SpaceLiftHom : Type _ :=
  (modulePullback B (Spec (.of Λ)) hΛ (spaceRetractionSpecial B hΛ hSpec X hX toK i)).obj
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ
        (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) ≫
          spaceStructureMap B hΛ hSpec X hX toK)) ⟶
    conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
      (spacePointSpecial B hΛ hSpec X hX toK xε.1)

/-- The lifts of `e₀ = π|_G` over `Spec k`. -/
abbrev SpaceLifts : Type _ :=
  TopLifts B (Spec (.of Λ)) hΛ (spacePointSpecial B hΛ hSpec X hX toK xε.1)
    (spaceStructureMap B hΛ hSpec X hX toK) (spaceRetractionSpecial B hΛ hSpec X hX toK i)
    (spaceRetraction B hΛ hSpec X hX toK i)

/-- The torsor of lifts, based at `π`. -/
def spaceLiftsEquiv : SpaceLiftHom B hΛ hSpec X hX toK i ≃ SpaceLifts B hΛ hSpec X hX toK i :=
  topLiftsEquiv B (Spec (.of Λ)) hΛ (spacePointSpecial B hΛ hSpec X hX toK xε.1)
    (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair)
    (spaceStructureMap B hΛ hSpec X hX toK) (spaceRetractionSpecial B hΛ hSpec X hX toK i)
    (spaceRetraction B hΛ hSpec X hX toK i) (spaceRetractionSpecial_spec B hΛ hSpec X hX toK i)

/-- The self-map of the total space of a fibre automorphism, as a morphism of algebraic
spaces. -/
abbrev spaceAutHom (a : Aut xε) :
    spaceTotalSpace B hΛ hSpec xε.1.left ⟶ spaceTotalSpace B hΛ hSpec xε.1.left :=
  ObjectProperty.homMk (spaceFiberAutMap B hΛ hSpec X hX toK a)

/-- A self-map of `X'` fixing the special-fibre map restricts to the identity of `G`, as
morphisms of algebraic spaces. -/
theorem subspaceInclusion_comp_of_fixes
    (c : spaceTotalSpace B hΛ hSpec xε.1.left ⟶ spaceTotalSpace B hΛ hSpec xε.1.left)
    (hc : spaceSpecialMap B hΛ hSpec X hX toK xε.1 ≫ c.hom =
      spaceSpecialMap B hΛ hSpec X hX toK xε.1) :
    subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) ≫ c =
      𝟙 _ ≫ subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) :=
  ObjectProperty.hom_ext _ (spacePointSpecial_ι_comp_of_fixes B hΛ hSpec X hX toK xε.1 c.hom hc)

/-- **The lift `a ≫ π` of a fibre automorphism `a`.** -/
def spaceAutLift (a : Aut xε) : SpaceLifts B hΛ hSpec X hX toK i :=
  ⟨spaceAutHom B hΛ hSpec X hX toK a ≫ spaceRetraction B hΛ hSpec X hX toK i, by
    have h := subspaceInclusion_comp_of_fixes B hΛ hSpec X hX toK
      (spaceAutHom B hΛ hSpec X hX toK a)
      (spaceSpecialMap_comp_spaceFiberAutMap B hΛ hSpec X hX toK a)
    rw [← Category.assoc, h, Category.id_comp]
    exact spaceRetractionSpecial_spec B hΛ hSpec X hX toK i,
    ObjectProperty.hom_ext _ ((Category.assoc _ _ _).trans
      (comp_spaceRetraction_comp_toK B hΛ hSpec X hX toK i _
        (spaceFiberAutMap_comp_toBase B hΛ hSpec X hX toK a)))⟩

/-- An automorphism is determined by its lift. -/
theorem spaceAutLift_injective :
    Function.Injective (spaceAutLift B hΛ hSpec X hX toK i) := by
  intro a b h
  apply spaceFiberAutMap_injective
  refine spaceTotal_hom_ext B hΛ hSpec X hX toK i ?_ ?_
  · exact congrArg (fun m => m.hom) (congrArg Subtype.val h)
  · exact (spaceFiberAutMap_comp_toBase B hΛ hSpec X hX toK a).trans
      (spaceFiberAutMap_comp_toBase B hΛ hSpec X hX toK b).symm

/-- **The map `θ` of a fibre automorphism**: the unique `θ` with `θ · π = a ≫ π`. -/
def spaceAutToHom (a : Aut xε) : SpaceLiftHom B hΛ hSpec X hX toK i :=
  (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i).symm (spaceAutLift B hΛ hSpec X hX toK i a)

/-- The lift `θ · π` of the map `θ` attached to a fibre automorphism `a` is `a ≫ π`. -/
theorem spaceLiftsEquiv_spaceAutToHom (a : Aut xε) :
    (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i (spaceAutToHom B hΛ hSpec X hX toK hpair i a)).1 =
      spaceAutHom B hΛ hSpec X hX toK a ≫ spaceRetraction B hΛ hSpec X hX toK i :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- The identity square of the special fibre. -/
theorem subspaceInclusion_comp_id_special :
    subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) ≫ 𝟙 _ =
      𝟙 _ ≫ subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Precomposition with a self-map over `Spec Aε` fixing `X` commutes with the action** on the
lifts. -/
theorem comp_derivationMove_spaceRetraction
    (c : spaceTotalSpace B hΛ hSpec xε.1.left ⟶ spaceTotalSpace B hΛ hSpec xε.1.left)
    (hcb : c.hom ≫ xε.1.left.toBase = xε.1.left.toBase)
    (hc : spaceSpecialMap B hΛ hSpec X hX toK xε.1 ≫ c.hom =
      spaceSpecialMap B hΛ hSpec X hX toK xε.1)
    (θ : SpaceLiftHom B hΛ hSpec X hX toK i)
    (hac : subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
        (spacePointSpecial B hΛ hSpec X hX toK xε.1) ≫ c ≫ spaceRetraction B hΛ hSpec X hX toK i =
      spaceRetractionSpecial B hΛ hSpec X hX toK i ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))) :
    c ≫ (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).1 =
      derivationMove B (Spec (.of Λ)) hΛ (spacePointSpecial B hΛ hSpec X hX toK xε.1)
        (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
        (spaceRetractionSpecial B hΛ hSpec X hX toK i) (spaceStructureMap B hΛ hSpec X hX toK)
        (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair)
        (c ≫ spaceRetraction B hΛ hSpec X hX toK i) hac θ
        ((c ≫ spaceRetraction B hΛ hSpec X hX toK i) ≫ spaceStructureMap B hΛ hSpec X hX toK)
        rfl :=
  comp_derivationMove_top B (Spec (.of Λ)) hΛ (spacePointSpecial B hΛ hSpec X hX toK xε.1)
    (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair)
    (spaceStructureMap B hΛ hSpec X hX toK) (spaceRetractionSpecial B hΛ hSpec X hX toK i)
    (spaceRetraction B hΛ hSpec X hX toK i) (spaceRetractionSpecial_spec B hΛ hSpec X hX toK i)
    c (subspaceInclusion_comp_of_fixes B hΛ hSpec X hX toK c hc)
    (subspaceInclusion_comp_id_special B hΛ hSpec X hX toK)
    (conormalMap_spaceSpecialSubspace_eq_id B hΛ hSpec xε.1.left xε.1.hom.base c
      (ObjectProperty.hom_ext _ hcb) _ _) θ hac

/-- **`(θ₁ + θ₂) · π = θ₁ · (θ₂ · π)`**, with the outer action based at the lift `θ₂ · π`. -/
theorem spaceLiftsEquiv_add (θ₁ θ₂ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i (θ₁ + θ₂)).1 =
      derivationMove B (Spec (.of Λ)) hΛ (spacePointSpecial B hΛ hSpec X hX toK xε.1)
        (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
        (spaceRetractionSpecial B hΛ hSpec X hX toK i) (spaceStructureMap B hΛ hSpec X hX toK)
        (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair)
        (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ₂).1
        (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ₂).2.1 θ₁
        (spaceRetraction B hΛ hSpec X hX toK i ≫ spaceStructureMap B hΛ hSpec X hX toK)
        (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ₂).2.2 :=
  derivationMove_add B (Spec (.of Λ)) hΛ (spacePointSpecial B hΛ hSpec X hX toK xε.1)
    (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
    (spaceRetractionSpecial B hΛ hSpec X hX toK i) (spaceStructureMap B hΛ hSpec X hX toK)
    (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair)
    (isFirstOrderThickening_topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
    (spaceRetraction B hΛ hSpec X hX toK i) (spaceRetractionSpecial_spec B hΛ hSpec X hX toK i)
    _ rfl θ₁ θ₂ _ _

/-- **Composition of fibre automorphisms is addition of their maps.** -/
theorem spaceAutToHom_mul (a b : Aut xε) :
    spaceAutToHom B hΛ hSpec X hX toK hpair i (a * b) =
      spaceAutToHom B hΛ hSpec X hX toK hpair i a +
        spaceAutToHom B hΛ hSpec X hX toK hpair i b := by
  apply (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i).injective
  apply TopLifts.ext
  rw [spaceLiftsEquiv_spaceAutToHom, add_comm, spaceLiftsEquiv_add]
  have hB := spaceLiftsEquiv_spaceAutToHom B hΛ hSpec X hX toK hpair i b
  have hcomm := comp_derivationMove_spaceRetraction B hΛ hSpec X hX toK hpair i
    (spaceAutHom B hΛ hSpec X hX toK a) (spaceFiberAutMap_comp_toBase B hΛ hSpec X hX toK a)
    (spaceSpecialMap_comp_spaceFiberAutMap B hΛ hSpec X hX toK a)
    (spaceAutToHom B hΛ hSpec X hX toK hpair i b) (spaceAutLift B hΛ hSpec X hX toK i a).2.1
  rw [hB] at hcomm
  refine Eq.trans ?_ (Eq.trans hcomm ?_)
  · rfl
  · exact derivationMove_congr_of_eq B (Spec (.of Λ)) hΛ _
      (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair) _ _ rfl
      (spaceLiftsEquiv_spaceAutToHom B hΛ hSpec X hX toK hpair i a).symm _ _
      (spaceAutLift B hΛ hSpec X hX toK i a).2.2 _ _

/-! ### The automorphism attached to a map -/

/-- The self-map of `X'` over `Spec Aε` attached to `θ`: the morphism into the pullback
`X' = X ×_{Spec k} Spec Aε` with components `θ · π` and the structure morphism. -/
def spaceSelfMapOfHom (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    xε.1.left.space ⟶ xε.1.left.space :=
  i.left.cartesian.lift
    ((spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).1.hom ≫
      spaceSpecialMap B hΛ hSpec X hX toK x₀.1)
    xε.1.left.toBase (by
      have hℓ := congrArg (fun m => m.hom) (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).2.2
      change (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).1.hom ≫ toK =
        (spaceRetraction B hΛ hSpec X hX toK i).hom ≫ toK at hℓ
      calc ((spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).1.hom ≫
            spaceSpecialMap B hΛ hSpec X hX toK x₀.1) ≫ x₀.1.left.toBase
          = (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).1.hom ≫
              (toK ≫ yoneda.map (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base)) :=
            (Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (spaceSpecialMap_isPullback B hΛ hSpec X hX toK x₀.1).w)
        _ = (spaceRetraction B hΛ hSpec X hX toK i).hom ≫
              (toK ≫ yoneda.map (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base)) :=
            (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hℓ).trans (Category.assoc _ _ _))
        _ = _ := spaceRetraction_comp_toK B hΛ hSpec X hX toK i)

/-- The self-map of `X'` attached to `θ` lies over `Spec Aε`. -/
theorem spaceSelfMapOfHom_comp_toBase (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ ≫ xε.1.left.toBase = xε.1.left.toBase :=
  i.left.cartesian.lift_snd _ _ _

/-- The self-map of `X'` attached to `θ`, followed by the retraction `π`, is `θ · π`. -/
theorem spaceSelfMapOfHom_comp_retraction (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ ≫ (spaceRetraction B hΛ hSpec X hX toK i).hom =
      (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).1.hom := by
  have := isIso_spaceSpecialMap_of_residueFieldObject B hΛ hSpec X hX toK x₀
  show spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ ≫ i.left.map ≫
    inv (spaceSpecialMap B hΛ hSpec X hX toK x₀.1) = _
  rw [← Category.assoc, spaceSelfMapOfHom, IsPullback.lift_fst, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

/-- The self-map attached to `θ` fixes the special-fibre map. -/
theorem spaceSpecialMap_comp_spaceSelfMapOfHom (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    spaceSpecialMap B hΛ hSpec X hX toK xε.1 ≫ spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ =
      spaceSpecialMap B hΛ hSpec X hX toK xε.1 := by
  have hG : (spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫
      spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ =
      (spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι := by
    refine spaceTotal_hom_ext B hΛ hSpec X hX toK i ?_ ?_
    · rw [Category.assoc, spaceSelfMapOfHom_comp_retraction]
      exact congrArg (fun m => m.hom) ((spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).2.1.trans
        (spaceRetractionSpecial_spec B hΛ hSpec X hX toK i).symm)
    · rw [Category.assoc, spaceSelfMapOfHom_comp_toBase]
  rw [← spaceSpecialMapToSpecial_ι, Category.assoc, hG]

/-- The self-map of `θ`, followed by `π`, is `θ · π`, as morphisms of algebraic spaces. -/
theorem spaceSelfMapOfHom_lift (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    (ObjectProperty.homMk (spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ) :
        spaceTotalSpace B hΛ hSpec xε.1.left ⟶ spaceTotalSpace B hΛ hSpec xε.1.left) ≫
        spaceRetraction B hΛ hSpec X hX toK i =
      (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).1 :=
  ObjectProperty.hom_ext _ (spaceSelfMapOfHom_comp_retraction B hΛ hSpec X hX toK hpair i θ)

/-- **`m_θ ≫ m_{θ'}` is `m_{θ' + θ}`**, after `π`: the action commutes with precomposition. -/
theorem spaceSelfMapOfHom_comp_comp_retraction (θ θ' : SpaceLiftHom B hΛ hSpec X hX toK i) :
    (spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ ≫
        spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ') ≫
        (spaceRetraction B hΛ hSpec X hX toK i).hom =
      (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i (θ' + θ)).1.hom := by
  let c : spaceTotalSpace B hΛ hSpec xε.1.left ⟶ spaceTotalSpace B hΛ hSpec xε.1.left :=
    ObjectProperty.homMk (spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ)
  have hcomm := comp_derivationMove_spaceRetraction B hΛ hSpec X hX toK hpair i c
    (spaceSelfMapOfHom_comp_toBase B hΛ hSpec X hX toK hpair i θ)
    (spaceSpecialMap_comp_spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ) θ'
    (by
      rw [spaceSelfMapOfHom_lift]
      exact (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).2.1)
  refine (Category.assoc _ _ _).trans ?_
  rw [spaceSelfMapOfHom_comp_retraction]
  refine (congrArg (fun m => m.hom) hcomm).trans ?_
  rw [spaceLiftsEquiv_add]
  exact congrArg (fun m => m.hom) (derivationMove_congr_of_eq B (Spec (.of Λ)) hΛ _
      (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair) _ _ rfl
      (spaceSelfMapOfHom_lift B hΛ hSpec X hX toK hpair i θ) _ _
      ((congrArg (· ≫ spaceStructureMap B hΛ hSpec X hX toK)
        (spaceSelfMapOfHom_lift B hΛ hSpec X hX toK hpair i θ)).trans
        (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i θ).2.2) _ _)

/-- `m_θ ≫ m_{-θ} = 𝟙`. -/
theorem spaceSelfMapOfHom_comp_neg (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ ≫
        spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i (-θ) = 𝟙 _ := by
  refine spaceTotal_hom_ext B hΛ hSpec X hX toK i ?_ ?_
  · rw [spaceSelfMapOfHom_comp_comp_retraction, neg_add_cancel, Category.id_comp]
    exact congrArg (fun m => m.hom) (topLiftsEquiv_zero B (Spec (.of Λ)) hΛ
      (spacePointSpecial B hΛ hSpec X hX toK xε.1)
      (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair)
      (spaceStructureMap B hΛ hSpec X hX toK) (spaceRetractionSpecial B hΛ hSpec X hX toK i)
      (spaceRetraction B hΛ hSpec X hX toK i) (spaceRetractionSpecial_spec B hΛ hSpec X hX toK i))
  · rw [Category.assoc, spaceSelfMapOfHom_comp_toBase, spaceSelfMapOfHom_comp_toBase,
      Category.id_comp]

/-- `m_{-θ} ≫ m_θ = 𝟙`. -/
theorem spaceSelfMapOfHom_neg_comp (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i (-θ) ≫
        spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ = 𝟙 _ := by
  have h := spaceSelfMapOfHom_comp_neg B hΛ hSpec X hX toK hpair i (-θ)
  rwa [neg_neg] at h

/-- The self-map attached to `θ` is an isomorphism. -/
theorem isIso_spaceSelfMapOfHom (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    IsIso (spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ) :=
  ⟨⟨spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i (-θ),
    spaceSelfMapOfHom_comp_neg B hΛ hSpec X hX toK hpair i θ,
    spaceSelfMapOfHom_neg_comp B hΛ hSpec X hX toK hpair i θ⟩⟩

/-- The endomorphism of the family of `xε` attached to `θ`. -/
def spaceFamilyHomOfHom (θ : SpaceLiftHom B hΛ hSpec X hX toK i) : xε.1.left ⟶ xε.1.left where
  base := 𝟙 _
  map := spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ
  cartesian := by
    have := isIso_spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ
    rw [spaceBaseOverMap_id, CategoryTheory.Functor.map_id]
    exact IsPullback.of_horiz_isIso
      ⟨(spaceSelfMapOfHom_comp_toBase B hΛ hSpec X hX toK hpair i θ).trans
        (Category.comp_id _).symm⟩

/-- The endomorphism of the point `xε` of the deformation category attached to `θ`. -/
def spaceOverHomOfHom (θ : SpaceLiftHom B hΛ hSpec X hX toK i) : xε.1 ⟶ xε.1 :=
  Over.homMk (spaceFamilyHomOfHom B hΛ hSpec X hX toK hpair i θ) (by
    apply FlatAlgebraicSpaceFamily.Hom.ext
    · exact Category.id_comp _
    · exact spaceSpecialMap_comp_spaceSelfMapOfHom B hΛ hSpec X hX toK hpair i θ)

/-- The endomorphism attached to `θ` lies over the identity of `Aε`. -/
theorem spaceOverHomOfHom_isHomLift (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift (𝟙 Aε)
      (spaceOverHomOfHom B hΛ hSpec X hX toK hpair i θ) :=
  IsHomLift.of_fac' _ (𝟙 Aε) _ xε.2 xε.2 (by
    rw [Category.id_comp, eqToHom_trans, eqToHom_refl]
    rfl)

/-- The fibre endomorphism attached to `θ`. -/
def spaceFiberHomOfHom (θ : SpaceLiftHom B hΛ hSpec X hX toK i) : xε ⟶ xε :=
  ⟨spaceOverHomOfHom B hΛ hSpec X hX toK hpair i θ,
    spaceOverHomOfHom_isHomLift B hΛ hSpec X hX toK hpair i θ⟩

/-- The fibre endomorphism attached to `θ`, followed by the one attached to `-θ`, is the
identity. -/
theorem spaceFiberHomOfHom_comp_neg (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    spaceFiberHomOfHom B hΛ hSpec X hX toK hpair i θ ≫
      spaceFiberHomOfHom B hΛ hSpec X hX toK hpair i (-θ) = 𝟙 xε := by
  apply Functor.Fiber.hom_ext
  apply Over.OverMorphism.ext
  apply FlatAlgebraicSpaceFamily.Hom.ext
  · exact Category.id_comp _
  · exact spaceSelfMapOfHom_neg_comp B hΛ hSpec X hX toK hpair i θ

/-- The fibre endomorphism attached to `-θ`, followed by the one attached to `θ`, is the
identity. -/
theorem spaceFiberHomOfHom_neg_comp (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    spaceFiberHomOfHom B hΛ hSpec X hX toK hpair i (-θ) ≫
      spaceFiberHomOfHom B hΛ hSpec X hX toK hpair i θ = 𝟙 xε := by
  have h := spaceFiberHomOfHom_comp_neg B hΛ hSpec X hX toK hpair i (-θ)
  rwa [neg_neg] at h

/-- **The fibre automorphism of `xε` attached to `θ`**: the self-map of `X'` over `Spec Aε` with
`m ≫ π = θ · π`, whose inverse is attached to `-θ`. -/
def spaceAutOfHom (θ : SpaceLiftHom B hΛ hSpec X hX toK i) : Aut xε where
  hom := spaceFiberHomOfHom B hΛ hSpec X hX toK hpair i θ
  inv := spaceFiberHomOfHom B hΛ hSpec X hX toK hpair i (-θ)
  hom_inv_id := spaceFiberHomOfHom_comp_neg B hΛ hSpec X hX toK hpair i θ
  inv_hom_id := spaceFiberHomOfHom_neg_comp B hΛ hSpec X hX toK hpair i θ

/-- The map attached to the fibre automorphism of `θ` is `θ`. -/
theorem spaceAutToHom_spaceAutOfHom (θ : SpaceLiftHom B hΛ hSpec X hX toK i) :
    spaceAutToHom B hΛ hSpec X hX toK hpair i (spaceAutOfHom B hΛ hSpec X hX toK hpair i θ) =
      θ := by
  apply (spaceLiftsEquiv B hΛ hSpec X hX toK hpair i).injective
  apply TopLifts.ext
  rw [spaceLiftsEquiv_spaceAutToHom]
  exact spaceSelfMapOfHom_lift B hΛ hSpec X hX toK hpair i θ

/-- A fibre automorphism is determined by its map `θ`. -/
theorem spaceAutToHom_injective :
    Function.Injective (spaceAutToHom B hΛ hSpec X hX toK hpair i) := fun _ _ h =>
  spaceAutLift_injective B hΛ hSpec X hX toK i
    ((spaceLiftsEquiv B hΛ hSpec X hX toK hpair i).symm.injective h)

/-- **The automorphism group of `xε` in its fibre is the group `Hom(e₀^*Ω_{X/k}, 𝒞_{G/X'})`**:
`a ↦ θ` with `θ · π = a ≫ π`, composition of automorphisms being addition. -/
def spaceAutMulEquivHom : Aut xε ≃* Multiplicative (SpaceLiftHom B hΛ hSpec X hX toK i) where
  toFun a := Multiplicative.ofAdd (spaceAutToHom B hΛ hSpec X hX toK hpair i a)
  invFun θ := spaceAutOfHom B hΛ hSpec X hX toK hpair i (Multiplicative.toAdd θ)
  left_inv _ := spaceAutToHom_injective B hΛ hSpec X hX toK hpair i
    (spaceAutToHom_spaceAutOfHom B hΛ hSpec X hX toK hpair i _)
  right_inv θ := spaceAutToHom_spaceAutOfHom B hΛ hSpec X hX toK hpair i (Multiplicative.toAdd θ)
  map_mul' a b := congrArg Multiplicative.ofAdd (spaceAutToHom_mul B hΛ hSpec X hX toK hpair i a b)

end Deformation.Examples

end
