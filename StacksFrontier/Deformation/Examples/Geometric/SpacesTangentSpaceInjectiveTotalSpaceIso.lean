module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceInjectiveTotalSpace

/-!
# The isomorphism of total spaces given by an isomorphism of extensions

Let `x, x'` be two deformations of the algebraic space `X` over `k[V]` (Stacks 0E3Z), and let
`e` be an isomorphism of their extensions (`Deformation.Examples.spaceTangentExtension`). Then the
total spaces `X'₁, X'₂` are isomorphic under `X` and over `Spec k[V]`
(`Deformation.Examples.exists_iso_spaceDefoArrow_comp_eq_of_iso`).

## Main definitions

* `Deformation.Examples.spaceTangentGenerators`: the constants and the elements of `V`, as
  functions of `Spec k[V]`.
* `Deformation.Examples.spaceTangentInverseImageIso`: the isomorphism of the inverse images on `X`
  of the structure sheaves of the total spaces underlying an isomorphism of extensions.

## Main results

* `Deformation.Examples.closure_spaceTangentGenerators`: the constants and `V` generate the ring
  of functions of `Spec k[V]`.
* `Deformation.Examples.spaceDefoFunctionSectionE_spaceTangentRetraction`,
  `Deformation.Examples.spaceDefoFunctionSectionE_spaceTangentFunction`: an isomorphism of
  extensions carries the global sections given by these generators on `x` to those on `x'`.
* `Deformation.Examples.exists_iso_spaceDefoArrow_comp_eq_of_iso`: isomorphic extensions give
  total spaces isomorphic under `X` and over `Spec k[V]`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf
open AlgebraicGeometry.Space Deformation.Artin Deformation.AlgebraExtension

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace Deformation.Examples

/- Lean v4.35.0: instance search for products of presheaves and the terminal sheaf of sets
times out; supply them directly. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_TotalSpaceIso
    {C : Type*} [Category C] (J : Type*) [HasLimitsOfShape (Discrete J) (Type u)] :
    HasLimitsOfShape (Discrete J) (Cᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasTerminal` on a category of sheaves of types is deep
local instance (priority := high) hasTerminal_sheaf_TotalSpaceIso
    {C : Type*} [Category C] (J : GrothendieckTopology C) :
    HasTerminal (Sheaf J (Type u)) :=
  inferInstance

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- Cancelling an isomorphism in an equation of global sections: if
`A ≫ F(α₂) = (B ≫ F(α₁)) ≫ F(r)` then `A = B ≫ F(α₁ ≪≫ r ≪≫ α₂⁻¹)`. -/
theorem eq_comp_map_trans_hom_of_comp_map_hom_eq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P Q R₁ R₂ : C} {W : D} (α₁ : P ≅ R₁) (r : R₁ ≅ R₂) (α₂ : Q ≅ R₂)
    (A : W ⟶ F.obj Q) (B' : W ⟶ F.obj P)
    (h : A ≫ F.map α₂.hom = (B' ≫ F.map α₁.hom) ≫ F.map r.hom) :
    A = B' ≫ F.map (α₁ ≪≫ r ≪≫ α₂.symm).hom := by
  calc A = (A ≫ F.map α₂.hom) ≫ F.map α₂.inv := by
        rw [Category.assoc, ← F.map_comp, α₂.hom_inv_id, F.map_id, Category.comp_id]
    _ = ((B' ≫ F.map α₁.hom) ≫ F.map r.hom) ≫ F.map α₂.inv := by rw [h]
    _ = B' ≫ F.map (α₁ ≪≫ r ≪≫ α₂.symm).hom := by
        simp only [Iso.trans_hom, Iso.symm_hom, F.map_comp, Category.assoc]

/-! ### The functions of `Spec k[V]` -/

section Generators

variable (V : FGModuleCat.{u} k)

/-- **The generators `k ∪ V` of the functions of `Spec k[V]`**: the constants and the elements of
`V`, read in `Γ(Spec k[V])` through `k[V] ≃ Γ(Spec k[V])`. -/
def spaceTangentGenerators :
    Set (baseRing B (Spec (.of Λ)) hΛ
      (spaceBaseOver B hΛ hSpec ((squareZeroExtensionArtinian Λ k).obj V))) :=
  Set.range (fun c : k => spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
      ((squareZeroExtensionArtinian Λ k).obj V) (TrivSqZeroExt.inl (M := V.obj) c)) ∪
    Set.range (fun v : V.obj => spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
      ((squareZeroExtensionArtinian Λ k).obj V) (TrivSqZeroExt.inr (R := k) v))

/-- The constants and `V` generate the ring of functions of `Spec k[V]`. -/
theorem closure_spaceTangentGenerators :
    Subring.closure (spaceTangentGenerators B hΛ hSpec V) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨z, rfl⟩ := (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
    ((squareZeroExtensionArtinian Λ k).obj V)).surjective a
  let z' : TrivSqZeroExt k V.obj := z
  have h2 : z = (show ↑((squareZeroExtensionArtinian Λ k).obj V) from TrivSqZeroExt.inl z'.fst) +
      (show ↑((squareZeroExtensionArtinian Λ k).obj V) from TrivSqZeroExt.inr z'.snd) :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq (R := k) (M := V.obj) z').symm
  rw [h2, map_add]
  exact Subring.add_mem _ (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

end Generators

section Fiber

variable {V : FGModuleCat.{u} k}

variable (x : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
  ((squareZeroExtensionArtinian Λ k).obj V))

/-- Postcomposition with `X ≅ Z` is continuous for the small étale topologies. -/
local instance smallEtalePostcomp_spaceDefoThickeningIso_isContinuous'
    (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal y.left.base ^ 2 = ⊥) :
    (smallEtalePostcomp B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))).IsContinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK y hsq).1) :=
  smallEtalePostcomp_isContinuous B (Spec (.of Λ)) hΛ _ _

/-- Postcomposition with `X ≅ Z` is cocontinuous for the small étale topologies. -/
local instance smallEtalePostcomp_spaceDefoThickeningIso_isCocontinuous'
    (y : Over (spaceSpecialFiber B hΛ hSpec X hX toK))
    (hsq : IsLocalRing.maximalIdeal y.left.base ^ 2 = ⊥) :
    (smallEtalePostcomp B (Spec (.of Λ)) hΛ (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK y hsq))).IsCocontinuous
    (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (SmallEtale.topology B (Spec (.of Λ)) hΛ (spaceDefoFibreSpace B hΛ hSpec X hX toK y hsq).1) :=
  smallEtalePostcomp_isCocontinuous B (Spec (.of Λ)) hΛ _ _

/-- **The structure morphism `X' ⟶ Spec k[V]`** of a deformation over `k[V]`: the structure
morphism to `Spec A` followed by the identification `A = k[V]`. -/
abbrev spaceTangentStructureMap :
    spaceTotalSpace B hΛ hSpec x.1.left ⟶
      schemeSpace (spaceBaseOver B hΛ hSpec ((squareZeroExtensionArtinian Λ k).obj V)) :=
  spaceTotalToBase B hΛ hSpec x.1.left ≫ (schemeSpaceFunctor B (Spec (.of Λ)) hΛ).map
    (spaceBaseOverMap B hΛ hSpec (eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x).symm))

/-- The inclusion `X ≅ Z ⊂ X'` of a deformation over `k[V]`. -/
abbrev spaceTangentInclusion :
    spaceOf B hΛ X hX ⟶ spaceTotalSpace B hΛ hSpec x.1.left :=
  (spaceDefoThickeningIso B hΛ hSpec X hX toK x.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)).hom ≫
    subspaceInclusion B (Spec (.of Λ)) hΛ _
      (spaceDefoThickening B hΛ hSpec X hX toK x.1
        (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x))

/-- `(θ ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_X`, the middle term of the extension of a deformation. -/
abbrev spaceTangentRingComparison :=
  (etaleRestrictionRingComparison B (Spec (.of Λ)) hΛ
    (spaceDefoThickeningIso B hΛ hSpec X hX toK x.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)).hom
    (isEtale_hom_of_iso B (Spec (.of Λ)) hΛ
      (spaceDefoThickeningIso B hΛ hSpec X hX toK x.1
        (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)))
    (subspaceInclusion B (Spec (.of Λ)) hΛ _
      (spaceDefoThickening B hΛ hSpec X hX toK x.1
        (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)))).α

/-- Pulling back the constant `c` along `Spec A ⟶ Spec k[V]` is pulling it back along the
retraction of the constants. -/
theorem Γ_map_spaceBaseOverMap_inl (c : k) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceBaseOverMap B hΛ hSpec
          (eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x).symm))).op).hom
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
          ((squareZeroExtensionArtinian Λ k).obj V) (TrivSqZeroExt.inl (M := V.obj) c)) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceTangentRetraction B hΛ hSpec X hX toK x)).op).hom
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)
          c) :=
  (Γ_map_spaceBaseOverMap_spaceDefoAlgebraEquiv B hΛ hSpec _ _).trans
    (Γ_map_spaceBaseOverMap_spaceDefoAlgebraEquiv B hΛ hSpec
      (spaceFiberConstants B hΛ hSpec X hX toK x) c).symm

/-- Pulling back the function `v ∈ V` along `Spec A ⟶ Spec k[V]` is the function of the base given
by `v`. -/
theorem Γ_map_spaceBaseOverMap_inr (v : V.obj) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceBaseOverMap B hΛ hSpec
          (eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x).symm))).op).hom
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
          ((squareZeroExtensionArtinian Λ k).obj V) (TrivSqZeroExt.inr (R := k) v)) =
      spaceTangentFunction B hΛ hSpec X hX toK x v :=
  (Γ_map_spaceBaseOverMap_spaceDefoAlgebraEquiv B hΛ hSpec _ _).trans
    (spaceTangentFunction_eq B hΛ hSpec X hX toK x v).symm

end Fiber

section Iso

variable {V : FGModuleCat.{u} k}

/-- The category of extensions of `f⁻¹𝒪_{Spec k}`-algebras of `𝒪_X` by `𝒪_X ⊗_k V`, with its
universes named. -/
local instance spaceTangentExtensionCategory :
    Category.{u + 1, u + 1} (AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (inverseImageBaseMap B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
      ((baseRingTensorModule B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (spaceDefoFieldHom B hΛ hSpec X hX toK)).obj
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V))) :=
  AlgebraExtension.instCategory.{u, u + 1, u}

variable {x x' : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    ((squareZeroExtensionArtinian Λ k).obj V)}
  (e : spaceTangentExtension B hΛ hSpec X hX toK x ≅ spaceTangentExtension B hΛ hSpec X hX toK x')

/-- **The isomorphism of the inverse images of the structure sheaves of the total spaces**
underlying an isomorphism of the extensions of two deformations over `k[V]`, read on `X`. -/
def spaceTangentInverseImageIso :
    inverseImageStructureSheaf B (Spec (.of Λ)) hΛ (spaceTangentInclusion B hΛ hSpec X hX toK x) ≅
      inverseImageStructureSheaf B (Spec (.of Λ)) hΛ
        (spaceTangentInclusion B hΛ hSpec X hX toK x') :=
  spaceTangentRingComparison B hΛ hSpec X hX toK x ≪≫
    AlgebraExtension.extensionRingIso.{u, u + 1, u} e ≪≫
    (spaceTangentRingComparison B hΛ hSpec X hX toK x').symm

/-- The isomorphism of inverse images of structure sheaves lies over `𝒪_X`. -/
theorem spaceTangentInverseImageIso_hom_comp :
    (spaceTangentInverseImageIso B hΛ hSpec X hX toK e).hom ≫
        structureSharpInverseImage B (Spec (.of Λ)) hΛ
          (spaceTangentInclusion B hΛ hSpec X hX toK x') =
      structureSharpInverseImage B (Spec (.of Λ)) hΛ
        (spaceTangentInclusion B hΛ hSpec X hX toK x) :=
  trans_trans_symm_hom_comp_eq_of_comp_eq _ _ _ _ _ _ _
    (etaleRestrictionRingComparison_α_hom_comp_reduction B (Spec (.of Λ)) hΛ _ _ _)
    (etaleRestrictionRingComparison_α_hom_comp_reduction B (Spec (.of Λ)) hΛ _ _ _)
    (AlgebraExtension.extensionRingIso_hom_comp_reduction.{u, u + 1, u} e)

/-- **The functions of the base given by constants correspond under an isomorphism of
extensions**: the global section of the middle term of `x'` given by the pullback of a constant
`c` is the image under `e` of that of `x`. -/
theorem spaceDefoFunctionSectionE_spaceTangentRetraction
    (c : baseRing B (Spec (.of Λ)) hΛ (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k))) :
    spaceDefoFunctionSectionE B hΛ hSpec X hX toK x'.1
        (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x')
        ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceTangentRetraction B hΛ hSpec X hX toK x')).op).hom c) =
      spaceDefoFunctionSectionE B hΛ hSpec X hX toK x.1
          (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
          ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
            (spaceTangentRetraction B hΛ hSpec X hX toK x)).op).hom c) ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (AlgebraExtension.extensionRingIso.{u, u + 1, u} e).hom := by
  have key := fun y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V) =>
    spaceDefoFunctionSectionE_map_retraction B hΛ hSpec X hX toK
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK y)
      (spaceTangentRetraction B hΛ hSpec X hX toK y)
      (spaceDefoBaseImmersion_comp_spaceTangentRetraction B hΛ hSpec X hX toK y) c
  rw [key x', key x]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) ((congrArg (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
    (forget CommRingCat.{u})).map e.hom.algebraMap_comm.symm).trans (Functor.map_comp _ _ _))

/-- **The functions of the base given by `v ∈ V` correspond under an isomorphism of
extensions**: the global section of the middle term of `x'` given by `v` is the image under `e`
of that of `x`. -/
theorem spaceDefoFunctionSectionE_spaceTangentFunction (v : V.obj) :
    spaceDefoFunctionSectionE B hΛ hSpec X hX toK x'.1
        (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x')
        (spaceTangentFunction B hΛ hSpec X hX toK x' v) =
      spaceDefoFunctionSectionE B hΛ hSpec X hX toK x.1
          (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
          (spaceTangentFunction B hΛ hSpec X hX toK x v) ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (AlgebraExtension.extensionRingIso.{u, u + 1, u} e).hom := by
  refine Sheaf.hom_ext ?_
  ext W p
  have key := fun y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V) =>
    (spaceTangentExtension_incl_baseRingTensorSection B hΛ hSpec X hX toK y v W p).trans
      (congrArg (fun s => (sectionsFunctor _ W).map s p)
        (spaceDefoFunctionSection_eq B hΛ hSpec X hX toK y.1
          (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK y)
          (spaceTangentFunction B hΛ hSpec X hX toK y v)))
  have h₁ := key x
  have h₂ := key x'
  exact h₂.symm.trans ((e.hom.kernel_comm W _).symm.trans (congrArg (e.hom.hom.hom.app W) h₁))

/-- **The isomorphism of inverse images of structure sheaves on a function of `Spec k[V]`**: if
the global sections of the middle terms given by the pullbacks of `a ∈ Γ(Spec k[V])` correspond
under the isomorphism of middle terms, then the inverse images along `X ⟶ X'_j` of the functions
`p_j^♯a` correspond under `AlgebraicGeometry.Space.spaceTangentInverseImageIso`. -/
theorem globalSectionMap_spaceTangentInclusion_functionGlobalSection
    (a : baseRing B (Spec (.of Λ)) hΛ
      (spaceBaseOver B hΛ hSpec ((squareZeroExtensionArtinian Λ k).obj V)))
    (h : spaceDefoFunctionSectionE B hΛ hSpec X hX toK x'.1
        (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x')
        ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map (spaceBaseOverMap B hΛ hSpec
          (eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x').symm))).op).hom a) =
      spaceDefoFunctionSectionE B hΛ hSpec X hX toK x.1
          (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
          ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
            (spaceBaseOverMap B hΛ hSpec
              (eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x).symm))).op).hom a) ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (AlgebraExtension.extensionRingIso.{u, u + 1, u} e).hom) :
    (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
        (spaceTangentInclusion B hΛ hSpec X hX toK x')).toToposHom.inverseImage.globalSectionMap
        (functionGlobalSection (spaceTangentStructureMap B hΛ hSpec X hX toK x') a) =
      (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
          (spaceTangentInclusion B hΛ hSpec X hX toK x)).toToposHom.inverseImage.globalSectionMap
          (functionGlobalSection (spaceTangentStructureMap B hΛ hSpec X hX toK x) a) ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (spaceTangentInverseImageIso B hΛ hSpec X hX toK e).hom := by
  have hfun : ∀ y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V),
      functionGlobalSection (spaceTangentStructureMap B hΛ hSpec X hX toK y) a =
        functionGlobalSection (spaceTotalToBase B hΛ hSpec y.1.left)
          ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
            (spaceBaseOverMap B hΛ hSpec
              (eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK y).symm))).op).hom a) := fun y =>
    congrArg (fun t => (ringOneHom (structureRingSheaf B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec y.1.left)) ≫
      (moduleSheafFunctor (structureRingSheaf B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec y.1.left))).map
        (unitModuleMul B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.1.left) t) :
      ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ
        (spaceTotalSpace B hΛ hSpec y.1.left).1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec y.1.left)).O))
      (globalFunctionsOfMap_comp B (Spec (.of Λ)) hΛ _ _ a)
  refine (congrArg (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
      (spaceTangentInclusion B hΛ hSpec X hX toK x')).toToposHom.inverseImage.globalSectionMap
        (hfun x')).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
      (spaceTangentInclusion B hΛ hSpec X hX toK x)).toToposHom.inverseImage.globalSectionMap t ≫
        (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u})).map
          (spaceTangentInverseImageIso B hΛ hSpec X hX toK e).hom) (hfun x)).symm
  exact eq_comp_map_trans_hom_of_comp_map_hom_eq
    (sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (forget CommRingCat.{u}))
    (spaceTangentRingComparison B hΛ hSpec X hX toK x)
    (AlgebraExtension.extensionRingIso.{u, u + 1, u} e)
    (spaceTangentRingComparison B hΛ hSpec X hX toK x') _ _ h

include e in
/-- **Isomorphic extensions give isomorphic total spaces under `X` and over `Spec k[V]`.** An
isomorphism of the extensions of two deformations `x, x'` of `X` over `k[V]` gives an isomorphism
`f : X'₁ ≅ X'₂` of their total spaces commuting with the arrows `X ⟶ X'_j` and with the
structure morphisms `X'_j ⟶ Spec k[V]` (Stacks 05YZ, Stacks 05Z1). -/
theorem exists_iso_spaceDefoArrow_comp_eq_of_iso :
    ∃ f : spaceTotalSpace B hΛ hSpec x.1.left ≅ spaceTotalSpace B hΛ hSpec x'.1.left,
      spaceDefoArrow B hΛ hSpec X hX toK x.1 ≫ f.hom = spaceDefoArrow B hΛ hSpec X hX toK x'.1 ∧
        f.hom ≫ spaceTangentStructureMap B hΛ hSpec X hX toK x' =
          spaceTangentStructureMap B hΛ hSpec X hX toK x := by
  have := isEquivalence_pushforward_spaceDefoThickeningIso_hom_comp B hΛ hSpec X hX toK x.1
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x)
  have := isEquivalence_pushforward_spaceDefoThickeningIso_hom_comp B hΛ hSpec X hX toK x'.1
    (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x')
  have := isAffine_toScheme_spaceBaseOver B hΛ hSpec ((squareZeroExtensionArtinian Λ k).obj V)
  obtain ⟨f, hf, hp, -⟩ := exists_iso_comp_eq_of_inverseImageStructureSheafIso_of_functions _ _
    (spaceTangentInverseImageIso B hΛ hSpec X hX toK e)
    (spaceTangentStructureMap B hΛ hSpec X hX toK x)
    (spaceTangentStructureMap B hΛ hSpec X hX toK x')
    (spaceTangentGenerators B hΛ hSpec V) (closure_spaceTangentGenerators B hΛ hSpec V)
    (spaceTangentInverseImageIso_hom_comp B hΛ hSpec X hX toK e) (fun a ha => by
      refine globalSectionMap_spaceTangentInclusion_functionGlobalSection B hΛ hSpec X hX toK e a ?_
      rcases ha with ⟨c, rfl⟩ | ⟨v, rfl⟩
      · rw [Γ_map_spaceBaseOverMap_inl, Γ_map_spaceBaseOverMap_inl]
        exact spaceDefoFunctionSectionE_spaceTangentRetraction B hΛ hSpec X hX toK e _
      · rw [Γ_map_spaceBaseOverMap_inr, Γ_map_spaceBaseOverMap_inr]
        exact spaceDefoFunctionSectionE_spaceTangentFunction B hΛ hSpec X hX toK e v)
  refine ⟨f, ?_, hp⟩
  rwa [← spaceDefoThickeningIso_hom_comp_subspaceInclusion B hΛ hSpec X hX toK x.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x),
    ← spaceDefoThickeningIso_hom_comp_subspaceInclusion B hΛ hSpec X hX toK x'.1
      (spaceFiber_maximalIdeal_sq B hΛ hSpec X hX toK x')]

end Iso

end Deformation.Examples

end
