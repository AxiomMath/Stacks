module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatPredeformationFiniteTangentTotalSpace
public import StacksFrontier.AlgebraicGeometry.Quot.CurveDeformationsSchemes
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfPostInclusion

/-!
# Injectivity of the class map of deformations in `Spaces'_{fp, flat, proper}`

Let `x₀ = (X₀ ⟶ Spec k)` be an object of `Spaces'_{fp, flat, proper}` over the big fppf site of an
arbitrary scheme `S`. Two deformations `x, x'` of `x₀` over `k[V]` with the same class in
`Ext¹(NL_{X₀/k}, 𝒪_{X₀} ⊗_k V)` (`AlgebraicGeometry.Space.deformationTangentClass`) are
isomorphic: equal classes give isomorphic extensions (Stacks 0GQ5), isomorphic extensions give
an isomorphism of the total spaces under `X₀` and over `Spec k[V]` (Stacks 05YZ, 05Z1), and such an
isomorphism is an isomorphism of deformations, an isomorphism of total spaces over an
isomorphism of bases being a cartesian square.

Consequently the class map on isomorphism classes of deformations over `k[ε]`
(`AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtClassAt` at `V = k`) is injective: the
injectivity of the classes in the proof of [Stacks Project, Tag 0D1K].

## Main results

* `AlgebraicGeometry.ProperFlatSpaceDeformation.exists_iso_deformationArrow_comp_eq_of_iso`:
  isomorphic extensions give total spaces isomorphic under `X₀` and over `Spec k[V]`.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.isIsomorphic_of_tangentFiberClass_eq`:
  deformations over `k[V]` with the same class are isomorphic.
* `AlgebraicGeometry.ProperFlatSpaceDeformation.tangentExtClassAt_injective`: the class map at
  `V = k` is injective.

## References

* [Stacks Project, Tag 0D1K](https://stacks.math.columbia.edu/tag/0D1K)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Sheaf
open Deformation Deformation.Artin Deformation.AlgebraExtension AlgebraicGeometry.Space

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.ProperFlatSpaceDeformation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (iΛ : Spec (.of Λ) ⟶ S)
  {x₀ : CartesianProperFlatSpaces B S hS}
  {hx₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj x₀ =
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}

/-- Discrete limits of presheaves of sets on the small étale site (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_finiteTangentInjective
    (Z : AlgebraicSpaces B S hS) (J : Type) :
    HasLimitsOfShape (Discrete J) ((Space.smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- Discrete limits of presheaves of sets on the small étale site, indexed in universe `u`
(instance search times out without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_finiteTangentInjective'
    (Z : AlgebraicSpaces B S hS) (J : Type u) :
    HasLimitsOfShape (Discrete J) ((Space.smallEtaleRingedTopos B S hS Z).Cᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- The terminal sheaf of sets on the small étale site (instance search times out without this
shortcut). -/
local instance (priority := high) hasTerminal_topos_finiteTangentInjective
    (Z : AlgebraicSpaces B S hS) :
    HasLimitsOfShape (Discrete PEmpty.{1}) (Space.smallEtaleRingedTopos B S hS Z).Topos :=
  letI : HasLimitsOfShape (Discrete PEmpty.{1}) ((Space.SmallEtale B S hS Z.1)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasLimitsOfShape
  letI : CreatesLimitsOfShape (Discrete PEmpty.{1})
      (sheafToPresheaf (Space.SmallEtale.topology B S hS Z.1) (Type u)) :=
    Sheaf.createsLimitsOfShape
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (sheafToPresheaf (Space.SmallEtale.topology B S hS Z.1) (Type u))

/-- The right action of `k` on a `k`-module, the one through which `k[V]` is formed. -/
local instance (M : FGModuleCat.{u} k) : Module kᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring k M

/-- The left and right actions of `k` on a `k`-module agree. -/
local instance (M : FGModuleCat.{u} k) : IsCentralScalar k M :=
  Module.isCentralScalar_oppositeOfCommSemiring k M

/-- Postcomposition with `X₀ ≅ Z` is continuous for the small étale topologies. -/
local instance smallEtalePostcomp_deformationThickeningIso_isContinuous'
    (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀)
    (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥) :
    (Space.smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).IsContinuous
    (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
    (Space.SmallEtale.topology B S hS (deformationFibreSpace B S hS x hsq).1) :=
  Space.smallEtalePostcomp_isContinuous B S hS _ _

/-- Postcomposition with `X₀ ≅ Z` is cocontinuous for the small étale topologies. -/
local instance smallEtalePostcomp_deformationThickeningIso_isCocontinuous'
    (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀)
    (hsq : RingHom.ker (residueMap x.algebra) ^ 2 = ⊥) :
    (Space.smallEtalePostcomp B S hS (deformationThickeningIso B S hS x hsq).hom
    (isEtale_hom_of_iso B S hS (deformationThickeningIso B S hS x hsq))).IsCocontinuous
    (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
    (Space.SmallEtale.topology B S hS (deformationFibreSpace B S hS x hsq).1) :=
  Space.smallEtalePostcomp_isCocontinuous B S hS _ _

/-! ### The base `Spec k[V]` -/

section Base

variable (V : FGModuleCat.{u} k)
  (hV : B.Contains (Spec (.of ((artinianSquareZeroExtensionFunctor Λ k).obj V))))

/-- **`Spec k[V]` as an object of the big fppf site of `S`**, through `Spec k[V] ⟶ Spec Λ ⟶ S`. -/
abbrev tangentBase : BigFppfOver B S hS :=
  algebraOver ((artinianSquareZeroExtensionFunctor Λ k).obj V) B S hS
    (Spec.map (CommRingCat.ofHom (algebraMap Λ ((artinianSquareZeroExtensionFunctor Λ k).obj V))) ≫
      iΛ) hV

/-- The base `Spec k[V]` is affine. -/
instance isAffine_toScheme_tangentBase :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (tangentBase B S hS iΛ V hV)) := by
  change IsAffine (Spec _); infer_instance

/-- `k[V] ≃ Γ(Spec k[V])`. -/
abbrev tangentAlgebraEquiv :
    (artinianSquareZeroExtensionFunctor Λ k).obj V ≃+*
      baseRing B S hS (tangentBase B S hS iΛ V hV) :=
  (Scheme.ΓSpecIso (CommRingCat.of
    ((artinianSquareZeroExtensionFunctor Λ k).obj V))).symm.commRingCatIsoToRingEquiv

/-- **The generators `k ∪ V` of the functions of `Spec k[V]`**: the constants and the elements of
`V`, read in `Γ(Spec k[V])`. -/
def tangentGenerators : Set (baseRing B S hS (tangentBase B S hS iΛ V hV)) :=
  Set.range (fun c : k => tangentAlgebraEquiv B S hS iΛ V hV
      (TrivSqZeroExt.inl (M := V.obj) c)) ∪
    Set.range (fun v : V.obj => tangentAlgebraEquiv B S hS iΛ V hV
      (TrivSqZeroExt.inr (R := k) v))

/-- The constants and `V` generate the ring of functions of `Spec k[V]`. -/
theorem closure_tangentGenerators :
    Subring.closure (tangentGenerators B S hS iΛ V hV) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨z, rfl⟩ := (tangentAlgebraEquiv B S hS iΛ V hV).surjective a
  let z' : TrivSqZeroExt k V.obj := z
  have h2 : z = (show ↑((artinianSquareZeroExtensionFunctor Λ k).obj V) from
      TrivSqZeroExt.inl z'.fst) +
      (show ↑((artinianSquareZeroExtensionFunctor Λ k).obj V) from TrivSqZeroExt.inr z'.snd) :=
    (TrivSqZeroExt.inl_fst_add_inr_snd_eq (R := k) (M := V.obj) z').symm
  rw [h2, map_add]
  exact Subring.add_mem _ (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
    (Subring.subset_closure (Or.inr ⟨_, rfl⟩))

/-- The structure object of `Spec A` over `S` for `A = k[V]` is that of `Spec k[V]`. -/
theorem over_mk_eq_post_tangentBase (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (h : A = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ) =
      (Over.post B.inclusion).obj (tangentBase B S hS iΛ V hV) := by
  subst h
  rfl

variable {V}
  (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    x₀ hx₀)
  (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)

include hx in
/-- The base of a deformation over `k[V]` is `Spec k[V]`. -/
theorem base_eq_tangentBase :
    (cartesianProperFlatProjection B S hS).obj x.point = tangentBase B S hS iΛ V hV :=
  BigFppfOver.obj_injective_post_inclusion B S hS
    (x.base.trans (over_mk_eq_post_tangentBase B S hS iΛ V hV x.algebra hx))

/-- **The structure morphism `X' ⟶ Spec k[V]`** of a deformation over `k[V]`. -/
abbrev tangentStructureMap :
    deformationSpace B S hS x ⟶ schemeSpace (tangentBase B S hS iΛ V hV) :=
  deformationStructureMap B S hS x ≫ (schemeSpaceFunctor B S hS).map
    (eqToHom (base_eq_tangentBase B S hS iΛ hV x hx))

/-- Pulling back functions along a transport of affine schemes along `A = k[V]`. -/
theorem Γ_map_eqToHom_ΓSpecIso_inv (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (h : A = (artinianSquareZeroExtensionFunctor Λ k).obj V) (X : Scheme.{u})
    (E₁ : X = Spec (.of ((artinianSquareZeroExtensionFunctor Λ k).obj V)))
    (E₂ : X = Spec (.of A)) (a : (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    (Scheme.Γ.map (eqToHom E₁).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of ((artinianSquareZeroExtensionFunctor Λ k).obj V))).inv.hom
          a) =
      (Scheme.Γ.map (eqToHom E₂).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ((eqToHom h.symm).hom.toRingHom a)) := by
  subst h
  rfl

/-- **Functions of `Spec k[V]` pulled back to the base of a deformation over `k[V]`.** -/
theorem Γ_map_eqToHom_tangentAlgebraEquiv (a : (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (eqToHom (base_eq_tangentBase B S hS iΛ hV x hx))).op).hom
        (tangentAlgebraEquiv B S hS iΛ V hV a) =
      deformationAlgebraEquiv B S hS x ((eqToHom hx.symm).hom.toRingHom a) := by
  rw [eqToHom_map]
  exact Γ_map_eqToHom_ΓSpecIso_inv x.algebra hx _ _ (congrArg Over.left x.base) a

/-- **Pullback of a constant along the retraction of the constants**: through `A ≅ Γ(Spec A)`
and `k ≅ Γ(Spec k)`, pullback of functions along the retraction attached to a section `σ` of the
residue map is `σ`. -/
theorem Γ_map_baseRetraction (σ : k →+* x.algebra)
    (hσΛ : σ.comp (algebraMap Λ k) = algebraMap Λ x.algebra) (c : k) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (baseRetraction (cartesianProperFlatProjection B S hS) x σ hσΛ)).op).hom
        (baseResidueFieldEquiv B S hS hx₀ c) =
      deformationAlgebraEquiv B S hS x (σ c) := by
  have hF : (BigFppfOver.toScheme B S hS).map
      (baseRetraction (cartesianProperFlatProjection B S hS) x σ hσΛ) =
      eqToHom (congrArg Over.left x.base) ≫ Spec.map (CommRingCat.ofHom σ) ≫
        eqToHom (congrArg Over.left hx₀).symm := by
    change ((Over.post B.inclusion).map
      (baseRetraction (cartesianProperFlatProjection B S hS) x σ hσΛ)).left = _
    rw [baseRetraction, Functor.map_preimage]
    simp only [Over.comp_left, Over.eqToHom_left, Over.homMk_left]
  have key : ∀ (X Y : Scheme.{u}) (ex : X = Spec (.of x.algebra)) (e₀ : Y = Spec (.of k)),
      (Scheme.Γ.map (eqToHom ex ≫ Spec.map (CommRingCat.ofHom σ) ≫ eqToHom e₀.symm).op).hom
          ((Scheme.Γ.map (eqToHom e₀).op).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) =
        (Scheme.Γ.map (eqToHom ex).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of x.algebra)).inv.hom (σ c)) := by
    intro X Y ex e₀
    subst ex e₀
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, op_id,
      CategoryTheory.Functor.map_id]
    exact (congrArg (fun m => m.hom c) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom σ))).symm
  rw [hF]
  exact key _ _ (congrArg Over.left x.base) (congrArg Over.left hx₀)


/-- Pulling back the constant `c` along `Spec A ⟶ Spec k[V]` is pulling it back along the
retraction of the constants. -/
theorem Γ_map_eqToHom_inl (c : k) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (eqToHom (base_eq_tangentBase B S hS iΛ hV x hx))).op).hom
        (tangentAlgebraEquiv B S hS iΛ V hV (TrivSqZeroExt.inl (M := V.obj) c)) =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (tangentRetraction B S hS V x hx)).op).hom (baseResidueFieldEquiv B S hS hx₀ c) :=
  (Γ_map_eqToHom_tangentAlgebraEquiv B S hS iΛ hV x hx _).trans
    (Γ_map_baseRetraction B S hS iΛ x (tangentSection B S hS V x hx)
      (tangentSection_comp_algebraMap B S hS V x hx) c).symm

/-- Pulling back the function `v ∈ V` along `Spec A ⟶ Spec k[V]` is the function of the base given
by `v`. -/
theorem Γ_map_eqToHom_inr (v : V.obj) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (eqToHom (base_eq_tangentBase B S hS iΛ hV x hx))).op).hom
        (tangentAlgebraEquiv B S hS iΛ V hV (TrivSqZeroExt.inr (R := k) v)) =
      deformationTangentFunction B S hS V hx v :=
  (Γ_map_eqToHom_tangentAlgebraEquiv B S hS iΛ hV x hx _).trans
    (deformationTangentFunction_eq B S hS V hx v).symm

/-- The inclusion `X₀ ≅ Z ⊂ X'` of a deformation over `k[V]`. -/
abbrev tangentInclusion : x₀.obj.obj.left ⟶ deformationSpace B S hS x :=
  (deformationThickeningIso B S hS x (ker_residueMap_sq_of_eq B S hS V x hx)).hom ≫
    Space.subspaceInclusion B S hS _
      (deformationThickening B S hS x (ker_residueMap_sq_of_eq B S hS V x hx))

/-- `(θ ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`, the middle term of the extension of a deformation. -/
abbrev tangentRingComparison :=
  (etaleRestrictionRingComparison B S hS
    (deformationThickeningIso B S hS x (ker_residueMap_sq_of_eq B S hS V x hx)).hom
    (isEtale_hom_of_iso B S hS
      (deformationThickeningIso B S hS x (ker_residueMap_sq_of_eq B S hS V x hx)))
    (Space.subspaceInclusion B S hS _
      (deformationThickening B S hS x (ker_residueMap_sq_of_eq B S hS V x hx)))).α

/-- `deformationTangentExtension_incl_baseRingTensorSection`, read through
`(e ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_{X₀}`. -/
theorem tangentExtension_incl_baseRingTensorSection_eq_sectionE
    (v : (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V)
    (W : (Space.SmallEtale B S hS x₀.obj.obj.left.1)ᵒᵖ)
    (p : (sectionsFunctor _ W).obj
      (⊤_ Sheaf (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1) (Type u))) :
    (deformationTangentExtension B S hS V x hx).incl
        ((baseRingTensorSection B S hS x₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hx₀))
          ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V) v).val.app W
          (1 : (Space.structureRingSheaf B S hS x₀.obj.obj.left).obj.obj W)) =
      (sectionsFunctor _ W).map (deformationFunctionSectionE B S hS x
        (ker_residueMap_sq_of_eq B S hS V x hx) (deformationTangentFunction B S hS V hx v)) p :=
  (deformationTangentExtension_incl_baseRingTensorSection B S hS V hx v W p).trans
    (sectionsFunctor_map_congr (deformationFunctionSection_eq B S hS x
      (ker_residueMap_sq_of_eq B S hS V x hx) (deformationTangentFunction B S hS V hx v)) W p)

end Base

/-! ### Isomorphic extensions give isomorphic total spaces -/

section Iso

variable {V : FGModuleCat.{u} k}
  (hV : B.Contains (Spec (.of ((artinianSquareZeroExtensionFunctor Λ k).obj V))))

/-- The category of extensions of `f₀⁻¹𝒪_{Spec k}`-algebras of `𝒪_{X₀}` by `𝒪_{X₀} ⊗_k V`, with its
universes named (instance search does not find them here). -/
local instance tangentExtensionCategory :
    Category.{u + 1, u + 1} (AlgebraExtension
      (J := Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
      (inverseImageBaseMap B S hS (baseStructureMap B S hS (y₀ := x₀)))
      ((baseRingTensorModule B S hS x₀.obj.obj.left (baseFieldHom B S hS (hy₀ := hx₀))).obj
        ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj V))) :=
  AlgebraExtension.instCategory.{u, u + 1, u}

variable {x x' : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    x₀ hx₀}
  {hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V}
  {hx' : x'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V}
  (e : deformationTangentExtension B S hS V x hx ≅ deformationTangentExtension B S hS V x' hx')

/-- **The isomorphism of the inverse images of the structure sheaves of the total spaces**
underlying an isomorphism of the extensions of two deformations over `k[V]`, read on `X₀`. -/
def tangentInverseImageIso :
    Space.inverseImageStructureSheaf B S hS (tangentInclusion B S hS iΛ x hx) ≅
      Space.inverseImageStructureSheaf B S hS (tangentInclusion B S hS iΛ x' hx') :=
  tangentRingComparison B S hS iΛ x hx ≪≫
    AlgebraExtension.extensionRingIso.{u, u + 1, u} e ≪≫
    (tangentRingComparison B S hS iΛ x' hx').symm

/-- The isomorphism of inverse images of structure sheaves lies over `𝒪_{X₀}`. -/
theorem tangentInverseImageIso_hom_comp :
    (tangentInverseImageIso B S hS iΛ e).hom ≫
        structureSharpInverseImage B S hS (tangentInclusion B S hS iΛ x' hx') =
      structureSharpInverseImage B S hS (tangentInclusion B S hS iΛ x hx) :=
  trans_trans_symm_hom_comp_eq_of_comp_eq _ _ _ _ _ _ _
    (etaleRestrictionRingComparison_α_hom_comp_reduction B S hS _ _ _)
    (etaleRestrictionRingComparison_α_hom_comp_reduction B S hS _ _ _)
    (AlgebraExtension.extensionRingIso_hom_comp_reduction.{u, u + 1, u} e)

/-- **The functions of the base given by constants correspond under an isomorphism of
extensions.** -/
theorem deformationFunctionSectionE_tangentRetraction
    (c : baseRing B S hS ((cartesianProperFlatProjection B S hS).obj x₀)) :
    deformationFunctionSectionE B S hS x' (ker_residueMap_sq_of_eq B S hS V x' hx')
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (tangentRetraction B S hS V x' hx')).op).hom c) =
      deformationFunctionSectionE B S hS x (ker_residueMap_sq_of_eq B S hS V x hx)
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (tangentRetraction B S hS V x hx)).op).hom c) ≫
        (sheafCompose (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
          (forget CommRingCat.{u})).map
          (AlgebraExtension.extensionRingIso.{u, u + 1, u} e).hom := by
  refine (deformationFunctionSectionE_map_retraction B S hS
      (ker_residueMap_sq_of_eq B S hS V x' hx') (tangentRetraction B S hS V x' hx')
      (map_arrow_comp_tangentRetraction B S hS V x' hx') c).trans
    (Eq.trans ?_ (congrArg (· ≫ _) (deformationFunctionSectionE_map_retraction B S hS
      (ker_residueMap_sq_of_eq B S hS V x hx) (tangentRetraction B S hS V x hx)
      (map_arrow_comp_tangentRetraction B S hS V x hx) c)).symm)
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) ((congrArg (sheafCompose
    (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
    (forget CommRingCat.{u})).map e.hom.algebraMap_comm.symm).trans (Functor.map_comp _ _ _))

/-- **The functions of the base given by `v ∈ V` correspond under an isomorphism of
extensions.** -/
theorem deformationFunctionSectionE_tangentFunction (v : V.obj) :
    deformationFunctionSectionE B S hS x' (ker_residueMap_sq_of_eq B S hS V x' hx')
        (deformationTangentFunction B S hS V hx' v) =
      deformationFunctionSectionE B S hS x (ker_residueMap_sq_of_eq B S hS V x hx)
          (deformationTangentFunction B S hS V hx v) ≫
        (sheafCompose (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
          (forget CommRingCat.{u})).map
          (AlgebraExtension.extensionRingIso.{u, u + 1, u} e).hom := by
  refine Sheaf.hom_ext ?_
  ext W p
  have h₁ := tangentExtension_incl_baseRingTensorSection_eq_sectionE B S hS iΛ x hx v W p
  have h₂ := tangentExtension_incl_baseRingTensorSection_eq_sectionE B S hS iΛ x' hx' v W p
  exact h₂.symm.trans ((e.hom.kernel_comm W _).symm.trans (congrArg (e.hom.hom.hom.app W) h₁))

/-- **The isomorphism of inverse images of structure sheaves on a function of `Spec k[V]`.** -/
theorem globalSectionMap_tangentInclusion_functionGlobalSection
    (a : baseRing B S hS (tangentBase B S hS iΛ V hV))
    (h : deformationFunctionSectionE B S hS x' (ker_residueMap_sq_of_eq B S hS V x' hx')
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (eqToHom (base_eq_tangentBase B S hS iΛ hV x' hx'))).op).hom a) =
      deformationFunctionSectionE B S hS x (ker_residueMap_sq_of_eq B S hS V x hx)
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (eqToHom (base_eq_tangentBase B S hS iΛ hV x hx))).op).hom a) ≫
        (sheafCompose (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
          (forget CommRingCat.{u})).map
          (AlgebraExtension.extensionRingIso.{u, u + 1, u} e).hom) :
    (Space.smallEtaleRingedToposHom B S hS
        (tangentInclusion B S hS iΛ x' hx')).toToposHom.inverseImage.globalSectionMap
        (functionGlobalSection (tangentStructureMap B S hS iΛ hV x' hx') a) =
      (Space.smallEtaleRingedToposHom B S hS
          (tangentInclusion B S hS iΛ x hx)).toToposHom.inverseImage.globalSectionMap
          (functionGlobalSection (tangentStructureMap B S hS iΛ hV x hx) a) ≫
        (sheafCompose (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
          (forget CommRingCat.{u})).map
          (tangentInverseImageIso B S hS iΛ e).hom := by
  have hfun : ∀ (y : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion) x₀ hx₀)
      (hy : y.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V),
      functionGlobalSection (tangentStructureMap B S hS iΛ hV y hy) a =
        functionGlobalSection (deformationStructureMap B S hS y)
          ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (eqToHom (base_eq_tangentBase B S hS iΛ hV y hy))).op).hom a) := fun y hy =>
    congrArg (fun t => (ringOneHom (Space.structureRingSheaf B S hS (deformationSpace B S hS y)) ≫
      (moduleSheafFunctor (Space.structureRingSheaf B S hS (deformationSpace B S hS y))).map
        (unitModuleMul B S hS (deformationSpace B S hS y) t) :
      ⊤_ _ ⟶ (sheafCompose (Space.SmallEtale.topology B S hS (deformationSpace B S hS y).1)
        (forget CommRingCat.{u})).obj
          (Space.smallEtaleRingedTopos B S hS (deformationSpace B S hS y)).O))
      (globalFunctionsOfMap_comp B S hS _ _ a)
  refine (congrArg (Space.smallEtaleRingedToposHom B S hS
      (tangentInclusion B S hS iΛ x' hx')).toToposHom.inverseImage.globalSectionMap
        (hfun x' hx')).trans ?_
  refine Eq.trans ?_ (congrArg (fun t => (Space.smallEtaleRingedToposHom B S hS
      (tangentInclusion B S hS iΛ x hx)).toToposHom.inverseImage.globalSectionMap t ≫
        (sheafCompose (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1)
          (forget CommRingCat.{u})).map
          (tangentInverseImageIso B S hS iΛ e).hom) (hfun x hx)).symm
  exact Deformation.Examples.eq_comp_map_trans_hom_of_comp_map_hom_eq
    (sheafCompose (Space.SmallEtale.topology B S hS x₀.obj.obj.left.1) (forget CommRingCat.{u}))
    (tangentRingComparison B S hS iΛ x hx)
    (AlgebraExtension.extensionRingIso.{u, u + 1, u} e)
    (tangentRingComparison B S hS iΛ x' hx') _ _ h

include e in
/-- **Isomorphic extensions give isomorphic total spaces under `X₀` and over `Spec k[V]`.** An
isomorphism of the extensions of two deformations `x, x'` of `x₀` over `k[V]` gives an isomorphism
`f : X'₁ ≅ X'₂` of their total spaces commuting with the arrows `X₀ ⟶ X'_j` and with the
structure morphisms `X'_j ⟶ Spec k[V]` (Stacks 05YZ, Stacks 05Z1). -/
theorem exists_iso_deformationArrow_comp_eq_of_iso :
    ∃ f : deformationSpace B S hS x ≅ deformationSpace B S hS x',
      (deformationArrow B S hS x).left ≫ f.hom = (deformationArrow B S hS x').left ∧
        f.hom ≫ tangentStructureMap B S hS iΛ hV x' hx' =
          tangentStructureMap B S hS iΛ hV x hx := by
  have := isEquivalence_pushforward_deformationThickeningIso_hom_comp B S hS x
    (ker_residueMap_sq_of_eq B S hS V x hx)
  have := isEquivalence_pushforward_deformationThickeningIso_hom_comp B S hS x'
    (ker_residueMap_sq_of_eq B S hS V x' hx')
  obtain ⟨f, hf, hp, -⟩ := exists_iso_comp_eq_of_inverseImageStructureSheafIso_of_functions _ _
    (tangentInverseImageIso B S hS iΛ e)
    (tangentStructureMap B S hS iΛ hV x hx)
    (tangentStructureMap B S hS iΛ hV x' hx')
    (tangentGenerators B S hS iΛ V hV) (closure_tangentGenerators B S hS iΛ V hV)
    (tangentInverseImageIso_hom_comp B S hS iΛ e) (fun a ha => by
      refine globalSectionMap_tangentInclusion_functionGlobalSection B S hS iΛ hV e a ?_
      rcases ha with ⟨c, rfl⟩ | ⟨v, rfl⟩
      · rw [Γ_map_eqToHom_inl, Γ_map_eqToHom_inl]
        exact deformationFunctionSectionE_tangentRetraction B S hS iΛ e _
      · rw [Γ_map_eqToHom_inr, Γ_map_eqToHom_inr]
        exact deformationFunctionSectionE_tangentFunction B S hS iΛ e v)
  refine ⟨f, ?_, hp⟩
  rwa [← deformationThickeningIso_hom_comp_subspaceInclusion B S hS x
      (ker_residueMap_sq_of_eq B S hS V x hx),
    ← deformationThickeningIso_hom_comp_subspaceInclusion B S hS x'
      (ker_residueMap_sq_of_eq B S hS V x' hx')]

end Iso

/-! ### An isomorphism of total spaces is an isomorphism of deformations -/

section FiberIso

attribute [local instance] PredeformationConstruction.category

variable {V : FGModuleCat.{u} k}
  (hV : B.Contains (Spec (.of ((artinianSquareZeroExtensionFunctor Λ k).obj V))))

/-- The closed immersion `Spec k ⟶ Spec A` of a deformation over `A = k[V]`, followed by the
identification of its base with `Spec k[V]`, is the spectrum of the residue map of `k[V]`. -/
theorem left_post_map_arrow_comp_eqToHom
    (x : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀)
    (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V) :
    ((Over.post B.inclusion).map ((cartesianProperFlatProjection B S hS).map x.arrow ≫
        eqToHom (base_eq_tangentBase B S hS iΛ hV x hx))).left =
      eqToHom (congrArg Over.left hx₀) ≫
        Spec.map (CommRingCat.ofHom
          (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V))) := by
  have key : ∀ (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
      (h : A = (artinianSquareZeroExtensionFunctor Λ k).obj V)
      (E : Spec (.of A) = Spec (.of ((artinianSquareZeroExtensionFunctor Λ k).obj V))),
      Spec.map (CommRingCat.ofHom (residueMap A)) ≫ eqToHom E =
        Spec.map (CommRingCat.ofHom
          (residueMap ((artinianSquareZeroExtensionFunctor Λ k).obj V))) := by
    intro A h E
    subst h
    simp
  have hb := x.arrow_base
  rw [Functor.map_comp, Over.comp_left, eqToHom_map, Over.eqToHom_left]
  have h1 :
      ((Over.post B.inclusion).map ((cartesianProperFlatProjection B S hS).map x.arrow)).left =
      eqToHom (congrArg Over.left hx₀) ≫ Spec.map (CommRingCat.ofHom (residueMap x.algebra)) ≫
        eqToHom (congrArg Over.left x.base).symm := by
    rw [← hb]
    simp only [Functor.comp_map, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, eqToHom_trans, Category.comp_id]
  rw [h1, Category.assoc, Category.assoc, eqToHom_trans]
  exact congrArg (eqToHom (congrArg Over.left hx₀) ≫ ·) (key x.algebra hx _)

variable {x x' : DeformationObject iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion)
    x₀ hx₀}
  (hx : x.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
  (hx' : x'.algebra = (artinianSquareZeroExtensionFunctor Λ k).obj V)
  (f : deformationSpace B S hS x ≅ deformationSpace B S hS x')
  (harr : (deformationArrow B S hS x).left ≫ f.hom = (deformationArrow B S hS x').left)
  (hstr : f.hom ≫ tangentStructureMap B S hS iΛ hV x' hx' = tangentStructureMap B S hS iΛ hV x hx)

/-- Cancelling transports along two identifications with a common object. -/
theorem comp_eq_comp_map_eqToHom_trans {C D : Type*} [Category C] [Category D] {A A' T : C}
    (hb : A = T) (hb' : A' = T) (F : C ⥤ D) {Z Z' : D} (a : Z ⟶ F.obj A) (a' : Z' ⟶ F.obj A')
    (u : Z' ⟶ Z) (v : Z ⟶ Z') (huv : u ≫ v = 𝟙 _)
    (hh : v ≫ a' ≫ F.map (eqToHom hb') = a ≫ F.map (eqToHom hb)) :
    u ≫ a = a' ≫ F.map (eqToHom (hb'.trans hb.symm)) := by
  subst hb hb'
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id] at hh ⊢
  rw [← hh, ← Category.assoc, huv, Category.id_comp]

include hstr in
/-- The inverse of an isomorphism of total spaces over `Spec k[V]` commutes with the structure
morphisms, through the identification of the bases. -/
theorem inv_hom_comp_hom_eq :
    f.inv.hom ≫ x.point.obj.obj.hom = x'.point.obj.obj.hom ≫
      yoneda.map (eqToHom ((base_eq_tangentBase B S hS iΛ hV x' hx').trans
        (base_eq_tangentBase B S hS iΛ hV x hx).symm)) :=
  comp_eq_comp_map_eqToHom_trans (base_eq_tangentBase B S hS iΛ hV x hx)
    (base_eq_tangentBase B S hS iΛ hV x' hx') yoneda x.point.obj.obj.hom x'.point.obj.obj.hom
    f.inv.hom f.hom.hom (congrArg (fun g => g.hom) f.inv_hom_id) (congrArg (fun g => g.hom) hstr)

/-- **The isomorphism of families given by an isomorphism of total spaces over `Spec k[V]`**:
its inverse, over the identification of the bases. -/
def tangentCommaIso : x'.point.obj.obj ≅ x.point.obj.obj :=
  Comma.isoMk f.symm (eqToIso ((base_eq_tangentBase B S hS iΛ hV x' hx').trans
    (base_eq_tangentBase B S hS iΛ hV x hx).symm))
    (inv_hom_comp_hom_eq B S hS iΛ hV hx hx' f hstr)

/-- **The reversed arrow of `Spaces'_{fp, flat, proper}` given by an isomorphism of total spaces
over `Spec k[V]`**: an isomorphism of families, hence strongly cartesian. -/
def tangentArrowOfIso : x'.point ⟶ x.point :=
  ⟨ObjectProperty.homMk (tangentCommaIso B S hS iΛ hV hx hx' f hstr).hom, by
    have : IsIso ((isProperFlatSpace B S hS).ι.map
        (ObjectProperty.homMk (tangentCommaIso B S hS iΛ hV hx hx' f hstr).hom :
          x'.point.obj ⟶ x.point.obj)) :=
      inferInstanceAs (IsIso (tangentCommaIso B S hS iΛ hV hx hx' f hstr).hom)
    change (spacesProjection B S hS).IsStronglyCartesian
      ((spacesProjection B S hS).map ((isProperFlatSpace B S hS).ι.map
        (ObjectProperty.homMk (tangentCommaIso B S hS iΛ hV hx hx' f hstr).hom :
          x'.point.obj ⟶ x.point.obj)))
      ((isProperFlatSpace B S hS).ι.map
        (ObjectProperty.homMk (tangentCommaIso B S hS iΛ hV hx hx' f hstr).hom :
          x'.point.obj ⟶ x.point.obj))
    exact Functor.IsStronglyCartesian.of_isIso (spacesProjection B S hS) _ _⟩

include harr in
/-- The reversed arrow commutes with the arrows out of `x₀`. -/
theorem arrow_comp_tangentArrowOfIso :
    x'.arrow ≫ tangentArrowOfIso B S hS iΛ hV hx hx' f hstr = x.arrow := by
  apply WideSubcategory.hom_ext
  apply ObjectProperty.hom_ext
  apply Comma.hom_ext
  · change (deformationArrow B S hS x').left ≫ f.inv = (deformationArrow B S hS x).left
    rw [← harr, Category.assoc, f.hom_inv_id, Category.comp_id]
  · change (cartesianProperFlatProjection B S hS).map x'.arrow ≫
        eqToHom ((base_eq_tangentBase B S hS iΛ hV x' hx').trans
          (base_eq_tangentBase B S hS iΛ hV x hx).symm) =
      (cartesianProperFlatProjection B S hS).map x.arrow
    have h : (cartesianProperFlatProjection B S hS).map x'.arrow ≫
        eqToHom (base_eq_tangentBase B S hS iΛ hV x' hx') =
        (cartesianProperFlatProjection B S hS).map x.arrow ≫
          eqToHom (base_eq_tangentBase B S hS iΛ hV x hx) := by
      apply BigFppfOver.map_injective_post_inclusion B S hS
      apply Over.OverMorphism.ext
      exact (left_post_map_arrow_comp_eqToHom B S hS iΛ hV x' hx').trans
        (left_post_map_arrow_comp_eqToHom B S hS iΛ hV x hx).symm
    rw [← eqToHom_trans (base_eq_tangentBase B S hS iΛ hV x' hx')
      (base_eq_tangentBase B S hS iΛ hV x hx).symm, ← Category.assoc, h, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- A transport of spectra along an identification of algebras is the spectrum of the
identification. -/
theorem eqToHom_eq_spec_map_eqToHom (A A' : ArtinianLocalAlgCat.{u, u, u} Λ k) (h : A = A')
    (E : Spec (.of A') = Spec (.of A)) :
    eqToHom E = Spec.map (CommRingCat.ofHom (eqToHom h).hom.toRingHom) := by
  subst h
  simp

/-- **The morphism of deformations given by an isomorphism of total spaces under `X₀` and over
`Spec k[V]`.** -/
def tangentDeformationMorphismOfIso :
    DeformationMorphism iΛ (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion) x₀ hx₀
      x x' where
  ringHom := eqToHom (hx.trans hx'.symm)
  arrow := tangentArrowOfIso B S hS iΛ hV hx hx' f hstr
  triangle := arrow_comp_tangentArrowOfIso B S hS iΛ hV hx hx' f harr hstr
  arrow_base := by
    change eqToHom (congrArg Over.left x'.base).symm ≫
        ((Over.post B.inclusion).map (eqToHom ((base_eq_tangentBase B S hS iΛ hV x' hx').trans
          (base_eq_tangentBase B S hS iΛ hV x hx).symm))).left ≫
        eqToHom (congrArg Over.left x.base) = _
    rw [eqToHom_map, Over.eqToHom_left, eqToHom_trans, eqToHom_trans]
    exact eqToHom_eq_spec_map_eqToHom x.algebra x'.algebra (hx.trans hx'.symm) _

include harr in
/-- The inverse of an isomorphism of total spaces under `X₀` is under `X₀`. -/
theorem deformationArrow_comp_inv :
    (deformationArrow B S hS x').left ≫ f.inv = (deformationArrow B S hS x).left := by
  rw [← harr, Category.assoc, Iso.hom_inv_id, Category.comp_id]

include hstr in
/-- The inverse of an isomorphism of total spaces over `Spec k[V]` is over `Spec k[V]`. -/
theorem inv_comp_tangentStructureMap :
    f.inv ≫ tangentStructureMap B S hS iΛ hV x hx = tangentStructureMap B S hS iΛ hV x' hx' := by
  rw [← hstr, Iso.inv_hom_id_assoc]

/-- **An isomorphism of total spaces under `X₀` and over `Spec k[V]` is an isomorphism of
deformations**, in the fibre of `𝓕` over `k[V]`. -/
def tangentFiberIsoOfIso
    (y y' : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber
      ((squareZeroExtensionArtinian Λ k).obj V))
    (f : deformationSpace B S hS y.1 ≅ deformationSpace B S hS y'.1)
    (harr : (deformationArrow B S hS y.1).left ≫ f.hom = (deformationArrow B S hS y'.1).left)
    (hstr : f.hom ≫ tangentStructureMap B S hS iΛ hV y'.1 y'.2 =
      tangentStructureMap B S hS iΛ hV y.1 y.2) : y ≅ y' where
  hom := ⟨tangentDeformationMorphismOfIso B S hS iΛ hV y.2 y'.2 f harr hstr,
    IsHomLift.of_fac' (predeformationBased B S hS iΛ x₀ hx₀).p _ _ y.2 y'.2 (by
      change eqToHom (y.2.trans y'.2.symm) = _
      simp only [eqToHom_trans, Category.id_comp])⟩
  inv := ⟨tangentDeformationMorphismOfIso B S hS iΛ hV y'.2 y.2 f.symm
      (deformationArrow_comp_inv B S hS iΛ f harr)
      (inv_comp_tangentStructureMap B S hS iΛ hV y.2 y'.2 f hstr),
    IsHomLift.of_fac' (predeformationBased B S hS iΛ x₀ hx₀).p _ _ y'.2 y.2 (by
      change eqToHom (y'.2.trans y.2.symm) = _
      simp only [eqToHom_trans, Category.id_comp])⟩
  hom_inv_id := by
    apply Functor.Fiber.hom_ext
    apply DeformationMorphism.ext_of_components
    · change eqToHom (y.2.trans y'.2.symm) ≫ eqToHom (y'.2.trans y.2.symm) = 𝟙 _
      simp only [eqToHom_trans, eqToHom_refl]
    · apply WideSubcategory.hom_ext
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · change f.symm.inv ≫ f.inv = 𝟙 _
        exact f.hom_inv_id
      · change eqToHom ((base_eq_tangentBase B S hS iΛ hV y.1 y.2).trans
            (base_eq_tangentBase B S hS iΛ hV y'.1 y'.2).symm) ≫
          eqToHom ((base_eq_tangentBase B S hS iΛ hV y'.1 y'.2).trans
            (base_eq_tangentBase B S hS iΛ hV y.1 y.2).symm) = 𝟙 _
        simp only [eqToHom_trans, eqToHom_refl]
  inv_hom_id := by
    apply Functor.Fiber.hom_ext
    apply DeformationMorphism.ext_of_components
    · change eqToHom (y'.2.trans y.2.symm) ≫ eqToHom (y.2.trans y'.2.symm) = 𝟙 _
      simp only [eqToHom_trans, eqToHom_refl]
    · apply WideSubcategory.hom_ext
      apply ObjectProperty.hom_ext
      apply Comma.hom_ext
      · change f.inv ≫ f.symm.inv = 𝟙 _
        exact f.inv_hom_id
      · change eqToHom ((base_eq_tangentBase B S hS iΛ hV y'.1 y'.2).trans
            (base_eq_tangentBase B S hS iΛ hV y.1 y.2).symm) ≫
          eqToHom ((base_eq_tangentBase B S hS iΛ hV y.1 y.2).trans
            (base_eq_tangentBase B S hS iΛ hV y'.1 y'.2).symm) = 𝟙 _
        simp only [eqToHom_trans, eqToHom_refl]

end FiberIso

/-! ### Injectivity -/

section Injective

attribute [local instance] PredeformationConstruction.category

/-- The spectrum of `k[V]` lies in the site. -/
theorem contains_spec_squareZero (y₀ : CartesianProperFlatSpaces B S hS)
    (hy₀ : (cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion).obj y₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) (V : FGModuleCat.{u} k) :
    B.Contains (Spec (.of ((artinianSquareZeroExtensionFunctor Λ k).obj V))) := by
  have h : B.inclusion.obj ((cartesianProperFlatProjection B S hS).obj y₀).left = Spec (.of k) :=
    congrArg Comma.left hy₀
  exact contains_spec_of_artinianLocalAlgCat _
    (h ▸ ((cartesianProperFlatProjection B S hS).obj y₀).left.property)

/-- **Deformations over `k[V]` with the same class are isomorphic**: equal classes give
isomorphic extensions (Stacks 0GQ5), hence isomorphic total spaces under `X₀` and over
`Spec k[V]` (Stacks 05YZ, 05Z1), hence isomorphic deformations. -/
theorem isIsomorphic_of_tangentFiberClass_eq {V : FGModuleCat.{u} k}
    (y y' : (predeformationBased B S hS iΛ x₀ hx₀).p.Fiber
      ((squareZeroExtensionArtinian Λ k).obj V))
    (h : tangentFiberClass y = tangentFiberClass y') :
    IsIsomorphic y y' := by
  obtain ⟨e⟩ := nonempty_iso_of_modelExtClass_eq B S hS h
  obtain ⟨f, harr, hstr⟩ := exists_iso_deformationArrow_comp_eq_of_iso B S hS iΛ
    (contains_spec_squareZero B S hS iΛ x₀ hx₀ V) e
  exact ⟨tangentFiberIsoOfIso B S hS iΛ _ y y' f harr hstr⟩

/-- **The class map of deformations over `k[ε]` is injective**: two first-order deformations of
`x₀` with the same class in `Ext¹(NL_{X₀/k}, 𝒪_{X₀})` are isomorphic. -/
theorem tangentExtClassAt_injective
    (h𝓕 : IsCofiberedInGroupoids (predeformationBased B S hS iΛ x₀ hx₀).p) :
    Function.Injective (tangentExtClassAt B S hS iΛ x₀ hx₀ h𝓕 (FGModuleCat.of k k)) := by
  intro z z' h
  obtain ⟨y, rfl⟩ := classOf_surjective (predeformationBased B S hS iΛ x₀ hx₀) h𝓕
    ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k k)) z
  obtain ⟨y', rfl⟩ := classOf_surjective (predeformationBased B S hS iΛ x₀ hx₀) h𝓕
    ((squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k k)) z'
  have h₁ := tangentExtClassAt_classOf B S hS iΛ x₀ hx₀ h𝓕 (FGModuleCat.of k k) y
  have h₂ := tangentExtClassAt_classOf B S hS iΛ x₀ hx₀ h𝓕 (FGModuleCat.of k k) y'
  exact classOf_eq_of_isIsomorphic _ _ y y'
    (isIsomorphic_of_tangentFiberClass_eq B S hS iΛ y y' (h₁.symm.trans (h.trans h₂)))

end Injective

end AlgebraicGeometry.ProperFlatSpaceDeformation

end
