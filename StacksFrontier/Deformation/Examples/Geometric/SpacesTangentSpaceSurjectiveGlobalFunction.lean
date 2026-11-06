module

public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineOver
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientGlobalSections
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveRealization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The function `ε` on the thickening realizing an extension, and the map to `Spec k[ε]`

In the situation of `Deformation.Examples.spaceSurjAmbient`, let `X ⊂ X'` be the thickening
realizing an extension `P` of `f⁻¹𝒪_{Spec k}`-algebras of `𝒪_X` by `𝒪_X ⊗_k k`. The section
`1 ⊗ 1` of the ideal is a global section `e` of the middle term `𝒜 = i⁻¹𝒪_{X'}` of square zero;
the inverse image along `X ⟶ X'` being bijective on global sections (Stacks 05ZM), it comes from a
unique global function `ε` of `X'`. On the charts `W' ⟶ X'` of the thickened quotient, `ε` is
`e` read in `Γ(W', ⊤) = 𝒜(W)`; so `ε² = 0`, and `k[ε] ⟶ Γ(X', 𝒪_{X'})`, `a + bε ↦ a + bε`, is
a homomorphism of `k`-algebras. By Stacks 05Z1 over `Spec k` it is a morphism
`X' ⟶ Spec k[ε]` over `Spec k`.

## Main definitions

* `Deformation.Examples.spaceRankOneSection`: the section `1 ⊗ 1` of `𝒪_X ⊗_k k`.
* `Deformation.Examples.spaceSurjEpsSection`: its image `e` in the middle term of `P`.
* `Deformation.Examples.spaceSurjEps`: the global function `ε` of `X'`.
* `Deformation.Examples.spaceSurjToDual`: the morphism `X' ⟶ Spec k[ε]`.

## References

* [Stacks Project, Tag 05Z1](https://stacks.math.columbia.edu/tag/05Z1)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space AlgebraicGeometry.Space.SquareZeroExtension
open Deformation.AlgebraExtension CategoryTheory.Sheaf Deformation.Artin

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

/-- Presheaves of sets have products indexed by `Type u`, stated directly so that instance search
does not time out. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheafType_spaceSurjGlobalFunction
    {C : Type*} [Category C] (K : Type u) : HasLimitsOfShape (Discrete K) (C ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- Presheaves of sets have products indexed by `Type`, stated directly so that instance search
does not time out. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheafType₀_spaceSurjGlobalFunction
    {C : Type*} [Category C] (K : Type) : HasLimitsOfShape (Discrete K) (C ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

/-- Sheaves of sets have a terminal object, stated directly so that instance search does not
time out. -/
local instance (priority := high) hasTerminal_sheafType_spaceSurjGlobalFunction
    {C : Type*} [Category C] (J : GrothendieckTopology C) : HasTerminal (Sheaf J (Type u)) :=
  inferInstanceAs (HasLimitsOfShape (Discrete PEmpty) (Sheaf J (Type u)))

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **The section `1 ⊗ 1` of `𝒪_X ⊗_k k`.** -/
abbrev spaceRankOneSection :
    unitModule B (Spec (.of Λ)) hΛ hX ⟶ spaceRankOneCoefficient B hΛ hSpec X hX toK :=
  baseRingTensorSection B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
    (spaceDefoFieldHom B hΛ hSpec X hX toK)
    ((forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) (1 : k)

variable (P : AlgebraExtension (J := SmallEtale.topology B (Spec (.of Λ)) hΛ X)
  (inverseImageBaseMap B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))
  (spaceRankOneCoefficient B hΛ hSpec X hX toK))

/-- **The global section `e = 1 ⊗ 1` of the middle term of `P`**, on sheaves of sets. -/
abbrev spaceSurjEpsSection :
    ⊤_ Sheaf (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj P.extension :=
  ringOneHom ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).O) ≫
    (moduleSheafFunctor ((sheafCompose (SmallEtale.topology B (Spec (.of Λ)) hΛ X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).O)).map
      (spaceRankOneSection B hΛ hSpec X hX toK) ≫
    P.inclSheafSets

/-- The value of `e` at `U` is the image in the middle term of `P` of the value of `1 ⊗ 1`
at `U`. -/
theorem spaceSurjEpsSection_app (U : (SmallEtale B (Spec (.of Λ)) hΛ X)ᵒᵖ)
    (p : (⊤_ Sheaf (SmallEtale.topology B (Spec (.of Λ)) hΛ X) (Type u)).obj.obj U) :
    (spaceSurjEpsSection B hΛ hSpec X hX toK P).hom.app U p =
      P.incl ((spaceRankOneSection B hΛ hSpec X hX toK).val.app U
        (1 : (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)).obj.obj U)) :=
  rfl

/-- Abbreviation for the square-zero extension `spaceSurjExtension`. -/
local notation "E" => spaceSurjExtension B hΛ hSpec X hX toK P
/-- Abbreviation for the presentation. -/
local notation "Pp" => spaceSurjPresentation B hΛ hSpec X hX toK
/-- Abbreviation for the containment of the chart thickening. -/
local notation "hU" => contains_spaceSurj_chartRealizedScheme B hΛ hSpec X hX toK P _

/-- **The global function `ε` of `X'`**, on sheaves of sets: the unique global section of
`𝒪_{X'}` whose inverse image along `X ⟶ X'`, read in `𝒜`, is `e`. -/
def spaceSurjEpsSet :
    ⊤_ Sheaf (SmallEtale.topology B (Spec (.of Λ)) hΛ
        (spaceSurjAmbient B hΛ hSpec X hX toK P).1) (Type u) ⟶
      (sheafCompose _ (forget CommRingCat.{u})).obj
        (smallEtaleRingedTopos B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)).O :=
  (Equiv.ofBijective _ ((E).bijective_globalSectionMap_thickeningImmersion Pp hU hU _)).symm
    (spaceSurjEpsSection B hΛ hSpec X hX toK P ≫
      (sheafCompose _ (forget CommRingCat.{u})).map ((E).quotientSheafIso Pp hU hU).inv)

/-- The inverse image of `ε` along `X ⟶ X'`, read in the middle term `𝒜` of `P`, is `e`. -/
theorem globalSectionMap_spaceSurjEpsSet :
    (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
        (spaceSurjImmersion B hΛ hSpec X hX toK P)).toToposHom.inverseImage.globalSectionMap
        (spaceSurjEpsSet B hΛ hSpec X hX toK P) ≫
      (sheafCompose _ (forget CommRingCat.{u})).map ((E).quotientSheafIso Pp hU hU).hom =
    spaceSurjEpsSection B hΛ hSpec X hX toK P := by
  have h := (Equiv.ofBijective _
    ((E).bijective_globalSectionMap_thickeningImmersion Pp hU hU _)).apply_symm_apply
    (spaceSurjEpsSection B hΛ hSpec X hX toK P ≫
      (sheafCompose _ (forget CommRingCat.{u})).map ((E).quotientSheafIso Pp hU hU).inv)
  change (smallEtaleRingedToposHom B (Spec (.of Λ)) hΛ
        (spaceSurjImmersion B hΛ hSpec X hX toK P)).toToposHom.inverseImage.globalSectionMap
        (spaceSurjEpsSet B hΛ hSpec X hX toK P) = _ at h
  refine (congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans ?_)
  refine (congrArg (_ ≫ ·) ((Functor.map_comp _ _ _).symm.trans ((congrArg _
    (Iso.inv_hom_id _)).trans (CategoryTheory.Functor.map_id _ _)))).trans ?_
  exact Category.comp_id _

/-- **The global function `ε` of `X'`.** -/
abbrev spaceSurjEps : globalFunctions B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P).1 :=
  globalFunctionsOfSection (spaceSurjEpsSet B hΛ hSpec X hX toK P)

/-- **`ε² = 0`.** -/
theorem spaceSurjEps_mul_self :
    spaceSurjEps B hΛ hSpec X hX toK P * spaceSurjEps B hΛ hSpec X hX toK P = 0 :=
  (E).globalFunctionsOfSection_mul_self_eq_zero Pp hU hU _ _
    (globalSectionMap_spaceSurjEpsSet B hΛ hSpec X hX toK P) fun W p => by
      refine (map_mul ((E).chartRealizedSchemeΓIso W.obj).hom.hom _ _).symm.trans ?_
      refine (congrArg _ ?_).trans (map_zero _)
      exact P.incl_mul_incl _ _

/-- The right action of `k` on a `k`-module, the one through which `k[V]` is formed. -/
local instance (M : FGModuleCat.{u} k) : Module kᵐᵒᵖ M :=
  Module.oppositeOfCommSemiring k M

local instance (M : FGModuleCat.{u} k) : IsCentralScalar k M :=
  Module.isCentralScalar_oppositeOfCommSemiring k M

/-- The dual numbers `k[ε]`, as an object of `𝒞_Λ`. -/
@[sga "3 III 4.38" "partial", sga "3 VIIB 2.6" "special case"]
abbrev spaceDualNumbers : ArtinianLocalAlgCat.{u, u, u} Λ k :=
  (squareZeroExtensionArtinian Λ k).obj (FGModuleCat.of k k)

/-- The pullback of functions along `X' ⟶ Spec k`, from `k`. -/
abbrev spaceSurjConstants : k →+* globalFunctions B (Spec (.of Λ)) hΛ
    (spaceSurjAmbient B hΛ hSpec X hX toK P).1 :=
  (pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)
    (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) (spaceSurjToBase B hΛ hSpec X hX toK P)).comp
    (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)).toRingHom

/-- **`k[ε] ⟶ Γ(X', 𝒪_{X'})`, `a + bε ↦ a + bε`.** -/
def spaceSurjDualHom : spaceDualNumbers (Λ := Λ) (k := k) →+*
    globalFunctions B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P).1 where
  toFun r := spaceSurjConstants B hΛ hSpec X hX toK P (TrivSqZeroExt.fst (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r) +
    spaceSurjConstants B hΛ hSpec X hX toK P (show k from TrivSqZeroExt.snd (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r) *
      spaceSurjEps B hΛ hSpec X hX toK P
  map_one' := by
    change spaceSurjConstants B hΛ hSpec X hX toK P 1 +
      spaceSurjConstants B hΛ hSpec X hX toK P 0 * spaceSurjEps B hΛ hSpec X hX toK P = 1
    rw [map_one, map_zero, zero_mul, add_zero]
  map_mul' r r' := by
    change spaceSurjConstants B hΛ hSpec X hX toK P (TrivSqZeroExt.fst (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r * TrivSqZeroExt.fst (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r') +
      spaceSurjConstants B hΛ hSpec X hX toK P
        ((show k from TrivSqZeroExt.fst (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r * (show k from TrivSqZeroExt.snd (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r')) +
          (show k from TrivSqZeroExt.fst (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r' * (show k from TrivSqZeroExt.snd (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r))) *
        spaceSurjEps B hΛ hSpec X hX toK P = _
    have he := spaceSurjEps_mul_self B hΛ hSpec X hX toK P
    simp only [map_add, map_mul]
    linear_combination -(spaceSurjConstants B hΛ hSpec X hX toK P (show k from TrivSqZeroExt.snd (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r) *
      spaceSurjConstants B hΛ hSpec X hX toK P (show k from TrivSqZeroExt.snd (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r')) * he
  map_zero' := by
    change spaceSurjConstants B hΛ hSpec X hX toK P 0 +
      spaceSurjConstants B hΛ hSpec X hX toK P 0 * spaceSurjEps B hΛ hSpec X hX toK P = 0
    rw [map_zero, zero_mul, add_zero]
  map_add' r r' := by
    change spaceSurjConstants B hΛ hSpec X hX toK P (TrivSqZeroExt.fst (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r + TrivSqZeroExt.fst (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r') +
      spaceSurjConstants B hΛ hSpec X hX toK P
        ((show k from TrivSqZeroExt.snd (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r) + (show k from TrivSqZeroExt.snd (R := k) (M := (forget₂ (FGModuleCat.{u} k) (ModuleCat.{u} k)).obj (FGModuleCat.of k k)) r')) *
        spaceSurjEps B hΛ hSpec X hX toK P = _
    simp only [map_add]
    ring

/-- `k[ε] ⟶ Γ(X', 𝒪_{X'})` sends a constant `a ∈ k` to its pullback along `X' ⟶ Spec k`. -/
theorem spaceSurjDualHom_inl (a : k) :
    spaceSurjDualHom B hΛ hSpec X hX toK P (squareZeroSection Λ k (FGModuleCat.of k k) a) =
      spaceSurjConstants B hΛ hSpec X hX toK P a := by
  change spaceSurjConstants B hΛ hSpec X hX toK P a +
    spaceSurjConstants B hΛ hSpec X hX toK P 0 * spaceSurjEps B hΛ hSpec X hX toK P = _
  rw [map_zero, zero_mul, add_zero]

variable (Λ) in
/-- **Pullback of functions along the retraction `Spec k[V] ⟶ Spec k` is the inclusion of
constants**, through `k ≃ Γ(Spec k)` and `k[V] ≃ Γ(Spec k[V])`. -/
theorem spaceConstants_Γ_comp (V : FGModuleCat.{u} k) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceBaseOverMap B hΛ hSpec (spaceConstants Λ V))).op).hom.comp
        (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)).toRingHom =
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
        ((squareZeroExtensionArtinian Λ k).obj V)).toRingHom.comp
        (spaceConstants Λ V).hom.toRingHom := by
  have hm : (BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
      (spaceBaseOverMap B hΛ hSpec (spaceConstants Λ V)) =
      Spec.map (CommRingCat.ofHom (spaceConstants Λ V).hom.toRingHom) := B.inclusion.map_preimage _
  rw [hm]
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (spaceConstants Λ V).hom.toRingHom)
  ext a
  exact (congrArg (fun g => g.hom a) h).symm

/-- The retraction `Spec k[ε] ⟶ Spec k` of the constants. -/
abbrev spaceDualRetraction :
    spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k)) ⟶
      spaceBaseOver B hΛ hSpec (residueFieldBase Λ k) :=
  spaceBaseOverMap B hΛ hSpec (spaceConstants Λ (FGModuleCat.of k k))

/-- **`Γ(Spec k[ε]) ⟶ Γ(X', 𝒪_{X'})`.** -/
abbrev spaceSurjFunctions :
    Γ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).obj
        (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))), ⊤) →+*
      globalFunctions B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P).1 :=
  (spaceSurjDualHom B hΛ hSpec X hX toK P).comp
    (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) _).symm.toRingHom

/-- The composite `Γ(Spec k) ⟶ Γ(Spec k[ε]) ⟶ Γ(X', 𝒪_{X'})` is the pullback of functions along
`X' ⟶ Spec k`. -/
theorem spaceSurjFunctions_comp :
    (spaceSurjFunctions B hΛ hSpec X hX toK P).comp
        (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
          (spaceDualRetraction B hΛ hSpec)).op).hom =
      pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)
        (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)) (spaceSurjToBase B hΛ hSpec X hX toK P) := by
  ext1 x
  obtain ⟨a, rfl⟩ := (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec)
    (residueFieldBase Λ k)).surjective x
  have h := congrArg (fun φ => φ a) (spaceConstants_Γ_comp Λ B hΛ hSpec (FGModuleCat.of k k))
  change spaceSurjDualHom B hΛ hSpec X hX toK P
    ((spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) _).symm
      ((Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceDualRetraction B hΛ hSpec)).op).hom
          ((spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)) a))) = _
  rw [show (Scheme.Γ.map ((BigFppfOver.toScheme B (Spec (.of Λ)) hΛ).map
        (spaceDualRetraction B hΛ hSpec)).op).hom
          ((spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) (residueFieldBase Λ k)) a) =
      (spaceDefoAlgebraEquiv (B := B) (hΛ := hΛ) (hSpec := hSpec) _)
        ((spaceConstants Λ (FGModuleCat.of k k)).hom.toRingHom a) from h,
    RingEquiv.symm_apply_apply]
  exact spaceSurjDualHom_inl B hΛ hSpec X hX toK P a


/-- **The morphism `X' ⟶ Spec k[ε]` over `Spec k`** (Stacks 05Z1 over `Spec k`) whose pullback of
functions is `k[ε] ⟶ Γ(X', 𝒪_{X'})`, `ε ↦ ε`. -/
def spaceSurjToDual :
    spaceSurjAmbient B hΛ hSpec X hX toK P ⟶
      schemeSpace (spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))) :=
  haveI := isAffine_toScheme_spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)
  haveI := isAffine_toScheme_spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))
  ((morphismToAffineOverEquiv B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)
    (spaceDualRetraction B hΛ hSpec) (spaceSurjToBase B hΛ hSpec X hX toK P)).1.symm
      ⟨spaceSurjFunctions B hΛ hSpec X hX toK P, spaceSurjFunctions_comp B hΛ hSpec X hX toK P⟩).1

/-- `X' ⟶ Spec k[ε]` is a morphism over `Spec k`: followed by the retraction
`Spec k[ε] ⟶ Spec k`, it is `X' ⟶ Spec k`. -/
theorem spaceSurjToDual_comp :
    spaceSurjToDual B hΛ hSpec X hX toK P ≫ schemeSpaceMap (spaceDualRetraction B hΛ hSpec) =
      spaceSurjToBase B hΛ hSpec X hX toK P :=
  haveI := isAffine_toScheme_spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)
  haveI := isAffine_toScheme_spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))
  ((morphismToAffineOverEquiv B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)
    (spaceDualRetraction B hΛ hSpec) (spaceSurjToBase B hΛ hSpec X hX toK P)).1.symm
      ⟨spaceSurjFunctions B hΛ hSpec X hX toK P, spaceSurjFunctions_comp B hΛ hSpec X hX toK P⟩).2

/-- The pullback of functions along `X' ⟶ Spec k[ε]` is `Γ(Spec k[ε]) ⟶ Γ(X', 𝒪_{X'})`. -/
theorem pullbackToGlobalFunctions_spaceSurjToDual :
    pullbackToGlobalFunctions B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P) _
        (spaceSurjToDual B hΛ hSpec X hX toK P) =
      spaceSurjFunctions B hΛ hSpec X hX toK P := by
  haveI := isAffine_toScheme_spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)
  haveI := isAffine_toScheme_spaceBaseOver B hΛ hSpec (spaceDualNumbers (Λ := Λ) (k := k))
  let e := morphismToAffineOverEquiv B (Spec (.of Λ)) hΛ (spaceSurjAmbient B hΛ hSpec X hX toK P)
    (spaceDualRetraction B hΛ hSpec) (spaceSurjToBase B hΛ hSpec X hX toK P)
  exact (e.2 (e.1.symm ⟨_, spaceSurjFunctions_comp B hΛ hSpec X hX toK P⟩)).symm.trans
    (congrArg Subtype.val (e.1.apply_symm_apply _))

end Deformation.Examples


end
