module

public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ComplexMapInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseRingTensorModuleFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.Cotangent.SheavesOfRings.RingedToposNaiveExtComparison
public import StacksFrontier.Deformation.ToposThickening.SolutionAutomorphismsExt
public import StacksFrontier.Deformation.ToposThickening.SolutionSiteTransport

/-!
# The functors `M ↦ Ext^i_{𝒪_X}(L_{X/Y}, 𝒪_X ⊗_R M)` of an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S : Scheme.{u}`, and let
`φ : R →+* Γ(X, 𝒪_X)` be a ring map, read on the `Type u` model of the small étale site of `X`.
In [Stacks Project, Remark 0D1P] the deformations and obstructions of `X` over `Y = Spec(R)` are
the groups

`T^i(M) = Ext^i_{𝒪_X}(L_{X/Y}, 𝒪_X ⊗_R M)`,  `i = 1, 2`,

functors of the `R`-module `M`, with a connecting map `T¹(M₃) ⟶ T²(M₁)` attached to every short
exact sequence `0 → M₁ → M₂ → M₃ → 0` when `𝒪_X` is flat over `R`. This file constructs them as
functors `ModuleCat R ⥤ ModuleCat R`, as the fields `T₁`, `T₂` and `δ` of
`Deformation.Artin.FunctorDeformationTheory` need them.

## Where the groups are formed

The small étale site of `X` has objects in `Type (u + 1)`, so its sheaves of modules with sections
in `Type u` have no cotangent complex of their own: the standard resolution is formed in a universe
containing the site. The groups are therefore formed on the `Type u` model of that site, the ringed
topos `(smallEtaleRingedTopos X).ofSiteEquivalence` of
`StacksFrontier/Deformation/ToposThickening/SolutionSiteTransport.lean`, whose site, morphisms and
sections all live in `Type u`:

* `L_{X/Y}` is the cotangent complex `L_{f'}` of the transported morphism of ringed topoi
  `f' = AlgebraicGeometry.Space.modelRingedToposHom f`, the cotangent complex of the structure map
  `f'⁻¹𝒪_Y ⟶ 𝒪_X` restricted to the model (Tag 08SU);
* `𝒪_X ⊗_R M` is `Stacks.Cohomology.SiteModules.baseRingTensorFunctor φ M` of Tag 0D3F, formed on
  the same model, which is what `AlgebraicGeometry.Space.baseRingTensorModule` carries back to `X`.

This is the topos on which [Stacks Project, Tag 08V5] applies verbatim, through
`Deformation.ToposThickening.RingedToposExtensionProblem.siteTransport`.

## Main definitions

* `Deformation.Artin.small_shiftedHom_singleFunctor`: in a locally `w`-small abelian category with
  enough injectives, `Hom_{D}(K, G[n])` is `w`-small for every complex `K` and object `G`.
* `Deformation.Artin.moduleFunctorOfAdditive`: an additive functor
  `F : ModuleCat R ⥤ AddCommGrpCat` with small values, made `R`-linear by letting `r` act on
  `F(M)` through `F(r • 𝟙)`.
* `AlgebraicGeometry.Space.modelRingedToposHom`: the transported morphism `f'`.
* `AlgebraicGeometry.Space.cotangentExtFunctor`: `M ↦ Ext^i(L_{X/Y}, 𝒪_X ⊗_R M)`, and
  `AlgebraicGeometry.Space.cotangentExtOne`, `AlgebraicGeometry.Space.cotangentExtTwo` its values
  at `i = 1, 2`.
* `AlgebraicGeometry.Space.cotangentExtConnecting`: the connecting map `T¹(M₃) ⟶ T²(M₁)`.

## Conventions

* An element of `T^i(M)` is the image under `equivShrink` of a morphism
  `ξ : L_{X/Y} ⟶ (𝒪_X ⊗_R M)[0]⟦i⟧` of the derived category, a `ShiftedHom` of degree `i`.
* `r : R` acts by pushing forward along `𝒪_X ⊗ (r • 𝟙_M)`: `r • ξ = ξ ≫ (𝒪_X ⊗ (r • 𝟙))[0]⟦i⟧`.
* The connecting map of a short exact sequence `0 → M₁ → M₂ → M₃ → 0` sends `ξ` to
  `ξ.comp δ (1 + 1 = 2)`, where `δ : (𝒪_X ⊗ M₃)[0] ⟶ (𝒪_X ⊗ M₁)[0]⟦1⟧` is Mathlib's
  `CategoryTheory.ShortComplex.ShortExact.singleδ` of the short exact sequence
  `0 → 𝒪_X ⊗ M₁ → 𝒪_X ⊗ M₂ → 𝒪_X ⊗ M₃ → 0`. No sign is inserted.

## References

* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t u

namespace Deformation.Artin

/-! ### Smallness of morphisms into a shifted single complex -/

section Smallness

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **Morphisms into a shifted single complex are small.** In a locally `w`-small abelian
category with enough injectives, `Hom_{D}(K, G[0]⟦n⟧)` is `w`-small for every complex `K`: by an
injective resolution `G → I`, it is the group of homotopy classes of chain maps `K ⟶ I⟦n⟧`, a
quotient of a subtype of `∏ᵢ Hom(Kⁱ, Iⁱ⁺ⁿ)`. -/
theorem small_shiftedHom_singleFunctor [LocallySmall.{w} C] [EnoughInjectives C]
    (K : CochainComplex C ℤ) (G : C) (n : ℤ) :
    Small.{w} (ShiftedHom (DerivedCategory.Q.obj K)
      ((DerivedCategory.singleFunctor C 0).obj G) n) := by
  let R : InjectiveResolution G := injectiveResolution G
  have : CochainComplex.IsKInjective R.cochainComplex :=
    CochainComplex.isKInjective_of_injective _ 0
  let e : ((DerivedCategory.singleFunctor C 0).obj G)⟦n⟧ ≅
      DerivedCategory.Q.obj (R.cochainComplex⟦n⟧) :=
    (shiftFunctor _ n).mapIso (Functor.singleIsoResolution R) ≪≫
      (DerivedCategory.Q.commShiftIso n).symm.app R.cochainComplex
  have hchain : Small.{w} (K ⟶ R.cochainComplex⟦n⟧) :=
    small_of_injective (f := fun φ : K ⟶ R.cochainComplex⟦n⟧ => φ.f)
      (fun _ _ h => HomologicalComplex.hom_ext _ _ (fun i => congrFun h i))
  have hhtpy : Small.{w} ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (R.cochainComplex⟦n⟧)) :=
    small_of_surjective (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective
  exact small_of_injective (f := fun φ =>
      (Functor.derivedHomAddEquivOfIsKInjective K (R.cochainComplex⟦n⟧)).symm (φ ≫ e.hom))
    (fun φ ψ h => by simpa [cancel_mono] using h)

end Smallness

/-! ### Additive functors with values in `R`-modules -/

section ModuleFunctor

variable {R : Type u} [CommRing R] (F : ModuleCat.{u} R ⥤ AddCommGrpCat.{t}) [F.Additive]

/-- The action of `r : R` on `F(M)` through `F(r • 𝟙_M)`. -/
def scalarAction (M : ModuleCat.{u} R) : R →+* AddMonoid.End (F.obj M) where
  toFun r := (F.map (r • 𝟙 M)).hom
  map_one' := by
    rw [one_smul, F.map_id]
    rfl
  map_mul' r s := by
    have h : (r * s) • 𝟙 M = (s • 𝟙 M) ≫ (r • 𝟙 M) := by
      rw [Linear.smul_comp, Linear.comp_smul, Category.comp_id, smul_smul, mul_comm]
    rw [h, F.map_comp]
    rfl
  map_zero' := by
    rw [zero_smul, F.map_zero]
    rfl
  map_add' r s := by
    rw [add_smul, F.map_add]
    rfl

/-- The `R`-module structure of `F(M)`: `r` acts through `F(r • 𝟙_M)`. -/
@[reducible]
def scalarModule (M : ModuleCat.{u} R) : Module R (F.obj M) :=
  Module.compHom (F.obj M) (scalarAction F M)

attribute [local instance] scalarModule

/-- `r : R` acts on `F(M)` through `F(r • 𝟙_M)`. -/
theorem scalarModule_smul (M : ModuleCat.{u} R) (r : R) (x : F.obj M) :
    r • x = (F.map (r • 𝟙 M)).hom x :=
  rfl

/-- `F(g)` is `R`-linear for the structures `scalarModule`. -/
def scalarLinearMap {M N : ModuleCat.{u} R} (g : M ⟶ N) : F.obj M →ₗ[R] F.obj N where
  toFun := (F.map g).hom
  map_add' := map_add _
  map_smul' r x := by
    change (F.map g).hom ((F.map (r • 𝟙 M)).hom x) = (F.map (r • 𝟙 N)).hom ((F.map g).hom x)
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← F.map_comp,
      ← F.map_comp, Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

variable [∀ M, Small.{u} (F.obj M)]

/-- **An additive functor to abelian groups with small values, as a functor to `R`-modules.**
`M ↦ F(M)`, shrunk to `Type u`, with `r` acting through `F(r • 𝟙_M)`. -/
def moduleFunctorOfAdditive : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (Shrink.{u} (F.obj M))
  map {M N} g := ModuleCat.ofHom ((Shrink.linearEquiv R (F.obj N)).symm.toLinearMap ∘ₗ
    scalarLinearMap F g ∘ₗ (Shrink.linearEquiv R (F.obj M)).toLinearMap)
  map_id M := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (Shrink.linearEquiv R (F.obj M)).symm ((F.map (𝟙 M)).hom
      (Shrink.linearEquiv R (F.obj M) x)) = x
    rw [F.map_id]
    exact (Shrink.linearEquiv R (F.obj M)).symm_apply_apply x
  map_comp {M N P} g g' := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    change (Shrink.linearEquiv R (F.obj P)).symm ((F.map (g ≫ g')).hom
      (Shrink.linearEquiv R (F.obj M) x)) = (Shrink.linearEquiv R (F.obj P)).symm
        ((F.map g').hom ((Shrink.linearEquiv R (F.obj N))
          ((Shrink.linearEquiv R (F.obj N)).symm ((F.map g).hom
            (Shrink.linearEquiv R (F.obj M) x)))))
    rw [LinearEquiv.apply_symm_apply, F.map_comp]
    rfl

/-- The identification of a value of `moduleFunctorOfAdditive F` with the value of `F`. -/
def moduleFunctorOfAdditiveObjEquiv (M : ModuleCat.{u} R) :
    (moduleFunctorOfAdditive F).obj M ≃ₗ[R] F.obj M :=
  Shrink.linearEquiv R (F.obj M)

/-- Read through `moduleFunctorOfAdditiveObjEquiv`, `(moduleFunctorOfAdditive F).map g` is
`F(g)`. -/
theorem moduleFunctorOfAdditive_map_apply {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (x : (moduleFunctorOfAdditive F).obj M) :
    moduleFunctorOfAdditiveObjEquiv F N ((moduleFunctorOfAdditive F).map g x) =
      (F.map g).hom (moduleFunctorOfAdditiveObjEquiv F M x) :=
  (Shrink.linearEquiv R (F.obj N)).apply_symm_apply _

/-- `moduleFunctorOfAdditive F` is additive. -/
instance moduleFunctorOfAdditive_additive : (moduleFunctorOfAdditive F).Additive where
  map_add {M N g g'} := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine (moduleFunctorOfAdditiveObjEquiv F N).injective ?_
    change moduleFunctorOfAdditiveObjEquiv F N ((moduleFunctorOfAdditive F).map (g + g') x) =
      moduleFunctorOfAdditiveObjEquiv F N ((moduleFunctorOfAdditive F).map g x +
        (moduleFunctorOfAdditive F).map g' x)
    rw [map_add, moduleFunctorOfAdditive_map_apply, moduleFunctorOfAdditive_map_apply,
      moduleFunctorOfAdditive_map_apply, F.map_add]
    rfl

/-- `moduleFunctorOfAdditive F` is `R`-linear. -/
instance moduleFunctorOfAdditive_linear : (moduleFunctorOfAdditive F).Linear R where
  map_smul {M N} g r := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    refine (moduleFunctorOfAdditiveObjEquiv F N).injective ?_
    change moduleFunctorOfAdditiveObjEquiv F N ((moduleFunctorOfAdditive F).map (r • g) x) =
      moduleFunctorOfAdditiveObjEquiv F N (r • (moduleFunctorOfAdditive F).map g x)
    rw [map_smul, moduleFunctorOfAdditive_map_apply, moduleFunctorOfAdditive_map_apply,
      scalarModule_smul, ← ConcreteCategory.comp_apply, ← F.map_comp, Linear.comp_smul,
      Category.comp_id]

/-- The action of `r` on `moduleFunctorOfAdditive F` is `moduleFunctorOfAdditive F` applied to
`r • 𝟙`. -/
theorem moduleFunctorOfAdditive_smul (M : ModuleCat.{u} R) (r : R)
    (x : (moduleFunctorOfAdditive F).obj M) :
    r • x = (moduleFunctorOfAdditive F).map (r • 𝟙 M) x := by
  refine (moduleFunctorOfAdditiveObjEquiv F M).injective ?_
  rw [map_smul, moduleFunctorOfAdditive_map_apply, scalarModule_smul]

end ModuleFunctor

end Deformation.Artin

namespace AlgebraicGeometry.Space

open Deformation.ToposThickening Deformation.ToposThickening.RingedToposExtensionProblem
open Stacks.Cohomology.SiteModules

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The `Type u` model of the small étale ringed topos of `X`**, as the transport of
`(X_étale, 𝒪_X)` along the comparison with the small model of its site: a
`RingedTopos.{u, u, u}`. -/
abbrev modelTopos (X : AlgebraicSpaces B S hS) : RingedTopos.{u, u, u} :=
  (smallEtaleRingedTopos B S hS X).ofSiteEquivalence (smallEtaleModelTopology B S hS X.1)
    (smallEtaleModelEquiv B S hS X)

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- **The morphism of small étale ringed topoi of `f`, transported to the model of the site of
`X`**: the composite of the equivalence `Sh(model) ≅ Sh(X_étale)` with `f_small`. Its cotangent
complex is `L_{X/Y}` formed on the model. -/
abbrev modelRingedToposHom : RingedToposHom (modelTopos X) (smallEtaleRingedTopos B S hS Y) :=
  siteTransportHom (X := smallEtaleRingedTopos B S hS X) (B := smallEtaleRingedTopos B S hS Y)
    (smallEtaleModelTopology B S hS X.1) (smallEtaleModelEquiv B S hS X)
    (smallEtaleRingedToposHom B S hS f)

/-- The sheaves of `𝒪_X`-modules on the model, the coefficients of `L_{X/Y}`. -/
abbrev modelModules (X : AlgebraicSpaces B S hS) :=
  Sheaf.targetModules.{u, u, u} (modelTopos X).J (modelTopos X).O

/-- The category of sheaves of `𝒪_X`-modules on the model is locally `u`-small. -/
instance locallySmall_modelModules (X : AlgebraicSpaces B S hS) :
    LocallySmall.{u} (modelModules X) :=
  locallySmall_self _

/-- The category of sheaves of `𝒪_X`-modules on the model has enough injectives. -/
instance enoughInjectives_modelModules (X : AlgebraicSpaces B S hS) :
    EnoughInjectives (modelModules X) :=
  moduleSheavesEnoughInjectives.{u, u, u, u} _

/-- **The canonical map `L_{X/Y} ⟶ NL_{X/Y}`** on the model, Tag 08US for the structure map of
`modelRingedToposHom f`. Precomposition with it is
`AlgebraicGeometry.RingedToposHom.naiveExtOneEquiv`, `Ext¹(NL_{X/Y}, G) ≃+ Ext¹(L_{X/Y}, G)`. -/
abbrev modelCotangentToNaive :
    (modelRingedToposHom f).cotangentComplex ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} (modelTopos X).J _ (modelTopos X).O
        (modelRingedToposHom f).fSharpInverseImage :=
  (modelRingedToposHom f).canonicalNaiveComparison

variable {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)

/-- **The module `𝒪_X ⊗_R M` on the model** (Tag 0D3F), for the base-ring datum `φ`. -/
abbrev modelTensorFunctor : ModuleCat.{u} R ⥤ modelModules X :=
  baseRingTensorFunctor.{u, u, u, u, u} φ

/-- `M ↦ 𝒪_X ⊗_R M` is an additive functor on the model. -/
instance additive_modelTensorFunctor : (modelTensorFunctor φ).Additive := by
  have : (modelTensorFunctor φ).IsLeftAdjoint :=
    (baseRingTensorAdjunction.{u, u, u, u, u} φ).isLeftAdjoint
  have : PreservesBinaryBiproducts (modelTensorFunctor φ) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

variable [HasDerivedCategory.{t} (modelModules X)]

/-- `M ↦ Ext^i(L_{X/Y}, 𝒪_X ⊗_R M)`, as a functor to abelian groups: morphisms
`L_{X/Y} ⟶ (𝒪_X ⊗_R M)[0]⟦i⟧` in the derived category of the model. -/
abbrev cotangentExtAddFunctor (i : ℤ) : ModuleCat.{u} R ⥤ AddCommGrpCat.{t} :=
  modelTensorFunctor φ ⋙ DerivedCategory.singleFunctor _ 0 ⋙ shiftFunctor _ i ⋙
    preadditiveCoyoneda.obj (op (modelRingedToposHom f).cotangentComplexDerived)

/-- The group `Ext^i(L_{X/Y}, 𝒪_X ⊗_R M)` on the model is `u`-small. -/
instance small_cotangentExtAddFunctor_obj (i : ℤ) (M : ModuleCat.{u} R) :
    Small.{u} ((cotangentExtAddFunctor f φ i).obj M) :=
  Deformation.Artin.small_shiftedHom_singleFunctor.{u} _ _ i

/-- **`T^i(M) = Ext^i_{𝒪_X}(L_{X/Y}, 𝒪_X ⊗_R M)`** of [Stacks Project, Remark 0D1P], as a functor
`ModuleCat R ⥤ ModuleCat R`: `r` acts through `𝒪_X ⊗ (r • 𝟙_M)`. -/
abbrev cotangentExtFunctor (i : ℤ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  Deformation.Artin.moduleFunctorOfAdditive (cotangentExtAddFunctor f φ i)

/-- `T¹(M) = Ext¹_{𝒪_X}(L_{X/Y}, 𝒪_X ⊗_R M)`, the tangent functor of Remark 0D1P. -/
abbrev cotangentExtOne : ModuleCat.{u} R ⥤ ModuleCat.{u} R := cotangentExtFunctor f φ 1

/-- `T²(M) = Ext²_{𝒪_X}(L_{X/Y}, 𝒪_X ⊗_R M)`, the obstruction functor of Remark 0D1P. -/
abbrev cotangentExtTwo : ModuleCat.{u} R ⥤ ModuleCat.{u} R := cotangentExtFunctor f φ 2

attribute [local instance] Deformation.Artin.scalarModule in
/-- The identification of `T^i(M)` with the `Ext` group it shrinks. -/
def cotangentExtFunctorObjEquiv (i : ℤ) (M : ModuleCat.{u} R) :
    (cotangentExtFunctor f φ i).obj M ≃+
      ShiftedHom (modelRingedToposHom f).cotangentComplexDerived
        ((DerivedCategory.singleFunctor _ 0).obj ((modelTensorFunctor φ).obj M)) i :=
  (Deformation.Artin.moduleFunctorOfAdditiveObjEquiv _ M).toAddEquiv

/-- `T^i` of a map `g`, read on `Ext` groups, is postcomposition with `(𝒪_X ⊗ g)[0]⟦i⟧`. -/
theorem cotangentExtFunctorObjEquiv_map (i : ℤ) {M N : ModuleCat.{u} R} (g : M ⟶ N)
    (x : (cotangentExtFunctor f φ i).obj M) :
    cotangentExtFunctorObjEquiv f φ i N ((cotangentExtFunctor f φ i).map g x) =
      cotangentExtFunctorObjEquiv f φ i M x ≫
        ((DerivedCategory.singleFunctor _ 0).map ((modelTensorFunctor φ).map g))⟦i⟧' :=
  Deformation.Artin.moduleFunctorOfAdditive_map_apply _ g x

/-- `r : R` acts on `T^i(M)` by postcomposition with `(𝒪_X ⊗ (r • 𝟙_M))[0]⟦i⟧`. -/
theorem cotangentExtFunctorObjEquiv_smul (i : ℤ) (M : ModuleCat.{u} R) (r : R)
    (x : (cotangentExtFunctor f φ i).obj M) :
    cotangentExtFunctorObjEquiv f φ i M (r • x) =
      cotangentExtFunctorObjEquiv f φ i M x ≫
        ((DerivedCategory.singleFunctor _ 0).map ((modelTensorFunctor φ).map (r • 𝟙 M)))⟦i⟧' := by
  rw [Deformation.Artin.moduleFunctorOfAdditive_smul]
  exact cotangentExtFunctorObjEquiv_map f φ i (r • 𝟙 M) x

/-! ### The connecting map -/

section Connecting

variable {Sq : ShortComplex (ModuleCat.{u} R)}

/-- The endomorphism `𝒪_X ⊗ (r • 𝟙)` of the short complex `𝒪_X ⊗ Sq`. -/
def tensorSmulShortComplexHom (Sq : ShortComplex (ModuleCat.{u} R)) (r : R) :
    Sq.map (modelTensorFunctor φ) ⟶ Sq.map (modelTensorFunctor φ) where
  τ₁ := (modelTensorFunctor φ).map (r • 𝟙 Sq.X₁)
  τ₂ := (modelTensorFunctor φ).map (r • 𝟙 Sq.X₂)
  τ₃ := (modelTensorFunctor φ).map (r • 𝟙 Sq.X₃)
  comm₁₂ := by
    dsimp
    rw [← Functor.map_comp, ← Functor.map_comp, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]
  comm₂₃ := by
    dsimp
    rw [← Functor.map_comp, ← Functor.map_comp, Linear.smul_comp, Linear.comp_smul,
      Category.id_comp, Category.comp_id]

/-- The connecting map commutes with the action of `r`, read on `Ext` groups. -/
theorem comp_singleδ_smul (h : (Sq.map (modelTensorFunctor φ)).ShortExact) (r : R)
    (ξ : ShiftedHom (modelRingedToposHom f).cotangentComplexDerived
      ((DerivedCategory.singleFunctor _ 0).obj ((modelTensorFunctor φ).obj Sq.X₃)) 1) :
    ShiftedHom.comp (a := (1 : ℤ)) (ξ ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((modelTensorFunctor φ).map (r • 𝟙 Sq.X₃)))⟦(1 : ℤ)⟧') h.singleδ
          (show (1 : ℤ) + 1 = 2 by norm_num) =
      ξ.comp h.singleδ (show (1 : ℤ) + 1 = 2 by norm_num) ≫
        ((DerivedCategory.singleFunctor _ 0).map
          ((modelTensorFunctor φ).map (r • 𝟙 Sq.X₁)))⟦(2 : ℤ)⟧' := by
  have h₃ : (DerivedCategory.singleFunctor _ 0).map ((modelTensorFunctor φ).map (r • 𝟙 Sq.X₃)) ≫
      h.singleδ = h.singleδ ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((modelTensorFunctor φ).map (r • 𝟙 Sq.X₁)))⟦(1 : ℤ)⟧' :=
    (ShortComplex.ShortExact.singleTriangle.map h h (tensorSmulShortComplexHom φ Sq r)).comm₃.symm
  simp only [ShiftedHom.comp, Category.assoc]
  rw [← Functor.map_comp_assoc, h₃, Functor.map_comp, Category.assoc]
  congr 2
  exact (shiftFunctorAdd' (DerivedCategory (modelModules X)) (1 : ℤ) 1 2
    (by norm_num)).inv.naturality _

/-- **The connecting map `T¹(M₃) ⟶ T²(M₁)`** of a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` whose image `0 → 𝒪_X ⊗ M₁ → 𝒪_X ⊗ M₂ → 𝒪_X ⊗ M₃ → 0` is short exact:
`ξ ↦ ξ.comp δ`, with `δ = ShortComplex.ShortExact.singleδ` the connecting morphism
`(𝒪_X ⊗ M₃)[0] ⟶ (𝒪_X ⊗ M₁)[0]⟦1⟧` of Mathlib. -/
def cotangentExtConnecting (h : (Sq.map (modelTensorFunctor φ)).ShortExact) :
    (cotangentExtOne f φ).obj Sq.X₃ ⟶ (cotangentExtTwo f φ).obj Sq.X₁ :=
  ModuleCat.ofHom (X := (cotangentExtOne f φ).obj Sq.X₃) (Y := (cotangentExtTwo f φ).obj Sq.X₁)
    { toFun x := (cotangentExtFunctorObjEquiv f φ 2 Sq.X₁).symm
        ((cotangentExtFunctorObjEquiv f φ 1 Sq.X₃ x).comp h.singleδ
          (show (1 : ℤ) + 1 = 2 by norm_num))
      map_add' x y := by
        rw [map_add, ShiftedHom.add_comp, map_add]
      map_smul' r x := by
        refine (cotangentExtFunctorObjEquiv f φ 2 Sq.X₁).injective ?_
        refine ((cotangentExtFunctorObjEquiv f φ 2 Sq.X₁).apply_symm_apply _).trans ?_
        refine Eq.trans ?_ (cotangentExtFunctorObjEquiv_smul f φ 2 Sq.X₁ r _).symm
        rw [AddEquiv.apply_symm_apply]
        refine (congrArg (fun ξ => ShiftedHom.comp ξ h.singleδ
          (show (1 : ℤ) + 1 = 2 by norm_num))
            (cotangentExtFunctorObjEquiv_smul f φ 1 Sq.X₃ r x)).trans ?_
        exact comp_singleδ_smul f φ h r _ }

/-- `cotangentExtConnecting`, read on `Ext` groups. -/
theorem cotangentExtFunctorObjEquiv_cotangentExtConnecting
    (h : (Sq.map (modelTensorFunctor φ)).ShortExact) (x : (cotangentExtOne f φ).obj Sq.X₃) :
    cotangentExtFunctorObjEquiv f φ 2 Sq.X₁ (cotangentExtConnecting f φ h x) =
      (cotangentExtFunctorObjEquiv f φ 1 Sq.X₃ x).comp h.singleδ
        (show (1 : ℤ) + 1 = 2 by norm_num) :=
  (cotangentExtFunctorObjEquiv f φ 2 Sq.X₁).apply_symm_apply _

end Connecting

/-! ### The flat case -/

section Flat

variable {T : BigFppfOver B S hS} (g : X ⟶ schemeSpace T) (hflat : IsFlat B S hS g.hom)
  (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))

omit [HasDerivedCategory.{t} (modelModules X)] in
include hflat hT in
/-- **For flat `g : X ⟶ Spec(R)`, `M ↦ 𝒪_X ⊗_R M` is exact** on the model: it is a left adjoint,
hence right exact, and it carries injections to monomorphisms (Tag 0D3F). -/
theorem shortExact_map_modelTensorFunctor_of_isFlat
    {Sq : ShortComplex (ModuleCat.{u} (baseRing B S hS T))} (hSq : Sq.ShortExact) :
    (Sq.map (modelTensorFunctor (baseRingHomOfMap g))).ShortExact := by
  have : (modelTensorFunctor (baseRingHomOfMap g)).IsLeftAdjoint :=
    (baseRingTensorAdjunction.{u, u, u, u, u} (baseRingHomOfMap g)).isLeftAdjoint
  have := hSq.mono_f
  have := hSq.epi_g
  have : Mono (Sq.map (modelTensorFunctor (baseRingHomOfMap g))).f :=
    mono_baseRingTensorFunctor_map (baseRingHomOfMap g)
      (exists_ofArrows_mem_modelTopology_flat g hflat hT) Sq.f
      ((ModuleCat.mono_iff_injective Sq.f).1 inferInstance)
  have : Epi (Sq.map (modelTensorFunctor (baseRingHomOfMap g))).g :=
    inferInstanceAs (Epi ((modelTensorFunctor (baseRingHomOfMap g)).map Sq.g))
  exact ShortComplex.ShortExact.mk' (hSq.exact.map_of_epi_of_preservesCokernel _ inferInstance
    inferInstance) inferInstance inferInstance

include hflat hT in
/-- **The connecting map `T¹(M₃) ⟶ T²(M₁)` of a flat `g : X ⟶ Spec(R)`**, for every short exact
sequence `0 → M₁ → M₂ → M₃ → 0` of `R`-modules: `cotangentExtConnecting` of the short exact
sequence `0 → 𝒪_X ⊗ M₁ → 𝒪_X ⊗ M₂ → 𝒪_X ⊗ M₃ → 0`. This is the field `δ` of
`Deformation.Artin.FunctorDeformationTheory`. -/
def cotangentExtConnectingOfIsFlat {Sq : ShortComplex (ModuleCat.{u} (baseRing B S hS T))}
    (hSq : Sq.ShortExact) :
    (cotangentExtOne g (baseRingHomOfMap g)).obj Sq.X₃ ⟶
      (cotangentExtTwo g (baseRingHomOfMap g)).obj Sq.X₁ :=
  cotangentExtConnecting g (baseRingHomOfMap g)
    (shortExact_map_modelTensorFunctor_of_isFlat g hflat hT hSq)

end Flat

end AlgebraicGeometry.Space

end
