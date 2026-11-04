module

public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedModulePullbackBaseChangeEquivalence
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangePathComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeUnderived

/-!
# Affine base change for the derived associated-module functor of a representable space

Let `g : U' ⟶ U` be a morphism of the big fppf site over `S` whose source and target have affine
underlying schemes, with rings of global functions `R = Γ(U, 𝒪)` and `R' = Γ(U', 𝒪)` and induced
ring map `φ : R ⟶ R'`. Write `Φ_R : D(R) ⥤ D(𝒪_{yoneda.obj U})` for the derived associated-module
functor of `StacksFrontier/AlgebraicGeometry/Spaces/AffineQuasicoherentDerivedEquivalence.lean` and
`Lg^*` for the derived pullback along the morphism of algebraic spaces `yoneda.map g`. This file
proves

`Lg^*(Φ_R K) ≅ Φ_{R'}(K ⊗^L_R R')`

naturally in `K ∈ D(R)`, with no flatness hypothesis on `g`, where `- ⊗^L_R R'` is the chosen
unbounded derived extension of scalars
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso`: the underived statement
  `g^*(M^~) ≅ (R' ⊗_R M)^~`, naturally in the `R`-module `M`.
* `AlgebraicGeometry.Space.representedAffineDerivedBaseChangeHom`: the base change morphism
  `Lg^* ∘ Φ_R ⟶ Φ_{R'} ∘ (- ⊗^L_R R')`.
* `AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso`: the same, as an isomorphism.

## Main results

* `AlgebraicGeometry.Space.isIso_representedAffineDerivedBaseChangeHom`: the base change
  morphism is invertible.
* `AlgebraicGeometry.Space.isIso_of_isIso_app_singleFunctor_of_adjunction`: a morphism between
  two left adjoints out of `D(R)` is invertible as soon as it is invertible at every `R[q]`.

## Implementation notes

The morphism is produced by the universal property of `Φ_{R'} ∘ (- ⊗^L_R R')` as a left derived
functor of degreewise extension of scalars followed by the associated module (derived extension
of scalars is absolute,
`CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp`): on a complex
`K`, it is the comparison `Lg^*(K^~) ⟶ g^*(K^~)` of Stacks 06YY followed by the underived
isomorphism.

It is invertible at `R[q]`: there `(R[q])^~ = 𝒪[q]` is a bounded above complex of flat modules,
so the comparison of Stacks 06YY is invertible, and `R[q]` is a bounded above complex of
projectives, so derived extension of scalars is computed termwise. Both functors are left
adjoints, `Lg^* ∘ Φ_R ⊣ RΓ_R ∘ Rg_*` and `Φ_{R'} ∘ (- ⊗^L_R R') ⊣ res ∘ RΓ_{R'}`, so the
conjugate morphism of right adjoints is bijective on morphisms out of every `R[q]`, hence
invertible because `R[q]` corepresents `H^q` on `D(R)`; this needs neither compact generation
nor a commutation with shifts.

## References

* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

/-! ### A morphism of left adjoints out of `D(R)` invertible on the `R[q]` -/

/-- The free module of rank one over `R` is projective. -/
private theorem projective_of_self {R : Type u} [CommRing R] : Projective (ModuleCat.of R R) :=
  ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} _)

section General

variable {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- A component of a natural transformation at an object isomorphic to one where it is invertible
is invertible. -/
theorem isIso_app_of_iso_of_isIso_app {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (τ : F ⟶ G) {X Y : C} (e : X ≅ Y) [IsIso (τ.app Y)] : IsIso (τ.app X) := by
  have : τ.app X = F.map e.hom ≫ τ.app Y ≫ G.map e.inv := by
    rw [← Category.assoc, τ.naturality e.hom, Category.assoc, ← Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this]
  infer_instance

/-- A morphism `f : M ⟶ N` in `D(R)` is invertible as soon as postcomposition with `f` is
bijective on morphisms out of every `R[q]`: `R[q]` corepresents `H^q` (`R` is projective). -/
theorem isIso_of_bijective_comp_singleFunctor {M N : DerivedCategory (ModuleCat.{u} R)}
    (f : M ⟶ N) (hf : ∀ q : ℤ, Function.Bijective
      (fun g : (DerivedCategory.singleFunctor _ q).obj (ModuleCat.of R R) ⟶ M => g ≫ f)) :
    IsIso f := by
  have : Projective (ModuleCat.of R R) := projective_of_self
  rw [DerivedCategory.isIso_iff]
  intro q
  refine isIso_of_bijective_comp_moduleCat _ ?_
  have h₁ := DerivedCategory.bijective_homologyFromSingle_of_projective (ModuleCat.of R R) M q
  have h₂ := DerivedCategory.bijective_homologyFromSingle_of_projective (ModuleCat.of R R) N q
  have hk : (DerivedCategory.homologyFromSingle (ModuleCat.of R R) _ q) ∘
      (fun g : (DerivedCategory.singleFunctor _ q).obj (ModuleCat.of R R) ⟶ M => g ≫ f) =
      (fun g => g ≫ (DerivedCategory.homologyFunctor _ q).map f) ∘
        (DerivedCategory.homologyFromSingle (ModuleCat.of R R) M q) := by
    funext g
    exact DerivedCategory.homologyFromSingle_comp (ModuleCat.of R R) M q g f
  have := h₂.comp (hf q)
  rw [hk] at this
  exact (Function.Bijective.of_comp_iff _ h₁).mp this

/-- **A morphism of left adjoints out of `D(R)` is invertible as soon as it is invertible at every
`R[q]`.**  Its conjugate morphism of right adjoints is then bijective on morphisms out of every
`R[q]`, hence invertible since `R[q]` corepresents `H^q`. -/
theorem isIso_of_isIso_app_singleFunctor_of_adjunction {T : Type*} [Category T]
    {L₁ L₂ : DerivedCategory (ModuleCat.{u} R) ⥤ T} {R₁ R₂ : T ⥤ DerivedCategory (ModuleCat.{u} R)}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (τ : L₁ ⟶ L₂)
    (hτ : ∀ q : ℤ, IsIso (τ.app ((DerivedCategory.singleFunctor _ q).obj (ModuleCat.of R R)))) :
    IsIso τ := by
  suffices IsIso (conjugateEquiv adj₂ adj₁ τ) from conjugateEquiv_of_iso adj₂ adj₁ τ
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun E => ?_
  refine isIso_of_bijective_comp_singleFunctor _ fun q => ?_
  set X := (DerivedCategory.singleFunctor (ModuleCat.{u} R) q).obj (ModuleCat.of R R)
  have hk : (fun g : X ⟶ R₂.obj E => g ≫ (conjugateEquiv adj₂ adj₁ τ).app E) =
      (adj₁.homEquiv X E) ∘ (fun h : L₂.obj X ⟶ E => τ.app X ≫ h) ∘ (adj₂.homEquiv X E).symm := by
    funext g
    obtain ⟨h, rfl⟩ := (adj₂.homEquiv X E).surjective g
    rw [Function.comp_apply, Function.comp_apply, Equiv.symm_apply_apply]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    rw [Category.assoc, (conjugateEquiv adj₂ adj₁ τ).naturality h, ← Category.assoc,
      unit_conjugateEquiv adj₂ adj₁ τ X, Category.assoc]
  rw [hk]
  have := hτ q
  exact (adj₁.homEquiv X E).bijective.comp
    ((bijective_iso_comp (asIso (τ.app X))).comp (adj₂.homEquiv X E).symm.bijective)

end General

/-! ### Normalizing an isomorphism `G ∘ Φ ≅ Φ' ∘ (B ⊗_A -)` at the unit -/

section Normalization

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')

/-- An endomorphism of the free module `A'` is multiplication by its value at `1`. -/
private theorem hom_apply_eq_mul_hom_one (f : ModuleCat.of A' A' ⟶ ModuleCat.of A' A') (x : A') :
    f x = x * f 1 := by
  conv_lhs => rw [← mul_one x]
  exact f.hom.map_smul x 1

/-- Multiplication by a unit of `A'`, as an automorphism of extension of scalars `A' ⊗_A -`. -/
def extendScalarsUnitIso (c : A'ˣ) : ModuleCat.extendScalars.{u, u, u} φ ≅ ModuleCat.extendScalars φ :=
  NatIso.ofComponents (fun M =>
    { hom := (c : A') • 𝟙 _
      inv := ((c⁻¹ : A'ˣ) : A') • 𝟙 _
      hom_inv_id := by rw [Linear.smul_comp, Category.id_comp, smul_smul, Units.mul_inv, one_smul]
      inv_hom_id := by rw [Linear.smul_comp, Category.id_comp, smul_smul, Units.inv_mul, one_smul] })
    (fun f => by
      dsimp only
      rw [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp])

theorem extendScalarsUnitIso_hom_app (c : A'ˣ) (M : ModuleCat.{u} A) :
    (extendScalarsUnitIso φ c).hom.app M = (c : A') • 𝟙 _ :=
  rfl

variable {D C : Type*} [Category* C] [Category* D] {Φ : ModuleCat.{u} A ⥤ C}
  {Φ' : ModuleCat.{u} A' ⥤ D} (hΦ' : Φ'.FullyFaithful) {G : C ⥤ D}
  (ρ : Φ ⋙ G ≅ ModuleCat.extendScalars.{u, u, u} φ ⋙ Φ')
  (θ : G.obj (Φ.obj (ModuleCat.of A A)) ≅ Φ'.obj (ModuleCat.of A' A'))

/-- The automorphism of `A'` by which `ρ` at `A` differs from the trivialization `θ`. -/
def normalizationIso : ModuleCat.of A' A' ≅ ModuleCat.of A' A' :=
  hΦ'.preimageIso (θ.symm ≪≫ ρ.app (ModuleCat.of A A) ≪≫
    Φ'.mapIso (ModuleCat.ExtendScalars.objSelfIso φ))

theorem normalizationIso_hom_apply (x : A') :
    (normalizationIso φ hΦ' ρ θ).hom x = x * (normalizationIso φ hΦ' ρ θ).hom 1 :=
  hom_apply_eq_mul_hom_one _ x

theorem normalizationIso_inv_apply (x : A') :
    (normalizationIso φ hΦ' ρ θ).inv x = x * (normalizationIso φ hΦ' ρ θ).inv 1 :=
  hom_apply_eq_mul_hom_one _ x

/-- The unit of `A'` by which `ρ` at `A` differs from the trivialization `θ`. -/
def normalizationUnit : A'ˣ where
  val := (normalizationIso φ hΦ' ρ θ).hom 1
  inv := (normalizationIso φ hΦ' ρ θ).inv 1
  val_inv := by
    rw [mul_comm, ← normalizationIso_hom_apply]
    exact congrArg (fun g => g.hom 1) (normalizationIso φ hΦ' ρ θ).inv_hom_id
  inv_val := by
    rw [mul_comm, ← normalizationIso_inv_apply]
    exact congrArg (fun g => g.hom 1) (normalizationIso φ hΦ' ρ θ).hom_inv_id

theorem normalizationIso_hom :
    (normalizationIso φ hΦ' ρ θ).hom = ((normalizationUnit φ hΦ' ρ θ : A'ˣ) : A') • 𝟙 _ := by
  ext
  change _ = ((normalizationUnit φ hΦ' ρ θ : A'ˣ) : A') • (1 : A')
  rw [smul_eq_mul, mul_one]
  rfl

/-- **The normalization of `ρ` at the unit**: `ρ` followed by multiplication by the inverse of
`normalizationUnit`, so that at `A` it becomes `θ` through `A' ⊗_A A = A'`. -/
def normalizedIso : Φ ⋙ G ≅ ModuleCat.extendScalars.{u, u, u} φ ⋙ Φ' :=
  ρ ≪≫ Functor.isoWhiskerRight (extendScalarsUnitIso φ (normalizationUnit φ hΦ' ρ θ)⁻¹) Φ'

/-- At `A`, the normalized isomorphism is the trivialization `θ`. -/
theorem normalizedIso_hom_app_self :
    (normalizedIso φ hΦ' ρ θ).hom.app (ModuleCat.of A A) ≫
        Φ'.map (ModuleCat.ExtendScalars.objSelfIso φ).hom = θ.hom := by
  have h₁ : ρ.hom.app (ModuleCat.of A A) ≫ Φ'.map (ModuleCat.ExtendScalars.objSelfIso φ).hom =
      θ.hom ≫ Φ'.map (normalizationIso φ hΦ' ρ θ).hom := by
    rw [normalizationIso, Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage]
    simp
  have h₂ : ((((normalizationUnit φ hΦ' ρ θ)⁻¹ : A'ˣ) : A') • 𝟙 _) ≫
      (ModuleCat.ExtendScalars.objSelfIso φ).hom = (ModuleCat.ExtendScalars.objSelfIso φ).hom ≫
        ((((normalizationUnit φ hΦ' ρ θ)⁻¹ : A'ˣ) : A') • 𝟙 _) := by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have h₃ : (normalizedIso φ hΦ' ρ θ).hom.app (ModuleCat.of A A) =
      ρ.hom.app (ModuleCat.of A A) ≫
        Φ'.map ((((normalizationUnit φ hΦ' ρ θ)⁻¹ : A'ˣ) : A') • 𝟙 _) := rfl
  rw [h₃, Category.assoc, ← Φ'.map_comp, h₂, Φ'.map_comp, ← Category.assoc, h₁, Category.assoc,
    ← Φ'.map_comp, normalizationIso_hom, Linear.smul_comp, Category.id_comp, smul_smul,
    Units.mul_inv, one_smul, Φ'.map_id, Category.comp_id]

end Normalization

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- The map of rings of global functions `Γ(U, 𝒪) ⟶ Γ(U', 𝒪)` induced by `g : U' ⟶ U`. -/
abbrev representedAffineCommRingCatHom :
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) ⟶ Γ((BigFppfOver.toScheme B S hS).obj U', ⊤) :=
  Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map g)

/-- The trivialization of `g^*(R^~)`: `g^*(R^~) ≅ g^*𝒪_U ≅ 𝒪_{U'} ≅ R'^~`, by the associated
module of the ring and the identification of the inverse image of the structure sheaf
(Stacks 03LU). -/
def representedAffinePullbackUnitIso :
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS _)
        (Y := smallEtaleRingedTopos B S hS _)
        (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).obj
      ((representedAffineAssociated B S hS U).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) ≅
      (representedAffineAssociated B S hS U').obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) :=
  (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).mapIso
      (representedAffineAssociatedObjUnitIso B S hS U) ≪≫
    (Stacks.Sheaves.RingedToposModules.pullbackModulesObjUnitIso
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).symm ≪≫
    (representedAffineAssociatedObjUnitIso B S hS U').symm

/-- **The pullback of an associated module along a morphism of affine representables.**  For
`g : U' ⟶ U` with affine underlying schemes and `φ : R ⟶ R'` the map of rings of global
functions, `g^*(M^~) ≅ (R' ⊗_R M)^~`, naturally in the `R`-module `M`.  It is normalized so that
at `M = R` it is `AlgebraicGeometry.Space.representedAffinePullbackUnitIso` through
`R' ⊗_R R = R'` (`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_hom_app_self`). -/
def representedAffineAssociatedPullbackIso :
    representedAffineAssociated B S hS U ⋙
        Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom ≅
      ModuleCat.extendScalars (representedAffineCommRingCatHom B S hS g).hom ⋙
        representedAffineAssociated B S hS U' :=
  normalizedIso (representedAffineCommRingCatHom B S hS g).hom
    (representedAffineAssociatedFullyFaithful B S hS U') (  Functor.isoWhiskerLeft (representedAffineAssociated B S hS U)
      (pullbackModulesIsoModulePullback B S hS (representedSpaceMap B S hS g)) ≪≫
    (Functor.associator (Stacks.AlgebraicGeometry.AffineTilde.tildeOf _)
      (_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⋙
        (representedSmallEtaleModuleEquivalence B S hS U).functor) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (representedSmallEtaleModuleEquivalencePullbackIso B S hS g) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (_root_.AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso
        (associatedBigEtaleSite B) g.left).symm _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Stacks.AlgebraicGeometry.AffineTilde.tildeOfPullbackIso
      ((BigFppfOver.toScheme B S hS).map g)) _ ≪≫
    Functor.associator _ _ _)
    (representedAffinePullbackUnitIso B S hS g)

/-- At `M = R`, the pullback isomorphism is the trivialization
`AlgebraicGeometry.Space.representedAffinePullbackUnitIso` through `R' ⊗_R R = R'`. -/
theorem representedAffineAssociatedPullbackIso_hom_app_self :
    (representedAffineAssociatedPullbackIso B S hS g).hom.app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≫
      (representedAffineAssociated B S hS U').map
        (ModuleCat.ExtendScalars.objSelfIso (representedAffineCommRingCatHom B S hS g).hom).hom =
      (representedAffinePullbackUnitIso B S hS g).hom :=
  normalizedIso_hom_app_self _ _ _ _

attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
  enoughInjectives_modules_ringUniverse isGrothendieckAbelian_modules_ringUniverse

/-- Extension of scalars is additive, being a left adjoint. -/
local instance additive_extendScalars_representedAffineRingHom :
    (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom).Additive :=
  (ModuleCat.extendRestrictScalarsAdj (representedAffineCommRingCatHom B S hS g).hom).left_adjoint_additive

/-- The associated-module functor is additive, at the spelling used below. -/
local instance additive_representedAffineAssociated' (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    (representedAffineAssociated B S hS V).Additive :=
  additive_representedAffineAssociated B S hS V

/-- Pullback of modules along `g` is additive, at the spelling used below. -/
local instance additive_pullbackModules_representedSpaceMap :
    (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).Additive :=
  pullbackModules_smallEtale_additive _

/-- Extension of scalars followed by the associated module is additive. -/
local instance additive_extendScalars_comp_representedAffineAssociated :
    (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom ⋙
      representedAffineAssociated B S hS U').Additive :=
  inferInstance

/-- The chosen total derived extension of scalars `- ⊗^L_R R'` along the map of rings of global
functions. -/
abbrev representedAffineDerivedExtension :=
  CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (representedAffineCommRingCatHom B S hS g).hom

/-- The associated module of a complex of `Γ(V, 𝒪)`-modules, degreewise, in the homotopy
category. -/
abbrev representedAffineHomotopyAssociated (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ℤ ⥤
      HomotopyCategory (Modules.{u, u} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V))
        (ComplexShape.up ℤ) :=
  (representedAffineAssociated B S hS V).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomotopyCategory.quotient _ _

/-- `Φ_R` on a localized complex is the localization of the degreewise associated module. -/
def representedAffineDerivedAssociatedFactors (V : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] :
    DerivedCategory.Q ⋙ representedAffineDerivedAssociated B S hS V ≅
      representedAffineHomotopyAssociated B S hS V ⋙ DerivedCategory.Qh :=
  (representedAffineAssociated B S hS V).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso _).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Degreewise pullback of degreewise associated modules is the degreewise associated module of
the degreewise extension of scalars, on cochain complexes. -/
def representedAffineComplexPullbackIso :
    (representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS g)).toModulesHom).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (representedAffineAssociated B S hS U').mapHomologicalComplex (ComplexShape.up ℤ) :=
  @Functor.mapHomologicalComplexCompIso _ _ _ _ _ _ _ _ _ _ _ _ _
      (representedAffineAssociatedPullbackIso B S hS g) _
      (pullbackModules_smallEtale_additive _)
      (additive_extendScalars_comp_representedAffineAssociated B S hS g)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (F := ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom)
      (G := representedAffineAssociated B S hS U') (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- Degreewise pullback of degreewise associated modules is the degreewise associated module of
the degreewise extension of scalars, in the homotopy category, by
`AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso`. -/
def representedAffineHomotopyPullbackIso :
    representedAffineHomotopyAssociated B S hS U ⋙
        smallEtalePullbackMapHomotopy B S hS (representedSpaceMap B S hS g) ≅
      (ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ representedAffineHomotopyAssociated B S hS U' :=
  NatIso.ofComponents (fun K => (HomotopyCategory.quotient
      (Modules.{u, u} B S hS (yoneda.obj U') (isAlgebraicSpace_yoneda B S hS U'))
      (ComplexShape.up ℤ)).mapIso ((representedAffineComplexPullbackIso B S hS g).app K))
    (fun {K L} φ => ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient
        (Modules.{u, u} B S hS (yoneda.obj U') (isAlgebraicSpace_yoneda B S hS U'))
        (ComplexShape.up ℤ)).map
        ((representedAffineComplexPullbackIso B S hS g).hom.naturality φ)).trans
        ((HomotopyCategory.quotient _ _).map_comp _ _)))

/-- The value of `AlgebraicGeometry.Space.representedAffineHomotopyPullbackIso` at a complex. -/
theorem representedAffineHomotopyPullbackIso_hom_app
    (K : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineHomotopyPullbackIso B S hS g).hom.app K =
      (HomotopyCategory.quotient
        (Modules.{u, u} B S hS (yoneda.obj U') (isAlgebraicSpace_yoneda B S hS U'))
        (ComplexShape.up ℤ)).map ((representedAffineComplexPullbackIso B S hS g).hom.app K) :=
  rfl

/-- The comparison on complexes out of which the base change morphism is built:
`Lg^*(Φ_R K) ⟶ g^*(K^~) ≅ (R' ⊗_R K)^~` for a complex `K` of `R`-modules. -/
def representedAffineBaseChangeComparison :
    DerivedCategory.Q ⋙ (representedAffineDerivedAssociated B S hS U ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)) ⟶
      ((ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        representedAffineDerivedAssociated B S hS U' :=
  Stacks.CategoryTheory.BaseChange.edgeComparison
    (representedAffineDerivedAssociatedFactors B S hS U)
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g))
    (smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g))
    (representedAffineHomotopyPullbackIso B S hS g).hom
    (representedAffineDerivedAssociatedFactors B S hS U')

/-- The value of `AlgebraicGeometry.Space.representedAffineBaseChangeComparison` at a complex. -/
theorem representedAffineBaseChangeComparison_app
    (K : CochainComplex (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ℤ) :
    (representedAffineBaseChangeComparison B S hS g).app K =
      (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).map
          ((representedAffineDerivedAssociatedFactors B S hS U).hom.app K) ≫
        (smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g)).app
          ((representedAffineHomotopyAssociated B S hS U).obj K) ≫
        DerivedCategory.Qh.map ((representedAffineHomotopyPullbackIso B S hS g).hom.app K) ≫
        (representedAffineDerivedAssociatedFactors B S hS U').inv.app
          (((ModuleCat.extendScalars.{u, u, u}
            (representedAffineCommRingCatHom B S hS g).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K) :=
  Stacks.CategoryTheory.BaseChange.edgeComparison_app _ _ _ _ _ K

/-- The derived extension of scalars followed by `Φ_{R'}` is a left derived functor of degreewise
extension of scalars followed by the associated module. -/
instance isLeftDerivedFunctor_representedAffineDerivedExtension_comp :
    ((representedAffineDerivedExtension B S hS g).functor ⋙
        representedAffineDerivedAssociated B S hS U').IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
          (representedAffineDerivedAssociated B S hS U'))
      (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) := by
  exact @CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{u, u, u}
    _ _ _ _ (representedAffineCommRingCatHom B S hS g).hom _ _
    (representedAffineDerivedExtension B S hS g).functor
    (representedAffineDerivedExtension B S hS g).comparison
    (representedAffineDerivedExtension B S hS g).isLeftDerived _ _
    (representedAffineDerivedAssociated B S hS U')

/-- **The base change morphism** `Lg^*(Φ_R K) ⟶ Φ_{R'}(K ⊗^L_R R')`. -/
def representedAffineDerivedBaseChangeHom :
    representedAffineDerivedAssociated B S hS U ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ⟶
      (representedAffineDerivedExtension B S hS g).functor ⋙
        representedAffineDerivedAssociated B S hS U' :=
  Functor.leftDerivedLift _ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
        (representedAffineDerivedAssociated B S hS U'))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
    (representedAffineBaseChangeComparison B S hS g)

/-- The terms of `Φ_R(R[q])`, degreewise, are flat: `R^~ ≅ 𝒪` and the others vanish. -/
theorem isFlat_representedAffineAssociated_mapHomologicalComplex_single_X (q i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u + 1, u, u}
      (O := (smallEtaleRingedTopos B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O)
      ((((representedAffineAssociated B S hS U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor _ q).obj
          (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
            Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))).X i) := by
  by_cases h : i = q
  · subst h
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso _
      ((representedAffineAssociated B S hS U).mapIso
        (HomologicalComplex.singleObjXSelf _ _ _) ≪≫
        representedAffineAssociatedObjUnitIso B S hS U).symm
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
        (Y := smallEtaleRingedSite B S hS _ (isAlgebraicSpace_yoneda B S hS U)))
  · exact isFlat_of_isZero B S hS
      (Functor.map_isZero (representedAffineAssociated B S hS U)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q _ i h))

/-- The base change morphism is invertible at `R[q]`, read on complexes. -/
theorem isIso_representedAffineDerivedBaseChangeHom_app_Q_single (q : ℤ) :
    IsIso ((representedAffineDerivedBaseChangeHom B S hS g).app
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ q).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))))) := by
  set R₀ := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  set X := (CochainComplex.singleFunctor (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    q).obj R₀
  have : Projective R₀ := projective_of_self
  have : ∀ i, Projective (X.X i) := fun i => by
    by_cases h : i = q
    · subst h
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm inferInstance
    · exact Projective.of_iso ((isZero_zero _).iso
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ h)) inferInstance
  have h₁ : IsIso (((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
        (representedAffineDerivedAssociated B S hS U')).app X) := by
    have := (representedAffineDerivedExtension B S hS g).comparison_isIso_of_projective X q
    dsimp
    infer_instance
  have hle : CochainComplex.IsStrictlyLE (((representedAffineAssociated B S hS U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj X) q :=
    (CochainComplex.isStrictlyLE_iff _ q).2 fun i hi =>
      Functor.map_isZero (representedAffineAssociated B S hS U)
        (CochainComplex.isZero_of_isStrictlyLE X q i hi)
  have h₂ : IsIso ((representedAffineBaseChangeComparison B S hS g).app X) := by
    have := @isIso_smallEtaleDerivedModulePullbackComparison_app B S hS _ _
      (representedSpaceMap B S hS g) _
      (@smallEtaleModuleKFlat_of_isStrictlyLE B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
        (((representedAffineAssociated B S hS U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj X) q hle
        (isFlat_representedAffineAssociated_mapHomologicalComplex_single_X B S hS q))
    rw [representedAffineBaseChangeComparison_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _
      ((Functor.mapIso (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g))
        ((representedAffineDerivedAssociatedFactors B S hS U).app X)).isIso_hom)
      (@IsIso.comp_isIso _ _ _ _ _ _ _ this (@IsIso.comp_isIso _ _ _ _ _ _ _
        ((Functor.mapIso DerivedCategory.Qh
          ((representedAffineHomotopyPullbackIso B S hS g).app X)).isIso_hom)
        ((representedAffineDerivedAssociatedFactors B S hS U').app _).isIso_inv))
  have hfac := Functor.leftDerived_fac_app _ ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (representedAffineDerivedExtension B S hS g).comparison
        (representedAffineDerivedAssociated B S hS U'))
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _
    (representedAffineBaseChangeComparison B S hS g) X
  exact @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ h₁ h₂ hfac

/-- **The base change morphism is an isomorphism.** -/
instance isIso_representedAffineDerivedBaseChangeHom :
    IsIso (representedAffineDerivedBaseChangeHom B S hS g) := by
  refine isIso_of_isIso_app_singleFunctor_of_adjunction
    ((representedAffineDerivedAdjunction B S hS U).comp
      (smallEtaleDerivedModuleAdjunction B S hS (representedSpaceMap B S hS g)))
    ((@CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u}
      _ _ _ _ (representedAffineCommRingCatHom B S hS g).hom _ _
      (representedAffineDerivedExtension B S hS g).functor
      (representedAffineDerivedExtension B S hS g).comparison
      (representedAffineDerivedExtension B S hS g).isLeftDerived).comp
      (representedAffineDerivedAdjunction B S hS U')) _ fun q => ?_
  set R₀ := ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
    Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
  exact @isIso_app_of_iso_of_isIso_app _ _ _ _ _ _ (representedAffineDerivedBaseChangeHom B S hS g)
    _ _ ((DerivedCategory.singleFunctorIsoCompQ
      (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) q).app R₀)
    (isIso_representedAffineDerivedBaseChangeHom_app_Q_single B S hS g q)

/-- **Affine base change for `Φ`.**  For a morphism `g : U' ⟶ U` of the big fppf site over `S`
whose source and target have affine underlying schemes, with `φ : R ⟶ R'` the induced map of
rings of global functions, the derived pullback along `g` of the associated module of
`K ∈ D(R)` is the associated module of `K ⊗^L_R R'`:
`Lg^*(Φ_R K) ≅ Φ_{R'}(K ⊗^L_R R')`, naturally in `K`. -/
def representedAffineDerivedBaseChangeIso :
    representedAffineDerivedAssociated B S hS U ⋙
        smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g) ≅
      (representedAffineDerivedExtension B S hS g).functor ⋙
        representedAffineDerivedAssociated B S hS U' :=
  asIso (representedAffineDerivedBaseChangeHom B S hS g)

end AlgebraicGeometry.Space
