module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsExtZero
public import StacksFrontier.CategoryTheory.Sites.Modules.ComplexesDGCategoryBaseRing

/-!
# The universal property of `Ω_{X/Y}` is linear over the global functions

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `F` an `𝒪_X`-module.  The `f♯`-derivations
of `𝒪_X` with values in `F` are a module over the ring `Γ(X, 𝒪_X)` of global functions, a global
function `a` acting by `(a • D)(x) = a|_U · D(x)` on sections over an étale chart `U`; this is
postcomposition of `D` with multiplication by `a` on `F`.  The universal property of the sheaf of
differentials of Stacks 04CT, `Hom_{𝒪_X}(Ω_{X/Y}, F) ≅ Der_Y(𝒪_X, F)`, is then `Γ(X, 𝒪_X)`-linear,
and so linear over any ring `R` mapping to `Γ(X, 𝒪_X)`, for the linear structure on `𝒪_X`-modules
it induces (`CategoryTheory.Linear.ofRingHom`).

For an algebraic space over a field `k`, `R = k` acting through the pullback of functions along
the structure morphism is the `k`-structure of `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)` and of
`Der_k(𝒪_X, 𝒪_X)` in [Stacks Project, Tag 0E41].

## Main definitions

* `AlgebraicGeometry.Space.derivationGlobalSectionModule`: the `Γ(X, 𝒪_X)`-module of
  derivations.
* `AlgebraicGeometry.Space.derivationModuleOfRingHom`: the `R`-module of derivations, for
  `ψ : R →+* Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.Space.differentialsHomGlobalSectionLinearEquiv` and
  `AlgebraicGeometry.Space.differentialsHomLinearEquiv`: `Hom(Ω_{X/Y}, F) ≃ₗ Der_Y(𝒪_X, F)`.

## References

* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe w v u

namespace AlgebraicGeometry.Space

section Generic

variable {C : Type*} [Category C] {R₀ R : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : R₀ ⟶ R)
  (M : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))

/-- **Multiplication of a derivation by a family of sections compatible with restriction**:
`(a • D)(x) = a_U · D(x)` for `x` a section over `U`. -/
def derivationSectionSmul (a : ∀ U, R.obj U) (ha : ∀ {U V : Cᵒᵖ} (g : U ⟶ V), R.map g (a U) = a V)
    (D : PresheafOfModulesOfCommRing.Derivation' M φ) :
    PresheafOfModulesOfCommRing.Derivation' M φ where
  d {U} :=
    (DistribSMul.toAddMonoidHom (M.obj U) (a U : (R ⋙ forget₂ CommRingCat RingCat).obj U)).comp D.d
  d_mul {U} x y := by
    change (a U : (R ⋙ forget₂ CommRingCat RingCat).obj U) • D.d (x * y) =
      x • (a U : (R ⋙ forget₂ CommRingCat RingCat).obj U) • D.d y +
        y • (a U : (R ⋙ forget₂ CommRingCat RingCat).obj U) • D.d x
    rw [D.d_mul, smul_add, smul_comm _ x, smul_comm _ y]
  d_map {U V} g x := by
    change (a V : (R ⋙ forget₂ CommRingCat RingCat).obj V) •
        D.d ((R ⋙ forget₂ CommRingCat RingCat).map g x) =
      M.map g ((a U : (R ⋙ forget₂ CommRingCat RingCat).obj U) • D.d x)
    refine (congrArg (fun m => (a V : (R ⋙ forget₂ CommRingCat RingCat).obj V) • m)
      (D.d_map g x)).trans ?_
    refine Eq.trans ?_ (M.map_smul g _ _).symm
    exact congrArg (· • M.map g (D.d x)) (ha g).symm
  d_app {U} r := by
    change (a U : (R ⋙ forget₂ CommRingCat RingCat).obj U) • D.d (φ.app U r) = 0
    rw [D.d_app, smul_zero]

/-- The derivation `a • D` sends a section `x` over `U` to `a_U • D(x)`. -/
theorem derivationSectionSmul_d (a : ∀ U, R.obj U)
    (ha : ∀ {U V : Cᵒᵖ} (g : U ⟶ V), R.map g (a U) = a V)
    (D : PresheafOfModulesOfCommRing.Derivation' M φ) {U : Cᵒᵖ}
    (x : R.obj U) :
    (derivationSectionSmul φ M a ha D).d x =
      (a U : (R ⋙ forget₂ CommRingCat RingCat).obj U) • D.d x :=
  rfl

end Generic

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- The sections of the structure ring sheaf of an algebraic space commute, in the shape the
global-section constructions of `Stacks.Cohomology.SiteModules` take as a hypothesis. -/
instance structureRingSheaf_isMulCommutative (X : AlgebraicSpaces B S hS)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    IsMulCommutative ((structureRingSheaf B S hS X).obj.obj U) :=
  RingedSite.ringSheafSectionsIsMulCommutative (smallEtaleRingedSite B S hS X.1 X.2) U

/-- The ring `Γ(X, 𝒪_X)` of global functions of an algebraic space is commutative. -/
instance structureGlobalSectionCommRing (X : AlgebraicSpaces B S hS) :
    CommRing (GlobalSectionRing (structureRingSheaf B S hS X)) :=
  inferInstance

/-- The `𝒪_X`-modules form a `Γ(X, 𝒪_X)`-linear category. -/
instance modulesGlobalSectionLinear (X : AlgebraicSpaces B S hS) :
    Linear (GlobalSectionRing (structureRingSheaf B S hS X)) (Modules.{u, u} B S hS X.1 X.2) :=
  linearSheafOfModules (structureRingSheaf B S hS X)

/-- **The derivations of `𝒪_X` are a module over the global functions**: a global function `a`
acts by `(a • D)(x) = a|_U · D(x)` on a section `x` over an étale chart `U`. -/
instance derivationGlobalSectionModule (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    Module (GlobalSectionRing (structureRingSheaf B S hS X))
      (PresheafOfModulesOfCommRing.Derivation' F.val
        (structureSharpInverseImage B S hS f).hom) where
  smul a D := derivationSectionSmul _ F.val (fun U => a.1 U) (fun g => a.2 g) D
  one_smul D := by
    ext U x
    exact one_smul _ _
  mul_smul a b D := by
    ext U x
    exact mul_smul _ _ _
  smul_zero a := by
    ext U x
    exact smul_zero _
  smul_add a D E := by
    ext U x
    exact smul_add _ _ _
  add_smul a b D := by
    ext U x
    exact add_smul _ _ _
  zero_smul D := by
    ext U x
    exact zero_smul _ _

/-- A global function acts on the values of a derivation by multiplication by its
restriction. -/
theorem derivationGlobalSectionModule_smul_d (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (a : GlobalSectionRing (structureRingSheaf B S hS X))
    (D : PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom)
    {U} (x : (structureRingSheaf B S hS X).obj.obj U) :
    (a • D).d x = (globalSmul _ a F).val.app U (D.d x) :=
  rfl

/-- **The universal property of `Ω_{X/Y}` is `Γ(X, 𝒪_X)`-linear.**  Postcomposition with the
universal derivation `d_{X/Y}` of Stacks 04CT is an isomorphism of `Γ(X, 𝒪_X)`-modules
`Hom_{𝒪_X}(Ω_{X/Y}, F) ≅ Der_Y(𝒪_X, F)`. -/
def differentialsHomGlobalSectionLinearEquiv (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    (sheafOfDifferentials B S hS f ⟶ F) ≃ₗ[GlobalSectionRing (structureRingSheaf B S hS X)]
      PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom :=
  { differentialsHomAddEquiv B S hS f F with
    map_smul' := fun a g => by
      ext U x
      exact (g.val.app U).hom.map_smul _ _ }

/-- `differentialsHomGlobalSectionLinearEquiv` sends `g : Ω_{X/Y} ⟶ F` to the composite of the
universal derivation with `g`. -/
theorem differentialsHomGlobalSectionLinearEquiv_apply (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (g : sheafOfDifferentials B S hS f ⟶ F) :
    differentialsHomGlobalSectionLinearEquiv B S hS f F g =
      (universalDerivation B S hS f).postcomp g.val :=
  rfl

section RingHom

variable {R : Type*} [CommRing R] (ψ : R →+* GlobalSectionRing (structureRingSheaf B S hS X))

/-- The `R`-linear structure on the `𝒪_X`-modules induced by a ring homomorphism
`ψ : R →+* Γ(X, 𝒪_X)`: `r` acts as multiplication by the global function `ψ r`. -/
@[instance_reducible]
def modulesLinearOfRingHom : Linear R (Modules.{u, u} B S hS X.1 X.2) :=
  Linear.ofRingHom (D := Modules.{u, u} B S hS X.1 X.2) ψ

/-- The `R`-module of derivations of `𝒪_X`, for a ring homomorphism `ψ : R →+* Γ(X, 𝒪_X)`:
`r` acts as the global function `ψ r`. -/
@[instance_reducible]
def derivationModuleOfRingHom (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    Module R
      (PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom) :=
  Module.compHom _ ψ

/-- **The universal property of `Ω_{X/Y}` is `R`-linear**, for the `R`-linear structure on
`𝒪_X`-modules and the `R`-module of derivations induced by `ψ : R →+* Γ(X, 𝒪_X)`. -/
def differentialsHomLinearEquiv (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) :
    letI := (modulesLinearOfRingHom B S hS ψ).homModule
      (sheafOfDifferentials B S hS f) F
    letI := derivationModuleOfRingHom B S hS ψ f F
    (sheafOfDifferentials B S hS f ⟶ F) ≃ₗ[R]
      PresheafOfModulesOfCommRing.Derivation' F.val (structureSharpInverseImage B S hS f).hom :=
  letI := (modulesLinearOfRingHom B S hS ψ).homModule
    (sheafOfDifferentials B S hS f) F
  letI := derivationModuleOfRingHom B S hS ψ f F
  { differentialsHomAddEquiv B S hS f F with
    map_smul' := fun r g =>
      (differentialsHomGlobalSectionLinearEquiv B S hS f F).map_smul (ψ r) g }

/-- `differentialsHomLinearEquiv` sends `g : Ω_{X/Y} ⟶ F` to the composite of the universal
derivation with `g`. -/
theorem differentialsHomLinearEquiv_apply (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (g : sheafOfDifferentials B S hS f ⟶ F) :
    differentialsHomLinearEquiv B S hS ψ f F g =
      (universalDerivation B S hS f).postcomp g.val :=
  rfl

end RingHom

end AlgebraicGeometry.Space

end
