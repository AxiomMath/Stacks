module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksCore.Tactic.StacksAttribute

/-!
# The affine dictionary: restricting `M^~` along an affine open immersion

Let `φ : R ⟶ S` be a morphism of commutative rings such that `Spec φ` is an open immersion —
for instance the localization `R ⟶ R_g` away from an element. This file identifies the
restriction of the sheaf `M^~` of `𝒪_{Spec R}`-modules associated to an `R`-module `M` along
`Spec φ` with the sheaf associated to the `S`-module `S ⊗_R M`:

`M ↦ (M^~)|_{Spec S}` and `M ↦ (S ⊗_R M)^~`

are isomorphic as functors `ModuleCat R ⥤ (Spec S).Modules`, and likewise on complexes.

## Main definitions

* `Stacks.AffineTilde.pushforwardGammaIso`: the global sections of `φ_* N`, as an `R`-module,
  are the global sections of `N` with its `S`-action restricted along `φ`. This holds for every
  morphism of rings, with no open-immersion hypothesis.
* `Stacks.AffineTilde.tildeRestrictIso`: **the dictionary.**
  `M ↦ (M^~)|_{Spec S} ≅ M ↦ (S ⊗_R M)^~`.
* `Stacks.AffineTilde.tildeRestrictComplexIso` and
  `Stacks.AffineTilde.restrictTildeComplexIso`: the same on cochain complexes, as an
  isomorphism of functors and as an isomorphism at a fixed complex.
* `AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctor`: restriction of
  `𝒪_X`-modules to an open subspace `U` of a scheme, as a pushforward along the inclusion of
  opens, is restriction along the open immersion `U.ι`.
* `AlgebraicGeometry.RingedSpace.restrictModulesIsoRestrictFunctorComp` and
  `AlgebraicGeometry.RingedSpace.restrictComplexIsoRestrictFunctor`: hence restricting to `U`
  and then along a morphism `Y ⟶ U` is restricting along the composite `Y ⟶ X`.

## References

* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
* [Stacks Project, Tag 066D](https://stacks.math.columbia.edu/tag/066D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

/-- Restriction of `𝒪_Y`-modules along an open immersion is an additive functor. -/
public instance AlgebraicGeometry.Scheme.Modules.additive_restrictFunctor {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] : (Scheme.Modules.restrictFunctor f).Additive :=
  have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (Scheme.Modules.restrictFunctor f)
  Functor.additive_of_preservesBinaryBiproducts _

namespace Stacks.AffineTilde

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-! ### Global sections of a pushforward along `Spec φ` -/

/-- The two `R`-actions on the global sections of an `𝒪_{Spec S}`-module `N` agree: acting
through `R ⟶ Γ(Spec R, ⊤) ⟶ Γ(Spec S, ⊤)` is acting through `R ⟶ S ⟶ Γ(Spec S, ⊤)`. -/
theorem appTop_ΓSpecIso_inv_smul (N : (Spec S).Modules) (r : R) (x : Γ(N, ⊤)) :
    ((Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r)) • x =
      ((Scheme.ΓSpecIso S).inv (φ r)) • x := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- The global sections of `(Spec φ)_* N`, as an `R`-module, are the global sections of `N` with
its `S`-action restricted along `φ`; the underlying map is the identity. -/
def pushforwardGammaIsoApp (N : (Spec S).Modules) :
    (Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor).obj N ≅
      (moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj N :=
  (AddEquiv.toLinearEquiv
    (M := ↑((Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor).obj N))
    (M₂ := ↑((moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom).obj N))
    (by rfl) (appTop_ΓSpecIso_inv_smul φ N)).toModuleIso

/-- Taking global sections of a pushforward along `Spec φ` is taking global sections and then
restricting scalars along `φ`, naturally in the `𝒪_{Spec S}`-module. -/
def pushforwardGammaIso :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents (pushforwardGammaIsoApp φ) fun _ ↦ rfl

/-! ### The dictionary -/

variable [IsOpenImmersion (Spec.map φ)]

/-- **The affine dictionary.** If `Spec φ` is an open immersion, then restricting the sheaf
`M^~` associated to an `R`-module `M` along `Spec φ` gives the sheaf associated to the
`S`-module `S ⊗_R M`, naturally in `M`. -/
def tildeRestrictIso :
    tilde.functor R ⋙ Scheme.Modules.restrictFunctor (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S :=
  (tilde.adjunction.comp (Scheme.Modules.restrictAdjunction _)).leftAdjointUniq
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).comp
      tilde.adjunction).ofNatIsoRight (pushforwardGammaIso φ).symm)

/-- **The affine dictionary on cochain complexes.** Restricting the complex of
`𝒪_{Spec R}`-modules associated to a complex `M^•` of `R`-modules along an open immersion
`Spec φ` gives the complex of `𝒪_{Spec S}`-modules associated to `S ⊗_R M^•`. -/
def tildeRestrictComplexIso :
    (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (Scheme.Modules.restrictFunctor (Spec.map φ)).mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (ModuleCat.extendScalars φ.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (tildeRestrictIso φ) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl
      (ModuleCat.extendScalars φ.hom ⋙ tilde.functor S)) (ComplexShape.up ℤ)).symm

/-- The affine dictionary at a fixed complex: the restriction of `\widetilde{M^•}` along the
open immersion `Spec φ` is `\widetilde{S ⊗_R M^•}`. -/
def restrictTildeComplexIso (M : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((Scheme.Modules.restrictFunctor (Spec.map φ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≅
      ((tilde.functor S).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) :=
  (tildeRestrictComplexIso φ).app M

end Stacks.AffineTilde

/-! ### The ringed-space idiom -/

namespace AlgebraicGeometry.RingedSpace

/-- Restriction of `𝒪_X`-modules to an open subspace `U` of a scheme, as a pushforward along the
inclusion of opens, is restriction along the open immersion `U.ι`. -/
public def restrictModulesIsoRestrictFunctor (X : Scheme.{u}) (U : X.Opens) :
    restrictModules X.toRingedSpace U ≅ Scheme.Modules.restrictFunctor U.ι :=
  letI : (U.isOpenEmbedding.functor).IsContinuous
      (Opens.grothendieckTopology (X.toRingedSpace.restrict U.isOpenEmbedding).carrier)
      (Opens.grothendieckTopology X.toRingedSpace.carrier) :=
    U.isOpenEmbedding.functor_isContinuous
  SheafOfModules.pushforwardCongr (by
    ext V x
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl)

/-- Restricting `𝒪_X`-modules to an open subspace `U` of a scheme `X` and then along a morphism
`f : Y ⟶ U.toScheme` is restricting along the composite `f ≫ U.ι`. -/
public def restrictModulesIsoRestrictFunctorComp {X Y : Scheme.{u}} (U : X.Opens)
    (f : Y ⟶ U.toScheme) [IsOpenImmersion f] :
    restrictModules X.toRingedSpace U ⋙ Scheme.Modules.restrictFunctor f ≅
      Scheme.Modules.restrictFunctor (f ≫ U.ι) :=
  Functor.isoWhiskerRight (restrictModulesIsoRestrictFunctor X U)
      (Scheme.Modules.restrictFunctor f) ≪≫
    (Scheme.Modules.restrictFunctorComp f U.ι).symm

/-- The same on cochain complexes: restricting a complex of `𝒪_X`-modules to an open subspace
`U` and then along `f : Y ⟶ U.toScheme` is restricting along `f ≫ U.ι`. -/
public def restrictComplexIsoRestrictFunctor {X Y : Scheme.{u}} (U : X.Opens)
    (f : Y ⟶ U.toScheme) [IsOpenImmersion f]
    (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) ℤ) :
    ((Scheme.Modules.restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (restrictComplex E U) ≅
      ((Scheme.Modules.restrictFunctor (f ≫ U.ι)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E :=
  letI : (restrictModules X.toRingedSpace U ⋙
      Scheme.Modules.restrictFunctor f).PreservesZeroMorphisms := ⟨fun _ _ ↦ by ext _ _; rfl⟩
  letI : (show StrictlyPerfect.OXMod.{u, u} X.toRingedSpace ⥤ Y.Modules from
      Scheme.Modules.restrictFunctor (f ≫ U.ι)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ by ext _ _; rfl⟩
  (NatIso.mapHomologicalComplex (restrictModulesIsoRestrictFunctorComp U f)
    (ComplexShape.up ℤ)).app E

end AlgebraicGeometry.RingedSpace

end
