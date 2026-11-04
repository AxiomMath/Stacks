module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-!
# Sections of a quasi-coherent module on a basic open are a localization

Let `F` be a quasi-coherent `𝒪_X`-module on a scheme `X`, let `U` be an affine open and let
`g ∈ Γ(X, U)`. Restriction

  `Γ(F, U) ⟶ Γ(F, X.basicOpen g)`

exhibits the sections over the basic open as the localization of the sections over `U` at `g`.
This is the module half of [Stacks, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7) in the
case of an affine open, and it is the input every affine-local computation with a
quasi-coherent module needs.

## Main definitions

* `AlgebraicGeometry.sectionsLinearEquivOfIso`: an isomorphism of modules on a scheme induces a
  linear equivalence on the sections over any open.
* `AlgebraicGeometry.pullbackIdSectionsEquiv`: pulling back along `𝟙 X` does not change the
  sections.
* `AlgebraicGeometry.basicOpenSectionsBaseChangeEquiv`: the sections over a basic open of an
  affine open are the base change of the sections over the affine open.

## Main results

* `AlgebraicGeometry.isLocalizedModule_restrict_basicOpen`: the restriction map is a
  localization of modules at the powers of `g`.

## Implementation notes

The localization statement is obtained from base change rather than proved by hand. The
isomorphism `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` identifies
`Γ(Y, V) ⊗_{Γ(X, U)} Γ(F, U)` with the sections of `f^*F` over `V` for a compatible pair of
affine opens, normalized on `1 ⊗ a`; taking `f = 𝟙 X` and `V = X.basicOpen g` turns it into an
identification of `Γ(X, X.basicOpen g) ⊗_{Γ(X, U)} Γ(F, U)` with `Γ(F, X.basicOpen g)` sending
`1 ⊗ a` to the restriction of `a`. That is exactly `IsBaseChange.of_equiv`, and
`isLocalizedModule_iff_isBaseChange` converts it, since `Γ(X, X.basicOpen g)` is the
localization of `Γ(X, U)` at `g` by `IsAffineOpen.isLocalization_basicOpen`.

Pulling back along `𝟙 X` is not the identity functor on modules, only isomorphic to it; the
comparison is `AlgebraicGeometry.Scheme.Modules.restrictFunctorId` composed with
`restrictFunctorIsoPullback`, and `pullbackIdSectionsEquiv` packages it as a linear
equivalence on sections. Its value on a pullback section is
`pullbackIdSectionsEquiv_pullbackSection`, which is what carries the normalization across.

The `Γ(X, U)`-module structure on `Γ(F, X.basicOpen g)` is not an instance — it is restriction
of scalars along the restriction map of the structure sheaf — so it is taken as a hypothesis
together with its scalar tower, in the shape a caller that has just built it by
`Module.compHom` can supply. The map itself is taken as a parameter pinned by its values, for
the same reason: the caller has it in whatever shape its own instances produced.

## References

* [Stacks Project, Tag 01P7](https://stacks.math.columbia.edu/tag/01P7)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- An isomorphism of modules on a scheme induces a linear equivalence on the sections over
any open. -/
noncomputable def sectionsLinearEquivOfIso {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(N, V) where
  toFun a := Scheme.Modules.Hom.app e.hom V a
  map_add' a b := by exact map_add _ a b
  map_smul' r a := Scheme.Modules.Hom.app_smul e.hom r a
  invFun a := Scheme.Modules.Hom.app e.inv V a
  left_inv a := by
    have h : Scheme.Modules.Hom.app e.hom V ≫ Scheme.Modules.Hom.app e.inv V = 𝟙 _ := by
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]
    calc Scheme.Modules.Hom.app e.inv V (Scheme.Modules.Hom.app e.hom V a)
        = (Scheme.Modules.Hom.app e.hom V ≫ Scheme.Modules.Hom.app e.inv V) a :=
          (ConcreteCategory.comp_apply _ _ a).symm
      _ = a := by rw [h]; rfl
  right_inv a := by
    have h : Scheme.Modules.Hom.app e.inv V ≫ Scheme.Modules.Hom.app e.hom V = 𝟙 _ := by
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
    calc Scheme.Modules.Hom.app e.hom V (Scheme.Modules.Hom.app e.inv V a)
        = (Scheme.Modules.Hom.app e.inv V ≫ Scheme.Modules.Hom.app e.hom V) a :=
          (ConcreteCategory.comp_apply _ _ a).symm
      _ = a := by rw [h]; rfl

@[simp]
theorem sectionsLinearEquivOfIso_apply {M N : X.Modules} (e : M ≅ N) (V : X.Opens)
    (a : Γ(M, V)) :
    sectionsLinearEquivOfIso e V a = Scheme.Modules.Hom.app e.hom V a := rfl

/-- Pulling a module back along the identity is isomorphic to doing nothing. -/
noncomputable def pullbackIdIso (F : X.Modules) :
    (Scheme.Modules.pullback (𝟙 X)).obj F ≅ F :=
  ((Scheme.Modules.restrictFunctorIsoPullback (𝟙 X)).app F).symm ≪≫
    (Scheme.Modules.restrictFunctorId (X := X)).app F

/-- Pulling a module back along the identity does not change the sections over an open. -/
noncomputable def pullbackIdSectionsEquiv (F : X.Modules) (V : X.Opens) :
    Γ((Scheme.Modules.pullback (𝟙 X)).obj F, V) ≃ₗ[Γ(X, V)] Γ(F, V) :=
  sectionsLinearEquivOfIso (pullbackIdIso F) V

/-- `AlgebraicGeometry.pullbackIdSectionsEquiv` sends the pullback of a section along `𝟙 X` to
the restriction of that section. -/
theorem pullbackIdSectionsEquiv_pullbackSection (F : X.Modules) (U V : X.Opens)
    (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (h' : V ≤ U) (a : Γ(F, U)) :
    pullbackIdSectionsEquiv F V (Scheme.Modules.pullbackSection (𝟙 X) F U V h a) =
      F.presheaf.map (homOfLE h').op a := by
  have hIm : (𝟙 X) ''ᵁ V ≤ U := by simpa using h'
  have hVeq : V = (𝟙 X) ''ᵁ V := by simp
  have h₁ := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection (𝟙 X) F U V h hIm a
  have hcomp : F.presheaf.map (homOfLE hIm).op ≫ F.presheaf.map (eqToHom hVeq).op =
      F.presheaf.map (homOfLE h').op := by
    rw [← Functor.map_comp]
    congr 1
  calc pullbackIdSectionsEquiv F V (Scheme.Modules.pullbackSection (𝟙 X) F U V h a)
      = Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorId (X := X)).hom.app F) V
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.restrictFunctorIsoPullback (𝟙 X)).inv.app F) V
            (Scheme.Modules.pullbackSection (𝟙 X) F U V h a)) := rfl
    _ = Scheme.Modules.Hom.app ((Scheme.Modules.restrictFunctorId (X := X)).hom.app F) V
          (F.presheaf.map (homOfLE hIm).op a) :=
        congrArg _ h₁
    _ = F.presheaf.map (eqToHom hVeq).op (F.presheaf.map (homOfLE hIm).op a) := by
        rw [Scheme.Modules.restrictFunctorId_hom_app_app]
        rfl
    _ = F.presheaf.map (homOfLE h').op a := by
        rw [← ConcreteCategory.comp_apply, hcomp]

/-- An isomorphism of modules on a scheme, read on the sections over an open as an
isomorphism of modules over the functions on that open. -/
noncomputable def sectionsModuleIsoOfIso {M N : X.Modules} (e : M ≅ N) (V : X.Opens) :
    ModuleCat.of Γ(X, V) Γ(M, V) ≅ ModuleCat.of Γ(X, V) Γ(N, V) :=
  (sectionsLinearEquivOfIso e V).toModuleIso

variable (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) (g : Γ(X, U))

/-- A basic open of an open sits inside the preimage of that open along the identity. -/
theorem basicOpen_le_id_preimage : X.basicOpen g ≤ (𝟙 X) ⁻¹ᵁ U := by
  simpa using X.basicOpen_le g

/-- The sections of a quasi-coherent module over a basic open of an affine open, identified with
the base change of the sections over that affine open. -/
noncomputable def basicOpenSectionsBaseChangeIso :
    (ModuleCat.extendScalars (Scheme.Hom.appLE (𝟙 X) U (X.basicOpen g)
          (basicOpen_le_id_preimage g)).hom).obj (ModuleCat.of Γ(X, U) Γ(F, U)) ≅
      ModuleCat.of Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) :=
  affinePullbackSectionsBaseChangeIso (𝟙 X) F hU (hU.basicOpen g)
      (basicOpen_le_id_preimage g) ≪≫
    sectionsModuleIsoOfIso (pullbackIdIso F) (X.basicOpen g)

/-- `AlgebraicGeometry.basicOpenSectionsBaseChangeIso` sends `1 ⊗ a` to the restriction of `a`,
which is what identifies it as the canonical comparison. -/
theorem basicOpenSectionsBaseChangeIso_hom_one_tmul (a : Γ(F, U)) :
    (basicOpenSectionsBaseChangeIso F hU g).hom
        ((1 : Γ(X, X.basicOpen g)) ⊗ₜ[Γ(X, U),
          (Scheme.Hom.appLE (𝟙 X) U (X.basicOpen g) (basicOpen_le_id_preimage g)).hom] a) =
      F.presheaf.map (homOfLE (X.basicOpen_le g)).op a := by
  have h1 := affinePullbackSectionsBaseChangeIso_one_tmul (𝟙 X) F hU (hU.basicOpen g)
    (basicOpen_le_id_preimage g) a
  have h2 := pullbackIdSectionsEquiv_pullbackSection F U (X.basicOpen g)
    (basicOpen_le_id_preimage g) (X.basicOpen_le g) a
  refine (ConcreteCategory.comp_apply _ _ _).trans ?_
  exact (congrArg
    (fun z => (sectionsModuleIsoOfIso (pullbackIdIso F) (X.basicOpen g)).hom z) h1).trans h2

/-- The base-change criterion, with the comparison isomorphism as a parameter. Keeping it
opaque is what makes the proof cheap: the two spellings of `1 ⊗ a` — through the `Algebra`
instance of the structure sheaf and through the ring map the extension of scalars is taken
along — are definitionally equal, but checking that under a *named* comparison unfolds the
comparison, and under a parameter it does not. -/
private theorem isBaseChange_of_iso {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (g : Γ(X, U)) (h : X.basicOpen g ≤ (𝟙 X) ⁻¹ᵁ U)
    [Module Γ(X, U) Γ(F, X.basicOpen g)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen g) Γ(F, X.basicOpen g)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, X.basicOpen g))
    (Φ : ((ModuleCat.extendScalars (Scheme.Hom.appLE (𝟙 X) U (X.basicOpen g) h).hom).obj
        (ModuleCat.of Γ(X, U) Γ(F, U))) ≅
      ModuleCat.of Γ(X, X.basicOpen g) Γ(F, X.basicOpen g))
    (hΦ : ∀ a, Φ.hom ((1 : Γ(X, X.basicOpen g)) ⊗ₜ[Γ(X, U),
        (Scheme.Hom.appLE (𝟙 X) U (X.basicOpen g) h).hom] a) = ρ a) :
    IsBaseChange Γ(X, X.basicOpen g) ρ :=
  IsBaseChange.of_equiv Φ.toLinearEquiv fun a =>
    (Iso.toLinearEquiv_apply Φ _).trans (hΦ a)

include hU in
/-- **The module half of Tag 01P7 on an affine open.** For a quasi-coherent module on a scheme,
restriction to a basic open of an affine open exhibits the sections there as the localization of
the sections over the affine open at the powers of that function. -/
theorem isLocalizedModule_restrict_basicOpen
    [Module Γ(X, U) Γ(F, X.basicOpen g)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen g) Γ(F, X.basicOpen g)]
    (ρ : Γ(F, U) →ₗ[Γ(X, U)] Γ(F, X.basicOpen g))
    (hρ : ∀ a, ρ a = F.presheaf.map (homOfLE (X.basicOpen_le g)).op a) :
    IsLocalizedModule (Submonoid.powers g) ρ := by
  have : IsLocalization.Away g Γ(X, X.basicOpen g) := hU.isLocalization_basicOpen g
  rw [isLocalizedModule_iff_isBaseChange (Submonoid.powers g) Γ(X, X.basicOpen g)]
  exact isBaseChange_of_iso F g (basicOpen_le_id_preimage g) ρ
    (basicOpenSectionsBaseChangeIso F hU g)
    fun a => (basicOpenSectionsBaseChangeIso_hom_one_tmul F hU g a).trans (hρ a).symm

end AlgebraicGeometry

end
