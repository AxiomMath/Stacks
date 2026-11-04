module

public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels

/-!
# Quasi-coherent modules on an arbitrary scheme form a weak Serre subcategory

Let `X` be a scheme. The quasi-coherent `𝒪_X`-modules contain the zero module and are closed
under kernels, cokernels and extensions, so they form a weak Serre subcategory of all
`𝒪_X`-modules; consequently the complexes of `𝒪_X`-modules with quasi-coherent cohomology form a
strictly full saturated triangulated subcategory `D_QCoh(𝒪_X)` of `D(𝒪_X)`.

Three of the four closure properties were already available on an arbitrary scheme: kernels are
`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`, cokernels are
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel`, and the zero module is
the kernel of the identity of the structure sheaf, which is quasi-coherent
(`Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`). What was missing was
closure under extensions, available only over an affine base as
`AlgebraicGeometry.isQuasicoherent_X₂_of_shortExact`. This file supplies it in general, and
assembles the weak Serre statement and the triangulated subcategory from it.

## Main results

* `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_X₂_of_shortExact` — an
  extension of quasi-coherent `𝒪_X`-modules is quasi-coherent, for an arbitrary scheme `X`.
* `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerreClass` and
  `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre` — the
  quasi-coherent `𝒪_X`-modules form a weak Serre subcategory, in the
  `ObjectProperty.IsWeakSerreClass` and in the five-term `WeakSerre.IsWeakSerre` formulation.
* `Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated` —
  `D_QCoh(𝒪_X)` is a strictly full saturated triangulated subcategory of `D(𝒪_X)`.

## Implementation notes

Extension closure is proved by reduction to the affine case through the locality of
quasi-coherence, in exactly the shape the colimit statement uses it: a module whose restriction to
every affine open is quasi-coherent is quasi-coherent
(`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens`), and an
affine open `V` of `X` comes with `V.2.isoSpec : V.toScheme ≅ Spec Γ(X, V)`.

What makes the reduction work is that restriction along an open immersion is *exact*: it is
additive and preserves finite limits by
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_additive` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits`, and preserves colimits
because it is a left adjoint. So `ShortComplex.ShortExact.map_of_exact` carries a short exact
sequence of `𝒪_X`-modules to a short exact sequence of `𝒪_V`-modules, and the two outer terms stay
quasi-coherent by `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_restrictFunctor`. This is the
step that has no colimit analogue in
`Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit`, where the diagram
is transported along the left adjoint `~` instead.

Quasi-coherence of the outer terms is passed as an explicit argument rather than as an instance
hypothesis, because in `ShortComplex.map` form the subterm `(S.map F).X₁` is only
definitionally `F.obj S.X₁` and instance search does not see through it.

No `@[stacks]` attribute is attached. The statement that quasi-coherent modules form a weak Serre
subcategory is part of [Stacks, Tag 01LA] and is the input to [Stacks, Tag 06VT]; the covering
sets of both tags contain further declarations (06VT in particular asserts the comparison functor
`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X)`, which is not here), so a tag on these declarations would report
those tags as formalized when they are not.

The derived category in force is the locally small one,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, which puts the morphisms of `D(𝒪_X)` in the
universe of `X`; this and not `HasDerivedCategory.standard` is the model against which the
direct-sum and Brown-representability statements about `D_QCoh(𝒪_X)` have content.

## References

* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 077P](https://stacks.math.columbia.edu/tag/077P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.AlgebraicGeometry.QuasicoherentWeakSerre

open Stacks.AlgebraicGeometry.QuasicoherentColimits

/-! ### Closure under extensions -/

/-- Restriction along an open immersion sends a short exact sequence of modules with
quasi-coherent outer terms to one of the same kind. -/
private theorem shortExact_map_restrictFunctor_isQuasicoherent {Y Z : Scheme.{u}} (f : Z ⟶ Y)
    [IsOpenImmersion f] {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    (S.map (Scheme.Modules.restrictFunctor f)).ShortExact ∧
      (S.map (Scheme.Modules.restrictFunctor f)).X₁.IsQuasicoherent ∧
      (S.map (Scheme.Modules.restrictFunctor f)).X₃.IsQuasicoherent :=
  ⟨hS.map_of_exact _, Scheme.Modules.isQuasicoherent_restrictFunctor f S.X₁,
    Scheme.Modules.isQuasicoherent_restrictFunctor f S.X₃⟩

/-- On a scheme isomorphic to a spectrum, an extension of quasi-coherent modules is
quasi-coherent: restriction along the isomorphism is exact and preserves quasi-coherence, so the
affine statement `AlgebraicGeometry.isQuasicoherent_X₂_of_shortExact` applies, and the result is
carried back along the inverse. -/
theorem isQuasicoherent_X₂_of_shortExact_of_isoSpec {Y : Scheme.{u}} {R : CommRingCat.{u}}
    (e : Y ≅ Spec R) {S : ShortComplex Y.Modules} (hS : S.ShortExact)
    (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := by
  obtain ⟨hS', h₁', h₃'⟩ := shortExact_map_restrictFunctor_isQuasicoherent e.inv hS h₁ h₃
  have key : ((Scheme.Modules.restrictFunctor e.inv).obj S.X₂).IsQuasicoherent :=
    _root_.AlgebraicGeometry.isQuasicoherent_X₂_of_shortExact R (S := S.map _) hS'
  have iso : ((Scheme.Modules.restrictFunctor e.inv).obj S.X₂).restrict e.hom ≅ S.X₂ :=
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).app S.X₂).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.hom_inv_id).app S.X₂ ≪≫
      Scheme.Modules.restrictFunctorId.app S.X₂
  have := Scheme.Modules.isQuasicoherent_restrictFunctor e.hom
    ((Scheme.Modules.restrictFunctor e.inv).obj S.X₂)
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso iso this

/-- **Quasi-coherent modules on a scheme are closed under extensions.** If `0 → M₁ → M₂ → M₃ → 0`
is a short exact sequence of `𝒪_X`-modules with `M₁` and `M₃` quasi-coherent, then `M₂` is
quasi-coherent. The statement is local on `X`, and on an affine open it is
`AlgebraicGeometry.isQuasicoherent_X₂_of_shortExact`. -/
theorem isQuasicoherent_X₂_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) (h₁ : S.X₁.IsQuasicoherent) (h₃ : S.X₃.IsQuasicoherent) :
    S.X₂.IsQuasicoherent := by
  refine isQuasicoherent_of_restrict_affineOpens _ fun V ↦ ?_
  obtain ⟨hS', h₁', h₃'⟩ :=
    shortExact_map_restrictFunctor_isQuasicoherent (V : X.Opens).ι hS h₁ h₃
  exact isQuasicoherent_X₂_of_shortExact_of_isoSpec V.2.isoSpec hS' h₁' h₃'

/-! ### The weak Serre subcategory -/

variable (X : Scheme.{u})

/-- The zero `𝒪_X`-module is quasi-coherent, being the kernel of the identity of the structure
sheaf. -/
instance isQuasicoherent_containsZero :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero :=
  letI 𝒪 : X.Modules := SheafOfModules.unit X.ringCatSheaf
  haveI : 𝒪.IsQuasicoherent := inferInstance
  ⟨kernel (𝟙 𝒪), (isZero_zero _).of_iso (kernel.ofMono (𝟙 𝒪)),
    (inferInstance : (kernel (𝟙 𝒪)).IsQuasicoherent)⟩

/-- Quasi-coherent `𝒪_X`-modules are closed under extensions. -/
instance isQuasicoherent_isClosedUnderExtensions :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := isQuasicoherent_X₂_of_shortExact hS h₁ h₃

/-- **Quasi-coherent modules on a scheme form a weak Serre subcategory**: they contain zero, are
closed under isomorphisms, and are closed under kernels, cokernels and extensions. -/
instance isQuasicoherent_isWeakSerreClass :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsWeakSerreClass where

/-- The five-term formulation of `isQuasicoherent_isWeakSerreClass`: in an exact sequence
`M₀ → M₁ → M₂ → M₃ → M₄` of `𝒪_X`-modules with the four outer terms quasi-coherent, the middle
term is quasi-coherent. -/
theorem isQuasicoherent_isWeakSerre :
    WeakSerre.IsWeakSerre (SheafOfModules.isQuasicoherent X.ringCatSheaf) := by
  refine ⟨inferInstance,
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).exists_prop_of_isWeakSerreClass,
    fun E h₀ h₁ h₃ h₄ => ?_⟩
  exact prop_mid_of_exact₄
    ((SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_obj₂_of_exact)
    E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄

/-- `D_QCoh(𝒪_X)`, the complexes of `𝒪_X`-modules with quasi-coherent cohomology, is a strictly
full saturated triangulated subcategory of `D(𝒪_X)`, for an arbitrary scheme `X`. -/
instance derivedQuasicoherent_isTriangulated :
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _ (isQuasicoherent_isWeakSerre X)

end Stacks.AlgebraicGeometry.QuasicoherentWeakSerre

end
