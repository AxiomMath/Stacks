module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.KerDetected.RingColimit
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap

/-!
# Projecting an ideal through an affine morphism

For an affine morphism of schemes `f : Y ⟶ X`, a quasi-coherent `𝒪_Y`-module `F` and a
quasi-coherent ideal sheaf `I` on `X`, multiplying the pushforward `f₊ F` by `I` agrees with
pushing forward the product of `F` by the inverse-image ideal `f⁻¹ I`:
`I · f₊ F = f₊ ((f⁻¹ I) · F)`.

## Main definitions

* `Stacks.AlgebraicGeometry.AffineIdealPushforward.pushforwardIdealMultipleSections` is the
  ideal multiple of the pushforward module on an affine open.
* `Stacks.AlgebraicGeometry.AffineIdealPushforward.pullbackIdealMultiplePushforwardSections`
  is the pushforward, on the same affine open, of the multiple by the inverse-image ideal.

## Main results

* `Stacks.AlgebraicGeometry.AffineIdealPushforward.ideal_smul_pushforward_sections_eq`
  identifies these two submodules sectionwise on every affine open.

## Implementation notes

Mathlib represents a quasi-coherent ideal sheaf by `AlgebraicGeometry.Scheme.IdealSheafData`,
whose data are its ideals on affine opens. Accordingly the equality of subsheaves is expressed
as equality of their sets of sections over every affine open; those opens form a basis, so this
is the affine-basis form of the sheaf equality in the source. The right-hand side is transported
along the canonical identification of sections of a pushforward with sections over the inverse
image, which is available because `f` is affine and hence `f ⁻¹ᵁ U` is affine.

The mathematical core is `ideal_comap_affine`: for an affine morphism the inverse-image ideal
sheaf is computed on affine opens by `Ideal.map` along `f.app U`. That in turn reduces, via the
affine-local description of `Scheme.IdealSheafData.comap`, to
`Stacks.IdealSheaf.ideal_comap_top_of_isAffine`, which is the same computation on global
sections for a morphism of affine schemes.

Once the two ideals are identified, the equality of section submodules is the restriction-of-
scalars identity `Submodule.restrictScalars_map_smul_eq` for the ring map `f.app U`.

## References

* [Stacks Project, Tag 01YP](https://stacks.math.columbia.edu/tag/01YP)
-/

@[expose] public section

noncomputable section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.AffineIdealPushforward

section

open CategoryTheory.Limits

/-- Transporting `Scheme.Hom.appLE` along equalities of the opens involved. -/
private theorem appLE_hom_heq {X Y : Scheme.{u}} (f : Y ⟶ X)
    {U U' : X.Opens} {V V' : Y.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (hU : U = U') (hV : V = V') :
    HEq (f.appLE U V e).hom (f.appLE U' V' (hU ▸ hV ▸ e)).hom := by
  cases hU
  cases hV
  rfl

/-- The top-open map of a restricted morphism is the map on the open it was restricted to. -/
private theorem morphismRestrict_appTop_heq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (U : X.affineOpens) :
    HEq ((f ∣_ U.1).appTop).hom (f.app U.1).hom := by
  have h1 : HEq ((f ∣_ U.1).appTop).hom
      (f.appLE (U.1.ι ''ᵁ ⊤) ((f ⁻¹ᵁ U.1).ι ''ᵁ ⊤)
        (image_morphismRestrict_preimage f U.1 ⊤).le).hom := by
    rw [morphismRestrict_appTop]
    rfl
  simpa [Scheme.Hom.appLE] using h1.trans
    (appLE_hom_heq f (image_morphismRestrict_preimage f U.1 ⊤).le
      (Scheme.Opens.ι_image_top U.1) (Scheme.Opens.ι_image_top (f ⁻¹ᵁ U.1)))

/-- For an affine morphism, the inverse-image ideal sheaf on the preimage of an affine open is
the `Ideal.map` along `f.app U` of the ideal on that open. -/
private theorem ideal_comap_affine {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsAffineHom f] (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap f).ideal ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ =
      Ideal.map (f.app U.1).hom (I.ideal U) := by
  let V : Y.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
  have : IsAffine U.1 := U.2
  have : IsAffine V.1 := V.2
  have hcomp : (I.comap f).comap V.1.ι = (I.comap U.1.ι).comap (f ∣_ U.1) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have htarget := Stacks.Divisors.ideal_comap_top_heq (I.comap f) V
  have hΓ (Z : Scheme.{u}) (W : Z.Opens) : Γ(W, ⊤) = Γ(Z, W) := by
    show Γ(Z, (Scheme.Hom.opensFunctor W.ι).obj ⊤) = Γ(Z, W)
    rw [Scheme.Opens.ι_image_top]
  rw [hcomp] at htarget
  exact eq_of_heq ((htarget.symm.trans (heq_of_eq
    (Stacks.IdealSheaf.ideal_comap_top_of_isAffine (I.comap U.1.ι) (f ∣_ U.1)))).trans
    (Stacks.AlgebraicGeometry.ideal_map_heq (hΓ X U.1) (hΓ Y V.1) (morphismRestrict_appTop_heq f U)
      (Stacks.Divisors.ideal_comap_top_heq I U)))

end

variable {X Y : Scheme.{u}}

/-- On an affine open `U ⊆ X`, the sections of `I · f₊ F ⊆ f₊ F`. -/
def pushforwardIdealMultipleSections (f : Y ⟶ X) (I : X.IdealSheafData)
    (F : Y.Modules) (U : X.affineOpens) :
    Set Γ((Scheme.Modules.pushforward f).obj F, U) :=
  ↑(I.ideal U •
    (⊤ : Submodule Γ(X, U) Γ((Scheme.Modules.pushforward f).obj F, U)))

/-- On an affine open `U ⊆ X`, the sections of `f₊((f⁻¹ I) · F)`, viewed inside the sections of
`f₊ F`.

The affine hypothesis ensures that `f ⁻¹ᵁ U` is affine, so the pulled-back ideal sheaf can be
evaluated there. -/
def pullbackIdealMultiplePushforwardSections (f : Y ⟶ X) [IsAffineHom f]
    (I : X.IdealSheafData) (F : Y.Modules) (U : X.affineOpens) :
    Set Γ((Scheme.Modules.pushforward f).obj F, U) :=
  { s | Equiv.cast
      (congrArg (fun M ↦ ↑M) (Scheme.Modules.pushforward_obj_obj f F U)) s ∈
      (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ •
        (⊤ : Submodule Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U)) }

/-- **Stacks Project, Tag 01YP.** If `f : Y ⟶ X` is affine, `F` is a quasi-coherent
`𝒪_Y`-module, and `I` is a quasi-coherent ideal sheaf on `X`, then `I · f₊ F = f₊((f⁻¹ I) · F)`.

The equality is stated on every affine open, using the affine-open presentation of
quasi-coherent ideal sheaves. -/
@[stacks 01YP]
theorem ideal_smul_pushforward_sections_eq (f : Y ⟶ X) [IsAffineHom f]
    (I : X.IdealSheafData) (F : Y.Modules) [F.IsQuasicoherent]
    (U : X.affineOpens) :
    pushforwardIdealMultipleSections f I F U =
      pullbackIdealMultiplePushforwardSections f I F U := by
  ext s
  show s ∈ (I.ideal U • (⊤ : Submodule Γ(X, U) Γ((Scheme.Modules.pushforward f).obj F, U))) ↔
    (Equiv.cast (congrArg (fun M ↦ ↑M) (Scheme.Modules.pushforward_obj_obj f F U))) s ∈
      (I.comap f).ideal ⟨f ⁻¹ᵁ U, U.2.preimage f⟩ •
        (⊤ : Submodule Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U))
  rw [ideal_comap_affine f I U]
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Module Γ(X, U) Γ(F, f ⁻¹ᵁ U) :=
    Module.restrictScalars Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U)
  have : IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U) :=
    IsScalarTower.restrictScalars Γ(X, U) Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U)
  have h := Submodule.restrictScalars_map_smul_eq (R := Γ(Y, f ⁻¹ᵁ U))
    (S := Γ(X, U)) (M := Γ(F, f ⁻¹ᵁ U)) (I.ideal U)
    (⊤ : Submodule Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U))
  show s ∈ (I.ideal U • (⊤ : Submodule Γ(X, U) Γ(F, f ⁻¹ᵁ U))) ↔
    s ∈ Ideal.map (f.app U).hom (I.ideal U) •
      (⊤ : Submodule Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U))
  convert (Iff.of_eq (congrArg (fun N : Submodule Γ(X, U) Γ(F, f ⁻¹ᵁ U) => s ∈ N)
    h).symm).trans (Submodule.restrictScalars_mem Γ(X, U)
      (Ideal.map (f.app U).hom (I.ideal U) •
        (⊤ : Submodule Γ(Y, f ⁻¹ᵁ U) Γ(F, f ⁻¹ᵁ U)))
      (show Γ(F, f ⁻¹ᵁ U) from s)) using 1
  · simp only [Submodule.restrictScalars_top]

end Stacks.AlgebraicGeometry.AffineIdealPushforward

end

end
