module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget

/-!
# Global sections of a flat base change

Let `X` be a quasi-compact quasi-separated scheme over `Spec R` and let `R ⟶ L` be a flat ring
map.  This file records that the canonical square of global sections

```
Γ(Spec R, ⊤) ⟶ Γ(X, ⊤)
     |             |
     v             v
Γ(Spec L, ⊤) ⟶ Γ(X ×_{Spec R} Spec L, ⊤)
```

is a pushout of rings, and the consequence that the canonical morphisms to the spectra of the
rings of global sections form a pullback square of schemes.

## Main results

* `isPushout_appTop`: the square of global sections above is a pushout square in `CommRingCat`.
* `isPullback_toSpecΓ`: the square
  `X ×_{Spec R} Spec L ⟶ X`, `· ⟶ Spec Γ(X ×_{Spec R} Spec L, ⊤)`, `X ⟶ Spec Γ(X, ⊤)` is a
  pullback square of schemes.

## Implementation notes

The pushout square is *not* proved here:  it is `AlgebraicGeometry.isIso_pushoutSection_iff`
together with `AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`, both of
which are in Mathlib at the present pin.  This file only instantiates them at the top open of
every scheme involved, which is the shape every consumer in this repository wants, and derives the
pullback square of spectra from it.

Two module docstrings in this repository —
`StacksFrontier/AlgebraicGeometry/ProperGeomConnected/Basic.lean` and
`StacksDraft/AlgebraicGeometry/F3/ProperSectionsGeom/{Connected,Separable}.lean` — assert that
degree-zero flat base change for cohomology is absent from Mathlib at the present pin.  That
assertion is false, and `isPushout_appTop` is the witness.

## References

* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.GlobalSectionsBaseChange

/-- `appLE` between the top opens is `appTop`. -/
alias appLE_top_top := Stacks.Descent.appLE_top_top

variable {R L : CommRingCat.{u}} {φ : R ⟶ L} {X Y : Scheme.{u}}
  {iX : X ⟶ Spec R} {p : Y ⟶ X} {iY : Y ⟶ Spec L}

/-- **Degree-zero flat base change.**  If `X` is quasi-compact and quasi-separated over `Spec R`
and `φ : R ⟶ L` is flat, then the global sections of the base change `Y = X ×_{Spec R} Spec L`
are the pushout `Γ(X, ⊤) ⊗_R L`. -/
theorem isPushout_appTop [CompactSpace X] [QuasiSeparatedSpace X]
    (H : IsPullback p iY iX (Spec.map φ)) (hφ : φ.hom.Flat) :
    IsPushout iX.appTop (Spec.map φ).appTop p.appTop iY.appTop := by
  have : AlgebraicGeometry.Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ
  have key := AlgebraicGeometry.isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤) H (le_of_eq (by simp)) (le_of_eq (by simp)) (by simp)
    (isAffineOpen_top _) (isAffineOpen_top _)
    (by rw [TopologicalSpace.Opens.coe_top]; exact isCompact_univ)
    (by rw [TopologicalSpace.Opens.coe_top]; exact isQuasiSeparated_univ)
  have key2 := (AlgebraicGeometry.isIso_pushoutSection_iff ..).mp key
  simpa only [appLE_top_top] using key2

/-- **The base-change square of canonical morphisms to the spectrum of global sections.**  If `X`
is quasi-compact and quasi-separated over `Spec R` and `φ : R ⟶ L` is flat, then
`Y = X ×_{Spec R} Spec L` is the fibre product of `X` and `Spec Γ(Y, ⊤)` over `Spec Γ(X, ⊤)`. -/
theorem isPullback_toSpecΓ [CompactSpace X] [QuasiSeparatedSpace X]
    (H : IsPullback p iY iX (Spec.map φ)) (hφ : φ.hom.Flat) :
    IsPullback p Y.toSpecΓ X.toSpecΓ (Spec.map p.appTop) := by
  have t : IsPullback (Spec.map p.appTop) (Spec.map iY.appTop) (Spec.map iX.appTop)
      (Spec.map (Spec.map φ).appTop) :=
    AlgebraicGeometry.isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_appTop H hφ)
  have t' : IsPullback (Spec.map φ) (Spec L).toSpecΓ (Spec R).toSpecΓ
      (Spec.map (Spec.map φ).appTop) :=
    IsPullback.of_vert_isIso_mono ⟨Scheme.toSpecΓ_naturality _⟩
  refine IsPullback.of_bot ?_ (Scheme.toSpecΓ_naturality p) t
  have h2 := H.paste_vert t'
  rwa [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality] at h2

end Stacks.AlgebraicGeometry.GlobalSectionsBaseChange
