module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreOverField
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPerfection.Assembly
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatUntensoredBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of the fibres of a proper flat module

Let `f : X ⟶ S` be proper and of finite presentation and let `ℱ` be an `𝒪_X`-module of finite
presentation, flat over `S`. Then `s ↦ χ(X_s, ℱ_s)` is locally constant on `S`, and its formation
commutes with base change.

Here `χ(X_s, ℱ_s) = ∑ (-1)ⁿ dim_{κ(s)} Hⁿ(X_s, ℱ_s)` (`AlgebraicGeometry.eulerCharacteristic` is
this sum for a coherent module), with `X_s` the scheme-theoretic fibre and `ℱ_s` the pullback of
`ℱ` to it.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.fibreEulerCharacteristic` — the function
  `s ↦ χ(X_s, ℱ_s)`.

## Main results

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isLocallyConstant_fibreEulerCharacteristic`
  — `s ↦ χ(X_s, ℱ_s)` is locally constant.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.fibreEulerCharacteristic_baseChange` —
  formation of `s ↦ χ(X_s, ℱ_s)` commutes with base change.

## References

* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

attribute [local instance] HasDerivedCategory.standard

/-- The Euler characteristic `∑ (-1)ⁿ dim_K Hⁿ(Y, 𝒢)` of a module on a scheme over a field. -/
def eulerSum (K : Type u) [Field K] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) (G : Y.Modules) : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank K (cohomologyOverField K g G n) : ℤ)

/-- Isomorphic modules on a scheme over a field have the same Euler characteristic. -/
theorem eulerSum_congr (K : Type u) [Field K] {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K))
    {G G' : Y.Modules} (e : G ≅ G') : eulerSum K g G = eulerSum K g G' := by
  refine finsum_congr fun n => ?_
  rw [show Module.finrank K (cohomologyOverField K g G n) =
      Module.finrank K (cohomologyOverField K g G' n) from ?_]
  exact ((ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of K)).inv ≫ g.appLE ⊤ ⊤ (by simp)).hom).mapIso
      (((SheafOfModules.evaluation Y.ringCatSheaf (op (⊤ : Y.Opens))).rightDerived n).mapIso
        e)).toLinearEquiv.finrank_eq

/-- The function `s ↦ χ(X_s, ℱ_s)`: the Euler characteristic of the pullback of `ℱ` to the
scheme-theoretic fibre `X_s`. -/
def fibreEulerCharacteristic {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S) : ℤ :=
  eulerSum (S.residueField s) (f.fiberToSpecResidueField s)
    ((Scheme.Modules.pullback (f.fiberι s)).obj F)

/-- **The derived-fibre Euler characteristic at a field-valued point is the Euler characteristic
of the base change.** For a cartesian square with `p : Spec K ⟶ S`, the derived-fibre Euler
characteristic of `Rf_*ℱ` at the image of the point of `Spec K` is `χ(Y, q^*ℱ)` for the base
change `Y = X ×_S Spec K`. -/
theorem chiDerivedFibre_eq_eulerSum {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
    [IsProper f] (F : X.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (K : Type u) [Field K] (p : Spec (.of K) ⟶ S) {Y : Scheme.{u}} (q : Y ⟶ X)
    (g : Y ⟶ Spec (.of K)) (hsq : IsPullback q g f p) (pt : Spec (.of K)) :
    DerivedFibreBetti.chiDerivedFibre S (derivedPushforwardModule f F)
        (DerivedFibreBetti.isPseudoCoherent_of_isPerfect _
          (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward f hf
            inferInstance F hF hflat)) (p.base pt) =
      eulerSum K g ((Scheme.Modules.pullback q).obj F) := by
  have hpc := DerivedFibreBetti.isPseudoCoherent_of_isPerfect _
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward f hf inferInstance F hF
      hflat)
  obtain ⟨e⟩ := baseChangeDerivedPushforward f p g q hsq hf inferInstance F hF hflat
  have hpc₁ := DerivedFibreBetti.isPseudoCoherent_derivedPullback p _ hpc
  let : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} (Spec (.of K)).toRingedSpace) :=
    HasDerivedCategory.standard (Spec (.of K)).Modules
  have hpc₂ := RingedSpace.IsPseudoCoherent.of_iso.{u, u + 1} hpc₁ e
  have h1 := congrFun (DerivedFibreBetti.chiDerivedFibre_derivedPullback p _ hpc) pt
  rw [Function.comp_apply] at h1
  rw [← h1, DerivedFibreBetti.chiDerivedFibre_congr _ hpc₁ hpc₂ e,
    DerivedFibreOverField.chiDerivedFibre_derivedPushforwardModule K g _ hpc₂ pt]
  rfl

/-- The derived-fibre Euler characteristic of `Rf_*ℱ` at the image of `s'` under `g : S' ⟶ S` is
the Euler characteristic of the pullback of `ℱ` to the fibre of the base change `f'` at `s'`. -/
private theorem chiDerivedFibre_base_apply_eq_eulerSum {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g)
    (hf : FinitePresentation f) [IsProper f] (F : X.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (s' : S') :
    DerivedFibreBetti.chiDerivedFibre S (derivedPushforwardModule f F)
        (DerivedFibreBetti.isPseudoCoherent_of_isPerfect _
          (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward f hf
            inferInstance F hF hflat)) (g.base s') =
      eulerSum (S'.residueField s') (f'.fiberToSpecResidueField s')
        ((Scheme.Modules.pullback (f'.fiberι s' ≫ g')).obj F) := by
  have hpaste : IsPullback (f'.fiberι s' ≫ g') (f'.fiberToSpecResidueField s') f
      (S'.fromSpecResidueField s' ≫ g) :=
    (IsPullback.of_hasPullback f' (S'.fromSpecResidueField s')).paste_horiz hsq
  have h := chiDerivedFibre_eq_eulerSum f hf F hF hflat (S'.residueField s')
    (S'.fromSpecResidueField s' ≫ g) (f'.fiberι s' ≫ g') (f'.fiberToSpecResidueField s') hpaste
    (IsLocalRing.closedPoint _)
  have hpt : (S'.fromSpecResidueField s' ≫ g).base (IsLocalRing.closedPoint _) = g.base s' :=
    congrArg g.base (S'.fromSpecResidueField_apply s' _)
  rwa [hpt] at h

/-- The function `s ↦ χ(X_s, ℱ_s)` is the derived-fibre Euler characteristic of `Rf_*ℱ`. -/
theorem fibreEulerCharacteristic_eq_chiDerivedFibre {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) [IsProper f] (F : X.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    fibreEulerCharacteristic f F =
      DerivedFibreBetti.chiDerivedFibre S (derivedPushforwardModule f F)
        (DerivedFibreBetti.isPseudoCoherent_of_isPerfect _
          (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward f hf
            inferInstance F hF hflat)) := by
  funext s
  simpa [fibreEulerCharacteristic] using
    (chiDerivedFibre_base_apply_eq_eulerSum f (𝟙 S) f (𝟙 X) IsPullback.of_id_fst hf F hF hflat
      s).symm

/-- For `f : X ⟶ S` proper and of finite presentation and `ℱ` an `𝒪_X`-module of finite
presentation, flat over `S`, the function `s ↦ χ(X_s, ℱ_s)` is locally constant on `S`. -/
@[stacks 0B9T "local constancy of s |-> chi(X_s, F_s)",
  ega "III 7.9.4" "special case",
  ega "III 7.9.5" "special case"]
theorem isLocallyConstant_fibreEulerCharacteristic {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : FinitePresentation f) [IsProper f] (F : X.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsLocallyConstant (fibreEulerCharacteristic f F) := by
  rw [fibreEulerCharacteristic_eq_chiDerivedFibre f hf F hF hflat]
  exact DerivedFibreBetti.isLocallyConstant_chiDerivedFibre S _
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward f hf inferInstance F hF
      hflat)

/-- Formation of `s ↦ χ(X_s, ℱ_s)` commutes with base change: for a cartesian square with
`g : S' ⟶ S`, the function attached to the base change `f' : X' ⟶ S'` and `(g')^*ℱ` is the
function attached to `f` and `ℱ`, composed with `g`. -/
@[stacks 0B9T "formation of s |-> chi(X_s, F_s) commutes with base change",
  ega "III 7.9.7" "special case"]
theorem fibreEulerCharacteristic_baseChange {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (f' : X' ⟶ S') (g' : X' ⟶ X) (hsq : IsPullback g' f' f g) (hf : FinitePresentation f)
    [IsProper f] (F : X.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    fibreEulerCharacteristic f' ((Scheme.Modules.pullback g').obj F) =
      fibreEulerCharacteristic f F ∘ g.base := by
  funext s'
  rw [Function.comp_apply, fibreEulerCharacteristic_eq_chiDerivedFibre f hf F hF hflat,
    chiDerivedFibre_base_apply_eq_eulerSum f g f' g' hsq hf F hF hflat s', fibreEulerCharacteristic]
  exact eulerSum_congr _ _ ((Scheme.Modules.pullbackComp (f'.fiberι s') g').app F)

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end
