module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural
public import StacksFrontier.AlgebraicGeometry.AmpleCohomologicalCriterion.Twist
public import StacksFrontier.AlgebraicGeometry.AmplePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Devissage.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic

/-!
# Uniform vanishing of the twists of a family whose coproduct is a direct image

Let `π : X' ⟶ X` be an affine morphism, let `f' : X' ⟶ Spec R` be proper with `R` Noetherian, let
`F'` be a coherent `𝒪_{X'}`-module, and let `L` be an invertible `𝒪_X`-module **whose pullback
`π^* L` is ample on `X'`**. Suppose a family `M : ℕ → X.Modules` has

`∐ₙ Mₙ ≅ π_* F'`.

Then one integer `d₀` makes `Hᵖ(X, Mₙ ⊗ L ^⊗ d) = 0` for every `p > 0`, every `d ≥ d₀` **and
every `n`** at once.

This is the cohomological engine of [Stacks, Tag 0897] part (2) with the comparison of the
cohomology upstairs against the cohomology of the pieces downstairs *proved* rather than assumed:
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/Basic.lean` carries that comparison as the
hypothesis `hcmp`, and all a caller has to supply here is the isomorphism `ε`.

## The argument

The uniformity is not an extra input. [Stacks, Tag 02O1] over the affine base `Spec R` produces
one `d₀` serving every positive degree for the single coherent module `F'` upstairs
(`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`), and the
whole family `(Mₙ)` is accounted for by that one module. Three identifications from the library bring the
vanishing down to `X` and a retract finishes it:

* `(π^* L) ^⊗ d ≅ π^*(L ^⊗ d)` by `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, so the
  twist [Stacks, Tag 02O1] is applied to can be read with the inverse image outside the power;
* `π` is affine, so `Hᵖ(X', -) ≅ Hᵖ(X, π_* -)` on quasi-coherent modules by [Stacks, Tag 089W]
  (`Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp`);
* `L ^⊗ d` is invertible, so the projection formula `π_* F' ⊗ L ^⊗ d ≅ π_*(F' ⊗ π^*(L ^⊗ d))`
  holds with no hypothesis on `π` or `F'` ([Stacks, Tag 0FZE],
  `Stacks.ProjectionFormula.isIso_projectionFormulaMap`);
* finally `Mₙ` is a retract of `∐ₘ Mₘ` — the `n`-th coproduct injection is split by the map that
  is the identity on the `n`-th summand and zero on the others — and
  `Stacks.AlgebraicGeometry.Tag01YQDevissage.isZero_obj_of_isZero_obj_of_retraction` carries that
  retract along `(- ⊗ L ^⊗ d) ⋙ Hᵖ(X, -)`, under which the coproduct goes to a zero object.

No hypothesis on `X` beyond ampleness of `π^* L` on `X'` is used, and `M` is an arbitrary family:
the graded structure of [Stacks, Tag 0897] enters only through `ε`.

## Why ampleness is asked for upstairs, and why that is not the same as asking for it on `X`

The source of [Stacks, Tag 0897] assumes `L` ample on `X` and derives ampleness of `π^* L` from
it, `π` being affine ([Stacks, Tag 0892] part (2),
`Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`). Since that derivation is the only
use the argument makes of ampleness downstairs, the hypothesis below is the derived one. The
resulting statement is strictly more general, and the extra generality is exactly what
[Stacks, Tag 0D2M] needs.

That is worth spelling out, because the weakening looks vacuous and is not. For a **surjective**
affine `π`, ampleness of `π^* L` on `X'` gives ampleness of `L` on `X` back
([Stacks, Tag 0B5V], `Stacks.AmpleFiniteSurjective`), so for such a `π` the two hypotheses do
agree. But the `π` of [Stacks, Tag 0D2M] is not surjective: there the graded algebra is the
associated graded `⨁ₙ 𝓘 ⁿ / 𝓘 ⁿ⁺¹` of an ideal sheaf, whose structure morphism `𝒪_X ⟶ 𝓑` kills
`𝓘`, so the relative spectrum `π : Spec_X(𝓑) ⟶ X` factors through the closed subscheme cut out by
`𝓘` — the fibre `X_y` when `𝓘 = 𝔪 𝒪_X` for the maximal ideal of a local base. Ampleness of
`π^* L` is then available from ampleness of `L` **on the fibre alone**, which is all
[Stacks, Tag 0D2M] grants and all [Stacks, Tag 0D2N] grants it in turn. Stating the engine with
`IsAmple X L` makes it inapplicable there; stating it with `IsAmple X' (π^* L)` does not.

## Main results

* `Stacks.GradedProperCohomology.coprodRetraction`: the retraction `∐ₘ Mₘ ⟶ Mₙ` of the `n`-th
  coproduct injection.
* `Stacks.GradedProperCohomology.exists_isZero_Hgroup_tensorPowTwist_of_coprodIso` — the theorem
  displayed above.

## Implementation notes

**No `stacks` attribute is attached.** This is a step inside the proof of [Stacks, Tag 0897]
part (2), whose site is the statement in
`StacksFrontier/AlgebraicGeometry/GradedProperCohomology/Basic.lean`; it is not a numbered result of
the source.

**The exponent is a natural number.** [Stacks, Tag 02O1] in the form used here and
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` are both stated for natural exponents, and
the bound produced is nonnegative, so nothing is lost; a caller wanting an integer exponent casts
the bound and rewrites along `Stacks.RelativeVeryAmple.tensorPowModuleCongr`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
* [Stacks Project, Tag 0B5V](https://stacks.math.columbia.edu/tag/0B5V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.GradedProperCohomology

/-! ### A summand of a coproduct is a retract of it -/

/-- **The retraction of the `n`-th coproduct injection**: the morphism out of `∐ₘ Mₘ` which is
the identity on the `n`-th summand and zero on every other one. -/
public def coprodRetraction {X : Scheme.{u}} (M : ℕ → X.Modules) (n : ℕ) : (∐ M) ⟶ M n :=
  Sigma.desc fun m => if h : m = n then eqToHom (congrArg M h) else 0

/-- The `n`-th coproduct injection followed by `coprodRetraction M n` is the identity of
`M n`. -/
@[simp]
public theorem ι_comp_coprodRetraction {X : Scheme.{u}} (M : ℕ → X.Modules) (n : ℕ) :
    Sigma.ι M n ≫ coprodRetraction M n = 𝟙 (M n) := by
  rw [coprodRetraction, Sigma.ι_desc, dite_eq_left rfl]
  simp

/-! ### The uniform vanishing -/

/-- **[Stacks, Tag 0897] part (2), with the comparison discharged and ampleness asked for
upstairs.** Let `π : X' ⟶ X` be affine, `f' : X' ⟶ Spec R` proper with `R` Noetherian, `F'` a
coherent `𝒪_{X'}`-module and `L` an invertible `𝒪_X`-module whose pullback `π^* L` is ample on
`X'`. If the coproduct of a family `M : ℕ → X.Modules` is the direct image of `F'` along `π`,
then there is a `d₀` with

`Hᵖ(X, Mₙ ⊗ L ^⊗ d) = 0` for every `p > 0`, every `d ≥ d₀` and every `n`,

one bound serving all three.

The bound is the one [Stacks, Tag 02O1] produces upstairs for `F'` and `π^* L`; see the module
documentation for the steps that bring it down to `X`, and for why ampleness upstairs is a
genuinely weaker hypothesis than ampleness of `L` on `X` for the morphisms
[Stacks, Tag 0D2M] applies this to. -/
public theorem exists_isZero_Hgroup_tensorPowTwist_of_coprodIso {X X' : Scheme.{u}} {R : Type u}
    [CommRing R] [IsNoetherianRing R] (π : X' ⟶ X) [_root_.AlgebraicGeometry.IsAffineHom π]
    (f' : X' ⟶ Spec (CommRingCat.of R)) [IsProper f']
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X' (pullbackModule π L))
    (F' : X'.Modules) [_root_.SheafOfModules.IsCoherent F']
    (M : ℕ → X.Modules) (ε : (∐ M) ≅ (Scheme.Modules.pushforward π).obj F') :
    ∃ d₀ : ℕ, ∀ d p : ℕ, d₀ ≤ d → 0 < p → ∀ n : ℕ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (M n) (tensorPowModule X L (d : ℤ)))) := by
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist f' F'
      (pullbackModule π L) hL
  refine ⟨d₀, fun d p hd hp n => ?_⟩
  -- The twist upstairs, read with the inverse image outside the tensor power.
  have hup : IsZero (Hgroup X'.ringCatSheaf ⊤ p
      (tensorModules X' F' ((Scheme.Modules.pullback π).obj (tensorPowModule X L (d : ℤ))))) :=
    (hd₀ d p hd hp).of_iso ((Hfunctor X'.ringCatSheaf ⊤ p).mapIso
      (tensorModulesMapIso X' (Iso.refl F') (pullbackTensorPowModuleIso π L d)))
  -- Quasi-coherence of that twist, which is what [Stacks, Tag 089W] asks of it.
  have hpow : ((Scheme.Modules.pullback π).obj
      (tensorPowModule X L (d : ℤ))).IsQuasicoherent :=
    (_root_.SheafOfModules.isQuasicoherent X'.ringCatSheaf).prop_of_iso
      (pullbackTensorPowModuleIso π L d).symm
      (Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule
        (pullbackModule π L) (d : ℤ))
  have hqc : (tensorModules X' F'
      ((Scheme.Modules.pullback π).obj (tensorPowModule X L (d : ℤ)))).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent X'.toRingedSpace _ _
      (_root_.isQuasicoherent_of_isCoherent F') hpow
  -- The projection formula for the invertible `L ^⊗ d`, and the comparison it assembles into.
  have : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace).property
      (tensorPowModule X L (d : ℤ)) :=
    Stacks.Ample.isInvertibleModule_tensorPowModule X L (d : ℤ)
  have hpf : IsIso (Stacks.ProjectionFormula.projectionFormulaMap' π.toLRSHom.toShHom F'
      (tensorPowModule X L (d : ℤ))) :=
    Stacks.ProjectionFormula.isIso_projectionFormulaMap π.toLRSHom.toShHom F'
      (tensorPowModule X L (d : ℤ))
  have hcoprod : IsZero (Hgroup X.ringCatSheaf ⊤ p
      (tensorModules X (∐ M) (tensorPowModule X L (d : ℤ)))) :=
    hup.of_iso
      ((Hfunctor X.ringCatSheaf ⊤ p).mapIso
          ((tensorModulesMapIso X ε (Iso.refl (tensorPowModule X L (d : ℤ)))).trans
            (@asIso _ _ _ _ _ hpf)) ≪≫
        (@Stacks.AffineCohomologyPushforward.cohomologyPushforwardIsoApp
          X' X π _ p _ hqc).symm)
  -- `M n` is a retract of the coproduct, and twisting carries that retract along.
  let T : X.Modules ⥤ X.Modules :=
    Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules X
      (tensorPowModule X L (d : ℤ))
  exact Stacks.AlgebraicGeometry.Tag01YQDevissage.isZero_obj_of_isZero_obj_of_retraction
    (Hfunctor X.ringCatSheaf ⊤ p) (T.map (Sigma.ι M n)) (T.map (coprodRetraction M n))
    (((T.map_comp _ _).symm.trans (congrArg T.map (ι_comp_coprodRetraction M n))).trans
      (T.map_id (M n))) hcoprod

end Stacks.GradedProperCohomology

end
