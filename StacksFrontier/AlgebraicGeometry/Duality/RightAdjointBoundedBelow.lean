module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBound
import StacksCore.Tactic.StacksAttribute

/-!
# The right adjoint of `Rf_*` carries bounded-below complexes to bounded-below complexes

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes and let
`a : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` be the right adjoint of `Rf_*` of [Stacks, Tag 0A9E]. Then `a`
carries `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`, and with an explicit bound: there is an integer
`N`, depending on `f` alone, with `H^i(a(K)) = 0` for `i < c - N` whenever `H^i(K) = 0` for
`i < c`.

The proof is the one of [Stacks, Tag 0A9I]. Let `N` be the uniform bound of [Stacks, Tag 08D5]
part (2): `Rf_*L` lives in degrees `≤ b + N` whenever `L` lives in degrees `≤ b`. Write
`c - N = d + 1` and let `E = a(K)`. The truncation `τ_{≤ d}E` again has quasi-coherent cohomology
([Stacks, Tag 0D73], here through `AlgebraicGeometry.isIso_homology_truncLE`), so it is an object
`T` of `D_QCoh(𝒪_X)`, and adjunction identifies

  `Hom_{D_QCoh(𝒪_X)}(T, a(K)) = Hom_{D_QCoh(𝒪_Y)}(Rf_*T, K)`.

The right-hand group vanishes: `Rf_*T` lives in degrees `≤ d + N = c - 1` and `K` in degrees
`≥ c`. So the canonical map `τ_{≤ d}E ⟶ E` is zero, and then every map into `E` out of an object
in degrees `≤ d` is zero, since it factors through that truncation. By
`CategoryTheory.Triangulated.TStructure.isGE_iff_orthogonal` this says exactly that `E` lives in
degrees `≥ d + 1 = c - N`.

## Main results

* `Stacks.Duality.isGE_rightAdjoint_obj` — the statement above, for an arbitrary right adjoint of
  `Rf_*`, a free model of the derived categories, and a given uniform bound.
* `Stacks.Duality.exists_isGE_rightAdjoint_obj` — the same at `HasDerivedCategory.standard`, with
  the uniform bound found by [Stacks, Tag 08D5].
* `Stacks.Duality.isBoundedBelow_rightAdjoint_obj` — the bounded-below consequence at
  `HasDerivedCategory.standard`: `a` carries `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`.

[Stacks, Tag 0A9I] itself, for the right adjoint of [Stacks, Tag 0A9E] and with nothing left to
supply, is `Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_and_exists_bound` of
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BoundedBelow.lean`, which applies
`isGE_rightAdjoint_obj` at the locally small model.

## Implementation notes

*Why the right adjoint is a parameter.* [Stacks, Tag 0A9E] is available as
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward` of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineOpensChaoticQuasicoherentEquality.lean`, but only
at the locally small model and for a quasi-compact target. Tag 0A9I is a statement *about* that
adjoint and is proved here from the adjunction alone, at a free model and with no hypothesis on
the target, so the functor `a` and the adjunction are taken as parameters. Nothing else about `a`
is used; in particular the two statements below are not weakened by it, they are exactly Tag
0A9I's content with its Tag 0A9E input named.

*Why the uniform bound is a parameter in the general form.* `isGE_rightAdjoint_obj` is stated at
a free `[HasDerivedCategory.{w}]` binder, so that it applies at the locally small model — the
only model at which `a` can exist at all, see
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean`. Tag 08D5
is proved only at `HasDerivedCategory.standard`, so at a free model its bound has to be supplied;
`Stacks.Duality.exists_isLE_derivedPushforward_obj` supplies it at `standard`, which is what
`exists_isGE_rightAdjoint_obj` does.

*Quasi-coherence of truncations* is reproved here for a free model, as
`isQuasicoherent_homology_truncLE`. `AlgebraicGeometry.isQuasicoherent_homology_truncLE` is the
same statement with the model fixed at `HasDerivedCategory.standard`, and its proof — the private
`homology_truncLE_property` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedAmplitude/UpperBounds.lean` — is already model-free;
only the three-line specialisation is repeated.

## References

* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w u

namespace Stacks.Duality

section FreeModel

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]

/-- The cohomology of a truncation from above of a complex with quasi-coherent cohomology is
quasi-coherent, for an arbitrary model of the derived category.

This is `AlgebraicGeometry.isQuasicoherent_homology_truncLE` with the model left free; the
argument is the same, that the inclusion of the truncation is an isomorphism on cohomology below
the truncation degree and that the cohomology vanishes above it. -/
theorem isQuasicoherent_homology_truncLE (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (d i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE d).obj E)).IsQuasicoherent := by
  by_cases hi : i ≤ d
  · have := AlgebraicGeometry.isIso_homology_truncLE E d i hi
    exact AlgebraicGeometry.isQuasicoherent_of_iso X _ _
      (asIso ((DerivedCategory.homologyFunctor X.Modules i).map
        ((DerivedCategory.TStructure.t.truncLEι d).app E))).symm (hE i)
  · exact AlgebraicGeometry.isQuasicoherent_of_isZero X _
      (DerivedCategory.isZero_of_isLE _ d i (by omega))

variable (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The argument of [Stacks, Tag 0A9I], for an arbitrary right adjoint of `Rf_*`.** Let
`f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves quasi-coherent
cohomology, and let `a` be a right adjoint of the restriction
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Suppose `N : ℤ` is a uniform bound for `Rf_*`, that is, `Rf_*E` lives in degrees `≤ b + N` for every `E` of `D_QCoh(𝒪_X)` in degrees `≤ b`.
Then `a` carries an object living in degrees `≥ c` to one living in degrees `≥ c - N`.

In particular `a` carries `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`. The case of the twisted inverse
image, which is [Stacks, Tag 0A9I], is
`Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_and_exists_bound`. -/
theorem isGE_rightAdjoint_obj {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a) (N : ℤ)
    (hN : ∀ E : DerivedCategory X.Modules,
      (∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent) →
      ∀ b : ℤ, E.IsLE b → ((derivedPushforward f).obj E).IsLE (b + N))
    (K : quasiCoherentDerivedCategory Y) (c : ℤ) (hK : K.obj.IsGE c) :
    ((a.obj K).obj).IsGE (c - N) := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ, c - N = d + 1 := ⟨c - N - 1, by omega⟩
  -- `T`: the truncation of `a(K)` in degrees `≤ d`, again with quasi-coherent cohomology, so
  -- again an object of `D_QCoh(𝒪_X)`.
  have hTq : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE d).obj (a.obj K).obj)).IsQuasicoherent :=
    fun i ↦ isQuasicoherent_homology_truncLE _ (a.obj K).property d i
  let T : quasiCoherentDerivedCategory X :=
    ⟨(DerivedCategory.TStructure.t.truncLE d).obj (a.obj K).obj, hTq⟩
  -- `Rf_*T` lives in degrees `≤ d + N = c - 1`, while `K` lives in degrees `≥ c`, so every
  -- morphism `Rf_*T ⟶ K` vanishes.
  have hRLE : (((quasiCoherentDerivedPushforward f hpush).obj T).obj).IsLE (d + N) :=
    hN T.obj hTq d inferInstance
  have hzero : ∀ g₁ g₂ : (quasiCoherentDerivedPushforward f hpush).obj T ⟶ K, g₁ = g₂ := by
    intro g₁ g₂
    refine ObjectProperty.hom_ext _ ?_
    rw [DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₁.hom (d + N) c (by omega) hRLE hK,
      DerivedCategory.TStructure.t.zero_of_isLE_of_isGE g₂.hom (d + N) c (by omega) hRLE hK]
  -- Adjunction transports that to the morphisms `T ⟶ a(K)`, so `τ_{≤ d}a(K) ⟶ a(K)` is zero.
  have hsub : ∀ g₁ g₂ : T ⟶ a.obj K, g₁ = g₂ := fun g₁ g₂ ↦
    (adj.homEquiv T K).symm.injective (hzero _ _)
  have hι : (DerivedCategory.TStructure.t.truncLTι (d + 1)).app (a.obj K).obj = 0 :=
    congrArg InducedCategory.Hom.hom
      (hsub (ObjectProperty.homMk
        ((DerivedCategory.TStructure.t.truncLEι d).app (a.obj K).obj))
        (ObjectProperty.homMk 0))
  -- Every morphism into `a(K)` from an object in degrees `≤ d` factors through that truncation.
  rw [hd]
  refine (DerivedCategory.TStructure.t.isGE_iff_orthogonal d (d + 1) rfl _).2 fun Z g hZ ↦ ?_
  have := hZ
  rw [← DerivedCategory.TStructure.t.liftTruncLT_ι g d (d + 1) rfl, hι, comp_zero]

end FreeModel

section Standard

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

/-- **The bound of [Stacks, Tag 0A9I] at the standard model, for an arbitrary right adjoint.**
Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of
schemes with `Y` quasi-compact, along which derived direct image preserves quasi-coherent
cohomology, and let `a` be a right adjoint of the restriction
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then there is an integer
`N`, depending on `f` alone, such that `a` carries an object living in degrees `≥ c` to one
living in degrees `≥ c - N`; in particular `a` carries `D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`.

This is `Stacks.Duality.isGE_rightAdjoint_obj` with the uniform bound discharged by
`Stacks.Duality.exists_isLE_derivedPushforward_obj`, which is [Stacks, Tag 08D5] part (2). The
right adjoint of [Stacks, Tag 0A9E] exists at the locally small model, where the tag is
`Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_and_exists_bound`. -/
theorem exists_isGE_rightAdjoint_obj [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a) :
    ∃ N : ℤ, ∀ (K : quasiCoherentDerivedCategory Y) (c : ℤ),
      K.obj.IsGE c → ((a.obj K).obj).IsGE (c - N) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj f
  exact ⟨N, fun K c hK ↦ isGE_rightAdjoint_obj f hpush adj N hN K c hK⟩

/-- **The bounded-below statement of [Stacks, Tag 0A9I] at the standard model.** In the situation of
`Stacks.Duality.exists_isGE_rightAdjoint_obj`, the right adjoint `a` of `Rf_*` carries
`D^+_QCoh(𝒪_Y)` into `D^+_QCoh(𝒪_X)`: a complex with quasi-coherent cohomology bounded below goes
to one bounded below.

This is the uniform bound applied at a single object, the integer `N` being irrelevant once the
bound on the source is allowed to depend on the object. For the twisted inverse image at the
locally small model this is `Stacks.Duality.isBoundedBelow_twistedInverseImage_obj`. -/
theorem isBoundedBelow_rightAdjoint_obj [QuasiCompact f] [QuasiSeparated f] [CompactSpace Y]
    {a : quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentDerivedPushforward f hpush ⊣ a)
    (K : quasiCoherentDerivedCategory Y)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow ((a.obj K).obj) := by
  obtain ⟨N, hN⟩ := exists_isGE_rightAdjoint_obj f hpush adj
  obtain ⟨n₀, hn₀⟩ := hK
  have hGE : K.obj.IsGE n₀ := (DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hn₀ i hi
  have := hN K n₀ hGE
  exact ⟨n₀ - N, fun n hn ↦ DerivedCategory.isZero_of_isGE _ (n₀ - N) n hn⟩

end Standard

end Stacks.Duality

end
