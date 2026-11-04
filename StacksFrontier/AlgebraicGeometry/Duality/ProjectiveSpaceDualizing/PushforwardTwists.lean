module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.BoundedDirectSums
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Trace
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaClosedEmbeddingUnconditional

/-!
# The derived direct image of the twists of the structure sheaf on projective space

Let `S` be a scheme, let `n = m + 1 ≥ 1` and let `f : ℙⁿ_S ⟶ S` be the structure morphism. The
higher direct images of the twists `𝒪(d)` are computed by [Stacks, Tag 01XW] over an arbitrary
base: they vanish outside the degrees `0` and `n`, `f_* 𝒪 = 𝒪_S`, every twist in the band
`-n ≤ d ≤ -1` has no higher direct image at all, and `Rⁿ f_* 𝒪(-n-1) ≅ 𝒪_S` is the trace. Read in
the unbounded derived category, through `H^q(Rf_*(ℱ[a])) = R^{q-a} f_* ℱ`, this says:

* `Rf_*(𝒪(d)[a]) = 0` for `-n ≤ d ≤ -1`;
* `Rf_*(𝒪[a]) ≅ 𝒪_S[a]`;
* `Rf_*(𝒪(-n-1)[a]) ≅ 𝒪_S[a - n]`.

These are the three computations the proof of [Stacks, Tag 0A9W] feeds into the right adjoint of
`Rf_*`.

## Main results

* `Stacks.Duality.ProjectiveSpaceDualizing.isZero_derivedPushforward_twistOver`: the twists in the
  band `-n ≤ d ≤ -1` have zero derived direct image.
* `Stacks.Duality.ProjectiveSpaceDualizing.derivedPushforwardUnitIso`:
  `Rf_*(𝒪_{ℙⁿ_S}[a]) ≅ 𝒪_S[a]`.
* `Stacks.Duality.ProjectiveSpaceDualizing.derivedPushforwardTwistDualizingIso`:
  `Rf_*(𝒪(-n-1)[a]) ≅ 𝒪_S[a + n]` in the cohomological indexing of the single functors, i.e. the
  object is concentrated in degree `a + n`.

## Implementation notes

The derived categories are at a free model `HasDerivedCategory.{w}`, as for
`Stacks.Duality.derivedPushforward` itself; the identification of the cohomology of
`Rf_*(ℱ[a])` with the classical right derived functors is
`Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso`, which holds at every
model. The vanishing statements of the higher direct images are stated with
`CategoryTheory.Functor.rightDerivedPlus` at the standard model and are converted to Mathlib's
`ℕ`-indexed right derived functors by `Stacks.DerivedIndexing.rightDerivedIso`, in a section of its
own so that the standard model never meets the free one.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistZeroIsoUnit)
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

universe w u

namespace Stacks.Duality.ProjectiveSpaceDualizing

variable (m : ℕ) (S : Scheme.{u})

/-! ### The higher direct images in Mathlib's indexing -/

section Classical

attribute [local instance 2000] HasDerivedCategory.standard

/-- A vanishing of `R^q f_*` stated with `rightDerivedPlus` gives the same vanishing in Mathlib's
`ℕ`-indexing. -/
theorem isZero_push_of_isZero_rightDerivedPlus (q : ℕ) (F : (projectiveSpaceOver (m + 1) S).Modules)
    (h : IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
      (q : ℤ)).obj F)) :
    IsZero ((push m S q).obj F) :=
  IsZero.of_iso h ((Stacks.DerivedIndexing.rightDerivedIso
    (Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)) q).app F)

/-- **`R^q f_* 𝒪 = 0` for `q > 0`.** -/
theorem isZero_push_twistOver_zero (q : ℕ) (hq : q ≠ 0) :
    IsZero ((push m S q).obj (twistOver (m + 1) S 0)) := by
  refine isZero_push_of_isZero_rightDerivedPlus m S q _ ?_
  by_cases hqn : q = m + 1
  · subst hqn
    exact isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt m S (by omega)
  · exact MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne (m + 1) S 0 q
      (by exact_mod_cast hq) (by exact_mod_cast hqn)

/-- **`R^q f_* 𝒪(-n-1) = 0` for `q ≠ n`.** -/
theorem isZero_push_twistOver_dualizing (q : ℕ) (hq : q ≠ m + 1) :
    IsZero ((push m S q).obj (twistOver (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1))) := by
  refine isZero_push_of_isZero_rightDerivedPlus m S q _ ?_
  by_cases hq0 : q = 0
  · subst hq0
    exact MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg (m + 1)
      (by omega) S _ (by omega)
  · exact MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne (m + 1) S _ q
      (by exact_mod_cast hq0) (by exact_mod_cast hq)

end Classical

/-! ### The derived direct image -/

variable [HasDerivedCategory.{w} (projectiveSpaceOver (m + 1) S).Modules]
  [HasDerivedCategory.{w} S.Modules]

/-- The cohomology of `Rf_*(ℱ[a])` in a degree `q` vanishes when `R^{q-a} f_* ℱ` does, and below
degree `a` it always vanishes; for an arbitrary morphism of schemes `f`. -/
theorem isZero_homology_derivedPushforward_single {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules] (F : X.Modules)
    (a q : ℤ)
    (h : ∀ k : ℕ, q - a = k → IsZero (((Scheme.Modules.pushforward f).rightDerived k).obj F)) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules q).obj
      ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ a).obj F))) := by
  rcases lt_or_ge q a with hlt | hle
  · have : ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ a).obj F)).IsGE a :=
      Stacks.DerivedFunctor.isGE_totalRightDerived_obj _ _ a
    exact DerivedCategory.isZero_of_isGE _ a q hlt
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, q - a = (k : ℤ) := ⟨(q - a).toNat, by omega⟩
    exact IsZero.of_iso (h k hk)
      ((Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso f a q k hk).app F)

/-- **The twists in the band `-n ≤ d ≤ -1` have zero derived direct image**:
`Rf_*(𝒪(d)[a]) = 0`. -/
theorem isZero_derivedPushforward_twistOver {d : ℤ} (hd₁ : -((m + 1 : ℕ) : ℤ) ≤ d) (hd₂ : d < 0)
    (a : ℤ) :
    IsZero ((derivedPushforward (projectiveSpaceOver (m + 1) S ↘ S)).obj
      ((DerivedCategory.singleFunctor _ a).obj (twistOver (m + 1) S d))) :=
  CategoryTheory.DerivedCategory.isZero_of_forall_isZero_homology fun q =>
    isZero_homology_derivedPushforward_single (projectiveSpaceOver (m + 1) S ↘ S) _ a q fun k _ =>
      isZero_push_twistOver_of_acyclic m S k hd₁ hd₂

/-- An object of the derived category whose cohomology is concentrated in degree `b`, where it is
isomorphic to `M`, is isomorphic to `M[b]`. -/
def isoSingleOfConcentrated {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
    (K : DerivedCategory 𝒜) (b : ℤ) (M : 𝒜)
    (h : ∀ q, q ≠ b → IsZero ((DerivedCategory.homologyFunctor 𝒜 q).obj K))
    (e : (DerivedCategory.homologyFunctor 𝒜 b).obj K ≅ M) :
    K ≅ (DerivedCategory.singleFunctor 𝒜 b).obj M :=
  haveI : K.IsGE b := (DerivedCategory.isGE_iff K b).2 fun q hq => h q (by omega)
  haveI : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun q hq => h q (by omega)
  let Y := (DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K b).choose
  let e₁ : K ≅ (DerivedCategory.singleFunctor 𝒜 b).obj Y :=
    (DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K b).choose_spec.some
  e₁ ≪≫ (DerivedCategory.singleFunctor 𝒜 b).mapIso
    (((DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒜 b).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor 𝒜 b).mapIso e₁.symm ≪≫ e)

/-- **`Rf_*(𝒪_{ℙⁿ_S}[a]) ≅ 𝒪_S[a]`**: the structure sheaf has no higher direct image and
`f_* 𝒪 = 𝒪_S`. -/
def derivedPushforwardUnitIso (a : ℤ) :
    (derivedPushforward (projectiveSpaceOver (m + 1) S ↘ S)).obj
        ((DerivedCategory.singleFunctor _ a).obj
          (Scheme.unitModule (projectiveSpaceOver (m + 1) S))) ≅
      (DerivedCategory.singleFunctor S.Modules a).obj (Scheme.unitModule S) :=
  (derivedPushforward (projectiveSpaceOver (m + 1) S ↘ S)).mapIso
      ((DerivedCategory.singleFunctor _ a).mapIso (twistZeroIsoUnit (m + 1) S).symm) ≪≫
    isoSingleOfConcentrated _ a _
      (fun q hq => isZero_homology_derivedPushforward_single (projectiveSpaceOver (m + 1) S ↘ S)
        _ a q fun k hk =>
        isZero_push_twistOver_zero m S k (by rintro rfl; exact hq (by omega)))
      ((Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso
          (projectiveSpaceOver (m + 1) S ↘ S) a a 0 (by simp)).app _ ≪≫
        pushZeroTwistIso m S)

/-- **`Rf_*(𝒪(-n-1)[a]) ≅ 𝒪_S[a + n]`**: the twist `𝒪(-n-1)` has cohomology only in the top
degree `n`, where the trace identifies it with `𝒪_S`. -/
def derivedPushforwardTwistDualizingIso (a : ℤ) :
    (derivedPushforward (projectiveSpaceOver (m + 1) S ↘ S)).obj
        ((DerivedCategory.singleFunctor _ a).obj
          (twistOver (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1))) ≅
      (DerivedCategory.singleFunctor S.Modules (a + (m + 1 : ℕ))).obj (Scheme.unitModule S) :=
  isoSingleOfConcentrated _ _ _
    (fun q hq => isZero_homology_derivedPushforward_single (projectiveSpaceOver (m + 1) S ↘ S)
      _ a q fun k hk =>
      isZero_push_twistOver_dualizing m S k (by rintro rfl; exact hq (by omega)))
    ((Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso
        (projectiveSpaceOver (m + 1) S ↘ S) a (a + (m + 1 : ℕ)) (m + 1) (by simp)).app _ ≪≫
      trace m S)

end Stacks.Duality.ProjectiveSpaceDualizing

end
