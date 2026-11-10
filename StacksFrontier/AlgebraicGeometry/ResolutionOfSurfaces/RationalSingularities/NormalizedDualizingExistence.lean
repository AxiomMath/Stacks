module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeExtra
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.FibreDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingModule
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StalkVanishingCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
import StacksCore.Tactic.StacksAttribute

/-!
# The twisted inverse image, and the normalization of [Stacks, Remark 0B4R], at a modification

In Situation [Stacks, Tag 0B4W] the modification `f : X ⟶ Spec(A)` is proper, hence
quasi-compact and quasi-separated, and its target is quasi-compact. So [Stacks, Tag 0A9E] applies
unconditionally: `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec A})` has a right adjoint, and the twisted
inverse image `f^! = Stacks.Duality.twistedInverseImage` is available at `f`. This file records
that instance and the facts about `Rf_*` that reading Grothendieck duality in a single degree
needs.

Against that `f^!` it then states the normalization of [Stacks, Remark 0B4R]: `ω_X` is *the*
dualizing module of `X` normalized relative to `ω_A` when `ω_X[2]` is the dualizing complex
normalized relative to `ω_A[2]`, equivalently — `f^!` commuting with the shift, being the right
adjoint of a functor that does — when `ω_X ≅ f^!(ω_A)` with both sides in degree zero. That is
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization`, and two things are
proved about it: a module normalized in this sense satisfies the degree-zero condition
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule`, so the development
resting on that condition applies to it; and the normalization determines `ω_X` up to
isomorphism, with no vanishing involved, which the degree-zero condition does not do.

## Main definitions

* `AlgebraicGeometry.RationalSingularitySituation.derivedPushforwardUnit` — the comparison from
  degreewise direct image to `Rf_*`.
* `AlgebraicGeometry.RationalSingularitySituation.baseDualizingComplex` and
  `.relativeDualizingComplex` — the dualizing module of the base in degree zero, and `f^!` of it.
* `AlgebraicGeometry.RationalSingularitySituation.pushforwardSingle` — `Rf_*(ℱ[0])`.
* `AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization` —
  **[Stacks, Remark 0B4R]**: `ω_X` dualizing together with `f^!(ω_A) ≅ ω_X` in degree zero.
* `AlgebraicGeometry.RationalSingularitySituation.relativeDualizingTrace` — the counit
  `Rf_*(f^!ω_A) ⟶ ω̃_A` of `Rf_* ⊣ f^!`, read in `D(𝒪_{Spec A})`.
* `AlgebraicGeometry.RationalSingularitySituation.normalizationPairing` and
  `.normalizationTrace` — the degree-zero duality pairing attached to a morphism
  `ω_X ⟶ f^!ω_A`, and its value at the identity of `ω_X`.
* `AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization.moduleIso` — the
  isomorphism between two modules normalized relative to the same `ω_A`.

## Main results

* `AlgebraicGeometry.RationalSingularitySituation.isLeftAdjoint_derivedPushforward` —
  **[Stacks, Tag 0A9E] at `f`**, as an instance, so that `Stacks.Duality.twistedInverseImage` and
  `Stacks.Duality.relativeDualizingComplexHomEquiv` can be read at the modification.
* `AlgebraicGeometry.RationalSingularitySituation.isZero_rightDerived_pushforward_of_pos` — the
  higher direct images of a quasi-coherent module vanish in positive degrees as soon as the first
  cohomology does: in degree one this is the hypothesis, and above degree one it is the fibre
  dimension of `f`, which is at most one.
* `AlgebraicGeometry.RationalSingularitySituation.isZero_homology_derivedPushforward_single` —
  `Rf_*(ℱ[0])` has no cohomology outside degree zero, for such an `ℱ`.
* `AlgebraicGeometry.RationalSingularitySituation.derivedPushforwardSingleIso` —
  `H⁰(Rf_*(ℱ[0])) ≅ f_*ℱ`, naturally in `ℱ`, with no vanishing hypothesis: direct image is left
  exact, so it is its own zeroth right derived functor.
* `AlgebraicGeometry.bijective_moduleSpecΓFunctor_map` — `Hom_{𝒪_{Spec R}}(𝒢, Ñ)` is
  `Hom_R(Γ(Spec R, 𝒢), N)` for a quasi-coherent `𝒢`, by global sections.
* `AlgebraicGeometry.RationalSingularitySituation.normalizationPairing_eq` — the duality
  pairing of `c : ω_X ⟶ f^!ω_A` at `φ` is the global sections of `φ` followed by its trace.
* `AlgebraicGeometry.RationalSingularitySituation.bijective_normalizationPairing` — for an
  invertible `c` the pairing is bijective against every quasi-coherent `ℱ` with `H¹(X, ℱ) = 0`.
* `AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization`
  `.normalizedDualizingModule` — a module normalized in the sense of [Stacks, Remark 0B4R]
  satisfies the degree-zero condition `NormalizedDualizingModule`.
* `AlgebraicGeometry.RationalSingularitySituation`
  `.isEmpty_dualizingNormalization_of_not_isIsomorphic` — of two non-isomorphic modules at most
  one is normalized relative to a given `ω_A`.

Together with `DerivedCategory`
`.bijective_homologyFunctor_map_comp_singleFunctorCompHomologyFunctorIso`
these are the four bijections whose composition is relative duality in degree zero for a module
`ω_X` with `ω_X ≅ f^! ω_A`: placing a morphism in degree zero is bijective because the single
functor is fully faithful, Grothendieck duality is the adjunction of
`isLeftAdjoint_derivedPushforward`, degree-zero cohomology is bijective against a module in
degree zero because `Rf_*(ℱ[0])` is concentrated there, and global sections is the last one.

## Implementation notes

**Two models of the derived category.** `Stacks.Duality.derivedPushforward` and the right adjoint
of [Stacks, Tag 0A9E] are read at `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, the
locally small model: Brown representability needs direct sums indexed by the morphism universe,
and at `HasDerivedCategory.standard` those do not exist. The cohomology vanishing results this
file consumes are stated at `HasDerivedCategory.standard`. The two are crossed through
`CategoryTheory.Functor.rightDerived`, the derived functor computed by injective resolutions,
which mentions no derived category at all:
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` compares it to `Functor.rightDerivedPlus` at
whichever model is in scope, so applying it at the standard model and again at the locally small
one transports a vanishing between them. Every statement below whose shape allows it is therefore
phrased with `Functor.rightDerived` and a natural-number degree.

**Fibre dimension.** `AlgebraicGeometry.RationalSingularitySituation`
`.topologicalKrullDim_fiber_le_one` is the bound `dim(X_y) ≤ 1` for every `y`, so
[Stacks, Tag 0E7D] over the affine base — that is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange`
`.isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_affineBase` — gives `H^i(X, ℱ) = 0` for
`i ≥ 2` with no further hypothesis. Only `H¹` is left, and that is the hypothesis of the
normalization condition.

## Why `ω_X` is not constructed here

`f^!` is available at the modification — `isLeftAdjoint_derivedPushforward` below is [Stacks, Tag
0A9E] at `S.f`, so `Stacks.Duality.twistedInverseImage` reads here with nothing assumed, and
`relativeDualizingComplex` is `f^!ω_A`. What is **not** available is either of the two properties
that `NormalizedDualizingModule.isDualizing` needs of it.

*Dualizingness.* The only route to "`f^!` of a dualizing complex is dualizing" is [Stacks, Tag
0AU3]/[Stacks, Tag 0AA3], which is `Stacks.Duality.isDualizingComplex_upperShriek_of_fts` — but
with `f^!` an opaque functor parameter characterised by the affine-chart description of
[Stacks, Tag 0AA1] and [Stacks, Tag 0BV2], carried there as `h0AA1`. That hypothesis is **not
provable** for `Stacks.Duality.twistedInverseImage`: restricting `f^×` to an affine open `U ⊆ X`
would need `j^! = j^*` for the open immersion `j`, and `j^× ≠ j^*`, since the right adjoint of
`Rj_*` is coinduction rather than localisation — concretely `a(k[t]) ≠ k[t, 1/t]` for
`U = D(t) ⊆ Spec k[t]`. The identification `j^! = j^*` is [Stacks, Tag 0AU0], a statement about the
*compactification* construction of `f^!`, not about the right adjoint of `Rj_*`.

*Concentration in degree zero.* Even granted dualizingness, `f^!ω_A ≅ ω_X[0]` is Duality for
Schemes, Lemma 48.23.1 at scheme level. The ring-level [Stacks, Tag 0AWS] is
`Dualizing.isCohenMacaulay_tfae_dualizingComplex`, and `X` is Cohen–Macaulay by
`isCohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two`, but the degree is pinned only by the
normalization itself: duality against `𝒪_X` together with `R¹f_*𝒪_X = 0` puts the lowest
nonvanishing degree of `f^×(ω_A[2])` at `≤ -2`, and the amplitude `[0,1]` of `Rf_*` puts it at
`≥ -3`; dualizingness alone does not exclude `-3`.

Neither obstruction touches the *statement* of the normalization: `DualizingNormalization` asks
for a dualizing `ω_X` and an isomorphism `f^!(ω_A) ≅ ω_X`, and both are written down with `f^!`
the functor `Stacks.Duality.twistedInverseImage`. Of the two halves of [Stacks, Remark 0B4R] at a
modification — the normalization condition and the existence of a module satisfying it — this
file treats the first, and the normalization enters [Stacks, Tag 0B64] as the datum the source
itself supplies when it writes "`ω_X` the dualizing module of `X`".

**What the normalization adds over the degree-zero condition.** `NormalizedDualizingModule` is
the special case of Grothendieck duality that `DualizingNormalization` implies, by
`DualizingNormalization.normalizedDualizingModule`; the implication does not reverse, and the
counterexample is in the implementation notes of `NormalizedDualizingModule`. The separation is
`DualizingNormalization.moduleIso`: a module normalized in the sense of the remark is determined
up to isomorphism outright, because the functor placing a module in degree zero is fully
faithful, so two normalized modules are both `f^!(ω_A)` read in degree zero. The degree-zero
condition determines `ω_X` only inside `{ω_X : H¹(X, ω_X) = 0}`, which is exactly why clause (2)
of [Stacks, Tag 0B64] cannot be proved from it and carries `hcurve` there.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0AUA](https://stacks.math.columbia.edu/tag/0AUA)
* [Stacks Project, Tag 0AA2](https://stacks.math.columbia.edu/tag/0AA2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open Stacks.Duality (isQuasicoherent_homology_derivedPushforward_of_qcqs)
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Duality (singleQuasiCoherent)
open Stacks.Cohomology.AffineBase (moduleGlobalSections)
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace AlgebraicGeometry

/-! ### Morphisms into the sheaf associated with a module -/

/-- Precomposition with an isomorphism is bijective. -/
private theorem bijective_comp_left_of_isIso {C : Type*} [Category C] {X Y Z : C} (e : X ⟶ Y)
    [IsIso e] : Function.Bijective (fun v : Y ⟶ Z => e ≫ v) :=
  ⟨fun _ _ h => (cancel_epi e).1 h, fun u => ⟨inv e ≫ u, by simp⟩⟩

/-- Postcomposition with an isomorphism is bijective. -/
private theorem bijective_comp_right_of_isIso {C : Type*} [Category C] {X Y Z : C} (c : Y ⟶ Z)
    [IsIso c] : Function.Bijective (fun u : X ⟶ Y => u ≫ c) :=
  ⟨fun _ _ h => (cancel_mono c).1 h, fun v => ⟨v ≫ inv c, by simp⟩⟩

/-- **`Hom_{𝒪_{Spec R}}(𝒢, Ñ) = Hom_R(Γ(Spec R, 𝒢), N)` for a quasi-coherent `𝒢`.** The map is
global sections, read through `Γ(Spec R, Ñ) = N`. The associated-sheaf functor is fully faithful
and a quasi-coherent module is the sheaf associated with its own global sections, so the two
sides have the same morphisms; as in
`DerivedCategory.bijective_homologyFunctor_map_comp_singleFunctorCompHomologyFunctorIso`, the
non-canonical ingredient appears only in the proof. -/
theorem bijective_moduleSpecΓFunctor_map {R : CommRingCat.{u}}
    (G : (Spec R).Modules) [G.IsQuasicoherent] (N : ModuleCat.{u} R) :
    Function.Bijective (fun v : G ⟶ (tilde.functor R).obj N =>
      moduleSpecΓFunctor.map v ≫ (tilde.toTildeΓNatIso.app N).inv) := by
  let := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent G
  let e := asIso (Scheme.Modules.fromTildeΓ G)
  let ρ : moduleSpecΓFunctor.obj G ≅ moduleSpecΓFunctor.obj G :=
    moduleSpecΓFunctor.mapIso e.symm ≪≫
      (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj G)).symm
  have hρhom : ρ.hom = moduleSpecΓFunctor.map e.inv ≫
      (tilde.toTildeΓNatIso.app (moduleSpecΓFunctor.obj G)).inv := rfl
  have hτ : Function.Bijective (fun w : moduleSpecΓFunctor.obj G ⟶ N =>
      e.inv ≫ (tilde.functor R).map w) :=
    (bijective_comp_left_of_isIso (Z := (tilde.functor R).obj N) e.inv).comp
      ⟨(tilde.functor R).map_injective, (tilde.functor R).map_surjective⟩
  have hcomp : (fun v : G ⟶ (tilde.functor R).obj N =>
        moduleSpecΓFunctor.map v ≫ (tilde.toTildeΓNatIso.app N).inv) ∘
      (fun w : moduleSpecΓFunctor.obj G ⟶ N => e.inv ≫ (tilde.functor R).map w) =
      fun w : moduleSpecΓFunctor.obj G ⟶ N => ρ.hom ≫ w := by
    funext w
    have hnat := tilde.toTildeΓNatIso.inv.naturality w
    rw [hρhom]
    simp only [Function.comp_apply]
    exact congrArg (moduleSpecΓFunctor.map e.inv ≫ ·) hnat
  refine (Function.Bijective.of_comp_iff _ hτ).1 ?_
  rw [hcomp]
  exact bijective_comp_left_of_isIso ρ.hom

namespace RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

/-! ### The twisted inverse image at the modification -/

/-- **[Stacks, Tag 0A9E] at the modification.** `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_{Spec A})` has a
right adjoint, the twisted inverse image `f^!`. -/
instance isLeftAdjoint_derivedPushforward :
    (Stacks.Duality.quasiCoherentDerivedPushforward S.f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)).IsLeftAdjoint :=
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward S.f

/-- The comparison from degreewise direct image to `Rf_*`, the unit exhibiting `Rf_*` as a total
right derived functor. -/
abbrev derivedPushforwardUnit :
    (Scheme.Modules.pushforward S.f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ Stacks.Duality.derivedPushforward S.f :=
  (Stacks.Duality.homotopyPushforward S.f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso S.X.Modules (ComplexShape.up ℤ))

/-! ### Vanishing of the higher direct images -/

/-- **The higher direct images of a quasi-coherent module vanish in positive degrees as soon as
the first cohomology does.** In degree one the conclusion is the hypothesis, read through the
affine base; above degree one it is [Stacks, Tag 0E7D], the fibres of `f` having dimension at
most one.

The hypothesis and the conclusion are both about `CategoryTheory.Functor.rightDerived`, which
does not mention a derived category; see this module's implementation notes. -/
theorem isZero_rightDerived_pushforward_of_pos (F : S.X.Modules) (hF : F.IsQuasicoherent)
    (hH : IsZero (((moduleGlobalSections S.X).rightDerived 1).obj F)) (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward S.f).rightDerived n).obj F) := by
  let := HasDerivedCategory.standard S.X.Modules
  let := HasDerivedCategory.standard S.base.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, ⊤))
  let : F.IsQuasicoherent := hF
  have hcoh : IsZero (((moduleGlobalSections S.X).rightDerivedPlus (n : ℤ)).obj F) := by
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      exact hn1 ▸ (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 F).1 hH
    · exact isZero_rightDerivedPlus_of_forall_fiber_dim_le_of_affineBase S.f 1
        (fun y => S.topologicalKrullDim_fiber_le_natCast_one y) (n : ℤ)
        (by exact_mod_cast h2) F hF
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n F).2
    ((isZero_cohomology_iff_isZero_rightDerivedPlus_pushforward S.f (n : ℤ) F).1 hcoh)

/-- **`Rf_*(ℱ[0])` has no cohomology outside degree zero.** Below degree zero this is left
t-exactness of a right derived functor; above it, it is the vanishing of the higher direct images
of `ℱ`, which `isZero_rightDerived_pushforward_of_pos` supplies.

The crossing between the two models of the derived category happens here: the hypothesis speaks
of `Functor.rightDerived`, and `isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus` consumes
`Functor.rightDerivedPlus` at the model of the conclusion. -/
theorem isZero_homology_derivedPushforward_single (F : S.X.Modules) (hF : F.IsQuasicoherent)
    (hH : IsZero (((moduleGlobalSections S.X).rightDerived 1).obj F)) (j : ℤ) (hj : j ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor S.base.Modules j).obj
      ((Stacks.Duality.derivedPushforward S.f).obj
        ((DerivedCategory.singleFunctor S.X.Modules 0).obj F))) := by
  rcases lt_or_gt_of_ne hj with hneg | hpos
  · exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (Scheme.Modules.pushforward S.f) ((DerivedCategory.singleFunctor S.X.Modules 0).obj F) 0
      j hneg
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    refine isZero_homologyFunctor_obj_of_isZero_rightDerivedPlus
      (Scheme.Modules.pushforward S.f) (Stacks.Duality.derivedPushforward S.f)
      S.derivedPushforwardUnit
      (fun I hI => isIso_app_isKInjective_of_isRightDerivedFunctor S.X _ _ _ I hI) F _ ?_
    exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n F).1
      (S.isZero_rightDerived_pushforward_of_pos F hF hH n (by exact_mod_cast hpos))

/-- **`H⁰(Rf_*(ℱ[0])) ≅ f_*ℱ`, naturally in `ℱ`.** Direct image is left exact, so it is its own
zeroth right derived functor; no vanishing hypothesis is involved. -/
def derivedPushforwardSingleIso :
    DerivedCategory.singleFunctor S.X.Modules 0 ⋙ Stacks.Duality.derivedPushforward S.f ⋙
        DerivedCategory.homologyFunctor S.base.Modules 0 ≅ Scheme.Modules.pushforward S.f :=
  Stacks.DerivedFunctor.derivedDegreeNatIsoOfKInjective (Scheme.Modules.pushforward S.f)
    (Stacks.Duality.derivedPushforward S.f) S.derivedPushforwardUnit
    (fun _ => Stacks.DerivedFunctor.isGE_totalRightDerived_obj _ _ 0)
    (Scheme.Modules.exists_quasiIso_isKInjective S.X) 0

/-! ### Relative duality in degree zero -/

/-- **The dualizing module of the base, in degree zero.** This is the object `ω_A[2]` of
[Stacks, Remark 0B4R] with the shift `[-2]` applied: `f^!` commutes with the shift, being the
right adjoint of a functor that does, so asking `ω_X[2] ≅ f^!(ω_A[2])` is asking
`ω_X ≅ f^!(ω_A)` with both modules in degree zero, and the latter mentions no shift. -/
def baseDualizingComplex (ωA : ModuleCat.{u} S.A) :
    Stacks.Duality.quasiCoherentDerivedCategory S.base :=
  singleQuasiCoherent ((tilde.functor (.of S.A)).obj ωA) inferInstance 0

/-- **The relative dualizing complex of the situation**, `f^! ω_A` — the twisted inverse image of
[Stacks, Tag 0A9E] applied to the dualizing module of the base in degree zero. -/
abbrev relativeDualizingComplex (ωA : ModuleCat.{u} S.A) :
    Stacks.Duality.quasiCoherentDerivedCategory S.X :=
  Stacks.Duality.relativeDualizingComplex S.f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f) (S.baseDualizingComplex ωA)

/-- `Rf_*(ℱ[0])`, as an object of `D_QCoh(𝒪_{Spec A})`. -/
abbrev pushforwardSingle (F : S.X.Modules) (hF : F.IsQuasicoherent) :
    Stacks.Duality.quasiCoherentDerivedCategory S.base :=
  (Stacks.Duality.quasiCoherentDerivedPushforward S.f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)).obj
    (singleQuasiCoherent F hF 0)

/-- `pushforwardSingle` read in `D(𝒪_{Spec A})` is `Rf_*` applied to `ℱ` placed in degree zero. -/
theorem pushforwardSingle_obj (F : S.X.Modules) (hF : F.IsQuasicoherent) :
    (S.pushforwardSingle F hF).obj = (Stacks.Duality.derivedPushforward S.f).obj
      ((DerivedCategory.singleFunctor S.X.Modules 0).obj F) :=
  rfl

/-! ### The normalization of [Stacks, Remark 0B4R] -/

section Normalization

variable [IsLocallyNoetherian S.X]

/-- **The dualizing module of `X` normalized relative to `ω_A`** of [Stacks, Remark 0B4R]: a
dualizing module `ω_X` on `X` together with an isomorphism `f^!(ω_A) ≅ ω_X` in `D_QCoh(𝒪_X)`,
both sides placed in degree zero.

The source asks that `ω_X[2]` be the dualizing complex normalized relative to `ω_A[2]`. The
twisted inverse image commutes with the shift, being the right adjoint of a functor that does,
so `ω_X[2] ≅ f^!(ω_A[2])` is `ω_X ≅ f^!(ω_A)` with both modules in degree zero; `ω_A` in degree
zero is `baseDualizingComplex` and `f^!` of it is `relativeDualizingComplex`, the twisted inverse
image of [Stacks, Tag 0A9E] at the modification, which `isLeftAdjoint_derivedPushforward` makes
available with nothing assumed.

The `f^!` here is `Stacks.Duality.twistedInverseImage`, not a functor described by its
restriction to affine charts: no clause of [Stacks, Tag 0AU3] enters either this definition or
anything proved about it below.

**What the source's "normalized relative to" is.** [Stacks, Definition 0AUA] builds the
dualizing complex normalized relative to `ω_S^•` on a finite type `S`-scheme by glueing
`(U ⟶ S)^!ω_S^•` over the opens `U` separated over `S`, and records that for an `X` itself
separated over `S` the result is `p^!ω_S^•` for the structure morphism `p`. A modification is
proper, hence separated, so for `f : X ⟶ Spec(A)` the normalized dualizing complex is
`f^!(ω_A^•)` and the condition below is the source's. The remaining identification — that for a
proper morphism the `f^!` of [Stacks, Section 48.16] is the right adjoint of `Rf_*`, which is
what `Stacks.Duality.twistedInverseImage` is — is [Stacks, Tag 0AA2]; the condition below is
stated against that right adjoint, the characterisation that makes the normalization say
something, and the two are equivalent because a right adjoint is unique up to canonical
isomorphism. -/
structure DualizingNormalization (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules) where
  /-- `ω_X` is a dualizing module on `X`. -/
  isDualizing : Stacks.Duality.IsDualizingModule ωX
  /-- The normalization `f^!(ω_A) ≅ ω_X`, both sides in degree zero. -/
  normalizedIso : (S.relativeDualizingComplex ωA).obj ≅
    (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX

/-- The trace `Rf_*(f^!ω_A) ⟶ ω̃_A`, as a morphism of `D(𝒪_{Spec A})`: the counit of
`Rf_* ⊣ f^!` at `ω_A` in degree zero, read through the inclusion of `D_QCoh(𝒪_{Spec A})`. -/
abbrev relativeDualizingTrace (ωA : ModuleCat.{u} S.A) :
    (Stacks.Duality.derivedPushforward S.f).obj (S.relativeDualizingComplex ωA).obj ⟶
      (DerivedCategory.singleFunctor S.base.Modules 0).obj
        ((tilde.functor (CommRingCat.of S.A)).obj ωA) :=
  (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace S.f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f) (S.baseDualizingComplex ωA))

/-- The degree-zero duality pairing attached to a morphism `c : ω_X ⟶ f^!ω_A` of
`D_QCoh(𝒪_X)`, both sides in degree zero: it sends `φ : ℱ ⟶ ω_X` to the `A`-linear map
`H⁰(X, ℱ) ⟶ ω_A` obtained by placing `φ` in degree zero, composing with `c`, applying
Grothendieck duality, and reading the result in degree zero over the affine base.

Nothing is assumed of `c` or of `ℱ` here, so the pairing is defined for every `ℱ`.
`normalizationPairing_eq` says the pairing at `φ` is the global sections of `φ` followed by the
trace, and `bijective_normalizationPairing` says that each of its steps, hence the pairing, is
bijective once `c` is invertible and `ℱ` is quasi-coherent with vanishing first cohomology. -/
def normalizationPairing (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules)
    (c : (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX ⟶
      (S.relativeDualizingComplex ωA).obj)
    (F : S.X.Modules) (φ : F ⟶ ωX) : S.globalSectionsModule F ⟶ ωA :=
  moduleSpecΓFunctor.map ((S.derivedPushforwardSingleIso.app F).inv ≫
    (DerivedCategory.homologyFunctor S.base.Modules 0).map
      ((Stacks.Duality.derivedPushforward S.f).map
        ((DerivedCategory.singleFunctor S.X.Modules 0).map φ ≫ c) ≫
          S.relativeDualizingTrace ωA) ≫
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso S.base.Modules 0).app
      ((tilde.functor (CommRingCat.of S.A)).obj ωA)).hom) ≫
  ((tilde.toTildeΓNatIso (R := CommRingCat.of S.A)).app ωA).inv

/-- The trace `H⁰(X, ω_X) ⟶ ω_A` attached to a morphism `c : ω_X ⟶ f^!ω_A`: the duality
pairing of `c` with the identity of `ω_X`, written out. That it *is* the pairing at the identity
is `normalizationTrace_eq_pairing_id`. -/
def normalizationTrace (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules)
    (c : (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX ⟶
      (S.relativeDualizingComplex ωA).obj) : S.globalSectionsModule ωX ⟶ ωA :=
  moduleSpecΓFunctor.map ((S.derivedPushforwardSingleIso.app ωX).inv ≫
    (DerivedCategory.homologyFunctor S.base.Modules 0).map
      ((Stacks.Duality.derivedPushforward S.f).map c ≫ S.relativeDualizingTrace ωA) ≫
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso S.base.Modules 0).app
      ((tilde.functor (CommRingCat.of S.A)).obj ωA)).hom) ≫
  ((tilde.toTildeΓNatIso (R := CommRingCat.of S.A)).app ωA).inv

omit [IsLocallyNoetherian S.X] in
/-- Global sections over `Spec(A)` of the direct image of a morphism is its global sections
over `X`, as a map of `A`-modules. -/
theorem moduleSpecΓFunctor_map_pushforward_map {F G : S.X.Modules} (φ : F ⟶ G) :
    moduleSpecΓFunctor.map ((Scheme.Modules.pushforward S.f).map φ) = S.globalSectionsMap φ :=
  rfl

omit [IsLocallyNoetherian S.X] in
/-- **The duality pairing of `c` is composition with its trace.** Every step of the pairing is
either a functor applied to `φ` or composition with a morphism not depending on `φ`, so the
pairing is natural in `ℱ`; its value at `φ` is therefore its value at the identity of `ω_X`
precomposed with the global sections of `φ`. -/
theorem normalizationPairing_eq (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules)
    (c : (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX ⟶
      (S.relativeDualizingComplex ωA).obj)
    (F : S.X.Modules) (φ : F ⟶ ωX) :
    S.normalizationPairing ωA ωX c F φ =
      S.globalSectionsMap φ ≫ S.normalizationTrace ωA ωX c := by
  have hpre : (S.derivedPushforwardSingleIso.app F).inv ≫
      (DerivedCategory.homologyFunctor S.base.Modules 0).map
        ((Stacks.Duality.derivedPushforward S.f).map
          ((DerivedCategory.singleFunctor S.X.Modules 0).map φ)) =
      (Scheme.Modules.pushforward S.f).map φ ≫ (S.derivedPushforwardSingleIso.app ωX).inv :=
    (S.derivedPushforwardSingleIso.inv.naturality φ).symm
  have hinner : (S.derivedPushforwardSingleIso.app F).inv ≫
      (DerivedCategory.homologyFunctor S.base.Modules 0).map
        ((Stacks.Duality.derivedPushforward S.f).map
          ((DerivedCategory.singleFunctor S.X.Modules 0).map φ ≫ c) ≫
            S.relativeDualizingTrace ωA) ≫
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso S.base.Modules 0).app
        ((tilde.functor (CommRingCat.of S.A)).obj ωA)).hom =
      (Scheme.Modules.pushforward S.f).map φ ≫ ((S.derivedPushforwardSingleIso.app ωX).inv ≫
        (DerivedCategory.homologyFunctor S.base.Modules 0).map
          ((Stacks.Duality.derivedPushforward S.f).map c ≫ S.relativeDualizingTrace ωA) ≫
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso S.base.Modules 0).app
          ((tilde.functor (CommRingCat.of S.A)).obj ωA)).hom) := by
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hpre]
  refine (congrArg (fun w : (Scheme.Modules.pushforward S.f).obj F ⟶
      (tilde.functor (CommRingCat.of S.A)).obj ωA => moduleSpecΓFunctor.map w ≫
        ((tilde.toTildeΓNatIso (R := CommRingCat.of S.A)).app ωA).inv) hinner).trans ?_
  exact (congrArg (fun v : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward S.f).obj F) ⟶
      moduleSpecΓFunctor.obj ((tilde.functor (CommRingCat.of S.A)).obj ωA) =>
      v ≫ ((tilde.toTildeΓNatIso (R := CommRingCat.of S.A)).app ωA).inv)
      (moduleSpecΓFunctor.map_comp _ _)).trans (Category.assoc _ _ _)

omit [IsLocallyNoetherian S.X] in
/-- **Relative duality in degree zero for a module isomorphic to `f^!ω_A`.** When `c` is
invertible the duality pairing is bijective against every quasi-coherent `ℱ` whose first
cohomology vanishes: it is the composite of six bijections — placing `φ` in degree zero (the
single functor is fully faithful), composing with the isomorphism `c`, Grothendieck duality for
`Rf_* ⊣ f^!`, reading the result in degree zero (`Rf_*(ℱ[0])` is concentrated there), the
comparison `H⁰(Rf_*(ℱ[0])) ≅ f_*ℱ`, and global sections over the affine base. -/
theorem bijective_normalizationPairing (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules)
    (c : (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX ⟶
      (S.relativeDualizingComplex ωA).obj) [IsIso c]
    (F : S.X.Modules) (hF : F.IsQuasicoherent)
    (hH : IsZero (((moduleGlobalSections S.X).rightDerived 1).obj F)) :
    Function.Bijective (S.normalizationPairing ωA ωX c F) := by
  let : ((Scheme.Modules.pushforward S.f).obj F).IsQuasicoherent :=
    isQuasicoherent_of_iso S.base _ _ (S.derivedPushforwardSingleIso.app F)
      ((isQuasicoherent_homology_derivedPushforward_of_qcqs S.f) (singleQuasiCoherent F hF 0) 0)
  have hb1 : Function.Bijective
      ((DerivedCategory.singleFunctor S.X.Modules 0).map (X := F) (Y := ωX)) :=
    (Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _
  have hb2 := bijective_comp_right_of_isIso
    (X := (DerivedCategory.singleFunctor S.X.Modules 0).obj F) c
  have hι : Function.Bijective ((ObjectProperty.ι _).map
      (X := singleQuasiCoherent F hF 0) (Y := S.relativeDualizingComplex ωA)) :=
    (Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _
  have hι' : Function.Bijective ((ObjectProperty.ι _).map
      (X := (Stacks.Duality.quasiCoherentDerivedPushforward S.f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)).obj (singleQuasiCoherent F hF 0))
      (Y := S.baseDualizingComplex ωA)) :=
    (Functor.FullyFaithful.ofFullyFaithful _).map_bijective _ _
  have hb3 : Function.Bijective (fun u : (DerivedCategory.singleFunctor S.X.Modules 0).obj F ⟶
      (S.relativeDualizingComplex ωA).obj =>
        (Stacks.Duality.derivedPushforward S.f).map u ≫ S.relativeDualizingTrace ωA) := by
    refine (Function.Bijective.of_comp_iff _ hι).1 ?_
    have hc : (fun u : (DerivedCategory.singleFunctor S.X.Modules 0).obj F ⟶
          (S.relativeDualizingComplex ωA).obj =>
            (Stacks.Duality.derivedPushforward S.f).map u ≫ S.relativeDualizingTrace ωA) ∘
        ((ObjectProperty.ι _).map
          (X := singleQuasiCoherent F hF 0) (Y := S.relativeDualizingComplex ωA)) =
        ((ObjectProperty.ι _).map
          (X := (Stacks.Duality.quasiCoherentDerivedPushforward S.f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)).obj
              (singleQuasiCoherent F hF 0))
          (Y := S.baseDualizingComplex ωA)) ∘
        ⇑(Stacks.Duality.relativeDualizingComplexHomEquiv S.f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)
          (S.baseDualizingComplex ωA) (singleQuasiCoherent F hF 0)) :=
      funext fun u => (congrArg (ObjectProperty.ι _).map
        (Stacks.Duality.relativeDualizingComplexHomEquiv_apply S.f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)
          (S.baseDualizingComplex ωA) (singleQuasiCoherent F hF 0) u)).symm
    exact Eq.mpr (congrArg Function.Bijective hc) (hι'.comp (Equiv.bijective _))
  have hb4 :=
    DerivedCategory.bijective_homologyFunctor_map_comp_singleFunctorCompHomologyFunctorIso
      ((Stacks.Duality.derivedPushforward S.f).obj
        ((DerivedCategory.singleFunctor S.X.Modules 0).obj F)) 0
      (fun j hj => S.isZero_homology_derivedPushforward_single F hF hH j hj)
      ((tilde.functor (CommRingCat.of S.A)).obj ωA)
  have hb5 := bijective_comp_left_of_isIso (Z := (tilde.functor (CommRingCat.of S.A)).obj ωA)
    (S.derivedPushforwardSingleIso.app F).inv
  have hb6 := bijective_moduleSpecΓFunctor_map (R := CommRingCat.of S.A)
    ((Scheme.Modules.pushforward S.f).obj F) ωA
  exact hb6.comp (hb5.comp (hb4.comp (hb3.comp (hb2.comp hb1))))

omit [IsLocallyNoetherian S.X] in
/-- The trace is the duality pairing at the identity. -/
theorem normalizationTrace_eq_pairing_id (ωA : ModuleCat.{u} S.A) (ωX : S.X.Modules)
    (c : (DerivedCategory.singleFunctor S.X.Modules 0).obj ωX ⟶
      (S.relativeDualizingComplex ωA).obj) :
    S.normalizationPairing ωA ωX c ωX (𝟙 ωX) = S.normalizationTrace ωA ωX c := by
  rw [S.normalizationPairing_eq ωA ωX c ωX (𝟙 ωX), S.globalSectionsMap_id, Category.id_comp]

/-! ### A normalized module satisfies the degree-zero normalization condition -/

/-- **The normalization of [Stacks, Remark 0B4R] implies the degree-zero normalization condition
of `NormalizedDualizingModule`.** The trace is the duality pairing of `f^!(ω_A) ≅ ω_X` at the
identity of `ω_X`, and relative duality in degree zero for it is
`bijective_normalizationPairing`. So the whole development resting on
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule` — the trace
isomorphism of [Stacks, Tag 0BBU], the uniqueness up to a unique trace-compatible isomorphism —
applies to a module normalized in the sense of the remark. -/
def DualizingNormalization.normalizedDualizingModule {ωA : ModuleCat.{u} S.A}
    {ωX : S.X.Modules} (N : S.DualizingNormalization ωA ωX) :
    S.NormalizedDualizingModule ωA ωX where
  isDualizing := N.isDualizing
  trace := S.normalizationTrace ωA ωX N.normalizedIso.inv
  bijective_tracePairing F hF h1 := by
    have hH : IsZero (((moduleGlobalSections S.X).rightDerived 1).obj F) := by
      let := HasDerivedCategory.standard S.X.Modules
      let := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, ⊤))
      exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 F).2 h1
    have hfun : S.tracePairing (S.normalizationTrace ωA ωX N.normalizedIso.inv) F =
        S.normalizationPairing ωA ωX N.normalizedIso.inv F :=
      (funext fun φ => S.normalizationPairing_eq ωA ωX N.normalizedIso.inv F φ).symm
    exact Eq.mpr (congrArg Function.Bijective hfun)
      (S.bijective_normalizationPairing ωA ωX N.normalizedIso.inv F hF hH)

/-! ### The normalization determines `ω_X` -/

/-- **Two modules normalized relative to the same `ω_A` are isomorphic.** Both are `f^!(ω_A)`
read in degree zero, and the functor placing a module in degree zero is fully faithful.

No vanishing is involved, in contrast with
`AlgebraicGeometry.RationalSingularitySituation.normalizedDualizingIso`, which compares two
modules satisfying the degree-zero condition and needs the first cohomology of both to vanish.
That is the whole difference between the two notions: the degree-zero condition is satisfied by
every member of a family of mutually non-isomorphic modules — on the blowup of
`ℚ[x, y, z]/(xz - y²)` localized at `(x, y, z)`, by `𝒪_X` and by `𝒪_X(E)` with the same trace,
as the implementation notes of
`AlgebraicGeometry.RationalSingularitySituation.NormalizedDualizingModule`
record — whereas the normalization of the remark is satisfied by at most one isomorphism class. -/
def DualizingNormalization.moduleIso {ωA : ModuleCat.{u} S.A} {ωX ωX' : S.X.Modules}
    (N : S.DualizingNormalization ωA ωX) (N' : S.DualizingNormalization ωA ωX') : ωX ≅ ωX' :=
  (DerivedCategory.singleFunctor S.X.Modules 0).preimageIso
    (N.normalizedIso.symm ≪≫ N'.normalizedIso)

/-- **The normalization separates two modules that are not isomorphic.** Of two
non-isomorphic modules at most one is normalized relative to a given `ω_A`; this is what the
degree-zero condition fails to do. -/
theorem isEmpty_dualizingNormalization_of_not_isIsomorphic {ωA : ModuleCat.{u} S.A}
    {ωX ωX' : S.X.Modules} (h : ¬ IsIsomorphic ωX ωX')
    (N : S.DualizingNormalization ωA ωX) : IsEmpty (S.DualizingNormalization ωA ωX') :=
  ⟨fun N' => h ⟨DualizingNormalization.moduleIso S N N'⟩⟩

end Normalization

end RationalSingularitySituation

end AlgebraicGeometry

end
