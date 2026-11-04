module

public import StacksFrontier.AlgebraicGeometry.Cohomology.QuasicoherentAmplitude
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.DerivedLimitBounded
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QuasiCoherentAffineAmplitude
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnconditionalBoundedness
public import StacksCore.Tactic.StacksAttribute

/-!
# The coherator is bounded above on objects whose affine hypercohomology is bounded above

Let `X` be a quasi-compact and quasi-separated scheme and let `DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)` be a
coherator of `X` ([Stacks, Tag 0CR0]). [Stacks, Tag 0CSA] says that `DQ_X` has bounded
cohomological dimension: there is an integer `N` such that the cohomology sheaves of `DQ_X(K)` lie
in `[a, b + N]` whenever `H^i(U, K) = 0` for every affine open `U ⊆ X` and every `i ∉ [a, b]`. Its
proof, an induction over the quasi-compact opens of `X` along Mayer–Vietoris triangles, treats the
two ends of the interval separately, and the upper end needs no lower bound at all: if
`H^i(U, K) = 0` for every affine open `U` and every `i > b`, then `H^i(DQ_X(K)) = 0` for
`i > b + N`.
This is the form in which "`DQ_X` has bounded cohomological dimension" is used for objects of
`D(𝒪_X)` that are only bounded above, as in the proof of [Stacks, Tag 0DIC], where the objects
are derived limits of pseudo-coherent complexes and have no lower bound.

This file proves that upper bound, by the source's induction, and records the two facts that feed
it in practice: a complex with quasi-coherent cohomology sheaves vanishing above `a` has affine
hypercohomology vanishing above `a` ([Stacks, Tag 08D4] part (3) with Serre vanishing,
[Stacks, Tag 01XB]), and a chosen coherator of `X`.

## Main definitions

* `Stacks.Duality.Coherator.AffineAmplitudeLE` — the one-sided hypothesis: `H^i(U, K) = 0` for
  every affine open `U ⊆ X` and every `i > b`.
* `Stacks.Duality.Coherator.HasCoheratorUpperBoundAt` — the upper bound localized at an open `W`,
  the predicate the induction runs on.
* `Stacks.Duality.Coherator.derivedCoherator` — the coherator `DQ_X` of a quasi-compact
  quasi-separated scheme, chosen as the right adjoint of the inclusion whose existence is
  [Stacks, Tag 0CR0], with `Stacks.Duality.Coherator.derivedCoheratorAdjunction`.

## Main results

* `Stacks.Duality.Coherator.hasCoheratorUpperBoundAt_of_isAffineOpen` — the affine base case.
* `Stacks.Duality.Coherator.hasCoheratorUpperBoundAt_sup` — the inductive step.
* `Stacks.Duality.Coherator.exists_isLE_coherator_obj_of_qcqs` — the upper bound for an arbitrary
  coherator of a quasi-compact quasi-separated scheme.
* `Stacks.Duality.Coherator.affineAmplitudeLE_of_isLE` — a complex with quasi-coherent cohomology
  in degrees `≤ a` has affine hypercohomology in degrees `≤ a`.

## Implementation notes

Everything is at the locally small model of `D(𝒪_X)`, which is where the coherator of
[Stacks, Tag 0CR0] and the vocabulary of `Stacks.Duality.Coherator.AffineAmplitudeIn` live. The
two-sided statement of [Stacks, Tag 0CSA] is
`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj_of_qcqs`; it does not imply the one
proved here, because its hypothesis asks for a lower bound on the affine hypercohomology. The
ingredients of the induction are the ones that statement uses — the Mayer–Vietoris triangles of
[Stacks, Tag 08BV], the commutation of the coherator with direct image of [Stacks, Tag 0CR1] and
the bound of [Stacks, Tag 08D5] on direct images — each taken from where it is proved.

## References

* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Stacks.Duality

universe u

namespace Stacks.Duality.Coherator

variable (X : Scheme.{u})

/-! ### The one-sided hypothesis and the localized conclusion -/

/-- **The affine hypercohomology of `K` vanishes above `b`**: `H^i(U, K) = 0` for every affine
open `U` of `X` and every `i > b`. This is the upper half of
`Stacks.Duality.Coherator.AffineAmplitudeIn`, with no condition in low degrees. -/
def AffineAmplitudeLE (b : ℤ) (K : DerivedCategory X.Modules) : Prop :=
  ∀ (U : X.affineOpens) (i : ℤ), b < i →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) i).obj
      ((derivedSectionsLocallySmall X U.1).obj K))

variable (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)

/-- **The upper bound on the coherator, localized at an open `W` of `X`**: there is an integer
`N`, depending on `W` but not on `K` or `b`, such that the cohomology sheaves of
`DQ_X(Rj_{W,*}(K|_W))` vanish above `b + N` whenever the affine hypercohomology of `K` vanishes
above `b`. This is the predicate the induction of [Stacks, Tag 08DR] runs on. -/
def HasCoheratorUpperBoundAt (W : X.Opens) : Prop :=
  ∃ N : ℤ, ∀ (b : ℤ) (K : DerivedCategory X.Modules), AffineAmplitudeLE X b K →
    ((quasiCoherentι X).obj (DQ.obj (restrictPushforward W K))).IsLE (b + N)

/-! ### The affine base case -/

/-- **The affine base case.** For an affine open `U` of a quasi-compact quasi-separated scheme `X`
and a coherator `DQ_X` of `X`, the localized upper bound holds at `U`.

This is the upper half of `Stacks.Duality.Coherator.hasCoheratorBoundAt_of_isAffineOpen`, with the
same proof: for `φ : Spec Γ(X, U) ⟶ X` the object `DQ_X(Rj_{U,*}(K|_U))` is
`Rφ_*(DQ_{Spec Γ(X, U)}(K|_{Spec Γ(X, U)}))` by [Stacks, Tag 0CR1]; the inner coherator is derived
global sections followed by sheafification, so it vanishes above `b` as `RΓ(U, K)` does; and `Rφ_*`
raises an upper bound by the integer of [Stacks, Tag 08D5], which depends on `φ` alone. -/
theorem hasCoheratorUpperBoundAt_of_isAffineOpen {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X]
    {DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X}
    (adj : quasiCoherentι X ⊣ DQ) (U : X.Opens) (hU : IsAffineOpen U) :
    HasCoheratorUpperBoundAt X DQ U := by
  have hpush := isQuasicoherent_homology_derivedPushforward_of_qcqs hU.fromSpec
  have e0CR1 := coheratorDerivedPushforwardIso hU.fromSpec hpush
    (specCoherator Γ(X, U)) DQ (specCoheratorAdjunction Γ(X, U)) adj
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj_anyModel hU.fromSpec
  refine ⟨N, fun b K hK => ?_⟩
  obtain ⟨eSec⟩ := nonempty_iso_derivedGlobalSectionsFromSpec hU K
  obtain ⟨eF⟩ := nonempty_iso_restrictPushforwardFromSpec hU K
  set L := (OpenImmersion.derivedRestrict hU.fromSpec).obj K with hLdef
  have hYle : ((quasiCoherentι (Spec Γ(X, U))).obj ((specCoherator Γ(X, U)).obj L)).IsLE b := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact isZero_homology_specCoherator Γ(X, U) L i (IsZero.of_iso (hK ⟨U, hU⟩ i hi)
      ((DerivedCategory.homologyFunctor _ i).mapIso eSec))
  have ecomp : (quasiCoherentι X).obj (DQ.obj (restrictPushforward U K)) ≅
      (derivedPushforward hU.fromSpec).obj
        ((quasiCoherentι (Spec Γ(X, U))).obj ((specCoherator Γ(X, U)).obj L)) :=
    (quasiCoherentι X).mapIso (DQ.mapIso eF.symm ≪≫ (e0CR1.app L).symm)
  have := hN ((quasiCoherentι (Spec Γ(X, U))).obj ((specCoherator Γ(X, U)).obj L))
    (fun j => ((specCoherator Γ(X, U)).obj L).2 j) b hYle
  exact DerivedCategory.TStructure.t.isLE_of_iso ecomp.symm (b + N)

/-! ### The inductive step -/

section Estimate

variable {X} {DQ} (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated]

include adj

/-- **The upper bound along a Mayer–Vietoris triangle.** If the coherator of each of the three
terms `Rj_{U,*}(K|_U)`, `Rj_{V,*}(K|_V)`, `Rj_{U ∩ V,*}(K|_{U ∩ V})` has its cohomology sheaves in
degrees `≤ c`, then those of `DQ_X(A)` lie in degrees `≤ c + 1`, for a Mayer–Vietoris apex `A` of
`U`, `V` and `K`.

This is the long exact cohomology sequence of the image under the exact functor `ι ∘ DQ_X` of the
inverse rotation of the apex triangle, whose middle term is `ι(DQ_X A)`; the outer term
`ι(DQ_X(Rj_{U ∩ V,*}(K|_{U ∩ V})))⟦-1⟧` costs the extra degree. -/
theorem isLE_coherator_of_isMayerVietorisApex {U V : X.Opens}
    {K A : DerivedCategory X.Modules} (hA : IsMayerVietorisApex X U V K A) (c : ℤ)
    (hU : ((quasiCoherentι X).obj (DQ.obj (restrictPushforward U K))).IsLE c)
    (hV : ((quasiCoherentι X).obj (DQ.obj (restrictPushforward V K))).IsLE c)
    (hUV : ((quasiCoherentι X).obj (DQ.obj (restrictPushforward (U ⊓ V) K))).IsLE c) :
    ((quasiCoherentι X).obj (DQ.obj A)).IsLE (c + 1) := by
  have : (DQ ⋙ quasiCoherentι X).IsTriangulated := isTriangulated_comp_quasiCoherentι adj
  obtain ⟨f, g, h, hT⟩ := hA
  have hmid := DerivedCategory.TStructure.t.isLE₂ _
    ((DQ ⋙ quasiCoherentι X).map_distinguished _
      (binaryBiproductTriangle_distinguished (restrictPushforward U K)
        (restrictPushforward V K))) c hU hV
  have hdist := inv_rot_of_distTriang _ ((DQ ⋙ quasiCoherentι X).map_distinguished _ hT)
  have := hUV
  exact DerivedCategory.TStructure.t.isLE₂ _ hdist (c + 1)
    (DerivedCategory.TStructure.t.isLE_shift
      ((quasiCoherentι X).obj (DQ.obj (restrictPushforward (U ⊓ V) K))) c (-1) (c + 1)
      (by omega))
    (@Triangulated.TStructure.isLE_of_le _ _ _ _ _ _ _ DerivedCategory.TStructure.t
      _ c (c + 1) (by omega) hmid)

/-- **The inductive step.** If the localized upper bound holds at `U`, at `V` and at `U ⊓ V`,
then it holds at `U ⊔ V`, with the largest of the three integers increased by one. -/
theorem hasCoheratorUpperBoundAt_sup
    (hmv : ∀ (U V : X.Opens) (K : DerivedCategory X.Modules),
      IsMayerVietorisApex X U V K (restrictPushforward (U ⊔ V) K))
    (U V : X.Opens) (hU : HasCoheratorUpperBoundAt X DQ U)
    (hV : HasCoheratorUpperBoundAt X DQ V) (hUV : HasCoheratorUpperBoundAt X DQ (U ⊓ V)) :
    HasCoheratorUpperBoundAt X DQ (U ⊔ V) := by
  obtain ⟨N₁, h₁⟩ := hU
  obtain ⟨N₂, h₂⟩ := hV
  obtain ⟨N₃, h₃⟩ := hUV
  refine ⟨max N₁ (max N₂ N₃) + 1, fun b K hK => ?_⟩
  have mono : ∀ (N : ℤ), N ≤ max N₁ (max N₂ N₃) → ∀ Y : DerivedCategory X.Modules,
      Y.IsLE (b + N) → Y.IsLE (b + max N₁ (max N₂ N₃)) := fun N hN Y _ =>
    DerivedCategory.TStructure.t.isLE_of_le Y (b + N) _ (by omega)
  have key := isLE_coherator_of_isMayerVietorisApex adj (hmv U V K) (b + max N₁ (max N₂ N₃))
    (mono _ (by omega) _ (h₁ b K hK)) (mono _ (by omega) _ (h₂ b K hK))
    (mono _ (by omega) _ (h₃ b K hK))
  rwa [← add_assoc]

end Estimate

/-! ### The upper bound -/

/-- **The coherator has bounded cohomological dimension from above** ([Stacks, Tag 0CSA], the upper
end of the interval). Let `X` be a quasi-compact quasi-separated scheme and `DQ_X` a coherator of
`X`. There is an integer `N`, depending only on `X` and `DQ_X`, such that for every `K` in
`D(𝒪_X)` and every integer `b`, if `H^i(U, K) = 0` for every affine open `U ⊆ X` and every
`i > b`, then the cohomology sheaves `H^i(DQ_X(K))` vanish for `i > b + N`. No lower bound on `K`
is assumed.

The proof is the source's induction over the quasi-compact opens of `X` ([Stacks, Tag 08DR]):
the affine base case is `Stacks.Duality.Coherator.hasCoheratorUpperBoundAt_of_isAffineOpen`, the
inductive step `Stacks.Duality.Coherator.hasCoheratorUpperBoundAt_sup` runs on the Mayer–Vietoris
triangles of [Stacks, Tag 08BV], and the Mayer–Vietoris triangle for the cover of `X` by `⊤` and
`⊤` passes from the bound at `⊤` to the bound on `DQ_X(K)` itself. -/
theorem exists_isLE_coherator_obj_of_qcqs (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
    (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ] [adj.IsTriangulated] :
    ∃ N : ℤ, ∀ (b : ℤ) (K : DerivedCategory X.Modules), AffineAmplitudeLE X b K →
      ((quasiCoherentι X).obj (DQ.obj K)).IsLE (b + N) := by
  have htop : HasCoheratorUpperBoundAt X DQ ⊤ :=
    Stacks.AlgebraicGeometry.InductionPrinciple.induction_isCompact_open
      (HasCoheratorUpperBoundAt X DQ)
      (fun U hU => hasCoheratorUpperBoundAt_of_isAffineOpen adj U hU)
      (fun U V _ _ hU hV hUV => hasCoheratorUpperBoundAt_sup adj
        (fun U V K => isMayerVietorisApex_restrictPushforward_sup U V K) U V hU hV hUV) ⊤
      (by simpa using isCompact_univ (X := X))
  obtain ⟨N, hN⟩ := htop
  refine ⟨N + 1, fun b K hK => ?_⟩
  have hinf : (⊤ : X.Opens) ⊓ (⊤ : X.Opens) = ⊤ := inf_idem _
  have key := isLE_coherator_of_isMayerVietorisApex adj
    (isMayerVietorisApex_self ⊤ ⊤ (by simp) K) (b + N) (hN b K hK) (hN b K hK)
    (by rw [hinf]; exact hN b K hK)
  rwa [← add_assoc]

/-! ### Affine hypercohomology of a complex with quasi-coherent cohomology -/

/-- The classical higher right derived functors of sections over an affine open vanish on a
quasi-coherent module ([Stacks, Tag 01XB]), in the `ℤ`-indexed spelling. -/
private theorem isZero_rightDerivedPlus_sectionsFunctor (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) (hM : M.IsQuasicoherent) (p : ℤ) (hp : 0 < p) :
    IsZero (((Stacks.Cohomology.sectionsFunctor X U).rightDerivedPlus p).obj M) := by
  rw [Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _
    (show p = (p.toNat : ℤ) by omega) M]
  exact AlgebraicGeometry.isZero_rightDerived_evaluation_of_isAffineOpen X M U hU p.toNat
    (by omega)

/-- **A complex with quasi-coherent cohomology in degrees `≤ a` has affine hypercohomology in
degrees `≤ a`.** If the cohomology sheaves of `K` are quasi-coherent and vanish above `a`, then
`H^i(U, K) = 0` for every affine open `U ⊆ X` and every `i > a`.

This is [Stacks, Tag 08D4] part (3), upper bound
(`Stacks.QuasicoherentAmplitude.isLE_obj_of_isZero`), for sections over `U`, with `N = 1` supplied
by Serre vanishing on the affine open `U` ([Stacks, Tag 01XB]). No lower bound on `K` is needed. -/
theorem affineAmplitudeLE_of_isLE (K : DerivedCategory X.Modules)
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj K).IsQuasicoherent)
    (a : ℤ) (ha : K.IsLE a) : AffineAmplitudeLE X a K := by
  intro U i hi
  have h := Stacks.QuasicoherentAmplitude.isLE_obj_of_isZero X
    (Stacks.Cohomology.sectionsFunctor X U.1) (derivedSectionsLocallySmall X U.1)
    (derivedSectionsLocallySmallUnit X U.1) 1
    (fun M hM p hp => isZero_rightDerivedPlus_sectionsFunctor X U.1 U.2 M hM p (by omega))
    K hK a ha
  exact DerivedCategory.isZero_of_isLE _ (a + ((1 : ℕ) : ℤ) - 1) i (by omega)

/-! ### A chosen coherator -/

variable [CompactSpace X] [QuasiSeparatedSpace X]

/-- **The coherator `DQ_X`** of a quasi-compact quasi-separated scheme `X`: the right adjoint of
the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, which exists by [Stacks, Tag 0CR0]
(`Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`). It is unique up to unique isomorphism,
as any right adjoint is. -/
def derivedCoherator : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X :=
  have := isLeftAdjoint_quasiCoherentι X
  (quasiCoherentι X).rightAdjoint

/-- The adjunction `ι ⊣ DQ_X` exhibiting `Stacks.Duality.Coherator.derivedCoherator` as a
coherator. -/
def derivedCoheratorAdjunction : quasiCoherentι X ⊣ derivedCoherator X :=
  have := isLeftAdjoint_quasiCoherentι X
  Adjunction.ofIsLeftAdjoint (quasiCoherentι X)

/-- The coherator commutes with the shift, as a right adjoint of a functor which does. -/
instance : (derivedCoherator X).CommShift ℤ :=
  (derivedCoheratorAdjunction X).rightAdjointCommShift ℤ

/-- The adjunction `ι ⊣ DQ_X` is compatible with the shifts on both categories. -/
instance : (derivedCoheratorAdjunction X).CommShift ℤ :=
  (derivedCoheratorAdjunction X).commShift_of_leftAdjoint ℤ

/-- The adjunction `ι ⊣ DQ_X` is triangulated: a right adjoint of an exact functor is exact. -/
instance : (derivedCoheratorAdjunction X).IsTriangulated :=
  Adjunction.IsTriangulated.mk' _

end Stacks.Duality.Coherator

end
