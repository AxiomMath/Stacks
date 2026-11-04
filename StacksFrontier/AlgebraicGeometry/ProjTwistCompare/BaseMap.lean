module

public import StacksFrontier.AlgebraicGeometry.ProjMapData.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The points and the fibres of the morphism induced by a graded ring homomorphism

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings, let
`U(ψ) ⊆ Proj ℬ` be `Stacks.AlgebraicGeometry.ProjShared.mapDomain`, and let
`mapHom : U(ψ) ⟶ Proj 𝒜` be `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`. This file
identifies `mapHom` on points: the homogeneous prime attached to `y ∈ U(ψ)` is sent to its
preimage `ψ⁻¹` — Mathlib's `ProjectiveSpectrum.comap`, but with no hypothesis on `ψ`.

From that identification the file builds the comparison map on the *fibres* of the twisting
sheaves: for `y ∈ U(ψ)` with image `x`, a ring map

`𝒜_x = (𝒜 localized at x) ⟶ (ℬ localized at y) = ℬ_y`,

carrying the fibre of `𝒪_{Proj 𝒜}(n)` at `x` to the fibre of `𝒪_{Proj ℬ}(n)` at `y` and
sending a homogeneous fraction `a / s` to `ψ a / ψ s`. These fibres are exactly the fibres over
which `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf` — and therefore
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf` — takes its sections, so this is the
pointwise half of the comparison map on twists.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistCompare.notMem_mapHom_base_iff`: the pointwise form of
  Tag 01MY part (2), for a homogeneous element of *any* degree — including degree zero, which
  the standard-open statement does not reach.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.mapHom_base_asHomogeneousIdeal`: the homogeneous
  prime at `mapHom y` is `ψ⁻¹` of the one at `y`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.mapHom_base_eq`: the same, as an equality of
  points of `Proj 𝒜`.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.notMem_of_notMem`: a homogeneous element omitted
  by every prime of a fibre of `mapHom` has its image omitted too — the denominator half of
  the local-fraction condition.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.homogeneousFibreMap` and
  `Stacks.AlgebraicGeometry.ProjTwistCompare.fibreMap`: the comparison ring map on the fibres of
  the structure sheaves, and on those of the associated-module sheaves, at a pair of homogeneous
  primes related by `ψ`; `fibreMap_mk` computes the second on a fraction and
  `val_homogeneousFibreMap` identifies the two.
* `Stacks.AlgebraicGeometry.ProjTwistCompare.map_mem_integerGrading` and
  `Stacks.AlgebraicGeometry.ProjTwistCompare.map_mem_twistGrading`: a graded homomorphism
  preserves the integer-extended grading and each of its shifts, so it carries a homogeneous
  numerator for `𝒪_{Proj 𝒜}(n)` to one for `𝒪_{Proj ℬ}(n)`.

## Implementation notes

The route to the identification of points is
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_preimage_basicOpen`, which is Tag 01MY part (2)
for standard opens, and `HomogeneousIdeal.ext'`, which reduces an equality of homogeneous
ideals to membership of homogeneous elements. The part (2) statement is available only for `f`
homogeneous of *positive* degree, so degree zero is reached by multiplying by a positive-degree
`g` that the prime at `y` omits — such a `g` exists precisely because `y` lies in `U(ψ)`, which
is where the restriction to the domain of definition enters. Nothing here needs Mathlib's
hypothesis `ℬ₊ ≤ 𝒜₊.map ψ`, and nothing here needs the gluing to be unwound: the pointwise
formula is a consequence of the covering statement, not of the construction.

The fibre of the structure sheaf at a homogeneous prime is
`HomogeneousLocalization.AtPrime`, and Mathlib already has the comparison map between two such
fibres along a graded homomorphism, `HomogeneousLocalization.localRingHom`; what was missing
was its hypothesis, an *equality* of the two homogeneous ideals, which is exactly
`mapHom_base_asHomogeneousIdeal`. The fibres of `associatedModuleSheaf` are instead the
ordinary localizations `LocalizedModule x.primeCompl`, which for the twisting sheaves — whose
underlying module is the ring itself — is the same type as `Localization x.primeCompl`
(both unfold to `OreLocalization`); `fibreMap` is therefore stated as a map of those, using
`Localization.localRingHom`, and `HomogeneousLocalization.val_localRingHom` relates the two.

There is no universe subtlety: both rings live in a single universe `u`, forced because
`Proj ℬ ⟶ Proj 𝒜` must be a morphism of `Scheme.{u}`, while the two `SetLike` carriers are
independent. One transparency gotcha of the neighbouring files does appear, and it dictates the
shape of the fibre maps: a point of `Proj 𝒜` is a term of `↥(Proj 𝒜)`, which is
`ProjectiveSpectrum 𝒜` only at default transparency, so instance search does not find the
primality of its homogeneous ideal and therefore does not form the complement of that prime.
`homogeneousFibreMap` and `fibreMap` consequently take their two points as explicit
`ProjectiveSpectrum` parameters together with the relating equation, rather than taking a point
of `U(ψ)`; `mapHom_base_asHomogeneousIdeal` is what supplies that equation at every point of
`U(ψ)`, and the companion file binds the composite under a name.

What is **not** done here: the comparison map on twists itself, which is assembled from
`fibreMap` in `StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist`. That assembly needs the
action of `Γ(Proj 𝒜, U)` on the pushed-forward sections to be known pointwise, that is, it needs
the value of `mapHom.app U r` at a point to be the fibre comparison of the value of `r`; that is
`Stacks.AlgebraicGeometry.ProjTwistCompare.val_app` of the intermediate file
`StacksFrontier.AlgebraicGeometry.ProjTwistCompare.SectionValue`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.ProjTwistCompare

attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The identification of points -/

/-- The pointwise form of Tag 01MY part (2) for a homogeneous element of positive degree: a
point of `U(ψ)` omits `ψ f` exactly when its image omits `f`. -/
public theorem notMem_mapHom_base_iff_of_pos (ψ : 𝒜 →+*ᵍ ℬ)
    (y : (mapDomain 𝒜 ℬ ψ).toScheme) {k : ℕ} (hk : 0 < k) {f : A} (hf : f ∈ 𝒜 k) :
    f ∉ ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal ↔
      ψ f ∉ (y.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal := by
  have h := mapHom_preimage_basicOpen 𝒜 ℬ ψ f k hf hk
  have h1 : ((mapHom 𝒜 ℬ ψ).base y ∈ Proj.basicOpen 𝒜 f) ↔
      (y.1 ∈ Proj.basicOpen ℬ (ψ f)) := by
    refine ⟨fun hm => ?_, fun hm => ?_⟩
    · have hm' : y ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ Proj.basicOpen 𝒜 f := hm
      rw [h] at hm'
      exact hm'
    · have hm' : y ∈ (mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f) := hm
      rw [← h] at hm'
      exact hm'
  simpa only [Proj.mem_basicOpen] using h1

/-- The pointwise form of Tag 01MY part (2) for a homogeneous element of **any** degree. The
standard-open statement reaches only positive degrees; degree zero follows by multiplying by a
positive-degree element that the prime at `y` omits, which exists because `y ∈ U(ψ)`. -/
public theorem notMem_mapHom_base_iff (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    {k : ℕ} {f : A} (hf : f ∈ 𝒜 k) :
    f ∉ ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal ↔
      ψ f ∉ (y.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal := by
  obtain ⟨e, g, he, hg, hgy⟩ := (mem_mapDomain_iff 𝒜 ℬ ψ y.1).mp y.2
  have hgx : g ∉ ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal :=
    (notMem_mapHom_base_iff_of_pos 𝒜 ℬ ψ y he hg).mpr hgy
  have h2 := notMem_mapHom_base_iff_of_pos 𝒜 ℬ ψ y (k := k + e) (by omega)
    (SetLike.mul_mem_graded hf hg)
  rw [map_mul] at h2
  refine ⟨fun hfx hfy => ?_, fun hfy hfx => ?_⟩
  · refine hgx ?_
    rcases ((mapHom 𝒜 ℬ ψ).base y).isPrime.mem_or_mem
      (show f * g ∈ _ from by
        by_contra hh
        exact (h2.mp hh) (Ideal.mul_mem_right _ _ hfy)) with h | h
    · exact absurd h hfx
    · exact h
  · refine hgy ?_
    rcases (y.1 : ProjectiveSpectrum ℬ).isPrime.mem_or_mem
      (show ψ f * ψ g ∈ _ from by
        by_contra hh
        exact (h2.mpr hh) (Ideal.mul_mem_right _ _ hfx)) with h | h
    · exact absurd h hfy
    · exact h

/-- **Tag 01MY, the morphism on points**: the homogeneous prime attached to the image of
`y ∈ U(ψ)` under the induced morphism is the preimage under `ψ` of the homogeneous prime
attached to `y`. Compare `ProjectiveSpectrum.comapFun`, which Mathlib states only under
`ℬ₊ ≤ 𝒜₊.map ψ`. -/
@[ega "II 2.8.1"]
public theorem mapHom_base_asHomogeneousIdeal (ψ : 𝒜 →+*ᵍ ℬ)
    (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal =
      (y.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal.comap ψ :=
  HomogeneousIdeal.ext' fun _ a ha => by
    have h := notMem_mapHom_base_iff 𝒜 ℬ ψ y ha
    exact ⟨fun hm => by by_contra hh; exact (h.mpr hh) hm,
      fun hm => by by_contra hh; exact (h.mp hh) hm⟩

/-- The ideal form of `mapHom_base_asHomogeneousIdeal`, in the shape
`HomogeneousLocalization.localRingHom` and `Localization.localRingHom` ask for. -/
public theorem mapHom_base_toIdeal (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal.toIdeal =
      Ideal.comap (ψ : A →+* B) (y.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal.toIdeal :=
  congrArg HomogeneousIdeal.toIdeal (mapHom_base_asHomogeneousIdeal 𝒜 ℬ ψ y)

/-- `mapHom_base_asHomogeneousIdeal` as an equality of points of `Proj 𝒜`. -/
public theorem mapHom_base_eq (ψ : 𝒜 →+*ᵍ ℬ) (y : (mapDomain 𝒜 ℬ ψ).toScheme) :
    ((mapHom 𝒜 ℬ ψ).base y : ProjectiveSpectrum 𝒜) =
      { asHomogeneousIdeal := (y.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal.comap ψ
        isPrime := (mapHom_base_asHomogeneousIdeal 𝒜 ℬ ψ y) ▸
          ((mapHom 𝒜 ℬ ψ).base y).isPrime
        not_irrelevant_le := (mapHom_base_asHomogeneousIdeal 𝒜 ℬ ψ y) ▸
          ((mapHom 𝒜 ℬ ψ).base y).not_irrelevant_le } :=
  ProjectiveSpectrum.ext (mapHom_base_asHomogeneousIdeal 𝒜 ℬ ψ y)

/-- The denominator half of the local-fraction condition: a homogeneous element omitted by the
prime at every point of the image of an open `V ⊆ U(ψ)` has its `ψ`-image omitted by the prime
at every point of `V`. -/
public theorem notMem_of_notMem (ψ : 𝒜 →+*ᵍ ℬ) {k : ℕ} {s : A} (hs : s ∈ 𝒜 k)
    (y : (mapDomain 𝒜 ℬ ψ).toScheme)
    (h : s ∉ ((mapHom 𝒜 ℬ ψ).base y).asHomogeneousIdeal) :
    ψ s ∉ (y.1 : ProjectiveSpectrum ℬ).asHomogeneousIdeal :=
  (notMem_mapHom_base_iff 𝒜 ℬ ψ y hs).mp h

/-! ### Degree preservation on the twisting gradings -/

omit [GradedRing 𝒜] [GradedRing ℬ] in
/-- A graded ring homomorphism preserves the grading extended to `ℤ` by zero. -/
public theorem map_mem_integerGrading (ψ : 𝒜 →+*ᵍ ℬ) (i : ℤ) {m : A}
    (hm : m ∈ integerGrading (S := A) 𝒜 i) : ψ m ∈ integerGrading (S := B) ℬ i := by
  by_cases hi : 0 ≤ i
  · have hA : integerGrading (S := A) 𝒜 i = homogeneousSubmodule (S := A) 𝒜 i.toNat := by
      simp [integerGrading, hi]
    have hB : integerGrading (S := B) ℬ i = homogeneousSubmodule (S := B) ℬ i.toNat := by
      simp [integerGrading, hi]
    rw [hA, mem_homogeneousSubmodule] at hm
    rw [hB, mem_homogeneousSubmodule]
    exact ψ.map_mem hm
  · have hA : integerGrading (S := A) 𝒜 i = ⊥ := by simp [integerGrading, hi]
    have hB : integerGrading (S := B) ℬ i = ⊥ := by simp [integerGrading, hi]
    rw [hA, Submodule.mem_bot] at hm
    rw [hB, Submodule.mem_bot, hm, map_zero]

omit [GradedRing 𝒜] [GradedRing ℬ] in
/-- A graded ring homomorphism preserves every shift of the grading: a homogeneous numerator
for `𝒪_{Proj 𝒜}(n)` goes to one for `𝒪_{Proj ℬ}(n)`. -/
public theorem map_mem_twistGrading (ψ : 𝒜 →+*ᵍ ℬ) (n i : ℤ) {m : A}
    (hm : m ∈ twistGrading (S := A) 𝒜 n i) : ψ m ∈ twistGrading (S := B) ℬ n i :=
  map_mem_integerGrading 𝒜 ℬ ψ (i + n) hm

/-! ### The comparison map on fibres -/

section fibre

variable (ψ : 𝒜 →+*ᵍ ℬ) (x : ProjectiveSpectrum 𝒜) (y : ProjectiveSpectrum ℬ)
  (h : x.asHomogeneousIdeal = y.asHomogeneousIdeal.comap ψ)

/-- The comparison map on the fibres of the structure sheaves at a pair of homogeneous primes
related by `ψ`. This is `HomogeneousLocalization.localRingHom`; the content is the hypothesis,
which `mapHom_base_asHomogeneousIdeal` supplies at every point of `U(ψ)`. -/
public def homogeneousFibreMap :
    AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal →+* AtPrime ℬ y.asHomogeneousIdeal.toIdeal :=
  HomogeneousLocalization.localRingHom ψ _ _ (congrArg HomogeneousIdeal.toIdeal h)

/-- The comparison map on the fibres of `associatedModuleSheaf` for the twisting sheaves. The
underlying module of every twist of `𝒜` is `A` itself, so the fibre is the ordinary
localization of `A` and the map is `Localization.localRingHom`. -/
public def fibreMap :
    ModuleFiber (M := A) 𝒜 x →+* ModuleFiber (M := B) ℬ y :=
  Localization.localRingHom _ _ (ψ : A →+* B) (congrArg HomogeneousIdeal.toIdeal h)

/-- The comparison map on fibres sends `a / s` to `ψ a / ψ s`. -/
public theorem fibreMap_mk (a s : A) (hs : s ∉ x.asHomogeneousIdeal.toIdeal)
    (hψs : ψ s ∉ y.asHomogeneousIdeal.toIdeal) :
    fibreMap 𝒜 ℬ ψ x y h (LocalizedModule.mk a ⟨s, hs⟩) =
      LocalizedModule.mk (ψ a) ⟨ψ s, hψs⟩ :=
  Localization.localRingHom_mk _ _ _ _ a ⟨s, hs⟩

/-- `fibreMap` is the fibre comparison of the structure sheaves, read in the ambient
localization. -/
public theorem val_homogeneousFibreMap (z : AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :
    (homogeneousFibreMap 𝒜 ℬ ψ x y h z).val = fibreMap 𝒜 ℬ ψ x y h z.val :=
  HomogeneousLocalization.val_localRingHom z

end fibre

end Stacks.AlgebraicGeometry.ProjTwistCompare

end
