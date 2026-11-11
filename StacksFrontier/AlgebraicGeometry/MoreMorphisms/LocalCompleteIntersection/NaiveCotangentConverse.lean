module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.NaiveCotangent
public import StacksFrontier.AlgebraicGeometry.Perfect.LocalTorDimensionCanonicalCertificate
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Restriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0FK2: the naive cotangent complex detects local complete intersection morphisms

For a perfect morphism `f : X ⟶ Y` of locally Noetherian schemes the following are equivalent:
`f` is a local complete intersection morphism; `NL_{X/Y}` has Tor amplitude in `[-1, 0]`;
`NL_{X/Y}` is perfect with Tor amplitude in `[-1, 0]`.

## Main results

* `isLocalCompleteIntersectionMorphism_of_hasTorAmplitude_naiveCotangentComplex_of_perfect`:
  **Stacks 0FK2**, the implication (2) ⇒ (1).
* `isLocalCompleteIntersectionMorphism_of_isPerfect_of_hasTorAmplitude`:
  **Stacks 0FK2**, the implication (3) ⇒ (1).
* `naiveCotangentComplex_tfae_isLocalCompleteIntersectionMorphism`:
  **Stacks 0FK2**, the three conditions in one statement.

## Implementation notes

The forward implications (1) ⇒ (2) and (1) ⇒ (3), and the projection (3) ⇒ (2), are in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/LocalCompleteIntersection/NaiveCotangent.lean`; what
is proved here are the two converses, and then all three conditions are collected into a single
`List.TFAE`, which is the statement the tag is registered on.

Only (2) ⇒ (1) has content, (3) ⇒ (1) being (3) ⇒ (2) followed by it. It is the affine-local
computation of that file read backwards. Being a local complete intersection morphism is Zariski
local on the source and on the target, so by
`AlgebraicGeometry.IsZariskiLocalAtSource.iff_exists_resLE` it is enough to produce, around every
point of `X`, an affine open `V ⊆ X` lying over an affine open `U ⊆ Y` with `f|_V^U` a local
complete intersection morphism; by Stacks 07DB that is a condition on `Γ(Y, U) → Γ(X, V)`.

Tor amplitude restricts to an open subspace, by
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_restrictModules`, and on such a `V` the
restriction `NL_{X/Y}|_V` is the derived pullback along `V ≅ Spec Γ(X, V)` of the derived
sheafification of `NL_{Γ(X, V)/Γ(Y, U)}` — this is
`AlgebraicGeometry.NaiveCotangentLocalCompleteIntersection.naiveCotangentComplexRestrictIso`,
built from Stacks 0D0I. Stacks 08E9 and Stacks 08EB are equivalences, so the hypothesis descends
to Tor amplitude in `[-1, 0]` of `NL_{Γ(X, V)/Γ(Y, U)}` in `D(Γ(X, V))`, read at the canonical
derived tensor product of Stacks 0BYI.

There Stacks 0FJT applies: `Γ(Y, U)` and `Γ(X, V)` are Noetherian because `Y` and `X` are
locally Noetherian, and `Γ(Y, U) → Γ(X, V)` is a perfect ring map because `f` is a perfect
morphism: the chart property of Stacks 0687, read through Mathlib's
`AlgebraicGeometry.HasRingHomProperty.appLE`. Its equivalence (1) ⇒ (3) makes `Γ(Y, U) → Γ(X, V)`
a local complete intersection homomorphism.

The ring-level conclusion arrives in the `Scheme.Hom.appLE` spelling, while Stacks 07DB is stated
at `Scheme.Hom.appTop` of the restriction `f|_V^U`; the two are converted into one another by
`AlgebraicGeometry.Scheme.Hom.resLE_appLE`, exactly as
`isLocalCompleteIntersection_appLE_of_appTop` of the forward file does in the other direction.

## References

* [Stacks Project, Lemma 37.62.16 (0FK2)](https://stacks.math.columbia.edu/tag/0FK2)
* [Stacks Project, Lemma 23.11.4 (0FJT)](https://stacks.math.columbia.edu/tag/0FJT)
* [Stacks Project, Lemma 37.62.5 (07DB)](https://stacks.math.columbia.edu/tag/07DB)
* [Stacks Project, Lemma 37.13.2 (0D0I)](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Definition 37.62.1 (069F)](https://stacks.math.columbia.edu/tag/069F)
* [Stacks Project, Definition 36.61.2 (0687)](https://stacks.math.columbia.edu/tag/0687)
* [Stacks Project, Definition 20.48.1 (08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Definition 20.49.1 (08CM)](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Lemma 36.10.4 (08E9)](https://stacks.math.columbia.edu/tag/08E9)
* [Stacks Project, Lemma 36.10.7 (08EB)](https://stacks.math.columbia.edu/tag/08EB)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

namespace NaiveCotangentLocalCompleteIntersection

/-! ### The local complete intersection condition on sections, read backwards -/

/-- The local complete intersection condition on the sections of `f` over the pair `U`, `V` is
the same condition on the global sections of the restriction `f|_V^U`.

This is the converse of `isLocalCompleteIntersection_appLE_of_appTop`, and is proved the same
way: `Scheme.Hom.resLE_appLE` identifies the sections of the restriction over the two total
opens with the sections of `f` over the images of those opens, which are `U` and `V`. -/
theorem isLocalCompleteIntersection_appTop_of_appLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)
    (h : RingHom.IsLocalCompleteIntersection ((f.appLE U V hVU).hom)) :
    RingHom.IsLocalCompleteIntersection ((f.resLE U V hVU).appTop.hom) := by
  have h1 : RingHom.IsLocalCompleteIntersection
      (((f.resLE U V hVU).appLE ⊤ ⊤ le_top).hom) := by
    rw [Scheme.Hom.resLE_appLE f hVU ⊤ ⊤ le_top]
    exact isLocalCompleteIntersection_appLE_congr f U.ι_image_top.symm V.ι_image_top.symm h
  rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app]
  exact isLocalCompleteIntersection_appLE_congr _ rfl (by simp) h1

/-! ### The affine-local computation, read backwards -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U)

/-- **Tor amplitude of `NL_{X/Y}` descends to `NL_{Γ(X, V)/Γ(Y, U)}`.** For `V` an affine open of
`X` lying over an affine open `U` of `Y`, Tor amplitude in `[-1, 0]` of `NL_{X/Y}` gives Tor
amplitude in `[-1, 0]` of `NL_{Γ(X, V)/Γ(Y, U)}` in `D(Γ(X, V))`, at the canonical derived tensor
product.

Tor amplitude restricts to the open subspace `V`, where `NL_{X/Y}|_V` is the derived pullback
along `V ≅ Spec Γ(X, V)` of the derived sheafification of `NL_{Γ(X, V)/Γ(Y, U)}` by Stacks 0D0I;
Stacks 08E9 is an equivalence, so the condition descends. -/
alias hasTorAmplitudeCanonical_naiveCotangentObject_of_hasTorAmplitude :=
  hasTorAmplitudeCanonical_of_hasTorAmplitude

/-- **Stacks 0FJT at `Γ(Y, U) → Γ(X, V)`.** For `V` an affine open of `X` lying over an affine
open `U` of `Y`, Tor amplitude in `[-1, 0]` of `NL_{X/Y}` makes `Γ(Y, U) → Γ(X, V)` a local
complete intersection homomorphism: the two rings are Noetherian because `X` and `Y` are locally
Noetherian, and the map is perfect because `f` is, that being the defining condition of
Stacks 0687. -/
theorem isLocalCompleteIntersection_appLE_of_hasTorAmplitude
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Perfect f]
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    RingHom.IsLocalCompleteIntersection ((f.appLE U V hVU).hom) := by
  let := Stacks.NaiveCotangentAffineStalk.algebraAppLE f hVU
  have _hA : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have _hB : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  -- Perfectness of `Γ(Y, U) → Γ(X, V)`: the chart property of Stacks 0687.
  have : Algebra.Perfect Γ(Y, U) Γ(X, V) :=
    RingHom.perfect_algebraMap.mp (HasRingHomProperty.appLE @Perfect f ‹_› ⟨U, hU⟩ ⟨V, hV⟩ hVU)
  -- Condition (1) of Stacks 0FJT is Tor amplitude at the three fields of the canonical
  -- certificate; both it and `HasTorAmplitudeCanonical` are read off a bounded flat
  -- representative, by Stacks 0654.
  have harg := (StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative
      (StacksDraft.TorAmplitude.canonicalTensorComparison Γ(X, V))
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived Γ(X, V))
      (NaiveCotangent.naiveCotangentObject Γ(Y, U) Γ(X, V)) (-1) 0).2
    ((StacksDraft.TorAmplitude.hasTorAmplitudeCanonical_iff_hasFlatRepresentative
        Γ(X, V) (NaiveCotangent.naiveCotangentObject Γ(Y, U) Γ(X, V)) (-1) 0).1
      (hasTorAmplitudeCanonical_naiveCotangentObject_of_hasTorAmplitude f hVU hU hV hamp))
  exact ((NaiveCotangent.hasTorAmplitude_tfae_isLocalCompleteIntersection
    Γ(Y, U) Γ(X, V)).out 1 3).mp harg

end NaiveCotangentLocalCompleteIntersection

open NaiveCotangentLocalCompleteIntersection

/-! ### The two converses -/

/-- **Stacks 0FK2, the implication (2) ⇒ (1).** If `f : X ⟶ Y` is a perfect morphism of locally
Noetherian schemes and `NL_{X/Y}` has Tor amplitude in `[-1, 0]`, then `f` is a local complete
intersection morphism.

Being a local complete intersection morphism is Zariski local on the source and on the target, so
it suffices to check it on the restrictions `f|_V^U` for `V` an affine open of `X` lying over an
affine open `U` of `Y` covering `X`; by Stacks 07DB that is the condition on `Γ(Y, U) → Γ(X, V)`
supplied by Stacks 0FJT. -/
theorem isLocalCompleteIntersectionMorphism_of_hasTorAmplitude_naiveCotangentComplex_of_perfect
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Perfect f]
    (hamp : Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
      (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    IsLocalCompleteIntersectionMorphism f := by
  classical
  have hchart : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      IsLocalCompleteIntersectionMorphism (W.ι ≫ f) := by
    intro x
    obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (Opens.mem_top (f.base x))
    obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ U from hxU)
    have _hUaff : IsAffine (U : Scheme.{u}) := hU
    have _hVaff : IsAffine (V : Scheme.{u}) := hV
    have h1 : IsLocalCompleteIntersectionMorphism (f.resLE U V hVU) :=
      (isLocalCompleteIntersectionMorphism_iff_appTop (f.resLE U V hVU)).2
        (isLocalCompleteIntersection_appTop_of_appLE f hVU
          (isLocalCompleteIntersection_appLE_of_hasTorAmplitude f hVU hU hV hamp))
    have h2 : IsLocalCompleteIntersectionMorphism (f.resLE U V hVU ≫ Scheme.Opens.ι U) :=
      isLocalCompleteIntersectionMorphism_comp (f.resLE U V hVU) (Scheme.Opens.ι U) h1
        (isLocalCompleteIntersectionMorphism_of_isOpenImmersion (Scheme.Opens.ι U))
    rw [Scheme.Hom.resLE_comp_ι f hVU] at h2
    exact ⟨V, hxV, h2⟩
  choose W hxW hW using hchart
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @IsLocalCompleteIntersectionMorphism.{u}) W
    (top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxW x⟩) hW

/-- **Stacks 0FK2, the implication (3) ⇒ (1).** If `f : X ⟶ Y` is a perfect morphism of locally
Noetherian schemes and `NL_{X/Y}` is perfect with Tor amplitude in `[-1, 0]`, then `f` is a local
complete intersection morphism. Perfectness of the complex is discarded: the implication is
(3) ⇒ (2) followed by (2) ⇒ (1). -/
theorem isLocalCompleteIntersectionMorphism_of_isPerfect_of_hasTorAmplitude
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Perfect f]
    (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
      Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
        (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0) :
    IsLocalCompleteIntersectionMorphism f :=
  isLocalCompleteIntersectionMorphism_of_hasTorAmplitude_naiveCotangentComplex_of_perfect f h.2

/-! ### Stacks 0FK2 -/

/-- **Stacks 0FK2.** Let `f : X ⟶ Y` be a perfect morphism of locally Noetherian schemes. The
following are equivalent:

1. `f` is a local complete intersection morphism;
2. `NL_{X/Y}` has Tor amplitude in `[-1, 0]`;
3. `NL_{X/Y}` is perfect with Tor amplitude in `[-1, 0]`.

Here `NL_{X/Y}` is `AlgebraicGeometry.Scheme.naiveCotangentComplex`, Stacks 0D0H, read at its
class in `D(𝒪_X)`; Tor amplitude is `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`, Stacks
08CG, taken against the canonical derived tensor product of a ringed space, and perfectness is
`Stacks.Cohomology.PerfectComplexes.IsPerfect`, Stacks 08CM. Both are stated at the underlying
ringed space of `X`, with the standard derived category, as they are for Stacks 08E9 and Stacks
08EB.

Rendered on sections over a compatible pair of affine opens the statement is Stacks 0FJT; the
translation is Stacks 07DB and Stacks 0D0I together with Stacks 08E9 and Stacks 08EB. -/
@[stacks 0FK2, sga "6 VIII 2.4" "partial", sga "6 XIV 2.1" "(1) ⇒ (3), special case"]
theorem naiveCotangentComplex_tfae_isLocalCompleteIntersectionMorphism {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Perfect f] :
    List.TFAE
      [IsLocalCompleteIntersectionMorphism f,
        Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
          (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0,
        Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) ∧
          Stacks.Cohomology.TorAmplitude.HasTorAmplitude X.toRingedSpace
            (DerivedCategory.Q.obj (Scheme.naiveCotangentComplex f)) (-1) 0] := by
  tfae_have 1 → 3 := isPerfect_and_hasTorAmplitude_naiveCotangentComplex f
  tfae_have 3 → 2 := fun h => h.2
  tfae_have 2 → 1 :=
    isLocalCompleteIntersectionMorphism_of_hasTorAmplitude_naiveCotangentComplex_of_perfect f
  tfae_finish

end AlgebraicGeometry

end
