module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.FibreUnitAgreement
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.PullbackDenominators

/-!
# The family `φ^*(g_i) s` of Tag 0BD7, with `s` and the `g_i` meromorphic

The chart of [Stacks, Tag 0BD7] is built in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartSaturation.lean` from a family `t` of
sections of `ℒ`, each defined on its own open, together with the two properties `hex` and
`hagree` that the penultimate paragraph of that proof establishes; and
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/FibreUnitAgreement.lean` discharges
`hagree` from a unit relation on the base. This file says what the family *is*.

In the source neither factor of a member of that family is a regular section:

> Choose a trivializing section `s ∈ Γ(X_ξ, ℒ_ξ)` … Hence we can think of `s` as a regular
> meromorphic section of `ℒ`

and the multipliers are the meromorphic functions `g ∈ 𝒦_Y(V)` with `φ^*(g) s ∈ ℒ(φ^{-1} V)`,
whose ratios are units of the total ring of fractions `R(Y)`. Affinely `s = a/r` with `r ≠ 0` in
`R`, and the product `φ^*(r/g) s` is a *unit of* `A` while `s ∉ A` and `r/g ∉ R`. **A product of
two regular things cannot express that**, so the family is given here as a *meromorphic*
multiplier `g i ∈ 𝒦_Y(A i)` together with the regular section `t i` of `ℒ` on `φ^{-1}(A i)` that
the product *is*: the membership condition of
`Stacks.Meromorphic.exists_pullbackDenominatorModuleι_app_eq_iff`, the defining property of the
module `𝒩 ⊂ 𝒦_Y` of the source. The section `s` is a global section of `𝒦_X(ℒ)`, not of `ℒ` —
which is the point, because Tag 0BD7 gives `ℒ` no nonzero global regular section, and
`AlgebraicGeometry.meromorphicSectionOfGenericStalk` produces such an `s` from an element of the
stalk of `ℒ` at the generic point of `X`, which is exactly what the first paragraph of the proof
has.

There is no single open carrying every member of the family, and no `U` with
`φ^{-1}(A i) ≤ U` for all `i`: each `t i` lives on its own `φ^{-1}(A i)`, which is the shape
`Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections` consumes; see the
implementation notes.

## Main definitions

* `Stacks.InvertiblePullback.IsPullMeromorphicFamily`: `t i` is the regular section of `ℒ` on
  `φ^{-1}(A i)` that the meromorphic product `φ^*(g_i) s` is equal to, for every `i`.

## Main results

* `Stacks.InvertiblePullback.restrictₛₗ_pullbackMeromorphicMul_eq_smul`: a relation
  `g₁ = w g₂` between two meromorphic functions on the base transports to the meromorphic
  products `φ^*(g_k) s`, with nothing assumed of `ℒ` or of `s`.
* `Stacks.InvertiblePullback.restrictₛₗ_eq_smul_of_isPullMeromorphicFamily`: a relation
  `g_i = w g_j` between the *meromorphic* multipliers on a common open of the base transports to
  the relation `t_i = φ^*(w) t_j` between the regular sections, for an invertible `ℒ`. This is
  the whole content of the file: injectivity of `ℒ ⟶ 𝒦_X(ℒ)` is what lets a statement about
  sections of `ℒ` be read off a statement about meromorphic functions.
* `Stacks.InvertiblePullback.forall_mem_generatingLocus_iff_of_isPullMeromorphicFamily`: hence
  `hagree` for the family, from a relation between the meromorphic multipliers alone, with `w`
  regular and a unit at the image point — which is the source's "`g` and `g'` differ
  (multiplicatively) by an element of `𝒪_{Y, y}^*`", the ratio of two meromorphic multipliers of
  one `s` being regular and invertible although neither multiplier is.
* `Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections_of_isPullMeromorphicFamily`:
  the chart datum of
  `StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/ChartFromGenerators.lean` for this
  family. Its conclusion is that of
  `Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections`, unchanged.

## Implementation notes

Every statement here takes as hypotheses the family, its existence property `hex`, and the
relation between its multipliers; a family is constructed in
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/LocalFamilyAgreement.lean`.

**Why the family is meromorphic rather than regular.** A regular formulation — one section `s`
of `ℒ` on an open `U` with `φ^{-1}(A i) ≤ U` for every `i` — has jointly satisfiable hypotheses
only when `U` is all of `X`: with `hex` and `Stacks.SheafOfModules.generatingLocus_le` every
point of `X` lies in some `φ^{-1}(A i) ≤ U`, hence `U = ⊤` and `s` is a global regular
section of `ℒ` — which Tag 0BD7 does not provide. What is used instead is the
source's own vocabulary: with each `t i` on its own open, the same `hex` forces only
`(⨆ i, φ^{-1}(A i)) = ⊤`, a cover, and `s` lives in `𝒦_X(ℒ)` where the first paragraph of the
proof puts it.

Two of the repository's three `IsInvertible` classes occur in the signatures below, and both are
needed: the instance argument is the one
`Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections` takes, and the explicit `hL`
is the one `AlgebraicGeometry.mono_toMeromorphicSectionSheafAsModule` takes. They are distinct
constants with the same single field over different spellings of the structure sheaf of rings.

`w` is bound at the spelling `Γ(Y, A')` that `Stacks.InvertiblePullback`'s unit-germ results use,
and its action on `AlgebraicGeometry.totalQuotientSheafAsModule` is written with the scalar type
as a *named implicit placed before the argument*: a type ascription at that position does not
change the instance that is found, `show _ from _` leaves a `have` in the elaborated statement,
and binding `w` at the `RingCat` spelling makes `(f.app A').hom w` a deterministic `whnf` timeout.
For the same reason the transport lemma is a declaration of its own rather than a step inside the
agreement theorem, which would otherwise exceed the default heartbeat limit.

Every restriction is `PresheafOfModules.restrictₛₗ`, whose codomain is declared: written with
`PresheafOfModules.map` the restricted section lands in a `ModuleCat.restrictScalars` wrapper
whose scalar action is a different instance, and a rewrite by the semilinearity of the
multiplication map then fails to find its own pattern.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.Meromorphic

universe u

namespace Stacks.InvertiblePullback

open Stacks.SheafOfModules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    (s : MeromorphicSection X.sheaf L)
    {ι : Type*} {A : ι → Y.Opens}
    (g : ∀ i, (totalQuotientSheafAsModule Y).val.obj (op (A i)))
    (t : ∀ i, L.val.obj (op ((f ⁻¹ᵁ A i : X.Opens) : Opens X.toRingedSpace.carrier)))

/-- **The family `φ^*(g_i) s` of [Stacks, Tag 0BD7], as a family of regular sections.** `s` is a
meromorphic section of `ℒ`, `g i` a meromorphic function on an open `A i` of the base, and `t i`
a regular section of `ℒ` on `φ^{-1}(A i)` whose image in `𝒦_X(ℒ)` is the product `φ^*(g_i) s`.
That image condition is the membership `g_i ∈ 𝒩(A i)` of the source, stated by
`Stacks.Meromorphic.exists_pullbackDenominatorModuleι_app_eq_iff`; the `t i` is the section of
`ℒ` that membership asserts to exist, named so that it can be handed to the chart. -/
def IsPullMeromorphicFamily : Prop :=
  ∀ i, (pullbackMeromorphicMul f L s).val.app (op (A i)) (g i)
    = ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).map
        (toMeromorphicSectionSheafAsModule X L)).val.app (op (A i)) (t i)

/-- **A relation between the meromorphic multipliers transports to the meromorphic products.**
If `g₁` and `g₂` agree on `A'` up to a factor `w` regular there, then the products `φ^*(g₁) s`
and `φ^*(g₂) s` agree over `A'` up to `w` as well. Only linearity and naturality of the
multiplication map `g ↦ φ^*(g) s` enter: no hypothesis on `ℒ` or on `s`, and no regular section
representing either product. -/
theorem restrictₛₗ_pullbackMeromorphicMul_eq_smul {A₁ A₂ A' : Y.Opens}
    (g₁ : (totalQuotientSheafAsModule Y).val.obj (op A₁))
    (g₂ : (totalQuotientSheafAsModule Y).val.obj (op A₂))
    (h₁ : A' ≤ A₁) (h₂ : A' ≤ A₂) (w : Γ(Y, A'))
    (hw : (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE h₁).op g₁
      = HSMul.hSMul
          (α := (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y)
            Y.sheaf).obj.obj (op A'))
          w ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE h₂).op g₂)) :
    ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj
        (meromorphicSectionSheafAsModule X L)).val.restrictₛₗ (homOfLE h₁).op
        ((pullbackMeromorphicMul f L s).val.app (op A₁) g₁)
      = HSMul.hSMul
          (α := (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y)
            Y.sheaf).obj.obj (op A'))
          w (((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj
            (meromorphicSectionSheafAsModule X L)).val.restrictₛₗ (homOfLE h₂).op
            ((pullbackMeromorphicMul f L s).val.app (op A₂) g₂)) := by
  have hmu : ∀ (C : Y.Opens) (h : A' ≤ C) (x : (totalQuotientSheafAsModule Y).val.obj (op C)),
      (pullbackMeromorphicMul f L s).val.app (op A')
          ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE h).op x)
        = ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj
            (meromorphicSectionSheafAsModule X L)).val.restrictₛₗ (homOfLE h).op
            ((pullbackMeromorphicMul f L s).val.app (op C) x) := by
    intro C h x
    exact PresheafOfModules.naturality_apply _ _ _
  have hsmu : ∀ x : (totalQuotientSheafAsModule Y).val.obj (op A'),
      (pullbackMeromorphicMul f L s).val.app (op A')
          (HSMul.hSMul (α := (Stacks.Sheaves.Differentials.ringSheaf (J :=
            Opens.grothendieckTopology Y)
            Y.sheaf).obj.obj (op A')) w x)
        = HSMul.hSMul (α := (Stacks.Sheaves.Differentials.ringSheaf (J :=
          Opens.grothendieckTopology Y)
            Y.sheaf).obj.obj (op A')) w
            ((pullbackMeromorphicMul f L s).val.app (op A') x) := by
    intro x
    exact map_smul _ _ _
  rw [← hmu A₁ h₁ g₁, hw, hsmu, hmu A₂ h₂ g₂]

/-- **A relation between the meromorphic multipliers transports to the regular sections.** If
`g_i` and `g_j` agree on `A'` up to a factor `w` regular there, then the regular sections `t_i`
and `t_j` representing `φ^*(g_i) s` and `φ^*(g_j) s` agree on `φ^{-1}(A')` up to `φ^*(w)`.

The common factor `s` is cancelled not by dividing but by injectivity of `ℒ ⟶ 𝒦_X(ℒ)` for an
invertible `ℒ` (`AlgebraicGeometry.mono_toMeromorphicSectionSheafAsModule`, the injectivity
clause of [Stacks, Tag 02P0]), pushed forward to `Y`: the two sides have the same image in
`φ_*𝒦_X(ℒ)` because the multiplication map `g ↦ φ^*(g) s` is `𝒪_Y`-linear and natural, so they
are equal. No hypothesis about `s` is needed beyond its being a meromorphic section, and in
particular `s` is nowhere required to be regular. -/
theorem restrictₛₗ_eq_smul_of_isPullMeromorphicFamily
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (ht : IsPullMeromorphicFamily f L s g t)
    (i j : ι) {A' : Y.Opens} (hi : A' ≤ A i) (hj : A' ≤ A j) (w : Γ(Y, A'))
    (hw : (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hi).op (g i)
      = HSMul.hSMul
          (α := (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y)
            Y.sheaf).obj.obj (op A'))
          w ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hj).op (g j)))
    (hpi : ((f ⁻¹ᵁ A' : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A i : X.Opens))
    (hpj : ((f ⁻¹ᵁ A' : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A j : X.Opens)) :
    L.val.restrictₛₗ (homOfLE hpi).op (t i)
      = (f.app A').hom w • L.val.restrictₛₗ (homOfLE hpj).op (t j) := by
  have hrel : ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj L).val.restrictₛₗ
        (homOfLE hi).op (t i)
      = HSMul.hSMul
          (α := (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology Y)
            Y.sheaf).obj.obj (op A'))
          w (((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj L).val.restrictₛₗ
            (homOfLE hj).op (t j)) := by
    have hnu : ∀ (k : ι) (h : A' ≤ A k),
        ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).map
            (toMeromorphicSectionSheafAsModule X L)).val.app (op A')
            (((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj L).val.restrictₛₗ
              (homOfLE h).op (t k))
          = ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj
              (meromorphicSectionSheafAsModule X L)).val.restrictₛₗ (homOfLE h).op
              (((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).map
                (toMeromorphicSectionSheafAsModule X L)).val.app (op (A k)) (t k)) :=
      fun _ _ => PresheafOfModules.naturality_apply _ _ _
    have hsnu : ∀ x : ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).obj L).val.obj
          (op A'),
        ((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).map
            (toMeromorphicSectionSheafAsModule X L)).val.app (op A')
            (HSMul.hSMul (α := (Stacks.Sheaves.Differentials.ringSheaf (J :=
              Opens.grothendieckTopology Y)
              Y.sheaf).obj.obj (op A')) w x)
          = HSMul.hSMul (α := (Stacks.Sheaves.Differentials.ringSheaf (J :=
            Opens.grothendieckTopology Y)
              Y.sheaf).obj.obj (op A')) w
              (((_root_.SheafOfModules.pushforward f.toRingCatSheafHom).map
                (toMeromorphicSectionSheafAsModule X L)).val.app (op A') x) :=
      fun _ => map_smul _ _ _
    refine CategoryTheory.SheafOfModules.app_injective_of_mono
      (mono_pushforward_map f (toMeromorphicSectionSheafAsModule X L)
        (mono_toMeromorphicSectionSheafAsModule X L hL)) (op A') ?_
    rw [hnu i hi, ← ht i,
      restrictₛₗ_pullbackMeromorphicMul_eq_smul f L s (g i) (g j) hi hj w hw, ht j,
      ← hnu j hj, ← hsnu]
  exact hrel

/-- **The agreement hypothesis of the chart of [Stacks, Tag 0BD7] for this family.** The
hypothesis is a relation between the *meromorphic* multipliers on an open of the base, with the
factor `w` regular and a unit at the image point — the source's uniqueness sentence, in which the
two multipliers are meromorphic and their ratio is not. Neither `ℒ`, nor `s`, nor any point of
`X` other than `x` appears in it. -/
theorem forall_mem_generatingLocus_iff_of_isPullMeromorphicFamily
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (ht : IsPullMeromorphicFamily f L s g t)
    (hg : ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∃ (A' : Y.Opens) (hxA : f.base x ∈ A') (hi : A' ≤ A i) (hj : A' ≤ A j) (w : Γ(Y, A')),
        IsUnit (Y.presheaf.germ A' (f.base x) hxA w) ∧
          (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hi).op (g i)
            = HSMul.hSMul (α := (Stacks.Sheaves.Differentials.ringSheaf (J :=
              Opens.grothendieckTopology Y)
                Y.sheaf).obj.obj (op A')) w
                ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hj).op (g j))) :
    ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∀ z : X.toRingedSpace.carrier, f.base z = f.base x →
        (z ∈ generatingLocus L (t i) ↔ z ∈ generatingLocus L (t j)) := by
  refine forall_mem_generatingLocus_iff_of_exists_base_germ_unit f L t fun i j x hxi hxj => ?_
  obtain ⟨A', hxA, hi, hj, w, hwu, hw⟩ := hg i j x hxi hxj
  have hpi : ((f ⁻¹ᵁ A' : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A i : X.Opens) :=
    fun z hz => hi hz
  have hpj : ((f ⁻¹ᵁ A' : X.Opens) : Opens X.toRingedSpace.carrier) ≤ (f ⁻¹ᵁ A j : X.Opens) :=
    fun z hz => hj hz
  exact ⟨A', hxA, hpi, hpj, w, hwu,
    restrictₛₗ_eq_smul_of_isPullMeromorphicFamily f L s g t hL ht i j hi hj w hw hpi hpj⟩

/-- **The chart datum of [Stacks, Tag 0BD7] for the family `φ^*(g_i) s`.** The only hypotheses
left that are not statements about the base are `hex` — that some member of the family generates
`ℒ` at each point of `X` — and the irreducibility of the fibres, which is hypothesis (2) of the
tag through `Stacks.InvertiblePullback.isIrreducible_preimage_singleton_of_isIntegral_fiber`.

The conclusion is that of
`Stacks.InvertiblePullback.exists_chart_nonempty_generatorSections`, which is what
`Stacks.InvertiblePullback.exists_isInvertible_pullback_iso_of_isIntegral_fiber` consumes. No
open of `X` carries the whole family, so `hex` constrains the family only through
`(⨆ i, φ^{-1}(A i)) = ⊤`. -/
theorem exists_chart_nonempty_generatorSections_of_isPullMeromorphicFamily
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L]
    [IsLocallyNoetherian Y]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X) X.sheaf).property
        L)
    (ht : IsPullMeromorphicFamily f L s g t)
    (hex : ∀ z : X.toRingedSpace.carrier, ∃ i, z ∈ generatingLocus L (t i))
    (hirr : ∀ y : Y, IsIrreducible (f.base ⁻¹' {y}))
    (hg : ∀ (i j : ι) (x : X.toRingedSpace.carrier),
      x ∈ generatingLocus L (t i) → x ∈ generatingLocus L (t j) →
      ∃ (A' : Y.Opens) (hxA : f.base x ∈ A') (hi : A' ≤ A i) (hj : A' ≤ A j) (w : Γ(Y, A')),
        IsUnit (Y.presheaf.germ A' (f.base x) hxA w) ∧
          (totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hi).op (g i)
            = HSMul.hSMul (α := (Stacks.Sheaves.Differentials.ringSheaf (J :=
              Opens.grothendieckTopology Y)
                Y.sheaf).obj.obj (op A')) w
                ((totalQuotientSheafAsModule Y).val.restrictₛₗ (homOfLE hj).op (g j)))
    (hfiber : ∀ y : Y, Nonempty (f.fiber y))
    (hfinite : QuasiCompact f ∨ LocallyOfFiniteType f) :
    ∃ chart : Y → Y.Opens, (∀ y, y ∈ chart y) ∧
      ∀ y, Nonempty (GeneratorSections X.toRingedSpace L (f ⁻¹ᵁ chart y)) :=
  exists_chart_nonempty_generatorSections f L t hex hirr
    (forall_mem_generatingLocus_iff_of_isPullMeromorphicFamily f L s g t hL ht hg) hfiber hfinite

end Stacks.InvertiblePullback

end
