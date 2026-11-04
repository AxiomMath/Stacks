module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Sections
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterionMain

/-!
# Descent of finiteness of the sections over an open of a Noetherian affine scheme

Let `A` be a Noetherian ring and `V` an open of `Spec A`. This file collects the ways in which
finiteness of the `A`-module `Γ(Spec A, V)` travels along a ring map `φ : A ⟶ B`: it is preserved
by any flat `φ` and reflected by any faithfully flat one. These are the module-level statements
corresponding to the sheaf-level ones of
`StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterionMain`, and they are
what the reduction steps of [Stacks, Tag 0BK1] consume.

## Main results

* `Stacks.LocalCohomology.module_finite_sections_preimage_of_flat_of_isNoetherianRing`:
  `Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_sections_preimage_of_flat` with its two
  topological hypotheses discharged — over a Noetherian affine base every open is automatically
  quasi-compact and quasi-separated, because `Spec A` is then a Noetherian space.
* `Stacks.LocalCohomology.module_finite_sections_preimage_of_isLocalizationAtPrime`: the same at a
  localization of `A` at a prime, which is the direction of the localization reduction of
  [Stacks, Tag 0AW9] that is immediate.
* `Stacks.LocalCohomology.module_finite_sections_of_module_finite_sections_preimage`: finiteness
  of the sections *descends* along a faithfully flat map of Noetherian affine schemes.
* `Stacks.LocalCohomology.module_finite_sections_preimage_iff_of_flat_surjective`: the two
  together, as an equivalence.

## What [Stacks, Tag 0AW9] still needs

No `@[stacks 0AW9]` attribute is attached to anything here, and none may be. The tag states, for
`A` Noetherian, `I ⊂ A` an ideal, `M` a finite `A`-module, `Z = V(I)` and `n ≥ 0`, that the local
cohomology modules `H^i_Z(M)` are finite `A`-modules for `i ≤ n` if and only if `H^i_Z(M)_𝔭` is a
finite `A_𝔭`-module for every prime `𝔭` and every `i ≤ n`. That statement cannot be written in
this library at all: there is no local cohomology *module* `H^i_Z(M)`. The two constructions the
repository has — `Stacks.LocalCohomology.localCohomologyWithSupportInPlus` and
`Dualizing.localCohomology` — both
take an object of a derived category rather than a module, and nothing instantiates either at a
single module; there is no long exact sequence, no compatibility with localization
([Stacks, Tag 0ALZ]), and no finiteness statement about a local cohomology module anywhere.

Reading the tag off the sections instead does not make it cheaper. The shape that
[Stacks, Tag 0BK1] actually consumes is obtained by combining it with [Stacks, Tag 0BK0]:

```
A : Type u
inst : CommRing A
inst : IsNoetherianRing A
V : (Spec (CommRingCat.of A)).Opens
h : ∀ p : PrimeSpectrum A,
      Module.Finite (Localization.AtPrime p.asIdeal)
        Γ(Spec (CommRingCat.of (Localization.AtPrime p.asIdeal)),
          Spec.map (CommRingCat.ofHom
            (algebraMap A (Localization.AtPrime p.asIdeal))) ⁻¹ᵁ V)
⊢ Module.Finite A Γ(Spec (CommRingCat.of A), V)
```

and this is the first unproved step. It is *not* an instance of flat descent, so none of the
lemmas below reach it: the family `{Spec A_𝔭 → Spec A}` indexed by all primes is faithfully flat
but need not be quasi-compact — finitely many of its members cover `Spec A` only when `A` is
semi-local — so in general it is not an fpqc covering and
`Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_of_pullback_fpqcCover` ([Stacks, Tag 05AZ])
does not apply to it. Nor is finiteness of a quasi-coherent module a stalk-local condition: over
`A = ℤ` the module `⨁_p ℤ/p` has every localization finite and is not finite. The tag is true for
`Γ(Spec A, V)` only because `H^i_Z(A)` is `I`-power torsion, which is what lets the Stacks proof
bound `Ass(H^i_Z(A))` and then annihilate the whole module by a single power `I^e`
([Stacks, Tag 0AW8], also absent). Everything in that argument is missing, starting with the
object `H^i_Z(M)` itself.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.LocalCohomology

/-! ### Flat base change over a Noetherian affine base -/

/-- **Flat base change preserves finiteness of the sections over an open of a Noetherian affine
scheme.** Let `φ : A ⟶ B` be a flat ring map with `A` Noetherian and let `V` be an open of
`Spec A`. If `Γ(Spec A, V)` is a finite `A`-module then `Γ(Spec B, Spec.map φ ⁻¹ᵁ V)` is a finite
`B`-module.

This is `Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_sections_preimage_of_flat` with its
two instance hypotheses on `V.toScheme` discharged: neither `CompactSpace` nor
`QuasiSeparatedSpace` is found by instance search for an open of `Spec A`, but both follow from
`Stacks.AlgebraicGeometry.FlatBaseChange.noetherianSpace_opens` once `A` is Noetherian, because
`Spec` of a Noetherian ring is a Noetherian space. -/
theorem module_finite_sections_preimage_of_flat_of_isNoetherianRing {A B : CommRingCat.{u}}
    [IsNoetherianRing A] (φ : A ⟶ B) (hφ : φ.hom.Flat) (V : (Spec A).Opens)
    (hfin : Module.Finite (ToType A) Γ(Spec A, V)) :
    Module.Finite (ToType B) Γ(Spec B, Spec.map φ ⁻¹ᵁ V) := by
  have hV : NoetherianSpace V.toScheme :=
    Stacks.AlgebraicGeometry.FlatBaseChange.noetherianSpace_opens V
  have : CompactSpace V.toScheme := NoetherianSpace.compactSpace _
  have : QuasiSeparatedSpace V.toScheme := NoetherianSpace.to_quasiSeparatedSpace
  exact Stacks.AlgebraicGeometry.FlatBaseChange.module_finite_sections_preimage_of_flat φ hφ V hfin

/-- **Finiteness of the sections over an open passes to a localization at a prime.** Let `A` be a
Noetherian ring, `𝔭` a prime of `A`, `B` a localization of `A` at `𝔭` and `V` an open of
`Spec A`. If `Γ(Spec A, V)` is a finite `A`-module then its base change to `B` — the sections of
`𝒪` over the preimage of `V` in `Spec B` — is a finite `B`-module.

This is the implication `(1) ⇒ (2)` of [Stacks, Tag 0AW9], read on the sections rather than on
the local cohomology modules: a localization is flat, so
`module_finite_sections_preimage_of_flat_of_isNoetherianRing` applies. The converse — which is
the content of that tag, and the step [Stacks, Tag 0BK1] needs — is not proved; see the module
docstring.

`B` is a *variable* of `CommRingCat` rather than `CommRingCat.of (Localization.AtPrime 𝔭)`: for a
concrete `CommRingCat.of` the instance `Algebra ↑(CommRingCat.of C) Γ(Spec (CommRingCat.of C), U)`
is not found, because it is keyed on the `CommRing` instance carried by `CommRingCat` and instance
search finds `C`'s own instead. Applying this lemma at a concrete localization is fine; stating it
there is not. -/
theorem module_finite_sections_preimage_of_isLocalizationAtPrime {A B : CommRingCat.{u}}
    [IsNoetherianRing A] [Algebra (ToType A) (ToType B)] (p : PrimeSpectrum (ToType A))
    [IsLocalization.AtPrime (ToType B) p.asIdeal] (V : (Spec A).Opens)
    (hfin : Module.Finite (ToType A) Γ(Spec A, V)) :
    Module.Finite (ToType B)
      Γ(Spec B, Spec.map (CommRingCat.ofHom (algebraMap (ToType A) (ToType B))) ⁻¹ᵁ V) :=
  module_finite_sections_preimage_of_flat_of_isNoetherianRing
    (CommRingCat.ofHom (algebraMap (ToType A) (ToType B)))
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ p.asIdeal.primeCompl)) V hfin

/-! ### Faithfully flat descent over a Noetherian affine base -/

/-- **Finiteness of the sections over an open descends along a faithfully flat map of Noetherian
affine schemes.** Let `φ : A ⟶ B` be a ring map between Noetherian rings with `Spec φ` flat and
surjective, and let `V` be an open of `Spec A`. If `Γ(Spec B, Spec.map φ ⁻¹ᵁ V)` is a finite
`B`-module then `Γ(Spec A, V)` is a finite `A`-module.

This is the module-level form of
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_flat_surjective`, obtained from
it by the two equivalences between coherence of the direct image and finiteness of the sections
over a Noetherian affine base: `isCoherent_pushforward_structureSheaf_of_module_finite_sections`
turns the hypothesis into coherence over `Spec B`, the descent carries that to `Spec A`, and
`module_finite_sections_of_isCoherent` reads the conclusion back off the sections. -/
theorem module_finite_sections_of_module_finite_sections_preimage {A B : CommRingCat.{u}}
    [IsNoetherianRing A] [IsNoetherianRing B] {φ : A ⟶ B} (hflat : Flat (Spec.map φ))
    (hsurj : Surjective (Spec.map φ)) (V : (Spec A).Opens)
    (hfin : Module.Finite (ToType B) Γ(Spec B, Spec.map φ ⁻¹ᵁ V)) :
    Module.Finite (ToType A) Γ(Spec A, V) :=
  module_finite_sections_of_isCoherent A V
    (isCoherent_pushforward_structureSheaf_of_flat_surjective hflat hsurj V
      (isCoherent_pushforward_structureSheaf_of_module_finite_sections B
        (Spec.map φ ⁻¹ᵁ V) hfin))

/-- **Finiteness of the sections over an open is insensitive to a faithfully flat base change of
Noetherian affine schemes.** For `φ : A ⟶ B` between Noetherian rings with `Spec φ` flat and
surjective, and `V` an open of `Spec A`, the `B`-module `Γ(Spec B, Spec.map φ ⁻¹ᵁ V)` is finite
exactly when the `A`-module `Γ(Spec A, V)` is.

The two directions are `module_finite_sections_preimage_of_flat_of_isNoetherianRing` and
`module_finite_sections_of_module_finite_sections_preimage`. Applied at the completion map of a
Noetherian local ring — flat and surjective on spectra by
`flat_specMap_adicCompletion` and `surjective_specMap_adicCompletion` — this is the last step of
[Stacks, Tag 0BK1] read on the sections. -/
theorem module_finite_sections_preimage_iff_of_flat_surjective {A B : CommRingCat.{u}}
    [IsNoetherianRing A] [IsNoetherianRing B] {φ : A ⟶ B} (hflat : Flat (Spec.map φ))
    (hsurj : Surjective (Spec.map φ)) (V : (Spec A).Opens) :
    Module.Finite (ToType B) Γ(Spec B, Spec.map φ ⁻¹ᵁ V) ↔
      Module.Finite (ToType A) Γ(Spec A, V) :=
  ⟨module_finite_sections_of_module_finite_sections_preimage hflat hsurj V,
    module_finite_sections_preimage_of_flat_of_isNoetherianRing φ
      (AlgebraicGeometry.Flat.SpecMap_iff.mp hflat) V⟩

end Stacks.LocalCohomology

end
