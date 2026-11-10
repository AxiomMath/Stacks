module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import StacksFrontier.AlgebraicGeometry.Crystalline.FCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.DerivedTensorBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal
public import StacksFrontier.Homology.ExtendScalars.Flat

/-!
# Inverting `p` on `D(A)`, and the statement of [Stacks, Tag 07N5]

[Stacks, Tag 07N5] says that in Situation [Stacks, Tag 07N2], for `(E, F_E)` a nondegenerate
`F`-crystal over a `p`-adically complete Noetherian `A` with `X → S₀` proper smooth, the canonical
map

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

**becomes an isomorphism after inverting `p`**.

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/DerivedTensorBaseChange.lean` built the
source and the target of that map and wrote down its type, `FrobeniusMap07N5`, and recorded at its
lines 175-177 that the conclusion could not be stated at all, "there being no localization of a
derived category of modules at an element of the ring in this library".

**That is what this file supplies, and it needed no new localization of a category.**  "After
inverting `p`" is a change of coefficient ring, `A ⟶ A[1/p]`, not a localization of the
triangulated category `D(A)`: the assertion is that the image of the map under
`- ⊗_A A[1/p] : D(Mod_A) ⥤ D(Mod_{A[1/p]})` is an isomorphism.  Since `A[1/p]` is a localization
of `A` it is flat over `A`, so extension of scalars along `A ⟶ A[1/p]` is an exact functor of
abelian categories and induces a functor of derived categories degreewise, by Mathlib's
`CategoryTheory.Functor.mapDerivedCategory`.  That functor is `invertPrime` below, and
`BecomesIsoAfterInvertingPrime` is the conclusion of the tag read at a given morphism of `D(A)`.

Two consequences worth recording.

**No choice is involved.**  `invertPrime` is the functor induced *degreewise* by `- ⊗_A A[1/p]`,
not a total left derived functor chosen by `Classical.choice` the way
`Crystalline.GlobalCrystallineSituation.SmallSite.derivedBaseChangeTensor` must be.  The
derivation is unnecessary precisely because the ring map is flat; this is the same observation
`StacksFrontier/RingTheory/Dualizing/LocalizationTransport.lean` makes, where the two are compared
and shown isomorphic for an exact extension of scalars.  So `invertPrime` *is* `- ⊗^L_A A[1/p]`,
and the statement below does not depend on a choice.

**Nothing weaker is being asserted.**  The nearby [Stacks, Tag 07QB] and [Stacks, Tag 07QA]
conclude that a map has kernel and cokernel annihilated by a power of `p`, and the library has a
developed vocabulary for that in
`StacksFrontier/AlgebraicGeometry/Crystalline/AlphaPCoverCohomologyBound.lean`.  That vocabulary is
*not* used here.  Annihilation of the kernel and cokernel by a fixed power of `p` implies, but is
not implied by, becoming an isomorphism after inverting `p` — the two agree only for bounded
complexes with finitely generated cohomology — so stating 07N5 that way would state a different
theorem.  `BecomesIsoAfterInvertingPrime` is the tag's own conclusion and not a surrogate for it.

## The hypotheses, and where each comes from

Situation [Stacks, Tag 07N2] is `Crystalline.FCrystalSituation`, which carries the underlying
Situation [Stacks, Tag 07MF], the affineness of `S` (so that `A = Γ(S, 𝒪_S)`), the membership of
`p` in the divided power ideal, and the divided power endomorphism `σ` lifting the absolute
Frobenius.  Everything 07N5 assumes beyond that situation is an explicit hypothesis of
`Statement07N5`:

| source hypothesis | spelling here |
| --- | --- |
| `(E, F_E)` is an `F`-crystal | `E : Crystalline.FCrystal T`, the 07N3 structure |
| `(E, F_E)` is nondegenerate | `E.Nondegenerate`, the 07N3 predicate |
| `A` is Noetherian | `IsNoetherianRing ↥Γ(S, 𝒪_S)` |
| `A` is `p`-adically complete | `IsAdicComplete (Ideal.span {(p : A)}) A` |
| `X → S₀` is proper | `IsProper S.toClosedFiber` |
| `X → S₀` is smooth | `Smooth S.toClosedFiber` |
| the map becomes an isomorphism | `BecomesIsoAfterInvertingPrime` |
| after inverting `p` | |

No coefficient hypothesis is stated twice.  `Crystalline.FCrystal` already carries
`Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal` on its underlying
sheaf, and that **is** 07N3's "crystal in finite locally free `𝒪_{X/S}`-modules", the notion of
[Stacks, Tag 07IU]: quasi-coherence in the sense of [Stacks, Tag 07IS](2) — which by
[Stacks, Tag 07IT] is what "crystal in quasi-coherent modules" means — together with finite local
freeness.  Adding a further coefficient predicate alongside it would assume more than the source
does and make the proposition strictly weaker than the tag.

`Crystalline.FCrystal` is deliberately not built on
`...GlobalCrystallineSituation.IsFiniteLocallyFreeCrystal`, which reads the crystal
condition with the comparison maps of *presheaves* of modules, which is strictly stronger than
[Stacks, Tag 07IS](3) and carries no tag, so an `F`-crystal built on it would be a narrower class
of objects than 07N3's and an assertion about it would not be the tag.  See the module
documentation of `StacksFrontier/AlgebraicGeometry/Crystalline/FCrystal.lean`.

Nor is any hypothesis dropped.  Noetherianness, `p`-adic completeness and proper smoothness are
all standing hypotheses of 07N5 — they are what let its proof invoke [Stacks, Tag 07MY], that
`RΓ(Cris(X/S), E)` is a perfect object of `D(A)` — and a statement omitting them would assert
something stronger than, and so not, the tag.  None is used by anything below, because nothing
below is proved; they are present because the proposition is the tag's and not a weakening of it.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `invertPrimeRing` — the ring `A[1/p]`, as `Localization.Away (p : A)`.
* `invertPrimeRingHom` — the ring map `A ⟶ A[1/p]`.
* `invertPrime` — **the functor `- ⊗_A A[1/p] : D(Mod_A) ⥤ D(Mod_{A[1/p]})`**, which is what
  "inverting `p`" means on the derived category of modules.
* `BecomesIsoAfterInvertingPrime` — **the conclusion of [Stacks, Tag 07N5] read at a given
  morphism of `D(Mod_A)`**: its image under `invertPrime` is an isomorphism.
* `toSmallFCrystal` — **the sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` underlying an
  `F`-crystal**, the restriction along `Cris(X/S) ⥤ CRIS(X/S)` of its module on the big site.
* `Statement07N5` — **the statement of [Stacks, Tag 07N5]**, with its standing hypotheses, for
  the one input the library is still missing carried as a parameter.

## Main results

* `invertPrimeRingHom_flat` — `A ⟶ A[1/p]` is flat, which is what makes `invertPrime` exist as a
  functor induced degreewise rather than as a derived functor.
* `isIso_nsmul_id_invertPrime_obj` — **`p ^ n` acts invertibly on every object in the image of
  `invertPrime`**, which is what certifies that the functor really does invert `p`.
* `becomesIsoAfterInvertingPrime_of_comp_eq_nsmul` — **a morphism with a two-sided inverse up to a
  power of `p` becomes an isomorphism after inverting `p`**.  This is the criterion by which the
  third of the three maps the source's proof factors through becomes an isomorphism, `F_E` having
  an inverse up to a power of `p` by nondegeneracy.  It is proved here for an arbitrary morphism
  of `D(Mod_A)`, and it *is* applied to that third map, in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusCohomologyIsogeny.lean`.

## Where the tag is proved

**No `@[stacks 07N5]` attribute is placed in this file.**  `Statement07N5` is the statement of the
tag; it is proved at the canonical map `...SmallSite.frobeniusMap07N5Canonical` (constructed in
`SmallSite/FrobeniusDerivedGlobalSections.lean`) as
`Crystalline.GlobalCrystallineSituation.SmallSite.statement07N5` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/Frobenius07N5Theorem.lean`, where the tag is
registered and whose documentation describes the proof through the three arrows (07QC), (07N6)
and (07QD).  What this file contributes is the vocabulary of the conclusion: the functor
`invertPrime`, the flatness that makes it the degreewise one, the invertibility of `p` on its
values, and the criterion `becomesIsoAfterInvertingPrime_of_comp_eq_nsmul`.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 07N4](https://stacks.math.columbia.edu/tag/07N4)
* [Stacks Project, Tag 07MY](https://stacks.math.columbia.edu/tag/07MY)
* [Stacks Project, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wA wP

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-! ### Inverting `p` on the derived category of `A`-modules -/

/-- **The ring `A[1/p]`**, where `A = Γ(S, 𝒪_S)` is the base ring of a global crystalline
situation and `p` is its distinguished prime: the localization of `A` away from `p`. -/
abbrev invertPrimeRing : Type u := Localization.Away (S.p : Γ(S.S.scheme, ⊤))

/-- **The ring map `A ⟶ A[1/p]`**, the structure map of the localization away from `p`. -/
abbrev invertPrimeRingHom : ↥Γ(S.S.scheme, ⊤) →+* invertPrimeRing S := algebraMap _ _

/-- **`A ⟶ A[1/p]` is flat**, a localization being flat over the ring it localizes.  This is what
makes extension of scalars along it exact, and so lets `invertPrime` be the functor induced
degreewise on derived categories rather than a derived functor. -/
theorem invertPrimeRingHom_flat : (invertPrimeRingHom S).Flat :=
  RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (invertPrimeRing S) (Submonoid.powers (S.p : Γ(S.S.scheme, ⊤))))

/-- Extension of scalars along `A ⟶ A[1/p]` preserves finite limits, by flatness. -/
instance extendScalarsInvertPrime_preservesFiniteLimits :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} (invertPrimeRingHom S)) :=
  extendScalars_preservesFiniteLimits_of_flat'.{u, u + 1} _ (invertPrimeRingHom_flat S)

/-- Extension of scalars along `A ⟶ A[1/p]` preserves finite colimits: it is a left adjoint, so
it preserves all colimits. -/
instance extendScalarsInvertPrime_preservesFiniteColimits :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} (invertPrimeRingHom S)) :=
  have : PreservesColimitsOfSize.{0, 0}
      (ModuleCat.extendScalars.{u, u, u + 1} (invertPrimeRingHom S)) :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
      (invertPrimeRingHom S)).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Extension of scalars along `A ⟶ A[1/p]` is additive. -/
instance extendScalarsInvertPrime_additive :
    (ModuleCat.extendScalars.{u, u, u + 1} (invertPrimeRingHom S)).Additive :=
  extendScalars_additive.{u, u, u + 1} _

variable [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
  [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing S))]

/-- **Inverting `p`: the functor `- ⊗_A A[1/p] : D(Mod_A) ⥤ D(Mod_{A[1/p]})`.**

This is what "after inverting `p`" means for an object or a map of the derived category of
`A`-modules: not a localization of the triangulated category `D(A)`, but the change of coefficient
ring along `A ⟶ A[1/p]`.  Because that ring map is flat (`invertPrimeRingHom_flat`), extension of
scalars along it is exact and the functor of derived categories it induces is the degreewise one,
`CategoryTheory.Functor.mapDerivedCategory`, so no derived functor and no choice is needed. -/
def invertPrime : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) ⥤
    DerivedCategory (ModuleCat.{u + 1} (invertPrimeRing S)) :=
  (ModuleCat.extendScalars.{u, u, u + 1} (invertPrimeRingHom S)).mapDerivedCategory

/-- **The conclusion of [Stacks, Tag 07N5] read at a given morphism of `D(Mod_A)`**: the morphism
becomes an isomorphism after inverting `p`, that is, its image under `invertPrime` is an
isomorphism of `D(Mod_{A[1/p]})`.

This is the tag's own conclusion.  It is *not* the weaker-looking but strictly stronger assertion
that the kernel and cokernel of the morphism are killed by a fixed power of `p`, which is what
[Stacks, Tag 07QA] and [Stacks, Tag 07QB] conclude about their maps; the module docstring explains
why that form is not used here. -/
def BecomesIsoAfterInvertingPrime {X Y : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))}
    (φ : X ⟶ Y) : Prop :=
  IsIso ((invertPrime S).map φ)

/-- Inverting `p` is an additive functor, so it carries a multiple of an identity to the same
multiple of an identity.  It is in fact exact — `invertPrime` is triangulated, being induced by an
exact functor — but only additivity is needed below. -/
instance invertPrime_additive : (invertPrime S).Additive :=
  inferInstanceAs (ModuleCat.extendScalars.{u, u, u + 1}
    (invertPrimeRingHom S)).mapDerivedCategory.Additive

/-- **`p ^ n` acts invertibly on everything in the image of `invertPrime`.**  The image lies in
`D(Mod_{A[1/p]})`, which is `A[1/p]`-linear, and `p` is a unit of `A[1/p]` because `A[1/p]` is a
localization of `A` at a submonoid containing `p`; an invertible scalar acts invertibly in a
linear category.

This certifies that `invertPrime` really does invert `p`, so that
`BecomesIsoAfterInvertingPrime` asserts what its name says rather than merely some change of
coefficient rings. -/
theorem isIso_nsmul_id_invertPrime_obj (n : ℕ)
    (K : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))) :
    IsIso ((S.p ^ n) • 𝟙 ((invertPrime S).obj K)) := by
  have h : IsUnit (algebraMap ↥Γ(S.S.scheme, ⊤) (invertPrimeRing S) (S.p : Γ(S.S.scheme, ⊤))) :=
    IsLocalization.map_units (invertPrimeRing S)
      ⟨(S.p : Γ(S.S.scheme, ⊤)), Submonoid.mem_powers _⟩
  rw [map_natCast] at h
  obtain ⟨v, hv⟩ := h.pow n
  rw [← Nat.cast_smul_eq_nsmul (invertPrimeRing S), Nat.cast_pow, ← hv]
  refine ⟨⟨((v⁻¹ : (invertPrimeRing S)ˣ) : invertPrimeRing S) • 𝟙 _, ?_, ?_⟩⟩
  · rw [Linear.smul_comp, Category.id_comp, smul_smul, Units.mul_inv, one_smul]
  · rw [Linear.smul_comp, Category.id_comp, smul_smul, Units.inv_mul, one_smul]

/-- **A morphism with a two-sided inverse up to a power of `p` becomes an isomorphism after
inverting `p`.**

This is the elementary criterion by which the third of the three maps that the proof of
[Stacks, Tag 07N5] factors its map through becomes an isomorphism: `F_E` has an inverse up to a
power of `p` precisely because the `F`-crystal is nondegenerate.  The hypothesis asked for here is
the two-sided one, and the one-sided condition of `Crystalline.FCrystal.Nondegenerate` upgrades to
it when the rank of the crystal is bounded, which is [Stacks, Tag 07N4] — proved as
`Crystalline.FCrystal.exists_pow_nsmul_kernel_cokernel_eq_zero_of_boundedCommonLocalRank`.

What this does *not* do is apply that criterion to 07N5's map, which would need the map to exist;
see the module docstring. -/
theorem becomesIsoAfterInvertingPrime_of_comp_eq_nsmul
    {X Y : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))} (φ : X ⟶ Y) (ψ : Y ⟶ X) (n : ℕ)
    (hφψ : φ ≫ ψ = (S.p ^ n) • 𝟙 X) (hψφ : ψ ≫ φ = (S.p ^ n) • 𝟙 Y) :
    BecomesIsoAfterInvertingPrime S φ := by
  change IsIso ((invertPrime S).map φ)
  have key : ∀ {X Y : DerivedCategory (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))} (φ : X ⟶ Y)
      (ψ : Y ⟶ X), φ ≫ ψ = (S.p ^ n) • 𝟙 X →
      IsSplitMono ((invertPrime S).map φ) ∧ IsSplitEpi ((invertPrime S).map ψ) := by
    intro X Y φ ψ h
    have := isIso_nsmul_id_invertPrime_obj S n X
    have h1 : (invertPrime S).map φ ≫ (invertPrime S).map ψ =
        (S.p ^ n) • 𝟙 ((invertPrime S).obj X) := by
      rw [← Functor.map_comp, h, Functor.map_nsmul, CategoryTheory.Functor.map_id]
    exact ⟨IsSplitMono.mk' ⟨(invertPrime S).map ψ ≫ inv ((S.p ^ n) • 𝟙 _), by
        rw [← Category.assoc, h1, IsIso.hom_inv_id]⟩,
      IsSplitEpi.mk' ⟨inv ((S.p ^ n) • 𝟙 _) ≫ (invertPrime S).map φ, by
        rw [Category.assoc, h1, IsIso.inv_hom_id]⟩⟩
  have := (key φ ψ hφψ).1
  have := (key ψ φ hψφ).2
  exact isIso_of_mono_of_isSplitEpi _

/-! ### The underlying module of an `F`-crystal, on the small crystalline site -/

/-- **The sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` underlying an `F`-crystal.**

`Crystalline.FCrystal.crystal` is a sheaf of modules on the **big** crystalline site
`CRIS(X/S)`, while `RΓ(Cris(X/S), -)` — and hence `FrobeniusMap07N5` — takes a sheaf on the
**small** one.  The passage between them is restriction along the inclusion
`Cris(X/S) ⥤ CRIS(X/S)`, which is the comparison `i_X^{-1}` of [Stacks, Tag 07IM] and is what
the source means by reading the cohomology of an `F`-crystal on the small site.  It is
`Crystalline.GlobalCrystallineSituation.SmallSite.restrictSheafOfModules`, already in the
library and already at the module universe `u` that both sides use, so no construction is
needed here.

The module docstring used to list this passage as one of two missing ingredients of
[Stacks, Tag 07N5], carried as the parameter `toSmall` of `Statement07N5`.  That was wrong, and
`Statement07N5` now uses this. -/
def toSmallFCrystal {T : Crystalline.FCrystalSituation.{u}} (E : Crystalline.FCrystal T) :
    SheafOfModules.{u} (structureSheaf T.global) :=
  restrictSheafOfModules E.crystal

/-- **The module on `Cris(X/S)` underlying an `F`-crystal is a crystal there.**  An `F`-crystal is
a crystal in finite locally free `𝒪_{X/S}`-modules in the sense of [Stacks, Tag 07IU], which this
library reads — as the source permits, the two forms of [Stacks, Tag 07IT] being declared
interchangeable — as quasi-coherence together with finite local freeness,
`Crystalline.GlobalCrystallineSituation.IsFiniteLocallyFreeQuasicoherentCrystal`.  So the crystal
property of the module is present in the `F`-crystal, but as form (1); getting it out as the
comparison-map condition of [Stacks, Tag 07IS](3) is exactly the implication (1) ⟹ (2) of
[Stacks, Tag 07IT], of which the library proves only the locally-quasi-coherent half
(`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite`).  That
implication is therefore the argument `h07IT` here, in the same shape in which
`Crystalline.GlobalCrystallineSituation.SmallSite.Computes07LG` and the `07JG` development carry
it, read on `CRIS(X/S)` because that is the site the `F`-crystal's module lives on.  The
sheaf-level condition it yields on `CRIS(X/S)` then descends along the restriction to the small
site by
`Crystalline.GlobalCrystallineSituation.SmallSite.isSheafCrystal_restrictSheafOfModules`.

This is what makes `toSmallFCrystal` the passage the source intends and not an arbitrary choice
of functor: it lands in the crystals, where the cohomology of [Stacks, Tag 07N5] is taken.

For a module already known to satisfy the sheaf-level crystal condition on `CRIS(X/S)` no input is
needed: `isSheafCrystal_restrictSheafOfModules` applies to it directly, and
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isCrystal` supplies that condition from
the presheaf-level one. -/
theorem isSheafCrystal_toSmallFCrystal {T : Crystalline.FCrystalSituation.{u}}
    (h07IT : ∀ F : SheafOfModules.{u} (crystallineStructureSheaf T.global),
      F.IsQuasicoherentOnSite → Crystalline.GlobalCrystallineSituation.IsSheafCrystal F)
    (E : Crystalline.FCrystal T) : IsSheafCrystal (toSmallFCrystal E) :=
  isSheafCrystal_restrictSheafOfModules
    (h07IT _ E.isFiniteLocallyFreeQuasicoherentCrystal.isQuasicoherentOnSite)

/-! ### The statement of [Stacks, Tag 07N5] -/

/-- **The statement of [Stacks, Tag 07N5].**  In Situation [Stacks, Tag 07N2], let `(E, F_E)` be a
nondegenerate `F`-crystal, let `A = Γ(S, 𝒪_S)` be Noetherian and `p`-adically complete and let
`X → S₀` be proper and smooth.  Then the canonical map

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

becomes an isomorphism after inverting `p`.

The `F`-crystal and its nondegeneracy are the [Stacks, Tag 07N3] `Crystalline.FCrystal` and
`Crystalline.FCrystal.Nondegenerate`; the map lives in the type `FrobeniusMap07N5`, whose source
`RΓ(Cris(X/S), E) ⊗^L_{A, σ} A` is
`Crystalline.GlobalCrystallineSituation.SmallSite.frobeniusDerivedBaseChangeTensorGlobalSections`
and whose twist is `σ` by
`Crystalline.GlobalCrystallineSituation.SmallSite.baseChangeRingHom_specSigma`.

**One** parameter is carried: `frobeniusMap`, the map `F_E ∘ (F_X)^*_cris` itself.  With the
canonical choice of it this is the tag verbatim; for an arbitrary choice it is formally stronger.
That canonical choice is available, as
`Crystalline.GlobalCrystallineSituation.SmallSite.frobeniusMap07N5Canonical` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FrobeniusDerivedGlobalSections.lean`, and at
it this proposition is equivalent to the isogeny of the first two arrows of the source's proof,
`...SmallSite.statement07N5_canonical_iff_baseChangeArrows07N5Isogeny`.

The underlying sheaf of modules on the small site is **not** a parameter: it is
`toSmallFCrystal`, the restriction along `Cris(X/S) ⥤ CRIS(X/S)` of the `F`-crystal's module,
which `isSheafCrystal_toSmallFCrystal` shows is a crystal on the small site once the implication
(1) ⟹ (2) of [Stacks, Tag 07IT] is supplied.  So this statement is pinned to the
source's own reading at that argument instead of being quantified over an arbitrary functor.

This is the statement; it is proved at the canonical map as
`...SmallSite.statement07N5` (`SmallSite/Frobenius07N5Theorem.lean`), where the tag is
registered. -/
def Statement07N5 (T : Crystalline.FCrystalSituation.{u})
    [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
    [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
    [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))]
    (frobeniusMap : ∀ E : Crystalline.FCrystal T, FrobeniusMap07N5 T (toSmallFCrystal E)) :
    Prop :=
  IsNoetherianRing ↥Γ(T.global.S.scheme, ⊤) →
    IsAdicComplete (Ideal.span {(T.global.p : Γ(T.global.S.scheme, ⊤))})
        ↥Γ(T.global.S.scheme, ⊤) →
      IsProper T.global.toClosedFiber → Smooth T.global.toClosedFiber →
        ∀ E : Crystalline.FCrystal T, E.Nondegenerate →
          BecomesIsoAfterInvertingPrime T.global (frobeniusMap E)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
