module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PuncturedSpectrumSchemeStalks
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardOpensRangeTransport
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SectionsFinitenessIsLocal
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SmallerOpenPushforwardMono
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.FiniteModule
public import Mathlib.RingTheory.Localization.LocalizationLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The recursion of [Stacks, Tag 0BK1]

The argument of [Stacks, Tag 0BK1] first reduces the tag to the punctured spectra of the local
rings along the complement: for an open immersion `j' : W ⟶ Z` of a nonempty scheme into an
integral locally Noetherian scheme, `j'_*𝒪_W` is coherent as soon as the direct image of the
structure sheaf of the punctured spectrum of `𝒪_{Z,z}` is coherent at every point `z` outside the
image of `j'`. This file proves that reduction,
`Stacks.LocalCohomology.puncturedSpectrumReduction`. It is a Noetherian induction on the Krull
dimension of the local rings along the complement, whose step is
`Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_of_basicOpen_le`; the file holds
the pieces of the wiring around that step and the induction itself.

## Main results

* `Stacks.LocalCohomology.primeIdealOf_fromSpec`: the primes of `Γ(Z, V)` and the points of an
  affine open `V` of `Z` are matched by `IsAffineOpen.fromSpec` and `IsAffineOpen.primeIdealOf`,
  in the direction Mathlib does not record.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_bot`: the degenerate case of an
  empty open.
* `Stacks.LocalCohomology.opensRange_preimage_ι_comp_ι`: for a nested pair of opens `V' ≤ P` the
  composite `(P.ι ⁻¹ᵁ V').ι ≫ P.ι` has image `V'`, which is what lets
  `isCoherent_pushforward_structureSheaf_of_opensRange_eq` identify the conclusion of the
  inductive step with the statement being proved.
* `Stacks.LocalCohomology.exists_section_basicOpen_le`: the function the inductive step consumes —
  a nonzero global function on `P` whose principal open lies inside `V'`.
* `Stacks.LocalCohomology.isCoherent_pushforward_structureSheaf_puncturedSpectrum_comap`: the
  coherence hypothesis at a prime of `Γ(Z, V)` read at a prime of the localization
  `Localization.AtPrime 𝔭`, which is where the inductive hypothesis needs it.
* `Stacks.LocalCohomology.puncturedSpectrumReduction`: the reduction of [Stacks, Tag 0BK1] to the
  punctured spectra of the local rings along the complement.

## Implementation notes

The identification of a prime of `A = R_𝔭` with the prime of `R` under it, and of `A_𝔮` with
`R_{𝔮 ∩ R}`, is Mathlib's
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`. It is stated for
`Localization M`, and `Localization.AtPrime 𝔭` is by definition `Localization 𝔭.primeCompl`, so
it applies on the nose.

The choice of the function `f` is the only place the integrality of the ambient scheme is used
twice: once to know that the ideal cutting out the complement of `V'` has a nonzero element, and
once to know that restricting a nonzero global function to the nonempty open `P` keeps it
nonzero (`AlgebraicGeometry.map_injective_of_isIntegral`).

## References

* [Stacks Project, Tag 0BK1](https://stacks.math.columbia.edu/tag/0BK1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.LocalCohomology

/-! ### Points of an affine open and primes of its ring of functions -/

/-- **A prime of `Γ(Z, V)` is recovered from the point of `V` it names.**
`AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf` is the other composite; this one holds
because `hV.fromSpec` is an open immersion and therefore injective on points. -/
theorem primeIdealOf_fromSpec {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V)
    (p : Spec Γ(Z, V)) (hp : hV.fromSpec p ∈ V) :
    hV.primeIdealOf ⟨hV.fromSpec p, hp⟩ = p :=
  hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨hV.fromSpec p, hp⟩)

/-! ### The empty open -/

/-- **The direct image of the structure sheaf of the empty open is coherent.** Its sections over
any open are a subsingleton, hence a finite module. -/
theorem isCoherent_pushforward_structureSheaf_bot (R : CommRingCat.{u}) [IsNoetherianRing R]
    {V : (Spec R).Opens} (hV : V = ⊥) :
    ((Scheme.Modules.pushforward V.ι).obj
      (SheafOfModules.unit.{u} V.toScheme.ringCatSheaf)).IsCoherent := by
  refine isCoherent_pushforward_structureSheaf_of_module_finite_sections R V ?_
  have hsub : Subsingleton Γ(Spec R, V) := by rw [hV]; infer_instance
  exact Module.Finite.of_surjective (Algebra.linearMap (ToType R) Γ(Spec R, V))
    fun _ => ⟨0, Subsingleton.elim _ _⟩

/-! ### A nested pair of opens, read two ways -/

/-- **For `V' ≤ P` the composite `(P.ι ⁻¹ᵁ V').ι ≫ P.ι` has image `V'`.** The inductive step of
[Stacks, Tag 0BK1] concludes about that composite, while the statement being proved is about
`V'.ι`; `isCoherent_pushforward_structureSheaf_of_opensRange_eq` bridges the two along this
equality. -/
theorem opensRange_preimage_ι_comp_ι {X : Scheme.{u}} {P V' : X.Opens} (hle : V' ≤ P) :
    ((P.ι ⁻¹ᵁ V').ι ≫ P.ι).opensRange = V' := by
  rw [Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr hle]

/-! ### The function the inductive step consumes -/

/-- **A nonzero function on `P` whose principal open lies inside `V'`.** Let `A` be a domain,
`V' ≤ P` opens of `Spec A` with `V'` nonempty. Then there is a nonzero `f ∈ Γ(P, ⊤)` with
`D(f) ≤ P.ι ⁻¹ᵁ V'`.

This is the choice of function in the induction of [Stacks, Tag 0BK1]: the complement of `V'` is
the zero locus of an ideal `I` (`exists_eq_zeroLocusCompl`), which is nonzero because `V'` is
nonempty, and any nonzero `a ∈ I` has `D(a) ≤ V'`. Restricting `a` to `P` keeps it nonzero
because `Spec A` is integral and `P` is nonempty. -/
theorem exists_section_basicOpen_le {A : Type u} [CommRing A] [IsDomain A]
    {P V' : (Spec (CommRingCat.of A)).Opens} (hle : V' ≤ P)
    (hne : Nonempty V'.toScheme) :
    ∃ f : Γ(P.toScheme, ⊤), f ≠ 0 ∧ P.toScheme.basicOpen f ≤ P.ι ⁻¹ᵁ V' := by
  obtain ⟨I, hI⟩ := exists_eq_zeroLocusCompl (CommRingCat.of A) V'
  obtain ⟨x₀⟩ := hne
  obtain ⟨x, hx⟩ : ∃ x : Spec (CommRingCat.of A), x ∈ V' := ⟨x₀.1, x₀.2⟩
  -- `I` has a nonzero element, because `V'` is nonempty.
  obtain ⟨a, haI, ha0⟩ : ∃ a ∈ I, a ≠ (0 : ToType (CommRingCat.of A)) := by
    by_contra hcon
    push Not at hcon
    rw [hI] at hx
    exact hx fun b hb => by
      rw [hcon b hb]
      exact SetLike.mem_coe.mpr x.asIdeal.zero_mem
  -- the corresponding global function on `Spec A`, and its restriction to `P`
  set a₀ : Γ(Spec (CommRingCat.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv a with ha₀
  have ha₀0 : a₀ ≠ 0 := fun h =>
    ha0 ((ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1 (h.trans (map_zero _).symm))
  have hbas : (Spec (CommRingCat.of A)).basicOpen a₀ ≤ V' := by
    rw [hI, ha₀, basicOpen_eq_of_affine]
    exact fun q hq hsub => hq (hsub haI)
  have hPne : Nonempty P.toScheme := ⟨⟨x, hle hx⟩⟩
  set r : Γ(Spec (CommRingCat.of A), P) :=
    (Spec (CommRingCat.of A)).presheaf.map (homOfLE (le_top : P ≤ ⊤)).op a₀ with hr
  have hr0 : r ≠ 0 := fun h =>
    ha₀0 (map_injective_of_isIntegral (X := Spec (CommRingCat.of A))
      (homOfLE (le_top : P ≤ ⊤)) (h.trans (map_zero _).symm))
  refine ⟨P.topIso.inv r, fun h =>
    hr0 ((ConcreteCategory.bijective_of_isIso P.topIso.inv).1 (h.trans (map_zero _).symm)), ?_⟩
  have hle' : P.ι ''ᵁ P.toScheme.basicOpen (P.topIso.inv r) ≤ V' := by
    rw [Scheme.Opens.ι_image_basicOpen_topIso_inv (X := Spec (CommRingCat.of A)) (U := P) r, hr,
      Scheme.basicOpen_res]
    exact le_trans inf_le_right hbas
  calc P.toScheme.basicOpen (P.topIso.inv r)
      = P.ι ⁻¹ᵁ (P.ι ''ᵁ P.toScheme.basicOpen (P.topIso.inv r)) :=
        (Scheme.Hom.preimage_image_eq P.ι _).symm
    _ ≤ P.ι ⁻¹ᵁ V' := fun y hy => hle' hy

/-! ### The coherence hypothesis at a prime of a localization -/

/-- **The coherence hypothesis of `Stacks.LocalCohomology.puncturedSpectrumReduction` at a prime
of a localization.** Let `R` be a ring, `𝔭` a prime of `R`, and `𝔮` a prime of
`A = Localization.AtPrime 𝔭`. If the punctured spectrum of `Localization.AtPrime (𝔮 ∩ R)` has
coherent direct image, then so does the punctured spectrum of `Localization.AtPrime 𝔮`.

The two rings are isomorphic by
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, and
`isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_ringEquiv` transports coherence. This
is how the induction reads its hypothesis at the points of the punctured spectrum of a stalk:
those are primes of the stalk, while the hypothesis is available at primes of the affine chart. -/
theorem isCoherent_pushforward_structureSheaf_puncturedSpectrum_comap {R : Type u} [CommRing R]
    [IsNoetherianRing R] (p : Ideal R) [p.IsPrime]
    (q : Ideal (Localization.AtPrime p)) [q.IsPrime]
    (h : ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum
        (Localization.AtPrime (q.comap (algebraMap R (Localization.AtPrime p))))).ι).obj
      (SheafOfModules.unit.{u} (Stacks.Divisors.puncturedSpectrum
        (Localization.AtPrime
          (q.comap (algebraMap R (Localization.AtPrime p))))).toScheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward
        (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime q)).ι).obj
      (SheafOfModules.unit.{u} (Stacks.Divisors.puncturedSpectrum
        (Localization.AtPrime q)).toScheme.ringCatSheaf)).IsCoherent :=
  have : IsNoetherianRing
      (Localization.AtPrime (q.comap (algebraMap R (Localization.AtPrime p)))) :=
    IsLocalization.isNoetherianRing
      (q.comap (algebraMap R (Localization.AtPrime p))).primeCompl _ inferInstance
  isCoherent_pushforward_structureSheaf_puncturedSpectrum_of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      p.primeCompl q).toRingEquiv h

/-! ### The arithmetic of the measure -/

/-- In `WithBot ℕ∞`, an element strictly below `d` is at most `m` whenever `d ≤ m + 1`. The
measure of the induction of [Stacks, Tag 0BK1] lives in `WithBot ℕ∞`, and this is the step from
"the dimension drops" to "the inductive hypothesis at `d - 1` applies". It is stated with `m` a
variable rather than as `x ≤ ((d - 1 : ℕ) : WithBot ℕ∞)` because `norm_cast` cannot push a cast
through a truncated subtraction. -/
theorem le_of_lt_natCast_of_le_succ {x : WithBot ℕ∞} {d m : ℕ} (hm : d ≤ m + 1)
    (h : x < (d : WithBot ℕ∞)) : x ≤ (m : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact absurd h (by simp)
    | coe k =>
      have hk : k < d := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.mp (lt_of_lt_of_le hk hm)

/-! ### The hypothesis of the reduction, abbreviated -/

/-- The coherence hypothesis of `Stacks.LocalCohomology.puncturedSpectrumReduction` at a local
ring: the direct image of the structure sheaf of the punctured spectrum of `A` is coherent. -/
@[ega "IV 5.11.5" "special case"]
abbrev PuncturedSpectrumCoherent (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ((Scheme.Modules.pushforward (Stacks.Divisors.puncturedSpectrum A).ι).obj
    (SheafOfModules.unit.{u}
      (Stacks.Divisors.puncturedSpectrum A).toScheme.ringCatSheaf)).IsCoherent

/-! ### The opening reduction, and the hypothesis read at a prime of an affine chart -/

/-- **The opening reduction of [Stacks, Tag 0BK1].** Coherence of `j'_*𝒪_W` follows from
coherence of the direct image of `𝒪` along the inclusion of the preimage of the image of `j'` in
`Spec Γ(Z, V)_𝔭`, as `V` runs over the affine opens of `Z` and `𝔭` over the primes of `Γ(Z, V)`.

This is the first two steps of the source's argument: coherence is local on the target, so it may
be checked on the affine charts (`isCoherent_pushforward_structureSheaf_of_forall_affineOpen`),
and over a Noetherian affine base finiteness of the sections may be checked after localizing at
every prime ([Stacks, Tag 0AW9],
`isCoherent_pushforward_structureSheaf_of_forall_localization`). An empty chart is disposed of
first: its ring of functions is the zero ring, over which every module is finite.

Both the step of the induction and the removal of its dimension hypothesis begin here. -/
theorem isCoherent_pushforward_structureSheaf_of_forall_affineOpen_prime {W Z : Scheme.{u}}
    (j' : W ⟶ Z) [IsOpenImmersion j'] [IsLocallyNoetherian Z]
    (hstep : ∀ (V : Z.Opens) (hV : IsAffineOpen V), Nonempty V →
      ∀ p : PrimeSpectrum (ToType Γ(Z, V)),
      ((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom
            (algebraMap (ToType Γ(Z, V)) (Localization.AtPrime p.asIdeal))) ⁻¹ᵁ
          (hV.fromSpec ⁻¹ᵁ j'.opensRange)).ι).obj
        (SheafOfModules.unit.{u} (Spec.map (CommRingCat.ofHom
            (algebraMap (ToType Γ(Z, V)) (Localization.AtPrime p.asIdeal))) ⁻¹ᵁ
          (hV.fromSpec ⁻¹ᵁ j'.opensRange)).toScheme.ringCatSheaf)).IsCoherent) :
    ((Scheme.Modules.pushforward j').obj (SheafOfModules.unit.{u} W.ringCatSheaf)).IsCoherent := by
  refine isCoherent_pushforward_structureSheaf_of_forall_affineOpen j' fun Vp => ?_
  obtain ⟨V, hV⟩ := Vp
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  by_cases hVbot : V = ⊥
  · have : Subsingleton (ToType Γ(Z, V)) := by rw [hVbot]; infer_instance
    have := Module.subsingleton (ToType Γ(Z, V))
      Γ(Spec Γ(Z, V), hV.fromSpec ⁻¹ᵁ j'.opensRange)
    exact Module.Finite.of_surjective
      (Algebra.linearMap (ToType Γ(Z, V)) Γ(Spec Γ(Z, V), hV.fromSpec ⁻¹ᵁ j'.opensRange))
      fun _ => ⟨0, Subsingleton.elim _ _⟩
  have hVne : Nonempty V := by
    rw [← TopologicalSpace.Opens.coe_eq_empty] at hVbot
    exact Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr hVbot)
  exact module_finite_sections_of_isCoherent Γ(Z, V) _
    (isCoherent_pushforward_structureSheaf_of_forall_localization Γ(Z, V) _
      (hstep V hV hVne))

/-- **Every prime of an affine chart names a point of that chart.** -/
theorem fromSpec_mem {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V)
    (q : PrimeSpectrum (ToType Γ(Z, V))) : hV.fromSpec q ∈ V :=
  le_of_eq hV.opensRange_fromSpec ⟨q, rfl⟩

/-- **The coherence hypothesis of `Stacks.LocalCohomology.puncturedSpectrumReduction`, read at a
prime of an affine chart.** A prime `𝔮` of `Γ(Z, V)` outside `hV.fromSpec ⁻¹ᵁ j'.opensRange`
names a point of `Z` outside the image of `j'`, so the hypothesis applies at that point; and the
local ring there is `Γ(Z, V)_𝔮`, by
`isCoherent_pushforward_structureSheaf_puncturedSpectrum_localization` together with
`primeIdealOf_fromSpec`. -/
theorem isCoherent_puncturedSpectrum_localization_of_notMem {W Z : Scheme.{u}} (j' : W ⟶ Z)
    [IsOpenImmersion j'] [IsLocallyNoetherian Z] {V : Z.Opens} (hV : IsAffineOpen V)
    (hcoh : ∀ z : Z, z ∉ Set.range j'.base → PuncturedSpectrumCoherent.{u} (Z.presheaf.stalk z))
    (q : PrimeSpectrum (ToType Γ(Z, V))) (hq : q ∉ hV.fromSpec ⁻¹ᵁ j'.opensRange) :
    PuncturedSpectrumCoherent.{u} (Localization.AtPrime q.asIdeal) := by
  have h := isCoherent_pushforward_structureSheaf_puncturedSpectrum_localization hV
    (hV.fromSpec q) (fromSpec_mem hV q) (hcoh _ fun hc => hq hc)
  rwa [primeIdealOf_fromSpec hV q (fromSpec_mem hV q)] at h

/-- **The local ring of `Z` at the point named by a prime of an affine chart is the localization
there**, as far as the Krull dimension is concerned. -/
theorem ringKrullDim_localization_eq_stalk {Z : Scheme.{u}} [IsLocallyNoetherian Z] {V : Z.Opens}
    (hV : IsAffineOpen V) (q : PrimeSpectrum (ToType Γ(Z, V))) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Z.presheaf.stalk (hV.fromSpec q)) := by
  let : Algebra (ToType Γ(Z, V)) (ToType (Z.presheaf.stalk (hV.fromSpec q))) :=
    Z.presheaf.algebra_section_stalk (U := V) ⟨hV.fromSpec q, fromSpec_mem hV q⟩
  have hloc : IsLocalization.AtPrime (ToType (Z.presheaf.stalk (hV.fromSpec q))) q.asIdeal := by
    have h := hV.isLocalization_stalk (⟨hV.fromSpec q, fromSpec_mem hV q⟩ : V)
    rwa [primeIdealOf_fromSpec hV q (fromSpec_mem hV q)] at h
  exact ringKrullDim_eq_of_ringEquiv (IsLocalization.algEquiv q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal)
    (ToType (Z.presheaf.stalk (hV.fromSpec q)))).toRingEquiv

/-! ### The induction -/

/-- The statement of `Stacks.LocalCohomology.puncturedSpectrumReduction` with the dimension of
the local rings along the complement bounded by `d`. This is the statement the Noetherian
induction of [Stacks, Tag 0BK1] runs on. -/
def ReductionBoundedBy (d : ℕ) : Prop :=
  ∀ (W Z : Scheme.{u}) (j' : W ⟶ Z) [IsOpenImmersion j'] [IsIntegral Z]
    [IsLocallyNoetherian Z] [Nonempty W],
    (∀ z : Z, z ∉ Set.range j'.base → PuncturedSpectrumCoherent.{u} (Z.presheaf.stalk z)) →
    (∀ z : Z, z ∉ Set.range j'.base →
      ringKrullDim (Z.presheaf.stalk z) ≤ (d : WithBot ℕ∞)) →
    ((Scheme.Modules.pushforward j').obj (SheafOfModules.unit.{u} W.ringCatSheaf)).IsCoherent

/-- **The affine-local case of [Stacks, Tag 0BK1], granted the statement below `d`.** Let `A` be
a Noetherian local domain of dimension at most `d` and `V'` an open of `Spec A`. If the punctured
spectrum of `A_𝔮` has coherent direct image for every prime `𝔮` outside `V'`, and the punctured
spectrum of `A` itself does when `V'` misses the closed point, then `V'_*𝒪` is coherent.

This is steps three to five of the source's argument. `eq_top_of_closedPoint_mem` disposes of the
case in which `V'` still contains the closed point, and `isCoherent_pushforward_structureSheaf_bot`
of the case in which `V'` is empty. Otherwise `V'` sits inside the punctured spectrum `P` of `A`,
whose local rings have strictly smaller dimension
(`ringKrullDim_stalk_puncturedSpectrum_lt`), so the statement at `d - 1` applied to `P` makes
`(P.ι ⁻¹ᵁ V')_*𝒪` coherent on `P`; `exists_section_basicOpen_le` supplies the function `f` that
`isCoherent_pushforward_structureSheaf_of_basicOpen_le` consumes, and
`isCoherent_pushforward_structureSheaf_of_opensRange_eq` reads its conclusion, which is about
`(P.ι ⁻¹ᵁ V').ι ≫ P.ι`, as a statement about `V'.ι`. -/
theorem isCoherent_pushforward_structureSheaf_localRing (d : ℕ)
    (ih : ∀ m : ℕ, m < d → ReductionBoundedBy.{u} m) (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]
    (V' : (Spec (CommRingCat.of A)).Opens)
    (hAd : (IsLocalRing.closedPoint A : Spec (CommRingCat.of A)) ∉ V' →
      ringKrullDim A ≤ (d : WithBot ℕ∞))
    (hPcoh : (IsLocalRing.closedPoint A : Spec (CommRingCat.of A)) ∉ V' →
      PuncturedSpectrumCoherent.{u} A)
    (hcohA : ∀ q : PrimeSpectrum A, q ∉ V' →
      PuncturedSpectrumCoherent.{u} (Localization.AtPrime q.asIdeal)) :
    ((Scheme.Modules.pushforward V'.ι).obj
      (SheafOfModules.unit.{u} V'.toScheme.ringCatSheaf)).IsCoherent := by
  have : IsNoetherianRing (CommRingCat.of A) := ‹IsNoetherianRing A›
  by_cases hWbot : V' = ⊥
  · exact isCoherent_pushforward_structureSheaf_bot _ hWbot
  by_cases hcp : (IsLocalRing.closedPoint A : Spec (CommRingCat.of A)) ∈
      (V' : Set (Spec (CommRingCat.of A)))
  · rw [eq_top_of_closedPoint_mem V' hcp]
    exact isCoherent_pushforward_structureSheaf_top _
  -- the main case
  have hAd' : ringKrullDim A ≤ (d : WithBot ℕ∞) := hAd hcp
  have hWle : V' ≤ Stacks.Divisors.puncturedSpectrum A := by
    intro y hy hcontra
    exact hcp (Set.mem_singleton_iff.mp hcontra ▸ hy)
  have hWnes : (V' : Set (Spec (CommRingCat.of A))).Nonempty := by
    by_contra hc
    exact hWbot ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot V').mp hc)
  obtain ⟨y₀, hy₀⟩ := hWnes
  have hWne : Nonempty V'.toScheme := ⟨⟨y₀, hy₀⟩⟩
  have hPne : Nonempty (Stacks.Divisors.puncturedSpectrum A).toScheme := ⟨⟨y₀, hWle hy₀⟩⟩
  have : Nonempty ((Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V').toScheme :=
    ⟨⟨⟨y₀, hWle hy₀⟩, hy₀⟩⟩
  have : IsIntegral (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    isIntegral_puncturedSpectrum A
  have : AlgebraicGeometry.IsNoetherian (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    isNoetherian_puncturedSpectrum A
  have hdrop : ∀ y : (Stacks.Divisors.puncturedSpectrum A).toScheme,
      ringKrullDim ((Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf.stalk y) <
        ringKrullDim A := fun y =>
    ringKrullDim_stalk_puncturedSpectrum_lt y.1 (Set.mem_compl_singleton_iff.mp y.2)
  have hd1 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · obtain ⟨y₁⟩ := hPne
      subst hd
      exact absurd (lt_of_lt_of_le (lt_of_le_of_lt ringKrullDim_nonneg_of_nontrivial
        (hdrop y₁)) (by simpa using hAd')) (lt_irrefl _)
    · exact hd
  have hout : ∀ y : (Stacks.Divisors.puncturedSpectrum A).toScheme,
      y ∉ Set.range ((Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V').ι.base →
      (y.1 : PrimeSpectrum A) ∉ V' := fun y hy hc => hy ⟨⟨y, hc⟩, rfl⟩
  have hGcoh := ih (d - 1) (by omega)
    ((Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V').toScheme
    (Stacks.Divisors.puncturedSpectrum A).toScheme
    ((Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V').ι
    (fun y hy => isCoherent_pushforward_structureSheaf_puncturedSpectrum_stalk y.1
      (Set.mem_compl_singleton_iff.mp y.2) (hcohA y.1 (hout y hy)))
    (fun y _ => le_of_lt_natCast_of_le_succ (by omega) (lt_of_lt_of_le (hdrop y) hAd'))
  obtain ⟨f, hf0, hf⟩ := exists_section_basicOpen_le (A := A) hWle hWne
  exact isCoherent_pushforward_structureSheaf_of_opensRange_eq _ V'.ι
    (by rw [opensRange_preimage_ι_comp_ι hWle, Scheme.Opens.opensRange_ι])
    (isCoherent_pushforward_structureSheaf_of_basicOpen_le
      ((Stacks.Divisors.puncturedSpectrum A).ι ⁻¹ᵁ V').ι
      (Stacks.Divisors.puncturedSpectrum A).ι hGcoh (hPcoh hcp) f hf0
      (by rw [Scheme.Opens.opensRange_ι]; exact hf))

/-- **The step of the Noetherian induction of [Stacks, Tag 0BK1].** -/
theorem reductionBoundedBy_of_forall_lt (d : ℕ)
    (ih : ∀ m : ℕ, m < d → ReductionBoundedBy.{u} m) : ReductionBoundedBy.{u} d := by
  intro W Z j' _ _ _ _ hcoh hdim
  refine isCoherent_pushforward_structureSheaf_of_forall_affineOpen_prime j'
    fun V hV hVne p => ?_
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsDomain Γ(Z, V) := IsIntegral.component_integral V
  have : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  have : IsDomain (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl_le_nonZeroDivisors
  have hclp : Spec.map (CommRingCat.ofHom
      (algebraMap (ToType Γ(Z, V)) (Localization.AtPrime p.asIdeal)))
      (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  have hpV' : ∀ _ : (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) :
      Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))) ∉
      Spec.map (CommRingCat.ofHom (algebraMap (ToType Γ(Z, V))
        (Localization.AtPrime p.asIdeal))) ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ j'.opensRange),
      p ∉ hV.fromSpec ⁻¹ᵁ j'.opensRange := fun hcp hc => hcp (by
    show Spec.map (CommRingCat.ofHom (algebraMap (ToType Γ(Z, V))
      (Localization.AtPrime p.asIdeal))) (IsLocalRing.closedPoint
        (Localization.AtPrime p.asIdeal)) ∈ hV.fromSpec ⁻¹ᵁ j'.opensRange
    rw [hclp]
    exact hc)
  refine isCoherent_pushforward_structureSheaf_localRing d ih
    (Localization.AtPrime p.asIdeal) _ (fun hcp => ?_) (fun hcp => ?_) ?_
  · rw [ringKrullDim_localization_eq_stalk hV p]
    exact hdim _ fun hc => hpV' hcp hc
  · exact isCoherent_puncturedSpectrum_localization_of_notMem j' hV hcoh p (hpV' hcp)
  · intro q hq
    exact isCoherent_pushforward_structureSheaf_puncturedSpectrum_comap p.asIdeal q.asIdeal
      (isCoherent_puncturedSpectrum_localization_of_notMem j' hV hcoh
        (PrimeSpectrum.comap (algebraMap (ToType Γ(Z, V)) (Localization.AtPrime p.asIdeal)) q) hq)

/-- **The recursion of [Stacks, Tag 0BK1].** -/
theorem reductionBoundedBy (d : ℕ) : ReductionBoundedBy.{u} d :=
  Nat.strongRecOn d fun n ih => reductionBoundedBy_of_forall_lt n ih

/-- **The reduction of [Stacks, Tag 0BK1] to the punctured spectra of its local rings.** Let
`j' : W ⟶ Z` be an open immersion of a nonempty scheme into an integral locally Noetherian scheme.
If the direct image of the structure sheaf of the punctured spectrum of `𝒪_{Z,z}` is coherent for
every point `z` outside the image of `j'`, then `j'_*𝒪_W` is coherent.

This is the first five steps of the argument of [Stacks, Tag 0BK1]: coherence is checked on the
affine charts and at their primes, and the bound on the Krull dimension of the local ring there
feeds the induction `reductionBoundedBy`. -/
@[ega "I 1.5.2" "special case"]
theorem puncturedSpectrumReduction {W Z : Scheme.{u}} (j' : W ⟶ Z) [IsOpenImmersion j']
    [IsIntegral Z] [IsLocallyNoetherian Z] [Nonempty W]
    (hcoh : ∀ z : Z, z ∉ Set.range j'.base → PuncturedSpectrumCoherent.{u} (Z.presheaf.stalk z)) :
    ((Scheme.Modules.pushforward j').obj (SheafOfModules.unit.{u} W.ringCatSheaf)).IsCoherent := by
  refine isCoherent_pushforward_structureSheaf_of_forall_affineOpen_prime j'
    fun V hV hVne p => ?_
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsDomain Γ(Z, V) := IsIntegral.component_integral V
  have : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  have : IsDomain (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl_le_nonZeroDivisors
  have hclp : Spec.map (CommRingCat.ofHom
      (algebraMap (ToType Γ(Z, V)) (Localization.AtPrime p.asIdeal)))
      (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal)) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  obtain ⟨n, hn⟩ : ∃ n : ℕ,
      ringKrullDim (Localization.AtPrime p.asIdeal) ≤ (n : WithBot ℕ∞) := by
    refine ⟨(IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)).height.toNat, ?_⟩
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      (R := Localization.AtPrime p.asIdeal)]
    exact_mod_cast le_of_eq (ENat.natCast_toNat_eq_self.mpr
      (Ideal.height_ne_top_of_isPrime
        (I := IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)))).symm
  have hpV' : ∀ _ : (IsLocalRing.closedPoint (Localization.AtPrime p.asIdeal) :
      Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))) ∉
      Spec.map (CommRingCat.ofHom (algebraMap (ToType Γ(Z, V))
        (Localization.AtPrime p.asIdeal))) ⁻¹ᵁ (hV.fromSpec ⁻¹ᵁ j'.opensRange),
      p ∉ hV.fromSpec ⁻¹ᵁ j'.opensRange := fun hcp hc => hcp (by
    show Spec.map (CommRingCat.ofHom (algebraMap (ToType Γ(Z, V))
      (Localization.AtPrime p.asIdeal))) (IsLocalRing.closedPoint
        (Localization.AtPrime p.asIdeal)) ∈ hV.fromSpec ⁻¹ᵁ j'.opensRange
    rw [hclp]
    exact hc)
  refine isCoherent_pushforward_structureSheaf_localRing n
    (fun m _ => reductionBoundedBy m) (Localization.AtPrime p.asIdeal) _ (fun _ => hn)
    (fun hcp => ?_) ?_
  · exact isCoherent_puncturedSpectrum_localization_of_notMem j' hV hcoh p (hpV' hcp)
  · intro q hq
    exact isCoherent_pushforward_structureSheaf_puncturedSpectrum_comap p.asIdeal q.asIdeal
      (isCoherent_puncturedSpectrum_localization_of_notMem j' hV hcoh
        (PrimeSpectrum.comap (algebraMap (ToType Γ(Z, V)) (Localization.AtPrime p.asIdeal)) q) hq)

end Stacks.LocalCohomology

end
