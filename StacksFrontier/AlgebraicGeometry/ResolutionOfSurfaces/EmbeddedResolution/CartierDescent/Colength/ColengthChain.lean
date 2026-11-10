module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Colength.LocalizedColength
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierDescent.Colength.Realization

/-!
# The colength drop on the two charts

This file assembles the chart-level form of the colength drop of [Stacks, Tag 0AGT]. In the
two-chart situation of the sibling file `CartierDescent.Colength.Realization` — a ring `R` inside
a field `K`, elements `x y : R` and `t s : K` with `t * s = 1` and `x t = y`, the charts
`B = Algebra.adjoin R {t}` and `C = Algebra.adjoin R {s}`, an ideal `L` of `R` of finite colength
and residual ideals `Rx`, `Ry` with `(ξ ^ d)·Rx = L·B` and `(η ^ d)·Ry = L·C` — the sum of the
local colengths of `Rx` over *all* primes above it, plus the sum of the local colengths of `Ry`
over any family of primes above it at which `s` is not invertible, is strictly smaller than the
colength of `L`.

The three inputs are: the realisation theorem of the sibling file, which makes the product of the
two families of local residues a quotient of the ideal `W` of elements divisible by `x ^ d` on
the first chart and by `y ^ d` on the second; the properness of `W`, which holds because `x` is
not invertible on the first chart and `d` is positive; and the strict length drop
`Stacks.ResolutionOfSurfaces.CartierDescent.length_submodule_quotient_lt` for a proper ideal
containing `L`.

## Main results

* `Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_localization_quotient_lt`: the colength
  drop on the two charts.
* `Stacks.ResolutionOfSurfaces.CartierDescent.length_quotient_add_sum_length_localization_lt`: the
  same drop with every length taken over `R`, the family of all primes above `Rx` reassembled
  into the single quotient `B ⧸ Rx`.

## Implementation notes

The map out of `W` is the honest division by `x ^ d`: since `K` is a field and `x ≠ 0`, the
formula `a ↦ (x ^ d)⁻¹ a` is `R`-linear on `K`, and membership in `W` says exactly that it lands
in the chart. No choice and no cancellation lemma is needed to define it, and the realisation
theorem's conclusion is stated in the matching form `a = x ^ d β`, so that the value of the map
at the realising element is the realising cofactor on the nose.

The length bookkeeping is isolated in a lemma stated for *abstract* chart rings. That is forced
rather than stylistic: the two products of localizations are `Pi` types, so a `LinearMap.pi` into
one of them demands a family of `Module` instances indexed by the finite set, and synthesising
that family over a subalgebra of a field exhausts the instance budget. With the chart rings
behind variables the same search is immediate, and the abstract lemma's own statement mentions
only `Localization.AtPrime … ⧸ Ideal.map …`, whose instances are cheap at the chart.

Both conclusions are drawn from one inequality, `length_prod_lt_of_surjective`: the product of the
two families of local residues is shorter than `R ⧸ L` over `R`. Summing it with each local length
taken over its own local ring loses the degrees of the residue field extensions, which is harmless
for the consumers of the stalk colengths but not for a length over the base; that is why the
version over `R` is recorded as well, and it is the one that bounds the global sections of the
residual quotient.

The two sums are compared with the lengths of the two products by
`Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_localizedModule_le_of_surjective` applied
to the *identity* of the product, which is the cheapest way to get that comparison; the two
products are then joined by `Module.length_prod`. The conversion between the two models of a
local colength is
`Stacks.ResolutionOfSurfaces.CartierDescent.length_localizedModule_quotient_eq_length_map`,
applied only at the end, so that everything before it runs in the `LocalizedModule` model that
the Chinese remainder step produces.

Finiteness of the colength of `L` enters as `[IsArtinian R (R ⧸ L)]` rather than as
`[IsArtinianRing (R ⧸ L)]`: Mathlib's `Submodule.length_lt` is what is used, and that is the
hypothesis it wants.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
-/

@[expose] public noncomputable section

universe u

namespace Stacks.ResolutionOfSurfaces.CartierDescent

section Abstract

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- **A module surjected onto by a proper ideal on which `L` acts as zero is shorter than
`R ⧸ L`.** If `L ≤ W` are ideals of `R`, `W` is proper, `R ⧸ L` has finite length and the
`R`-module `P` is a quotient of `W` killed by `L`, then `P` is shorter than `R ⧸ L`.

The map factors through the image of `W` in `R ⧸ L`, which is a proper submodule by
`Stacks.ResolutionOfSurfaces.CartierDescent.map_mkQ_ne_top`. -/
private theorem length_lt_of_surjective_of_le {L W : Ideal R} (hLW : L ≤ W) (hW : W ≠ ⊤)
    [IsArtinian R (R ⧸ L)] {P : Type u} [AddCommGroup P] [Module R P] (f : ↥W →ₗ[R] P)
    (hf : Function.Surjective f) (hfL : ∀ a : ↥W, (a : R) ∈ L → f a = 0) :
    Module.length R P < Module.length R (R ⧸ L) := by
  set q : ↥W →ₗ[R] ↥(Submodule.map (Submodule.mkQ (L : Submodule R R)) (W : Submodule R R)) :=
    { toFun := fun a => ⟨Submodule.mkQ (L : Submodule R R) (a : R),
        Submodule.mem_map_of_mem a.2⟩
      map_add' := fun a b => Subtype.ext (map_add (Submodule.mkQ (L : Submodule R R)) _ _)
      map_smul' := fun c a =>
        Subtype.ext (map_smul (Submodule.mkQ (L : Submodule R R)) c (a : R)) }
  have hqs : Function.Surjective q := by
    rintro ⟨_, w, hw, rfl⟩
    exact ⟨⟨w, hw⟩, rfl⟩
  have hker : LinearMap.ker q ≤ LinearMap.ker f := by
    intro a ha
    refine LinearMap.mem_ker.2 (hfL a ?_)
    have h0 : Submodule.mkQ (L : Submodule R R) (a : R) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.1 ha)
    exact (Submodule.Quotient.mk_eq_zero _).1 h0
  have hlift : Function.Surjective (Submodule.liftQ (LinearMap.ker q) f hker) := by
    intro p
    obtain ⟨a, ha⟩ := hf p
    refine ⟨Submodule.mkQ (LinearMap.ker q) a, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
    exact ha
  refine lt_of_le_of_lt ((Module.length_le_of_surjective _ hlift).trans_eq ?_)
    (Submodule.length_lt (map_mkQ_ne_top hLW hW))
  exact (LinearMap.quotKerEquivOfSurjective q hqs).length_eq

variable {Bt Ct : Type u} [CommRing Bt] [CommRing Ct] [Algebra R Bt] [Algebra R Ct]

/-- **The length bookkeeping of the colength drop, over abstract chart rings.** Let `L ≤ W` be
ideals of `R` with `W` proper and `R ⧸ L` of finite length, let `Rx`, `Ry` be ideals of two
`R`-algebras `Bt`, `Ct`, and let `δB`, `δC` be `R`-linear maps from `W` to `Bt` and `Ct` which
carry `L` into `Rx` and into `Ry` and which, read modulo those ideals and localized along finite
families `Sx`, `Sy'` of primes, are jointly surjective. Then the product of the two families of
localizations is, over `R`, strictly shorter than `R ⧸ L`.

The chart rings are kept behind variables so that the families of `Module` instances on the two
products of localizations are synthesised here rather than at a subalgebra of a field, where the
search is too expensive. -/
private theorem length_prod_lt_of_surjective {L W : Ideal R} (hLW : L ≤ W) (hW : W ≠ ⊤)
    [IsArtinian R (R ⧸ L)] (Rx : Ideal Bt) (Ry : Ideal Ct)
    (Sx : Finset (PrimeSpectrum Bt)) (Sy' : Finset (PrimeSpectrum Ct))
    (δB : ↥W →ₗ[R] Bt) (δC : ↥W →ₗ[R] Ct)
    (hsurj : ∀ (ζ : ∀ w : Sx, LocalizedModule
          (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx))
        (ζ' : ∀ v : Sy', LocalizedModule
          (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry)), ∃ a : ↥W,
        (∀ w : Sx, (LocalizedModule.mkLinearMap
            (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx))
              (Ideal.Quotient.mk Rx (δB a)) = ζ w) ∧
          ∀ v : Sy', (LocalizedModule.mkLinearMap
            (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry))
              (Ideal.Quotient.mk Ry (δC a)) = ζ' v)
    (hkerB : ∀ a : ↥W, (a : R) ∈ L → δB a ∈ Rx)
    (hkerC : ∀ a : ↥W, (a : R) ∈ L → δC a ∈ Ry) :
    Module.length R
        ((∀ w : Sx, LocalizedModule (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx)) ×
          (∀ v : Sy', LocalizedModule (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry))) <
      Module.length R (R ⧸ L) := by
  set gB : Bt →ₗ[R] (∀ w : Sx, LocalizedModule
      (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx)) :=
    LinearMap.restrictScalars R (LinearMap.pi fun w : Sx =>
      (LocalizedModule.mkLinearMap (w : PrimeSpectrum Bt).asIdeal.primeCompl
        (Bt ⧸ Rx)).comp (Submodule.mkQ (Rx : Submodule Bt Bt)))
  set gC : Ct →ₗ[R] (∀ v : Sy', LocalizedModule
      (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry)) :=
    LinearMap.restrictScalars R (LinearMap.pi fun v : Sy' =>
      (LocalizedModule.mkLinearMap (v : PrimeSpectrum Ct).asIdeal.primeCompl
        (Ct ⧸ Ry)).comp (Submodule.mkQ (Ry : Submodule Ct Ct)))
  set f := (gB.comp δB).prod (gC.comp δC)
  have hfs : Function.Surjective f := by
    rintro ⟨ζ, ζ'⟩
    obtain ⟨a, h1, h2⟩ := hsurj ζ ζ'
    exact ⟨a, Prod.ext (funext h1) (funext h2)⟩
  have hfL : ∀ a : ↥W, (a : R) ∈ L → f a = 0 := by
    intro a haL
    refine Prod.ext (funext fun w => ?_) (funext fun v => ?_)
    · change (LocalizedModule.mkLinearMap (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx))
        (Submodule.mkQ (Rx : Submodule Bt Bt) (δB a)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (hkerB a haL), map_zero]
    · change (LocalizedModule.mkLinearMap (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry))
        (Submodule.mkQ (Ry : Submodule Ct Ct) (δC a)) = 0
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (hkerC a haL), map_zero]
  exact length_lt_of_surjective_of_le hLW hW f hfs hfL

omit [IsNoetherianRing R] in
/-- **The two sums of local colengths are at most the `R`-length of the product of the two
families of localizations.** Each local colength, taken over its own local ring, is at most the
`R`-length of the same module, and the two products are joined by `Module.length_prod`. -/
private theorem sum_length_le_length_prod (Rx : Ideal Bt) (Ry : Ideal Ct)
    (Sx : Finset (PrimeSpectrum Bt)) (Sy' : Finset (PrimeSpectrum Ct)) :
    ∑ w ∈ Sx, Module.length (Localization.AtPrime w.asIdeal)
        (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap Bt (Localization.AtPrime w.asIdeal)) Rx) +
      ∑ v ∈ Sy', Module.length (Localization.AtPrime v.asIdeal)
        (Localization.AtPrime v.asIdeal ⧸
          Ideal.map (algebraMap Ct (Localization.AtPrime v.asIdeal)) Ry) ≤
      Module.length R
        ((∀ w : Sx, LocalizedModule (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx)) ×
          (∀ v : Sy', LocalizedModule (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry))) := by
  calc _ = ∑ w ∈ Sx, Module.length (Localization.AtPrime w.asIdeal)
            (LocalizedModule w.asIdeal.primeCompl (Bt ⧸ Rx)) +
          ∑ v ∈ Sy', Module.length (Localization.AtPrime v.asIdeal)
            (LocalizedModule v.asIdeal.primeCompl (Ct ⧸ Ry)) :=
        congrArg₂ (· + ·)
          (Finset.sum_congr rfl fun w _ =>
            (length_localizedModule_quotient_eq_length_map Rx w.asIdeal).symm)
          (Finset.sum_congr rfl fun v _ =>
            (length_localizedModule_quotient_eq_length_map Ry v.asIdeal).symm)
    _ ≤ Module.length R (∀ w : Sx, LocalizedModule
            (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx)) +
          Module.length R (∀ v : Sy', LocalizedModule
            (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry)) :=
        add_le_add
          (sum_length_localizedModule_le_of_surjective (A := R) Sx (Bt ⧸ Rx)
            LinearMap.id Function.surjective_id)
          (sum_length_localizedModule_le_of_surjective (A := R) Sy' (Ct ⧸ Ry)
            LinearMap.id Function.surjective_id)
    _ = Module.length R _ := (Module.length_prod R _ _).symm

omit [IsNoetherianRing R] in
/-- **The `R`-length of the product of the two families of localizations, computed over `R`.** If
`Sx` consists of *all* the primes above `Rx` and the residual quotient on the first chart is
Artinian, the first family reassembles into that quotient, by the Chinese remainder theorem; the
second family contributes the sum of its local pieces. -/
private theorem length_quotient_add_sum_length_eq_length_prod (Rx : Ideal Bt) (Ry : Ideal Ct)
    [IsArtinianRing (Bt ⧸ Rx)] (Sx : Finset (PrimeSpectrum Bt))
    (hSx : ∀ w : PrimeSpectrum Bt, w ∈ Sx ↔ Rx ≤ w.asIdeal)
    (Sy' : Finset (PrimeSpectrum Ct)) :
    Module.length R (Bt ⧸ Rx) +
      ∑ v ∈ Sy', Module.length R (Localization.AtPrime v.asIdeal ⧸
        Ideal.map (algebraMap Ct (Localization.AtPrime v.asIdeal)) Ry) =
      Module.length R
        ((∀ w : Sx, LocalizedModule (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx)) ×
          (∀ v : Sy', LocalizedModule (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry))) := by
  rw [Module.length_prod]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [length_quotient_eq_sum_length_localizedModule (A := R) Rx Sx hSx,
      Module.length_pi_of_fintype]
    exact (Finset.sum_coe_sort Sx
      (fun w => Module.length R (LocalizedModule
        (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx)))).symm
  · rw [Module.length_pi_of_fintype, Finset.sum_coe_sort Sy'
      (fun v => Module.length R (LocalizedModule
        (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry)))]
    exact Finset.sum_congr rfl fun v _ =>
      (length_localizedModule_quotient_eq_length_map_base (R := R) Ry v.asIdeal).symm

section Data

/-- The joint surjectivity of the two division maps, read modulo the residual ideals and
localized along the two families of primes. This is what the realisation theorem delivers and
what the two length bookkeeping lemmas below consume. -/
private abbrev JointlySurjective {W : Ideal R} (Rx : Ideal Bt) (Ry : Ideal Ct)
    (Sx : Finset (PrimeSpectrum Bt)) (Sy' : Finset (PrimeSpectrum Ct))
    (δB : ↥W →ₗ[R] Bt) (δC : ↥W →ₗ[R] Ct) : Prop :=
  ∀ (ζ : ∀ w : Sx, LocalizedModule (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx))
      (ζ' : ∀ v : Sy', LocalizedModule (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry)),
    ∃ a : ↥W,
      (∀ w : Sx, (LocalizedModule.mkLinearMap
          (w : PrimeSpectrum Bt).asIdeal.primeCompl (Bt ⧸ Rx))
            (Ideal.Quotient.mk Rx (δB a)) = ζ w) ∧
        ∀ v : Sy', (LocalizedModule.mkLinearMap
          (v : PrimeSpectrum Ct).asIdeal.primeCompl (Ct ⧸ Ry))
            (Ideal.Quotient.mk Ry (δC a)) = ζ' v

/-- **The length bookkeeping of the colength drop, over abstract chart rings.** The two sums of
local colengths, each over its own local ring, are together strictly smaller than the colength of
`L`. -/
private theorem sum_length_lt_of_surjective {L W : Ideal R} (hLW : L ≤ W) (hW : W ≠ ⊤)
    [IsArtinian R (R ⧸ L)] (Rx : Ideal Bt) (Ry : Ideal Ct)
    (Sx : Finset (PrimeSpectrum Bt)) (Sy' : Finset (PrimeSpectrum Ct))
    (δB : ↥W →ₗ[R] Bt) (δC : ↥W →ₗ[R] Ct)
    (hsurj : JointlySurjective Rx Ry Sx Sy' δB δC)
    (hkerB : ∀ a : ↥W, (a : R) ∈ L → δB a ∈ Rx)
    (hkerC : ∀ a : ↥W, (a : R) ∈ L → δC a ∈ Ry) :
    ∑ w ∈ Sx, Module.length (Localization.AtPrime w.asIdeal)
        (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap Bt (Localization.AtPrime w.asIdeal)) Rx) +
      ∑ v ∈ Sy', Module.length (Localization.AtPrime v.asIdeal)
        (Localization.AtPrime v.asIdeal ⧸
          Ideal.map (algebraMap Ct (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) :=
  lt_of_le_of_lt (sum_length_le_length_prod Rx Ry Sx Sy')
    (length_prod_lt_of_surjective hLW hW Rx Ry Sx Sy' δB δC hsurj hkerB hkerC)

/-- **The length bookkeeping of the colength drop over the base ring, over abstract chart
rings.** When `Sx` is the family of *all* primes above `Rx`, the `R`-colength of the residual
quotient on the first chart plus the sum of the `R`-colengths on the second is strictly smaller
than the `R`-colength of `L`. -/
private theorem length_quotient_add_sum_length_lt_of_surjective {L W : Ideal R} (hLW : L ≤ W)
    (hW : W ≠ ⊤) [IsArtinian R (R ⧸ L)] (Rx : Ideal Bt) (Ry : Ideal Ct)
    [IsArtinianRing (Bt ⧸ Rx)]
    (Sx : Finset (PrimeSpectrum Bt)) (Sy' : Finset (PrimeSpectrum Ct))
    (δB : ↥W →ₗ[R] Bt) (δC : ↥W →ₗ[R] Ct)
    (hSx : ∀ w : PrimeSpectrum Bt, w ∈ Sx ↔ Rx ≤ w.asIdeal)
    (hsurj : JointlySurjective Rx Ry Sx Sy' δB δC)
    (hkerB : ∀ a : ↥W, (a : R) ∈ L → δB a ∈ Rx)
    (hkerC : ∀ a : ↥W, (a : R) ∈ L → δC a ∈ Ry) :
    Module.length R (Bt ⧸ Rx) +
      ∑ v ∈ Sy', Module.length R (Localization.AtPrime v.asIdeal ⧸
        Ideal.map (algebraMap Ct (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) :=
  (length_quotient_add_sum_length_eq_length_prod Rx Ry Sx hSx Sy').trans_lt
    (length_prod_lt_of_surjective hLW hW Rx Ry Sx Sy' δB δC hsurj hkerB hkerC)

end Data

end Abstract

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K]

/-- **Division by a nonzero element of `K`, as a map from an ideal to a chart.** If every element
of the ideal `W` of `R` becomes, after division by `w` in `K`, an element of the subalgebra `S`,
then that division is an `R`-linear map from `W` to `S`. -/
private def divPow (W : Ideal R) (S : Subalgebra R K) (w : K)
    (h : ∀ a ∈ W, w⁻¹ * algebraMap R K a ∈ S) : ↥W →ₗ[R] ↥S where
  toFun a := ⟨w⁻¹ * algebraMap R K (a : R), h (a : R) a.2⟩
  map_add' a b := Subtype.ext (by simp [mul_add])
  map_smul' c a := Subtype.ext (by simp [Algebra.smul_def, mul_left_comm])

/-- The value of `Stacks.ResolutionOfSurfaces.CartierDescent.divPow`, read inside `K`. -/
private theorem coe_divPow_apply (W : Ideal R) (S : Subalgebra R K) (w : K)
    (h : ∀ a ∈ W, w⁻¹ * algebraMap R K a ∈ S) (a : ↥W) :
    ((divPow W S w h a : ↥S) : K) = w⁻¹ * algebraMap R K (a : R) := rfl

/-- The division map sends `a` to `β` as soon as `a = w * β` in `K`. -/
private theorem divPow_eq_of_eq_mul (W : Ideal R) (S : Subalgebra R K) {w : K} (hw : w ≠ 0)
    (h : ∀ a ∈ W, w⁻¹ * algebraMap R K a ∈ S) (a : ↥W) {β : ↥S}
    (hβ : algebraMap R K (a : R) = w * (β : K)) : divPow W S w h a = β :=
  Subtype.ext (by rw [coe_divPow_apply, hβ, inv_mul_cancel_left₀ hw])

/-- **`L` lies in the glued ideal.** The chart equations exhibit the extended ideals `L·B` and
`L·C` as divisible by `x ^ d` and by `y ^ d`, which is what
`Stacks.ResolutionOfSurfaces.CartierDescent.le_gluedIdeal` asks for. -/
private theorem le_gluedIdeal_of_span_pow_mul {x y : R} {B C : Subalgebra R K} (L : Ideal R)
    {d : ℕ} (Rx : Ideal ↥B) (Ry : Ideal ↥C)
    (hRx : Ideal.span {algebraMap R ↥B x ^ d} * Rx = Ideal.map (algebraMap R ↥B) L)
    (hRy : Ideal.span {algebraMap R ↥C y ^ d} * Ry = Ideal.map (algebraMap R ↥C) L) :
    L ≤ gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C :=
  le_gluedIdeal L _ _ d B C
    (exists_eq_mul_pow_of_mem_chartIdealSpan L B (algebraMap R ↥B x) d
      (hRx ▸ Ideal.mul_le_left))
    (exists_eq_mul_pow_of_mem_chartIdealSpan L C (algebraMap R ↥C y) d
      (hRy ▸ Ideal.mul_le_left))

/-- **The glued ideal is proper** as soon as `d` is positive and `x` is not invertible on the
first chart: were `x ^ d` a factor of `1` there, `x` would be a unit. -/
private theorem gluedIdeal_ne_top_of_not_isUnit {x : R} (y : R) {B : Subalgebra R K}
    (C : Subalgebra R K) {d : ℕ} (hd : 0 < d) (hxnu : ¬ IsUnit (algebraMap R ↥B x)) :
    gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C ≠ ⊤ := by
  refine gluedIdeal_ne_top _ _ d B C ?_
  rintro ⟨v, hv, hveq⟩
  refine hxnu (IsUnit.of_mul_eq_one (algebraMap R ↥B x ^ (d - 1) * ⟨v, hv⟩) (Subtype.ext ?_))
  have hdd : d - 1 + 1 = d := Nat.succ_pred_eq_of_pos hd
  change algebraMap R K x * (algebraMap R K x ^ (d - 1) * v) = 1
  rw [← mul_assoc, ← pow_succ', hdd]
  exact hveq.symm

/-- Dividing an element of the glued ideal by `x ^ d` lands in the first chart. -/
private theorem inv_mul_mem_left_of_mem_gluedIdeal (x y : R) {d : ℕ} (B C : Subalgebra R K)
    (hxd0 : algebraMap R K x ^ d ≠ 0) :
    ∀ a ∈ gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C,
      (algebraMap R K x ^ d)⁻¹ * algebraMap R K a ∈ B := by
  intro a ha
  obtain ⟨⟨v, hv, hveq⟩, -⟩ := (mem_gluedIdeal_iff _ _ d B C a).1 ha
  rwa [hveq, inv_mul_cancel_left₀ hxd0]

/-- Dividing an element of the glued ideal by `y ^ d` lands in the second chart. -/
private theorem inv_mul_mem_right_of_mem_gluedIdeal (x y : R) {d : ℕ} (B C : Subalgebra R K)
    (hyd0 : algebraMap R K y ^ d ≠ 0) :
    ∀ a ∈ gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C,
      (algebraMap R K y ^ d)⁻¹ * algebraMap R K a ∈ C := by
  intro a ha
  obtain ⟨-, ⟨v, hv, hveq⟩⟩ := (mem_gluedIdeal_iff _ _ d B C a).1 ha
  rwa [hveq, inv_mul_cancel_left₀ hyd0]

/-- The division map carries `L` into the residual ideal of the chart: an element of `L` is
`x ^ d` times an element of `Rx` by the chart equation. -/
private theorem divPow_mem_of_mem {x : R} {B : Subalgebra R K} {L W : Ideal R} {d : ℕ}
    (Rx : Ideal ↥B) (hRx : Ideal.span {algebraMap R ↥B x ^ d} * Rx = Ideal.map (algebraMap R ↥B) L)
    (hxd0 : algebraMap R K x ^ d ≠ 0)
    (h : ∀ a ∈ W, (algebraMap R K x ^ d)⁻¹ * algebraMap R K a ∈ B) (a : ↥W)
    (haL : (a : R) ∈ L) : divPow W B (algebraMap R K x ^ d) h a ∈ Rx := by
  obtain ⟨r, hr, hreq⟩ := mem_span_singleton_mul_iff.1
    (hRx.symm ▸ Ideal.mem_map_of_mem (algebraMap R ↥B) haL)
  have hcoe := congrArg (fun z : ↥B => (z : K)) hreq
  push_cast at hcoe
  exact divPow_eq_of_eq_mul W B hxd0 h a hcoe ▸ hr

/-- **The realisation theorem in the form the length bookkeeping consumes.** The glued ideal
contains `L` and is proper, and the division maps out of it carry `L` into the residual ideals
and are jointly surjective. The cofactors produced by
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_mem_gluedIdeal_realizing` are the values of
the division maps, because the realising element `a` satisfies `a = x ^ d β` and `a = y ^ d γ`
on the nose. -/
private theorem exists_divPow_data
    (hinj : Function.Injective (algebraMap R K)) {x y : R} {t s : K} (hts : t * s = 1)
    (hxt : algebraMap R K x * t = algebraMap R K y) (hx : x ≠ 0)
    (hreg : ∀ a : R, a * y ∈ Ideal.span ({x} : Set R) → a ∈ Ideal.span ({x} : Set R))
    {B C : Subalgebra R K} (hB : B = Algebra.adjoin R ({t} : Set K))
    (hC : C = Algebra.adjoin R ({s} : Set K)) (hsC : s ∈ C)
    (L : Ideal R) {d : ℕ} (hd : 0 < d) (Rx : Ideal ↥B) (Ry : Ideal ↥C)
    [IsArtinianRing (↥B ⧸ Rx)] [IsArtinianRing (↥C ⧸ Ry)]
    (hRx : Ideal.span {algebraMap R ↥B x ^ d} * Rx = Ideal.map (algebraMap R ↥B) L)
    (hRy : Ideal.span {algebraMap R ↥C y ^ d} * Ry = Ideal.map (algebraMap R ↥C) L)
    (hxnu : ¬ IsUnit (algebraMap R ↥B x))
    (Sx : Finset (PrimeSpectrum ↥B))
    (hSx : ∀ p : PrimeSpectrum ↥B, p ∈ Sx ↔ Rx ≤ p.asIdeal)
    (Sy Sy' : Finset (PrimeSpectrum ↥C))
    (hSy : ∀ p : PrimeSpectrum ↥C, p ∈ Sy ↔ Ry ≤ p.asIdeal) (hSy'le : Sy' ⊆ Sy)
    (hSy'mem : ∀ v ∈ Sy', (⟨s, hsC⟩ : ↥C) ∈ v.asIdeal) :
    L ≤ gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C ∧
      gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C ≠ ⊤ ∧
      ∃ (δB : ↥(gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C) →ₗ[R] ↥B)
        (δC : ↥(gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C) →ₗ[R] ↥C),
        JointlySurjective Rx Ry Sx Sy' δB δC ∧
          (∀ a : ↥(gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C),
            (a : R) ∈ L → δB a ∈ Rx) ∧
          ∀ a : ↥(gluedIdeal (algebraMap R K x) (algebraMap R K y) d B C),
            (a : R) ∈ L → δC a ∈ Ry := by
  have hx0 : algebraMap R K x ≠ 0 := fun h => hx (hinj (by rw [h, map_zero]))
  have hxd0 : algebraMap R K x ^ d ≠ 0 := pow_ne_zero d hx0
  have hy0 : algebraMap R K y ≠ 0 := by
    rw [← hxt]
    exact mul_ne_zero hx0 fun h => by simp [h] at hts
  have hyd0 : algebraMap R K y ^ d ≠ 0 := pow_ne_zero d hy0
  have hmemB := inv_mul_mem_left_of_mem_gluedIdeal x y B C hxd0
  have hmemC := inv_mul_mem_right_of_mem_gluedIdeal x y B C hyd0
  refine ⟨le_gluedIdeal_of_span_pow_mul L Rx Ry hRx hRy,
    gluedIdeal_ne_top_of_not_isUnit y C hd hxnu, divPow _ B _ hmemB, divPow _ C _ hmemC,
    fun ζ ζ' => ?_, fun a haL => divPow_mem_of_mem Rx hRx hxd0 hmemB a haL,
    fun a haL => divPow_mem_of_mem Ry hRy hyd0 hmemC a haL⟩
  obtain ⟨a, ha, β, γ, hβ, hγ, hζ, hζ'⟩ := exists_mem_gluedIdeal_realizing hinj hts hxt hx
    hreg hB hC hsC L d Rx Ry hRx hRy Sx hSx Sy Sy' hSy hSy'le hSy'mem ζ ζ'
  exact ⟨⟨a, ha⟩, fun w => by rw [divPow_eq_of_eq_mul _ _ hxd0 _ _ hβ]; exact hζ w,
    fun v => by rw [divPow_eq_of_eq_mul _ _ hyd0 _ _ hγ]; exact hζ' v⟩

/-- **The colength drop on the two charts.** With the data of
`Stacks.ResolutionOfSurfaces.CartierDescent.exists_mem_gluedIdeal_realizing`, and assuming in
addition that `R` is Noetherian, that `R ⧸ L` has finite length, that `d` is positive and that
`x` is not invertible on the first chart, the sum of the local colengths of the residual ideal
`Rx` over all primes above it, plus the sum of the local colengths of `Ry` over the given family
of primes above it, is strictly smaller than the colength of `L`.

This is the inequality of [Stacks, Tag 0AGT], read on the two standard charts of the blowup. -/
public theorem sum_length_localization_quotient_lt [IsNoetherianRing R]
    (hinj : Function.Injective (algebraMap R K)) {x y : R} {t s : K} (hts : t * s = 1)
    (hxt : algebraMap R K x * t = algebraMap R K y) (hx : x ≠ 0)
    (hreg : ∀ a : R, a * y ∈ Ideal.span ({x} : Set R) → a ∈ Ideal.span ({x} : Set R))
    {B C : Subalgebra R K} (hB : B = Algebra.adjoin R ({t} : Set K))
    (hC : C = Algebra.adjoin R ({s} : Set K)) (hsC : s ∈ C)
    (L : Ideal R) [IsArtinian R (R ⧸ L)] {d : ℕ} (hd : 0 < d)
    (Rx : Ideal ↥B) (Ry : Ideal ↥C)
    [IsArtinianRing (↥B ⧸ Rx)] [IsArtinianRing (↥C ⧸ Ry)]
    (hRx : Ideal.span {algebraMap R ↥B x ^ d} * Rx = Ideal.map (algebraMap R ↥B) L)
    (hRy : Ideal.span {algebraMap R ↥C y ^ d} * Ry = Ideal.map (algebraMap R ↥C) L)
    (hxnu : ¬ IsUnit (algebraMap R ↥B x))
    (Sx : Finset (PrimeSpectrum ↥B))
    (hSx : ∀ p : PrimeSpectrum ↥B, p ∈ Sx ↔ Rx ≤ p.asIdeal)
    (Sy Sy' : Finset (PrimeSpectrum ↥C))
    (hSy : ∀ p : PrimeSpectrum ↥C, p ∈ Sy ↔ Ry ≤ p.asIdeal) (hSy'le : Sy' ⊆ Sy)
    (hSy'mem : ∀ v ∈ Sy', (⟨s, hsC⟩ : ↥C) ∈ v.asIdeal) :
    ∑ w ∈ Sx, Module.length (Localization.AtPrime w.asIdeal)
        (Localization.AtPrime w.asIdeal ⧸
          Ideal.map (algebraMap ↥B (Localization.AtPrime w.asIdeal)) Rx) +
      ∑ v ∈ Sy', Module.length (Localization.AtPrime v.asIdeal)
        (Localization.AtPrime v.asIdeal ⧸
          Ideal.map (algebraMap ↥C (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) := by
  obtain ⟨hLW, hW, δB, δC, hsurj, hkerB, hkerC⟩ := exists_divPow_data hinj hts hxt hx hreg hB
    hC hsC L hd Rx Ry hRx hRy hxnu Sx hSx Sy Sy' hSy hSy'le hSy'mem
  have := sum_length_lt_of_surjective hLW hW Rx Ry Sx Sy' δB δC hsurj hkerB hkerC
  exact this

/-- **The colength drop on the two charts, over the base ring.** Same situation as
`Stacks.ResolutionOfSurfaces.CartierDescent.sum_length_localization_quotient_lt`, with every
length taken over `R`: the `R`-colength of the residual ideal on the first chart, plus the sum of
the `R`-colengths of the residual ideal on the second chart over the given family of primes, is
strictly smaller than the `R`-colength of `L`.

This is the form the inequality of [Stacks, Tag 0AGT] takes when the global sections of the
residual quotient are measured over the base: the sum of the local colengths over their own local
rings is in general strictly smaller, by the degrees of the residue field extensions, so it is
this stronger statement that bounds `length_A Γ(X, 𝒪_X/𝒥')`. Over the first chart the family of
all primes above `Rx` reassembles into the single quotient `B ⧸ Rx`. -/
public theorem length_quotient_add_sum_length_localization_lt [IsNoetherianRing R]
    (hinj : Function.Injective (algebraMap R K)) {x y : R} {t s : K} (hts : t * s = 1)
    (hxt : algebraMap R K x * t = algebraMap R K y) (hx : x ≠ 0)
    (hreg : ∀ a : R, a * y ∈ Ideal.span ({x} : Set R) → a ∈ Ideal.span ({x} : Set R))
    {B C : Subalgebra R K} (hB : B = Algebra.adjoin R ({t} : Set K))
    (hC : C = Algebra.adjoin R ({s} : Set K)) (hsC : s ∈ C)
    (L : Ideal R) [IsArtinian R (R ⧸ L)] {d : ℕ} (hd : 0 < d)
    (Rx : Ideal ↥B) (Ry : Ideal ↥C)
    [IsArtinianRing (↥B ⧸ Rx)] [IsArtinianRing (↥C ⧸ Ry)]
    (hRx : Ideal.span {algebraMap R ↥B x ^ d} * Rx = Ideal.map (algebraMap R ↥B) L)
    (hRy : Ideal.span {algebraMap R ↥C y ^ d} * Ry = Ideal.map (algebraMap R ↥C) L)
    (hxnu : ¬ IsUnit (algebraMap R ↥B x))
    (Sx : Finset (PrimeSpectrum ↥B))
    (hSx : ∀ p : PrimeSpectrum ↥B, p ∈ Sx ↔ Rx ≤ p.asIdeal)
    (Sy Sy' : Finset (PrimeSpectrum ↥C))
    (hSy : ∀ p : PrimeSpectrum ↥C, p ∈ Sy ↔ Ry ≤ p.asIdeal) (hSy'le : Sy' ⊆ Sy)
    (hSy'mem : ∀ v ∈ Sy', (⟨s, hsC⟩ : ↥C) ∈ v.asIdeal) :
    Module.length R (↥B ⧸ Rx) +
      ∑ v ∈ Sy', Module.length R (Localization.AtPrime v.asIdeal ⧸
        Ideal.map (algebraMap ↥C (Localization.AtPrime v.asIdeal)) Ry) <
      Module.length R (R ⧸ L) := by
  obtain ⟨hLW, hW, δB, δC, hsurj, hkerB, hkerC⟩ := exists_divPow_data hinj hts hxt hx hreg hB
    hC hsC L hd Rx Ry hRx hRy hxnu Sx hSx Sy Sy' hSy hSy'le hSy'mem
  have := length_quotient_add_sum_length_lt_of_surjective hLW hW Rx Ry Sx Sy' δB δC hSx hsurj
    hkerB hkerC
  exact this

end Stacks.ResolutionOfSurfaces.CartierDescent

end
