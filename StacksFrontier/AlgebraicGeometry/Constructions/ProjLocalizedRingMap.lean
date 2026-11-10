module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjBasicOpen

/-!
# Restriction maps between localizations at standard opens of Proj

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and let `f`, `g` be homogeneous elements of positive
degree with `D₊(g) ⊆ D₊(f)`. This file constructs the two canonical restriction maps attached to
that containment — the map `A_f → A_g` of ordinary localizations and the map `A₍f₎ → A₍g₎` of
their degree-zero parts — and identifies the second as a localization of the first.

Both maps come from the same source: by `ProjectiveSpectrum.exists_pow_eq_mul_of_basicOpen_le`
the containment gives a factorization `g ^ e = a * f` with `a` homogeneous, which makes `f`
invertible after inverting `g`, so the universal property of `A_f` supplies a unique
`A`-algebra map to `A_g`. The degree-zero map is the restriction of that one, and the content of
`isLocalizationAway_degreeZeroRingMap` is that it exhibits `A₍g₎` as the localization of `A₍f₎`
at the single degree-zero fraction `g ^ deg f / f ^ deg g` — the algebraic statement behind the
fact that `D₊(g)` is a standard open of the affine scheme `D₊(f) = Spec A₍f₎`.

## Main definitions

* `ProjectiveSpectrum.localizedRingMap`: the canonical `A`-algebra map `A_f → A_g`.
* `ProjectiveSpectrum.degreeZeroRingMap`: the canonical `𝒜 0`-algebra map `A₍f₎ → A₍g₎`.
* `HomogeneousLocalization.mapIdₐ`: the algebra-map form of `HomogeneousLocalization.mapId`.

## Main results

* `ProjectiveSpectrum.val_degreeZeroRingMap`: the degree-zero map agrees with the map of
  ordinary localizations under the canonical embeddings `A₍f₎ ↪ A_f`.
* `ProjectiveSpectrum.isLocalizationAway_degreeZeroRingMap`: `A₍g₎` is the localization of
  `A₍f₎` at `g ^ deg f / f ^ deg g`.

## Implementation notes

The degrees of `f` and `g` enter `localizedRingMap` and `degreeZeroRingMap` as the bare existence
statements `∃ d, 0 < d ∧ f ∈ 𝒜 d`, so that the maps depend on no choice of degree; the
factorization is then extracted with `Classical.choose`. The localization statement, by contrast,
takes the degrees explicitly, since they appear in the element being inverted.

`localizedRingMap` is stated for a monoid grading (`AddSubmonoidClass`) and derives the
invertibility of `f` in `A_g` from the factorization directly. The degree-zero material needs
subtraction of degrees and so assumes `AddSubgroupClass`; there it is
`ProjectiveSpectrum.isUnit_algebraMap_away_of_basicOpen_le` that supplies the same invertibility.
The two derivations are deliberately kept separate rather than merged: using the second inside
`localizedRingMap` would strengthen that map's hypotheses.

The intermediate maps attached to a factorization `g ^ e = a * f` are public rather than private,
because the construction of `degreeZeroRingMap` is reducible and so names them.

## References

* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
-/

@[expose] public section

namespace HomogeneousLocalization

variable {S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- `HomogeneousLocalization.mapId` as a map of `𝒜 0`-algebras: enlarging the denominators of a
degree-zero fraction fixes the elements of degree zero. -/
public def mapIdₐ {x y : S} (h : Submonoid.powers x ≤ Submonoid.powers y) :
    HomogeneousLocalization.Away 𝒜 x →ₐ[𝒜 0] HomogeneousLocalization.Away 𝒜 y where
  __ := HomogeneousLocalization.mapId 𝒜 h
  commutes' z := by
    ext
    rfl

/-- Enlarging denominators commutes with the embedding of a degree-zero localization into the
ordinary localization. -/
public lemma val_mapIdₐ {x y : S} (h : Submonoid.powers x ≤ Submonoid.powers y)
    (z : HomogeneousLocalization.Away 𝒜 x) :
    HomogeneousLocalization.val (mapIdₐ 𝒜 h z) =
      IsLocalization.map (M := Submonoid.powers x) (S := Localization.Away x)
        (T := Submonoid.powers y) (Localization.Away y) (RingHom.id S)
        (by intro w hw; simpa using h hw) (HomogeneousLocalization.val z) := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  change HomogeneousLocalization.val
      (HomogeneousLocalization.map (.id 𝒜) (by intro w hw; simpa using h hw)
        (HomogeneousLocalization.mk c)) = _
  simp only [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  change IsLocalization.mk' _ (c.num : S) _ = IsLocalization.mk' _ (c.num : S) _
  rfl

end HomogeneousLocalization

namespace ProjectiveSpectrum

section AddSubmonoidClass

variable {S σ : Type*} [CommRing S] [SetLike σ S] [AddSubmonoidClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If `f` and `g` are homogeneous elements of positive degree and `D₊(g) ⊆ D₊(f)`,
then there is a canonical `S`-algebra map `S_f → S_g`. -/
public noncomputable def localizedRingMap (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Localization.Away f →ₐ[S] Localization.Away g := by
  let d : ℕ := Classical.choose hf
  let hd : 0 < d := (Classical.choose_spec hf).1
  let hfd : f ∈ 𝒜 d := (Classical.choose_spec hf).2
  let n : ℕ := Classical.choose hg
  let hn : 0 < n := (Classical.choose_spec hg).1
  let hgn : g ∈ 𝒜 n := (Classical.choose_spec hg).2
  let hdiv := exists_pow_eq_mul_of_basicOpen_le 𝒜 hfd hd hgn hn hfg
  let e : ℕ := Classical.choose hdiv
  let hcoeff := (Classical.choose_spec hdiv).2
  let a : S := Classical.choose hcoeff
  have hga : g ^ e = a * f := (Classical.choose_spec hcoeff).2
  have hgu : IsUnit (algebraMap S (Localization.Away g) g) :=
    IsLocalization.Away.algebraMap_isUnit g
  have hpow : IsUnit (algebraMap S (Localization.Away g) (g ^ e)) := by
    simpa only [map_pow] using hgu.pow e
  have hamul : IsUnit (algebraMap S (Localization.Away g) a *
      algebraMap S (Localization.Away g) f) := by
    rw [← map_mul, ← hga]
    exact hpow
  have hfunit : IsUnit (algebraMap S (Localization.Away g) f) :=
    isUnit_of_mul_isUnit_right hamul
  exact IsLocalization.Away.liftAlgHom
    (f := Algebra.ofId S (Localization.Away g)) f hfunit

end AddSubmonoidClass

section AddSubgroupClass

variable {S σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-zero map `S_(f) → S_(g)` determined by a factorization `g ^ e = a * f` with `a`
homogeneous: enlarge the denominators of `HomogeneousLocalization.awayMapₐ` from powers of
`g ^ e` to powers of `g`. -/
public noncomputable def degreeZeroMapOfFactorization {f g a : S} {e d : ℕ}
    (ha : a ∈ 𝒜 d) (hga : g ^ e = a * f) :
    HomogeneousLocalization.Away 𝒜 f →ₐ[𝒜 0] HomogeneousLocalization.Away 𝒜 g :=
  (HomogeneousLocalization.mapIdₐ 𝒜 (Submonoid.powers_le.mpr ⟨e, rfl⟩)).comp
    (HomogeneousLocalization.awayMapₐ 𝒜 ha (by rw [mul_comm]; exact hga))

/-- The map `S_f → S_g` of ordinary localizations determined by a factorization `g ^ e = a * f`:
such a factorization makes `f` a unit in `S_g`. -/
public noncomputable def localizationMapOfFactorization {f g a : S} {e : ℕ}
    (hga : g ^ e = a * f) : Localization.Away f →ₐ[S] Localization.Away g := by
  have hgu : IsUnit (algebraMap S (Localization.Away g) g) :=
    IsLocalization.Away.algebraMap_isUnit g
  have hpow : IsUnit (algebraMap S (Localization.Away g) (g ^ e)) := by
    simpa only [map_pow] using hgu.pow e
  have hamul : IsUnit (algebraMap S (Localization.Away g) a *
      algebraMap S (Localization.Away g) f) := by
    rw [← map_mul, ← hga]
    exact hpow
  exact IsLocalization.Away.liftAlgHom
    (f := Algebra.ofId S (Localization.Away g)) f (isUnit_of_mul_isUnit_right hamul)

/-- The same map `S_f → S_g`, factored through `S_{g ^ e}`. This is the route taken by
`HomogeneousLocalization.awayMap`, and `val_degreeZeroMapOfFactorization` identifies it with
`localizationMapOfFactorization`. -/
public noncomputable def localizationMapViaPower {f g a : S} {e : ℕ}
    (hga : g ^ e = a * f) : Localization.Away f →+* Localization.Away g :=
  (IsLocalization.map (M := Submonoid.powers (g ^ e))
    (S := Localization.Away (g ^ e)) (T := Submonoid.powers g)
    (Localization.Away g) (RingHom.id S)
    (by
      intro z hz
      simpa using
        (Submonoid.powers_le (n := g ^ e) (P := Submonoid.powers g)).mpr ⟨e, rfl⟩ hz)).comp
  (Localization.awayLift (algebraMap S (Localization.Away (g ^ e))) f
    (isUnit_of_dvd_unit (map_dvd _ ⟨a, by rw [mul_comm]; exact hga⟩)
      (IsLocalization.Away.algebraMap_isUnit (g ^ e))))

/-- The degree-zero map of a factorization agrees with its map of ordinary localizations under
the canonical embeddings of degree-zero localizations. -/
public lemma val_degreeZeroMapOfFactorization {f g a : S} {e d : ℕ}
    (ha : a ∈ 𝒜 d) (hga : g ^ e = a * f)
    (z : HomogeneousLocalization.Away 𝒜 f) :
    HomogeneousLocalization.val (degreeZeroMapOfFactorization 𝒜 ha hga z) =
      localizationMapOfFactorization hga (HomogeneousLocalization.val z) := by
  rw [degreeZeroMapOfFactorization, AlgHom.comp_apply, HomogeneousLocalization.val_mapIdₐ,
    HomogeneousLocalization.awayMapₐ_apply, HomogeneousLocalization.val_awayMap]
  change localizationMapViaPower hga (HomogeneousLocalization.val z) =
    localizationMapOfFactorization hga (HomogeneousLocalization.val z)
  apply DFunLike.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers f) ?_)
  ext s
  simp [localizationMapViaPower, localizationMapOfFactorization]

/-- If `f` and `g` are homogeneous elements of positive degree and `D₊(g) ⊆ D₊(f)`, then
there is a canonical `S₀`-algebra map `S_(f) → S_(g)`. -/
public noncomputable def degreeZeroRingMap (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    HomogeneousLocalization.Away 𝒜 f →ₐ[𝒜 0] HomogeneousLocalization.Away 𝒜 g := by
  let d : ℕ := Classical.choose hf
  let hd : 0 < d := (Classical.choose_spec hf).1
  let hfd : f ∈ 𝒜 d := (Classical.choose_spec hf).2
  let n : ℕ := Classical.choose hg
  let hn : 0 < n := (Classical.choose_spec hg).1
  let hgn : g ∈ 𝒜 n := (Classical.choose_spec hg).2
  let hdiv := exists_pow_eq_mul_of_basicOpen_le 𝒜 hfd hd hgn hn hfg
  let hcoeff := (Classical.choose_spec hdiv).2
  let ha := (Classical.choose_spec hcoeff).1
  exact degreeZeroMapOfFactorization 𝒜 (Classical.choose_spec ha)
    (Classical.choose_spec hcoeff).2

/-- The degree-zero localization map agrees, under the canonical embeddings, with the map of
ordinary localizations. -/
public theorem val_degreeZeroRingMap (f g : S)
    (hf : ∃ d : ℕ, 0 < d ∧ f ∈ 𝒜 d) (hg : ∃ d : ℕ, 0 < d ∧ g ∈ 𝒜 d)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (x : HomogeneousLocalization.Away 𝒜 f) :
    HomogeneousLocalization.val (degreeZeroRingMap 𝒜 f g hf hg hfg x) =
      localizedRingMap 𝒜 f g hf hg hfg (HomogeneousLocalization.val x) := by
  dsimp [degreeZeroRingMap]
  rw [val_degreeZeroMapOfFactorization]
  apply DFunLike.congr_fun
  apply Localization.algHom_ext
  ext

/-- With the degrees of `f` and `g` named, `localizedRingMap` is the lift of `S → S_g` through
the universal property of `S_f`, the invertibility of `f` in `S_g` being
`isUnit_algebraMap_away_of_basicOpen_le`. -/
private lemma localizedRingMap_eq_awayLift (f g : S) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    localizedRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg =
      IsLocalization.Away.liftAlgHom (A := S) (P := Localization.Away g)
        (f := Algebra.ofId S (Localization.Away g)) f
        (by simpa using
          (isUnit_algebraMap_away_of_basicOpen_le 𝒜 hf hd hg he hfg)) := by
  apply Localization.algHom_ext
  ext

/-- The value of `degreeZeroRingMap` on the fraction `a * g ^ ((d - 1) * n) / f ^ (n * e)`. -/
private lemma degreeZeroRingMap_val_mk (f g : S) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (n : ℕ) (a : S) (ha : a ∈ 𝒜 (n • e)) :
    HomogeneousLocalization.val
        ((degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg)
          (HomogeneousLocalization.Away.mk 𝒜 hf (n * e) (a * g ^ ((d - 1) * n)) (by
            convert SetLike.mul_mem_graded ha
              (SetLike.pow_mem_graded ((d - 1) * n) hg) using 2
            simp only [Nat.mul_comm, smul_eq_mul, Nat.mul_sub_left_distrib, mul_one,
              Nat.mul_left_comm]
            have hle : e * n ≤ d * (e * n) := Nat.le_mul_of_pos_left _ hd
            exact (Nat.add_sub_of_le hle).symm))) =
      (IsLocalization.Away.liftAlgHom (A := S) (P := Localization.Away g)
        (f := Algebra.ofId S (Localization.Away g)) f
        (by simpa using
          (isUnit_algebraMap_away_of_basicOpen_le 𝒜 hf hd hg he hfg)))
        (Localization.mk (a * g ^ ((d - 1) * n))
          ⟨f ^ (n * e), by
            exact (Submonoid.mem_powers_iff (f ^ (n * e)) f).2 ⟨n * e, rfl⟩⟩) := by
  rw [val_degreeZeroRingMap, localizedRingMap_eq_awayLift 𝒜 f g d e hd he hf hg hfg]
  rfl

/-- The degree-zero localization `S_(g)` is the localization of `S_(f)` at the element
`g ^ d / f ^ e`, where `d` and `e` are the positive degrees of `f` and `g` respectively. -/
public theorem isLocalizationAway_degreeZeroRingMap (f g : S) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    letI : Algebra (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away 𝒜 g) :=
      (degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom.toAlgebra
    IsLocalization.Away
      (HomogeneousLocalization.Away.mk 𝒜 hf e (g ^ d) (by
        simpa [mul_comm] using SetLike.pow_mem_graded d hg))
      (HomogeneousLocalization.Away 𝒜 g) := by
  let : Algebra (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away 𝒜 g) :=
    (degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).toRingHom.toAlgebra
  let t : HomogeneousLocalization.Away 𝒜 f :=
    HomogeneousLocalization.Away.mk 𝒜 hf e (g ^ d) (by
      simpa [mul_comm] using SetLike.pow_mem_graded d hg)
  let u : HomogeneousLocalization.Away 𝒜 g :=
    HomogeneousLocalization.Away.mk 𝒜 hg d (f ^ e) (by
      simpa [mul_comm] using SetLike.pow_mem_graded e hf)
  have htu : (degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg) t * u = 1 := by
    apply HomogeneousLocalization.val_injective (Submonoid.powers g)
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
      HomogeneousLocalization.Away.val_mk]
    rw [val_degreeZeroRingMap, localizedRingMap_eq_awayLift 𝒜 f g d e hd he hf hg hfg]
    dsimp [t, u]
    rw [Localization.mk_eq_mk', Localization.mk_eq_mk']
    set F : Localization.Away f →+* Localization.Away g := IsLocalization.Away.lift f
      (by simpa using (isUnit_algebraMap_away_of_basicOpen_le 𝒜 hf hd hg he hfg))
    have hfunit : IsUnit ((algebraMap S (Localization.Away g)) (f ^ e)) := by
      simpa using (isUnit_algebraMap_away_of_basicOpen_le 𝒜 hf hd hg he hfg).pow e
    apply hfunit.mul_left_cancel
    rw [mul_one, ← mul_assoc]
    have hF : (algebraMap S (Localization.Away g)) (f ^ e) *
        F (IsLocalization.mk' (Localization.Away f) (g ^ d)
          (⟨f ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers f)) =
        (algebraMap S (Localization.Away g)) (g ^ d) :=
      ((IsLocalization.lift_mk'_spec
        (M := Submonoid.powers f) (S := Localization.Away f)
        (g := algebraMap S (Localization.Away g))
        (fun y => by
          obtain ⟨k, hk⟩ := y.2
          rw [← hk]
          simpa only [map_pow] using
            (isUnit_algebraMap_away_of_basicOpen_le 𝒜 hf hd hg he hfg).pow k)
        (g ^ d) _ (⟨f ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers f)).mp rfl).symm
    rw [hF]
    exact IsLocalization.mk'_spec' (M := Submonoid.powers g)
      (Localization.Away g) (f ^ e) (⟨g ^ d, ⟨d, rfl⟩⟩ : Submonoid.powers g)
  have ht : IsUnit ((algebraMap (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.Away 𝒜 g)) t) := by
    rw [show algebraMap (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away 𝒜 g) =
        degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg from rfl]
    exact isUnit_iff_exists_inv.mpr ⟨u, htu⟩
  constructor
  constructor
  · rintro ⟨r, n, rfl⟩
    rw [map_pow]
    exact ht.pow n
  · intro z
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hg z
    let x : HomogeneousLocalization.Away 𝒜 f :=
      HomogeneousLocalization.Away.mk 𝒜 hf (n * e)
        (a * g ^ ((d - 1) * n)) (by
          convert SetLike.mul_mem_graded ha
            (SetLike.pow_mem_graded ((d - 1) * n) hg) using 2
          simp only [Nat.mul_comm, smul_eq_mul, Nat.mul_sub_left_distrib, mul_one,
            Nat.mul_left_comm]
          have hle : e * n ≤ d * (e * n) := Nat.le_mul_of_pos_left _ hd
          exact (Nat.add_sub_of_le hle).symm)
    refine ⟨⟨x, ⟨t ^ n, show t ^ n ∈ Submonoid.powers t from ⟨n, rfl⟩⟩⟩, ?_⟩
    apply HomogeneousLocalization.val_injective (Submonoid.powers g)
    dsimp
    rw [show algebraMap (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away 𝒜 g) =
        degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg from rfl]
    change HomogeneousLocalization.val
      (HomogeneousLocalization.Away.mk 𝒜 hg n a ha *
        (degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg) (t ^ n)) =
      HomogeneousLocalization.val
        ((degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg) x)
    dsimp [x]
    rw [HomogeneousLocalization.val_mul]
    rw [val_degreeZeroRingMap, degreeZeroRingMap_val_mk 𝒜 f g d e hd he hf hg hfg n a ha]
    rw [localizedRingMap_eq_awayLift 𝒜 f g d e hd he hf hg hfg]
    simp only [HomogeneousLocalization.Away.val_mk]
    have hZ : (algebraMap S (Localization.Away g)) (g ^ n) *
        IsLocalization.mk' (Localization.Away g) a
          (⟨g ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g) =
        (algebraMap S (Localization.Away g)) a :=
      IsLocalization.mk'_spec' (M := Submonoid.powers g)
        (Localization.Away g) a (⟨g ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g)
    have hfunitN : IsUnit ((algebraMap S (Localization.Away g)) (f ^ (n * e))) := by
      simpa using
        (isUnit_algebraMap_away_of_basicOpen_le 𝒜 hf hd hg he hfg).pow (n * e)
    apply hfunitN.mul_left_cancel
    rw [HomogeneousLocalization.val_pow]
    simp only [t, HomogeneousLocalization.Away.val_mk]
    simp only [IsLocalization.Away.liftAlgHom_apply]
    rw [Localization.mk_eq_mk']
    rw [map_pow (IsLocalization.Away.lift f _) (Localization.mk (g ^ d)
      (⟨f ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers f)) n]
    set L' : Localization.Away g :=
      (IsLocalization.Away.lift f _)
        (Localization.mk (g ^ d) (⟨f ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers f))
    have hL' : (algebraMap S (Localization.Away g)) (f ^ e) * L' =
        (algebraMap S (Localization.Away g)) (g ^ d) := by
      dsimp [L']
      rw [Localization.mk_eq_mk']
      exact ((IsLocalization.lift_mk'_spec
        (M := Submonoid.powers f) (S := Localization.Away f)
        (g := algebraMap S (Localization.Away g)) _ (g ^ d) _
        (⟨f ^ e, ⟨e, rfl⟩⟩ : Submonoid.powers f)).mp rfl).symm
    rw [mul_left_comm]
    have hLn := congrArg (fun q : Localization.Away g => q ^ n) hL'
    simp only [mul_pow] at hLn
    conv_lhs => rw [Nat.mul_comm n e, pow_mul, map_pow]
    rw [hLn]
    have hd_eq : d = 1 + (d - 1) := by omega
    conv_lhs => rw [← map_pow, ← pow_mul g d n, hd_eq, add_mul, one_mul, pow_add, map_mul]
    rw [← mul_assoc, mul_comm (IsLocalization.mk' (Localization.Away g) a
      (⟨g ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers g)), hZ]
    rw [← map_mul]
    apply (IsLocalization.lift_mk'_spec
      (M := Submonoid.powers f) (S := Localization.Away f)
      (g := algebraMap S (Localization.Away g)) _
      (a * g ^ ((d - 1) * n)) _
      (⟨f ^ (n * e), ⟨n * e, rfl⟩⟩ : Submonoid.powers f)).mp
    · rw [← Localization.mk_eq_mk'_apply]
      congr
    · intro y
      obtain ⟨j, hj⟩ := y.2
      rw [← hj]
      simpa only [map_pow] using
        (isUnit_algebraMap_away_of_basicOpen_le 𝒜 hf hd hg he hfg).pow j
  · intro x y hxy
    rw [show algebraMap (HomogeneousLocalization.Away 𝒜 f)
        (HomogeneousLocalization.Away 𝒜 g) =
        degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg from rfl] at hxy
    have hxy' := congrArg HomogeneousLocalization.val hxy
    change HomogeneousLocalization.val
      ((degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg) x) =
      HomogeneousLocalization.val
        ((degreeZeroRingMap 𝒜 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg) y) at hxy'
    simp_rw [val_degreeZeroRingMap] at hxy'
    rw [localizedRingMap_eq_awayLift 𝒜 f g d e hd he hf hg hfg] at hxy'
    obtain ⟨a, sa, hxa⟩ := IsLocalization.exists_mk'_eq
      (Submonoid.powers f) (HomogeneousLocalization.val x)
    obtain ⟨b, sb, hyb⟩ := IsLocalization.exists_mk'_eq
      (Submonoid.powers f) (HomogeneousLocalization.val y)
    rw [← hxa, ← hyb] at hxy'
    let hfUnits : ∀ z : Submonoid.powers f,
        IsUnit ((algebraMap S (Localization.Away g)) z) := fun z => by
      obtain ⟨j, hj⟩ := z.2
      rw [← hj]
      simpa only [map_pow] using
        (isUnit_algebraMap_away_of_basicOpen_le 𝒜 hf hd hg he hfg).pow j
    change (IsLocalization.lift hfUnits) (IsLocalization.mk' (Localization.Away f) a sa) =
      (IsLocalization.lift hfUnits) (IsLocalization.mk' (Localization.Away f) b sb) at hxy'
    have hab : (algebraMap S (Localization.Away g)) (a * sb) =
        (algebraMap S (Localization.Away g)) (b * sa) :=
      (IsLocalization.lift_eq_iff (M := Submonoid.powers f)
        (R := S) (S := Localization.Away f) (g := algebraMap S (Localization.Away g))
        (x := (a, sa)) (y := (b, sb)) hfUnits).mp hxy'
    obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq g hab
    refine ⟨⟨t ^ k, ⟨k, rfl⟩⟩, ?_⟩
    apply HomogeneousLocalization.val_injective (Submonoid.powers f)
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_pow, HomogeneousLocalization.Away.val_mk, ← hxa, ← hyb]
    rw [Localization.mk_eq_mk']
    simp only [← IsLocalization.mk'_pow, ← IsLocalization.mk'_mul]
    apply IsLocalization.mk'_eq_of_eq
    change ((f ^ e) ^ k * (sa : S)) * ((g ^ d) ^ k * b) =
      ((f ^ e) ^ k * (sb : S)) * ((g ^ d) ^ k * a)
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    linear_combination -((f ^ e) ^ k * (g ^ d') ^ k) * hk

end AddSubgroupClass

end ProjectiveSpectrum
