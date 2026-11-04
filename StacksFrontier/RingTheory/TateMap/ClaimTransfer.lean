module

public import StacksFrontier.RingTheory.TateMap.ClaimEngine

/-!
# The Claim of Proposition 0FKD: transfer along nice families

The Tate map pulled back along a classification by a basic chart of the universal family is
compared across classifications in four steps.

* *The engine*: if a nice chart `Z` maps to `A → B` and is classified in two ways, the two
  composite classifications of `A → B` give the same Tate map, by uniqueness on `Z`.
* *Locality*: Tate maps agreeing on a principal cover agree.
* *Invariance*: two classifications of the same presentation give the same Tate map (through a
  common degree bound).
* *Transfer*: a nice family with two presentations, specializing to two presentations of `B`,
  makes classifications of the two presentations of `B` give the same Tate map.

Two presentations whose classifications give the same Tate map on every localization are called
*Tate-related* (`PresRel`); the relation is symmetric and transitive, holds for presentations
differing only in the localization element, and is produced by transfer.

All names are in the namespace `Stacks.TateMap`.

## Main definitions

* `awaySquare`: the restriction of `A → B` to a principal open `D(b)`.
* `awayChartAlgebra`: the chart map of a classification followed by `B → B_b`.
* `PresRel`: Tate-relatedness of two presentations.

## Main results

* `tateOf_eq_of_isNiceChart`: the engine.
* `tateOf_eq_of_local`: locality.
* `tateOf_classificationOf_eq_trunc`: raising the degree bound of a classification does not change
  the Tate map.
* `tateOf_classificationOf_invariant`: invariance.
* `tateOf_transfer`, `presRel_of_transfer`: transfer.
* `PresRel.symm`, `PresRel.trans`, `presRel_of_eqRelations`: properties of Tate-relatedness.

## References

* [Stacks Project, Tag 0FKD](https://stacks.math.columbia.edu/tag/0FKD)
-/

@[expose] public noncomputable section

open Stacks.Discriminant MvPolynomial

universe u

namespace Stacks.TateMap

section Engine

variable {A B ZA ZB : Type u} [CommRing A] [CommRing B] [CommRing ZA] [CommRing ZB]
  [Algebra A B] [Algebra ZA ZB] [Algebra ZA A] [Algebra ZB B]
  [Algebra.Syntomic A B] [Algebra.Syntomic ZA ZB] [IsNoetherianRing A] [IsNoetherianRing ZA]
  [IsNoetherianRing ZB] [Algebra.QuasiFinite ZA ZB]

/-- **The engine.** Let `Z` be a nice chart with a chart base change `E` to `A → B`, and let
`F₁`, `F₂` be two classifications of `Z`. Any two classifications of `A → B` whose ring maps are
those of the composites `E ∘ F₁` and `E ∘ F₂` give the same Tate map. -/
theorem tateOf_eq_of_isNiceChart (hZ : IsNiceChart ZA ZB) (E : ChartBaseChange ZA ZB A B)
    {n₁ d₁ : ℕ} (k₁ : MvPolynomial (Fin n₁) (univBase.{u} n₁ d₁))
    [Algebra.QuasiFinite (univBase.{u} n₁ d₁) (univChart n₁ d₁ k₁)]
    {n₂ d₂ : ℕ} (k₂ : MvPolynomial (Fin n₂) (univBase.{u} n₂ d₂))
    [Algebra.QuasiFinite (univBase.{u} n₂ d₂) (univChart n₂ d₂ k₂)]
    (iR₁ : Algebra (univBase.{u} n₁ d₁) ZA) (iC₁ : Algebra (univChart n₁ d₁ k₁) ZB)
    (F₁ : @ChartBaseChange _ _ ZA ZB _ _ _ _ _ iR₁ _ iC₁)
    (iR₂ : Algebra (univBase.{u} n₂ d₂) ZA) (iC₂ : Algebra (univChart n₂ d₂ k₂) ZB)
    (F₂ : @ChartBaseChange _ _ ZA ZB _ _ _ _ _ iR₂ _ iC₂)
    (jR₁ : Algebra (univBase.{u} n₁ d₁) A) (jC₁ : Algebra (univChart n₁ d₁ k₁) B)
    (hR₁ : ∀ x, @algebraMap _ _ _ _ jR₁ x = algebraMap ZA A (@algebraMap _ _ _ _ iR₁ x))
    (hC₁ : ∀ x, @algebraMap _ _ _ _ jC₁ x = algebraMap ZB B (@algebraMap _ _ _ _ iC₁ x))
    (D₁ : @ChartBaseChange _ _ A B _ _ _ _ _ jR₁ _ jC₁)
    (jR₂ : Algebra (univBase.{u} n₂ d₂) A) (jC₂ : Algebra (univChart n₂ d₂ k₂) B)
    (hR₂ : ∀ x, @algebraMap _ _ _ _ jR₂ x = algebraMap ZA A (@algebraMap _ _ _ _ iR₂ x))
    (hC₂ : ∀ x, @algebraMap _ _ _ _ jC₂ x = algebraMap ZB B (@algebraMap _ _ _ _ iC₂ x))
    (D₂ : @ChartBaseChange _ _ A B _ _ _ _ _ jR₂ _ jC₂)
    (G : FiniteOpenFactorization.{u, u, u} A B) :
    tateOf k₁ jR₁ jC₁ D₁ G = tateOf k₂ jR₂ jC₂ D₂ G := by
  obtain ⟨H⟩ := nonempty_finiteOpenFactorization.{u, u} (A := ZA) (B := ZB)
  have key : ∀ {n d : ℕ} (k : MvPolynomial (Fin n) (univBase.{u} n d))
      [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]
      (iR : Algebra (univBase.{u} n d) ZA) (iC : Algebra (univChart n d k) ZB)
      (F : @ChartBaseChange _ _ ZA ZB _ _ _ _ _ iR _ iC)
      (jR : Algebra (univBase.{u} n d) A) (jC : Algebra (univChart n d k) B)
      (hR : ∀ x, @algebraMap _ _ _ _ jR x = algebraMap ZA A (@algebraMap _ _ _ _ iR x))
      (hC : ∀ x, @algebraMap _ _ _ _ jC x = algebraMap ZB B (@algebraMap _ _ _ _ iC x))
      (D : @ChartBaseChange _ _ A B _ _ _ _ _ jR _ jC),
      tateOf k jR jC D G = pullbackTate E (pullbackTate F (cUniv n d k
        (nonempty_finiteOpenFactorization.{u, u} (A := univBase.{u} n d)
          (B := univChart n d k)).some) H) G := by
    intro n d k _ iR iC F jR jC hR hC D
    have : IsScalarTower (univBase.{u} n d) ZA A := IsScalarTower.of_algebraMap_eq hR
    have : IsScalarTower (univChart n d k) ZB B := IsScalarTower.of_algebraMap_eq hC
    exact pullbackTate_comp F E D _ H G
  rw [key k₁ iR₁ iC₁ F₁ jR₁ jC₁ hR₁ hC₁ D₁, key k₂ iR₂ iC₂ F₂ jR₂ jC₂ hR₂ hC₂ D₂]
  congr 1
  exact hZ.linearEquiv_ext H _ _ (deltaNL ZA ZB)
    (pullbackTate_deltaNL F₁ _ H (cUniv_deltaNL _ _ _ _))
    (pullbackTate_deltaNL F₂ _ H (cUniv_deltaNL _ _ _ _))

end Engine

section Local

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
  [IsNoetherianRing A] [Algebra.QuasiFinite A B]

/-- The restriction of `A → B` to the principal open `D(b)` of the source. -/
noncomputable def awaySquare (b : B) :
    ChartBaseChange A B A (Localization.Away b) :=
  haveI : IsLocalization.Away (1 : A) A :=
    IsLocalization.away_of_isUnit_of_bijective A isUnit_one Function.bijective_id
  ChartBaseChange.ofAway (1 : A) b fun x ↦ (IsScalarTower.algebraMap_apply A B _ x).symm

/-- A localization `B_b` of a syntomic `A`-algebra `B` is syntomic over `A`. -/
instance syntomic_localizationAway (b : B) : Algebra.Syntomic A (Localization.Away b) :=
  haveI : Algebra.Syntomic B (Localization.Away b) := Algebra.Smooth.syntomic B _
  Algebra.Syntomic.comp A B (Localization.Away b)

/-- The chart map of a classification, followed by the localization `B → B_b`. -/
@[instance_reducible]
noncomputable def awayChartAlgebra {C : Type*} [CommRing C] (jC : Algebra C B) (b : B) :
    Algebra C (Localization.Away b) :=
  ((algebraMap B (Localization.Away b)).comp (@algebraMap _ _ _ _ jC)).toAlgebra

/-- **Locality of the Tate maps of classifications.** If, around every maximal ideal of `B`,
there is a principal open `D(b)` on which any two classifications with the restricted ring maps
give the same Tate map, then the two classifications give the same Tate map. -/
theorem tateOf_eq_of_local
    {n₁ d₁ : ℕ} (k₁ : MvPolynomial (Fin n₁) (univBase.{u} n₁ d₁))
    [Algebra.QuasiFinite (univBase.{u} n₁ d₁) (univChart n₁ d₁ k₁)]
    {n₂ d₂ : ℕ} (k₂ : MvPolynomial (Fin n₂) (univBase.{u} n₂ d₂))
    [Algebra.QuasiFinite (univBase.{u} n₂ d₂) (univChart n₂ d₂ k₂)]
    (jR₁ : Algebra (univBase.{u} n₁ d₁) A) (jC₁ : Algebra (univChart n₁ d₁ k₁) B)
    (D₁ : @ChartBaseChange _ _ A B _ _ _ _ _ jR₁ _ jC₁)
    (jR₂ : Algebra (univBase.{u} n₂ d₂) A) (jC₂ : Algebra (univChart n₂ d₂ k₂) B)
    (D₂ : @ChartBaseChange _ _ A B _ _ _ _ _ jR₂ _ jC₂)
    (G : FiniteOpenFactorization.{u, u, u} A B)
    (H : ∀ q : Ideal B, q.IsMaximal → ∃ b ∉ q,
      ∀ (D₁' : @ChartBaseChange _ _ A (Localization.Away b) _ _ _ _ _ jR₁ _
          (awayChartAlgebra jC₁ b))
        (D₂' : @ChartBaseChange _ _ A (Localization.Away b) _ _ _ _ _ jR₂ _
          (awayChartAlgebra jC₂ b))
        (G' : FiniteOpenFactorization.{u, u, u} A (Localization.Away b)),
        tateOf k₁ jR₁ (awayChartAlgebra jC₁ b) D₁' G' =
          tateOf k₂ jR₂ (awayChartAlgebra jC₂ b) D₂' G') :
    tateOf k₁ jR₁ jC₁ D₁ G = tateOf k₂ jR₂ jC₂ D₂ G := by
  classical
  choose b hb hH using fun q : {q : Ideal B // q.IsMaximal} ↦ H q.1 q.2
  let s : Set B := Set.range b
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hb ⟨m, hm⟩ (hle (Ideal.subset_span ⟨⟨m, hm⟩, rfl⟩))
  have hq : ∀ c : s, ∃ q : {q : Ideal B // q.IsMaximal}, b q = c := fun c ↦ c.2
  choose q hqc using hq
  have : ∀ c : s, IsLocalization.Away (c : B) (Localization.Away (c : B)) := fun _ ↦
    inferInstance
  have key : ∀ (c : s) {n d : ℕ} (k : MvPolynomial (Fin n) (univBase.{u} n d))
      [Algebra.QuasiFinite (univBase.{u} n d) (univChart n d k)]
      (jR : Algebra (univBase.{u} n d) A) (jC : Algebra (univChart n d k) B)
      (D : @ChartBaseChange _ _ A B _ _ _ _ _ jR _ jC)
      (G' : FiniteOpenFactorization.{u, u, u} A (Localization.Away (c : B))),
      pullbackTate (awaySquare (c : B)) (tateOf k jR jC D G) G' =
        tateOf k jR (awayChartAlgebra jC c) (D := by
          let := awayChartAlgebra jC (c : B)
          have : @IsScalarTower (univChart n d k) B (Localization.Away (c : B)) jC.toSMul
              Algebra.toSMul (awayChartAlgebra jC (c : B)).toSMul :=
            IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
          exact (awaySquare (c : B)).comp D) G' := by
    intro c n d k _ jR jC D G'
    let := awayChartAlgebra jC (c : B)
    have : @IsScalarTower (univChart n d k) B (Localization.Away (c : B)) jC.toSMul
        Algebra.toSMul (awayChartAlgebra jC (c : B)).toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact (pullbackTate_comp D (awaySquare (c : B)) _ _ G G').symm
  have hG : ∀ c : s,
      Nonempty (FiniteOpenFactorization.{u, u, u} A (Localization.Away (c : B))) := fun c ↦
    nonempty_finiteOpenFactorization.{u, u}
  refine eq_of_pullbackTate_eq s hs (fun _ ↦ A) (fun c ↦ Localization.Away (c : B))
    (fun c ↦ awaySquare (c : B)) (fun c ↦ (hG c).some) _ _ fun c ↦ ?_
  rw [key c k₁ jR₁ jC₁ D₁, key c k₂ jR₂ jC₂ D₂]
  have := hH (q c)
  rw [hqc c] at this
  exact this _ _ _

end Local

end Stacks.TateMap

namespace Stacks.TateMap

section Truncation

/-- A localization of a localization of `P[x]` away from `x` at an element associated to the image
of `y` is the localization away from `x * y`. -/
private theorem isLocalization_away_mul_of_associated {P R S T : Type*} [CommRing P] [CommRing R]
    [CommRing S] [CommRing T] [Algebra P R] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] {x y : P} {s : S} [IsLocalization.Away (algebraMap P R x) S]
    [IsLocalization.Away s T] (h : Associated s (algebraMap R S (algebraMap P R y))) :
    IsLocalization.Away (algebraMap P R (x * y)) T := by
  have : IsLocalization.Away (algebraMap R S (algebraMap P R y)) T :=
    (IsLocalization.Away.iff_of_associated h).mp inferInstance
  rw [map_mul]
  exact IsLocalization.Away.mul' S T _ _

/-- If the image of `x` in `S` is a unit, so is its image in any `S`-algebra `T`. -/
private theorem isUnit_algebraMap_of_isScalarTower {R S : Type*} (T : Type*) [CommRing R]
    [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    {x : R} (hx : IsUnit (algebraMap R S x)) : IsUnit (algebraMap R T x) := by
  rw [IsScalarTower.algebraMap_apply R S T]
  exact hx.map _

variable {A B' : Type u} [CommRing A] [CommRing B'] [Algebra A B'] [Algebra.Syntomic A B']
  [IsNoetherianRing A] [Algebra.QuasiFinite A B'] [IsNoetherianRing B']
  {N : ℕ} (h g : MvPolynomial (Fin N) A) (f : Fin N → MvPolynomial (Fin N) A)
  [Algebra (localizedCompleteIntersection A N h f) B']
  [IsScalarTower A (localizedCompleteIntersection A N h f) B']
  [IsLocalization.Away (algebraMap (MvPolynomial (Fin N) A)
    (localizedCompleteIntersection A N h f) g) B']

omit [Algebra.QuasiFinite A B'] [IsNoetherianRing B'] in
/-- **Raising the degree bound of a classification.** A classification by `univChart N d k`
and the classification by `univChart N D k_D`, `d ≤ D`, through the truncation of coefficients,
give the same Tate map. -/
theorem tateOf_classificationOf_eq_trunc {d D : ℕ} [NeZero d] (hdD : d ≤ D)
    (k : MvPolynomial (Fin N) (univBase.{u} N d))
    [Algebra.QuasiFinite (univBase.{u} N d) (univChart N d k)]
    (φ : univBase.{u} N d →+* A) (hf : ∀ i, MvPolynomial.map φ (univPoly N d i) = f i)
    (hk : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B'
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φ k))))
    (kD : MvPolynomial (Fin N) (univBase.{u} N D))
    [Algebra.QuasiFinite (univBase.{u} N D) (univChart N D kD)]
    (hfD : ∀ i, MvPolynomial.map (φ.comp (univTrunc N (d := d) (D := D))) (univPoly N D i) = f i)
    (hkD : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B'
      (algebraMap (MvPolynomial (Fin N) A) _
        (MvPolynomial.map (φ.comp (univTrunc N (d := d) (D := D))) kD))))
    (G : FiniteOpenFactorization.{u, u, u} A B') :
    tateOf k φ.toAlgebra (classificationAlgebra k φ h f hf B' hk)
        (classificationOf k φ h f hf g B' hk) G =
      tateOf kD (φ.comp (univTrunc N (d := d) (D := D))).toAlgebra
        (classificationAlgebra kD _ h f hfD B' hkD)
        (classificationOf kD _ h f hfD g B' hkD) G := by
  classical
  set kt : MvPolynomial (Fin N) (univBase.{u} N d) :=
    MvPolynomial.map (univTrunc N (d := d) (D := D)) kD with hkt
  have hmapkt : MvPolynomial.map φ kt = MvPolynomial.map (φ.comp (univTrunc N)) kD := by
    rw [hkt, MvPolynomial.map_map]
  have hkE : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B'
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φ (k * kt)))) := by
    rw [map_mul, map_mul, map_mul, hmapkt]
    exact hk.mul hkD
  have hZqf : Algebra.QuasiFinite (univBase.{u} N d) (univChart N d (k * kt)) := by
    let iA := (lciAwayHom k kt (univPoly N d)).toRingHom.toAlgebra
    have := isLocalization_lciAwayHom k kt (univPoly N d)
    have : @IsScalarTower (univBase.{u} N d) (univChart N d k) (univChart N d (k * kt))
        Algebra.toSMul iA.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun c ↦ ((lciAwayHom k kt (univPoly N d)).commutes c).symm
    exact Algebra.QuasiFinite.of_isLocalization (Submonoid.powers (lciMk k (univPoly N d) kt))
  have hZnice := isNiceChart_univChart N d (k * kt)
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin N) (univBase.{u} N d))
      (univChart N d (k * kt)) 1) (univChart N d (k * kt)) := by
    rw [map_one]
    exact IsLocalization.away_of_isUnit_of_bijective _ isUnit_one
      ⟨fun _ _ h ↦ h, fun x ↦ ⟨x, rfl⟩⟩
  have hkkt := isUnit_lciMk (k * kt) (univPoly.{u} N d)
  rw [map_mul] at hkkt
  have hfF₁ : ∀ i, MvPolynomial.map (RingHom.id (univBase.{u} N d)) (univPoly N d i) =
      univPoly N d i := fun i ↦ MvPolynomial.map_id _
  have hkF₁ : IsUnit (algebraMap (univChart N d (k * kt)) (univChart N d (k * kt))
      (algebraMap (MvPolynomial (Fin N) (univBase.{u} N d)) _
        (MvPolynomial.map (RingHom.id _) k))) := by
    rw [MvPolynomial.map_id]
    exact isUnit_of_mul_isUnit_left hkkt
  have hfF₂ := map_univTrunc_univPoly.{u} N hdD
  have hkF₂ : IsUnit (algebraMap (univChart N d (k * kt)) (univChart N d (k * kt))
      (algebraMap (MvPolynomial (Fin N) (univBase.{u} N d)) _
        (MvPolynomial.map (univTrunc N (d := d) (D := D)) kD))) :=
    isUnit_of_mul_isUnit_right hkkt
  let instEA : Algebra (univBase.{u} N d) A := φ.toAlgebra
  let instEC : Algebra (univChart N d (k * kt)) B' :=
    classificationAlgebra (k * kt) φ h f hf B' hkE
  have hE₁ := fun c ↦ classificationAlgebra_algebraMap_base (k * kt) φ h f hf B' hkE c
  have hE₂ := fun i ↦ classificationAlgebra_lciMk_X (k * kt) φ h f hf B' hkE i
  refine tateOf_eq_of_isNiceChart hZnice (classificationOf (k * kt) φ h f hf g B' hkE) k kD
    (RingHom.id _).toAlgebra
    (classificationAlgebra k (RingHom.id _) (k * kt) (univPoly N d) hfF₁ _ hkF₁)
    (classificationOf k (RingHom.id _) (k * kt) (univPoly N d) hfF₁ 1 _ hkF₁)
    (univTrunc N (d := d) (D := D)).toAlgebra
    (classificationAlgebra kD (univTrunc N) (k * kt) (univPoly N d) hfF₂ _ hkF₂)
    (classificationOf kD (univTrunc N) (k * kt) (univPoly N d) hfF₂ 1 _ hkF₂)
    _ _ (fun _ ↦ rfl) (fun x ↦ ?_) _ _ _ (fun _ ↦ rfl) (fun x ↦ ?_) _ G
  · refine (eq_classificationAlgebra k φ h f hf B' hk
      ((algebraMap (univChart N d (k * kt)) B').comp
        (@algebraMap _ _ _ _ (classificationAlgebra k (RingHom.id _) (k * kt) (univPoly N d)
          hfF₁ _ hkF₁))) (fun c ↦ ?_) (fun i ↦ ?_) x).symm
    · rw [RingHom.comp_apply, classificationAlgebra_algebraMap_base]
      exact hE₁ c
    · rw [RingHom.comp_apply, classificationAlgebra_lciMk_X]
      exact hE₂ i
  · refine (eq_classificationAlgebra kD _ h f hfD B' hkD
      ((algebraMap (univChart N d (k * kt)) B').comp
        (@algebraMap _ _ _ _ (classificationAlgebra kD (univTrunc N) (k * kt) (univPoly N d)
          hfF₂ _ hkF₂))) (fun c ↦ ?_) (fun i ↦ ?_) x).symm
    · rw [RingHom.comp_apply, classificationAlgebra_algebraMap_base]
      exact hE₁ _
    · rw [RingHom.comp_apply, classificationAlgebra_lciMk_X]
      exact hE₂ i

omit [IsNoetherianRing B'] in
/-- **Invariance of the Tate map of a presentation.** Two classifications of the same
presentation `B' = (A[x, 1/h]/(f))_g` give the same Tate map. -/
theorem tateOf_classificationOf_invariant
    [Algebra.QuasiFinite A (localizedCompleteIntersection A N h f)]
    {d : ℕ} [NeZero d] (k : MvPolynomial (Fin N) (univBase.{u} N d))
    [Algebra.QuasiFinite (univBase.{u} N d) (univChart N d k)]
    (φ : univBase.{u} N d →+* A) (hf : ∀ i, MvPolynomial.map φ (univPoly N d i) = f i)
    (hk : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B'
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φ k))))
    {d' : ℕ} [NeZero d'] (k' : MvPolynomial (Fin N) (univBase.{u} N d'))
    [Algebra.QuasiFinite (univBase.{u} N d') (univChart N d' k')]
    (φ' : univBase.{u} N d' →+* A) (hf' : ∀ i, MvPolynomial.map φ' (univPoly N d' i) = f i)
    (hk' : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B'
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φ' k'))))
    (G : FiniteOpenFactorization.{u, u, u} A B') :
    tateOf k φ.toAlgebra (classificationAlgebra k φ h f hf B' hk)
        (classificationOf k φ h f hf g B' hk) G =
      tateOf k' φ'.toAlgebra (classificationAlgebra k' φ' h f hf' B' hk')
        (classificationOf k' φ' h f hf' g B' hk') G := by
  classical
  refine tateOf_eq_of_local k k' _ _ _ _ _ _ G fun q hq ↦ ?_
  set p := q.comap (algebraMap (localizedCompleteIntersection A N h f) B')
  have : p.IsPrime := Ideal.comap_isPrime _ _
  set D := max d d'
  have : NeZero D := ⟨by have := NeZero.ne d; omega⟩
  set φD := φ.comp (univTrunc N (d := d) (D := D))
  have hφD : ∀ i, MvPolynomial.map φD (univPoly N D i) = f i := fun i ↦ by
    rw [← MvPolynomial.map_map, map_univTrunc_univPoly N (le_max_left _ _), hf]
  have hφ' : φ'.comp (univTrunc N (d := d') (D := D)) = φD := univBase_ringHom_ext fun i ↦ by
    rw [← MvPolynomial.map_map, map_univTrunc_univPoly N (le_max_right _ _), hf', hφD]
  have hφD' : ∀ i, MvPolynomial.map (φ'.comp (univTrunc N (d := d') (D := D)))
      (univPoly N D i) = f i := fun i ↦ by rw [hφ', hφD]
  obtain ⟨kD, hkDqf, hkDp⟩ := exists_classification_of_map h f p φD hφD
  set b := algebraMap (localizedCompleteIntersection A N h f) B'
    (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φD kD))
  refine ⟨b, fun hb ↦ hkDp (Ideal.mem_comap.mpr hb), fun D₁' D₂' G' ↦ ?_⟩
  set Loc := Localization.Away b
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin N) A)
      (localizedCompleteIntersection A N h f) (g * MvPolynomial.map φD kD)) Loc :=
    isLocalization_away_mul_of_associated (s := b) (Associated.refl _)
  have hkL := isUnit_algebraMap_of_isScalarTower Loc hk
  have hkL' := isUnit_algebraMap_of_isScalarTower Loc hk'
  have hkDL : IsUnit (algebraMap (localizedCompleteIntersection A N h f) Loc
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φD kD))) := by
    rw [IsScalarTower.algebraMap_apply _ B' Loc]
    exact IsLocalization.Away.algebraMap_isUnit b
  have hkDL' : IsUnit (algebraMap (localizedCompleteIntersection A N h f) Loc
      (algebraMap (MvPolynomial (Fin N) A) _
        (MvPolynomial.map (φ'.comp (univTrunc N (d := d') (D := D))) kD))) := by
    rw [hφ']
    exact hkDL
  have hchart : ∀ {n' e : ℕ} (k₀ : MvPolynomial (Fin N) (univBase.{u} N e))
      (φ₀ : univBase.{u} N e →+* A)
      (hf₀ : ∀ i, MvPolynomial.map φ₀ (univPoly N e i) = f i)
      (hk₀ : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B'
        (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φ₀ k₀))))
      (hk₀L : IsUnit (algebraMap (localizedCompleteIntersection A N h f) Loc
        (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φ₀ k₀)))) (x : univChart N e k₀),
      @algebraMap _ _ _ _ (awayChartAlgebra (classificationAlgebra k₀ φ₀ h f hf₀ B' hk₀) b) x =
        @algebraMap _ _ _ _ (classificationAlgebra k₀ φ₀ h f hf₀ Loc hk₀L) x := by
    intro _ e k₀ φ₀ hf₀ hk₀ hk₀L x
    refine eq_classificationAlgebra k₀ φ₀ h f hf₀ Loc hk₀L _ (fun c ↦ ?_) (fun i ↦ ?_) x
    · change algebraMap B' Loc (@algebraMap _ _ _ _ (classificationAlgebra k₀ φ₀ h f hf₀ B' hk₀)
        (algebraMap _ _ c)) = _
      rw [classificationAlgebra_algebraMap_base, ← IsScalarTower.algebraMap_apply]
    · change algebraMap B' Loc (@algebraMap _ _ _ _ (classificationAlgebra k₀ φ₀ h f hf₀ B' hk₀)
        (lciMk k₀ _ (X i))) = _
      rw [classificationAlgebra_lciMk_X, ← IsScalarTower.algebraMap_apply]
  calc tateOf k φ.toAlgebra (awayChartAlgebra (classificationAlgebra k φ h f hf B' hk) b) D₁' G'
      = tateOf k φ.toAlgebra (classificationAlgebra k φ h f hf Loc hkL)
          (classificationOf k φ h f hf (g * MvPolynomial.map φD kD) Loc hkL) G' :=
        tateOf_congr _ _ _ _ _ (fun _ ↦ rfl) (hchart (n' := 0) k φ hf hk hkL) _ _ G'
    _ = tateOf kD φD.toAlgebra (classificationAlgebra kD φD h f hφD Loc hkDL)
          (classificationOf kD φD h f hφD (g * MvPolynomial.map φD kD) Loc hkDL) G' :=
        tateOf_classificationOf_eq_trunc h _ f (le_max_left _ _) k φ hf hkL kD hφD hkDL G'
    _ = tateOf kD (φ'.comp (univTrunc N (d := d') (D := D))).toAlgebra
          (classificationAlgebra kD _ h f hφD' Loc hkDL')
          (classificationOf kD _ h f hφD' (g * MvPolynomial.map φD kD) Loc hkDL') G' := by
        refine tateOf_congr _ _ _ _ _ (fun x ↦ by rw [hφ']) (fun x ↦ ?_) _ _ G'
        refine eq_classificationAlgebra kD _ h f hφD' Loc hkDL'
          (@algebraMap _ _ _ _ (classificationAlgebra kD φD h f hφD Loc hkDL)) (fun c ↦ ?_)
          (fun i ↦ classificationAlgebra_lciMk_X kD φD h f hφD Loc hkDL i) x
        rw [classificationAlgebra_algebraMap_base, hφ']
    _ = tateOf k' φ'.toAlgebra (classificationAlgebra k' φ' h f hf' Loc hkL')
          (classificationOf k' φ' h f hf' (g * MvPolynomial.map φD kD) Loc hkL') G' :=
        (tateOf_classificationOf_eq_trunc h _ f (le_max_right _ _) k' φ' hf' hkL' kD hφD'
          hkDL' G').symm
    _ = tateOf k' φ'.toAlgebra (awayChartAlgebra (classificationAlgebra k' φ' h f hf' B' hk') b)
          D₂' G' :=
        (tateOf_congr _ _ _ _ _ (fun _ ↦ rfl) (hchart (n' := 0) k' φ' hf' hk' hkL') _ _ G').symm

end Truncation

end Stacks.TateMap

namespace Stacks.TateMap

section Assoc

/-- Every element of a localization of `A[x, 1/h]/(f)` away from a polynomial is associated to
the image of the class of a polynomial. -/
theorem exists_associated_lciMk {A B : Type u} [CommRing A] [CommRing B] {N : ℕ}
    {h : MvPolynomial (Fin N) A} (g : MvPolynomial (Fin N) A)
    {f : Fin N → MvPolynomial (Fin N) A} [Algebra (localizedCompleteIntersection A N h f) B]
    [IsLocalization.Away (algebraMap (MvPolynomial (Fin N) A)
      (localizedCompleteIntersection A N h f) g) B] (z : B) :
    ∃ p : MvPolynomial (Fin N) A,
      Associated z (algebraMap (localizedCompleteIntersection A N h f) B (lciMk h f p)) := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (algebraMap (MvPolynomial (Fin N) A)
    (localizedCompleteIntersection A N h f) g) z
  obtain ⟨p, j, hp⟩ := exists_mul_pow_eq_lciMk h f a
  refine ⟨p, ?_⟩
  have hu1 : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B
      (algebraMap (MvPolynomial (Fin N) A) _ g) ^ n) :=
    (IsLocalization.Away.algebraMap_isUnit _).pow n
  have hu2 : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B (lciMk h f h) ^ j) :=
    ((isUnit_lciMk h f).map _).pow j
  rw [← hp, map_mul, ← ha, mul_assoc, map_pow]
  exact associated_mul_unit_right _ _ (hu1.mul hu2)

end Assoc

end Stacks.TateMap

namespace Stacks.TateMap

section AwayChart

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {N : ℕ}
  (h : MvPolynomial (Fin N) A) (f : Fin N → MvPolynomial (Fin N) A)
  [Algebra (localizedCompleteIntersection A N h f) B]
  [IsScalarTower A (localizedCompleteIntersection A N h f) B]

/-- The chart map of a classification of `B`, followed by `B → B_b`, is the chart map of the
classification of `B_b`. -/
theorem awayChartAlgebra_classificationAlgebra (b : B) {e : ℕ}
    (k₀ : MvPolynomial (Fin N) (univBase.{u} N e)) (φ₀ : univBase.{u} N e →+* A)
    (hf₀ : ∀ i, MvPolynomial.map φ₀ (univPoly N e i) = f i)
    (hk₀ : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φ₀ k₀))))
    (hk₀L : IsUnit (algebraMap (localizedCompleteIntersection A N h f) (Localization.Away b)
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φ₀ k₀))))
    (x : univChart N e k₀) :
    @algebraMap _ _ _ _ (awayChartAlgebra (classificationAlgebra k₀ φ₀ h f hf₀ B hk₀) b) x =
      @algebraMap _ _ _ _ (classificationAlgebra k₀ φ₀ h f hf₀ (Localization.Away b) hk₀L) x := by
  refine eq_classificationAlgebra k₀ φ₀ h f hf₀ (Localization.Away b) hk₀L _ (fun c ↦ ?_)
    (fun i ↦ ?_) x
  · change algebraMap B (Localization.Away b)
      (@algebraMap _ _ _ _ (classificationAlgebra k₀ φ₀ h f hf₀ B hk₀) (algebraMap _ _ c)) = _
    rw [classificationAlgebra_algebraMap_base, ← IsScalarTower.algebraMap_apply]
  · change algebraMap B (Localization.Away b)
      (@algebraMap _ _ _ _ (classificationAlgebra k₀ φ₀ h f hf₀ B hk₀) (lciMk k₀ _ (X i))) = _
    rw [classificationAlgebra_lciMk_X, ← IsScalarTower.algebraMap_apply]

end AwayChart

section Transfer

/-- Over a Noetherian ring `S`, the ring `S[x, 1/h]/(f)` is Noetherian. -/
instance lci_isNoetherianRing {S : Type u} [CommRing S] [IsNoetherianRing S] {N : ℕ}
    (h : MvPolynomial (Fin N) S) (f : Fin N → MvPolynomial (Fin N) S) :
    IsNoetherianRing (localizedCompleteIntersection S N h f) :=
  haveI := finitePresentation_localizedCompleteIntersection S N h f
  Algebra.FiniteType.isNoetherianRing S _

/-- A quasi-finite `S`-algebra `S[x, 1/h]/(f)` is flat over `S`. -/
instance lci_flat {S : Type u} [CommRing S] {N : ℕ}
    (h : MvPolynomial (Fin N) S) (f : Fin N → MvPolynomial (Fin N) S)
    [Algebra.QuasiFinite S (localizedCompleteIntersection S N h f)] :
    Module.Flat S (localizedCompleteIntersection S N h f) :=
  flat_localizedCompleteIntersection S N h f

/-- A quasi-finite `S`-algebra `S[x, 1/h]/(f)` is syntomic over `S`. -/
instance lci_syntomic {S : Type u} [CommRing S] {N : ℕ}
    (h : MvPolynomial (Fin N) S) (f : Fin N → MvPolynomial (Fin N) S)
    [Algebra.QuasiFinite S (localizedCompleteIntersection S N h f)] :
    Algebra.Syntomic S (localizedCompleteIntersection S N h f) :=
  syntomic_of_algEquiv_localizedCompleteIntersection AlgEquiv.refl

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.Syntomic A B]
  [IsNoetherianRing A] [Algebra.QuasiFinite A B] [IsNoetherianRing B]

omit [IsNoetherianRing B] in
/-- **Transfer along a nice family.** Let `Z = S[x, 1/h₀]/(f₀)` be a nice family over a
Noetherian ring `S`, with a second presentation `θ : Z ≅ S[y, 1/h₁]/(f₁)`. Let `ε : S → A` carry
the two presentations of `Z` to two presentations of `B`, compatibly with the variables. Then
classifications of the two presentations of `B` give the same Tate map. -/
theorem tateOf_transfer {S : Type u} [CommRing S] [IsNoetherianRing S]
    {Na Nb : ℕ} (h₀ : MvPolynomial (Fin Na) S) (f₀ : Fin Na → MvPolynomial (Fin Na) S)
    (h₁ : MvPolynomial (Fin Nb) S) (f₁ : Fin Nb → MvPolynomial (Fin Nb) S)
    [Algebra.QuasiFinite S (localizedCompleteIntersection S Na h₀ f₀)]
    (hZ : IsNiceChart S (localizedCompleteIntersection S Na h₀ f₀))
    (θ : localizedCompleteIntersection S Na h₀ f₀ ≃ₐ[S] localizedCompleteIntersection S Nb h₁ f₁)
    (ε : S →+* A)
    (ha ga : MvPolynomial (Fin Na) A) (fa : Fin Na → MvPolynomial (Fin Na) A)
    [Algebra (localizedCompleteIntersection A Na ha fa) B]
    [IsScalarTower A (localizedCompleteIntersection A Na ha fa) B]
    [IsLocalization.Away (algebraMap (MvPolynomial (Fin Na) A)
      (localizedCompleteIntersection A Na ha fa) ga) B]
    [Algebra.QuasiFinite A (localizedCompleteIntersection A Na ha fa)]
    (hb gb : MvPolynomial (Fin Nb) A) (fb : Fin Nb → MvPolynomial (Fin Nb) A)
    [Algebra (localizedCompleteIntersection A Nb hb fb) B]
    [IsScalarTower A (localizedCompleteIntersection A Nb hb fb) B]
    [IsLocalization.Away (algebraMap (MvPolynomial (Fin Nb) A)
      (localizedCompleteIntersection A Nb hb fb) gb) B]
    [Algebra.QuasiFinite A (localizedCompleteIntersection A Nb hb fb)]
    (hfa : ∀ i, MvPolynomial.map ε (f₀ i) = fa i) (hfb : ∀ j, MvPolynomial.map ε (f₁ j) = fb j)
    (hka : IsUnit (algebraMap (localizedCompleteIntersection A Na ha fa) B
      (algebraMap (MvPolynomial (Fin Na) A) _ (MvPolynomial.map ε h₀))))
    (hθ : ∀ j, @algebraMap _ _ _ _ (classificationAlgebra h₀ ε ha fa hfa B hka)
      (θ.symm (lciMk h₁ f₁ (X j))) =
        algebraMap (localizedCompleteIntersection A Nb hb fb) B (lciMk hb fb (X j)))
    {d : ℕ} [NeZero d] (k : MvPolynomial (Fin Na) (univBase.{u} Na d))
    [Algebra.QuasiFinite (univBase.{u} Na d) (univChart Na d k)]
    (φ : univBase.{u} Na d →+* A) (hf : ∀ i, MvPolynomial.map φ (univPoly Na d i) = fa i)
    (hk : IsUnit (algebraMap (localizedCompleteIntersection A Na ha fa) B
      (algebraMap (MvPolynomial (Fin Na) A) _ (MvPolynomial.map φ k))))
    {d' : ℕ} [NeZero d'] (k' : MvPolynomial (Fin Nb) (univBase.{u} Nb d'))
    [Algebra.QuasiFinite (univBase.{u} Nb d') (univChart Nb d' k')]
    (φ' : univBase.{u} Nb d' →+* A) (hf' : ∀ j, MvPolynomial.map φ' (univPoly Nb d' j) = fb j)
    (hk' : IsUnit (algebraMap (localizedCompleteIntersection A Nb hb fb) B
      (algebraMap (MvPolynomial (Fin Nb) A) _ (MvPolynomial.map φ' k'))))
    (G : FiniteOpenFactorization.{u, u, u} A B) :
    tateOf k φ.toAlgebra (classificationAlgebra k φ ha fa hf B hk)
        (classificationOf k φ ha fa hf ga B hk) G =
      tateOf k' φ'.toAlgebra (classificationAlgebra k' φ' hb fb hf' B hk')
        (classificationOf k' φ' hb fb hf' gb B hk') G := by
  classical
  set Z := localizedCompleteIntersection S Na h₀ f₀
  set Z₁ := localizedCompleteIntersection S Nb h₁ f₁
  have : Algebra.QuasiFinite S Z₁ := (Algebra.QuasiFinite.iff_of_algEquiv θ).mp inferInstance
  set σ := @algebraMap _ _ _ _ (classificationAlgebra h₀ ε ha fa hfa B hka)
  refine tateOf_eq_of_local k k' _ _ _ _ _ _ G fun q hq ↦ ?_
  set z := q.comap σ
  have : z.IsPrime := Ideal.comap_isPrime _ _
  set z₁ := z.comap (θ.symm : Z₁ →+* Z)
  have : z₁.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨d₀, _, k₀, φ₀, hf₀, hqf₀, hz₀⟩ := exists_classification h₀ f₀ z
  obtain ⟨d₁, _, k₁, φ₁, hf₁, hqf₁, hz₁⟩ := exists_classification h₁ f₁ z₁
  have : Algebra.FinitePresentation S Z :=
    finitePresentation_localizedCompleteIntersection S Na h₀ f₀
  set w₀ : Z := lciMk h₀ f₀ (MvPolynomial.map φ₀ k₀)
  set w₁ : Z := θ.symm (lciMk h₁ f₁ (MvPolynomial.map φ₁ k₁))
  have hzh : lciMk h₀ f₀ h₀ ∉ z := fun hm ↦ Ideal.IsPrime.ne_top ‹_›
    (Ideal.eq_top_of_isUnit_mem _ hm (isUnit_lciMk h₀ f₀))
  have hW : w₀ * w₁ ∉ z := fun hm ↦ (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hz₀
    (fun h ↦ hz₁ (Ideal.mem_comap.mpr h))
  obtain ⟨pt, j, hpt⟩ := exists_mul_pow_eq_lciMk h₀ f₀ (w₀ * w₁)
  have hptz : lciMk h₀ f₀ pt ∉ z := by
    rw [← hpt]
    exact fun hm ↦ (Ideal.IsPrime.mem_or_mem ‹_› hm).elim hW
      (fun h ↦ hzh (Ideal.IsPrime.mem_of_pow_mem ‹_› _ h))
  set Z' := localizedCompleteIntersection S Na (h₀ * pt) f₀
  let iZZ' : Algebra Z Z' := (lciAwayHom h₀ pt f₀).toRingHom.toAlgebra
  have := isLocalization_lciAwayHom h₀ pt f₀
  have : @IsScalarTower S Z Z' Algebra.toSMul iZZ'.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((lciAwayHom h₀ pt f₀).commutes c).symm
  have : Algebra.QuasiFinite S Z' :=
    Algebra.QuasiFinite.of_isLocalization (Submonoid.powers (lciMk h₀ f₀ pt))
  have hZ'nice : IsNiceChart S Z' := hZ.of_isLocalizationAway (lciMk h₀ f₀ pt)
  have hptu : IsUnit (algebraMap Z Z' (lciMk h₀ f₀ pt)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hWu : IsUnit (algebraMap Z Z' (w₀ * w₁)) := by
    rw [← hpt, map_mul] at hptu
    exact isUnit_of_mul_isUnit_left hptu
  rw [map_mul] at hWu
  have hw₀u := isUnit_of_mul_isUnit_left hWu
  have hw₁u := isUnit_of_mul_isUnit_right hWu
  have hσ : ∀ p : MvPolynomial (Fin Na) S, σ (lciMk h₀ f₀ p) =
      algebraMap (localizedCompleteIntersection A Na ha fa) B
        (lciMk ha fa (MvPolynomial.map ε p)) := fun p ↦
    classificationAlgebra_algebraMap h₀ ε ha fa hfa B hka p
  set bB := σ (lciMk h₀ f₀ pt) with hbB
  have hbq : bB ∉ q := fun hm ↦ hptz (Ideal.mem_comap.mpr hm)
  refine ⟨bB, hbq, fun D₁' D₂' G' ↦ ?_⟩
  set Loc := Localization.Away bB
  have hLa : IsLocalization.Away (algebraMap (MvPolynomial (Fin Na) A)
      (localizedCompleteIntersection A Na ha fa) (ga * MvPolynomial.map ε pt)) Loc :=
    isLocalization_away_mul_of_associated (s := bB) (Associated.of_eq (hσ pt))
  obtain ⟨pb, hpb⟩ := exists_associated_lciMk gb bB (h := hb) (f := fb)
  have hLb : IsLocalization.Away (algebraMap (MvPolynomial (Fin Nb) A)
      (localizedCompleteIntersection A Nb hb fb) (gb * pb)) Loc :=
    isLocalization_away_mul_of_associated hpb
  have hbLu : IsUnit (algebraMap B Loc bB) := IsLocalization.Away.algebraMap_isUnit bB
  have hkE : IsUnit (algebraMap (localizedCompleteIntersection A Na ha fa) Loc
      (algebraMap (MvPolynomial (Fin Na) A) _ (MvPolynomial.map ε (h₀ * pt)))) := by
    rw [map_mul, map_mul, map_mul, IsScalarTower.algebraMap_apply _ B Loc,
      IsScalarTower.algebraMap_apply _ B Loc (algebraMap (MvPolynomial (Fin Na) A) _ _)]
    have e : algebraMap (localizedCompleteIntersection A Na ha fa) B
        (algebraMap (MvPolynomial (Fin Na) A) _ (MvPolynomial.map ε pt)) = bB := (hσ pt).symm
    rw [e]
    exact (hka.map _).mul hbLu
  let iEA : Algebra S A := ε.toAlgebra
  let iEC : Algebra Z' Loc := classificationAlgebra (h₀ * pt) ε ha fa hfa Loc hkE
  set E := classificationOf (h₀ * pt) ε ha fa hfa (ga * MvPolynomial.map ε pt) Loc hkE
  have hk₀Z : IsUnit (algebraMap Z Z' (algebraMap (MvPolynomial (Fin Na) S) Z
      (MvPolynomial.map φ₀ k₀))) := hw₀u
  let iZ₁Z' : Algebra Z₁ Z' :=
    ((lciAwayHom h₀ pt f₀).toRingHom.comp θ.symm.toRingEquiv.toRingHom).toAlgebra
  have : @IsScalarTower S Z₁ Z' Algebra.toSMul iZ₁Z'.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change _ = lciAwayHom h₀ pt f₀ (θ.symm (algebraMap S Z₁ c))
      rw [AlgEquiv.commutes, AlgHom.commutes]
  obtain ⟨pt₁, j₁, hpt₁⟩ := exists_mul_pow_eq_lciMk h₁ f₁ (θ (lciMk h₀ f₀ pt))
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin Nb) S) Z₁ pt₁) Z' := by
    have H := IsLocalization.isLocalization_of_base_ringEquiv
      (Submonoid.powers (lciMk h₀ f₀ pt)) Z' θ.toRingEquiv
    rw [Submonoid.map_powers] at H
    have : IsLocalization.Away (θ (lciMk h₀ f₀ pt)) Z' := H
    have hassoc : Associated (θ (lciMk h₀ f₀ pt)) (lciMk h₁ f₁ pt₁) := by
      rw [← hpt₁]
      exact associated_mul_unit_right _ _ ((isUnit_lciMk h₁ f₁).pow j₁)
    exact (IsLocalization.Away.iff_of_associated hassoc).mp inferInstance
  have hk₁Z : IsUnit (algebraMap Z₁ Z' (algebraMap (MvPolynomial (Fin Nb) S) Z₁
      (MvPolynomial.map φ₁ k₁))) := hw₁u
  have hE₁ := fun c ↦ classificationAlgebra_algebraMap_base (h₀ * pt) ε ha fa hfa Loc hkE c
  have hE₂ := fun i ↦ classificationAlgebra_lciMk_X (h₀ * pt) ε ha fa hfa Loc hkE i
  have K1 : ∀ x : Z, algebraMap Z' Loc (algebraMap Z Z' x) = algebraMap B Loc (σ x) := by
    have := lci_ringHom_ext (ψ := (algebraMap Z' Loc).comp (algebraMap Z Z'))
      (ψ' := (algebraMap B Loc).comp σ) (fun c ↦ ?_) (fun i ↦ ?_)
    · exact fun x ↦ congrArg (· x) this
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply S Z Z', hE₁,
        classificationAlgebra_algebraMap_base, ← IsScalarTower.algebraMap_apply A B Loc]
    · change algebraMap Z' Loc (lciAwayHom h₀ pt f₀ _) = _
      rw [RingHom.comp_apply, lciAwayHom_lciMk, hE₂, classificationAlgebra_lciMk_X,
        ← IsScalarTower.algebraMap_apply]
  have K2 : ∀ p : MvPolynomial (Fin Nb) S,
      algebraMap (localizedCompleteIntersection A Nb hb fb) Loc
        (lciMk hb fb (MvPolynomial.map ε p)) = algebraMap B Loc (σ (θ.symm (lciMk h₁ f₁ p))) := by
    have := MvPolynomial.ringHom_ext
      (f := ((algebraMap (localizedCompleteIntersection A Nb hb fb) Loc).comp
        (lciMk hb fb : MvPolynomial (Fin Nb) A →+* _)).comp (MvPolynomial.map ε))
      (g := ((algebraMap B Loc).comp σ).comp
        ((θ.symm : Z₁ →+* Z).comp (lciMk h₁ f₁ : MvPolynomial (Fin Nb) S →+* Z₁)))
      (fun c ↦ ?_) (fun j ↦ ?_)
    · exact fun p ↦ congrArg (· p) this
    · simp only [RingHom.comp_apply, MvPolynomial.map_C, RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, ← MvPolynomial.algebraMap_eq,
        AlgHom.commutes, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply,
        classificationAlgebra_algebraMap_base, ← IsScalarTower.algebraMap_apply]
    · simp only [RingHom.comp_apply, MvPolynomial.map_X, RingHom.coe_coe]
      rw [hθ, ← IsScalarTower.algebraMap_apply]
  have hf₀' : ∀ i, MvPolynomial.map (ε.comp φ₀) (univPoly Na d₀ i) = fa i := fun i ↦ by
    rw [← MvPolynomial.map_map, hf₀, hfa]
  have hf₁' : ∀ j, MvPolynomial.map (ε.comp φ₁) (univPoly Nb d₁ j) = fb j := fun j ↦ by
    rw [← MvPolynomial.map_map, hf₁, hfb]
  have hk₀L : IsUnit (algebraMap (localizedCompleteIntersection A Na ha fa) Loc
      (algebraMap (MvPolynomial (Fin Na) A) _ (MvPolynomial.map (ε.comp φ₀) k₀))) := by
    rw [← MvPolynomial.map_map, ← classificationAlgebra_algebraMap (h₀ * pt) ε ha fa hfa Loc hkE,
      ← lciMk_apply, ← lciAwayHom_lciMk h₀ pt f₀]
    exact hw₀u.map _
  have hk₁L : IsUnit (algebraMap (localizedCompleteIntersection A Nb hb fb) Loc
      (algebraMap (MvPolynomial (Fin Nb) A) _ (MvPolynomial.map (ε.comp φ₁) k₁))) := by
    rw [← MvPolynomial.map_map, ← lciMk_apply, K2, ← K1]
    exact hw₁u.map _
  have hC₀ : ∀ x, @algebraMap _ _ _ _
      (classificationAlgebra k₀ (ε.comp φ₀) ha fa hf₀' Loc hk₀L) x =
      algebraMap Z' Loc (@algebraMap _ _ _ _
        (classificationAlgebra k₀ φ₀ h₀ f₀ hf₀ Z' hk₀Z) x) := by
    refine fun x ↦ (eq_classificationAlgebra k₀ (ε.comp φ₀) ha fa hf₀' Loc hk₀L
      ((algebraMap Z' Loc).comp (@algebraMap _ _ _ _
        (classificationAlgebra k₀ φ₀ h₀ f₀ hf₀ Z' hk₀Z))) (fun c ↦ ?_) (fun i ↦ ?_) x).symm
    · rw [RingHom.comp_apply, classificationAlgebra_algebraMap_base, hE₁]
      rfl
    · rw [RingHom.comp_apply, classificationAlgebra_lciMk_X]
      change algebraMap Z' Loc (lciAwayHom h₀ pt f₀ _) = _
      rw [lciAwayHom_lciMk, hE₂]
  have hC₁ : ∀ x, @algebraMap _ _ _ _
      (classificationAlgebra k₁ (ε.comp φ₁) hb fb hf₁' Loc hk₁L) x =
      algebraMap Z' Loc (@algebraMap _ _ _ _
        (classificationAlgebra k₁ φ₁ h₁ f₁ hf₁ Z' hk₁Z) x) := by
    refine fun x ↦ (eq_classificationAlgebra k₁ (ε.comp φ₁) hb fb hf₁' Loc hk₁L
      ((algebraMap Z' Loc).comp (@algebraMap _ _ _ _
        (classificationAlgebra k₁ φ₁ h₁ f₁ hf₁ Z' hk₁Z))) (fun c ↦ ?_) (fun j ↦ ?_) x).symm
    · rw [RingHom.comp_apply, classificationAlgebra_algebraMap_base, hE₁]
      rfl
    · rw [RingHom.comp_apply, classificationAlgebra_lciMk_X]
      change algebraMap Z' Loc (lciAwayHom h₀ pt f₀ (θ.symm _)) = _
      have := K2 (X j)
      rw [MvPolynomial.map_X] at this
      rw [this, ← K1]
      rfl
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin Na) S) Z pt) Z' :=
    isLocalization_lciAwayHom h₀ pt f₀
  have heng := tateOf_eq_of_isNiceChart hZ'nice E k₀ k₁ φ₀.toAlgebra
    (classificationAlgebra k₀ φ₀ h₀ f₀ hf₀ Z' hk₀Z)
    (classificationOf k₀ φ₀ h₀ f₀ hf₀ pt Z' hk₀Z) φ₁.toAlgebra
    (classificationAlgebra k₁ φ₁ h₁ f₁ hf₁ Z' hk₁Z)
    (classificationOf k₁ φ₁ h₁ f₁ hf₁ pt₁ Z' hk₁Z)
    (ε.comp φ₀).toAlgebra (classificationAlgebra k₀ (ε.comp φ₀) ha fa hf₀' Loc hk₀L)
    (fun _ ↦ rfl) hC₀
    (classificationOf k₀ (ε.comp φ₀) ha fa hf₀' (ga * MvPolynomial.map ε pt) Loc hk₀L)
    (ε.comp φ₁).toAlgebra (classificationAlgebra k₁ (ε.comp φ₁) hb fb hf₁' Loc hk₁L)
    (fun _ ↦ rfl) hC₁ (classificationOf k₁ (ε.comp φ₁) hb fb hf₁' (gb * pb) Loc hk₁L) G'
  have hkL := isUnit_algebraMap_of_isScalarTower Loc hk
  have hkL' := isUnit_algebraMap_of_isScalarTower Loc hk'
  calc tateOf k φ.toAlgebra (awayChartAlgebra (classificationAlgebra k φ ha fa hf B hk) bB) D₁' G'
      = tateOf k φ.toAlgebra (classificationAlgebra k φ ha fa hf Loc hkL)
          (classificationOf k φ ha fa hf (ga * MvPolynomial.map ε pt) Loc hkL) G' :=
        tateOf_congr _ _ _ _ _ (fun _ ↦ rfl)
          (awayChartAlgebra_classificationAlgebra ha fa bB k φ hf hk hkL) _ _ G'
    _ = tateOf k₀ (ε.comp φ₀).toAlgebra (classificationAlgebra k₀ (ε.comp φ₀) ha fa hf₀' Loc hk₀L)
          (classificationOf k₀ (ε.comp φ₀) ha fa hf₀' (ga * MvPolynomial.map ε pt) Loc hk₀L) G' :=
        tateOf_classificationOf_invariant ha _ fa k φ hf hkL k₀ (ε.comp φ₀) hf₀' hk₀L G'
    _ = tateOf k₁ (ε.comp φ₁).toAlgebra (classificationAlgebra k₁ (ε.comp φ₁) hb fb hf₁' Loc hk₁L)
          (classificationOf k₁ (ε.comp φ₁) hb fb hf₁' (gb * pb) Loc hk₁L) G' := heng
    _ = tateOf k' φ'.toAlgebra (classificationAlgebra k' φ' hb fb hf' Loc hkL')
          (classificationOf k' φ' hb fb hf' (gb * pb) Loc hkL') G' :=
        tateOf_classificationOf_invariant hb _ fb k₁ (ε.comp φ₁) hf₁' hk₁L k' φ' hf' hkL' G'
    _ = tateOf k' φ'.toAlgebra (awayChartAlgebra (classificationAlgebra k' φ' hb fb hf' B hk') bB)
          D₂' G' :=
        (tateOf_congr _ _ _ _ _ (fun _ ↦ rfl)
          (awayChartAlgebra_classificationAlgebra hb fb bB k' φ' hf' hk' hkL') _ _ G').symm

end Transfer

end Stacks.TateMap

namespace Stacks.TateMap

section PresRel

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]

/-- Two presentations `B = (A[x, 1/ha]/(fa))_{ga} = (A[y, 1/hb]/(fb))_{gb}` are *Tate-related* if,
on every algebra `B'` over `B` which is a localization of both presentations, any classification
of the first and any classification of the second give the same Tate map. -/
def PresRel {Na Nb : ℕ} (ha : MvPolynomial (Fin Na) A) (fa : Fin Na → MvPolynomial (Fin Na) A)
    (hb : MvPolynomial (Fin Nb) A) (fb : Fin Nb → MvPolynomial (Fin Nb) A)
    [Algebra (localizedCompleteIntersection A Na ha fa) B]
    [Algebra (localizedCompleteIntersection A Nb hb fb) B] : Prop :=
  ∀ (b₀ : B) (B' : Type u) [CommRing B'] [Algebra B B'] [IsLocalization.Away b₀ B'] [Algebra A B']
    [IsScalarTower A B B'] [Algebra.Syntomic A B'] [Algebra.QuasiFinite A B'] [IsNoetherianRing B']
    [Algebra (localizedCompleteIntersection A Na ha fa) B']
    [IsScalarTower (localizedCompleteIntersection A Na ha fa) B B']
    [IsScalarTower A (localizedCompleteIntersection A Na ha fa) B']
    (ga : MvPolynomial (Fin Na) A)
    [IsLocalization.Away (algebraMap (MvPolynomial (Fin Na) A)
      (localizedCompleteIntersection A Na ha fa) ga) B']
    [Algebra (localizedCompleteIntersection A Nb hb fb) B']
    [IsScalarTower (localizedCompleteIntersection A Nb hb fb) B B']
    [IsScalarTower A (localizedCompleteIntersection A Nb hb fb) B']
    (gb : MvPolynomial (Fin Nb) A)
    [IsLocalization.Away (algebraMap (MvPolynomial (Fin Nb) A)
      (localizedCompleteIntersection A Nb hb fb) gb) B']
    {d : ℕ} [NeZero d] (k : MvPolynomial (Fin Na) (univBase.{u} Na d))
    [Algebra.QuasiFinite (univBase.{u} Na d) (univChart Na d k)]
    (φ : univBase.{u} Na d →+* A) (hf : ∀ i, MvPolynomial.map φ (univPoly Na d i) = fa i)
    (hk : IsUnit (algebraMap (localizedCompleteIntersection A Na ha fa) B'
      (algebraMap (MvPolynomial (Fin Na) A) _ (MvPolynomial.map φ k))))
    {d' : ℕ} [NeZero d'] (k' : MvPolynomial (Fin Nb) (univBase.{u} Nb d'))
    [Algebra.QuasiFinite (univBase.{u} Nb d') (univChart Nb d' k')]
    (φ' : univBase.{u} Nb d' →+* A) (hf' : ∀ j, MvPolynomial.map φ' (univPoly Nb d' j) = fb j)
    (hk' : IsUnit (algebraMap (localizedCompleteIntersection A Nb hb fb) B'
      (algebraMap (MvPolynomial (Fin Nb) A) _ (MvPolynomial.map φ' k'))))
    (G : FiniteOpenFactorization.{u, u, u} A B'),
    tateOf k φ.toAlgebra (classificationAlgebra k φ ha fa hf B' hk)
        (classificationOf k φ ha fa hf ga B' hk) G =
      tateOf k' φ'.toAlgebra (classificationAlgebra k' φ' hb fb hf' B' hk')
        (classificationOf k' φ' hb fb hf' gb B' hk') G

omit [IsNoetherianRing A] in
/-- The chart map of a classification of `B`, followed by `B → B'`, is the chart map of the
classification of `B'`. -/
theorem classificationAlgebra_comp_eq {S : Type u} [CommRing S] {N : ℕ}
    (h₀ : MvPolynomial (Fin N) S) (f₀ : Fin N → MvPolynomial (Fin N) S) (ε : S →+* A)
    (h : MvPolynomial (Fin N) A) (f : Fin N → MvPolynomial (Fin N) A)
    (hf : ∀ i, MvPolynomial.map ε (f₀ i) = f i)
    [Algebra (localizedCompleteIntersection A N h f) B]
    [IsScalarTower A (localizedCompleteIntersection A N h f) B]
    (B' : Type u) [CommRing B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A B B']
    [Algebra (localizedCompleteIntersection A N h f) B']
    [IsScalarTower (localizedCompleteIntersection A N h f) B B']
    [IsScalarTower A (localizedCompleteIntersection A N h f) B']
    (hk : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map ε h₀))))
    (hk' : IsUnit (algebraMap (localizedCompleteIntersection A N h f) B'
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map ε h₀))))
    (x : localizedCompleteIntersection S N h₀ f₀) :
    @algebraMap _ _ _ _ (classificationAlgebra h₀ ε h f hf B' hk') x =
      algebraMap B B' (@algebraMap _ _ _ _ (classificationAlgebra h₀ ε h f hf B hk) x) := by
  refine (eq_classificationAlgebra h₀ ε h f hf B' hk'
    ((algebraMap B B').comp (@algebraMap _ _ _ _ (classificationAlgebra h₀ ε h f hf B hk)))
    (fun c ↦ ?_) (fun i ↦ ?_) x).symm
  · rw [RingHom.comp_apply, classificationAlgebra_algebraMap_base,
      ← IsScalarTower.algebraMap_apply]
  · rw [RingHom.comp_apply, classificationAlgebra_lciMk_X, ← IsScalarTower.algebraMap_apply]

/-- **Transfer gives Tate-related presentations.** -/
theorem presRel_of_transfer [Algebra.Syntomic A B] [Algebra.QuasiFinite A B]
    {S : Type u} [CommRing S] [IsNoetherianRing S]
    {Na Nb : ℕ} (h₀ : MvPolynomial (Fin Na) S) (f₀ : Fin Na → MvPolynomial (Fin Na) S)
    (h₁ : MvPolynomial (Fin Nb) S) (f₁ : Fin Nb → MvPolynomial (Fin Nb) S)
    [Algebra.QuasiFinite S (localizedCompleteIntersection S Na h₀ f₀)]
    (hZ : IsNiceChart S (localizedCompleteIntersection S Na h₀ f₀))
    (θ : localizedCompleteIntersection S Na h₀ f₀ ≃ₐ[S] localizedCompleteIntersection S Nb h₁ f₁)
    (ε : S →+* A)
    (ha : MvPolynomial (Fin Na) A) (fa : Fin Na → MvPolynomial (Fin Na) A)
    [Algebra (localizedCompleteIntersection A Na ha fa) B]
    [IsScalarTower A (localizedCompleteIntersection A Na ha fa) B]
    [Algebra.QuasiFinite A (localizedCompleteIntersection A Na ha fa)]
    (hb : MvPolynomial (Fin Nb) A) (fb : Fin Nb → MvPolynomial (Fin Nb) A)
    [Algebra (localizedCompleteIntersection A Nb hb fb) B]
    [IsScalarTower A (localizedCompleteIntersection A Nb hb fb) B]
    [Algebra.QuasiFinite A (localizedCompleteIntersection A Nb hb fb)]
    (hfa : ∀ i, MvPolynomial.map ε (f₀ i) = fa i) (hfb : ∀ j, MvPolynomial.map ε (f₁ j) = fb j)
    (hka : IsUnit (algebraMap (localizedCompleteIntersection A Na ha fa) B
      (algebraMap (MvPolynomial (Fin Na) A) _ (MvPolynomial.map ε h₀))))
    (hθ : ∀ j, @algebraMap _ _ _ _ (classificationAlgebra h₀ ε ha fa hfa B hka)
      (θ.symm (lciMk h₁ f₁ (X j))) =
        algebraMap (localizedCompleteIntersection A Nb hb fb) B (lciMk hb fb (X j))) :
    PresRel (B := B) ha fa hb fb := by
  intro b₀ B' _ _ _ _ _ _ _ _ _ _ _ ga _ _ _ _ gb _ d _ k _ φ hf hk d' _ k' _ φ' hf' hk' G
  have hka' : IsUnit (algebraMap (localizedCompleteIntersection A Na ha fa) B'
      (algebraMap (MvPolynomial (Fin Na) A) _ (MvPolynomial.map ε h₀))) := by
    rw [IsScalarTower.algebraMap_apply _ B B']
    exact hka.map _
  refine tateOf_transfer h₀ f₀ h₁ f₁ hZ θ ε ha ga fa hb gb fb hfa hfb hka' (fun j ↦ ?_)
    k φ hf hk k' φ' hf' hk' G
  rw [classificationAlgebra_comp_eq h₀ f₀ ε ha fa hfa B' hka hka', hθ,
    ← IsScalarTower.algebraMap_apply]

/-- Every element of a localization `B'` of `B` away from `b₀` is associated to the image of an
element of `B`. -/
theorem exists_associated_algebraMap {B' : Type*} [CommRing B'] [Algebra B B'] (b₀ : B)
    [IsLocalization.Away b₀ B'] (z : B') : ∃ x : B, Associated z (algebraMap B B' x) := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj b₀ z
  exact ⟨a, ha ▸ associated_mul_unit_right _ _ ((IsLocalization.Away.algebraMap_isUnit b₀).pow n)⟩

/-- **Transitivity of Tate-relatedness**, through a presentation which `B` is a localization of. -/
theorem PresRel.trans [Algebra.Syntomic A B] [Algebra.QuasiFinite A B]
    {Na Nb Nc : ℕ} {ha : MvPolynomial (Fin Na) A} {fa : Fin Na → MvPolynomial (Fin Na) A}
    {hb : MvPolynomial (Fin Nb) A} {fb : Fin Nb → MvPolynomial (Fin Nb) A}
    {hc : MvPolynomial (Fin Nc) A} {fc : Fin Nc → MvPolynomial (Fin Nc) A}
    [Algebra (localizedCompleteIntersection A Na ha fa) B]
    [Algebra (localizedCompleteIntersection A Nb hb fb) B]
    [IsScalarTower A (localizedCompleteIntersection A Nb hb fb) B]
    [Algebra (localizedCompleteIntersection A Nc hc fc) B]
    [Algebra.QuasiFinite A (localizedCompleteIntersection A Nb hb fb)]
    (gb₀ : MvPolynomial (Fin Nb) A) [IsLocalization.Away (algebraMap (MvPolynomial (Fin Nb) A)
      (localizedCompleteIntersection A Nb hb fb) gb₀) B]
    (hab : PresRel (B := B) ha fa hb fb) (hbc : PresRel (B := B) hb fb hc fc) :
    PresRel (B := B) ha fa hc fc := by
  intro b₀ B' _ _ _ _ _ _ _ _ _ _ _ ga _ _ _ _ gc _ d _ k _ φ hf hk d' _ k' _ φ' hf' hk' G
  let : Algebra (localizedCompleteIntersection A Nb hb fb) B' :=
    ((algebraMap B B').comp (algebraMap (localizedCompleteIntersection A Nb hb fb) B)).toAlgebra
  have : IsScalarTower (localizedCompleteIntersection A Nb hb fb) B B' :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (localizedCompleteIntersection A Nb hb fb) B' :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = algebraMap B B' (algebraMap _ B (algebraMap A _ a))
      rw [← IsScalarTower.algebraMap_apply A (localizedCompleteIntersection A Nb hb fb) B,
        ← IsScalarTower.algebraMap_apply A B B']
  refine tateOf_eq_of_local k k' _ _ _ _ _ _ G fun q hq ↦ ?_
  set p := q.comap (algebraMap (localizedCompleteIntersection A Nb hb fb) B')
  have : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨d₁, _, k₁, φ₁, hf₁, hqf₁, hk₁p⟩ := exists_classification hb fb p
  set b' := algebraMap (localizedCompleteIntersection A Nb hb fb) B'
    (algebraMap (MvPolynomial (Fin Nb) A) _ (MvPolynomial.map φ₁ k₁))
  refine ⟨b', fun hm ↦ hk₁p (Ideal.mem_comap.mpr hm), fun D₁' D₂' G' ↦ ?_⟩
  set Loc := Localization.Away b'
  obtain ⟨x, hx⟩ := exists_associated_algebraMap b₀ b'
  have : IsLocalization.Away (algebraMap B B' x) Loc :=
    (IsLocalization.Away.iff_of_associated hx).mp inferInstance
  have hLB : IsLocalization.Away (b₀ * x) Loc := IsLocalization.Away.mul' B' Loc _ _
  have : IsScalarTower A B Loc := inferInstance
  have : IsScalarTower (localizedCompleteIntersection A Na ha fa) B Loc := inferInstance
  have : IsScalarTower A (localizedCompleteIntersection A Na ha fa) Loc := inferInstance
  have : IsScalarTower (localizedCompleteIntersection A Nb hb fb) B Loc := inferInstance
  have : IsScalarTower A (localizedCompleteIntersection A Nb hb fb) Loc := inferInstance
  have : IsScalarTower (localizedCompleteIntersection A Nc hc fc) B Loc := inferInstance
  have : IsScalarTower A (localizedCompleteIntersection A Nc hc fc) Loc := inferInstance
  obtain ⟨ra, hra⟩ := exists_associated_lciMk ga b' (h := ha) (f := fa)
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin Na) A)
      (localizedCompleteIntersection A Na ha fa) (ga * ra)) Loc :=
    isLocalization_away_mul_of_associated hra
  obtain ⟨rc, hrc⟩ := exists_associated_lciMk gc b' (h := hc) (f := fc)
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin Nc) A)
      (localizedCompleteIntersection A Nc hc fc) (gc * rc)) Loc :=
    isLocalization_away_mul_of_associated hrc
  obtain ⟨rb, hrb⟩ := exists_associated_lciMk gb₀ (b₀ * x) (h := hb) (f := fb)
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin Nb) A)
      (localizedCompleteIntersection A Nb hb fb) (gb₀ * rb)) Loc :=
    isLocalization_away_mul_of_associated hrb
  have hkL := isUnit_algebraMap_of_isScalarTower Loc hk
  have hkL' := isUnit_algebraMap_of_isScalarTower Loc hk'
  have hk₁L : IsUnit (algebraMap (localizedCompleteIntersection A Nb hb fb) Loc
      (algebraMap (MvPolynomial (Fin Nb) A) _ (MvPolynomial.map φ₁ k₁))) := by
    rw [IsScalarTower.algebraMap_apply _ B' Loc]
    exact IsLocalization.Away.algebraMap_isUnit b'
  calc tateOf k φ.toAlgebra (awayChartAlgebra (classificationAlgebra k φ ha fa hf B' hk) b') D₁' G'
      = tateOf k φ.toAlgebra (classificationAlgebra k φ ha fa hf Loc hkL)
          (classificationOf k φ ha fa hf (ga * ra) Loc hkL) G' :=
        tateOf_congr _ _ _ _ _ (fun _ ↦ rfl)
          (awayChartAlgebra_classificationAlgebra ha fa b' k φ hf hk hkL) _ _ G'
    _ = tateOf k₁ φ₁.toAlgebra (classificationAlgebra k₁ φ₁ hb fb hf₁ Loc hk₁L)
          (classificationOf k₁ φ₁ hb fb hf₁ (gb₀ * rb) Loc hk₁L) G' :=
        hab (b₀ * x) Loc (ga * ra) (gb₀ * rb) k φ hf hkL k₁ φ₁ hf₁ hk₁L G'
    _ = tateOf k' φ'.toAlgebra (classificationAlgebra k' φ' hc fc hf' Loc hkL')
          (classificationOf k' φ' hc fc hf' (gc * rc) Loc hkL') G' :=
        hbc (b₀ * x) Loc (gb₀ * rb) (gc * rc) k₁ φ₁ hf₁ hk₁L k' φ' hf' hkL' G'
    _ = tateOf k' φ'.toAlgebra (awayChartAlgebra (classificationAlgebra k' φ' hc fc hf' B' hk') b')
          D₂' G' :=
        (tateOf_congr _ _ _ _ _ (fun _ ↦ rfl)
          (awayChartAlgebra_classificationAlgebra hc fc b' k' φ' hf' hk' hkL') _ _ G').symm

/-- **Changing only the localization element.** Two presentations with equal relations and the
same images of the variables are Tate-related. -/
theorem presRel_of_eqRelations [Algebra.Syntomic A B] [Algebra.QuasiFinite A B]
    {N : ℕ} {ha hb : MvPolynomial (Fin N) A} {f fb : Fin N → MvPolynomial (Fin N) A}
    [Algebra (localizedCompleteIntersection A N ha f) B]
    [IsScalarTower A (localizedCompleteIntersection A N ha f) B]
    [Algebra (localizedCompleteIntersection A N hb fb) B]
    [IsScalarTower A (localizedCompleteIntersection A N hb fb) B]
    [Algebra.QuasiFinite A (localizedCompleteIntersection A N ha f)]
    [Algebra.QuasiFinite A (localizedCompleteIntersection A N hb fb)]
    (hff : ∀ i, f i = fb i)
    (hX : ∀ i, algebraMap (localizedCompleteIntersection A N ha f) B (lciMk ha f (X i)) =
      algebraMap (localizedCompleteIntersection A N hb fb) B (lciMk hb fb (X i))) :
    PresRel (B := B) ha f hb fb := by
  intro b₀ B' _ _ _ _ _ _ _ _ _ _ _ ga _ _ _ _ gb _ d _ k _ φ hf hk d' _ k' _ φ' hf' hk' G
  have hP : ∀ p : MvPolynomial (Fin N) A,
      algebraMap (localizedCompleteIntersection A N ha f) B' (lciMk ha f p) =
        algebraMap (localizedCompleteIntersection A N hb fb) B' (lciMk hb fb p) := by
    have := MvPolynomial.ringHom_ext
      (f := (algebraMap (localizedCompleteIntersection A N ha f) B').comp
        (lciMk ha f).toRingHom)
      (g := (algebraMap (localizedCompleteIntersection A N hb fb) B').comp
        (lciMk hb fb).toRingHom) (fun c ↦ ?_) (fun i ↦ ?_)
    · exact fun p ↦ congrArg (· p) this
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [IsScalarTower.algebraMap_apply _ B B', hX, ← IsScalarTower.algebraMap_apply]
  refine tateOf_eq_of_local k k' _ _ _ _ _ _ G fun q hq ↦ ?_
  set p := q.comap (algebraMap (localizedCompleteIntersection A N ha f) B')
  have : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨D, _, kD, φD, hfD, hqfD, hkDp⟩ := exists_classification ha f p
  set b' := algebraMap (localizedCompleteIntersection A N ha f) B'
    (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φD kD))
  refine ⟨b', fun hm ↦ hkDp (Ideal.mem_comap.mpr hm), fun D₁' D₂' G' ↦ ?_⟩
  set Loc := Localization.Away b'
  obtain ⟨ra, hra⟩ := exists_associated_lciMk ga b' (h := ha) (f := f)
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin N) A)
      (localizedCompleteIntersection A N ha f) (ga * ra)) Loc :=
    isLocalization_away_mul_of_associated hra
  obtain ⟨rb, hrb⟩ := exists_associated_lciMk gb b' (h := hb) (f := fb)
  have : IsLocalization.Away (algebraMap (MvPolynomial (Fin N) A)
      (localizedCompleteIntersection A N hb fb) (gb * rb)) Loc :=
    isLocalization_away_mul_of_associated hrb
  have hkL := isUnit_algebraMap_of_isScalarTower Loc hk
  have hkL' := isUnit_algebraMap_of_isScalarTower Loc hk'
  have hkDa : IsUnit (algebraMap (localizedCompleteIntersection A N ha f) Loc
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φD kD))) := by
    rw [IsScalarTower.algebraMap_apply _ B' Loc]
    exact IsLocalization.Away.algebraMap_isUnit b'
  have hfDb : ∀ i, MvPolynomial.map φD (univPoly N D i) = fb i := fun i ↦ (hfD i).trans (hff i)
  have hkDb : IsUnit (algebraMap (localizedCompleteIntersection A N hb fb) Loc
      (algebraMap (MvPolynomial (Fin N) A) _ (MvPolynomial.map φD kD))) := by
    rw [IsScalarTower.algebraMap_apply _ B' Loc, ← lciMk_apply, ← hP]
    exact IsLocalization.Away.algebraMap_isUnit b'
  calc tateOf k φ.toAlgebra (awayChartAlgebra (classificationAlgebra k φ ha f hf B' hk) b') D₁' G'
      = tateOf k φ.toAlgebra (classificationAlgebra k φ ha f hf Loc hkL)
          (classificationOf k φ ha f hf (ga * ra) Loc hkL) G' :=
        tateOf_congr _ _ _ _ _ (fun _ ↦ rfl)
          (awayChartAlgebra_classificationAlgebra ha f b' k φ hf hk hkL) _ _ G'
    _ = tateOf kD φD.toAlgebra (classificationAlgebra kD φD ha f hfD Loc hkDa)
          (classificationOf kD φD ha f hfD (ga * ra) Loc hkDa) G' :=
        tateOf_classificationOf_invariant ha _ f k φ hf hkL kD φD hfD hkDa G'
    _ = tateOf kD φD.toAlgebra (classificationAlgebra kD φD hb fb hfDb Loc hkDb)
          (classificationOf kD φD hb fb hfDb (gb * rb) Loc hkDb) G' := by
        refine tateOf_congr _ _ _ _ _ (fun _ ↦ rfl) (fun x ↦ ?_) _ _ G'
        refine eq_classificationAlgebra kD φD hb fb hfDb Loc hkDb _
          (fun c ↦ classificationAlgebra_algebraMap_base kD φD ha f hfD Loc hkDa c)
          (fun i ↦ ?_) x
        rw [classificationAlgebra_lciMk_X, IsScalarTower.algebraMap_apply _ B' Loc, hP,
          ← IsScalarTower.algebraMap_apply]
    _ = tateOf k' φ'.toAlgebra (classificationAlgebra k' φ' hb fb hf' Loc hkL')
          (classificationOf k' φ' hb fb hf' (gb * rb) Loc hkL') G' :=
        tateOf_classificationOf_invariant hb _ fb kD φD hfDb hkDb k' φ' hf' hkL' G'
    _ = tateOf k' φ'.toAlgebra (awayChartAlgebra (classificationAlgebra k' φ' hb fb hf' B' hk') b')
          D₂' G' :=
        (tateOf_congr _ _ _ _ _ (fun _ ↦ rfl)
          (awayChartAlgebra_classificationAlgebra hb fb b' k' φ' hf' hk' hkL') _ _ G').symm

/-- Tate-relatedness is symmetric. -/
theorem PresRel.symm {Na Nb : ℕ} {ha : MvPolynomial (Fin Na) A}
    {fa : Fin Na → MvPolynomial (Fin Na) A} {hb : MvPolynomial (Fin Nb) A}
    {fb : Fin Nb → MvPolynomial (Fin Nb) A}
    [Algebra (localizedCompleteIntersection A Na ha fa) B]
    [Algebra (localizedCompleteIntersection A Nb hb fb) B]
    (hab : PresRel (B := B) ha fa hb fb) : PresRel (B := B) hb fb ha fa := by
  intro b₀ B' _ _ _ _ _ _ _ _ _ _ _ gb _ _ _ _ ga _ d _ k _ φ hf hk d' _ k' _ φ' hf' hk' G
  exact (hab b₀ B' ga gb k' φ' hf' hk' k φ hf hk G).symm

end PresRel

end Stacks.TateMap
