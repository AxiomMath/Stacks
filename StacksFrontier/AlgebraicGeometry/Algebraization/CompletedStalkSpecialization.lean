module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalk
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.RingTheory.AdicCompletion.AlgEquivOfQuotientEquiv
public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.AdicCompletion.DvrValuedPoints
public import StacksFrontier.RingTheory.AdicCompletion.MapOfPowLe
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow

/-!
# Completed local rings along a specialization

Let `X` be a scheme, let `ℐ` be a quasi-coherent sheaf of ideals on `X` and let `y ⤳ y'` be a
specialization of points of `X`. The specialization map of stalks
`TopCat.Presheaf.stalkSpecializes` carries `ℐ_{y'}` onto `ℐ_y`, so it induces a ring map

  `𝒪_{X,y'}^∧ ⟶ 𝒪_{X,y}^∧`

of the adically completed local rings of `Stacks.Algebraization.completedLocalRing`. This file
constructs that map and identifies its target.

The algebra behind the identification is the following. Let `R` be a ring, `J ⊆ R` an ideal and
`𝔭 ⊇ J` a prime. The composite `R^∧ → R/J → R/𝔭` of `AdicCompletion.evalOneₐ` with the
comparison of quotients is a surjection onto a domain, so its kernel is a prime `𝔮` of `R^∧`
with

* `𝔮 ∩ R = 𝔭`, and `𝔮 ⊇ JR^∧`;
* `R^∧/𝔮 = R/𝔭`, hence `dim(R^∧/𝔮) = dim(R/𝔭)`.

Moreover, for `J` finitely generated, the `J`-adic completion of the localization `R_𝔭` is the
`J`-adic completion of the localization `(R^∧)_𝔮`. Level by level both are the localization of
`R/Jⁿ` at the image of the complement of `𝔭`: for `R_𝔭` by definition, and for `(R^∧)_𝔮` because
the identification `R^∧/JⁿR^∧ = R/Jⁿ` carries the complement of `𝔮` onto the complement of `𝔭`.

Geometrically `AlgebraicGeometry.Scheme.fromSpecStalk` identifies the points specializing to `y'`
with the primes of `𝒪_{X,y'}`; if `𝔭` is the prime corresponding to `y`, then `𝒪_{X,y}` is the
localization of `𝒪_{X,y'}` at `𝔭`, so `𝒪_{X,y}^∧` is the adic completion of the localization of
`𝒪_{X,y'}^∧` at `𝔮`.

## Main definitions

* `Stacks.Algebraization.adicResidue` — the surjection `R^∧ → R/𝔭`.
* `Stacks.Algebraization.adicPrimeOver` — the prime `𝔮` of `R^∧` above `𝔭`.
* `Stacks.Algebraization.quotientAdicPrimeOverEquiv` — the identification `R^∧/𝔮 = R/𝔭`.
* `Stacks.Algebraization.quotPowAdicEquiv` — the identification `R^∧/JⁿR^∧ = R/Jⁿ`.
* `Stacks.Algebraization.levelRingEquiv`, `Stacks.Algebraization.levelRingEquivPow` and
  `Stacks.Algebraization.levelAlgEquivPow` — the level-`n` comparison of the two localizations.
* `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv` — **the comparison itself**: the
  `J`-adic completion of `R_𝔭` as the `J`-adic completion of `(R^∧)_𝔮`, as `R`-algebras.
* `Stacks.Algebraization.completedLocalRingSpecializes` — the ring map
  `𝒪_{X,y'}^∧ ⟶ 𝒪_{X,y}^∧` induced by a specialization `y ⤳ y'`.
* `Stacks.Algebraization.completedStalkPrime` — the prime `𝔮` of `𝒪_{X,y'}^∧` attached to a
  prime of `𝒪_{X,y'}` containing `ℐ_{y'}`.

## Main results

* `Stacks.Algebraization.comap_adicPrimeOver`, `Stacks.Algebraization.map_le_adicPrimeOver`,
  `Stacks.Algebraization.ringKrullDim_quotient_adicPrimeOver` — the three properties of `𝔮`.
* `Stacks.Algebraization.evalₐ_adicCompletionLocalizationAlgEquiv`,
  `Stacks.Algebraization.eq_adicCompletionLocalizationAlgEquiv_of_evalₐ`,
  `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv_algebraMap` and
  `Stacks.Algebraization.mem_ker_evalₐ_adicCompletionLocalizationAlgEquiv` — the clauses that
  characterize the comparison: its level-`n` reduction, the uniqueness that clause gives, its
  compatibility with the structure maps from `R` and with the adic filtration.
* `Stacks.Algebraization.nonempty_algEquiv_adicCompletion_localization` — **the adic completion
  of `R_𝔭` is the adic completion of `(R^∧)_𝔮`**, the bare existential form of the above.
* `Stacks.Algebraization.completedLocalRingSpecializes_comp_algebraMap` and
  `Stacks.Algebraization.map_completedLocalIdeal_completedLocalRingSpecializes` — the
  specialization map of completions is compatible with the maps from the uncompleted local rings
  and carries `ℐ𝒪_{X,y'}^∧` onto `ℐ𝒪_{X,y}^∧`.
* `Stacks.Algebraization.exists_fromSpecStalk_eq_of_specializes` — a specialization `y ⤳ y'` does
  come from a prime of `𝒪_{X,y'}`.
* `Stacks.Algebraization.ringKrullDim_quotient_completedStalkPrime` —
  `dim(𝒪_{X,y'}^∧/𝔮) = dim(𝒪_{X,y'}/𝔭)`.
* `Stacks.Algebraization.nonempty_algEquiv_completedLocalRing_of_specializes` — **`𝒪_{X,y}^∧` is
  the adic completion of the localization of `𝒪_{X,y'}^∧` at `𝔮`**.

## Implementation notes

The induced map on completions is `adicCompletionMap`, whose compatibility with the structure
maps is reproved here because the available form of that statement is private to its file.

The prime `𝔮` is defined as a kernel rather than as a contraction: the composite
`R^∧ → R/J → R/𝔭` is surjective onto a domain, which makes primality, the identification of the
quotient and the computation of the contraction immediate.

The two localizations are presented abstractly, by `IsLocalization` hypotheses rather than by
`Localization.AtPrime`, and the comparison of the completions is assembled from the level-`n`
comparisons by `adicCompletionAlgEquivOfQuotientEquiv`. The level-`n` comparison is
`IsLocalization.ringEquivOfRingEquiv` along `R^∧/JⁿR^∧ = R/Jⁿ`, which is why the correspondence
of multiplicative sets, `Stacks.Algebraization.map_algebraMapSubmonoid_quotPowAdicEquiv_symm`, is
the substance: an element of `R^∧` outside `𝔮` agrees at every level with an element of `R`
outside `𝔭`, because an element of the completion is congruent modulo `J^{max n 1}R^∧` to an
element of `R`, and that ideal lies both in the level-`n` kernel and in `JR^∧ ⊆ 𝔮`.

Because the two adic ideals are the extensions of one ideal of `R` rather than powers of a
single ideal of the localization, the level-`n` statements are related to the powers of the
extended ideals by `Ideal.map_pow`, and the comparison maps are corrected by
`Ideal.quotEquivOfEq` on both sides.

None of these declarations carries a `stacks` attribute: they are the substrate on which the
local statements of the chapter on algebraic and formal geometry are phrased, not the content of
a tag.

## References

* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the paragraph
  introducing `𝒪_{X,y}^∧`.
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7), the primes of a local
  ring of a scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v

namespace Stacks.Algebraization

/-! ### The map of adic completions induced by a ring homomorphism -/

/-! ### The prime of an adic completion above a prime containing the ideal -/

section Algebra

variable {R : Type u} [CommRing R] (J : Ideal R) {p : Ideal R}

/-- The surjection `R^∧ → R/𝔭` attached to a prime `𝔭` of `R` containing `J`: the evaluation of
the `J`-adic completion at level one followed by the comparison of the two quotients. -/
def adicResidue (hJp : J ≤ p) : AdicCompletion J R →+* (R ⧸ p) :=
  (Ideal.Quotient.factor hJp).comp (AdicCompletion.evalOneₐ J).toRingHom

/-- The composite of the canonical map `R → R^∧` with `adicResidue` is the quotient map
`R → R/𝔭`. -/
theorem adicResidue_comp_algebraMap (hJp : J ≤ p) :
    (adicResidue J hJp).comp (algebraMap R (AdicCompletion J R)) = Ideal.Quotient.mk p := by
  rw [adicResidue, RingHom.comp_assoc, AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk J]
  rfl

/-- The residue map `adicResidue : R^∧ → R/𝔭` is surjective. -/
theorem adicResidue_surjective (hJp : J ≤ p) : Function.Surjective (adicResidue J hJp) :=
  (Ideal.Quotient.factor_surjective hJp).comp (AdicCompletion.evalOneₐ_surjective J)

/-- **The prime of the adic completion above a prime of the ring containing the ideal.** For a
prime `𝔭 ⊇ J` of `R` this is the kernel of the surjection `R^∧ → R/𝔭`. -/
def adicPrimeOver [p.IsPrime] (hJp : J ≤ p) : PrimeSpectrum (AdicCompletion J R) :=
  ⟨RingHom.ker (adicResidue J hJp), RingHom.ker_isPrime _⟩

/-- Membership in `𝔮` is vanishing of the residue. -/
theorem mem_adicPrimeOver_iff [p.IsPrime] (hJp : J ≤ p) (x : AdicCompletion J R) :
    x ∈ (adicPrimeOver J hJp).asIdeal ↔ adicResidue J hJp x = 0 :=
  RingHom.mem_ker

/-- **The contraction of `𝔮` to `R` is `𝔭`.** -/
theorem comap_adicPrimeOver [p.IsPrime] (hJp : J ≤ p) :
    (adicPrimeOver J hJp).asIdeal.comap (algebraMap R (AdicCompletion J R)) = p := by
  have h : (adicPrimeOver J hJp).asIdeal.comap (algebraMap R (AdicCompletion J R)) =
      RingHom.ker ((adicResidue J hJp).comp (algebraMap R (AdicCompletion J R))) := rfl
  rw [h, adicResidue_comp_algebraMap, Ideal.mk_ker]

/-- An element of `R` has image in `𝔮` exactly when it lies in `𝔭`. -/
private theorem algebraMap_mem_adicPrimeOver_iff [p.IsPrime] (hJp : J ≤ p) (a : R) :
    algebraMap R (AdicCompletion J R) a ∈ (adicPrimeOver J hJp).asIdeal ↔ a ∈ p := by
  rw [← Ideal.mem_comap, comap_adicPrimeOver]

/-- **`𝔮` contains the extension `JR^∧` of the adic ideal.** -/
theorem map_le_adicPrimeOver [p.IsPrime] (hJp : J ≤ p) :
    J.map (algebraMap R (AdicCompletion J R)) ≤ (adicPrimeOver J hJp).asIdeal := by
  rwa [Ideal.map_le_iff_le_comap, comap_adicPrimeOver]

/-- **The quotient of the adic completion by `𝔮` is `R/𝔭`.** -/
def quotientAdicPrimeOverEquiv [p.IsPrime] (hJp : J ≤ p) :
    (AdicCompletion J R ⧸ (adicPrimeOver J hJp).asIdeal) ≃+* (R ⧸ p) :=
  RingHom.quotientKerEquivOfSurjective (adicResidue_surjective J hJp)

/-- **The dimension of the quotient of the adic completion by `𝔮`** is the dimension of
`R/𝔭`. -/
theorem ringKrullDim_quotient_adicPrimeOver [p.IsPrime] (hJp : J ≤ p) :
    ringKrullDim (AdicCompletion J R ⧸ (adicPrimeOver J hJp).asIdeal) = ringKrullDim (R ⧸ p) :=
  ringKrullDim_eq_of_ringEquiv (quotientAdicPrimeOverEquiv J hJp)

end Algebra

variable {X : Scheme.{u}}

/-! ### The specialization map between completed local rings -/

/-- The ring map `𝒪_{X,y'}^∧ ⟶ 𝒪_{X,y}^∧` of completed local rings induced by a specialization
`y ⤳ y'`.

The specialization map `TopCat.Presheaf.stalkSpecializes` carries the stalk `ℐ_{y'}` onto the
stalk `ℐ_y` (`Stacks.Chow.idealStalk_eq_map_stalkSpecializes`), so it is a map of rings with
adic ideals and completes. -/
def completedLocalRingSpecializes (I : X.IdealSheafData) {y y' : X} (h : y ⤳ y') :
    completedLocalRing I y' →+* completedLocalRing I y :=
  adicCompletionMap (X.presheaf.stalkSpecializes h).hom (IdealSheafData.stalk I y')
    (IdealSheafData.stalk I y) (Chow.idealStalk_eq_map_stalkSpecializes I h).ge

/-- The specialization map of completed local rings is compatible with the maps from the
uncompleted local rings. -/
theorem completedLocalRingSpecializes_comp_algebraMap (I : X.IdealSheafData) {y y' : X}
    (h : y ⤳ y') :
    (completedLocalRingSpecializes I h).comp
        (algebraMap (X.presheaf.stalk y') (completedLocalRing I y')) =
      (algebraMap (X.presheaf.stalk y) (completedLocalRing I y)).comp
        (X.presheaf.stalkSpecializes h).hom :=
  adicCompletionMap_comp_algebraMap _ _ _ _

/-- The specialization map of completed local rings carries `ℐ𝒪_{X,y'}^∧` onto `ℐ𝒪_{X,y}^∧`. -/
theorem map_completedLocalIdeal_completedLocalRingSpecializes (I : X.IdealSheafData) {y y' : X}
    (h : y ⤳ y') :
    (completedLocalIdeal I y').map (completedLocalRingSpecializes I h) =
      completedLocalIdeal I y := by
  rw [completedLocalIdeal, Ideal.map_map, completedLocalRingSpecializes_comp_algebraMap,
    ← Ideal.map_map, ← Chow.idealStalk_eq_map_stalkSpecializes I h]

/-! ### The prime of the completed local ring attached to a specialization -/

variable (I : X.IdealSheafData) (y' : X) (p : PrimeSpectrum (X.presheaf.stalk y'))

/-- **The prime of the completed local ring `𝒪_{X,y'}^∧` above a prime `𝔭` of `𝒪_{X,y'}`
containing the stalk `ℐ_{y'}`**, that is, above a point of the closed subscheme cut out by `ℐ`
specializing to `y'`. -/
def completedStalkPrime (hp : IdealSheafData.stalk I y' ≤ p.asIdeal) :
    PrimeSpectrum (completedLocalRing I y') :=
  adicPrimeOver (IdealSheafData.stalk I y') hp

/-- The contraction of `𝔮` to the local ring `𝒪_{X,y'}` is `𝔭`. -/
theorem comap_completedStalkPrime (hp : IdealSheafData.stalk I y' ≤ p.asIdeal) :
    (completedStalkPrime I y' p hp).asIdeal.comap
        (algebraMap (X.presheaf.stalk y') (completedLocalRing I y')) = p.asIdeal :=
  comap_adicPrimeOver (IdealSheafData.stalk I y') hp

/-- The prime `𝔮` contains the completed adic ideal `ℐ𝒪_{X,y'}^∧`. -/
theorem completedLocalIdeal_le_completedStalkPrime
    (hp : IdealSheafData.stalk I y' ≤ p.asIdeal) :
    completedLocalIdeal I y' ≤ (completedStalkPrime I y' p hp).asIdeal :=
  map_le_adicPrimeOver (IdealSheafData.stalk I y') hp

/-- **The dimension of the quotient of the completed local ring by `𝔮`** is the dimension of
`𝒪_{X,y'}/𝔭`. -/
theorem ringKrullDim_quotient_completedStalkPrime
    (hp : IdealSheafData.stalk I y' ≤ p.asIdeal) :
    ringKrullDim (completedLocalRing I y' ⧸ (completedStalkPrime I y' p hp).asIdeal) =
      ringKrullDim (X.presheaf.stalk y' ⧸ p.asIdeal) :=
  ringKrullDim_quotient_adicPrimeOver (IdealSheafData.stalk I y') hp

/-- A point specializing to `y'` is the image of a prime of `𝒪_{X,y'}` under
`AlgebraicGeometry.Scheme.fromSpecStalk`. -/
theorem exists_fromSpecStalk_eq_of_specializes {y y' : X} (h : y ⤳ y') :
    ∃ p : PrimeSpectrum (X.presheaf.stalk y'), X.fromSpecStalk y' p = y := by
  change y ∈ Set.range (X.fromSpecStalk y')
  rwa [Scheme.range_fromSpecStalk]


/-! ### The level-`n` quotients of an adic completion -/

section Identification

variable {R : Type u} [CommRing R] (J : Ideal R) {p : Ideal R}

/-- **The level-`n` quotient of an adic completion is the level-`n` quotient of the ring**:
`R^∧/JⁿR^∧ = R/Jⁿ`, the isomorphism induced by `AdicCompletion.evalₐ`. -/
def quotPowAdicEquiv (hJ : J.FG) (n : ℕ) :
    (AdicCompletion J R ⧸ (J ^ n).map (algebraMap R (AdicCompletion J R))) ≃+* (R ⧸ J ^ n) :=
  (Ideal.quotEquivOfEq (AdicCompletion.ker_evalₐ_eq_map_pow J hJ n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (AdicCompletion.surjective_evalₐ J n))

/-- The isomorphism `quotPowAdicEquiv` sends the class of `x ∈ R^∧` to its level-`n` component
in `R/Jⁿ`. -/
theorem quotPowAdicEquiv_mk (hJ : J.FG) (n : ℕ) (x : AdicCompletion J R) :
    quotPowAdicEquiv J hJ n (Ideal.Quotient.mk _ x) = AdicCompletion.evalₐ J n x := by
  simp only [quotPowAdicEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

/-- The inverse of `quotPowAdicEquiv` sends the class of `a ∈ R` modulo `Jⁿ` to the class of its
image in `R^∧`. -/
theorem quotPowAdicEquiv_symm_mk (hJ : J.FG) (n : ℕ) (a : R) :
    (quotPowAdicEquiv J hJ n).symm (Ideal.Quotient.mk (J ^ n) a) =
      Ideal.Quotient.mk _ (algebraMap R (AdicCompletion J R) a) := by
  apply (quotPowAdicEquiv J hJ n).injective
  rw [RingEquiv.apply_symm_apply, quotPowAdicEquiv_mk]
  exact (AdicCompletion.evalₐ_of J n a).symm

/-- An element of the completion outside `𝔮` has, at every level, the same image as an element of
`R` outside `𝔭`.

An element of the completion is congruent to an element `a` of `R` modulo `J^{max n 1}R^∧`; that
ideal is contained in `JⁿR^∧`, which is the kernel at level `n`, and in `JR^∧ ⊆ 𝔮`, so `a` cannot
lie in `𝔭`. -/
theorem exists_notMem_evalₐ_eq_mk (hJ : J.FG) [p.IsPrime] (hJp : J ≤ p) (n : ℕ)
    {x : AdicCompletion J R} (hx : x ∉ (adicPrimeOver J hJp).asIdeal) :
    ∃ a : R, a ∉ p ∧ AdicCompletion.evalₐ J n x = Ideal.Quotient.mk (J ^ n) a := by
  obtain ⟨a, ha⟩ := AdicCompletion.exists_sub_mem_map_pow J hJ (max n 1) x
  have hmax0 : max n 1 ≠ 0 := by omega
  refine ⟨a, ?_, ?_⟩
  · intro hap
    refine hx ?_
    have h1 : x - algebraMap R (AdicCompletion J R) a ∈ (adicPrimeOver J hJp).asIdeal :=
      map_le_adicPrimeOver J hJp
        (Ideal.map_mono (Ideal.pow_le_self hmax0) ha)
    simpa using (adicPrimeOver J hJp).asIdeal.add_mem h1
      ((algebraMap_mem_adicPrimeOver_iff J hJp a).2 hap)
  · have hker : x - algebraMap R (AdicCompletion J R) a ∈
        RingHom.ker (AdicCompletion.evalₐ J n).toRingHom := by
      rw [AdicCompletion.ker_evalₐ_eq_map_pow J hJ n]
      exact Ideal.map_mono (Ideal.pow_le_pow_right (le_max_left n 1)) ha
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hker
    exact hker.trans (AdicCompletion.evalₐ_of J n a)

/-- The multiplicative set computing the localization at `𝔭` corresponds, under
`R^∧/JⁿR^∧ = R/Jⁿ`, to the one computing the localization at `𝔮`. -/
theorem map_algebraMapSubmonoid_quotPowAdicEquiv_symm (hJ : J.FG) [p.IsPrime] (hJp : J ≤ p)
    (n : ℕ) :
    Submonoid.map (quotPowAdicEquiv J hJ n).symm.toMonoidHom
        (Algebra.algebraMapSubmonoid (R ⧸ J ^ n) p.primeCompl) =
      Algebra.algebraMapSubmonoid
        (AdicCompletion J R ⧸ (J ^ n).map (algebraMap R (AdicCompletion J R)))
        (adicPrimeOver J hJp).asIdeal.primeCompl := by
  have hmkR : ∀ a : R, algebraMap R (R ⧸ J ^ n) a = Ideal.Quotient.mk (J ^ n) a := fun a => rfl
  have hmkC : ∀ x : AdicCompletion J R,
      algebraMap (AdicCompletion J R)
          (AdicCompletion J R ⧸ (J ^ n).map (algebraMap R (AdicCompletion J R))) x =
        Ideal.Quotient.mk _ x := fun x => rfl
  have hcoe : ∀ w : R ⧸ J ^ n, (quotPowAdicEquiv J hJ n).symm.toMonoidHom w =
      (quotPowAdicEquiv J hJ n).symm w := fun _ => rfl
  ext z
  simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, hcoe, Ideal.primeCompl,
    Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨w, ⟨a, ha, rfl⟩, rfl⟩
    refine ⟨algebraMap R (AdicCompletion J R) a, ?_, ?_⟩
    · exact fun hmem => ha ((algebraMap_mem_adicPrimeOver_iff J hJp a).1 hmem)
    · rw [hmkR a, quotPowAdicEquiv_symm_mk J hJ n a, hmkC]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, hax⟩ := exists_notMem_evalₐ_eq_mk J hJ hJp n hx
    refine ⟨Ideal.Quotient.mk (J ^ n) a, ⟨a, ha, (hmkR a).symm⟩, ?_⟩
    apply (quotPowAdicEquiv J hJ n).injective
    rw [RingEquiv.apply_symm_apply, hmkC, quotPowAdicEquiv_mk, hax]

/-! ### The adic completion of the localization at `𝔭` -/

section Level

variable (hJ : J.FG) [p.IsPrime] (hJp : J ≤ p)
  (Rp : Type v) [CommRing Rp] [Algebra R Rp] [IsLocalization p.primeCompl Rp]
  (Rq : Type v) [CommRing Rq] [Algebra (AdicCompletion J R) Rq] [Algebra R Rq]
  [IsScalarTower R (AdicCompletion J R) Rq]
  [IsLocalization (adicPrimeOver J hJp).asIdeal.primeCompl Rq]

/-- Extending `Jⁿ` to the completion and then to the localization of the completion at `𝔮` is
extending it to that localization directly. -/
theorem map_map_pow_eq_pow_map (n : ℕ) :
    ((J ^ n).map (algebraMap R (AdicCompletion J R))).map
        (algebraMap (AdicCompletion J R) Rq) = (J.map (algebraMap R Rq)) ^ n := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_pow]

/-- The level-`n` comparison of the localization of `R` at `𝔭` with the localization of the
completion at `𝔮`: both are localizations of `R/Jⁿ = R^∧/JⁿR^∧` at corresponding multiplicative
sets. -/
def levelRingEquiv (n : ℕ) :
    (Rp ⧸ (J ^ n).map (algebraMap R Rp)) ≃+*
      (Rq ⧸ ((J ^ n).map (algebraMap R (AdicCompletion J R))).map
        (algebraMap (AdicCompletion J R) Rq)) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Algebra.algebraMapSubmonoid (R ⧸ J ^ n) p.primeCompl) _ _
    (quotPowAdicEquiv J hJ n).symm (map_algebraMapSubmonoid_quotPowAdicEquiv_symm J hJ hJp n)

/-- The level-`n` comparison, written for the powers of the extended ideals. -/
def levelRingEquivPow (n : ℕ) :
    (Rp ⧸ (J.map (algebraMap R Rp)) ^ n) ≃+* (Rq ⧸ (J.map (algebraMap R Rq)) ^ n) :=
  (Ideal.quotEquivOfEq (show (J.map (algebraMap R Rp)) ^ n = (J ^ n).map (algebraMap R Rp) by
      rw [Ideal.map_pow])).trans
    ((levelRingEquiv J hJ hJp Rp Rq n).trans
      (Ideal.quotEquivOfEq (map_map_pow_eq_pow_map J Rq n)))

/-- The level-`n` comparison is a map of `R`-algebras. -/
theorem levelRingEquivPow_algebraMap (n : ℕ) (a : R) :
    levelRingEquivPow J hJ hJp Rp Rq n (algebraMap R (Rp ⧸ (J.map (algebraMap R Rp)) ^ n) a) =
      algebraMap R (Rq ⧸ (J.map (algebraMap R Rq)) ^ n) a := by
  have hp : algebraMap R (Rp ⧸ (J.map (algebraMap R Rp)) ^ n) a =
      Ideal.Quotient.mk _ (algebraMap R Rp a) := rfl
  have hq : algebraMap R (Rq ⧸ (J.map (algebraMap R Rq)) ^ n) a =
      Ideal.Quotient.mk _ (algebraMap R Rq a) := rfl
  have hbase : algebraMap (R ⧸ J ^ n) (Rp ⧸ (J ^ n).map (algebraMap R Rp))
      (Ideal.Quotient.mk (J ^ n) a) = Ideal.Quotient.mk _ (algebraMap R Rp a) := rfl
  have hbase' : algebraMap (AdicCompletion J R ⧸ (J ^ n).map (algebraMap R (AdicCompletion J R)))
      (Rq ⧸ ((J ^ n).map (algebraMap R (AdicCompletion J R))).map
        (algebraMap (AdicCompletion J R) Rq))
      (Ideal.Quotient.mk _ (algebraMap R (AdicCompletion J R) a)) =
      Ideal.Quotient.mk _ (algebraMap (AdicCompletion J R) Rq
        (algebraMap R (AdicCompletion J R) a)) := rfl
  rw [hp, hq, levelRingEquivPow, RingEquiv.trans_apply, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, ← hbase, levelRingEquiv,
    IsLocalization.ringEquivOfRingEquiv_eq, quotPowAdicEquiv_symm_mk, hbase',
    Ideal.quotEquivOfEq_mk, ← IsScalarTower.algebraMap_apply]

/-- The level-`n` comparisons are compatible with the transition maps of the inverse systems. -/
theorem levelRingEquivPow_factorPow {m n : ℕ} (hmn : m ≤ n)
    (x : Rp ⧸ (J.map (algebraMap R Rp)) ^ n) :
    Ideal.Quotient.factorPow (J.map (algebraMap R Rq)) hmn
        (levelRingEquivPow J hJ hJp Rp Rq n x) =
      levelRingEquivPow J hJ hJp Rp Rq m
        (Ideal.Quotient.factorPow (J.map (algebraMap R Rp)) hmn x) := by
  classical
  set c : (Rp ⧸ (J.map (algebraMap R Rp)) ^ n) ≃+* (Rp ⧸ (J ^ n).map (algebraMap R Rp)) :=
    Ideal.quotEquivOfEq ((Ideal.map_pow (algebraMap R Rp) J n).symm)
  set F : (Rp ⧸ (J ^ n).map (algebraMap R Rp)) →+* (Rq ⧸ (J.map (algebraMap R Rq)) ^ m) :=
    ((Ideal.Quotient.factorPow (J.map (algebraMap R Rq)) hmn).comp
        (levelRingEquivPow J hJ hJp Rp Rq n).toRingHom).comp c.symm.toRingHom with hF
  set G : (Rp ⧸ (J ^ n).map (algebraMap R Rp)) →+* (Rq ⧸ (J.map (algebraMap R Rq)) ^ m) :=
    (((levelRingEquivPow J hJ hJp Rp Rq m).toRingHom.comp
        (Ideal.Quotient.factorPow (J.map (algebraMap R Rp)) hmn)).comp
      c.symm.toRingHom) with hG
  have hfactor : ∀ {S : Type v} [CommRing S] [Algebra R S] (a : R) (k l : ℕ) (h : k ≤ l),
      Ideal.Quotient.factorPow (J.map (algebraMap R S)) h
          (algebraMap R (S ⧸ (J.map (algebraMap R S)) ^ l) a) =
        algebraMap R (S ⧸ (J.map (algebraMap R S)) ^ k) a := fun a k l h => rfl
  have hcsymm : ∀ a : R, c.symm (algebraMap R (Rp ⧸ (J ^ n).map (algebraMap R Rp)) a) =
      algebraMap R (Rp ⧸ (J.map (algebraMap R Rp)) ^ n) a := fun _ => rfl
  have key : F = G := by
    refine IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid (R ⧸ J ^ n) p.primeCompl) ?_
    refine RingHom.ext fun w => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective w
    have hw : algebraMap (R ⧸ J ^ n) (Rp ⧸ (J ^ n).map (algebraMap R Rp))
        (Ideal.Quotient.mk (J ^ n) a) = algebraMap R (Rp ⧸ (J ^ n).map (algebraMap R Rp)) a := rfl
    simp only [RingHom.comp_apply, hw, hF, hG, hcsymm, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe]
    rw [levelRingEquivPow_algebraMap, hfactor, hfactor, levelRingEquivPow_algebraMap]
  simpa only [hF, hG, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    c.symm_apply_apply] using DFunLike.congr_fun key (c x)

/-- The level-`n` comparison as an `R`-algebra equivalence. -/
def levelAlgEquivPow (n : ℕ) :
    (Rp ⧸ (J.map (algebraMap R Rp)) ^ n) ≃ₐ[R] (Rq ⧸ (J.map (algebraMap R Rq)) ^ n) :=
  { levelRingEquivPow J hJ hJp Rp Rq n with
    commutes' := levelRingEquivPow_algebraMap J hJ hJp Rp Rq n }

/-- The algebra equivalence `levelAlgEquivPow` acts as the ring equivalence
`levelRingEquivPow`. -/
@[simp]
theorem levelAlgEquivPow_apply (n : ℕ) (x : Rp ⧸ (J.map (algebraMap R Rp)) ^ n) :
    levelAlgEquivPow J hJ hJp Rp Rq n x = levelRingEquivPow J hJ hJp Rp Rq n x :=
  rfl

/-- **The adic completion of the localization at `𝔭` is the adic completion of the localization
of the adic completion at `𝔮`.**

Let `R` be a ring, `J ⊆ R` a finitely generated ideal and `𝔭 ⊇ J` a prime, let `R_𝔭` be the
localization of `R` at `𝔭` and let `𝔮` be the prime `Stacks.Algebraization.adicPrimeOver` of the
`J`-adic completion `R^∧` above `𝔭`. Then the `J`-adic completion of `R_𝔭` is the `J`-adic
completion of the localization `(R^∧)_𝔮`, as `R`-algebras.

Level by level both sides are the localization of `R/Jⁿ` at the image of the complement of `𝔭`:
for the first side by definition, and for the second because `R^∧/JⁿR^∧ = R/Jⁿ` carries the
complement of `𝔮` onto the complement of `𝔭`. This equivalence is assembled from those level-`n`
comparisons, and that is exactly what characterizes it: see
`Stacks.Algebraization.evalₐ_adicCompletionLocalizationAlgEquiv` for the clause and
`Stacks.Algebraization.eq_adicCompletionLocalizationAlgEquiv_of_evalₐ` for the uniqueness it
provides. -/
def adicCompletionLocalizationAlgEquiv :
    AdicCompletion (J.map (algebraMap R Rp)) Rp ≃ₐ[R]
      AdicCompletion (J.map (algebraMap R Rq)) Rq :=
  adicCompletionAlgEquivOfQuotientEquiv _ _ (levelAlgEquivPow J hJ hJp Rp Rq)
    (fun {_ _} hmn x => levelRingEquivPow_factorPow J hJ hJp Rp Rq hmn x)

/-- **The defining clause of `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv`**: its
level-`n` reduction is the level-`n` comparison of the two localizations. -/
theorem evalₐ_adicCompletionLocalizationAlgEquiv (n : ℕ)
    (x : AdicCompletion (J.map (algebraMap R Rp)) Rp) :
    AdicCompletion.evalₐ (J.map (algebraMap R Rq)) n
        (adicCompletionLocalizationAlgEquiv J hJ hJp Rp Rq x) =
      levelRingEquivPow J hJ hJp Rp Rq n
        (AdicCompletion.evalₐ (J.map (algebraMap R Rp)) n x) :=
  AdicCompletion.evalₐ_adicCompletionAlgEquivOfQuotientEquiv _ _ _ _ n x

/-- **The defining clause determines `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv`**:
any map computed by the level-`n` comparisons is that equivalence. -/
theorem eq_adicCompletionLocalizationAlgEquiv_of_evalₐ
    (F : AdicCompletion (J.map (algebraMap R Rp)) Rp →
      AdicCompletion (J.map (algebraMap R Rq)) Rq)
    (hF : ∀ (n : ℕ) (x : AdicCompletion (J.map (algebraMap R Rp)) Rp),
      AdicCompletion.evalₐ (J.map (algebraMap R Rq)) n (F x) =
        levelRingEquivPow J hJ hJp Rp Rq n
          (AdicCompletion.evalₐ (J.map (algebraMap R Rp)) n x))
    (x : AdicCompletion (J.map (algebraMap R Rp)) Rp) :
    F x = adicCompletionLocalizationAlgEquiv J hJ hJp Rp Rq x :=
  AdicCompletion.eq_adicCompletionAlgEquivOfQuotientEquiv_of_evalₐ _ _ _ _ F hF x

/-- **Compatibility with the structure maps from the base**: the comparison is a map of
`R`-algebras, so it carries the canonical image of `r : R` to the canonical image of `r`. -/
theorem adicCompletionLocalizationAlgEquiv_algebraMap (r : R) :
    adicCompletionLocalizationAlgEquiv J hJ hJp Rp Rq
        (algebraMap R (AdicCompletion (J.map (algebraMap R Rp)) Rp) r) =
      algebraMap R (AdicCompletion (J.map (algebraMap R Rq)) Rq) r :=
  (adicCompletionLocalizationAlgEquiv J hJ hJp Rp Rq).commutes r

/-- **Compatibility with the adic filtration**: the comparison matches the `n`-th stage of the
filtration on the two sides, the stage being the kernel of the level-`n` evaluation. -/
theorem mem_ker_evalₐ_adicCompletionLocalizationAlgEquiv (n : ℕ)
    (x : AdicCompletion (J.map (algebraMap R Rp)) Rp) :
    adicCompletionLocalizationAlgEquiv J hJ hJp Rp Rq x ∈
        RingHom.ker (AdicCompletion.evalₐ (J.map (algebraMap R Rq)) n) ↔
      x ∈ RingHom.ker (AdicCompletion.evalₐ (J.map (algebraMap R Rp)) n) := by
  rw [RingHom.mem_ker, RingHom.mem_ker,
    evalₐ_adicCompletionLocalizationAlgEquiv J hJ hJp Rp Rq n x]
  exact map_eq_zero_iff _ (levelRingEquivPow J hJ hJp Rp Rq n).injective

include hJ hJp in
/-- **The adic completion of the localization at `𝔭` is the adic completion of the localization
of the adic completion at `𝔮`**, in bare existential form. The equivalence itself, with its
characterizing clauses, is `Stacks.Algebraization.adicCompletionLocalizationAlgEquiv`. -/
theorem nonempty_algEquiv_adicCompletion_localization :
    Nonempty (AdicCompletion (J.map (algebraMap R Rp)) Rp ≃ₐ[R]
      AdicCompletion (J.map (algebraMap R Rq)) Rq) :=
  ⟨adicCompletionLocalizationAlgEquiv J hJ hJp Rp Rq⟩

end Level

/-! ### The completed local ring at a generalization -/

/-- **The completed local ring at a generalization is the completion of a localization of the
completed local ring.**

Let `X` be a scheme, `ℐ` a quasi-coherent sheaf of ideals, `y ⤳ y'` a specialization and `𝔭` the
prime of `𝒪_{X,y'}` corresponding to `y`, assumed to contain `ℐ_{y'}`, that is, `y` is assumed to
lie in the closed subscheme cut out by `ℐ`. Let `𝔮` be the prime
`Stacks.Algebraization.completedStalkPrime` of `𝒪_{X,y'}^∧` above `𝔭`. Then `𝒪_{X,y}^∧` is the
adic completion of the localization of `𝒪_{X,y'}^∧` at `𝔮`.

Together with `Stacks.Algebraization.ringKrullDim_quotient_completedStalkPrime` this is the first
input of the proof of [Stacks, Tag 0EJA]: the ring map `𝒪_{X,y'}^∧ → 𝒪_{X,y}^∧` realizing the
target as the completion of a localization of the source at a prime `𝔮` whose quotient has the
dimension of `𝒪_{X,y'}/𝔭`. -/
theorem nonempty_algEquiv_completedLocalRing_of_specializes (I : X.IdealSheafData) {y y' : X}
    (h : y ⤳ y') (hfg : (IdealSheafData.stalk I y').FG)
    (q : PrimeSpectrum (X.presheaf.stalk y')) (hqy : X.fromSpecStalk y' q = y)
    (hq : IdealSheafData.stalk I y' ≤ q.asIdeal)
    (Rq : Type u) [CommRing Rq] [Algebra (completedLocalRing I y') Rq]
    [IsLocalization (completedStalkPrime I y' q hq).asIdeal.primeCompl Rq] :
    letI : Algebra (X.presheaf.stalk y') (X.presheaf.stalk y) :=
      (X.presheaf.stalkSpecializes h).hom.toAlgebra
    letI : Algebra (X.presheaf.stalk y') Rq :=
      ((algebraMap (completedLocalRing I y') Rq).comp
        (algebraMap (X.presheaf.stalk y') (completedLocalRing I y'))).toAlgebra
    Nonempty (completedLocalRing I y ≃ₐ[X.presheaf.stalk y']
      AdicCompletion ((IdealSheafData.stalk I y').map
        (algebraMap (X.presheaf.stalk y') Rq)) Rq) := by
  let _ : Algebra (X.presheaf.stalk y') (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let _ : Algebra (X.presheaf.stalk y') Rq :=
    ((algebraMap (completedLocalRing I y') Rq).comp
      (algebraMap (X.presheaf.stalk y') (completedLocalRing I y'))).toAlgebra
  have _ : IsScalarTower (X.presheaf.stalk y') (completedLocalRing I y') Rq :=
    IsScalarTower.of_algebraMap_eq' rfl
  have _ : q.asIdeal.IsPrime := q.2
  have _ : IsLocalization q.asIdeal.primeCompl (X.presheaf.stalk y) :=
    Chow.isLocalization_stalk_of_specializes h q hqy
  have _ : IsLocalization
      (adicPrimeOver (IdealSheafData.stalk I y') hq).asIdeal.primeCompl Rq :=
    inferInstanceAs (IsLocalization (completedStalkPrime I y' q hq).asIdeal.primeCompl Rq)
  have hmap : (IdealSheafData.stalk I y').map
      (algebraMap (X.presheaf.stalk y') (X.presheaf.stalk y)) = IdealSheafData.stalk I y :=
    (Chow.idealStalk_eq_map_stalkSpecializes I h).symm
  have hcomp := nonempty_algEquiv_adicCompletion_localization (IdealSheafData.stalk I y') hfg hq
    (X.presheaf.stalk y) Rq
  rwa [hmap] at hcomp

end Identification


end Stacks.Algebraization

end
