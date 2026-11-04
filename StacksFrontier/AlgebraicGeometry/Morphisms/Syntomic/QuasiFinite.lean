module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Jacobson.Artinian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Syntomic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberCriterion
public import StacksFrontier.RingTheory.Syntomic.SquarePresentation
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt

/-!
# Locally quasi-finite syntomic morphisms

A locally quasi-finite morphism of schemes is syntomic exactly when it is flat and a local
complete intersection morphism; exactly when it is flat, locally of finite presentation and all
of its fibres are local complete intersections over the residue fields of their base points; and
exactly when near every point of its source it is given by a *square* relative global complete
intersection, a presentation `B = A[x_1, …, x_n]/(f_1, …, f_n)` with as many relations as
variables.

## Main definitions

* `AlgebraicGeometry.HasLocalSquarePresentation`: part (4) of Stacks 0BWE, local presentations
  `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`.
* `AlgebraicGeometry.HasLocalSquareRelativeGlobalCompleteIntersection`: part (5) of Stacks 0BWE,
  local relative global complete intersections with as many relations as variables.

## Main results

* `AlgebraicGeometry.locallyQuasiFinite_syntomic_tfae`: **Stacks 0BWE**, the equivalence of
  parts (1), (2), (3), (4) and (5); the equivalence with parts (6) and (7) is
  `AlgebraicGeometry.locallyQuasiFinite_syntomic_tfae_naiveCotangentComplex`.
* `AlgebraicGeometry.hasLocalSquareRelativeGlobalCompleteIntersection_iff`: **Stacks 0BWE**,
  the equivalence of parts (1) and (5).

## References

* [Stacks Project, Tag 0BWE](https://stacks.math.columbia.edu/tag/0BWE)
* [Stacks Project, Tag 069K](https://stacks.math.columbia.edu/tag/069K)
* [Stacks Project, Tag 00SY](https://stacks.math.columbia.edu/tag/00SY)
* [Stacks Project, Tag 00SW](https://stacks.math.columbia.edu/tag/00SW)
* [Stacks Project, Tag 00SP](https://stacks.math.columbia.edu/tag/00SP)
* [Stacks Project, Tag 01UF](https://stacks.math.columbia.edu/tag/01UF)
* [Stacks Project, Tag 01UI](https://stacks.math.columbia.edu/tag/01UI)
* [Stacks Project, Tag 01UK](https://stacks.math.columbia.edu/tag/01UK)
* [Stacks Project, Tag 01UL](https://stacks.math.columbia.edu/tag/01UL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### Square presentations of quasi-finite algebras -/

/-- **An algebra with a square relative global complete intersection presentation is
quasi-finite.** -/
theorem Algebra.QuasiFinite.of_square_presentation {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {ι σ : Type*} [Finite ι] [Finite σ]
    {P : Algebra.Presentation R S ι σ} (hP : P.IsRelativeGlobalCompleteIntersection)
    (hcard : Nat.card σ = Nat.card ι) : Algebra.QuasiFinite R S := by
  have : Algebra.FinitePresentation R S := P.finitePresentation_of_isFinite
  refine ⟨fun p _ => ?_⟩
  rcases subsingleton_or_nontrivial (p.Fiber S) with h | h
  · exact Module.Finite.of_surjective (0 : p.ResidueField →ₗ[p.ResidueField] p.Fiber S)
      fun x => ⟨0, Subsingleton.elim _ _⟩
  · have hdim := hP.ringKrullDim_fiber_add_card_eq_card p h
    rw [hcard] at hdim
    have hz : ringKrullDim (p.Fiber S) = 0 := by
      obtain ⟨-, hx⟩ := WithBot.le_and_eq_tsub_of_add_natCast_eq hdim
      simp [hx]
    exact (Module.finite_iff_krullDimLE_zero _ _).mpr
      (ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hz)

/-- An algebra `S` presented by `n` variables and `n` relations over `R` is also of the form
`R[x_1, …, x_n, 1/h]/(f_1, …, f_n)`, with `h = 1`. -/
private theorem Algebra.Presentation.exists_localization_away_quotient_algEquiv
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
    (P : Algebra.Presentation R S (Fin n) (Fin n)) :
    ∃ (h : MvPolynomial (Fin n) R) (g : Fin n → MvPolynomial (Fin n) R),
      Nonempty (S ≃ₐ[R] (Localization.Away h ⧸ Ideal.span
        (Set.range fun i ↦ algebraMap (MvPolynomial (Fin n) R) (Localization.Away h) (g i)))) := by
  refine ⟨1, P.relation, ⟨?_⟩⟩
  have hH : Submonoid.powers (1 : MvPolynomial (Fin n) R) ≤
      IsUnit.submonoid (MvPolynomial (Fin n) R) := by
    rintro x ⟨k, rfl⟩
    simp
  let e : MvPolynomial (Fin n) R ≃ₐ[R] Localization.Away (1 : MvPolynomial (Fin n) R) :=
    (IsLocalization.atUnits (MvPolynomial (Fin n) R) (Submonoid.powers 1)
      (S := Localization.Away (1 : MvPolynomial (Fin n) R)) hH).restrictScalars R
  have eS : S ≃ₐ[R] MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P.relation) :=
    (P.quotientEquiv.restrictScalars R).symm.trans
      (Ideal.quotientEquivAlgOfEq R P.span_range_relation_eq_ker.symm)
  refine eS.trans (Ideal.quotientEquivAlg _ _ e ?_)
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

/-- **A square presentation of a quasi-finite algebra is a relative global complete
intersection.** -/
public theorem Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.QuasiFinite R S]
    {ι σ : Type*} [Finite ι] [Finite σ] (P : Algebra.Presentation R S ι σ)
    (hcard : Nat.card σ = Nat.card ι) : P.IsRelativeGlobalCompleteIntersection := by
  refine ⟨fun p _ hp => ?_⟩
  rw [Algebra.QuasiFinite.ringKrullDim_fiber_eq_zero p, zero_add, hcard]

/-- The algebra map of the quotient `A ⧸ I → B ⧸ IB` induced by an `A`-algebra `B`, on classes of
elements of `A`. -/
private theorem Ideal.quotientMapAlgebra_algebraMap_mk {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) :
    letI : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
      (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map).toAlgebra
    ∀ x : A, algebraMap (A ⧸ I) (B ⧸ I.map (algebraMap A B)) (Ideal.Quotient.mk I x)
      = Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B x) :=
  fun x ↦ by simp [RingHom.algebraMap_toAlgebra]

/-- **Localization commutes with taking quotients.** If `B` is the localization of `A` away from
`a` and `I` is an ideal of `A`, then `B ⧸ IB` is the localization of `A ⧸ I` away from the class
of `a`. -/
private theorem IsLocalization.Away.quotient {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (a : A) [IsLocalization.Away a B] (I : Ideal A) :
    letI : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
      (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk I a) (B ⧸ I.map (algebraMap A B)) := by
  let _ : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map).toAlgebra
  have hmap := Ideal.quotientMapAlgebra_algebraMap_mk (B := B) I
  have hloc : IsLocalization ((Submonoid.powers a).map (Ideal.Quotient.mk I))
      (B ⧸ I.map (algebraMap A B)) :=
    IsLocalization.of_surjective (M := Submonoid.powers a) (S := B)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (RingHom.ext fun x ↦ by simpa using (hmap x).symm)
      (by simp [Ideal.mk_ker])
  rwa [Submonoid.map_powers] at hloc

/-- The quotients `A ⧸ I` and `B ⧸ IB` of an `A`-algebra `B` form a tower over any base ring of
`A` and `B`. -/
private theorem IsScalarTower.quotient_map {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {R : Type*} [CommRing R] [Algebra R A] [Algebra R B] [IsScalarTower R A B] (I : Ideal A) :
    letI : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
      (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map).toAlgebra
    IsScalarTower R (A ⧸ I) (B ⧸ I.map (algebraMap A B)) := by
  let _ : Algebra (A ⧸ I) (B ⧸ I.map (algebraMap A B)) :=
    (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map).toAlgebra
  exact .of_algebraMap_eq fun r ↦ by
    rw [IsScalarTower.algebraMap_apply R A (A ⧸ I), Ideal.Quotient.algebraMap_eq,
      Ideal.quotientMapAlgebra_algebraMap_mk (B := B) I, ← IsScalarTower.algebraMap_apply R A B,
      ← Ideal.Quotient.mk_algebraMap]


/-- **A quasi-finite algebra of the form `R[x_1, …, x_n, 1/h]/(f_1, …, f_n)` has a square
relative global complete intersection presentation.** -/
theorem Algebra.exists_square_presentation_of_away_quotient {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.QuasiFinite R S] {n : ℕ}
    (h : MvPolynomial (Fin n) R) (g : Fin n → MvPolynomial (Fin n) R)
    (e : S ≃ₐ[R] (Localization.Away h ⧸ Ideal.span (Set.range fun i ↦
      algebraMap (MvPolynomial (Fin n) R) (Localization.Away h) (g i)))) :
    ∃ (m : ℕ) (P : Algebra.Presentation R S (Fin m) (Fin m)),
      P.IsRelativeGlobalCompleteIntersection := by
  have hJ : Ideal.span (Set.range fun i ↦ algebraMap (MvPolynomial (Fin n) R)
        (Localization.Away h) (g i)) =
      (Ideal.span (Set.range g)).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h)) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  let Q : Algebra.Presentation R
      (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)) (Fin n) (Fin n) :=
    Algebra.Presentation.naive (v := g)
  have hAway : IsLocalization.Away
      (algebraMap Q.Ring (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g)) h)
      (Localization.Away h ⧸ (Ideal.span (Set.range g)).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h))) := by
    rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
    exact inferInstanceAs (IsLocalization
      (Algebra.algebraMapSubmonoid (_ ⧸ Ideal.span (Set.range g)) (.powers h)) _)
  have : IsScalarTower R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range g))
      (Localization.Away h ⧸ (Ideal.span (Set.range g)).map
        (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h))) :=
    .of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R)
          (_ ⧸ Ideal.span (Set.range g)),
        ← IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) R) (_ ⧸ _),
        ← IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R)]
  let P₀ := Q.localizationAwayComp h
    (Localization.Away h ⧸ (Ideal.span (Set.range g)).map
      (algebraMap (MvPolynomial (Fin n) R) (Localization.Away h)))
  let eqv : Fin (n + 1) ≃ Unit ⊕ Fin n :=
    (finSuccEquiv' (0 : Fin (n + 1))).trans
      ((Equiv.optionEquivSumPUnit _).trans (Equiv.sumComm _ _))
  let e' := e.trans (Ideal.quotientEquivAlgOfEq R hJ)
  exact ⟨n + 1, (P₀.reindex eqv eqv).ofAlgEquiv e'.symm,
    Algebra.Presentation.isRelativeGlobalCompleteIntersection_of_quasiFinite _ rfl⟩

namespace AlgebraicGeometry

/-! ### The conditions of parts (4) and (5) -/

/-- The local presentation condition of part (4) of Stacks 0BWE: around every point `y` of the
source there are affine opens `y ∈ V ⊆ Y` and `U ⊆ X` with `f(V) ⊆ U`, an integer `n`, and
`h, f_1, …, f_n ∈ A[x_1, …, x_n]` with `A = Γ(X, U)`, such that
`Γ(Y, V) = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
def HasLocalSquarePresentation {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∀ y : Y, ∃ (V : Y.affineOpens) (U : X.affineOpens) (_ : y ∈ V.1)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    ∃ (n : ℕ) (h : MvPolynomial (Fin n) Γ(X, U.1))
      (g : Fin n → MvPolynomial (Fin n) Γ(X, U.1)),
      Nonempty (Γ(Y, V.1) ≃ₐ[Γ(X, U.1)]
        (Localization.Away h ⧸ Ideal.span
          (Set.range fun i ↦ algebraMap (MvPolynomial (Fin n) Γ(X, U.1))
            (Localization.Away h) (g i))))

/-- The local presentation condition of part (5) of Stacks 0BWE: around every point `y` of the
source there are affine opens `y ∈ V ⊆ Y` and `U ⊆ X` with `f(V) ⊆ U` for which
`Γ(X, U) → Γ(Y, V)` is a relative global complete intersection with as many relations as
variables, `Γ(Y, V) = Γ(X, U)[x_1, …, x_n]/(f_1, …, f_n)`. -/
def HasLocalSquareRelativeGlobalCompleteIntersection {Y X : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∀ y : Y, ∃ (V : Y.affineOpens) (U : X.affineOpens) (_ : y ∈ V.1)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    ∃ (n : ℕ) (P : Algebra.Presentation Γ(X, U.1) Γ(Y, V.1) (Fin n) (Fin n)),
      P.IsRelativeGlobalCompleteIntersection

/-! ### The individual implications -/

/-- Every fibre of a syntomic morphism is a local complete intersection over the residue field of
its base point. -/
theorem isLocalCompleteIntersectionOverField_fiber_of_syntomic {Y X : Scheme.{u}} {f : Y ⟶ X}
    (hf : Syntomic f) (x : X) :
    IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x) :=
  syntomic_isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback f (X.fromSpecResidueField x)) hf

/-- On affine opens, a locally quasi-finite morphism induces a quasi-finite algebra. -/
theorem quasiFinite_appLE {Y X : Scheme.{u}} {f : Y ⟶ X} (hqf : LocallyQuasiFinite f)
    (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
  (HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)
    (Q := RingHom.QuasiFinite)).mp hqf U V hVU

/-- A locally quasi-finite syntomic morphism of schemes has, around every point of its source, a
square relative global complete intersection presentation. -/
@[stacks 0BWE "the implication (1) ⟹ (5)"]
theorem hasLocalSquareRelativeGlobalCompleteIntersection_of_locallyQuasiFinite_syntomic
    {Y X : Scheme.{u}} {f : Y ⟶ X} (hqf : LocallyQuasiFinite f) (hf : Syntomic f) :
    HasLocalSquareRelativeGlobalCompleteIntersection f := by
  intro y
  obtain ⟨V₀, hyV₀, U, hVU, hsyn⟩ := hf y
  let _ : Algebra Γ(X, U.1) Γ(Y, V₀.1) := (f.appLE U.1 V₀.1 hVU).hom.toAlgebra
  have : Algebra.Syntomic Γ(X, U.1) Γ(Y, V₀.1) := hsyn
  have : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V₀.1) := quasiFinite_appLE hqf U V₀ hVU
  obtain ⟨r, hr, hrgci⟩ := Algebra.Syntomic.exists_notMem_isRelativeGlobalCompleteIntersection
    (R := Γ(X, U.1)) (V₀.2.primeIdealOf ⟨y, hyV₀⟩).asIdeal
  have hyr : y ∈ Y.basicOpen r := by
    have h1 : V₀.2.primeIdealOf ⟨y, hyV₀⟩ ∈ V₀.2.fromSpec ⁻¹ᵁ Y.basicOpen r := by
      rw [V₀.2.fromSpec_preimage_basicOpen r]
      exact (PrimeSpectrum.mem_basicOpen r _).mpr hr
    have h2 : V₀.2.fromSpec (V₀.2.primeIdealOf ⟨y, hyV₀⟩) ∈ Y.basicOpen r := h1
    rwa [V₀.2.fromSpec_primeIdealOf ⟨y, hyV₀⟩] at h2
  have hle : Y.basicOpen r ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le r).trans hVU
  refine ⟨⟨Y.basicOpen r, V₀.2.basicOpen r⟩, U, hyr, hle, ?_⟩
  let _ : Algebra Γ(X, U.1) Γ(Y, Y.basicOpen r) :=
    (f.appLE U.1 (Y.basicOpen r) hle).hom.toAlgebra
  have := V₀.2.isLocalization_basicOpen r
  have : IsScalarTower Γ(X, U.1) Γ(Y, V₀.1) Γ(Y, Y.basicOpen r) :=
    .of_algebraMap_eq fun x => by
      simp only [RingHom.algebraMap_toAlgebra, ← ConcreteCategory.comp_apply,
        Scheme.Hom.appLE_map]
  have : Algebra.IsRelativeGlobalCompleteIntersection Γ(X, U.1) Γ(Y, Y.basicOpen r) :=
    .of_algEquiv ((IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r)
      Γ(Y, Y.basicOpen r)).restrictScalars Γ(X, U.1))
  have : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, Y.basicOpen r) :=
    quasiFinite_appLE hqf U ⟨Y.basicOpen r, V₀.2.basicOpen r⟩ hle
  exact Algebra.exists_square_presentation ((V₀.2.basicOpen r).primeIdealOf ⟨y, hyr⟩).asIdeal

/-- A morphism of schemes with square relative global complete intersection presentations around
every point of its source is locally quasi-finite. -/
@[stacks 0BWE "the implication (5) ⟹ (1), the locally-quasi-finite conjunct"]
theorem locallyQuasiFinite_of_hasLocalSquareRelativeGlobalCompleteIntersection
    {Y X : Scheme.{u}} {f : Y ⟶ X} (h : HasLocalSquareRelativeGlobalCompleteIntersection f) :
    LocallyQuasiFinite f := by
  refine (HasRingHomProperty.iff_exists_appLE (P := @LocallyQuasiFinite)
    (Q := RingHom.QuasiFinite)
    (RingHom.QuasiFinite.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.QuasiFinite.holdsForLocalizationAway).left).2 fun y => ?_
  obtain ⟨V, U, hyV, hVU, hex⟩ := h y
  let _ : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨n, P, hP⟩ := hex
  exact ⟨U, V, hyV, hVU, Algebra.QuasiFinite.of_square_presentation hP rfl⟩

/-- A morphism of schemes with square relative global complete intersection presentations around
every point of its source is syntomic. -/
@[stacks 0BWE "the implication (5) ⟹ (1), the syntomic conjunct"]
theorem syntomic_of_hasLocalSquareRelativeGlobalCompleteIntersection {Y X : Scheme.{u}}
    {f : Y ⟶ X} (h : HasLocalSquareRelativeGlobalCompleteIntersection f) : Syntomic f := by
  intro y
  obtain ⟨V, U, hyV, hVU, hex⟩ := h y
  refine ⟨V, hyV, U, hVU, ?_⟩
  let _ : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨n, P, hP⟩ := hex
  have : Algebra.IsRelativeGlobalCompleteIntersection Γ(X, U.1) Γ(Y, V.1) := ⟨⟨n, n, P, hP⟩⟩
  exact Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection _ _

/-- A morphism of schemes which is locally a square relative global complete intersection
`B = A[x_1, …, x_n]/(f_1, …, f_n)` is locally of the form `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`,
with `h = 1`. -/
@[stacks 0BWE "the implication (5) ⟹ (4), the presentation conjunct"]
theorem hasLocalSquarePresentation_of_hasLocalSquareRelativeGlobalCompleteIntersection
    {Y X : Scheme.{u}} {f : Y ⟶ X} (h : HasLocalSquareRelativeGlobalCompleteIntersection f) :
    HasLocalSquarePresentation f := by
  intro y
  obtain ⟨V, U, hyV, hVU, hex⟩ := h y
  let _ : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨n, P, -⟩ := hex
  exact ⟨V, U, hyV, hVU, n, P.exists_localization_away_quotient_algEquiv⟩

/-- A locally quasi-finite morphism of schemes which is locally of the form
`B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` is locally a square relative global complete
intersection. -/
@[stacks 0BWE "the implication (4) ⟹ (5)"]
theorem hasLocalSquareRelativeGlobalCompleteIntersection_of_hasLocalSquarePresentation
    {Y X : Scheme.{u}} {f : Y ⟶ X} (hqf : LocallyQuasiFinite f)
    (h : HasLocalSquarePresentation f) :
    HasLocalSquareRelativeGlobalCompleteIntersection f := by
  intro y
  obtain ⟨V, U, hyV, hVU, hex⟩ := h y
  let _ : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  have : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) := quasiFinite_appLE hqf U V hVU
  obtain ⟨n, hh, g, ⟨e⟩⟩ := hex
  exact ⟨V, U, hyV, hVU, Algebra.exists_square_presentation_of_away_quotient hh g e⟩

/-! ### The equivalence -/

/-- For a morphism of schemes `f : Y ⟶ X` the following are equivalent:

1. `f` is locally quasi-finite and syntomic;
2. `f` is locally quasi-finite, flat, and a local complete intersection morphism;
3. `f` is locally quasi-finite, flat, locally of finite presentation, and all the fibres of `f`
   are local complete intersections over the residue fields of their base points;
4. `f` is locally quasi-finite and, around every point of its source, there are affine opens
   `y ∈ V = Spec(B) ⊆ Y` and `U = Spec(A) ⊆ X` with `f(V) ⊆ U`, an integer `n` and
   `h, f_1, …, f_n ∈ A[x_1, …, x_n]` with `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`;
5. around every point of the source there are such affine opens with `A → B` a relative global
   complete intersection of the form `B = A[x_1, …, x_n]/(f_1, …, f_n)`. -/
@[stacks 0BWE "the equivalence of (1), (2), (3), (4) and (5)"]
theorem locallyQuasiFinite_syntomic_tfae {Y X : Scheme.{u}} (f : Y ⟶ X) :
    List.TFAE [
      LocallyQuasiFinite f ∧ Syntomic f,
      (LocallyQuasiFinite f ∧ Flat f) ∧ IsLocalCompleteIntersectionMorphism f,
      ((LocallyQuasiFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
        ∀ x : X, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x),
      LocallyQuasiFinite f ∧ HasLocalSquarePresentation f,
      HasLocalSquareRelativeGlobalCompleteIntersection f] := by
  tfae_have 1 → 2 := fun h =>
    ⟨⟨h.1, flat h.2⟩, isLocalCompleteIntersectionMorphism_of_syntomic h.2⟩
  tfae_have 2 → 3 := fun h =>
    have hf : Syntomic f :=
      syntomic_of_flat_of_isLocalCompleteIntersectionMorphism h.1.2 h.2
    ⟨⟨⟨h.1.1, h.1.2⟩, locallyOfFinitePresentation hf⟩,
      isLocalCompleteIntersectionOverField_fiber_of_syntomic hf⟩
  tfae_have 3 → 1 := fun h =>
    let _ : Flat f := h.1.1.2
    let _ : LocallyOfFinitePresentation f := h.1.2
    ⟨h.1.1.1, syntomic_of_lci_fibers f h.2⟩
  tfae_have 1 → 5 := fun h =>
    hasLocalSquareRelativeGlobalCompleteIntersection_of_locallyQuasiFinite_syntomic h.1 h.2
  tfae_have 5 → 1 := fun h =>
    ⟨locallyQuasiFinite_of_hasLocalSquareRelativeGlobalCompleteIntersection h,
      syntomic_of_hasLocalSquareRelativeGlobalCompleteIntersection h⟩
  tfae_have 5 → 4 := fun h =>
    ⟨locallyQuasiFinite_of_hasLocalSquareRelativeGlobalCompleteIntersection h,
      hasLocalSquarePresentation_of_hasLocalSquareRelativeGlobalCompleteIntersection h⟩
  tfae_have 4 → 5 := fun h =>
    hasLocalSquareRelativeGlobalCompleteIntersection_of_hasLocalSquarePresentation h.1 h.2
  tfae_finish

/-- A locally quasi-finite syntomic morphism of schemes is locally quasi-finite, flat, and a local
complete intersection morphism. -/
@[stacks 0BWE "the implication (1) ⟹ (2)"]
theorem flat_and_isLocalCompleteIntersectionMorphism_of_locallyQuasiFinite_syntomic
    {Y X : Scheme.{u}} {f : Y ⟶ X} (h : LocallyQuasiFinite f ∧ Syntomic f) :
    (LocallyQuasiFinite f ∧ Flat f) ∧ IsLocalCompleteIntersectionMorphism f :=
  (locallyQuasiFinite_syntomic_tfae f).out 1 2 |>.mp h

/-- A locally quasi-finite flat local complete intersection morphism of schemes is locally of
finite presentation and all of its fibres are local complete intersections over the residue fields
of their base points. -/
@[stacks 0BWE "the implication (2) ⟹ (3)", sga "6 VIII 1.4" "special case"]
theorem locallyOfFinitePresentation_and_lci_fibers_of_locallyQuasiFinite_flat_lci
    {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : (LocallyQuasiFinite f ∧ Flat f) ∧ IsLocalCompleteIntersectionMorphism f) :
    ((LocallyQuasiFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      ∀ x : X, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x) :=
  (locallyQuasiFinite_syntomic_tfae f).out 2 3 |>.mp h

/-- A locally quasi-finite flat morphism of schemes which is locally of finite presentation and
all of whose fibres are local complete intersections over the residue fields of their base points
is, around every point of its source, of the form `B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`. -/
@[stacks 0BWE "the implication (3) ⟹ (4)"]
theorem locallyQuasiFinite_and_hasLocalSquarePresentation_of_lci_fibers {Y X : Scheme.{u}}
    {f : Y ⟶ X}
    (h : ((LocallyQuasiFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      ∀ x : X, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x)) :
    LocallyQuasiFinite f ∧ HasLocalSquarePresentation f :=
  (locallyQuasiFinite_syntomic_tfae f).out 3 4 |>.mp h

/-- A locally quasi-finite morphism of schemes which is locally of the form
`B = A[x_1, …, x_n, 1/h]/(f_1, …, f_n)`, with as many relations as variables, is syntomic. -/
@[stacks 0BWE "the implication (4) ⟹ (1)"]
theorem locallyQuasiFinite_and_syntomic_of_hasLocalSquarePresentation {Y X : Scheme.{u}}
    {f : Y ⟶ X} (h : LocallyQuasiFinite f ∧ HasLocalSquarePresentation f) :
    LocallyQuasiFinite f ∧ Syntomic f :=
  (locallyQuasiFinite_syntomic_tfae f).out 4 1 |>.mp h

/-- A locally quasi-finite flat morphism of schemes which is locally of finite presentation and
all of whose fibres are local complete intersections over the residue fields of their base points
is syntomic. -/
@[stacks 0BWE "the implication (3) ⟹ (1)"]
theorem locallyQuasiFinite_and_syntomic_of_lci_fibers {Y X : Scheme.{u}} {f : Y ⟶ X}
    (h : ((LocallyQuasiFinite f ∧ Flat f) ∧ LocallyOfFinitePresentation f) ∧
      ∀ x : X, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField x)) :
    LocallyQuasiFinite f ∧ Syntomic f :=
  (locallyQuasiFinite_syntomic_tfae f).out 3 1 |>.mp h

/-- A morphism of schemes has a square relative global complete intersection presentation around
every point of its source if and only if it is locally quasi-finite and syntomic. -/
@[stacks 0BWE "the equivalence of (1) and (5)"]
theorem hasLocalSquareRelativeGlobalCompleteIntersection_iff {Y X : Scheme.{u}} (f : Y ⟶ X) :
    HasLocalSquareRelativeGlobalCompleteIntersection f ↔
      LocallyQuasiFinite f ∧ Syntomic f :=
  (locallyQuasiFinite_syntomic_tfae f).out 5 1

end AlgebraicGeometry

end
