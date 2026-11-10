module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.QuasiFiniteSyntomic.UniversalFamily
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.QuasiFinite

/-!
# Quasi-finite syntomic morphisms are locally base changes of the universal family

A locally quasi-finite syntomic morphism `f : Y ⟶ X` is, around every point of its source, the
base change of the universal family `Y_{n, d} ⟶ X_{n, d}` of Example 0FK8: there are opens
`y ∈ V ⊆ Y` and `U ⊆ X` with `f(V) ⊆ U` for which the square formed by `V ⟶ U` and
`Y_{n, d} ⟶ X_{n, d}` is cartesian.

## Main results

* `AlgebraicGeometry.exists_universalPolynomial_specialization`: **Stacks 0FKA**, the
  cocartesian diagram of rings underlying the construction — a square presentation of the
  sections of `f` whose relations are specializations of the universal polynomials.
* `AlgebraicGeometry.exists_isPullback_universalQuasiFiniteMorphism`: **Stacks 0FKA**, the
  cartesian square with the universal family.

## Implementation notes

The left-hand square of the source diagram, the one formed by the two open immersions and `f`,
is encoded by the restricted morphism `AlgebraicGeometry.Scheme.Hom.resLE`; the right-hand
square is an `CategoryTheory.IsPullback`.

The ring-theoretic content is `exists_universalPolynomial_specialization` and is universe
polymorphic: by part (5) of Stacks 0BWE the morphism is given on affine opens by a square
relative global complete intersection `Γ(Y, V) = Γ(X, U)[x_1, …, x_n]/(g_1, …, g_n)`, and
choosing `d` larger than the total degrees of the `g_i` lets the universal coefficients
`a_{i, E}` be specialized to the coefficients of the `g_i`; the universal polynomials then map
to the `g_i`. A square presentation is padded by one variable and one relation so that the index
`n` is positive, as Example 0FK8 requires.

The geometric statement is restricted to `Scheme.{0}`. The universal family of Example 0FK8 is
built from a polynomial ring over `ℤ`, so `AlgebraicGeometry.universalBaseScheme` and
`AlgebraicGeometry.universalQuasiFiniteScheme` are objects of `Scheme.{0}`, and a square
comparing a morphism of `Scheme.{u}` with them is not well typed for `u ≠ 0`. Making the
geometric statement universe polymorphic requires a universe-polymorphic form of Example 0FK8.

Passing from `Spec(Γ(X, U) ⊗_A B)` to the open subscheme `Y_{n, d} ⊆ Spec(B)` uses that the
quasi-finite locus is stable under base change (Stacks 01TM): every point of `V` is quasi-finite
over `U`, hence its image in `Spec(B)` is quasi-finite over `Spec(A)` and so lies in
`Y_{n, d}`. The comparison morphism therefore factors through `Y_{n, d}`, and pasting the
pullback square of that factorization onto the affine square gives the cartesian square.

## References

* [Stacks Project, Tag 0FKA](https://stacks.math.columbia.edu/tag/0FKA)
* [Stacks Project, Tag 0FK8](https://stacks.math.columbia.edu/tag/0FK8)
* [Stacks Project, Tag 0BWE](https://stacks.math.columbia.edu/tag/0BWE)
* [Stacks Project, Tag 01TM](https://stacks.math.columbia.edu/tag/01TM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Specializing the universal polynomials -/

/-- The bounded multi-index of Example 0FK8 attached to an exponent vector of total degree at
most `d`. -/
def MultiIndex.ofFinsupp {n d : ℕ} (m : Fin n →₀ ℕ) (hm : ∑ i, m i ≤ d) :
    MultiIndex n d :=
  ⟨fun i ↦ ⟨m i, Nat.lt_succ_iff.mpr
    ((Finset.single_le_sum (f := fun i : Fin n ↦ m i) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ i)).trans hm)⟩, by simpa using hm⟩

/-- The exponent vector of `MultiIndex.ofFinsupp m hm` is `m`. -/
@[simp]
theorem multiIndexExponent_ofFinsupp {n d : ℕ} (m : Fin n →₀ ℕ) (hm : ∑ i, m i ≤ d) :
    multiIndexExponent n d (MultiIndex.ofFinsupp m hm) = m := by
  ext i
  simp [multiIndexExponent, MultiIndex.ofFinsupp]

/-- The specialization of the universal coefficients `a_{i, E}` to the coefficients of a given
family `p_1, …, p_n` of polynomials in `n` variables. -/
private def universalCoefficientSpecialization {R : Type*} [CommRing R] (n d : ℕ)
    (p : Fin n → MvPolynomial (Fin n) R) : universalCoefficientRing n d →+* R :=
  (MvPolynomial.aeval fun j : Fin n × MultiIndex n d ↦
    (p j.1).coeff (multiIndexExponent n d j.2)).toRingHom

/-- Specializing the universal coefficients to the coefficients of `p_i` turns the universal
polynomial `f_i` into `p_i`, provided every `p_i` has total degree at most `d`. -/
private theorem map_universalPolynomial_eq {R : Type*} [CommRing R] (n d : ℕ)
    (p : Fin n → MvPolynomial (Fin n) R) (hd : ∀ i, (p i).totalDegree ≤ d) (i : Fin n) :
    MvPolynomial.map (universalCoefficientSpecialization n d p) (universalPolynomial n d i)
      = p i := by
  classical
  refine MvPolynomial.ext _ _ fun m ↦ ?_
  simp only [universalPolynomial, map_sum, MvPolynomial.map_monomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial]
  by_cases hcoeff : (p i).coeff m = 0
  · rw [hcoeff]
    refine Finset.sum_eq_zero fun E _ ↦ ?_
    by_cases he : multiIndexExponent n d E = m
    · simp [he, universalCoefficientSpecialization, universalCoefficient, hcoeff]
    · simp [he]
  · have hm : ∑ j : Fin n, m j ≤ d := by
      simpa [Finsupp.sum_fintype] using
        (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcoeff)).trans (hd i)
    rw [Finset.sum_eq_single (MultiIndex.ofFinsupp m hm)]
    · simp [universalCoefficientSpecialization, universalCoefficient]
    · intro F _ hFE
      have hFm : multiIndexExponent n d F ≠ m := fun he ↦
        hFE (multiIndexExponent_injective n d (he.trans (by simp)))
      simp [hFm]
    · exact fun h ↦ absurd (Finset.mem_univ _) h

/-- Every finite family of polynomials in `n` variables is the specialization of the universal
polynomials of Example 0FK8 for some positive degree bound `d`. -/
theorem exists_universalCoefficientSpecialization {R : Type*} [CommRing R] (n : ℕ)
    (p : Fin n → MvPolynomial (Fin n) R) :
    ∃ (d : ℕ) (_ : NeZero d) (φ : universalCoefficientRing n d →+* R),
      ∀ i, MvPolynomial.map φ (universalPolynomial n d i) = p i := by
  classical
  exact ⟨Finset.univ.sup (fun i : Fin n ↦ (p i).totalDegree) + 1, ⟨Nat.succ_ne_zero _⟩,
    universalCoefficientSpecialization _ _ p, map_universalPolynomial_eq _ _ p fun i ↦
      (Finset.le_sup (f := fun j : Fin n ↦ (p j).totalDegree) (Finset.mem_univ i)).trans
        (Nat.le_succ _)⟩

/-! ### Padding a square presentation -/

/-- A square presentation with `n` variables and `n` relations, read as one with `n + 1`
variables and `n + 1` relations by adjoining the inverse of `1`. -/
private def padSquarePresentation {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {n : ℕ} (P : Algebra.Presentation R S (Fin n) (Fin n)) :
    Algebra.Presentation R S (Fin (n + 1)) (Fin (n + 1)) :=
  let Q₀ : Algebra.Presentation S (Localization.Away (1 : S)) Unit Unit :=
    Algebra.Presentation.localizationAway (R := S) (S := Localization.Away (1 : S)) 1
  let Q := Q₀.ofAlgEquiv (IsLocalization.atOne S (Localization.Away (1 : S))).symm
  let e : Fin (n + 1) ≃ Unit ⊕ Fin n :=
    (Fintype.equivFinOfCardEq (α := Unit ⊕ Fin n) (by simp [Nat.add_comm])).symm
  (Q.comp P).reindex e e

/-! ### The universal family is locally the source -/

/-- **Stacks Project, Tag 0FKA, the cocartesian diagram of rings.** Around every point of the
source of a locally quasi-finite syntomic morphism there are affine opens `y ∈ V ⊆ Y` and
`U ⊆ X` with `f(V) ⊆ U`, positive integers `n` and `d`, a specialization
`φ : ℤ[a_{i, E}] → Γ(X, U)` of the universal coefficients of Example 0FK8, and a presentation
`Γ(Y, V) = Γ(X, U)[x_1, …, x_n]/(g_1, …, g_n)` whose relations `g_i` are the images under `φ` of
the universal polynomials `f_i`. -/
theorem exists_universalPolynomial_specialization {Y X : Scheme.{u}} {f : Y ⟶ X}
    (hf : HasLocalSquareRelativeGlobalCompleteIntersection f) (y : Y) :
    ∃ (V : Y.affineOpens) (U : X.affineOpens) (_ : y ∈ V.1) (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
      ∃ (n d : ℕ) (_ : NeZero n) (_ : NeZero d)
        (φ : universalCoefficientRing n d →+* Γ(X, U.1))
        (P : Algebra.Presentation Γ(X, U.1) Γ(Y, V.1) (Fin n) (Fin n)),
        ∀ i, MvPolynomial.map φ (universalPolynomial n d i) = P.relation i := by
  obtain ⟨V, U, hyV, hVU, n, P, -⟩ := hf y
  let _ : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨d, hd, φ, hφ⟩ :=
    exists_universalCoefficientSpecialization (n + 1) (padSquarePresentation P).relation
  exact ⟨V, U, hyV, hVU, n + 1, d, ⟨Nat.succ_ne_zero _⟩, hd, φ, padSquarePresentation P, hφ⟩

/-! ### The cartesian square -/

/-- **The base change of the universal family.** If the relations of a square presentation of
`S` over `R` are the specializations of the universal polynomials along `A → R`, then `S` is the
base change `R ⊗_A B` of the universal quotient algebra. -/
private def universalBaseChangeEquiv (n d : ℕ) {R S : Type*} [CommRing R] [CommRing S]
    [Algebra (universalCoefficientRing n d) R] [Algebra R S]
    [Algebra (universalCoefficientRing n d) S]
    [IsScalarTower (universalCoefficientRing n d) R S]
    (P : Algebra.Presentation R S (Fin n) (Fin n))
    (hrel : ∀ i, MvPolynomial.map (algebraMap (universalCoefficientRing n d) R)
      (universalPolynomial n d i) = P.relation i) :
    (R ⊗[universalCoefficientRing n d] universalQuotientRing n d) ≃ₐ[R] S :=
  let Q : Algebra.Presentation (universalCoefficientRing n d) (universalQuotientRing n d)
      (Fin n) (Fin n) := Algebra.Presentation.naive (v := universalPolynomial n d)
  let Q' := Q.baseChange R
  have hker : Q'.ker = P.ker := by
    rw [← Q'.span_range_relation_eq_ker, ← P.span_range_relation_eq_ker]
    exact congrArg (Ideal.span ·) (congrArg Set.range (funext hrel))
  (Q'.quotientEquiv.restrictScalars R).symm.trans
    (((Ideal.quotientEquivAlgOfEq Q'.Ring hker).restrictScalars R).trans
      (P.quotientEquiv.restrictScalars R))

/-- If the relations of a square presentation of `S` over `R` are the specializations of the
universal polynomials along `φ`, then `Spec S ⟶ Spec R` is a base change of the universal ambient
morphism `Spec B ⟶ Spec A` of Example 0FK8. -/
theorem exists_isPullback_Spec_universalAmbientMorphism (n d : ℕ) [NeZero n] [NeZero d]
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (φ : universalCoefficientRing n d →+* R) (P : Algebra.Presentation R S (Fin n) (Fin n))
    (hrel : ∀ i, MvPolynomial.map φ (universalPolynomial n d i) = P.relation i) :
    ∃ g : Spec (CommRingCat.of S) ⟶ universalAmbientScheme n d,
      IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) g
        (Spec.map (CommRingCat.ofHom φ) : Spec (CommRingCat.of R) ⟶ universalBaseScheme n d)
        (universalAmbientMorphism n d) := by
  let _ : Algebra (universalCoefficientRing n d) R := φ.toAlgebra
  let _ : Algebra (universalCoefficientRing n d) S := ((algebraMap R S).comp φ).toAlgebra
  have : IsScalarTower (universalCoefficientRing n d) R S := .of_algebraMap_eq fun _ ↦ rfl
  let e := universalBaseChangeEquiv n d P hrel
  let _ : Algebra (universalQuotientRing n d) S :=
    RingHom.toAlgebra (e.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := universalCoefficientRing n d)
        (A := R) (B := universalQuotientRing n d)).toRingHom)
  have htower := IsScalarTower.of_algebraMap_eq (R := universalCoefficientRing n d)
      (S := universalQuotientRing n d) (A := S) fun a ↦ by
    change algebraMap (universalCoefficientRing n d) S a
        = e ((1 : R) ⊗ₜ[universalCoefficientRing n d]
            algebraMap (universalCoefficientRing n d) (universalQuotientRing n d) a)
    exact (e.commutes (algebraMap (universalCoefficientRing n d) R a)).symm.trans
      (congrArg e ((Algebra.TensorProduct.algebraMap_apply
        (R := universalCoefficientRing n d) (S := universalCoefficientRing n d) a).symm.trans
        (Algebra.TensorProduct.algebraMap_apply' a)))
  have hpo : Algebra.IsPushout (universalCoefficientRing n d) R (universalQuotientRing n d) S :=
    ⟨IsBaseChange.of_equiv e.toLinearEquiv fun _ ↦ rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom (algebraMap (universalQuotientRing n d) S)), ?_⟩
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout (universalCoefficientRing n d) R
      (universalQuotientRing n d) S)).of_iso' (Iso.refl _) (Iso.refl _)
    (Iso.refl (universalAmbientScheme n d)) (Iso.refl (universalBaseScheme n d))
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)
    ((Category.id_comp _).trans (Category.comp_id _).symm)

/-- A pullback square over `Spec` of the ring map `f.appLE U V hVU` of affine opens gives a
pullback square over the restriction `f.resLE U V hVU`. -/
theorem isPullback_resLE_of_isPullback_SpecMap_appLE {Y X A B : Scheme.{u}} (f : Y ⟶ X)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hVU : V ≤ f ⁻¹ᵁ U) {g : Spec Γ(Y, V) ⟶ B} {h : Spec Γ(X, U) ⟶ A} {k : B ⟶ A}
    (hsq : IsPullback (Spec.map (f.appLE U V hVU)) g h k) :
    IsPullback (f.resLE U V hVU) (hV.isoSpec.hom ≫ g) (hU.isoSpec.hom ≫ h) k := by
  refine hsq.of_iso' hV.isoSpec hU.isoSpec (Iso.refl _) (Iso.refl _) ?_ (Category.comp_id _).symm
    (Category.comp_id _).symm ((Category.id_comp _).trans (Category.comp_id _).symm)
  rw [← cancel_mono (hU.isoSpec.inv ≫ U.ι)]
  simp only [Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.isoSpec_hom_fromSpec,
    Scheme.Hom.resLE_comp_ι]
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU, ← Category.assoc, hV.isoSpec_hom_fromSpec]

/-- If `f` satisfies a local-on-affines property, so does `Spec` of its ring map `f.appLE U V hVU`
on sections over affine opens. -/
private theorem spec_appLE {P : MorphismProperty Scheme.{u}} {Q : ∀ {R S : Type u} [CommRing R]
    [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q] {Y X : Scheme.{u}} (f : Y ⟶ X)
    (hf : P f) (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    P (Spec.map (f.appLE U.1 V.1 hVU)) :=
  (HasRingHomProperty.Spec_iff (P := P)).mpr (HasRingHomProperty.appLE P f hf U V hVU)

/-- **Stacks Project, Tag 0FKA.** Let `f : Y ⟶ X` be a morphism of schemes satisfying the
equivalent conditions of Stacks 0BWE. Then every point `y` of `Y` has opens `y ∈ V ⊆ Y` and
`U ⊆ X` with `f(V) ⊆ U`, together with positive integers `n` and `d` and a commutative diagram
whose right-hand square, over the family `Y_{n, d} ⟶ X_{n, d}` of Example 0FK8, is cartesian. -/
@[stacks 0FKA "stated for schemes in the universe of the universal family `Y_{n, d} ⟶ X_{n, d}`
of Example 0FK8, which is built from a polynomial ring over `ℤ` and so lives in `Scheme.{0}`."]
theorem exists_isPullback_universalQuasiFiniteMorphism {Y X : Scheme.{0}} {f : Y ⟶ X}
    (hqf : LocallyQuasiFinite f) (hsyn : Syntomic f) (y : Y) :
    ∃ (U : X.Opens) (V : Y.Opens) (_ : y ∈ V) (hVU : V ≤ f ⁻¹ᵁ U) (n d : ℕ)
      (_ : NeZero n) (_ : NeZero d) (p : U.toScheme ⟶ universalBaseScheme n d)
      (q : V.toScheme ⟶ universalQuasiFiniteScheme n d),
      IsPullback (f.resLE U V hVU) q p (universalQuasiFiniteMorphism n d) := by
  obtain ⟨V, U, hyV, hVU, n, d, hn, hd, φ, P, hrel⟩ :=
    exists_universalPolynomial_specialization
      ((hasLocalSquareRelativeGlobalCompleteIntersection_iff f).mpr ⟨hqf, hsyn⟩) y
  have := hn
  have := hd
  let _ : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  obtain ⟨g, hsqU⟩ := exists_isPullback_Spec_universalAmbientMorphism n d φ P hrel
  have hV : IsAffineOpen V.1 := V.2
  have hU : IsAffineOpen U.1 := U.2
  have hgeom := isPullback_resLE_of_isPullback_SpecMap_appLE f hU hV hVU hsqU
  refine ⟨U.1, V.1, hyV, hVU, n, d, hn, hd,
    hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ), ?_⟩
  have hfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hsyn
  have hambFT : LocallyOfFiniteType (universalAmbientMorphism n d) := inferInstance
  have hrange : Set.range (hV.isoSpec.hom ≫ g) ⊆ Set.range (universalQuasiFiniteOpen n d).ι := by
    have hlocus := @quasiFiniteLocus_eq_preimage_of_isPullback _ _ _ _ _ _ _ _ hambFT
      hsqU.flip
    rintro _ ⟨z, rfl⟩
    have hz := (mem_quasiFiniteLocus_iff
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) Γ(Y, V.1)))) (hV.isoSpec.hom z)).mpr
      (((forall_quasiFiniteAt_iff _).mpr
        ⟨spec_appLE (P := @LocallyOfFiniteType) (Q := RingHom.FiniteType) f inferInstance U V hVU,
          spec_appLE (P := @LocallyQuasiFinite) (Q := RingHom.QuasiFinite) f hqf U V hVU⟩)
        (hV.isoSpec.hom z))
    rw [hlocus] at hz
    exact ⟨⟨_, (mem_universalQuasiFiniteOpen_iff n d _).mpr
      ((mem_quasiFiniteLocus_iff _ _).mp hz)⟩, rfl⟩
  refine ⟨(IsOpenImmersion.lift (universalQuasiFiniteOpen n d).ι _ hrange :
    V.1.toScheme ⟶ (universalQuasiFiniteOpen n d).toScheme), ?_⟩
  have hpaste := ((IsOpenImmersion.isPullback_lift_id _ (universalQuasiFiniteOpen n d).ι
    hrange).paste_vert hgeom.flip).flip
  rw [Category.id_comp] at hpaste
  exact hpaste

end AlgebraicGeometry

end
