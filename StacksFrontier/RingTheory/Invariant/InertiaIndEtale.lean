module

public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.Invariant.Inertia
public import StacksFrontier.RingTheory.Invariant.Primes

/-!
# Inertia invariants are ind-étale locally

Let `A` be a normal domain with fraction field `K`, let `L / K` be a possibly infinite Galois
extension with group `G = Gal(L/K)`, and let `B` be the integral closure of `A` in `L`. For a
prime `q` of `B` the inertia subgroup is
`I = {σ ∈ G | σ q = q and σ ≡ id modulo q}`, which is Mathlib's `Ideal.inertia`. The localization
of `B ^ I` at the prime below `q` is then a filtered colimit of étale `A`-algebras.

## Main results

* `IsIntegralClosure.isFilteredColimitOfEtale_localization_fixedPoints_inertia` (Stacks 0BSU):
  the inertia invariants of the integral closure, localized at the prime below `q`, are a
  filtered colimit of étale `A`-algebras.

## Implementation notes

The Stacks proof writes `L` as the filtered colimit of its finite Galois subextensions and
appeals to the stability of ind-étaleness under iterated filtered colimits (Stacks 0BSJ). That
route is unavailable at the generality wanted here, because the colimit formulation of 0BSJ in
this library is stated for a base ring in `Type`. Instead the ind-étale conclusion is obtained
from the factorization criterion `CommRingCat.ind_under_iff_exists_factorization`: it suffices
that every map of a finitely presented `A`-algebra into the localization factors through an
étale `A`-algebra. Such a factorization is produced by descending the finitely many
denominators and numerators involved to a single finite Galois subextension `E / K` — possible
because restriction carries the inertia group at `q` onto the inertia group at its contraction
(Stacks 0BSX) — applying the finite-group statement (Stacks 0BST) there, and then inverting
the one remaining denominator. The construction keeps everything in a single universe `u`,
which is what the predicate `IsFilteredColimitOfEtaleHom` requires of its base and target.

The inertia condition `σ ≡ id modulo q` already forces `σ q = q`
(`Ideal.inertia_le_stabilizer`), so `Ideal.inertia` expresses both clauses of the displayed
definition of `I`, and `FixedPoints.subalgebra` expresses `B ^ I`.

## References

* [Stacks Project, Tag 0BSU](https://stacks.math.columbia.edu/tag/0BSU)
-/

@[expose] public section

namespace IsIntegralClosure

open CategoryTheory

universe u

/-- A map `φ` from a finitely presented `A`-algebra `P` into `S` factors through the
localization of `R` away from `d`, as soon as `fTarget d` is a unit and each image
`φ (ψ (X i))` of a generator of `P` is `fTarget (a i) / fTarget d` for some `a i : R`. -/
private lemma exists_factorization_through_away
    (A R S P : Type u) [CommRing A] [CommRing R] [CommRing S] [CommRing P]
    [Algebra A R] [Algebra A S] [Algebra A P]
    (fTarget : R →ₐ[A] S) (hinj : Function.Injective fTarget)
    (d : R) (hd : IsUnit (fTarget d))
    (n : ℕ) (ψ : MvPolynomial (Fin n) A →ₐ[A] P) (hψ : Function.Surjective ψ)
    (φ : P →ₐ[A] S) (a : Fin n → R)
    (ha : ∀ i, fTarget (a i) = fTarget d * φ (ψ (MvPolynomial.X i))) :
    ∃ θ : P →ₐ[A] Localization.Away d,
      (IsLocalization.Away.liftAlgHom (f := fTarget) d hd).comp θ = φ := by
  classical
  let μ₀ : Localization.Away d →ₐ[A] S := IsLocalization.Away.liftAlgHom (f := fTarget) d hd
  let du : IsUnit (algebraMap R (Localization.Away d) d) :=
    IsLocalization.map_units _ ⟨d, Submonoid.mem_powers _⟩
  let v : Localization.Away d := ↑du.unit⁻¹
  have hvmul : algebraMap R (Localization.Away d) d * v = 1 := du.mul_val_inv
  let θ₀ : MvPolynomial (Fin n) A →ₐ[A] Localization.Away d :=
    MvPolynomial.aeval fun i => algebraMap R (Localization.Away d) (a i) * v
  have hμalg (x : R) : μ₀ (algebraMap R (Localization.Away d) x) = fTarget x :=
    IsLocalization.Away.lift_eq d hd x
  have hvB : μ₀ v = ↑hd.unit⁻¹ := by
    refine hd.mul_left_cancel ?_
    rw [hd.mul_val_inv, ← hμalg d, ← map_mul, hvmul, map_one]
  have hcomp : μ₀.comp θ₀ = φ.comp ψ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    change μ₀ (θ₀ (MvPolynomial.X i)) = φ (ψ (MvPolynomial.X i))
    dsimp only [θ₀]
    rw [MvPolynomial.aeval_X, map_mul, hμalg, hvB, ha i, mul_right_comm, hd.mul_val_inv, one_mul]
  have hμ₀inj : Function.Injective μ₀.toRingHom := by
    apply IsLocalization.injective_of_map_algebraMap_zero
      (M := Submonoid.powers d) (T := S) (Localization.Away d) μ₀.toRingHom
    intro x hx
    change μ₀ (algebraMap R (Localization.Away d) x) = 0 at hx
    rw [hμalg] at hx
    rw [hinj (hx.trans (map_zero fTarget).symm), map_zero]
  have hkerθ : RingHom.ker ψ.toRingHom ≤ RingHom.ker θ₀.toRingHom := by
    intro r hr
    refine RingHom.mem_ker.mpr (hμ₀inj ?_)
    change μ₀ (θ₀ r) = μ₀ 0
    rw [map_zero, ← AlgHom.comp_apply, hcomp, AlgHom.comp_apply]
    exact (congrArg φ (RingHom.mem_ker.mp hr)).trans (map_zero φ)
  refine ⟨ψ.liftOfSurjective hψ θ₀ hkerθ, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hψ x
  rw [AlgHom.comp_apply, AlgHom.liftOfSurjective_apply, ← AlgHom.comp_apply, hcomp,
    AlgHom.comp_apply]

/-- A map into a ring `S` that already factors through the localization of `R` away from one
element `d` factors through an étale `A`-algebra, provided some `g : R` with `fTarget g` a unit
makes `R` away from `g` étale over `A`: inverting the image of `d` in that étale algebra is
again étale, and the two localizations are compared by the universal property. -/
private lemma exists_etale_factorization_of_isUnit
    (A R S P : Type u) [CommRing A] [CommRing R] [CommRing S] [CommRing P]
    [Algebra A R] [Algebra A S] [Algebra A P]
    (fTarget : R →ₐ[A] S) (d g : R) (hd : IsUnit (fTarget d)) (hg : IsUnit (fTarget g))
    (hEtaleAway : Algebra.Etale A (Localization.Away g))
    (φ : P →ₐ[A] S) (θ : P →ₐ[A] Localization.Away d)
    (hθ : (IsLocalization.Away.liftAlgHom (f := fTarget) d hd).comp θ = φ) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T),
      Algebra.Etale A T ∧
        ∃ (g' : P →ₐ[A] T) (h : T →ₐ[A] S), h.comp g' = φ := by
  classical
  let μ₀ : Localization.Away d →ₐ[A] S := IsLocalization.Away.liftAlgHom (f := fTarget) d hd
  let R₀ := Localization.Away g
  let dR₀ : R₀ := algebraMap R R₀ d
  let R₁ := Localization.Away dR₀
  have hEtale₀ : Algebra.Etale A R₀ := hEtaleAway
  have hEtale₁ : Algebra.Etale R₀ R₁ := Algebra.Etale.of_isLocalizationAway dR₀
  have hEtale : Algebra.Etale A R₁ := Algebra.Etale.comp A R₀ R₁
  let iota : R →ₐ[A] R₁ :=
    (IsScalarTower.toAlgHom A R₀ R₁).comp (IsScalarTower.toAlgHom A R R₀)
  let μg : R₀ →ₐ[A] S := IsLocalization.Away.liftAlgHom (f := fTarget) g hg
  have hμgalg (x : R) : μg (algebraMap R R₀ x) = fTarget x :=
    IsLocalization.Away.lift_eq g hg x
  have hunitdR₀ : IsUnit (μg dR₀) := hμgalg d ▸ hd
  let h : R₁ →ₐ[A] S := IsLocalization.Away.liftAlgHom (f := μg) dR₀ hunitdR₀
  have hunitIota : IsUnit (iota d) := by
    change IsUnit (algebraMap R₀ R₁ dR₀)
    exact IsLocalization.map_units R₁ ⟨dR₀, Submonoid.mem_powers _⟩
  let ν : Localization.Away d →ₐ[A] R₁ := IsLocalization.Away.liftAlgHom (f := iota) d hunitIota
  have hνalg (x : R) : ν (algebraMap R (Localization.Away d) x) = iota x :=
    IsLocalization.Away.lift_eq d hunitIota x
  have hhalg (x : R₀) : h (algebraMap R₀ R₁ x) = μg x :=
    IsLocalization.Away.lift_eq dR₀ hunitdR₀ x
  have hμalg (x : R) : μ₀ (algebraMap R (Localization.Away d) x) = fTarget x :=
    IsLocalization.Away.lift_eq d hd x
  have hcompLoc : (h.toRingHom.comp ν.toRingHom) = μ₀.toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers d) (RingHom.ext fun x => by
      change h (ν (algebraMap R (Localization.Away d) x)) =
        μ₀ (algebraMap R (Localization.Away d) x)
      rw [hνalg]
      change h (algebraMap R₀ R₁ (algebraMap R R₀ x)) = _
      rw [hhalg, hμgalg, hμalg])
  refine ⟨R₁, inferInstance, inferInstance, hEtale, ν.comp θ, h, Eq.trans ?_ hθ⟩
  apply AlgHom.toRingHom_injective
  exact congrArg (fun k : Localization.Away d →+* S => k.comp θ.toRingHom) hcompLoc

/-- The ind-étale factorization criterion for a localization at a prime, in the form it is
applied: if every finite subset of `C` lies in the image of an injective `A`-algebra map from
some `R` that also carries an element `g` avoiding `p` with `R` away from `g` étale over `A`,
then every map of a finitely presented `A`-algebra into `Localization.AtPrime p` factors
through an étale `A`-algebra. A common denominator for the images of the generators is chosen
in `C`, pulled back to `R` together with the numerators, and the two localizations of `R` are
compared. -/
private lemma exists_etale_factorization_of_finsetDescent
    (A C : Type u) [CommRing A] [CommRing C] [NoZeroDivisors C] [Algebra A C]
    (p : Ideal C) [p.IsPrime]
    (hdesc : ∀ s : Finset C, ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R)
      (fC : R →ₐ[A] C), Function.Injective fC ∧ (∀ x ∈ s, ∃ y : R, fC y = x) ∧
        ∃ g : R, fC g ∉ p ∧ Algebra.Etale A (Localization.Away g))
    (P : Type u) [CommRing P] [Algebra A P] [Algebra.FinitePresentation A P]
    (φ : P →ₐ[A] Localization.AtPrime p) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra A T),
      Algebra.Etale A T ∧
        ∃ (g : P →ₐ[A] T) (h : T →ₐ[A] Localization.AtPrime p), h.comp g = φ := by
  classical
  let B := Localization.AtPrime p
  obtain ⟨n, ψ, hψ, _⟩ := Algebra.FinitePresentation.out (R := A) (A := P)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite p.primeCompl
    (fun i : Fin n => φ (ψ (MvPolynomial.X i)))
  have hd' : ∀ i : Fin n, ∃ x : C,
      algebraMap C B x = algebraMap C B (d : C) * φ (ψ (MvPolynomial.X i)) := fun i =>
    (hd i).imp fun _ hx => by simpa only [Algebra.smul_def] using hx
  choose a ha using hd'
  obtain ⟨R, _, _, fC, hfCinj, hrep, g, hg, hEtaleAway⟩ :=
    hdesc (insert (d : C) (Finset.univ.image a))
  obtain ⟨d0, hd0⟩ := hrep (d : C) (Finset.mem_insert_self _ _)
  choose a0 ha0 using fun i => hrep (a i) (Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  let fTarget : R →ₐ[A] B := (IsScalarTower.toAlgHom A C B).comp fC
  have hCinj : Function.Injective (algebraMap C B) :=
    IsLocalization.injective B p.primeCompl_le_nonZeroDivisors
  have hfTargetInj : Function.Injective fTarget := fun x y hxy => hfCinj (hCinj hxy)
  have hden : fTarget d0 = algebraMap C B (d : C) := congrArg (algebraMap C B) hd0
  have hunitd : IsUnit (fTarget d0) := hden ▸ IsLocalization.map_units B d
  have hunitg : IsUnit (fTarget g) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff B p (fC g)).mpr hg
  have ha' : ∀ i, fTarget (a0 i) = fTarget d0 * φ (ψ (MvPolynomial.X i)) := fun i => by
    have hnum : fTarget (a0 i) = algebraMap C B (a i) := congrArg (algebraMap C B) (ha0 i)
    rw [hnum, ha i, hden]
  obtain ⟨θ, hμθ⟩ := exists_factorization_through_away A R B P fTarget hfTargetInj d0
    hunitd n ψ hψ φ a0 ha'
  exact exists_etale_factorization_of_isUnit A R B P fTarget d0 g hunitd hunitg
    hEtaleAway φ θ hμθ

variable (A K L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsFractionRing A K] [IsGalois K L]

/-- The action of `Gal(L/K)` on the integral closure of `A` in `L`. -/
noncomputable local instance galAction :
    _root_.MulSemiringAction Gal(L/K) (integralClosure A L) :=
  IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)

omit [IsDomain A] [IsIntegrallyClosed A] in
/-- The action of `Gal(L/K)` on the integral closure is the restriction of the action on `L`. -/
lemma coe_galSmul (σ : Gal(L/K)) (x : integralClosure A L) :
    ((σ • x : integralClosure A L) : L) = σ (x : L) :=
  algebraMap_galRestrict_apply A σ x

/-- The Galois action on the integral closure commutes with the `A`-algebra structure. -/
noncomputable local instance galSMulCommClass :
    SMulCommClass Gal(L/K) A (integralClosure A L) :=
  ⟨fun σ a b => by
    simp only [Algebra.smul_def, smul_mul']
    congr 1
    exact (galRestrict A K L (integralClosure A L) σ).commutes a⟩

variable (E₀ : FiniteGaloisIntermediateField K L)

/-- A finite Galois subextension is Galois over `K`. -/
local instance inertiaStageIsGalois : IsGalois K E₀.toIntermediateField := E₀.isGalois

/-- `A` acts on `L` through a finite Galois subextension. -/
local instance inertiaStageTower : IsScalarTower A E₀.toIntermediateField L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The integral closure of `A` in a finite Galois subextension maps into the integral closure
of `A` in `L`. -/
noncomputable def inertiaStageHom :
    integralClosure A E₀.toIntermediateField →ₐ[A] integralClosure A L :=
  (IsScalarTower.toAlgHom A E₀.toIntermediateField L).mapIntegralClosure

/-- The algebra structure on the integral closure of `A` in `L` over the integral closure of `A`
in a finite Galois subextension, induced by `inertiaStageHom`. -/
noncomputable local instance inertiaStageAlgebra :
    Algebra (integralClosure A E₀.toIntermediateField) (integralClosure A L) :=
  (inertiaStageHom A K L E₀).toRingHom.toAlgebra

/-- `inertiaStageHom` is a map of `A`-algebras. -/
local instance inertiaStageTowerBase :
    IsScalarTower A (integralClosure A E₀.toIntermediateField) (integralClosure A L) :=
  IsScalarTower.of_algebraMap_eq fun z => ((inertiaStageHom A K L E₀).commutes z).symm

/-- `inertiaStageHom` is compatible with the inclusions into `L`. -/
local instance inertiaStageTowerTop :
    IsScalarTower (integralClosure A E₀.toIntermediateField) (integralClosure A L) L :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The Galois group of a finite Galois subextension acts on the integral closure of `A` in it. -/
noncomputable local instance inertiaStageGalAction :
    _root_.MulSemiringAction Gal(E₀.toIntermediateField/K)
      (integralClosure A E₀.toIntermediateField) :=
  IsIntegralClosure.MulSemiringAction A K E₀.toIntermediateField
    (integralClosure A E₀.toIntermediateField)

/-- A finite Galois subextension has the integral closure of `A` in it as a subring with
fraction field the subextension. -/
noncomputable local instance inertiaStageIsFractionRing :
    IsFractionRing (integralClosure A E₀.toIntermediateField) E₀.toIntermediateField :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K E₀.toIntermediateField
    (integralClosure A E₀.toIntermediateField)

/-- **Stacks 0BSX at a finite Galois stage.** Restriction to a finite Galois subextension
carries the inertia group at `q` onto the inertia group at the contraction of `q`. Moreover
`inertiaStageHom` is equivariant along this restriction. -/
private lemma image_inertia_restrictNormalHom_stage
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    (AlgEquiv.restrictNormalHom E₀.toIntermediateField :
        Gal(L/K) →* Gal(E₀.toIntermediateField/K)) ''
          (q.inertia Gal(L/K) : Set Gal(L/K)) =
      ((q.under (integralClosure A E₀.toIntermediateField)).inertia
        Gal(E₀.toIntermediateField/K) : Set Gal(E₀.toIntermediateField/K)) ∧
    ∀ (τ : Gal(L/K)) (y : integralClosure A E₀.toIntermediateField),
      inertiaStageHom A K L E₀ (AlgEquiv.restrictNormalHom E₀.toIntermediateField τ • y) =
        τ • inertiaStageHom A K L E₀ y :=
  let : Algebra.IsAlgebraic A L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K L)
  let : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L) fun _ hx =>
      IsFractionRing.to_map_eq_zero_iff.mp
        ((map_eq_zero (algebraMap K L)).mp <|
          (IsScalarTower.algebraMap_apply A K L _).symm.trans hx)
  ⟨(IsIntegralClosure.image_stabilizer_and_inertia_restrictNormalHom A K
    E₀.toIntermediateField L (integralClosure A E₀.toIntermediateField)
    (integralClosure A L) q).2, fun τ y => Subtype.ext <| by
      rw [coe_galSmul]
      exact (congrArg (algebraMap E₀.toIntermediateField L)
        (coe_galSmul A K E₀.toIntermediateField _ y)).trans
          (AlgEquiv.restrictNormalHom_apply E₀.toIntermediateField τ _)⟩

/-- The inertia invariants at a finite Galois stage map injectively, by `inertiaStageHom`, into the
inertia invariants upstairs, compatibly with the structure maps from `A`. -/
private lemma exists_stage_invariant_hom (q : Ideal (integralClosure A L)) [q.IsPrime] :
    ∃ f : FixedPoints.subring (integralClosure A E₀.toIntermediateField)
          ((q.under (integralClosure A E₀.toIntermediateField)).inertia
            Gal(E₀.toIntermediateField/K)) →+*
        FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K)),
      Function.Injective f ∧
        (∀ y, (f y).1 = inertiaStageHom A K L E₀ y.1) ∧
        f.comp ((Subring.inclusion (show
            FixedPoints.subring (integralClosure A E₀.toIntermediateField)
                Gal(E₀.toIntermediateField/K) ≤
              FixedPoints.subring (integralClosure A E₀.toIntermediateField)
                ((q.under (integralClosure A E₀.toIntermediateField)).inertia
                  Gal(E₀.toIntermediateField/K)) from by
              intro x hx σ
              exact hx (σ : Gal(E₀.toIntermediateField/K)))).comp
          ((algebraMap A (integralClosure A E₀.toIntermediateField)).codRestrict
            (FixedPoints.subring (integralClosure A E₀.toIntermediateField)
              Gal(E₀.toIntermediateField/K)) (fun a => by intro σ; simp))) =
        algebraMap A
          (FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K))) := by
  classical
  set E := E₀.toIntermediateField with hE
  let B₀ := integralClosure A E
  let I₀ := (q.under B₀).inertia Gal(E/K)
  let res : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hImage : res '' (q.inertia Gal(L/K) : Set Gal(L/K)) = (I₀ : Set Gal(E/K)) :=
    (image_inertia_restrictNormalHom_stage A K L E₀ q).1
  let fB : FixedPoints.subring B₀ I₀ →+* integralClosure A L :=
    (inertiaStageHom A K L E₀).toRingHom.comp (FixedPoints.subring B₀ I₀).subtype
  have hmem : ∀ x : FixedPoints.subring B₀ I₀,
      fB x ∈ FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K)) := by
    intro x τ
    have hτ : res (τ : Gal(L/K)) ∈ I₀ :=
      (Set.ext_iff.mp hImage _).mp ⟨τ, τ.property, rfl⟩
    have hx := x.2 ⟨res (τ : Gal(L/K)), hτ⟩
    change (res (τ : Gal(L/K))) • x.1 = x.1 at hx
    change (τ : Gal(L/K)) • inertiaStageHom A K L E₀ x.1 = inertiaStageHom A K L E₀ x.1
    rw [← (image_inertia_restrictNormalHom_stage A K L E₀ q).2, hx]
  refine ⟨fB.codRestrict _ hmem, ?_, fun y => rfl, ?_⟩
  · exact fun x y hxy => Subtype.ext (Subtype.ext (FaithfulSMul.algebraMap_injective E L
      (congrArg (fun z : integralClosure A L => (z : L)) (congrArg Subtype.val hxy))))
  · exact RingHom.ext fun a => Subtype.ext ((inertiaStageHom A K L E₀).commutes a)

/-- A finite subset of the integral closure fixed by the inertia group at `q` descends to a
finite Galois subextension on which it is fixed by the inertia group at the contraction of `q`:
each element has a `inertiaStageHom`-preimage there that is inertia invariant. -/
private lemma exists_finiteGalois_stage_of_inertia_invariant_finset
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    (s : Finset (integralClosure A L))
    (hs : ∀ x ∈ s, ∀ τ : Gal(L/K), τ ∈ q.inertia Gal(L/K) → τ • x = x) :
    ∃ F : FiniteGaloisIntermediateField K L,
      ∀ x ∈ s, ∃ y : integralClosure A F.toIntermediateField,
        inertiaStageHom A K L F y = x ∧
          ∀ σ : Gal(F.toIntermediateField/K),
            σ ∈ (q.under (integralClosure A F.toIntermediateField)).inertia
              Gal(F.toIntermediateField/K) → σ • y = y := by
  classical
  let sL : Finset L := s.image (fun x : integralClosure A L => (x : L))
  refine ⟨FiniteGaloisIntermediateField.adjoin K (sL : Set L), ?_⟩
  set F := FiniteGaloisIntermediateField.adjoin K (sL : Set L) with hF
  set E := F.toIntermediateField with hE
  have hImage :
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)) ''
          (q.inertia Gal(L/K) : Set Gal(L/K)) =
        ((q.under (integralClosure A E)).inertia Gal(E/K) : Set Gal(E/K)) :=
    (image_inertia_restrictNormalHom_stage A K L F q).1
  intro x hx
  let xE : E := ⟨(x : L), by
    rw [hE, hF]
    apply FiniteGaloisIntermediateField.subset_adjoin K (sL : Set L)
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  let y : integralClosure A E := ⟨xE, by
    have hxint : IsIntegral A (algebraMap (integralClosure A L) L x) :=
      (IsIntegralClosure.isIntegral A L x).map
        (IsScalarTower.toAlgHom A (integralClosure A L) L)
    have hxint' : IsIntegral A (algebraMap E L xE) := by simpa [xE] using hxint
    exact (isIntegral_algebraMap_iff).mp hxint'⟩
  refine ⟨y, Subtype.ext rfl, ?_⟩
  intro σ hσ
  obtain ⟨τ, hτ, hres⟩ := (Set.ext_iff.mp hImage σ).mpr hσ
  refine Subtype.ext (FaithfulSMul.algebraMap_injective E L ?_)
  have h := (image_inertia_restrictNormalHom_stage A K L F q).2 τ y
  rw [hres] at h
  exact congrArg (fun z : integralClosure A L => (z : L)) (h.trans (hs x hx τ hτ))

omit [Algebra A L] [IsScalarTower A K L] in
/-- **Stacks 0BST at a finite Galois stage.** For a finite Galois subextension `E / K` the
inertia invariants of the integral closure of `A` in `E` become étale over `A` after inverting
a single element outside the prime below `q₀`. The invariants of the full Galois group are
identified with `A` because `A` is integrally closed in `K`. -/
private lemma stage_inertia_invariants_etale
    (E : IntermediateField K L) [IsGalois K E] [Algebra A E]
    [IsScalarTower A K E] [FiniteDimensional K E]
    (q₀ : Ideal (integralClosure A E)) [q₀.IsPrime] :
    ∃ g : FixedPoints.subring (integralClosure A E) (q₀.inertia Gal(E/K)),
      g ∉ q₀.comap (FixedPoints.subring (integralClosure A E)
        (q₀.inertia Gal(E/K))).subtype ∧
      RingHom.Etale
        ((algebraMap (FixedPoints.subring (integralClosure A E)
          (q₀.inertia Gal(E/K))) (Localization.Away g)).comp
        ((Subring.inclusion (show FixedPoints.subring (integralClosure A E) Gal(E/K) ≤
          FixedPoints.subring (integralClosure A E) (q₀.inertia Gal(E/K)) from by
            intro x hx σ
            exact hx σ)).comp
          ((algebraMap A (integralClosure A E)).codRestrict
            (FixedPoints.subring (integralClosure A E) Gal(E/K))
            (fun a => by intro σ; simp)))) := by
  classical
  let B₀ := integralClosure A E
  let : Algebra.IsAlgebraic A E :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K E)
  let : IsFractionRing B₀ E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K E B₀
  let : _root_.MulSemiringAction Gal(E/K) B₀ := IsIntegralClosure.MulSemiringAction A K E B₀
  let : SMulCommClass Gal(E/K) A B₀ := ⟨fun σ a b => by
    change galRestrict A K E B₀ σ (a • b) = a • galRestrict A K E B₀ σ b
    exact map_smul (galRestrict A K E B₀ σ) a b⟩
  let RG := FixedPoints.subring B₀ Gal(E/K)
  let RI := FixedPoints.subring B₀ (q₀.inertia Gal(E/K))
  have hInv : Algebra.IsInvariant A B₀ Gal(E/K) :=
    Algebra.isInvariant_of_isGalois A K E B₀
  let fA : A →+* RG :=
    (algebraMap A B₀).codRestrict RG (fun a => by intro σ; simp)
  let : Algebra A RG := fA.toAlgebra
  let fAAlg : A →ₐ[A] RG := Algebra.ofId A RG
  have hfAinj : Function.Injective fA := by
    intro x y hxy
    have hval : algebraMap A B₀ x = algebraMap A B₀ y := congrArg Subtype.val hxy
    have h := congrArg (algebraMap B₀ E) hval
    have hE : algebraMap A E x = algebraMap A E y := by
      simpa [IsScalarTower.algebraMap_apply] using h
    apply IsFractionRing.injective A K
    apply FaithfulSMul.algebraMap_injective K E
    rwa [← IsScalarTower.algebraMap_apply A K E x, ← IsScalarTower.algebraMap_apply A K E y]
  have hfAsurj : Function.Surjective fA := fun x =>
    (hInv.isInvariant x.1 fun σ => x.2 σ).imp fun _ => Subtype.ext
  let eA : A ≃ₐ[A] RG := AlgEquiv.ofBijective fAAlg ⟨hfAinj, hfAsurj⟩
  let : Algebra RG RI := (Subring.inclusion (show RG ≤ RI from fun _ hx σ => hx σ)).toAlgebra
  obtain ⟨g, hg, hEtale⟩ :=
    MulSemiringAction.exists_etale_away_fixedPoints_inertia (R := B₀)
      (G := Gal(E/K)) q₀
  let : Algebra RI (Localization.Away g) := (algebraMap RI (Localization.Away g)).toAlgebra
  let : Algebra A (Localization.Away g) :=
    ((algebraMap RG (Localization.Away g)).comp fA).toAlgebra
  let : IsScalarTower A RG (Localization.Away g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.Etale A RG := Algebra.Etale.of_equiv eA
  let : Algebra.Etale RG (Localization.Away g) := hEtale
  have hEtaleComp : Algebra.Etale A (Localization.Away g) :=
    Algebra.Etale.comp A RG (Localization.Away g)
  refine ⟨g, hg, ?_⟩
  convert (RingHom.etale_algebraMap.mpr hEtaleComp) using 1

/-- Any finite subset of the inertia invariants lies in the image of an injective `A`-algebra
map from a ring `R` attached to a single finite Galois stage, and `R` carries an element `g`
whose image avoids the prime below `q` such that `R` away from `g` is étale over `A`. This
bundles the descent to a finite Galois subextension with the finite-group statement
Stacks 0BST applied there. -/
private lemma exists_stage_subring_etale_away
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    (s : Finset (FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K)))) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra A R)
      (fC : R →ₐ[A] FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K))),
      Function.Injective fC ∧ (∀ x ∈ s, ∃ y : R, fC y = x) ∧
        ∃ g : R,
          fC g ∉ q.comap (FixedPoints.subalgebra A (integralClosure A L)
            (q.inertia Gal(L/K))).val ∧
          Algebra.Etale A (Localization.Away g) := by
  classical
  let C := FixedPoints.subalgebra A (integralClosure A L) (q.inertia Gal(L/K))
  let sB : Finset (integralClosure A L) := s.image (fun x : C => (x.1 : integralClosure A L))
  have hsB : ∀ x ∈ sB, ∀ τ : Gal(L/K), τ ∈ q.inertia Gal(L/K) → τ • x = x := by
    intro x hx τ hτ
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
    exact c.2 ⟨τ, hτ⟩
  obtain ⟨E₀, hstage⟩ :=
    exists_finiteGalois_stage_of_inertia_invariant_finset A K L q sB hsB
  set E := E₀.toIntermediateField with hE
  let B₀ := integralClosure A E
  let q₀ := q.under B₀
  let RI := FixedPoints.subring B₀ (q₀.inertia Gal(E/K))
  obtain ⟨f, hf, hfval, hcomm⟩ := exists_stage_invariant_hom A K L E₀ q
  let fA : A →+* RI :=
    (Subring.inclusion (show FixedPoints.subring B₀ Gal(E/K) ≤ RI from
        fun _ hx σ => hx (σ : Gal(E/K)))).comp
      ((algebraMap A B₀).codRestrict (FixedPoints.subring B₀ Gal(E/K))
        (fun a => by intro σ; simp))
  let : Algebra A RI := fA.toAlgebra
  let fAlg : RI →ₐ[A] C :=
    { __ := f
      commutes' := fun r => RingHom.congr_fun hcomm r }
  obtain ⟨g, hg, hEtale⟩ := stage_inertia_invariants_etale A K L E q₀
  refine ⟨RI, inferInstance, inferInstance, fAlg, hf, ?_, g, ?_, ?_⟩
  · intro x hx
    have hxB : (x.1 : integralClosure A L) ∈ sB := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hfix⟩ := hstage (x.1) hxB
    exact ⟨⟨y, fun σ => hfix σ σ.property⟩, Subtype.ext ((hfval _).trans hy)⟩
  · intro hmemp
    apply hg
    change inertiaStageHom A K L E₀ g.1 ∈ q
    rwa [← hfval g]
  · exact RingHom.etale_algebraMap.mp hEtale

/-- **Stacks 0BSU.** Let `A` be a normal domain with fraction field `K`, let `L / K` be a
possibly infinite Galois extension with group `G = Gal(L/K)`, and let `B` be the integral
closure of `A` in `L`. For a prime `q` of `B` with inertia subgroup
`I = {σ ∈ G | σ q = q and σ ≡ id modulo q}`, the localization of `B ^ I` at the prime below `q`
is a filtered colimit of étale `A`-algebras. -/
@[stacks 0BSU]
public theorem isFilteredColimitOfEtale_localization_fixedPoints_inertia
    (q : Ideal (integralClosure A L)) (hq : q.IsPrime) :
    let C := FixedPoints.subalgebra A (integralClosure A L)
      (q.inertia Gal(L/K))
    let p := q.comap C.val
    IsFilteredColimitOfEtaleHom (A := Localization.AtPrime p)
      ((algebraMap C (Localization.AtPrime p)).comp (algebraMap A C)) := by
  classical
  let C := FixedPoints.subalgebra A (integralClosure A L)
    (q.inertia Gal(L/K))
  let p := q.comap C.val
  let B := Localization.AtPrime p
  let fAB : A →+* B := (algebraMap C B).comp (algebraMap A C)
  let : q.IsPrime := hq
  let : p.IsPrime := Ideal.comap_isPrime C.val q
  change IsFilteredColimitOfEtaleHom (A := B) fAB
  rw [show fAB = algebraMap A B from (IsScalarTower.algebraMap_eq A C B).symm]
  unfold IsFilteredColimitOfEtaleHom
  rw [toAlgebra_algebraMap]
  have hind : (CommAlgCat.etale A).ind (CommAlgCat.of A B) := by
    rw [CommAlgCat.ind_etale_iff_ind_algebraMap,
      MorphismProperty.ind_iff_ind_underMk,
      CommRingCat.ind_under_iff_exists_factorization _
        (fun (X : Under (CommRingCat.of A)) (hX : CommRingCat.etale.underObj X) =>
          (RingHom.Etale.iff_flat_and_formallyUnramified.mp hX).2.2)]
    intro Pu hP f
    let _ : Algebra A Pu.right := (CommRingCat.Hom.hom Pu.hom).toAlgebra
    have hfp : Algebra.FinitePresentation A Pu.right :=
      RingHom.finitePresentation_algebraMap.mp hP
    let φ : Pu.right →ₐ[A] B :=
      { CommRingCat.Hom.hom f.right with
        commutes' := fun r => congrArg (fun h => CommRingCat.Hom.hom h r) (Under.w f) }
    obtain ⟨T, _, _, hEtale, g, h, hgh⟩ :=
      exists_etale_factorization_of_finsetDescent A C p
        (fun s => exists_stage_subring_etale_away A K L q s) Pu.right φ
    refine ⟨Under.mk (CommRingCat.ofHom (algebraMap A T)),
      Under.homMk (CommRingCat.ofHom (g : Pu.right →+* T)) ?_,
      Under.homMk (CommRingCat.ofHom (h : T →+* B)) ?_, ?_, ?_⟩
    · ext a
      exact g.commutes a
    · ext a
      exact h.commutes a
    · ext a
      exact AlgHom.congr_fun hgh a
    · change RingHom.Etale (algebraMap A T)
      exact RingHom.etale_algebraMap.mpr hEtale
  rcases hind with ⟨J, hJ, hJf, pres, hEtale⟩
  exact ⟨J, hJ, hJf, pres.diag, hEtale, pres.cocone,
    ⟨Iso.refl _⟩, ⟨pres.isColimit⟩⟩

end IsIntegralClosure

end


