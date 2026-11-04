module

public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Localization.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Branches.Completion
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.Henselian.HenselizationMinimalPrimes
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRing

/-!
# The henselization as a subring of the completion

Let `(R, 𝔪)` be a Noetherian local ring with henselization `Rʰ`. The canonical `R`-algebra map
`Rʰ → R^∧` into the `𝔪`-adic completion is injective, so `Rʰ` is a subring of `R^∧`. When `R`
is moreover a domain, every element of `Rʰ` is algebraic over `R`.

When `R` is in addition a G-ring, the converse holds and `Rʰ` is *exactly* the set of elements of
`R^∧` algebraic over the fraction field of `R`.

## Main definitions

* `IsLocalRing.henselizationToAdicCompletion` is the canonical `R`-algebra map `Rʰ → R^∧`, the
  map of the universal property of the henselization applied to the henselian local ring `R^∧`.

## Main results

* `IsLocalRing.isNoetherianRing_henselization` and
  `IsLocalRing.exists_ringEquiv_adicCompletion_henselization` recall the two properties of a
  henselization of a Noetherian local ring that make it a subring of the completion.
* `IsLocalRing.injective_henselizationToAdicCompletion`: the canonical map is injective.
* `IsLocalRing.isAlgebraic_of_isHenselization`: over a local domain every element of a
  henselization is algebraic.
* `IsLocalRing.finite_setOf_aeval_eq_zero_of_isHenselization`: over a Noetherian local domain a
  nonzero polynomial has only finitely many roots in a henselization, because the henselization
  is a subring of its fibre over the generic point, which is a finite product of field
  extensions of the fraction field.
* `IsLocalRing.range_henselizationToAdicCompletion_eq_setOf_isAlgebraic`: the conclusion of the
  example — for a Noetherian local domain which is a G-ring, `Rʰ ⊆ R^∧` is exactly the set of
  elements of `R^∧` algebraic over the fraction field.

## Implementation notes

Algebraicity over the fraction field `K` of `R` is formalized as `IsAlgebraic R f`, a nonzero
polynomial relation with coefficients in `R`: because `R` is a domain the two notions agree, a
relation over `K` becoming one over `R` after clearing denominators. This is also the form in
which the source states the condition, as `aₙfⁿ + ⋯ + a₀ = 0` with `aᵢ ∈ R` and `aₙ ≠ 0`.

The converse inclusion — that an element of `R^∧` algebraic over `R` lies in `Rʰ` when `R` is a
G-ring — rests on the approximation property of a Noetherian local G-ring, Theorem 07QZ, whose
own proof goes through Popescu's Theorem 07GC. Both are proved in this library, 07QZ as
`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`, so nothing is assumed here. Everything
in the source's argument is proved: both inclusions, the factorization of the étale solution
through `Rʰ`, and the limiting argument from the finiteness of the root set.

What this argument needs of Theorem 07QZ is the part of its conclusion that lives in `R^∧`: an
étale `R → R'`, a solution in `R'`, and an `R`-algebra map `τ : R' → R^∧` local at the
distinguished prime `𝔪'`, modulo whose `N`-th power the congruence holds — the element being
approximated is an element of `R^∧`. That is the embedding `R' ⊂ R'_{𝔪'} ⊂ Rʰ ⊂ R^∧` of the
remark preceding the theorem in the source, and it is what
`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing` supplies alongside the
`StacksDraft.ArtinApproximation.LocalEtaleSolution` structure. The structure's own congruence is
instead read inside `(R'_{𝔪'})^∧`, which is the form Lemma 0CAR states; the two are one
statement, because
`StacksDraft.ArtinApproximation.exists_algHom_approx_of_localEtaleSolution` converts the second
into the first along the comparison `R^∧ ≅ (R'_{𝔪'})^∧`. So there is no second named spelling of
07QZ in this file.

The étale solution is pushed into `Rʰ` by `exists_algHom_eq_of_etale` below: an `R`-algebra map
from an étale `R`-algebra into `R^∧` factors through `Rʰ`, because both `Rʰ` and `R^∧` are
henselian local with residue field `κ(𝔪)` and a map out of an étale algebra into a henselian local
ring is determined by the residue-field point it induces
(`HenselianLocalRing.existsUnique_algHom_residue_of_etale`). The source instead reads this off its
remark that the embedding factors as `R' ⊂ R'_{𝔪'} ⊂ Rʰ ⊂ R^∧`; it is proved here rather than
taken from that remark, so all that is used of Theorem 07QZ is a map into `R^∧`.

## References

* [Stacks Project, Tag 0A1W](https://stacks.math.columbia.edu/tag/0A1W)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w

namespace IsLocalRing

/-! ### The two properties of a henselization of a Noetherian local ring -/

/-- **A henselization of a Noetherian local ring is Noetherian** (Stacks 06LJ, recalled in the
discussion of Stacks 0A1W). -/
@[stacks 0A1W "the henselization is Noetherian; this is Stacks 06LJ, proved in the library as
`isNoetherianRing_of_isHenselization`", ega "IV 18.6.6" "(v)", sga "4 VIII 4.1"]
theorem isNoetherianRing_henselization (R : Type u) (Rh : Type v) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R (ResidueField R) Rh] : IsNoetherianRing Rh :=
  isNoetherianRing_of_isHenselization (A := R) (B := Rh) (ResidueField R)

/-- **The completion of a henselization is the completion of the base** (Stacks 06LJ, recalled in
the discussion of Stacks 0A1W): `R^∧ → (Rʰ)^∧` is an isomorphism. -/
@[stacks 0A1W "the map on completions `R^∧ → (Rʰ)^∧` is an isomorphism; this is Stacks 06LJ,
proved in the library as `exists_ringEquiv_adicCompletion_of_isHenselization`"]
theorem exists_ringEquiv_adicCompletion_henselization (R Rh : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R (ResidueField R) Rh] :
    ∃ e : AdicCompletion (maximalIdeal R) R ≃+* AdicCompletion (maximalIdeal Rh) Rh,
      ∀ x : R, e (algebraMap R (AdicCompletion (maximalIdeal R) R) x) =
        algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh) (algebraMap R Rh x) :=
  exists_ringEquiv_adicCompletion_of_isHenselization R Rh

/-! ### The canonical map from the henselization to the completion -/

section ToAdicCompletion

/-- An `A`-algebra map out of a henselization of `A` into an `A`-algebra flat over `A` is
flat. -/
private theorem flat_of_isHenselization_algHom' {A : Type u} {Ah : Type v} {B : Type w}
    [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah] [CommRing B]
    [Algebra A Ah] [Algebra A B] [Module.Flat A B]
    [IsHenselization A (ResidueField A) Ah] (f : Ah →ₐ[A] B) : f.toRingHom.Flat := by
  let : Algebra Ah B := f.toRingHom.toAlgebra
  have : IsScalarTower A Ah B := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  let : Algebra (ULift.{u} Ah) B := ULift.algebra' Ah B
  have : IsScalarTower A (ULift.{u} Ah) B :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := ULift.{u} Ah) (A := B) fun x => by
      show algebraMap A B x = f (algebraMap A Ah x)
      exact (f.commutes x).symm
  exact Module.Flat.ulift_left_iff.mp
    (_root_.flat_restrictScalars_of_ind_etale A (ULift.{u} Ah) B
      (IsHenselization.ind_etale (R := A) (L := ResidueField A) (Rh := Ah)))

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (Rh : Type v) [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
  [IsHenselization R (ResidueField R) Rh]

/-- The `𝔪`-adic completion of a Noetherian local ring is a henselian local ring. -/
@[sga "3 X 4.0" "partial"]
theorem henselianLocalRing_adicCompletion_of_isNoetherianRing :
    HenselianLocalRing (AdicCompletion (maximalIdeal R) R) :=
  henselianLocalRing_adicCompletion R (maximalIdeal R).fg_of_isNoetherianRing

/-- **The canonical map from a henselization into the completion.** The completion of a
Noetherian local ring is a henselian local ring, so the universal property of the henselization
provides a unique local `R`-algebra map `Rʰ → R^∧`. -/
noncomputable def henselizationToAdicCompletion :
    Rh →ₐ[R] AdicCompletion (maximalIdeal R) R :=
  letI : HenselianLocalRing (AdicCompletion (maximalIdeal R) R) :=
    henselianLocalRing_adicCompletion_of_isNoetherianRing R
  letI : IsLocalHom (algebraMap R Rh) := IsHenselization.isLocalHom (L := ResidueField R)
  letI : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isLocalRing_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  letI : IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
    AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  HenselianLocalRing.indEtaleAlgHom
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh))
    (IsHenselization.residueField_map_bijective (R := R) (Rh := Rh)).2

/-- The canonical map `Rʰ → R^∧` is a local ring map. -/
theorem isLocalHom_henselizationToAdicCompletion :
    letI : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
      AdicCompletion.isLocalRing_of_fg (maximalIdeal R).fg_of_isNoetherianRing
    IsLocalHom (henselizationToAdicCompletion R Rh).toRingHom := by
  have : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isLocalRing_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  have : IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
    AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  exact isLocalHom_of_isHenselization_algHom (henselizationToAdicCompletion R Rh)

/-- **A henselization of a Noetherian local ring is a subring of the completion** (Stacks 0A1W).
The canonical map `Rʰ → R^∧` is faithfully flat, because it is flat — the completion is flat over
`R` and the henselization is ind-étale over `R` — and local; hence it is injective. -/
@[stacks 0A1W "the henselization is a subring of the completion: the canonical map is injective"]
theorem injective_henselizationToAdicCompletion :
    Function.Injective (henselizationToAdicCompletion R Rh) := by
  have : IsLocalRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isLocalRing_of_fg (maximalIdeal R).fg_of_isNoetherianRing
  set ι := henselizationToAdicCompletion R Rh
  let : Algebra Rh (AdicCompletion (maximalIdeal R) R) := ι.toRingHom.toAlgebra
  have : Module.Flat Rh (AdicCompletion (maximalIdeal R) R) := flat_of_isHenselization_algHom' ι
  have : IsLocalHom (algebraMap Rh (AdicCompletion (maximalIdeal R) R)) :=
    isLocalHom_henselizationToAdicCompletion R Rh
  have : Module.FaithfullyFlat Rh (AdicCompletion (maximalIdeal R) R) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective Rh (AdicCompletion (maximalIdeal R) R)

end ToAdicCompletion

/-! ### Elements of a henselization are algebraic -/

/-- An étale algebra over a field is finite: it is a finite product of finite extensions. -/
private theorem module_finite_of_etale_over_field {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] [Algebra.Etale K A] : Module.Finite K A := by
  classical
  obtain ⟨I, hI, L, hLfield, hLalg, e, hLfinite⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  have : Finite I := hI
  let : ∀ i, Field (L i) := hLfield
  let : ∀ i, Algebra K (L i) := hLalg
  have (i : I) : Module.Finite K (L i) := (hLfinite i).1
  have : Module.Finite K (∀ i, L i) := Module.Finite.pi
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- **Every element of an étale algebra over a domain is algebraic over it.** After inverting the
base the algebra becomes étale, hence finite, over the fraction field, and the base change map is
injective because the fraction field is flat over the domain. -/
theorem isAlgebraic_of_etale {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.Etale R A] (x : A) : IsAlgebraic R x := by
  let K := FractionRing R
  let D := TensorProduct R K A
  let : Algebra K D := Algebra.TensorProduct.leftAlgebra
  have : Algebra.Etale K D := Algebra.Etale.baseChange R A K
  have : Module.Finite K D := module_finite_of_etale_over_field
  let j : A →ₐ[R] D := Algebra.TensorProduct.includeRight
  have hj : Function.Injective j :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K)
  exact (isAlgebraic_algHom_iff j hj).mp ((IsFractionRing.isAlgebraic_iff R K D).mpr
    ((Algebra.IsAlgebraic.of_finite K D).isAlgebraic (j x)))

/-- Every element of an ind-étale algebra comes from an étale stage of a presentation. -/
private theorem exists_etale_stage_eq (R : Type u) [CommRing R] (S : Type w) [CommRing S]
    [Algebra R S] (hind : (CommAlgCat.etale.{w} R).ind.{w} (CommAlgCat.of R S)) (x : S) :
    ∃ (A : CommAlgCat.{w} R) (_ : Algebra.Etale R (A : Type w))
      (f : A ⟶ CommAlgCat.of R S) (a : A), f.hom a = x := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  obtain ⟨j, a, ha⟩ := CommAlgCat.exists_app_eq pres.isColimit x
  exact ⟨pres.diag.obj j, hpres j, pres.ι.app j, a, ha⟩

/-- **Every element of a henselization of a local domain is algebraic over it** (Stacks 0A1W).
A henselization is a filtered colimit of étale algebras, so the element comes from an étale
stage, where `isAlgebraic_of_etale` applies. -/
@[stacks 0A1W "every element of the henselization is algebraic over `R`, equivalently over its
fraction field"]
theorem isAlgebraic_of_isHenselization (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    (Rh : Type v) [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R (ResidueField R) Rh] (g : Rh) : IsAlgebraic R g := by
  classical
  obtain ⟨A, hA, f, a, ha⟩ := exists_etale_stage_eq R (ULift.{u} Rh)
    (IsHenselization.ind_etale (R := R) (L := ResidueField R) (Rh := Rh)) (ULift.up g)
  have : Algebra.Etale R (A : Type max u v) := hA
  let φ : (A : Type max u v) →ₐ[R] Rh :=
    (ULift.algEquiv : ULift.{u} Rh ≃ₐ[R] Rh).toAlgHom.comp f.hom
  have hφ : φ a = g := congrArg ULift.down ha
  exact hφ ▸ (isAlgebraic_of_etale (R := R) (A := (A : Type max u v)) a).algHom φ

/-! ### Finiteness of the root set in a henselization -/

/-- **A nonzero polynomial has only finitely many roots in a henselization of a Noetherian local
domain** (Stacks 0A1W). The henselization is flat over the base, so it injects into its fibre
over the generic point, and that fibre is a finite product of field extensions of the fraction
field by Stacks 0AH1; a nonzero polynomial has finitely many roots in each factor. -/
@[stacks 0A1W "`Rʰ ⊆ Rʰ ⊗_R K` and `Rʰ ⊗_R K` is a finite product of field extensions of `K`;
hence a nonzero polynomial over `R` has only finitely many roots in `Rʰ`"]
theorem finite_setOf_aeval_eq_zero_of_isHenselization (R : Type u) [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsNoetherianRing R] (Rh : Type u) [CommRing Rh] [IsLocalRing Rh]
    [Algebra R Rh] [IsHenselization R (ResidueField R) Rh]
    (p : Polynomial R) (hp : p ≠ 0) :
    {g : Rh | Polynomial.aeval g p = 0}.Finite := by
  classical
  have : IsNoetherianRing Rh := isNoetherianRing_henselization R Rh
  have : Module.Flat R Rh := IsHenselization.flat (L := ResidueField R)
  obtain ⟨r, q, hq, hlo, hmain, -, -⟩ :=
    IsFilteredColimitEtale.exists_fiber_algEquiv_pi_residueField
      (Stacks.Henselization.Shared.isFilteredColimitEtale_of_ind R Rh
        (IsHenselization.ind_etale_of_universe_le (R := R) (ResidueField R) (Rh := Rh)))
      (⊥ : Ideal R)
  have : ∀ i, (q i).IsPrime := hq
  let : ∀ i, Algebra (⊥ : Ideal R).ResidueField (q i).ResidueField := fun i =>
    (Ideal.ResidueField.map (⊥ : Ideal R) (q i) (algebraMap R Rh) (hlo i).over).toAlgebra
  obtain ⟨⟨e⟩, -, -⟩ := hmain
  set K := (⊥ : Ideal R).ResidueField
  set T := TensorProduct R K Rh
  -- `p` stays nonzero over the fraction field `K`.
  have hinjRK : Function.Injective (algebraMap R K) := FaithfulSMul.algebraMap_injective R K
  set P := p.map (algebraMap R K) with hP
  have hPne : P ≠ 0 := (Polynomial.map_ne_zero_iff hinjRK).2 hp
  -- The henselization injects into the fibre over the generic point.
  let j : Rh →ₐ[R] T := Algebra.TensorProduct.includeRight
  have hj : Function.Injective j :=
    Algebra.TensorProduct.includeRight_injective hinjRK
  -- A root of `p` in `Rh` becomes a root of `P` in the fibre.
  have hroot (g : Rh) (hg : Polynomial.aeval g p = 0) :
      Polynomial.aeval (j g) P = 0 := by
    rw [hP, Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply, hg, map_zero]
  -- In each factor a nonzero polynomial over a field has finitely many roots.
  have hfactor (i : Fin r) : {y : (q i).ResidueField | Polynomial.aeval y P = 0}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot ((Polynomial.map_ne_zero_iff
      (FaithfulSMul.algebraMap_injective K (q i).ResidueField)).2 hPne)).subset fun y hy => ?_
    simpa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] using hy
  have : ∀ i : Fin r, Finite {y : (q i).ResidueField // Polynomial.aeval y P = 0} :=
    fun i => (hfactor i).to_subtype
  -- Hence finitely many roots in the product, and so in `Rh`.
  let Φ : {g : Rh // Polynomial.aeval g p = 0} →
      ∀ i : Fin r, {y : (q i).ResidueField // Polynomial.aeval y P = 0} := fun g i =>
    ⟨e (j g.1) i, by
      simpa [hroot g.1 g.2] using Polynomial.aeval_algHom_apply
        ((Pi.evalAlgHom K (fun i => (q i).ResidueField) i).comp e.toAlgHom) (j g.1) P⟩
  have hΦ : Function.Injective Φ := fun g g' h =>
    Subtype.ext (hj (e.injective (funext fun i => congrArg Subtype.val (congrFun h i))))
  exact Set.finite_coe_iff.mp (Finite.of_injective Φ hΦ)

/-! ### The algebraic elements of the completion are exactly the henselization -/

/-- A one-variable polynomial read as a polynomial system in one variable: evaluating the
corresponding multivariate polynomial at `a` is evaluating the original at `a 0`. -/
private theorem aeval_aeval_X_zero {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] (p : Polynomial R) (a : Fin 1 → A) :
    MvPolynomial.aeval a
        (Polynomial.aeval (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) R) p) =
      Polynomial.aeval (a 0) p := by
  rw [← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]

section Conclusion

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (Rh : Type u) [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
  [IsHenselization R (ResidueField R) Rh]

/-- The canonical map `Rʰ → R^∧`, as a local map in the `AlgHom` form that
`IsLocalRing.ResidueField.mapAlgHom` wants. -/
private theorem isLocalHom_henselizationToAdicCompletion' :
    IsLocalHom (henselizationToAdicCompletion R Rh) :=
  let := isLocalHom_henselizationToAdicCompletion R Rh
  ⟨fun a ha => IsLocalHom.map_nonunit
    (f := (henselizationToAdicCompletion R Rh).toRingHom) a ha⟩

/-- **An `R`-algebra map from an étale `R`-algebra into `R^∧` factors through `Rʰ`.** Both `Rʰ`
and `R^∧` are henselian local rings with residue field `κ(𝔪)`, and a map out of an étale algebra
into a henselian local ring is determined by the residue-field point it induces; transporting the
point of `R^∧` to `Rʰ` along the induced isomorphism of residue fields and lifting it there
produces the factorization. -/
private theorem exists_algHom_eq_of_etale
    (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra.Etale R R']
    (τ : R' →ₐ[R] AdicCompletion (maximalIdeal R) R) :
    ∃ φ : R' →ₐ[R] Rh, ∀ y : R', henselizationToAdicCompletion R Rh (φ y) = τ y := by
  have : HenselianLocalRing Rh :=
    IsHenselization.henselian (R := R) (L := ResidueField R) (Rh := Rh)
  have : HenselianLocalRing (AdicCompletion (maximalIdeal R) R) :=
    henselianLocalRing_adicCompletion R (maximalIdeal R).fg_of_isNoetherianRing
  have : IsLocalHom (algebraMap R Rh) := IsHenselization.isLocalHom (L := ResidueField R)
  have := isLocalHom_henselizationToAdicCompletion' R Rh
  set emb := henselizationToAdicCompletion R Rh
  -- The residue field of `R^∧` is `κ(𝔪)`.
  set eT : ResidueField R ≃+* ResidueField (AdicCompletion (maximalIdeal R) R) :=
    RingEquiv.ofBijective _ (AdicCompletion.residueField_map_bijective R)
  -- `emb` is compatible with the two identifications of `κ(𝔪)`.
  have hpt : ∀ y : ResidueField R,
      ResidueField.mapAlgHom emb (ResidueField.map (algebraMap R Rh) y) = eT y := by
    intro y
    obtain ⟨r, rfl⟩ := residue_surjective y
    show ResidueField.mapAlgHom emb (ResidueField.map (algebraMap R Rh) (residue R r)) =
      ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) (residue R r)
    rw [ResidueField.map_residue, ResidueField.map_residue,
      ResidueField.mapAlgHom_residue, emb.commutes r]
  -- The residue-field point of `R'` determined by `τ`, and its transport to `Rʰ`.
  set ψT : R' →ₐ[R] ResidueField (AdicCompletion (maximalIdeal R) R) :=
    { toRingHom := (residue (AdicCompletion (maximalIdeal R) R)).comp
        (τ : R' →+* AdicCompletion (maximalIdeal R) R)
      commutes' := fun r => by
        show residue (AdicCompletion (maximalIdeal R) R) (τ (algebraMap R R' r)) = _
        rw [τ.commutes r]
        rfl }
  have hψTapp : ∀ y : R', ψT y = residue (AdicCompletion (maximalIdeal R) R) (τ y) :=
    fun _ => rfl
  set ψh : R' →ₐ[R] ResidueField Rh :=
    { toRingHom := (ResidueField.map (algebraMap R Rh)).comp
        ((eT.symm : ResidueField (AdicCompletion (maximalIdeal R) R) →+* ResidueField R).comp
          (ψT : R' →+* ResidueField (AdicCompletion (maximalIdeal R) R)))
      commutes' := fun r => by
        show ResidueField.map (algebraMap R Rh) (eT.symm (ψT (algebraMap R R' r))) = _
        have h1 : ψT (algebraMap R R' r) = eT (residue R r) := by
          rw [hψTapp, τ.commutes r]
          show _ = ResidueField.map (algebraMap R (AdicCompletion (maximalIdeal R) R))
            (residue R r)
          rw [ResidueField.map_residue]
        rw [h1, eT.symm_apply_apply, ResidueField.map_residue]
        rfl }
  have hψhapp : ∀ y : R', ψh y =
      ResidueField.map (algebraMap R Rh) (eT.symm (ψT y)) := fun _ => rfl
  -- Lift the point to `Rʰ`, then compare the two lifts over `R^∧`.
  obtain ⟨φ, hφ, -⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale
    (R := R) (A := R') (S := Rh) ψh
  obtain ⟨σ, -, huniq⟩ := HenselianLocalRing.existsUnique_algHom_residue_of_etale
    (R := R) (A := R') (S := AdicCompletion (maximalIdeal R) R) ψT
  have hcomp : emb.comp φ = τ := by
    refine (huniq _ fun y => ?_).trans (huniq τ fun y => (hψTapp y).symm).symm
    show residue (AdicCompletion (maximalIdeal R) R) (emb (φ y)) = ψT y
    rw [← ResidueField.mapAlgHom_residue emb (φ y), hφ y, hψhapp y, hpt (eT.symm (ψT y)),
      eT.apply_symm_apply]
  exact ⟨φ, fun y => AlgHom.congr_fun hcomp y⟩

/-- **Stacks 0A1W, the conclusion of the example.** Let `R` be a Noetherian local domain with
fraction field `K` which is a G-ring. Then the henselization `Rʰ`, viewed as a subring of the
completion `R^∧`, is exactly the set of elements of `R^∧` that are algebraic over `K`.

The inclusion `⊆` is `isAlgebraic_of_isHenselization`. For `⊇`, Theorem 07QZ produces, for each
`N`, a root `g` of the same polynomial in an étale extension of `R`; that root is pushed into `Rʰ`
by `exists_algHom_eq_of_etale` and satisfies `f - g ∈ (𝔪 R^∧)^N`. Since the polynomial has only
finitely many roots in `Rʰ` and `⋂_N (𝔪 R^∧)^N = 0`, one of them must equal `f`. -/
@[stacks 0A1W "the conclusion of the example, with NO carried hypotheses: for a Noetherian local
domain `R` which is a G-ring, the image of the henselization in `R^∧` is exactly the set of
elements of `R^∧` algebraic over `R`. Algebraicity over the fraction field `K` is `IsAlgebraic
R`, the source's own form `a_n f^n + ⋯ + a_0 = 0` with `a_i ∈ R` and `a_n ≠ 0`, which over a
domain is equivalent to algebraicity over `K`. Both inclusions are proved: `⊆` is
`isAlgebraic_of_isHenselization`, and `⊇` uses Theorem 07QZ
(`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`, unconditional), the factorization of
its étale solution through `Rʰ` (`exists_algHom_eq_of_etale`, proved here rather than taken
from the source's remark that the embedding factors as `R' ⊂ R'_{𝔪'} ⊂ Rʰ ⊂ R^∧`), the
finiteness of the root set in `Rʰ` (`finite_setOf_aeval_eq_zero_of_isHenselization`) and Krull's
intersection theorem in `R^∧`. The other clauses of this tag -- that `Rʰ` is Noetherian, that
`R^∧ → (Rʰ)^∧` is an isomorphism, that `Rʰ → R^∧` is injective, and the two statements about
`Rʰ ⊗_R K` -- are registered separately above."]
theorem range_henselizationToAdicCompletion_eq_setOf_isAlgebraic [IsDomain R]
    (hG : IsGRing R) :
    Set.range (henselizationToAdicCompletion R Rh) =
      {x : AdicCompletion (maximalIdeal R) R | IsAlgebraic R x} := by
  classical
  set T := AdicCompletion (maximalIdeal R) R
  set emb := henselizationToAdicCompletion R Rh
  refine Set.eq_of_subset_of_subset ?_ ?_
  · rintro x ⟨g, rfl⟩
    exact (isAlgebraic_of_isHenselization R Rh g).algHom emb
  · rintro x ⟨p, hp, hpx⟩
    -- The roots of `p` in `Rʰ` form a finite set.
    have hfin : {g : Rh | Polynomial.aeval g p = 0}.Finite :=
      finite_setOf_aeval_eq_zero_of_isHenselization R Rh p hp
    -- Theorem 07QZ, in the one-variable case, pushed into `Rʰ`.
    have hstep : ∀ N : ℕ, ∃ g : Rh, Polynomial.aeval g p = 0 ∧ x - emb g ∈ maximalIdeal T ^ N := by
      intro N
      obtain ⟨s, -, τ, hτlocal, happrox, -⟩ :=
        Stacks.Smoothing.exists_localEtaleSolution_of_isGRing hG
          (fun _ : Fin 1 => Polynomial.aeval (MvPolynomial.X (0 : Fin 1)) p) N
          (fun _ => x) (fun _ => by rwa [aeval_aeval_X_zero])
      obtain ⟨φ, hφ⟩ := exists_algHom_eq_of_etale R Rh s.carrier τ
      refine ⟨φ (s.sol 0), ?_, ?_⟩
      · have h1 := s.eval_sol 0
        rw [← MvPolynomial.aeval_def, aeval_aeval_X_zero] at h1
        rw [Polynomial.aeval_algHom_apply, h1, map_zero]
      · have hloc : s.prime.map (τ : s.carrier →+* T) ≤ maximalIdeal T :=
          Ideal.map_le_iff_le_comap.2 fun y hy => (hτlocal y).1 hy
        have hle : (s.prime ^ N).map (τ : s.carrier →+* T) ≤ maximalIdeal T ^ N := by
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono hloc N
        rw [hφ (s.sol 0)]
        exact hle (happrox 0)
    -- Krull's intersection theorem in the Noetherian local ring `R^∧`.
    by_contra hxnot
    have hex : ∀ g : Rh, ∃ n : ℕ, x - emb g ∉ maximalIdeal T ^ n := by
      intro g
      by_contra! hall
      refine hxnot ⟨g, (sub_eq_zero.mp ?_).symm⟩
      have hmem : x - emb g ∈ ⨅ i : ℕ, maximalIdeal T ^ i := Submodule.mem_iInf _ |>.2 hall
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal T)
        (inferInstance : (maximalIdeal T).IsMaximal).ne_top] at hmem
      simpa using hmem
    choose ν hν using hex
    obtain ⟨M, hM⟩ := (hfin.image ν).bddAbove
    obtain ⟨g, hg0, hgmem⟩ := hstep M
    exact hν g (Ideal.pow_le_pow_right
      (hM (Set.mem_image_of_mem ν (show g ∈ {g : Rh | Polynomial.aeval g p = 0} from hg0)))
      hgmem)

end Conclusion

end IsLocalRing

end
