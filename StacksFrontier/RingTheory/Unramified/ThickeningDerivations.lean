module

public import StacksFrontier.RingTheory.Unramified.Thickening

/-!
# Derivations along the universal first-order thickening

Let `R → A → B` be ring maps and let `B' → B` be a universal first-order thickening of `B` over
`A` in the sense of `Algebra.Extension.IsUniversalFirstOrderThickening`
([Stacks Project, Tag 04EC]). For a module `M` carrying compatible actions of `A`, `B'` and `B`,
restriction of derivations along `A → B'` is a **bijection**

`Derivation R B' M ≃ Derivation R A M`.

This is the derivation form of the second assertion of [Stacks Project, Tag 04EF], which says
that the canonical map `B ⊗_A Ω_{A/R} → B ⊗_{B'} Ω_{B'/R}` is an isomorphism; the two statements
are each other's transport across the universal property of Kähler differentials and the
adjunction between base change and restriction of scalars.

## Main results

* `Algebra.Extension.IsUniversalFirstOrderThickening.bijective_compAlgebraMap`: restriction of
  derivations along `A → B'` is bijective.
* `Algebra.Extension.IsUniversalFirstOrderThickening.derivationEquiv` packages it as an
  equivalence, with `derivationEquiv_symm_apply_algebraMap` recording that the inverse really is
  an extension: the derivation it produces restricts to the given one.
* `Algebra.Extension.IsUniversalFirstOrderThickening.bijective_comp_kaehlerDifferentialMap`: the
  same statement for `A`-linear maps out of `Ω_{A/R}`, which is the form the proof runs on.

## Implementation notes

The whole content is
`Algebra.Extension.IsUniversalFirstOrderThickening.formallyUnramified_ring_and_bijective_map`
(Tag 04EF). Write `θ : B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R]` for the canonical map that
it asserts to be bijective. Then for any `M` as above:

* `LinearMap.liftBaseChangeEquiv` identifies `B`-linear maps out of each base change with linear
  maps out of the un-based-changed module, i.e. `Hom_B(B ⊗[A] Ω[A⁄R], M) ≃ Hom_A(Ω[A⁄R], M)` and
  likewise over `B'`;
* under that identification, precomposition with `θ` becomes precomposition with
  `KaehlerDifferential.map R R A P.Ring`, because `θ (1 ⊗ ω) = 1 ⊗ (map ω)`; and
* precomposition with a bijective linear map is bijective.

That gives `bijective_comp_kaehlerDifferentialMap`, and
`KaehlerDifferential.linearMapEquivDerivation` turns it into the statement about derivations,
the square commuting by `KaehlerDifferential.map_D`.

Why this is worth stating separately: consumers at the level of schemes meet the universal
property of `Ω_{X/S}` in derivation form — `Stacks.Smooth.existsUnique_linearMap_comp_pullbackD`
identifies the `Γ(T, ⊤)`-linear maps out of `Γ(a^*Ω_{X/S}, ⊤)` with the `Γ(S, V)`-derivations of
`Γ(X, W)` — so the bijection they need from the affine theory is the one on derivations, not the
isomorphism of base-changed differentials. Tag 04EF's own proof contains the two halves of this
bijection internally (`exists_derivation_restrict_eq` and the injectivity half in
`StacksFrontier.RingTheory.Unramified.Thickening`), but both are `private` there, so they are
unavailable; nothing is re-proved here, the public Tag 04EF being transported instead.

The hypotheses on `M` are the four module structures and the four scalar towers that let both
sides of the bijection be written at all. No universe restriction is needed: unlike the
`TrivSqZeroExt` argument inside Tag 04EF's proof, which builds a ring out of `M` and so needs
`M` in the universe of `B'`, the transport above only moves `M` through `Hom`-sets.

## References

* [Stacks Project, Tag 04EF](https://stacks.math.columbia.edu/tag/04EF)
* [Stacks Project, Tag 04EC](https://stacks.math.columbia.edu/tag/04EC)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.Extension.IsUniversalFirstOrderThickening

variable (R : Type u) {A : Type v} {B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] {P : Extension.{w} A B}
  (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [Module P.Ring M] [Module B M]
  [IsScalarTower R A M] [IsScalarTower A B M] [IsScalarTower A P.Ring M]
  [IsScalarTower R P.Ring M] [IsScalarTower P.Ring B M]

/-- The canonical map `B ⊗_A Ω_{A/R} → B ⊗_{B'} Ω_{B'/R}` whose bijectivity is the second
assertion of [Stacks Project, Tag 04EF]. It is the `B`-linear extension of
`ω ↦ 1 ⊗ KaehlerDifferential.map R R A P.Ring ω`, and is named here only so that the two
statements below can refer to it. -/
noncomputable abbrev cotangentBaseChangeMap :
    B ⊗[A] Ω[A⁄R] →ₗ[B] B ⊗[P.Ring] Ω[P.Ring⁄R] :=
  (((TensorProduct.mk P.Ring B Ω[P.Ring⁄R] 1).restrictScalars A).comp
    (KaehlerDifferential.map R R A P.Ring)).liftBaseChange B

/-- Precomposition with a surjective `B`-linear map is injective, and precomposition with a
bijective one is bijective: the inverse is precomposition with the inverse map. -/
private lemma bijective_comp_of_bijective {N₁ N₂ : Type*} [AddCommGroup N₁] [Module B N₁]
    [AddCommGroup N₂] [Module B N₂] (θ : N₁ →ₗ[B] N₂) (hθ : Function.Bijective θ) :
    Function.Bijective fun l : N₂ →ₗ[B] M => l.comp θ := by
  let e : N₁ ≃ₗ[B] N₂ := LinearEquiv.ofBijective θ hθ
  refine ⟨fun l₁ l₂ hl => LinearMap.ext fun x => ?_, fun l => ⟨l.comp e.symm.toLinearMap, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := hθ.2 x
    exact LinearMap.congr_fun hl y
  · exact LinearMap.ext fun x => congrArg l (e.symm_apply_apply x)

omit [Module R M] [IsScalarTower R A M] [IsScalarTower R P.Ring M] in
/-- **Linear maps out of `Ω_{A/R}` with values in a `B`-module are exactly those factoring
through `Ω_{B'/R}`.** Precomposition with `KaehlerDifferential.map R R A P.Ring` is a bijection
from the `B'`-linear maps `Ω_{B'/R} → M` to the `A`-linear maps `Ω_{A/R} → M`. -/
theorem bijective_comp_kaehlerDifferentialMap (hP : P.IsUniversalFirstOrderThickening) :
    Function.Bijective fun Φ : Ω[P.Ring⁄R] →ₗ[P.Ring] M =>
      (Φ.restrictScalars A).comp (KaehlerDifferential.map R R A P.Ring) := by
  -- the bijection on base-changed `Hom`s supplied by Tag 04EF
  have hcomp := bijective_comp_of_bijective (B := B) M (cotangentBaseChangeMap R (P := P))
    (hP.formallyUnramified_ring_and_bijective_map R).2
  -- transport it across `LinearMap.liftBaseChangeEquiv` on both sides
  have hsq : ∀ Φ : Ω[P.Ring⁄R] →ₗ[P.Ring] M,
      LinearMap.liftBaseChangeEquiv B ((Φ.restrictScalars A).comp
          (KaehlerDifferential.map R R A P.Ring))
        = (LinearMap.liftBaseChangeEquiv B Φ).comp (cotangentBaseChangeMap R (P := P)) := by
    intro Φ
    refine (LinearMap.liftBaseChangeEquiv (R := A) (A := B)).symm.injective
      (LinearMap.ext fun ω => ?_)
    simp [LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.liftBaseChange_tmul]
  have hcompose : Function.Bijective fun Φ : Ω[P.Ring⁄R] →ₗ[P.Ring] M =>
      LinearMap.liftBaseChangeEquiv B ((Φ.restrictScalars A).comp
        (KaehlerDifferential.map R R A P.Ring)) := by
    rw [funext hsq]
    exact hcomp.comp (LinearMap.liftBaseChangeEquiv (R := P.Ring) (A := B)).bijective
  exact ((LinearMap.liftBaseChangeEquiv (R := A) (A := B)).bijective.of_comp_iff' _).1 hcompose

/-- **Stacks Project, Tag 04EF, in derivation form.** For `B' → B` a universal first-order
thickening of `B` over `A` and `M` a module with compatible `A`-, `B'`- and `B`-actions,
restriction of derivations along `A → B'` is a bijection
`Derivation R B' M ≃ Derivation R A M`. -/
theorem bijective_compAlgebraMap (hP : P.IsUniversalFirstOrderThickening) :
    Function.Bijective fun D : Derivation R P.Ring M => D.compAlgebraMap A := by
  have hsq : ∀ Φ : Ω[P.Ring⁄R] →ₗ[P.Ring] M,
      (KaehlerDifferential.linearMapEquivDerivation R P.Ring Φ).compAlgebraMap A
        = KaehlerDifferential.linearMapEquivDerivation R A
            ((Φ.restrictScalars A).comp (KaehlerDifferential.map R R A P.Ring)) := by
    intro Φ
    refine Derivation.ext fun a => ?_
    simp [KaehlerDifferential.map_D]
  have hcompose : Function.Bijective fun Φ : Ω[P.Ring⁄R] →ₗ[P.Ring] M =>
      (KaehlerDifferential.linearMapEquivDerivation R P.Ring Φ).compAlgebraMap A := by
    rw [funext hsq]
    exact (KaehlerDifferential.linearMapEquivDerivation R A (M := M)).bijective.comp
      (bijective_comp_kaehlerDifferentialMap R M hP)
  exact (Function.Bijective.of_comp_iff _
    (KaehlerDifferential.linearMapEquivDerivation R P.Ring (M := M)).bijective).1 hcompose

/-- Restriction of derivations along `A → B'` as an equivalence
`Derivation R B' M ≃ Derivation R A M`, for `B' → B` a universal first-order thickening of `B`
over `A`. -/
noncomputable def derivationEquiv (hP : P.IsUniversalFirstOrderThickening) :
    Derivation R P.Ring M ≃ Derivation R A M :=
  Equiv.ofBijective _ (bijective_compAlgebraMap R M hP)

/-- `derivationEquiv` sends a derivation `D` of `B'` to its restriction `D.compAlgebraMap A`. -/
@[simp]
theorem derivationEquiv_apply (hP : P.IsUniversalFirstOrderThickening)
    (D : Derivation R P.Ring M) : derivationEquiv R M hP D = D.compAlgebraMap A :=
  rfl

/-- The derivation of `B'` produced by the inverse of `derivationEquiv` from a derivation `D` of
`A` agrees with `D` on the image of `A → B'`. -/
@[simp]
theorem derivationEquiv_symm_apply_algebraMap (hP : P.IsUniversalFirstOrderThickening)
    (D : Derivation R A M) (a : A) :
    (derivationEquiv R M hP).symm D (algebraMap A P.Ring a) = D a :=
  congrFun (congrArg (fun E : Derivation R A M => (E : A → M))
    ((derivationEquiv R M hP).apply_symm_apply D)) a

end Algebra.Extension.IsUniversalFirstOrderThickening

end
