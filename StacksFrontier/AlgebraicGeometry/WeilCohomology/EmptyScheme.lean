module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSmooth
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of the empty scheme

Let `H^*` be a Weil cohomology theory over `k` with coefficient field `F` of characteristic
zero. Then `H^*(∅) = 0`. This is the empty case of Stacks 0FHF; the two clauses for a nonempty
`X` are in `StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme`.

The proof is the source's. Let `E` be the empty scheme over `k` and let `Y` be a smooth
projective scheme over `k` of positive dimension `d`. The projection `E ×_k Y ⟶ E` is an
isomorphism of schemes, both sides being empty, so axiom `(B)(a)` for the product `E ×_k Y` reads
`H^*(E) ⊗_F H^*(Y) ≅ H^*(E)`, whence
`dim_F H^*(E) · dim_F H^*(Y) = dim_F H^*(E)`. It therefore suffices to produce two distinct
degrees in which `H^*(Y)` is nonzero, and the source produces them from Poincaré duality and
the nonvanishing of `H^0(Y)`: the unit of `H^0(Y)` is nonzero by the second clause of this same
tag, `Stacks.WeilCohomology.one_ne_zero_of_nonempty`, and axiom `(A)(b)`, the perfectness of
the cup-product trace pairing `H^0(Y) × H^{2d}(Y)(d) → F`, then forces `H^{2d}(Y)(d)` to be
nonzero as well. Since `d > 0` the degrees `0` and `2d` are distinct, so `dim_F H^*(Y) ≥ 2` and
`dim_F H^*(E) = 0`.

The scheme `Y` is the projective line `ℙ¹_k`, built by gluing two affine lines in
`StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLine`. It is nonempty, smooth and
proper over `k` of relative dimension one:
`AlgebraicGeometry.projectiveLine_smooth`, `AlgebraicGeometry.projectiveLine_isProper` and
`AlgebraicGeometry.projectiveLine_relativeDimension`. Its grading, its trace pairing, its cup
product and its cycle class map are the values at `ℙ¹_k` of the data `(D1)`, `(D2)`, `(D3)` and
of the axioms `(A)` and `(C)(b)`, which are quantified over the smooth projective schemes over
`k` exactly as in the source.

The source's opening step — that axiom `(B)(a)` for `E ×_k E` makes `H^*(E)` at most
one-dimensional — is subsumed by this count and is not needed.

## Main results

* `Stacks.WeilCohomology.subsingleton_cohomology_of_empty`: the total cohomology of the empty
  smooth projective scheme over `k` vanishes.
* `Stacks.WeilCohomology.one_lt_finrank_cohomology_of_pos_dim`: the total cohomology of a
  nonempty smooth projective scheme over `k` of positive dimension has dimension at least two
  over `F`.

## Implementation notes

As in the rest of this directory the cohomological data is supplied as explicit arguments
rather than through a bundled Weil cohomology theory. The dictionary:

* `H` is the total cohomology `H^*(-)` of `(D1)`, and `Hcongr` is the isomorphism it induces on
  an isomorphism of schemes, which is all of its functoriality that the argument uses. `Hgr` is
  the grading by cohomological degree and `grading` the identification `H^*(T) = ⨁_i H^i(T)` of
  `(D1)`; `one` is the unit of `H^0(T)` and `cup` with `cup_one` the unit law of the cup
  product. The Tate twist of `H^{2d}(T)(d)` is suppressed, as elsewhere in this directory: it is
  a tensor product with a one-dimensional `F`-vector space and changes no dimension.
* `kunneth` is axiom `(B)(a)`, `finiteDimensional` the finiteness clause of axiom `(A)`, and
  `pairing` with `pairing_perfect` is axiom `(A)(b)` in the one pair of complementary degrees
  that is used, `0` and `2d`. `cycleClass` is `(D2)`, `pushforward` is the pushforward `(D3)`
  furnishes by Poincaré duality, and `cycleClass_pushforward` is axiom `(C)(b)`, all three for a
  zero-cycle on a scheme of dimension `d`, which is the one degree the argument reaches. Each is
  quantified over the smooth projective schemes over `k`, and is evaluated at the empty scheme
  `E` and at the projective line.
* Smoothness and properness of the structure morphism of `E` follow from `E` being empty, so
  they are not hypotheses; the dimension count needs the finiteness clause of axiom `(A)` at
  both `E` and the projective line, and the hypothesis `finiteDimensional` supplies it at each.
* `Hpt`, `HptZero`, `degreeZeroPoint`, `kunnethPoint`, `cycleClassPoint`, `integrationPoint`,
  `integration_cycleClassPoint` and `cycleClassPoint_mul` are the data and axioms at the base
  point, as in `StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme`; Stacks 0FHE,
  `Stacks.Weil.cycleClass_fundamentalClass_eq_one`, turns them into `γ([Spec(k)]) = 1`.
* `one_lt_finrank_cohomology_of_pos_dim` is the dimension count for one scheme of positive
  dimension, and takes that scheme's grading, pairing and cup product directly; the tagged
  theorem instantiates the quantified axioms at the projective line to produce them.
* The axioms are quantified over schemes exactly where a second scheme is needed, and no
  further: this clause reaches both the empty scheme and the projective line, so the data at a
  scheme is a family here, whereas the two clauses for a nonempty `X` in
  `StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme` reach only the given `X` and
  take the data there.
* The data and the axioms are spelled out as binders rather than projected out of a bundled
  datum because Section 45.9 has no bundle in this repository that this clause could use; the
  reasons are in the implementation notes of
  `StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme`. One of them is decisive for the
  witness in particular: both candidates put cohomology on
  `(SmoothProjective k).FullSubcategory`, whose objects carry `IsProjectiveMorphism`
  (`StacksFrontier/AlgebraicGeometry/WeilCohomology/ProjectionFormula/Setup.lean:102`), and the
  projective line is available here with properness rather than with projectivity in that
  sense, so the witness this clause constructs is not an object of that subcategory.

## References

* [Stacks Project, Tag 0FHF](https://stacks.math.columbia.edu/tag/0FHF)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u v w x

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] {F : Type v} [Field F]
  (Hpt : ℤ → Type x) [∀ i : ℤ, AddCommGroup (Hpt i)] [∀ i : ℤ, Module F (Hpt i)]
  [∀ i : ℤ, FiniteDimensional F (Hpt i)]
  (HptZero : Type x) [CommRing HptZero] [Algebra F HptZero]
  (degreeZeroPoint : Hpt 0 ≃ₗ[F] HptZero)
  (kunnethPoint : ∀ n : ℤ,
    DirectSum ℤ (fun j : ℤ ↦ TensorProduct F (Hpt j) (Hpt (n - j))) ≃ₗ[F] Hpt n)
  (cycleClassPoint : chowGroup (fieldChowSituation k) (𝟙 _) 0 →+ HptZero)
  (integrationPoint : HptZero →ₗ[F] F)
  (integration_cycleClassPoint :
    integrationPoint (cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0)) = 1)
  (cycleClassPoint_mul :
    cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) *
        cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) =
      cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0))

include degreeZeroPoint kunnethPoint integration_cycleClassPoint cycleClassPoint_mul in
/-- **The dimension count of the empty case of Stacks 0FHF.** The total cohomology of a nonempty
smooth projective scheme `Y` over `k` of positive dimension `d` has dimension at least two over
the coefficient field: the unit of `H^0(Y)` is nonzero by
`Stacks.WeilCohomology.one_ne_zero_of_nonempty`, axiom `(A)(b)` carries that nonvanishing to
`H^{2d}(Y)(d)`, and `0 ≠ 2d`. -/
theorem one_lt_finrank_cohomology_of_pos_dim [CharZero F]
    {Y : Scheme.{u}} [Nonempty (Y : Type u)]
    (pY : Y ⟶ (fieldChowSituation k).S) [Smooth pY] [IsProper pY]
    (d : ℕ) (hd0 : d ≠ 0)
    {HYtot : Type w} [AddCommGroup HYtot] [Module F HYtot] [FiniteDimensional F HYtot]
    (HY : ℤ → Type w) [∀ i, AddCommGroup (HY i)] [∀ i, Module F (HY i)]
    (grading : DirectSum ℤ HY ≃ₗ[F] HYtot)
    (pairing : HY 0 →ₗ[F] HY (2 * (d : ℤ)) →ₗ[F] F) (pairing_perfect : pairing.IsPerfPair)
    (one : HY 0) (cup : HY (2 * (d : ℤ)) →ₗ[F] HY 0 →ₗ[F] HY (2 * (d : ℤ)))
    (cup_one : ∀ a : HY (2 * (d : ℤ)), cup a one = a)
    (cycleClassY : chowGroup (fieldChowSituation k) pY 0 →+ HY (2 * (d : ℤ)))
    (pushforward : HY (2 * (d : ℤ)) →ₗ[F] HptZero)
    (cycleClass_pushforward : ∀ β,
      pushforward (cycleClassY β) =
        cycleClassPoint (properChowPushforward (fieldChowSituation k) pY (𝟙 _) pY
          (Category.comp_id pY) 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
            pY (𝟙 _) pY (Category.comp_id pY) 0) β)) :
    1 < Module.finrank F HYtot := by
  classical
  have := pairing_perfect
  have hone : one ≠ 0 :=
    one_ne_zero_of_nonempty Hpt HptZero degreeZeroPoint kunnethPoint cycleClassPoint
      integrationPoint integration_cycleClassPoint cycleClassPoint_mul pY one cup cup_one
      cycleClassY pushforward cycleClass_pushforward
  have htop : ∃ b : HY (2 * (d : ℤ)), b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hsub : ∀ f g : HY (2 * (d : ℤ)) →ₗ[F] F, f = g := fun f g ↦
      LinearMap.ext fun x ↦ by rw [hcon x, map_zero, map_zero]
    exact hone (LinearMap.IsPerfPair.bijective_left pairing |>.injective (hsub _ _))
  obtain ⟨b, hb⟩ := htop
  have hdZ : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd0
  have hne : (0 : ℤ) ≠ 2 * (d : ℤ) := by omega
  set f : F × F →ₗ[F] DirectSum ℤ HY :=
    (DirectSum.lof F ℤ HY 0).comp
        ((LinearMap.toSpanSingleton F (HY 0) one).comp (LinearMap.fst F F F)) +
      (DirectSum.lof F ℤ HY (2 * (d : ℤ))).comp
        ((LinearMap.toSpanSingleton F (HY (2 * (d : ℤ))) b).comp (LinearMap.snd F F F)) with hf
  have hfinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    simp only [hf, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.coe_comp,
      Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply] at hy
    have h1 := congrArg (DirectSum.component F ℤ HY 0) hy
    have h2 := congrArg (DirectSum.component F ℤ HY (2 * (d : ℤ))) hy
    simp only [map_add, DirectSum.component.lof_self, DirectSum.component.of, hne.symm,
      ↓reduceDIte, add_zero, map_zero, hne, zero_add,
      LinearMap.toSpanSingleton_apply] at h1 h2
    refine Prod.ext ?_ ?_
    · simpa [smul_eq_zero, hone] using h1
    · simpa [smul_eq_zero, hb] using h2
  have hinj : Function.Injective (grading.toLinearMap.comp f) := grading.injective.comp hfinj
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_self] at hle

include degreeZeroPoint kunnethPoint integration_cycleClassPoint cycleClassPoint_mul in
/-- **Stacks Project, Tag 0FHF**, the empty case: the total cohomology of the empty smooth
projective scheme over `k` is the zero `F`-vector space.

Axiom `(B)(a)` for the product `E ×_k Y`, with `Y` the projective line, together with the
isomorphism `E ×_k Y ≅ E` of schemes over `k`, gives `H^*(E) ⊗_F H^*(Y) ≅ H^*(E)`, so
`dim_F H^*(E) · dim_F H^*(Y) = dim_F H^*(E)`; and `dim_F H^*(Y) ≥ 2` by
`Stacks.WeilCohomology.one_lt_finrank_cohomology_of_pos_dim`, whose hypotheses are the values at
the projective line of the quantified axioms. The projective line is nonempty, smooth and proper
over `k` of relative dimension one, by `AlgebraicGeometry.projectiveLine_smooth`,
`AlgebraicGeometry.projectiveLine_isProper` and
`AlgebraicGeometry.projectiveLine_relativeDimension`. -/
@[stacks 0FHF "the empty case: `H^*(∅) = 0`"]
theorem subsingleton_cohomology_of_empty [CharZero F]
    (H : Scheme.{u} → Type w) [∀ T, AddCommGroup (H T)] [∀ T, Module F (H T)]
    (Hcongr : ∀ {T T' : Scheme.{u}}, (T ≅ T') → (H T' ≃ₗ[F] H T))
    (Hgr : Scheme.{u} → ℤ → Type w)
    [∀ (T : Scheme.{u}) (i : ℤ), AddCommGroup (Hgr T i)]
    [∀ (T : Scheme.{u}) (i : ℤ), Module F (Hgr T i)]
    (grading : ∀ T : Scheme.{u}, DirectSum ℤ (Hgr T) ≃ₗ[F] H T)
    (finiteDimensional : ∀ (T : Scheme.{u}) (pT : T ⟶ (fieldChowSituation k).S),
      Smooth pT → IsProper pT → FiniteDimensional F (H T))
    (kunneth : ∀ (T T' : Scheme.{u}) (pT : T ⟶ (fieldChowSituation k).S)
      (pT' : T' ⟶ (fieldChowSituation k).S), Smooth pT → IsProper pT → Smooth pT' →
      IsProper pT' → (TensorProduct F (H T) (H T') ≃ₗ[F] H (pullback pT pT')))
    (pairing : ∀ (T : Scheme.{u}) (pT : T ⟶ (fieldChowSituation k).S) (_ : Smooth pT)
      (_ : IsProper pT) (d : ℕ), AlgebraicGeometry.RelativeDimension pT d →
      (Hgr T 0 →ₗ[F] Hgr T (2 * (d : ℤ)) →ₗ[F] F))
    (pairing_perfect : ∀ (T : Scheme.{u}) (pT : T ⟶ (fieldChowSituation k).S)
      (hsm : Smooth pT) (hpr : IsProper pT) (d : ℕ)
      (hd : AlgebraicGeometry.RelativeDimension pT d),
      (pairing T pT hsm hpr d hd).IsPerfPair)
    (one : ∀ T : Scheme.{u}, Hgr T 0)
    (cup : ∀ (T : Scheme.{u}) (i : ℤ), Hgr T i →ₗ[F] Hgr T 0 →ₗ[F] Hgr T i)
    (cup_one : ∀ (T : Scheme.{u}) (i : ℤ) (a : Hgr T i), cup T i a (one T) = a)
    (cycleClass : ∀ (T : Scheme.{u}) (pT : T ⟶ (fieldChowSituation k).S) (_ : Smooth pT)
      (_ : IsProper pT) (d : ℕ), AlgebraicGeometry.RelativeDimension pT d →
      (chowGroup (fieldChowSituation k) pT 0 →+ Hgr T (2 * (d : ℤ))))
    (pushforward : ∀ (T : Scheme.{u}) (pT : T ⟶ (fieldChowSituation k).S) (_ : Smooth pT)
      (_ : IsProper pT) (d : ℕ), AlgebraicGeometry.RelativeDimension pT d →
      (Hgr T (2 * (d : ℤ)) →ₗ[F] HptZero))
    (cycleClass_pushforward : ∀ (T : Scheme.{u}) (pT : T ⟶ (fieldChowSituation k).S)
      (hsm : Smooth pT) (hpr : IsProper pT) (d : ℕ)
      (hd : AlgebraicGeometry.RelativeDimension pT d)
      (β : chowGroup (fieldChowSituation k) pT 0),
      letI : Smooth pT := hsm
      letI : IsProper pT := hpr
      pushforward T pT hsm hpr d hd (cycleClass T pT hsm hpr d hd β) =
        cycleClassPoint (properChowPushforward (fieldChowSituation k) pT (𝟙 _) pT
          (Category.comp_id pT) 0
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
            pT (𝟙 _) pT (Category.comp_id pT) 0) β))
    {E : Scheme.{u}} [IsEmpty (E : Type u)] (pE : E ⟶ (fieldChowSituation k).S) :
    Subsingleton (H E) := by
  set pY : projectiveLine k ⟶ (fieldChowSituation k).S := projectiveLine k ↘ Spec (.of k) with hpY
  have hsmY : Smooth pY := projectiveLine_smooth k
  have hprY : IsProper pY := projectiveLine_isProper k
  have hdY : AlgebraicGeometry.RelativeDimension pY 1 := projectiveLine_relativeDimension k
  have : FiniteDimensional F (H E) :=
    finiteDimensional E pE inferInstance inferInstance
  have : FiniteDimensional F (H (projectiveLine k)) :=
    finiteDimensional (projectiveLine k) pY hsmY hprY
  have hY : 1 < Module.finrank F (H (projectiveLine k)) :=
    one_lt_finrank_cohomology_of_pos_dim Hpt HptZero degreeZeroPoint kunnethPoint cycleClassPoint
      integrationPoint integration_cycleClassPoint cycleClassPoint_mul pY 1 one_ne_zero
      (Hgr (projectiveLine k)) (grading (projectiveLine k))
      (pairing (projectiveLine k) pY hsmY hprY 1 hdY)
      (pairing_perfect (projectiveLine k) pY hsmY hprY 1 hdY) (one (projectiveLine k))
      (cup (projectiveLine k) (2 * (1 : ℤ))) (cup_one (projectiveLine k) (2 * (1 : ℤ)))
      (cycleClass (projectiveLine k) pY hsmY hprY 1 hdY)
      (pushforward (projectiveLine k) pY hsmY hprY 1 hdY)
      (cycleClass_pushforward (projectiveLine k) pY hsmY hprY 1 hdY)
  have habs : TensorProduct F (H E) (H (projectiveLine k)) ≃ₗ[F] H E :=
    (kunneth E (projectiveLine k) pE pY inferInstance inferInstance hsmY hprY).trans
      (Hcongr (asIso (pullback.fst pE pY))).symm
  refine (Module.finrank_zero_iff (R := F)).mp ?_
  have h := habs.finrank_eq
  rw [Module.finrank_tensorProduct] at h
  nlinarith

end Stacks.WeilCohomology

end
