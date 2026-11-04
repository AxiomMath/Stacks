module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessBaseChangeAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreFlatnessGeometricPoint

/-!
# Conditions (1) and (2) of Stacks 05WY over a pushout, with the quotient side derived

`Module.Flat.quotSMul_iff_tensor_of_isPushout` of
`StacksFrontier/AlgebraicGeometry/Spaces/FibreFlatnessBaseChangeAlgebra.lean` compares the two
conditions of Stacks 05WY over a pushout of rings, but it asks for its quotient-side structure
as about twenty separate hypotheses: algebra structures of `R/I` and `A/IA` on `R'`, `T` and
`A'` and the scalar towers relating them.  All of those are *consequences* of one fact, that `I`
dies in `R'`, together with the base-change square itself.

This file derives them.  The result,
`Module.Flat.flatQuotSMul_iff_flat_tensor_of_isPushout`, asks only for

* the base square: `R → A`, `R → R'`, the pushout `T`, and a flat `T`-algebra `A'`, with the
  towers relating them;
* an algebra structure of `R/I` on `R'` compatible with `R` — this is where "`I` dies in `R'`"
  enters, and in the intended application it comes from
  `AlgebraicGeometry.Space.map_maximalIdeal_etaleLocalRingMap_fieldFibreSpace_eq_bot`;
* flatness of `R'` over `R/I`, locality of `A'` and of `A/IA`, and that `A → A'` is local,

and concludes the equivalence in the `Module.FlatQuotSMul` spelling in which this development
states condition (1) of Stacks 05WY.

## Main results

* `Module.Flat.flatQuotSMul_iff_flat_tensor_of_isPushout`: the equivalence, with the
  quotient-side instances derived rather than assumed.

## Implementation notes

The `Module.FlatQuotSMul` spelling of condition (1) needs no bridging lemma to reach the
left-hand side of `Module.Flat.quotSMul_iff_tensor_of_isPushout`: `Module.FlatQuotSMul` restricts
scalars along `Ideal.quotientMap`, and the `Algebra (R ⧸ I) (A ⧸ IA)` instance used here is
`Ideal.Quotient.algebraQuotientOfLEComap`, whose `algebraMap` *is* that `Ideal.quotientMap`.  The
two propositions are therefore the same term.

Two things cost time here and are worth recording.

*The quotient instances must be introduced with `let`, not `have`.* The scalar towers between
them are proved by `IsScalarTower.of_algebraMap_eq'` applied to `rfl`, which needs the
*definition* of the algebra structure, and `have` discards it; with `have` the tower goals
become unprovable even though the statement is correct.

*`T` must be supplied explicitly* when applying
`Module.Flat.quotSMul_iff_tensor_of_isPushout`: the pushout does not appear in the conclusion,
only in the hypotheses, so it is not determined by unification and instance search gets stuck on
`IsScalarTower (A ⧸ IA) ?T A'`.

A third, inherited from the geometric side: inside `Ideal.map`, `rw` cannot rewrite the
homomorphism along `AlgebraicGeometry.Space.etaleLocalRingMap_comp`, because the `FunLike`
instance is a fixed argument of the application while the two spellings of the image geometric
point are only definitionally equal.  Go pointwise through `Ideal.map_eq_bot_iff_le_ker`
instead, as `AlgebraicGeometry.Space.map_maximalIdeal_etaleLocalRingMap_comp_eq_bot` does.

## References

* [Stacks Project, Tag 05WY](https://stacks.math.columbia.edu/tag/05WY)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
* [Stacks Project, Tag 0584](https://stacks.math.columbia.edu/tag/0584)
-/

@[expose] public section

open scoped TensorProduct

/-- If an ideal `I` of `R` dies in `R'`, then `IA` dies in every `A`-algebra `T` that is an
`R'`-algebra compatibly with `R`. -/
private theorem map_le_ker_algebraMap_of_le_ker {R A R' T : Type*}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing T]
    [Algebra R A] [Algebra R R'] [Algebra R T] [Algebra A T] [Algebra R' T]
    [IsScalarTower R A T] [IsScalarTower R R' T] {I : Ideal R}
    (h : I ≤ RingHom.ker (algebraMap R R')) :
    I.map (algebraMap R A) ≤ RingHom.ker (algebraMap A T) := by
  rw [Ideal.map_le_iff_le_comap]
  intro i hi
  rw [Ideal.mem_comap, RingHom.mem_ker, ← IsScalarTower.algebraMap_apply R A T,
    IsScalarTower.algebraMap_apply R R' T, RingHom.mem_ker.mp (h hi), map_zero]

/-- **Conditions (1) and (2) of Stacks 05WY over a pushout of rings, from the base square
alone.**  Let `R → A` and `R → R'` be ring homomorphisms, let `T` be the pushout `A ⊗_R R'` and
let `A'` be a flat `T`-algebra, in a commuting square with `A → A'` and `R' → A'`.  Let `I` be an
ideal of `R` which dies in `R'`, in the sense that `R'` carries an `R/I`-algebra structure
compatible with its `R`-algebra structure, and assume `R'` is flat over `R/I`, that `A'` and
`A/IA` are local and that `A → A'` is a local homomorphism.

Then for an `A`-module `M` the fibre `M/IA·M` is flat over `R/I` exactly when the base change
`A' ⊗_A M` is flat over `R'`.

This is `Module.Flat.quotSMul_iff_tensor_of_isPushout` with its quotient-side algebra structures
and scalar towers constructed instead of assumed: `I` dies in `R'`, hence in `T` and in `A'`
through `R'`, and `IA` dies in `T` and in `A'` for the same reason, which is what every one of
those instances records. -/
theorem Module.Flat.flatQuotSMul_iff_flat_tensor_of_isPushout
    {R A R' T A' M : Type*}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing T] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R T] [Algebra A T] [Algebra R' T] [Algebra T A']
    [Algebra A A'] [Algebra R' A'] [Algebra R A']
    [IsScalarTower R A T] [IsScalarTower R R' T] [IsScalarTower A T A'] [IsScalarTower R' T A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A T] [Module.Flat T A']
    (I : Ideal R)
    [Algebra (R ⧸ I) R'] [IsScalarTower R (R ⧸ I) R'] [Module.Flat (R ⧸ I) R']
    [IsLocalRing A'] [IsLocalRing (A ⧸ I.map (algebraMap R A))]
    [IsLocalHom (algebraMap A A')]
    [AddCommGroup M] [Module A M] :
    Module.FlatQuotSMul (algebraMap R A) I (I.map (algebraMap R A)) rfl M ↔
      Module.Flat R' (TensorProduct A A' M) := by
  -- `I` dies in `R'`, because `R'` is an `R/I`-algebra compatibly with `R`
  have hIR' : I ≤ RingHom.ker (algebraMap R R') := by
    intro i hi
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R (R ⧸ I) R',
      show (algebraMap R (R ⧸ I)) i = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hi, map_zero]
  -- hence `I` dies in `T` and in `A'`, through `R'`
  let instQT : Algebra (R ⧸ I) T := ((algebraMap R' T).comp (algebraMap (R ⧸ I) R')).toAlgebra
  have towQR'T : IsScalarTower (R ⧸ I) R' T := IsScalarTower.of_algebraMap_eq' rfl
  have towQT : IsScalarTower R (R ⧸ I) T :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show (algebraMap R T) r
        = (algebraMap R' T) ((algebraMap (R ⧸ I) R') ((algebraMap R (R ⧸ I)) r))
      rw [← IsScalarTower.algebraMap_apply R (R ⧸ I) R',
        ← IsScalarTower.algebraMap_apply R R' T]
  let instQA' : Algebra (R ⧸ I) A' := ((algebraMap R' A').comp (algebraMap (R ⧸ I) R')).toAlgebra
  have towQR'A' : IsScalarTower (R ⧸ I) R' A' := IsScalarTower.of_algebraMap_eq' rfl
  -- the quotient `A/IA` as an `R/I`-algebra
  let instQQ : Algebra (R ⧸ I) (A ⧸ I.map (algebraMap R A)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  -- `IA` dies in `T` and in `A'`, because `I` already dies in `R'`
  have hJT : I.map (algebraMap R A) ≤ RingHom.ker (algebraMap A T) :=
    map_le_ker_algebraMap_of_le_ker (R' := R') hIR'
  have hJA' : I.map (algebraMap R A) ≤ RingHom.ker (algebraMap A A') :=
    map_le_ker_algebraMap_of_le_ker (R' := R') hIR'
  let instJT : Algebra (A ⧸ I.map (algebraMap R A)) T :=
    (Ideal.Quotient.lift _ (algebraMap A T) fun a ha => hJT ha).toAlgebra
  let instJA' : Algebra (A ⧸ I.map (algebraMap R A)) A' :=
    (Ideal.Quotient.lift _ (algebraMap A A') fun a ha => hJA' ha).toAlgebra
  have towAJT : IsScalarTower A (A ⧸ I.map (algebraMap R A)) T :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have towAJA' : IsScalarTower A (A ⧸ I.map (algebraMap R A)) A' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have towJTA' : IsScalarTower (A ⧸ I.map (algebraMap R A)) T A' :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      induction a using Quotient.ind with | _ a =>
      show (algebraMap A A') a = (algebraMap T A') ((algebraMap A T) a)
      exact IsScalarTower.algebraMap_apply A T A' a)
  have towQJT : IsScalarTower (R ⧸ I) (A ⧸ I.map (algebraMap R A)) T :=
    IsScalarTower.of_algebraMap_eq (by
      intro r
      induction r using Quotient.ind with | _ r =>
      show (algebraMap R' T) ((algebraMap (R ⧸ I) R') ((algebraMap R (R ⧸ I)) r))
        = (algebraMap A T) ((algebraMap R A) r)
      rw [← IsScalarTower.algebraMap_apply R (R ⧸ I) R',
        ← IsScalarTower.algebraMap_apply R R' T, ← IsScalarTower.algebraMap_apply R A T])
  have towRJT : IsScalarTower R (A ⧸ I.map (algebraMap R A)) T :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R A T r).trans
        (IsScalarTower.algebraMap_apply A (A ⧸ I.map (algebraMap R A)) T _)
  have towQJA' : IsScalarTower (R ⧸ I) (A ⧸ I.map (algebraMap R A)) A' :=
    IsScalarTower.of_algebraMap_eq (by
      intro r
      induction r using Quotient.ind with | _ r =>
      show (algebraMap R' A') ((algebraMap (R ⧸ I) R') ((algebraMap R (R ⧸ I)) r))
        = (algebraMap A A') ((algebraMap R A) r)
      rw [← IsScalarTower.algebraMap_apply R (R ⧸ I) R',
        ← IsScalarTower.algebraMap_apply R R' A', ← IsScalarTower.algebraMap_apply R A A'])
  -- a local homomorphism stays local after dividing the source by an ideal
  have instLH : IsLocalHom (algebraMap (A ⧸ I.map (algebraMap R A)) A') := by
    refine ⟨fun a ha => ?_⟩
    induction a using Quotient.ind with | _ a =>
    exact IsUnit.map (Ideal.Quotient.mk _) (IsLocalHom.map_nonunit (f := algebraMap A A') a ha)
  exact Module.Flat.quotSMul_iff_tensor_of_isPushout (T := T) (M := M) I

/-- **Flatness of the upper-right corner over the fibre of the base, for a base change along a
field.**  Let `R` be a local ring, let `R → A` and `R → R'` be ring homomorphisms with `R'` a
*field* in which the maximal ideal of `R` dies, let `T` be the pushout `A ⊗_R R'` and let `A'` be
a flat `T`-algebra sitting in the commuting square.  Then `A'` is flat over the fibre `A/𝔪_R·A`.

This is the flatness input that `Module.Flat.flatQuotSMul_iff_flat_tensor_of_isPushout` asks of
its `R'`, in the geometric situation of Stacks 05WY condition (2): there `R` is `𝒪_{Z, z̄}`, `A`
is `𝒪_{Y, ȳ}`, `R'` is the étale local ring of `Spec(K)` — a field, by
`AlgebraicGeometry.Space.isField_etaleLocalRing_yoneda` — and `A'` is `𝒪_{Y_z, ȳ_z}`, flat over
the pushout by `AlgebraicGeometry.Space.cartesian_etaleStalk_tensor_flat` applied to the
*defining* square of the field fibre.

The proof is the cancellation the source's argument rests on: `A/𝔪_R·A` is the pushout of `A`
along `R → R/𝔪_R` (`Algebra.IsPushout.quotIdealMap`), so `T` is also the pushout of `A/𝔪_R·A`
along `R/𝔪_R → R'` and is therefore flat over `A/𝔪_R·A` by
`Module.Flat.quotient_of_isPushout` — flatness of `R'` over `R/𝔪_R` being automatic, since
`R/𝔪_R` is a field.  Transitivity through `T` gives the claim. -/
theorem Module.Flat.quotMaximalIdeal_of_isPushout_of_isField
    {R A R' T A' : Type*}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing T] [CommRing A'] [IsLocalRing R]
    [Algebra R A] [Algebra R R'] [Algebra R T] [Algebra A T] [Algebra R' T] [Algebra T A']
    [Algebra A A'] [Algebra R' A'] [Algebra R A']
    [IsScalarTower R A T] [IsScalarTower R R' T] [IsScalarTower A T A'] [IsScalarTower R' T A']
    [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R R' A T] [Module.Flat T A']
    [Algebra (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) A']
    [IsScalarTower A (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) A']
    (hdies : (IsLocalRing.maximalIdeal R).map (algebraMap R R') = ⊥) :
    Module.Flat (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) A' := by
  -- `𝔪_R` dies in `R'`, hence in `T` through `R'`
  have hmR' : IsLocalRing.maximalIdeal R ≤ RingHom.ker (algebraMap R R') :=
    (Ideal.map_eq_bot_iff_le_ker _).mp hdies
  have hJT : (IsLocalRing.maximalIdeal R).map (algebraMap R A)
      ≤ RingHom.ker (algebraMap A T) :=
    map_le_ker_algebraMap_of_le_ker (R' := R') hmR'
  -- `R/𝔪_R` is a field, so `R'` is automatically flat over it
  let instFieldQ : Field (R ⧸ IsLocalRing.maximalIdeal R) :=
    Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let instQR' : Algebra (R ⧸ IsLocalRing.maximalIdeal R) R' :=
    (Ideal.Quotient.lift _ (algebraMap R R') fun a ha => hmR' ha).toAlgebra
  have towQR' : IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) R' :=
    IsScalarTower.of_algebraMap_eq fun r => (Ideal.Quotient.lift_mk _ _ _).symm
  have instFlatQR' : Module.Flat (R ⧸ IsLocalRing.maximalIdeal R) R' := Module.Flat.of_free
  -- the fibre `A/𝔪_R·A`, as an algebra over `R/𝔪_R` and over `T`
  let instQQ : Algebra (R ⧸ IsLocalRing.maximalIdeal R)
      (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let instJT : Algebra (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) T :=
    (Ideal.Quotient.lift _ (algebraMap A T) fun a ha => hJT ha).toAlgebra
  let instQT : Algebra (R ⧸ IsLocalRing.maximalIdeal R) T :=
    ((algebraMap R' T).comp (algebraMap (R ⧸ IsLocalRing.maximalIdeal R) R')).toAlgebra
  have towQR'T : IsScalarTower (R ⧸ IsLocalRing.maximalIdeal R) R' T :=
    IsScalarTower.of_algebraMap_eq' rfl
  have towRQT : IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) T :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show (algebraMap R T) r = (algebraMap R' T)
        ((algebraMap (R ⧸ IsLocalRing.maximalIdeal R) R')
          ((algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) r))
      rw [← IsScalarTower.algebraMap_apply R (R ⧸ IsLocalRing.maximalIdeal R) R',
        ← IsScalarTower.algebraMap_apply R R' T]
  have towAJT : IsScalarTower A (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) T :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have towRJT : IsScalarTower R (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) T :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (IsScalarTower.algebraMap_apply R A T r).trans
        (IsScalarTower.algebraMap_apply A
          (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) T _)
  have towQJT : IsScalarTower (R ⧸ IsLocalRing.maximalIdeal R)
      (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) T :=
    IsScalarTower.of_algebraMap_eq (by
      intro r
      induction r using Quotient.ind with | _ r =>
      show (algebraMap R' T) ((algebraMap (R ⧸ IsLocalRing.maximalIdeal R) R')
          ((algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) r))
        = (algebraMap A T) ((algebraMap R A) r)
      rw [← IsScalarTower.algebraMap_apply R (R ⧸ IsLocalRing.maximalIdeal R) R',
        ← IsScalarTower.algebraMap_apply R R' T, ← IsScalarTower.algebraMap_apply R A T])
  -- `A/𝔪_R·A` is the pushout of `A` along `R → R/𝔪_R`; cancelling it leaves `T` over it
  have instPushQ : Algebra.IsPushout R (R ⧸ IsLocalRing.maximalIdeal R) A
      (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    Algebra.IsPushout.quotIdealMap (IsLocalRing.maximalIdeal R)
  have hTJ : Module.Flat (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) T :=
    Module.Flat.quotient_of_isPushout (R := R) (R₀ := R ⧸ IsLocalRing.maximalIdeal R) (A := A)
      (A₀ := A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) (R' := R') (T := T)
  -- `A/𝔪_R·A → A'` is the hypothesis instance, so it is opaque: the only way to compute it on
  -- `⟦a⟧` is the given tower `A → A/𝔪_R·A → A'`.
  have towJTA' : IsScalarTower (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) T A' :=
    IsScalarTower.of_algebraMap_eq (by
      intro a
      induction a using Quotient.ind with | _ a =>
      exact (IsScalarTower.algebraMap_apply A
          (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) A' a).symm.trans
        (IsScalarTower.algebraMap_apply A T A' a))
  exact Module.Flat.trans (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) T A'

/-- **The fibre of a local ring along a local homomorphism is local.**  For local rings `R` and
`A` with a local homomorphism `R → A`, the fibre `A/𝔪_R·A` is a local ring.

The ideal `𝔪_R·A` lies in `𝔪_A` precisely because the homomorphism is local, so it is proper and
the quotient is a nontrivial quotient of a local ring.

This is the `IsLocalRing (A ⧸ IA)` hypothesis of
`Module.Flat.flatQuotSMul_iff_flat_tensor_of_isPushout`, which in the geometric situation of
Stacks 05WY condition (2) is asked of `𝒪_{X, x̄}/𝔪_z̄𝒪_{X, x̄}`. -/
theorem IsLocalRing.quotient_map_maximalIdeal {R A : Type*} [CommRing R] [CommRing A]
    [IsLocalRing R] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)] :
    IsLocalRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) := by
  have : Nontrivial (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :=
    Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R A)).ne
  exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

end
