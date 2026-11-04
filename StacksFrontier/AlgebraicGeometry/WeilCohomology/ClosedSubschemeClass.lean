module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardRationalEquivalence.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme
public import StacksCore.Tactic.StacksAttribute

/-!
# The cycle class of a closed subscheme is a pushforward of the unit

Let `i : X ⟶ Y` be a closed immersion of nonempty smooth projective equidimensional schemes over
a field `k`, let `d = dim X` and `e = dim Y`, and put `c = e - d`. The closed subscheme `X ⊆ Y`
has a cycle `[X]` on `Y`, of dimension `d` and hence of codimension `c`, and its cycle class
`γ([X]) ∈ H^{2c}(Y)(c)` is the pushforward `i_* 1` of the unit of `H^0(X)`.

The proof is the source's: `1 = γ([X])` in `H^0(X)` by Stacks 0FHF, and then axiom (C)(b) for the
closed immersion `i`, which is proper, together with the identity `i_*[X] = [X ⊆ Y]` of cycles.
The identity `γ([X]) = 1` is not assumed: it is
`Stacks.WeilCohomology.cycleClass_fundamentalChowClass_eq_one_of_relativeDimension`, the
equidimensional form of the first clause of Stacks 0FHF, which derives it from axiom (C)(a) for
the structure morphism of `X` and the normalisation `γ([Spec(k)]) = 1` of Stacks 0FHE.

## Main results

* `Stacks.WeilCohomology.cycleClass_closedSubscheme_eq_pushforward_one`: the cycle class of the
  closed subscheme `X ⊆ Y` is the pushforward of the unit along `i : X ⟶ Y`.

## Implementation notes

The cohomological data is supplied as explicit arguments rather than through a bundled Weil
cohomology theory, as everywhere in this directory (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/WeilCohomology/NonemptyScheme.lean` for why no bundle applies),
while the cycle side uses the Chow groups of `StacksDraft.AlgebraicGeometry.Chow` over the base
situation `Stacks.Chow.fieldChowSituation k`, whose base scheme is `Spec(k)`. The dictionary is
as follows.

* `Hpt`, `HptZero`, `degreeZeroPoint`, `kunnethPoint`, `cycleClassPoint`, `integrationPoint`,
  `integration_cycleClassPoint` and `cycleClassPoint_mul` are the data `(D1)`, `(D2)`, `(D3)` at
  the base point `Spec(k)` together with axioms `(A)(a)`, `(B)(a)`, `(C)(d)` and `(C)(c)` there,
  exactly as in `Stacks.WeilCohomology.cycleClass_fundamentalChowClass_eq_one`.
* `HX` stands for `H^0(X)` and `HY` for `H^{2c}(Y)(c)`; `one` is the unit of `H^0(X)` and
  `cycleClassX`, `cycleClassY` are the cycle class maps `γ` of the two schemes in the relevant
  degrees. The map `pullbackMap` is `p^* : H^0(Spec(k)) → H^0(X)` for the structure morphism
  `p = sX`, and `pullbackMap_one` says that it carries the unit to the unit, as the pullback of
  `(D1)` is a homomorphism of `F`-algebras. The map `pushforward` is
  `i_* : H^0(X) → H^{2c}(Y)(c)`, the pushforward defined by Poincaré duality (see Stacks 0FHA).
  Its source is untwisted and its target is `c`-twisted, which the source's convention on the
  data (D0) permits: a linear map `U ⊗ V → W` induces `U(n) ⊗ V(m) → W(n + m)`.
* The hypothesis `cycleClass_pullback` is axiom (C)(a) for the structure morphism `sX` in the one
  degree where it is used: for the smooth morphism `sX` the Gysin map of (C)(a) is flat pullback
  (Chow Homology, Tag 0FF4). The hypothesis `cycleClass_pushforward` is axiom (C)(b) for `i`, in
  the one degree where it is used.
* `Stacks.Chow.chowGroup` is indexed by **dimension**, not codimension. Both the fundamental
  class `[X]` on `X` and the class `[X ⊆ Y]` on `Y` have dimension index `d = dim X`, written
  `0 + d` because that is the index the flat-pullback law produces out of `A_0(Spec(k))`; in the
  source's codimension indexing these are the classes in `CH^0(X)` and `CH^c(Y)` respectively.
  So the single index serves for both Chow groups, and `e` enters only through `HY`.
* Equidimensionality of `X` of dimension `d` is the hypothesis `hd`, that the structure morphism
  has relative dimension `d`. Smoothness of `X` enters only through flatness of `sX`, and
  properness of `i`, which (C)(b) requires, is not a hypothesis: a closed immersion is proper,
  and `Stacks.Chow.chowPushforwardOfIsClosedImmersion` is unconditional for that reason.
  Nonemptiness, projectivity and smoothness of `Y` enter only through the availability of the
  data. The statement is therefore more general than the source's rather than weaker.

## References

* [Stacks Project, Tag 0FHG](https://stacks.math.columbia.edu/tag/0FHG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u v w x

namespace Stacks.WeilCohomology

/-- **Stacks Project, Tag 0FHG.** Let `i : X ⟶ Y` be a closed immersion of nonempty smooth
projective equidimensional schemes over `k`, and let `c = dim Y - dim X`. Then the cycle class of
the closed subscheme `X ⊆ Y`, taken in `H^{2c}(Y)(c)`, is `i_* 1`, the pushforward of the unit of
`H^0(X)`.

The cycle `[X]` here is the cycle of the closed subscheme `X` on the ambient scheme `Y`, of
dimension `d = dim X`, and not the fundamental cycle of `X` on itself. The hypotheses are the
data and axioms of a Weil cohomology theory that the source's two-line proof uses: axiom (C)(a)
for the structure morphism of `X` and the data and axioms at the base point, from which Stacks
0FHF (`Stacks.WeilCohomology.cycleClass_fundamentalChowClass_eq_one_of_relativeDimension`) gives
`γ([X]) = 1` in `H^0(X)`, and axiom (C)(b) for `i`. -/
@[stacks 0FHG]
theorem cycleClass_closedSubscheme_eq_pushforward_one
    {k : Type u} [Field k] {F : Type v} [Field F]
    (Hpt : ℤ → Type x) [∀ i : ℤ, AddCommGroup (Hpt i)] [∀ i : ℤ, Module F (Hpt i)]
    [∀ i : ℤ, FiniteDimensional F (Hpt i)]
    (HptZero : Type x) [CommRing HptZero] [Algebra F HptZero]
    (degreeZeroPoint : Hpt 0 ≃ₗ[F] HptZero)
    (kunnethPoint : ∀ n : ℤ,
      DirectSum ℤ (fun j : ℤ ↦ TensorProduct F (Hpt j) (Hpt (n - j))) ≃ₗ[F] Hpt n)
    (cycleClassPoint : chowGroup (fieldChowSituation k) (𝟙 _) 0 →+ HptZero)
    (integrationPoint : HptZero →ₗ[F] F)
    (integration_cycleClassPoint : integrationPoint
      (cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0)) = 1)
    (cycleClassPoint_mul :
      cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) *
          cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) =
        cycleClassPoint (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0))
    {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [Flat sX]
    (d : ℕ) (hd : AlgebraicGeometry.RelativeDimension sX d)
    (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sY]
    (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ sY = sX)
    {HX HY : Type w} [AddCommGroup HX] [Module F HX] [AddCommGroup HY] [Module F HY]
    (one : HX)
    (cycleClassX : chowGroup (fieldChowSituation k) sX (0 + (d : ℤ)) →+ HX)
    (cycleClassY : chowGroup (fieldChowSituation k) sY (0 + (d : ℤ)) →+ HY)
    (pullbackMap : HptZero →ₗ[F] HX) (pullbackMap_one : pullbackMap 1 = one)
    (pushforward : HX →ₗ[F] HY)
    (cycleClass_pullback : ∀ α,
      cycleClassX (flatPullbackChowOfRelativeDimension (fieldChowSituation k) sX (𝟙 _) sX
          (Category.comp_id sX) d hd 0 α) =
        pullbackMap (cycleClassPoint α))
    (cycleClass_pushforward : ∀ α,
      cycleClassY (chowPushforwardOfIsClosedImmersion (fieldChowSituation k) sX sY i hi
          (0 + (d : ℤ)) α) =
        pushforward (cycleClassX α)) :
    cycleClassY (QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sY i (0 + (d : ℤ)))) =
      pushforward one := by
  have hX : cycleClassX (fundamentalChowClass (fieldChowSituation k) sX (0 + (d : ℤ))) = one :=
    cycleClass_fundamentalChowClass_eq_one_of_relativeDimension Hpt HptZero degreeZeroPoint
      kunnethPoint cycleClassPoint integrationPoint integration_cycleClassPoint
      cycleClassPoint_mul sX d hd one cycleClassX pullbackMap cycleClass_pullback pullbackMap_one
  rw [← chowPushforwardOfIsClosedImmersion_cycleAssociatedToClosedSubscheme
    (fieldChowSituation k) sX sY i hi (0 + (d : ℤ)), cycleClass_pushforward, ← hX]
  rfl

end Stacks.WeilCohomology

end
