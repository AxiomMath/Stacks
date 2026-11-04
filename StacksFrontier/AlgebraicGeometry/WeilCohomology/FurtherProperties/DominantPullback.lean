module

public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.CurveDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ProjectionFormula.Pushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# Injectivity of pullback along a dominant morphism

Let `f : X ⟶ Y` be a dominant morphism of irreducible smooth projective schemes over a field
`k`, and let `H^*` be a Weil cohomology theory over `k` with coefficients in a field `F` of
characteristic zero. Then `f^* : H^*(Y) ⟶ H^*(X)` is injective.

The proof is the source's. There is an integral closed subscheme `Z ⊆ X` of the same dimension
`e` as `Y` mapping onto `Y`, so that `f_*[Z] = m[Y]` for some `m > 0`. Since `γ([Y]) = 1`
(Stacks 0FHF) and the cycle class map commutes with pushforward (axiom (C)(b)), the class
`z = γ([Z])` satisfies `f_* z = m · 1` in `H^0(Y)`. The projection formula (Stacks 0FHB) then
gives

`f_*(f^* a ∪ z) = a ∪ f_* z = m · a`

for every `a ∈ H^i(Y)`, and `m` is invertible in `F`, so `f^* a = 0` forces `a = 0`.

Neither `γ([Y]) = 1` nor the projection formula is assumed. The first is
`Stacks.WeilCohomology.cycleClass_fundamentalChowClass_eq_one_of_relativeDimension`, which derives
it from axiom (C)(a) for the structure morphism of `Y` and the data and axioms at the base point
`Spec(k)`; the second is `Stacks.WeilCohomology.poincareDualPushforward_cup`, applied to the
trace pairings `(a, b) ↦ ∫ a ∪ b`, whose compatibility with cup product is associativity of the
cup product. The geometric input — the subscheme `Z` and the identity `f_*[Z] = m[Y]` — is
`Stacks.Chow.exists_properPushforward_eq_nsmul_fundamentalCycle`.

## Main results

* `Stacks.WeilCohomology.injective_of_pushforward_cup_eq_nsmul`: a linear map over a field of
  characteristic zero with a left inverse up to a nonzero natural multiple is injective.
* `Stacks.WeilCohomology.pushforward_cycleClass_eq_nsmul_one`: for a proper dominant morphism
  onto an integral scheme, the cohomology class of a suitable cycle on `X` pushes forward to a
  nonzero multiple of `γ([Y])`.
* `Stacks.WeilCohomology.injective_pullback_of_isDominant`: the injectivity statement.

## Implementation notes

As elsewhere in this directory the cohomological data is supplied as explicit arguments rather
than through a bundled Weil cohomology theory (see the implementation notes of
`StacksFrontier/AlgebraicGeometry/WeilCohomology/NonemptyScheme.lean` for why no bundle applies),
while the cycle side uses the Chow groups of `StacksDraft.AlgebraicGeometry.Chow` over the base
situation `Stacks.Chow.fieldChowSituation k`, whose base scheme is `Spec(k)`. The dictionary is
as follows; `d = dim X`, `e = dim Y`, `c = d - e`, and `i` is the cohomological degree in which
injectivity is asserted.

* `Hpt`, `HptZero`, `degreeZeroPoint`, `kunnethPoint`, `cycleClassPoint`, `integrationPoint`,
  `integration_cycleClassPoint` and `cycleClassPoint_mul` are the data `(D1)`, `(D2)`, `(D3)` at
  the base point `Spec(k)` together with axioms `(A)(a)`, `(B)(a)`, `(C)(d)` and `(C)(c)` there,
  exactly as in `Stacks.WeilCohomology.cycleClass_fundamentalChowClass_eq_one` and Stacks 0FHG.
* `BY` stands for `H^i(Y)` and `BX` for `H^i(X)`, and `pullbackB` is `f^* : H^i(Y) → H^i(X)`,
  the map whose injectivity is the conclusion.
* `DYtop` is `H^0(Y)`, with `one` its unit, and `DXtop` is `H^{2c}(X)(c)`, where the cycle class
  of a cycle of dimension `e` on `X` lives. `HYtop` and `HXtop` are the complementary groups
  `H^{2e}(Y)(e)` and `H^{2e}(X)(e)`, `TopY = H^{2e}(Y)(e)` and `TopX = H^{2d}(X)(d)` are the
  top degrees, and `integralY`, `integralX` are the trace maps `∫_Y`, `∫_X` of `(D3)`.
* `cupTopY : HYtop × DYtop → TopY` and `cupTopX : HXtop × DXtop → TopX` are cup product into the
  top degree; the trace pairings of `(A)` are `cupTopY.compr₂ integralY` and
  `cupTopX.compr₂ integralX`, and perfectness of the first is axiom `(A)` for `Y`. Likewise
  `cupY' : HY' × BY → TopY` and `cupX' : HX' × DX' → TopX` with `HY' = H^{2e-i}(Y)(e)`,
  `HX' = H^{2e-i}(X)(e)` and `DX' = H^{i+2c}(X)(c)`, and `cupY'.compr₂ integralY` is perfect
  by axiom `(A)` for `Y` in degree `i`.
* `cupY : BY × DYtop → BY`, `cupX : BX × DXtop → DX'`, `cupLeftY : HY' × BY → HYtop` and
  `cupLeftX : HX' × BX → HXtop` are the remaining cup products. `cup_assoc_Y` and `cup_assoc_X`
  are associativity of the cup product, `cupY_one` is the unit law `a ∪ 1 = a`, and
  `pullback_cup` is multiplicativity of `f^*`; all of these are part of `(D1)`, as is
  `pullbackPt_one`, that `p^* : H^0(Spec(k)) → H^0(Y)` carries the unit to the unit.
* `cycleClassY : CH^0(Y) = A_e(Y) → H^0(Y)` and `cycleClassX : A_e(X) → H^{2c}(X)(c)` are the
  cycle class maps `γ` of `(D2)` in the relevant degree. The Chow groups are indexed by
  dimension, written `0 + e` because that is the index the flat-pullback law produces out of
  `A_0(Spec(k))`.
* `cycleClass_pullback` is axiom `(C)(a)` for the structure morphism `sY`, in the one degree
  where it is used: for the smooth morphism `sY` the Gysin map of `(C)(a)` is flat pullback
  (Chow Homology, Tag 0FF4). `cycleClass_pushforward` is axiom `(C)(b)` for `f`, in the one
  degree where it is used, with the pushforward on cohomology the one defined by Poincaré
  duality (see Stacks 0FHA); proper pushforward on Chow groups exists by Stacks 02S2,
  `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`.

The geometric hypotheses are those of the source, partly in a more general form. `Y` is smooth
over `k` and irreducible, and `hd` records that its dimension is `e`: for an irreducible scheme
over a field relative dimension `e` in the sense of Tag 02NJ is dimension `e`. Integrality of `Y`
is derived, a smooth scheme over a field being reduced. Of `X` and `f` only properness of `f`
is used, which holds when `X` is projective over `k` and `Y` is separated; smoothness,
projectivity and irreducibility of `X` and projectivity of `Y` enter only through the
availability of the data. The statement is therefore more general than the source's rather than
weaker.

The source states injectivity of `H^*(Y) ⟶ H^*(X)` on total cohomology; since cohomological
pullback is a graded map, that is equivalent to injectivity in each degree, which is what is
asserted here for the data of an arbitrary degree `i`.

## References

* [Stacks Project, Tag 0FHW](https://stacks.math.columbia.edu/tag/0FHW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u x

namespace Stacks.WeilCohomology

/-! ### A map with a left inverse up to a nonzero multiple -/

/-- A linear map over a field of characteristic zero which admits a left inverse up to a nonzero
natural multiple is injective. -/
theorem injective_of_pushforward_cup_eq_nsmul {F : Type*} [Field F] [CharZero F]
    {B B' : Type*} [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']
    (pullback : B →ₗ[F] B') (pushforward : B' →ₗ[F] B) (m : ℕ) (hm : m ≠ 0)
    (key : ∀ b, pushforward (pullback b) = m • b) :
    Function.Injective pullback := by
  intro a b hab
  have h : m • (a - b) = 0 := by
    rw [← key, map_sub, hab, sub_self, map_zero]
  have hm' : (m : F) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [← Nat.cast_smul_eq_nsmul F, smul_eq_zero] at h
  exact sub_eq_zero.mp (h.resolve_left hm')

/-! ### The pushforward of the cycle class of a dominating prime cycle -/

/-- For a proper dominant morphism `f : X ⟶ Y` onto an integral scheme of delta-dimension `k`,
and cycle class maps on `A_k(X)` and `A_k(Y)` compatible with a pushforward on cohomology, some
class on `X` has cohomology class pushing forward to a nonzero multiple of `γ([Y])`. The class
is that of an integral closed subscheme of `X` of dimension `k` dominating `Y`; its pushforward
is `m [Y]` with `m > 0`. -/
theorem pushforward_cycleClass_eq_nsmul_one {F : Type*} [Field F]
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hf : f ≫ sY = sX) [IsIntegral Y] (k : ℤ)
    (hk : Stacks.Chow.relativeDimension C.dimensionFunction sY (genericPoint Y) = k)
    {DX DY : Type*} [AddCommGroup DX] [Module F DX] [AddCommGroup DY] [Module F DY]
    (pushforward : DX →ₗ[F] DY)
    (cycleClassX : chowGroup C sX k →+ DX) (cycleClassY : chowGroup C sY k →+ DY)
    (cycleClass_pushforward : ∀ α,
      cycleClassY (properChowPushforward C sX sY f hf k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY f hf k) α) =
        pushforward (cycleClassX α)) :
    ∃ (α : chowGroup C sX k) (m : ℕ), m ≠ 0 ∧
      pushforward (cycleClassX α) = m • cycleClassY (fundamentalChowClass C sY k) := by
  obtain ⟨W, hW, m, hm, hpush⟩ :=
    exists_properPushforward_eq_nsmul_fundamentalCycle C sX sY f hf k hk
  refine ⟨QuotientAddGroup.mk' (rationalEquivalences C sX k)
    (cycleAssociatedToClosedSubscheme C sX W.subschemeι k), m, hm, ?_⟩
  rw [← cycleClass_pushforward, properChowPushforward_mk, hpush, map_nsmul, map_nsmul,
    fundamentalChowClass, fundamentalCycle]

/-! ### Injectivity of the pullback -/

/-- **Stacks Project, Tag 0FHW.** Let `f : X ⟶ Y` be a dominant morphism of irreducible smooth
projective schemes over a field `k`, and let `H^*` be a Weil cohomology theory over `k` with
coefficients in a field `F` of characteristic zero. Then `f^* : H^i(Y) ⟶ H^i(X)` is injective.

The cohomological data and the axioms the proof uses are the explicit arguments: the data and
axioms at the base point `Spec(k)`, the trace maps `∫_X`, `∫_Y` and the cup products of `(D1)`
and `(D3)` with associativity, the unit law and multiplicativity of `f^*`, perfectness of the
trace pairings of `Y` (axiom (A)), axiom (C)(a) for the structure morphism of `Y` and axiom
(C)(b) for `f`. The identity `γ([Y]) = 1` of Stacks 0FHF and the projection formula of Stacks
0FHB are derived from these, not assumed. -/
@[stacks 0FHW]
theorem injective_pullback_of_isDominant {k : Type u} [Field k] {F : Type*} [Field F]
    [CharZero F]
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
    {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ (fieldChowSituation k).S) [Smooth sY] [IrreducibleSpace Y]
    (e : ℕ) (hd : AlgebraicGeometry.RelativeDimension sY e)
    (f : X ⟶ Y) [IsProper f] [IsDominant f] (hf : f ≫ sY = sX)
    {BX BY DXtop DYtop HXtop HYtop TopX TopY HX' HY' DX' : Type*}
    [AddCommGroup BX] [Module F BX] [AddCommGroup BY] [Module F BY]
    [AddCommGroup DXtop] [Module F DXtop] [AddCommGroup DYtop] [Module F DYtop]
    [AddCommGroup HXtop] [Module F HXtop] [AddCommGroup HYtop] [Module F HYtop]
    [AddCommGroup TopX] [Module F TopX] [AddCommGroup TopY] [Module F TopY]
    [AddCommGroup HX'] [Module F HX'] [AddCommGroup HY'] [Module F HY']
    [AddCommGroup DX'] [Module F DX']
    (integralX : TopX →ₗ[F] F) (integralY : TopY →ₗ[F] F)
    (cupTopX : HXtop →ₗ[F] DXtop →ₗ[F] TopX) (cupTopY : HYtop →ₗ[F] DYtop →ₗ[F] TopY)
    (cupX' : HX' →ₗ[F] DX' →ₗ[F] TopX) (cupY' : HY' →ₗ[F] BY →ₗ[F] TopY)
    [(cupTopY.compr₂ integralY).IsPerfPair] [(cupY'.compr₂ integralY).IsPerfPair]
    (cupX : BX →ₗ[F] DXtop →ₗ[F] DX') (cupY : BY →ₗ[F] DYtop →ₗ[F] BY)
    (cupLeftX : HX' →ₗ[F] BX →ₗ[F] HXtop) (cupLeftY : HY' →ₗ[F] BY →ₗ[F] HYtop)
    (one : DYtop)
    (cup_assoc_X : ∀ c b a, cupX' c (cupX b a) = cupTopX (cupLeftX c b) a)
    (cup_assoc_Y : ∀ c b a, cupY' c (cupY b a) = cupTopY (cupLeftY c b) a)
    (cupY_one : ∀ b, cupY b one = b)
    (pullbackB : BY →ₗ[F] BX) (pullbackTop : HYtop →ₗ[F] HXtop) (pullback' : HY' →ₗ[F] HX')
    (pullback_cup : ∀ c b, pullbackTop (cupLeftY c b) = cupLeftX (pullback' c) (pullbackB b))
    (pullbackPt : HptZero →ₗ[F] DYtop) (pullbackPt_one : pullbackPt 1 = one)
    (cycleClassX : chowGroup (fieldChowSituation k) sX (0 + (e : ℤ)) →+ DXtop)
    (cycleClassY : chowGroup (fieldChowSituation k) sY (0 + (e : ℤ)) →+ DYtop)
    (cycleClass_pullback : ∀ α,
      cycleClassY (flatPullbackChowOfRelativeDimension (fieldChowSituation k) sY (𝟙 _) sY
          (Category.comp_id sY) e hd 0 α) =
        pullbackPt (cycleClassPoint α))
    (cycleClass_pushforward : ∀ α,
      cycleClassY (properChowPushforward (fieldChowSituation k) sX sY f hf (0 + (e : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
            sX sY f hf (0 + (e : ℤ))) α) =
        poincareDualPushforward (cupTopX.compr₂ integralX) (cupTopY.compr₂ integralY)
          pullbackTop (cycleClassX α)) :
    Function.Injective pullbackB := by
  -- `Y` is integral of dimension `e`
  have : IsReduced Y := isReduced_of_smooth sY
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have hk : Stacks.Chow.relativeDimension (fieldChowSituation k).dimensionFunction sY
      (genericPoint Y) = 0 + (e : ℤ) := by
    rw [zero_add]
    exact relativeDimension_fieldChowSituation_genericPoint sY
      (topologicalKrullDim_eq_of_relativeDimension sY hd)
  -- `γ([Y]) = 1`, Stacks 0FHF
  have hY : cycleClassY (fundamentalChowClass (fieldChowSituation k) sY (0 + (e : ℤ))) = one :=
    cycleClass_fundamentalChowClass_eq_one_of_relativeDimension Hpt HptZero degreeZeroPoint
      kunnethPoint cycleClassPoint integrationPoint integration_cycleClassPoint
      cycleClassPoint_mul sY e hd one cycleClassY pullbackPt cycleClass_pullback pullbackPt_one
  -- `f_* γ([Z]) = m · 1`
  obtain ⟨α, m, hm, hz⟩ := pushforward_cycleClass_eq_nsmul_one (fieldChowSituation k) sX sY f hf
    (0 + (e : ℤ)) hk
    (poincareDualPushforward (cupTopX.compr₂ integralX) (cupTopY.compr₂ integralY) pullbackTop)
    cycleClassX cycleClassY cycleClass_pushforward
  rw [hY] at hz
  -- the projection formula, Stacks 0FHB
  refine injective_of_pushforward_cup_eq_nsmul pullbackB
    ((poincareDualPushforward (cupX'.compr₂ integralX) (cupY'.compr₂ integralY) pullback').comp
      (cupX.flip (cycleClassX α))) m hm fun b ↦ ?_
  have hkey := poincareDualPushforward_cup (cupTopX.compr₂ integralX) (cupTopY.compr₂ integralY)
    (cupX'.compr₂ integralX) (cupY'.compr₂ integralY) pullbackTop pullback' pullbackB cupX cupY
    cupLeftX cupLeftY pullback_cup
    (fun c b a ↦ by rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, cup_assoc_X])
    (fun c b a ↦ by rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply, cup_assoc_Y])
    b (cycleClassX α)
  simp only [LinearMap.comp_apply, LinearMap.flip_apply]
  rw [hkey, hz, map_nsmul, cupY_one]

end Stacks.WeilCohomology

end
