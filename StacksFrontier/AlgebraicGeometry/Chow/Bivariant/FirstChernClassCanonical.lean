module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Canonical
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClassOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.GysinNaturality
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapProperPushforward.Invertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.BivariantClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClasses.FlatPullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapPullback
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.BaseChangeIsoGysinSystem
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapGysinCommute
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InverseIsoGysin
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors

/-!
# The canonical first Chern class cap product, and its naturality on the test schemes

`Stacks.Chow.FirstChernCapRule` is the datum standing for Stacks 02SO together with Stacks 02TI:
for every scheme locally of finite type over the base and every invertible module on it, the cap
product `c₁(-) ∩ - : A_{k+1} ⟶ A_k` in every degree. This file constructs it, proves the three
naturality axioms of Stacks 0B76 for the identity cap rule it induces, and obtains the bivariant
first Chern class `c₁(ℒ) ∈ A^1(X)` of Stacks 0FDW and 0B77 with no hypothesis.

## Main definitions

* `Stacks.Chow.canonicalFirstChernCapRule` — the cap product an invertible module provides, as a
  `Stacks.Chow.FirstChernCapRule`.
* `Stacks.Chow.firstChernClassBivariantCanonical` — **Stacks 0FDW**, the first Chern class
  `c₁(ℒ) ∈ A^1(X)` as a bivariant class at the canonical Gysin system.

## Main results

* `Stacks.Chow.canonicalFirstChernCapRule_capOnChow` — its operation is
  `Stacks.Chow.firstChernClassCapChow`, the descended cap product of Stacks 02TI.
* `Stacks.Chow.firstChernIdentityCapRule_canonical_apply` — the identity cap rule it induces,
  with the degree transport discharged.
* `Stacks.Chow.properNaturality_firstChernIdentityCapRule`,
  `Stacks.Chow.flatNaturality_firstChernIdentityCapRule`,
  `Stacks.Chow.gysinNaturality_firstChernIdentityCapRule` — **Stacks 02SU**, **02SS** and
  **0B72**: the three naturality axioms of Stacks 0B76 for that rule on the test schemes.
* `Stacks.Chow.canonicalGysinSystem_isNaturalUnderInverseIso`,
  `Stacks.Chow.canonicalGysinSystem_isNaturalUnderBaseChangeIso` — **Stacks 02TA**, the isomorphism
  cases of the naturality of the Gysin operation for the canonical Gysin system.
* `Stacks.Chow.isFirstChernClassBivariant_firstChernClassBivariantCanonical` — **Stacks 0B77**, the
  class caps by `c₁(g^*ℒ) ∩ -` on every test scheme.

## References

* [Stacks Project, Tag 0B77](https://stacks.math.columbia.edu/tag/0B77)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The degree transport, moved onto the argument -/

/-- The two spellings of the transport of a Chow class along an equality of degrees agree:
`Stacks.Chow.chowGroupCast` and the `Eq.mp` of the congruence. -/
theorem chowGroupCast_eq_eq_mp (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {k l : ℤ} (h : k = l) (α : chowGroup C p k) :
    chowGroupCast C p h α = Eq.mp (congrArg (chowGroup C p) h) α := by
  subst h
  rfl

/-! ### The canonical cap product -/

/-- **Stacks 02SO and 02TI as the datum `Stacks.Chow.FirstChernCapRule`.** The cap product
`c₁(ℳ) ∩ - : A_{k+1}(T) ⟶ A_k(T)` an invertible module `ℳ` on a scheme `T` locally of finite type
over the base provides: the integral-component rule of Stacks 02SO in every degree, together with
the factoring through rational equivalence of Stacks 02TI. -/
def canonicalFirstChernCapRule (C : ChowSituation.{u}) : FirstChernCapRule C :=
  fun {_T} q _ M _ =>
    { chern := fun k => firstChernComponentCycleRule C q k M
      factors := fun k =>
        firstChernClassCapFactorsThroughRationalEquivalence_firstChernComponentCycleRule C k q M }

/-- The operation of the canonical cap product is the descended cap product of Stacks 02TI. -/
theorem canonicalFirstChernCapRule_capOnChow (C : ChowSituation.{u}) {T : Scheme.{u}}
    (q : T ⟶ C.S) [LocallyOfFiniteType q] (M : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible T.sheaf.obj T.ringCatSheaf.property M]
    (k : ℤ) :
    (canonicalFirstChernCapRule C q M).capOnChow C q k = firstChernClassCapChow C k q M :=
  rfl

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The identity cap rule of the canonical cap product: on a test scheme `g : T ⟶ X` it is the
descended cap product of `g^*ℒ` in degree `k - 1`, read on the transport of the argument along
`k = (k - 1) + 1`. -/
theorem firstChernIdentityCapRule_canonical_apply {T : Scheme.{u}} (g : T ⟶ X)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sX) k) :
    firstChernIdentityCapRule C sX (canonicalFirstChernCapRule C) L g k α =
      firstChernClassCapChow C (k - 1) (g ≫ sX) ((Scheme.Modules.pullback g).obj L)
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) (by omega : k = k - 1 + 1)) α) :=
  (chowGroupDegreeCast_apply C (g ≫ sX) (by omega) _ α).trans
    (congrArg _ (chowGroupCast_eq_eq_mp C (g ≫ sX) (by omega) α))

/-- **The descended cap product depends only on the isomorphism class of the invertible
module.** -/
theorem firstChernClassCapChow_congr' (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (k : ℤ) (M N : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property N]
    (e : M ≅ N) :
    firstChernClassCapChow C k q M = firstChernClassCapChow C k q N := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun α ↦ ?_)
  change firstChernClassCapChow C k q M
        (QuotientAddGroup.mk' (rationalEquivalences C q (k + 1)) α) =
      firstChernClassCapChow C k q N
        (QuotientAddGroup.mk' (rationalEquivalences C q (k + 1)) α)
  rw [firstChernClassCapChow_mk, firstChernClassCapChow_mk]
  exact firstChernClassCapOfInvertible_congr C q k M N e α

/-- The descended cap product of the pullback along a composite is that of the iterated pullback. -/
private theorem firstChernClassCapChow_pullback_comp (C : ChowSituation.{u}) {X T T' : Scheme.{u}}
    (q : T' ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ) (g : T ⟶ X) (h : T' ⟶ T) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    firstChernClassCapChow C k q ((Scheme.Modules.pullback (h ≫ g)).obj L) =
      firstChernClassCapChow C k q
        ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback g).obj L)) :=
  firstChernClassCapChow_congr' C q k _ _ ((Scheme.Modules.pullbackComp h g).app L).symm

/-! ### Stacks 02SU for the descended cap product -/

/-- **Stacks 02SU for the descended cap product of Stacks 02TI.** The projection formula
`w_*(c₁(w^*ℳ) ∩ α) = c₁(ℳ) ∩ w_*α` for the operation on Chow groups. -/
theorem properChowPushforward_comp_firstChernClassCapChow_of_isProper (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (w : A ⟶ B) [IsProper w] (hw : w ≫ sB = sA) (k : ℤ) (M : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property M]
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB w hw k)
    (hfacUp : ProperPushforwardFactorsThroughRationalEquivalence C sA sB w hw (k + 1))
    :
    (properChowPushforward C sA sB w hw k hfac).comp
        (firstChernClassCapChow C k sA ((Scheme.Modules.pullback w).obj M)) =
      (firstChernClassCapChow C k sB M).comp
        (properChowPushforward C sA sB w hw (k + 1) hfacUp) := by
  refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun γ ↦ ?_)
  change properChowPushforward C sA sB w hw k hfac
      (firstChernClassCapChow C k sA ((Scheme.Modules.pullback w).obj M)
        (QuotientAddGroup.mk' (rationalEquivalences C sA (k + 1)) γ)) =
    firstChernClassCapChow C k sB M
      (properChowPushforward C sA sB w hw (k + 1) hfacUp
        (QuotientAddGroup.mk' (rationalEquivalences C sA (k + 1)) γ))
  rw [firstChernClassCapChow_mk, properChowPushforward_mk, firstChernClassCapChow_mk]
  exact properChowPushforward_firstChernClassCapOfInvertible_of_isProper' C sA sB w hw k M γ

/-- **Stacks 02SU for the descended cap product**, read on a class. -/
theorem properChowPushforward_firstChernClassCapChow_of_isProper (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (w : A ⟶ B) [IsProper w] (hw : w ≫ sB = sA) (k : ℤ) (M : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property M]
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sA sB w hw k)
    (hfacUp : ProperPushforwardFactorsThroughRationalEquivalence C sA sB w hw (k + 1))
    (α : chowGroup C sA (k + 1)) :
    properChowPushforward C sA sB w hw k hfac
        (firstChernClassCapChow C k sA ((Scheme.Modules.pullback w).obj M) α) =
      firstChernClassCapChow C k sB M
        (properChowPushforward C sA sB w hw (k + 1) hfacUp α) :=
  DFunLike.congr_fun (properChowPushforward_comp_firstChernClassCapChow_of_isProper C sA sB w hw k
    M hfac hfacUp) α

/-! ### Stacks 02SU for the canonical rule on the test schemes -/

/-- **The projection formula on the test schemes.** For the canonical first Chern class cap product
and test morphisms `g : T ⟶ X` and `h : T' ⟶ T` with `h` proper,

  `c₁(g^*ℒ) ∩ h_*α = h_*(c₁((h ∘ g)^*ℒ) ∩ α)`.

This is `Stacks.Chow.IdentityCapRule.ProperNaturality` for
`Stacks.Chow.firstChernIdentityCapRule` at the canonical cap product. -/
@[stacks 02SU "the projection formula read for the identity cap rule of the canonical first \
Chern class cap product on the test schemes of X, i.e. the predicate \
`IdentityCapRule.ProperNaturality` that the bivariant class of Stacks 0B77 takes as its first \
naturality hypothesis, with no hypothesis of its own"]
theorem properNaturality_firstChernIdentityCapRule :
    IdentityCapRule.ProperNaturality C sX 1
      (firstChernIdentityCapRule C sX (canonicalFirstChernCapRule C) L) := by
  intro T T' g _ h _ k hfac hfacp α
  have hp : h ≫ g ≫ sX = (h ≫ g) ≫ sX := by simp [Category.assoc]
  have hk : k = k - 1 + 1 := by omega
  rw [firstChernIdentityCapRule_canonical_apply, firstChernIdentityCapRule_canonical_apply,
    properChowPushforward_cast C ((h ≫ g) ≫ sX) (g ≫ sX) h hp hk hfac
      (properPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h hp
        (k - 1 + 1)) α]
  rw [firstChernClassCapChow_pullback_comp C ((h ≫ g) ≫ sX) (k - 1) g h L]
  exact (properChowPushforward_firstChernClassCapChow_of_isProper C ((h ≫ g) ≫ sX) (g ≫ sX) h hp
    (k - 1) ((Scheme.Modules.pullback g).obj L) hfacp
    (properPushforwardFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h hp
      (k - 1 + 1)) _).symm

/-! ### Stacks 02SS for the descended cap product -/

/-- `Stacks.Chow.chowGroupCast_mk` in the `Eq.mp` spelling: the transport of the class of a cycle
along an equality of degrees is the class of the transported cycle. -/
private theorem eq_mp_mk_cycleGroup (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] {i j : ℤ} (hij : i = j) (β : CycleGroup C q i) :
    Eq.mp (congrArg (chowGroup C q) hij)
        (QuotientAddGroup.mk' (rationalEquivalences C q i) β) =
      QuotientAddGroup.mk' (rationalEquivalences C q j) (hij ▸ β) :=
  (chowGroupCast_eq_eq_mp C q hij _).symm.trans (chowGroupCast_mk C q hij β)

/-- The descended cap product of Stacks 02TI respects heterogeneous equality of its argument
across an equality of degrees. -/
theorem heq_firstChernClassCapChow (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    {i j : ℤ} (hij : i = j) {x : chowGroup C q (i + 1)} {y : chowGroup C q (j + 1)}
    (hxy : HEq x y) :
    HEq (firstChernClassCapChow C i q M x) (firstChernClassCapChow C j q M y) := by
  subst hij
  exact heq_of_eq (congrArg _ (eq_of_heq hxy))

/-- **Stacks 02SS for the descended cap product of Stacks 02TI**: the identity
`v^*(c₁(ℳ) ∩ α) = c₁(v^*ℳ) ∩ v^*α` on Chow groups, with the structure morphism of the source an
independent morphism and `v ≫ sB = sA` a hypothesis. -/
theorem flatPullbackChow_firstChernClassCapChow_of_base (C : ChowSituation.{u})
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (v : A ⟶ B) [LocallyOfFiniteType v] [Flat v] (hv : v ≫ sB = sA)
    (r : ℕ) (hvr : AlgebraicGeometry.RelativeDimension v r) (k : ℤ) (M : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.sheaf.obj B.ringCatSheaf.property M]
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hvr k)
    (hfacUp : FlatPullbackFactorsThroughRationalEquivalence C sA sB v hv r hvr (k + 1))
    (hcast : k + 1 + (r : ℤ) = k + (r : ℤ) + 1) (α : chowGroup C sB (k + 1)) :
    flatPullbackChow C sA sB v hv r hvr k hfac (firstChernClassCapChow C k sB M α) =
      firstChernClassCapChow C (k + (r : ℤ)) sA ((Scheme.Modules.pullback v).obj M)
        (Eq.mp (congrArg (chowGroup C sA) hcast)
          (flatPullbackChow C sA sB v hv r hvr (k + 1) hfacUp α)) := by
  induction α using QuotientAddGroup.induction_on with
  | H β =>
    change flatPullbackChow C sA sB v hv r hvr k hfac
          (firstChernClassCapChow C k sB M
            (QuotientAddGroup.mk' (rationalEquivalences C sB (k + 1)) β)) =
        firstChernClassCapChow C (k + (r : ℤ)) sA ((Scheme.Modules.pullback v).obj M)
          (Eq.mp (congrArg (chowGroup C sA) hcast)
            (flatPullbackChow C sA sB v hv r hvr (k + 1) hfacUp
              (QuotientAddGroup.mk' (rationalEquivalences C sB (k + 1)) β)))
    rw [firstChernClassCapChow_mk, flatPullbackChow_mk, eq_mp_mk_cycleGroup C sA hcast,
      firstChernClassCapChow_mk]
    exact flatPullbackChow_firstChernClassCapOfInvertible_of_base C sA sB v hv r hvr k M hfac
      (firstChernCapRationallyCompatibleWithFlatPullback_invertible C sB v r hvr k M) β

/-! ### Stacks 02SS for the canonical rule on the test schemes -/

/-- **The flat-pullback identity on the test schemes.** For the canonical first Chern class cap
product and test morphisms `g : T ⟶ X` and `h : T' ⟶ T` with `h` flat of relative dimension `r`,

  `c₁((h ∘ g)^*ℒ) ∩ h^*α = h^*(c₁(g^*ℒ) ∩ α)`,

the two sides sitting in the degrees `(k + r) - 1` and `(k - 1) + r`. This is
`Stacks.Chow.IdentityCapRule.FlatNaturality` for `Stacks.Chow.firstChernIdentityCapRule` at the
canonical cap product. -/
@[stacks 02SS "the flat-pullback identity read for the identity cap rule of the canonical first \
Chern class cap product on the test schemes of X, i.e. the predicate \
`IdentityCapRule.FlatNaturality` that the bivariant class of Stacks 0B77 takes as its second \
naturality hypothesis, with no hypothesis of its own"]
theorem flatNaturality_firstChernIdentityCapRule :
    IdentityCapRule.FlatNaturality C sX 1
      (firstChernIdentityCapRule C sX (canonicalFirstChernCapRule C) L) := by
  intro T T' g _ h _ _ r hr k hfac hfacp α
  have hb : h ≫ g ≫ sX = (h ≫ g) ≫ sX := by simp [Category.assoc]
  have hk : k = k - 1 + 1 := by omega
  have hfacUp : FlatPullbackFactorsThroughRationalEquivalence C ((h ≫ g) ≫ sX) (g ≫ sX) h hb r hr
      (k - 1 + 1) :=
    flatPullbackFactorsThroughRationalEquivalence_cast C ((h ≫ g) ≫ sX) (g ≫ sX) h hb r hr
      (by omega : k - 1 + 1 = k) hfac
  rw [firstChernIdentityCapRule_canonical_apply, firstChernIdentityCapRule_canonical_apply,
    flatPullbackChow_firstChernClassCapChow_of_base C ((h ≫ g) ≫ sX) (g ≫ sX) h hb r hr (k - 1)
      ((Scheme.Modules.pullback g).obj L) hfacp hfacUp (by omega),
    ← firstChernClassCapChow_pullback_comp C ((h ≫ g) ≫ sX) (k - 1 + (r : ℤ)) g h L]
  refine heq_firstChernClassCapChow C ((h ≫ g) ≫ sX) _ (by omega) ?_
  have hmid : HEq (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h hb r hr k hfac α)
      (flatPullbackChow C ((h ≫ g) ≫ sX) (g ≫ sX) h hb r hr (k - 1 + 1) hfacUp
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hk) α)) :=
    (heq_eq_mp_index (congrArg (· + (r : ℤ)) hk) _).trans (heq_of_eq
      (flatPullbackChow_cast C ((h ≫ g) ≫ sX) (g ≫ sX) h hb r hr hk
        hfac hfacUp α))
  exact ((chowGroup_cast_heq ((h ≫ g) ≫ sX)
        (show k + (r : ℤ) = k + (r : ℤ) - 1 + 1 by omega) _).trans hmid).trans
    (chowGroup_cast_heq ((h ≫ g) ≫ sX)
      (show k - 1 + 1 + (r : ℤ) = k - 1 + (r : ℤ) + 1 by omega) _).symm

/-! ### Stacks 0B72 for the canonical rule on the test schemes -/

/-- The Gysin map of Stacks 02TO respects heterogeneous equality of its argument across an
equality of degrees. -/
private theorem heq_gysinChowOfInvertible (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S)
    [LocallyOfFiniteType q] (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
    (t : Γ(M, ⊤)) {i j : ℤ} (hij : i = j) {x : chowGroup C q (i + 1)}
    {y : chowGroup C q (j + 1)} (hxy : HEq x y) :
    HEq (gysinChowOfInvertible C q i M t x) (gysinChowOfInvertible C q j M t y) := by
  subst hij
  exact heq_of_eq (congrArg _ (eq_of_heq hxy))

/-- **The Gysin identity on the test schemes.** For the canonical first Chern class cap product, a
test morphism `g : T ⟶ X`, and an invertible module `𝒩` on `T` with a global section `s` and zero
scheme `i : D = Z(s) ⟶ T`,

  `c₁((i ∘ g)^*ℒ) ∩ i^*α = i^*(c₁(g^*ℒ) ∩ α)`.

This is `Stacks.Chow.IdentityCapRule.GysinNaturality` for
`Stacks.Chow.firstChernIdentityCapRule` at the canonical cap product and the canonical Gysin
system. -/
@[stacks 0B72 "the Gysin identity read for the identity cap rule of the canonical first \
Chern class cap product on the test schemes of X, i.e. the predicate \
`IdentityCapRule.GysinNaturality` that the bivariant class of Stacks 0B77 takes as its third \
naturality hypothesis, with no hypothesis of its own"]
theorem gysinNaturality_firstChernIdentityCapRule :
    IdentityCapRule.GysinNaturality C sX 1
      (firstChernIdentityCapRule C sX (canonicalFirstChernCapRule C) L)
      (canonicalGysinSystem C) := by
  intro T g _ N _ s k α
  dsimp only
  have hC : k + 1 = k - 1 + 1 + 1 := by omega
  have hA : k = k - 1 + 1 := by omega
  have hB : k + 1 - 1 = k - 1 + 1 := by omega
  have key := gysinChowOfInvertible_firstChernClassCapChow C (g ≫ sX) (k - 1) N s
    ((Scheme.Modules.pullback g).obj L)
    (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hC) α)
  have hleft : Eq.mp (congrArg (chowGroup C
          (((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) ≫ sX)) hA)
        ((canonicalGysinSystem C).onChow (g ≫ sX) N s k α) =
      gysinChowOfInvertible C (g ≫ sX) (k - 1 + 1) N s
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hC) α) :=
    eq_mp_index_of_heq
      (α := chowGroup C (((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) ≫ sX)) hA
      (heq_gysinChowOfInvertible C (g ≫ sX) N s hA (heq_eq_mp_index hC α))
  have hright : Eq.mp (congrArg (chowGroup C (g ≫ sX)) hB)
        (firstChernIdentityCapRule C sX (canonicalFirstChernCapRule C) L g (k + 1) α) =
      firstChernClassCapChow C (k - 1 + 1) (g ≫ sX) ((Scheme.Modules.pullback g).obj L)
        (Eq.mp (congrArg (chowGroup C (g ≫ sX)) hC) α) := by
    rw [firstChernIdentityCapRule_canonical_apply C sX L g (k + 1) α]
    exact eq_mp_index_of_heq (α := chowGroup C (g ≫ sX)) hB
      (heq_firstChernClassCapChow C (g ≫ sX) ((Scheme.Modules.pullback g).obj L) hB
        ((heq_eq_mp_index (show k + 1 = k + 1 - 1 + 1 by omega) α).symm.trans
          (heq_eq_mp_index hC α)))
  refine (firstChernIdentityCapRule_canonical_apply C sX L
    ((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) k
    ((canonicalGysinSystem C).onChow (g ≫ sX) N s k α)).trans ?_
  rw [firstChernClassCapChow_pullback_comp C
      (((Stacks.Divisors.zeroScheme T N s).subschemeι ≫ g) ≫ sX) (k - 1) g
      (Stacks.Divisors.zeroScheme T N s).subschemeι L, hleft, hright]
  exact key.symm

/-! ### The isomorphism case of Stacks 02TA for the canonical Gysin system -/

/-- **The canonical Gysin system is natural under inverse isomorphisms**: the inverse-isomorphism
case of the naturality of the Gysin operation. -/
@[stacks 02TA "the inverse-isomorphism case of the naturality of the Gysin operation, for the \
canonical Gysin system of Stacks 02TO, with no hypothesis"]
theorem canonicalGysinSystem_isNaturalUnderInverseIso (C : ChowSituation.{u}) :
    (canonicalGysinSystem C).IsNaturalUnderInverseIso :=
  GenuineChern.gysinSystemOfInvertible_isNaturalUnderInverseIso C

/-- **The canonical Gysin system is natural under base-change isomorphisms**: the
base-change-isomorphism case of the naturality of the Gysin operation. -/
@[stacks 02TA "the base-change-isomorphism case of the naturality of the Gysin operation, for \
the canonical Gysin system of Stacks 02TO, with no hypothesis"]
theorem canonicalGysinSystem_isNaturalUnderBaseChangeIso (C : ChowSituation.{u}) :
    (canonicalGysinSystem C).IsNaturalUnderBaseChangeIso :=
  gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C

/-! ### The bivariant first Chern class, with nothing assumed -/

/-- The first Chern class `c₁(ℒ) ∈ A^1(X)` of an invertible module `ℒ` on a scheme `X` locally of
finite type over the base, as a bivariant class of degree `1` for `𝟙 X` at the canonical Gysin
system. -/
@[stacks 0FDW]
def firstChernClassBivariantCanonical :
    BivariantClass C (canonicalGysinSystem C) sX sX (𝟙 X) (Category.id_comp sX) 1 :=
  firstChernClassBivariant C sX (canonicalFirstChernCapRule C) L (canonicalGysinSystem C)
    (properNaturality_firstChernIdentityCapRule C sX L)
    (flatNaturality_firstChernIdentityCapRule C sX L)
    (gysinNaturality_firstChernIdentityCapRule C sX L)
    (canonicalGysinSystem_isNaturalUnderInverseIso C)

/-- The bivariant class `Stacks.Chow.firstChernClassBivariantCanonical` caps by `c₁(g^*ℒ) ∩ -` on
every test scheme. -/
@[stacks 0B77]
theorem isFirstChernClassBivariant_firstChernClassBivariantCanonical :
    IsFirstChernClassBivariant C sX (canonicalFirstChernCapRule C) L (canonicalGysinSystem C)
      (firstChernClassBivariantCanonical C sX L) :=
  isFirstChernClassBivariant_firstChernClassBivariant C sX (canonicalFirstChernCapRule C) L
    (canonicalGysinSystem C) (properNaturality_firstChernIdentityCapRule C sX L)
    (flatNaturality_firstChernIdentityCapRule C sX L)
    (gysinNaturality_firstChernIdentityCapRule C sX L)
    (canonicalGysinSystem_isNaturalUnderInverseIso C)

end Stacks.Chow

end
