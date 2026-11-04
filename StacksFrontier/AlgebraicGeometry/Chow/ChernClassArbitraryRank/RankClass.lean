module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity

/-!
# The rank of a finite locally free module as a bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `E` be a finite locally free `O_X`-module whose rank need
not be constant. Write `X = X_0 ⊔ X_1 ⊔ X_2 ⊔ …` for the decomposition into the loci where the
rank of `E` is `r`. **Stacks 0ESW** defines the *rank* of `E` to be the element
`r(E) ∈ A^0(X)` given by the bivariant operation which sends
`(α_r) ∈ ∏_r CH_*(X'_r)` to `(r α_r)`, for every `X' ⟶ X` locally of finite type.

Under the product decomposition `A^0(X) = ∏_r A^0(X_r)` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.Basic` that class is the family whose
`r`-th member is `r` times the unit of `A^0(X_r)`, and that is how it is built here.

## Main definitions

* `Stacks.Chow.identityCapRuleZero` — the degree-zero identity cap rule, `α ↦ α`.
* `Stacks.Chow.chowCohomologyOne` — the unit `1 ∈ A^0(W)` of Chow cohomology.
* `Stacks.Chow.rankBivariantClass` — **Stacks 0ESW**, the class `r(E) ∈ A^0(X)`.

## Main results

* `Stacks.Chow.chowGroupDegreeEquiv_properChowPushforward` — proper pushforward commutes with
  transport along an equality of degrees.
* `Stacks.Chow.properNaturality_identityCapRuleZero` — the degree-zero identity cap rule satisfies
  the projection formula, which is axiom (1) of Stacks 0B76 for it.
* `Stacks.Chow.transportFlatNaturality_identityCapRuleZero`,
  `Stacks.Chow.transportFlatNaturality_rankLocus` — it also satisfies axiom (2), the
  flat-pullback axiom, so that axiom is not a hypothesis of anything below.
* `Stacks.Chow.chowCohomologyOne_cap`, `Stacks.Chow.zsmul_chowCohomologyOne_cap` — capping with
  the unit is the identity, and capping with an integer multiple of it is multiplication by that
  integer.
* `Stacks.Chow.rankLocusRestriction_rankBivariantClass` — **Stacks 0ESW**, the component of
  `r(E)` on `X_r` is `r` times the unit.
* `Stacks.Chow.rankBivariantClass_cap` — **Stacks 0ESW**, `r(E)` sends `(α_r)` to `(r α_r)`: on a
  test scheme over `X_r`, capping with `r(E)` is multiplication by `r`.
* `Stacks.Chow.eq_rankBivariantClass_of_rankLocusRestriction_eq` — `r(E)` is the only degree-zero
  class with those components.

## Implementation notes

### The unit of `A^0`, and the one naturality axiom still carried

`Stacks.Chow.chowCohomology` carries no multiplication in this repository, so it has no unit to
scale: composition of bivariant classes is available only as the characterization
`Stacks.Chow.IsBivariantClassComposition`. The unit is therefore built here from the identity cap
rule by `Stacks.Chow.IdentityCapRule.toBivariantClass`, which asks for the three naturality axioms
of Stacks 0B76 for the transport of that rule to the chosen pullbacks `W ×_W T`.

Two of the three are proved here. The projection formula is, for the identity rule, the statement
that proper pushforward commutes with the transport along `k = k - 0`, which is
`Stacks.Chow.chowGroupDegreeEquiv_properChowPushforward`, and its transport to the pullbacks is
`Stacks.Chow.IdentityCapRule.transport_proper_naturality`. The flat-pullback axiom is
`Stacks.Chow.transportFlatNaturality_identityCapRuleZero`: the rule of this file is the rule
`Stacks.Chow.identityCapRule` of
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity` — the two differ only in the proof of
`k = k - 0`, which is proof-irrelevant — so the isomorphism case of Stacks 02RG at the
base-change isomorphisms `W ×_W T ≅ T` settles it. The four declarations carrying the Stacks 0ESW
attribute therefore take **no** flat hypothesis; what remains of it in this file is only the
`hflat` argument of `Stacks.Chow.chowCohomologyOne` itself, which keeps its signature.

### Why the Gysin axiom is still a hypothesis, and what it would take to remove it

The Gysin axiom is the one hypothesis left, as `hgysin`. It is literally the `gysin_naturality`
field of `Stacks.Chow.BivariantClass` for the transported rule, hence the weakest hypothesis that
yields the class, and it is a `Prop`, so the class does not depend on which proof is supplied.

It is not an oversight. At degree `0` the axiom compares the Gysin map of a
`Stacks.Chow.GysinSystem` at an invertible module `N` on a test scheme `T` with its Gysin map at
`(Scheme.Modules.pullback (pullback.snd (𝟙 W) g)).obj N` on `W ×_W T`, the two being related by
pushforward along the base-change isomorphism `W ×_W T ≅ T`. The library's uniform naturality
property `Stacks.Chow.GysinSystem.IsNaturalUnderBaseChangeIso` does not reach it: that property
compares the Gysin maps at the pullbacks of a *common* module along two maps `qA`, `qB` out of a
common base, so matching it here forces `qA = 𝟙 T`, and the module on that side is then
`(Scheme.Modules.pullback (𝟙 T)).obj N` rather than `N`. Those two are not definitionally equal —
`rfl` does not close `(Scheme.Modules.pullback (𝟙 T)).obj N = N` — so a bridge would need
`Stacks.Chow.GysinSystem.onChow` to be natural in the module along an isomorphism of invertible
modules. No such naturality is derivable: the `chern` field of `Stacks.Chow.GysinSystem` assigns
unrelated data to each triple of a scheme, an invertible module and a degree. Removing `hgysin`
therefore needs a strengthening of `Stacks.Chow.GysinSystem` itself, not a proof about the rank
loci, and the same obstruction is recorded for the identity class at
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity`.

### Why `r` times the unit is the operation of the source

The source describes `r(E)` by its action, not by a formula. The two agree:
`Stacks.Chow.rankBivariantClass_cap` computes the action on a test scheme over `X_r` and finds
multiplication by `r`, from additivity of the cap operation in the class,
`Stacks.Chow.BivariantClass.zsmul_cap`, together with the cap formula for the unit. Since a class
is determined by its components, `Stacks.Chow.eq_rankBivariantClass_of_rankLocusRestriction_eq`,
nothing is lost in defining it by the formula.

## References

* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B7E](https://stacks.math.columbia.edu/tag/0B7E)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Proper pushforward commutes with transport along an equality of degrees. -/
theorem chowGroupDegreeEquiv_properChowPushforward (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (q : X ⟶ Y) [IsProper q] (hq : q ≫ sY = sX) {k l : ℤ} (hkl : k = l)
    (hfack : ProperPushforwardFactorsThroughRationalEquivalence C sX sY q hq k)
    (hfacl : ProperPushforwardFactorsThroughRationalEquivalence C sX sY q hq l)
    (α : chowGroup C sX k) :
    chowGroupDegreeEquiv C sY hkl (properChowPushforward C sX sY q hq k hfack α) =
      properChowPushforward C sX sY q hq l hfacl (chowGroupDegreeEquiv C sX hkl α) := by
  subst hkl
  rfl

/-! ### The unit of Chow cohomology -/

section Unit

variable (C : ChowSituation.{u}) {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  (G : GysinSystem C)

/-- The degree-zero identity cap rule: on every test scheme it is the identity map of the Chow
group, read in degree `k - 0`. -/
def identityCapRuleZero : IdentityCapRule C sW 0 := fun {_T} g _ k ↦
  (chowGroupDegreeEquiv C (g ≫ sW) (by omega : k = k - 0)).toAddMonoidHom

/-- The degree-zero identity cap rule satisfies the projection formula of Stacks 0B76 (1). -/
theorem properNaturality_identityCapRuleZero :
    IdentityCapRule.ProperNaturality C sW 0 (identityCapRuleZero C sW) := by
  intro T T' g _ q _ k hfac hfacp α
  exact chowGroupDegreeEquiv_properChowPushforward C ((q ≫ g) ≫ sW) (g ≫ sW) q
    (by simp [Category.assoc]) (by omega) hfac hfacp α

/-- **Stacks 0B76 (2) for the degree-zero identity cap rule.** The flat-pullback axiom holds; it
is not a hypothesis.

The rule of this file and `Stacks.Chow.identityCapRule` of
`StacksFrontier.AlgebraicGeometry.Chow.DiagonalGysinIdentity` both send a class to its transport
along `k = k - 0` and differ only in the proof of that equality of degrees, which is
proof-irrelevant; so `Stacks.Chow.identityCapRule_transportFlatNaturality` — the isomorphism case
of Stacks 02RG at the base-change isomorphisms `W ×_W T ≅ T` — proves it outright. -/
theorem transportFlatNaturality_identityCapRuleZero :
    IdentityCapRule.TransportFlatNaturality C sW 0 (identityCapRuleZero C sW) :=
  identityCapRule_transportFlatNaturality C sW

variable (hflat : IdentityCapRule.TransportFlatNaturality C sW 0 (identityCapRuleZero C sW))
  (hgysin : IdentityCapRule.TransportGysinNaturality C sW 0 (identityCapRuleZero C sW) G)

/-- The unit `1 ∈ A^0(W)` of Chow cohomology: the bivariant class of degree zero for the identity
of `W` whose cap operation is the identity on every test scheme. -/
def chowCohomologyOne : chowCohomologyComponent C G sW 0 :=
  IdentityCapRule.toBivariantClass C sW 0 (identityCapRuleZero C sW) G
    (properNaturality_identityCapRuleZero C sW) hflat hgysin

/-- Capping with the unit is the identity. -/
theorem chowCohomologyOne_cap {T : Scheme.{u}} (g : T ⟶ W) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ sW) k) :
    chowPushforwardOfIso C (pullback.fst (𝟙 W) g ≫ sW) (g ≫ sW) (identityBaseChangeIso g).hom
        (identityBaseChangeIso_hom_comp_base C sW g) (k - 0)
        ((chowCohomologyOne C sW G hflat hgysin).cap g k α) =
      chowGroupDegreeEquiv C (g ≫ sW) (by omega : k = k - 0) α :=
  IdentityCapRule.pushforward_transport C sW 0 (identityCapRuleZero C sW) g k α

/-- Capping with an integer multiple of the unit is multiplication by that integer. -/
theorem zsmul_chowCohomologyOne_cap (n : ℤ) {T : Scheme.{u}} (g : T ⟶ W)
    [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ sW) k) :
    chowPushforwardOfIso C (pullback.fst (𝟙 W) g ≫ sW) (g ≫ sW) (identityBaseChangeIso g).hom
        (identityBaseChangeIso_hom_comp_base C sW g) (k - 0)
        ((n • chowCohomologyOne C sW G hflat hgysin).cap g k α) =
      n • chowGroupDegreeEquiv C (g ≫ sW) (by omega : k = k - 0) α := by
  rw [BivariantClass.zsmul_cap, map_zsmul]
  exact congrArg (fun z ↦ n • z) (chowCohomologyOne_cap C sW G hflat hgysin g k α)

end Unit

/-! ### The rank of a finite locally free module as a bivariant class -/

section RankClass

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
  (hgysO : G.IsNaturalUnderOpenImmersion) (hgysR : G.IsNaturalUnderOpensRestriction)
  (hgysC : G.IsNaturalUnderPullbackComp)
  (hgysin : ∀ r : ℕ, IdentityCapRule.TransportGysinNaturality C ((rankLocus E r).ι ≫ sX) 0
    (identityCapRuleZero C ((rankLocus E r).ι ≫ sX)) G)

/-- **The flat-pullback axiom of Stacks 0B76 on the rank-`r` locus, discharged.**  This is
`Stacks.Chow.transportFlatNaturality_identityCapRuleZero` at the structure morphism of the
locus; it is what lets the declarations below carry no flat hypothesis. -/
theorem transportFlatNaturality_rankLocus (r : ℕ) :
    IdentityCapRule.TransportFlatNaturality C ((rankLocus E r).ι ≫ sX) 0
      (identityCapRuleZero C ((rankLocus E r).ι ≫ sX)) :=
  transportFlatNaturality_identityCapRuleZero C _

/-- **Stacks 0ESW.** The rank `r(E) ∈ A^0(X)` of a finite locally free module whose rank need not
be constant: the bivariant class which preserves the product decomposition of the Chow groups
along the rank loci and acts on the rank-`r` factor by multiplication by `r`. -/
@[stacks 0ESW "rank_bivariant_class; the flat transport axiom of Stacks 0B76 is proved here, \
and only the Gysin transport axiom is carried, as for the library's own first Chern class at \
Tag 0FDW"]
def rankBivariantClass : chowCohomologyComponent C G sX 0 :=
  rankLocusAssembly C G sX E hgysO hgysR hgysC 0
    fun r ↦ (r : ℤ) • chowCohomologyOne C ((rankLocus E r).ι ≫ sX) G
      (transportFlatNaturality_rankLocus C sX E r) (hgysin r)

/-- **Stacks 0ESW.** The component of `r(E)` on the rank-`r` locus is `r` times the unit. -/
@[stacks 0ESW "rank_bivariant_class; the flat transport axiom of Stacks 0B76 is proved here, \
and only the Gysin transport axiom is carried, as for the library's own first Chern class at \
Tag 0FDW"]
theorem rankLocusRestriction_rankBivariantClass (r : ℕ) :
    rankLocusRestriction C G sX E hgysO 0
        (rankBivariantClass C G sX E hgysO hgysR hgysC hgysin) r =
      (r : ℤ) • chowCohomologyOne C ((rankLocus E r).ι ≫ sX) G
        (transportFlatNaturality_rankLocus C sX E r) (hgysin r) :=
  rankLocusRestriction_rankLocusAssembly C G sX E hgysO hgysR hgysC 0 _ r

/-- **Stacks 0ESW.** `r(E)` sends `(α_r)` to `(r α_r)`: on a test scheme over the rank-`r` locus,
capping with `r(E)` is multiplication by `r`. -/
@[stacks 0ESW "rank_bivariant_class; the flat transport axiom of Stacks 0B76 is proved here, \
and only the Gysin transport axiom is carried, as for the library's own first Chern class at \
Tag 0FDW"]
theorem rankBivariantClass_cap (r : ℕ) {T : Scheme.{u}}
    (g : T ⟶ (rankLocus E r : Scheme.{u})) [LocallyOfFiniteType g] (k : ℤ)
    (α : chowGroup C (g ≫ ((rankLocus E r).ι ≫ sX)) k) :
    chowPushforwardOfIso C
        (pullback.fst (𝟙 (rankLocus E r : Scheme.{u})) g ≫ ((rankLocus E r).ι ≫ sX))
        (g ≫ ((rankLocus E r).ι ≫ sX)) (identityBaseChangeIso g).hom
        (identityBaseChangeIso_hom_comp_base C ((rankLocus E r).ι ≫ sX) g) (k - 0)
        ((rankLocusRestriction C G sX E hgysO 0
          (rankBivariantClass C G sX E hgysO hgysR hgysC hgysin) r).cap g k α) =
      (r : ℤ) • chowGroupDegreeEquiv C (g ≫ ((rankLocus E r).ι ≫ sX))
        (by omega : k = k - 0) α := by
  rw [rankLocusRestriction_rankBivariantClass C G sX E hgysO hgysR hgysC hgysin r]
  exact zsmul_chowCohomologyOne_cap C ((rankLocus E r).ι ≫ sX) G
    (transportFlatNaturality_rankLocus C sX E r) (hgysin r) (r : ℤ) g k α

include hgysR hgysC in
/-- **Stacks 0ESW.** `r(E)` is the only degree-zero class with those components. -/
@[stacks 0ESW "rank_bivariant_class; the flat transport axiom of Stacks 0B76 is proved here, \
and only the Gysin transport axiom is carried, as for the library's own first Chern class at \
Tag 0FDW"]
theorem eq_rankBivariantClass_of_rankLocusRestriction_eq
    {c : chowCohomologyComponent C G sX 0}
    (h : ∀ r : ℕ, rankLocusRestriction C G sX E hgysO 0 c r =
      (r : ℤ) • chowCohomologyOne C ((rankLocus E r).ι ≫ sX) G
        (transportFlatNaturality_rankLocus C sX E r) (hgysin r)) :
    c = rankBivariantClass C G sX E hgysO hgysR hgysC hgysin :=
  eq_of_rankLocusRestriction_eq C G sX E hgysO hgysR hgysC 0 fun r ↦
    (h r).trans (rankLocusRestriction_rankBivariantClass C G sX E hgysO hgysR hgysC
      hgysin r).symm

end RankClass

end Stacks.Chow

end
