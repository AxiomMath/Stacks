module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.BivariantFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChowCohomologyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FirstChernCapRuleDifferenceCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackRationalEquivalenceSummand
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinFlatPullbackContained
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GysinPushforwardFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IteratedFirstChernCapCommutativity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClassesCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClassesIntertwining
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleInjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProperPushforwardChowComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.FirstChernCapChow
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFirstChernCapChowGroup
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.RationalEquivalenceSumsCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroSchemeMaximality

/-!
# Chern classes commute with Chow cohomology classes

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r`. **Stacks 0ES1** asserts that `c_j(ℰ) ∈ A^j(X)` commutes with every element `c ∈ A^p(X)`, and
in particular that `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α` for a second finite locally free
`ℱ` of rank `s` and every `α ∈ CH_k(X)`. (The statement in the source reads `c_j(ℒ)`; the proof
and the "in particular" make clear that `c_j(ℰ)` is meant.)

An identity in `A^*(X)` is an identity of the cap operations on `CH_*(X')` for every good
`X' ⟶ X`, and the cap operation of `c_j(ℰ)` on `X'` is `c_j(ℰ|_{X'}) ∩ -`. Here this is proved
for every finite locally free module on `X'`, not only for those pulled back from `X`.

The Chern classes of Stacks 0ERZ (`AlgebraicGeometry.Space.PrivateChern.chernCap`) are
polynomials in the Segre operations (Stacks 0ERY, 0ERV), so it suffices that `c` commutes with
proper pushforward and flat pullback, axioms (1) and (2) of a bivariant class (Stacks 0ERJ), and
with the first Chern class of every invertible module on a test space, which is Stacks 0ERR and
follows from axiom (3) at the zero section, where the Gysin map of Stacks 0ER1 is the cap product
with the first Chern class. For the "in particular" the Segre operations of `ℰ` and `ℱ` commute,
by Stacks 0EPD, 0EQT, 0EQR and 0EQZ.

## Main definitions

* `AlgebraicGeometry.Space.ChowCohomologyClass.capChowHomology`: the cap operation of a class
  `c ∈ A^p(X)` on the Chow homology `CH_*(X') = ⨁_k CH_k(X')` of a good test space `X' ⟶ X`.

## Main results

* `AlgebraicGeometry.Space.ChowCohomologyClass.chernCap_commute_capChowHomology`: **Stacks 0ES1**,
  `c ∩ (c_j(ℰ') ∩ α) = c_j(ℰ') ∩ (c ∩ α)` on `CH_*(X')`.
* `AlgebraicGeometry.Space.commute_chernCap_chernCap` and
  `AlgebraicGeometry.Space.chernCap_chernCap_comm`: **Stacks 0ES1, in particular**,
  `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α`.

## Implementation notes

The cap operations of `c` are maps of the Chow groups `chowGroupCanonical` of Stacks 0EQ6, and
the Chern classes act on `CH_*(X) = ⨁_k chowGroup`. These are the quotient of `Z_k(X)` by the
same subgroup (`AlgebraicGeometry.Space.rationalEquivalencesCanonical_eq_rationalEquivalences`),
and `c` is read on `CH_*` through that identification
(`AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`).

## References

* [Stacks Project, Tag 0ES1](https://stacks.math.columbia.edu/tag/0ES1)
* [Stacks Project, Tag 0ERR](https://stacks.math.columbia.edu/tag/0ERR)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

open PrivateChern

/-! ### Operations on Chow homology -/

section Homology

variable {D : BaseSpaceDimensionSituation.{u}}

/-- An additive map intertwining two endomorphisms intertwines their powers. -/
private theorem map_pow_apply_of_intertwines {M M' : Type*} [AddCommGroup M] [AddCommGroup M']
    (φ : M →+ M') (a : AddMonoid.End M) (b : AddMonoid.End M') (h : ∀ x, φ (a x) = b (φ x))
    (m : ℕ) (x : M) : φ ((a ^ m) x) = (b ^ m) (φ x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, pow_succ]
    change φ ((a ^ m) (a x)) = (b ^ m) (b (φ x))
    rw [ih, h]

/-- Proper pushforward on Chow homology along equal morphisms. -/
private theorem properPushforwardChow_congr {Z P : D.Ambient} (sZ : Z ⟶ D.space)
    (hZ : D.IsGood sZ) (sP : P ⟶ D.space) (hP : D.IsGood sP) {q₁ q₂ : Z ⟶ P} (h : q₁ = q₂)
    (hq₁ : q₁ ≫ sP = sZ) (hq₂ : q₂ ≫ sP = sZ) (hp₁ : IsProper D.site D.base D.base_mem q₁)
    (hp₂ : IsProper D.site D.base D.base_mem q₂) (β : chowHomology.{u, u + 1} D sZ hZ) :
    properPushforwardChow.{u, u + 1} D sZ hZ sP hP q₁ hq₁ hp₁ β =
      properPushforwardChow.{u, u + 1} D sZ hZ sP hP q₂ hq₂ hp₂ β := by
  subst h
  rfl

/-- **Stacks 0EQT on Chow homology**: `q_*(c₁(q^*ℒ) ∩ β) = c₁(ℒ) ∩ q_*β` for `q` proper. -/
private theorem properPushforwardChow_firstChernCapChow_pullbackLine {Z P : D.Ambient}
    (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ) (sP : P ⟶ D.space) (hP : D.IsGood sP) (q : Z ⟶ P)
    (hq : q ≫ sP = sZ) (hqp : IsProper D.site D.base D.base_mem q)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (hL : IsInvertibleModule (⟨P, hP.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (β : chowHomology.{u, u + 1} D sZ hZ) :
    properPushforwardChow.{u, u + 1} D sZ hZ sP hP q hq hqp
        (firstChernCapChow.{u, u + 1} D sZ hZ (pullbackLine D sZ hZ sP hP q L)
          (isInvertibleModule_pullbackLine D sZ hZ sP hP q L hL) β) =
      firstChernCapChow.{u, u + 1} D sP hP L hL
        (properPushforwardChow.{u, u + 1} D sZ hZ sP hP q hq hqp β) := by
  refine DFunLike.congr_fun (chowHomology_hom_ext
    (φ := (properPushforwardChow.{u, u + 1} D sZ hZ sP hP q hq hqp).comp
      (firstChernCapChow.{u, u + 1} D sZ hZ (pullbackLine D sZ hZ sP hP q L)
        (isInvertibleModule_pullbackLine D sZ hZ sP hP q L hL)))
    (ψ := (firstChernCapChow.{u, u + 1} D sP hP L hL).comp
      (properPushforwardChow.{u, u + 1} D sZ hZ sP hP q hq hqp)) D sZ hZ fun k b => ?_) β
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [AddMonoidHom.comp_apply]
  rw [firstChernCapChow_of_chowClass, properPushforwardChow_of,
    chowGroupProperPushforward_chowClass, properPushforwardChow_of,
    chowGroupProperPushforward_chowClass, firstChernCapChow_of_chowClass]
  exact congrArg _ (chowClass_eq_of_chowClassCanonical_eq D sP hP
    (chowClassCanonical_properCyclePushforward_firstChernCapCycleMap D hZ hP
      (ObjectProperty.homMk q) hq hqp L hL j b))

/-- **Stacks 0EQZ on Chow homology**: the cap products with two first Chern classes commute. -/
private theorem commute_firstChernCapChow {Z : D.Ambient} (sZ : Z ⟶ D.space) (hZ : D.IsGood sZ)
    (L N : Modules.{u, u} D.site D.base D.base_mem Z hZ.1)
    (hL : IsInvertibleModule (⟨Z, hZ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)
    (hN : IsInvertibleModule (⟨Z, hZ.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N) :
    @Commute (AddMonoid.End (chowHomology.{u, u + 1} D sZ hZ)) _
      (firstChernCapChow.{u, u + 1} D sZ hZ L hL) (firstChernCapChow.{u, u + 1} D sZ hZ N hN) := by
  unfold Commute SemiconjBy
  refine chowHomology_hom_ext D sZ hZ fun k b => ?_
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 + 1 := ⟨k - 2, by omega⟩
  change firstChernCapChow.{u, u + 1} D sZ hZ L hL (firstChernCapChow.{u, u + 1} D sZ hZ N hN
      (DirectSum.of _ (j + 1 + 1) (chowClass.{u + 1} D sZ hZ (j + 1 + 1) b))) =
    firstChernCapChow.{u, u + 1} D sZ hZ N hN (firstChernCapChow.{u, u + 1} D sZ hZ L hL
      (DirectSum.of _ (j + 1 + 1) (chowClass.{u + 1} D sZ hZ (j + 1 + 1) b)))
  rw [firstChernCapChow_of_chowClass, firstChernCapChow_of_chowClass,
    firstChernCapChow_of_chowClass, firstChernCapChow_of_chowClass]
  exact congrArg _ (canonicalFirstChernCap_firstChernCapCycleMap_comm.{u + 1, u} D sZ hZ L hL N hN
    j b)

/-- **The Segre operations of two projective bundles commute.** For projective bundle data
`(π₁ : P₁ ⟶ X, 𝒪_{P₁}(1))` and `(π₂ : P₂ ⟶ X, 𝒪_{P₂}(1))` over a good `X`, `t_a(P₁) ∘ t_b(P₂) =
t_b(P₂) ∘ t_a(P₁)` on `CH_*(X)`: on `Q = P₁ ×_X P₂`, with `H` and `K` the pullbacks of the two
twists, both composites are `q_*(c₁(H)^{d₁+a} c₁(K)^{d₂+b} ∩ q^*α)`. -/
private theorem commute_segreCap {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX}
    {d₁ d₂ : ℕ} (P₁ : ProjectiveBundleDatum D sX hX d₁) (P₂ : ProjectiveBundleDatum D sX hX d₂)
    (a b : ℕ) : Commute (P₁.segreCap.{u, u + 1} a) (P₂.segreCap.{u, u + 1} b) := by
  have sq : IsPullback (pullback.fst P₁.proj P₂.proj) (pullback.snd P₁.proj P₂.proj) P₁.proj
      P₂.proj := IsPullback.of_hasPullback _ _
  have hQ : D.IsGood (pullback.fst P₁.proj P₂.proj ≫ P₁.toBase) :=
    isGood_pullback_of_isProper D sX hX P₂.isGood.1 P₂.proj P₂.isProper P₁.toBase P₁.isGood
      P₁.proj
  have hsnd : pullback.snd P₁.proj P₂.proj ≫ P₂.toBase =
      pullback.fst P₁.proj P₂.proj ≫ P₁.toBase := by
    rw [← P₁.proj_comp, ← P₂.proj_comp, ← Category.assoc, ← Category.assoc, pullback.condition]
  have hfst₂ := isFlat_and_hasRelativeDimension_of_isPullback D
    (pullback.fst P₁.proj P₂.proj ≫ P₁.toBase) hQ P₁.toBase P₁.isGood P₂.toBase P₂.isGood sX hX
    rfl P₂.proj_comp sq d₂ P₂.isFlat P₂.hasRelativeDimension
  have hsnd₁ := isFlat_and_hasRelativeDimension_of_isPullback D
    (pullback.fst P₁.proj P₂.proj ≫ P₁.toBase) hQ P₂.toBase P₂.isGood P₁.toBase P₁.isGood sX hX
    hsnd P₁.proj_comp sq.flip d₁ P₁.isFlat P₁.hasRelativeDimension
  let P₂' : ProjectiveBundleDatum D P₁.toBase P₁.isGood d₂ :=
    { space := pullback P₁.proj P₂.proj
      toBase := pullback.fst P₁.proj P₂.proj ≫ P₁.toBase
      isGood := hQ
      proj := pullback.fst P₁.proj P₂.proj
      proj_comp := rfl
      isProper := isProper_of_isPullback D.site D.base D.base_mem hQ.1 P₂.isGood.1 P₁.isGood.1
        hX.1 sq.flip P₂.isProper
      isFlat := hfst₂.2.1
      hasRelativeDimension := hfst₂.2.2
      twist := pullbackLine D _ hQ P₂.toBase P₂.isGood (pullback.snd P₁.proj P₂.proj) P₂.twist
      isInvertible_twist := isInvertibleModule_pullbackLine D _ hQ P₂.toBase P₂.isGood _ P₂.twist
        P₂.isInvertible_twist }
  let P₁' : ProjectiveBundleDatum D P₂.toBase P₂.isGood d₁ :=
    { space := pullback P₁.proj P₂.proj
      toBase := pullback.fst P₁.proj P₂.proj ≫ P₁.toBase
      isGood := hQ
      proj := pullback.snd P₁.proj P₂.proj
      proj_comp := hsnd
      isProper := isProper_of_isPullback D.site D.base D.base_mem hQ.1 P₁.isGood.1 P₂.isGood.1
        hX.1 sq P₁.isProper
      isFlat := hsnd₁.2.1
      hasRelativeDimension := hsnd₁.2.2
      twist := pullbackLine D _ hQ P₁.toBase P₁.isGood (pullback.fst P₁.proj P₂.proj) P₁.twist
      isInvertible_twist := isInvertibleModule_pullbackLine D _ hQ P₁.toBase P₁.isGood _ P₁.twist
        P₁.isInvertible_twist }
  have h₁ : ∀ α, P₂'.segreCap b (P₁.pullbackChow α) = P₁.pullbackChow (P₂.segreCap b α) :=
    fun α => ProjectiveBundleDatum.segreCap_flatPullbackChow P₂ P₂' P₁.proj_comp d₁ P₁.isFlat
      P₁.hasRelativeDimension (f' := pullback.snd P₁.proj P₂.proj) sq.flip (Iso.refl _) b α
  have h₂ : ∀ α, P₁'.segreCap a (P₂.pullbackChow α) = P₂.pullbackChow (P₁.segreCap a α) :=
    fun α => ProjectiveBundleDatum.segreCap_flatPullbackChow P₁ P₁' P₂.proj_comp d₂ P₂.isFlat
      P₂.hasRelativeDimension (f' := pullback.fst P₁.proj P₂.proj) sq (Iso.refl _) a α
  have hpow₁ : ∀ β, (P₁.twistCap ^ (d₁ + a)) (P₂'.pushforwardChow β) =
      P₂'.pushforwardChow ((P₁'.twistCap ^ (d₁ + a)) β) := fun β =>
    (map_pow_apply_of_intertwines P₂'.pushforwardChow P₁'.twistCap P₁.twistCap
      (fun x => properPushforwardChow_firstChernCapChow_pullbackLine _ hQ _ P₁.isGood
        (pullback.fst P₁.proj P₂.proj) rfl P₂'.isProper P₁.twist P₁.isInvertible_twist x)
      (d₁ + a) β).symm
  have hpow₂ : ∀ β, (P₂.twistCap ^ (d₂ + b)) (P₁'.pushforwardChow β) =
      P₁'.pushforwardChow ((P₂'.twistCap ^ (d₂ + b)) β) := fun β =>
    (map_pow_apply_of_intertwines P₁'.pushforwardChow P₂'.twistCap P₂.twistCap
      (fun x => properPushforwardChow_firstChernCapChow_pullbackLine _ hQ _ P₂.isGood
        (pullback.snd P₁.proj P₂.proj) hsnd P₁'.isProper P₂.twist P₂.isInvertible_twist x)
      (d₂ + b) β).symm
  have hpull : ∀ α, P₂'.pullbackChow (P₁.pullbackChow α) = P₁'.pullbackChow (P₂.pullbackChow α) :=
    fun α => flatPullbackChow_flatPullbackChow_of_comm D _ hQ _ P₁.isGood _ P₂.isGood sX hX
      pullback.condition P₂'.proj_comp P₁.proj_comp P₁'.proj_comp P₂.proj_comp d₂ d₁ d₁ d₂
      (Nat.add_comm _ _) P₂'.isFlat P₂'.hasRelativeDimension P₁.isFlat P₁.hasRelativeDimension
      P₁'.isFlat P₁'.hasRelativeDimension P₂.isFlat P₂.hasRelativeDimension α
  have hpush : ∀ β, P₁.pushforwardChow (P₂'.pushforwardChow β) =
      P₂.pushforwardChow (P₁'.pushforwardChow β) := fun β => by
    rw [properPushforwardChow_comp, properPushforwardChow_comp]
    exact properPushforwardChow_congr _ hQ sX hX pullback.condition _ _ _ _ β
  have hc := (commute_firstChernCapChow _ hQ P₁'.twist P₂'.twist P₁'.isInvertible_twist
    P₂'.isInvertible_twist).pow_pow (d₁ + a) (d₂ + b)
  change _ * _ = _ * _
  refine DFunLike.ext _ _ fun α => ?_
  calc P₁.segreCap a (P₂.segreCap b α)
      = P₁.pushforwardChow ((P₁.twistCap ^ (d₁ + a)) (P₁.pullbackChow (P₂.segreCap b α))) := rfl
    _ = P₁.pushforwardChow ((P₁.twistCap ^ (d₁ + a)) (P₂'.pushforwardChow
          ((P₂'.twistCap ^ (d₂ + b)) (P₂'.pullbackChow (P₁.pullbackChow α))))) := by
        rw [← h₁]
        rfl
    _ = P₁.pushforwardChow (P₂'.pushforwardChow ((P₁'.twistCap ^ (d₁ + a))
          ((P₂'.twistCap ^ (d₂ + b)) (P₂'.pullbackChow (P₁.pullbackChow α))))) := by
        rw [hpow₁]
    _ = P₂.pushforwardChow (P₁'.pushforwardChow ((P₂'.twistCap ^ (d₂ + b))
          ((P₁'.twistCap ^ (d₁ + a)) (P₁'.pullbackChow (P₂.pullbackChow α))))) := by
        rw [hpush, hpull]
        exact congrArg _ (congrArg _ (DFunLike.congr_fun hc.eq _))
    _ = P₂.pushforwardChow ((P₂.twistCap ^ (d₂ + b)) (P₁'.pushforwardChow
          ((P₁'.twistCap ^ (d₁ + a)) (P₁'.pullbackChow (P₂.pullbackChow α))))) := by
        rw [hpow₂]
    _ = P₂.segreCap b (P₁.segreCap a α) := by
        change _ = P₂.pushforwardChow ((P₂.twistCap ^ (d₂ + b)) (P₂.pullbackChow (P₁.segreCap a α)))
        rw [← h₂]
        rfl

end Homology

/-! ### The cap operation of a Chow cohomology class on Chow homology -/

namespace ChowCohomologyClass

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} {p : ℤ} (c : ChowCohomologyClass D sX hX p)

/-- Every class in `CH_k(X)` is the class of a cycle. -/
private theorem exists_chowClassCanonical_eq {Y : D.Ambient} (s : Y ⟶ D.space) (hY : D.IsGood s)
    (k : ℤ) (y : chowGroupCanonical.{u + 1} D s hY k) :
    ∃ γ, chowClassCanonical.{u + 1} D s hY k γ = y :=
  QuotientAddGroup.mk'_surjective _ y

/-- **Stacks 0ERR, on a test space.** A class `c ∈ A^p(X)` commutes with the cap product with the
first Chern class of every invertible module `𝒩` on a good test space `g : Y ⟶ X`:
`c ∩ (c₁(𝒩) ∩ x) = c₁(𝒩) ∩ (c ∩ x)`. -/
private theorem cap_canonicalFirstChernCapCanonicalChowMap {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (N : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hN : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (k l : ℤ) (hkl : l + p = k) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k + 1)) :
    c.cap g hY k l hkl (canonicalFirstChernCapCanonicalChowMap D (g ≫ sX) hY k N hN x) =
      canonicalFirstChernCapCanonicalChowMap D (g ≫ sX) hY l N hN
        (c.cap g hY (k + 1) (l + 1) (by omega) x) := by
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
  obtain ⟨γ, hγ⟩ := exists_chowClassCanonical_eq (g ≫ sX) hY (l + 1)
    (c.cap g hY (k + 1) (l + 1) (by omega) (chowClassCanonical.{u + 1} D (g ≫ sX) hY (k + 1) α))
  have hNs : IsInvertibleSheaf D (g ≫ sX) hY N :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hN
  have hE := vanishingLocus_zero D (g ≫ sX) hY N
  have : IsIso (vanishingLocus D (g ≫ sX) hY N 0).1.ι := (Subfunctor.eq_top_iff_isIso _).mp hE
  have hι : IsProper D.site D.base D.base_mem (vanishingLocus D (g ≫ sX) hY N 0).1.ι :=
    isProper_of_isIso D.site D.base D.base_mem _
  have hEg := isGood_vanishingLocus_comp D sX g hY N 0
  obtain ⟨β, h₁, h₂⟩ := c.proper_naturality g hY (vanishingLocus D (g ≫ sX) hY N 0).1.ι hEg hι
    k l hkl (gysinCycleMap D (g ≫ sX) (vanishingLocus D (g ≫ sX) hY N 0)
      (isGood_vanishingLocus D (g ≫ sX) hY N 0) k (sectionGysinRule D (g ≫ sX) hY N 0 k hNs) α)
  have h₃ := c.gysin_naturality g hY N 0 hNs k l hkl
    (chowClassCanonical.{u + 1} D (g ≫ sX) hY (k + 1) α)
  rw [← hγ, sectionGysinChowGroupMap_chowClassCanonical,
    sectionGysinChowGroupMap_chowClassCanonical] at h₃
  have h₄ := congrArg (chowGroupCanonicalProperPushforward.{u + 1} D
    (((vanishingLocus D (g ≫ sX) hY N 0).1.ι ≫ g) ≫ sX) hEg (g ≫ sX) hY
    (Category.assoc _ g sX).symm hι l) (h₁.symm.trans h₃)
  have h₅ : chowClassCanonical.{u + 1} D (g ≫ sX) hY l
        (properCyclePushforward D (((vanishingLocus D (g ≫ sX) hY N 0).1.ι ≫ g) ≫ sX) hEg
          (g ≫ sX) hY (Category.assoc _ g sX).symm hι.2.1.2 l β) =
      chowClassCanonical.{u + 1} D (g ≫ sX) hY l
        (properCyclePushforward D ((vanishingLocus D (g ≫ sX) hY N 0).1.ι ≫ g ≫ sX)
          (isGood_vanishingLocus D (g ≫ sX) hY N 0) (g ≫ sX) hY rfl
          (isQuasiCompact_of_isClosedImmersion' D.site D.base D.base_mem
            (vanishingLocus D (g ≫ sX) hY N 0).2.2) l
          (gysinCycleMap D (g ≫ sX) (vanishingLocus D (g ≫ sX) hY N 0)
            (isGood_vanishingLocus D (g ≫ sX) hY N 0) l (sectionGysinRule D (g ≫ sX) hY N 0 l hNs)
            γ)) := h₄
  have hzα := chowClassCanonical_properCyclePushforward_gysinCycleMap_of_eq_top D (g ≫ sX) hY N 0
    hE hNs hN k α
  have hzγ := chowClassCanonical_properCyclePushforward_gysinCycleMap_of_eq_top D (g ≫ sX) hY N 0
    hE hNs hN l γ
  have hlast : canonicalFirstChernCapCanonical.{u + 1} D (g ≫ sX) hY N hN l γ =
      canonicalFirstChernCapCanonicalChowMap D (g ≫ sX) hY l N hN
        (c.cap g hY (k + 1) (l + 1) (by omega)
          (chowClassCanonical.{u + 1} D (g ≫ sX) hY (k + 1) α)) := by
    rw [← hγ]
    rfl
  exact (congrArg (c.cap g hY k l hkl) hzα.symm).trans (h₂.trans (h₅.trans (hzγ.trans hlast)))

/-- **The cap operation of `c ∈ A^p(X)` on Chow homology.** For a good test space `g : Y ⟶ X`,
the homogeneous operation of degree `-p` on `CH_*(Y) = ⨁_k CH_k(Y)` given on `CH_k(Y)` by
`c ∩ - : CH_k(Y) ⟶ CH_{k-p}(Y)` (Stacks 0ERJ), the Chow groups of the class `c`
(`chowGroupCanonical`) being identified with those of `CH_*(Y)` (`chowGroup`), which are the
quotient of `Z_k(Y)` by the same subgroup, through
`AlgebraicGeometry.Space.chowGroupCanonicalEquivChowGroup`. -/
def capChowHomology {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    chowHomology.{u, u + 1} D (g ≫ sX) hY →+ chowHomology.{u, u + 1} D (g ≫ sX) hY :=
  gradedChowMap.{u, u + 1} D (g ≫ sX) hY (g ≫ sX) hY (-p) fun k =>
    (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY (k + -p)).toAddMonoidHom.comp
      ((c.cap g hY k (k + -p) (by omega)).comp
        (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY k).symm.toAddMonoidHom)

/-- The cap operation of `c` on the class of a cycle, in any way of writing the target degree. -/
private theorem capChowHomology_of_chowClass {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k l : ℤ) (hl : l + p = k) (b : CycleGroup D (g ≫ sX) k) :
    c.capChowHomology g hY (DirectSum.of _ k (chowClass.{u + 1} D (g ≫ sX) hY k b)) =
      DirectSum.of (fun k => chowGroup.{u + 1} D (g ≫ sX) hY k) l
        (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY l
          (c.cap g hY k l hl (chowClassCanonical.{u + 1} D (g ≫ sX) hY k b))) := by
  obtain rfl : l = k + -p := by omega
  have hsymm : (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY k).symm
      (chowClass.{u + 1} D (g ≫ sX) hY k b) = chowClassCanonical.{u + 1} D (g ≫ sX) hY k b :=
    (AddEquiv.symm_apply_eq _).2
      (chowGroupCanonicalEquivChowGroup_chowClassCanonical.{u + 1} D (g ≫ sX) hY k b).symm
  rw [capChowHomology, gradedChowMap_of, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.coe_toAddMonoidHom, hsymm]

/-- The cap operation of `c` on a test space `g : Y ⟶ X` whose structure morphism is given as any
morphism equal to `g ≫ sX`. -/
private def capChowHomologyAt {Y : D.Ambient} (g : Y ⟶ X) {s : Y ⟶ D.space} (hs : g ≫ sX = s)
    (hY : D.IsGood s) : chowHomology.{u, u + 1} D s hY →+ chowHomology.{u, u + 1} D s hY := by
  subst hs
  exact c.capChowHomology g hY

private theorem capChowHomologyAt_rfl {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) :
    c.capChowHomologyAt g rfl hY = c.capChowHomology g hY :=
  rfl

/-- **Axiom (1) of Stacks 0ERJ on Chow homology**: `c ∩ h_*β = h_*(c ∩ β)` for `h` proper. -/
private theorem capChowHomologyAt_properPushforwardChow {Y Z : D.Ambient} {gY : Y ⟶ X}
    {gZ : Z ⟶ X} {sY : Y ⟶ D.space} {sZ : Z ⟶ D.space} (hsY : gY ≫ sX = sY)
    (hsZ : gZ ≫ sX = sZ) (hY : D.IsGood sY) (hZ : D.IsGood sZ) {h : Z ⟶ Y} (hgZ : h ≫ gY = gZ)
    (hb : h ≫ sY = sZ) (hh : IsProper D.site D.base D.base_mem h)
    (β : chowHomology.{u, u + 1} D sZ hZ) :
    c.capChowHomologyAt gY hsY hY (properPushforwardChow.{u, u + 1} D sZ hZ sY hY h hb hh β) =
      properPushforwardChow.{u, u + 1} D sZ hZ sY hY h hb hh (c.capChowHomologyAt gZ hsZ hZ β) := by
  subst hgZ hsZ hsY
  rw [capChowHomologyAt_rfl, capChowHomologyAt_rfl]
  refine DFunLike.congr_fun (chowHomology_hom_ext
    (φ := (c.capChowHomology gY hY).comp (properPushforwardChow.{u, u + 1} D _ hZ _ hY h hb hh))
    (ψ := (properPushforwardChow.{u, u + 1} D _ hZ _ hY h hb hh).comp
      (c.capChowHomology (h ≫ gY) hZ)) D _ hZ fun k b => ?_) β
  simp only [AddMonoidHom.comp_apply]
  obtain ⟨β', h₁, h₂⟩ := c.proper_naturality gY hY h hZ hh k (k + -p) (by omega) b
  rw [properPushforwardChow_of, chowGroupProperPushforward_chowClass,
    capChowHomology_of_chowClass c gY hY k (k + -p) (by omega),
    capChowHomology_of_chowClass c (h ≫ gY) hZ k (k + -p) (by omega), h₁, h₂,
    chowGroupCanonicalEquivChowGroup_chowClassCanonical,
    chowGroupCanonicalEquivChowGroup_chowClassCanonical, properPushforwardChow_of,
    chowGroupProperPushforward_chowClass]

/-- **Axiom (2) of Stacks 0ERJ on Chow homology**: `c ∩ h^*α = h^*(c ∩ α)` for `h` flat. -/
private theorem capChowHomologyAt_flatPullbackChow {Y Z : D.Ambient} {gY : Y ⟶ X}
    {gZ : Z ⟶ X} {sY : Y ⟶ D.space} {sZ : Z ⟶ D.space} (hsY : gY ≫ sX = sY)
    (hsZ : gZ ≫ sX = sZ) (hY : D.IsGood sY) (hZ : D.IsGood sZ) {h : Z ⟶ Y} (hgZ : h ≫ gY = gZ)
    (hb : h ≫ sY = sZ) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem h)
    (hr : HasRelativeDimension r D.site D.base D.base_mem h)
    (α : chowHomology.{u, u + 1} D sY hY) :
    c.capChowHomologyAt gZ hsZ hZ (flatPullbackChow.{u, u + 1} D sZ hZ sY hY h hb r hflat hr α) =
      flatPullbackChow.{u, u + 1} D sZ hZ sY hY h hb r hflat hr
        (c.capChowHomologyAt gY hsY hY α) := by
  subst hgZ hsZ hsY
  rw [capChowHomologyAt_rfl, capChowHomologyAt_rfl]
  refine DFunLike.congr_fun (chowHomology_hom_ext
    (φ := (c.capChowHomology (h ≫ gY) hZ).comp
      (flatPullbackChow.{u, u + 1} D _ hZ _ hY h hb r hflat hr))
    (ψ := (flatPullbackChow.{u, u + 1} D _ hZ _ hY h hb r hflat hr).comp
      (c.capChowHomology gY hY)) D _ hY fun k b => ?_) α
  simp only [AddMonoidHom.comp_apply]
  obtain ⟨γ, hγ⟩ := exists_chowClassCanonical_eq (gY ≫ sX) hY (k + -p)
    (c.cap gY hY k (k + -p) (by omega) (chowClassCanonical.{u + 1} D (gY ≫ sX) hY k b))
  have hfl := c.flat_naturality gY hY h hZ r hflat hr k (k + -p) (by omega) (k + r) (k + -p + r)
    rfl rfl (chowClassCanonical.{u + 1} D (gY ≫ sX) hY k b)
  rw [← hγ, flatPullbackChowMapCanonical_chowClassCanonical,
    flatPullbackChowMapCanonical_chowClassCanonical] at hfl
  rw [flatPullbackChow_of_chowClass_eq D _ hZ _ hY h hb r hflat hr k (k + r) rfl,
    capChowHomology_of_chowClass c (h ≫ gY) hZ (k + r) (k + -p + r) (by omega),
    capChowHomology_of_chowClass c gY hY k (k + -p) (by omega), ← hγ,
    chowGroupCanonicalEquivChowGroup_chowClassCanonical,
    flatPullbackChow_of_chowClass_eq D _ hZ _ hY h hb r hflat hr (k + -p) (k + -p + r) rfl, hfl,
    chowGroupCanonicalEquivChowGroup_chowClassCanonical]

/-- **Stacks 0ERR on Chow homology**: `c ∩ (c₁(𝒩) ∩ β) = c₁(𝒩) ∩ (c ∩ β)` for every invertible
`𝒩` on a good test space. -/
private theorem capChowHomologyAt_firstChernCapChow {Y : D.Ambient} {g : Y ⟶ X}
    {s : Y ⟶ D.space} (hs : g ≫ sX = s) (hY : D.IsGood s)
    (N : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hN : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) N)
    (β : chowHomology.{u, u + 1} D s hY) :
    c.capChowHomologyAt g hs hY (firstChernCapChow.{u, u + 1} D s hY N hN β) =
      firstChernCapChow.{u, u + 1} D s hY N hN (c.capChowHomologyAt g hs hY β) := by
  subst hs
  rw [capChowHomologyAt_rfl]
  refine DFunLike.congr_fun (chowHomology_hom_ext
    (φ := (c.capChowHomology g hY).comp (firstChernCapChow.{u, u + 1} D _ hY N hN))
    (ψ := (firstChernCapChow.{u, u + 1} D _ hY N hN).comp (c.capChowHomology g hY)) D _ hY
    fun k b => ?_) β
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [AddMonoidHom.comp_apply]
  obtain ⟨γ, hγ⟩ := exists_chowClassCanonical_eq (g ≫ sX) hY (j + -p + 1)
    (c.cap g hY (j + 1) (j + -p + 1) (by omega)
      (chowClassCanonical.{u + 1} D (g ≫ sX) hY (j + 1) b))
  have h₁ := c.cap_canonicalFirstChernCapCanonicalChowMap g hY N hN j (j + -p) (by omega)
    (chowClassCanonical.{u + 1} D (g ≫ sX) hY (j + 1) b)
  rw [← hγ, canonicalFirstChernCapCanonicalChowMap_chowClassCanonical,
    canonicalFirstChernCapCanonicalChowMap_chowClassCanonical] at h₁
  rw [firstChernCapChow_of_chowClass, capChowHomology_of_chowClass c g hY j (j + -p) (by omega),
    capChowHomology_of_chowClass c g hY (j + 1) (j + -p + 1) (by omega), ← hγ,
    chowGroupCanonicalEquivChowGroup_chowClassCanonical, firstChernCapChow_of_chowClass]
  exact congrArg _ (congrArg (chowGroupCanonicalEquivChowGroup.{u + 1} D (g ≫ sX) hY (j + -p)) h₁)

/-- **Stacks 0ES1.** In Situation 0EDT let `X/B` be good and let `c ∈ A^p(X)` (Stacks 0ERK,
`AlgebraicGeometry.Space.ChowCohomologyClass`). Then `c` commutes with the Chern classes of
Stacks 0ERZ (`AlgebraicGeometry.Space.PrivateChern.chernCap`): for every good test space
`g : X' ⟶ X`, every finite locally free `𝒪_{X'}`-module `ℰ'` of rank `r` and every `j`,

  `c ∩ (c_j(ℰ') ∩ α) = c_j(ℰ') ∩ (c ∩ α)`  for all `α ∈ CH_*(X')`,

where `c ∩ -` is the cap operation of `c` on `X'` (`capChowHomology`). For a finite locally free
`ℰ` of rank `r` on `X` the bivariant class `c_j(ℰ) ∈ A^j(X)` caps on `X'` as `c_j(ℰ|_{X'}) ∩ -`,
so taking `ℰ' = ℰ|_{X'}` this is the identity `c ∘ c_j(ℰ) = c_j(ℰ) ∘ c` in `A^*(X)` (two
bivariant classes being equal when their cap operations on all test spaces are); the statement
here allows any `ℰ'` on `X'`. -/
@[stacks 0ES1 "the main assertion: for every good test space g : X' → X, every finite locally \
free E' of rank r on X' (in particular E' = g^*E) and every j, the cap operation of c ∈ A^p(X) on \
CH_*(X') commutes with c_j(E') ∩ -; this is c ∘ c_j(E) = c_j(E) ∘ c in A^*(X). The source's \
c_j(L) is a typo for c_j(E)"]
theorem chernCap_commute_capChowHomology {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (E : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (r : ℕ)
    (hE : PrivateChern.IsFiniteLocallyFreeOfRank D (g ≫ sX) hY E r) (j : ℕ) :
    Commute (chernCap.{u, u + 1} E r hE j) (c.capChowHomology g hY) := by
  change _ * _ = _ * _
  refine DFunLike.ext _ _ fun α => ?_
  change chernCap.{u, u + 1} E r hE j (c.capChowHomology g hY α) =
    c.capChowHomology g hY (chernCap.{u, u + 1} E r hE j α)
  cases r with
  | zero => exact chernCap_apply_of_rank_zero E E hE hE (c.capChowHomology g hY) j α
  | succ d =>
    have hsP : ((projectiveBundleDatum E d hE).proj ≫ g) ≫ sX =
        (projectiveBundleDatum E d hE).toBase :=
      (Category.assoc _ _ _).trans (projectiveBundleDatum E d hE).proj_comp
    exact chernCap_apply_of_compatible E E hE hE (c.capChowHomology g hY)
      (c.capChowHomologyAt ((projectiveBundleDatum E d hE).proj ≫ g) hsP
        (projectiveBundleDatum E d hE).isGood)
      (fun β => c.capChowHomologyAt_properPushforwardChow rfl hsP hY _ rfl _
        (projectiveBundleDatum E d hE).isProper β)
      (fun β => c.capChowHomologyAt_firstChernCapChow hsP _ _ _ β)
      (fun α => c.capChowHomologyAt_flatPullbackChow rfl hsP hY _ rfl _ d
        (projectiveBundleDatum E d hE).isFlat (projectiveBundleDatum E d hE).hasRelativeDimension
        α) j α

end ChowCohomologyClass

/-! ### Chern classes commute with each other -/

section Commutation

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}

/-- **Stacks 0ES1, in particular**, as a commutation of operations on `CH_*(X)`: for finite
locally free `ℰ` of rank `r` and `ℱ` of rank `s` on a good `X`,
`c_i(ℰ) ∘ c_j(ℱ) = c_j(ℱ) ∘ c_i(ℰ)`. -/
theorem commute_chernCap_chernCap (hX : D.IsGood sX)
    (E F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r s : ℕ)
    (hE : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX E r)
    (hF : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX F s)
    (i j : ℕ) : Commute (chernCap.{u, u + 1} E r hE i) (chernCap.{u, u + 1} F s hF j) := by
  refine chernCap_commute_of_segreCap_commute E F r s hE hF (fun a b => ?_) i j
  cases r with
  | zero => exact Commute.zero_left _
  | succ d₁ =>
    cases s with
    | zero => exact Commute.zero_right _
    | succ d₂ =>
      exact commute_segreCap (projectiveBundleDatum E d₁ hE) (projectiveBundleDatum F d₂ hF) a b

/-- **Stacks 0ES1, in particular.** In Situation 0EDT let `X/B` be good and let `ℰ`, `ℱ` be
finite locally free `𝒪_X`-modules of ranks `r` and `s`. Then

  `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α`

for all `α ∈ CH_k(X)`, the Chern classes being those of Stacks 0ERZ
(`AlgebraicGeometry.Space.PrivateChern.chernCap`), operations on `CH_*(X) = ⨁_k CH_k(X)` carrying
`CH_k(X)` to `CH_{k-n}(X)`. The identity is stated in `CH_*(X)`, where `α` is placed in degree
`k`; both sides lie in the summand `CH_{k-i-j}(X)`, and an identity in `CH_*(X)` is in particular
one of its components in `CH_{k-i-j}(X)`. -/
@[stacks 0ES1 "in particular: c_i(E) ∩ c_j(F) ∩ α = c_j(F) ∩ c_i(E) ∩ α for every α ∈ CH_k(X), \
as an identity in CH_*(X) = ⊕_k CH_k(X) (hence of the components in CH_{k-i-j}(X))"]
theorem chernCap_chernCap_comm (hX : D.IsGood sX)
    (E F : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r s : ℕ)
    (hE : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX E r)
    (hF : PrivateChern.IsFiniteLocallyFreeOfRank D sX hX F s)
    (i j : ℕ) (k : ℤ) (α : chowGroup.{u + 1} D sX hX k) :
    chernCap.{u, u + 1} E r hE i
        (chernCap.{u, u + 1} F s hF j (DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k α)) =
      chernCap.{u, u + 1} F s hF j
        (chernCap.{u, u + 1} E r hE i (DirectSum.of (fun k => chowGroup.{u + 1} D sX hX k) k α)) :=
  DFunLike.congr_fun (commute_chernCap_chernCap hX E F r s hE hF i j).eq _

end Commutation

end AlgebraicGeometry.Space

end
