module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.ChernRelations
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveCompletionChern.TwistTrivial
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.TowerBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedIntertwining
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0FEF: the Chern classes of the zero section of a projective completion

Let `X` be locally of finite type over the base of chapter 42, `𝒞` locally free of rank `r`,
`π : E = Proj_X(Sym^*(𝒞)[T]) ⟶ X` the projective completion, `i : X ⟶ E` its zero section and
`j : C = Spec_X(Sym^*(𝒞)) ⟶ E`, `p : C ⟶ X` the inclusion and the structure morphism of the vector
bundle. Stacks 0FEF asserts that `c_t(i_*𝒪_X) = 0` for `t = 1, …, r - 1` and that
`p^* ∘ π_* ∘ c_r(i_*𝒪_X) = (-1)^{r-1} (r-1)! j^*` in `A⁰(C ⟶ E)`.

The second identity is read, as in the proof of the source, on the classes of `E' = E ×_X X'` for
every `f : X' ⟶ X` locally of finite type (any cartesian square), with `π' : E' ⟶ X'`,
`j' : C' = C ×_E E' ⟶ E'` and `p' = π' ∘ j'` the base changes: these are the test schemes over
`E` on which `π_*` of the left-hand side is defined. By Stacks 02TX every class on `E'` is a sum of
classes
`h^i ∩ π'^* β` with `h = c₁(𝒪(1))`. With `𝒦 = Ker(π^*(𝒞 ⊕ 𝒪_X) ⟶ 𝒪(1))`, the Koszul resolution of
`i_*𝒪_X` gives `c_r(i_*𝒪_X) = -(r-1)! c_r(𝒦)`; the Whitney formula gives `c_r(𝒦) h = 0` and
`c_r(𝒦) = ∑_j (-h)^j c_{r-j}(π^*(𝒞 ⊕ 𝒪_X))`, so Stacks 02TW gives
`π'_*(c_r(𝒦) ∩ π'^* β) = (-1)^r β`; finally `𝒪(1)` is trivial on `C`, so `j'^*` kills
`h^i ∩ -` for `i ≥ 1`, and `j'^* π'^* = p'^*`.

## Main results

* `flatPullbackChow_properChowPushforward_perfectChernClass_of_isPullback` (and its
  specialization to the chosen fibre products): the second conclusion on every cartesian square
  `E' = E ×_X X'`, `C' = C ×_E E'`.
* `Stacks.Chow.ProjectiveCompletion.chernClasses_zeroSecObject`: Stacks 0FEF.

## References

* [Stacks Project, Tag 0FEF](https://stacks.math.columbia.edu/tag/0FEF)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Finset

universe u

namespace Stacks.Chow.ProjectiveCompletion

attribute [local instance 2000] HasDerivedCategory.standard

variable {X : Scheme.{u}} (𝒞 : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} 𝒞] (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} 𝒞 r]

attribute [local instance] isFiniteLocallyFreeOfRank_kernelModule
  isFiniteLocallyFreeOfRank_pullbackModule

/-- An element of a Chow group heterogeneously equal to zero in an equal degree is zero. -/
theorem chowGroup_eq_zero_of_heq {Y : Scheme.{u}} (C : ChowSituation.{u}) {q : Y ⟶ C.S}
    [LocallyOfFiniteType q] {d d' : ℤ} (hd : d = d') {x : chowGroup C q d}
    (hx : x ≍ (0 : chowGroup C q d')) : x = 0 := by
  subst hd
  exact eq_of_heq hx

/-- Integer multiples of heterogeneously equal elements in equal degrees. -/
theorem chowGroup_zsmul_heq {Y : Scheme.{u}} (C : ChowSituation.{u}) {q : Y ⟶ C.S}
    [LocallyOfFiniteType q] {d d' : ℤ} (hd : d = d') {x : chowGroup C q d}
    {y : chowGroup C q d'} (hxy : x ≍ y) (n : ℤ) : n • x ≍ n • y := by
  subst hd
  cases hxy
  rfl

/-- The powers of a pair intertwined by a degree-shifting map are intertwined. -/
theorem intertwines_pow {G H : ℤ → Type u} [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)]
    {d : ℤ} {pull : ∀ k : ℤ, G k →+ H (k + d)} {a : GradedCapFamily G} {a' : GradedCapFamily H}
    (ha : Intertwines pull a a') (n : ℕ) : Intertwines pull (a ^ n) (a' ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using Intertwines.one
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact ih.mul ha

/-- A power of a homogeneous total class of degree one is homogeneous. -/
theorem isHomogeneous_pow_of_isHomogeneous_one {C : ChowSituation.{u}} {Y : Scheme.{u}}
    {sY : Y ⟶ C.S} [LocallyOfFiniteType sY] {h : TotalChowClass C sY}
    (hh : h.IsHomogeneous 1) (n : ℕ) : (h ^ n).IsHomogeneous n := by
  induction n with
  | zero =>
      rw [pow_zero]
      exact fun _ hp => TotalChowClass.one_apply_of_ne hp
  | succ n ih =>
      rw [pow_succ]
      exact ih.mul hh

include r in
/-- The projective completion `π : E ⟶ X` is flat. -/
theorem flat_proj : Flat (proj 𝒞) :=
  have := isFiniteLocallyFreeOfRank_module 𝒞 r
  flat_bundleProj (module 𝒞) r

/-- The projective completion `π : E ⟶ X` has relative dimension `r`. -/
theorem relativeDimension_proj [LocallyOfFiniteType (proj 𝒞)] :
    AlgebraicGeometry.RelativeDimension (proj 𝒞) r :=
  have := isFiniteLocallyFreeOfRank_module 𝒞 r
  relativeDimension_bundleProj (module 𝒞) r

/-- The projective completion `π : E ⟶ X`, with `𝒪(1)`, is locally a projective bundle of rank
`r`. -/
theorem isLocallyProjectiveTower_proj :
    IsLocallyProjectiveTower r (proj 𝒞) (twist 𝒞) :=
  have := isFiniteLocallyFreeOfRank_module 𝒞 r
  isLocallyProjectiveTower_bundle (module 𝒞) r

section BaseChange

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  {X' E' C' : Scheme.{u}} {f : X' ⟶ X} [LocallyOfFiniteType f] {g : E' ⟶ space 𝒞}
  {π' : E' ⟶ X'} [LocallyOfFiniteType g] [Flat π'] [IsProper π']
  (hsq : IsPullback g π' (proj 𝒞) f) {q : C' ⟶ Scheme.Modules.vectorBundle X 𝒞} (j' : C' ⟶ E')
  [IsOpenImmersion j'] (hsqC : IsPullback q j' (vectorBundleIncl 𝒞 r) g)

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Flat π'] [IsProper π'] in
include hsq in
/-- The square `E' = E ×_X X'` commutes over the base. -/
theorem snd_comp_eq :
    π' ≫ f ≫ sX = g ≫ proj 𝒞 ≫ sX := by
  rw [← Category.assoc, ← hsq.w, Category.assoc]

omit [Flat (proj 𝒞)] [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Flat π'] in
include hsq in
/-- The base change `E' ⟶ X'` has relative dimension `r`. -/
theorem relativeDimension_snd :
    AlgebraicGeometry.RelativeDimension (π') r :=
  AlgebraicGeometry.RelativeDimension.of_isPullback hsq (relativeDimension_proj 𝒞 r)

omit [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)] [LocallyOfFiniteType f]
  [LocallyOfFiniteType g] [Flat π'] [IsProper π'] in
include hsq in
/-- The base change `E' ⟶ X'`, with the pullback of `𝒪_E(1)`, is a projective tower locally on
`X'`. -/
theorem isLocallyProjectiveTower_snd :
    IsLocallyProjectiveTower r (π')
      ((Scheme.Modules.pullback (g)).obj (twist 𝒞)) :=
  (isLocallyProjectiveTower_proj 𝒞 r).of_isPullback hsq (Iso.refl _)

include hsqC in
/-- **`𝒪(1)` is trivial on `C' = C ×_E E'`.** -/
def pullbackInclTwistIso :
    (Scheme.Modules.pullback (j' ≫
      g)).obj (twist 𝒞) ≅
      SheafOfModules.unit
        (C').ringCatSheaf :=
  (Scheme.Modules.pullbackCongr hsqC.w.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp q (vectorBundleIncl 𝒞 r)).app (twist 𝒞)).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (pullbackTwistIso 𝒞 r) ≪≫
    Scheme.Modules.pullbackUnitIso _

omit [Flat (proj 𝒞)] in
include hsqC in
/-- **Flat pullback to `C'` kills `c₁(𝒪(1))`**: it intertwines the operation of `c₁(𝒪(1))` on
`E'` with `0`, `𝒪(1)` being trivial on `C'`. -/
theorem intertwines_incl_firstChernTotal :
    Intertwines (fun k => flatPullbackChow C
        (j' ≫
          g ≫ proj 𝒞 ≫ sX)
        (g ≫ proj 𝒞 ≫ sX)
        (j') rfl 0
        (relativeDimension_of_isOpenImmersion _) k
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
          (relativeDimension_of_isOpenImmersion _) k))
      ((TotalChowClass.firstChernTotal C (proj 𝒞 ≫ sX) (twist 𝒞)).op (g))
      0 := by
  let := isFiniteLocallyFreeOfRank_one_of_isInvertible (twist 𝒞)
  rw [TotalChowClass.firstChernTotal_eq_homComponent_totalChern, TotalChowClass.op_homComponent,
    op_totalChern]
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (twist 𝒞) 1
    (g)
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank (twist 𝒞) 1
    (j' ≫ g)
  have h := (GenuineChern.intertwines_chernFamily C (g ≫ proj 𝒞 ≫ sX)
    ((Scheme.Modules.pullback (g)).obj (twist 𝒞)) 1 _
    (j') rfl 0
    (relativeDimension_of_isOpenImmersion _)
    ((Scheme.Modules.pullback (j' ≫
      g)).obj (twist 𝒞))
    ((Scheme.Modules.pullbackComp _ _).app (twist 𝒞)).symm).homComponent 1
  rw [GenuineChern.chernFamily_eq_one_of_iso_unit C _ _ (pullbackInclTwistIso 𝒞 r j' hsqC)] at h
  have h0 : Stacks.Chow.homComponent 1 (1 : GradedCapFamily (chowGroup C
      (j' ≫
        g ≫ proj 𝒞 ≫ sX))) = 0 := by
    funext k i
    rw [Stacks.Chow.homComponent_apply]
    split_ifs with hi
    · subst hi
      exact gradedCap_one_of_ne one_ne_zero k
    · rfl
  rw [h0] at h
  exact h

omit [Flat (proj 𝒞)] in
include hsqC in
/-- **Flat pullback to `C'` kills `c₁(𝒪(1))^i ∩ -` for `i ≥ 1`.** -/
theorem flatPullback_incl_capPow_eq_zero (i : ℕ) (hi : 0 < i) (a b : ℤ) (h : a = b + i)
    (z : chowGroup C (g ≫ proj 𝒞 ≫ sX) a) :
    haveI := isInvertible_pullback (g) (twist 𝒞)
    flatPullbackChow C
        (j' ≫
          g ≫ proj 𝒞 ≫ sX)
        (g ≫ proj 𝒞 ≫ sX)
        (j') rfl 0
        (relativeDimension_of_isOpenImmersion _) b
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
          (relativeDimension_of_isOpenImmersion _) b)
        (capPow C (g ≫ proj 𝒞 ≫ sX)
          (invCap C (g ≫ proj 𝒞 ≫ sX)
            ((Scheme.Modules.pullback (g)).obj (twist 𝒞))) i a b h z) = 0 := by
  have := isInvertible_pullback (g) (twist 𝒞)
  have hint := intertwines_pow (intertwines_incl_firstChernTotal 𝒞 r C sX j' hsqC) i
  rw [zero_pow (Nat.pos_iff_ne_zero.1 hi)] at hint
  have h1 := hint a i z
  rw [Pi.zero_apply, Pi.zero_apply, AddMonoidHom.zero_apply, map_zero] at h1
  refine chowGroup_eq_zero_of_heq C (show b + ((0 : ℕ) : ℤ) = a - i + ((0 : ℕ) : ℤ) by omega) ?_
  refine HEq.trans ?_ (heq_of_eq h1)
  refine flatPullbackChow_heq C _ _ _ rfl 0 (relativeDimension_of_isOpenImmersion _)
    (fun k => flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
      (relativeDimension_of_isOpenImmersion _) k) (by omega) ?_
  refine HEq.trans ?_ (TotalChowClass.op_firstChernTotal_pow_heq C (proj 𝒞 ≫ sX) (twist 𝒞)
    (g) i a z).symm
  exact GenuineChern.capPow_heq C _ _ _ _ rfl rfl (by omega) HEq.rfl

omit [Flat (proj 𝒞)] in
/-- **`c_r(𝒦) ∩ c₁(𝒪(1))^i ∩ - = 0` for `i ≥ 1`**, on `E'`. -/
theorem homComponent_rank_op_pow_eq_zero (i : ℕ) (hi : 0 < i) (a : ℤ)
    (z : chowGroup C (g ≫ proj 𝒞 ≫ sX) a) :
    (TotalChowClass.homComponent r (totalChern C (proj 𝒞 ≫ sX) (kernelModule 𝒞) r)).op
        (g) (a - i) r
      (((TotalChowClass.firstChernTotal C (proj 𝒞 ≫ sX) (twist 𝒞)).op
        (g) ^ i) a i z) = 0 := by
  have hy : ((TotalChowClass.firstChernTotal C (proj 𝒞 ≫ sX) (twist 𝒞)).op
      (g) ^ i).IsHomogeneous i := by
    rw [← TotalChowClass.op_pow]
    exact TotalChowClass.IsHomogeneous.op (isHomogeneous_pow_of_isHomogeneous_one
      (TotalChowClass.isHomogeneous_firstChernTotal C _ (twist 𝒞)) i) _
  have hm := mul_apply_of_isHomogeneous
    (x := (TotalChowClass.homComponent r (totalChern C (proj 𝒞 ≫ sX) (kernelModule 𝒞) r)).op
      (g)) hy (rfl : r + i = r + i) a z
  rw [← TotalChowClass.op_pow, ← TotalChowClass.op_mul] at hm
  have h0 : TotalChowClass.homComponent r (totalChern C (proj 𝒞 ≫ sX) (kernelModule 𝒞) r) *
      TotalChowClass.firstChernTotal C (proj 𝒞 ≫ sX) (twist 𝒞) ^ i = 0 := by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_lt hi
    rw [pow_succ', ← mul_assoc, homComponent_rank_mul_firstChernTotal, zero_mul]
  rw [h0, TotalChowClass.op_zero, Pi.zero_apply, Pi.zero_apply, AddMonoidHom.zero_apply,
    capTo_def] at hm
  rw [← TotalChowClass.op_pow]
  exact (gradedDegreeCast _ _).map_eq_zero_iff.1 hm.symm

include hsq in
/-- The comparison `g^* π^* (𝒞 ⊕ 𝒪_X) ≅ π'^* f^* (𝒞 ⊕ 𝒪_X)` on `E'`. -/
def pullbackModuleIso :
    (Scheme.Modules.pullback (g)).obj
        ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)) ≅
      (Scheme.Modules.pullback (π')).obj
        ((Scheme.Modules.pullback f).obj (module 𝒞)) :=
  (Scheme.Modules.pullbackComp _ _).app (module 𝒞) ≪≫
    (Scheme.Modules.pullbackCongr hsq.w).app (module 𝒞) ≪≫
    ((Scheme.Modules.pullbackComp _ _).app (module 𝒞)).symm

omit [Flat (proj 𝒞)] in
/-- **One term of the expansion of `c_r(𝒦)`, pushed forward to `X'`.** For `β ∈ A_m(X')`, the
class `π'_*(h^j c_{r-j}(π^*(𝒞 ⊕ 𝒪_X)) ∩ π'^* β)` is the operation of Stacks 02TW applied to
`c_{r-j}(f^*(𝒞 ⊕ 𝒪_X)) ∩ β`. -/
theorem pushforward_term_heq (m : ℤ) (β : chowGroup C (f ≫ sX) m) (j : ℕ) (hj : j ≤ r) :
    haveI := isInvertible_pullback (g) (twist 𝒞)
    haveI := isFiniteLocallyFreeOfRank_module 𝒞 r
    haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f (module 𝒞) (r + 1)
    properChowPushforward C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) (m + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
          (snd_comp_eq 𝒞 C sX hsq) (m + r - r))
        (((TotalChowClass.firstChernTotal C (proj 𝒞 ≫ sX) (twist 𝒞) ^ j *
          TotalChowClass.homComponent (r - j)
            (totalChern C (proj 𝒞 ≫ sX) ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞))
              (r + 1))).op (g)) (m + r) r
          (bundlePullback C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
            (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq) m
            β)) ≍
      bundleProjection C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (invCap C (g ≫ proj 𝒞 ≫ sX)
          ((Scheme.Modules.pullback (g)).obj (twist 𝒞)))
        j (m - ((r - j : ℕ) : ℤ)) m (by omega)
        (GenuineChern.chernFamily C (f ≫ sX) ((Scheme.Modules.pullback f).obj (module 𝒞)) (r + 1)
          m (r - j) β) := by
  have := isInvertible_pullback (g) (twist 𝒞)
  have := isFiniteLocallyFreeOfRank_module 𝒞 r
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f (module 𝒞) (r + 1)
  let := pullbackPreservesRank_of_isFiniteLocallyFreeOfRank
    ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞)) (r + 1) (g)
  have hy : ((TotalChowClass.homComponent (r - j)
      (totalChern C (proj 𝒞 ≫ sX) ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞))
        (r + 1))).op (g)).IsHomogeneous (r - j) :=
    TotalChowClass.IsHomogeneous.op (TotalChowClass.isHomogeneous_homComponent _ _) _
  rw [TotalChowClass.op_mul, TotalChowClass.op_pow,
    mul_apply_of_isHomogeneous hy (show j + (r - j) = r by omega), capTo_def]
  refine (properChowPushforward_heq C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
    (π') (snd_comp_eq 𝒞 C sX hsq)
    (show m + r - r = m + r - ((r - j : ℕ) : ℤ) - j by omega)
    (gradedDegreeCast_heq (G := fun k => chowGroup C (g ≫ proj 𝒞 ≫ sX) k)
      _ _)).trans ?_
  refine properChowPushforward_heq C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
    (π') (snd_comp_eq 𝒞 C sX hsq) (by omega) ?_
  refine (TotalChowClass.op_firstChernTotal_pow_heq C (proj 𝒞 ≫ sX) (twist 𝒞)
    (g) j _ _).trans ?_
  refine GenuineChern.capPow_heq C _ _ _ _ rfl (by omega) (by omega) ?_
  rw [TotalChowClass.op_homComponent, Stacks.Chow.homComponent_apply_self, op_totalChern]
  have hI := GenuineChern.intertwines_chernFamily C (f ≫ sX)
    ((Scheme.Modules.pullback f).obj (module 𝒞)) (r + 1) (g ≫ proj 𝒞 ≫ sX)
    (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
    ((Scheme.Modules.pullback (g)).obj
      ((Scheme.Modules.pullback (proj 𝒞)).obj (module 𝒞))) (pullbackModuleIso 𝒞 hsq) m (r - j) β
  exact ((gradedDegreeCast_heq _ _).symm.trans (heq_of_eq hI.symm))

/-- The operation of Stacks 02TW at heterogeneously equal arguments in equal degrees. -/
theorem bundleProjection_heq {P U : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU]
    (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ U) [Flat π]
    [IsProper π] (hsP : π ≫ sU = sP) (n : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π n)
    (ξ : ChernCapOperator C sP) (s : ℕ) {k k' m m' : ℤ} (hk : k = k') (hm : m = m')
    (h : k + n = m + s) (h' : k' + n = m' + s) {x : chowGroup C sU k} {x' : chowGroup C sU k'}
    (hx : x ≍ x') :
    bundleProjection C sU sP π hsP n hπ ξ s k m h x ≍
      bundleProjection C sU sP π hsP n hπ ξ s k' m' h' x' := by
  subst hk hm
  cases hx
  rfl

/-- A graded cap family at equal indices. -/
theorem gradedCapFamily_index_heq {G : ℤ → Type u} [∀ k, AddCommGroup (G k)]
    (a : GradedCapFamily G) {i i' : ℕ} (hi : i = i') (k : ℤ) (x : G k) : a k i x ≍ a k i' x := by
  subst hi
  rfl

omit [Flat (proj 𝒞)] in
/-- **The pushforward of `c_r(𝒦) ∩ π'^* β` is `(-1)^r β`**: in the expansion of `c_r(𝒦)` only the
term `(-h)^r` survives the pushforward to `X'`, by Stacks 02TW, and `c_0 = 1`. -/
theorem pushforward_homComponent_rank_heq (m : ℤ) (β : chowGroup C (f ≫ sX) m) :
    properChowPushforward C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) (m + r - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
          (snd_comp_eq 𝒞 C sX hsq) (m + r - r))
        (((TotalChowClass.homComponent r (totalChern C (proj 𝒞 ≫ sX) (kernelModule 𝒞) r)).op
          (g)) (m + r) r
          (bundlePullback C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
            (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq) m
            β)) ≍
      ((-1 : ℤ) ^ r • β) := by
  have := isInvertible_pullback (g) (twist 𝒞)
  have := isFiniteLocallyFreeOfRank_module 𝒞 r
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback f (module 𝒞) (r + 1)
  rw [homComponent_rank_eq_sum 𝒞 r C (proj 𝒞 ≫ sX), TotalChowClass.op_sum, gradedCap_sum_apply,
    map_sum]
  simp only [TotalChowClass.op_zsmul, Pi.smul_apply, AddMonoidHom.smul_apply, map_zsmul]
  rw [Finset.sum_eq_single r]
  · refine chowGroup_zsmul_heq C (by omega) ?_ _
    refine (pushforward_term_heq 𝒞 r C sX hsq m β r le_rfl).trans ?_
    refine (bundleProjection_heq C _ _ _ _ r _ _ r (x' := β)
      (show m - ((r - r : ℕ) : ℤ) = m by omega) rfl _ (by ring) ?_).trans ?_
    · refine (gradedCapFamily_index_heq _ (Nat.sub_self r) m β).trans ?_
      rw [GenuineChern.chernFamily_apply_zero, gradedCap_one_apply_zero]
      exact gradedDegreeCast_heq _ _
    · exact heq_of_eq ((isLocallyProjectiveTower_snd 𝒞 r hsq).bundleProjection_self C (f ≫ sX) _
        (snd_comp_eq 𝒞 C sX hsq) (relativeDimension_snd 𝒞 r hsq) m β)
  · intro j hj hjr
    have hjr' : j < r := by have := mem_range.1 hj; omega
    rw [chowGroup_eq_zero_of_heq C (show m + r - r = m by omega)
      ((pushforward_term_heq 𝒞 r C sX hsq m β j hjr'.le).trans
      (heq_of_eq (bundleProjection_eq_zero_of_lt C (f ≫ sX) _ _ (snd_comp_eq 𝒞 C sX hsq) r
        (relativeDimension_snd 𝒞 r hsq) _ j hjr' _ _ _ _))), smul_zero]
  · intro hr
    exact absurd (mem_range.2 (Nat.lt_succ_self r)) hr

/-- Flat pullback along a morphism read at two equal relative dimensions. -/
theorem flatPullbackChow_heq_of_dim {Y Z : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (q : Y ⟶ Z) [LocallyOfFiniteType q] [Flat q]
    (hq : q ≫ sZ = sY) {d d' : ℕ} (hdd : d = d') (hd : AlgebraicGeometry.RelativeDimension q d)
    (hd' : AlgebraicGeometry.RelativeDimension q d') (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sY sZ q hq d hd k)
    (hfac' : FlatPullbackFactorsThroughRationalEquivalence C sY sZ q hq d' hd' k)
    (x : chowGroup C sZ k) :
    flatPullbackChow C sY sZ q hq d hd k hfac x ≍
      flatPullbackChow C sY sZ q hq d' hd' k hfac' x := by
  subst hdd
  rfl

omit [LocallyOfFiniteType sX] [LocallyOfFiniteType (proj 𝒞)] [Flat (proj 𝒞)]
  [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Flat π'] [IsProper π']
  [IsOpenImmersion j'] in
include hsq in
/-- The morphism `C' ⟶ E' ⟶ X'` commutes over the base. -/
theorem incl_snd_comp_eq :
    (j' ≫
        π') ≫ f ≫ sX =
      j' ≫
        g ≫ proj 𝒞 ≫ sX := by
  rw [Category.assoc, snd_comp_eq 𝒞 C sX hsq]

omit [Flat (proj 𝒞)] [LocallyOfFiniteType f] [LocallyOfFiniteType g] [Flat π'] in
include hsq in
/-- The morphism `p' : C' ⟶ X'` has relative dimension `r`. -/
theorem relativeDimension_incl_snd :
    AlgebraicGeometry.RelativeDimension
      (j' ≫
        π') r := by
  have h := AlgebraicGeometry.RelativeDimension.comp_of_flat _ _
    (relativeDimension_of_isOpenImmersion
      (j'))
    (relativeDimension_snd 𝒞 r hsq)
  rwa [Nat.zero_add] at h

omit [Flat (proj 𝒞)] in
/-- **Flat pullback to `C'` of a pulled-back class is the flat pullback along `p'`.** -/
theorem flatPullback_incl_bundlePullback_heq (m : ℤ) (b : chowGroup C (f ≫ sX) m) :
    flatPullbackChow C
        (j' ≫
          g ≫ proj 𝒞 ≫ sX)
        (g ≫ proj 𝒞 ≫ sX)
        (j') rfl 0
        (relativeDimension_of_isOpenImmersion _) (m + r)
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
          (relativeDimension_of_isOpenImmersion _) (m + r))
        (bundlePullback C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
          (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq) m b) ≍
      flatPullbackChow C
        (j' ≫
          g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
        (j' ≫
          π') (incl_snd_comp_eq 𝒞 C sX hsq j') r
        (relativeDimension_incl_snd 𝒞 r hsq j') m
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
          (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') m) b := by
  refine (flatPullbackChow_comp C _ _ (f ≫ sX)
    (j')
    (π') rfl (snd_comp_eq 𝒞 C sX hsq) 0 r
    (relativeDimension_of_isOpenImmersion _) (relativeDimension_snd 𝒞 r hsq) m
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
      (relativeDimension_of_isOpenImmersion _) (m + r))
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ (snd_comp_eq 𝒞 C sX hsq) r
      (relativeDimension_snd 𝒞 r hsq) m)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ (0 + r) _ m) b).trans ?_
  exact flatPullbackChow_heq_of_dim C _ _ _ _ (Nat.zero_add r) _ _ m _ _ b

/-- The operation `α ↦ p'^* π'_*(c_r(𝒦) ∩ α)`, `A_k(E') ⟶ A_k(C')`. -/
def lhsHom (k : ℤ) :
    chowGroup C (g ≫ proj 𝒞 ≫ sX) k →+
      chowGroup C (j' ≫
        g ≫ proj 𝒞 ≫ sX) (k - r + r) :=
  (flatPullbackChow C _ (f ≫ sX)
      (j' ≫ π')
      (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') (k - r)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
        (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') (k - r))).comp
    ((properChowPushforward C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) (k - r)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
          (snd_comp_eq 𝒞 C sX hsq) (k - r))).comp
      ((TotalChowClass.homComponent r (totalChern C (proj 𝒞 ≫ sX) (kernelModule 𝒞) r)).op
        (g) k r))

/-- The operation `α ↦ j'^* α`, `A_k(E') ⟶ A_k(C')`. -/
def rhsHom (k : ℤ) :
    chowGroup C (g ≫ proj 𝒞 ≫ sX) k →+
      chowGroup C (j' ≫
        g ≫ proj 𝒞 ≫ sX) (k - r + r) :=
  (chowGroupCast C _ (show k + ((0 : ℕ) : ℤ) = k - r + r by push_cast; ring)).toAddMonoidHom.comp
    (flatPullbackChow C _ (g ≫ proj 𝒞 ≫ sX)
      (j') rfl 0
      (relativeDimension_of_isOpenImmersion _) k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
        (relativeDimension_of_isOpenImmersion _) k))

/-- The transport `A_{k - r + r}(E') ≅ A_k(E')`. -/
abbrev castE {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (k : ℤ) :
    chowGroup C sY (k - r + r) ≃+ chowGroup C sY k :=
  chowGroupCast C _ (by ring)

omit [Flat (proj 𝒞)] in /-- A class on `E'` is a transported `bundleMap`. -/ private theorem
    exists_eq_castE_bundleMap (k : ℤ) (α : chowGroup C (g ≫ proj 𝒞 ≫ sX) k) :
    haveI := isInvertible_pullback (g) (twist 𝒞)
    ∃ β, α = castE r C (g ≫ proj 𝒞 ≫ sX) k (bundleMap C (f ≫ sX) _ _ (snd_comp_eq 𝒞 C sX hsq) r
      (relativeDimension_snd 𝒞 r hsq) (invCap C (g ≫ proj 𝒞 ≫ sX)
        ((Scheme.Modules.pullback (g)).obj (twist 𝒞))) (k - r) β) := by
  have := isInvertible_pullback (g) (twist 𝒞)
  obtain ⟨β, hβ⟩ := (isLocallyProjectiveTower_snd 𝒞 r hsq).bundleMap_surjective C
    (affineBundleSurjectivity C) (f ≫ sX) _ (snd_comp_eq 𝒞 C sX hsq) (relativeDimension_snd 𝒞 r hsq)
    (k - r) ((castE r C (g ≫ proj 𝒞 ≫ sX) k).symm α)
  exact ⟨β, by rw [hβ, AddEquiv.apply_symm_apply]⟩

omit [Flat (proj 𝒞)] in
/-- On the class `π'^* β`, the operation `lhsHom` is `(-1)^r p'^* β`. -/
theorem lhsHom_term_zero (k : ℤ) (b : chowGroup C (f ≫ sX) (k - r + ((0 : ℕ) : ℤ))) :
    haveI := isInvertible_pullback (g) (twist 𝒞)
    lhsHom 𝒞 r C sX hsq j' k (castE r C (g ≫ proj 𝒞 ≫ sX) k
      (bundleTerm C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (invCap C (g ≫ proj 𝒞 ≫ sX)
          ((Scheme.Modules.pullback (g)).obj (twist 𝒞))) (k - r) 0 b)) ≍
      ((-1 : ℤ) ^ r • flatPullbackChow C _ (f ≫ sX)
        (j' ≫
          π') (incl_snd_comp_eq 𝒞 C sX hsq j') r
        (relativeDimension_incl_snd 𝒞 r hsq j') (k - r + ((0 : ℕ) : ℤ))
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
          (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') _) b) := by
  have := isInvertible_pullback (g) (twist 𝒞)
  rw [← map_zsmul]
  refine flatPullbackChow_heq C _ _ _ _ r _
    (fun d => flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
      (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') d)
    (by push_cast; ring)
    ?_
  refine HEq.trans ?_ (pushforward_homComponent_rank_heq 𝒞 r C sX hsq _ b)
  refine properChowPushforward_heq C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
    (π') (snd_comp_eq 𝒞 C sX hsq) (by push_cast; ring) ?_
  refine GradedCapFamily.apply_heq _ (by push_cast; ring) r ?_
  refine (chowGroupCast_heq C _ _ _).trans ?_
  rw [bundleTerm, AddMonoidHom.comp_apply, capPow_zero_apply]
  exact chowGroupCast_heq C _ _ _

omit [Flat (proj 𝒞)] in
/-- On the class `π'^* β`, the operation `rhsHom` is `p'^* β`. -/
theorem rhsHom_term_zero (k : ℤ) (b : chowGroup C (f ≫ sX) (k - r + ((0 : ℕ) : ℤ))) :
    haveI := isInvertible_pullback (g) (twist 𝒞)
    rhsHom 𝒞 r C sX j' k (castE r C (g ≫ proj 𝒞 ≫ sX) k
      (bundleTerm C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (invCap C (g ≫ proj 𝒞 ≫ sX)
          ((Scheme.Modules.pullback (g)).obj (twist 𝒞))) (k - r) 0 b)) ≍
      flatPullbackChow C _ (f ≫ sX)
        (j' ≫
          π') (incl_snd_comp_eq 𝒞 C sX hsq j') r
        (relativeDimension_incl_snd 𝒞 r hsq j') (k - r + ((0 : ℕ) : ℤ))
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
          (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') _) b := by
  have := isInvertible_pullback (g) (twist 𝒞)
  refine (chowGroupCast_heq C _ (show k + ((0 : ℕ) : ℤ) = k - r + r by push_cast; ring) _).trans ?_
  refine HEq.trans ?_ (flatPullback_incl_bundlePullback_heq 𝒞 r C sX hsq j' _ b)
  refine flatPullbackChow_heq C _ _ _ rfl 0 (relativeDimension_of_isOpenImmersion _)
    (fun d => flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
      (relativeDimension_of_isOpenImmersion _) d) (by push_cast; ring) ?_
  refine (chowGroupCast_heq C _ _ _).trans ?_
  rw [bundleTerm, AddMonoidHom.comp_apply, capPow_zero_apply]
  exact chowGroupCast_heq C _ _ _

omit [Flat (proj 𝒞)] in
/-- For `i > 0`, the operation `lhsHom` vanishes on the class `h^i ∩ π'^* β`. -/
theorem lhsHom_term_pos (k : ℤ) (i : ℕ) (hi : 0 < i) (b : chowGroup C (f ≫ sX) (k - r + i)) :
    haveI := isInvertible_pullback (g) (twist 𝒞)
    lhsHom 𝒞 r C sX hsq j' k (castE r C (g ≫ proj 𝒞 ≫ sX) k
      (bundleTerm C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (invCap C (g ≫ proj 𝒞 ≫ sX)
          ((Scheme.Modules.pullback (g)).obj (twist 𝒞))) (k - r) i b)) =
      0 := by
  have := isInvertible_pullback (g) (twist 𝒞)
  have h0 : ((TotalChowClass.homComponent r (totalChern C (proj 𝒞 ≫ sX) (kernelModule 𝒞) r)).op
      (g)) k r (castE r C (g ≫ proj 𝒞 ≫ sX) k
      (bundleTerm C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (invCap C (g ≫ proj 𝒞 ≫ sX)
          ((Scheme.Modules.pullback (g)).obj (twist 𝒞))) (k - r) i b)) =
      0 := by
    refine chowGroup_eq_zero_of_heq C (show k - r = k - r + i + r - i - r by ring) ?_
    refine HEq.trans ?_ (heq_of_eq (homComponent_rank_op_pow_eq_zero 𝒞 r C sX i hi
      (k - r + i + r) (bundlePullback C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (k - r + i) b)))
    refine GradedCapFamily.apply_heq _ (by ring) r ?_
    refine (chowGroupCast_heq C _ _ _).trans ?_
    refine HEq.trans ?_ (TotalChowClass.op_firstChernTotal_pow_heq C (proj 𝒞 ≫ sX) (twist 𝒞)
      (g) i _ _).symm
    exact GenuineChern.capPow_heq C _ _ _ _ rfl rfl (by ring) HEq.rfl
  simp only [lhsHom, AddMonoidHom.comp_apply, h0, map_zero]

omit [Flat (proj 𝒞)] in
include hsqC in
/-- For `i > 0`, the operation `rhsHom` vanishes on the class `h^i ∩ π'^* β`. -/
theorem rhsHom_term_pos (k : ℤ) (i : ℕ) (hi : 0 < i) (b : chowGroup C (f ≫ sX) (k - r + i)) :
    haveI := isInvertible_pullback (g) (twist 𝒞)
    rhsHom 𝒞 r C sX j' k (castE r C (g ≫ proj 𝒞 ≫ sX) k
      (bundleTerm C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (invCap C (g ≫ proj 𝒞 ≫ sX)
          ((Scheme.Modules.pullback (g)).obj (twist 𝒞))) (k - r) i b)) =
      0 := by
  have := isInvertible_pullback (g) (twist 𝒞)
  have h0 : flatPullbackChow C _ (g ≫ proj 𝒞 ≫ sX)
      (j') rfl 0
      (relativeDimension_of_isOpenImmersion _) k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
        (relativeDimension_of_isOpenImmersion _) k) (castE r C (g ≫ proj 𝒞 ≫ sX) k
      (bundleTerm C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (invCap C (g ≫ proj 𝒞 ≫ sX)
          ((Scheme.Modules.pullback (g)).obj (twist 𝒞))) (k - r) i b)) =
      0 := by
    refine chowGroup_eq_zero_of_heq C (show k + ((0 : ℕ) : ℤ) = k - r + r + ((0 : ℕ) : ℤ) by ring)
      ?_
    refine HEq.trans ?_ (heq_of_eq (flatPullback_incl_capPow_eq_zero 𝒞 r C sX j' hsqC i hi
      (k - r + i + r) (k - r + r) (by ring)
      (bundlePullback C (f ≫ sX) (g ≫ proj 𝒞 ≫ sX)
        (π') (snd_comp_eq 𝒞 C sX hsq) r (relativeDimension_snd 𝒞 r hsq)
        (k - r + i) b)))
    exact flatPullbackChow_heq C _ _ _ rfl 0 (relativeDimension_of_isOpenImmersion _)
      (fun d => flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
        (relativeDimension_of_isOpenImmersion _) d) (by ring) (chowGroupCast_heq C _ _ _)
  simp only [rhsHom, AddMonoidHom.comp_apply, h0, map_zero]

omit [Flat (proj 𝒞)] in
include hsqC in
/-- **`p'^* π'_*(c_r(𝒦) ∩ -) = (-1)^r j'^*`** on `A_k(E')`. Both sides are checked on the classes
`h^i ∩ π'^* β` of the projective bundle formula, Stacks 02TX: for `i ≥ 1` both vanish, `c_r(𝒦) h`
being `0` and `h` being trivial on `C'`; for `i = 0` the expansion of `c_r(𝒦)` and Stacks 02TW
give `π'_*(c_r(𝒦) ∩ π'^* β) = (-1)^r β`, while `j'^* π'^* = p'^*`. -/
theorem lhsHom_eq (k : ℤ) : lhsHom 𝒞 r C sX hsq j' k = (-1 : ℤ) ^ r • rhsHom 𝒞 r C sX j' k := by
  have := isInvertible_pullback (g) (twist 𝒞)
  refine AddMonoidHom.ext fun α => ?_
  obtain ⟨β, hα⟩ := exists_eq_castE_bundleMap 𝒞 r C sX hsq k α
  rw [hα, bundleMap_apply, map_sum, map_sum, AddMonoidHom.smul_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨i, hi⟩ := i
  rcases i with _ | i
  · exact eq_of_heq ((lhsHom_term_zero 𝒞 r C sX hsq j' k _).trans
      (chowGroup_zsmul_heq C (by push_cast; ring) (rhsHom_term_zero 𝒞 r C sX hsq j' k _) _).symm)
  · rw [lhsHom_term_pos 𝒞 r C sX hsq j' k (i + 1) (Nat.succ_pos i),
      rhsHom_term_pos 𝒞 r C sX hsq j' hsqC k (i + 1) (Nat.succ_pos i), smul_zero]

omit [Flat (proj 𝒞)] in
/-- **The case `r = 0`**: `c_0 = 1` and `π'_* π'^* = 1`, so `p'^* π'_*(c_0(i_*𝒪_X) ∩ -) = j'^*`. -/
theorem lhs_eq_rhsHom_of_eq_zero (hr : r = 0) (k : ℤ)
    (α : chowGroup C (g ≫ proj 𝒞 ≫ sX) k) :
    flatPullbackChow C (j' ≫
          g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
        (j' ≫
          π') (incl_snd_comp_eq 𝒞 C sX hsq j') r
        (relativeDimension_incl_snd 𝒞 r hsq j') (k - r)
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
          (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') (k - r))
        (properChowPushforward C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
          (π') (snd_comp_eq 𝒞 C sX hsq) (k - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
            (snd_comp_eq 𝒞 C sX hsq) (k - r))
          ((perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)).op
            (g) k r α)) = rhsHom 𝒞 r C sX j' k α := by
  subst hr
  have := isInvertible_pullback (g) (twist 𝒞)
  have h0 : ∀ y : chowGroup C (g ≫ proj 𝒞 ≫ sX) k,
      (perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 0)).op
        (g) k 0 y = gradedDegreeCast _ (by simp) y := by
    intro y
    rw [TotalChowClass.op_apply, perfectChernClass_apply_zero, ← TotalChowClass.op_apply,
      TotalChowClass.op_one, gradedCap_one_apply_zero]
  obtain ⟨β, hα⟩ := exists_eq_castE_bundleMap 𝒞 0 C sX hsq k α
  rw [hα, bundleMap_apply, map_sum, Fin.sum_univ_one, h0]
  refine eq_of_heq (HEq.trans ?_ (rhsHom_term_zero 𝒞 0 C sX hsq j' k (β 0)).symm)
  refine flatPullbackChow_heq C _ _ _ _ 0 _
    (fun d => flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
      (incl_snd_comp_eq 𝒞 C sX hsq j') 0 (relativeDimension_incl_snd 𝒞 0 hsq j') d)
    (by push_cast; ring)
    ?_
  refine HEq.trans ?_ (heq_of_eq ((isLocallyProjectiveTower_snd 𝒞 0 hsq).bundleProjection_self C
    (f ≫ sX) _ (snd_comp_eq 𝒞 C sX hsq) (relativeDimension_snd 𝒞 0 hsq) _ (β 0)))
  refine properChowPushforward_heq C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
    (π') (snd_comp_eq 𝒞 C sX hsq) (by simp) ?_
  exact (gradedDegreeCast_heq _ _).trans (chowGroupCast_heq C _ _ _)

omit [Flat (proj 𝒞)] in
include hsqC in
/-- **The second conclusion of Stacks 0FEF on a cartesian square.** For `E'` the base change of
the projective completion along `f : X' ⟶ X`, with projections `g : E' ⟶ E` and `π' : E' ⟶ X'`,
and `j' : C' ⟶ E'` the base change of the inclusion `j : C ⟶ E` of the vector bundle along `g`,
`p'^* π'_*(c_r(i_*𝒪_X) ∩ α) = (-1)^{r-1} (r-1)! j'^* α` for `α ∈ A_k(E')`, with
`p' = π' ∘ j'`. -/
theorem flatPullbackChow_properChowPushforward_perfectChernClass_of_isPullback (k : ℤ)
    (α : chowGroup C (g ≫ proj 𝒞 ≫ sX) k) :
    flatPullbackChow C (j' ≫
          g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
        (j' ≫
          π') (incl_snd_comp_eq 𝒞 C sX hsq j') r
        (relativeDimension_incl_snd 𝒞 r hsq j') (k - r)
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
          (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') (k - r))
        (properChowPushforward C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX)
          (π') (snd_comp_eq 𝒞 C sX hsq) (k - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
            (snd_comp_eq 𝒞 C sX hsq) (k - r))
          ((perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)).op
            (g) k r α)) =
      chowGroupCast C _ (show k + ((0 : ℕ) : ℤ) = k - r + r by push_cast; ring)
        (((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
          flatPullbackChow C _ (g ≫ proj 𝒞 ≫ sX)
            (j') rfl 0
            (relativeDimension_of_isOpenImmersion _) k
            (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
              (relativeDimension_of_isOpenImmersion _) k) α) := by
  by_cases hr : r = 0
  · rw [lhs_eq_rhsHom_of_eq_zero 𝒞 r C sX hsq j' hr]
    subst hr
    rw [Nat.zero_sub, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, one_smul]
    rfl
  have hc : (perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)).op
      (g) k r α =
      -(((r - 1).factorial : ℤ) • ((TotalChowClass.homComponent r
        (totalChern C (proj 𝒞 ≫ sX) (kernelModule 𝒞) r)).op (g) k r α)) := by
    have h1 : (perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)).op
        (g) k r α =
        (TotalChowClass.homComponent r (perfectChernClass C (proj 𝒞 ≫ sX)
          (hasDefinedChernClasses_zeroSecObject 𝒞 r))).op (g) k r α := by
      rw [TotalChowClass.op_homComponent, Stacks.Chow.homComponent_apply_self]
    rw [h1, homComponent_perfectChernClass_zeroSecObject_rank 𝒞 r C sX hr, ← natCast_zsmul,
      TotalChowClass.op_neg, TotalChowClass.op_zsmul]
    rfl
  rw [hc, map_neg, map_zsmul, map_neg, map_zsmul]
  change -(((r - 1).factorial : ℤ) • lhsHom 𝒞 r C sX hsq j' k α) = _
  rw [lhsHom_eq 𝒞 r C sX hsq j' hsqC, AddMonoidHom.smul_apply, map_zsmul]
  change _ = _ • rhsHom 𝒞 r C sX j' k α
  rw [smul_smul, ← neg_smul]
  congr 1
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  rw [Nat.succ_sub_one, pow_succ]
  ring

end BaseChange

section Main

variable (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  {X' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f]

omit [LocallyOfFiniteType f] in
/-- **`C' = C ×_E E'` is `C ×_X X'`**: the morphism `p' : C' ⟶ E' ⟶ X'` is the base change of the
structure morphism `p : C ⟶ X` of the vector bundle along `f`. -/
theorem isPullback_incl_snd :
    IsPullback (pullback.fst (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞) f))
      (pullback.snd (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞) f) ≫ pullback.snd (proj 𝒞) f)
      (Scheme.Modules.vectorBundleToBase X 𝒞) f := by
  rw [← vectorBundleIncl_proj 𝒞 r]
  exact (IsPullback.of_hasPullback _ _).paste_vert (IsPullback.of_hasPullback _ _)

/-- **Stacks 0FEF, the second conclusion**: `p^* ∘ π_* ∘ c_r(i_*𝒪_X) = (-1)^{r-1} (r-1)! j^*` in
`A⁰(C ⟶ E)`, read on the classes of the schemes `E' = E ×_X X'` for `f : X' ⟶ X` locally of
finite type, as in the proof of the source.

Here `π : E = Proj_X(Sym^*(𝒞)[T]) ⟶ X` is the projective completion of a locally free module `𝒞`
of rank `r ≥ 1`, `i : X ⟶ E` its zero section, `j : C = Spec_X(Sym^*(𝒞)) ⟶ E` the inclusion of
the vector bundle and `p : C ⟶ X` its structure morphism. For `f : X' ⟶ X`, write
`π' : E' ⟶ X'` for the base change of `π`, `j' : C' = C ×_E E' ⟶ E'` for the base change of `j`
and `p' = π' ∘ j' : C' ⟶ X'`, the base change of `p` (`isPullback_incl_snd`). Then for every
`α ∈ A_k(E')`,

  `p'^* π'_*(c_r(i_*𝒪_X) ∩ α) = (-1)^{r-1} (r-1)! j'^* α`  in `A_k(C')`,

where `c_r(i_*𝒪_X)` is the Chern class of Stacks 0F9E of the perfect object `i_*𝒪_X` of
`D(𝒪_E)` and `- ∩ α` its operation on `E' ⟶ E`. The two sides are read in the degrees
`(k - r) + r` and `k + 0` produced by flat pullback, compared by the transport between them. -/
theorem flatPullbackChow_properChowPushforward_perfectChernClass (k : ℤ)
    (α : chowGroup C (pullback.fst (proj 𝒞) f ≫ proj 𝒞 ≫ sX) k) :
    haveI := locallyOfFiniteType_proj 𝒞 r
    haveI := flat_proj 𝒞 r
    flatPullbackChow C (pullback.snd (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞) f) ≫
          pullback.fst (proj 𝒞) f ≫ proj 𝒞 ≫ sX) (f ≫ sX)
        (pullback.snd (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞) f) ≫
          pullback.snd (proj 𝒞) f)
        (incl_snd_comp_eq 𝒞 C sX (IsPullback.of_hasPullback (proj 𝒞) f) _) r
        (relativeDimension_incl_snd 𝒞 r (IsPullback.of_hasPullback (proj 𝒞) f) _) (k - r)
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
          (incl_snd_comp_eq 𝒞 C sX (IsPullback.of_hasPullback (proj 𝒞) f) _) r
          (relativeDimension_incl_snd 𝒞 r (IsPullback.of_hasPullback (proj 𝒞) f) _) (k - r))
        (properChowPushforward C (pullback.fst (proj 𝒞) f ≫ proj 𝒞 ≫ sX) (f ≫ sX)
          (pullback.snd (proj 𝒞) f) (snd_comp_eq 𝒞 C sX (IsPullback.of_hasPullback (proj 𝒞) f))
          (k - r)
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
            (snd_comp_eq 𝒞 C sX (IsPullback.of_hasPullback (proj 𝒞) f)) (k - r))
          ((perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)).op
            (pullback.fst (proj 𝒞) f) k r α)) =
      chowGroupCast C _ (show k + ((0 : ℕ) : ℤ) = k - r + r by push_cast; ring)
        (((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
          flatPullbackChow C _ (pullback.fst (proj 𝒞) f ≫ proj 𝒞 ≫ sX)
            (pullback.snd (vectorBundleIncl 𝒞 r) (pullback.fst (proj 𝒞) f)) rfl 0
            (relativeDimension_of_isOpenImmersion _) k
            (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
              (relativeDimension_of_isOpenImmersion _) k) α) := by
  have := locallyOfFiniteType_proj 𝒞 r
  have := flat_proj 𝒞 r
  exact flatPullbackChow_properChowPushforward_perfectChernClass_of_isPullback 𝒞 r C sX
    (IsPullback.of_hasPullback (proj 𝒞) f) _ (IsPullback.of_hasPullback _ _) k α

/-- **Stacks 0FEF.** Let `𝒞` be a locally free `𝒪_X`-module of rank `r` on `X` locally of finite
type over the base of chapter 42, `π : E = Proj_X(Sym^*(𝒞)[T]) ⟶ X` its projective completion with
zero section `i : X ⟶ E`, and `j : C = Spec_X(Sym^*(𝒞)) ⟶ E`, `p : C ⟶ X` the inclusion and the
structure morphism of the vector bundle. Then

1. `c_t(i_*𝒪_X) = 0` for `t = 1, …, r - 1`, and
2. `p^* ∘ π_* ∘ c_r(i_*𝒪_X) = (-1)^{r-1} (r-1)! j^*`, as operations on every test scheme
   `g : E' ⟶ E` on which the left-hand side is defined: for every cartesian square
   `E' = E ×_X X'` over `f : X' ⟶ X` locally of finite type, with `π' : E' ⟶ X'`, every
   cartesian square `C' = C ×_E E'` with `j' : C' ⟶ E'`, and every `α ∈ A_k(E')`,
   `p'^* π'_*(c_r(i_*𝒪_X) ∩ α) = (-1)^{r-1} (r-1)! j'^* α` in `A_k(C')`, where `p' = π' ∘ j'`.

The Chern classes are those of Stacks 0F9E of the perfect object `i_*𝒪_X` of `D(𝒪_E)`, and
`c_r(i_*𝒪_X) ∩ α` is the operation of `c_r(i_*𝒪_X) ∈ A^r(E)` on the test scheme `g`.

On the reading of (2). In the conventions of bivariant classes, `c_r(i_*𝒪_X) ∈ A^r(E ⟶ E)` and the
pushforward `π_* ∘ -` of Stacks 0EPK applies to a class of `A^*(E ⟶ Z)` for a morphism `E ⟶ Z`
factoring through `π`, so `p^* ∘ π_* ∘ c_r(i_*𝒪_X)` is not a composite of bivariant classes landing
in `A⁰(C ⟶ E)`. The operation it names is defined on those test schemes `E' ⟶ E` that are base
changes of `π`, where `π'_*` exists, and these are the test schemes on which the proof of the
source compares the two sides ("after replacing `X` by a scheme locally of finite type over
`X` ... both sides have the same effect on `α ∈ CH_*(E)`"). Statement (2) is the identity of the
two operations at every such test scheme. -/
@[stacks 0FEF "both conclusions: (1) c_t(i_*O_X) = 0 for t = 1, ..., r - 1; (2) \
p^* o pi_* o c_r(i_*O_X) = (-1)^(r-1) (r-1)! j^*, as an identity of operations at every test \
scheme E' -> E on which the left side is defined, namely every base change E' = E x_X X' of pi \
along f : X' -> X locally of finite type (any cartesian square), with C' = C x_E E' any cartesian \
square: p'^* pi'_* (c_r(i_*O_X) cap alpha) = (-1)^(r-1) (r-1)! j'^* alpha for alpha in A_k(E'). \
In the bivariant conventions c_r(i_*O_X) lies in A^r(E -> E) and the pushforward of 0EPK needs a \
class over a morphism factoring through pi, so the left side is not a composite of bivariant \
classes in A^0(C -> E); its operation exists exactly on these test schemes, which are those on \
which the source's proof compares the two sides"]
theorem chernClasses_zeroSecObject :
    (letI := locallyOfFiniteType_proj_comp 𝒞 r C sX
      ∀ t : ℕ, 0 < t → t < r →
        perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r) t = 0) ∧
    ∀ {X' E' C' : Scheme.{u}} (f : X' ⟶ X) [LocallyOfFiniteType f] (g : E' ⟶ space 𝒞)
      (π' : E' ⟶ X') (hsq : IsPullback g π' (proj 𝒞) f)
      (q : C' ⟶ Scheme.Modules.vectorBundle X 𝒞) (j' : C' ⟶ E')
      (hsqC : IsPullback q j' (vectorBundleIncl 𝒞 r) g) (k : ℤ),
      haveI := locallyOfFiniteType_proj 𝒞 r
      haveI := flat_proj 𝒞 r
      haveI : LocallyOfFiniteType g := MorphismProperty.of_isPullback hsq.flip inferInstance
      haveI : LocallyOfFiniteType π' := MorphismProperty.of_isPullback hsq inferInstance
      haveI : Flat π' := MorphismProperty.of_isPullback hsq inferInstance
      haveI : IsProper π' := MorphismProperty.of_isPullback hsq inferInstance
      haveI : IsOpenImmersion j' := MorphismProperty.of_isPullback hsqC inferInstance
      ∀ α : chowGroup C (g ≫ proj 𝒞 ≫ sX) k,
      flatPullbackChow C (j' ≫ g ≫ proj 𝒞 ≫ sX) (f ≫ sX) (j' ≫ π')
          (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') (k - r)
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _
            (incl_snd_comp_eq 𝒞 C sX hsq j') r (relativeDimension_incl_snd 𝒞 r hsq j') (k - r))
          (properChowPushforward C (g ≫ proj 𝒞 ≫ sX) (f ≫ sX) π' (snd_comp_eq 𝒞 C sX hsq) (k - r)
            (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ _ _
              (snd_comp_eq 𝒞 C sX hsq) (k - r))
            ((perfectChernClass C (proj 𝒞 ≫ sX) (hasDefinedChernClasses_zeroSecObject 𝒞 r)).op
              g k r α)) =
        chowGroupCast C _ (show k + ((0 : ℕ) : ℤ) = k - r + r by push_cast; ring)
          (((-1 : ℤ) ^ (r - 1) * ((r - 1).factorial : ℤ)) •
            flatPullbackChow C _ (g ≫ proj 𝒞 ≫ sX) j' rfl 0
              (relativeDimension_of_isOpenImmersion _) k
              (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ rfl 0
                (relativeDimension_of_isOpenImmersion _) k) α) :=
  ⟨perfectChernClass_zeroSecObject_eq_zero 𝒞 r C sX,
    fun _f _ g π' hsq _q j' hsqC k α =>
      have := locallyOfFiniteType_proj 𝒞 r
      have := flat_proj 𝒞 r
      have : LocallyOfFiniteType g := MorphismProperty.of_isPullback hsq.flip inferInstance
      have : LocallyOfFiniteType π' := MorphismProperty.of_isPullback hsq inferInstance
      have : Flat π' := MorphismProperty.of_isPullback hsq inferInstance
      have : IsProper π' := MorphismProperty.of_isPullback hsq inferInstance
      have : IsOpenImmersion j' := MorphismProperty.of_isPullback hsqC inferInstance
      flatPullbackChow_properChowPushforward_perfectChernClass_of_isPullback 𝒞 r C sX hsq j' hsqC
        k α⟩

end Main

end Stacks.Chow.ProjectiveCompletion

end
