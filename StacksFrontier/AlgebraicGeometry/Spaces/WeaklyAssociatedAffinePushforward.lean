module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Weakly associated points of an affine direct image

Let `f : X → Y` be an affine morphism of algebraic spaces with `X` locally Noetherian and let
`F` be a quasi-coherent `𝒪_X`-module. Then `WeakAss(f_*F) = f(WeakAss(F))`. The inclusion from
right to left is obtained here from a presentation of the two geometric stalks as flat base
changes of one module of sections over an affine étale chart.

## Main definitions

* `AlgebraicGeometry.Space.HasAffineStalkSquare`: the geometric stalks of `F` at `x̄` and of
  `G` at a geometric point over the image of `x̄` are base changes of one module along a
  commuting square of flat ring maps whose vertical maps are local.

## Main results

* `IsWeaklyAssociatedPrime.tensorProduct_of_flat_square`: weak association of the maximal
  ideal transports across a commuting square of flat base changes of one module.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_hasAffineStalkSquare`: such a square
  carries weak association at `x̄` to weak association at the image point.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_modulePushforward_eq_image_of_isAffineHom`:
  the equality of sets of points, from the stalk squares and the inclusion `⊆`. Stacks 0CU8
  without these inputs is
  `weaklyAssociatedPoints_modulePushforward_eq_image_of_isAffineHom_locallyNoetherian`.

## Implementation notes

The commutative algebra rests on the flat base-change description of associated primes of
Stacks 0312: over a Noetherian ring the associated primes of `A' ⊗_A M` lie over associated
primes of `M`, and conversely an associated prime of `M` whose extension to a flat algebra is
prime is associated to the base change. Weak and ordinary association agree over a Noetherian
ring, which is how the two are interchanged below.

The geometric input is isolated in `AlgebraicGeometry.Space.HasAffineStalkSquare`, which
records the data the source's chart argument produces at a geometric point: an affine étale
chart `U` of `X` above an affine étale chart `V` of `Y`, the module `M = F(U)` of sections over
it, and the identifications `F_{x̄} = 𝒪_{X, x̄} ⊗_{Γ(U)} M` and `(f_*F)_{ȳ} = 𝒪_{Y, ȳ} ⊗_{Γ(V)} M`
of Stacks 05VP together with the quasi-coherence of the direct image of Stacks 03M9. The
pushforward functor used is the one of Stacks 03LU on modules with sections in the same
universe as the site.

## References

* [Stacks Project, Lemma 71.2.2 (Tag 0CU8)](https://stacks.math.columbia.edu/tag/0CU8)
* [Stacks Project, Tag 05EY](https://stacks.math.columbia.edu/tag/05EY)
* [Stacks Project, Tag 0312](https://stacks.math.columbia.edu/tag/0312)
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u

section CommutativeAlgebra

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Restriction of scalars along `R → A` carries an associated prime of an `A`-module to the
associated prime of the underlying `R`-module obtained by contraction. -/
@[ega "IV 3.1.10.1" "Contraction inclusion"]
theorem IsAssociatedPrimeStacks.comap [AddCommGroup M] [Module A M] [Module R M]
    [IsScalarTower R A M] {p : Ideal A} (hp : IsAssociatedPrimeStacks A M p) :
    IsAssociatedPrimeStacks R M (Ideal.comap (algebraMap R A) p) := by
  obtain ⟨hp, m, hann⟩ := hp
  refine ⟨hp.comap (algebraMap R A), m, ?_⟩
  rw [← hann]
  ext r
  simp only [Ideal.mem_comap, Submodule.colon_span, Submodule.mem_colon_singleton,
    Submodule.mem_bot, algebraMap_smul]

/-- `IsAssociatedPrimeStacks` with the colon ideal taken against a singleton set. -/
private theorem isAssociatedPrimeStacks_iff_colon_singleton [AddCommGroup M] [Module R M]
    {p : Ideal R} : IsAssociatedPrimeStacks R M p ↔
      p.IsPrime ∧ ∃ m : M, (⊥ : Submodule R M).colon {m} = p := by
  simp only [IsAssociatedPrimeStacks, Submodule.colon_span]

/-- An associated prime in the source's sense is weakly associated. -/
theorem IsAssociatedPrimeStacks.isWeaklyAssociatedPrime [AddCommGroup M] [Module R M]
    {p : Ideal R} (hp : IsAssociatedPrimeStacks R M p) : IsWeaklyAssociatedPrime R M p := by
  obtain ⟨hp, m, hm⟩ := hp
  rw [Submodule.bot_colon] at hm
  rw [← hm] at hp ⊢
  exact ⟨m, ⟨⟨hp, le_rfl⟩, fun q hq _ => hq.2⟩⟩

/-- Over a Noetherian ring a weakly associated prime is associated in the source's sense. -/
theorem IsWeaklyAssociatedPrime.isAssociatedPrimeStacks [IsNoetherianRing R] [AddCommGroup M]
    [Module R M] {p : Ideal R} (hp : IsWeaklyAssociatedPrime R M p) :
    IsAssociatedPrimeStacks R M p := by
  obtain ⟨hp, m, hm⟩ :=
    ((isAssociatedPrime_tfae_of_fg (M := M) p.fg_of_isNoetherianRing).out 3 1).mp hp
  exact isAssociatedPrimeStacks_iff_colon_singleton.mpr
    ⟨hp, m, by simpa only [Submodule.bot_colon'] using hm.symm⟩

/-- Weak association of an ideal is invariant under a linear equivalence of modules. -/
theorem IsWeaklyAssociatedPrime.of_linearEquiv {N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) {p : Ideal R}
    (hp : IsWeaklyAssociatedPrime R M p) : IsWeaklyAssociatedPrime R N p := by
  obtain ⟨m, hm⟩ := hp
  refine ⟨e m, ?_⟩
  have hann : (R ∙ e m).annihilator = (R ∙ m).annihilator := by
    ext r
    simp only [Submodule.mem_annihilator_span_singleton]
    rw [← e.map_smul, e.map_eq_zero_iff]
  simpa [hann] using hm

variable {N : Type*} [AddCommGroup N] [Module A N] [Module R N] [IsScalarTower R A N]

private theorem smul_mem_ideal_smul_top (I : Ideal R) (a : A) {n : N}
    (hn : n ∈ I • (⊤ : Submodule R N)) : a • n ∈ I • (⊤ : Submodule R N) := by
  refine Submodule.smul_induction_on hn ?_ fun n₁ n₂ h₁ h₂ => ?_
  · intro r hr n _
    rw [smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [smul_add]
    exact add_mem h₁ h₂

private theorem mem_map_smul_top_iff (I : Ideal R) (n : N) :
    n ∈ I.map (algebraMap R A) • (⊤ : Submodule A N) ↔ n ∈ I • (⊤ : Submodule R N) := by
  constructor
  · intro hn
    refine Submodule.smul_induction_on hn ?_ fun n₁ n₂ h₁ h₂ => add_mem h₁ h₂
    intro a ha n _
    rw [Ideal.map, Ideal.span] at ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨r, hr, rfl⟩ := ha
        rw [algebraMap_smul]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
    | zero => simp
    | add a₁ a₂ _ _ h₁ h₂ =>
        rw [add_smul]
        exact add_mem h₁ h₂
    | smul a₁ a₂ _ h =>
        rw [smul_eq_mul, mul_smul]
        exact smul_mem_ideal_smul_top I a₁ h
  · intro hn
    refine Submodule.smul_induction_on hn ?_ fun n₁ n₂ h₁ h₂ => add_mem h₁ h₂
    intro r hr n _
    rw [← algebraMap_smul A r n]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top

/-- Killing the extension of an ideal `I` of `R` on an `A`-module `N` computes the tensor
product of `N` with `R ⧸ I`. -/
private noncomputable def quotientSMulEquivTensorQuotient (I : Ideal R) :
    (N ⧸ (I.map (algebraMap R A) • (⊤ : Submodule A N))) ≃ₗ[A] N ⊗[R] (R ⧸ I) := by
  let t := (TensorProduct.AlgebraTensorModule.mk R A N (R ⧸ I)).flip 1
  have hker : LinearMap.ker t = I.map (algebraMap R A) • (⊤ : Submodule A N) := by
    ext n
    change n ⊗ₜ[R] (1 : R ⧸ I) = 0 ↔ _
    rw [← TensorProduct.tensorQuotEquivQuotSMul_symm_mk I n, LinearEquiv.map_eq_zero_iff,
      Submodule.Quotient.mk_eq_zero, mem_map_smul_top_iff]
  have hsurj : Function.Surjective t := by
    intro n
    obtain ⟨m, hm⟩ := ((TensorProduct.tensorQuotEquivQuotSMul N I).symm.surjective.comp
      (Submodule.mkQ_surjective (I • (⊤ : Submodule R N)))) n
    exact ⟨m, by simpa [t, TensorProduct.tensorQuotEquivQuotSMul_symm_mk] using hm⟩
  exact LinearEquiv.ofBijective (Submodule.liftQ _ t hker.ge)
    ⟨LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ hker.symm), by
      rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_eq_top]
      exact hsurj⟩

/-- **Stacks 0312**, one half: over a Noetherian ring an associated prime of a flat base change
`A ⊗_R M` contracts to an associated prime of `M`. -/
theorem IsAssociatedPrimeStacks.comap_of_tensorProduct_of_flat [IsNoetherianRing R]
    [Module.Flat R A] [AddCommGroup M] [Module R M] {p : Ideal A}
    (hp : IsAssociatedPrimeStacks A (A ⊗[R] M) p) :
    IsAssociatedPrime (Ideal.comap (algebraMap R A) p) M := by
  have hformula :=
    (associatedPrimes.tensorProduct_of_flat (R := R) (S := A) (M := M) (N := A)).2 inferInstance
  have hmem : p ∈ {q : Ideal A | q.IsPrime ∧
      ∃ w : A ⊗[R] M, (⊥ : Submodule A (A ⊗[R] M)).colon {w} = q} := by
    exact isAssociatedPrimeStacks_iff_colon_singleton.mp hp
  rw [hformula] at hmem
  obtain ⟨p₀, hp₀, hquot⟩ := Set.mem_iUnion₂.mp hmem
  have hp₀' : p₀.IsPrime := hp₀.isPrime
  rcases hquot with ⟨hpprime, w, hw⟩
  have hle : p₀ ≤ Ideal.comap (algebraMap R A) p := by
    intro r hr
    rw [Ideal.mem_comap, ← hw, Submodule.mem_colon_singleton, Submodule.mem_bot]
    obtain ⟨a, rfl⟩ :=
      Submodule.Quotient.mk_surjective (Ideal.map (algebraMap R A) p₀ • (⊤ : Submodule A A)) w
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem (algebraMap R A) hr) Submodule.mem_top
  have hge : Ideal.comap (algebraMap R A) p ≤ p₀ := by
    intro r hr
    by_contra hnot
    have hregular : IsSMulRegular (R ⧸ p₀) r := by
      refine (isSMulRegular_quotient_iff_mem_of_smul_mem (p₀ : Submodule R R) r).mpr ?_
      intro s hs
      exact (hp₀'.mem_or_mem hs).resolve_left hnot
    let mul := (r • LinearMap.id : R ⧸ p₀ →ₗ[R] R ⧸ p₀)
    have hinj : Function.Injective (LinearMap.lTensor A mul) :=
      Module.Flat.lTensor_preserves_injective_linearMap mul hregular
    have hregular' : IsSMulRegular (A ⊗[R] (R ⧸ p₀)) r := by
      have heq : LinearMap.lTensor A mul = r • (LinearMap.id : A ⊗[R] (R ⧸ p₀) →ₗ[R] _) := by
        ext a
        simp [mul]
      rw [heq] at hinj
      exact hinj
    have hann : algebraMap R A r • w = 0 := by
      have hr' := hr
      rw [Ideal.mem_comap, ← hw, Submodule.mem_colon_singleton, Submodule.mem_bot] at hr'
      exact hr'
    let e := quotientSMulEquivTensorQuotient (A := A) (N := A) p₀
    have hzero : w = 0 := by
      refine e.injective (hregular' ?_)
      change r • e w = r • e 0
      rw [map_zero, smul_zero, ← algebraMap_smul A, ← e.map_smul, hann, map_zero]
    exact hpprime.one_notMem (by
      rw [← hw, Submodule.mem_colon_singleton, Submodule.mem_bot, hzero, smul_zero])
  exact (le_antisymm hge hle).symm ▸ hp₀

/-- **Stacks 0312**, the other half: an associated prime of `M` whose extension along a flat
algebra is prime is associated to the base change `A ⊗_R M`. -/
theorem IsAssociatedPrimeStacks.tensorProduct_of_map_eq [AddCommGroup M] [Module R M]
    [Module.Flat R A] {p : Ideal R} {q : Ideal A} (hp : IsAssociatedPrimeStacks R M p)
    (hq : q.IsPrime) (hmap : p.map (algebraMap R A) = q) :
    IsAssociatedPrimeStacks A (A ⊗[R] M) q := by
  have hformula :=
    (associatedPrimes.tensorProduct_of_flat (R := R) (S := A) (M := M) (N := A)).1
  have hp' : p ∈ {q : Ideal R | q.IsPrime ∧
      ∃ m : M, (⊥ : Submodule R M).colon {m} = q} := by
    exact isAssociatedPrimeStacks_iff_colon_singleton.mp hp
  have hmem : q ∈ {q : Ideal A | q.IsPrime ∧
      ∃ w : A ⧸ (p.map (algebraMap R A) • (⊤ : Submodule A A)),
        (⊥ : Submodule A (A ⧸ (p.map (algebraMap R A) • (⊤ : Submodule A A)))).colon {w} = q} := by
    refine ⟨hq, Submodule.Quotient.mk (1 : A), ?_⟩
    ext a
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul, mul_one, hmap, Ideal.mul_top]
  exact isAssociatedPrimeStacks_iff_colon_singleton.mpr
    (hformula (Set.mem_iUnion₂.mpr ⟨p, hp', hmem⟩))

/-- Weak association transports across a commuting square of flat base changes of one module:
if the maximal ideal of `A'` is weakly associated to `A' ⊗_A M` and contracts through `A` and
`R` to an ideal whose extension to `R'` is the prime `q`, then `q` is weakly associated to
`R' ⊗_R M`. -/
theorem IsWeaklyAssociatedPrime.tensorProduct_of_flat_square {R A R' A' M : Type*} [CommRing R]
    [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra A A'] [Algebra R R']
    [IsNoetherianRing A] [IsNoetherianRing A'] [Module.Flat A A'] [Module.Flat R R']
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] {p : Ideal A'}
    {q : Ideal R'} (hq : q.IsPrime)
    (hmap : (Ideal.comap (algebraMap R A) (Ideal.comap (algebraMap A A') p)).map
      (algebraMap R R') = q)
    (hp : IsWeaklyAssociatedPrime A' (A' ⊗[A] M) p) :
    IsWeaklyAssociatedPrime R' (R' ⊗[R] M) q := by
  obtain ⟨hprime, m, hm⟩ :=
    isAssociatedPrime_iff.mp hp.isAssociatedPrimeStacks.comap_of_tensorProduct_of_flat
  have hA : IsAssociatedPrimeStacks A M (Ideal.comap (algebraMap A A') p) :=
    isAssociatedPrimeStacks_iff_colon_singleton.mpr ⟨hprime, m, hm.symm⟩
  exact (hA.comap (R := R)).tensorProduct_of_map_eq hq hmap |>.isWeaklyAssociatedPrime

end CommutativeAlgebra

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- The affine chart presentation of a pair of geometric stalks at a geometric point `x̄` of `X`:
a geometric point `ȳ` of `Y` over the image of `x̄`, rings of sections `R` and `A` over affine
étale charts of `Y` and of `X` above it, a module `M` of sections of `F` over the chart of `X`,
and identifications `F_{x̄} = 𝒪_{X, x̄} ⊗_A M` and `G_{ȳ} = 𝒪_{Y, ȳ} ⊗_R M` along flat maps for
which the maximal ideal of `𝒪_{X, x̄}` contracts and extends to that of `𝒪_{Y, ȳ}`. -/
def HasAffineStalkSquare (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (xbar : GeometricPoint B S hS X.1) : Prop :=
  ∃ ybar : GeometricPoint B S hS Y.1,
    ybar.LiesOver (pointsMap B S hS X.1 f.hom xbar.image) ∧
    ∃ (R A M : Type u) (_ : CommRing R) (_ : CommRing A) (_ : AddCommGroup M)
      (_ : Algebra R A) (_ : Module A M) (_ : Module R M) (_ : IsScalarTower R A M)
      (_ : Algebra A (etaleLocalRing B S hS X.1 xbar))
      (_ : Algebra R (etaleLocalRing B S hS Y.1 ybar))
      (_ : IsNoetherianRing A) (_ : IsNoetherianRing (etaleLocalRing B S hS X.1 xbar))
      (_ : Module.Flat A (etaleLocalRing B S hS X.1 xbar))
      (_ : Module.Flat R (etaleLocalRing B S hS Y.1 ybar)),
      letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
        isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
      letI : IsLocalRing (etaleLocalRing B S hS Y.1 ybar) :=
        isLocalRing_etaleLocalRing B S hS Y.1 Y.2 ybar
      letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
        (geometricModuleStalk B S hS X xbar F).isModule
      letI : Module (etaleLocalRing B S hS Y.1 ybar) (geometricModuleStalk B S hS Y ybar G) :=
        (geometricModuleStalk B S hS Y ybar G).isModule
      (Ideal.comap (algebraMap R A)
            (Ideal.comap (algebraMap A (etaleLocalRing B S hS X.1 xbar))
              (maximalIdeal (etaleLocalRing B S hS X.1 xbar)))).map
          (algebraMap R (etaleLocalRing B S hS Y.1 ybar)) =
        maximalIdeal (etaleLocalRing B S hS Y.1 ybar) ∧
      Nonempty (etaleLocalRing B S hS X.1 xbar ⊗[A] M ≃ₗ[etaleLocalRing B S hS X.1 xbar]
        geometricModuleStalk B S hS X xbar F) ∧
      Nonempty (etaleLocalRing B S hS Y.1 ybar ⊗[R] M ≃ₗ[etaleLocalRing B S hS Y.1 ybar]
        geometricModuleStalk B S hS Y ybar G)

/-- An affine chart presentation of the stalks carries weak association at `x̄` to weak
association at the image of `x̄`. -/
theorem isWeaklyAssociatedPoint_of_hasAffineStalkSquare {F : Modules.{u, u} B S hS X.1 X.2}
    {G : Modules.{u, u} B S hS Y.1 Y.2} {xbar : GeometricPoint B S hS X.1}
    (hsq : HasAffineStalkSquare B S hS f F G xbar)
    (hx : letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
        isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
      letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
        (geometricModuleStalk B S hS X xbar F).isModule
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
        (geometricModuleStalk B S hS X xbar F)
        (maximalIdeal (etaleLocalRing B S hS X.1 xbar))) :
    IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X.1 f.hom xbar.image) := by
  obtain ⟨ybar, hybar, R, A, M, hR, hA, hM, hRA, hAM, hRM, htower, hAA', hRR', hnA, hnA',
    hflatA, hflatR, hmap, ⟨eX⟩, ⟨eY⟩⟩ := hsq
  refine ⟨ybar, hybar, ?_⟩
  let _ : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  let _ : IsLocalRing (etaleLocalRing B S hS Y.1 ybar) :=
    isLocalRing_etaleLocalRing B S hS Y.1 Y.2 ybar
  let _ : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
    (geometricModuleStalk B S hS X xbar F).isModule
  let _ : Module (etaleLocalRing B S hS Y.1 ybar) (geometricModuleStalk B S hS Y ybar G) :=
    (geometricModuleStalk B S hS Y ybar G).isModule
  exact (IsWeaklyAssociatedPrime.of_linearEquiv eX.symm hx).tensorProduct_of_flat_square
    (maximalIdeal.isMaximal _).isPrime hmap |>.of_linearEquiv eY

/-- Let `f : X → Y` be an affine morphism of algebraic spaces with `X` locally Noetherian and
let `F` be a quasi-coherent `𝒪_X`-module. Given the inclusion `h0CU2` of the weakly associated
points of `f_*F` in the image of those of `F`, and the affine chart presentations `h05VP` of the
geometric stalks of `F` and `f_*F` at every geometric point of `X`, the two sets of points are
equal. Stacks 0CU8 itself, with neither input assumed, is
`weaklyAssociatedPoints_modulePushforward_eq_image_of_isAffineHom_locallyNoetherian`. -/
theorem weaklyAssociatedPoints_modulePushforward_eq_image_of_isAffineHom
    (hf : IsAffineHom B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (h0CU2 : IsAffineHom B S hS f.hom →
      HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T) →
      F.IsQuasicoherentOnSite →
      weaklyAssociatedPoints B S hS Y ((modulePushforward B S hS f).obj F) ⊆
        pointsMap B S hS X.1 f.hom '' weaklyAssociatedPoints B S hS X F)
    (h05VP : IsAffineHom B S hS f.hom →
      HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T) →
      F.IsQuasicoherentOnSite →
      ∀ xbar : GeometricPoint B S hS X.1,
        HasAffineStalkSquare B S hS f F ((modulePushforward B S hS f).obj F) xbar) :
    weaklyAssociatedPoints B S hS Y ((modulePushforward B S hS f).obj F) =
      pointsMap B S hS X.1 f.hom '' weaklyAssociatedPoints B S hS X F := by
  refine Set.Subset.antisymm (h0CU2 hf hX hF) ?_
  rintro y ⟨x, ⟨xbar, hxbar, hx⟩, rfl⟩
  rw [← hxbar]
  exact isWeaklyAssociatedPoint_of_hasAffineStalkSquare B S hS f (h05VP hf hX hF xbar) hx

end AlgebraicGeometry.Space

end
