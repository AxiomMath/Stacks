module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardTensor
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.CoherentQuotientOfTwists
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteTypeSubobjectColimit
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# The twists `𝒪(-m)` generate `D^+_QCoh` of projective space over an affine base

Let `S` be a scheme and `X = ℙⁿ_S`. The proof of [Stacks, Tag 0A9W] tests a morphism of
`D_QCoh(𝒪_X)` on the functors `Hom(𝒪(i), (-)[p])`, `-n ≤ i ≤ 0`, using that the twists
`𝒪, 𝒪(-1), …, 𝒪(-n)` generate ([Stacks, Tag 0A9V]). This file proves the part of that
generation the proof needs: an object of `D(𝒪_X)` which is bounded below, has quasi-coherent
cohomology and receives no nonzero morphism from a shift of `𝒪, 𝒪(-1), …, 𝒪(-n)` is zero, for
`S` affine.

The argument is in two steps.

* *The Koszul step*, for an arbitrary base: vanishing against `𝒪, …, 𝒪(-n)` propagates to every
  `𝒪(-m)`, `m ≥ 0`. The twists of `ℙⁿ_S` are pulled back from the integral model `ℙⁿ_ℤ`, so by the
  adjunction `L g^* ⊣ R g_*` along `g : ℙⁿ_S ⟶ ℙⁿ_ℤ` this is the statement for `R g_* K` on the
  integral model, which is the Koszul generation step
  `Stacks.AlgebraicGeometry.ExampleGenerator.twist_neg_mem_gen` together with
  [Stacks, Tag 09SK].
* *Detection*, over an affine base: if `K ≠ 0`, the lowest nonzero cohomology sheaf `H^q(K)` is a
  nonzero quasi-coherent module, it receives a nonzero morphism from some `𝒪(-m)` (a nonzero
  finite type quasi-coherent submodule, [Stacks, Tag 01PG], is a quotient of a sum of negative
  twists, [Stacks, Tag 01YS]), and since `K` lives in degrees `≥ q` that morphism is
  `H^q` of a nonzero morphism `𝒪(-m)[-q] ⟶ K`. This is the module form of [Stacks, Tag 0BQR]
  run at the bottom of a bounded-below complex.

## Main results

* `Stacks.Duality.ProjectiveSpace.exists_twistOver_hom_ne_zero` — a nonzero quasi-coherent module
  on `ℙⁿ_S`, `S` affine, receives a nonzero morphism from some `𝒪(-m)`, `m ≥ 0`.
* `Stacks.Duality.ProjectiveSpace.subsingleton_twistOver_shift_hom` — the Koszul step.
* `Stacks.Duality.ProjectiveSpace.isZero_of_subsingleton_twistOver_shift_hom` — the twists
  `𝒪(-m)` detect bounded-below objects with quasi-coherent cohomology, `S` affine.

## Implementation notes

The derived categories are the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which [Stacks, Tag 0A9E] is proved.
Only bounded-below objects are treated: the consumer applies the detection to the cone of a
morphism between bounded-below objects ([Stacks, Tag 0A9I]), and this avoids the unbounded form
of [Stacks, Tag 0BQR].

## References

* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace Stacks.Duality.ProjectiveSpace

variable (n : ℕ) (S : Scheme.{u})

/-- Projective space over a quasi-compact scheme is quasi-compact: its structure morphism is
proper. -/
instance compactSpace_projectiveSpaceOver [CompactSpace S] :
    CompactSpace (projectiveSpaceOver n S) :=
  QuasiCompact.compactSpace_of_compactSpace (projectiveSpaceOver n S ↘ S)

/-- Projective space over a quasi-separated scheme is quasi-separated: its structure morphism is
proper. -/
instance quasiSeparatedSpace_projectiveSpaceOver [QuasiSeparatedSpace S] :
    QuasiSeparatedSpace (projectiveSpaceOver n S) :=
  quasiSeparatedSpace_of_quasiSeparated (projectiveSpaceOver n S ↘ S)

/-- A nonzero quasi-coherent module on a quasi-compact quasi-separated scheme has a nonzero
quasi-coherent submodule of finite type. -/
theorem exists_finiteType_subobject_arrow_ne_zero {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (F : X.Modules) [F.IsQuasicoherent] (hF : ¬ IsZero F) :
    ∃ G : FiniteTypeQuasicoherentSubobject F, G.obj.arrow ≠ 0 := by
  by_contra h
  push Not at h
  refine hF ((IsZero.iff_id_eq_zero F).2 ?_)
  exact (isColimit_finiteTypeQuasicoherentSubobjectCocone F).hom_ext fun G => by
    show G.obj.arrow ≫ 𝟙 F = G.obj.arrow ≫ 0
    rw [h G, zero_comp, zero_comp]

/-- **[Stacks, Tag 0BQR] at a module, on projective space over an affine base, in the twist
vocabulary.** A nonzero quasi-coherent module `F` on `ℙⁿ_S`, `S` affine, receives a nonzero
morphism from some twist `𝒪(-m)`, `m ≥ 0`. -/
theorem exists_twistOver_hom_ne_zero [IsAffine S] (F : (projectiveSpaceOver n S).Modules)
    [F.IsQuasicoherent] (hF : ¬ IsZero F) :
    ∃ (m : ℕ) (φ : twistOver n S (-(m : ℤ)) ⟶ F), φ ≠ 0 := by
  obtain ⟨G, hG⟩ := exists_finiteType_subobject_arrow_ne_zero F hF
  let : (G.obj : (projectiveSpaceOver n S).Modules).IsQuasicoherent := G.property.1
  obtain ⟨r, d, b, hb, p, hp, hd⟩ :=
    Stacks.ProjectiveSpace.exists_epi_biproduct_tensorPowModule n S 0 G.obj
      G.property.1 G.property.2
  have hpG : p ≫ G.obj.arrow ≠ 0 := fun h => hG ((cancel_epi p).1 (h.trans (comp_zero).symm))
  obtain ⟨j, hj⟩ : ∃ j, b.ι j ≫ p ≫ G.obj.arrow ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hpG (hb.isColimit.hom_ext fun ⟨j⟩ => by simpa using hall j)
  obtain ⟨m, hm⟩ : ∃ m : ℕ, d j = -(m : ℤ) := ⟨(-d j).toNat, by have := hd j; omega⟩
  let e := Stacks.AlgebraicGeometry.ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso n S (d j)
  refine ⟨m, eqToHom (congrArg (twistOver n S) hm.symm) ≫ e.inv ≫ b.ι j ≫ p ≫ G.obj.arrow,
    fun h => hj ?_⟩
  simpa using congrArg (fun φ => e.hom ≫ eqToHom (congrArg (twistOver n S) hm) ≫ φ) h

/-! ### Vanishing of morphisms, read through equivalences of morphism types -/

section Vanishing

variable {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]

/-- The vanishing of every morphism `E⟦q⟧ ⟶ K`, for all `q`, is the vanishing of every morphism
`E ⟶ K⟦q⟧`, for all `q`: the shift by `q` is an equivalence with inverse the shift by `-q`. -/
theorem forall_subsingleton_shift_hom_iff (E K : C) :
    (∀ q : ℤ, Subsingleton ((shiftFunctor C q).obj E ⟶ K)) ↔
      ∀ q : ℤ, Subsingleton (E ⟶ (shiftFunctor C q).obj K) := by
  refine ⟨fun h q => ?_, fun h q =>
    ((shiftEquiv C q).toAdjunction.homEquiv E K).subsingleton_congr.2 (h (-q))⟩
  have h' := ((shiftEquiv C (-q)).toAdjunction.homEquiv E K).subsingleton_congr.1 (h (-q))
  change Subsingleton (E ⟶ (shiftFunctor C (-(-q))).obj K) at h'
  rwa [neg_neg] at h'

end Vanishing

/-! ### The Koszul step, pulled back from the integral model -/

section Koszul

open Stacks.AlgebraicGeometry.ExampleGenerator Stacks.TriangulatedGenerators

/-- The projection of `ℙⁿ_S` to the integral model `ℙⁿ_ℤ`. -/
abbrev toIntegral : projectiveSpaceOver n S ⟶ projectiveSpaceAtUniverse.{u} n :=
  projectiveSpaceOver.toIntegralAtUniverse n S

/-- `L g^*` of the twist `𝒪(d)` of the integral model, placed in degree zero, is the twist
`𝒪(d)` of `ℙⁿ_S` placed in degree zero: the twists of the integral model are invertible, hence
flat, and a flat module in a single degree is K-flat. -/
def derivedPullbackTwistIso (d : ℤ) :
    (Stacks.Duality.derivedPullback (toIntegral n S)).obj (twist (ULift.{u} ℤ) n d) ≅
      (DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (twistOver n S d) :=
  Stacks.AlgebraicGeometry.DerivedAffinePushforward.derivedPullbackSingleIsoOfFlat _ _
    (Stacks.Chow.isFlat_of_isInvertible (h :=
      Stacks.AlgebraicGeometry.ProjTwistTensorPow.isInvertibleModule_twistingSheaf_integralModel
        n d) _)

/-- Morphisms from the twist `𝒪(d)` of `ℙⁿ_S` into a shift of `K` are morphisms from the twist
`𝒪(d)` of the integral model into the same shift of `R g_* K`, by the adjunction `L g^* ⊣ R g_*`
and the compatibility of `R g_*` with the shift. -/
def twistHomEquiv (K : DerivedCategory (projectiveSpaceOver n S).Modules) (d q : ℤ) :
    ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj (twistOver n S d) ⟶
        (shiftFunctor _ q).obj K) ≃
      (twist (ULift.{u} ℤ) n d ⟶ (shiftFunctor _ q).obj
        ((Stacks.Duality.derivedPushforward (toIntegral n S)).obj K)) :=
  ((derivedPullbackTwistIso n S d).homFromEquiv).symm.trans
    (((Stacks.Duality.derivedAdjunction (toIntegral n S)).homEquiv _ _).trans
      (((Stacks.Duality.derivedPushforward (toIntegral n S)).commShiftIso q).app K).homToEquiv)

/-- **The Koszul step of [Stacks, Tag 0A9V] on `ℙⁿ_S`, for an arbitrary base.** If an object
`K` of `D(𝒪_{ℙⁿ_S})` receives only zero morphisms from the shifts of `𝒪, 𝒪(-1), …, 𝒪(-n)`, then
it receives only zero morphisms from the shifts of every twist `𝒪(-m)`, `m ≥ 0`.

The twists of `ℙⁿ_S` are pulled back from the integral model, so by the adjunction
`L g^* ⊣ R g_*` along `g : ℙⁿ_S ⟶ ℙⁿ_ℤ` the statement is the one for `R g_* K` on the integral
model, which is the generation step `Stacks.AlgebraicGeometry.ExampleGenerator.twist_neg_mem_gen`
together with [Stacks, Tag 09SK]. -/
theorem subsingleton_twistOver_shift_hom (K : DerivedCategory (projectiveSpaceOver n S).Modules)
    (h : ∀ i : ℕ, i ≤ n → ∀ q : ℤ, Subsingleton ((shiftFunctor _ q).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (twistOver n S (-(i : ℤ)))) ⟶ K)) (m : ℕ) (q : ℤ) :
    Subsingleton ((shiftFunctor _ q).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (twistOver n S (-(m : ℤ)))) ⟶ K) := by
  let RK : DerivedCategory (Mods (ULift.{u} ℤ) n) :=
    (Stacks.Duality.derivedPushforward (toIntegral n S)).obj K
  have h₁ : ∀ (i : Fin (n + 1)) (p : ℤ), Subsingleton (twist (ULift.{u} ℤ) n (-(i : ℤ)) ⟶
      (shiftFunctor (DerivedCategory (Mods (ULift.{u} ℤ) n)) p).obj RK) := fun i p =>
    (twistHomEquiv n S K _ p).subsingleton_congr.1
      ((forall_subsingleton_shift_hom_iff _ K).1 (h i (Nat.lt_succ_iff.1 i.2)) p)
  have h₂ : ∀ (p : ℤ) (f : twistSum (ULift.{u} ℤ) n ⟶
      (shiftFunctor (DerivedCategory (Mods (ULift.{u} ℤ) n)) p).obj RK), f = 0 :=
    fun p f => biproduct.hom_ext' _ _ fun i => (h₁ i p).elim _ _
  have h₃ := (hom_vanishing_iff_gen (twistSum (ULift.{u} ℤ) n) RK).1 h₂
  have h₄ : ∀ p : ℤ, Subsingleton ((shiftFunctor (DerivedCategory (Mods (ULift.{u} ℤ) n)) p).obj
      (twist (ULift.{u} ℤ) n (-(m : ℤ))) ⟶ RK) := fun p =>
    subsingleton_of_forall_eq 0
      (h₃ _ (shift_mem_gen_of_mem p (twist_neg_mem_gen (ULift.{u} ℤ) n m)))
  exact (forall_subsingleton_shift_hom_iff _ K).2 (fun p =>
    (twistHomEquiv n S K _ p).subsingleton_congr.2
      ((forall_subsingleton_shift_hom_iff _ RK).1 h₄ p)) q

end Koszul

/-! ### Detection by the twists, over an affine base -/

section Detection

variable [IsAffine S]

/-- **The twists `𝒪(-m)` detect bounded-below complexes with quasi-coherent cohomology on
`ℙⁿ_S`, `S` affine.** Let `K` be an object of `D(𝒪_{ℙⁿ_S})` which is bounded below and has
quasi-coherent cohomology sheaves. If every morphism from a shift of a twist `𝒪(-m)`, `m ≥ 0`, to
`K` vanishes, then `K = 0`.

If `K ≠ 0`, let `q` be the least degree with `H^q(K) ≠ 0`. Then `K` lives in degrees `≥ q`, so the
morphisms `𝒪(-m)[-q] ⟶ K` are the morphisms `𝒪(-m) ⟶ H^q(K)`, and
`exists_twistOver_hom_ne_zero` produces a nonzero one. -/
theorem isZero_of_subsingleton_twistOver_shift_hom
    (K : DerivedCategory (projectiveSpaceOver n S).Modules) (q₀ : ℤ) (hK : K.IsGE q₀)
    (hqc : ∀ j : ℤ, ((DerivedCategory.homologyFunctor _ j).obj K).IsQuasicoherent)
    (h : ∀ (m : ℕ) (q : ℤ), Subsingleton ((shiftFunctor _ q).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (twistOver n S (-(m : ℤ)))) ⟶ K)) :
    IsZero K := by
  by_contra hK0
  have hex : ∃ j : ℤ, ¬ IsZero ((DerivedCategory.homologyFunctor _ j).obj K) := by
    by_contra hall
    push Not at hall
    exact hK0 (Stacks.Cohomology.PushforwardRestriction.isZero_derived_of_homology_isZero K hall)
  obtain ⟨j, hj, hjmin⟩ := Int.exists_least_of_bdd ⟨q₀, fun z hz => by
    by_contra hlt
    exact hz (DerivedCategory.isZero_of_isGE K q₀ z (by omega))⟩ hex
  have hKj : K.IsGE j := (DerivedCategory.isGE_iff K j).2 fun i hi => by
    by_contra hi'
    exact absurd (hjmin i hi') (by omega)
  let := hqc j
  obtain ⟨m, φ, hφ⟩ := exists_twistOver_hom_ne_zero n S _ hj
  obtain ⟨u, hu⟩ := (DerivedCategory.bijective_homologyFromSingle_of_isGE _ K j).2 φ
  let e := ((DerivedCategory.singleFunctors (projectiveSpaceOver n S).Modules).shiftIso
    (-j) j 0 (by omega)).app (twistOver n S (-(m : ℤ)))
  have hu0 : u = 0 := by
    simpa using congrArg (e.inv ≫ ·) ((h m (-j)).elim (e.hom ≫ u) 0)
  exact hφ (by rw [← hu, hu0, map_zero])

end Detection

end Stacks.Duality.ProjectiveSpace
