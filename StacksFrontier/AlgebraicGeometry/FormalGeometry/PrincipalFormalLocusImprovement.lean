module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleCokernelStalk
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.CompactFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Mono
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SupportClosure
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Vanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.TorsionFreeRealization
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalComplement
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.ExceptionalAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusDimensionCriterion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusSurjectivity
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Filtration
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.CodimensionOneObstruction.AssociatedPointTransfer
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.UniversallyCatenaryDimension
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.ExistenceDepthOutside
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterionGlobal
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.AlgebraicGeometry.ReflexiveExtend.Basic
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.RestrictStalk
public import StacksFrontier.RingTheory.Catenary.Localization
public import StacksFrontier.RingTheory.Depth.AssociatedPrime
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.Topology.Dimension.CatenaryAdditive

/-!
# Improving a module with one associated point along a principal formal locus

Let `A` be a Noetherian ring, let `f ∈ A`, let `𝔞 ⊆ A` be an ideal, let `U = Spec(A) ∖ V(𝔞)` and
let `F` be a coherent `𝒪_U`-module with a single associated point `x₀ ∉ V(f)`. Assume `A` is
universally catenary with `(S₁)` formal fibres, and that condition (2) of Stacks 0H49 holds at
`x₀`. This file constructs the improvement of `F` used in the proof of Stacks 0H49 in
`StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalLocusAlgebraization`: a short
exact sequence `0 → F → G → Q → 0` of coherent modules in which `f` is a nonzerodivisor on `G`,
`Q` is supported on `V(f)`, and `j_*(G / f G)` is coherent on `Spec(A)` for `j : U ⟶ Spec(A)`,
i.e. `H⁰(U, G / f G)` is a finite `A`-module.

## The construction

Let `D` be the (finite) set of associated points of `F / f F`; they lie in `V(f)` and specialize
`x₀`. Let `Z'` be the union of the closures of the points of `D` which are *not* immediate
specializations of `x₀`, and `V = U ∖ Z'`. Then `G = j_{V,*}(F|_V)` and `F ⟶ G` is the unit.

* `G` is coherent by Stacks 0AWB: a point of `Z'` lies below a point of `D` strictly between
  `x₀` and it, or is itself such a point, and in either case is not an immediate
  specialization of `x₀`; a point of `V(𝔞)` on the closure of `x₀` has codimension greater than
  two by condition (2), which applies because the closure of `x₀` meets `V(f)` off `V(𝔞)`.
* `G` has depth at least two along `Z'` (Stacks 0EY0), agrees with `F` on `V`, and so has `x₀` as
  its only associated point; `F ⟶ G` is injective and its cokernel is supported on `Z' ⊆ V(f)`.
* An associated point `y` of `G / f G` has depth one in `G`, hence lies off `Z'`, hence is a
  point of `D` not in `Z'`, hence an immediate specialization of `x₀`. For `z ∈ V(𝔞)` on the
  closure of `y`, condition (2) and the catenarity of `A` give
  `dim(𝒪_{closure{y}, z}) = dim(𝒪_{closure{x₀}, z}) − 1 ≥ 2`, which is the hypothesis of
  Stacks 0AWB for `j_*(G / f G)`.

If the closure of `x₀` does not meet `V(f)` inside `U`, then `F / f F` has no associated point and
`G = F` already works.

This is where the first proof of Stacks 0H49 needs repair: its observation (3) is asserted for an
`F` with several associated points, through Stacks 0DX5, and fails there; with one associated
point the closures above cannot reach an immediate specialization of `x₀`.

## Main results

* `Stacks.Algebraization.isCoherent_pushforward_spec_of_two_le_topCodim` — Stacks 0AWB over
  `Spec(A)`, with its dimension condition read as codimensions of closures of primes.
* `Stacks.Algebraization.isIso_stalkFunctor_map_of_isIso_restrictFunctor_map`,
  `Stacks.Algebraization.isIso_restrictFunctor_map_unit`,
  `Stacks.Algebraization.isIso_unit_app_pushforward` — the unit of an open immersion.
* `Stacks.Algebraization.exists_shortExact_isCoherent_pushforward_of_associatedPoints_eq_singleton`
  — the improvement.

## References

* [Stacks Project, Tag 0H49](https://stacks.math.columbia.edu/tag/0H49)
* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Codimensions of closures of points of `Spec A` -/

section Codimension

open TopologicalSpace IrreducibleClosedsCodim

variable {A : Type u} [CommRing A]

/-- Along a strict inclusion of primes `𝔭 ⊊ 𝔮` the closure of `𝔮` is strictly contained in the
closure of `𝔭`. -/
public theorem primeSpectrum_closureSingleton_lt_of_lt {p q : PrimeSpectrum A} (h : p < q) :
    IrreducibleCloseds.closureSingleton q < IrreducibleCloseds.closureSingleton p :=
  (PrimeSpectrum.pointsEquivIrreducibleCloseds A).strictMono h

/-- A prime strictly between `𝔭` and `𝔮` makes the codimension of `V(𝔮)` in `V(𝔭)` at least
two. -/
public theorem two_le_topCodim_of_lt_of_lt {p r q : PrimeSpectrum A} (h₁ : p < r) (h₂ : r < q) :
    2 ≤ topCodim (IrreducibleCloseds.closureSingleton q)
      (IrreducibleCloseds.closureSingleton p) := by
  let s : LTSeries (IrreducibleCloseds (PrimeSpectrum A)) :=
    ⟨2, ![IrreducibleCloseds.closureSingleton q, IrreducibleCloseds.closureSingleton r,
      IrreducibleCloseds.closureSingleton p], fun i => by
        fin_cases i
        · exact primeSpectrum_closureSingleton_lt_of_lt h₂
        · exact primeSpectrum_closureSingleton_lt_of_lt h₁⟩
  exact_mod_cast length_le_topCodim _ _ s rfl rfl

/-- A chain of length three of primes between `𝔭` and `𝔮` makes the codimension of `V(𝔮)` in
`V(𝔭)` at least three. -/
public theorem three_le_topCodim_of_lt_of_lt_of_lt {p r r' q : PrimeSpectrum A} (h₁ : p < r)
    (h₂ : r < r') (h₃ : r' < q) :
    3 ≤ topCodim (IrreducibleCloseds.closureSingleton q)
      (IrreducibleCloseds.closureSingleton p) := by
  let s : LTSeries (IrreducibleCloseds (PrimeSpectrum A)) :=
    ⟨3, ![IrreducibleCloseds.closureSingleton q, IrreducibleCloseds.closureSingleton r',
      IrreducibleCloseds.closureSingleton r, IrreducibleCloseds.closureSingleton p], fun i => by
        fin_cases i
        · exact primeSpectrum_closureSingleton_lt_of_lt h₃
        · exact primeSpectrum_closureSingleton_lt_of_lt h₂
        · exact primeSpectrum_closureSingleton_lt_of_lt h₁⟩
  exact_mod_cast length_le_topCodim _ _ s rfl rfl

/-- If the local ring of the closure of `𝔭` at `𝔮` has dimension greater than two, then the
codimension of `V(𝔮)` in `V(𝔭)` is at least three. -/
public theorem three_le_topCodim_of_two_lt_closureLocalDimension {p q : PrimeSpectrum A}
    (h : (2 : WithBot ℕ∞) < closureLocalDimension A p q) :
    3 ≤ topCodim (IrreducibleCloseds.closureSingleton q)
      (IrreducibleCloseds.closureSingleton p) := by
  have hnot : ¬ closureLocalDimension A p q < ((3 : ℕ) : WithBot ℕ∞) := by
    intro hlt
    have hlt' : closureLocalDimension A p q < ((2 : ℕ) : WithBot ℕ∞) + 1 := by
      exact_mod_cast hlt
    have hle : closureLocalDimension A p q ≤ ((2 : ℕ) : WithBot ℕ∞) :=
      ENat.WithBot.lt_add_one_iff.mp hlt'
    exact absurd (h.trans_le hle) (by exact_mod_cast lt_irrefl (2 : WithBot ℕ∞))
  have hex : ∃ l : LTSeries {r : PrimeSpectrum A // p.asIdeal ≤ r.asIdeal ∧
      r.asIdeal ≤ q.asIdeal}, ¬ l.length < 3 := by
    by_contra hcon
    push Not at hcon
    exact hnot (Order.krullDim_lt_coe_iff.mpr hcon)
  obtain ⟨l, hl⟩ := hex
  have hmono := l.strictMono
  have hl3 : 3 ≤ l.length := by omega
  let i : ℕ → Fin (l.length + 1) := fun k => ⟨min k 3, by omega⟩
  have h01 : l (i 0) < l (i 1) := hmono (by simp [i, Fin.lt_def])
  have h12 : l (i 1) < l (i 2) := hmono (by simp [i, Fin.lt_def])
  have h23 : l (i 2) < l (i 3) := hmono (by simp [i, Fin.lt_def])
  exact three_le_topCodim_of_lt_of_lt_of_lt
    (lt_of_le_of_lt (l (i 0)).2.1 h01) h12 (lt_of_lt_of_le h23 (l (i 3)).2.2)

/-- If no prime lies strictly between `𝔭 ⊊ 𝔮`, the codimension of `V(𝔮)` in `V(𝔭)` is at most
one. -/
public theorem topCodim_le_one_of_forall_not_lt {p q : PrimeSpectrum A}
    (himm : ∀ r : PrimeSpectrum A, p < r → ¬ r < q) :
    topCodim (IrreducibleCloseds.closureSingleton q)
      (IrreducibleCloseds.closureSingleton p) ≤ 1 := by
  refine topCodim_le_iff.mpr fun s hh hl => ?_
  by_contra hlen
  have h2 : 2 ≤ s.length := by
    by_contra h'
    exact hlen (by exact_mod_cast (show s.length ≤ 1 by omega))
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  let Y := s ⟨1, by omega⟩
  let r : PrimeSpectrum A := e.symm (OrderDual.toDual Y)
  have hr : IrreducibleCloseds.closureSingleton r = Y := by
    show OrderDual.ofDual (e (e.symm (OrderDual.toDual Y))) = Y
    rw [e.apply_symm_apply]
    rfl
  have hqY : IrreducibleCloseds.closureSingleton q < Y := by
    rw [← hh]
    exact s.strictMono (show (0 : Fin (s.length + 1)) < ⟨1, by omega⟩ by
      simp [Fin.lt_def])
  have hYp : Y < IrreducibleCloseds.closureSingleton p := by
    rw [← hl]
    exact s.strictMono (show (⟨1, by omega⟩ : Fin (s.length + 1)) < Fin.last _ by
      simp [Fin.lt_def]
      omega)
  rw [← hr] at hqY hYp
  exact himm r ((e.lt_iff_lt).mp hYp) ((e.lt_iff_lt).mp hqY)

/-- **The catenary step.** In a ring with catenary spectrum, if `𝔭 ⊊ 𝔶` has no prime strictly
between, `𝔶 ⊆ 𝔷`, and the codimension of `V(𝔷)` in `V(𝔭)` is at least three, then the
codimension of `V(𝔷)` in `V(𝔶)` is at least two. -/
public theorem two_le_topCodim_of_catenary {p y z : PrimeSpectrum A}
    (hX : IsCatenarySpace (PrimeSpectrum A)) (hpy : p ≤ y)
    (himm : ∀ r : PrimeSpectrum A, p < r → ¬ r < y) (hyz : y ≤ z)
    (h3 : 3 ≤ topCodim (IrreducibleCloseds.closureSingleton z)
      (IrreducibleCloseds.closureSingleton p)) :
    2 ≤ topCodim (IrreducibleCloseds.closureSingleton z)
      (IrreducibleCloseds.closureSingleton y) := by
  let e := PrimeSpectrum.pointsEquivIrreducibleCloseds A
  have hadd := topCodim_additive_of_catenary hX (IrreducibleCloseds.closureSingleton z)
    (IrreducibleCloseds.closureSingleton y) (IrreducibleCloseds.closureSingleton p)
    (e.monotone hyz) (e.monotone hpy)
  rw [hadd] at h3
  by_contra hlt
  have hle : topCodim (IrreducibleCloseds.closureSingleton z)
      (IrreducibleCloseds.closureSingleton y) ≤ 1 :=
    Order.le_of_lt_add_one (by simpa [one_add_one_eq_two] using not_le.mp hlt)
  exact absurd (h3.trans (add_le_add hle (topCodim_le_one_of_forall_not_lt himm)))
    (not_le.mpr (by norm_num))

end Codimension

/-! ### Multiplication by a global function, at a stalk -/

section Scalar

open Stacks.AlgebraicGeometry.PrincipalIdealExtension (smulPowHom)

variable {X : Scheme.{u}}

/-- If the stalk `M_x / a M_x` vanishes, `x` is not associated to `M / a M`; this holds in
particular when `M_x = 0`, or when the germ of `a` at `x` is a unit. -/
public theorem notMem_associatedPoints_cokernel_smulPowHom_of_forall (M : X.Modules)
    (a : Γ(X, ⊤)) (x : X)
    (h : ∀ n : M.presheaf.stalk x, n ∈ Ideal.span {(X.presheaf.Γgerm x).hom a} •
      (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x))) :
    x ∉ Stacks.Divisors.associatedPoints (cokernel (smulPowHom M a 1)) := by
  intro hx
  rw [Stacks.Divisors.mem_associatedPoints_iff,
    isAssociatedPoint_cokernel_smulPowHom_one_iff] at hx
  obtain ⟨hp, m, hm⟩ := hx
  refine hp.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hm]
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  refine Submodule.mem_colon_span_singleton.2 ?_
  rw [one_smul, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  exact h n

/-- At a point where the germ of `a` is a unit, `M / a M` has no associated point. -/
public theorem notMem_associatedPoints_cokernel_smulPowHom_of_isUnit (M : X.Modules)
    (a : Γ(X, ⊤)) (x : X) (hu : IsUnit ((X.presheaf.Γgerm x).hom a)) :
    x ∉ Stacks.Divisors.associatedPoints (cokernel (smulPowHom M a 1)) := by
  refine notMem_associatedPoints_cokernel_smulPowHom_of_forall M a x fun n => ?_
  rw [Ideal.span_singleton_eq_top.mpr hu, Submodule.top_smul]
  trivial

/-- An associated point of `M / a M` lies in the support of `M`. -/
public theorem nontrivial_stalk_of_mem_associatedPoints_cokernel_smulPowHom (M : X.Modules)
    (a : Γ(X, ⊤)) (x : X)
    (hx : x ∈ Stacks.Divisors.associatedPoints (cokernel (smulPowHom M a 1))) :
    Nontrivial (M.presheaf.stalk x) := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  exact notMem_associatedPoints_cokernel_smulPowHom_of_forall M a x
    (fun n => (Subsingleton.elim n 0).symm ▸ Submodule.zero_mem _) hx

/-- Multiplication by `a` is injective on every stalk at which the germ of `a` is a unit. -/
public theorem injective_stalk_smulPowHom_of_isUnit (M : X.Modules) (a : Γ(X, ⊤)) (x : X)
    (hu : IsUnit ((X.presheaf.Γgerm x).hom a)) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (smulPowHom M a 1).val)).hom := by
  intro m n hmn
  have hm := stalkLinearMap_smulPowHom_one M a x m
  have hn := stalkLinearMap_smulPowHom_one M a x n
  have hreg : IsSMulRegular (M.presheaf.stalk x) ((X.presheaf.Γgerm x).hom a) :=
    IsUnit.isSMulRegular _ hu
  exact hreg (hm.symm.trans (hmn.trans hn))

/-- **Multiplication by `a` is a monomorphism as soon as `a` is invertible at every associated
point.** This is Stacks 0AVL for the endomorphism `a · −`. -/
public theorem mono_smulPowHom_of_isUnit_germ [IsLocallyNoetherian X] (M : X.Modules)
    [M.IsQuasicoherent] (a : Γ(X, ⊤))
    (h : ∀ x ∈ Stacks.Divisors.associatedPoints M, IsUnit ((X.presheaf.Γgerm x).hom a)) :
    Mono (smulPowHom M a 1) :=
  Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints _
    fun x => by
      by_cases hx : x ∈ Stacks.Divisors.associatedPoints M
      · exact Or.inl (injective_stalk_smulPowHom_of_isUnit M a x (h x hx))
      · exact Or.inr hx

/-- **A point where `M` has depth at least two is not associated to `M / a M`**, when
multiplication by `a` is injective on `M`. Where the germ of `a` is a unit the quotient vanishes;
otherwise the germ lies in the maximal ideal and is `M_x`-regular, so the depth of
`M_x / a M_x` is one less than that of `M_x` (Stacks 090R), hence positive. -/
public theorem notMem_associatedPoints_cokernel_smulPowHom_of_two_le_depth
    [IsLocallyNoetherian X] (M : X.Modules) [M.IsCoherent] (a : Γ(X, ⊤))
    [Mono (smulPowHom M a 1)] (x : X)
    (hdepth :
      letI : Module (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := X.presheaf) M.val x
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) M.val.presheaf x)) :
    x ∉ Stacks.Divisors.associatedPoints (cokernel (smulPowHom M a 1)) := by
  let := PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) M.val x
  set g := (X.presheaf.Γgerm x).hom a with hg
  by_cases hu : IsUnit g
  · exact notMem_associatedPoints_cokernel_smulPowHom_of_isUnit M a x hu
  have hgm : g ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := hu
  have : Module.Finite (X.presheaf.stalk x) (M.presheaf.stalk x) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent M x
  have hreg : IsSMulRegular (M.presheaf.stalk x) g := fun m n hmn =>
    AlgebraicGeometry.stalk_map_injective_of_mono (smulPowHom M a 1) x
      ((stalkLinearMap_smulPowHom_one M a x m).trans
        (hmn.trans (stalkLinearMap_smulPowHom_one M a x n).symm))
  have h090R := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (M.presheaf.stalk x)).1 g hgm hreg
  have hone : (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (QuotSMulTop g (M.presheaf.stalk x)) := by
    by_contra hlt
    have h0 := ENat.lt_one_iff_eq_zero.mp (not_le.mp hlt)
    rw [h0, zero_add] at h090R
    exact absurd (h090R ▸ hdepth) (by norm_num)
  have hnot := maximalIdeal_not_isAssociatedPrimeStacks_of_one_le_depth hone
  intro hx
  rw [Stacks.Divisors.mem_associatedPoints_iff,
    isAssociatedPoint_cokernel_smulPowHom_one_iff] at hx
  exact hnot (Stacks.Divisors.isAssociatedPrimeStacks_of_linearEquiv
    (Submodule.quotEquivOfEq _ _ (Submodule.ideal_span_singleton_smul g ⊤)) hx)

end Scalar

/-! ### Stacks 0AWB over `Spec A`, in terms of codimensions -/

section Pushforward

open TopologicalSpace.IrreducibleCloseds (closureSingleton)
open IrreducibleClosedsCodim (topCodim)

/-- **Stacks 0AWB over `Spec A`, read with codimensions of closures of primes.** Let `A` be a
Noetherian universally catenary ring whose local rings have `(S₁)` formal fibres, let
`j : V ⟶ Spec A` be an open immersion and let `M` be a coherent `𝒪_V`-module. If for every
associated point `x` of `M` and every prime `𝔷 ⊇ 𝔭_{j x}` outside the image of `j` the
codimension of `V(𝔷)` in `V(𝔭_{j x})` is at least two, then `j_* M` is coherent. -/
public theorem isCoherent_pushforward_spec_of_two_le_topCodim
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hcat : Ring.IsUniversallyCatenary A)
    (hfib : ∀ (z : Spec (CommRingCat.of A))
      (q : PrimeSpectrum ((Spec (CommRingCat.of A)).presheaf.stalk z)),
      HasSerreCondition ((Spec (CommRingCat.of A)).completedLocalRing z
        ⊗[(Spec (CommRingCat.of A)).presheaf.stalk z] q.asIdeal.ResidueField) 1)
    {V : Scheme.{u}} (j : V ⟶ Spec (CommRingCat.of A)) [IsOpenImmersion j]
    (M : V.Modules) [M.IsCoherent]
    (h : ∀ x ∈ Stacks.Divisors.associatedPoints M, ∀ z : PrimeSpectrum A,
      (j.base x).asIdeal ≤ z.asIdeal → z ∉ Set.range j.base →
        2 ≤ topCodim (closureSingleton z) (closureSingleton (j.base x : PrimeSpectrum A))) :
    ((Scheme.Modules.pushforward j).obj M).IsCoherent := by
  rw [isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure j
    (Scheme.isUniversallyCatenary_spec A hcat) (fun z _ q => hfib z q)]
  intro x hx y hy
  rw [ringKrullDim_stalk_vanishingIdeal_closure_eq_topCodim]
  have hz : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set (Spec (CommRingCat.of A))))).subschemeι.base y ∈
        closure ({j x} : Set (Spec (CommRingCat.of A))) := by
    rw [← range_subschemeι_vanishingIdeal_closure (j x)]
    exact ⟨y, rfl⟩
  have hle : (j.base x).asIdeal ≤ ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set (Spec (CommRingCat.of A))))).subschemeι.base y).asIdeal :=
    (PrimeSpectrum.le_iff_specializes (j.base x) _).2 (specializes_iff_mem_closure.2 hz)
  have hrange : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set (Spec (CommRingCat.of A))))).subschemeι.base y ∉
        Set.range j.base := fun hmem => hy (by simpa [Scheme.Hom.coe_opensRange] using hmem)
  exact WithBot.coe_le_coe.mpr (h x hx _ hle hrange)

end Pushforward

/-! ### Stalks of a morphism which is an isomorphism over an open -/

section OverOpen

open Stacks.AlgebraicGeometry.PrincipalIdealExtension (smulPowHom)

variable {X : Scheme.{u}}

/-- A morphism of sheaves of modules whose restriction to an open `V` is an isomorphism is an
isomorphism on the stalks at the points of `V`: the stalk of the restriction at a point of `V`
is the stalk of the sheaf there (`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`). -/
public theorem isIso_stalkFunctor_map_of_isIso_restrictFunctor_map (V : X.Opens)
    {M N : X.Modules} (φ : M ⟶ N) (hφ : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ))
    (x : X) (hx : x ∈ V) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf) := by
  let xV : V.toScheme := ⟨x, hx⟩
  let κ := Scheme.Modules.restrictStalkNatIso V.ι xV
  have h₁ : IsIso ((Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} xV).map φ) :=
    Functor.map_isIso (Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} xV)
      ((Scheme.Modules.restrictFunctor V.ι).map φ)
  have h₂ : IsIso (κ.hom.app M ≫ (Scheme.Modules.toPresheaf _ ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} (V.ι xV)).map φ) := by
    rw [← κ.hom.naturality φ]
    infer_instance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (κ.hom.app M) _ _ h₂

/-- Under an isomorphism of stalks at `x`, the point `x` is associated to `M / a M` exactly when
it is associated to `N / a N`. -/
public theorem isAssociatedPoint_cokernel_smulPowHom_iff_of_isIso_stalk {M N : X.Modules}
    (φ : M ⟶ N) (a : Γ(X, ⊤)) (x : X)
    (hφ : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf)) :
    Stacks.Divisors.IsAssociatedPoint (cokernel (smulPowHom M a 1)) x ↔
      Stacks.Divisors.IsAssociatedPoint (cokernel (smulPowHom N a 1)) x := by
  rw [isAssociatedPoint_cokernel_smulPowHom_one_iff, isAssociatedPoint_cokernel_smulPowHom_one_iff]
  let e : M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
    LinearEquiv.ofBijective (AlgebraicGeometry.stalkLinearMap M N φ x)
      (ConcreteCategory.bijective_of_isIso
        ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map φ.mapPresheaf))
  let J : Ideal (X.presheaf.stalk x) := Ideal.span {(X.presheaf.Γgerm x).hom a}
  have hmap : (J • (⊤ : Submodule (X.presheaf.stalk x) (M.presheaf.stalk x))).map
      (e : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N.presheaf.stalk x) =
        J • (⊤ : Submodule (X.presheaf.stalk x) (N.presheaf.stalk x)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  let E := Submodule.Quotient.equiv _ _ e hmap
  exact ⟨Stacks.Divisors.isAssociatedPrimeStacks_of_linearEquiv E,
    Stacks.Divisors.isAssociatedPrimeStacks_of_linearEquiv E.symm⟩

/-- The unit `M ⟶ j_* j^* M` of an open immersion `j : V ⟶ X` becomes an isomorphism after
restriction to `V`. -/
public theorem isIso_restrictFunctor_map_unit (V : X.Opens) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M)) := by
  let L := Scheme.Modules.restrictFunctor V.ι
  let R := Scheme.Modules.pushforward V.ι
  let adjL := Scheme.Modules.restrictAdjunction V.ι
  let adjP := Scheme.Modules.pullbackPushforwardAdjunction V.ι
  let α := Scheme.Modules.restrictFunctorIsoPullback V.ι
  have hunit : adjL.unit.app M ≫ R.map (α.hom.app M) = adjP.unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app adjL adjP M
  have hLunit : IsIso (L.map (adjL.unit.app M)) := by
    have htri : L.map (adjL.unit.app M) ≫ adjL.counit.app (L.obj M) = 𝟙 (L.obj M) := by
      simp [L, adjL, (Scheme.Modules.restrictAdjunction V.ι).left_triangle_components M]
    have : IsIso (L.map (adjL.unit.app M) ≫ adjL.counit.app (L.obj M)) := by
      rw [htri]
      infer_instance
    exact IsIso.of_isIso_comp_right (L.map (adjL.unit.app M)) (adjL.counit.app (L.obj M))
  have : IsIso (L.map (R.map (α.hom.app M))) := inferInstance
  have hfactor : L.map (adjL.unit.app M) ≫ L.map (R.map (α.hom.app M)) =
      L.map (adjP.unit.app M) := by
    rw [← Functor.map_comp, hunit]
  rw [← hfactor]
  infer_instance

/-- The unit of an open immersion `j : V ⟶ X` at a pushforward `j_* N` is an isomorphism: the
counit `j^* j_* N ⟶ N` is, and the triangle identity relates the two. -/
public theorem isIso_unit_app_pushforward (V : X.Opens) (N : V.toScheme.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
      ((Scheme.Modules.pushforward V.ι).obj N)) := by
  have := Stacks.AlgebraicGeometry.ReflexiveModules.isIso_pullbackPushforwardAdjunction_counit X V
  have : IsIso ((Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).counit.app N)) := inferInstance
  have h1 : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app
        ((Scheme.Modules.pushforward V.ι).obj N) ≫ (Scheme.Modules.pushforward V.ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).counit.app N)) := by
    rw [(Scheme.Modules.pullbackPushforwardAdjunction V.ι).right_triangle_components N]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).counit.app N))

end OverOpen

open Stacks.AlgebraicGeometry.PrincipalIdealExtension (smulPowHom) in
/-- **The improvement of a module with one associated point.** Let `A` be a Noetherian,
universally catenary ring whose local rings have `(S₁)` formal fibres, let `f ∈ A`, let
`U = Spec(A) ∖ V(𝔞)` and let `F` be a coherent `𝒪_U`-module whose associated points lie in
`{x₀}` with `f ∉ 𝔭_{x₀}`. Assume condition (2) of Stacks 0H49 at `x₀`. Then there is a short
exact sequence `0 → F → G → Q → 0` of coherent modules such that no associated point of `G` lies
in `V(f)`, every associated point of `Q` lies in `V(f)`, and the pushforward to `Spec(A)` of
`G / f G` is coherent. See the module documentation for the construction. -/
theorem exists_shortExact_isCoherent_pushforward_of_associatedPoints_eq_singleton
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Ideal A) (f : A)
    (hcat : Ring.IsUniversallyCatenary A)
    (hfib : ∀ (z : Spec (CommRingCat.of A))
      (q : PrimeSpectrum ((Spec (CommRingCat.of A)).presheaf.stalk z)),
      HasSerreCondition ((Spec (CommRingCat.of A)).completedLocalRing z
        ⊗[(Spec (CommRingCat.of A)).presheaf.stalk z] q.asIdeal.ResidueField) 1)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (x₀ : (complementZeroLocus A a : Scheme))
    (hAss : Stacks.Divisors.associatedPoints F ⊆ {x₀}) (hx₀ : f ∉ x₀.1.asIdeal)
    (hdim : (∃ y : PrimeSpectrum A,
        x₀.1.asIdeal ≤ y.asIdeal ∧ f ∈ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, x₀.1.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        (2 : WithBot ℕ∞) < closureLocalDimension A x₀.1 z) :
    ∃ (G Q : (complementZeroLocus A a : Scheme).Modules) (i : F ⟶ G) (p : G ⟶ Q)
      (w : i ≫ p = 0), (ShortComplex.mk i p w).ShortExact ∧ G.IsCoherent ∧ Q.IsCoherent ∧
      (∀ x ∈ Stacks.Divisors.associatedPoints G, f ∉ x.1.asIdeal) ∧
      (∀ x ∈ Stacks.Divisors.associatedPoints Q, f ∈ x.1.asIdeal) ∧
      ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj
        ((quotientSystemNearVanishing A (Ideal.span {f}) a G).obj (op 1))).IsCoherent := by
  classical
  -- notation
  let U := (complementZeroLocus A a : Scheme)
  let fU : Γ(U, ⊤) := complementTopScalars a f
  let Q₁ : U.Modules → U.Modules := fun M => cokernel (smulPowHom M fU 1)
  have hunit : ∀ x : U, IsUnit ((U.presheaf.Γgerm x).hom fU) ↔ f ∉ x.1.asIdeal := fun x =>
    (U.mem_basicOpen fU x trivial).symm.trans (mem_basicOpen_complementScalar_iff A a x f)
  have _ : (Q₁ F).IsCoherent := SheafOfModules.cokernel_isCoherent _
  have hle : ∀ {z w : U}, z ⤳ w → z.1.asIdeal ≤ w.1.asIdeal :=
    fun h => (PrimeSpectrum.le_iff_specializes _ _).2 ((subtype_specializes_iff _ _).1 h)
  have hF : F.IsQuasicoherent ∧ F.IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  have _ : F.IsQuasicoherent := hF.1
  have _ : F.IsFiniteType := hF.2
  -- every point of the support specializes from `x₀`
  have hsupp : ∀ x : U, Nontrivial (F.presheaf.stalk x) → x₀.1.asIdeal ≤ x.1.asIdeal := by
    intro x hx
    have hx' : x ∈ SheafOfModules.supp F := (SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).2 hx
    rw [supp_eq_closure_associatedPoints] at hx'
    exact hle (specializes_iff_mem_closure.2 (closure_mono hAss hx'))
  -- `f` is regular on `F`
  have hmonoF : Mono (smulPowHom F fU 1) :=
    mono_smulPowHom_of_isUnit_germ F fU fun x hx => (hunit x).2 (by
      rw [Set.mem_singleton_iff.1 (hAss hx)]; exact hx₀)
  -- the associated points of `F / f F`
  have hQF : ∀ y ∈ Stacks.Divisors.associatedPoints (Q₁ F),
      f ∈ y.1.asIdeal ∧ x₀.1.asIdeal ≤ y.1.asIdeal := fun y hy =>
    ⟨by_contra fun h => notMem_associatedPoints_cokernel_smulPowHom_of_isUnit F fU y
        ((hunit y).2 h) hy,
      hsupp y (nontrivial_stalk_of_mem_associatedPoints_cokernel_smulPowHom F fU y hy)⟩
  -- the comparison of `G / f G` with the quotient tower
  have htower : ∀ G : U.Modules, ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj
      (Q₁ G)).IsCoherent → ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj
        ((quotientSystemNearVanishing A (Ideal.span {f}) a G).obj (op 1))).IsCoherent := by
    intro G hG
    obtain ⟨e, -⟩ := principalPowerQuotientIso ((Stacks.SheafOfModules.terminalSectionToEnd
        (complementZeroLocus A a : Scheme).ringCatSheaf ⊤ isTerminalTop (complementTopScalars a
        f))) G 1
    have heq := idealSheafNearVanishing_span_singleton_eq_scalarIdealData A a f
    show ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj
      (cokernel (idealPowerMultiple (idealSheafNearVanishing A (Ideal.span {f}) a) 1
          G).ι)).IsCoherent
    rw [heq]
    exact Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso'
      ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).mapIso e) hG
  by_cases hmeet : ∃ y : PrimeSpectrum A,
      x₀.1.asIdeal ≤ y.asIdeal ∧ f ∈ y.asIdeal ∧ ¬ a ≤ y.asIdeal
  · have hcatX : IrreducibleClosedsCodim.IsCatenarySpace (PrimeSpectrum A) :=
      Ring.isUniversallyCatenary_iff_isUniversallyCatenary.1 hcat A inferInstance
    -- the points of `D` which are not immediate specializations of `x₀`, and their closures
    let Imm : U → Prop := fun y =>
      ∀ r : PrimeSpectrum A, x₀.1.asIdeal < r.asIdeal → ¬ r.asIdeal < y.1.asIdeal
    let D := Stacks.Divisors.associatedPoints (Q₁ F)
    let Z' : Set U := ⋃ y ∈ {y | y ∈ D ∧ ¬ Imm y}, closure {y}
    have hDfin : D.Finite := AlgebraicGeometry.associatedPoints_finite (Q₁ F)
    have hZ'closed : IsClosed Z' :=
      (hDfin.subset fun _ hy => hy.1).isClosed_biUnion fun _ _ => isClosed_closure
    let V : U.Opens := ⟨Z'ᶜ, hZ'closed.isOpen_compl⟩
    have hZ' : ∀ z ∈ Z', ∃ y ∈ D, ¬ Imm y ∧ y.1.asIdeal ≤ z.1.asIdeal := by
      intro z hz
      simp only [Z', Set.mem_iUnion] at hz
      obtain ⟨y, ⟨hyD, hy⟩, hzy⟩ := hz
      exact ⟨y, hyD, hy, hle (specializes_iff_mem_closure.2 hzy)⟩
    have hZ'f : ∀ z ∈ Z', f ∈ z.1.asIdeal := fun z hz => by
      obtain ⟨y, hyD, -, hyz⟩ := hZ' z hz
      exact hyz (hQF y hyD).1
    have hx₀V : x₀ ∈ V := fun h => hx₀ (hZ'f x₀ h)
    have hchain : ∀ z ∈ Z', ∃ r : PrimeSpectrum A,
        x₀.1.asIdeal < r.asIdeal ∧ r.asIdeal < z.1.asIdeal := by
      intro z hz
      obtain ⟨y, hyD, hy, hyz⟩ := hZ' z hz
      obtain ⟨hfy, hx₀y⟩ := hQF y hyD
      by_cases hyz' : y.1.asIdeal = z.1.asIdeal
      · simp only [Imm, not_forall, not_not, exists_prop] at hy
        obtain ⟨r, h₁, h₂⟩ := hy
        exact ⟨r, h₁, hyz' ▸ h₂⟩
      · exact ⟨y.1, lt_of_le_of_ne hx₀y fun h => hx₀ (h ▸ hfy), lt_of_le_of_ne hyz hyz'⟩
    -- the improvement `G = j_*(F|_V)` and the unit `F ⟶ G`
    let M := (Scheme.Modules.pullback V.ι).obj F
    let G := (Scheme.Modules.pushforward V.ι).obj M
    let i : F ⟶ G := (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app F
    have hM : M.IsCoherent := AlgebraicGeometry.isCoherent_pullback V.ι F
    have hAssM : ∀ x ∈ Stacks.Divisors.associatedPoints M, V.ι.base x = x₀ := by
      intro x hx
      have h1 : Stacks.Divisors.IsAssociatedPoint (Scheme.Modules.restrict F V.ι) x :=
        (Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_congr
          ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app F) x).2 hx
      exact Set.mem_singleton_iff.1 (hAss
        ((Stacks.AlgebraicGeometry.CodimensionOneObstruction.isAssociatedPoint_restrict_iff
          V.ι F x).1 h1))
    have hcohJ : ((Scheme.Modules.pushforward (V.ι ≫ (complementZeroLocus A a).ι)).obj
        M).IsCoherent := by
      refine isCoherent_pushforward_spec_of_two_le_topCodim A hcat hfib _ M fun x hx z hxz hz => ?_
      have hx' : (V.ι ≫ (complementZeroLocus A a).ι).base x = x₀.1 := by
        show (complementZeroLocus A a).ι.base (V.ι.base x) = x₀.1
        rw [hAssM x hx]
        rfl
      rw [hx'] at hxz ⊢
      by_cases ha : a ≤ z.asIdeal
      · exact le_trans (by norm_num)
          (three_le_topCodim_of_two_lt_closureLocalDimension (hdim hmeet z hxz ha))
      · let z' : U := ⟨z, ha⟩
        have hz' : z' ∈ Z' := by
          by_contra hzV
          refine hz ⟨(⟨z', hzV⟩ : V.toScheme), ?_⟩
          rfl
        obtain ⟨r, h₁, h₂⟩ := hchain z' hz'
        exact two_le_topCodim_of_lt_of_lt (p := (x₀.1 : PrimeSpectrum A)) h₁ h₂
    have hG : G.IsCoherent := by
      have h1 : ((Scheme.Modules.pushforward (complementZeroLocus A a).ι).obj G).IsCoherent :=
        Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso'
          ((Scheme.Modules.pushforwardComp V.ι (complementZeroLocus A a).ι).app M) hcohJ
      exact Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_of_iso'
        ((Scheme.Modules.restrictFunctorAdjCounitIso (complementZeroLocus A a).ι).app G).symm
        (Stacks.AlgebraicGeometry.ReflexiveModules.isCoherent_restrict_of_isOpenImmersion
          (complementZeroLocus A a).ι _ h1)
    have hGq : G.IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1
    have hiV : IsIso ((Scheme.Modules.restrictFunctor V.ι).map i) :=
      isIso_restrictFunctor_map_unit V F
    have hstalk : ∀ x ∈ V, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map i.mapPresheaf) :=
      isIso_stalkFunctor_map_of_isIso_restrictFunctor_map V i hiV
    -- `i` is a monomorphism: its kernel is supported off `V` while `x₀ ∈ V`
    have hmono : Mono i := by
      have _ : (kernel i).IsCoherent := SheafOfModules.kernel_isCoherent i
      have _ : (kernel i).IsQuasicoherent :=
        (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
      have hsuppK := Stacks.Coherent.supp_subset_compl_of_isZero_restrict V (kernel i)
        (Stacks.Coherent.isZero_restrict_kernel_of_isIso_restrict V i hiV)
      have hK : IsZero (kernel i) := by
        rw [isZero_iff_associatedPoints_eq_empty U]
        refine Set.eq_empty_of_forall_notMem fun x hx => ?_
        have hxF : x ∈ Stacks.Divisors.associatedPoints F :=
          AlgebraicGeometry.associatedPoints_subset_of_mono (kernel.ι i) hx
        rw [Set.mem_singleton_iff.1 (hAss hxF)] at hx
        exact hsuppK (AlgebraicGeometry.associatedPoints_subset_support _ hx) hx₀V
      exact (Preadditive.mono_iff_isZero_kernel i).2 hK
    -- depth at least two off `V`, and the associated points of `G`
    have hdepth := fun (z : U) (hz : z ∉ (V : Set U)) =>
      two_le_depth_stalk_of_isIso_unit_outside U V G hG (isIso_unit_app_pushforward V M) z hz
    have hAssG : ∀ x ∈ Stacks.Divisors.associatedPoints G, x = x₀ := by
      intro x hx
      by_cases hxV : x ∈ V
      · open Stacks.AlgebraicGeometry.CodimensionOneObstruction in
        exact Set.mem_singleton_iff.1 (hAss
          ((isAssociatedPoint_iff_of_isIso_stalkFunctor_map i x (hstalk x hxV)).2 hx))
      · exact absurd hx (Stacks.Divisors.notMem_associatedPoints_of_one_le_depth G x
          (le_trans (by norm_num) (hdepth x hxV)))
    have hmonoG : Mono (smulPowHom G fU 1) :=
      mono_smulPowHom_of_isUnit_germ G fU fun x hx => (hunit x).2 (by
        rw [hAssG x hx]; exact hx₀)
    have _ : (Q₁ G).IsCoherent := SheafOfModules.cokernel_isCoherent _
    refine ⟨G, cokernel i, i, cokernel.π i, cokernel.condition _,
      { exact := ShortComplex.exact_cokernel i }, hG, SheafOfModules.cokernel_isCoherent _,
      fun x hx hfx => hx₀ (by rw [← hAssG x hx]; exact hfx), ?_, ?_⟩
    · -- the cokernel vanishes on `V`, which contains `U ∖ V(f)`
      intro x hx
      by_contra hfx
      have hsuppQ := Stacks.Coherent.supp_subset_compl_of_isZero_restrict V (cokernel i)
        (Stacks.Coherent.isZero_restrict_cokernel_of_isIso_restrict V i hiV)
      exact hsuppQ (AlgebraicGeometry.associatedPoints_subset_support _ hx)
        fun hxZ => hfx (hZ'f x hxZ)
    · -- the associated points of `G / f G` are immediate specializations of `x₀` in `V(f)`
      refine htower G (isCoherent_pushforward_spec_of_two_le_topCodim A hcat hfib _ (Q₁ G)
        fun x hx z hxz hz => ?_)
      have hfx : f ∈ x.1.asIdeal := by_contra fun h =>
        notMem_associatedPoints_cokernel_smulPowHom_of_isUnit G fU x ((hunit x).2 h) hx
      have hxV : x ∈ V := by
        by_contra hxV
        exact notMem_associatedPoints_cokernel_smulPowHom_of_two_le_depth G fU x
          (hdepth x hxV) hx
      have hxD : x ∈ D :=
        (isAssociatedPoint_cokernel_smulPowHom_iff_of_isIso_stalk i fU x (hstalk x hxV)).2 hx
      have hImm : Imm x := by
        by_contra hI
        exact hxV (Set.mem_biUnion (x := x) ⟨hxD, hI⟩ (subset_closure rfl))
      have hx₀x : x₀.1.asIdeal ≤ x.1.asIdeal := (hQF x hxD).2
      change x.1.asIdeal ≤ z.asIdeal at hxz
      have ha : a ≤ z.asIdeal := by
        by_contra ha
        exact hz ⟨⟨z, ha⟩, rfl⟩
      have h3 := three_le_topCodim_of_two_lt_closureLocalDimension
        (hdim ⟨x.1, hx₀x, hfx, x.2⟩ z (hx₀x.trans hxz) ha)
      exact two_le_topCodim_of_catenary hcatX hx₀x hImm hxz h3
  · -- no point of `U ∩ V(f)` lies on the closure of `x₀`: `F / f F` has no associated point
    refine ⟨F, cokernel (𝟙 F), 𝟙 F, cokernel.π (𝟙 F), cokernel.condition _,
      { exact := ShortComplex.exact_cokernel (𝟙 F) }, inferInstance,
      SheafOfModules.cokernel_isCoherent _,
      fun x hx hfx => hx₀ (by rw [← Set.mem_singleton_iff.1 (hAss hx)]; exact hfx), ?_, ?_⟩
    · intro x hx
      have _ : (cokernel (𝟙 F)).IsCoherent := SheafOfModules.cokernel_isCoherent _
      have _ : (cokernel (𝟙 F)).IsQuasicoherent :=
        (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
      rw [(isZero_iff_associatedPoints_eq_empty U _).1 (isZero_cokernel_of_epi (𝟙 F))] at hx
      exact absurd hx (Set.notMem_empty x)
    · refine htower F (isCoherent_pushforward_spec_of_two_le_topCodim A hcat hfib _ (Q₁ F)
        fun y hy => ?_)
      obtain ⟨hfy, hx₀y⟩ := hQF y hy
      exact absurd ⟨y.1, hx₀y, hfy, y.2⟩ hmeet

end Stacks.Algebraization

end
