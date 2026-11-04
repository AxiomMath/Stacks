module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.DepthThreeCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.DepthThreeImprovementInputs
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.IdealPowerDirectSum
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FinitenessDepthCriterionDualizing
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.FlatLocalBaseCanonicalExtension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CanonicalExtensionDepthThree
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KernelStalk
public import StacksFrontier.AlgebraicGeometry.StalkFiniteType.Basic
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.Topology.Sheaves.PresheafOfModules.StalkMap

/-!
# The `Iᵏ`-torsion subsheaf of a coherent module on `U` and its cohomology

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, and assume `A` has a dualizing complex. Let `𝒢` be a
coherent `𝒪_U`-module with `depth(𝒢_y) + δ^Y_Z(y) ≥ 3` at every point `y` of `U ∩ Y`, and let
`k ≥ 0`. This file constructs the `Iᵏ`-torsion subsheaf `𝒦 ⊆ 𝒢` — every map into `𝒢` from an
`𝒪_U`-module killed by `Iᵏ` factors through it — and shows that `H⁰(U, 𝒦)` and `H¹(U, 𝒦)` are
finite `A`-modules. This is the finiteness input of the proof of [Stacks, Tag 0EJI], where
`𝒦` is the `Iᵏ`-torsion of a term `ℱ''_N` of the system of [Stacks, Tag 0EJG].

## Main definitions

* `Stacks.Algebraization.killChain`: for global functions `b₁, …, b_r`, the subsheaf of sections
  killed by all of them, as an iterated kernel.

## Main results

* `Stacks.Algebraization.min_depth_two_le_depth_ker_lsmul`: over a Noetherian ring, the kernel of
  multiplication by an element on a finite module `N` has depth at least `min(depth N, 2)`.
* `Stacks.Algebraization.exists_torsionSubsheaf_finite`: the `Iᵏ`-torsion subsheaf exists, with
  `H⁰` and `H¹` finite; it is `killChain` for a family of generators of `Iᵏ`.

## Implementation notes

The kernel of multiplication by `b` on a stalk sits in `0 → ker(b) → N → bN → 0`, and `bN ⊆ N`
sits in `0 → bN → N → N/bN → 0`; the depth lemma [Stacks, Tag 00LX] applied to both gives
`depth(bN) ≥ min(depth N, 1)` and then `depth ker(b) ≥ min(depth N, 2)`. Off `U ∩ Y` some
generator of `Iᵏ` is a unit in the local ring, so the stalk of `𝒦` vanishes there. On `U ∩ Y`,
`δ^Y_Z ≥ 1`, so `depth(𝒦_y) + δ^Y_Z(y) ≥ min(depth(𝒢_y) + δ^Y_Z(y), 2 + δ^Y_Z(y)) ≥ 3`, and
`Stacks.Algebraization.finite_complementSheafCohomology_of_three_le_depth_add_distanceToZ`
applies to `𝒦`.

## References

* [Stacks Project, Tag 0EJI](https://stacks.math.columbia.edu/tag/0EJI)
* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 00LX](https://stacks.math.columbia.edu/tag/00LX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing

universe u

namespace Stacks.Algebraization

/-! ### The depth of the kernel of a multiplication -/

/-- `min(d, 2) ≤ min(d, 1) + 1` in `ℕ∞`. -/
private theorem min_two_le_min_one_add_one (d : ℕ∞) : min d 2 ≤ min d 1 + 1 := by
  rcases le_total d 1 with h | h
  · rw [min_eq_left h]
    exact (min_le_left d 2).trans le_self_add
  · rw [min_eq_right h]
    exact (min_le_right d 2).trans (by norm_num)

/-- A submodule `P` of a finite module `N` which is the kernel of a surjection `g : N → M` has
`I`-depth at least `min(depth N, depth M + 1)`. -/
private theorem min_add_one_le_depth_of_surjective {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {N M : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [AddCommGroup M] [Module R M] {g : N →ₗ[R] M} {P : Submodule R N} (hg : Function.Surjective g)
    (hP : LinearMap.ker g = P) :
    min (Module.depth R I N) (Module.depth R I M + 1) ≤ Module.depth R I P := by
  subst hP
  exact (Module.min_depth_le_depth_of_exact I (LinearMap.exact_subtype_ker_map g)
    (Submodule.injective_subtype _) hg).2.2

/-- **The kernel of a multiplication has depth at least `min(depth N, 2)`.** Over a Noetherian
ring `R`, for an ideal `I`, a finite module `N` and `b ∈ R`, the submodule of `N` killed by `b`
has `I`-depth at least `min(depth_I N, 2)`. -/
public theorem min_depth_two_le_depth_ker_lsmul {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] (b : R) :
    min (Module.depth R I N) 2 ≤ Module.depth R I (LinearMap.ker (LinearMap.lsmul R N b)) := by
  set f := LinearMap.lsmul R N b
  -- the image `bN` has depth at least `min(depth N, 1)`
  have hQ : min (Module.depth R I N) 1 ≤ Module.depth R I (LinearMap.range f) :=
    (min_le_min_left _ le_add_self).trans
      (min_add_one_le_depth_of_surjective I (Submodule.mkQ_surjective _) (Submodule.ker_mkQ _))
  have hK := min_add_one_le_depth_of_surjective I (LinearMap.surjective_rangeRestrict f)
    (LinearMap.ker_rangeRestrict f)
  exact (le_min (min_le_left _ _)
    ((min_two_le_min_one_add_one _).trans (add_le_add hQ le_rfl))).trans hK

/-! ### The stalk of the kernel of a multiplication -/

section KillChain

variable {X : Scheme.{u}}

/-- The stalk map of a morphism of `𝒪_X`-modules, as a linear map of stalks over the local ring. -/
private def stalkLin {M N : X.Modules} (f : M ⟶ N) (y : X) :
    M.presheaf.stalk y →ₗ[X.presheaf.stalk y] N.presheaf.stalk y :=
  AlgebraicGeometry.stalkMapLinear (R := X.presheaf) _ _ f.val y

/-- The stalk at `y` of the subsheaf of `M` killed by a global function `b`, as a submodule of the
stalk of `M`: it is the kernel of multiplication by the germ of `b`. -/
private theorem range_stalk_kernel_ι_sectionSmul (b : Γ(X, ⊤)) (M : X.Modules) (y : X) :
    LinearMap.range (stalkLin (kernel.ι (sectionSmul b M)) y) =
      LinearMap.ker (LinearMap.lsmul (X.presheaf.stalk y) (M.presheaf.stalk y)
        ((X.presheaf.germ ⊤ y trivial).hom b)) := by
  have hsmul : ∀ w : M.presheaf.stalk y,
      stalkLin (sectionSmul b M) y w = (X.presheaf.germ ⊤ y trivial).hom b • w := fun w =>
    stalk_sectionSmul_apply b M y w
  refine SetLike.ext fun m => ?_
  have h' := SetLike.ext_iff.1
    (Stacks.SheafOfModules.TensorStalkRingedSpace.range_stalkMapL_kernel_ι
      (X := X.toRingedSpace) (sectionSmul b M) y) m
  simp only [LinearMap.mem_range, LinearMap.mem_ker] at h' ⊢
  rwa [LinearMap.lsmul_apply, ← hsmul]

/-- The stalk of a kernel injects into the stalk of the source. -/
private theorem injective_stalk_kernel_ι {M N : X.Modules} (f : M ⟶ N) (y : X) :
    Function.Injective (stalkLin (kernel.ι f) y) :=
  Stacks.SheafOfModules.TensorStalkRingedSpace.injective_stalkMapL_kernel_ι
    (X := X.toRingedSpace) f y

/-- **The kernel of a multiplication on a stalk has depth at least `min(depth, 2)`.** For a
module `M` of finite type on a locally Noetherian scheme and a global function `b`, the stalk of
the subsheaf of `M` killed by `b` has depth at least `min(depth(M_y), 2)`. -/
public theorem min_depth_two_le_depth_stalk_kernel_sectionSmul [IsLocallyNoetherian X]
    (b : Γ(X, ⊤)) (M : X.Modules) [M.IsFiniteType] (y : X) :
    min (Module.depth (X.presheaf.stalk y) (maximalIdeal (X.presheaf.stalk y))
        (M.presheaf.stalk y)) 2 ≤
      Module.depth (X.presheaf.stalk y) (maximalIdeal (X.presheaf.stalk y))
        ((kernel (sectionSmul b M)).presheaf.stalk y) := by
  have : Module.Finite (X.presheaf.stalk y) (M.presheaf.stalk y) :=
    Stacks.StalkFiniteType.finite_stalk M y
  let e := (LinearEquiv.ofInjective _ (injective_stalk_kernel_ι (sectionSmul b M) y)).trans
    (LinearEquiv.ofEq _ _ (range_stalk_kernel_ι_sectionSmul b M y))
  rw [Module.depth_eq_depth_of_linearEquiv _ e]
  exact min_depth_two_le_depth_ker_lsmul _ _

/-- Where the germ of `b` is a unit, the subsheaf killed by `b` has zero stalk. -/
public theorem subsingleton_stalk_kernel_sectionSmul (b : Γ(X, ⊤)) (M : X.Modules) (y : X)
    (hb : IsUnit ((X.presheaf.germ ⊤ y trivial).hom b)) :
    Subsingleton ((kernel (sectionSmul b M)).presheaf.stalk y) := by
  have hker : ∀ m, stalkLin (kernel.ι (sectionSmul b M)) y m = 0 := fun m => by
    have hm : stalkLin (kernel.ι (sectionSmul b M)) y m ∈
        LinearMap.ker (LinearMap.lsmul (X.presheaf.stalk y) (M.presheaf.stalk y)
          ((X.presheaf.germ ⊤ y trivial).hom b)) := by
      rw [← range_stalk_kernel_ι_sectionSmul]
      exact LinearMap.mem_range_self _ m
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply] at hm
    exact hb.smul_left_cancel.mp (hm.trans (smul_zero _).symm)
  exact ⟨fun m₁ m₂ => injective_stalk_kernel_ι (sectionSmul b M) y
    ((hker m₁).trans (hker m₂).symm)⟩

/-- A module whose stalk injects into a zero stalk has zero stalk. -/
private theorem subsingleton_stalk_kernel_of_subsingleton {M N : X.Modules} (f : M ⟶ N) (y : X)
    [Subsingleton (M.presheaf.stalk y)] : Subsingleton ((kernel f).presheaf.stalk y) :=
  ⟨fun _ _ => injective_stalk_kernel_ι f y (Subsingleton.elim _ _)⟩

/-- The subsheaf of `M` of sections killed by all the global functions in a list, as an iterated
kernel of multiplications. -/
public def killChain (M : X.Modules) : List Γ(X, ⊤) → X.Modules
  | [] => M
  | b :: l => kernel (sectionSmul b (killChain M l))

/-- The inclusion of `Stacks.Algebraization.killChain` into `M`. -/
public def killChainι (M : X.Modules) : (l : List Γ(X, ⊤)) → killChain M l ⟶ M
  | [] => 𝟙 M
  | b :: l => kernel.ι (sectionSmul b (killChain M l)) ≫ killChainι M l

/-- The iterated kernel of multiplications on a coherent module is coherent. -/
public theorem isCoherent_killChain [IsLocallyNoetherian X] (M : X.Modules) [M.IsCoherent] :
    ∀ l : List Γ(X, ⊤), (killChain M l).IsCoherent
  | [] => ‹M.IsCoherent›
  | b :: l =>
    have : (killChain M l).IsCoherent := isCoherent_killChain M l
    AlgebraicGeometry.isCoherent_kernel (sectionSmul b (killChain M l))

/-- **The universal property of the iterated kernel.** A map into `M` from a module on which
every function of the list acts by zero factors through `killChain M l`. -/
public theorem exists_lift_killChain (M : X.Modules) :
    ∀ (l : List Γ(X, ⊤)) {P : X.Modules} (φ : P ⟶ M), (∀ b ∈ l, sectionSmul b P = 0) →
      ∃ φ' : P ⟶ killChain M l, φ' ≫ killChainι M l = φ
  | [], _, φ, _ => ⟨φ, Category.comp_id φ⟩
  | b :: l, P, φ, h => by
    obtain ⟨φ', hφ'⟩ := exists_lift_killChain M l φ fun b' hb' => h b' (List.mem_cons_of_mem _ hb')
    have hzero : φ' ≫ sectionSmul b (killChain M l) = 0 := by
      have hnat := (Stacks.RegularSequence.globalSmulCenter X b).naturality φ'
      change φ' ≫ sectionSmul b (killChain M l) = sectionSmul b P ≫ φ' at hnat
      rw [hnat, h b List.mem_cons_self, zero_comp]
    refine ⟨kernel.lift _ φ' hzero, ?_⟩
    show kernel.lift _ φ' hzero ≫ (kernel.ι _ ≫ killChainι M l) = φ
    rw [← Category.assoc, kernel.lift_ι, hφ']

/-- The stalks of the iterated kernel have depth at least `min(depth(M_y), 2)`. -/
public theorem min_depth_two_le_depth_stalk_killChain [IsLocallyNoetherian X] (M : X.Modules)
    [M.IsCoherent] (y : X) :
    ∀ l : List Γ(X, ⊤),
      min (Module.depth (X.presheaf.stalk y) (maximalIdeal (X.presheaf.stalk y))
          (M.presheaf.stalk y)) 2 ≤
        Module.depth (X.presheaf.stalk y) (maximalIdeal (X.presheaf.stalk y))
          ((killChain M l).presheaf.stalk y)
  | [] => min_le_left _ _
  | b :: l => by
    have : (killChain M l).IsCoherent := isCoherent_killChain M l
    have : (killChain M l).IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
    have ih := min_depth_two_le_depth_stalk_killChain M y l
    exact (le_min ih (min_le_right _ _)).trans
      (min_depth_two_le_depth_stalk_kernel_sectionSmul b (killChain M l) y)

/-- Where the germ of a function of the list is a unit, the iterated kernel has zero stalk. -/
public theorem subsingleton_stalk_killChain (M : X.Modules) (y : X) :
    ∀ l : List Γ(X, ⊤), ∀ b ∈ l, IsUnit ((X.presheaf.germ ⊤ y trivial).hom b) →
      Subsingleton ((killChain M l).presheaf.stalk y)
  | [], _, hb, _ => absurd hb List.not_mem_nil
  | b' :: l, b, hb, hunit => by
    rcases List.mem_cons.mp hb with rfl | hbl
    · exact subsingleton_stalk_kernel_sectionSmul b (killChain M l) y hunit
    · have := subsingleton_stalk_killChain M y l b hbl hunit
      exact subsingleton_stalk_kernel_of_subsingleton (sectionSmul b' (killChain M l)) y

end KillChain

/-! ### The `Iᵏ`-torsion subsheaf on `U` -/

variable (S : AlgebraizationSituation.{u})

/-- At a point of `U` not lying over `Y`, some element of a generating set of `Iᵏ` has a unit
germ: the prime of the point does not contain `I`, hence not `Iᵏ`, hence not all the
generators. -/
private theorem exists_mem_isUnit_germ (k : ℕ) (t : Finset S.A)
    (ht : Ideal.span (t : Set S.A) = S.I ^ k) (y : S.U.toScheme)
    (hy : ∀ z : S.Y, S.U.ι.base y ≠ S.Yι.base z) :
    ∃ g ∈ t, IsUnit ((S.U.toScheme.presheaf.germ ⊤ y trivial).hom (scalarMap S g)) := by
  set p : PrimeSpectrum S.A := S.U.ι.base y
  have hIp : ¬ S.I ≤ p.asIdeal := by
    intro hI
    let z : PrimeSpectrum (S.A ⧸ S.I) :=
      ⟨p.asIdeal.map (Ideal.Quotient.mk S.I), Ideal.isPrime_map_quotientMk_of_isPrime hI⟩
    exact hy z (PrimeSpectrum.ext (Ideal.comap_map_mk hI).symm)
  obtain ⟨g, hgt, hgp⟩ : ∃ g ∈ t, g ∉ p.asIdeal := by
    by_contra! hcon
    exact hIp (Ideal.IsPrime.le_of_pow_le (ht ▸ Ideal.span_le.mpr hcon))
  refine ⟨g, hgt, ?_⟩
  rw [← Scheme.mem_basicOpen_top]
  show y ∈ S.U.toScheme.basicOpen (S.U.ι.appTop ((Scheme.ΓSpecIso (.of S.A)).inv g))
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  exact hgp

/-- `min(d, 2) + δ ≥ 3` from `d + δ ≥ 3` and `δ ≥ 1`. -/
private theorem three_le_min_two_add {d δ : ℕ∞} (h : 3 ≤ d + δ) (hδ : 1 ≤ δ) :
    3 ≤ min d 2 + δ := by
  rcases le_total d 2 with hd | hd
  · rwa [min_eq_left hd]
  · rw [min_eq_right hd]
    calc (3 : ℕ∞) = 2 + 1 := by norm_num
      _ ≤ 2 + δ := add_le_add le_rfl hδ

/-- **The `Iᵏ`-torsion subsheaf and the finiteness of its cohomology.** Let `A` have a dualizing
complex and let `𝒢` be a coherent `𝒪_U`-module with `depth(𝒢_y) + δ^Y_Z(y) ≥ 3` at every point
`y` of `U ∩ Y`. For every `k` there is a subsheaf `𝒦 ⊆ 𝒢` through which every map into `𝒢` from
an `𝒪_U`-module killed by `Iᵏ` factors, and `H⁰(U, 𝒦)` and `H¹(U, 𝒦)` are finite `A`-modules. -/
public theorem exists_torsionSubsheaf_finite
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (G : S.U.toScheme.Modules) [G.IsCoherent]
    (hdepth : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
      3 ≤ depthOfStalkOnOpen S G y + S.distanceToZ z)
    (k : ℕ) :
    ∃ (K : S.U.toScheme.Modules) (ι : K ⟶ G),
      (∀ {P : S.U.toScheme.Modules} (φ : P ⟶ G),
          (∀ a ∈ S.I ^ k, sectionSmul (scalarMap S a) P = 0) → ∃ φ' : P ⟶ K, φ' ≫ ι = φ) ∧
      ∀ p : ℕ, p ≤ 1 → Module.Finite S.A ((openCohomologyFunctor S p).obj K) := by
  obtain ⟨t, ht⟩ := Ideal.fg_of_isNoetherianRing (S.I ^ k)
  let l : List Γ(S.U.toScheme, ⊤) := t.toList.map (scalarMap S)
  have : (killChain G l).IsCoherent := isCoherent_killChain G l
  refine ⟨killChain G l, killChainι G l, fun φ hφ => ?_, fun p hp => ?_⟩
  · refine exists_lift_killChain G l φ fun b hb => ?_
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hb
    exact hφ g (ht ▸ Ideal.subset_span (Finset.mem_toList.mp hg))
  · have htop : ∀ y : S.U.toScheme, (∀ z : S.Y, S.U.ι.base y ≠ S.Yι.base z) →
        Module.depth (S.U.toScheme.presheaf.stalk y)
          (maximalIdeal (S.U.toScheme.presheaf.stalk y))
          ((killChain G l).presheaf.stalk y) = ⊤ := fun y hy => by
      obtain ⟨g, hgt, hunit⟩ := exists_mem_isUnit_germ S k t ht y hy
      have := subsingleton_stalk_killChain G y l (scalarMap S g)
        (List.mem_map.mpr ⟨g, Finset.mem_toList.mpr hgt, rfl⟩) hunit
      exact Module.depth_eq_top_of_subsingleton _
    have hdep : ∀ (y : S.U.toScheme) (z : S.Y), S.U.ι.base y = S.Yι.base z →
        (3 : ℕ∞) ≤ Module.depth (S.U.toScheme.presheaf.stalk y)
            (maximalIdeal (S.U.toScheme.presheaf.stalk y))
            ((killChain G l).presheaf.stalk y) + S.distanceToZ z := fun y z hyz =>
      (three_le_min_two_add (hdepth y z hyz) (S.one_le_distanceToZ y z hyz)).trans
        (add_le_add (min_depth_two_le_depth_stalk_killChain G y l) le_rfl)
    have hfin := finite_complementSheafCohomology_of_three_le_depth_add_distanceToZ S hdual
      (killChain G l) htop hdep p hp
    exact finite_openCohomology_of_finite_cohomologyOverBase S p _ <| Module.Finite.equiv
      (cohomologyOverBaseLinearEquivComplementSheafCohomology S (killChain G l) p).symm

end Stacks.Algebraization

end
