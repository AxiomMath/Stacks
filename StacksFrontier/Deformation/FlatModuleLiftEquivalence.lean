module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.CanonicalObstructionVanishing
public import StacksFrontier.Homology.Perfect.NilpotentLifting
public import StacksFrontier.Homology.Tor.BaseChangeIndependence.DerivedLift
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism

/-!
# Reductions for the two lifting problems of a flat module along a thickening

Let `A' → A` be a surjection of commutative rings with nilpotent kernel, let `P' → Q'` be a flat
map of `A'`-algebras, and let `P`, `Q` be their base changes to `A`. For an `A`-flat `P`-module
`M`, Stacks 0DZ2 compares the problem of lifting `M` to an `A'`-flat `P'`-module with that of
lifting `M ⊗_P Q` to an `A'`-flat `Q'`-module. The source's proof recasts both problems as the
vanishing of one class in a `P`-module and then compares the two; this file contains the
reductions that surround that comparison.

## Main results

* `Deformation.squareZero_devissage`: a property of surjections of commutative rings that holds
  for the square-zero ones and is stable under composition holds for every surjection with
  nilpotent kernel. This is the reduction to the square-zero case that Stacks 0DZ2 leaves to the
  reader.
* `Deformation.exists_pow_smul_eq_zero_of_mem`: an element killed by a power of every element of
  a finitely generated ideal is killed by a power of the ideal.
* `Deformation.exists_pow_smul_eq_zero_of_localization_eq_zero`: an element whose image in the
  localization at `g` vanishes is killed by a power of `g`.
* `Deformation.eq_zero_of_one_tmul_eq_zero`: a flat base change which is an isomorphism modulo a
  finitely generated ideal `I` is injective on the `I`-primary component.
* `Deformation.eq_zero_iff_one_tmul_eq_zero_of_localization`: an element which dies in the
  localization at every element of `I` vanishes if and only if its base change does. This is the
  reduction of Stacks 0DZ2 to the local liftability hypothesis, with the obstruction class
  abstracted to an arbitrary element of an arbitrary module.
* `Deformation.exists_flat_lift_iff_canonicalObstructionMap_eq_zero`: over a thickening with
  nilpotent kernel, a flat lift of `M` to a `P'`-module exists exactly when the canonical
  obstruction morphism of Stacks 0DYR vanishes.
* `Deformation.eq_zero_iff_eq_zero_of_baseChange`: two classes corresponding under base change
  vanish together, given the local hypothesis on the source class.
* `Deformation.exists_flat_lift_iff_exists_flat_lift_baseChange`: the equivalence of the two
  lifting problems, conditional on base change of the canonical obstruction class.

## Implementation notes

The obstruction classes are morphisms of the derived category, so they live one universe above
the rings; the base-change lemmas are therefore stated for modules in `Type (max u w)` over
rings in `Type u` and are applied at `w = u + 1`.

`exists_flat_lift_iff_exists_flat_lift_baseChange` is **not** a proof of Stacks 0DZ2: it carries
two hypotheses that the source proves. `hbc` is base change of the canonical obstruction map,
which is part (3) of Stacks 0DYR, combined with the base-change identification of the two Ext
groups from Stacks 0A6A. `hloc` is the conclusion of the source's localization step, which again
needs base change of the obstruction map, at the localization squares.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 05EC](https://stacks.math.columbia.edu/tag/05EC)
-/

@[expose] public section

open CategoryTheory CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u w

namespace Deformation

/-! ### Reduction to a square-zero thickening -/

/-- The square of the `k`-th power of an ideal is contained in its `(k+1)`-st power for
`1 ≤ k`: the tower of quotients `A'/Iᵏ` has square-zero successive thickenings. -/
theorem sq_pow_le_pow_succ {A' : Type u} [CommRing A'] (I : Ideal A') {k : ℕ} (hk : 1 ≤ k) :
    (I ^ k) ^ 2 ≤ I ^ (k + 1) := by
  rw [← pow_mul]
  exact Ideal.pow_le_pow_right (by omega)

/-- **Reduction to the square-zero case.** A property `motive` of surjections of commutative
rings which holds for the square-zero surjections and is stable under composition and under
isomorphisms of the target holds for every surjection with nilpotent kernel. The interpolating
rings are the quotients by the powers of the kernel. -/
theorem squareZero_devissage
    (motive : ∀ (R S : Type u) [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hiso : ∀ (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
      (g : R →+* S) (e : S ≃+* T), motive R S g → motive R T ((e : S →+* T).comp g))
    (hsq : ∀ (R S : Type u) [CommRing R] [CommRing S] (g : R →+* S),
      Function.Surjective g → (RingHom.ker g) ^ 2 = ⊥ → motive R S g)
    (hcomp : ∀ (R S T : Type u) [CommRing R] [CommRing S] [CommRing T]
      (g : R →+* S) (h : S →+* T), Function.Surjective g → Function.Surjective h →
      motive R S g → motive S T h → motive R T (h.comp g))
    {A' A : Type u} [CommRing A'] [CommRing A] (f : A' →+* A)
    (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f)) :
    motive A' A f := by
  have key : ∀ (n : ℕ) (R : Type u) (_ : CommRing R) (I : Ideal R), I ^ n = ⊥ →
      motive R (R ⧸ I) (Ideal.Quotient.mk I) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R _ I hI
      have hsq' : ∀ J : Ideal R, J ^ 2 ≤ ⊥ → motive R (R ⧸ J) (Ideal.Quotient.mk J) :=
        fun J hJ => hsq R _ _ Ideal.Quotient.mk_surjective
          (by rw [Ideal.mk_ker]; exact le_bot_iff.mp hJ)
      rcases le_or_gt n 2 with hn | hn
      · exact hsq' I (by rw [← hI]; exact Ideal.pow_le_pow_right hn)
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hm : 2 ≤ m := by omega
        set K : Ideal R := I ^ m with hK
        have hKsq : K ^ 2 ≤ ⊥ := by
          rw [← hI, hK]
          exact sq_pow_le_pow_succ I (by omega)
        have hKI : K ≤ I := Ideal.pow_le_self (by omega)
        have hmapI : (Ideal.map (Ideal.Quotient.mk K) I) ^ m = ⊥ := by
          rw [← Ideal.map_pow, ← hK, Ideal.map_quotient_self]
        have htail : motive (R ⧸ K) ((R ⧸ K) ⧸ Ideal.map (Ideal.Quotient.mk K) I)
            (Ideal.Quotient.mk _) := ih m (by omega) (R ⧸ K) inferInstance _ hmapI
        have hfact : motive (R ⧸ K) (R ⧸ I) (Ideal.Quotient.factor hKI) := by
          have h := hiso (R ⧸ K) ((R ⧸ K) ⧸ Ideal.map (Ideal.Quotient.mk K) I) (R ⧸ I)
            (Ideal.Quotient.mk _) (DoubleQuot.quotQuotEquivQuotOfLE hKI) htail
          refine cast (congrArg (motive (R ⧸ K) (R ⧸ I)) ?_) h
          ext x
          exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk x hKI
        have hcompose := hcomp R (R ⧸ K) (R ⧸ I) (Ideal.Quotient.mk K)
          (Ideal.Quotient.factor hKI) Ideal.Quotient.mk_surjective
          (Ideal.Quotient.factor_surjective hKI) (hsq' K hKsq) hfact
        rwa [Ideal.Quotient.factor_comp_mk] at hcompose
  obtain ⟨n, hn⟩ := hnil
  have h := key n A' inferInstance (RingHom.ker f) hn
  have h2 := hiso A' (A' ⧸ RingHom.ker f) A (Ideal.Quotient.mk _)
    (RingHom.quotientKerEquivOfSurjective hf) h
  refine cast (congrArg (motive A' A) ?_) h2
  ext x
  rfl

/-! ### Power torsion from pointwise annihilation -/

/-- An element of a module killed by some power of every element of a finitely generated ideal
`I` is killed by a power of `I`. -/
theorem exists_pow_smul_eq_zero_of_mem {R : Type*} [CommRing R] {M : Type*}
    [AddCommGroup M] [Module R M] {I : Ideal R} (hI : I.FG) {m : M}
    (h : ∀ g ∈ I, ∃ n : ℕ, g ^ n • m = 0) : ∃ n : ℕ, 0 < n ∧ ∀ a ∈ I ^ n, a • m = 0 := by
  have hsub : I ≤ ((R ∙ m).annihilator).radical := by
    intro g hg
    obtain ⟨n, hn⟩ := h g hg
    exact ⟨n, (Submodule.mem_annihilator_span_singleton _ _).mpr hn⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hsub hI
  exact ⟨n + 1, n.succ_pos, fun a ha =>
    (Submodule.mem_annihilator_span_singleton _ _).mp (hn (Ideal.pow_le_pow_right n.le_succ ha))⟩

/-- A module each of whose elements is killed by a power of every element of a finitely generated
ideal `I` is `I`-power torsion. -/
theorem isIPowerTorsion_of_forall_exists_pow_smul_eq_zero {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R} (hI : I.FG)
    (h : ∀ m : M, ∀ g ∈ I, ∃ n : ℕ, g ^ n • m = 0) : IsIPowerTorsion R M I :=
  fun m => exists_pow_smul_eq_zero_of_mem hI (h m)

/-- An element killed by a power of every element of a finitely generated ideal `I` lies in the
`I`-primary component. -/
theorem mem_primaryComponent_of_forall_exists_pow_smul_eq_zero {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R} (hI : I.FG) {m : M}
    (h : ∀ g ∈ I, ∃ n : ℕ, g ^ n • m = 0) : m ∈ Ideal.primaryComponent M I := by
  obtain ⟨n, -, hn⟩ := exists_pow_smul_eq_zero_of_mem hI h
  refine (Ideal.primaryComponent_mem M I m).mpr ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff]
  exact fun a => hn a.1 a.2

/-- An element whose image in the localization at `g` vanishes is killed by a power of `g`. -/
theorem exists_pow_smul_eq_zero_of_localization_eq_zero {R : Type*} [CommRing R]
    {M Mg : Type*} [AddCommGroup M] [Module R M] [AddCommGroup Mg] [Module R Mg] (g : R)
    (loc : M →ₗ[R] Mg) [IsLocalizedModule (Submonoid.powers g) loc] {m : M}
    (h : loc m = 0) : ∃ n : ℕ, g ^ n • m = 0 := by
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers g) loc).mp h
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, ?_⟩
  rw [show g ^ n = (s : R) from hn]
  exact hs

/-! ### Injectivity of base change on power torsion -/

/-- **Stacks 05EC, injectivity.** If `R → S` is flat and induces an isomorphism `R/I ≅ S/IS`
for a finitely generated ideal `I`, then `m ↦ 1 ⊗ m` is injective on the `I`-primary component
of any `R`-module. -/
theorem eq_zero_of_one_tmul_eq_zero {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M : Type (max u w)} [AddCommGroup M] [Module R M] {m : M}
    (hm : m ∈ Ideal.primaryComponent M I) (hzero : (1 : S) ⊗ₜ[R] m = 0) : m = 0 := by
  obtain ⟨e, he⟩ := (IPowerTorsion.baseChange_equiv_of_quotientMap_bijective.{u, u, w}
    R S I hI hflat hq).1 M
  have h0 : e ⟨m, hm⟩ = 0 := by
    apply Subtype.ext
    rw [he ⟨m, hm⟩]
    simpa using hzero
  have h1 : (⟨m, hm⟩ : Ideal.primaryComponent M I) = 0 :=
    e.injective (by simpa using h0)
  exact congrArg Subtype.val h1

/-- **The torsion criterion behind Stacks 0DZ2.** Let `S` be a flat `R`-algebra inducing an
isomorphism `R/I ≅ S/IS` for a finitely generated ideal `I`. An element of an `R`-module which
is killed by a power of every element of `I` vanishes exactly when its base change to `S` does.

Applied to the canonical obstruction class of Stacks 0DYR this is the step of Stacks 0DZ2 which
turns the hypothesis that `M` lifts over each `(P')_g` into the equivalence of the two lifting
problems. -/
theorem eq_zero_iff_one_tmul_eq_zero_of_localization {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {M : Type (max u w)} [AddCommGroup M] [Module R M] {m : M}
    (hloc : ∀ g ∈ I, ∃ n : ℕ, g ^ n • m = 0) :
    m = 0 ↔ (1 : S) ⊗ₜ[R] m = 0 := by
  refine ⟨fun h => by rw [h, TensorProduct.tmul_zero], fun h => ?_⟩
  exact eq_zero_of_one_tmul_eq_zero.{u, w} I hI hflat hq
    (mem_primaryComponent_of_forall_exists_pow_smul_eq_zero hI hloc) h

/-! ### Liftability as the vanishing of the obstruction class -/

/-- A bounded-above object of `D(P)` whose derived reduction along a surjection with nilpotent
kernel admits a bounded-above projective representative is itself bounded above. -/
theorem minus_of_derivedExtensionScalars_iso {P' P : Type u} [CommRing P'] [CommRing P]
    (f : P' →+* P) (hf : Function.Surjective f) (hnil : IsNilpotent (RingHom.ker f))
    (K : DerivedCategory (ModuleCat.{u} P))
    (hK : (DerivedCategory.TStructure.t (C := ModuleCat.{u} P)).minus K)
    (K' : DerivedCategory (ModuleCat.{u} P'))
    (e : (derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj K' ≅ K) :
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} P')).minus K' := by
  obtain ⟨N, hN⟩ := (DerivedCategory.minus_iff K).1 hK
  obtain ⟨E, hEproj, hEb, ⟨eE⟩⟩ :=
    StacksDraft.TorAmplitude.exists_projective_representative_of_isLE K (N - 1)
      (fun i hi => hN i (by omega))
  have hEmod : ∀ i : ℤ, Module.Projective P (E.X i) := by
    intro i
    have := hEproj i
    infer_instance
  obtain ⟨C, ⟨b, hb⟩, -, ⟨eC⟩, -⟩ :=
    StacksDraft.Perfect.exists_boundedAbove_projective_lift_representing_of_surjective.{u, u, u}
      f hf E K' ⟨N - 1, hEb⟩ hEmod ⟨eE.symm ≪≫ e.symm⟩ hnil
  have : C.IsStrictlyLE b := hb
  have : (DerivedCategory.Q.obj C).IsLE b := inferInstance
  exact ⟨b, DerivedCategory.TStructure.t.isLE_of_iso eC b⟩

/-- **Stacks 0DZ2, steps (b) and (c).** Let `A' → A` be a surjection with nilpotent kernel, let
`P'` be a flat `A'`-algebra and `P = P' ⊗_{A'} A`, and let `M` be an `A`-flat `P`-module. Then
`M` has an `A'`-flat lift to a `P'`-module if and only if the canonical obstruction morphism of
Stacks 0DYR for the square-zero surjection `P' → P` vanishes on `M`.

The two halves are Stacks 0DZ1, which turns a flat lift into a bounded-above derived lift, and
the vanishing criterion of Stacks 0DYR, which turns a derived lift into the vanishing of the
obstruction; the derived lift produced by the latter is bounded above because the kernel of
`P' → P` is nilpotent. -/
theorem exists_flat_lift_iff_canonicalObstructionMap_eq_zero
    (A' A P' : Type u) [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Module.Flat A' P']
    (hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)))
    (hzeroP : (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) ^ 2 = ⊥)
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
    [IsScalarTower A (TensorProduct A' P' A) M] [Module.Flat A M]
    (K : DerivedCategory (ModuleCat.{u} (TensorProduct A' P' A)))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} (TensorProduct A' P' A))).minus K)
    (eK : K ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)))) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap P' (TensorProduct A' P' A))).obj (ModuleCat.of P' M') ≅
          ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) ↔
      (Deformation.Obstruction.canonicalObstructionMap
        (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK).val = 0 := by
  classical
  rw [Deformation.Obstruction.canonicalObstructionMap_eq_zero_iff_exists_lift
      (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK,
    Examples.DerivedLift.exists_flat_lift_iff_exists_derived_lift A' A P' hsurjA hnilA M]
  constructor
  · rintro ⟨Kminus, ⟨e⟩⟩
    exact ⟨Kminus.obj, ⟨e ≪≫ eK.symm⟩⟩
  · rintro ⟨K', ⟨e⟩⟩
    exact ⟨⟨K', minus_of_derivedExtensionScalars_iso _ hsurjP ⟨2, hzeroP⟩ K hK K' e⟩,
      ⟨e ≪≫ eK⟩⟩

/-! ### Comparing the two obstruction classes -/

/-- **Stacks 0DZ2, steps (e)–(g), in module-theoretic form.** Let `S` be a flat `R`-algebra
inducing an isomorphism `R/I ≅ S/IS` for a finitely generated ideal `I`. If a class `ωS` in an
`S`-module corresponds to the base change of a class `ωR` which is killed by a power of every
element of `I`, then the two classes vanish together.

Instantiated at the canonical obstruction classes of Stacks 0DYR this is the comparison of the
two obstructions: the correspondence is base change of the obstruction class, and the hypothesis
on `ωR` comes from the assumed local liftability. -/
theorem eq_zero_iff_eq_zero_of_baseChange {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {E F : Type (max u w)} [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]
    {ωR : E} {ωS : F}
    (hbc : ∃ e : F ≃ₗ[S] TensorProduct R S E, e ωS = (1 : S) ⊗ₜ[R] ωR)
    (hloc : ∀ g ∈ I, ∃ n : ℕ, g ^ n • ωR = 0) :
    ωR = 0 ↔ ωS = 0 := by
  obtain ⟨e, he⟩ := hbc
  rw [eq_zero_iff_one_tmul_eq_zero_of_localization.{u, w} I hI hflat hquot hloc, ← he]
  exact ⟨fun h => e.injective (by simp [h]), fun h => by simp [h]⟩

/-- **Stacks 0DZ2, conditional on base change of the canonical obstruction class.** In the
situation of Stacks 0DZ2 — a surjection `A' → A` with square-zero kernel, flat `A'`-algebras
`P'` and `Q'` with `P' → Q'` flat, `P = P' ⊗_{A'} A`, `Q = Q' ⊗_{A'} A` with `P/J ≅ Q/JQ` for a
finitely generated ideal `J` of `P`, and `N` the base change of `M` to `Q` — an `A`-flat
`P`-module `M` has an `A'`-flat lift to a `P'`-module if and only if `N` has an `A'`-flat lift
to a `Q'`-module.

The hypothesis `hbc` is base change of the canonical obstruction class, Stacks 0DYR(3): the
obstruction class of `N` corresponds to `1 ⊗ ω(M)` under the base-change identification of the
two Ext groups. The hypothesis `hloc` is the standing local liftability hypothesis of the
source, in the form it is used: the obstruction class of `M` is killed by a power of every
element of `J`. -/
theorem exists_flat_lift_iff_exists_flat_lift_baseChange
    (A' A P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q']
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hnilA : IsNilpotent (RingHom.ker (algebraMap A' A)))
    [Module.Flat A' P'] [Module.Flat A' Q']
    (hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)))
    (hzeroP : (RingHom.ker (algebraMap P' (TensorProduct A' P' A))) ^ 2 = ⊥)
    (hsurjQ : Function.Surjective (algebraMap Q' (TensorProduct A' Q' A)))
    (hzeroQ : (RingHom.ker (algebraMap Q' (TensorProduct A' Q' A))) ^ 2 = ⊥)
    [Algebra (TensorProduct A' P' A) (TensorProduct A' Q' A)]
    (hflatPQ : Module.Flat (TensorProduct A' P' A) (TensorProduct A' Q' A))
    (J : Ideal (TensorProduct A' P' A)) (hJ : J.FG)
    (hquot : Function.Bijective (Ideal.quotientMap
      (J.map (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)))
      (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)) Ideal.le_comap_map))
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
    [IsScalarTower A (TensorProduct A' P' A) M] [Module.Flat A M]
    (N : Type u) [AddCommGroup N] [Module (TensorProduct A' Q' A) N] [Module A N]
    [IsScalarTower A (TensorProduct A' Q' A) N] [Module.Flat A N]
    (hN : Nonempty (N ≃ₗ[TensorProduct A' Q' A]
      TensorProduct (TensorProduct A' P' A) (TensorProduct A' Q' A) M))
    (K : DerivedCategory (ModuleCat.{u} (TensorProduct A' P' A)))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} (TensorProduct A' P' A))).minus K)
    (eK : K ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' P' A)) 0).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))))
    (L : DerivedCategory (ModuleCat.{u} (TensorProduct A' Q' A)))
    (hL : (DerivedCategory.TStructure.t
      (C := ModuleCat.{u} (TensorProduct A' Q' A))).minus L)
    (eL : L ≅ DerivedCategory.Q.obj ((CochainComplex.singleFunctor
      (ModuleCat.{u} (TensorProduct A' Q' A)) 0).obj
        (ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N))))
    (hbc : ∃ e : (L ⟶ (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
            (TensorProduct A' Q' A)).obj L).obj
          (Deformation.Obstruction.squareZeroKernelObject
            (algebraMap Q' (TensorProduct A' Q' A)) hsurjQ))⟦(2 : ℤ)⟧)
        ≃ₗ[TensorProduct A' Q' A]
          TensorProduct (TensorProduct A' P' A) (TensorProduct A' Q' A)
            (K ⟶ (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
              (TensorProduct A' P' A)).obj K).obj
                (Deformation.Obstruction.squareZeroKernelObject
                  (algebraMap P' (TensorProduct A' P' A)) hsurjP))⟦(2 : ℤ)⟧),
      e (Deformation.Obstruction.canonicalObstructionMap
            (algebraMap Q' (TensorProduct A' Q' A)) hsurjQ hzeroQ L hL).val =
        (1 : TensorProduct A' Q' A) ⊗ₜ[TensorProduct A' P' A]
          (Deformation.Obstruction.canonicalObstructionMap
            (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK).val)
    (hloc : ∀ g ∈ J, ∃ n : ℕ, g ^ n •
      (Deformation.Obstruction.canonicalObstructionMap
        (algebraMap P' (TensorProduct A' P' A)) hsurjP hzeroP K hK).val = 0) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap P' (TensorProduct A' P' A))).obj (ModuleCat.of P' M') ≅
          ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) ↔
      (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
        (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap Q' (TensorProduct A' Q' A))).obj (ModuleCat.of Q' N') ≅
          ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N))) := by
  obtain ⟨-⟩ := hN
  rw [exists_flat_lift_iff_canonicalObstructionMap_eq_zero A' A P' hsurjA hnilA hsurjP hzeroP
      M K hK eK,
    exists_flat_lift_iff_canonicalObstructionMap_eq_zero A' A Q' hsurjA hnilA hsurjQ hzeroQ
      N L hL eL]
  exact eq_zero_iff_eq_zero_of_baseChange.{u, u + 1} J hJ hflatPQ hquot hbc hloc

end Deformation

end
