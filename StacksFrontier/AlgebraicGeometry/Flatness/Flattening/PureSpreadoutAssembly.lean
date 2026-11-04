module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LocalQuotientSpreadout
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent

/-!
# Assembling the pure spreadout of Stacks 0AT8

This file constructs the pure spreadout of Stacks 0AT8 and proves steps 1 and 2 of its proof.

## Main results

* `AlgebraicGeometry.PureSpreadout.nonempty_of_data` is the constructor from data in the
  universes the structure demands, and `AlgebraicGeometry.PureSpreadout.nonempty_of_small` the
  one from a candidate spreadout module in an *arbitrary* universe. The test-module universe of
  the resulting universal injectivity is **free**, as Stacks 0AT8 requires.
* `AlgebraicGeometry.PureSpreadout.exists_finitePresentation_isLocalizedModule` is step 1 of the
  proof of Stacks 0AT8: clearing denominators.
* `AlgebraicGeometry.exists_mem_smul_mem_smul_top_of_isNoetherianRing_quotient` is step 2: the
  choice of the element `s` of the multiplicative subset.
* `AlgebraicGeometry.isNoetherianRing_quotient_map_maximalIdeal` is the finiteness input of
  step 2, and `AlgebraicGeometry.fibre_smul_mem_of_surjective` carries its conclusion from the
  local ring to a quotient of it.

## Implementation notes

The structure `AlgebraicGeometry.PureSpreadout` demands its module `N'` in the universe of the
situation's module `N`, whereas the module produced by the spreadout construction lives in the
universe of the situation's algebra `B`; neither universe dominates the other. The constructor
`nonempty_of_small` therefore only asks for `Small.{v₄} M`, extracts a model of `M` in the
smaller universe as an *opaque* type and transports every structure onto it along one
`AddEquiv`.

`Shrink.{v₄} M` is **not** usable as that model, even though
`Mathlib.Algebra.Module.Shrink` supplies `Module R (Shrink M)` and `Shrink.linearEquiv`: `Shrink`
also carries a `MulAction`-transported `SMul`, which is the instance `SMul R (Shrink M)` resolves
to, while `Module R (Shrink M)` has its own. The two are definitionally equal and not
syntactically equal, so `LinearMap.CompatibleSMul (Shrink M) M Y.B C` is not found and the
`restrictScalars` in the type of `PureSpreadout.isLocalizedModule` fails to elaborate. An opaque
model has no competing instances.

The closed-fibre hypothesis of the constructors is stated as an implication about elements of the
module rather than as membership in `nonZeroSMulDivisors` of a quotient, because that form
transports along a linear equivalence with no quotient bookkeeping; the translation to the form
`Stacks.UniversalInjectivity.universallyInjectivePoly_of_isLocalizedModule` consumes is done
inside `nonempty_of_data`.

In `nonempty_of_data`, `LinearMap.restrictScalars_trans` is rewritten in the *goal* before
`Stacks.UniversalInjectivity.universallyInjectivePoly_of_isLocalizedModule` is applied, with its
localization map supplied explicitly; otherwise the elaborator times out unifying
`?g.restrictScalars Y.A` against `g.restrictScalars Y.A` across two different base rings.

## References

* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
* [Stacks Project, Tag 0AT6](https://stacks.math.columbia.edu/tag/0AT6)
* [Stacks Project, Tag 05FR](https://stacks.math.columbia.edu/tag/05FR)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ w

namespace AlgebraicGeometry

/-- A finite module over a ring in universe `v` is `Small.{v}`. -/
theorem _root_.Stacks.Flatness.small_of_module_finite (A : Type v₂) [CommRing A] (M : Type w)
    [AddCommGroup M] [Module A M] [Module.Finite A M] : Small.{v₂} M := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  exact small_of_surjective
    ((span_range_eq_top_iff_surjective_fintypeLinearCombination A s).mp hs)

/-- A finitely generated submodule each of whose elements is annihilated by some element of a
multiplicative subset is annihilated by a single element of that subset. -/
theorem _root_.Submodule.exists_mem_smul_eq_zero_of_fg {R : Type*} {M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (S : Submonoid R) (K : Submodule R M) (hK : K.FG)
    (htor : ∀ x ∈ K, ∃ s ∈ S, s • x = 0) : ∃ s ∈ S, ∀ x ∈ K, s • x = 0 := by
  classical
  obtain ⟨t, ht⟩ := hK
  have htK : ∀ x ∈ t, x ∈ K := fun x hx ↦ ht ▸ Submodule.subset_span hx
  choose! c hcS hc0 using htor
  refine ⟨∏ x ∈ t, c x, Submonoid.prod_mem _ fun x hx ↦ hcS x (htK x hx), fun x hx ↦ ?_⟩
  have hle : K ≤ LinearMap.ker (LinearMap.lsmul R M (∏ y ∈ t, c y)) := by
    rw [← ht, Submodule.span_le]
    refine fun y hy ↦ LinearMap.mem_ker.mpr ?_
    rw [LinearMap.lsmul_apply, ← Finset.prod_erase_mul t c hy, mul_smul, hc0 y (htK y hy),
      smul_zero]
  exact hle hx

/-- **Descent of the closed-fibre injectivity condition along a surjection.** If `q : M → N'` is
a surjective `A`-linear map whose kernel lies inside `I • M`, and a monoid `T` acts on both
modules compatibly with `q`, then the condition "every element of `T` acts injectively modulo
`I`" descends from `M` to `N'`. -/
theorem fibre_smul_mem_of_surjective {A : Type*} [CommRing A] (I : Ideal A)
    {M : Type*} {N' : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N'] [Module A N']
    (q : M →ₗ[A] N') (hq : Function.Surjective q)
    (hker : LinearMap.ker q ≤ I • (⊤ : Submodule A M))
    {T : Type*} [SMul T M] [SMul T N'] (hequiv : ∀ (s : T) (x : M), q (s • x) = s • q x)
    (h : ∀ (s : T) (x : M), s • x ∈ I • (⊤ : Submodule A M) → x ∈ I • (⊤ : Submodule A M))
    (s : T) (y : N') (hy : s • y ∈ I • (⊤ : Submodule A N')) :
    y ∈ I • (⊤ : Submodule A N') := by
  have hmap : Submodule.map q (I • (⊤ : Submodule A M)) = I • (⊤ : Submodule A N') := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hq]
  obtain ⟨x, rfl⟩ := hq y
  rw [← hmap, ← hequiv] at hy
  rw [← hmap]
  obtain ⟨z, hz, hqz⟩ := hy
  have hsub : s • x - z ∈ LinearMap.ker q := by
    rw [LinearMap.mem_ker, map_sub, hqz, sub_self]
  exact Submodule.mem_map_of_mem (h s x (by simpa using Submodule.add_mem _ (hker hsub) hz))

/-- **The Noetherian closed fibre.** For a local ring `A` and an `A`-algebra `B` of finite type,
the closed fibre `B ⧸ 𝔪_A B` is a Noetherian ring. -/
theorem isNoetherianRing_quotient_map_maximalIdeal {A : Type u₁} [CommRing A] [IsLocalRing A]
    (B : Type u₂) [CommRing B] [Algebra A B] [Algebra.FiniteType A B] :
    IsNoetherianRing (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) := by
  have hker : ∀ a ∈ IsLocalRing.maximalIdeal A,
      algebraMap A (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) a = 0 :=
    fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  let _ialg : Algebra (IsLocalRing.ResidueField A)
      (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) :=
    (Ideal.Quotient.lift _ (algebraMap A _) hker).toAlgebra
  have _tow : IsScalarTower A (IsLocalRing.ResidueField A)
      (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ ↦ rfl)
  have _ftA : Algebra.FiniteType A
      (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A _) Ideal.Quotient.mk_surjective
  have _ftK : Algebra.FiniteType (IsLocalRing.ResidueField A)
      (B ⧸ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A _ _
  exact Algebra.FiniteType.isNoetherianRing (IsLocalRing.ResidueField A) _

/-- **Step 2 of the proof of Stacks 0AT8: the choice of `s`.** Let `J` be an ideal of `B` with
`B ⧸ J` Noetherian and let `N₀` be a finite `B`-module. Then some `s` of a given multiplicative
subset `S` absorbs every other one modulo `J`: whenever an element of `S` carries `y` into
`J N₀`, already `s` does. -/
theorem exists_mem_smul_mem_smul_top_of_isNoetherianRing_quotient {B : Type u₂} [CommRing B]
    (J : Ideal B) [IsNoetherianRing (B ⧸ J)] (S : Submonoid B)
    (N₀ : Type w) [AddCommGroup N₀] [Module B N₀] [Module.Finite B N₀] :
    ∃ s ∈ S, ∀ u ∈ S, ∀ y : N₀, u • y ∈ J • (⊤ : Submodule B N₀) →
      s • y ∈ J • (⊤ : Submodule B N₀) := by
  set P : Submodule B N₀ := J • (⊤ : Submodule B N₀) with hP
  have _fQ : Module.Finite B (N₀ ⧸ P) := Module.Finite.of_surjective P.mkQ P.mkQ_surjective
  have _fQ' : Module.Finite (B ⧸ J) (N₀ ⧸ P) := Module.Finite.of_restrictScalars_finite B _ _
  have key : ∀ (b : B) (x : N₀), algebraMap B (B ⧸ J) b • P.mkQ x = P.mkQ (b • x) :=
    fun b x ↦ by rw [IsScalarTower.algebraMap_smul, P.mkQ.map_smul]
  let K : Submodule (B ⧸ J) (N₀ ⧸ P) :=
    { carrier := {z | ∃ u ∈ S, algebraMap B (B ⧸ J) u • z = 0}
      zero_mem' := ⟨1, S.one_mem, smul_zero _⟩
      add_mem' := by
        rintro a b ⟨u, hu, ha⟩ ⟨v, hv, hb⟩
        have h1 : algebraMap B (B ⧸ J) (u * v) • a = 0 := by
          rw [map_mul, mul_comm, mul_smul, ha, smul_zero]
        have h2 : algebraMap B (B ⧸ J) (u * v) • b = 0 := by
          rw [map_mul, mul_smul, hb, smul_zero]
        exact ⟨u * v, S.mul_mem hu hv, by rw [smul_add, h1, h2, add_zero]⟩
      smul_mem' := by
        rintro c a ⟨u, hu, ha⟩
        exact ⟨u, hu, by rw [smul_comm, ha, smul_zero]⟩ }
  obtain ⟨sb, hsbmem, hsb⟩ := Submodule.exists_mem_smul_eq_zero_of_fg
    (S.map (algebraMap B (B ⧸ J))) K (IsNoetherian.noetherian K)
    (fun _ ⟨u, hu, hux⟩ ↦ ⟨algebraMap B (B ⧸ J) u, ⟨u, hu, rfl⟩, hux⟩)
  obtain ⟨s, hs, rfl⟩ := hsbmem
  refine ⟨s, hs, fun u hu y hy ↦ ?_⟩
  have hmem : P.mkQ y ∈ K :=
    ⟨u, hu, by rw [key]; exact (Submodule.Quotient.mk_eq_zero P).mpr hy⟩
  exact (Submodule.Quotient.mk_eq_zero P).mp ((key s y).symm.trans (hsb _ hmem))

namespace PureSpreadout

variable (Y : FinitelyPresentedLocalizedModuleSituation.{v₁, v₂, v₃, v₄})

/-- **Step 1 of the proof of Stacks 0AT8: clearing denominators.** In the situation of Stacks
0AT6 the module `N` is the localization at `S` of a finitely presented `B`-module.

This is Stacks 05N6 applied to the identity map of `N`, which is a localization at `S` because
`N` is already a module over the localization. -/
theorem exists_finitePresentation_isLocalizedModule :
    ∃ (N₀ : Type v₂) (_ : AddCommGroup N₀) (_ : Module Y.B N₀) (φ : N₀ →ₗ[Y.B] Y.N),
      Module.FinitePresentation Y.B N₀ ∧ IsLocalizedModule Y.S φ := by
  have _hid : IsLocalizedModule Y.S (LinearMap.id : Y.N →ₗ[Y.B] Y.N) :=
    isLocalizedModule_id Y.S Y.N Y.Bₛ
  obtain ⟨N₀, _, _, φ, _, hloc, hfp⟩ :=
    Module.exists_finite_isLocalizedModule_comp Y.S Y.Bₛ (LinearMap.id : Y.N →ₗ[Y.B] Y.N)
  exact ⟨N₀, ‹_›, ‹_›, LinearMap.id ∘ₗ φ, hfp inferInstance, hloc⟩

/-- The closed fibre of a module over the local base ring and over the algebra agree: extending
the maximal ideal to the algebra does not change the submodule it generates. -/
theorem mem_maximalIdeal_smul_top_iff {R : Type*} {S : Type*} {M : Type*}
    [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] (x : M) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔
      x ∈ Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule S M) := by
  have h : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) =
      (Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule S M)).restrictScalars R := by
    rw [Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  rw [h, Submodule.restrictScalars_mem]

/-- `Spec` of an abstract localization away from an element is an open immersion. -/
theorem isOpenImmersion_specMap_of_isLocalization_away {B : Type v₂} [CommRing B] (t : B)
    (C : Type v₂) [CommRing C] [Algebra B C] [IsLocalization.Away t C] :
    IsOpenImmersion (Scheme.Spec.map (CommRingCat.ofHom (algebraMap B C)).op) := by
  let e : Localization.Away t ≃ₐ[B] C :=
    IsLocalization.algEquiv (Submonoid.powers t) (Localization.Away t) C
  have hcomp : CommRingCat.ofHom (algebraMap B C) =
      CommRingCat.ofHom (algebraMap B (Localization.Away t)) ≫
        CommRingCat.ofHom (e : Localization.Away t →+* C) :=
    CommRingCat.hom_ext (RingHom.ext fun b ↦ (e.commutes b).symm)
  have _ : IsIso (CommRingCat.ofHom (e : Localization.Away t →+* C)) :=
    ⟨CommRingCat.ofHom (e.symm : C →+* Localization.Away t),
      CommRingCat.hom_ext (RingHom.ext fun x ↦ e.symm_apply_apply x),
      CommRingCat.hom_ext (RingHom.ext fun x ↦ e.apply_symm_apply x)⟩
  rw [hcomp]
  show IsOpenImmersion (Spec.map
    (CommRingCat.ofHom (algebraMap B (Localization.Away t)) ≫ CommRingCat.ofHom _))
  rw [Spec.map_comp]
  infer_instance

section Constructor

/-- An `R`-action obtained by restriction along `R → S → T` is the restriction of the
`S`-action. -/
theorem _root_.IsScalarTower.of_tower_algebra (R : Type*) (S : Type*) (T : Type*) (M : Type*)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [AddCommMonoid M] [Module R M] [Module S M] [Module T M]
    [IsScalarTower R T M] [IsScalarTower S T M] : IsScalarTower R S M := by
  refine IsScalarTower.of_algebraMap_smul fun a m ↦ ?_
  rw [← IsScalarTower.algebraMap_smul T (algebraMap R S a) m,
    ← IsScalarTower.algebraMap_apply R S T a, IsScalarTower.algebraMap_smul T a m]

/-- **The constructor for the pure spreadout of Stacks 0AT8.** The data of an affine open,
presented as an abstract localization away from an element, together with a spreadout module in
the universe of the situation's module, yields a pure spreadout.

The test-module universe `u₅` of the resulting universal injectivity is free: it is the free
universe of `Stacks.UniversalInjectivity.universallyInjectivePoly_of_isLocalizedModule`. -/
theorem nonempty_of_data [IsLocalRing Y.A] (t : Y.B) (C : Type v₂) [CommRing C]
    [Algebra Y.B C] [IsLocalization.Away t C] [Algebra Y.A C] [IsScalarTower Y.A Y.B C]
    [Algebra C Y.Bₛ] [IsScalarTower Y.B C Y.Bₛ]
    [Module C Y.N] [IsScalarTower C Y.Bₛ Y.N] [IsScalarTower Y.B C Y.N] [IsScalarTower Y.A C Y.N]
    (N' : Type v₄) [AddCommGroup N'] [Module C N']
    [Module Y.B N'] [Module Y.A N'] [IsScalarTower Y.B C N'] [IsScalarTower Y.A C N']
    [IsScalarTower Y.A Y.B N'] [Module.FinitePresentation C N'] [Module.Projective Y.A N']
    (g : N' →ₗ[C] Y.N) [IsLocalizedModule Y.S (g.restrictScalars Y.B)]
    (hfib : ∀ s ∈ Y.S, ∀ y : N',
      s • y ∈ IsLocalRing.maximalIdeal Y.A • (⊤ : Submodule Y.A N') →
        y ∈ IsLocalRing.maximalIdeal Y.A • (⊤ : Submodule Y.A N')) :
    Nonempty (PureSpreadout.{v₁, v₂, v₃, v₄, u₅} Y) := by
  have hT : ∀ s ∈ Y.S, s ∈ nonZeroSMulDivisors Y.B (N' ⧸
      (Ideal.map (algebraMap Y.A Y.B) (IsLocalRing.maximalIdeal Y.A) •
        (⊤ : Submodule Y.B N'))) := by
    intro s hs y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      ← mem_maximalIdeal_smul_top_iff, Submodule.Quotient.mk_eq_zero,
      ← mem_maximalIdeal_smul_top_iff]
    exact hfib s hs x
  refine ⟨{
    C := C
    N' := N'
    isOpenImmersion := isOpenImmersion_specMap_of_isLocalization_away t C
    finitePresentation := inferInstance
    projective := inferInstance
    localizationMap := g
    isLocalizedModule := inferInstance
    universallyInjective := ?_ }⟩
  rw [← LinearMap.restrictScalars_trans (R := Y.A) (S := Y.B) g]
  exact Stacks.UniversalInjectivity.universallyInjectivePoly_of_isLocalizedModule Y.S hT
    (g.restrictScalars Y.B)

/-- **The constructor for the pure spreadout of Stacks 0AT8, with the spreadout module in an
arbitrary universe.** Only smallness relative to the universe of the situation's module is
required. -/
theorem nonempty_of_small [IsLocalRing Y.A] (t : Y.B) (C : Type v₂) [CommRing C]
    [Algebra Y.B C] [IsLocalization.Away t C] [Algebra Y.A C] [IsScalarTower Y.A Y.B C]
    [Algebra C Y.Bₛ] [IsScalarTower Y.B C Y.Bₛ]
    [Module C Y.N] [IsScalarTower C Y.Bₛ Y.N] [IsScalarTower Y.B C Y.N] [IsScalarTower Y.A C Y.N]
    (M : Type w) [AddCommGroup M] [Module C M] [Small.{v₄} M]
    [Module Y.B M] [Module Y.A M] [IsScalarTower Y.B C M] [IsScalarTower Y.A C M]
    [Module.FinitePresentation C M] [Module.Projective Y.A M]
    (g : M →ₗ[C] Y.N) [IsLocalizedModule Y.S (g.restrictScalars Y.B)]
    (hfib : ∀ s ∈ Y.S, ∀ y : M,
      s • y ∈ IsLocalRing.maximalIdeal Y.A • (⊤ : Submodule Y.A M) →
        y ∈ IsLocalRing.maximalIdeal Y.A • (⊤ : Submodule Y.A M)) :
    Nonempty (PureSpreadout.{v₁, v₂, v₃, v₄, u₅} Y) := by
  have _tABM : IsScalarTower Y.A Y.B M := IsScalarTower.of_tower_algebra Y.A Y.B C M
  obtain ⟨N', ⟨q⟩⟩ := Small.equiv_small.{v₄} (α := M)
  let _acg : AddCommGroup N' := q.symm.addCommGroup
  let ead : N' ≃+ M := q.symm.addEquiv
  let _mC : Module C N' := ead.module C
  let _mB : Module Y.B N' := ead.module Y.B
  let _mA : Module Y.A N' := ead.module Y.A
  have _tBC : IsScalarTower Y.B C N' := LinearEquiv.isScalarTower C (ead.linearEquiv Y.B)
  have _tAC : IsScalarTower Y.A C N' := LinearEquiv.isScalarTower C (ead.linearEquiv Y.A)
  have _tAB : IsScalarTower Y.A Y.B N' := LinearEquiv.isScalarTower Y.B (ead.linearEquiv Y.A)
  have _fp : Module.FinitePresentation C N' :=
    Module.FinitePresentation.of_equiv (ead.linearEquiv C).symm
  have _proj : Module.Projective Y.A N' :=
    Module.Projective.of_equiv (ead.linearEquiv Y.A).symm
  have _loc : IsLocalizedModule Y.S
      ((g ∘ₗ (ead.linearEquiv C).toLinearMap).restrictScalars Y.B) :=
    IsLocalizedModule.of_linearEquiv_right Y.S (g.restrictScalars Y.B)
      ((ead.linearEquiv C).restrictScalars Y.B)
  refine nonempty_of_data Y t C N' (g ∘ₗ (ead.linearEquiv C).toLinearMap) ?_
  intro s hs y hy
  exact fibre_smul_mem_of_surjective _ (ead.linearEquiv Y.A).symm.toLinearMap
    (ead.linearEquiv Y.A).symm.surjective (by simp) (T := Y.S)
    (fun s x ↦ (ead.linearEquiv Y.B).symm.map_smul s x) (fun s x ↦ hfib s s.2 x) ⟨s, hs⟩ y hy

end Constructor

end PureSpreadout

end AlgebraicGeometry

end
