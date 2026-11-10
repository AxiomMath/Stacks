module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.Stratification
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.CokernelGenericFlatness
public import StacksFrontier.RingTheory.Flat.ShortExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kernels and base change for maps with flat target and flat cokernel

Let `φ : M → N` be a map of modules over a commutative ring `R` such that both `N` and the
cokernel `N ⧸ φ.range` are flat over `R`. Then `0 → ker φ → M → N → N ⧸ φ.range → 0` is exact
with flat tail, so tensoring with an arbitrary `R`-module `P` keeps the kernel: the kernel of
`P ⊗ φ` is the image of `P ⊗ ker φ`. For a map of `R`-algebras this says that the kernel ideal
commutes with base change, which is the algebraic heart of the statement that formation of the
scheme-theoretic image commutes with arbitrary base change (Stacks 0H41).

The second half of the file records the inputs needed to arrange that hypothesis generically.
Over a Noetherian domain, generic freeness (Stacks 051T) makes a finite type algebra flat after
inverting one element, and Stacks 0H40 makes the cokernel flat after inverting one more; the
lemmas about flatness of localized modules are there to move those two conclusions, which are
stated for the concrete `LocalizedModule.Away`, onto whatever model of the localization the
geometry produces.

## Main results

* `Module.Flat.ker_lTensor_eq_range_lTensor_ker_subtype`: the kernel of `P ⊗ φ` is the image of
  `P ⊗ ker φ` when `N` and `N ⧸ φ.range` are flat.
* `Stacks.GenericFlatness.ker_eq_map_of_isPushout_of_flat`: the ideal-theoretic form, for a
  pushout square of commutative rings.
* `Stacks.GenericFlatness.exists_flat_localizedModule_target_and_coker`: over a Noetherian
  domain, a finite type algebra map becomes one with flat target and flat cokernel after
  inverting a single nonzero element.
* `Stacks.GenericFlatness.flat_of_isLocalizedModule_away` and
  `Stacks.GenericFlatness.flat_quotient_of_isLocalizedModule_square`: transfer of those
  flatness conclusions to an arbitrary model of the localization.

## References

* [Stacks Project, Tag 0H41](https://stacks.math.columbia.edu/tag/0H41)
* [Stacks Project, Tag 0H40](https://stacks.math.columbia.edu/tag/0H40)
* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
* [Stacks Project, Tag 00HM](https://stacks.math.columbia.edu/tag/00HM)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

/-! ### The kernel after tensoring -/

namespace Module.Flat

/-- **Part of Stacks 0H41.** If a map of modules has flat target and flat cokernel, then
tensoring with an arbitrary module preserves its kernel: the kernel of `P ⊗ φ` is the image of
`P ⊗ ker φ`.

The proof factors `φ` through its range. Flatness of the range follows from the short exact
sequence defining the cokernel (Stacks 00HM), and both resulting short exact sequences stay
exact after tensoring (Stacks 00HL). -/
theorem ker_lTensor_eq_range_lTensor_ker_subtype
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (φ : M →ₗ[R] N) [Module.Flat R N] [Module.Flat R (N ⧸ φ.range)] :
    (LinearMap.lTensor P φ).ker =
      LinearMap.range (LinearMap.lTensor P φ.ker.subtype) := by
  let g : M →ₗ[R] φ.range := φ.codRestrict φ.range fun x ↦ ⟨x, rfl⟩
  have hN := flat_tor_zero (R := R) (M'' := φ.range) (M' := N)
    (M := N ⧸ φ.range) (N := P) φ.range.subtype φ.range.mkQ
    (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  have hflatRange : Module.Flat R φ.range :=
    flat_of_flat_of_flat_quotient (R := R) (M' := φ.range) (M := N)
      (M'' := N ⧸ φ.range) φ.range.subtype φ.range.mkQ
      (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ _)
      (Submodule.mkQ_surjective _)
  have := hflatRange
  have hg : Function.Surjective g := by
    rintro ⟨y, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  have hker : g.ker = φ.ker := by
    ext x
    exact ⟨fun hx ↦ congrArg Subtype.val hx, fun hx ↦ Subtype.ext hx⟩
  have hφg : Function.Exact φ.ker.subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    exact hker
  have hM := flat_tor_zero (R := R) (M'' := φ.ker) (M' := M)
    (M := φ.range) (N := P) φ.ker.subtype g
    (Submodule.injective_subtype _) hφg hg
  have hcomp : φ = φ.range.subtype.comp g := by ext x; rfl
  have htensorComp : LinearMap.lTensor P φ =
      (LinearMap.lTensor P φ.range.subtype).comp (LinearMap.lTensor P g) := by
    rw [← LinearMap.lTensor_comp]
    exact congrArg (LinearMap.lTensor P) hcomp
  have hExact : (LinearMap.lTensor P g).ker =
      LinearMap.range (LinearMap.lTensor P φ.ker.subtype) :=
    LinearMap.exact_iff.mp hM.2.1
  ext x
  constructor
  · intro hx
    have hxcomp : (LinearMap.lTensor P φ.range.subtype)
        ((LinearMap.lTensor P g) x) = 0 := by
      change (LinearMap.lTensor P φ) x = 0 at hx
      rw [htensorComp] at hx
      simpa only [LinearMap.comp_apply] using hx
    have hxg' : x ∈ (LinearMap.lTensor P g).ker := LinearMap.mem_ker.mpr (hN.1 hxcomp)
    rw [hExact] at hxg'
    exact hxg'
  · rintro ⟨y, rfl⟩
    have hzero : φ.comp φ.ker.subtype = 0 := by ext y; exact y.property
    have hzTensor : (LinearMap.lTensor P φ) ∘ₗ
        (LinearMap.lTensor P φ.ker.subtype) = 0 := by
      rw [← LinearMap.lTensor_comp, hzero, LinearMap.lTensor_zero]
    rw [LinearMap.mem_ker]
    change ((LinearMap.lTensor P φ).comp (LinearMap.lTensor P φ.ker.subtype)) y = 0
    exact congrArg (fun q ↦ q y) hzTensor

end Module.Flat

namespace Stacks.GenericFlatness

/-! ### The kernel ideal after base change -/

/-- **Part of Stacks 0H41.** For a map of `R`-algebras with flat target and flat cokernel, the
kernel ideal commutes with base change along `R → P`. -/
private theorem ker_tensorProduct_map_of_flat
    {R A B P : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [CommRing P] [Algebra R P]
    (φ : A →ₐ[R] B) [Module.Flat R B]
    [Module.Flat R (B ⧸ LinearMap.range φ.toLinearMap)] :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R P) φ) =
      (RingHom.ker φ).map
        (Algebra.TensorProduct.includeRight : A →ₐ[R] P ⊗[R] A) := by
  rw [← Submodule.restrictScalars_inj R]
  change LinearMap.ker (LinearMap.lTensor P φ.toLinearMap) = _
  rw [Ideal.map_includeRight_eq, Module.Flat.ker_lTensor_eq_range_lTensor_ker_subtype]
  rfl

/-- A pushout of commutative rings is isomorphic to the tensor product, compatibly with both
structure maps. -/
private theorem exists_iso_tensorProduct_of_isPushout
    {R A P A' : Type u} [CommRing R] [CommRing A] [CommRing P] [CommRing A']
    [Algebra R A] [Algebra R P] (a : A →+* A') (pA : P →+* A')
    (hA : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R P)) (CommRingCat.ofHom a) (CommRingCat.ofHom pA)) :
    ∃ e : CommRingCat.of A' ≅ CommRingCat.of (P ⊗[R] A),
      CommRingCat.ofHom a ≫ e.hom = CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] P ⊗[R] A).toRingHom ∧
      CommRingCat.ofHom pA ≫ e.hom = CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : P →ₐ[R] P ⊗[R] A).toRingHom := by
  let tA := (CommRingCat.isPushout_tensorProduct R P A).flip
  refine ⟨hA.isoPushout ≪≫ tA.isoPushout.symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, IsPushout.inl_isoPushout_hom_assoc,
      IsPushout.inl_isoPushout_inv]
  · simp only [Iso.trans_hom, Iso.symm_hom, IsPushout.inr_isoPushout_hom_assoc,
      IsPushout.inr_isoPushout_inv]
    rfl

/-- **Part of Stacks 0H41.** Let `φ : A → B` be a map of `R`-algebras with `B` and `B ⧸ φ(A)`
flat over `R`, and let both `A` and `B` be base changed along `R → P`, each square being a
pushout of commutative rings. Then the kernel of the base changed map is generated by the image
of the kernel of `φ`.

This is `Module.Flat.ker_lTensor_eq_range_lTensor_ker_subtype` transported along the canonical
identification of a pushout of commutative rings with a tensor product. -/
theorem ker_eq_map_of_isPushout_of_flat
    {R A B P A' B' : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing P] [CommRing A'] [CommRing B']
    [Algebra R A] [Algebra R B] [Algebra R P]
    (φ : A →ₐ[R] B) [Module.Flat R B]
    [Module.Flat R (B ⧸ LinearMap.range φ.toLinearMap)]
    (a : A →+* A') (b : B →+* B') (pA : P →+* A') (pB : P →+* B')
    (φ' : A' →+* B')
    (hA : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R P)) (CommRingCat.ofHom a) (CommRingCat.ofHom pA))
    (hB : IsPushout (CommRingCat.ofHom (algebraMap R B))
      (CommRingCat.ofHom (algebraMap R P)) (CommRingCat.ofHom b) (CommRingCat.ofHom pB))
    (ha : φ'.comp a = b.comp φ.toRingHom) (hp : φ'.comp pA = pB) :
    RingHom.ker φ' = (RingHom.ker φ).map a := by
  obtain ⟨eA, heAa, heAp⟩ := exists_iso_tensorProduct_of_isPushout a pA hA
  obtain ⟨eB, heBb, heBp⟩ := exists_iso_tensorProduct_of_isPushout b pB hB
  let ψ := Algebra.TensorProduct.map (AlgHom.id R P) φ
  have hw : CommRingCat.ofHom φ' ≫ eB.hom = eA.hom ≫ CommRingCat.ofHom ψ.toRingHom := by
    apply hA.hom_ext
    · rw [← Category.assoc, ← CommRingCat.ofHom_comp, ha, CommRingCat.ofHom_comp,
        Category.assoc, heBb, ← Category.assoc, heAa]
      ext x
      simp [ψ]
    · rw [← Category.assoc, ← CommRingCat.ofHom_comp, hp, heBp, ← Category.assoc, heAp]
      ext x
      simp [ψ]
  have hker : RingHom.ker φ' = (RingHom.ker ψ).comap eA.hom.hom := by
    ext x
    change φ' x = 0 ↔ ψ (eA.hom x) = 0
    have hx := congrArg (fun k : CommRingCat.of A' ⟶ _ ↦ k x) hw
    change eB.hom (φ' x) = ψ (eA.hom x) at hx
    rw [← hx]
    exact (map_eq_zero_iff eB.hom.hom (ConcreteCategory.bijective_of_isIso eB.hom).1).symm
  rw [hker, ker_tensorProduct_map_of_flat φ]
  have hcomp := congrArg CommRingCat.Hom.hom heAa
  change eA.hom.hom.comp a =
    (Algebra.TensorProduct.includeRight : A →ₐ[R] P ⊗[R] A).toRingHom at hcomp
  change ((RingHom.ker φ).map
    (Algebra.TensorProduct.includeRight : A →ₐ[R] P ⊗[R] A).toRingHom).comap _ = _
  rw [← hcomp, ← Ideal.map_map]
  exact Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso eA.hom)

/-! ### Flatness of localizations -/

/-- If `M` is flat after inverting `f`, then any base change `m : M → N` of `M` along a ring `P`
in which `f` is a unit is flat over `P`. -/
private theorem flat_of_isBaseChange_of_flat_away
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M] [CommRing P] [Algebra R P]
    [AddCommGroup N] [Module R N] [Module P N] [IsScalarTower R P N] {f : R}
    (hf : IsUnit (algebraMap R P f)) (m : M →ₗ[R] N) (hm : IsBaseChange P m)
    (h : Module.Flat (Localization.Away f) (LocalizedModule.Away f M)) :
    Module.Flat P N := by
  let Rf := Localization.Away f
  let _ : Algebra Rf P := (IsLocalization.Away.lift f hf).toAlgebra
  have : IsScalarTower R Rf P :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (IsLocalization.Away.lift_eq f hf x).symm
  have e₂ : Rf ⊗[R] M ≃ₗ[Rf] LocalizedModule.Away f M :=
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Rf
      (LocalizedModule.mkLinearMap _ M)).mp inferInstance).equiv
  have : Module.Flat Rf (Rf ⊗[R] M) := Module.Flat.of_linearEquiv e₂
  exact Module.Flat.of_linearEquiv
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R Rf P P M).trans hm.equiv).symm

/-- Flatness of a localized module transfers to any model of the same localization. -/
theorem flat_of_isLocalizedModule_away
    {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing P] [Algebra R P] {f : R} [IsLocalization.Away f P]
    [AddCommGroup N] [Module R N] [Module P N] [IsScalarTower R P N]
    (m : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers f) m]
    (h : Module.Flat (Localization.Away f) (LocalizedModule.Away f M)) :
    Module.Flat P N :=
  flat_of_isBaseChange_of_flat_away (IsLocalization.Away.algebraMap_isUnit f) m
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers f) P m).mp inferInstance) h

/-- Flatness after inverting one element persists after inverting a multiple. -/
private theorem flat_localizedModule_away_of_dvd
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {f g : R} (hfg : f ∣ g)
    (h : Module.Flat (Localization.Away f) (LocalizedModule.Away f M)) :
    Module.Flat (Localization.Away g) (LocalizedModule.Away g M) :=
  flat_of_isBaseChange_of_flat_away
    (isUnit_of_dvd_unit (map_dvd _ hfg) (IsLocalization.Away.algebraMap_isUnit g))
    (LocalizedModule.mkLinearMap _ M)
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers g) (Localization.Away g)
      (LocalizedModule.mkLinearMap _ M)).mp inferInstance) h

/-- The localization of a finite type algebra is flat over the localized base as soon as the
localization of the algebra at the image submonoid is. -/
private theorem flat_localizedModule_of_flat_algebra_localization
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (f : R)
    (h : Module.Flat (Localization.Away f)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)))) :
    Module.Flat (Localization.Away f) (LocalizedModule.Away f B) := by
  let Rf := Localization.Away f
  have e : Rf ⊗[R] B ≃ₗ[Rf] LocalizedModule.Away f B :=
    ((isLocalizedModule_iff_isBaseChange (Submonoid.powers f) Rf
      (LocalizedModule.mkLinearMap _ B)).mp inferInstance).equiv
  have hTensor : Module.Flat Rf (Rf ⊗[R] B) :=
    Module.Flat.of_linearEquiv
      (Localization.tensorRightAlgEquiv (Submonoid.powers f) B).toLinearEquiv
  have := hTensor
  exact Module.Flat.of_linearEquiv e.symm

/-- **Stacks 051T and 0H40 combined.** Let `R` be a Noetherian domain and `R → A → B` finite
type algebra maps. After inverting a single nonzero element of `R`, both `B` and the cokernel of
`A → B` become flat over the base.

Generic freeness gives flatness of `B`, and Stacks 0H40 gives flatness of the cokernel; the two
elements are combined into their product, since flatness after inverting an element persists
after inverting a multiple. -/
@[sga "1 IV 6.7" "M = B, flatness clause"]
theorem exists_flat_localizedModule_target_and_coker
    {R A B : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Algebra A B] [Algebra.FiniteType A B] [IsScalarTower R A B] :
    ∃ h : R, h ≠ 0 ∧
      Module.Flat (Localization.Away h) (LocalizedModule.Away h B) ∧
      Module.Flat (Localization.Away h)
        (LocalizedModule.Away h
          (B ⧸ LinearMap.range ((Algebra.linearMap A B).restrictScalars R))) := by
  obtain ⟨f, hf, hfree⟩ :=
    Algebra.exists_ne_zero_isFinitePresentationFreeAway (R := R) (S := B) (M := B)
  have hB : Module.Flat (Localization.Away f) (LocalizedModule.Away f B) :=
    flat_localizedModule_of_flat_algebra_localization f hfree.flat
  obtain ⟨g, hg, hC⟩ :=
    Module.exists_flat_localizedModule_coker (R := R) (A := A) (B := B)
      (M := A) (N := B) (Algebra.linearMap A B)
  refine ⟨f * g, mul_ne_zero hf hg,
    flat_localizedModule_away_of_dvd (dvd_mul_right f g) hB, ?_⟩
  exact flat_localizedModule_away_of_dvd ⟨f, by rw [mul_comm]⟩ hC

/-- In a pushout of commutative rings along a principal localization, the opposite edge is a
localization of modules over the original base. -/
theorem isLocalizedModule_of_isPushout_away
    {R A P B : Type u} [CommRing R] [CommRing A] [CommRing P] [CommRing B]
    [Algebra R A] [Algebra R P] [Algebra A B] [Algebra P B]
    [Algebra R B] [IsScalarTower R A B] [IsScalarTower R P B]
    (f : R) [IsLocalization.Away f P]
    (h : IsPushout (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap R P))
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap P B))) :
    IsLocalizedModule (Submonoid.powers f)
      (IsScalarTower.toAlgHom R A B).toLinearMap := by
  have hpush : Algebra.IsPushout R A P B :=
    CommRingCat.isPushout_iff_isPushout.mp h
  have hpush' : Algebra.IsPushout R P A B :=
    (Algebra.IsPushout.comm R A P B).mp hpush
  exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) P
    (IsScalarTower.toAlgHom R A B).toLinearMap).mpr
    ((Algebra.isPushout_iff R P A B).mp hpush')

/-- A commuting square of localized module maps localizes the quotient by the range, so flatness
of that quotient transfers to any model of the localization. -/
theorem flat_quotient_of_isLocalizedModule_square
    {R P M N M' N' : Type*} [CommRing R] [CommRing P]
    [Algebra R P] {f : R} [IsLocalization.Away f P]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M'] [Module R M'] [Module P M'] [IsScalarTower R P M']
    [AddCommGroup N'] [Module R N'] [Module P N'] [IsScalarTower R P N']
    (m : M →ₗ[R] M') (n : N →ₗ[R] N')
    [IsLocalizedModule (Submonoid.powers f) m]
    [IsLocalizedModule (Submonoid.powers f) n]
    (φ : M →ₗ[R] N) (φ' : M' →ₗ[P] N')
    (w : φ'.restrictScalars R ∘ₗ m = n ∘ₗ φ)
    (hflat : Module.Flat (Localization.Away f)
      (LocalizedModule.Away f (N ⧸ φ.range))) :
    Module.Flat P (N' ⧸ φ'.range) := by
  have hmap : IsLocalizedModule.map (Submonoid.powers f) m n φ =
      φ'.restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers f) m n
    rw [IsLocalizedModule.map_comp]
    exact w.symm
  have hrange : φ.range.localized' P (Submonoid.powers f) n = φ'.range := by
    rw [LinearMap.localized'_range_eq_range_localizedMap P (Submonoid.powers f) m n φ, hmap]
    rfl
  let e : (N' ⧸ φ.range.localized' P (Submonoid.powers f) n) ≃ₗ[P] (N' ⧸ φ'.range) :=
    Submodule.quotEquivOfEq _ _ hrange
  exact flat_of_isLocalizedModule_away
    ((e.restrictScalars R).toLinearMap ∘ₗ
      φ.range.toLocalizedQuotient' P (Submonoid.powers f) n) hflat

end Stacks.GenericFlatness

end
