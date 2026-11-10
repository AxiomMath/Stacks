module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingCategory
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingComplex
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.Modules
public import StacksFrontier.Topology.Sheaves.Glueing.Equivalence
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.BaseChange
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.LeftQuasiInverse
import all StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence.BaseChange

/-!
# Formal glueing of module categories: the formal glueing theorem and descent

This file completes the proof of the formal glueing theorem: for a flat map `R → S` inducing an
isomorphism `R / I ≅ S / IS`, the generic component of the counit of compatible sections is
surjective, so the canonical functor `Can` and the functor `H⁰` of compatible sections are
quasi-inverse equivalences of categories.

It also proves descent: an `S`-linear map to or from a module obtained by extension of scalars
descends to an `R`-linear map when its kernel and cokernel are `I`-power torsion, its kernel and
cokernel descending as well. Finally it registers Stacks 05EV.

## Main results

* `FormalGlueing.canonicalFunctor_sections_areQuasiInverse`: the formal glueing theorem — `Can`
  and `H⁰` are the forward and inverse functors of an equivalence.
* `FormalGlueing.exists_descent_of_idealPowerTorsion_kernel_cokernel`: both orientations of
  descent, together with compatibility with extension of scalars and the induced isomorphisms on
  kernels and cokernels.
* `TopCat.Sheaf.sheafEquivGlueData` (registered here for Stacks 05EV): sheaves on a space are
  identified with glueing data on an open cover.

## Implementation notes

For descent, extension and restriction of scalars are the canonical functors on `ModuleCat`, so
the source's tensor product is represented canonically and all compatibility statements are
equalities of module morphisms; the kernel and cokernel isomorphisms are stated after restriction
of scalars from `S` to `R`.

## References

* [Stacks Project, Tag 05ER](https://stacks.math.columbia.edu/tag/05ER)
* [Stacks Project, Tag 0ALK](https://stacks.math.columbia.edu/tag/0ALK)
* [Stacks Project, Tag 05EV](https://stacks.math.columbia.edu/tag/05EV)
-/

section

@[expose] public section

open CategoryTheory FormalGlueing TensorProduct

namespace FormalGlueing

universe u v w

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {r : ℕ} (f : Fin r → R)

attribute [local instance] FormalGlueing.restrictScalars_isScalarTower

private theorem smul_injective_of_isUnit {M : Type*} [AddCommGroup M] [Module R M] (a : R)
    (ha : IsUnit (algebraMap R (Module.End R M) a)) :
    Function.Injective (fun y : M ↦ a • y) :=
  ((Module.End.isUnit_iff _).mp ha).1

private theorem tensor_smul_injective_of_isUnit {M : Type*} [AddCommGroup M] [Module R M]
    (a : R) (ha : IsUnit (algebraMap R (Module.End R M) a)) :
    Function.Injective (fun y : S ⊗[R] M ↦ a • y) := by
  let e := LinearEquiv.ofBijective (algebraMap R (Module.End R M) a)
    ((Module.End.isUnit_iff _).mp ha)
  have he : ∀ y : S ⊗[R] M, LinearEquiv.lTensor S e y = a • y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul s m => simp [e, TensorProduct.tmul_smul]
    | add y z hy hz => simp only [map_add, hy, hz, smul_add]
  intro y z hyz
  apply (LinearEquiv.lTensor S e).injective
  simpa only [he] using hyz

private noncomputable def awayInvPowSMul (i : Fin r) (n : ℕ)
    (N : ModuleCat.{w} (Localization.Away (f i))) (y : restrictFromAway f i N) :
    restrictFromAway f i N :=
  (show N from
    (IsLocalization.Away.invSelf (f i) ^ n : Localization.Away (f i)) • (show N from y))

private theorem pow_smul_awayInvPowSMul (i : Fin r) (n : ℕ)
    (N : ModuleCat.{w} (Localization.Away (f i))) (y : restrictFromAway f i N) :
    (f i) ^ n • awayInvPowSMul f i n N y = y := by
  change (algebraMap R (Localization.Away (f i)) ((f i) ^ n)) •
    ((IsLocalization.Away.invSelf (f i) ^ n : Localization.Away (f i)) • (show N from y)) = y
  rw [smul_smul, map_pow, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, one_smul]

-- Elaborating the scalar restrictions of glueing data needs a larger budget.
private theorem mem_range_genericCounit_of_pow_smul
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (x : restrictFromTarget (R := R) S X.generic) (n : ℕ)
    (h : Fin r → FormalGlueing.sections S f X)
    (hh : ∀ i, (f i) ^ n • x = (h i).1.1)
    (hc : ∀ i j, (f j) ^ n • h i = (f i) ^ n • h j) :
    x ∈ LinearMap.range (FormalGlueing.sectionsGenericCounit S f X) := by
  let m : ∀ i, restrictFromAway f i (X.localPiece i) := fun i ↦
    awayInvPowSMul.{u, max u v w} f i n (X.localPiece i) ((h i).1.2 i)
  have hm : ∀ i, (f i) ^ n • m i = (h i).1.2 i := fun i ↦
    pow_smul_awayInvPowSMul.{u, max u v w} f i n (X.localPiece i) ((h i).1.2 i)
  have h1 : ∀ i, X.alpha i
      (LocalizedModule.mkLinearMap (Submonoid.powers (algebraMap R S (f i))) _ x) =
        (TensorProduct.mk R S _) 1 (m i) := by
    intro i
    apply tensor_smul_injective_of_isUnit S ((f i) ^ n)
      (FormalGlueing.localPiece_map_units S f X i ⟨(f i) ^ n, n, rfl⟩)
    dsimp only
    have := (h i).2.1 i
    rw [← hh i] at this
    change X.alpha i (LocalizedModule.mkLinearMap _ _
      ((algebraMap R S (f i ^ n)) • (show X.generic from x))) = _ at this
    rw [map_smul, map_smul, algebraMap_smul] at this
    rw [this, TensorProduct.mk_apply, TensorProduct.mk_apply, ← TensorProduct.tmul_smul, hm]
  have hloc : ∀ i j, (h i).1.2 j = (f i) ^ n • m j := by
    intro i j
    apply smul_injective_of_isUnit ((f j) ^ n)
      (FormalGlueing.localPiece_map_units S f X j ⟨(f j) ^ n, n, rfl⟩)
    have := congrArg (fun y : FormalGlueing.sections S f X ↦ y.1.2 j) (hc i j)
    dsimp only at this ⊢
    change (f j) ^ n • (h i).1.2 j = (f i) ^ n • (h j).1.2 j at this
    rw [this, ← hm j, smul_comm]
  have h2 : ∀ i j, X.alphaIJ i j
      (LocalizedModule.mkLinearMap (Cech.cechSub f {j}) _ (m i)) =
        LocalizedModule.mkLinearMap (Cech.cechSub f {i}) _ (m j) := by
    intro i j
    have := FormalGlueing.singletonLocalization_isLocalized f
      (restrictFromAway f j (X.localPiece j)) i
    apply smul_injective_of_isUnit ((f i) ^ n)
      (IsLocalizedModule.map_units (S := Submonoid.powers (f i))
        (LocalizedModule.mkLinearMap (Cech.cechSub f {i})
          (restrictFromAway f j (X.localPiece j))) ⟨(f i) ^ n, n, rfl⟩)
    dsimp only
    rw [← map_smul, ← map_smul, ← map_smul, hm, ← hloc]
    exact (h i).2.2 i j
  let t : FormalGlueing.sections S f X := ⟨(x, m), h1, h2⟩
  refine ⟨(1 : S) ⊗ₜ[R] t, ?_⟩
  rw [FormalGlueing.sectionsGenericCounit_tmul, one_smul]

/-- The generic counit, with target the underlying module over both `R` and `S`. -/
private noncomputable abbrev genericCounit
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    S ⊗[R] FormalGlueing.sections S f X →ₗ[S] restrictFromTarget (R := R) S X.generic :=
  FormalGlueing.sectionsGenericCounit S f X

private theorem exists_pow_smul_mem_range_genericCounit
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (x : restrictFromTarget (R := R) S X.generic) :
    ∃ n : ℕ, ∀ i, (f i) ^ n • x ∈
      (LinearMap.range (genericCounit S f X)).restrictScalars R := by
  choose n hn using fun i ↦ genericCounit_pow_smul_mem_range S f X i x
  refine ⟨∑ i, n i, fun i ↦ ?_⟩
  have hle : n i ≤ ∑ j, n j :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (n j)) (Finset.mem_univ i)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
  apply Submodule.smul_mem
  change algebraMap R S (f i ^ n i) • (show X.generic from x) ∈
    LinearMap.range (genericCounit S f X)
  rw [map_pow]
  exact hn i

private theorem torsion_of_generator_powers {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ} (a : Fin n → A)
    (h : ∀ x : M, ∀ i, ∃ k : ℕ, a i ^ k • x = 0) :
    IsIPowerTorsion A M (Ideal.span (Set.range a)) := by
  intro x
  let J : Ideal A := (LinearMap.toSpanSingleton A M x).ker
  have hJ : Ideal.span (Set.range a) ≤ J.radical := by
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    exact h x i
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ
    (Submodule.fg_span (Set.finite_range a))
  exact ⟨k + 1, Nat.succ_pos _, fun b hb ↦ hk (Ideal.pow_le_pow_right (Nat.le_succ k) hb)⟩

-- Elaborating the scalar restrictions of glueing data needs a larger budget.
private theorem genericCounit_surjective (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map))
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f)) :
    Function.Surjective (genericCounit S f X) := by
  let H := FormalGlueing.sections S f X
  let E' := restrictFromTarget (R := R) S X.generic
  let Ψ : S ⊗[R] H →ₗ[S] E' := genericCounit S f X
  let Q := E' ⧸ LinearMap.range Ψ
  have hQ : IsIPowerTorsion R Q (Ideal.span (Set.range f)) := by
    apply torsion_of_generator_powers f
    intro q i
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨n, hn⟩ := exists_pow_smul_mem_range_genericCounit S f X x
      refine ⟨n, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hn i
  have hflip :=
    ((IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective.{u, v,
    max u v w} R S (Ideal.span (Set.range f)) hflat).2 hq) Q hQ
  let μ : S ⊗[R] Q →ₗ[S] Q := LinearMap.liftBaseChange S LinearMap.id
  have hμ1 : ∀ q : Q, μ ((1 : S) ⊗ₜ[R] q) = q := fun q ↦ by
    simp [μ, LinearMap.liftBaseChange_tmul]
  have hone : Function.Bijective (fun q : Q ↦ (1 : S) ⊗ₜ[R] q) := by
    have : (fun q : Q ↦ (1 : S) ⊗ₜ[R] q) =
        TensorProduct.comm R Q S ∘ (TensorProduct.mk R Q S).flip 1 := by
      funext q; simp
    rw [this]
    exact (TensorProduct.comm R Q S).bijective.comp hflip
  have hμ : Function.Bijective μ := by
    refine ⟨fun y z hyz ↦ ?_, fun q ↦ ⟨_, hμ1 q⟩⟩
    obtain ⟨y, rfl⟩ := hone.2 y
    obtain ⟨z, rfl⟩ := hone.2 z
    simp only [hμ1] at hyz
    rw [hyz]
  let eμ := LinearEquiv.ofBijective μ hμ
  let P : E' →ₗ[S] S ⊗[R] Q := eμ.symm.toLinearMap.comp (LinearMap.range Ψ).mkQ
  have hP : ∀ x : E', P x = (1 : S) ⊗ₜ[R] (LinearMap.range Ψ).mkQ x := by
    intro x
    apply eμ.injective
    simp [P, eμ, hμ1]
    rfl
  have hPsurj : Function.Surjective P :=
    eμ.symm.surjective.comp (LinearMap.range Ψ).mkQ_surjective
  have hexact : Function.Exact Ψ P := by
    intro x
    simp only [P, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.map_eq_zero_iff, Set.mem_range]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  obtain ⟨E, _, _, a, b, c, ha, hab, hb, hca, hbc⟩ :=
    FormalGlueing.exists_shortExactSequence_lift_of_flat_baseChange.{u, v, max u v w, max u v w,
      max u v w} R S (Ideal.span (Set.range f)) (Submodule.fg_span (Set.finite_range f))
      hflat hq Q H hQ E' Ψ P (genericCounit_injective S f hflat hq X) hPsurj hexact
  have hc : ∀ e : E, c e ∈ LinearMap.range Ψ := by
    intro e
    obtain ⟨n, -, hn⟩ := hQ (b e)
    have hker : ∀ i, ∃ h : H, a h = (f i) ^ n • e := by
      intro i
      refine (hab _).1 ?_
      rw [map_smul]
      exact hn _ (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) n)
    choose h hh using hker
    have hca' : ∀ y : H, c (a y) = (y : _).1.1 := by
      intro y
      have := LinearMap.congr_fun hca y
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.restrictScalars_apply] at this
      rw [this]
      change FormalGlueing.sectionsGenericCounit S f X ((1 : S) ⊗ₜ[R] y) = _
      rw [FormalGlueing.sectionsGenericCounit_tmul, one_smul]
    apply mem_range_genericCounit_of_pow_smul S f X (c e) n h
    · intro i
      rw [← map_smul, ← hh i, hca']
    · intro i j
      apply ha
      rw [map_smul, map_smul, hh, hh, smul_smul, smul_smul, mul_comm]
  intro x
  obtain ⟨e, he⟩ := hb ((LinearMap.range Ψ).mkQ x)
  have h1 : P (c e) = P x := by
    have := LinearMap.congr_fun hbc e
    simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
      LinearMap.restrictScalars_apply] at this
    rw [← this, he, hP]
  have h2 : x - c e ∈ LinearMap.range Ψ := (hexact _).1 (by rw [map_sub, h1, sub_self])
  have h3 := Submodule.add_mem _ h2 (hc e)
  rw [sub_add_cancel] at h3
  exact LinearMap.mem_range.1 h3

/-- **Stacks 05ER.** For a flat ring map inducing an isomorphism modulo the ideal generated by
`f`, the canonical module glueing functor and compatible sections are quasi-inverse equivalences
of categories. -/
@[stacks 05ER]
public theorem canonicalFunctor_sections_areQuasiInverse
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap
        ((Ideal.span (Set.range f)).map (algebraMap R S))
        (algebraMap R S) Ideal.le_comap_map)) :
    let c := moduleGlueingConstruction.{u, v, w} S f
    letI := c.category
    ∃ e : ModuleCat.{max u v w} R ≌ ModuleGlueingDatum.{u, v, w} S f c.comparison,
      e.functor = c.canonical ∧ e.inverse = c.sections := by
  dsimp only [moduleGlueingConstruction]
  let := moduleGlueingCategory S f (localizationComparisons f)
  have : IsIso (canonicalSectionsUnit.{u, v, w} S f) :=
    FormalGlueing.canonicalSectionsUnit_isIso R S f hflat hq
  have : IsIso (FormalGlueing.sectionsCanonicalCounit.{u, v, w} S f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    exact FormalGlueing.glueingMap_isIso_of_bijective S f (FormalGlueing.sectionsCounit S f X)
      ⟨genericCounit_injective S f hflat hq X, genericCounit_surjective S f hflat hq X⟩
      (localCounit_bijective S f X)
  exact ⟨CategoryTheory.Equivalence.mk (canonicalFunctor S f)
    (compatibleSectionsFunctor S f (localizationComparisons f))
    (asIso (canonicalSectionsUnit S f))
    (asIso (FormalGlueing.sectionsCanonicalCounit.{u, v, w} S f)),
    rfl, rfl⟩

end FormalGlueing

end


end

/-! ### Descending module maps with ideal-power torsion kernel and cokernel -/

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct FormalGlueing

namespace FormalGlueing

universe u v w

private lemma torsion_map {A : Type*} [CommRing A] {M N : ModuleCat.{w} A}
    (I : Ideal A) (g : M ⟶ N) [IsIso g] (h : IsIPowerTorsion A M I) :
    IsIPowerTorsion A N I := by
  intro y
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso g).2 y
  obtain ⟨n, hn, hx⟩ := h x
  exact ⟨n, hn, fun a ha ↦ by rw [← map_smul, hx a ha, map_zero]⟩

/-- Some power of `a ∈ I` moves any element into the range when the cokernel is `I`-torsion. -/
private lemma pow_smul_mem_range_of_torsion {A : Type*} [CommRing A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    {I : Ideal A} {g : M →ₗ[A] N} (hC : IsIPowerTorsion A (N ⧸ g.range) I)
    {a : A} (ha : a ∈ I) (y : N) : ∃ n : ℕ, a ^ n • y ∈ g.range := by
  obtain ⟨n, hn, hy⟩ := hC (g.range.mkQ y)
  refine ⟨n, (Submodule.Quotient.mk_eq_zero g.range).1 ?_⟩
  simpa using hy (a ^ n) (Ideal.pow_mem_pow ha n)

private lemma localizedMap_bijective {A : Type*} [CommRing A]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (I : Ideal A) (g : M →ₗ[A] N)
    (hK : IsIPowerTorsion A g.ker I)
    (hC : IsIPowerTorsion A (N ⧸ g.range) I)
    (a : A) (ha : a ∈ I) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) g) := by
  let T := Submonoid.powers a
  constructor
  · apply IsLocalizedModule.injective_of_map_zero T (LocalizedModule.mkLinearMap T M)
    intro m hm
    change LocalizedModule.map T g (LocalizedModule.mk m 1) = 0 at hm
    rw [LocalizedModule.map_mk] at hm
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T
      (LocalizedModule.mkLinearMap T N)).1 hm
    have hg : g ((t : A) • m) = 0 := by simpa only [map_smul, Submonoid.smul_def] using ht
    obtain ⟨n, hn, h⟩ := hK ⟨(t : A) • m, hg⟩
    apply (IsLocalizedModule.eq_zero_iff T (LocalizedModule.mkLinearMap T M)).2
    refine ⟨⟨a ^ n, ⟨n, rfl⟩⟩ * t, ?_⟩
    have hh : a ^ n • ((t : A) • m) = 0 :=
      congrArg (fun z : g.ker ↦ (z : M)) (h (a ^ n) (Ideal.pow_mem_pow ha n))
    simpa only [Submonoid.smul_def, Submonoid.coe_mul, mul_smul] using hh
  · intro x
    induction x using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨n, y, hy⟩ := pow_smul_mem_range_of_torsion hC ha m
      let t : T := ⟨a ^ n, ⟨n, rfl⟩⟩
      refine ⟨LocalizedModule.mk y (t * s), ?_⟩
      rw [LocalizedModule.map_mk, hy]
      exact LocalizedModule.mk_cancel_common_left t s m

private lemma localizedMap_bijective_of_torsion {A : Type*} [CommRing A]
    {M N : ModuleCat.{w} A} (I : Ideal A) (g : M ⟶ N)
    (hK : IsIPowerTorsion A (↥(kernel g : ModuleCat A)) I)
    (hC : IsIPowerTorsion A (↥(cokernel g : ModuleCat A)) I)
    (a : A) (ha : a ∈ I) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers a) g.hom) :=
  localizedMap_bijective I g.hom
    (torsion_map I (ModuleCat.kernelIsoKer g).hom hK)
    (torsion_map I (ModuleCat.cokernelIsoRangeQuotient g).hom hC) a ha

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {r : ℕ} {f : Fin r → R}

/-- Replace the generic piece of a module glueing datum by a module mapping to it whose
localizations away from each `f i` are bijective, transporting the comparison isomorphisms along
those bijections. -/
noncomputable def pullGeneric
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (Y : ModuleCat.{max u v w} S) (g : Y ⟶ X.generic)
    (hg : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) g.hom)) :
    ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) where
  generic := Y
  localPiece := X.localPiece
  alpha i := (LinearEquiv.ofBijective
    ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) g.hom).restrictScalars S)
    (hg i)).trans (X.alpha i)
  alphaIJ := X.alphaIJ
  alpha_compatibility i j m := by
    change TensorProduct.map _ _ (TensorProduct.map _ _
      (X.alpha i (LocalizedModule.map _ g.hom (LocalizedModule.mk m 1)))) =
      TensorProduct.map _ _ (X.alpha j (LocalizedModule.map _ g.hom (LocalizedModule.mk m 1)))
    simp only [LocalizedModule.map_mk]
    exact X.alpha_compatibility i j (g m)
  cocycle := X.cocycle

/-- The map of module glueing data from `pullGeneric X Y g hg` to `X`: the map `g` on the generic
piece and the identity on every local piece. -/
public noncomputable def pullGenericMap
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (Y : ModuleCat.{max u v w} S) (g : Y ⟶ X.generic)
    (hg : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) g.hom)) :
    ModuleGlueingMap S f (localizationComparisons f) (pullGeneric X Y g hg) X where
  generic := g
  localPiece i := 𝟙 _
  alpha_compatibility i m := by
    change Y at m
    change X.alpha i (LocalizedModule.mk _ 1) =
      TensorProduct.map LinearMap.id LinearMap.id
        (X.alpha i (LocalizedModule.map _ g.hom (LocalizedModule.mk m 1)))
    simp only [LocalizedModule.map_mk, TensorProduct.map_id]
    rfl
  alphaIJ_compatibility i j m := by
    change X.alphaIJ i j (LocalizedModule.mk _ 1) =
      localizedMap f {i} LinearMap.id (X.alphaIJ i j (LocalizedModule.mk _ 1))
    rw [localizedMap_id]
    rfl

private lemma eq_of_comp_eq_of_torsion {A : Type*} [CommRing A]
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module A M] [Module A N] [Module A P]
    (I : Ideal A) (g : M →ₗ[A] N)
    (hC : IsIPowerTorsion A (N ⧸ g.range) I)
    (a : A) (ha : a ∈ I) (hinj : ∀ n : ℕ, Function.Injective (fun x : P ↦ a ^ n • x))
    (h k : N →ₗ[A] P) (he : h.comp g = k.comp g) : h = k := by
  ext y
  obtain ⟨n, x, hx⟩ := pow_smul_mem_range_of_torsion hC ha y
  apply hinj n
  change a ^ n • h y = a ^ n • k y
  rw [← map_smul, ← map_smul, ← hx]
  exact LinearMap.congr_fun he x

private noncomputable def pushGeneric
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (Y : ModuleCat.{max u v w} S) (g : X.generic ⟶ Y)
    (I : Ideal R) (hf : ∀ i, f i ∈ I)
    (hC : IsIPowerTorsion S (↥(cokernel g : ModuleCat S))
      (I.map (algebraMap R S)))
    (hg : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) g.hom)) :
    ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) := by
  let e i := LinearEquiv.ofBijective
    ((LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) g.hom).restrictScalars S)
    (hg i)
  let α i := (e i).symm.trans (X.alpha i)
  have he i m : α i (LocalizedModule.mkLinearMap _ _ (g m)) =
      X.alpha i (LocalizedModule.mkLinearMap _ _ m) := by
    change X.alpha i ((e i).symm (LocalizedModule.mk (g m) 1)) = _
    rw [← LocalizedModule.map_mk]
    exact congrArg (X.alpha i) ((e i).symm_apply_apply _)
  refine { generic := Y
           localPiece := X.localPiece
           alpha := α
           alphaIJ := X.alphaIJ
           cocycle := X.cocycle
           alpha_compatibility := ?_ }
  intro i j m
  let L := restrictFromAway f j (X.localPiece j)
  let P := TensorProduct R S (Cech.cechMod f L {i})
  let h : Y →ₗ[S] P :=
    (AlgebraTensorModule.lTensor S S (X.alphaIJ i j).toLinearMap).comp
      ((AlgebraTensorModule.lTensor S S (LocalizedModule.mkLinearMap (Cech.cechSub f {j}) _)).comp
        ((α i).toLinearMap.comp (LocalizedModule.mkLinearMap _ _)))
  let k : Y →ₗ[S] P :=
    (AlgebraTensorModule.lTensor S S (LocalizedModule.mkLinearMap (Cech.cechSub f {i}) _)).comp
      ((α j).toLinearMap.comp (LocalizedModule.mkLinearMap _ _))
  suffices h = k from LinearMap.congr_fun this m
  apply eq_of_comp_eq_of_torsion (I.map (algebraMap R S)) g.hom
    (torsion_map _ (ModuleCat.cokernelIsoRangeQuotient g).hom hC)
    (algebraMap R S (f i)) (Ideal.mem_map_of_mem _ (hf i))
  · intro n x y hxy
    have H := isLocalized_lTensor S (Cech.cechSub f {i})
      (LocalizedModule.mkLinearMap (Cech.cechSub f {i}) L)
    let := H
    have hu := H.map_units
      ⟨f i ^ n, by
        simp only [Cech.cechSub, Finset.prod_singleton]
        exact ⟨n, rfl⟩⟩
    rw [Module.End.isUnit_iff] at hu
    apply hu.1
    change f i ^ n • x = f i ^ n • y
    simpa only [← map_pow, IsScalarTower.algebraMap_smul S] using hxy
  · apply LinearMap.ext
    intro x
    dsimp only [h, k, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [he, he]
    exact X.alpha_compatibility i j x

private noncomputable def pushGenericMap
    (X : ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f))
    (Y : ModuleCat.{max u v w} S) (g : X.generic ⟶ Y)
    (I : Ideal R) (hf : ∀ i, f i ∈ I)
    (hC : IsIPowerTorsion S (↥(cokernel g : ModuleCat S))
      (I.map (algebraMap R S)))
    (hg : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap R S (f i))) g.hom)) :
    ModuleGlueingMap S f (localizationComparisons f) X (pushGeneric X Y g I hf hC hg) where
  generic := g
  localPiece i := 𝟙 _
  alpha_compatibility i m := by
    change X.generic at m
    change X.alpha i ((LinearEquiv.ofBijective _ (hg i)).symm
      (LocalizedModule.mk (g m) 1)) = TensorProduct.map LinearMap.id LinearMap.id
        (X.alpha i (LocalizedModule.mk m 1))
    simp only [TensorProduct.map_id, LinearMap.id_apply]
    rw [← LocalizedModule.map_mk]
    exact congrArg (X.alpha i) ((LinearEquiv.ofBijective _ (hg i)).symm_apply_apply _)
  alphaIJ_compatibility i j m := by
    change X.alphaIJ i j (LocalizedModule.mk _ 1) =
      localizedMap f {i} LinearMap.id (X.alphaIJ i j (LocalizedModule.mk _ 1))
    rw [localizedMap_id]
    rfl

private lemma torsion_kernel_cokernel_of_localized_bijective
    {A : Type*} [CommRing A] {M N : ModuleCat.{w} A}
    {n : ℕ} (a : Fin n → A) (g : M ⟶ N)
    (hg : ∀ i, Function.Bijective (LocalizedModule.map (Submonoid.powers (a i)) g.hom)) :
    IsIPowerTorsion A (↥(kernel g : ModuleCat A)) (Ideal.span (Set.range a)) ∧
    IsIPowerTorsion A (↥(cokernel g : ModuleCat A)) (Ideal.span (Set.range a)) := by
  have hK : IsIPowerTorsion A g.hom.ker (Ideal.span (Set.range a)) := by
    apply torsion_of_generator_powers a
    intro x i
    have hx : LocalizedModule.mkLinearMap (Submonoid.powers (a i)) M x = 0 := by
      apply (hg i).1
      change LocalizedModule.map _ g.hom (LocalizedModule.mk x.val 1) = _
      rw [LocalizedModule.map_mk, x.property, LocalizedModule.zero_mk, map_zero]
    obtain ⟨⟨b, ⟨k, rfl⟩⟩, hb⟩ :=
      (IsLocalizedModule.eq_zero_iff (Submonoid.powers (a i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (a i)) M)).1 hx
    refine ⟨k, Subtype.ext ?_⟩
    exact hb
  have hC : IsIPowerTorsion A (N ⧸ g.hom.range) (Ideal.span (Set.range a)) := by
    apply torsion_of_generator_powers a
    intro x i
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨z, hz⟩ := (hg i).2 (LocalizedModule.mk y 1)
      induction z using LocalizedModule.induction_on with
      | h m s =>
        rw [LocalizedModule.map_mk, LocalizedModule.mk_eq] at hz
        obtain ⟨t, ht⟩ := hz
        obtain ⟨k, hk⟩ := (t * s).property
        refine ⟨k, ?_⟩
        have hm : a i ^ k • y ∈ g.hom.range := by
          refine ⟨(t : A) • m, ?_⟩
          rw [map_smul]
          simpa only [Submonoid.smul_def, OneMemClass.coe_one, one_smul,
            ← mul_smul, ← Submonoid.coe_mul, ← hk] using ht
        exact (Submodule.Quotient.mk_eq_zero g.hom.range).2 hm
  exact ⟨torsion_map _ (ModuleCat.kernelIsoKer g).inv hK,
    torsion_map _ (ModuleCat.cokernelIsoRangeQuotient g).inv hC⟩

private noncomputable def genericFunctor (S : Type v) [CommRing S] [Algebra R S]
    (f : Fin r → R) :
    letI := moduleGlueingCategory S f (localizationComparisons f)
    ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) ⥤ ModuleCat.{max u v w} S := by
  letI := moduleGlueingCategory S f (localizationComparisons f)
  exact { obj := fun X ↦ X.generic
          map := fun g ↦ g.generic }

private noncomputable def localFunctor (S : Type v) [CommRing S] [Algebra R S]
    (f : Fin r → R) (i : Fin r) :
    letI := moduleGlueingCategory S f (localizationComparisons f)
    ModuleGlueingDatum.{u, v, w} S f (localizationComparisons f) ⥤
      ModuleCat.{max u v w} (Localization.Away (f i)) := by
  letI := moduleGlueingCategory S f (localizationComparisons f)
  exact { obj := fun X ↦ X.localPiece i
          map := fun g ↦ g.localPiece i }

omit [Algebra R S] in
private lemma extendScalars_preservesHomology (a : R →+* S)
    (hflat : let := a.toAlgebra; Module.Flat R S) :
    letI := (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} a).isLeftAdjoint
    (ModuleCat.extendScalars.{u, v, max u v w} a).PreservesHomology := by
  let := (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} a).isLeftAdjoint
  let := a.toAlgebra
  let := hflat
  apply Functor.preservesHomology_of_map_exact
  intro C hC
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  exact Module.Flat.lTensor_exact S hC

omit [Algebra R S] in
private noncomputable def torsionUnitIso (a : R →+* S) (I : Ideal R)
    (hflat : letI := a.toAlgebra; Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap (I.map a) a Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} R) (hM : IsIPowerTorsion R M I) :
    M ≅ (ModuleCat.restrictScalars a).obj ((ModuleCat.extendScalars a).obj M) := by
  letI := a.toAlgebra
  let η := (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} a).unit.app M
  have h := (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
    R S I hflat).2 hq M hM
  have hη : Function.Bijective η := by
    have H := (TensorProduct.comm R M S).bijective.comp h
    exact H
  exact (LinearEquiv.ofBijective η.hom hη).toModuleIso

omit [Algebra R S] in
private lemma kernel_cokernel_iso_of_localized_bijective
    (a : R →+* S) (f : Fin r → R)
    (hflat : let := a.toAlgebra; Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map a) a Ideal.le_comap_map))
    {M N : ModuleCat.{max u v w} R} (ψ : M ⟶ N)
    (hψ : ∀ i, Function.Bijective (LocalizedModule.map (Submonoid.powers (f i)) ψ.hom))
    {P Q : ModuleCat.{max u v w} S} (φ : P ⟶ Q)
    (eM : (ModuleCat.extendScalars a).obj M ≅ P)
    (eN : (ModuleCat.extendScalars a).obj N ≅ Q)
    (he : (ModuleCat.extendScalars a).map ψ ≫ eN.hom = eM.hom ≫ φ) :
    Nonempty ((ModuleCat.restrictScalars a).obj (kernel φ) ≅ kernel ψ) ∧
    Nonempty ((ModuleCat.restrictScalars a).obj (cokernel φ) ≅ cokernel ψ) := by
  let E := ModuleCat.extendScalars.{u, v, max u v w} a
  let U := ModuleCat.restrictScalars.{max u v w} a
  let := (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} a).isLeftAdjoint
  have : E.PreservesHomology := extendScalars_preservesHomology a hflat
  let := Functor.PreservesHomology.preservesKernel E ψ
  let := Functor.PreservesHomology.preservesCokernel E ψ
  obtain ⟨hK, hC⟩ := torsion_kernel_cokernel_of_localized_bijective f ψ hψ
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · exact (U.mapIso (kernel.mapIso (E.map ψ) φ eM eN he)).symm ≪≫
      U.mapIso (PreservesKernel.iso E ψ).symm ≪≫
      (torsionUnitIso a _ hflat hq (kernel ψ) hK).symm
  · exact (U.mapIso (cokernel.mapIso (E.map ψ) φ eM eN he)).symm ≪≫
      U.mapIso (PreservesCokernel.iso E ψ).symm ≪≫
      (torsionUnitIso a _ hflat hq (cokernel ψ) hC).symm

/-- Under the formal glueing hypotheses, the canonical functor is an equivalence. -/
private lemma isEquivalence_canonicalFunctor {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (a : A →+* B) {n : ℕ} (f : Fin n → A)
    (hflat : let := a.toAlgebra; Module.Flat A B)
    (hq : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map a) a Ideal.le_comap_map)) :
    letI := a.toAlgebra
    letI := moduleGlueingCategory B f (localizationComparisons f)
    (canonicalFunctor.{u, v, w} B f).IsEquivalence := by
  let := a.toAlgebra
  let := moduleGlueingCategory B f (localizationComparisons f)
  obtain ⟨eqv, hfun, _⟩ := FormalGlueing.canonicalFunctor_sections_areQuasiInverse.{u, v, w}
    A B f hflat hq
  change ModuleCat.{max u v w} A ≌
    ModuleGlueingDatum.{u, v, w} B f (localizationComparisons f) at eqv
  change eqv.functor = canonicalFunctor.{u, v, w} B f at hfun
  exact hfun ▸ (inferInstance : eqv.functor.IsEquivalence)

omit [Algebra R S] in
private lemma descend_incoming (a : R →+* S) (f : Fin r → R)
    (hflat : let := a.toAlgebra; Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map a) a Ideal.le_comap_map))
    (N : ModuleCat.{max u v w} R) (M' : ModuleCat.{max u v w} S)
    (φ : M' ⟶ (ModuleCat.extendScalars a).obj N)
    (hK : IsIPowerTorsion S (↥(kernel φ : ModuleCat S))
      ((Ideal.span (Set.range f)).map a))
    (hC : IsIPowerTorsion S (↥(cokernel φ : ModuleCat S))
      ((Ideal.span (Set.range f)).map a)) :
    ∃ (M : ModuleCat.{max u v w} R) (ψ : M ⟶ N)
      (e : (ModuleCat.extendScalars a).obj M ≅ M'),
      e.hom ≫ φ = (ModuleCat.extendScalars a).map ψ ∧
      ∀ i, Function.Bijective (LocalizedModule.map (Submonoid.powers (f i)) ψ.hom) := by
  let := a.toAlgebra
  let := moduleGlueingCategory S f (localizationComparisons f)
  let F := canonicalFunctor.{u, v, w} S f
  have : F.IsEquivalence := isEquivalence_canonicalFunctor.{u, v, w} a f hflat hq
  have hloc i := localizedMap_bijective_of_torsion _ φ hK hC (a (f i))
    (Ideal.mem_map_of_mem a (Ideal.subset_span (Set.mem_range_self i)))
  let X := pullGeneric (F.obj N) M' φ hloc
  let M := F.objPreimage X
  let e := F.objObjPreimageIso X
  let g : X ⟶ F.obj N := pullGenericMap (F.obj N) M' φ hloc
  let ψ := F.preimage (e.hom ≫ g)
  have hψ : F.map ψ = e.hom ≫ g := F.map_preimage _
  refine ⟨M, ψ, (genericFunctor S f).mapIso e, ?_, ?_⟩
  · exact (congrArg (fun k ↦ k.generic) hψ).symm
  · intro i
    have hi : canonicalLocalMap f ψ i = ((localFunctor S f i).mapIso e).hom := by
      have hh := congrArg (fun k ↦ k.localPiece i) hψ
      change canonicalLocalMap f ψ i = e.hom.localPiece i ≫ 𝟙 _ at hh
      change canonicalLocalMap f ψ i = e.hom.localPiece i
      exact hh.trans (Category.comp_id _)
    have hb := ConcreteCategory.bijective_of_isIso ((localFunctor S f i).mapIso e).hom
    rw [← hi] at hb
    exact hb

omit [Algebra R S] in
private lemma descend_outgoing (a : R →+* S) (f : Fin r → R)
    (hflat : let := a.toAlgebra; Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map a) a Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} R) (N' : ModuleCat.{max u v w} S)
    (φ : (ModuleCat.extendScalars a).obj M ⟶ N')
    (hK : IsIPowerTorsion S (↥(kernel φ : ModuleCat S))
      ((Ideal.span (Set.range f)).map a))
    (hC : IsIPowerTorsion S (↥(cokernel φ : ModuleCat S))
      ((Ideal.span (Set.range f)).map a)) :
    ∃ (N : ModuleCat.{max u v w} R) (ψ : M ⟶ N)
      (e : (ModuleCat.extendScalars a).obj N ≅ N'),
      (ModuleCat.extendScalars a).map ψ ≫ e.hom = φ ∧
      ∀ i, Function.Bijective (LocalizedModule.map (Submonoid.powers (f i)) ψ.hom) := by
  let := a.toAlgebra
  let := moduleGlueingCategory S f (localizationComparisons f)
  let F := canonicalFunctor.{u, v, w} S f
  have : F.IsEquivalence := isEquivalence_canonicalFunctor.{u, v, w} a f hflat hq
  have hf i : f i ∈ Ideal.span (Set.range f) := Ideal.subset_span (Set.mem_range_self i)
  have hloc i := localizedMap_bijective_of_torsion _ φ hK hC (a (f i))
    (Ideal.mem_map_of_mem a (hf i))
  let X := pushGeneric (F.obj M) N' φ _ hf hC hloc
  let N := F.objPreimage X
  let e := F.objObjPreimageIso X
  let g : F.obj M ⟶ X := pushGenericMap (F.obj M) N' φ _ hf hC hloc
  let ψ := F.preimage (g ≫ e.inv)
  have hψ : F.map ψ = g ≫ e.inv := F.map_preimage _
  let eS : (ModuleCat.extendScalars a).obj N ≅ N' := (genericFunctor S f).mapIso e
  refine ⟨N, ψ, eS, ?_, ?_⟩
  · have he : (ModuleCat.extendScalars a).map ψ = φ ≫ eS.inv :=
      congrArg (fun k ↦ k.generic) hψ
    rw [he, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro i
    have hi : canonicalLocalMap f ψ i = ((localFunctor S f i).mapIso e).inv := by
      have hh := congrArg (fun k ↦ k.localPiece i) hψ
      change canonicalLocalMap f ψ i = 𝟙 _ ≫ e.inv.localPiece i at hh
      change canonicalLocalMap f ψ i = e.inv.localPiece i
      exact hh.trans (Category.id_comp _)
    have hb := ConcreteCategory.bijective_of_isIso ((localFunctor S f i).mapIso e).inv
    rw [← hi] at hb
    exact hb

/-- **Stacks 0ALK.** A map to or from an extended module whose kernel and cokernel are
ideal-power torsion descends at the level of its source or target module, with the
given map recovered by extension of scalars and with the same kernel and cokernel after
restriction of scalars. -/
@[stacks 0ALK]
public theorem exists_descent_of_idealPowerTorsion_kernel_cokernel
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    let E := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)
    let U := ModuleCat.restrictScalars.{max u v w} (algebraMap R S)
    (∀ (N : ModuleCat.{max u v w} R) (M' : ModuleCat.{max u v w} S)
      (φ : M' ⟶ E.obj N),
      IsIPowerTorsion S
        (↥(kernel φ : ModuleCat.{max u v w} S)) (I.map (algebraMap R S)) →
      IsIPowerTorsion S
        (↥(cokernel φ : ModuleCat.{max u v w} S)) (I.map (algebraMap R S)) →
      ∃ (M : ModuleCat.{max u v w} R) (ψ : M ⟶ N) (e : E.obj M ≅ M')
          (_eKer : U.obj (kernel φ) ≅ kernel ψ)
          (_eCoker : U.obj (cokernel φ) ≅ cokernel ψ),
        e.hom ≫ φ = E.map ψ) ∧
    (∀ (M : ModuleCat.{max u v w} R) (N' : ModuleCat.{max u v w} S)
      (φ : E.obj M ⟶ N'),
      IsIPowerTorsion S
        (↥(kernel φ : ModuleCat.{max u v w} S)) (I.map (algebraMap R S)) →
      IsIPowerTorsion S
        (↥(cokernel φ : ModuleCat.{max u v w} S)) (I.map (algebraMap R S)) →
      ∃ (N : ModuleCat.{max u v w} R) (ψ : M ⟶ N) (e : E.obj N ≅ N')
          (_eKer : U.obj (kernel φ) ≅ kernel ψ)
          (_eCoker : U.obj (cokernel φ) ≅ cokernel ψ),
        E.map ψ ≫ e.hom = φ) := by
  dsimp only
  obtain ⟨r, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  change Ideal.span (Set.range f) = I at hf
  subst I
  let a := algebraMap R S
  have hflat' : let := a.toAlgebra; Module.Flat R S :=
    (show a.toAlgebra = ‹Algebra R S› from toAlgebra_algebraMap).symm ▸ hflat
  constructor
  · intro N M' φ hK hC
    obtain ⟨M, ψ, e, he, hψ⟩ := descend_incoming a f hflat' hq N M' φ hK hC
    obtain ⟨⟨eK⟩, ⟨eC⟩⟩ := kernel_cokernel_iso_of_localized_bijective
      a f hflat' hq ψ hψ φ e (Iso.refl _) (by
        change _ ≫ 𝟙 _ = _
        rw [Category.comp_id]
        exact he.symm)
    exact ⟨M, ψ, e, eK, eC, he⟩
  · intro M N' φ hK hC
    obtain ⟨N, ψ, e, he, hψ⟩ := descend_outgoing a f hflat' hq M N' φ hK hC
    obtain ⟨⟨eK⟩, ⟨eC⟩⟩ := kernel_cokernel_iso_of_localized_bijective
      a f hflat' hq ψ hψ φ (Iso.refl _) e (by
        change _ = 𝟙 _ ≫ _
        rw [Category.id_comp]
        exact he)
    exact ⟨N, ψ, e, eK, eC, he⟩

end FormalGlueing

end

end
/-! ### Sheaves from a tubular neighbourhood and its complement -/

/- Stacks 05EV is the remark that a sheaf on a space is determined by sheaves on an open cover
together with compatible identifications over the overlaps, the motivating cover being a tubular
neighbourhood of a closed submanifold and its complement. That content is the general
sheaf-glueing equivalence `TopCat.Sheaf.sheafEquivGlueData`, stated for an arbitrary open cover
of an arbitrary topological space, so the tag is registered against that declaration. -/
add_to_stacks 05EV TopCat.Sheaf.sheafEquivGlueData
