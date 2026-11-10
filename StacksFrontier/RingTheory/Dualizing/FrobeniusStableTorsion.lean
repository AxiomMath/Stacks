module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.RingTheory.MvPowerSeries.LeibnizTorsionModule
public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FrobeniusAction.Kunz
public import StacksFrontier.Algebra.Module.Essential
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Algebra.Module.InjectiveHull.Injective
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.NormalizedZeroDimensional
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
public import StacksFrontier.RingTheory.MvPowerSeries.LeibnizTorsionModule

/-!
# Frobenius-stable torsion modules over a regular local ring

Let `(A, 𝔪, k)` be a regular local ring in which a prime number `p` vanishes, and let
`F : A → A`, `a ↦ a ^ p` be its Frobenius endomorphism. An `𝔪`-power torsion `A`-module which
is unchanged by extension of scalars along `F` is a direct sum of copies of an injective hull
of `k`.

## Main results

* `Dualizing.isIPowerTorsion_frobeniusStable_exists_equiv_directSum_injectiveHull`
  ([stacks 0EC3]): the direct sum decomposition of a Frobenius-stable `𝔪`-power torsion module.

## Implementation notes

The twisted tensor product `M ⊗_{A, F} A` of the source is `ModuleCat.extendScalars F`, and the
source's phrase "isomorphic to a direct sum of copies of `E`" is an existentially quantified
index type together with a linear equivalence onto `⨁ _ : J, E`. An injective hull of the
residue field is represented by an arbitrary monomorphism satisfying `Module.IsInjectiveHull`,
so the statement does not depend on a chosen hull.

Injectivity of the comparison map uses that the socle `M[𝔪]` meets every nonzero cyclic
submodule, which is essentiality of the hull. Surjectivity replaces the source's divisibility
argument: Frobenius is flat by Kunz's theorem, so the submodule of `M` killed by the image of
`𝔪` along `F ^ n` is free over the corresponding Artinian quotient `A / I`. That quotient is a
zero-dimensional Gorenstein local ring, hence self-injective, so the socle-preserving embedding
splits on each step of the filtration and the comparison map is onto.

## References

* [Huneke--Sharp, *Bass numbers of local cohomology modules*][Huneke-Sharp]
* [Lyubeznik, *F-modules: applications to local cohomology and D-modules in characteristic
  p > 0*][Lyubeznik2]
* [Stacks Project, Tag 0EC3](https://stacks.math.columbia.edu/tag/0EC3)
-/

@[expose] public section

open CategoryTheory
open scoped DirectSum
open scoped TensorProduct

universe u v

namespace Dualizing

private lemma exists_nonzero_socle_multiple
    (A : Type u) [CommRing A] (M : Type (max u v))
    [AddCommGroup M] [Module A M] (m : Ideal A)
    (hM : IsIPowerTorsion A M m) {z : M} (hz : z ≠ 0) :
    ∃ a : A, a • z ∈ Submodule.torsionBySet A M (m : Set A) ∧ a • z ≠ 0 := by
  classical
  let P : ℕ → Prop := fun n => ∀ a : A, a ∈ m ^ n → a • z = 0
  have hex : ∃ n, P n := by
    obtain ⟨n, hn, hkill⟩ := hM z
    exact ⟨n, hkill⟩
  let n := Nat.find hex
  have hn : P n := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    exact hz (by simpa using hn 1 (by simp [hn0]))
  have hprev : ¬ P (n - 1) := by
    intro h
    have hmin := Nat.find_min' hex h
    omega
  change ¬ (∀ a : A, a ∈ m ^ (n - 1) → a • z = 0) at hprev
  push Not at hprev
  obtain ⟨a, ha, haz⟩ := hprev
  refine ⟨a, ?_, haz⟩
  rw [Submodule.mem_torsionBySet_iff]
  intro b
  have hab : a * b ∈ m ^ n := by
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    exact Ideal.mul_mem_mul ha b.property
  simpa [smul_smul, mul_comm] using hn (a * b) hab

private lemma dim_quotient_eq_zero_of_radical_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {I : Ideal R}
    (hI : I.radical = IsLocalRing.maximalIdeal R) :
    ringKrullDim (R ⧸ I) = 0 := by
  have hproper : I ≠ ⊤ := by
    intro h
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (by simpa [h, Ideal.radical_top] using hI.symm)
  have hnontrivial : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  apply (ringKrullDimZero_iff_ringKrullDim_eq_zero (R := R ⧸ I)).mp
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro J hJ
  have hmaxle : IsLocalRing.maximalIdeal R ≤ J := by
    rw [← hI]
    exact hJ.1.1.radical_le_iff.mpr hJ.1.2
  have hJmax : IsLocalRing.maximalIdeal R = J :=
    (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ.1.1.ne_top hmaxle
  rw [← hJmax]
  exact IsLocalRing.maximalIdeal.isMaximal R

private lemma frobeniusOfPrime_flat_of_isRegularLocalRing
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0) :
    RingHom.Flat (frobeniusOfPrime p hp hchar) :=
  (isRegularRing_iff_frobeniusOfPrime_flat p hp hchar).mp
    (((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp
      (inferInstance : IsRegularLocalRing A))

private lemma frobenius_iterate_flat
    (A : Type u) [CommRing A] (F : A →+* A) (hF : RingHom.Flat F) :
    ∀ n : ℕ, RingHom.Flat (F ^ n) := by
  intro n
  induction n with
  | zero =>
      convert RingHom.Flat.id A using 1
      ext x
      rfl
  | succ n ih =>
      rw [pow_succ, RingHom.mul_def]
      exact RingHom.Flat.comp hF ih

private def multiplicationFamily
    (A : Type*) [CommRing A] (M : Type*) [AddCommGroup M] [Module A M]
    {ι : Type*} (x : ι → A) : M →ₗ[A] (ι → M) where
  toFun m i := x i • m
  map_add' _ _ := funext fun _ => smul_add _ _ _
  map_smul' a m := funext fun i => smul_comm (x i) a m

/-- The kernel of `m ↦ (a i • m)ᵢ` is the torsion submodule of the ideal generated by the `a i`. -/
private lemma ker_multiplicationFamily
    {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    {ι : Type*} (a : ι → R) :
    LinearMap.ker (multiplicationFamily R M a) =
      Submodule.torsionBySet R M (Ideal.span (Set.range a) : Set R) := by
  rw [← Submodule.torsionBySet_eq_torsionBySet_span]
  ext x
  simp [multiplicationFamily, LinearMap.mem_ker, Submodule.mem_torsionBySet_iff, funext_iff]

private lemma piRight_baseChange_mulFamily
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M]
    [IsScalarTower R S S] {ι : Type*}
    (x : ι → R) (y : ι → S)
    (hxy : ∀ i, algebraMap R S (x i) = y i)
    (z : S ⊗[R] M) (i : ι) :
    TensorProduct.piRightHom R S S (fun _ : ι => M)
      ((multiplicationFamily R M x).baseChange S z) i = y i • z := by
  classical
  induction z using TensorProduct.inductionOn with
  | tmul a m =>
      change (TensorProduct.piRightHom R S S (fun _ : ι => M)
        (a ⊗ₜ[R] multiplicationFamily R M x m)) i = y i • (a ⊗ₜ[R] m)
      rw [TensorProduct.piRightHom_tmul]
      change a ⊗ₜ[R] (x i • m) = y i • (a ⊗ₜ[R] m)
      rw [TensorProduct.tmul_smul]
      apply congrArg (fun c : S => c ⊗ₜ[R] m)
      calc
        x i • a = algebraMap R S (x i) * a := by simp [Algebra.smul_def]
        _ = y i * a := by rw [hxy]
        _ = y i • a := by simp
  | add z w hz hw => simp [hz, hw]

private noncomputable def extendScalarsPowIso
    (A : Type u) [CommRing A] (F : A →+* A)
    (M : Type (max u v)) [AddCommGroup M] [Module A M]
    (hF : (ModuleCat.extendScalars F).obj (ModuleCat.of A M) ≅ ModuleCat.of A M) :
    ∀ n : ℕ,
      (ModuleCat.extendScalars (F ^ n)).obj (ModuleCat.of A M) ≅ ModuleCat.of A M := by
  intro n
  induction n with
  | zero =>
      simpa only [pow_zero, RingHom.one_def, Functor.id_obj] using
        (ModuleCat.extendScalarsId A).app (ModuleCat.of A M)
  | succ n ih =>
      rw [pow_succ, RingHom.mul_def]
      exact (ModuleCat.extendScalarsComp F (F ^ n)).app (ModuleCat.of A M) |>.trans
        (by
          simpa only [Functor.comp_obj] using
            (((ModuleCat.extendScalars (F ^ n)).mapIso hF).trans ih))

private theorem essentialMono_nonzero_multiple
    (R M E : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup E] [Module R E]
    (i : ModuleCat.of R M ⟶ ModuleCat.of R E) [Mono i]
    (hi : Module.IsEssentialMono i) :
    ∀ x : E, x ≠ 0 → ∃ r : R, r • x ∈ LinearMap.range i.hom ∧ r • x ≠ 0 := by
  intro x hx
  let e := ModuleCat.subobjectModule (ModuleCat.of R E)
  have hImage : e (Subobject.mk i) = LinearMap.range i.hom := by
    change LinearMap.range (Subobject.mk i).arrow.hom = LinearMap.range i.hom
    rw [← ModuleCat.hom_ext_iff.mp (Subobject.underlyingIso_hom_comp_eq_mk i), ModuleCat.hom_comp]
    exact LinearEquiv.range_comp (Subobject.underlyingIso i).toLinearEquiv i.hom
  let P : Submodule R E := R ∙ x
  have hP : P ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  have hPcat : e.symm P ≠ ⊥ := fun hz => hP <| by
    simpa only [e.apply_symm_apply, e.map_bot] using congrArg e hz
  have hmeet' : P ⊓ LinearMap.range i.hom ≠ ⊥ := fun hz => hi (e.symm P) hPcat <|
    e.injective <| by rwa [OrderIso.map_inf, e.apply_symm_apply, hImage, e.map_bot]
  obtain ⟨y, hy⟩ := Submodule.nonzero_mem_of_bot_lt ((bot_lt_iff_ne_bot).2 hmeet')
  have hyP : y.1 ∈ P := (Submodule.mem_inf.mp y.2).1
  have hyI : y.1 ∈ LinearMap.range i.hom := (Submodule.mem_inf.mp y.2).2
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hyP
  have hy0 : y.1 ≠ 0 := fun hz => hy (Subtype.ext hz)
  exact ⟨r, by simpa [hr] using hyI, by simpa [hr] using hy0⟩

private lemma socle_mem_range_injectiveHull
    (A E : Type u) [CommRing A] [IsLocalRing A] [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsEssentialMono i) {z : E}
    (hz : z ∈ Submodule.torsionBySet A E (IsLocalRing.maximalIdeal A : Set A)) :
    z ∈ LinearMap.range i.hom := by
  by_cases hz0 : z = 0
  · simp [hz0]
  obtain ⟨a, ha, haz⟩ := essentialMono_nonzero_multiple A _ E i hi z hz0
  have hau : IsUnit a := IsLocalRing.notMem_maximalIdeal.mp (fun h =>
    haz ((Submodule.mem_torsionBySet_iff _ _).mp hz ⟨a, h⟩))
  obtain ⟨a, rfl⟩ := hau
  simpa using (LinearMap.range i.hom).smul_mem (↑a⁻¹ : A) ha

private lemma injective_finsupp
    (R E : Type u) [CommRing R] [IsNoetherianRing R] [AddCommGroup E]
    [Module R E] [Module.Injective R E]
    (J : Type v) : Module.Injective R (J →₀ E) := by
  classical
  let : Module.Injective R (ULift.{max u v} E) :=
    Module.ulift_injective_of_injective R inferInstance
  let : Module.Injective R (⨁ _ : J, ULift.{max u v} E) :=
    Module.directSum_injective R (fun _ : J => ULift.{max u v} E)
  exact Module.Injective.of_ringEquiv (RingEquiv.refl R)
    ((finsuppLEquivDirectSum R (ULift.{max u v} E) J).symm ≪≫ₗ
      Finsupp.mapRange.linearEquiv (ULift.moduleEquiv (R := R)))

/-- The socle of a module over a local ring is free over the residue field. -/
private lemma exists_linearEquiv_torsion_finsupp
    {R : Type u} [CommRing R] [IsLocalRing R] (M : Type (max u v)) [AddCommGroup M]
    [Module R M] :
    ∃ J : Type (max u v), Nonempty
      (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R : Set R)
        ≃ₗ[R ⧸ IsLocalRing.maximalIdeal R] (J →₀ R ⧸ IsLocalRing.maximalIdeal R)) := by
  let m := IsLocalRing.maximalIdeal R
  let S := Submodule.torsionBySet R M (m : Set R)
  let k := R ⧸ m
  let : Field k := IsLocalRing.ResidueField.field R
  let moduleKS : Module k S := by
    dsimp [k, S, m]
    infer_instance
  let : Module k S := moduleKS
  let : Module.Free k S := @Module.Free.of_divisionRing k S _ _ moduleKS
  exact ⟨_, ⟨(Module.Free.chooseBasis k S).repr⟩⟩

private theorem exists_injective_to_directSum_hull
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type (max u v)) [AddCommGroup M] [Module A M]
    (hM : IsIPowerTorsion A M (IsLocalRing.maximalIdeal A))
    (E : Type u) [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∃ J : Type (max u v), ∃ f : M →ₗ[A] ⨁ _ : J, E, Function.Injective f ∧
      ∀ z, z ∈ Submodule.torsionBySet A (⨁ _ : J, E)
        (IsLocalRing.maximalIdeal A : Set A) → z ∈ LinearMap.range f := by
  classical
  let K := A ⧸ IsLocalRing.maximalIdeal A
  let S : Submodule A M := Submodule.torsionBySet A M (IsLocalRing.maximalIdeal A : Set A)
  obtain ⟨J, ⟨e⟩⟩ := exists_linearEquiv_torsion_finsupp (R := A) M
  let iK : K →ₗ[A] E := i.hom
  let g0 : (J →₀ K) →ₗ[A] (⨁ _ : J, E) :=
    (finsuppLEquivDirectSum A E J).toLinearMap.comp (Finsupp.mapRange.linearMap iK)
  let g : S →ₗ[A] (⨁ _ : J, E) := g0.comp (e.toLinearMap.restrictScalars A)
  have hi' : Function.Injective iK := (ModuleCat.mono_iff_injective i).mp inferInstance
  have hg0 : Function.Injective g0 := fun x y h =>
    Finsupp.ext fun j => hi' (congrArg (fun z : ⨁ _ : J, E => z j) h)
  have hg : Function.Injective g := hg0.comp e.injective
  let : Module.Injective A E :=
    (Module.injective_iff_injective_object A E).mpr hi.1
  let : Module.Injective A (J →₀ E) := injective_finsupp A E J
  let : Module.Injective A (⨁ j : J, E) :=
    Module.Injective.of_ringEquiv (RingEquiv.refl A) (finsuppLEquivDirectSum A E J)
  obtain ⟨f, hf⟩ := Module.Injective.extension_property A (⨁ j : J, E)
    S M S.subtype S.subtype_injective g
  refine ⟨J, f, ?_, ?_⟩
  · intro x y hxy
    by_contra hxy'
    obtain ⟨a, haS, haz⟩ := exists_nonzero_socle_multiple A M
      (IsLocalRing.maximalIdeal A) hM (z := x - y) (sub_ne_zero.mpr hxy')
    let s : S := ⟨a • (x - y), haS⟩
    have hgs : g s = 0 := by
      rw [← hf]
      simp [s, hxy]
    have hs : s = 0 := hg (by simpa using hgs)
    have hzero : a • (x - y) = 0 := by simpa [s] using congrArg Subtype.val hs
    exact haz (by simpa using hzero)
  · intro z hz
    have hcoord : ∀ j : J, z j ∈ LinearMap.range iK := by
      intro j
      apply socle_mem_range_injectiveHull A E i hi.2
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      exact congrArg (fun q : ⨁ _ : J, E => q j)
        ((Submodule.mem_torsionBySet_iff _ _).mp hz a)
    let root : E → K := Function.invFun iK
    have hr0 : root 0 = 0 := by
      simpa [root] using Function.leftInverse_invFun hi' 0
    let q : J →₀ K := z.toFinsupp.mapRange root hr0
    have hgq : g0 q = z := by
      ext j
      change iK (root (z j)) = z j
      obtain ⟨k, hk⟩ := hcoord j
      rw [← hk]
      exact Function.apply_invFun_apply
    refine ⟨(e.symm q : M), ?_⟩
    have h := LinearMap.congr_fun hf (e.symm q)
    change f (e.symm q) = g (e.symm q) at h
    rw [h]
    simpa [g] using hgq

private noncomputable def tensorTorsionEquiv
    {R B M : Type*} [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M] [Module.Flat R B]
    (I : Ideal R) (hI : I.FG) :
    B ⊗[R] Submodule.torsionBySet R M (I : Set R) ≃ₗ[B]
      Submodule.torsionBySet B (B ⊗[R] M) (I.map (algebraMap R B) : Set B) := by
  classical
  let hgen := Submodule.fg_iff_exists_fin_generating_family.mp hI
  let n := hgen.choose
  let a : Fin n → R := hgen.choose_spec.choose
  have ha : Submodule.span R (Set.range a) = I := hgen.choose_spec.choose_spec
  let f := multiplicationFamily R M a
  let g := multiplicationFamily B (B ⊗[R] M) (fun j => algebraMap R B (a j))
  have hker : LinearMap.ker f = Submodule.torsionBySet R M (I : Set R) := by
    rw [← ha]
    exact ker_multiplicationFamily M a
  have hgker : LinearMap.ker g =
      Submodule.torsionBySet B (B ⊗[R] M) (I.map (algebraMap R B) : Set B) := by
    rw [← ha, Ideal.map_span, ← Set.range_comp]
    exact ker_multiplicationFamily _ _
  let t := TensorProduct.AlgebraTensorModule.lTensor B B f
  have ht : LinearMap.ker t = LinearMap.ker g := by
    ext x
    change t x = 0 ↔ g x = 0
    rw [← (TensorProduct.piRight R B B (fun _ : Fin n => M)).map_eq_zero_iff]
    have hval : TensorProduct.piRight R B B (fun _ : Fin n => M) (t x) = g x := by
      ext j
      exact piRight_baseChange_mulFamily M a (fun j => algebraMap R B (a j))
        (fun _ => rfl) x j
    rw [hval]
  exact (LinearEquiv.baseChange R B _ _ (LinearEquiv.ofEq _ _ hker)).symm ≪≫ₗ
    LinearMap.tensorKerEquiv B B f ≪≫ₗ LinearEquiv.ofEq _ _ (ht.trans hgker)

/-- Linear maps send `I`-torsion elements to `I`-torsion elements. -/
private lemma map_mem_torsionBySet
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) {I : Set R} {x : M}
    (hx : x ∈ Submodule.torsionBySet R M I) : f x ∈ Submodule.torsionBySet R N I := by
  rw [Submodule.mem_torsionBySet_iff] at *
  intro a
  rw [← f.map_smul, hx a, f.map_zero]

private noncomputable def torsionCongr
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) :
    Submodule.torsionBySet R M (I : Set R) ≃ₗ[R]
      Submodule.torsionBySet R N (I : Set R) :=
  { toFun x := ⟨e x, map_mem_torsionBySet e.toLinearMap x.property⟩
    invFun x := ⟨e.symm x, map_mem_torsionBySet e.symm.toLinearMap x.property⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x)
    right_inv x := Subtype.ext (e.apply_symm_apply x)
    map_add' x y := Subtype.ext (e.map_add x y)
    map_smul' a x := Subtype.ext (e.map_smul a x) }

universe w

private lemma exists_tensor_torsion_equiv_finsupp
    {R : Type u} {B : Type*} [CommRing R] [CommRing B] [IsLocalRing R] [Algebra R B]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] :
    ∃ J : Type (max u v), Nonempty
      ((B ⊗[R] Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R : Set R))
        ≃ₗ[B] (J →₀ B ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R B))) := by
  classical
  obtain ⟨J, ⟨e⟩⟩ := exists_linearEquiv_torsion_finsupp (R := R) M
  exact ⟨J, ⟨LinearEquiv.baseChange R B _ _ (e.restrictScalars R) ≪≫ₗ
    TensorProduct.finsuppRight R B B _ _ ≪≫ₗ
    Finsupp.mapRange.linearEquiv
      (Ideal.quotMapEquivTensorQuot B (I := IsLocalRing.maximalIdeal R)).symm⟩⟩

private lemma surjective_of_injective_torsion_kernels
    {A : Type u} [CommRing A] (m : Ideal A)
    {M N : Type (max u v)} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (hf : Function.Injective f) (hN : IsIPowerTorsion A N m)
    (hsoc : ∀ z, z ∈ Submodule.torsionBySet A N (m : Set A) → z ∈ LinearMap.range f)
    (hfil : ∀ z : N, ∃ I : Ideal A,
      z ∈ Submodule.torsionBySet A N (I : Set A) ∧
      Module.Injective (A ⧸ I) (Submodule.torsionBySet A M (I : Set A))) :
    Function.Surjective f := by
  intro z
  obtain ⟨I, hz, hI⟩ := hfil z
  let P := Submodule.torsionBySet A M (I : Set A)
  let Q := Submodule.torsionBySet A N (I : Set A)
  let fI : P →ₗ[A ⧸ I] Q := LinearMap.extendScalarsOfSurjective
    (Ideal.Quotient.mk_surjective (I := I))
    ((f.comp P.subtype).codRestrict Q fun x => map_mem_torsionBySet f x.property)
  have hfI : Function.Injective fI := fun x y h => Subtype.ext (hf (congrArg Subtype.val h))
  let : Module.Injective (A ⧸ I) P := hI
  obtain ⟨g, hg⟩ := Module.Injective.out fI hfI (LinearMap.id (R := A ⧸ I) (M := P))
  let zI : Q := ⟨z, hz⟩
  let d : Q := zI - fI (g zI)
  have hdg : g d = 0 := by simp [d, hg]
  have hd0 : d = 0 := by
    by_contra hd
    obtain ⟨a, ha, had⟩ := exists_nonzero_socle_multiple A N m hN
      (fun h => hd (Subtype.ext h))
    obtain ⟨x, hx⟩ := hsoc (a • (d : N)) ha
    have hxI : x ∈ P := by
      rw [Submodule.mem_torsionBySet_iff]
      intro b
      apply hf
      rw [f.map_smul, f.map_zero, hx, smul_comm]
      rw [(Submodule.mem_torsionBySet_iff _ _).mp d.property b, smul_zero]
    let xI : P := ⟨x, hxI⟩
    have hx0 : xI = 0 :=
      calc
        xI = g (fI xI) := (hg xI).symm
        _ = g ((Ideal.Quotient.mk I a) • d) := congrArg g (Subtype.ext hx)
        _ = 0 := by rw [g.map_smul, hdg, smul_zero]
    apply had
    rw [← hx, show x = 0 from congrArg Subtype.val hx0, map_zero]
  exact ⟨(g zI : M), congrArg Subtype.val (sub_eq_zero.mp hd0).symm⟩

private lemma isIPowerTorsion_injectiveHull
    (A E : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    IsIPowerTorsion A E (IsLocalRing.maximalIdeal A) := by
  have htop := Dualizing.iSup_maximalIdealPowTorsion_eq_top A
    (ModuleCat.of A (IsLocalRing.ResidueField A)) (ModuleCat.of A E)
    (LinearEquiv.refl A _) i hi
  have hdir : Directed (· ≤ ·)
      (fun n : ℕ => Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E) n) := by
    apply Monotone.directed_le
    intro n m hnm
    exact Submodule.torsionBySet_le_torsionBySet_pow _ _ (by omega) _
  intro z
  have hz : z ∈ (⨆ n : ℕ,
      Dualizing.maximalIdealPowTorsion A (ModuleCat.of A E) n) := by simp [htop]
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _ hdir).mp hz
  exact ⟨n + 1, Nat.succ_pos n, fun a ha =>
    (Submodule.mem_torsionBySet_iff _ _).mp hn ⟨a, ha⟩⟩

attribute [local instance] HasDerivedCategory.standard in
private lemma injective_of_gorenstein_of_dim_zero
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : Dualizing.IsGorensteinLocalRing R) (hdim : ringKrullDim R = 0) :
    Module.Injective R R := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)
  let k := (ModuleCat.uliftFunctor.{0} R).obj
    (ModuleCat.of R (IsLocalRing.ResidueField R))
  obtain ⟨E, i, hi, hE⟩ := Module.exists_isInjectiveHull R k
  let : Mono i := hi
  obtain ⟨n, ⟨e⟩⟩ := Dualizing.exists_shift_iso_single_injectiveHull_of_ringKrullDim_eq_zero
    K hR hdim E i hE
  let HE := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj E
  let e₀ := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app
    (ModuleCat.of R R)
  let eH : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj K ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj HE :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).mapIso e ≪≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftIso n 0 n
        (add_zero n)).app HE
  have hn : n = 0 := by
    by_contra hn
    have hz : Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj HE) := by
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact DerivedCategory.isZero_of_isGE HE 0 n hlt
      · exact DerivedCategory.isZero_of_isLE HE 0 n hgt
    let := ModuleCat.isZero_iff_subsingleton.mp hz
    have : Subsingleton R :=
      (e₀.symm.toLinearEquiv.trans eH.toLinearEquiv).injective.subsingleton
    exact zero_ne_one (Subsingleton.elim (0 : R) 1)
  subst n
  let eR : ModuleCat.of R R ≅ E := e₀.symm ≪≫ eH ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app E
  exact (Module.injective_iff_injective_object R R).mpr (Injective.of_iso eR.symm hE.1)

private lemma injective_torsion_of_flat_baseChange
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    [IsNoetherianRing A] [IsLocalRing R] [Algebra R A] [Module.Flat R A]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module A M]
    (e : A ⊗[R] M ≃ₗ[A] M)
    (hI : Module.Injective (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
      (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))) :
    Module.Injective (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
      (Submodule.torsionBySet A M
        ((IsLocalRing.maximalIdeal R).map (algebraMap R A) : Set A)) := by
  let I := (IsLocalRing.maximalIdeal R).map (algebraMap R A)
  let P := Submodule.torsionBySet A M (I : Set A)
  let t : (A ⊗[R] Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R : Set R))
      ≃ₗ[A] P := tensorTorsionEquiv _ (IsNoetherian.noetherian _) ≪≫ₗ torsionCongr I e
  obtain ⟨J, ⟨eJ⟩⟩ := exists_tensor_torsion_equiv_finsupp (R := R) (B := A) M
  let eP : P ≃ₗ[A ⧸ I] (J →₀ A ⧸ I) :=
    LinearEquiv.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective (I := I))
      (t.symm ≪≫ₗ eJ)
  let : Module.Injective (A ⧸ I) (A ⧸ I) := hI
  let : Module.Injective (A ⧸ I) (J →₀ A ⧸ I) := injective_finsupp _ _ J
  exact Module.Injective.of_ringEquiv (RingEquiv.refl (A ⧸ I)) eP.symm

private lemma frobenius_pow_apply
    {A : Type*} [CommRing A] (p : ℕ) (hp : p.Prime) (hchar : (p : A) = 0)
    (n : ℕ) (a : A) : (frobeniusOfPrime p hp hchar ^ n) a = a ^ (p ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' (frobeniusOfPrime p hp hchar), RingHom.mul_def,
      RingHom.comp_apply, frobeniusOfPrime_apply, ih, pow_succ, pow_mul]

private lemma exists_injective_frobenius_kernel
    (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hchar : (p : A) = 0)
    (M : Type (max u v)) [AddCommGroup M] [Module A M]
    (hF : (ModuleCat.extendScalars (frobeniusOfPrime p hp hchar)).obj
      (ModuleCat.of A M) ≅ ModuleCat.of A M) (n : ℕ) :
    ∃ I : Ideal A, I ≤ IsLocalRing.maximalIdeal A ^ (p ^ n) ∧
      Module.Injective (A ⧸ I) (Submodule.torsionBySet A M (I : Set A)) := by
  let R := ULift.{0} A
  let e : R ≃+* A := ULift.ringEquiv
  let F := frobeniusOfPrime p hp hchar
  let g : R →+* A := (F ^ n).comp e.toRingHom
  let : IsRegularLocalRing R := IsRegularLocalRing.of_ringEquiv e.symm
  let : Module R M := Module.compHom M e.toRingHom
  let : Algebra R A := g.toAlgebra
  let : Module R A := g.toAlgebra.toModule
  have hgpow (x : R) : g x = (e x) ^ (p ^ n) :=
    frobenius_pow_apply p hp hchar n (e x)
  let : IsLocalHom g := ⟨fun x hx => by
    have hu : IsUnit (e x) := (isUnit_pow_iff (pow_ne_zero n hp.ne_zero)).mp
      (by rwa [← hgpow])
    simpa using hu.map e.symm.toMonoidHom⟩
  have hgflat : RingHom.Flat g :=
    (RingHom.Flat.of_bijective (f := e.toRingHom) e.bijective).comp
      (frobenius_iterate_flat A F
        (frobeniusOfPrime_flat_of_isRegularLocalRing A p hp hchar) n)
  let : Module.Flat R A := hgflat
  let I := (IsLocalRing.maximalIdeal R).map g
  have hmaple : I ≤ IsLocalRing.maximalIdeal A := IsLocalRing.map_maximalIdeal_le g
  have hIproper : I ≠ ⊤ := ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top g)
  have hrad : I.radical = IsLocalRing.maximalIdeal A := by
    apply le_antisymm
    · exact (IsLocalRing.maximalIdeal.isMaximal A).isPrime.isRadical.radical_le_iff.mpr hmaple
    · intro a ha
      rw [Ideal.mem_radical_iff]
      refine ⟨p ^ n, ?_⟩
      have hau : ULift.up a ∈ IsLocalRing.maximalIdeal R := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact (IsLocalRing.notMem_maximalIdeal.mpr (hu.map e.toMonoidHom)) ha
      have h := Ideal.mem_map_of_mem g hau
      rwa [hgpow] at h
  have hIle : I ≤ (IsLocalRing.maximalIdeal A) ^ (p ^ n) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hae : e a ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ha ⊢
      exact fun h => ha (by simpa using h.map e.symm.toMonoidHom)
    change g a ∈ (IsLocalRing.maximalIdeal A) ^ (p ^ n)
    rw [hgpow]
    exact Ideal.pow_mem_pow hae (p ^ n)
  let : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIproper
  let : IsLocalRing (A ⧸ I) := IsLocalRing.of_surjective'
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hG : Dualizing.IsGorensteinLocalRing (A ⧸ I) :=
    ((Dualizing.isGorensteinLocalRing_iff_of_flat R A).mp
      (Dualizing.IsRegularLocalRing.isGorensteinLocalRing A)).2
  have hself : Module.Injective (A ⧸ I) (A ⧸ I) :=
    injective_of_gorenstein_of_dim_zero _ hG
      (dim_quotient_eq_zero_of_radical_maximalIdeal hrad)
  have : (ModuleCat.restrictScalars.{max u v} e.toRingHom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  have : IsIso (ModuleCat.extendRestrictScalarsAdj.{max u v, u, u} e.toRingHom).counit :=
    Adjunction.counit_isIso_of_R_fully_faithful _
  let ec : (ModuleCat.extendScalars e.toRingHom).obj (ModuleCat.of R M) ≅
      ModuleCat.of A M :=
    (asIso (ModuleCat.extendRestrictScalarsAdj.{max u v, u, u} e.toRingHom).counit).app
      (ModuleCat.of A M)
  let em : (ModuleCat.extendScalars g).obj (ModuleCat.of R M) ≅ ModuleCat.of A M :=
    (ModuleCat.extendScalarsComp e.toRingHom (F ^ n)).app (ModuleCat.of R M) ≪≫
      (ModuleCat.extendScalars (F ^ n)).mapIso ec ≪≫ extendScalarsPowIso A F M hF n
  exact ⟨I, hIle, injective_torsion_of_flat_baseChange M em.toLinearEquiv hself⟩

-- Preserve the statement's instance choices despite the additional proof imports.
attribute [-instance] ReflQuiver.toQuiver in
attribute [local instance 2000] Limits.hasFiniteLimits_of_hasLimits in
/-- **Stacks Project, Tag 0EC3.** A maximal-ideal-power-torsion module over a regular local ring
of prime characteristic which is invariant under extension of scalars by Frobenius is a direct
sum of copies of the injective hull of the residue field. -/
@[stacks 0EC3]
public theorem isIPowerTorsion_frobeniusStable_exists_equiv_directSum_injectiveHull
    (p : ℕ) (hp : p.Prime)
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hchar : (p : A) = 0)
    (M : Type (max u v)) [AddCommGroup M] [Module A M]
    (hM : IsIPowerTorsion A M (IsLocalRing.maximalIdeal A))
    (hF : (ModuleCat.extendScalars (frobeniusOfPrime p hp hchar)).obj
      (ModuleCat.of A M) ≅ ModuleCat.of A M)
    (E : Type u) [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (IsLocalRing.ResidueField A) ⟶ ModuleCat.of A E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∃ J : Type (max u v), Nonempty (M ≃ₗ[A] ⨁ _ : J, E) := by
  obtain ⟨J, f, hf, hsoc⟩ := exists_injective_to_directSum_hull A M hM E i hi
  have hT : IsIPowerTorsion A (⨁ _ : J, E) (IsLocalRing.maximalIdeal A) :=
    MvPowerSeries.isIPowerTorsion_directSum A J (fun _ => E) _
      (fun _ => isIPowerTorsion_injectiveHull A E i hi)
  have hsurj : Function.Surjective f := by
    apply surjective_of_injective_torsion_kernels (IsLocalRing.maximalIdeal A) f hf hT hsoc
    intro z
    obtain ⟨k, -, hkill⟩ := hT z
    obtain ⟨I, hIle, hI⟩ := exists_injective_frobenius_kernel p hp A hchar M hF k
    exact ⟨I, (Submodule.mem_torsionBySet_iff _ _).mpr fun a =>
      hkill a (Ideal.pow_le_pow_right (Nat.lt_pow_self hp.one_lt).le (hIle a.property)), hI⟩
  exact ⟨J, ⟨LinearEquiv.ofBijective f ⟨hf, hsurj⟩⟩⟩

end Dualizing
