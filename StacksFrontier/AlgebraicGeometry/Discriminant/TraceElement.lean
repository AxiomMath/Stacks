module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Discriminant.DiscriminantIdeal

/-!
# Relative dualizing modules of quasi-finite ring maps, and trace elements

Let `A → B` be a quasi-finite homomorphism of Noetherian rings. By Zariski's main theorem there is
a factorization `A → B' → B` with `A → B'` finite and `Spec(B) → Spec(B')` an open immersion, and
the *relative dualizing module* is `ω_{B/A} = Hom_A(B', A) ⊗_{B'} B`. This file sets up that
construction and the commutative algebra needed for the theory of trace elements in `ω_{B/A}`.

The factorization is packaged as `FiniteOpenFactorization`, which records the intermediate
algebra together with the ring-theoretic form of "the map of spectra is an open immersion": the
induced map of prime spectra is an open embedding, and on every basic open contained in its image
the map of away localizations is bijective. Two consequences of that shape are proved here and
used repeatedly: the target is of finite type over the base, and the intermediate algebra maps to
the target by a ring epimorphism.

## Main definitions

* `Stacks.Discriminant.FiniteOpenFactorization` is the factorization through a finite algebra
  whose second map induces an open immersion on spectra.
* `Stacks.Discriminant.algebraDualModule` is the natural module structure of an algebra on its
  linear dual over the base.
* `Stacks.Discriminant.dualizingModule` is `Hom_A(B', A) ⊗_{B'} B`, with
  `Stacks.Discriminant.dualizingModule.tmul` its pure tensors.

## Main results

* `Stacks.Discriminant.dualizingModule.induction_on`: pure tensors generate the dualizing module.
* `Stacks.Discriminant.finiteType_of_finiteOpenFactorization`: the target of a finite-open
  factorization is of finite type over the base.
* `Stacks.Discriminant.isEpi_of_finiteOpenFactorization`: the intermediate algebra maps onto the
  target by a ring epimorphism.
* `Stacks.Discriminant.surjective_finite_factor`: a finite quotient of the target is already a
  quotient of the intermediate algebra.
* `Stacks.Discriminant.exists_smul_eq_zero_of_restriction_eq_zero`: an element of the dualizing
  module whose restriction to a finite direct factor vanishes is annihilated by a scalar
  restricting to `1` on that factor. This is the local step in the uniqueness of trace elements.
* `Stacks.Discriminant.mem_prime_of_tmul_eq_zero`: a pure tensor over a flat extension vanishes
  only if its coefficient lies in every prime above the annihilator of its second factor.

## Implementation notes

`dualizingModule F` is a type synonym for a tensor product. Its additive and `B`-module
structures are obtained by unfolding the synonym, so proofs that reason by induction on tensors
would otherwise have to unfold it too; `induction_on`, `zero_tmul` and `add_tmul` provide the API
that avoids this, and `smul_tmul` characterizes the `B`-action.

The restriction of a dualizing element to a finite direct factor is characterized on pure tensors
by the finite-projective trace of `Stacks.Discriminant.finiteProjectiveTrace`, and
`finiteProjectiveTrace_lmul_of_section` computes that trace on a split quotient as the splitting.
This is what makes `exists_smul_eq_zero_of_restriction_eq_zero` a statement about a projective
lifting rather than about a choice of basis.

## References

* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
* [Stacks Project, Tag 0BT7](https://stacks.math.columbia.edu/tag/0BT7)
-/

@[expose] public section

open Topology
open scoped Pointwise TensorProduct

universe u v w x y z

namespace Stacks.Discriminant

/-- A factorization of an algebra through a finite algebra such that the second map induces
an open immersion on prime spectra. -/
structure FiniteOpenFactorization (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] where
  /-- The intermediate algebra. -/
  middle : Type w
  /-- The intermediate algebra is a commutative ring. -/
  commRingMiddle : CommRing middle
  /-- The algebra structure on the intermediate ring. -/
  algebraMiddle : Algebra A middle
  /-- The map from the intermediate ring to the target. -/
  algebraTarget : Algebra middle B
  /-- The factorization is compatible with the given map from the source to the target. -/
  scalarTower : IsScalarTower A middle B
  /-- The intermediate algebra is finite over the source. -/
  finite_middle : Module.Finite A middle
  /-- The map on prime spectra is an open embedding. -/
  isOpenEmbedding_comap :
    IsOpenEmbedding (PrimeSpectrum.comap (algebraMap middle B))
  /-- On every basic open contained in the image, the map is the corresponding localization. -/
  awayMap_bijective (g : middle)
      (hg : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum middle)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap middle B))) :
    Function.Bijective (Localization.awayMap (algebraMap middle B) g)

namespace FiniteOpenFactorization

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The commutative ring structure of the intermediate algebra. -/
instance (F : FiniteOpenFactorization.{u, v, w} A B) : CommRing F.middle :=
  F.commRingMiddle

/-- The algebra structure of the intermediate ring over the source. -/
instance (F : FiniteOpenFactorization.{u, v, w} A B) : Algebra A F.middle :=
  F.algebraMiddle

/-- The algebra structure of the target over the intermediate ring. -/
instance (F : FiniteOpenFactorization.{u, v, w} A B) : Algebra F.middle B :=
  F.algebraTarget

/-- The source, the intermediate algebra and the target form a scalar tower. -/
instance (F : FiniteOpenFactorization.{u, v, w} A B) : IsScalarTower A F.middle B :=
  F.scalarTower

/-- The intermediate algebra is finite over the source. -/
instance (F : FiniteOpenFactorization.{u, v, w} A B) : Module.Finite A F.middle :=
  F.finite_middle

end FiniteOpenFactorization

/-- The natural module structure of an algebra on its linear dual over the base ring. -/
@[instance_reducible]
def algebraDualModule (A C : Type*) [CommRing A] [CommRing C]
    [Algebra A C] : Module C (Module.Dual A C) where
  smul c f := f.comp ((Algebra.lmul A C) c)
  one_smul f := by
    ext x
    change f (1 * x) = f x
    rw [one_mul]
  mul_smul b c f := by
    ext x
    change f ((b * c) * x) = f (c * (b * x))
    congr 1
    ac_rfl
  smul_zero c := by
    ext x
    rfl
  smul_add c f g := by
    ext x
    rfl
  add_smul b c f := by
    ext x
    change f ((b + c) * x) = f (b * x) + f (c * x)
    rw [add_mul, map_add]
  zero_smul f := by
    ext x
    change f (0 * x) = 0
    rw [zero_mul, map_zero]

attribute [local instance] algebraDualModule

/-- Evaluation characterizes the natural action of an algebra on its dual. -/
@[simp]
lemma algebraDualModule_smul_apply (A C : Type*) [CommRing A] [CommRing C]
    [Algebra A C] (c x : C) (f : Module.Dual A C) : (c • f) x = f (c * x) :=
  rfl

/-- The relative dualizing module `Hom_A(B', A) ⊗_{B'} B` of a finite-open factorization
`A → B' → B`. -/
@[stacks 0BSZ]
def dualizingModule {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) : Type (max u v w) :=
  letI := algebraDualModule A F.middle
  Module.Dual A F.middle ⊗[F.middle] B

namespace dualizingModule

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The additive group structure of the relative dualizing module. -/
instance (F : FiniteOpenFactorization.{u, v, w} A B) :
    AddCommGroup (dualizingModule F) := by
  unfold dualizingModule
  letI := algebraDualModule A F.middle
  exact TensorProduct.addCommGroup

/-- The `B`-module structure of the relative dualizing module, by multiplication on the factor
`B`. -/
instance (F : FiniteOpenFactorization.{u, v, w} A B) :
    Module B (dualizingModule F) := by
  unfold dualizingModule
  letI := algebraDualModule A F.middle
  letI : Module B (B ⊗[F.middle] Module.Dual A F.middle) :=
    TensorProduct.leftModule
  exact (TensorProduct.comm F.middle (Module.Dual A F.middle) B).toAddEquiv.module B

/-- A pure tensor in the relative dualizing module. -/
def tmul (F : FiniteOpenFactorization.{u, v, w} A B)
    (f : Module.Dual A F.middle) (x : B) : dualizingModule F :=
  f ⊗ₜ[F.middle] x

/-- The `B`-action on the relative dualizing module is multiplication on the tensor's
`B`-factor. -/
@[simp]
lemma smul_tmul (F : FiniteOpenFactorization.{u, v, w} A B) (b x : B)
    (f : Module.Dual A F.middle) : b • tmul F f x = tmul F f (b * x) := by
  show (TensorProduct.comm F.middle (Module.Dual A F.middle) B).symm
      (b • (TensorProduct.comm F.middle (Module.Dual A F.middle) B) (f ⊗ₜ x)) = _
  rw [TensorProduct.comm_tmul, TensorProduct.smul_tmul', TensorProduct.comm_symm_tmul]
  rfl

/-- Scaling the dual factor of a pure tensor by an element of the intermediate algebra is the
same as scaling the tensor by its image in the target. -/
theorem tmul_dual_smul (F : FiniteOpenFactorization.{u, v, w} A B)
    (c : F.middle) (φ : Module.Dual A F.middle) (b : B) :
    tmul F (c • φ) b = algebraMap F.middle B c • tmul F φ b := by
  rw [smul_tmul]
  simpa only [dualizingModule, dualizingModule.tmul, Algebra.smul_def] using
    (TensorProduct.smul_tmul (R := F.middle) c φ b)

/-- A pure tensor with vanishing dual factor vanishes. -/
@[simp]
lemma zero_tmul (F : FiniteOpenFactorization.{u, v, w} A B) (x : B) :
    tmul F 0 x = 0 :=
  TensorProduct.zero_tmul _ _

/-- A pure tensor is additive in its dual factor. -/
@[simp]
lemma add_tmul (F : FiniteOpenFactorization.{u, v, w} A B)
    (f g : Module.Dual A F.middle) (x : B) :
    tmul F (f + g) x = tmul F f x + tmul F g x :=
  TensorProduct.add_tmul _ _ _

/-- Pure tensors generate the relative dualizing module: to prove a property of every element it
suffices to prove it for `0`, for pure tensors, and for sums. This repackages
`TensorProduct.induction_on` so that consumers need not unfold `dualizingModule`. -/
theorem induction_on (F : FiniteOpenFactorization.{u, v, w} A B)
    {motive : dualizingModule F → Prop} (z : dualizingModule F) (zero : motive 0)
    (tmul : ∀ (f : Module.Dual A F.middle) (b : B), motive (dualizingModule.tmul F f b))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on (R := F.middle) (M := Module.Dual A F.middle) (N := B)
    z zero tmul add

end dualizingModule

/-- Every prime of the target has a basic open of the intermediate algebra around its contraction
that lies in the image of the spectrum map. -/
private theorem exists_basicOpen_subset_range
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (P : Ideal B) [hP : P.IsPrime] :
    ∃ g : F.middle, algebraMap F.middle B g ∉ P ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum F.middle)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) := by
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hqg, hbasic⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show PrimeSpectrum.comap (algebraMap F.middle B) ⟨P, hP⟩ ∈ Set.range _ from
        ⟨⟨P, hP⟩, rfl⟩)
      F.isOpenEmbedding_comap.isOpen_range
  exact ⟨g, by simpa using hqg, hbasic⟩

/-- A finite-open factorization makes the target a finite-type algebra. -/
lemma finiteType_of_finiteOpenFactorization
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization.{u, v, w} A B) :
    Algebra.FiniteType A B := by
  classical
  let M := F.middle
  let s : Set B := {b | ∃ g : M,
    algebraMap M B g = b ∧
      (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum M)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap M B))}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hspan⟩ := Ideal.exists_le_maximal (Ideal.span s) hne
    have := hPmax.isPrime
    obtain ⟨g, hg, hbasic⟩ := exists_basicOpen_subset_range F P
    exact hg (hspan (Ideal.subset_span ⟨g, rfl, hbasic⟩))
  refine Algebra.FiniteType.of_span_eq_top_target s hs ?_
  rintro _ ⟨g, rfl, hbasic⟩
  let e : Localization.Away g ≃ₐ[M]
      Localization.Away (algebraMap M B g) :=
    AlgEquiv.ofBijective (Localization.awayMapₐ (IsScalarTower.toAlgHom M M B) g)
      (F.awayMap_bijective g hbasic)
  have : Algebra.FiniteType A M := Module.Finite.finiteType M
  exact (inferInstance : Algebra.FiniteType A (Localization.Away g)).equiv (e.restrictScalars A)

/-- The algebra map of an open factorization is an epimorphism. -/
lemma isEpi_of_finiteOpenFactorization
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (F : FiniteOpenFactorization A B) : Algebra.IsEpi F.middle B := by
  classical
  let R := F.middle
  apply (Algebra.isEpi_iff_forall_one_tmul_eq R B).mpr
  intro b
  apply sub_eq_zero.mp
  let z : B ⊗[R] B := 1 ⊗ₜ[R] b - b ⊗ₜ[R] 1
  show z = 0
  by_contra hz
  let I := (Submodule.span B {z}).annihilator
  have hI : I ≠ ⊤ := by
    intro h
    have : (1 : B) ∈ I := h ▸ trivial
    rw [Submodule.mem_annihilator_span_singleton] at this
    exact hz (by simpa using this)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  have := hP.isPrime
  obtain ⟨g, hg, hbasic⟩ := exists_basicOpen_subset_range F P
  obtain ⟨a, n, ha⟩ := Localization.awayMap_surjective_iff.mp
    (F.awayMap_bijective g hbasic).2 b
  have hgz : algebraMap R B g ^ n ∈ I := by
    rw [Submodule.mem_annihilator_span_singleton]
    show (algebraMap R B g ^ n) • (1 ⊗ₜ[R] b - b ⊗ₜ[R] 1) = 0
    rw [smul_sub]
    have hleft : (algebraMap R B g ^ n) • ((1 : B) ⊗ₜ[R] b) =
        (1 : B) ⊗ₜ[R] (algebraMap R B g ^ n * b) := by
      show (algebraMap R B g ^ n * 1) ⊗ₜ[R] b = _
      simpa only [Algebra.smul_def, map_pow, mul_one] using
        TensorProduct.smul_tmul (g ^ n) (1 : B) b
    rw [hleft]
    show 1 ⊗ₜ[R] (algebraMap R B g ^ n * b) -
      (algebraMap R B g ^ n * b) ⊗ₜ[R] 1 = 0
    rw [← ha, Algebra.TensorProduct.tmul_one_eq_one_tmul, sub_self]
  exact hg (hP.isPrime.mem_of_pow_mem n (hIP hgz))

/-- A finite quotient of the open algebra is a quotient of the intermediate algebra. -/
lemma surjective_finite_factor
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] (F : FiniteOpenFactorization A B)
    [Algebra B C] [Algebra F.middle C] [IsScalarTower F.middle B C]
    [Module.Finite F.middle C] (h : Function.Surjective (algebraMap B C)) :
    Function.Surjective (algebraMap F.middle C) := by
  apply Algebra.isEpi_iff_surjective_algebraMap_of_finite.mp
  apply (Algebra.isEpi_iff_forall_one_tmul_eq F.middle C).mpr
  intro c
  obtain ⟨b, rfl⟩ := h c
  simpa using congrArg (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom F.middle B C) (IsScalarTower.toAlgHom F.middle B C))
    ((Algebra.isEpi_iff_forall_one_tmul_eq F.middle B).mp
      (isEpi_of_finiteOpenFactorization F) b)

/-- The projective trace of a rank-one endomorphism is evaluation. -/
lemma finiteProjectiveTrace_smulRight
    {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] (f : P →ₗ[R] R) (x : P) :
    finiteProjectiveTrace R P (f.smulRight x) = f x := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R P
  let n := h.choose
  let p : (Fin n → R) →ₗ[R] P := h.choose_spec.choose
  let i : P →ₗ[R] (Fin n → R) := h.choose_spec.choose_spec.choose
  have hpi : p.comp i = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  show LinearMap.trace R (Fin n → R) (i.comp ((f.smulRight x).comp p)) = _
  have heq : i.comp ((f.smulRight x).comp p) = (f.comp p).smulRight (i x) :=
    LinearMap.ext fun _ => i.map_smul _ _
  rw [heq, LinearMap.trace_smulRight]
  exact congrArg f (LinearMap.congr_fun hpi x)

/-- On a split quotient, the algebra trace is the linear section. -/
lemma finiteProjectiveTrace_lmul_of_section
    {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [Module.Finite R C] [Module.Projective R C]
    (l : C →ₗ[R] R) (hl : (Algebra.linearMap R C).comp l = LinearMap.id) (c : C) :
    finiteProjectiveTrace R C (Algebra.lmul R C c) = l c := by
  have heq : Algebra.lmul R C c = l.smulRight c := by
    ext b
    have hb := LinearMap.congr_fun hl b
    change algebraMap R C (l b) = b at hb
    simp [Algebra.smul_def, hb, mul_comm]
  rw [heq, finiteProjectiveTrace_smulRight]

/-- A functional on a ring epimorphism acts after extension by its value on one. -/
lemma algebraMap_apply_eq_mul_of_isEpi
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsEpi R S]
    (t : S →ₗ[R] R) (b : S) :
    algebraMap R S (t b) = b * algebraMap R S (t 1) := by
  have h := (Algebra.isEpi_iff_forall_one_tmul_eq R S).mp inferInstance b
  simpa [Algebra.smul_def, mul_comm] using
    congrArg (fun z => TensorProduct.rid R S (LinearMap.lTensor S t z)) h

/-- Vanishing on a finite factor is killed by a scalar that restricts to one there. -/
lemma exists_smul_eq_zero_of_restriction_eq_zero
    {A S C : Type*} [CommRing A] [CommRing S] [CommRing C] [Algebra A S]
    (F : FiniteOpenFactorization A S) [Algebra A C] [Algebra S C]
    [Algebra F.middle C] [IsScalarTower A F.middle C] [IsScalarTower F.middle S C]
    [Module.Finite F.middle C] [Module.Projective F.middle C]
    (hsurj : Function.Surjective (algebraMap S C)) :
    letI : Module A (dualizingModule F) := Module.compHom _ (algebraMap A S)
    ∀ (h : dualizingModule F →ₗ[A] Module.Dual A C),
      (∀ (f : Module.Dual A F.middle) (b : S) (c : C),
        h (dualizingModule.tmul F f b) c =
          f (finiteProjectiveTrace F.middle C
            (Algebra.lmul F.middle C (algebraMap S C b * c)))) →
      ∀ y, h y = 0 → ∃ a : F.middle,
        algebraMap F.middle C a = 1 ∧ algebraMap F.middle S a • y = 0 := by
  classical
  let := algebraDualModule A F.middle
  let : Module A (dualizingModule F) := Module.compHom _ (algebraMap A S)
  intro h hh y hy
  let R := F.middle
  obtain ⟨l, hl⟩ := Module.projective_lifting_property
    (Algebra.linearMap R C) (LinearMap.id : C →ₗ[R] C)
    (surjective_finite_factor F hsurj)
  let t : S →ₗ[R] R := l.comp (IsScalarTower.toAlgHom R S C).toLinearMap
  let a := l 1
  have ha : algebraMap R C a = 1 := LinearMap.congr_fun hl 1
  refine ⟨a, ha, ?_⟩
  let β : Module.Dual A C → dualizingModule F := fun g =>
    dualizingModule.tmul F (g.comp (IsScalarTower.toAlgHom A R C).toLinearMap) 1
  have hβzero : β 0 = 0 := by simp [β]
  have hβadd (g k : Module.Dual A C) : β (g + k) = β g + β k := by
    simp [β, LinearMap.add_comp]
  have hformula (z : dualizingModule F) : β (h z) = algebraMap R S a • z := by
    induction z using dualizingModule.induction_on with
    | zero => simp [hβzero]
    | add z z' hz hz' => rw [map_add, hβadd, hz, hz', smul_add]
    | tmul f b =>
      have hcomp : (h (dualizingModule.tmul F f b)).comp
          (IsScalarTower.toAlgHom A R C).toLinearMap = t b • f := by
        ext r
        show h (dualizingModule.tmul F f b) (algebraMap R C r) = f (t b * r)
        rw [hh, finiteProjectiveTrace_lmul_of_section l hl]
        congr 1
        show l (algebraMap S C b * algebraMap R C r) = l (algebraMap S C b) * r
        rw [mul_comm, ← Algebra.smul_def, map_smul]
        simp [mul_comm]
      show dualizingModule.tmul F
        ((h (dualizingModule.tmul F f b)).comp
          (IsScalarTower.toAlgHom A R C).toLinearMap) 1 =
        algebraMap R S a • dualizingModule.tmul F f b
      rw [hcomp, dualizingModule.smul_tmul]
      show (t b • f) ⊗ₜ[R] (1 : S) = f ⊗ₜ[R] (algebraMap R S a * b)
      rw [TensorProduct.smul_tmul]
      congr 1
      have : Algebra.IsEpi R S := isEpi_of_finiteOpenFactorization F
      simpa [Algebra.smul_def, t, a, mul_comm] using
        algebraMap_apply_eq_mul_of_isEpi t b
  rw [← hformula, hy, hβzero]

/-- An idempotent quotient is the corresponding localization. -/
lemma idempotent_quotient_isLocalization_away
    {S : Type u} [CommRing S] (e : S) (he : IsIdempotentElem e) :
    IsLocalization.Away e (S ⧸ Ideal.span {1 - e}) := by
  let Q := S ⧸ Ideal.span {1 - e}
  let : Algebra S Q := Ideal.Quotient.algebra _
  have heq : algebraMap S Q e = 1 := by
    show Ideal.Quotient.mk (Ideal.span {1 - e}) e =
      Ideal.Quotient.mk (Ideal.span {1 - e}) 1
    rw [Ideal.Quotient.eq, show e - 1 = -(1 - e) by ring]
    exact (Ideal.span {1 - e}).neg_mem (Ideal.subset_span (by simp))
  have hker : RingHom.ker (algebraMap S Q) = Ideal.span {1 - e} := by
    simp [Q]
  have hmul : e • RingHom.ker (algebraMap S Q) = ⊥ := by
    rw [hker, Submodule.smul_span]
    simp [he.mul_one_sub_self]
  exact IsLocalization.Away.of_surjective_of_isScalarTower
    (R := S) (S := S) (T := Q) Ideal.Quotient.mk_surjective
    Function.surjective_id e (isUnit_iff_exists_inv.mpr ⟨1, by simp [heq]⟩)
    (n := 1) (by simp [hmul])

/-- A vanishing tensor has coefficient in every ideal above the annihilator of its element.
Primality of neither ideal is used: only that `p` is the contraction of `P` and that it contains
the annihilator of `x`. -/
lemma mem_prime_of_tmul_eq_zero
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M]
    [Module.Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p]
    (x : M) (hxann : ∀ r : R, r • x = 0 → r ∈ p) (s : S) :
    s ⊗ₜ[R] x = 0 → s ∈ P := by
  intro hzero
  let f := LinearMap.toSpanSingleton R M x
  let I : Ideal R := f.ker
  have hExact : Function.Exact I.subtype f := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  have hsRange : s ⊗ₜ[R] (1 : R) ∈ (LinearMap.lTensor S I.subtype).range := by
    rw [← LinearMap.exact_iff.mp (Module.Flat.lTensor_exact S hExact)]
    exact LinearMap.mem_ker.mpr (by simpa [f] using hzero)
  have hmap : ∀ z : TensorProduct R S ↥I,
      (TensorProduct.rid R S) ((LinearMap.lTensor S I.subtype) z) ∈
        I.map (algebraMap R S) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s r =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
      simpa [Algebra.smul_def] using
        (I.map (algebraMap R S)).mul_mem_right s (Ideal.mem_map_of_mem (algebraMap R S) r.2)
    | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, map_add]
      exact (I.map (algebraMap R S)).add_mem hz₁ hz₂
  obtain ⟨z, hz⟩ := hsRange
  have hsMem : s ∈ I.map (algebraMap R S) := by simpa [hz] using hmap z
  have hmaple : I.map (algebraMap R S) ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (by
      have hpq : p = Ideal.comap (algebraMap R S) P := by
        simpa [Ideal.under] using P.over_def p
      rw [← hpq]
      exact fun r hr => hxann r (by simpa [I, f] using hr))
  exact hmaple hsMem

end Stacks.Discriminant

end
