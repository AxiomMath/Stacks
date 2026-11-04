module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Ideal.RelativeAssassin
public import StacksFrontier.RingTheory.Ideal.RelativeAssassin.Defs

/-!
# The relative assassin on an affine open

For a morphism of schemes and a quasi-coherent module, a prime in the relative assassin of the
module of sections over an affine open determines a point of the relative assassin of the
sheaf. The converse holds when the fibres are locally Noetherian.

The comparison runs through a chart of the fibre: over affine opens `U ⊆ X` and `V ⊆ S` with
`U ⊆ f⁻¹V`, the fibre of `f` over the image point `s` of a prime `q ⊆ Γ(X, U)` contains the
spectrum of `Γ(X, U) ⊗_{Γ(S, V)} κ(p)` as an open subscheme, where `p` is the contraction of
`q`. The sections of the restricted module over that chart are the base change of `Γ(F, U)`,
and the module-theoretic relative assassin of `Γ(F, U)` is read off from the associated primes
of that base change.

## Main definitions

* `AlgebraicGeometry.specPullbackSectionsIso`: the global sections of the pullback of a
  quasi-coherent module along a morphism of affine spectra, as the extension of scalars of its
  global sections. This is the chart-level input to the comparison, and is stated here for reuse.

## Main results

* `AlgebraicGeometry.mem_relativeAssassin_of_mem_relativeAssassin_sections`: the forward
  implication.
* `AlgebraicGeometry.mem_relativeAssassin_sections_iff_of_locallyNoetherian_fibers`: the
  equivalence when all fibres are locally Noetherian.

## Implementation notes

The coordinate rings are the rings of sections on the affine opens. The ring map from the
target to the source is induced by the scheme morphism, and also gives the restricted scalar
action on the module of sections. The prime corresponding to a point is
`IsAffineOpen.primeIdealOf`. The two tagged declarations state respectively the unconditional
implication and the locally Noetherian equivalence.

## References

* [Stacks Project, Tag 0CU5](https://stacks.math.columbia.edu/tag/0CU5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite TopologicalSpace

universe u v w

namespace AlgebraicGeometry

/-- The annihilator of `m`, written as a colon ideal against the cyclic submodule it generates,
is the colon ideal against the singleton `{m}`. -/
lemma colon_span_singleton_eq_colon_singleton {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (m : M) :
    (⊥ : Submodule R M).colon (Submodule.span R {m}) =
      (⊥ : Submodule R M).colon {m} := by
  ext r
  simp [Submodule.mem_colon_singleton]

private lemma associatedPrimeStacks_mem_associatedPrimes
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Ideal R}
    (h : IsAssociatedPrimeStacks R M p) : p ∈ associatedPrimes R M := by
  rcases h with ⟨hp, m, hm⟩
  rw [AssociatedPrimes.mem_iff]
  rw [colon_span_singleton_eq_colon_singleton] at hm
  exact ⟨hp, m, by rw [hm]; exact hp.radical.symm⟩

private lemma relativeAssassin_mem_fiber_associatedPrimes
    {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {q : PrimeSpectrum S}
    (h : q ∈ Module.relativeAssassin R S N) :
    ∃ Q : PrimeSpectrum (S ⊗[R]
        (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField),
      Q.asIdeal ∈ associatedPrimes
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
        ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N) ∧
      PrimeSpectrum.comap (algebraMap S
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q := by
  let A : Set (PrimeSpectrum S) := {q | q.asIdeal ∈
    associatedPrimes S (N ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)}
  let A' : Set (PrimeSpectrum S) := {q | ∃ Q : PrimeSpectrum
      (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField),
      Q.asIdeal ∈ associatedPrimes
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
        ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N) ∧
      PrimeSpectrum.comap (algebraMap S
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q}
  let Afin : Set (PrimeSpectrum S) := {q | q.asIdeal ∈ associatedPrimes S
      (N ⧸ ((PrimeSpectrum.comap (algebraMap R S) q).asIdeal.map (algebraMap R S) •
        (⊤ : Submodule S N)))}
  let A'fin : Set (PrimeSpectrum S) := {q | ∃ p : PrimeSpectrum R, q.asIdeal ∈ associatedPrimes S
      (N ⧸ (p.asIdeal.map (algebraMap R S) • (⊤ : Submodule S N)))}
  let B : Set (PrimeSpectrum S) := {q | ∃ (M : Type (max u v)) (_ : AddCommGroup M)
      (_ : Module R M), q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)}
  let Bfin : Set (PrimeSpectrum S) := {q | ∃ (M : Type (max u v)) (_ : AddCommGroup M)
      (_ : Module R M) (_ : Module.Finite R M), q.asIdeal ∈ associatedPrimes S (N ⊗[R] M)}
  have hcomp := Module.relativeAssassin_comparison R S N
    (A := A) (A' := A') (Afin := Afin) (A'fin := A'fin) (B := B) (Bfin := Bfin)
    rfl rfl rfl rfl rfl rfl
  rcases (Module.mem_relativeAssassin_iff (R := R) (S := S) (N := N)).mp h with ⟨m, hm⟩
  have hA : q ∈ A := by
    show q.asIdeal ∈ associatedPrimes S _
    exact associatedPrimeStacks_mem_associatedPrimes
      ⟨q.2, m, by rwa [colon_span_singleton_eq_colon_singleton]⟩
  rw [hcomp.1] at hA
  simpa [A'] using hA

/-- The base change of a module along `S ⟶ S ⊗[R] κ(p)`, computed as a tensor product over the
base ring. -/
private noncomputable def fiberModuleEquiv
    {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    (p : PrimeSpectrum R) :
    (S ⊗[R] p.asIdeal.ResidueField) ⊗[S] N ≃ₗ[S] N ⊗[R] p.asIdeal.ResidueField :=
  (TensorProduct.comm S _ N).trans
    (AlgebraTensorModule.cancelBaseChange R S S N p.asIdeal.ResidueField)

private lemma isUnit_algebraMap_tensor_residueField {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) {r : R} (hr : r ∉ p.asIdeal) :
    IsUnit (algebraMap R (S ⊗[R] p.asIdeal.ResidueField) r) := by
  let : Algebra p.asIdeal.ResidueField (S ⊗[R] p.asIdeal.ResidueField) :=
    Algebra.TensorProduct.rightAlgebra
  have hr0 : algebraMap R p.asIdeal.ResidueField r ≠ 0 := by
    intro hr0
    apply hr
    have : r ∈ RingHom.ker (algebraMap R p.asIdeal.ResidueField) :=
      RingHom.mem_ker.mpr hr0
    rwa [Ideal.ker_algebraMap_residueField] at this
  rw [IsScalarTower.algebraMap_apply R p.asIdeal.ResidueField (S ⊗[R] p.asIdeal.ResidueField)]
  exact (isUnit_iff_ne_zero.mpr hr0).map
    (algebraMap p.asIdeal.ResidueField (S ⊗[R] p.asIdeal.ResidueField))

private lemma exists_algebraMap_mul_eq_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) (c : S ⊗[R] p.asIdeal.ResidueField) :
    ∃ r ∉ p.asIdeal, ∃ s : S, algebraMap R (S ⊗[R] p.asIdeal.ResidueField) r * c =
      algebraMap S (S ⊗[R] p.asIdeal.ResidueField) s := by
  let comm := Algebra.TensorProduct.comm R S p.asIdeal.ResidueField
  obtain ⟨r, hr, s, hrs⟩ := Ideal.Fiber.exists_smul_eq_one_tmul (p := p.asIdeal) (comm c)
  refine ⟨r, hr, s, ?_⟩
  have h := congrArg comm.symm hrs
  have h₁ : comm.symm (r • comm c) = algebraMap R (S ⊗[R] p.asIdeal.ResidueField) r * c := by
    calc
      comm.symm (r • comm c) = r • comm.symm (comm c) :=
        comm.symm.toLinearEquiv.map_smul r (comm c)
      _ = r • c := by rw [comm.symm_apply_apply]
      _ = algebraMap R _ r * c := Algebra.smul_def _ _
  have h₂ : comm.symm (1 ⊗ₜ[R] s) = algebraMap S (S ⊗[R] p.asIdeal.ResidueField) s := by
    rw [Algebra.TensorProduct.comm_symm_tmul]
    rfl
  rwa [h₁, h₂] at h

private lemma relativeAssassin_fiber_exact_annihilator
    {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {q : PrimeSpectrum S} (h : q ∈ Module.relativeAssassin R S N)
    (Q : PrimeSpectrum (S ⊗[R]
      (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField))
    (hcomap : PrimeSpectrum.comap (algebraMap S
      (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q) :
    IsAssociatedPrimeStacks
      (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
      ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N)
      Q.asIdeal := by
  rcases (Module.mem_relativeAssassin_iff (R := R) (S := S) (N := N)).mp h with ⟨m, hm⟩
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let C := S ⊗[R] p.asIdeal.ResidueField
  let : IsScalarTower S C (C ⊗[S] N) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => by simp)
  let e : C ⊗[S] N ≃ₗ[S] N ⊗[R] p.asIdeal.ResidueField :=
    fiberModuleEquiv (R := R) (S := S) (N := N) p
  let z := e.symm m
  have hcolonS : (⊥ : Submodule S (N ⊗[R] p.asIdeal.ResidueField)).colon {m} = q.asIdeal := hm
  have hcomapIdeal : Q.asIdeal.comap (algebraMap S C) = q.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hcomap
  have hnot (r : R) (hr : r ∉ p.asIdeal) : algebraMap R C r ∉ Q.asIdeal := by
    intro hmem
    have hq : algebraMap R S r ∈ q.asIdeal := by
      rw [← hcomapIdeal, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply R S C r]
      exact hmem
    exact hr (by simpa [p] using hq)
  have hcolonC : (⊥ : Submodule C (C ⊗[S] N)).colon {z} = Q.asIdeal := by
    ext c
    simp only [Submodule.mem_colon_singleton]
    obtain ⟨r, hr, s, hrs'⟩ : ∃ r ∉ p.asIdeal, ∃ s : S, algebraMap R C r * c = algebraMap S C s :=
      exists_algebraMap_mul_eq_algebraMap p c
    have hscal : algebraMap R C r • (c • z) = (algebraMap S C s) • z := by
      rw [← mul_smul, hrs']
    have hmap : e ((algebraMap S C s) • z) = s • m := by
      show e ((algebraMap S C s) • e.symm m) = s • m
      rw [algebraMap_smul C s, e.map_smul, e.apply_symm_apply]
    have hsz : (algebraMap S C s) • z = 0 ↔ s ∈ q.asIdeal := by
      rw [← hcolonS, Submodule.mem_colon_singleton, Submodule.mem_bot, ← hmap,
        LinearEquiv.map_eq_zero_iff]
    have hsQ : (algebraMap S C s ∈ Q.asIdeal) ↔ s ∈ q.asIdeal := by
      rw [← hcomapIdeal]
      rfl
    constructor
    · intro hcz
      have hsann : s ∈ q.asIdeal := hsz.mp (hscal.symm.trans (by rw [hcz, smul_zero]))
      have hprod : algebraMap R C r * c ∈ Q.asIdeal := by rw [hrs']; exact hsQ.mpr hsann
      exact (Q.2.mul_mem_iff_mem_or_mem.mp hprod).resolve_left (hnot r hr)
    · intro hcQ
      have hsann : s ∈ q.asIdeal :=
        hsQ.mp (by rw [← hrs']; exact Q.asIdeal.mul_mem_left _ hcQ)
      have hunit : IsUnit (algebraMap R C r) := isUnit_algebraMap_tensor_residueField p hr
      simpa using hunit.smul_eq_zero.mp (hscal.trans (hsz.mpr hsann))
  refine ⟨Q.2, z, ?_⟩
  rw [colon_span_singleton_eq_colon_singleton z]
  simpa [C, p] using hcolonC

private lemma relativeAssassin_exists_fiber_associatedPrimeStacks
    {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {q : PrimeSpectrum S} (h : q ∈ Module.relativeAssassin R S N) :
    ∃ Q : PrimeSpectrum (S ⊗[R]
        (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField),
      IsAssociatedPrimeStacks
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
        ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N)
        Q.asIdeal ∧
      PrimeSpectrum.comap (algebraMap S
        (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q := by
  obtain ⟨Q, -, hcomap⟩ := relativeAssassin_mem_fiber_associatedPrimes h
  exact ⟨Q, relativeAssassin_fiber_exact_annihilator h Q hcomap, hcomap⟩

private lemma relativeAssassin_of_fiber_associatedPrimeStacks
    {R : Type u} {S : Type v} {N : Type w} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    {q : PrimeSpectrum S}
    (Q : PrimeSpectrum (S ⊗[R]
      (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField))
    (hQ : IsAssociatedPrimeStacks
      (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)
      ((S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField) ⊗[S] N)
      Q.asIdeal)
    (hcomap : PrimeSpectrum.comap (algebraMap S
      (S ⊗[R] (PrimeSpectrum.comap (algebraMap R S) q).asIdeal.ResidueField)) Q = q) :
    q ∈ Module.relativeAssassin R S N := by
  rcases hQ with ⟨_, z, hz⟩
  let p := PrimeSpectrum.comap (algebraMap R S) q
  let C := S ⊗[R] p.asIdeal.ResidueField
  let : IsScalarTower S C (C ⊗[S] N) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => by simp)
  have hcolonC : (⊥ : Submodule C (C ⊗[S] N)).colon {z} = Q.asIdeal :=
    (colon_span_singleton_eq_colon_singleton z).symm.trans hz
  let e : C ⊗[S] N ≃ₗ[S] N ⊗[R] p.asIdeal.ResidueField :=
    fiberModuleEquiv (R := R) (S := S) (N := N) p
  have hecolon : (⊥ : Submodule S (N ⊗[R] p.asIdeal.ResidueField)).colon {e z} =
      (⊥ : Submodule S (C ⊗[S] N)).colon {z} := by
    ext r
    simp only [Submodule.mem_colon_singleton]
    show r • e z = 0 ↔ r • z = 0
    rw [← e.map_smul, LinearEquiv.map_eq_zero_iff]
  refine (Module.mem_relativeAssassin_iff (R := R) (S := S) (N := N)).mpr ⟨e z, ?_⟩
  calc
    (⊥ : Submodule S (N ⊗[R] p.asIdeal.ResidueField)).colon {e z} =
        (⊥ : Submodule S (C ⊗[S] N)).colon {z} := hecolon
    _ = (Q.asIdeal).comap (algebraMap S C) := by
      ext r
      simp only [Ideal.mem_comap, ← hcolonC, Submodule.mem_colon_singleton,
        Submodule.mem_bot]
      rw [algebraMap_smul C r z]
    _ = q.asIdeal := congrArg PrimeSpectrum.asIdeal hcomap

private lemma isAssociatedPrimeStacks_iff_comap
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : S ≃+* R) (l : M ≃+ N)
    (hl : ∀ (s : S) (m : M), l (e s • m) = s • l m) (p : Ideal R) :
    IsAssociatedPrimeStacks R M p ↔
      IsAssociatedPrimeStacks S N (p.comap e.toRingHom) := by
  constructor
  · rintro ⟨hp, m, hm⟩
    refine ⟨Ideal.comap_isPrime _ _, l m, ?_⟩
    ext s
    rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot, Ideal.mem_comap, ← hm,
      Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← hl, map_eq_zero_iff _ l.injective]
    rfl
  · rintro ⟨hp, n, hn⟩
    have hp' : p.IsPrime := by
      have h := Ideal.comap_isPrime e.symm.toRingHom (p.comap e.toRingHom)
      have he : (p.comap e.toRingHom).comap e.symm.toRingHom = p := by
        ext r
        show e (e.symm r) ∈ p ↔ r ∈ p
        rw [e.apply_symm_apply]
      rwa [he] at h
    refine ⟨hp', l.symm n, ?_⟩
    ext r
    obtain ⟨s, rfl⟩ := e.surjective r
    rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot]
    have h := SetLike.ext_iff.mp hn s
    simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot, Ideal.mem_comap] at h
    change s • n = 0 ↔ e s ∈ p at h
    rw [← h, ← l.apply_symm_apply n, ← hl, map_eq_zero_iff _ l.injective]
    simp

private lemma primeIdealOf_spec_top (R : CommRingCat.{u}) (p : Spec R) :
    (isAffineOpen_top (Spec R)).primeIdealOf ⟨p, trivial⟩ =
      p.comap (Scheme.ΓSpecIso R).hom.hom := by
  apply (isAffineOpen_top (Spec R)).fromSpec.isOpenEmbedding.injective
  rw [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv]
  show p = (Spec.map (Scheme.ΓSpecIso R).hom ≫
    Spec.map (Scheme.ΓSpecIso R).inv) p
  simp

private lemma isAssociatedPrimeStacks_restrict_iff
    {X : Scheme.{u}} {R : CommRingCat.{u}} (g : Spec R ⟶ X) [IsOpenImmersion g]
    (F : X.Modules) (p : Spec R) :
    IsAssociatedPrimeStacks R Γ(F.restrict g, ⊤) p.asIdeal ↔
      IsAssociatedPrimeStacks Γ(X, g ''ᵁ ⊤) Γ(F, g ''ᵁ ⊤)
        (((isAffineOpen_top (Spec R)).image_of_isOpenImmersion g).primeIdealOf
          ⟨g p, by exact ⟨p, trivial, rfl⟩⟩).asIdeal := by
  let W := g ''ᵁ (⊤ : (Spec R).Opens)
  let e : Γ(X, W) ≅ R := (g.appIso ⊤) ≪≫ Scheme.ΓSpecIso R
  let l : Γ(F.restrict g, ⊤) ≃+ Γ(F, W) :=
    { toFun := (F.restrictAppIso g ⊤).hom
      invFun := (F.restrictAppIso g ⊤).inv
      left_inv m := ConcreteCategory.congr_hom (F.restrictAppIso g ⊤).hom_inv_id m
      right_inv m := ConcreteCategory.congr_hom (F.restrictAppIso g ⊤).inv_hom_id m
      map_add' := map_add _ }
  have hl (s : Γ(X, W)) (m : Γ(F.restrict g, ⊤)) :
      l (e.hom s • m) = s • l m := by
    rw [Scheme.Modules.smul_Spec_def]
    simp only [Opens.leTop, homOfLE_refl, op_id]
    show (F.restrictAppIso g ⊤).hom
      ((Scheme.ΓSpecIso R).inv (e.hom s) • m) = _
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [e, Iso.trans_hom, ← CommRingCat.comp_apply, Category.assoc,
      Iso.hom_inv_id, Category.id_comp]
    rfl
  have hprime := IsAffineOpen.comap_primeIdealOf_appLE (f := g)
    W ((isAffineOpen_top (Spec R)).image_of_isOpenImmersion g)
    ⊤ (isAffineOpen_top (Spec R)) (by simp [W]) (x := p) trivial
  rw [primeIdealOf_spec_top] at hprime
  have hmap : g.appLE W ⊤ (by simp [W]) = (g.appIso ⊤).hom := by
    rw [Scheme.Hom.appIso_hom']
  rw [hmap] at hprime
  have heq : (p.comap e.hom.hom).asIdeal =
      (((isAffineOpen_top (Spec R)).image_of_isOpenImmersion g).primeIdealOf
        ⟨g p, ⟨p, trivial, rfl⟩⟩).asIdeal :=
    congrArg PrimeSpectrum.asIdeal hprime
  rw [← heq]
  exact isAssociatedPrimeStacks_iff_comap e.commRingCatIsoToRingEquiv l hl p.asIdeal

/-- Global sections of the pullback of a quasi-coherent module along a morphism of affine
schemes are the extension of scalars of its global sections. -/
public noncomputable def specPullbackSectionsIso
    (A B : CommRingCat.{u}) (g : A ⟶ B) (G : (Spec A).Modules)
    [G.IsQuasicoherent] :
    (moduleSpecΓFunctor (R := B)).obj ((Scheme.Modules.pullback (Spec.map g)).obj G) ≅
      (ModuleCat.extendScalars g.hom).obj ((moduleSpecΓFunctor (R := A)).obj G) := by
  let M := (modulesSpecToSheaf.obj G).presheaf.obj (Opposite.op ⊤)
  have hG : IsIso G.fromTildeΓ := inferInstance
  let eG : (tilde.functor (R := A)).obj M ≅ G :=
    @CategoryTheory.asIso _ _ _ _ G.fromTildeΓ hG
  let e : (Scheme.Modules.pullback (Spec.map g)).obj G ≅
      (tilde.functor (R := B)).obj ((ModuleCat.extendScalars g.hom).obj M) :=
    (Scheme.Modules.pullback (Spec.map g)).mapIso eG.symm ≪≫
      (pullbackTildeIso A B g).app M
  exact (moduleSpecΓFunctor (R := B)).mapIso e ≪≫
    (tilde.toTildeΓNatIso (R := B)).symm.app ((ModuleCat.extendScalars g.hom).obj M)

/-- Global sections of the restriction of a pullback to an affine chart of the source, as the
base change of the sections over an affine open of the target. -/
private noncomputable def chartPullbackSectionsIso
    {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (B : CommRingCat.{u})
    (a : Γ(X, U) ⟶ B) (j : Spec B ⟶ Y) [IsOpenImmersion j]
    (hj : j ≫ g = Spec.map a ≫ hU.fromSpec) :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pullback g).obj F).restrict j) ≅
      (ModuleCat.extendScalars a.hom).obj (ModuleCat.of Γ(X, U) Γ(F, U)) := by
  let G := F.restrict hU.fromSpec
  let e : ((Scheme.Modules.pullback g).obj F).restrict j ≅
      (Scheme.Modules.pullback (Spec.map a)).obj G :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
    (Scheme.Modules.pullbackComp j g).app F ≪≫
    (Scheme.Modules.pullbackCongr hj).app F ≪≫
    ((Scheme.Modules.pullbackComp (Spec.map a) hU.fromSpec).app F).symm ≪≫
    (Scheme.Modules.pullback (Spec.map a)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.fromSpec).app F).symm
  exact moduleSpecΓFunctor.mapIso e ≪≫
    specPullbackSectionsIso Γ(X, U) B a G ≪≫
    (ModuleCat.extendScalars a.hom).mapIso (affineSectionsLinearEquiv F hU).toModuleIso

private lemma SpecMap_algebraMap_residueField_comp_fromSpec {S : Scheme.{u}} {V : S.Opens}
    (hV : IsAffineOpen V) (p : PrimeSpectrum Γ(S, V)) :
    letI pt : Spec Γ(S, V) := p
    Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) p.asIdeal.ResidueField)) ≫ hV.fromSpec =
      Spec.map (asIso (hV.fromSpec.residueFieldMap pt) ≪≫
        Scheme.Spec.residueFieldIso Γ(S, V) pt).hom ≫ S.fromSpecResidueField (hV.fromSpec pt) := by
  let R := Γ(S, V)
  let pt : ↥(Spec R) := p
  let K := p.asIdeal.ResidueField
  let s := hV.fromSpec pt
  let b : Spec (.of K) ⟶ Spec (S.residueField s) :=
    Spec.map (asIso (hV.fromSpec.residueFieldMap pt) ≪≫ Scheme.Spec.residueFieldIso R pt).hom
  have h1 : Spec.map (Scheme.Spec.residueFieldIso R pt).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K)) = (Spec R).fromSpecResidueField pt :=
    Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R pt
  have h2 : Spec.map (hV.fromSpec.residueFieldMap pt) ≫ S.fromSpecResidueField s =
      (Spec R).fromSpecResidueField pt ≫ hV.fromSpec :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField hV.fromSpec pt
  have hbeq : b = Spec.map (Scheme.Spec.residueFieldIso R pt).hom ≫
      Spec.map (hV.fromSpec.residueFieldMap pt) := by
    rw [show b = Spec.map (hV.fromSpec.residueFieldMap pt ≫
      (Scheme.Spec.residueFieldIso R pt).hom) from rfl, Spec.map_comp]
  have hid : Spec.map (Scheme.Spec.residueFieldIso R pt).hom ≫
      Spec.map (Scheme.Spec.residueFieldIso R pt).inv = 𝟙 _ := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  calc Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ hV.fromSpec
      = (Spec.map (Scheme.Spec.residueFieldIso R pt).hom ≫
          Spec.map (Scheme.Spec.residueFieldIso R pt).inv) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ hV.fromSpec := by
        rw [hid, Category.id_comp]
    _ = Spec.map (Scheme.Spec.residueFieldIso R pt).hom ≫
          (Spec.map (Scheme.Spec.residueFieldIso R pt).inv ≫
            Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ hV.fromSpec := by
        simp only [Category.assoc]
    _ = Spec.map (Scheme.Spec.residueFieldIso R pt).hom ≫
          (Spec R).fromSpecResidueField pt ≫ hV.fromSpec := by rw [h1]
    _ = Spec.map (Scheme.Spec.residueFieldIso R pt).hom ≫
          Spec.map (hV.fromSpec.residueFieldMap pt) ≫ S.fromSpecResidueField s := by rw [h2]
    _ = b ≫ S.fromSpecResidueField s := by rw [hbeq, Category.assoc]

private lemma exists_fiberChart {X S : Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (q : PrimeSpectrum Γ(X, U)) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    let p := PrimeSpectrum.comap (algebraMap Γ(S, V) Γ(X, U)) q
    let C := Γ(X, U) ⊗[Γ(S, V)] p.asIdeal.ResidueField
    ∃ (s : S) (j : Spec (.of C) ⟶ f.fiber s),
      s = f (hU.fromSpec q) ∧ IsOpenImmersion j ∧
      j ≫ f.fiberι s = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) C)) ≫ hU.fromSpec ∧
      Set.range (j ≫ f.fiberι s) = Set.range hU.fromSpec ∩ f ⁻¹' {s} := by
  let R := Γ(S, V)
  let A := Γ(X, U)
  let : Algebra R A := (f.appLE V U hUV).hom.toAlgebra
  let p := PrimeSpectrum.comap (algebraMap R A) q
  let pt : ↥(Spec R) := p
  let K := p.asIdeal.ResidueField
  let C := A ⊗[R] K
  let s := hV.fromSpec pt
  let e : S.residueField s ≅ CommRingCat.of K :=
    asIso (hV.fromSpec.residueFieldMap pt) ≪≫ Scheme.Spec.residueFieldIso R pt
  let b : Spec (.of K) ⟶ Spec (S.residueField s) := Spec.map e.hom
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ hV.fromSpec =
      b ≫ S.fromSpecResidueField s :=
    SpecMap_algebraMap_residueField_comp_fromSpec hV p
  have ha : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ hV.fromSpec = hU.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  have hbiso : IsIso b := by
    rw [show b = (Scheme.Spec.mapIso e.op).hom from rfl]
    infer_instance
  have : IsOpenImmersion b := inferInstance
  let m := pullback.map (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) f (S.fromSpecResidueField s)
    hU.fromSpec b hV.fromSpec ha hb
  have hmopen : IsOpenImmersion m := inferInstance
  let j := (pullbackSpecIso R A K).inv ≫ m
  have hjopen : IsOpenImmersion j := inferInstance
  have hj : j ≫ f.fiberι s =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ hU.fromSpec := by
    dsimp only [j, m, Scheme.Hom.fiberι, pullback.map]
    rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst']
  refine ⟨s, j, congrArg (fun k : Spec A ⟶ S => k q) ha, hjopen, hj, ?_⟩
  have hm : Set.range m =
      (f.fiberι s) ⁻¹' Set.range hU.fromSpec := by
    rw [Scheme.Pullback.range_map]
    have hrb : Set.range b = Set.univ :=
      (Scheme.Spec.mapIso e.op).schemeIsoToHomeo.surjective.range_eq
    rw [hrb]
    exact Set.inter_univ _
  have hr : Set.range j = Set.range m := by
    have hsurj : Function.Surjective (pullbackSpecIso R A K).inv :=
      (pullbackSpecIso R A K).schemeIsoToHomeo.symm.surjective
    rw [show (j : Spec (.of C) → f.fiber s) = m ∘ (pullbackSpecIso R A K).inv from rfl,
      Set.range_comp, hsurj.range_eq, Set.image_univ]
  have hrj : Set.range (j ≫ f.fiberι s) = f.fiberι s '' Set.range j := by
    apply Set.eq_of_subset_of_subset
    · rintro y ⟨z, hz⟩
      exact ⟨j z, ⟨z, rfl⟩, (Scheme.Hom.comp_apply j (f.fiberι s) z).symm.trans hz⟩
    · rintro y ⟨w, ⟨z, hz⟩, hw⟩
      exact ⟨z, (Scheme.Hom.comp_apply j (f.fiberι s) z).trans
        ((congrArg (fun t => f.fiberι s t) hz).trans hw)⟩
  have hkey : f.fiberι s '' (⇑(f.fiberι s) ⁻¹' Set.range hU.fromSpec) =
      Set.range hU.fromSpec ∩ f ⁻¹' {s} := by
    rw [Set.image_preimage_eq_inter_range, f.range_fiberι]
  exact hrj.trans ((congrArg (fun T => f.fiberι s '' T) (hr.trans hm)).trans hkey)

/-- Extension of scalars along the structure map of an algebra is the tensor product with the
algebra. -/
private noncomputable def extendScalarsAlgebraMapIso
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (M : ModuleCat.{w} R) :
    (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let : IsScalarTower R S S' := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let e : S' ≃ₗ[S] S := LinearEquiv.refl S S
  exact (AlgebraTensorModule.congr e (LinearEquiv.refl R M)).toModuleIso

private lemma isAssociatedPrimeStacks_iff_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) (p : Ideal R) :
    IsAssociatedPrimeStacks R M p ↔ IsAssociatedPrimeStacks R N p := by
  have h : p.comap (RingEquiv.refl R).toRingHom = p := by ext; rfl
  simpa only [h] using
    isAssociatedPrimeStacks_iff_comap (RingEquiv.refl R) e.toAddEquiv e.map_smul p

private lemma isAssociatedPoint_of_isAssociatedPrimeStacks_restrict
    {X : Scheme.{u}} {R : CommRingCat.{u}} (g : Spec R ⟶ X) [IsOpenImmersion g]
    (F : X.Modules) [F.IsQuasicoherent] (p : Spec R)
    (h : IsAssociatedPrimeStacks R Γ(F.restrict g, ⊤) p.asIdeal) :
    Stacks.Divisors.IsAssociatedPoint F (g p) :=
  isAssociatedPoint_of_isAssociatedPrime_sections F (g ''ᵁ ⊤)
    ((isAffineOpen_top (Spec R)).image_of_isOpenImmersion g) ⟨p, trivial, rfl⟩
    ((isAssociatedPrimeStacks_restrict_iff g F p).mp h)

private lemma isAssociatedPrimeStacks_restrict_of_isAssociatedPoint
    {X : Scheme.{u}} [IsLocallyNoetherian X] {R : CommRingCat.{u}}
    (g : Spec R ⟶ X) [IsOpenImmersion g]
    (F : X.Modules) [F.IsQuasicoherent] (p : Spec R)
    (h : Stacks.Divisors.IsAssociatedPoint F (g p)) :
    IsAssociatedPrimeStacks R Γ(F.restrict g, ⊤) p.asIdeal :=
  (isAssociatedPrimeStacks_restrict_iff g F p).mpr
    ((isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
      F (g ''ᵁ ⊤) ((isAffineOpen_top (Spec R)).image_of_isOpenImmersion g)
      ⟨p, trivial, rfl⟩).mpr h)

/-- Associated primes of the sections of the restriction of a pullback to an affine chart are
those of the base change of the sections over an affine open. -/
private lemma isAssociatedPrimeStacks_chart_iff
    {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (C : CommRingCat.{u}) [Algebra Γ(X, U) C]
    (j : Spec C ⟶ Y) [IsOpenImmersion j]
    (hj : j ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) C)) ≫ hU.fromSpec)
    (Q : Ideal C) :
    IsAssociatedPrimeStacks C Γ(((Scheme.Modules.pullback g).obj F).restrict j, ⊤) Q ↔
      IsAssociatedPrimeStacks C (C ⊗[Γ(X, U)] Γ(F, U)) Q :=
  isAssociatedPrimeStacks_iff_of_linearEquiv
    (chartPullbackSectionsIso g F U hU C (CommRingCat.ofHom (algebraMap Γ(X, U) C)) j hj ≪≫
    extendScalarsAlgebraMapIso (S := C) (ModuleCat.of Γ(X, U) Γ(F, U))).toLinearEquiv Q

/-- A point of a chart of the fibre maps to the point of `X` given by the contraction. -/
private lemma apply_eq_fromSpec_comap
    {X Y : Scheme.{u}} (g : Y ⟶ X) (U : X.Opens) (hU : IsAffineOpen U) (C : CommRingCat.{u})
    [Algebra Γ(X, U) C] (j : Spec C ⟶ Y)
    (hj : j ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) C)) ≫ hU.fromSpec)
    (Q : PrimeSpectrum C) :
    g (j Q) = hU.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, U) C) Q) :=
  congrArg (fun k : Spec (CommRingCat.of C) ⟶ X => k Q) hj

/-- **Stacks Project, Tag 0CU5.** A relative associated prime of the sections on an affine open
gives a relative associated point of the sheaf. -/
@[stacks 0CU5 "forward implication"]
public theorem mem_relativeAssassin_of_mem_relativeAssassin_sections
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ U) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI : Module Γ(S, V) Γ(F, U) :=
      Module.compHom Γ(F, U) (f.appLE V U hUV).hom
    letI : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
      IsScalarTower.of_compHom Γ(S, V) Γ(X, U) Γ(F, U)
    (hU.primeIdealOf ⟨x, hx⟩) ∈
      Module.relativeAssassin Γ(S, V) Γ(X, U) Γ(F, U) →
      x ∈ Stacks.Divisors.relativeAssassin f F := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module Γ(S, V) Γ(F, U) := Module.compHom Γ(F, U) (f.appLE V U hUV).hom
  let : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
    IsScalarTower.of_compHom Γ(S, V) Γ(X, U) Γ(F, U)
  intro h
  let q := hU.primeIdealOf ⟨x, hx⟩
  let p := PrimeSpectrum.comap (algebraMap Γ(S, V) Γ(X, U)) q
  let C := Γ(X, U) ⊗[Γ(S, V)] p.asIdeal.ResidueField
  obtain ⟨Q, hQ, hcomap⟩ := relativeAssassin_exists_fiber_associatedPrimeStacks h
  obtain ⟨s, j, -, hjopen, hj, -⟩ := exists_fiberChart f U V hU hV hUV q
  change Spec (CommRingCat.of C) ⟶ f.fiber s at j
  let := hjopen
  let G := (Scheme.Modules.pullback (f.fiberι s)).obj F
  have : G.IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (f.fiberι s) F inferInstance
  have hQ' := (isAssociatedPrimeStacks_chart_iff (f.fiberι s) F U hU (.of C) j hj Q.asIdeal).mpr hQ
  refine (Stacks.Divisors.mem_relativeAssassin f F x).mpr
    ⟨s, j Q, isAssociatedPoint_of_isAssociatedPrimeStacks_restrict j G Q hQ', ?_⟩
  have hproj := apply_eq_fromSpec_comap (f.fiberι s) U hU (.of C) j hj Q
  rw [hcomap] at hproj
  exact hproj.trans (hU.fromSpec_primeIdealOf ⟨x, hx⟩)

/-- **Stacks Project, Tag 0CU5.** With locally Noetherian fibres, the relative associated
primes of affine sections are exactly the relative associated points of the sheaf. -/
@[stacks 0CU5 "locally Noetherian equivalence"]
public theorem mem_relativeAssassin_sections_iff_of_locallyNoetherian_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (V : S.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (hf : ∀ s : S, IsLocallyNoetherian (f.fiber s))
    {x : X} (hx : x ∈ U) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    letI : Module Γ(S, V) Γ(F, U) :=
      Module.compHom Γ(F, U) (f.appLE V U hUV).hom
    letI : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
      IsScalarTower.of_compHom Γ(S, V) Γ(X, U) Γ(F, U)
    (hU.primeIdealOf ⟨x, hx⟩) ∈
      Module.relativeAssassin Γ(S, V) Γ(X, U) Γ(F, U) ↔
      x ∈ Stacks.Divisors.relativeAssassin f F := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module Γ(S, V) Γ(F, U) := Module.compHom Γ(F, U) (f.appLE V U hUV).hom
  let : IsScalarTower Γ(S, V) Γ(X, U) Γ(F, U) :=
    IsScalarTower.of_compHom Γ(S, V) Γ(X, U) Γ(F, U)
  refine ⟨mem_relativeAssassin_of_mem_relativeAssassin_sections f F U V hU hV hUV hx, fun h => ?_⟩
  let q := hU.primeIdealOf ⟨x, hx⟩
  let p := PrimeSpectrum.comap (algebraMap Γ(S, V) Γ(X, U)) q
  let C := Γ(X, U) ⊗[Γ(S, V)] p.asIdeal.ResidueField
  obtain ⟨s, j, hs, hjopen, hj, hrange⟩ := exists_fiberChart f U V hU hV hUV q
  change Spec (CommRingCat.of C) ⟶ f.fiber s at j
  let := hjopen
  obtain ⟨t, z, hz, hzx⟩ := (Stacks.Divisors.mem_relativeAssassin f F x).mp h
  have hxt : f x = t := by
    have hm : x ∈ Set.range (f.fiberι t) := ⟨z, hzx⟩
    rwa [f.range_fiberι] at hm
  have hst : s = t := hs.trans
    ((congrArg f (hU.fromSpec_primeIdealOf ⟨x, hx⟩)).trans hxt)
  cases hst
  obtain ⟨Q, hQx⟩ : x ∈ Set.range (j ≫ f.fiberι s) := by
    rw [hrange]
    exact ⟨⟨q, hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩, hxt⟩
  have hproj := apply_eq_fromSpec_comap (f.fiberι s) U hU (.of C) j hj Q
  have hcomap : PrimeSpectrum.comap (algebraMap Γ(X, U) C) Q = q :=
    hU.fromSpec.isOpenEmbedding.injective
      (hproj.symm.trans (hQx.trans (hU.fromSpec_primeIdealOf ⟨x, hx⟩).symm))
  have hjQz : j Q = z := (f.fiberι s).isEmbedding.injective (hQx.trans hzx.symm)
  let G := (Scheme.Modules.pullback (f.fiberι s)).obj F
  have : G.IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (f.fiberι s) F inferInstance
  have : IsLocallyNoetherian (f.fiber s) := hf s
  have hQ' := isAssociatedPrimeStacks_restrict_of_isAssociatedPoint j G Q (hjQz.symm ▸ hz)
  exact relativeAssassin_of_fiber_associatedPrimeStacks Q
    ((isAssociatedPrimeStacks_chart_iff (f.fiberι s) F U hU (.of C) j hj Q.asIdeal).mp hQ') hcomap

end AlgebraicGeometry

end
