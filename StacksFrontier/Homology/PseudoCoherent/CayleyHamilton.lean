module

public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import StacksFrontier.Homology.PseudoCoherent.Basic

/-!
# Cayley–Hamilton for pseudo-coherent complexes

Let `A` be a commutative ring and `M` a pseudo-coherent object of `D(A)`. Every endomorphism
`φ : M ⟶ M` in `D(A)` satisfies, on each cohomology module `Hⁱ(M)`, a monic polynomial: represent
`M` by a bounded-above complex `P` of finite free `A`-modules; `P` is K-projective, so `φ` comes
from a chain endomorphism `f` of `P`; Cayley–Hamilton on the finite module `Pⁱ` gives a monic `χ`
with `χ(fⁱ) = 0`, and `Hⁱ(φ)` is induced by `fⁱ` on the subquotient `Hⁱ(P)` of `Pⁱ`.

The cohomology modules of a pseudo-coherent complex need not be finite over `A` (`A` is not
assumed coherent), so this is not Cayley–Hamilton for `Hⁱ(M)` itself.

## Main results

* `StacksDraft.PseudoCoherence.comp_aeval_eq_aeval_comp`: a linear map intertwining two
  endomorphisms intertwines their polynomial expressions.
* `StacksDraft.PseudoCoherence.exists_monic_aeval_homologyFunctor_map_eq_zero`: an endomorphism of
  a pseudo-coherent object of `D(A)` satisfies a monic polynomial on each cohomology module.
* `StacksDraft.PseudoCoherence.exists_monic_aeval_homologyMap_eq_zero`: the same for a chain
  endomorphism of a complex that is pseudo-coherent in `D(A)`.
* `StacksDraft.PseudoCoherence.exists_ideal_finite_quotient_homologyMap_eq_zero`: if a finite type
  `A`-algebra `R` acts on such a complex, each cohomology module is killed by an ideal `J` with
  `R ⧸ J` finite over `A`. This is the algebraic heart of the per-degree support clause of
  Stacks 0DIR over an affine `X = Spec R`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Polynomial

namespace StacksDraft.PseudoCoherence

universe u v

/-- A linear map `a` with `a ∘ g = h ∘ a` satisfies `a ∘ p(g) = p(h) ∘ a` for every polynomial
`p`. -/
theorem comp_aeval_eq_aeval_comp {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (a : M →ₗ[R] N) {g : Module.End R M} {h : Module.End R N}
    (hgh : a ∘ₗ g = h ∘ₗ a) (p : R[X]) : a ∘ₗ aeval g p = aeval h p ∘ₗ a := by
  induction p using Polynomial.induction_on with
  | C r => ext x; simp
  | add p q hp hq => rw [map_add, map_add, LinearMap.comp_add, LinearMap.add_comp, hp, hq]
  | monomial n r ih =>
    rw [pow_succ, ← mul_assoc, map_mul (aeval g), map_mul (aeval h), aeval_X, aeval_X,
      Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih, LinearMap.comp_assoc, hgh,
      ← LinearMap.comp_assoc]

/-- **Cayley–Hamilton for pseudo-coherent complexes.** Let `A` be a commutative ring, `M` a
pseudo-coherent object of `D(A)` and `φ : M ⟶ M`. For every `i` there is a monic `p ∈ A[X]` with
`p(Hⁱ(φ)) = 0` on `Hⁱ(M)`. -/
theorem exists_monic_aeval_homologyFunctor_map_eq_zero {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{v} A)] {M : DerivedCategory (ModuleCat.{v} A)}
    (hM : IsPseudoCoherent M) (φ : M ⟶ M) (i : ℤ) :
    ∃ p : A[X], p.Monic ∧
      aeval ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map φ).hom p = 0 := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hM
  obtain ⟨b, hb⟩ := hP.upperBound
  have (j : ℤ) : Projective (P.X j) := by
    have := (hP.finiteFree j).2
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis A (P.X j))
  have := CochainComplex.isKProjective_of_projective P b
  obtain ⟨f, hf⟩ := exists_chainMap_of_isKProjective P P (e.hom ≫ φ ≫ e.inv)
  have := (hP.finiteFree i).1
  obtain ⟨p, hmon, hp⟩ := LinearMap.exists_monic_and_aeval_eq_zero A (f.f i).hom
  refine ⟨p, hmon, ?_⟩
  -- `p` kills the map induced by `f` on the cycles, a submodule of `Pⁱ`.
  have hcyc : aeval (HomologicalComplex.cyclesMap f i).hom p = 0 := by
    have h := comp_aeval_eq_aeval_comp (P.iCycles i).hom
      (g := (HomologicalComplex.cyclesMap f i).hom)
      (h := (f.f i).hom) (congrArg ModuleCat.Hom.hom (HomologicalComplex.cyclesMap_i f i)) p
    rw [hp, LinearMap.zero_comp] at h
    ext x
    apply (ModuleCat.mono_iff_injective (P.iCycles i)).1 inferInstance
    simpa using LinearMap.congr_fun h x
  -- hence the map induced on the homology, a quotient of the cycles.
  have hhom : aeval (HomologicalComplex.homologyMap f i).hom p = 0 := by
    have h := comp_aeval_eq_aeval_comp (P.homologyπ i).hom
      (g := (HomologicalComplex.cyclesMap f i).hom) (h := (HomologicalComplex.homologyMap f i).hom)
      (congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyπ_naturality f i).symm) p
    rw [hcyc, LinearMap.comp_zero] at h
    ext x
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (P.homologyπ i)).1 inferInstance x
    simpa using (LinearMap.congr_fun h y).symm
  -- transport along `Hⁱ(M) ≅ Hⁱ(P)`.
  let u : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj M ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) i).obj P :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) i).app P
  have hu : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map φ ≫ u.hom =
      u.hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) i).map f := by
    have h := (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) i).hom.naturality f
    rw [Functor.comp_map, hf] at h
    simp only [u, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom, Category.assoc,
      ← h, ← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
  have h := comp_aeval_eq_aeval_comp u.hom.hom
    (g := ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map φ).hom)
    (h := (HomologicalComplex.homologyMap f i).hom) (congrArg ModuleCat.Hom.hom hu) p
  ext x
  apply (ModuleCat.mono_iff_injective u.hom).1 inferInstance
  have hx := LinearMap.congr_fun h x
  have h0 := LinearMap.congr_fun hhom (u.hom.hom x)
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hx h0 ⊢
  rw [hx, map_zero]
  exact h0

/-- **Cayley–Hamilton for chain endomorphisms of pseudo-coherent complexes.** Let `N` be a complex
of modules over a commutative ring `A` that is pseudo-coherent in `D(A)`, and `f : N ⟶ N` a chain
map. For every `i` there is a monic `p ∈ A[X]` with `p(Hⁱ(f)) = 0` on `Hⁱ(N)`. -/
theorem exists_monic_aeval_homologyMap_eq_zero {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{v} A)] {N : CochainComplex (ModuleCat.{v} A) ℤ}
    (hN : IsPseudoCoherent (DerivedCategory.Q.obj N)) (f : N ⟶ N) (i : ℤ) :
    ∃ p : A[X], p.Monic ∧ aeval (HomologicalComplex.homologyMap f i).hom p = 0 := by
  obtain ⟨p, hmon, hp⟩ := exists_monic_aeval_homologyFunctor_map_eq_zero hN
    (DerivedCategory.Q.map f) i
  refine ⟨p, hmon, ?_⟩
  let u := (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) i).app N
  have hu : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map (DerivedCategory.Q.map f) ≫
      u.hom = u.hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) i).map f :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) i).hom.naturality f
  have h := comp_aeval_eq_aeval_comp u.hom.hom
    (g := ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (DerivedCategory.Q.map f)).hom)
    (h := (HomologicalComplex.homologyMap f i).hom) (congrArg ModuleCat.Hom.hom hu) p
  rw [hp, LinearMap.comp_zero] at h
  ext x
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective u.hom).1 inferInstance x
  exact (LinearMap.congr_fun h y).symm

/-- **The cohomology of a pseudo-coherent complex with an action of a finite type algebra is
supported finitely over the base.** Let `A` be a commutative ring, `R` a commutative `A`-algebra
of finite type, and `N` a complex of `A`-modules, pseudo-coherent in `D(A)`, on which `R` acts by
chain endomorphisms extending the action of `A` (a ring map `ρ : R → End(N)` with
`ρ(a) = a • 𝟙`). For every `i` there is an ideal `J ⊆ R` with `R ⧸ J` finite over `A` acting by
zero on `Hⁱ(N)`. For `N = RΓ(Spec R, K)` this is the support clause of Stacks 0DIR over an affine
base: `Supp Hⁱ(K) ⊆ V(J)`, which is finite over `A`. -/
theorem exists_ideal_finite_quotient_homologyMap_eq_zero {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat.{v} A)] {R : Type*} [CommRing R] [Algebra A R]
    [Algebra.FiniteType A R] {N : CochainComplex (ModuleCat.{v} A) ℤ}
    (hN : IsPseudoCoherent (DerivedCategory.Q.obj N)) (ρ : R →+* End N)
    (hρ : ∀ a : A, (ρ (algebraMap A R a)).asHom = a • (𝟙 N : N ⟶ N)) (i : ℤ) :
    ∃ J : Ideal R, Module.Finite A (R ⧸ J) ∧
      ∀ r ∈ J, HomologicalComplex.homologyMap (ρ r).asHom i = 0 := by
  classical
  -- the action of `R` on `Hⁱ(N)`, as an `A`-algebra map
  let σ : R →ₐ[A] Module.End A (N.homology i) :=
    { toFun r := (HomologicalComplex.homologyMap (ρ r).asHom i).hom
      map_one' := by
        rw [map_one, End.one_asHom, HomologicalComplex.homologyMap_id]; rfl
      map_mul' r s := by
        rw [map_mul, End.mul_asHom, HomologicalComplex.homologyMap_comp]; rfl
      map_zero' := by
        rw [map_zero, End.zero_asHom, HomologicalComplex.homologyMap_zero]; rfl
      map_add' r s := by
        rw [map_add, End.add_asHom, HomologicalComplex.homologyMap_add]; rfl
      commutes' a := by
        let F := HomologicalComplex.shortComplexFunctor (ModuleCat.{v} A) (ComplexShape.up ℤ) i
        have hsc : F.map (a • 𝟙 N) = a • 𝟙 (F.obj N) := by
          ext <;> rfl
        change (ShortComplex.homologyMap (F.map (ρ (algebraMap A R a)).asHom)).hom = _
        rw [hρ, hsc, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
        rw [Module.algebraMap_end_eq_smul_id]
        rfl }
  have hσ (r : R) : σ r = (HomologicalComplex.homologyMap (ρ r).asHom i).hom := rfl
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := A) (A := R)
  choose p hmon hp using fun r : R =>
    exists_monic_aeval_homologyMap_eq_zero hN (ρ r).asHom i
  let J : Ideal R := Ideal.span ((fun r => aeval r (p r)) '' (s : Set R))
  refine ⟨J, ?_, fun r hr => ?_⟩
  · let q := Ideal.Quotient.mkₐ A J
    have hint : ∀ x ∈ q '' (s : Set R), IsIntegral A x := by
      rintro _ ⟨r, hr, rfl⟩
      refine ⟨p r, hmon r, ?_⟩
      rw [← aeval_def, aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨r, hr, rfl⟩
    have hfg := fg_adjoin_of_finite ((s.finite_toSet).image q) hint
    rw [Algebra.adjoin_image, hs, Algebra.map_top,
      (AlgHom.range_eq_top _).2 (Ideal.Quotient.mkₐ_surjective A J)] at hfg
    exact ⟨by simpa using hfg⟩
  · have hle : J ≤ RingHom.ker σ.toRingHom := by
      rw [Ideal.span_le]
      rintro _ ⟨r, -, rfl⟩
      change σ (aeval r (p r)) = 0
      rw [← aeval_algHom_apply, hσ]
      exact hp r
    have h := hle hr
    rw [RingHom.mem_ker] at h
    ext x
    exact LinearMap.congr_fun h x

end StacksDraft.PseudoCoherence

end
