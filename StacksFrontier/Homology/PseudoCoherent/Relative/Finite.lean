module

public import StacksFrontier.Homology.PseudoCoherent.FiniteFree
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings

@[expose] public section

/-!
# Relative pseudo-coherence and restriction of scalars along a finite map

Relative pseudo-coherence is unchanged by restriction of scalars along a finite map of
finite-type algebras over the base.

## Main results

* `isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars`,
  Stacks 0673.

## Implementation notes

A presentation of the smaller algebra is extended by the generators of the finite extension,
and tag 064Z moves pseudo-coherence along the restriction; 065H makes the answer independent of
the presentation and 064T supplies the finite-free input.

## References

* [The Stacks Project, Lemma 15.82.5 (0673)](https://stacks.math.columbia.edu/tag/0673)
-/

open CategoryTheory CategoryTheory.Limits
open StacksDraft.PseudoCoherence

namespace PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

/-!
# Relative pseudo-coherence under finite restriction of scalars

Let `A → B` be a finite map of finite-type algebras over a commutative ring `R`. An object
of the derived category of `B`-modules is relatively `m`-pseudo-coherent over `R` if and only if
its restriction of scalars to `A` is. The analogous equivalence holds for relative
pseudo-coherence.

## Main definitions

No new definitions are introduced.

## Main results

* `isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars`
  gives both equivalences under restriction of scalars along a finite algebra.

## Implementation notes

Complexes are represented by objects of the derived category. The theorem is stated for an
arbitrary derived object, rather than one presented by a chosen complex. Finite type of `B` over
`R` is derived from finite type of `A` over `R` and module-finiteness of `B` over `A`.
The module universe contains `R`, so the finite free complexes over its polynomial algebras
and the intermediate finite algebras used in the proof fit in the ambient category.

## References

* [Stacks Project, Tag 0673](https://stacks.math.columbia.edu/tag/0673)
-/







/-- A module linearly equivalent to a finite free module is pseudo-coherent. -/
private lemma isModulePseudoCoherent_of_linearEquiv_finite_free
    {R : Type u} [CommRing R] {N M : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M] [Module.Finite R N] [Module.Free R N] (e : N ≃ₗ[R] M) :
    IsModulePseudoCoherent (R := R) M :=
  have := Module.Finite.equiv e
  have := Module.Free.of_equiv e
  StacksDraft.PseudoCoherence.isModulePseudoCoherent_of_finite_free M

private lemma isPseudoCoherentFrom_restrictScalars_ringEquiv
    {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)
    (K : DerivedCategory (ModuleCat.{u} S)) (m : ℤ) :
    IsPseudoCoherentFrom K m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} e.toRingHom).mapDerivedCategory.obj K) m := by
  exact isPseudoCoherentFrom_iff_restrictScalars e.toRingHom
    (isModulePseudoCoherent_of_linearEquiv_finite_free
      (ModuleCat.restrictScalarsIsoOfEquiv e).toLinearEquiv.symm) K m

private lemma isPseudoCoherentFrom_restrictScalars_comp_ringEquiv
    {R S : Type u} {T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) (f : S →+* T) (K : DerivedCategory (ModuleCat.{u} T)) (m : ℤ) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K) m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} (f.comp e.toRingHom)).mapDerivedCategory.obj K) m :=
  (isPseudoCoherentFrom_restrictScalars_ringEquiv e _ m).trans
    (isPseudoCoherentFrom_restrictScalars_comp_iff e.toRingHom f K m).symm

private lemma isModulePseudoCoherent_adjoinRoot_of
    {R : Type u} [CommRing R] (p : Polynomial R) (hp : p.Monic) :
    IsModulePseudoCoherent (R := R)
      ((ModuleCat.restrictScalars (AdjoinRoot.of p)).obj
        (ModuleCat.of (AdjoinRoot p) (AdjoinRoot p))) := by
  let M := (ModuleCat.restrictScalars (AdjoinRoot.of p)).obj
    (ModuleCat.of (AdjoinRoot p) (AdjoinRoot p))
  let e : AdjoinRoot p ≃ₗ[R] M :=
    { __ := Equiv.refl _
      map_add' := fun _ _ => rfl
      map_smul' := fun a b => by
        show a • b = AdjoinRoot.of p a * b
        rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq] }
  have := hp.free_adjoinRoot
  have := hp.finite_adjoinRoot
  exact isModulePseudoCoherent_of_linearEquiv_finite_free e

private lemma isPseudoCoherentFrom_restrictScalars_polynomial_eval₂
    {R : Type u} {B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
    (b : B) (hb : f.IsIntegralElem b)
    (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K) m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} (Polynomial.eval₂RingHom f b)).mapDerivedCategory.obj K)
        m := by
  obtain ⟨p, hp, hpb⟩ := hb
  let g := AdjoinRoot.lift f b hpb
  have h₁ : g.comp (AdjoinRoot.of p) = f := AdjoinRoot.lift_comp_of _
  have h₂ : g.comp (AdjoinRoot.mk p) = Polynomial.eval₂RingHom f b :=
    RingHom.ext fun q => AdjoinRoot.lift_mk hpb q
  have hP : IsModulePseudoCoherent (R := Polynomial R)
      ((ModuleCat.restrictScalars (AdjoinRoot.mk p)).obj
        (ModuleCat.of (AdjoinRoot p) (AdjoinRoot p))) :=
    PrincipalResolution.isModulePseudoCoherent (Polynomial R) p
      (fun a ha => hp.mul_right_eq_zero_iff.mp ha)
  rw [← h₂, ← h₁]
  exact (isPseudoCoherentFrom_restrictScalars_comp_iff (AdjoinRoot.of p) g K m).trans
    ((isPseudoCoherentFrom_iff_restrictScalars (AdjoinRoot.of p)
      (isModulePseudoCoherent_adjoinRoot_of p hp) _ m).symm.trans
      ((isPseudoCoherentFrom_iff_restrictScalars (AdjoinRoot.mk p) hP _ m).trans
        (isPseudoCoherentFrom_restrictScalars_comp_iff (AdjoinRoot.mk p) g K m).symm))

private lemma isPseudoCoherentFrom_restrictScalars_mvPolynomial_eval₂
    {R : Type u} {B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
    (n : ℕ) (b : Fin n → B) (hb : ∀ i, f.IsIntegralElem (b i))
    (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ) :
    IsPseudoCoherentFrom ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K) m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} (MvPolynomial.eval₂Hom f b)).mapDerivedCategory.obj K)
        m := by
  induction n with
  | zero =>
    have h : MvPolynomial.eval₂Hom f b =
        f.comp (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toRingHom := by
      ext r
      · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
        show f r = f ((MvPolynomial.isEmptyAlgEquiv R (Fin 0)) (MvPolynomial.C r))
        congr 1
        exact ((MvPolynomial.isEmptyAlgEquiv R (Fin 0)).commutes r).symm
      · exact Fin.elim0 r
    rw [h]
    exact isPseudoCoherentFrom_restrictScalars_comp_ringEquiv _ f K m
  | succ n ih =>
    let g := MvPolynomial.eval₂Hom f (fun i : Fin n => b i.succ)
    let e := (MvPolynomial.finSuccEquiv R n).toRingEquiv
    have hg : g.comp MvPolynomial.C = f := by ext r; simp [g]
    have hb₀ : g.IsIntegralElem (b 0) := by
      apply RingHom.IsIntegralElem.of_comp (f := MvPolynomial.C)
      rw [hg]
      exact hb 0
    have h : MvPolynomial.eval₂Hom f b =
        (Polynomial.eval₂RingHom g (b 0)).comp e.toRingHom := by
      ext r
      · simp [g, e, MvPolynomial.finSuccEquiv_apply]
      · refine Fin.cases ?_ (fun j => ?_) r
        · simp [g, e, MvPolynomial.finSuccEquiv_X_zero]
        · simp [g, e, MvPolynomial.finSuccEquiv_X_succ]
    rw [h]
    exact (ih (fun i => b i.succ) (fun i => hb i.succ)).trans
      ((isPseudoCoherentFrom_restrictScalars_polynomial_eval₂ g (b 0) hb₀ K m).trans
        (isPseudoCoherentFrom_restrictScalars_comp_ringEquiv e _ K m))

private lemma isRelativelyPseudoCoherentFrom_iff_polynomialPresentation
    {R : Type u} {B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ)
    {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] B) (hf : Function.Surjective f) :
    IsRelativelyPseudoCoherentFrom (R := R) K m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.obj K) m :=
  ⟨fun h => h n f hf, fun h =>
    (isPseudoCoherentFrom_polynomialPresentation_independent K m).1.mp
      ⟨n, f, hf, h⟩⟩

private lemma isRelativelyPseudoCoherentFrom_iff_restrictScalars_of_finite
    {R : Type u} {B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ)
    {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] B) (hf : f.toRingHom.Finite) :
    IsRelativelyPseudoCoherentFrom (R := R) K m ↔
      IsPseudoCoherentFrom
        ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.obj K) m := by
  obtain ⟨t, β, hβ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := B)).mp inferInstance
  let b : Fin t → B := fun i => β (MvPolynomial.X i)
  let g : MvPolynomial (Fin t) (MvPolynomial (Fin n) R) →ₐ[R] B :=
    { __ := MvPolynomial.eval₂Hom f.toRingHom b
      commutes' := fun r => by
        show MvPolynomial.eval₂Hom f.toRingHom b
          (MvPolynomial.C (MvPolynomial.C r)) = algebraMap R B r
        rw [MvPolynomial.eval₂Hom_C]
        exact f.commutes r }
  have hg : Function.Surjective g := by
    have h : g.toRingHom.comp (MvPolynomial.map (MvPolynomial.C : R →+* MvPolynomial (Fin n) R)) =
        β.toRingHom := by
      ext r
      · simp [g]
      · simp [g, b]
    intro a
    obtain ⟨p, hp⟩ := hβ a
    exact ⟨MvPolynomial.map MvPolynomial.C p, (RingHom.congr_fun h p).trans hp⟩
  let e : MvPolynomial (Fin (t + n)) R ≃ₐ[R]
      MvPolynomial (Fin t) (MvPolynomial (Fin n) R) :=
    (MvPolynomial.renameEquiv R finSumFinEquiv.symm).trans
      (MvPolynomial.sumAlgEquiv R (Fin t) (Fin n))
  have hfg := isPseudoCoherentFrom_restrictScalars_mvPolynomial_eval₂ f.toRingHom t b
    (fun i => hf.to_isIntegral (b i)) K m
  have he := isPseudoCoherentFrom_restrictScalars_comp_ringEquiv e.toRingEquiv g.toRingHom K m
  exact (isRelativelyPseudoCoherentFrom_iff_polynomialPresentation K m
    (g.comp e.toAlgHom) (hg.comp e.surjective)).trans (hfg.trans he).symm

/-- **Stacks 0673.** Restriction of scalars along a finite map of finite-type `R`-algebras
preserves and reflects relative `m`-pseudo-coherence and relative pseudo-coherence. -/
@[stacks 0673]
public theorem isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
    {R : Type u} {A : Type u} {B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B]
    (K : DerivedCategory (ModuleCat.{u} B)) (m : ℤ) :
    letI : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (Module.Finite.finiteType B)
    let Kₐ := (ModuleCat.restrictScalars.{u} (algebraMap A B)).mapDerivedCategory.obj K
    (IsRelativelyPseudoCoherentFrom (R := R) K m ↔
      IsRelativelyPseudoCoherentFrom (R := R) Kₐ m) ∧
    (IsRelativelyPseudoCoherent (R := R) K ↔
      IsRelativelyPseudoCoherent (R := R) Kₐ) := by
  dsimp only
  have : Algebra.FiniteType R B :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
      (Module.Finite.finiteType B)
  obtain ⟨n, α, hα⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := A)).mp inferInstance
  let f : MvPolynomial (Fin n) R →ₐ[R] B := (IsScalarTower.toAlgHom R A B).comp α
  have hf : f.toRingHom.Finite :=
    (RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite A B)).comp
      (RingHom.Finite.of_surjective α.toRingHom hα)
  have h (k : ℤ) : IsRelativelyPseudoCoherentFrom (R := R) K k ↔
      IsRelativelyPseudoCoherentFrom (R := R)
        ((ModuleCat.restrictScalars.{u} (algebraMap A B)).mapDerivedCategory.obj K) k :=
    (isRelativelyPseudoCoherentFrom_iff_restrictScalars_of_finite K k f hf).trans
      ((isPseudoCoherentFrom_restrictScalars_comp_iff α.toRingHom (algebraMap A B) K k).trans
        (isRelativelyPseudoCoherentFrom_iff_polynomialPresentation _ k α hα).symm)
  exact ⟨h m, forall_congr' h⟩

end PseudoCoherence
