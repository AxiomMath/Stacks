module

public import StacksFrontier.Homology.PseudoCoherent.Basic
import all StacksFrontier.Homology.RelativelyPerfect.FlatComplex
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
public import StacksFrontier.Homology.PseudoCoherent.Triangle
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.RingTheory.PseudoCoherentMap.Defs
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel

@[expose] public section

/-!
# Flat ring maps of finite presentation are perfect

A flat ring map of finite presentation is perfect: it is pseudo-coherent, and its target has
finite Tor dimension over its source.

## Main results

* `RingHom.isPerfectRingMap_of_flat_of_finitePresentation` (Stacks 067J).
* `RingHom.PseudoCoherent.of_flat_of_finitePresentation`: a flat ring map of finite presentation
  is pseudo-coherent, which is the pseudo-coherence half of Stacks 067J.

## Implementation notes

Pseudo-coherence of the ring map does not refer to a derived tensor product, so it is asserted
once; the finite Tor dimension half is quantified over the certified derived tensor product that
`RingHom.IsPerfectRingMap` takes as data, exactly as the definition has it.

Pseudo-coherence is proved by descending a presentation to a Noetherian model. Stacks 02JO
produces a finite-type `ℤ`-algebra `R₀`, a finite-type `R₀`-algebra `A₀` and a finite `A₀`-module
`M₀`, flat over `R₀`, with everything in sight obtained by base change; over the Noetherian ring
`A₀` the kernel of a finite free presentation of `M₀` is again finitely presented, and flatness
over `R₀` makes that presentation stay exact after base change. Iterating produces finite free
approximations to any prescribed degree, which is `m`-pseudo-coherence for every `m`, hence
pseudo-coherence by Stacks 064U.

Finite Tor dimension is Tor amplitude in `[0, 0]`: the target, being flat, is its own flat
resolution, so `StacksDraft.TorAmplitude.certifiedTensorHomologyIsoOfFlat` computes the derived
tensor product by the termwise one, which is concentrated in degree zero.

## References

* [The Stacks Project, Lemma 15.83.4 (067J)](https://stacks.math.columbia.edu/tag/067J)
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open StacksDraft.PseudoCoherence

namespace RingHom

universe u

attribute [local instance] HasDerivedCategory.standard


/-! ### Flatness and base change of a finite free presentation -/

/-- A finitely presented module over a finitely presented algebra, flat over the base, admits a
finite free presentation whose kernel is again finitely presented. -/
private lemma exists_finite_free_surjective_finitePresentation_ker
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A]
    (M : Type u) [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [Module.Flat R M] [Module.FinitePresentation A M] :
    ∃ (F : Type u) (_ : AddCommGroup F) (_ : Module A F) (p : F →ₗ[A] M),
      Module.Free A F ∧ Module.Finite A F ∧ Function.Surjective p ∧
        Module.FinitePresentation A p.ker := by
  obtain ⟨R₀, A₀, M₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, f,
      hR₀, hA₀, hM₀, hflat, hpush, hbase⟩ :=
    Module.Flat.exists_finiteType_model (R := R) (S := A) M
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R₀ A₀
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' A₀ M₀
  let F := A ⊗[A₀] (Fin n → A₀)
  let qA := q.baseChange A
  have hqA : Function.Surjective qA := LinearMap.lTensor_surjective A hq
  let fA := q.ker.subtype.baseChange A
  have hfA : Function.Injective fA :=
    PseudoCoherence.baseChange_injective_of_isPushout (R := R₀) (S := R) (B := A)
      q.ker.subtype q q.ker.subtype_injective hq (LinearMap.exact_subtype_ker_map q)
  have hex : Function.Exact fA qA :=
    lTensor_exact A (LinearMap.exact_subtype_ker_map q) hq
  have hEq : LinearMap.range fA = LinearMap.ker qA := (LinearMap.exact_iff.mp hex).symm
  have : Module.FinitePresentation A₀ q.ker := Module.finitePresentation_of_finite A₀ q.ker
  let e : (A ⊗[A₀] q.ker) ≃ₗ[A] qA.ker :=
    LinearEquiv.ofInjective fA hfA ≪≫ₗ LinearEquiv.ofEq _ _ hEq
  have : Module.FinitePresentation A qA.ker :=
    Module.FinitePresentation.of_equiv (R := A) (M := A ⊗[A₀] q.ker) (N := qA.ker) e
  let p := hbase.equiv.toLinearMap.comp qA
  have hp : Function.Surjective p := hbase.equiv.surjective.comp hqA
  have hpker : p.ker = qA.ker := by
    ext x
    simp [p]
  have : Module.FinitePresentation A p.ker := hpker.symm ▸ ‹Module.FinitePresentation A qA.ker›
  exact ⟨F, inferInstance, inferInstance, p, inferInstance, inferInstance, hp, inferInstance⟩

/-- Over a flat finitely presented algebra the presentation of the previous lemma can be taken
with kernel again flat over the base, so that the construction iterates. -/
private lemma exists_free_surjective_finitePresentation_flat_ker
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (M : ModuleCat.{u} A)
    [Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)]
    [Module.FinitePresentation A M] :
    ∃ (F : ModuleCat.{u} A) (p : F →ₗ[A] M),
      Module.Free A F ∧ Module.Finite A F ∧ Function.Surjective p ∧
        Module.FinitePresentation A p.ker ∧
        Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A p.ker)) := by
  let : Module R M := Module.compHom M (algebraMap R A)
  have : IsScalarTower R A M := .of_compHom R A M
  have : Module.Flat R M :=
    inferInstanceAs (Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M))
  obtain ⟨F, _, _, p, hfree, hfin, hp, hfp⟩ :=
    exists_finite_free_surjective_finitePresentation_ker (R := R) (A := A) (M := (M : Type u))
  refine ⟨ModuleCat.of A F, p, hfree, hfin, hp, hfp, ?_⟩
  let : Module R F := Module.compHom F (algebraMap R A)
  have : IsScalarTower R A F := .of_compHom R A F
  have : Module.Flat A F := Module.Flat.of_free
  have : Module.Flat R F := Module.Flat.trans R A F
  let : Module R p.ker := Module.compHom p.ker (algebraMap R A)
  have : IsScalarTower R A p.ker := .of_compHom R A p.ker
  exact PseudoCoherence.flat_of_exact (p.ker.subtype.restrictScalars R) (p.restrictScalars R)
    p.ker.subtype_injective hp (LinearMap.exact_subtype_ker_map p)

/-! ### Pseudo-coherence -/

/-- Each term of a module placed in degree zero is the module itself or subsingleton. -/
private lemma single_X_equiv_or_subsingleton
    {A : Type u} [Ring A] (M : ModuleCat.{u} A) (i : ℤ) :
    Nonempty (((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M).X i ≃ₗ[A] M) ∨
      Subsingleton (((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M).X i) := by
  by_cases hi : i = 0
  · subst i
    exact .inl ⟨(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).toLinearEquiv⟩
  · exact .inr (ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi))

/-- A finite free module placed in degree zero is pseudo-coherent. -/
private lemma pseudoCoherent_single_of_finite_free
    {A : Type u} [Ring A] (M : ModuleCat.{u} A) [Module.Free A M] [Module.Finite A M] :
    IsPseudoCoherent ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) := by
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M
  refine ⟨P, ⟨⟨0, inferInstance⟩, ?_⟩, ⟨Iso.refl _⟩⟩
  intro i
  rcases single_X_equiv_or_subsingleton M i with ⟨⟨e⟩⟩ | _
  · exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩
  · exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton A _⟩

/-- A module placed in degree zero is `m`-pseudo-coherent for every positive `m`. -/
private lemma pseudoCoherentFrom_single_of_pos
    {A : Type u} [Ring A] (M : ModuleCat.{u} A) (m : ℤ) (hm : 0 < m) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) m :=
  isPseudoCoherentFrom_of_homology_isZero _ _ fun i hi ↦
    (DerivedCategory.isLE_iff _ 0).mp inferInstance i (lt_of_lt_of_le hm hi)

/-- Iterating the flat finite free presentations gives `(-n)`-pseudo-coherence for every `n`. -/
private lemma pseudoCoherentFrom_single_of_flat_finitePresentation
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (n : ℕ) (M : ModuleCat.{u} A)
    [Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)]
    [Module.FinitePresentation A M] :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)
      (-(n : ℤ)) := by
  induction n generalizing M with
  | zero =>
      exact (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
        (R := A) (M : Type u)).1.mpr inferInstance
  | succ n ih =>
      obtain ⟨F, p, hfree, hfinite, hp, hfp, hflat⟩ :=
        exists_free_surjective_finitePresentation_flat_ker (R := R) M
      let N : ModuleCat.{u} A := ModuleCat.of A p.ker
      let S : ShortComplex (ModuleCat.{u} A) :=
        ShortComplex.mk (ModuleCat.ofHom p.ker.subtype) (ModuleCat.ofHom p) (by
          ext x
          exact x.property)
      have hS : S.ShortExact :=
        { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
            (LinearMap.exact_subtype_ker_map p)
          mono_f := (ModuleCat.mono_iff_injective _).mpr p.ker.subtype_injective
          epi_g := (ModuleCat.epi_iff_surjective _).mpr hp }
      have : PreservesFiniteLimits (CochainComplex.singleFunctor (ModuleCat.{u} A) 0) :=
        inferInstanceAs (PreservesFiniteLimits
          (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0))
      have : PreservesFiniteColimits (CochainComplex.singleFunctor (ModuleCat.{u} A) 0) :=
        inferInstanceAs (PreservesFiniteColimits
          (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0))
      have : Mono S.f := hS.mono_f
      have : Epi S.g := hS.epi_g
      have hSC := hS.map (CochainComplex.singleFunctor (ModuleCat.{u} A) 0)
      apply PseudoCoherence.isPseudoCoherent_of_distinguished_one (-(n + 1 : ℤ))
        (DerivedCategory.triangleOfSES hSC) (DerivedCategory.triangleOfSES_distinguished hSC)
      · show IsPseudoCoherentFrom
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) _
        convert ih N using 1
        simp
      · exact (pseudoCoherent_iff_all _).mp (pseudoCoherent_single_of_finite_free F) _

/-- A flat finitely presented module over a flat finitely presented algebra is pseudo-coherent
in the derived category of the algebra. -/
private lemma pseudoCoherent_single_of_flat_finitePresentation
    {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (M : ModuleCat.{u} A)
    [Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)]
    [Module.FinitePresentation A M] :
    IsPseudoCoherent ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) := by
  refine (pseudoCoherent_iff_all _).mpr fun m ↦ ?_
  by_cases hm : 0 < m
  · exact pseudoCoherentFrom_single_of_pos M m hm
  · have hm' : -(((-m).toNat : ℕ) : ℤ) = m := by omega
    rw [← hm']
    exact pseudoCoherentFrom_single_of_flat_finitePresentation (R := R) _ M

/-- For a polynomial presentation of a flat finitely presented algebra `B` over `A`, the
restriction of `B[0]` to the polynomial algebra is pseudo-coherent. -/
private lemma pseudoCoherent_restrictScalars_of_surjective
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    (n : ℕ) (f : MvPolynomial (Fin n) A →ₐ[A] B) (hf : Function.Surjective f) :
    IsPseudoCoherent
      ((ModuleCat.restrictScalars.{u} f.toRingHom).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) := by
  let P := MvPolynomial (Fin n) A
  let F := ModuleCat.restrictScalars.{u} f.toRingHom
  let M : ModuleCat.{u} P := F.obj (ModuleCat.of B B)
  have hfp : Module.FinitePresentation P M := by
    let q : P →ₗ[P] M := LinearMap.toSpanSingleton P M (show B from 1)
    have hq : ∀ x, q x = (show M from f x) := by
      intro x
      show f.toRingHom x * 1 = f x
      simp
    have hker : (LinearMap.ker q).FG := by
      have hk : LinearMap.ker q = RingHom.ker f.toRingHom := by
        ext x
        rw [LinearMap.mem_ker, hq, RingHom.mem_ker]
        rfl
      rw [hk]
      exact Algebra.FinitePresentation.ker_fG_of_surjective f hf
    refine Module.finitePresentation_of_surjective q (fun b ↦ ?_) hker
    obtain ⟨p, hp⟩ := hf (show B from b)
    exact ⟨p, by rw [hq, hp]⟩
  have hflat : Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P)).obj M) := by
    let e : ((ModuleCat.restrictScalars (algebraMap A P)).obj M) ≃ₗ[A] B :=
      { toFun := fun x => (show B from x)
        invFun := fun x => x
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_smul' := by
          intro a b
          show f (algebraMap A P a) * (show B from b) = a • (show B from b)
          rw [f.commutes, Algebra.smul_def] }
    exact Module.Flat.of_linearEquiv e
  obtain ⟨E, hE, ⟨e⟩⟩ := pseudoCoherent_single_of_flat_finitePresentation (R := A) (A := P) M
  exact ⟨E, hE, ⟨e ≪≫ ((F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of B B)).symm⟩⟩

/-! ### Finite Tor dimension -/

/-- A flat module is its own flat resolution, so it has Tor amplitude in `[0, 0]` for any
certified derived tensor product. -/
private lemma hasTorAmplitude_zero_of_flat
    {A : Type u} [CommRing A] (B : Type u) [AddCommGroup B] [Module A B] [Module.Flat A B]
    {derivedTensor : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A)}
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) :
    StacksDraft.TorAmplitude.HasTorAmplitude derivedTensor comparison isLeftDerived
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)) 0 0 := by
  let Mc : ModuleCat.{u} A := ModuleCat.of A B
  let P := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj Mc
  have hzeroX : ∀ i : ℤ, i ≠ 0 → IsZero (P.X i) := fun i hi =>
    HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 Mc i hi
  have hbounded : ∃ d : ℤ, ∀ i : ℤ, d < i → IsZero (P.X i) :=
    ⟨0, fun i hi => hzeroX i (by omega)⟩
  have hflat : ∀ i : ℤ, Module.Flat A (P.X i) := by
    intro i
    rcases single_X_equiv_or_subsingleton Mc i with ⟨⟨e⟩⟩ | _
    · exact Module.Flat.of_linearEquiv e
    · infer_instance
  have e : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj Mc :=
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app Mc).symm
  intro N i hi
  have hi0 : i ≠ 0 := by
    simp only [Set.mem_Icc] at hi
    omega
  have hX : IsZero ((((StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).X i) :=
    (StacksDraft.TorAmplitude.tensorModuleRight N).map_isZero (hzeroX i hi0)
  have hH : IsZero ((((StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P).homology i) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ i).mp
      (HomologicalComplex.ExactAt.of_isZero hX)
  have hP := hH.of_iso (StacksDraft.TorAmplitude.certifiedTensorHomologyIsoOfFlat
    comparison isLeftDerived P hbounded hflat N i)
  exact hP.of_iso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
    (((derivedTensor.mapIso e).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).symm))

/-! ### The theorem -/

/-- **Stacks 067J.** A flat ring map of finite presentation is perfect: it is pseudo-coherent,
and its target has finite Tor dimension over its source for every certified derived tensor
product. -/
@[stacks 067J]
public theorem isPerfectRingMap_of_flat_of_finitePresentation
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] :
    Algebra.PseudoCoherent A B ∧
    ∀ (derivedTensor : DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
      (comparison : ∀ N : ModuleCat.{u} A,
        DerivedCategory.Q ⋙ derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
          (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (isLeftDerived : ∀ N : ModuleCat.{u} A,
        (derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))),
      IsPerfectRingMap A B derivedTensor comparison isLeftDerived := by
  have hpc : Algebra.PseudoCoherent A B :=
    Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr fun m n f hf ↦
      (pseudoCoherent_iff_all _).mp (pseudoCoherent_restrictScalars_of_surjective n f hf) m
  exact ⟨hpc, fun _ comparison isLeftDerived ↦
    ⟨hpc, 0, 0, hasTorAmplitude_zero_of_flat B comparison isLeftDerived⟩⟩

/-- **The pseudo-coherence half of Stacks 067J.** A flat ring map of finite presentation is
pseudo-coherent.

This is the first component of
`RingHom.isPerfectRingMap_of_flat_of_finitePresentation`, read for the algebra structure that the
ring map itself induces. -/
public theorem PseudoCoherent.of_flat_of_finitePresentation {A B : Type u} [CommRing A]
    [CommRing B] {f : A →+* B} (hflat : f.Flat) (hfp : f.FinitePresentation) :
    f.PseudoCoherent := by
  algebraize [f]
  exact (isPerfectRingMap_of_flat_of_finitePresentation A B).1

end RingHom
