module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Homology.PseudoCoherent.Module
public import StacksFrontier.Homology.PseudoCoherent.Triangle
public import StacksFrontier.Homology.RelativelyPerfect.Tensor
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public noncomputable section

/-!
# Relatively perfect objects are the finite complexes of relatively flat modules

Let `R → A` be a flat ring map of finite presentation. An object of `D(A)` is perfect relative
to `R` (Stacks 0DHS) exactly when it is isomorphic to a finite complex of `A`-modules that are
flat over `R` and finitely presented over `A`.

## Main results

* `PseudoCoherence.isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation`
  (Stacks 0DHV).

## Implementation notes

The forward implication is
`PseudoCoherence.exists_bounded_relativelyFlat_representative` of
`StacksFrontier.Homology.RelativelyPerfect.Tensor`: a bounded-above finite free representative
truncated at the lower Tor bound, whose terms are flat over `R` by Stacks 0653 and finitely
presented over `A` because the term at the bound is the cokernel of a map of finite free modules.

The reverse implication splits along the definition of relative perfectness. Finite Tor dimension
over `R` is `PseudoCoherence.hasFiniteTorDimension_of_bounded_relativelyFlat`, which needs only
boundedness and flatness over `R`. Pseudo-coherence over `A` is Stacks 064Y
(`StacksDraft.PseudoCoherence.pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove`) applied to
the terms, and the work is the termwise statement: an `A`-module flat over `R` and finitely
presented over `A` is pseudo-coherent over `A`.

That termwise statement is the source's spreading-out argument, replayed here untagged because
the tree has no other provider for it. Stacks 02JO
(`Module.Flat.exists_flat_models_and_eventually_flat`) descends the module to a finite `A₀`-module
`M₀`, flat over a finite type `ℤ`-algebra `R₀`, with `A` and `M` obtained from `A₀` and `M₀` by
base change along `R₀ → R`. Over the Noetherian ring `A₀` the kernel of a finite free presentation
of `M₀` is again finitely presented, and flatness of `M₀` over `R₀` keeps that presentation exact
after base change, so `M` itself has a finite free presentation with finitely presented kernel;
the kernel is flat over `R` because it is the kernel of a surjection between modules flat over
`R`. Iterating gives finite free approximations to any prescribed degree, which is
`m`-pseudo-coherence for every `m`, hence pseudo-coherence by Stacks 064U. The induction step
reads the presentation as a distinguished triangle and propagates pseudo-coherence along it by
Stacks 064R.

The ring, algebra and module carrier universes are independent, as in Stacks 0DHS; the
spreading-out model is taken in the common carrier universe `max u v w`.

Two points of bookkeeping. The module structures over `R` obtained by restriction of scalars are
recognized behind the `ModuleCat` wrapper only under a relaxed transparency during unification,
so the file sets `backward.isDefEq.respectTransparency` to `false`, as its providers do. And
pseudo-coherence over `A` has two spellings in the tree, the one Stacks 0DHS is stated with
(`StacksDraft.PseudoCoherence.IsPseudoCoherent`) and the definitionally identical
`PseudoCoherence.IsPseudoCoherent` of
`StacksFrontier.Homology.PseudoCoherent.Characterization`; everything here is over the former, which
is why it is written out. Unifying them is a dedup target.

## References

* [The Stacks Project, Lemma 15.85.4 (0DHV)](https://stacks.math.columbia.edu/tag/0DHV)
-/

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace PseudoCoherence

universe u v w

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

open StacksDraft.PseudoCoherence StacksDraft.TorAmplitude

/-! ### Relatively flat finite free presentations -/

/-- In a pushout square, base change preserves a short exact sequence whose final module is flat
over the base ring. -/
private lemma baseChange_injective_of_isPushout
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
    [IsScalarTower R S B] [IsScalarTower R A B] [Algebra.IsPushout R S A B]
    {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module A M] [Module A N] [Module A P]
    [Module R M] [Module R N] [Module R P]
    [IsScalarTower R A M] [IsScalarTower R A N] [IsScalarTower R A P]
    [Module.Flat R P]
    (f : M →ₗ[A] N) (g : N →ₗ[A] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) : Function.Injective (f.baseChange B) := by
  let eM := Algebra.IsPushout.cancelBaseChange R S A B M
  let eN := Algebra.IsPushout.cancelBaseChange R S A B N
  have hi := LinearMap.lTensor_injective_of_exact_of_flat
    (g.restrictScalars R) hg (f.restrictScalars R) hf hex S
  have hc : ∀ z : S ⊗[R] M,
      eN.symm ((f.restrictScalars R).lTensor S z) = f.baseChange B (eM.symm z) := by
    intro z
    induction z with
    | tmul s m => simp [eM, eN, Algebra.IsPushout.cancelBaseChange_symm_tmul]
    | add x y hx hy => simp_all
  intro x y h
  apply eM.injective
  apply hi
  apply eN.symm.injective
  simpa only [hc, LinearEquiv.symm_apply_apply] using h

/-- The kernel of a surjection between flat modules is flat. -/
@[ega "0 20.6.21" "more general"]
private lemma flat_of_exact
    {R : Type*} [CommRing R] {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module R M] [Module R N] [Module R P]
    [Module.Flat R N] [Module.Flat R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hex : Function.Exact f g) : Module.Flat R M := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ a ha
  have hX := LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hex X
  have hN := Module.Flat.rTensor_preserves_injective_linearMap (M := N) a ha
  intro x y h
  apply hX
  apply hN
  have hc : (a.rTensor N).comp (f.lTensor X) = (f.lTensor Y).comp (a.rTensor M) := by
    ext x m
    rfl
  simpa only [← LinearMap.comp_apply, ← hc] using congrArg (f.lTensor Y) h

/-- A module flat over `R` and finitely presented over `A` admits a finite free presentation
over `A` whose kernel is again finitely presented: the module descends to a finite module over a
Noetherian model of `A`, where the kernel of a finite free presentation is finitely presented,
and base change keeps the presentation exact because the model is flat over its base. -/
private lemma exists_finite_free_surjective_finitePresentation_ker
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A]
    (M : Type w) [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [Module.Flat R M] [Module.FinitePresentation A M] :
    ∃ (F : Type (max u v w)) (_ : AddCommGroup F) (_ : Module A F) (p : F →ₗ[A] M),
      Module.Free A F ∧ Module.Finite A F ∧ Function.Surjective p ∧
        Module.FinitePresentation A p.ker := by
  obtain ⟨(R₀ : Type (max u v w)), (A₀ : Type (max u v w)), (M₀ : Type (max u v w)),
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, f, hR₀, hA₀, hM₀, hflat, hpush, hbase⟩ :=
      (Module.Flat.exists_flat_models_and_eventually_flat.{u, v, w, 0, 0, 0, 0,
        max u v w, max u v w, max u v w} (R := R) (S := A) (M := M)).1
  have := hR₀
  have := hA₀
  have := hM₀
  have := hflat
  have := hpush
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing R₀ A₀
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' A₀ M₀
  let F := A ⊗[A₀] (Fin n → A₀)
  let qA := q.baseChange A
  have hqA : Function.Surjective qA := LinearMap.lTensor_surjective A hq
  let fA := q.ker.subtype.baseChange A
  have hfA : Function.Injective fA :=
    baseChange_injective_of_isPushout (R := R₀) (S := R) (B := A)
      q.ker.subtype q q.ker.subtype_injective hq (LinearMap.exact_subtype_ker_map q)
  have hex : Function.Exact fA qA :=
    lTensor_exact A (LinearMap.exact_subtype_ker_map q) hq
  have : Module.FinitePresentation A₀ q.ker := Module.finitePresentation_of_finite A₀ q.ker
  have : Module.FinitePresentation A qA.ker :=
    Module.FinitePresentation.of_equiv (R := A) (M := A ⊗[A₀] q.ker) (N := qA.ker)
      (LinearEquiv.ofInjective fA hfA ≪≫ₗ LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp hex).symm)
  let p := hbase.equiv.toLinearMap.comp qA
  have hp : Function.Surjective p := hbase.equiv.surjective.comp hqA
  have hpker : p.ker = qA.ker := by
    ext x
    simp [p]
  have : Module.FinitePresentation A p.ker := hpker.symm ▸ ‹Module.FinitePresentation A qA.ker›
  exact ⟨F, inferInstance, inferInstance, p, inferInstance, inferInstance, hp, inferInstance⟩

/-- The previous presentation, shrunk into the module's own carrier universe and with the kernel's
flatness over `R` recorded: the kernel is the kernel of a surjection from a finite free
`A`-module, which is flat over `R` by transitivity of flatness. -/
private lemma exists_small_finite_free_surjective_finitePresentation_ker
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (M : ModuleCat.{max u v w} A)
    [Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)]
    [Module.FinitePresentation A M] :
    ∃ (F : ModuleCat.{max u v w} A) (p : F →ₗ[A] M),
      Module.Free A F ∧ Module.Finite A F ∧ Function.Surjective p ∧
        Module.FinitePresentation A p.ker ∧
        Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A p.ker)) := by
  let _ : Module R M := Module.compHom M (algebraMap R A)
  have : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R M :=
    inferInstanceAs (Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M))
  obtain ⟨F, _, _, p, hfree, hfin, hp, hfp⟩ :=
    exists_finite_free_surjective_finitePresentation_ker.{u, v, max u v w} (R := R) (A := A) M
  have := hfree
  have := hfin
  have := hfp
  have : Small.{max u v w} A := inferInstance
  have : Small.{max u v w} F := Module.Finite.small A F
  let e := Shrink.linearEquiv A F
  let F' : ModuleCat.{max u v w} A := ModuleCat.of A (Shrink.{max u v w} F)
  let p' : F' →ₗ[A] M := p.comp e.toLinearMap
  have hfree' : Module.Free A F' := Module.Free.of_equiv e.symm
  have hfin' : Module.Finite A F' :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have hfp' : Module.FinitePresentation A p'.ker := by
    show Module.FinitePresentation A (Submodule.comap e.toLinearMap p.ker)
    exact Module.FinitePresentation.of_equiv (e.ofSubmodule' p.ker).symm
  have hp' : Function.Surjective p' := hp.comp e.surjective
  refine ⟨F', p', hfree', hfin', hp', hfp', ?_⟩
  let _iF : Module R F' := Module.compHom F' (algebraMap R A)
  have _tF : IsScalarTower R A F' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _fF : Module.Flat A F' := Module.Flat.of_free
  have : Module.Flat R F' := Module.Flat.trans R A F'
  let _iK : Module R p'.ker := Module.compHom p'.ker (algebraMap R A)
  have _tK : IsScalarTower R A p'.ker := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact flat_of_exact (p'.ker.subtype.restrictScalars R) (p'.restrictScalars R)
    p'.ker.subtype_injective hp' (LinearMap.exact_subtype_ker_map p')

/-! ### Pseudo-coherence of a relatively flat finitely presented module -/

/-- A finite free module placed in degree zero is pseudo-coherent. -/
private lemma pseudoCoherent_single_of_finite_free {A : Type u} [Ring A]
    (M : ModuleCat.{v} A) [Module.Free A M] [Module.Finite A M] :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) := by
  let P := (CochainComplex.singleFunctor (ModuleCat.{v} A) 0).obj M
  refine ⟨P, ⟨⟨0, inferInstance⟩, ?_⟩, ⟨Iso.refl _⟩⟩
  intro i
  by_cases hi : i = 0
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).toLinearEquiv
    exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
      Module.Free.of_equiv e.symm⟩
  · have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi)
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton A _⟩

/-- A module placed in degree zero is `m`-pseudo-coherent for every positive `m`, its cohomology
vanishing there. -/
private lemma pseudoCoherentFrom_single_of_pos {A : Type u} [Ring A]
    (M : ModuleCat.{v} A) (m : ℤ) (hm : 0 < m) :
    IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) m := by
  apply isPseudoCoherentFrom_of_homology_isZero
  intro i hi
  exact (DerivedCategory.isLE_iff _ 0).mp inferInstance i (hm.trans_le hi)

/-- Iterating the relatively flat finite free presentation gives `(-n)`-pseudo-coherence of a
module flat over `R` and finitely presented over `A`, for every `n`. The presentation is read as
a distinguished triangle and pseudo-coherence propagates along it by Stacks 064R; the kernel is
again flat over `R` and finitely presented over `A`, which feeds the induction. -/
private lemma pseudoCoherentFrom_single_of_flat_finitePresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (n : ℕ) (M : ModuleCat.{max u v w} A)
    [Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)]
    [Module.FinitePresentation A M] :
    IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj M) (-(n : ℤ)) := by
  have : Small.{max u v w} A := inferInstance
  induction n generalizing M with
  | zero =>
      exact (modulePseudoCoherent_iff_finiteness_and_resolutions_of_small
        (R := A) M).1.mpr inferInstance
  | succ n ih =>
      obtain ⟨F, p, hfree, hfinite, hp, hfp, hflat⟩ :=
        exists_small_finite_free_surjective_finitePresentation_ker.{u, v, w} (R := R) M
      have := hfree
      have := hfinite
      have := hfp
      have := hflat
      let N : ModuleCat.{max u v w} A := ModuleCat.of A p.ker
      let S : ShortComplex (ModuleCat.{max u v w} A) :=
        ShortComplex.mk (ModuleCat.ofHom p.ker.subtype) (ModuleCat.ofHom p) (by
          ext x
          exact x.property)
      have hS : S.ShortExact :=
        { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
            (LinearMap.exact_subtype_ker_map p)
          mono_f := (ModuleCat.mono_iff_injective _).mpr p.ker.subtype_injective
          epi_g := (ModuleCat.epi_iff_surjective _).mpr hp }
      have : PreservesFiniteLimits (CochainComplex.singleFunctor (ModuleCat.{max u v w} A) 0) :=
        inferInstanceAs (PreservesFiniteLimits
          (HomologicalComplex.single (ModuleCat.{max u v w} A) (ComplexShape.up ℤ) 0))
      have : PreservesFiniteColimits (CochainComplex.singleFunctor (ModuleCat.{max u v w} A) 0) :=
        inferInstanceAs (PreservesFiniteColimits
          (HomologicalComplex.single (ModuleCat.{max u v w} A) (ComplexShape.up ℤ) 0))
      have : Mono S.f := hS.mono_f
      have : Epi S.g := hS.epi_g
      have hSC := hS.map (CochainComplex.singleFunctor (ModuleCat.{max u v w} A) 0)
      have hF := (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj F)).mp
          (pseudoCoherent_single_of_finite_free.{v, max u v w} F) (-(n + 1 : ℤ))
      apply PseudoCoherence.isPseudoCoherent_of_distinguished_one (-(n + 1 : ℤ))
        (DerivedCategory.triangleOfSES hSC) (DerivedCategory.triangleOfSES_distinguished hSC)
      · show IsPseudoCoherentFrom
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj N) _
        convert ih N using 1
        simp
      · exact hF

/-- An `A`-module flat over `R` and finitely presented over `A` is pseudo-coherent over `A`, for
`R → A` flat of finite presentation. This is the termwise content of Stacks 0DHV; it carries no
tag. -/
private lemma pseudoCoherent_single_of_flat_finitePresentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] [Module.Flat R A]
    (M : ModuleCat.{max u v w} A)
    [Module.Flat R ((ModuleCat.restrictScalars (algebraMap R A)).obj M)]
    [Module.FinitePresentation A M] :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} A) 0).obj M) := by
  apply (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).mpr
  intro m
  by_cases hm : 0 < m
  · exact pseudoCoherentFrom_single_of_pos.{v, max u v w} M m hm
  · have hm' : -(((-m).toNat : ℕ) : ℤ) = m := by omega
    rw [← hm']
    exact pseudoCoherentFrom_single_of_flat_finitePresentation.{u, v, w} (R := R) _ M

/-! ### Stacks 0DHV -/

section Main

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Flat R A] [Algebra.FinitePresentation R A]
  (derivedTensor : DerivedCategory (ModuleCat.{max u v w} R) ⥤
      DerivedCategory (ModuleCat.{max u v w} R) ⥤ DerivedCategory (ModuleCat.{max u v w} R))
  (comparison : ∀ N : ModuleCat.{max u v w} R,
    DerivedCategory.Q ⋙ derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj N) ⟶
      (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerived : ∀ N : ModuleCat.{max u v w} R,
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v w} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{max u v w} R) (ComplexShape.up ℤ)))

/-- **Stacks 0DHV.** For a flat, finitely presented ring map `R → A`, an object of `D(A)` is
perfect relative to `R` if and only if it is isomorphic to a finite complex of `A`-modules that
are flat over `R` and finitely presented over `A`. -/
@[stacks 0DHV]
theorem isRelativelyPerfect_iff_exists_bounded_flat_finitePresentation
    (K : DerivedCategory (ModuleCat.{max u v w} A)) :
    IsRelativelyPerfect.{u, v, w} derivedTensor comparison isLeftDerived K ↔
      ∃ (P : CochainComplex (ModuleCat.{max u v w} A) ℤ) (a b : ℤ),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Flat R
          ((ModuleCat.restrictScalars (algebraMap R A)).obj (P.X i))) ∧
        (∀ i : ℤ, Module.FinitePresentation A (P.X i)) ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  refine ⟨exists_bounded_relativelyFlat_representative derivedTensor comparison isLeftDerived K,
    ?_⟩
  rintro ⟨P, a, b, hGE, hLE, hflat, hfp, ⟨e⟩⟩
  have := hGE
  have := hLE
  refine ⟨?_, hasFiniteTorDimension_of_bounded_relativelyFlat derivedTensor comparison
    isLeftDerived K P a b hflat e⟩
  refine StacksDraft.PseudoCoherence.IsPseudoCoherent.ofIso
    ((pseudoCoherentFrom_and_pseudoCoherent_of_boundedAbove P ⟨b, hLE⟩).2 ?_) e.symm
  intro i
  have := hflat i
  have := hfp i
  exact pseudoCoherent_single_of_flat_finitePresentation.{u, v, w} (R := R) (P.X i)

end Main

end PseudoCoherence
