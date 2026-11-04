module

public import StacksFrontier.Algebra.Homology.Resolution.Defs.Comparison
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.TorAmplitude.Defs
import StacksFrontier.Homology.PseudoCoherent.Relative.Module
import StacksFrontier.Homology.PseudoCoherent.Relative.Presentation
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

/-!
# Pseudo-coherent and perfect ring maps

A ring map `A → B` is *pseudo-coherent* when `B` is a quotient `A[x₁, …, xₙ] ⧸ I` of a polynomial
algebra such that the `A[x₁, …, xₙ]`-module `A[x₁, …, xₙ] ⧸ I` has a resolution by finite free
modules; it is *perfect* when in addition `B` has finite Tor dimension as an `A`-module.

## Main definitions

* `Algebra.PseudoCoherent` (Stacks 067H (1)), and `RingHom.PseudoCoherent`, the same notion for a
  ring homomorphism and the algebra structure it induces;
* `RingHom.IsPerfectRingMap` (Stacks 067H (2)).

## Main results

* `Algebra.PseudoCoherent.finitePresentation`: a pseudo-coherent algebra is finitely presented
  (Stacks 0682), hence of finite type (an instance);
* `Algebra.PseudoCoherent.nonempty_finiteFreeModuleResolution`: the resolution exists over every
  finite polynomial presentation, not only over the one the definition provides;
* `Algebra.PseudoCoherent.equiv`: pseudo-coherence is invariant under isomorphisms of algebras;
* `Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent`: the definition as
  Stacks 067H (1) words it, through relative pseudo-coherence (Stacks 065I).

## Implementation notes

Stacks 067H (1) asks for `A → B` to be of finite type and for `B`, as a module over itself, to be
pseudo-coherent relative to `A`, a condition on derived categories of polynomial algebras. Right
after the definition Stacks notes that, by Stacks 0675, this says that `B = A[x₁, …, xₙ]/I` for some
`n` and `I`, with `B` resolved by finite free `A[x₁, …, xₙ]`-modules. That is the definition here,
with `B` replaced by the isomorphic `A[x₁, …, xₙ]`-module `A[x₁, …, xₙ] ⧸ I`, which lives in the
universe of `A`, so that `A` and `B` may live in different universes, as for
`Algebra.FinitePresentation`. It mentions no derived category, so it needs no model of one. Like
`Algebra.FinitePresentation`, it asks for one presentation, and independence of the presentation is
a theorem (Stacks 065H). Finite presentation, hence finite type, is a consequence (Stacks 0682).
When `A` and `B` live in one universe, the resolutions of `A[x₁, …, xₙ] ⧸ I` correspond to those
of `B` itself (`Algebra.PseudoCoherent.nonempty_finiteFreeModuleResolution_quotient_iff_compHom`).

The comparison with relative pseudo-coherence reads that notion in the model of the derived
category which `PseudoCoherence.IsModuleRelativelyPseudoCoherent` fixes
(`Homology/PseudoCoherent/Relative/Defs.lean`), with `A` and `B` in one universe.
`Algebra.pseudoCoherent_iff_isModulePseudoCoherent` reads pseudo-coherence over a single
presentation in any model.

Finite Tor dimension of a module is `StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension`, tag
0652 (4). There is no canonical derived tensor product here, so that notion carries its bifunctor,
comparison transformation and universal property as arguments — a datum certified as a *total left
derived* functor of termwise tensoring — and this definition passes them through unchanged, exactly
as `PseudoCoherence.IsRelativelyPerfect` does. The model of `D(A)` is an instance argument of
`RingHom.IsPerfectRingMap`, so the definition can be read at any model;
`RingHom.isPerfectRingMap_iff_exists_flat_roof` shows that its truth depends neither on the model
nor on the certificate.

## References

* [The Stacks Project, Definition 15.83.1 (067H)](https://stacks.math.columbia.edu/tag/067H)
* [The Stacks Project, Lemma 15.82.7 (0675)](https://stacks.math.columbia.edu/tag/0675)
-/

open CategoryTheory

universe u v w

/-- An `A`-algebra `B` is *pseudo-coherent* if `B` is a quotient `A[x₁, …, xₙ] ⧸ I` of a
polynomial algebra such that the `A[x₁, …, xₙ]`-module `A[x₁, …, xₙ] ⧸ I` has a resolution by
finite free modules.

This is Stacks 067H (1) in the form of the remark that follows it, with `B` replaced by the
isomorphic `A[x₁, …, xₙ]`-module `A[x₁, …, xₙ] ⧸ I`, which lives in the universe of `A`. By
Stacks 0675 it says that `A → B` is of finite type and that `B`, as a module over itself, is
pseudo-coherent relative to `A` (for `A` and `B` in one universe,
`Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent`). The resolution then exists
over every finite polynomial presentation
(`Algebra.PseudoCoherent.nonempty_finiteFreeModuleResolution`). When `A` and `B` live in one
universe, the condition is the same for `B` itself, made an `A[x₁, …, xₙ]`-module through the
presentation (`Algebra.PseudoCoherent.nonempty_finiteFreeModuleResolution_quotient_iff_compHom`). -/
@[stacks 067H "(1)", mk_iff]
public class Algebra.PseudoCoherent (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : Prop where
  out : ∃ (n : ℕ) (α : MvPolynomial (Fin n) A →ₐ[A] B), Function.Surjective α ∧
    Nonempty (FiniteFreeModuleResolution (MvPolynomial (Fin n) A)
      (MvPolynomial (Fin n) A ⧸ RingHom.ker α))

namespace RingHom

/-- A ring homomorphism `f : A →+* B` is *pseudo-coherent* if `B`, with the algebra structure
induced by `f`, is a pseudo-coherent `A`-algebra in the sense of Stacks 067H (1). -/
@[algebraize]
public def PseudoCoherent {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    Prop :=
  @Algebra.PseudoCoherent A B _ _ f.toAlgebra

/-- For the structure map of an algebra, `RingHom.PseudoCoherent` is pseudo-coherence of the
algebra in the sense of Stacks 067H (1). -/
public theorem pseudoCoherent_algebraMap {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] : PseudoCoherent (algebraMap A B) ↔ Algebra.PseudoCoherent A B := by
  rw [PseudoCoherent, toAlgebra_algebraMap]

/-- A ring map `A → B` is perfect if it is pseudo-coherent and `B`, regarded as an `A`-module, has
finite Tor dimension, read off the certified derived tensor product `derivedTensor` on a model of
`D(A)`. Neither the model nor the certificate matters
(`RingHom.isPerfectRingMap_iff_exists_flat_roof`). -/
@[stacks 067H "(2)", sga "6 III 4.1" "affine case"]
public def IsPerfectRingMap
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (derivedTensor :
      DerivedCategory (ModuleCat.{u} A) ⥤
        DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A))
    (comparison : ∀ N : ModuleCat.{u} A,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N) ⟶
        (StacksDraft.TorAmplitude.tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} A,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))) : Prop :=
  Algebra.PseudoCoherent A B ∧
    StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension derivedTensor comparison isLeftDerived
      (ModuleCat.of A B)

end RingHom

namespace FiniteFreeModuleResolution

variable {R : Type u} [Ring R] {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A resolution of `M` by finite free modules transported along a linear equivalence
`M ≃ₗ[R] N`: the same complex, with the augmentation followed by the equivalence. -/
public noncomputable def ofLinearEquiv (F : FiniteFreeModuleResolution R M) (e : M ≃ₗ[R] N) :
    FiniteFreeModuleResolution R N where
  complex := F.complex
  hasHomology := F.hasHomology
  π := F.π ≫ (ChainComplex.single₀ (ModuleCat.{v} R)).map e.toModuleIso.hom
  quasiIso := have := F.quasiIso; inferInstance
  free := F.free
  finite := F.finite

/-- A module with a resolution by finite free modules is finitely presented: the augmentation maps
the finite free module in degree `0` onto it, with kernel the image of the finite module in
degree `1`. -/
public theorem finitePresentation (F : FiniteFreeModuleResolution R M) :
    Module.FinitePresentation R M := by
  obtain ⟨⟨⟨C, _, π, _⟩, _⟩, _⟩ := F
  -- An opaque `P`, rather than a `let`, lets instance search find `Epi (P.π.f 0)`.
  obtain ⟨P, rfl⟩ : ∃ P : ProjectiveResolution (ModuleCat.of R M), P.complex = C :=
    ⟨{ complex := C, π }, rfl⟩
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0
    (ModuleCat.of R M)).toLinearEquiv.finitePresentation_iff.1 <|
    Module.finitePresentation_of_free_of_surjective (P.π.f 0).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      (P.exact₀.moduleCat_range_eq_ker ▸ Submodule.fg_range _)

end FiniteFreeModuleResolution

namespace Algebra.PseudoCoherent

section

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- **The algebra content of Stacks 0682.** A pseudo-coherent algebra is finitely presented, hence
of finite type (`Algebra.FiniteType.of_finitePresentation`).

The definition provides a surjection `α : P ↠ B` from a polynomial ring `P` over `A` in finitely
many variables such that `P ⧸ ker α` has a resolution by finite free `P`-modules. Degrees `0` and
`1` of the resolution make `P ⧸ ker α` a finitely presented `P`-module
(`FiniteFreeModuleResolution.finitePresentation`), so `ker α` is a finitely generated ideal. -/
public instance (priority := 100) finitePresentation [h : PseudoCoherent A B] :
    FinitePresentation A B := by
  obtain ⟨n, α, hα, ⟨F⟩⟩ := h
  have := F.finitePresentation
  exact ⟨n, α, hα, Submodule.ker_mkQ (RingHom.ker α) ▸
    Module.FinitePresentation.fg_ker _ (Submodule.mkQ_surjective _)⟩

/-- The quotient of `A[x₁, …, x_k]` by the kernel of a surjection `γ` onto `B` is isomorphic, as
an `A[x₁, …, x_k]`-module, to any `A`-algebra `B'` isomorphic to `B`, made a module through the
composite. -/
private noncomputable def quotientKerLinearEquiv {B' : Type*} [CommRing B'] [Algebra A B']
    {k : ℕ} {γ : MvPolynomial (Fin k) A →ₐ[A] B} (hγ : Function.Surjective γ) (e : B ≃ₐ[A] B') :
    letI : Module (MvPolynomial (Fin k) A) B' := Module.compHom B' (e.toAlgHom.comp γ).toRingHom
    (MvPolynomial (Fin k) A ⧸ RingHom.ker γ) ≃ₗ[MvPolynomial (Fin k) A] B' :=
  letI : Module (MvPolynomial (Fin k) A) B' := Module.compHom B' (e.toAlgHom.comp γ).toRingHom
  { ((Ideal.quotientKerAlgEquivOfSurjective hγ).trans e).toLinearEquiv.toAddEquiv with
    map_smul' := fun p x => by
      change ((Ideal.quotientKerAlgEquivOfSurjective hγ).trans e) (p • x) =
        e (γ p) * ((Ideal.quotientKerAlgEquivOfSurjective hγ).trans e) x
      rw [Algebra.smul_def, map_mul]
      simp }

/-- **The resolution exists over every presentation** (Stacks 065H). For every finite polynomial
presentation `α` of `B`, the `A[x₁, …, xₙ]`-module `A[x₁, …, xₙ] ⧸ ker α` has a resolution by finite
free modules, not only for the presentation that the definition provides. The algebra `B` is a
quotient of a polynomial algebra over `A`, hence `u`-small, and the presentations are compared on
`Shrink.{u} B` by `PseudoCoherence.nonempty_finiteFreeModuleResolution_iff_of_surjective`. -/
public theorem nonempty_finiteFreeModuleResolution [h : PseudoCoherent A B] {n : ℕ}
    (α : MvPolynomial (Fin n) A →ₐ[A] B) (hα : Function.Surjective α) :
    Nonempty (FiniteFreeModuleResolution (MvPolynomial (Fin n) A)
      (MvPolynomial (Fin n) A ⧸ RingHom.ker α)) := by
  obtain ⟨n₀, α₀, hα₀, ⟨F₀⟩⟩ := h
  have : Small.{u} B := small_of_surjective hα₀
  let e := (Shrink.algEquiv A B).symm
  let : Module (MvPolynomial (Fin n₀) A) (Shrink.{u} B) :=
    Module.compHom _ (e.toAlgHom.comp α₀).toRingHom
  let : Module (MvPolynomial (Fin n) A) (Shrink.{u} B) :=
    Module.compHom _ (e.toAlgHom.comp α).toRingHom
  obtain ⟨G⟩ := (PseudoCoherence.nonempty_finiteFreeModuleResolution_iff_of_surjective
    (α := e.toAlgHom.comp α₀) (β := e.toAlgHom.comp α) (Shrink.{u} B)
    (e.surjective.comp hα₀) (e.surjective.comp hα)).mp
    ⟨F₀.ofLinearEquiv (quotientKerLinearEquiv hα₀ e)⟩
  exact ⟨G.ofLinearEquiv (quotientKerLinearEquiv hα e).symm⟩

/-- If `e : B ≃ₐ[A] B'` and `B` is pseudo-coherent over `A`, then so is `B'`. -/
public theorem equiv {B' : Type*} [CommRing B'] [Algebra A B'] (h : PseudoCoherent A B)
    (e : B ≃ₐ[A] B') : PseudoCoherent A B' := by
  obtain ⟨n, α, hα, hF⟩ := h
  refine ⟨n, e.toAlgHom.comp α, e.surjective.comp hα, ?_⟩
  rwa [show RingHom.ker (e.toAlgHom.comp α) = RingHom.ker α by ext; simp]

end

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- When `A` and `B` live in one universe, the module `A[x₁, …, x_k] ⧸ ker γ` of the definition has
a resolution by finite free modules exactly when `B`, made an `A[x₁, …, x_k]`-module through `γ`,
has one. -/
public theorem nonempty_finiteFreeModuleResolution_quotient_iff_compHom {k : ℕ}
    {γ : MvPolynomial (Fin k) A →ₐ[A] B} (hγ : Function.Surjective γ) :
    Nonempty (FiniteFreeModuleResolution (MvPolynomial (Fin k) A)
      (MvPolynomial (Fin k) A ⧸ RingHom.ker γ)) ↔
      letI : Module (MvPolynomial (Fin k) A) B := Module.compHom B γ.toRingHom
      Nonempty (FiniteFreeModuleResolution (MvPolynomial (Fin k) A) B) := by
  let : Module (MvPolynomial (Fin k) A) B := Module.compHom B γ.toRingHom
  exact ⟨fun ⟨F⟩ => ⟨F.ofLinearEquiv (quotientKerLinearEquiv hγ AlgEquiv.refl)⟩,
    fun ⟨F⟩ => ⟨F.ofLinearEquiv (quotientKerLinearEquiv hγ AlgEquiv.refl).symm⟩⟩

end Algebra.PseudoCoherent

namespace RingHom

/-- A pseudo-coherent ring homomorphism is of finite presentation; this is Stacks 0682 for ring
maps, stated for `RingHom.PseudoCoherent`. -/
public theorem PseudoCoherent.finitePresentation {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] {f : A →+* B} (h : PseudoCoherent f) : f.FinitePresentation := by
  algebraize [f]
  exact Algebra.PseudoCoherent.finitePresentation

end RingHom

namespace Algebra

/-- Over a finite-type algebra, `A → B` is pseudo-coherent exactly when `B`, as a module over
itself, is pseudo-coherent relative to `A` (Stacks 0675). The right-hand side is read in the model
of the derived category that `PseudoCoherence.IsModuleRelativelyPseudoCoherent` fixes. -/
public theorem pseudoCoherent_iff_isModuleRelativelyPseudoCoherent
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B] [FiniteType A B] :
    PseudoCoherent A B ↔
      PseudoCoherence.IsModuleRelativelyPseudoCoherent (R := A) (A := B) B := by
  rw [(PseudoCoherence.moduleRelativelyPseudoCoherent_iff_finiteness_and_resolutions
    (R := A) (A := B) B).2.2.2]
  refine ⟨fun h n α hα => ?_, fun h => ?_⟩
  · exact (PseudoCoherent.nonempty_finiteFreeModuleResolution_quotient_iff_compHom hα).mp
      (h.nonempty_finiteFreeModuleResolution α hα)
  · obtain ⟨n, α, hα⟩ := (FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp ‹_›
    exact ⟨n, α, hα,
      (PseudoCoherent.nonempty_finiteFreeModuleResolution_quotient_iff_compHom hα).mpr (h n α hα)⟩

/-- **Stacks 067H (1) as worded.** A ring map `A → B` is pseudo-coherent exactly when it is of
finite type and `B`, as a module over itself, is pseudo-coherent relative to `A`. The right-hand
side is read in the model of the derived category that
`PseudoCoherence.IsModuleRelativelyPseudoCoherent` fixes. -/
public theorem pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent
    {A : Type u} {B : Type u} [CommRing A] [CommRing B] [Algebra A B] :
    PseudoCoherent A B ↔
      ∃ h : FiniteType A B,
        letI := h
        PseudoCoherence.IsModuleRelativelyPseudoCoherent (R := A) (A := B) B :=
  ⟨fun h => ⟨inferInstance, pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mp h⟩,
    fun ⟨_, h⟩ => pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr h⟩

end Algebra
