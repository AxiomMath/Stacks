module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite presentation of a constant sheaf of modules

Let `C` be a site with topology `J`, let `R` be a ring and let `M` be an `R`-module. Part (2)
of Stacks Tag 093N says that, on a site whose sheaf topos is not empty, the constant sheaf of
modules `M̲` over the constant sheaf of rings `R̲` is of finite presentation exactly when `M`
is a finitely presented `R`-module.

The implication from the sheaf to the module is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafFiniteness`, as
`Stacks.SheafOfModules.Constant.finitePresentation_of_isFinitePresentation`. This file proves
the remaining implication and assembles the equivalence.

## Main results

* `Stacks.SheafOfModules.Constant.isFinitePresentation_of_finitePresentation` — a constant
  sheaf of modules on a finitely presented module is of finite presentation.
* `Stacks.SheafOfModules.Constant.constantModuleSheaf_isFinitePresentation_iff` — the
  equivalence, i.e. the content of Stacks Tag 093N part (2).

## Implementation notes

* **The proof of the new implication.** A finitely presented `M` is in particular finite, so
  there is a surjection `φ : R^n ↠ M` of `R`-modules; `Module.FinitePresentation.fg_ker` makes
  `ker φ` a finite module, so there is a surjection `κ : R^m ↠ ker φ`. The constant sheaf
  functor preserves finite colimits, hence epimorphisms, and preserves finite limits, hence
  kernels; so `φ` gives generating sections of `M̲` indexed by a finite type, and `κ` gives
  generating sections — again finitely indexed — of the kernel of those generators, after the
  identification `kernel (free (Fin n) ⟶ M̲) ≅ (ker φ)̲` supplied by `kernelIsIsoComp` and
  `kernelIsoConstant`. That is a `SheafOfModules.Presentation` with `IsFinite`, and a global
  finite presentation gives a finite presentation on the trivial cover.
* **No new mathematics is needed for the kernel.** The constant sheaf functor's left
  exactness, `kernelIsoConstant`, and part (1) are all already in
  `ConstantSheafFiniteness.lean`; only the packaging into `Presentation` is new here.
* **Why no products on the site are assumed.** Passing a global `Presentation` to the trivial
  cover is Mathlib's `SheafOfModules.Presentation.quasicoherentData`, which asks restriction to
  a slice site to preserve colimits; the only route to that is
  `SheafOfModules.overPushforwardOverAdj`, whose right adjoint is built from
  `CategoryTheory.Over.star`, i.e. from binary products on the site — which Stacks (Tag 00VH)
  deliberately does not require of a site. The products-free substitute used here is
  `Stacks.SheafOfModules.SliceFinite.quasicoherentDataOfPresentation`: for a *finite*
  presentation only finite coproducts and one cokernel are ever restricted, finite coproducts
  are preserved by any additive functor, and the cokernel is handled by identifying the
  restricted kernel instead of mapping the colimit. The same substitution removes the products
  and the pullbacks from the other implication, where they came in through Tag 01BP; see
  `Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_generatingSections`.
* Consequently the equivalence carries exactly the hypotheses of the source — sheafification
  and local bijectivity for `RingCat` and `AddCommGrpCat` on `J` and on the slice topologies,
  which are what is needed to *state* that `M̲` is a sheaf of modules of finite presentation —
  and it carries the `@[stacks 093N]` attribute.
* The universes `u` (site objects), `v` (site morphisms) and `w` (ring and module) are
  independent. Nothing is narrowed.

## References

* [Stacks Project, Tag 093N](https://stacks.math.columbia.edu/tag/093N)
* [Stacks Project, Tag 00VH](https://stacks.math.columbia.edu/tag/00VH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules.Constant

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {R : Type w} [Ring R]
variable [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 093N, part (2), the implication from the module to the sheaf.** The
constant sheaf of modules on a finitely presented module is of finite presentation.

A surjection `φ : R^n ↠ M` has finitely generated kernel, so there is a surjection
`κ : R^m ↠ ker φ`. The constant sheaf functor carries both to epimorphisms and identifies
`ker φ` with the kernel of the first, which gives a finite global presentation of `M̲`; a
global finite presentation gives a finite presentation on the trivial cover. -/
theorem isFinitePresentation_of_finitePresentation (M : ModuleCat.{w} R)
    [Module.FinitePresentation R M] :
    SheafOfModules.IsFinitePresentation (constantModuleSheaf J M) := by
  classical
  have hs0 : HasSheafify J AddCommGrpCat.{w} :=
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  have hs1 : ∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w} := fun _ =>
    AlgebraicGeometry.SheafOfModules.hasSheafify_of_locallyBijective
  -- a finite module is a quotient of a finite free module, indexed in the ring universe
  have hepi : ∀ (N : ModuleCat.{w} R) [Module.Finite R N],
      ∃ (n : ℕ) (φ : ModuleCat.of R (ULift.{w} (Fin n) → R) ⟶ N), Epi φ := by
    intro N _
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R N
    let e : (Fin n → R) ≃ₗ[R] (ULift.{w} (Fin n) → R) :=
      LinearEquiv.funCongrLeft R R (Equiv.ulift.{w, 0})
    exact ⟨n, ModuleCat.ofHom (f ∘ₗ e.symm.toLinearMap),
      (ModuleCat.epi_iff_surjective _).mpr (hf.comp e.symm.surjective)⟩
  -- a finite free presentation of `M`, with the index types lifted to the ring universe
  obtain ⟨n, φ, hφ⟩ := hepi M
  -- the kernel of `φ` is a finite module, so it too is finitely generated
  have := Module.Finite.iff_fg.mpr
    (Module.FinitePresentation.fg_ker φ.hom ((ModuleCat.epi_iff_surjective φ).mp hφ))
  have : Module.Finite R (kernel φ : ModuleCat.{w} R) :=
    Module.Finite.equiv (ModuleCat.kernelIsoKer φ).toLinearEquiv.symm
  obtain ⟨m, κ, hκ⟩ := hepi (kernel φ : ModuleCat.{w} R)
  -- the generating sections of the constant sheaf
  let ψ : SheafOfModules.free (R := (constantSheaf J RingCat.{w}).obj (RingCat.of R))
      (ULift.{w} (Fin n)) ⟶ constantModuleSheaf J M :=
    (freeIsoPi J (ULift.{w} (Fin n))).hom ≫ constantModuleSheafMap J φ
  have : Epi (constantModuleSheafMap J φ) := epi_constantModuleSheafMap J φ
  -- generating sections given by an epimorphism from a free module
  let mk : ∀ {N : SheafOfModules.{w} ((constantSheaf J RingCat.{w}).obj (RingCat.of R))}
      {I : Type w} (f : SheafOfModules.free I ⟶ N), Epi f → N.GeneratingSections :=
    fun {N I} f hf => { I := I, s := N.freeHomEquiv f, epi := by simpa using hf }
  let gen := mk ψ (epi_comp _ _)
  have hgen : gen.π = ψ := (constantModuleSheaf J M).freeHomEquiv.symm_apply_apply ψ
  -- the kernel of the generators is the constant sheaf on the kernel of `φ`
  let ek : kernel gen.π ≅ constantModuleSheaf J (kernel φ) :=
    eqToIso (by rw [hgen]) ≪≫ kernelIsIsoComp (freeIsoPi J (ULift.{w} (Fin n))).hom
      (constantModuleSheafMap J φ) ≪≫ (kernelIsoConstant J φ).symm
  have : Epi (constantModuleSheafMap J κ) := epi_constantModuleSheafMap J κ
  let rel := mk ((freeIsoPi J (ULift.{w} (Fin m))).hom ≫ constantModuleSheafMap J κ ≫ ek.inv)
    (epi_comp _ _)
  let P : (constantModuleSheaf J M).Presentation := ⟨gen, rel⟩
  have hP : P.IsFinite :=
    { isFiniteType_generators := ⟨inferInstanceAs (Finite (ULift.{w} (Fin n)))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite (ULift.{w} (Fin m)))⟩ }
  exact Stacks.SheafOfModules.SliceFinite.isFinitePresentation_of_presentation P

/-- **Stacks Project, Tag 093N, part (2).** On a site with an object that is not sheaf
theoretically empty, a constant sheaf of modules is of finite presentation if and only if its
value is a finitely presented module. -/
@[stacks 093N "finite_presentation"]
theorem constantModuleSheaf_isFinitePresentation_iff
    (hJ : ∃ U : C, ¬ (⊥ : Sieve U) ∈ J U) (M : ModuleCat.{w} R) :
    SheafOfModules.IsFinitePresentation (constantModuleSheaf J M) ↔
      Module.FinitePresentation R M :=
  ⟨fun _ => finitePresentation_of_isFinitePresentation J hJ M,
    fun _ => isFinitePresentation_of_finitePresentation J M⟩

end Stacks.SheafOfModules.Constant

end
