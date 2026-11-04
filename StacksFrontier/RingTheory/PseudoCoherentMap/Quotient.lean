module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.Homology.PseudoCoherent.Relative.Finite
public import StacksFrontier.RingTheory.PseudoCoherentMap.Absolute
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat

@[expose] public noncomputable section

/-!
# Pseudo-coherence of a quotient of a flat algebra of finite presentation

Let `A → B` be flat of finite presentation and let `I` be an ideal of `B`. Then `A → B ⧸ I` is a
pseudo-coherent ring map exactly when `I` is pseudo-coherent as a `B`-module.

## Main results

* `Algebra.pseudoCoherent_quotient_iff_isModulePseudoCoherent` (Stacks 0697).
* `StacksDraft.PseudoCoherence.isModulePseudoCoherent_ideal_iff_quotient`: an ideal of a
  commutative ring is pseudo-coherent as a module exactly when the quotient by it is.

## Implementation notes

The quotient `B ⧸ I` is finite as a `B`-module, so Stacks 0673 moves relative pseudo-coherence
over `A` across `B → B ⧸ I`: pseudo-coherence of `B ⧸ I` relative to `A` in `D(B ⧸ I)` is
pseudo-coherence of its restriction to `B` relative to `A` in `D(B)`. Since `A → B` is flat of
finite presentation it is pseudo-coherent by Stacks 067J, so Stacks 0DHQ turns that relative
notion over `A` into the absolute one over `B`. What remains is to compare `B ⧸ I` with `I` as
`B`-modules, which the short exact sequence `0 → I → B → B ⧸ I → 0` and the two-out-of-three
property of Stacks 064V do, using that `B` is pseudo-coherent over itself because it is finite
free.

The Stacks proof instead fixes a presentation `B = A[x_1, …, x_n]/J`, observes that `B` is
pseudo-coherent as an `A[x_1, …, x_n]`-module, and crosses the surjection with Stacks 064Z. That
is the same argument: the route taken here reads the polynomial presentation off the definition
of a pseudo-coherent ring map through Stacks 0DHQ instead of choosing one by hand, and Stacks 0673
is Stacks 064Z for a finite ring map.

Restriction of scalars along `algebraMap B (B ⧸ I)` applied to `B ⧸ I` as a module over itself is
the canonical `B`-module structure on `B ⧸ I`, definitionally, so no comparison isomorphism is
needed at that step.

## References

* [The Stacks Project, Lemma 15.83.14 (0697)](https://stacks.math.columbia.edu/tag/0697)
* [The Stacks Project, Lemma 15.82.5 (0673)](https://stacks.math.columbia.edu/tag/0673)
* [The Stacks Project, Lemma 15.83.11 (0DHQ)](https://stacks.math.columbia.edu/tag/0DHQ)
* [The Stacks Project, Lemma 15.82.2 (064V)](https://stacks.math.columbia.edu/tag/064V)
* [The Stacks Project, Lemma 15.83.5 (067J)](https://stacks.math.columbia.edu/tag/067J)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StacksDraft.PseudoCoherence PseudoCoherence

universe u

namespace StacksDraft.PseudoCoherence

attribute [local instance] HasDerivedCategory.standard

/-- A ring is pseudo-coherent as a module over itself, being finite free. -/
private lemma isModulePseudoCoherent_self (B : Type u) [CommRing B] :
    IsModulePseudoCoherent (R := B) B :=
  ⟨(CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B),
    (isBoundedFiniteFree_single _ 0).isBoundedAboveFiniteFree, ⟨Iso.refl _⟩⟩

/-- **The two-out-of-three step of Stacks 0697.** An ideal of a commutative ring is
pseudo-coherent as a module exactly when the quotient by it is.

The ring sits in the middle of the short exact sequence `0 → I → B → B ⧸ I → 0` and is
pseudo-coherent over itself, so Stacks 064V applied to the associated distinguished triangle
transfers pseudo-coherence between the two outer terms in both directions. -/
theorem isModulePseudoCoherent_ideal_iff_quotient {B : Type u} [CommRing B] (I : Ideal B) :
    IsModulePseudoCoherent (R := B) I ↔ IsModulePseudoCoherent (R := B) (B ⧸ I) := by
  let S : ShortComplex (ModuleCat.{u} B) :=
    ShortComplex.mk (ModuleCat.ofHom I.subtype)
      (ModuleCat.ofHom (Ideal.Quotient.mkₐ B I).toLinearMap) (by
        ext x
        show Ideal.Quotient.mk I (x : B) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr x.property)
  have hS : S.ShortExact := by
    refine {
      exact := ?_
      mono_f := (ModuleCat.mono_iff_injective _).mpr I.subtype_injective
      epi_g := (ModuleCat.epi_iff_surjective _).mpr Ideal.Quotient.mk_surjective }
    refine (ShortComplex.moduleCat_exact_iff_range_eq_ker S).mpr (le_antisymm ?_ ?_)
    · rintro x ⟨y, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr y.property
    · intro x hx
      change Ideal.Quotient.mk I x = 0 at hx
      exact ⟨⟨x, Ideal.Quotient.eq_zero_iff_mem.mp hx⟩, rfl⟩
  have : PreservesFiniteLimits (CochainComplex.singleFunctor (ModuleCat.{u} B) 0) :=
    inferInstanceAs (PreservesFiniteLimits
      (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0))
  have : PreservesFiniteColimits (CochainComplex.singleFunctor (ModuleCat.{u} B) 0) :=
    inferInstanceAs (PreservesFiniteColimits
      (HomologicalComplex.single (ModuleCat.{u} B) (ComplexShape.up ℤ) 0))
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  have hSC := hS.map (CochainComplex.singleFunctor (ModuleCat.{u} B) 0)
  have hTd : DerivedCategory.triangleOfSES hSC ∈ distinguishedTriangles := by
    simpa using DerivedCategory.triangleOfSES_distinguished hSC
  have hthree := isPseudoCoherent_of_distinguished (DerivedCategory.triangleOfSES hSC) hTd
  have hB : IsPseudoCoherent (DerivedCategory.triangleOfSES hSC).obj₂ :=
    isModulePseudoCoherent_self B
  exact ⟨fun h ↦ hthree.1 h hB, fun h ↦ hthree.2.2 hB h⟩

end StacksDraft.PseudoCoherence

namespace Algebra

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks 0697.** Let `A → B` be a flat ring map of finite presentation and let `I` be an
ideal of `B`. Then `A → B ⧸ I` is pseudo-coherent if and only if `I` is pseudo-coherent as a
`B`-module.

Pseudo-coherence of `A → B ⧸ I` is pseudo-coherence of `B ⧸ I` relative to `A`; Stacks 0673
restricts that along the finite map `B → B ⧸ I`, Stacks 0DHQ makes it absolute over `B` because
`A → B` is itself pseudo-coherent by Stacks 067J, and Stacks 064V exchanges `B ⧸ I` for `I`. -/
@[stacks 0697]
theorem pseudoCoherent_quotient_iff_isModulePseudoCoherent
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    [Algebra.FinitePresentation A B] (I : Ideal B) :
    Algebra.PseudoCoherent A (B ⧸ I) ↔ IsModulePseudoCoherent (R := B) I := by
  have hAB : Algebra.PseudoCoherent A B :=
    (RingHom.isPerfectRingMap_of_flat_of_finitePresentation A B).1
  have : Module.Finite B (B ⧸ I) :=
    Module.Finite.of_surjective (Algebra.linearMap B (B ⧸ I)) Ideal.Quotient.mk_surjective
  have hdef : Algebra.PseudoCoherent A (B ⧸ I) ↔
      IsModuleRelativelyPseudoCoherent (R := A) (A := B ⧸ I) (B ⧸ I) :=
    Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent
  have hfinite := isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
    (R := A) (A := B) (B := B ⧸ I)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (B ⧸ I)) 0).obj
      (ModuleCat.of (B ⧸ I) (B ⧸ I))) 0
  dsimp only at hfinite
  have habs := relativelyPseudoCoherent_iff_pseudoCoherent (R := A) (A := B) hAB
    ((ModuleCat.restrictScalars.{u} (algebraMap B (B ⧸ I))).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (B ⧸ I)) 0).obj
        (ModuleCat.of (B ⧸ I) (B ⧸ I)))) 0
  have hsingle := ((ModuleCat.restrictScalars.{u}
    (algebraMap B (B ⧸ I))).mapDerivedCategorySingleFunctor 0).app (ModuleCat.of (B ⧸ I) (B ⧸ I))
  refine (hdef.trans (hfinite.2.trans (habs.2.trans ?_))).trans
    (isModulePseudoCoherent_ideal_iff_quotient I).symm
  exact ⟨fun h ↦ h.ofIso hsingle, fun h ↦ h.ofIso hsingle.symm⟩

end Algebra

end
