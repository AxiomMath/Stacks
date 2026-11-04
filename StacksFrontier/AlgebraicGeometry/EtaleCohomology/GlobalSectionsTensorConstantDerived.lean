module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.Basic
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ConstantBoundedBelow
public import StacksFrontier.Homology.DerivedCategory.Monoidal.BoundedBelowSubcategory
public import StacksFrontier.Homology.KFlat.ULiftIntFlatRepresentative

/-!
# The derived constant coefficient object of a bounded below complex of integers

Let `(C, J)` be a site and let `Λ = ULift ℤ` be a copy of the integers in the universe of the
sections of the sheaves on it. For `K ∈ D(Λ)` the source of [Stacks, Tag 0F0E] writes `K̲` for
the constant coefficient object of `K` and asserts, when `K` and `E ∈ D(C, J)` are bounded
below and the site is the small étale site of a quasi-compact and quasi-separated scheme,

> `RΓ(X, E ⊗_ℤ^L K̲) = RΓ(X, E) ⊗_ℤ^L K`.

This file supplies the object `K̲` and the first two steps of the source's proof: it constructs
the derived constant sheaf functor **on complexes**, `D(Λ) ⥤ D(Sheaf J (ModuleCat Λ))`, and it
proves that for `K` bounded below the derived tensor product `E ⊗_ℤ^L K̲` is computed by an
ordinary total tensor complex, with no resolution of either factor left implicit.

## Main definitions

* `Stacks.ModuleSheaf.derivedConstantSheafComplexes` — **the derived constant sheaf functor on
  complexes** `D(Λ) ⥤ D(Sheaf J (ModuleCat Λ))`, with its factorisation
  `derivedConstantSheafComplexesFactors` through the degreewise constant sheaf functor and its
  compatibility `derivedConstantSheafComplexesSingleFunctorIso` with placing a single module in
  degree zero.

## Main results

* `Stacks.ModuleSheaf.exists_derivedTensor_derivedConstantSheafComplexes_iso` — **steps 1 and 2
  of the source's proof.** For `E` cohomologically `≥ a` and `K` cohomologically `≥ b` there are
  a complex `N` of sheaves which is strictly `≥ a` and represents `E`, and a complex `P` of flat
  `Λ`-modules which is strictly `≥ b - 1` and represents `K`, such that

  > `E ⊗_ℤ^L K̲ ≅ Q(N ⊗ P̲)`,

  the right-hand side being the class of the ordinary total tensor complex of `N` with the
  complex of constant sheaves on the terms of `P`.
* `Stacks.ModuleSheaf.isGE_derivedTensor_derivedConstantSheafComplexes` — `E ⊗_ℤ^L K̲` is
  cohomologically `≥ a + (b - 1)`; in particular it is again bounded below, which is what makes
  the statement of the source's lemma about an object of `D⁺` at all.

## Implementation notes

*Why the total complex, and where the flatness comes from.* The derived tensor product is
computed by the total tensor complex as soon as one factor is K-flat, which is
`Stacks.ModuleSheaf.derivedTensorIsoOfKFlat`. The factor made K-flat here is `P̲`. That it is
K-flat is `Stacks.ModuleSheaf.kFlat_constantSheaf_of_isStrictlyGE_of_flat`, which asks for a
strictly bounded below complex of modules whose terms **and cycles** are flat — the terms alone
do not suffice, since a bounded below complex of flat objects need not be K-flat. Both
hypotheses are produced over the integers:
`CochainComplex.ULiftInt.exists_flat_isStrictlyGE_iso` is the source's step 1, which represents
a `K` cohomologically `≥ b` by a complex of flat modules strictly `≥ b - 1` (the drop by one is
`ℤ` having global dimension one, [Stacks, Tag 0653]), and
`CochainComplex.ULiftInt.flat_cycles` makes the cycles flat, a submodule of a flat module over
`ℤ` being flat.

*The derived constant sheaf functor needs no resolution.* `constantSheaf J A` is the constant
presheaf followed by sheafification, and both are exact, so it descends to derived categories by
`CategoryTheory.Functor.mapDerivedCategory`; no K-flat or K-injective resolution enters its
construction. The repository previously had only the degree-zero functor
`Stacks.ConstantSheaf.derivedConstantSheaf`, `ModuleCat Λ ⥤ D(Sheaf J (ModuleCat Λ))`, and the
degreewise functor on complexes; `derivedConstantSheafComplexesSingleFunctorIso` identifies the
restriction of the functor built here along `singleFunctor 0` with the former.

*Universes.* Everything is at the universe shape of the derived tensor product of sheaves of
modules: the site is `C : Type u` with `Category.{v} C` and the coefficient ring is
`Λ : Type w` with `UnivLE.{max u v, w}`. The coefficient ring of this file is `ULift.{w} ℤ`,
since `CochainComplex.ULiftInt.exists_flat_isStrictlyGE_iso` and the monoidal structure on
`ModuleCat.{w} Λ` both need the ring in the universe of its modules.

*The site is left general.* Nothing below is special to the étale site, so the statements are
made for an arbitrary `(C, J)`; the site of the source's lemma is the small étale site of a
scheme `X : Scheme.{u}`, which is `X.Etale : Type (u + 1)` with `Category.{u}`, and
instantiating there means taking `u := u + 1`, `v := u` and a coefficient universe
`w = max (u + 1) v`. That instantiation, at `v = 0`, is the one made in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGlobalSectionsTensorConstant`.

## Where the lemma is proved

The lemma itself is `nonempty_derivedSections_tensor_derivedConstantSheaf_iso`, in the namespace
`Stacks.EtaleCohomology.DerivedTensorConstant` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGlobalSectionsTensorConstant`. It uses
the functor `derivedConstantSheafComplexes` of this file and the same two flatness inputs, but it
represents `E` by a bounded below complex of injective sheaves and replaces the dévissages of
steps 3 to 5 by Leray's acyclicity lemma applied to the total tensor complex.

## References

* [Stacks Project, Tag 0F0E](https://stacks.math.columbia.edu/tag/0F0E)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe t t' w v u

namespace Stacks.ModuleSheaf

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory monoidalClosed
  CochainComplex.braidedCategory derivedMonoidal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max u v, w}]
  [HasDerivedCategory.{t} (Sheaf J (ModuleCat.{w} (ULift.{w} ℤ)))]
  [HasDerivedCategory.{t'} (ModuleCat.{w} (ULift.{w} ℤ))]

/-- **The derived constant sheaf functor on complexes**, `K ↦ K̲`, from the derived category of
`Λ`-modules to the derived category of sheaves of `Λ`-modules on a site, for `Λ` a copy of the
integers in the universe of the sections. The constant sheaf functor is the constant presheaf
followed by sheafification and both are exact, so it descends to derived categories degreewise;
no resolution is involved. -/
def derivedConstantSheafComplexes :
    DerivedCategory (ModuleCat.{w} (ULift.{w} ℤ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{w} (ULift.{w} ℤ))) :=
  (constantSheaf J (ModuleCat.{w} (ULift.{w} ℤ))).mapDerivedCategory

/-- **The constant coefficient object of a complex is the class of the complex of constant
sheaves on its terms.** This is what makes `derivedConstantSheafComplexes` computable in
practice: it has no resolution to unwind. -/
def derivedConstantSheafComplexesFactors :
    DerivedCategory.Q ⋙ derivedConstantSheafComplexes J ≅
      (constantSheaf J (ModuleCat.{w} (ULift.{w} ℤ))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (constantSheaf J (ModuleCat.{w} (ULift.{w} ℤ))).mapDerivedCategoryFactors

/-- **On a module placed in degree `n` the derived constant sheaf functor is the constant sheaf
placed in degree `n`.** This identifies the restriction of `derivedConstantSheafComplexes` along
`singleFunctor 0` with the degree-zero functor `Stacks.ConstantSheaf.derivedConstantSheaf`. -/
def derivedConstantSheafComplexesSingleFunctorIso (n : ℤ) :
    DerivedCategory.singleFunctor (ModuleCat.{w} (ULift.{w} ℤ)) n ⋙
        derivedConstantSheafComplexes J ≅
      constantSheaf J (ModuleCat.{w} (ULift.{w} ℤ)) ⋙
        DerivedCategory.singleFunctor (Sheaf J (ModuleCat.{w} (ULift.{w} ℤ))) n :=
  (constantSheaf J (ModuleCat.{w} (ULift.{w} ℤ))).mapDerivedCategorySingleFunctor n

/-- **Steps 1 and 2 of the proof of [Stacks, Tag 0F0E].** Let `E` be an object of the derived
category of sheaves of `Λ`-modules on a site whose cohomology vanishes below `a`, and let `K` be
an object of the derived category of `Λ`-modules whose cohomology vanishes below `b`, for `Λ` a
copy of the integers in the universe of the sections. Then there are

* a complex `N` of sheaves, vanishing below `a`, with `E ≅ Q(N)`, and
* a complex `P` of **flat** `Λ`-modules, vanishing below `b - 1`, with `Q(P) ≅ K`,

such that the derived tensor product of `E` with the constant coefficient object of `K` is the
class of the ordinary total tensor complex:

> `E ⊗_ℤ^L K̲ ≅ Q(N ⊗ P̲)`.

The complex `P` is step 1 of the source,
`CochainComplex.ULiftInt.exists_flat_isStrictlyGE_iso`, where the loss of one degree is `ℤ`
having global dimension one. Step 2 is the identification of the derived tensor product with the
total complex: `P̲` is K-flat by
`Stacks.ModuleSheaf.kFlat_constantSheaf_of_isStrictlyGE_of_flat`, whose hypothesis on the cycles
of `P` is met because over `ℤ` a submodule of a flat module is flat
(`CochainComplex.ULiftInt.flat_cycles`), and a K-flat factor computes the derived tensor product
against an arbitrary other factor by `Stacks.ModuleSheaf.derivedTensorIsoOfKFlat`. -/
theorem exists_derivedTensor_derivedConstantSheafComplexes_iso
    (E : DerivedCategory (Sheaf J (ModuleCat.{w} (ULift.{w} ℤ)))) (a : ℤ) [E.IsGE a]
    (K : DerivedCategory (ModuleCat.{w} (ULift.{w} ℤ))) (b : ℤ) [K.IsGE b] :
    ∃ (N : CochainComplex (Sheaf J (ModuleCat.{w} (ULift.{w} ℤ))) ℤ)
      (P : CochainComplex (ModuleCat.{w} (ULift.{w} ℤ)) ℤ),
      N.IsStrictlyGE a ∧ P.IsStrictlyGE (b - 1) ∧
        (∀ q, Module.Flat (ULift.{w} ℤ) (P.X q)) ∧
        Nonempty (E ≅ DerivedCategory.Q.obj N) ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) ∧
        Nonempty (E ⊗ (derivedConstantSheafComplexes J).obj K ≅
          DerivedCategory.Q.obj (N ⊗
            ((constantSheaf J (ModuleCat.{w} (ULift.{w} ℤ))).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨N, hN, ⟨eN⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE E a
  obtain ⟨P, hP, hflat, ⟨eP⟩⟩ := CochainComplex.ULiftInt.exists_flat_isStrictlyGE_iso K b
  refine ⟨N, P, hN, hP, hflat, ⟨eN⟩, ⟨eP⟩, ?_⟩
  have := hP
  have hkf := kFlat_constantSheaf_of_isStrictlyGE_of_flat J P (b - 1) hflat
    (CochainComplex.ULiftInt.flat_cycles P hflat)
  exact ⟨(eN ⊗ᵢ ((derivedConstantSheafComplexes J).mapIso eP.symm ≪≫
    (derivedConstantSheafComplexesFactors J).app P)) ≪≫ derivedTensorIsoOfKFlat N hkf⟩

/-- **The derived tensor product of a bounded below object with a bounded below constant
coefficient object is bounded below.** If the cohomology of `E` vanishes below `a` and that of
`K` below `b`, then the cohomology of `E ⊗_ℤ^L K̲` vanishes below `a + (b - 1)`.

This is what says that the two sides of [Stacks, Tag 0F0E] are objects of `D⁺`, so that
`RΓ` of the bounded below derived category may be applied to the left-hand side at all. It
follows from the previous theorem: the total tensor complex of a complex vanishing below `a`
and one vanishing below `b - 1` vanishes below `a + (b - 1)`, by
`CochainComplex.KFlatMonoidal.isStrictlyGE_tensorObj`. The loss of one degree is the same one as
in step 1, and is not removable by this argument. -/
theorem isGE_derivedTensor_derivedConstantSheafComplexes
    (E : DerivedCategory (Sheaf J (ModuleCat.{w} (ULift.{w} ℤ)))) (a : ℤ) [E.IsGE a]
    (K : DerivedCategory (ModuleCat.{w} (ULift.{w} ℤ))) (b : ℤ) [K.IsGE b] :
    (E ⊗ (derivedConstantSheafComplexes J).obj K).IsGE (a + (b - 1)) := by
  obtain ⟨N, P, hN, hP, hflat, -, -, ⟨e⟩⟩ :=
    exists_derivedTensor_derivedConstantSheafComplexes_iso J E a K b
  have := hN
  have := hP
  have := CochainComplex.KFlatMonoidal.isStrictlyGE_tensorObj
    (Sheaf J (ModuleCat.{w} (ULift.{w} ℤ))) N
    (((constantSheaf J (ModuleCat.{w} (ULift.{w} ℤ))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P) a (b - 1)
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm (a + (b - 1))

end Stacks.ModuleSheaf

end
