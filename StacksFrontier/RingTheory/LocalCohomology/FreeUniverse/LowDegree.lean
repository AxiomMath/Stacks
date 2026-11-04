module

public import StacksFrontier.RingTheory.LocalCohomology.FreeUniverse.Restriction
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Reduction

/-!
# The affine localization triangle data at an independent module universe

Let `I` be a finitely generated ideal of a commutative ring `R` in `Type u`, presented by a
finite family of generators `f : Fin r → R`, and let the module universe `v` be *independent* of
`u`. This file assembles a term of
`Stacks.LocalCohomology.LocalizationTriangleData.{u, v} R I hI` out of the four fields supplied by
`StacksFrontier/RingTheory/LocalCohomology/FreeUniverse/Triangle.lean` and the three sections fields
supplied here.

The sections fields come from the small model of the Čech complex exactly as they do at the
pinned universe. The degree-zero comparison is
`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKerFree` followed by the sheaf axiom
`Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections`; its naturality is
`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKerFree_naturality` followed by
`Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections_naturality`; and the formula
`m ↦ m/1` is `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKerFree_restriction`
followed by
`Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections_moduleSectionsMk`. The three
sheaf-side inputs hold with the module universe independent of the ring universe: the sections of
the associated sheaf live in `Type (max u v)` whatever `v` is, and the comparison between them
and the `Type v` cohomology of derived sections is a universe-heterogeneous `LinearEquiv`.

## Main definitions

* `Stacks.LocalCohomology.cechSectionsIsoFree` — the degree-zero sections comparison at an
  independent module universe.
* `Stacks.LocalCohomology.cechLocalizationTriangleDataFree` — **the affine localization triangle
  data of Stacks 0DWR at a module universe independent of the ring universe.**

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (I : Ideal R)
  (hIf : Ideal.span (Set.range f) = I)

/-! ### The degree-zero sections comparison -/

/-- **The degree-zero sections comparison of the localization triangle, at an independent module
universe.** The degree-zero cohomology of derived sections on `U = Spec R \ V(I)` is the module of
sections of `M̃` on `U`. -/
def cechSectionsIsoFree (M : ModuleCat.{v} R) :
    (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
        ((cechComplementFunctorShrink.{v} f).obj M) ≃ₗ[R]
      complementGlobalSections R I (complementTilde R I M) :=
  (cechComplementHomologyZeroEquivKerFree.{v} f M).trans
    (kerCechDOneEquivComplementGlobalSections I M f hIf)

/-- The degree-zero sections comparison is natural in the module. -/
theorem cechSectionsIsoFree_naturality {M N : ModuleCat.{v} R} (g : M ⟶ N)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).obj
      ((cechComplementFunctorShrink.{v} f).obj M)) :
    cechSectionsIsoFree.{v} f I hIf N ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
        ((cechComplementFunctorShrink.{v} f).map g) x) =
      (associatedAbPresheafMap g).app
        (op ((complementZeroLocus R I).ι ''ᵁ ⊤)) (cechSectionsIsoFree.{v} f I hIf M x) := by
  show kerCechDOneEquivComplementGlobalSections I N f hIf
      (cechComplementHomologyZeroEquivKerFree.{v} f N
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechComplementFunctorShrink.{v} f).map g) x)) = _
  rw [cechComplementHomologyZeroEquivKerFree_naturality]
  exact kerCechDOneEquivComplementGlobalSections_naturality f I hIf g _

/-- The map induced on sections by the second arrow of the triangle sends `m` to the constant
fraction `m / 1`. -/
theorem cechSectionsIsoFree_restriction (M : ModuleCat.{v} R) (m : M) :
    cechSectionsIsoFree.{v} f I hIf M
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{v} R) 0).inv.app M m)) =
      ⟨fun x ↦ LocalizedModule.mk m (1 : x.1.asIdeal.primeCompl),
        fun x ↦ ⟨_, x.2, 𝟙 _, m, 1, fun y ↦ ⟨by simp [Ideal.IsPrime.one_notMem], rfl⟩⟩⟩ := by
  show kerCechDOneEquivComplementGlobalSections I M f hIf
      (cechComplementHomologyZeroEquivKerFree.{v} f M
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) 0).map
          ((cechRestrictionShrink.{v} f).app M)
            ((DerivedCategory.singleFunctorCompHomologyFunctorIso
              (ModuleCat.{v} R) 0).inv.app M m))) = _
  rw [kerCechDOneEquivComplementGlobalSections_moduleSectionsMk f I M hIf m _
    (fun i => cechComplementHomologyZeroEquivKerFree_restriction.{v} f M m i)]
  rfl

/-! ### The localization triangle data -/

variable (hI : I.FG)

/-- **The affine localization triangle data of Stacks 0DWR at a module universe independent of
the ring universe.** For an ideal `I = (f₁, …, f_r)` of a commutative ring `R`, the localization
triangle
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`
over `U = Spec R \ V(I)` exists functorially in the module, with the counit of Stacks 0A6Q as its
first map, and with the degree-zero cohomology of its third term identified with the sections of
the associated sheaf on `U` so that the second map is `m ↦ m / 1` — for a module universe `v`
independent of the ring universe `u`.

This is `Stacks.LocalCohomology.cechLocalizationTriangleData` with the constraint
`ModuleCat.{max u v}` removed: all seven pieces of data come from the small model
`Cech.cechComplexShrink` of the Čech complex instead of from `Cech.cechComplex`. -/
def cechLocalizationTriangleDataFree : LocalizationTriangleData.{u, v} R I hI :=
  localizationTriangleDataOfSectionsIsoShrink.{v} f I hI hIf
    (fun M => cechSectionsIsoFree.{v} f I hIf M)
    (fun {_ _} g x => cechSectionsIsoFree_naturality.{v} f I hIf g x)
    (fun M m => cechSectionsIsoFree_restriction.{v} f I hIf M m)

end Stacks.LocalCohomology

end
