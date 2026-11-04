module

public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Naturality

/-!
# The localization triangle data, reduced to the mapping-cone comparison

Let `R` be a commutative ring, `I = (f₁, …, f_r)` a finitely generated ideal and
`U = Spec R \ V(I)`. `Stacks.LocalCohomology.localizationTriangleDataOfSectionsIso` reduces
`Stacks.LocalCohomology.LocalizationTriangleData` to three statements about the degree-zero
cohomology of the Čech cone: a natural `R`-linear identification with `Γ(U, M̃|U)`, its naturality,
and the formula `m ↦ m/1`. The first of those is
`Stacks.LocalCohomology.cechSectionsIso`, obtained by composing the identification of that
cohomology with the degree-one Čech cocycles
(`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer`) with the identification of those
cocycles with the sections (`Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections`).

This file does the same for the remaining two: it discharges the *sheaf-theoretic* half of each and
leaves only the *homological* half, two statements about
`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer` alone in which no sheaf, no open and no
section occur. In words, they say that the comparison of the degree-zero cohomology of the cone
with the degree-one Čech cocycles is natural in the module, and that it carries the class coming
from `M` in degree zero to the cocycle whose every coordinate is the constant fraction `m / 1`.

## Main definitions

* `Stacks.LocalCohomology.localizationTriangleDataOfCechHomologyComparison` — **the localization
  triangle data of Stacks 0DWR, given the naturality of
  `Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer` and its value on the image of
  `M`**.

## Main results

* `Stacks.LocalCohomology.kerCechDOneEquivComplementGlobalSections_moduleSectionsMk` — a degree-one
  cocycle all of whose coordinates are the constant fraction `m / 1` corresponds to the section
  `m / 1` on `U`.

## References

* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (I : Ideal R)

section Free

variable (M : ModuleCat.{v} R)

/-- **A cocycle of constant fractions is the constant section.** If every coordinate of a
degree-one Čech cocycle is the constant fraction `m / 1`, the section of `M̃` on `U` it
corresponds to is the constant fraction `m / 1`: the two sections agree after restriction to every
standard open `D(f_i)` of the cover, and the `D(f_i)` cover `U`. -/
theorem kerCechDOneEquivComplementGlobalSections_moduleSectionsMk
    (hIf : Ideal.span (Set.range f) = I) (m : M)
    (x : LinearMap.ker (Cech.cechD f (M : Type _) 1))
    (hx : ∀ i : Fin r, cechTermOneEquiv f M x.1 i =
      LocalizedModule.mkLinearMap (Cech.cechSub f {i}) (M : Type _) m) :
    kerCechDOneEquivComplementGlobalSections I M f hIf x =
      complementGlobalSectionsEquiv I M
        (moduleSectionsMk M ((complementZeroLocus R I).ι ''ᵁ ⊤) m) := by
  refine Subtype.ext (funext fun p => ?_)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    ((complementZeroLocus_eq_iSup_cechBasicOpen f I hIf).le
      ((Scheme.Opens.ι_image_top (complementZeroLocus R I)).le p.2))
  have hL := cechSectionsEquiv_restrict_kerCechDOneEquiv f I hIf x i
  rw [hx i] at hL
  have hR := (congrArg (cechSectionsEquiv f M {i}) (LinearMap.congr_fun
      (moduleSectionsRestrict_comp_moduleSectionsMk M
        (cechBasicOpen_le_ι_image_top f I hIf i)) m)).trans
    (cechSectionsEquiv_moduleSectionsMk f M {i} m)
  exact congrFun (congrArg Subtype.val
    ((cechSectionsEquiv f M {i}).injective (hL.trans hR.symm))) ⟨p.1, hi⟩

end Free

/-- **The affine localization triangle of Stacks 0DWR, reduced to two statements about the
mapping cone.** Everything sheaf-theoretic in
`Stacks.LocalCohomology.LocalizationTriangleData` has been discharged: given only that the
comparison of the degree-zero cohomology of the Čech cone with the degree-one Čech cocycles
(`Stacks.LocalCohomology.cechComplementHomologyZeroEquivKer`) is natural in the module, and that it
carries the class of `m` to the cocycle whose every coordinate is `m / 1`, the data exists.

Both hypotheses are statements about the cone of the Čech augmentation and the Čech complex alone;
no sheaf, open or section occurs in either. -/
def localizationTriangleDataOfCechHomologyComparison (hI : I.FG)
    (hIf : Ideal.span (Set.range f) = I)
    (hnat : ∀ {M N : ModuleCat.{max u v} R} (g : M ⟶ N)
        (z : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).obj
          ((cechComplementFunctor.{v} f).obj M)),
      cechComplementHomologyZeroEquivKer.{v} f N
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
            ((cechComplementFunctor.{v} f).map g) z) =
        kerCechDOneMap f g (cechComplementHomologyZeroEquivKer.{v} f M z))
    (hres : ∀ (M : ModuleCat.{max u v} R) (m : M) (i : Fin r),
      cechTermOneEquiv f M (cechComplementHomologyZeroEquivKer.{v} f M
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) 0).map
            ((cechRestriction.{v} f).app M)
              ((DerivedCategory.singleFunctorCompHomologyFunctorIso
                (ModuleCat.{max u v} R) 0).inv.app M m))).1 i =
        LocalizedModule.mkLinearMap (Cech.cechSub f {i}) (M : Type _) m) :
    LocalizationTriangleData.{u, max u v} R I hI :=
  localizationTriangleDataOfSectionsIso f I hI hIf (fun M => cechSectionsIso I M f hIf)
    (fun {M N} g z => by
      rw [cechSectionsIso_apply, cechSectionsIso_apply, hnat g z]
      exact kerCechDOneEquivComplementGlobalSections_naturality f I hIf g _)
    (fun M m => by
      rw [cechSectionsIso_apply,
        kerCechDOneEquivComplementGlobalSections_moduleSectionsMk f I M hIf m _ (hres M m)]
      rfl)

end Stacks.LocalCohomology

end
