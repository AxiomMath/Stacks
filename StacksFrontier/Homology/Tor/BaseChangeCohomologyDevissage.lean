module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.HomologyDirectSums
public import StacksFrontier.Homology.Devissage.CompactGeneratedHomologicalNatTrans
public import StacksFrontier.Homology.Tor.DerivedExtensionLocalizationComp
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.Homology.Tor.FlatDerivedExtensionScalars

@[expose] public noncomputable section

/-!
# The derived base change of a complex over an algebra, as a homological functor

Let `R → A` and `R → R'` be homomorphisms of commutative rings. The affine reduction of
[stacks 0DJ8] reads an object `K` of `D(A)` over `R` and base changes it along `R → R'`; the
functor so obtained,

`RingTheory.TorIndependence.derivedBaseChangeFunctor : D(A) ⥤ D(R')`,

is the one whose cohomology carries the `A ⊗[R] R'`-action of
`RingTheory.TorIndependence.baseChangeCohomology`. This file shows that this cohomology is a
homological functor and that it preserves direct sums.

Note that `derivedBaseChangeFunctor` is *not* extension of scalars along a ring map out of `A`:
that is the functor of [stacks 0DJD], and the two differ exactly by Tor independence.

## Main definitions

* `RingTheory.TorIndependence.derivedBaseChangeFunctor`: the derived base change `D(A) ⥤ D(R')`,
  read over `R`.

## Main results

* `RingTheory.TorIndependence.isHomological_derivedBaseChangeHomology`: its cohomology in a
  fixed degree is a homological functor.
* `RingTheory.TorIndependence.preservesColimitsOfShape_derivedBaseChangeHomology`: that
  cohomology preserves direct sums.
* `RingTheory.TorIndependence.preservesColimitsOfShape_mapDerivedCategory_restrictScalars`:
  restriction of scalars, read on derived categories, preserves direct sums.
* `RingTheory.TorIndependence.flatCompDerivedHomologyIso`: for `g : A → A₂` flat and `N` in
  `D(R)`, `H^n(N ⊗ᴸ_R A₂) ≅ A₂ ⊗_A H^n(N ⊗ᴸ_R A)`.

## Implementation notes

The homological statement leaves the model of the derived category free. The direct-sum
statement is pinned to the model `[HasDerivedCategory.{u} (ModuleCat.{u} ·)]`. That is forced and
not a choice: the index type must lie in the universe at which the Grothendieck-abelian structure
of `ModuleCat.{u}` produces coproducts, which is `u`, and at the same time in the universe at
which derived extension of scalars is known to preserve colimits, which is the morphism universe
of the derived category. It is also exactly the model at which the regular module is a compact
generator.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars

universe u w

namespace RingTheory.TorIndependence

/-! ### Restriction of scalars preserves direct sums on derived categories -/

section RestrictScalars

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- **Restriction of scalars, read on derived categories, preserves direct sums.** -/
theorem preservesColimitsOfShape_mapDerivedCategory_restrictScalars (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory := by
  let F := ModuleCat.restrictScalars.{u} (algebraMap R A)
  let : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := ModuleCat.{u} A)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts (ModuleCat.{u} A) J
  let : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := ModuleCat.{u} R)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts (ModuleCat.{u} R) J
  have hcomp : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.Q (C := ModuleCat.{u} A) ⋙ F.mapDerivedCategory) :=
    (preservesColimitsOfShape_iff_of_natIso F.mapDerivedCategoryFactors).2 inferInstance
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    (DerivedCategory.Q (C := ModuleCat.{u} A)) F.mapDerivedCategory J

end RestrictScalars

/-! ### The derived base change and its cohomology -/

section BaseChange

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')]

/-- **The derived base change of an `A`-complex along `R → R'`**: read the complex over `R`,
then apply derived extension of scalars to `R'`. Its cohomology in degree `n` is
`RingTheory.TorIndependence.baseChangeCohomologyOverBase`. -/
def derivedBaseChangeFunctor :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} R') :=
  (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙
    (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor

/-- **The cohomology of the derived base change is a homological functor.** -/
theorem isHomological_derivedBaseChangeHomology (n : ℤ) :
    (derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).IsHomological := by
  let := (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).commShift
  let := (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).isTriangulated
  exact inferInstanceAs
    (((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).IsHomological)

end BaseChange

section Coproducts

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  [HasDerivedCategory.{u} (ModuleCat.{u} R)] [HasDerivedCategory.{u} (ModuleCat.{u} A)]
  [HasDerivedCategory.{u} (ModuleCat.{u} R')]

/-- **The cohomology of the derived base change preserves direct sums.** -/
theorem preservesColimitsOfShape_derivedBaseChangeHomology (J : Type u) (n : ℤ) :
    PreservesColimitsOfShape (Discrete J)
      (derivedBaseChangeFunctor (R := R) (A := A) (R' := R') ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} R') n) := by
  let : PreservesColimitsOfShape (Discrete J)
      (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory :=
    preservesColimitsOfShape_mapDerivedCategory_restrictScalars J
  let : PreservesColimitsOfSize.{u, u}
      (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor :=
    preservesColimits_totalDerivedExtensionScalars (algebraMap R R')
  let : PreservesColimitsOfShape (Discrete J)
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n) :=
    Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor (ModuleCat.{u} R') n
  exact inferInstanceAs
    (PreservesColimitsOfShape (Discrete J)
      ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙
        (totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} R') n))

end Coproducts

/-! ### Localization in the ring direction -/

section FlatComposite

variable {R A A₂ : Type u} [CommRing R] [CommRing A] [CommRing A₂]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} A₂)]

/-- **A flat extension of the ring passes through the cohomology of a derived extension of
scalars.** For `f : R → A` and `g : A → A₂` with `g` flat — a localization, for instance — and
`N` an object of `D(R)`,

`H^n(N ⊗ᴸ_R A₂) ≅ A₂ ⊗_A H^n(N ⊗ᴸ_R A)`,

naturally in `N`. -/
def flatCompDerivedHomologyIso (f : R →+* A) (g : A →+* A₂) (hg : g.Flat) (n : ℤ) :
    (totalDerivedExtensionScalars.{u, u, u} (g.comp f)).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A₂) n ≅
      (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙
          ModuleCat.extendScalars.{u, u, u} g :=
  letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hg
  Functor.isoWhiskerRight (totalDerivedExtensionScalarsComp.{u, u} f g).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (flatDerivedExtensionScalarsIso.{u, w} g hg) _ ≪≫
        (ModuleCat.extendScalars.{u, u, u} g).mapDerivedCategoryHomologyIso n)

end FlatComposite

end RingTheory.TorIndependence

end
