module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.KFlatIntoKInjective
import StacksCore.Tactic.StacksAttribute

/-!
# Ext groups on an open as cohomology of the internal Hom complex

Let `(X, O_X)` be a ringed space and let `K`, `L` be objects of the derived category `D(O_X)`.
Choosing a K-flat complex `A` representing `K` and a K-injective complex `I` representing `L`,
the internal Hom complex `SheafHom^•(A, I)` is a complex of `O_X`-modules which is itself
K-injective ([Stacks, Tag 0A8T]), and for every open `U ⊆ X` and every degree `n`

`H^n(Γ(U, SheafHom^•(A, I))) = Ext^n(K|_U, L|_U)`.

This is the degree-`n` form of [Stacks, Tag 08DK], whose statement is the case `n = 0`. It is
obtained here **without** any shift of the derived internal Hom: the shift is taken on the
K-injective complex `I|_U`, where it is again K-injective, and `DerivedCategory.Q.commShiftIso`
carries it to the derived category. So nothing here needs a `CategoryTheory.Functor.CommShift`
for the derived internal Hom, which this development does not have.

## Main definitions

* `Stacks.SheafOfModules.homSheafComplex`: the internal Hom complex of the chosen
  representatives, a single complex of `O_X`-modules whose section cohomology computes
  `Ext^n(K|_U, L|_U)` in *every* degree and over *every* open.
* `Stacks.SheafOfModules.homSheafObject`: its class in `D(O_X)`, which is the object to feed to
  a statement about hypercohomology on a basis.

## Main results

* `Stacks.SheafOfModules.sheafHomComplexSectionHomologyEquivShiftedHom`: the degree-`n`
  identification at a K-injective target, the core of the file.
* `Stacks.SheafOfModules.homSheafComplexSectionHomologyEquiv`: the same for the chosen
  representatives of two objects of `D(O_X)`.
* `Stacks.SheafOfModules.isKInjective_homSheafComplex`: the chosen internal Hom complex is
  K-injective, so its *naive* sections already compute its hypercohomology.
* `Stacks.SheafOfModules.isZero_homology_mapHomologicalComplex_iff`: a faithful exact additive
  functor neither creates nor destroys the vanishing of a cohomology group.

## Implementation notes

The degree-`n` identification is assembled from
`AlgebraicGeometry.RingedSite.sheafHomComplexSectionHomologyEquivHomotopyCategory`, which is
already stated in every degree, followed by bijectivity of the localization functor on morphisms
into a K-injective target. The two K-injectivity facts it needs are that restriction to a slice
site preserves K-injectivity ([Stacks, Tag 08FI]) and that a shift of a K-injective complex is
K-injective; both are the ones used for the degree-zero statement.

`isZero_homology_mapHomologicalComplex_iff` exists because the hypercohomology of a complex over
the inverse image of an open is recorded as a module over the sections of the structure sheaf of
the *target*, whereas the internal Hom complex has its sections recorded as abelian groups. The
two differ by restriction of scalars followed by the forgetful functor, both of which are
faithful and exact, and vanishing of a cohomology group is `HomologicalComplex.ExactAt`, which
such a functor reflects.

`CategoryTheory.sheafCompose` is made `implicit_reducible` for this file, as in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom`, which defines the
machinery used here. The declarations below are stated over
`_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)`, i.e. modules over
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Rc`, whereas the ringed-site declarations they
are built from are stated over `SheafOfModules (Tensor.ringSheaf.{u, u, u} Rc)`, i.e. modules over
`Stacks.SheafOfModules.Tensor.ringSheaf Rc`. The two sheaves of rings are equal, but only after
unfolding `sheafCompose`, which instance search will not do at reducible transparency. Without this
attribute the `IsKInjective` instance for the chosen K-injective representative is carried at the
first spelling and is not found at the second. Do not remove it.

The attribute does not settle `PreservesFiniteLimits`, because there the two spellings differ in an
*explicit* argument of `SheafOfModules.overFunctor` rather than in an instance argument, so the
goal's discrimination key is computed on `(Tensor.ringSheaf.{u, u, u} Rc)` and the hypothesis
carried over `structureSheaf Rc` is never retrieved — the two are interchangeable by
`inferInstanceAs`, but instance search does not get far enough to try that. So
`Stacks.SheafOfModules.homSheafComplexSectionHomologyEquiv` opens its body with an explicitly typed
`letI` carrying the section's own hypothesis at the spelling
`AlgebraicGeometry.RingedSite.restrictModelIso` asks for. Only the limits half is needed; the
colimits hypothesis is reached at the spelling it is stated in.

## References

* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8T](https://stacks.math.columbia.edu/tag/0A8T)
* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.sheafCompose

/-! ### Vanishing of cohomology is reflected by a faithful exact functor -/

/-- A faithful exact additive functor neither creates nor destroys the vanishing of a cohomology
group: vanishing in degree `n` is exactness at `n`, which such a functor reflects. -/
theorem isZero_homology_mapHomologicalComplex_iff {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive] [G.Faithful]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (N : CochainComplex C ℤ) (n : ℤ) :
    IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N).homology n) ↔
      IsZero (N.homology n) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.exact_map_iff_of_faithful (N.sc n) G

/-- An exact additive functor computes cohomology: the degree-`n` cohomology of the image complex
is the image of the degree-`n` cohomology. -/
def homologyMapHomologicalComplexIso {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (N : CochainComplex C ℤ) (n : ℤ) :
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj N).homology n ≅ G.obj (N.homology n) :=
  ShortComplex.mapHomologyIso (N.sc n) G

/-! ### Section cohomology of the internal Hom complex in every degree -/

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)

/-- **Stacks 08DK at a K-injective target, in every degree.** If `I` is K-injective then the
degree-`n` cohomology of the sections over `U` of the internal Hom complex from `L` to `I` is the
group of degree-`n` morphisms `L|_U ⟶ I|_U` in the derived category of `O_U`-modules.

The source statement is the case `n = 0`; the general case costs no more, because the shift is
taken on the K-injective complex `I|_U` and carried to the derived category by
`DerivedCategory.Q.commShiftIso`. -/
def sheafHomComplexSectionHomologyEquivShiftedHom
    (L I : CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ)
    [I.IsKInjective] (U : Opens X) (n : ℤ) :
    ((sectionComplex Rc (sheafHomComplex Rc L I).obj U).homology n : Type u) ≃+
      ShiftedHom (DerivedCategory.Q.obj (restrictComplex Rc L U))
        (DerivedCategory.Q.obj (restrictComplex Rc I U)) n := by
  letI : (restrictComplex Rc I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over (Opens.grothendieckTopology X)
      (Tensor.ringSheaf.{u, u, u} Rc) U I
  letI : ((restrictComplex Rc I U)⟦n⟧).IsKInjective :=
    (CochainComplex.isKInjective_shift_iff _ _).2 inferInstance
  exact (RingedSite.sheafHomComplexSectionHomologyEquivHomotopyCategory
      (ringedSite Rc) L I U n).trans
    ((RingedSite.homotopyHomDerivedCategoryEquiv (restrictComplex Rc L U)
        ((restrictComplex Rc I U)⟦n⟧)).trans
      (CategoryTheory.Linear.homCongr ℤ (Iso.refl _)
        ((DerivedCategory.Q.commShiftIso n).app (restrictComplex Rc I U))).toAddEquiv)

/-! ### The internal Hom complex of chosen representatives -/

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} Rc)
      (ComplexShape.up ℤ)]

variable (K L : DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)))

/-- The chosen K-flat complex representing an object of `D(O_X)` ([Stacks, Tag 06YS]). -/
abbrev kFlatRepresentative :
    CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ :=
  RingedSite.kFlatModel (ringedSite Rc) K

/-- The chosen K-injective complex representing an object of `D(O_X)`. -/
abbrev kInjectiveRepresentative :
    CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ :=
  RingedSite.kInjectiveModel (ringedSite Rc) L

/-- The chosen K-injective representative is K-injective. -/
instance isKInjective_kInjectiveRepresentative :
    (kInjectiveRepresentative Rc L).IsKInjective :=
  RingedSite.isKInjective_kInjectiveModel (ringedSite Rc) L

/-- **The internal Hom complex of `K` and `L`.** The internal Hom complex from the chosen K-flat
representative of `K` into the chosen K-injective representative of `L`: a single complex of
`O_X`-modules whose cohomology of sections over an open `U` is `Ext^n(K|_U, L|_U)` in every
degree. -/
abbrev homSheafComplex :
    CochainComplex (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ :=
  (sheafHomComplex Rc (kFlatRepresentative Rc K) (kInjectiveRepresentative Rc L)).obj

/-- **The internal Hom complex is K-injective** ([Stacks, Tag 0A8T]): its source is K-flat and
its target K-injective. Hence its naive sections over an open already compute its
hypercohomology there. -/
instance isKInjective_homSheafComplex : (homSheafComplex Rc K L).IsKInjective :=
  RingedSite.isKInjective_sheafHomComplex_of_isKFlat (ringedSite Rc) _ _
    (RingedSite.isKFlat_kFlatModel (ringedSite Rc) K)

/-- **The derived internal Hom of `K` and `L` as an object of `D(O_X)`.** The class of
`Stacks.SheafOfModules.homSheafComplex`; it is isomorphic to `RSheafHom(K, L)` by
`Stacks.SheafOfModules.homSheafObjectIso`. -/
abbrev homSheafObject :
    DerivedCategory (_root_.SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) :=
  DerivedCategory.Q.obj (homSheafComplex Rc K L)

/-- The chosen internal Hom complex does represent the derived internal Hom `RSheafHom(K, L)`. -/
def homSheafObjectIso :
    ((derivedSheafHom Rc).obj (op K)).obj L ≅ homSheafObject Rc K L :=
  RingedSite.derivedSheafHomObjectsModelIso (ringedSite Rc)
      (RingedSite.kFlatModelIso (ringedSite Rc) K)
      (RingedSite.kInjectiveModelIso (ringedSite Rc) L) ≪≫
    @RingedSite.derivedSheafHomComparison (ringedSite Rc) _ _ _
      (RingedSite.isKInjective_kInjectiveModel (ringedSite Rc) L)

section Open

variable (U : Opens X)
  [PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf.{u, u, u} Rc) U)]
  [PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (Tensor.ringSheaf.{u, u, u} Rc) U)]

/-- **Ext on an open, in every degree.** The degree-`n` cohomology of the sections over `U` of
the internal Hom complex of `K` and `L` is the group `Ext^n(K|_U, L|_U)` of degree-`n` morphisms
between the restrictions, in the derived category of `O_U`-modules.

This is [Stacks, Tag 08DK] in every degree, with the restrictions read on the slice site over
`U`: the degree-`n` identification at the chosen representatives, transported along the
isomorphisms identifying their restrictions with `K|_U` and `L|_U`. -/
def homSheafComplexSectionHomologyEquiv (n : ℤ) :
    ((sectionComplex Rc (homSheafComplex Rc K L) U).homology n : Type u) ≃+
      ShiftedHom
        ((SheafOfModules.overFunctor.{u} (Tensor.ringSheaf.{u, u, u} Rc) U).mapDerivedCategory.obj
          K)
        ((SheafOfModules.overFunctor.{u} (Tensor.ringSheaf.{u, u, u} Rc) U).mapDerivedCategory.obj
          L)
        n :=
  (sheafHomComplexSectionHomologyEquivShiftedHom Rc _ _ U n).trans
    (CategoryTheory.Linear.homCongr ℤ
      (RingedSite.restrictModelIso (ringedSite Rc) U
        (RingedSite.kFlatModelIso (ringedSite Rc) K))
      ((shiftFunctor _ n).mapIso
        (RingedSite.restrictModelIso (ringedSite Rc) U
          (RingedSite.kInjectiveModelIso (ringedSite Rc) L)))).toAddEquiv

end Open

end Stacks.SheafOfModules

end
