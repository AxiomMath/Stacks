module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
public import StacksCore.Tactic.StacksAttribute

/-!
# Derived sheafification on an affine scheme

For a commutative ring `R` the associated-sheaf functor `M ↦ M̃` from `R`-modules to
`𝒪_{Spec R}`-modules is exact: it is a left adjoint, and it preserves finite limits because the
stalk of `M̃` at a prime `p` is the localization `M_p` and localization is exact (Stacks 01HV,
available as `AlgebraicGeometry.tilde.preservesFiniteLimits`). An exact functor between abelian
categories induces a functor between unbounded derived categories, so `~` induces
`D(R) ⥤ D(𝒪_{Spec R})`. Every cohomology sheaf of a complex in the image is of the form
`H^n(M^•)^~`, hence quasi-coherent, so the induced functor lands in the full subcategory
`D_QCoh(𝒪_{Spec R})` of complexes with quasi-coherent cohomology. That restriction is
*derived sheafification*, `AlgebraicGeometry.derivedTilde`.

## Main definitions

* `AlgebraicGeometry.derivedTilde` — derived sheafification
  `D(R) ⥤ D_QCoh(𝒪_{Spec R})`.
* `AlgebraicGeometry.derivedTildeCompι` — forgetting quasi-coherence of the cohomology
  recovers `(tilde.functor R).mapDerivedCategory`.
* `AlgebraicGeometry.derivedTildeFactors` — derived sheafification is degreewise
  sheafification followed by localization.

## Main results

* `AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj` — the cohomology
  sheaves of the image of a complex of `R`-modules are quasi-coherent.
* `AlgebraicGeometry.derivedTilde_commShift` — derived sheafification commutes with the shift.

## Implementation notes

`CategoryTheory.HasDerivedCategory` carries the localized category as *data*, so two instances
for the same abelian category give genuinely different types and a statement proved at one model
says nothing about the other. Everything below is therefore stated at **free**
`[HasDerivedCategory.{w} (ModuleCat.{u} R)]` and `[HasDerivedCategory.{w'} (Spec R).Modules]`
binders, with the two sides allowed independent morphism universes: nothing in derived
sheafification depends on the model, since `CategoryTheory.Functor.mapDerivedCategory` is
available for an exact functor at any pair of models.

The default a consumer gets, when it supplies nothing to those binders, is the preferred
*locally small* model: `ModuleCat.hasDerivedCategory`, `SheafOfModules.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. Its morphisms are in `Type u` rather than
`Type (u + 1)`, and it is the model Brown representability (Stacks 0A8G) needs: at
`HasDerivedCategory.standard` the morphisms of `D(𝒪_X)` live in `Type (u + 1)`, one universe
above the morphisms of `X.Modules` rather than above its objects, so the `HasCoproducts.{u}`
hypothesis is false rather than merely unavailable.

Those three are *global* instances, and a global instance beats `attribute [local instance]`, so
a consumer cannot select a different model by a local attribute. The free binders are what makes
a different model reachable at all: a binder is filled by an explicitly supplied instance, so a
statement elsewhere that is baked at `HasDerivedCategory.standard` can still be met.

`derivedTilde` is built as the `ObjectProperty.lift` of `(tilde.functor R).mapDerivedCategory`
along the quasi-coherent-cohomology property, rather than as the derived functor of the
equivalence `AlgebraicGeometry.tildeEquiv` followed by the comparison functor of Stacks 06VT.
The two agree, but the route taken here needs neither the abelian structure on the category of
quasi-coherent modules (Stacks 077P, which rests on Gabber's theorem, Stacks 077N) nor the weak
Serre property of Stacks 06VT; `derivedTildeFactors` characterizes `derivedTilde`, and follows
directly from `ObjectProperty.liftCompιIso`.

`derivedQuasicoherent_isStableUnderShift` reproves the special case of
`DerivedCategoryB.derivedCategoryB_isStableUnderShift` that is needed to put a shift on
`D_QCoh(𝒪_{Spec R})`. The general lemma asks for `DerivedCategoryB.WeakSerre.IsWeakSerre`, but
its proof uses only closure under isomorphisms, and that is available for quasi-coherence from
Mathlib.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u}) [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w'} (Spec R).Modules]

/-- Every cohomology sheaf of the image of a complex of `R`-modules under the functor
`D(R) ⥤ D(𝒪_{Spec R})` induced by `M ↦ M̃` is quasi-coherent. -/
theorem isQuasicoherent_homology_mapDerivedCategory_obj
    (K : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((tilde.functor R).mapDerivedCategory.obj K)) := by
  obtain ⟨L, ⟨e⟩⟩ : (DerivedCategory.Q (C := ModuleCat.{u} R)).essImage K :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) K
  let F := tilde.functor R
  let ε : (DerivedCategory.homologyFunctor (Spec R).Modules n).obj
      (F.mapDerivedCategory.obj K) ≅ F.obj (L.homology n) :=
    (DerivedCategory.homologyFunctor _ n).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso (F.mapDerivedCategoryFactors.app L) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≪≫
      (L.sc n).mapHomologyIso F
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso ε.symm inferInstance

/-- The property of a complex of `𝒪_{Spec R}`-modules of having quasi-coherent cohomology in
every degree is stable under the shift. -/
instance derivedQuasicoherent_isStableUnderShift :
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).IsStableUnderShift ℤ := by
  refine ⟨fun a => ⟨fun X hX => ?_⟩⟩
  rw [ObjectProperty.prop_shift_iff]
  intro n
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor (Spec R).Modules 0).shiftIso a n (a + n) rfl).app X).symm
    (hX (a + n))

/-- **Stacks 06Z0.** Derived sheafification: the exact functor `M ↦ M̃` induces a functor from
the unbounded derived category of `R`-modules to the full subcategory of `D(𝒪_{Spec R})` of
complexes with quasi-coherent cohomology. -/
def derivedTilde :
    DerivedCategory (ModuleCat.{u} R) ⥤
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).FullSubcategory :=
  (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).lift
      (tilde.functor R).mapDerivedCategory (isQuasicoherent_homology_mapDerivedCategory_obj R)

/-- Forgetting the quasi-coherence condition, derived sheafification is the derived functor of
the associated-sheaf functor. -/
def derivedTildeCompι :
    derivedTilde R ⋙ (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι ≅
      (tilde.functor R).mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

/-- After forgetting quasi-coherence, derived sheafification is degreewise sheafification
followed by localization. -/
def derivedTildeFactors :
    DerivedCategory.Q ⋙ (derivedTilde R ⋙
      (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι) ≅
      (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft _ (derivedTildeCompι R) ≪≫
    (tilde.functor R).mapDerivedCategoryFactors

/-- **Stacks 06Z0.** Derived sheafification commutes with the shift functors. -/
instance derivedTilde_commShift : (derivedTilde R).CommShift ℤ :=
  Functor.CommShift.ofComp (derivedTildeCompι R) ℤ

/-- The identification `derivedTildeCompι` of `derivedTilde R ⋙ ι` with the derived functor of
`~` is compatible with the shift, for the shift structure of `derivedTilde_commShift`. -/
instance derivedTildeCompι_natTrans_commShift :
    NatTrans.CommShift (derivedTildeCompι R).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (derivedTildeCompι R) ℤ

end AlgebraicGeometry

end
