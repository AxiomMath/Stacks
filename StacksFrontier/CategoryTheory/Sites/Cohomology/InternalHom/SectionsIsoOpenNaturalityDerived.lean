module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexGlobalValue
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SectionsIsoOpenNaturality

/-!
# The local description of derived-category morphisms is compatible with restriction

Let `(C, O)` be a ringed site, let `L` be a complex of `O`-modules and let `I` be a K-injective
complex of `O`-modules. The identification
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom` of the degree-zero
cohomology of the sections over an object `V` of the site of the internal Hom complex
`SheafHom(L, I)` with the group `Hom_{D(O|_V)}(L|_V, I|_V)` is compatible with restriction along
an arrow `g : W ⟶ V` of the site, that is,

```
H^0(Γ(V, SheafHom(L, I)))  ⟶  H^0(Γ(W, SheafHom(L, I)))
          ↓                              ↓
Hom_{D(O|_V)}(L|_V, I|_V)  ⟶  Hom_{D(O|_W)}(L|_W, I|_W)
```

commutes, the horizontal maps being
`AlgebraicGeometry.RingedSite.sectionComplexRestrict` read on `homologyMap` and
`AlgebraicGeometry.RingedSite.restrictDerivedSectionHom`.

## Main definitions

* `AlgebraicGeometry.RingedSite.restrictDerivedSectionHom`: the restriction along `g : W ⟶ V` of
  a morphism `L|_V ⟶ I|_V` of the derived category of `O|_V`-modules, with source and target
  written as the derived-category objects of the degreewise restrictions of `L` and `I`.
* `AlgebraicGeometry.RingedSite.cocycleRestrict`: the restriction along an arrow of the site of a
  degree-zero cocycle between the restrictions of two complexes of `O`-modules.
* `CochainComplex.HomComplex.cocycleOfCycle`: the cocycle attached to a cycle of a complex of
  abelian groups mapping to a Hom complex.

## Main results

* `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_restrict`: the
  commutativity of the square above.
* `AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ`: the
  identification, evaluated at the class of a cycle, is the image under the localisation functor
  of the morphism of complexes that cycle names.
* `CochainComplex.HomComplex.homologyAddEquiv_homologyMap`: the cohomology of a Hom complex,
  identified with the group of cohomology classes of cocycles, carries the map induced on
  homology by a morphism into that Hom complex to the class of the image cocycle.
* `AlgebraicGeometry.RingedSite.SheafHomComplex.sectionComplexRestrict_sectionsIso`: the chain
  level half of the square, as an equality of morphisms of complexes of abelian groups.
* `AlgebraicGeometry.RingedSite.restrictDerivedHom_restrictDerivedSectionHom`: the restriction
  maps `AlgebraicGeometry.RingedSite.restrictDerivedHom` and
  `AlgebraicGeometry.RingedSite.restrictDerivedSectionHom` agree.
* `AlgebraicGeometry.RingedSite.restrictDerivedHom_homCongr_restrictModelIso`: the same
  compatibility transported along `AlgebraicGeometry.RingedSite.restrictModelIso`, for two
  objects of `D(O)` presented by complexes.
* `Stacks.DerivedCategoryComparisons.homCongr_shiftFunctorZero`: normalising a degree-zero shift
  commutes with conjugating by two isomorphisms, the one at the target taken shifted.

## References

* [Stacks Project, Tag 0A94](https://stacks.math.columbia.edu/tag/0A94)
* [Stacks Project, Tag 0A8Y](https://stacks.math.columbia.edu/tag/0A8Y)
* [Stacks Project, Tag 0D68](https://stacks.math.columbia.edu/tag/0D68)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe v u u'

/-! ### Cohomology classes attached to cycles -/

namespace CochainComplex.HomComplex

variable {D : Type u'} [Category.{v} D] [Preadditive D] {K M : CochainComplex D ℤ}

/-- A morphism of complexes of abelian groups carries the class of a cycle to the class of the
image cycle. -/
private theorem homologyMap_homologyπ_apply {S T : CochainComplex AddCommGrpCat.{v} ℤ}
    (ψ : S ⟶ T) (n : ℤ) (z : (S.cycles n)) :
    HomologicalComplex.homologyMap ψ n (S.homologyπ n z) =
      T.homologyπ n (HomologicalComplex.cyclesMap ψ n z) := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality ψ n) z

/-- A morphism of complexes of abelian groups carries the underlying element of a cycle to the
underlying element of the image cycle. -/
private theorem iCycles_cyclesMap_apply {S T : CochainComplex AddCommGrpCat.{v} ℤ}
    (ψ : S ⟶ T) (n : ℤ) (z : (S.cycles n)) :
    AddCommGrpCat.Hom.hom (T.iCycles n) (HomologicalComplex.cyclesMap ψ n z) =
      AddCommGrpCat.Hom.hom (ψ.f n) (AddCommGrpCat.Hom.hom (S.iCycles n) z) := by
  simpa only [ConcreteCategory.comp_apply] using
    ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ n) z

/-- **The cohomology class of a cycle, as a cohomology class of cocycles.** The identification
`CochainComplex.HomComplex.homologyAddEquiv` of the degree-`n` homology of a Hom complex with the
degree-`n` cohomology classes of cocycles sends the class of a cycle to the class of the cocycle
that cycle is. -/
theorem homologyAddEquiv_homologyπ (K M : CochainComplex D ℤ) (n : ℤ)
    (z : ((K.HomComplex M).cycles n)) :
    homologyAddEquiv K M n ((K.HomComplex M).homologyπ n z) =
      CohomologyClass.mk ((leftHomologyData K M n).cyclesIso.hom z) :=
  ConcreteCategory.congr_hom
    (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom ((K.HomComplex M).sc n)
      (leftHomologyData K M n)) z

/-- **The cocycle named by a cycle of a complex of abelian groups over a Hom complex.** A
morphism of complexes of abelian groups `ψ : S ⟶ Hom^•(K, M)` carries a degree-`n` cycle of `S`
to a degree-`n` cocycle from `K` to `M`. -/
def cocycleOfCycle {S : CochainComplex AddCommGrpCat.{v} ℤ} (ψ : S ⟶ K.HomComplex M) (n : ℤ)
    (z : (S.cycles n)) : Cocycle K M n :=
  (leftHomologyData K M n).cyclesIso.hom (HomologicalComplex.cyclesMap ψ n z)

/-- The underlying cochain of `CochainComplex.HomComplex.cocycleOfCycle` is the image of the
underlying cochain of the cycle. -/
theorem cocycleOfCycle_coe {S : CochainComplex AddCommGrpCat.{v} ℤ} (ψ : S ⟶ K.HomComplex M)
    (n : ℤ) (z : (S.cycles n)) :
    (cocycleOfCycle ψ n z : Cochain K M n) =
      AddCommGrpCat.Hom.hom (ψ.f n) (AddCommGrpCat.Hom.hom (S.iCycles n) z) := by
  exact (ConcreteCategory.congr_hom (leftHomologyData K M n).cyclesIso_hom_comp_i
    ((HomologicalComplex.cyclesMap ψ n) z)).trans (iCycles_cyclesMap_apply ψ n z)

/-- **The cohomology of a Hom complex, read on a morphism into it.** The map induced on homology
by a morphism of complexes of abelian groups `ψ : S ⟶ Hom^•(K, M)` sends the class of a cycle to
the class of the cocycle named by its image. -/
theorem homologyAddEquiv_homologyMap {S : CochainComplex AddCommGrpCat.{v} ℤ}
    (ψ : S ⟶ K.HomComplex M) (n : ℤ) (z : (S.cycles n)) (x : Cocycle K M n)
    (hx : (x : Cochain K M n) =
      AddCommGrpCat.Hom.hom (ψ.f n) (AddCommGrpCat.Hom.hom (S.iCycles n) z)) :
    homologyAddEquiv K M n (HomologicalComplex.homologyMap ψ n (S.homologyπ n z)) =
      CohomologyClass.mk x := by
  rw [homologyMap_homologyπ_apply, homologyAddEquiv_homologyπ]
  congr 1
  exact Subtype.ext ((cocycleOfCycle_coe ψ n z).trans hx.symm)

/-- **A degree-zero cocycle, read as a morphism of complexes through the shift.** The morphism
`K ⟶ M⟦(0 : ℤ)⟧` that a degree-zero cocycle names, followed by the normalisation of the
degree-zero shift, is the morphism `K ⟶ M` of
`CochainComplex.HomComplex.Cocycle.homOf`. -/
theorem Cocycle.equivHomShift_symm_comp_shiftFunctorZero (x : Cocycle K M 0) :
    Cocycle.equivHomShift.symm x ≫ ((shiftFunctorZero (CochainComplex D ℤ) ℤ).app M).hom =
      Cocycle.homOf x := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  simp only [Iso.app_hom, Cocycle.equivHomShift_symm_apply, HomologicalComplex.comp_f,
    Cocycle.homOf_f, Cocycle.rightShift_coe, CochainComplex.shiftFunctorZero_hom_app_f,
    (x : Cochain K M 0).rightShift_v 0 0 (zero_add 0) p p (add_zero p) p (add_zero p),
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    eqToIso.inv, eqToIso.hom, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end CochainComplex.HomComplex

/-! ### `DerivedCategory.Q` and the derived action of an exact functor -/

namespace Stacks.DerivedCategoryComparisons

variable {C₁ : Type u} [Category.{v} C₁] [Abelian C₁] [HasDerivedCategory C₁]
  {C₂ : Type u'} [Category.{v} C₂] [Abelian C₂] [HasDerivedCategory C₂]

/-- **The derived action of an exact functor on the image of a morphism of complexes.** For an
exact functor `F`, the image under the localisation functor of `F` applied degreewise to a
morphism of complexes is the derived action of `F` on the image of that morphism, read through
`CategoryTheory.Functor.mapDerivedCategoryFactors`. -/
theorem Q_map_mapHomologicalComplex_map (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {K M : CochainComplex C₁ ℤ} (f : K ⟶ M) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) =
      F.mapDerivedCategoryFactors.inv.app K ≫
        F.mapDerivedCategory.map (DerivedCategory.Q.map f) ≫
          F.mapDerivedCategoryFactors.hom.app M := by
  rw [F.mapDerivedCategoryFactors_hom_naturality f, ← Category.assoc, Iso.inv_hom_id_app,
    Category.id_comp]

section Shift

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- **Conjugating a degree-zero shifted morphism, and normalising the shift, commute.** Reading a
degree-zero shifted morphism `A ⟶ C⟦0⟧` through isomorphisms `e₁ : A ≅ B` and `e₂ : C ≅ E` — the
second one shifted, as `CategoryTheory.Linear.homCongr` requires at a shifted target — and then
normalising the degree-zero shift away is normalising the shift away first and conjugating by `e₁`
and `e₂` afterwards. -/
theorem homCongr_shiftFunctorZero {A B C E : D} (e₁ : A ≅ B) (e₂ : C ≅ E)
    (ψ : ShiftedHom A C (0 : ℤ)) :
    Linear.homCongr ℤ (Iso.refl B) ((shiftFunctorZero D ℤ).app E)
        (Linear.homCongr ℤ e₁ ((CategoryTheory.shiftFunctor D (0 : ℤ)).mapIso e₂) ψ) =
      Linear.homCongr ℤ e₁ e₂
        (Linear.homCongr ℤ (Iso.refl A) ((shiftFunctorZero D ℤ).app C) ψ) := by
  simp only [Linear.homCongr_apply, Iso.refl_inv, Category.id_comp, Functor.mapIso_hom,
    Iso.app_hom, Category.assoc, (shiftFunctorZero D ℤ).hom.naturality e₂.hom, Functor.id_map]

end Shift

end Stacks.DerivedCategoryComparisons

namespace AlgebraicGeometry.RingedSite

section Zero

attribute [local instance 10000] HasDerivedCategory.standard

/-- **`sheafHomSectionHomologyEquivDerivedCategoryHom` at the class of a cycle is a single
`DerivedCategory.Q.map`.** Let `z` be a degree-zero cycle of the section complex over `U` of the
internal Hom complex from `L` to a K-injective `I`, and let `x` be the degree-zero cocycle from
`L|_U` to `I|_U` that the local description attaches to it. Then
`AlgebraicGeometry.RingedSite.sheafHomSectionHomologyEquivDerivedCategoryHom` sends the cohomology
class of `z` to the image under the localisation functor of the morphism of complexes
`L|_U ⟶ I|_U` that `x` names. -/
theorem sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ (X : RingedSite.{u, u, u})
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] (U : X.C)
    (z : ((sectionComplex X (sheafHomComplex X L I).obj U).cycles 0))
    (x : Cocycle (restrictComplex X L U) (restrictComplex X I U) 0)
    (hx : (x : Cochain (restrictComplex X L U) (restrictComplex X I U) 0) =
      AddCommGrpCat.Hom.hom (((sheafHomComplex X L I).sectionsIso U).hom.f 0)
        (AddCommGrpCat.Hom.hom ((sectionComplex X (sheafHomComplex X L I).obj U).iCycles 0) z)) :
    sheafHomSectionHomologyEquivDerivedCategoryHom X L I U
        ((sectionComplex X (sheafHomComplex X L I).obj U).homologyπ 0 z) =
      DerivedCategory.Q.map (Cocycle.homOf x) := by
  have : (restrictComplex X I U).IsKInjective :=
    Stacks.Cohomology.Localization.isKInjective_over X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U I
  rw [sheafHomSectionHomologyEquivDerivedCategoryHom_apply X L I U _,
    sheafHomSectionHomotopyCategoryHom_eq X L I U _, homologyAddEquiv_homologyMap _ 0 z x hx,
    CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk]
  refine (congrArg (fun θ => homotopyHomDerivedCategoryEquiv (restrictComplex X L U)
    (restrictComplex X I U) θ) ?_).trans
      (homotopyHomDerivedCategoryEquiv_quotient_map (Cocycle.homOf x))
  rw [Category.id_comp, ← Functor.map_comp]
  exact congrArg _ (Cocycle.equivHomShift_symm_comp_shiftFunctorZero x)

end Zero

/-! ### Restriction along an arrow of the site -/

section Restrict

attribute [local instance] additiveOverMap

variable {X : RingedSite.{u, u, u}}
  {K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The chain-level half of the naturality in the object of the site, as a square of morphisms
of complexes.** Restricting the sections of the internal Hom complex along `g : W ⟶ V` and then
reading them as cochains is reading them as cochains and then restricting the cochains. -/
theorem SheafHomComplex.sectionComplexRestrict_sectionsIso (H : SheafHomComplex X K M)
    {V W : X.C} (g : W ⟶ V) :
    sectionComplexRestrict X H.obj g ≫ (H.sectionsIso W).hom =
      (H.sectionsIso V).hom ≫ homComplexRestrict g :=
  HomologicalComplex.hom_ext _ _ fun n => AddCommGrpCat.hom_ext <| AddMonoidHom.ext fun s =>
    SheafHomComplex.sectionsEquiv_restrictSection H g n s

/-- **The restriction of a degree-zero cocycle along an arrow of the site.** A degree-zero
cocycle from `K|_V` to `M|_V` restricts to one from `K|_W` to `M|_W`: its underlying cochain is
the restriction of the underlying cochain, which is again a cocycle because restriction of
cochains commutes with the differential of the Hom complex. -/
def cocycleRestrict {V W : X.C} (g : W ⟶ V)
    (x : Cocycle (restrictComplex X K V) (restrictComplex X M V) 0) :
    Cocycle (restrictComplex X K W) (restrictComplex X M W) 0 :=
  Cocycle.mk (cochainRestrict g (x : Cochain (restrictComplex X K V) (restrictComplex X M V) 0))
    1 (zero_add 1) (by rw [delta_cochainRestrict, x.δ_eq_zero, cochainRestrict_zero])

/-- The underlying cochain of a restricted cocycle is the restricted cochain. -/
@[simp]
theorem cocycleRestrict_coe {V W : X.C} (g : W ⟶ V)
    (x : Cocycle (restrictComplex X K V) (restrictComplex X M V) 0) :
    (cocycleRestrict g x : Cochain (restrictComplex X K W) (restrictComplex X M W) 0) =
      cochainRestrict g (x : Cochain (restrictComplex X K V) (restrictComplex X M V) 0) :=
  rfl

/-- **A complex restricted to the slice over `W`, in two steps.** The restriction of `K` to the
slice over `W` is the restriction along `g : W ⟶ V` of its restriction to the slice over `V`, as
an equality of cochain complexes. -/
theorem restrictComplex_overMap
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V) :
    restrictComplex X K W =
      ((SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (restrictComplex X K V) :=
  rfl

/-- **The morphism of complexes named by a restricted cocycle.** It is the restriction along `g`
of the morphism named by the cocycle, with the identification of the two spellings of the
restriction in two steps carried as the `CategoryTheory.eqToHom` of
`AlgebraicGeometry.RingedSite.restrictComplex_overMap`. -/
theorem homOf_cocycleRestrict {V W : X.C} (g : W ⟶ V)
    (x : Cocycle (restrictComplex X K V) (restrictComplex X M V) 0) :
    Cocycle.homOf (cocycleRestrict g x) =
      eqToHom (restrictComplex_overMap K g) ≫
        ((SheafOfModules.overMap.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (Cocycle.homOf x) ≫
          eqToHom (restrictComplex_overMap M g).symm := by
  refine HomologicalComplex.hom_ext _ _ fun p => ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f, Cocycle.homOf_f,
    Functor.mapHomologicalComplex_map_f, cocycleRestrict_coe]
  exact cochainRestrict_v_eqToHom g _ p p (add_zero p)

end Restrict

/-! ### The derived-category restriction map, at the restrictions of two complexes -/

section Derived

attribute [local instance] hasSheafifyOver wEqualsLocallyBijectiveOver additiveOverMap
  preservesFiniteLimitsOverMap preservesFiniteColimitsOverMap

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **Restricting a morphism between the restrictions of two complexes of `O`-modules.** A
morphism `K|_V ⟶ M|_V` of the derived category of `O|_V`-modules, between the derived-category
objects of the degreewise restrictions of `K` and `M`, is carried to a morphism `K|_W ⟶ M|_W` by
restricting it along `g : W ⟶ V`: it is the derived action of restriction along `g`, conjugated
by `CategoryTheory.Functor.mapDerivedCategoryFactors` and by the `CategoryTheory.eqToHom` of
`AlgebraicGeometry.RingedSite.restrictComplex_overMap`. -/
def restrictDerivedSectionHom {V W : X.C} (g : W ⟶ V)
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (φ : DerivedCategory.Q.obj (restrictComplex X K V) ⟶
      DerivedCategory.Q.obj (restrictComplex X M V)) :
    DerivedCategory.Q.obj (restrictComplex X K W) ⟶
      DerivedCategory.Q.obj (restrictComplex X M W) :=
  DerivedCategory.Q.map (eqToHom (restrictComplex_overMap K g)) ≫
    (SheafOfModules.overMap.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategoryFactors.inv.app
        (restrictComplex X K V) ≫
      (SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory.map φ ≫
        (SheafOfModules.overMap.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategoryFactors.hom.app
          (restrictComplex X M V) ≫
          DerivedCategory.Q.map (eqToHom (restrictComplex_overMap M g).symm)

/-- **Restricting the image of a morphism of complexes is the image of its restriction.** -/
theorem restrictDerivedSectionHom_Q_map {V W : X.C} (g : W ⟶ V)
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (f : restrictComplex X K V ⟶ restrictComplex X M V) :
    restrictDerivedSectionHom X g K M (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map (eqToHom (restrictComplex_overMap K g) ≫
        ((SheafOfModules.overMap.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f ≫ eqToHom (restrictComplex_overMap M g).symm) := by
  rw [Functor.map_comp, Functor.map_comp, restrictDerivedSectionHom,
    Stacks.DerivedCategoryComparisons.Q_map_mapHomologicalComplex_map, Category.assoc,
    Category.assoc]

/-! ### The naturality in the object of the site -/

/-- **The restricted cycle names the restricted cocycle.** The cocycle that the local description
over `W` attaches to the restriction along `g : W ⟶ V` of a degree-zero cycle of the section
complex over `V` is the restriction of the cocycle it attaches over `V`. -/
private theorem cocycleRestrict_cocycleOfCycle
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V)
    (z : ((sectionComplex X (sheafHomComplex X L I).obj V).cycles 0)) :
    (cocycleRestrict g (cocycleOfCycle ((sheafHomComplex X L I).sectionsIso V).hom 0 z) :
        Cochain (restrictComplex X L W) (restrictComplex X I W) 0) =
      AddCommGrpCat.Hom.hom (((sheafHomComplex X L I).sectionsIso W).hom.f 0)
        (AddCommGrpCat.Hom.hom ((sectionComplex X (sheafHomComplex X L I).obj W).iCycles 0)
          (HomologicalComplex.cyclesMap
            (sectionComplexRestrict X (sheafHomComplex X L I).obj g) 0 z)) := by
  rw [cocycleRestrict_coe, cocycleOfCycle_coe, iCycles_cyclesMap_apply]
  exact (SheafHomComplex.sectionsEquiv_restrictSection (sheafHomComplex X L I) g 0 _).symm

/-- **`sheafHomSectionHomologyEquivDerivedCategoryHom` is natural in the object of the site.**
For an arrow `g : W ⟶ V` of the site, restricting a degree-zero cohomology class of the sections
over `V` of the internal Hom complex from `L` to a K-injective `I` and then reading it as a
morphism `L|_W ⟶ I|_W` of the derived category of `O|_W`-modules is reading it as a morphism
`L|_V ⟶ I|_V` and then restricting that morphism. -/
theorem sheafHomSectionHomologyEquivDerivedCategoryHom_restrict
    (L I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] {V W : X.C}
    (g : W ⟶ V) (η : (sectionComplex X (sheafHomComplex X L I).obj V).homology 0) :
    sheafHomSectionHomologyEquivDerivedCategoryHom X L I W
        (HomologicalComplex.homologyMap
          (sectionComplexRestrict X (sheafHomComplex X L I).obj g) 0 η) =
      restrictDerivedSectionHom X g L I
        (sheafHomSectionHomologyEquivDerivedCategoryHom X L I V η) := by
  obtain ⟨z, rfl⟩ :=
    (AddCommGrpCat.epi_iff_surjective
      ((sectionComplex X (sheafHomComplex X L I).obj V).homologyπ 0)).mp inferInstance η
  rw [homologyMap_homologyπ_apply,
    sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ X L I W _ _
      (cocycleRestrict_cocycleOfCycle X L I g z),
    sheafHomSectionHomologyEquivDerivedCategoryHom_homologyπ X L I V z _
      (cocycleOfCycle_coe ((sheafHomComplex X L I).sectionsIso V).hom 0 z),
    restrictDerivedSectionHom_Q_map, homOf_cocycleRestrict]

/-! ### The two spellings of the restriction map agree -/

/-- **The degreewise restriction comparison, at a complex, is the crossing `eqToHom`.** The
isomorphism `K|_W ≅ (K|_V)|_W` obtained by applying Mathlib's natural isomorphism
`SheafOfModules.overFunctorMap` degreewise is the `CategoryTheory.eqToIso` of
`AlgebraicGeometry.RingedSite.restrictComplex_overMap`. -/
theorem natIsoMapHomologicalComplex_overFunctorMap_app
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {V W : X.C} (g : W ⟶ V) :
    (NatIso.mapHomologicalComplex
        (SheafOfModules.overFunctorMap.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
        (ComplexShape.up ℤ)).app K = (eqToIso (restrictComplex_overMap K g)).symm := by
  refine Iso.ext (HomologicalComplex.hom_ext _ _ fun p => ?_)
  ext1
  ext1
  rfl

/-- **The restriction comparison on derived categories, at the image of a complex.** The inverse
of `AlgebraicGeometry.RingedSite.overMapDerivedCategoryRestrictIso` at `Q(K)` is the
factorization of restriction to the slice over `W`, followed by the crossing `eqToHom` and the
factorizations of restriction along `g` and to the slice over `V`. -/
theorem overMapDerivedCategoryRestrictIso_inv_app_Q {V W : X.C} (g : W ⟶ V)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (overMapDerivedCategoryRestrictIso X g).inv.app (DerivedCategory.Q.obj K) =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (eqToHom (restrictComplex_overMap K g)) ≫
          (SheafOfModules.overMap.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategoryFactors.inv.app
              (restrictComplex X K V) ≫
            (SheafOfModules.overMap.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory.map
              ((SheafOfModules.overFunctor.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.inv.app
                  K) := by
  rw [overMapDerivedCategoryRestrictIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_inv_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_hom_app_Q]
  rw [← Iso.app_inv, natIsoMapHomologicalComplex_overFunctorMap_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.symm_inv, eqToIso.hom]

/-- **The restriction comparison on derived categories, at the image of a complex**, in the other
direction. -/
theorem overMapDerivedCategoryRestrictIso_hom_app_Q {V W : X.C} (g : W ⟶ V)
    (M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (overMapDerivedCategoryRestrictIso X g).hom.app (DerivedCategory.Q.obj M) =
      (SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategory.map
          ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.hom.app M) ≫
        (SheafOfModules.overMap.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).mapDerivedCategoryFactors.hom.app
            (restrictComplex X M V) ≫
          DerivedCategory.Q.map (eqToHom (restrictComplex_overMap M g).symm) ≫
            (SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategoryFactors.inv.app
                M := by
  rw [overMapDerivedCategoryRestrictIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso_inv_app_Q]
  rw [← Iso.app_hom (NatIso.mapHomologicalComplex _ _),
    natIsoMapHomologicalComplex_overFunctorMap_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.symm_hom, eqToIso.inv]

/-- **The two spellings of the restriction of a morphism of derived categories agree.** A
morphism `K|_V ⟶ M|_V` written between the derived-category objects of the degreewise
restrictions, conjugated into a morphism between the derived actions of restriction by
`CategoryTheory.Functor.mapDerivedCategoryFactors`, has
`AlgebraicGeometry.RingedSite.restrictDerivedHom` for its restriction along `g : W ⟶ V`; and that
is the same conjugate of `AlgebraicGeometry.RingedSite.restrictDerivedSectionHom`. -/
theorem restrictDerivedHom_restrictDerivedSectionHom {V W : X.C} (g : W ⟶ V)
    (K M : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (φ : DerivedCategory.Q.obj (restrictComplex X K V) ⟶
      DerivedCategory.Q.obj (restrictComplex X M V)) :
    restrictDerivedHom X g (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M)
        ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.hom.app K ≫
          φ ≫ (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.inv.app M) =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategoryFactors.hom.app K ≫
        restrictDerivedSectionHom X g K M φ ≫
          (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).mapDerivedCategoryFactors.inv.app
              M := by
  rw [restrictDerivedHom, overMapDerivedCategoryRestrictIso_inv_app_Q,
    overMapDerivedCategoryRestrictIso_hom_app_Q, restrictDerivedSectionHom,
    Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc, Functor.comp_obj]

/-! ### The same square at chosen representatives of two objects of `D(O)` -/

/-- The inverse of the comparison of a representative with the object it represents, written out:
the restriction of `eA⁻¹` followed by the factorization of restriction through degreewise
restriction. -/
theorem restrictModelIso_inv (U : X.C)
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) :
    (restrictModelIso X U eA).inv =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map eA.inv ≫
        (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.hom.app A :=
  rfl

/-- The comparison of a representative with the object it represents, written out. -/
theorem restrictModelIso_hom (U : X.C)
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) :
    (restrictModelIso X U eA).hom =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.inv.app A ≫
        (SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.map eA.hom :=
  rfl

/-- **The comparisons of chosen representatives with the objects they represent are compatible
with restriction.** Let `eA : Q(A) ≅ L` and `eI : Q(I) ≅ M` present two objects of `D(O)` by
complexes. Reading a morphism `A|_V ⟶ I|_V` between the derived-category objects of the
degreewise restrictions as a morphism `L|_V ⟶ M|_V` through
`AlgebraicGeometry.RingedSite.restrictModelIso` and then restricting it along `g : W ⟶ V` with
`AlgebraicGeometry.RingedSite.restrictDerivedHom` is restricting it with
`AlgebraicGeometry.RingedSite.restrictDerivedSectionHom` and then reading the result over `W`. -/
theorem restrictDerivedHom_homCongr_restrictModelIso {V W : X.C} (g : W ⟶ V)
    {L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (eA : DerivedCategory.Q.obj A ≅ L) (eI : DerivedCategory.Q.obj I ≅ M)
    (φ : DerivedCategory.Q.obj (restrictComplex X A V) ⟶
      DerivedCategory.Q.obj (restrictComplex X I V)) :
    restrictDerivedHom X g L M
        (Linear.homCongr ℤ (restrictModelIso X V eA) (restrictModelIso X V eI) φ) =
      Linear.homCongr ℤ (restrictModelIso X W eA) (restrictModelIso X W eI)
        (restrictDerivedSectionHom X g A I φ) := by
  have harg : Linear.homCongr ℤ (restrictModelIso X V eA) (restrictModelIso X V eI) φ =
      (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.map eA.inv ≫
        ((SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.hom.app A ≫
            φ ≫ (SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.inv.app I) ≫
          (SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.map eI.hom := by
    simp only [Linear.homCongr_apply, restrictModelIso_inv, restrictModelIso_hom, Category.assoc]
  rw [harg, restrictDerivedHom_map_comp_map, restrictDerivedHom_restrictDerivedSectionHom,
    Linear.homCongr_apply, restrictModelIso_inv, restrictModelIso_hom]
  simp only [Category.assoc]

end Derived

end AlgebraicGeometry.RingedSite

end
