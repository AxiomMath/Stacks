module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# The cohomology presheaf of a complex of sheaves of modules

For a complex `K` of sheaves of modules, the presheaf `U ↦ Hⁿ(Γ(U, K))` sheafifies to the
cohomology sheaf `Hⁿ(K)`; the canonical map from the presheaf to the cohomology sheaf is locally
injective and locally surjective.

## Main definitions

* `AlgebraicGeometry.AffineExt.homologyPresheaf`: the presheaf `U ↦ Hⁿ(Γ(U, K))`.
* `AlgebraicGeometry.AffineExt.toHomologySheaf`: the canonical map from `homologyPresheaf K n` to
  the cohomology sheaf `Hⁿ(K)`.
* `AlgebraicGeometry.AffineExt.sectionsHomologyIso`: the value of the cohomology presheaf over `U`
  is the cohomology of the complex of sections over `U`.

## Main results

* `AlgebraicGeometry.AffineExt.sheafificationHomologyPresheafIso`: the sheafification of
  `homologyPresheaf K n` is isomorphic to `Hⁿ(K)`.
* `AlgebraicGeometry.AffineExt.isLocallyInjective_toHomologySheaf` and
  `AlgebraicGeometry.AffineExt.isLocallySurjective_toHomologySheaf`: the map `toHomologySheaf K n`
  is locally injective and locally surjective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.AffineExt

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable (K : CochainComplex (SheafOfModules.{u} R) ℤ) (n : ℤ)

/-- The presheaf of degree-`n` cohomology of the sections of a complex of sheaves of modules. -/
abbrev homologyPresheaf : PresheafOfModules.{u} R.obj :=
  (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology n

/-- Sheafifying the presheaf of cohomology of sections gives the cohomology sheaf. -/
def sheafificationHomologyPresheafIso :
    (PresheafOfModules.sheafification (𝟙 R.obj)).obj (homologyPresheaf K n) ≅ K.homology n :=
  (((((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc
      n).mapHomologyIso
      (PresheafOfModules.sheafification (𝟙 R.obj))).symm ≪≫
    HomologicalComplex.homologyMapIso
      ((NatIso.mapHomologicalComplex (asIso (PresheafOfModules.sheafificationAdjunction
        (𝟙 R.obj)).counit) (ComplexShape.up ℤ)).app K) n

/-- The canonical map from the presheaf of cohomology of sections to the cohomology sheaf. -/
def toHomologySheaf :
    homologyPresheaf K n ⟶
      (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).obj (K.homology n) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app _ ≫
    (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map
      (sheafificationHomologyPresheafIso K n).hom

/-- On underlying presheaves of abelian groups, `toHomologySheaf K n` is the sheafification unit
of `homologyPresheaf K n` followed by the isomorphism `sheafificationHomologyPresheafIso K n`. -/
lemma toPresheaf_map_toHomologySheaf :
    (PresheafOfModules.toPresheaf R.obj).map (toHomologySheaf K n) =
      (PresheafOfModules.toPresheaf R.obj).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app (homologyPresheaf K n)) ≫
        (PresheafOfModules.toPresheaf R.obj).map
          ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map
            (sheafificationHomologyPresheafIso K n).hom) :=
  Functor.map_comp _ _ _

/-- The canonical map from the cohomology presheaf to the cohomology sheaf is locally injective. -/
instance isLocallyInjective_toHomologySheaf :
    Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map (toHomologySheaf K n))
        := by
  rw [toPresheaf_map_toHomologySheaf]
  haveI : Presheaf.IsLocallyInjective J ((PresheafOfModules.toPresheaf R.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app (homologyPresheaf K n))) :=
    (inferInstance : Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J (homologyPresheaf K n).presheaf))
  infer_instance

/-- The canonical map from the cohomology presheaf to the cohomology sheaf is locally
surjective. -/
instance isLocallySurjective_toHomologySheaf :
    Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map (toHomologySheaf K
        n)) := by
  rw [toPresheaf_map_toHomologySheaf]
  haveI : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R.obj).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app (homologyPresheaf K n))) :=
    (inferInstance : Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J (homologyPresheaf K n).presheaf))
  infer_instance

/-- Sections over `U`, as abelian groups. -/
abbrev sectionsAb (U : Cᵒᵖ) : PresheafOfModules.{u} R.obj ⥤ AddCommGrpCat.{u} :=
  PresheafOfModules.toPresheaf R.obj ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj U

/-- The complex of sections over `U` of a complex of sheaves of modules. -/
abbrev sectionsComplex (U : Cᵒᵖ) : CochainComplex AddCommGrpCat.{u} ℤ :=
  ((sectionsAb U).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- The restriction maps of the complexes of sections. -/
abbrev sectionsComplexRestrict {U V : Cᵒᵖ} (f : U ⟶ V) : sectionsComplex K U ⟶ sectionsComplex K V
    :=
  (NatTrans.mapHomologicalComplex (Functor.whiskerLeft (PresheafOfModules.toPresheaf R.obj)
    ((evaluation Cᵒᵖ AddCommGrpCat.{u}).map f)) (ComplexShape.up ℤ)).app
      (((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

/-- The value of the cohomology presheaf over `U` is the cohomology of the complex of sections
over `U`. -/
def sectionsHomologyIso (U : Cᵒᵖ) :
    (sectionsComplex K U).homology n ≅ (homologyPresheaf K n).presheaf.obj U :=
  ((((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc
      n).mapHomologyIso
    (sectionsAb U)

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The isomorphisms `sectionsHomologyIso K n U` are natural in `U`: they commute with the maps
induced on cohomology by restriction of sections. -/
lemma sectionsHomologyIso_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    HomologicalComplex.homologyMap (sectionsComplexRestrict K f) n ≫ (sectionsHomologyIso K n
        V).hom =
      (sectionsHomologyIso K n U).hom ≫ (homologyPresheaf K n).presheaf.map f := by
  have h := NatTrans.app_homology (Functor.whiskerLeft (PresheafOfModules.toPresheaf R.obj)
    ((evaluation Cᵒᵖ AddCommGrpCat.{u}).map f))
    ((((SheafOfModules.forget R).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).sc n)
  refine Eq.trans ?_ (congrArg ((sectionsHomologyIso K n U).hom ≫ ·) h.symm)
  exact (Iso.hom_inv_id_assoc _ _).symm

end AlgebraicGeometry.AffineExt
