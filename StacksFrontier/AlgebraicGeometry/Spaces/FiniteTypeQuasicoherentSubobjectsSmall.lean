module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsQcqs

/-!
# The finite type quasi-coherent submodules of a module form an essentially small category

The category `AlgebraicGeometry.Space.FiniteTypeQuasicoherentSubobject` of finite type
quasi-coherent submodules of an `𝒪_X`-module on an algebraic space is a full subcategory of the
subobjects of the module, and the category of `𝒪_X`-modules is Grothendieck abelian
(`SheafOfModules.isGrothendieckAbelian_of_essentiallySmall`), hence well-powered.  So the index
category is essentially small, which is what reindexing a filtered colimit over it by a small
category needs.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- In a Grothendieck abelian category every full subcategory of the subobjects of an object is
essentially small: the category is well-powered. -/
theorem essentiallySmall_fullSubcategory_subobject.{v, w} {C : Type v} [Category.{w} C]
    [Abelian C] [IsGrothendieckAbelian.{u} C] {F : C} (P : ObjectProperty (Subobject F)) :
    EssentiallySmall.{u} P.FullSubcategory := by
  have : ObjectProperty.Small.{u} P := inferInstance
  infer_instance

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against `Modules.{u, u}`; the abelian structure used here is the
one at the pinned universes, as in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsQcqs`. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- **The finite type quasi-coherent submodules of an `𝒪_X`-module form an essentially small
category.** -/
theorem essentiallySmall_finiteTypeQuasicoherentSubobject (F : Modules.{u, u} B S hS X hX) :
    EssentiallySmall.{u} (FiniteTypeQuasicoherentSubobject B S hS X hX F) := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X hX).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X)
    infer_instance
  have _ : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X hX) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  exact essentiallySmall_fullSubcategory_subobject _

end AlgebraicGeometry.Space
