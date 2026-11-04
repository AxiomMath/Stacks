module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedTriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import StacksFrontier.Homology.Injectives.DerivedCategory.Existence
public import StacksFrontier.Homology.KFlat.FilteredColimitShifts

/-!
# The locally small derived category of sheaves of modules

Let `C` be a Grothendieck abelian category which is locally small in a universe `w`. Its
unbounded derived category then exists with morphism types in `w` and not merely in
`max u v`: morphisms out of a complex `K` into a complex `L` are computed as homotopy classes
of maps `K ⟶ I` into a K-injective resolution `L ⟶ I`, and such homotopy classes form a
subquotient of a morphism type of the category of complexes. This is Tag 079Q, available here
as `Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`; this file turns it into a
`HasDerivedCategory.{u}` model, to be activated where it is wanted, for the two categories of
geometric interest, sheaves of
modules `SheafOfModules R` over a sheaf of rings on a site and their special case `X.Modules`
for a scheme `X`, and records the consequence which is the whole point of having it.

That consequence is that the derived category `D(C)` inherits the `w`-indexed direct sums of
`C`, *at its own morphism universe*. The localization functor `Q : C(C) ⥤ D(C)` preserves
`w`-indexed coproducts, because the termwise direct sum of complexes is a coproduct already in
the homotopy category and the quasi-isomorphisms are stable under `w`-indexed coproducts by
Grothendieck's axiom AB4; since every object of `D(C)` is in the image of `Q` up to
isomorphism, `D(C)` has those coproducts. For `X.Modules` the Grothendieck universe is `u` and
the derived category constructed here has morphisms in `Type u`, so what comes out is
`HasCoproducts.{u} (DerivedCategory X.Modules)` with `u` *also* the morphism universe — which is
exactly the hypothesis that Brown representability, Tag 0A8G, asks for. With
`HasDerivedCategory.standard` it is not: there the morphisms live in `Type (u + 1)` and Tag 0A8G
would need a direct sum of a `Type (u + 1)`-indexed family of sheaves of `𝒪_X`-modules, which
does not exist.

## Main results

* `SheafOfModules.hasDerivedCategory` and
  `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` — the locally small derived category
  models, activated by `open scoped Stacks.SmallDerivedModel`: the morphisms of `D(SheafOfModules
  R)` and of `D(𝒪_X)` are in `Type u`.
* `Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory` — the derived category of a
  Grothendieck abelian category has direct sums indexed by its Grothendieck universe, for any
  choice of derived category.
* `AlgebraicGeometry.Scheme.Modules.exists_isTriangulated_rightAdjoint_of_compactlyGenerated` —
  Brown representability applied to `D(𝒪_X)`: a direct-sum-preserving exact functor out of a
  compactly generated `D(𝒪_X)` has an exact right adjoint. Every hypothesis of Tag 0A8G other
  than compact generation is discharged by instance search at the locally small model.

## Implementation notes

The three `HasDerivedCategory` declarations are `abbrev`s, not global instances, following
Mathlib's treatment of `HasDerivedCategory.standard`: a file chooses its model of `D(C)` and
says so. `HasDerivedCategory.{w}` leaves its universe `w` free, so whichever instance search
tries first decides which category `DerivedCategory C` denotes; as global instances these models
silently overrode a default-priority `attribute [local instance] HasDerivedCategory.standard` in
every file that could see them. A file that wants the locally small model writes
`attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` (or the
`ModuleCat`/`SheafOfModules` one), or `open scoped Stacks.SmallDerivedModel` for all three;
neither reaches the file's importers. A statement proved for the standard model says nothing
about this one, the two derived categories being merely equivalent and not equal.

`derivedCategoryQ_preservesCoproducts` differs from
`Stacks.Injectives.derivedCategoryQ_preservesCoproducts` in being stated for an arbitrary
`[HasDerivedCategory.{w'} C]`, where that one is stated for the standard model, which is fixed
by a file-level local instance there. The arbitrary-model form is what the results below need
and it is no harder: the underlying coproduct bridge
`CochainComplex.KFlat.CoproductBridge.derivedCategory_Q_preservesCoproductsOfShape` is already
model-agnostic.

That a right derived functor of an exact functor out of the homotopy category is itself exact is
`Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor`.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Mark Hovey, *Model category structures on chain complexes of sheaves*][hovey-2001]
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated Opposite

universe w' w v u

namespace Stacks.SmallDerivedCategory

/-! ### Direct sums in the derived category, at an arbitrary model -/

section Coproducts

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{w'} C]

/-- The localization functor `Q : C(C) ⥤ D(C)` of a Grothendieck abelian category preserves
coproducts indexed by any type of its Grothendieck universe, for any choice of derived
category. A Grothendieck abelian category has those coproducts and they are exact (AB4), which
is what makes the quasi-isomorphisms stable under them. -/
theorem derivedCategoryQ_preservesCoproducts (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q (C := C)) :=
  CochainComplex.KFlat.CoproductBridge.derivedCategory_Q_preservesCoproductsOfShape C
    ⟨inferInstance, fun _ => ⟨inferInstance, inferInstance⟩⟩ J

/-- The derived category of a Grothendieck abelian category has coproducts indexed by any type
of its Grothendieck universe: the termwise direct sum of a family of complexes represents the
direct sum of the objects they represent, and every object of the derived category is
represented by a complex. -/
theorem hasColimitsOfShape_discrete_derivedCategory (J : Type w) :
    HasColimitsOfShape (Discrete J) (DerivedCategory C) := by
  have := derivedCategoryQ_preservesCoproducts C J
  refine ⟨fun F => ?_⟩
  let K : Discrete J ⥤ CochainComplex C ℤ :=
    Discrete.functor fun j => DerivedCategory.Q.objPreimage (F.obj ⟨j⟩)
  have : HasColimit (K ⋙ DerivedCategory.Q) := inferInstance
  exact hasColimit_of_iso (F := K ⋙ DerivedCategory.Q)
    (Discrete.natIso fun j => (DerivedCategory.Q.objObjPreimageIso (F.obj j)).symm)

/-- **Direct sums in the derived category.** The derived category of a Grothendieck abelian
category has arbitrary direct sums indexed by its Grothendieck universe. -/
theorem hasCoproducts_derivedCategory : HasCoproducts.{w} (DerivedCategory C) := fun J =>
  hasColimitsOfShape_discrete_derivedCategory C J

end Coproducts

end Stacks.SmallDerivedCategory

/-! ### Modules over a ring -/

namespace ModuleCat

/-- **The locally small derived category of modules over a ring.** The morphisms of
`D(ModuleCat.{u} R)` are in `Type u` and not merely in `Type (u + 1)`: `R`-modules in `Type u`
form a Grothendieck abelian category locally small in `u`, so Tag 079Q applies.

This is the companion of `SheafOfModules.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, and is activated the same way:
a comparison between `D(R)` and `D(𝒪_X)` has content only when both sides are taken at a model
where the direct-sum and representability statements hold. -/
abbrev hasDerivedCategory {R : Type u} [Ring R] : HasDerivedCategory.{u} (ModuleCat.{u} R) :=
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

end ModuleCat

/-! ### Sheaves of modules on a site -/

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- **The locally small derived category of sheaves of modules.** Sheaves of `R`-modules on a
site with `R`-modules in `Type u` form a Grothendieck abelian category which is locally small
in `u`, so by Tag 079Q their unbounded derived category exists with morphisms again in
`Type u`. -/
abbrev hasDerivedCategory : HasDerivedCategory.{u} (SheafOfModules.{u} R) :=
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

attribute [local instance] hasDerivedCategory

/-- The derived category of sheaves of `R`-modules has direct sums indexed by any type in
`Type u`, which is also its morphism universe. -/
instance hasColimitsOfShape_discrete_derivedCategory (I : Type u) :
    HasColimitsOfShape (Discrete I) (DerivedCategory (SheafOfModules.{u} R)) :=
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory _ I

end SheafOfModules

/-! ### Sheaves of modules on a scheme, and Brown representability -/

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- **The locally small derived category of `𝒪_X`-modules.** For a scheme `X`, the unbounded
derived category of `𝒪_X`-modules exists with morphisms in `Type u`: `𝒪_X`-modules form a
Grothendieck abelian category locally small in `u`, and Tag 079Q computes the derived morphism
types as homotopy classes of maps into a K-injective resolution.

This, and not `HasDerivedCategory.standard`, is the derived category against which the
direct-sum and Brown-representability statements about `D(𝒪_X)` have content. -/
abbrev hasDerivedCategory : HasDerivedCategory.{u} X.Modules :=
  Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _

attribute [local instance] hasDerivedCategory

/-- `D(𝒪_X)` has direct sums indexed by any type in `Type u`, which is also its morphism
universe. -/
instance hasColimitsOfShape_discrete_derivedCategory (I : Type u) :
    HasColimitsOfShape (Discrete I) (DerivedCategory X.Modules) :=
  Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory _ I

variable {X}

/-- **Brown representability for `D(𝒪_X)`** ([Stacks, Tag 0A8G]). Let `X` and `Y` be schemes and
let `F : D(𝒪_X) ⥤ D(𝒪_Y)` be an exact functor of triangulated categories which preserves direct
sums. If `D(𝒪_X)` is compactly generated by a family `E` — each `preadditiveCoyoneda.obj (op
(E i))` preserves direct sums, and the only objects right orthogonal to all shifts of all `E i`
are the zero objects — then `F` has a right adjoint, which is again exact.

Of the hypotheses of Tag 0A8G, all but compact generation are discharged by instance search
here: `D(𝒪_X)` is triangulated, and it has the direct sums indexed by `Type u`, which is its
morphism universe because the derived category in force (by the local instance above) is the
locally small one. -/
theorem exists_isTriangulated_rightAdjoint_of_compactlyGenerated {Y : Scheme.{u}}
    (F : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ α : Type u, PreservesColimitsOfShape (Discrete α) F]
    {ι : Type u} (E : ι → DerivedCategory X.Modules)
    [∀ (i : ι) (α : Type u),
      PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (E i)))]
    (hE : ∀ K : DerivedCategory X.Modules,
      ((ofObj E).shiftClosure ℤ).rightOrthogonal K → IsZero K) :
    ∃ (G : DerivedCategory Y.Modules ⥤ DerivedCategory X.Modules) (adj : F ⊣ G)
      (_ : G.CommShift ℤ), adj.IsTriangulated :=
  Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated F E hE

end AlgebraicGeometry.Scheme.Modules

/-! ### Opting into the locally small models

`open scoped Stacks.SmallDerivedModel` makes the three locally small models
`ModuleCat.hasDerivedCategory`, `SheafOfModules.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` instances in the scope where it is
written, and nowhere else. A file that needs only one of them can instead write
`attribute [local instance] ModuleCat.hasDerivedCategory` (or the other two). -/
namespace Stacks.SmallDerivedModel

attribute [scoped instance] ModuleCat.hasDerivedCategory SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

end Stacks.SmallDerivedModel

end
