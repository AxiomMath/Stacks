module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyFilteredColimitsSpaceTypeU
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorMonoidalClosed

/-!
# The derived category of an algebraic space and its derived internal Hom

Let `X` be an algebraic space over a scheme `S`. Its `𝒪_X`-modules,
`AlgebraicGeometry.Space.Modules`, are the sheaves of modules on the small étale ringed site of
`X`, an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`. The derived internal Hom
`RSheafHom_{𝒪_X}(-, -)` of `D(𝒪_X)` is built in this development for ringed sites whose objects,
morphisms and sections lie in one universe, because the internal Hom complex of Stacks 0A8Z raises
the module universe of a site whose objects lie in `Type (u + 1)`.

The small étale site is essentially `u`-small, and
`AlgebraicGeometry.Space.modulesEquivModelModules` identifies the `𝒪_X`-modules with the sheaves
of modules on its equi-universe model `AlgebraicGeometry.Space.smallEtaleModelRingedSite`, an
`AlgebraicGeometry.RingedSite.{u, u, u}`. This file transports the derived internal Hom of the
model back to `D(𝒪_X)` along the derived equivalence of that identification. This is the device
the development already uses for the derived tensor–Hom statements on an algebraic space
(Stacks 0E4Q).

## Main definitions

* `AlgebraicGeometry.Space.DerivedModules`: `D(𝒪_X)`, at the model of the derived category at
  which the dualizing complexes of Stacks 0E4Z are defined.
* `AlgebraicGeometry.Space.modelDerivedEquivalence`: `D(𝒪_X) ≌ D(𝒪_{model})`.
* `AlgebraicGeometry.Space.derivedSheafHomBifunctor`: `RSheafHom_{𝒪_X}(-, -)`.
* `AlgebraicGeometry.Space.derivedHomology`: the cohomology sheaves `H^n(-)` on `D(𝒪_X)`.
* `AlgebraicGeometry.Space.coherentDerived`: `D_Coh(𝒪_X)`, the objects whose cohomology sheaves
  are coherent (Stacks 07UA).

## Implementation notes

The derived categories are written at `CategoryTheory.HasDerivedCategory.standard`, explicitly,
since the dualizing complexes of Stacks 0E4Z
(`AlgebraicGeometry.Space.IsDualizingComplexOnSpace`) and the derived biduality morphism of the
model (`AlgebraicGeometry.RingedSite.derivedBiduality`) are stated there; no instance of that
model is declared.

## References

* [Stacks Project, Tag 0E4Z](https://stacks.math.columbia.edu/tag/0E4Z)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- The equi-universe model of the small étale site of `F` has binary products: it is equivalent
to the small étale site, which has them. -/
instance smallEtaleModelRingedSite_hasBinaryProducts :
    HasBinaryProducts (smallEtaleModelRingedSite B S hS F hF).C := by
  change HasBinaryProducts (SmallEtaleModel B S hS F)
  haveI := (smallEtaleModelEquivalence B S hS F).isEquivalence_functor
  exact Adjunction.hasLimitsOfShape_of_equivalence (smallEtaleModelEquivalence B S hS F).functor

/-- Sheaves of modules on the equi-universe model of the small étale ringed site of `F`. -/
abbrev ModelModules :=
  SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)

/-- `D(𝒪_X)`: the derived category of the `𝒪_X`-modules of the algebraic space `F`, at the
standard model, at which the dualizing complexes of Stacks 0E4Z are defined. -/
abbrev DerivedModules :=
  @DerivedCategory (Modules.{u, u} B S hS F hF) _ _ (HasDerivedCategory.standard _)

/-- The derived category of the sheaves of modules on the equi-universe model, at the standard
model. -/
abbrev ModelDerivedModules :=
  @DerivedCategory (ModelModules B S hS F hF) _ _ (HasDerivedCategory.standard _)

/-- **`D(𝒪_X) ≌ D(𝒪_{model})`**: the equivalence of derived categories induced by the
identification `AlgebraicGeometry.Space.modulesEquivModelModules` of the `𝒪_X`-modules with the
sheaves of modules on the equi-universe model. -/
def modelDerivedEquivalence : DerivedModules B S hS F hF ≌ ModelDerivedModules B S hS F hF :=
  letI := additive_modulesEquivModelModules_functor B S hS F hF
  @Stacks.DerivedQCoh.Equivalence.mapDerivedCategory _ _ _ (HasDerivedCategory.standard _) _ _ _
    (HasDerivedCategory.standard _) (modulesEquivModelModules B S hS F hF) _

/-- **The derived internal Hom `RSheafHom_{𝒪_X}(-, -)` of an algebraic space**, contravariant in
its first variable: the derived internal Hom of the equi-universe model of the small étale
ringed site (Stacks 0A97), conjugated by `AlgebraicGeometry.Space.modelDerivedEquivalence`. -/
def derivedSheafHomBifunctor :
    (DerivedModules B S hS F hF)ᵒᵖ ⥤ DerivedModules B S hS F hF ⥤ DerivedModules B S hS F hF :=
  letI := HasDerivedCategory.standard (ModelModules B S hS F hF)
  (modelDerivedEquivalence B S hS F hF).functor.op ⋙
    RingedSite.derivedSheafHomBifunctor (smallEtaleModelRingedSite B S hS F hF) ⋙
    (Functor.whiskeringLeft _ _ _).obj (modelDerivedEquivalence B S hS F hF).functor ⋙
      (Functor.whiskeringRight _ _ _).obj (modelDerivedEquivalence B S hS F hF).inverse

/-- `RSheafHom_{𝒪_X}(A, B)`. -/
abbrev derivedSheafHom (A C : DerivedModules B S hS F hF) : DerivedModules B S hS F hF :=
  ((derivedSheafHomBifunctor B S hS F hF).obj (op A)).obj C

/-- The cohomology sheaf functor `H^n : D(𝒪_X) ⥤ Mod(𝒪_X)`. -/
abbrev derivedHomology (n : ℤ) : DerivedModules B S hS F hF ⥤ Modules.{u, u} B S hS F hF :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) n

/-- **`D_Coh(𝒪_X)`**: the objects of `D(𝒪_X)` all of whose cohomology sheaves are coherent
`𝒪_X`-modules in the sense of Stacks 07UA. -/
def coherentDerived : ObjectProperty (DerivedModules B S hS F hF) :=
  fun L => ∀ n : ℤ, IsCoherent B S hS F hF ((derivedHomology B S hS F hF n).obj L)

/-- `D^+(𝒪_X)`: cohomology sheaves vanish in all sufficiently negative degrees. -/
def IsBoundedBelow (L : DerivedModules B S hS F hF) : Prop :=
  ∃ n₀ : ℤ, ∀ n : ℤ, n < n₀ → IsZero ((derivedHomology B S hS F hF n).obj L)

/-- `D^-(𝒪_X)`: cohomology sheaves vanish in all sufficiently positive degrees. -/
def IsBoundedAbove (L : DerivedModules B S hS F hF) : Prop :=
  ∃ n₀ : ℤ, ∀ n : ℤ, n₀ < n → IsZero ((derivedHomology B S hS F hF n).obj L)

end AlgebraicGeometry.Space

end
