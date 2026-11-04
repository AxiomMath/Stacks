module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.FieldTheory.PurelyTranscendental
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Topology.Dimension.Krull

/-!
# One-step dévissage of a module

A *one-step dévissage* of a finite-type quasi-coherent `𝒪_X`-module `F` along `f : X ⟶ S` over
a point `s : S` presents `F` as the direct image from a finitely presented closed subscheme
`Z ⊆ X`, finite over an affine smooth `S`-scheme `Y` whose fibres are geometrically irreducible
of the dimension of the support of `F` on the fibre of `f` over `s`. All four schemes involved
are affine.

A one-step dévissage *at a point* `x : X` is a one-step dévissage over `f x` whose
distinguished fibre has maximal local dimension at `x`, together with a point `z : Z` above `x`
whose image `y : Y` has `z` as its only preimage and whose residue field is purely
transcendental over the residue field of `f x`.

A *standard shrinking* replaces the four schemes of a one-step dévissage at `x` by principal
open neighbourhoods of the four distinguished points, and records that the canonical
restrictions of all the data again form a one-step dévissage at `x`.

## Main definitions

* `AlgebraicGeometry.OneStepDevissage`: a one-step dévissage of `F/X/S` over `s`.
* `AlgebraicGeometry.OneStepDevissageAt`: a one-step dévissage of `F/X/S` at `x`.
* `AlgebraicGeometry.OneStepDevissageAt.StandardShrinking`: a standard shrinking of a one-step
  dévissage at `x`.

## Implementation notes

The maps `i`, `π` and `g` are morphisms over `S` by the commuting triangle `over_base`. The
identification of the module is a categorical isomorphism to the scheme-theoretic pushforward.
The dimension is the topological Krull dimension of the stalkwise support of the pullback of
`F` to the scheme-theoretic fibre, and the fibre-dimension condition is imposed at every point
of `S`, as in the source.

For a dévissage at a point, `x` is represented in the scheme-theoretic fibre by `f.asFiber x`.
Its membership in the support is recorded explicitly so that the local dimension can be taken
at the corresponding point of the support. The residue-field algebra structure is induced by
the canonical residue-field map, transported along the equality `g y = f x`.

In a standard shrinking the maps on the four opens are the canonical restrictions of the
original maps. Heterogeneous equalities identify the schemes, maps, modules and points of the
restricted dévissage with those canonical restrictions, so that no transport along an equality
of scheme structures has to be chosen. The restricted source module is the canonical
restriction rather than an arbitrarily isomorphic module, and the principal opens are taken
from global sections because all four schemes of a one-step dévissage are affine.

## References

* [Stacks Project, Tag 05H4](https://stacks.math.columbia.edu/tag/05H4)
* [Stacks Project, Tag 05H5](https://stacks.math.columbia.edu/tag/05H5)
* [Stacks Project, Tag 05H9](https://stacks.math.columbia.edu/tag/05H9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A one-step dévissage of `F/X/S` over `s`. -/
@[stacks 05H4]
structure OneStepDevissage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (s : S)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] where
  /-- The closed subscheme supporting the module. -/
  Z : Scheme.{u}
  /-- The smooth scheme finite under `Z`. -/
  Y : Scheme.{u}
  /-- The closed immersion. -/
  i : Z ⟶ X
  /-- The finite morphism. -/
  π : Z ⟶ Y
  /-- The smooth structure morphism. -/
  g : Y ⟶ S
  /-- The module on the closed subscheme. -/
  G : Z.Modules
  quasi_coherent_G : G.IsQuasicoherent
  finite_type_G : G.IsFiniteType
  /-- All three displayed maps are over `S`. -/
  over_base : i ≫ f = π ≫ g
  affine_X : IsAffine X
  affine_S : IsAffine S
  affine_Z : IsAffine Z
  affine_Y : IsAffine Y
  closed_immersion : IsClosedImmersion i
  finite_presentation : AlgebraicGeometry.FinitePresentation i
  module_iso : F ≅ (Scheme.Modules.pushforward i).obj G
  finite : IsFinite π
  smooth : Smooth g
  geometrically_irreducible : GeometricallyIrreducible g
  fiber_dimension : ∀ t : S, topologicalKrullDim (g.fiber t) =
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F))

/-- A one-step dévissage of `F/X/S` at `x`. -/
@[stacks 05H5]
structure OneStepDevissageAt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] where
  /-- The one-step dévissage over the image of `x`. -/
  toOneStepDevissage : OneStepDevissage f F (f x)
  /-- The point `x` belongs to the support of the fibre module. -/
  mem_fiber_support : f.asFiber x ∈
    SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F)
  /-- The local dimension of the support at `x` is its dimension. -/
  dimension :
    topologicalKrullDimAt
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
        ⟨f.asFiber x, mem_fiber_support⟩ =
      topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι (f x))).obj F))
  /-- The chosen point of the closed subscheme. -/
  z : toOneStepDevissage.Z
  /-- The image of `z` on the smooth scheme. -/
  y : toOneStepDevissage.Y
  /-- The distinguished point of the closed subscheme lies over `x`. -/
  i_z : toOneStepDevissage.i z = x
  /-- The distinguished points are related by the finite map. -/
  π_z : toOneStepDevissage.π z = y
  /-- The chosen point on the smooth scheme lies above the image of `x`. -/
  g_y : toOneStepDevissage.g y = f x
  /-- The fibre of the finite map above `y` consists only of `z`. -/
  fiber_eq_singleton : toOneStepDevissage.π ⁻¹' {y} = {z}
  /-- The residue field at `y` is purely transcendental over the residue field at `f x`. -/
  residueField_purelyTranscendental :
    letI : Algebra (S.residueField (f x)) (toOneStepDevissage.Y.residueField y) :=
      ((S.residueFieldCongr g_y).inv ≫ toOneStepDevissage.g.residueFieldMap y).hom.toAlgebra
    PurelyTranscendental (S.residueField (f x)) (toOneStepDevissage.Y.residueField y)

namespace OneStepDevissageAt

/-- A standard shrinking of a one-step dévissage at `x`. -/
@[stacks 05H9]
structure StandardShrinking {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) [LocallyOfFiniteType f]
    [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x) where
  S' : S.Opens
  X' : X.Opens
  Z' : D.toOneStepDevissage.Z.Opens
  Y' : D.toOneStepDevissage.Y.Opens
  base_section : Γ(S, ⊤)
  source_section : Γ(X, ⊤)
  closed_section : Γ(D.toOneStepDevissage.Z, ⊤)
  smooth_section : Γ(D.toOneStepDevissage.Y, ⊤)
  base_standard : S' = S.basicOpen base_section
  source_standard : X' = X.basicOpen source_section
  closed_standard : Z' = D.toOneStepDevissage.Z.basicOpen closed_section
  smooth_standard : Y' = D.toOneStepDevissage.Y.basicOpen smooth_section
  mem_base : f x ∈ S'
  mem_source : x ∈ X'
  mem_closed : D.z ∈ Z'
  mem_smooth : D.y ∈ Y'
  source_over_base : X' ≤ f ⁻¹ᵁ S'
  closed_over_source : Z' ≤ D.toOneStepDevissage.i ⁻¹ᵁ X'
  closed_over_smooth : Z' ≤ D.toOneStepDevissage.π ⁻¹ᵁ Y'
  smooth_over_base : Y' ≤ D.toOneStepDevissage.g ⁻¹ᵁ S'
  restricted_morphism : X'.toScheme ⟶ S'.toScheme
  restricted_morphism_eq : restricted_morphism = f.resLE S' X' source_over_base
  locally_finite_type : LocallyOfFiniteType restricted_morphism
  quasi_coherent : (F.restrict X'.ι).IsQuasicoherent
  finite_type : (F.restrict X'.ι).IsFiniteType
  restricted_devissage :
    @OneStepDevissageAt _ _ restricted_morphism (F.restrict X'.ι)
      ⟨x, mem_source⟩ locally_finite_type quasi_coherent finite_type
  restricted_closed : HEq restricted_devissage.toOneStepDevissage.Z Z'.toScheme
  restricted_smooth : HEq restricted_devissage.toOneStepDevissage.Y Y'.toScheme
  restricted_closed_map : HEq restricted_devissage.toOneStepDevissage.i
    (D.toOneStepDevissage.i.resLE X' Z' closed_over_source)
  restricted_finite_map : HEq restricted_devissage.toOneStepDevissage.π
    (D.toOneStepDevissage.π.resLE Y' Z' closed_over_smooth)
  restricted_smooth_map : HEq restricted_devissage.toOneStepDevissage.g
    (D.toOneStepDevissage.g.resLE S' Y' smooth_over_base)
  restricted_closed_module : HEq restricted_devissage.toOneStepDevissage.G
    (D.toOneStepDevissage.G.restrict Z'.ι)
  restricted_z : HEq restricted_devissage.z (⟨D.z, mem_closed⟩ : Z'.toScheme)
  restricted_y : HEq restricted_devissage.y (⟨D.y, mem_smooth⟩ : Y'.toScheme)

end OneStepDevissageAt

end AlgebraicGeometry

end
