module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleSitePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZero
public import StacksFrontier.CategoryTheory.Sites.Modules.Gate18.StalkOfExtensionByZero
public import StacksFrontier.CategoryTheory.Sites.Point.UniverseChange

/-!
# The stalk of an extension by zero along an étale morphism of algebraic spaces

Let `S` be a scheme and let `j_U : U ⟶ X` be an étale morphism of algebraic spaces over `S`.
Restriction of `𝒪_X`-modules along `j_U` has a left adjoint `j_{U!}`, extension by zero, and
for a sheaf of `𝒪_U`-modules `𝒢` and a geometric point `x̄ : Spec(k) ⟶ X` the stalk of
`j_{U!}𝒢` at `x̄` is the direct sum

```
(j_{U!}𝒢)_x̄ = ⨁_ū 𝒢_ū
```

of the stalks of `𝒢` at the geometric points `ū : Spec(k) ⟶ U` with `j_U ∘ ū = x̄`.

An étale morphism of algebraic spaces over `X` is an object `V` of the spaces-étale site of `X`,
and `𝒢` is a module on the ringed site localized at `V`.

## Main definitions

* `AlgebraicGeometry.Space.ExtensionByZeroStalk.sitePoint` is the point of that site
  determined by a geometric point, at the universe of the module sections.
* `AlgebraicGeometry.Space.ExtensionByZeroStalk.Lifts` is the set of geometric points of `U`
  lying over a geometric point of `X`, which indexes the direct sum.
* `AlgebraicGeometry.Space.ExtensionByZeroStalk.moduleStalk` and
  `AlgebraicGeometry.Space.ExtensionByZeroStalk.liftedStalk` are the stalk of an
  `𝒪_X`-module at a geometric point of `X` and the stalk of an `𝒪_U`-module at a lift of it.
* `AlgebraicGeometry.Space.ExtensionByZeroStalk.liftGeometricPoint` is the geometric point of
  `U` attached to a lift.

## Main results

* `AlgebraicGeometry.Space.ExtensionByZeroStalk.stalkExtensionByZeroIso` is Equation 08GU:
  the stalk of `j_{U!}𝒢` at `x̄` is the direct sum of the stalks of `𝒢` at the lifts of `x̄`.
* `AlgebraicGeometry.Space.ExtensionByZeroStalk.ι_stalkExtensionByZeroIso_inv` identifies the
  summand inclusions of the decomposition with those of Tag 0710.
* `AlgebraicGeometry.Space.ExtensionByZeroStalk.isZero_moduleStalk_extensionByZero` is the
  vanishing of the stalk at a geometric point admitting no lift.
* `AlgebraicGeometry.Space.ExtensionByZeroStalk.liftsEquivGeometricPoints` identifies the
  index set with the geometric points of `U` whose image is the given geometric point of `X`.

## Implementation notes

The site used is the spaces-étale ringed site of `X`, whose objects, morphisms and structure
rings live in one universe, and the module sections live in `Type (u + 1)`. The point attached
to a geometric point is raised to that universe by
`CategoryTheory.GrothendieckTopology.Point.ulift`, and the direct sum is indexed by the lifts
themselves, the morphisms `ū : Spec(k) ⟶ U` with `j_U ∘ ū = x̄`, not by isomorphism classes of
them. The isomorphism is stated on the underlying abelian groups of the module stalks, and the
summand indexed by a lift `ū` is the stalk of `𝒢` at the point of the localized site attached to
`ū` by Tag 04H3.

## References

* [Stacks Project, Tag 08GU](https://stacks.math.columbia.edu/tag/08GU)
* [Stacks Project, Tag 0710](https://stacks.math.columbia.edu/tag/0710)
* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 03G0](https://stacks.math.columbia.edu/tag/03G0)
* [Stacks Project, Tag 04H3](https://stacks.math.columbia.edu/tag/04H3)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04LY](https://stacks.math.columbia.edu/tag/04LY)
* [Stacks Project, Tag 0DF9](https://stacks.math.columbia.edu/tag/0DF9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace ExtensionByZeroStalk

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- Sheaves of `𝒪_X`-modules on the spaces-étale ringed site of `X`, with sections in the
universe in which that site lives. -/
abbrev Modules :=
  SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)

variable {B S hS X}

/-- The spaces-étale site of `X` is locally small at its own morphism universe. Instance search
for this times out before reaching `locallySmall_self`, so it is stated directly. -/
local instance (priority := high) locallySmall_spacesEtaleRingedSite_extensionByZeroStalk :
    LocallySmall.{u + 1} (spacesEtaleRingedSite B S hS X).C :=
  locallySmall_self _

/-- The point of the spaces-étale site of `X` determined by a geometric point of `X`, with its
fibre functor raised to the universe of the module sections. -/
abbrev sitePoint (x : GeometricPoint B S hS X.1) :
    GrothendieckTopology.Point.{u + 1} (spacesEtaleRingedSite B S hS X).J :=
  (spacesEtaleSitePoint x).ulift.{u + 1}

/-- The stalk of an `𝒪_X`-module at a geometric point of `X`: the filtered colimit of its
sections over the étale neighbourhoods of the point. -/
abbrev moduleStalk (x : GeometricPoint B S hS X.1) (F : Modules B S hS X) :
    AddCommGrpCat.{u + 1} :=
  (sitePoint x).presheafFiber.obj F.val.presheaf

/-- The lifts of a geometric point `x̄ : Spec(k) ⟶ X` through an algebraic space `V` étale
over `X`: the morphisms `ū : Spec(k) ⟶ U` from the field spectrum of `x̄` to the algebraic
space `U` underlying `V` whose composite with the structure morphism `j_U : U ⟶ X` is `x̄`.
These are the geometric points of `U` lying over `x̄`. -/
abbrev Lifts (V : (spacesEtaleRingedSite B S hS X).C) (x : GeometricPoint B S hS X.1) : Type u :=
  (spacesGeometricFiber x).obj V

/-- The point of the localized site `X_{spaces,étale}/V` determined by a lift of a geometric
point of `X`. By Tag 04H3 these are exactly the points of the localized site lying over the
point determined by `x̄`. -/
abbrev liftedPoint {V : (spacesEtaleRingedSite B S hS X).C} {x : GeometricPoint B S hS X.1}
    (v : Lifts V x) :
    GrothendieckTopology.Point.{u + 1} ((spacesEtaleRingedSite B S hS X).J.over V) :=
  (sitePoint x).over (ULift.up v)

/-- The stalk of an `𝒪_U`-module at a lift of a geometric point of `X`, the module being read
on the localized ringed site `X_{spaces,étale}/V`. -/
abbrev liftedStalk {V : (spacesEtaleRingedSite B S hS X).C} {x : GeometricPoint B S hS X.1}
    (v : Lifts V x)
    (G : SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over V)) :
    AddCommGrpCat.{u + 1} :=
  (liftedPoint v).presheafFiber.obj G.val.presheaf

/-- **Stacks 03EJ.** Extension by zero `j_{U!}` of `𝒪_U`-modules along an étale morphism
`j_U : U ⟶ X` of algebraic spaces, the left adjoint of restriction of `𝒪_X`-modules to the
localized ringed site at `V`. -/
abbrev extensionByZero (V : (spacesEtaleRingedSite B S hS X).C) :
    SheafOfModules.{u + 1}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over V) ⥤
      Modules B S hS X :=
  SheafOfModules.extensionByZero.{u + 1, u + 1, u + 1, u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O) V

/-- The reindexing of the direct sum of Tag 0710 along `Equiv.ulift`: its summands are
indexed by the fibre of the raised point over `V`, which is the `ULift` of the set of lifts of
the geometric point. -/
def sumReindex {V : (spacesEtaleRingedSite B S hS X).C} {x : GeometricPoint B S hS X.1}
    (G : SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over V)) :
    (∐ fun v : ULift.{u + 1} (Lifts V x) => liftedStalk v.down G) ≅
      ∐ fun v : Lifts V x => liftedStalk v G where
  hom := Sigma.desc fun v => Sigma.ι (fun v : Lifts V x => liftedStalk v G) v.down
  inv := Sigma.desc fun v =>
    Sigma.ι (fun v : ULift.{u + 1} (Lifts V x) => liftedStalk v.down G) (ULift.up v)
  hom_inv_id := Sigma.hom_ext _ _ fun ⟨v⟩ => by simp
  inv_hom_id := Sigma.hom_ext _ _ fun v => by simp

/-- Reindexing the direct sum along `Equiv.ulift` changes no summand inclusion. -/
@[simp]
theorem ι_sumReindex_inv {V : (spacesEtaleRingedSite B S hS X).C} {x : GeometricPoint B S hS X.1}
    (G : SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over V))
    (v : Lifts V x) :
    Sigma.ι (fun v : Lifts V x => liftedStalk v G) v ≫ (sumReindex G).inv =
      Sigma.ι (fun v : ULift.{u + 1} (Lifts V x) => liftedStalk v.down G) (ULift.up v) :=
  Sigma.ι_desc _ _

/-- **Stacks 08GU.** Equation 75.10.0.2: for an étale morphism `j_U : U ⟶ X` of algebraic
spaces, a sheaf of `𝒪_U`-modules `𝒢` and a geometric point `x̄ : Spec(k) ⟶ X`, the stalk of
the extension by zero `j_{U!}𝒢` at `x̄` is the direct sum of the stalks of `𝒢` at the
geometric points `ū : Spec(k) ⟶ U` with `j_U ∘ ū = x̄`. -/
@[stacks 08GU, sga "4 IV 11.3.5" "special case"]
def stalkExtensionByZeroIso (V : (spacesEtaleRingedSite B S hS X).C) (x : GeometricPoint B S hS X.1)
    (G : SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over V)) :
    moduleStalk x ((extensionByZero V).obj G) ≅ ∐ fun v : Lifts V x => liftedStalk v G :=
  Stacks.Sites.ExtensionByZero.stalkExtensionByZeroIso
    (spacesEtaleRingedSite B S hS X) (sitePoint x) V G ≪≫ sumReindex G

/-- The inclusion of the summand of Equation 08GU indexed by a lift `ū` of `x̄` is the
inclusion of the summand of Tag 0710 indexed by that lift, read in the fibre of the raised
point. -/
theorem ι_stalkExtensionByZeroIso_inv (V : (spacesEtaleRingedSite B S hS X).C)
    (x : GeometricPoint B S hS X.1)
    (G : SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over V))
    (v : Lifts V x) :
    Sigma.ι (fun v : Lifts V x => liftedStalk v G) v ≫
        (stalkExtensionByZeroIso V x G).inv =
      Sigma.ι (fun v : ULift.{u + 1} (Lifts V x) => liftedStalk v.down G) (ULift.up v) ≫
        (Stacks.Sites.ExtensionByZero.stalkExtensionByZeroIso
          (spacesEtaleRingedSite B S hS X) (sitePoint x) V G).inv :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (ι_sumReindex_inv G v))

/-- **Stacks 08GU.** At a geometric point of `X` admitting no lift to `U` the stalk of
`j_{U!}𝒢` vanishes. -/
@[stacks 08GU "vanishing away from the image"]
theorem isZero_moduleStalk_extensionByZero (V : (spacesEtaleRingedSite B S hS X).C)
    (x : GeometricPoint B S hS X.1)
    (G : SheafOfModules.{u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O).over V))
    [IsEmpty (Lifts V x)] :
    IsZero (moduleStalk x ((extensionByZero V).obj G)) :=
  IsZero.of_iso (AlgebraicGeometry.isZero_sigma_of_isEmpty _) (stalkExtensionByZeroIso V x G)

/-- The geometric point of `U` determined by a lift of a geometric point `x̄` of `X`: it keeps
the field of `x̄` and has the lift as its section, so distinct lifts give distinct geometric
points. -/
def liftGeometricPoint {V : (spacesEtaleRingedSite B S hS X).C} {x : GeometricPoint B S hS X.1}
    (v : Lifts V x) :
    GeometricPoint B S hS ((SpacesEtale.toSpaces B S hS X).obj V).1 :=
  ⟨{ carrier := x.val.carrier
     field := x.val.field
     contained := x.val.contained
     toBase := x.val.toBase
     value := v.1 }, x.2⟩

/-- A lift of a geometric point of `X` is a geometric point of `U` whose image under the
structure morphism `j_U : U ⟶ X` is the given one. -/
theorem geometricPointMap_liftGeometricPoint {V : (spacesEtaleRingedSite B S hS X).C}
    {x : GeometricPoint B S hS X.1} (v : Lifts V x) :
    geometricPointMap ((SpacesEtale.inclusion B S hS X).obj V).hom.hom
      (liftGeometricPoint v) = x := by
  apply Subtype.ext
  dsimp only [geometricPointMap, liftGeometricPoint, FieldValuedPoint.map]
  congr 1
  exact v.2

/-- **Stacks 08GU.** The index set of Equation 08GU is the set of geometric points of `U`
lying over the given geometric point of `X`. -/
@[stacks 08GU "the index set"]
def liftsEquivGeometricPoints (V : (spacesEtaleRingedSite B S hS X).C)
    (x : GeometricPoint B S hS X.1) :
    Lifts V x ≃
      {y : GeometricPoint B S hS ((SpacesEtale.toSpaces B S hS X).obj V).1 //
        geometricPointMap ((SpacesEtale.inclusion B S hS X).obj V).hom.hom y = x} :=
  Equiv.ofBijective (fun v => ⟨liftGeometricPoint v, geometricPointMap_liftGeometricPoint v⟩) <| by
    constructor
    · intro v v' h
      apply Subtype.ext
      simpa [liftGeometricPoint, Subtype.ext_iff] using h
    · rintro ⟨y, rfl⟩
      exact ⟨⟨y.val.value, rfl⟩, rfl⟩

end ExtensionByZeroStalk

end AlgebraicGeometry.Space

end
