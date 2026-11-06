module

public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessAndStrictTransformImageUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimageBaseChange
import all StacksFrontier.AlgebraicGeometry.Stacks.FlatAtAPoint

/-!
# Base change of the formal glueing situation

The situation of Stacks 0AEV — a quasi-compact, quasi-separated `f : Y ⟶ X`, a finitely
presented closed `Z ⊆ X` over which `f` is an isomorphism, with `f` flat along `f⁻¹(Z)` — is
stable under base change along an *arbitrary* morphism `g : X' ⟶ X` of algebraic spaces: take
`Y' = Y ×_X X'`, `Z' = g⁻¹(Z)` and `f'` the projection `Y' ⟶ X'`.

This file constructs that situation.  Nothing in the library did: every consumer of
`AlgebraicGeometry.Space.FormalGlueingSituation` took one as a parameter, and
`AlgebraicGeometry.Space.FormalGlueingSituation.FlatBaseChange` relates two situations that are
both given.  The implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Pushouts/FormalGlueingModulesFlatBaseChange.lean` list the
six stabilities such a construction asks for; all six are proved, and this file is their
assembly.

Flatness of `g` is **not** required.  It is needed only to produce the base-change data of
Stacks 0AEZ, and under that extra hypothesis the term is supplied as well.

## Main definitions

* `AlgebraicGeometry.Space.FormalGlueingSituation.baseChangeAlong`: the situation over `X'`,
  for the morphism given as a morphism of presheaves together with algebraicity of its source.
* `AlgebraicGeometry.Space.FormalGlueingSituation.baseChange`: the same for a morphism of
  `AlgebraicGeometry.AlgebraicSpaces`.
* `AlgebraicGeometry.Space.FormalGlueingSituation.flatBaseChangeAlong` and
  `AlgebraicGeometry.Space.FormalGlueingSituation.flatBaseChange`: for a flat `g`, the
  base-change data of Stacks 0AEZ relating the given situation to the constructed one, in the
  same two spellings.

## Which stability discharges which field

* algebraicity of `X'` is carried by the morphism's source; algebraicity of `Y'` is
  **Stacks 02X2**, `AlgebraicGeometry.isAlgebraicSpace_pullback`;
* quasi-compactness of `f'` is **Stacks 03HF**,
  `AlgebraicGeometry.Space.isQuasiCompact_of_isPullback`;
* quasi-separatedness of `f'` is **Stacks 03KL**, part (3),
  `AlgebraicGeometry.Space.isQuasiSeparated_pullback`;
* closedness of `Z'` is **Stacks 083Q**,
  `AlgebraicGeometry.Space.isClosedSubspace_preimage`;
* finite presentation of `Z' ↪ X'` is **Stacks 03XR**,
  `AlgebraicGeometry.Space.IsFinitePresentation.of_isPullback`, applied to the fibre-product
  characterization `CategoryTheory.Subfunctor.isPullback_preimage` of an inverse image
  (Stacks 083Q) — the inclusion of `Z'` is the base change of the inclusion of `Z`;
* invertibility of the projection `(f')⁻¹(Z') ⟶ Z'` is
  `CategoryTheory.Subfunctor.isIso_fromPreimage_preimage_of_isPullback`, isomorphisms being
  stable under base change;
* flatness of `f'` at every point of `(f')⁻¹(Z')` is the structure sheaf case of
  **Stacks 05VW**, `AlgebraicGeometry.Stack.AlgebraicStacks.isFlatAt_of_isPullback_presheaf`
  (a private lemma of `StacksFrontier/AlgebraicGeometry/Stacks/FlatAtAPoint.lean`, reached by
  `import all`), at the point of `(f)⁻¹(Z)` which the point of `(f')⁻¹(Z')` maps to.

## Implementation notes

No `@[stacks]` attribute is attached.  Stacks 0AEV is the situation itself, which
`AlgebraicGeometry.Space.FormalGlueingSituation` carries; this is infrastructure for it and not
a numbered result.

The closed part of the base change is the inverse image subfunctor `g⁻¹(Z)`, so the two open
parts of the constructed situation are the open complements of *that*, and the identification of
them with the inverse images of `U` and of `V` is `AlgebraicGeometry.Space.openComplement_preimage`
— a propositional equality and not a definitional one.  The morphisms `U' ⟶ U` and `V' ⟶ V` that
Stacks 0AEZ asks for are therefore built by
`CategoryTheory.Subfunctor.mapOfEqPreimage`, which takes exactly such an equality, rather than by
`CategoryTheory.Subfunctor.fromPreimage`.

The pointwise flatness field is the only one whose proof is not a single application: the point
of `(f')⁻¹(Z')` has to be pushed to a point of `f⁻¹(Z)`, and that is the projection of
`CategoryTheory.Subfunctor.mapOfEqPreimage` for the identification
`(f')⁻¹(g⁻¹Z) = (g_Y)⁻¹(f⁻¹Z)` of `CategoryTheory.Subfunctor.preimage_preimage_of_isPullback`,
read on points.

The compatibility with the restriction of `f` is
`CategoryTheory.Subfunctor.mapOfEqPreimage_comm`, stated there for a bare cartesian square of
presheaves: at a subfunctor of the base change the ambient space is reached only by unfolding
the constructor below, so a statement phrased at it is out of reach of `rw` and `simp`.

## References

* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AEZ](https://stacks.math.columbia.edu/tag/0AEZ)
* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
* [Stacks Project, Tag 03XR](https://stacks.math.columbia.edu/tag/03XR)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.FormalGlueingSituation

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullback_presheaf_FormalGlueingSituationBaseChange
    {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (Limits.functorCategoryHasLimitsOfShape :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)).has_limit _

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : FormalGlueingSituation B S hS) {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (g : X' ⟶ D.X)

/-- **The base change of a formal glueing situation along an arbitrary morphism of its ambient
space.** For `g : X' ⟶ X` the situation over `X'` has `Y' = Y ×_X X'`, closed part `g⁻¹(Z)` and
`f'` the projection `Y' ⟶ X'`.

Each of the six conditions of Stacks 0AEV is a base-change stability that is already proved; the module
docstring says which discharges which.  Flatness of `g` is not used. -/
def baseChangeAlong : FormalGlueingSituation B S hS where
  X := X'
  Y := pullback D.f g
  algebraicSpace_X := hX'
  algebraicSpace_Y :=
    isAlgebraicSpace_pullback B S hS D.f g D.algebraicSpace_Y hX' D.algebraicSpace_X
  f := pullback.snd D.f g
  quasiCompact_f :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback D.f g) D.quasiCompact_f
  quasiSeparated_f := isQuasiSeparated_pullback B S hS D.f g D.quasiSeparated_f
  Z := D.Z.preimage g
  closed_Z :=
    isClosedSubspace_preimage B S hS g D.Z D.algebraicSpace_X hX' D.closed_Z
  finitePresentation_Z :=
    IsFinitePresentation.of_isPullback B S hS
      (isClosedSubspace_preimage B S hS g D.Z D.algebraicSpace_X hX' D.closed_Z).1
      D.closed_Z.1 hX' D.algebraicSpace_X
      (Subfunctor.isPullback_preimage g D.Z) D.finitePresentation_Z
  iso_over_Z :=
    Subfunctor.isIso_fromPreimage_preimage_of_isPullback
      (IsPullback.of_hasPullback D.f g).flip D.Z D.iso_over_Z
  flat_at_preimage_Z := by
    intro x
    refine Stack.AlgebraicStacks.isFlatAt_of_isPullback_presheaf B S hS
      (isAlgebraicSpace_pullback B S hS D.f g D.algebraicSpace_Y hX'
        D.algebraicSpace_X)
      D.algebraicSpace_Y hX' D.algebraicSpace_X
      (IsPullback.of_hasPullback D.f g) _ ?_
    have hZ := Subfunctor.preimage_preimage_of_isPullback D.Z
      (IsPullback.of_hasPullback D.f g)
    have hι : Subfunctor.mapOfEqPreimage (D.Z.preimage D.f) (pullback.fst D.f g) hZ ≫
        (D.Z.preimage D.f).ι = _ ≫ pullback.fst D.f g := Subfunctor.lift_ι _ _
    have hflat := D.flat_at_preimage_Z (pointsMap B S hS _
      (Subfunctor.mapOfEqPreimage (D.Z.preimage D.f) (pullback.fst D.f g) hZ) x)
    rwa [← pointsMap_comp_apply, hι, pointsMap_comp_apply] at hflat

/-- The open complement of the closed part of the base change is the inverse image of the open
complement of the closed part: the closed parts correspond by construction, and taking open
complements commutes with inverse images. -/
theorem baseChangeAlong_U_eq : (D.baseChangeAlong hX' g).U = D.U.preimage g :=
  (openComplement_preimage B S hS D.Z g).symm

/-- The open complement of the inverse image of the closed part of the base change is the
inverse image of the open complement of the inverse image of the closed part: both are the
inverse image of `U` along the composite `Y' ⟶ X`. -/
theorem baseChangeAlong_V_eq : (D.baseChangeAlong hX' g).V = D.V.preimage (pullback.fst D.f g) := by
  show ((D.baseChangeAlong hX' g).U).preimage (pullback.snd D.f g) =
    (D.U.preimage D.f).preimage (pullback.fst D.f g)
  rw [baseChangeAlong_U_eq]
  exact Subfunctor.preimage_preimage_of_isPullback D.U (IsPullback.of_hasPullback D.f g)

/-- **The base-change data of Stacks 0AEZ for a flat morphism of ambient spaces.** For a flat
`g : X' ⟶ X` the situation `AlgebraicGeometry.Space.FormalGlueingSituation.baseChangeAlong` carries
the data relating it to the original: the morphisms of the four spaces, the three cartesian
squares, and the compatibility with the restriction of the morphism glued along.

Flatness of `g` enters only here, as the field it is the content of.  The two open parts are
the base changes of the two open parts of the original by
`AlgebraicGeometry.Space.FormalGlueingSituation.baseChangeAlong_U_eq` and
`baseChangeAlong_V_eq`, and their projections are
`CategoryTheory.Subfunctor.mapOfEqPreimage` for those equalities. -/
def flatBaseChangeAlong (hg : IsFlat B S hS g) : FlatBaseChange D (D.baseChangeAlong hX' g) where
  g := ObjectProperty.homMk g
  flat_g := hg
  gY := ObjectProperty.homMk (pullback.fst D.f g)
  isPullback_Y :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (IsPullback.of_hasPullback D.f g)
  Z_eq := rfl
  gU := ObjectProperty.homMk
    (Subfunctor.mapOfEqPreimage D.U g (baseChangeAlong_U_eq D hX' g))
  isPullback_U :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (Subfunctor.isPullback_mapOfEqPreimage D.U g (baseChangeAlong_U_eq D hX' g))
  gV := ObjectProperty.homMk
    (Subfunctor.mapOfEqPreimage D.V (pullback.fst D.f g) (baseChangeAlong_V_eq D hX' g))
  isPullback_V :=
    IsPullback.of_map_of_faithful
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
      (Subfunctor.isPullback_mapOfEqPreimage D.V (pullback.fst D.f g)
        (baseChangeAlong_V_eq D hX' g))
  overlapRestriction_comm :=
    ObjectProperty.hom_ext _
      (Subfunctor.mapOfEqPreimage_comm D.U (IsPullback.of_hasPullback D.f g)
        (baseChangeAlong_U_eq D hX' g) (baseChangeAlong_V_eq D hX' g))

/-! ### The same for a morphism of algebraic spaces -/

/-- **The base change of a formal glueing situation along a morphism of algebraic spaces into
its ambient space.** This is
`AlgebraicGeometry.Space.FormalGlueingSituation.baseChangeAlong` for the underlying morphism of
presheaves; the two carry the same data, since an object of
`AlgebraicGeometry.AlgebraicSpaces` is a presheaf together with the proof that it is an
algebraic space.

No flatness of `k` is required. -/
def baseChange {X'' : AlgebraicSpaces B S hS} (k : X'' ⟶ D.spaceX) :
    FormalGlueingSituation B S hS :=
  D.baseChangeAlong X''.property k.hom

/-- **The base-change data of Stacks 0AEZ** for a flat morphism of algebraic spaces into the
ambient space, relating the given situation to
`AlgebraicGeometry.Space.FormalGlueingSituation.baseChange`. -/
def flatBaseChange {X'' : AlgebraicSpaces B S hS} (k : X'' ⟶ D.spaceX)
    (hk : IsFlat B S hS k.hom) : FlatBaseChange D (D.baseChange k) :=
  D.flatBaseChangeAlong X''.property k.hom hk

end AlgebraicGeometry.Space.FormalGlueingSituation

end
