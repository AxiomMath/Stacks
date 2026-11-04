module

public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.Deformation.Examples.Geometric.SpecialFibreCartesian

/-!
# The two families of a deformation of a morphism are thickenings of the special fibre

A deformation `Q` of a morphism `f : X ⟶ Y` of schemes over the residue field carries two
identifications of special fibres, `Q.hom.source : X ⟶ Q.left.source` and
`Q.hom.target : Y ⟶ Q.left.target`.  Both are closed immersions and both are surjective on
points — the first two facts are
`Deformation.Examples.specialTarget_isClosedImmersion` and
`Deformation.Examples.specialTarget_surjective` together with their base changes along the
cartesian square of the arrow.  So both are **thickenings** in the sense of
[Stacks, Tag 04EX], and in particular both are homeomorphisms on underlying spaces.

That is the shape in which the remaining halves of [Stacks, Tag 0E3X] need them.  Full-ness
has to produce the target component `Q.left.target ⟶ P.left.target` of an arrow of
deformations out of the source component alone, and essential surjectivity has to produce the
whole target family out of the source family; in both cases the underlying space of the target
family is the underlying space of `Y`, read through
`Stacks.Thickenings.IsThickening.homeomorph`, and the only genuine datum is the structure
sheaf — which is `(Q.left.morphism)_* 𝒪_{Q.left.source}` by
`Deformation.Examples.isIso_unitToPushforwardUnit_of_deformation`, packaged here as an
isomorphism.

## Main definitions

* `Deformation.Examples.structureSheafIsoPushforwardSource` — **the structure sheaf of the
  target family is the direct image of the structure sheaf of the source family**, as an
  isomorphism rather than as the invertibility of a morphism.

## Main results

* `Deformation.Examples.isThickening_specialTarget` and
  `Deformation.Examples.isThickening_specialSource` — the two identifications of special
  fibres are thickenings.
* `Deformation.Examples.isHomeomorph_specialTarget` and
  `Deformation.Examples.isHomeomorph_specialSource` — hence homeomorphisms on underlying
  spaces.
* `Deformation.Examples.isIso_unitToPushforwardObjUnit_of_isIso_unitToPushforwardUnit` — the
  two spellings of the hypothesis `f_* 𝒪_X = 𝒪_Y` agree.

## Implementation notes

Surjectivity of the identification of the special fibre of the *source* family is obtained the
same way its closed-immersion property is, in
`Deformation.Examples.isIso_unitToPushforwardUnit_of_deformation`: the cartesian square
`Deformation.Examples.SchemeMorphismFamily.Hom.source_pullback` of the arrow to the special
fibre exhibits it as a base change of the identification of the special fibre of the target
family, and both properties are stable under base change.

The hypothesis `f_* 𝒪_X = 𝒪_Y` of the tag has two spellings in the library:
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit f` being invertible in
`AlgebraicGeometry.Scheme.Modules`, which is the form the filtration argument of
`StacksFrontier/AlgebraicGeometry/BaseAdicFiltration/` proves and consumes, and
`SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom` being invertible in
`SheafOfModules`, which is Mathlib's spelling and the one the statement of the tag is phrased
in.  The morphism is the same term and the two `Category` instances have the same identities
and composition — `AlgebraicGeometry.Scheme.Modules.instCategory` takes them from the
`SheafOfModules` instance and only respells the `Hom` type — so the two propositions are
definitionally equal; they are not *reducibly* equal, which is why the bridge is a `theorem`
with a declared type and not a `rfl` a caller can supply inline.

## References

* [Stacks Project, Tag 0E3X](https://stacks.math.columbia.edu/tag/0E3X)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

/-- **The two spellings of the hypothesis `f_* 𝒪_X = 𝒪_Y` agree.**  The morphism
`AlgebraicGeometry.Scheme.Modules.unitToPushforwardUnit g` *is*
`SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom`, and
`AlgebraicGeometry.Scheme.Modules` is the category of sheaves of modules over the structure
sheaf with its identities and composition; so invertibility in either category is
invertibility in the other. -/
theorem isIso_unitToPushforwardObjUnit_of_isIso_unitToPushforwardUnit {W Z : Scheme.{u}}
    (g : W ⟶ Z) :
    IsIso (C := Z.Modules) (Scheme.Modules.unitToPushforwardUnit g) ↔
      IsIso (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) :=
  Iff.rfl

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- **The identification of the special fibre of the target family is a thickening.**  It is a
closed immersion, being a base change of the closed point of the spectrum of the base, and it
is surjective on points, the spectrum of an Artinian local ring being a single point. -/
theorem isThickening_specialTarget (Q : schemeMorphismDeformationCategory f pX pY hf) :
    Stacks.Thickenings.IsThickening Q.hom.target :=
  ⟨specialTarget_isClosedImmersion f pX pY hf Q, specialTarget_surjective f pX pY hf Q⟩

/-- **The identification of the special fibre of the source family is a thickening.**  The
cartesian square of the arrow to the special fibre exhibits it as a base change of the
identification of the special fibre of the target family, and both halves of being a
thickening are stable under base change. -/
theorem isThickening_specialSource (Q : schemeMorphismDeformationCategory f pX pY hf) :
    Stacks.Thickenings.IsThickening Q.hom.source :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
      Q.hom.source_pullback (specialTarget_isClosedImmersion f pX pY hf Q),
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      Q.hom.source_pullback ⟨specialTarget_surjective f pX pY hf Q⟩).surj⟩

/-- **The target family of a deformation has the underlying space of `Y`.** -/
theorem isHomeomorph_specialTarget (Q : schemeMorphismDeformationCategory f pX pY hf) :
    IsHomeomorph Q.hom.target.base :=
  (isThickening_specialTarget f pX pY hf Q).isHomeomorph

/-- **The source family of a deformation has the underlying space of `X`.** -/
theorem isHomeomorph_specialSource (Q : schemeMorphismDeformationCategory f pX pY hf) :
    IsHomeomorph Q.hom.source.base :=
  (isThickening_specialSource f pX pY hf Q).isHomeomorph

/-- **The structure sheaf of the target family is the direct image of the structure sheaf of
the source family.**  This is
`Deformation.Examples.isIso_unitToPushforwardUnit_of_deformation` read as an isomorphism: for
every deformation of `f`, under the tag's two hypotheses on `f`, the comparison
`𝒪_{Q.target} ⟶ (Q.morphism)_* 𝒪_{Q.source}` is invertible.

Together with `Deformation.Examples.isHomeomorph_specialTarget` this is all the data the
target family carries: its space is the space of `Y` and its structure sheaf is determined by
the source family. -/
def structureSheafIsoPushforwardSource
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (Q : schemeMorphismDeformationCategory f pX pY hf) :
    Scheme.unitModule Q.left.target ≅
      (Scheme.Modules.pushforward Q.left.morphism).obj (Scheme.unitModule Q.left.source) :=
  haveI := isIso_unitToPushforwardUnit_of_deformation f pX pY hf h0 hR Q
  asIso (C := Q.left.target.Modules) (Scheme.Modules.unitToPushforwardUnit Q.left.morphism)

/-- The isomorphism `structureSheafIsoPushforwardSource` is the comparison map
`𝒪_{Q.target} ⟶ (Q.morphism)_* 𝒪_{Q.source}`. -/
@[simp]
theorem structureSheafIsoPushforwardSource_hom
    (h0 : IsIso (C := Y.Modules) (Scheme.Modules.unitToPushforwardUnit f))
    (hR : IsZero (((Scheme.Modules.pushforward f).rightDerived 1).obj
      (SheafOfModules.unit X.ringCatSheaf)))
    (Q : schemeMorphismDeformationCategory f pX pY hf) :
    (structureSheafIsoPushforwardSource f pX pY hf h0 hR Q).hom =
      Scheme.Modules.unitToPushforwardUnit Q.left.morphism :=
  rfl

end Deformation.Examples

end
