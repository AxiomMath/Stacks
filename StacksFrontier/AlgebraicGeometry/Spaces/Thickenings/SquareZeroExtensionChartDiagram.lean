module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SquareZeroQuotientImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings

/-!
# The chart diagram of a square-zero extension of a structure sheaf

Let `0 ⟶ ℐ ⟶ 𝒜 ⟶ 𝒪_X ⟶ 0` be a square-zero extension of the structure sheaf of an algebraic
space `X` over `Y`, in the sense of `AlgebraicGeometry.Space.SquareZeroExtension`.  The proof of
[Stacks Project, Tag 05ZT] builds the realizing thickening out of the affine charts
`U ↦ Spec(𝒜(U))` of the small étale site of `X`.  This file assembles those charts into a
*diagram* — a functor on the small étale site — together with the three natural transformations
the construction uses and the étaleness of the diagram's arrows.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.chartSpec`: **the chart diagram
  `U ↦ Spec(𝒜(U))`**, a functor from the small étale site of `X` to schemes.  It is covariant:
  a morphism `U ⟶ V` of charts restricts sections of `𝒜` from `V` to `U` and therefore maps
  `Spec(𝒜(U)) ⟶ Spec(𝒜(V))`, exactly as the charts themselves do.
* `AlgebraicGeometry.Space.structureSheafChartSpec` and
  `AlgebraicGeometry.Space.inverseImageChartSpec`: the same construction applied to `𝒪_X` and to
  `f^{-1}𝒪_Y`, which are the source and the target of the two comparisons below.
* `AlgebraicGeometry.Space.SquareZeroExtension.reductionChartSpec`: the closed immersion
  `Spec(𝒪_X(U)) ⟶ Spec(𝒜(U))` induced by the reduction `𝒜 ⟶ 𝒪_X`, as a natural
  transformation.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartSpecToBase`: the structure morphism
  `Spec(𝒜(U)) ⟶ Spec((f^{-1}𝒪_Y)(U))` induced by the `f^{-1}𝒪_Y`-algebra structure of `𝒜`, as a
  natural transformation.
* `AlgebraicGeometry.Space.structureSharpChartSpec`: the same for the structure map
  `f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of [Stacks Project, Tag 03G8].
* `AlgebraicGeometry.Space.structureSheafChartSpecIso`: an affine chart is the spectrum of its
  own sections of `𝒪_X`.
* `AlgebraicGeometry.Space.SquareZeroExtension.chartThickeningOfIsAffine`: the resulting morphism
  `U ⟶ Spec(𝒜(U))` from an affine chart into its chart of the extension.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.etale_chartSpec_map_of_isAffine`: **the arrows of
  the chart diagram between affine charts are étale**, with no hypothesis beyond the affineness
  of the two charts.  This is
  `AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isAffine` read through
  `AlgebraicGeometry.HasRingHomProperty.Spec_iff`.
* `Space.SquareZeroExtension.isClosedImmersion_reductionChartSpec_app_of_isAffine`:
  **the reduction is a closed immersion over an affine chart**, because the reduction of a
  square-zero extension is surjective on the sections over an affine chart.
* `AlgebraicGeometry.Space.SquareZeroExtension.isFirstOrderThickening_chartThickening_of_isAffine`:
  **over an affine chart the conclusion of [Stacks Project, Tag 05ZT] holds**: `U ⊂ Spec(𝒜(U))`
  is a first-order thickening of schemes, in the sense of
  `Stacks.Thickenings.IsFirstOrderThickening`.  Its square-zero half,
  `…isFirstOrderThickening_reductionChartSpec_app_of_isAffine`, uses the affineness of the chart
  only for the closed immersion.
* `AlgebraicGeometry.Space.SquareZeroExtension.reductionChartSpec_comp_chartSpecToBase`: **the
  two structure morphisms agree**: the composite
  `Spec(𝒪_X(U)) ⟶ Spec(𝒜(U)) ⟶ Spec((f^{-1}𝒪_Y)(U))` is `Spec(f^♯)`.  This is the field
  `toBase_π` of the datum, carried through `Spec`, and it is the chart-level form of the
  compatibility that [Stacks Project, Tag 05ZT] asks of the realizing thickening.

## Implementation notes

**Why `Functor.rightOp` and not `Functor.leftOp`.**  The extension sheaf is a presheaf
`𝒜 : (X_étale)ᵒᵖ ⥤ CommRingCat`, and `AlgebraicGeometry.Scheme.Spec` is a functor
`CommRingCatᵒᵖ ⥤ Scheme`.  The composite that type-checks is therefore
`𝒜.rightOp ⋙ Scheme.Spec`, since `CategoryTheory.Functor.rightOp` is the variant taking
`Cᵒᵖ ⥤ D` to `C ⥤ Dᵒᵖ`; `CategoryTheory.Functor.leftOp` goes the other way and does not apply.
The two cancelling contravariances leave the diagram covariant on the site, which is what makes
it a diagram of charts *of* the ambient space rather than *over* it.

**The three natural transformations are whiskerings, so their compatibility is free.**  Each of
`reductionChartSpec`, `chartSpecToBase` and `structureSharpChartSpec` is
`CategoryTheory.Functor.whiskerRight` of `CategoryTheory.NatTrans.rightOp` of a map of sheaves of
rings.  Both operations are functorial and `NatTrans.rightOp` reverses composition, so the
compatibility `reductionChartSpec_comp_chartSpecToBase` is the field `toBase_π` transported along
two functors and needs no computation on sections.  Stating it this way — rather than as a
family of equalities of scheme morphisms indexed by the charts — is what makes it usable as the
hypothesis of a descent, where the comparison must be natural.

**The étaleness and the closed immersion are only claimed over affine charts, and that is not a
weakening.**  An object of the small étale site of an algebraic space is an arbitrary étale
scheme over `X`, and `Spec(𝒜(U))` has no reason to be étale over `Spec(𝒜(V))` when the charts
are not affine — the sections of `𝒜` over a non-affine chart do not determine it.  The source
also restricts to affine charts at this step; the affine charts are cofinal in the small étale
site, which is what lets the construction descend.

**No `@[stacks]` attribute.**  Tag 05ZT concludes that the datum is realized by a first-order
thickening `X ⊂ X'` over `Y` with `𝒪_{X'} ≅ 𝒜`.  This file builds the diagram whose colimit is
`X'` in the proof of the source, records that its arrows are étale, and proves the conclusion
*chart by chart*; what is missing is the gluing of the diagram into an ambient algebraic space
and the identification of its structure sheaf.  Nothing in this file claims any part of the tag:
a family of thickenings of the charts is not a thickening of `X`, and no declaration here
quantifies over anything but a single chart.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV), the scheme-level
  statement, where the same diagram is indexed by the affine opens of `X`.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The spectra of the sections of the structure sheaf, as a diagram on the small étale
site**: `U ↦ Spec(𝒪_X(U))`.

Over an affine chart this is the chart itself; over a general chart it is the affine scheme the
chart's global functions define.  It is the source of
`AlgebraicGeometry.Space.SquareZeroExtension.reductionChartSpec`. -/
def structureSheafChartSpec (X : AlgebraicSpaces B S hS) :
    SmallEtale B S hS X.1 ⥤ Scheme.{u} :=
  (smallEtaleRingedTopos B S hS X).O.obj.rightOp ⋙ Scheme.Spec

/-- **The spectra of the sections of `f^{-1}𝒪_Y`, as a diagram on the small étale site of `X`**:
`U ↦ Spec((f^{-1}𝒪_Y)(U))`.

This is the target of the two structure morphisms
`AlgebraicGeometry.Space.SquareZeroExtension.chartSpecToBase` and
`AlgebraicGeometry.Space.structureSharpChartSpec`, which is the form in which "over `Y`" is
available on the charts. -/
def inverseImageChartSpec {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    SmallEtale B S hS X.1 ⥤ Scheme.{u} :=
  (inverseImageStructureCommRingSheaf B S hS f).obj.rightOp ⋙ Scheme.Spec

/-- **The structure map of `f`, read on the chart diagrams**: the natural transformation
`Spec(𝒪_X(U)) ⟶ Spec((f^{-1}𝒪_Y)(U))` induced by the inverse-image form
`f^♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of the structure map of [Stacks Project, Tag 03G8]. -/
def structureSharpChartSpec {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    structureSheafChartSpec B S hS X ⟶ inverseImageChartSpec B S hS f :=
  Functor.whiskerRight
    (NatTrans.rightOp (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom) Scheme.Spec

/-- **An affine chart is the spectrum of its own sections of the structure sheaf.**  The
sections of `𝒪_X` over a chart of the small étale site are by definition the global functions on
the chart's underlying scheme, so when that scheme is affine it is canonically isomorphic to
`Spec(𝒪_X(U))`, which is the chart diagram
`AlgebraicGeometry.Space.structureSheafChartSpec` at `U`.

This is `AlgebraicGeometry.Scheme.isoSpec` with its target read in the chart diagram.  Recording
it as a declaration rather than inlining `isoSpec` is what keeps the two spellings of the target
from diverging: `Spec Γ(U, ⊤)` and `(structureSheafChartSpec B S hS X).obj U` are definitionally
equal but not syntactically so, and `rw` type-checks its result under `implicit` transparency,
where the difference is fatal. -/
def structureSheafChartSpecIso (X : AlgebraicSpaces B S hS) (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    (SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U ≅
      (structureSheafChartSpec B S hS X).obj U :=
  letI := hU
  ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U).isoSpec

/-- The structure map of `f` on the chart diagrams, over a single chart. -/
theorem structureSharpChartSpec_app {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (U : SmallEtale B S hS X.1) :
    (structureSharpChartSpec B S hS f).app U =
      Spec.map ((smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom.app (op U)) :=
  rfl

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **The chart diagram `U ↦ Spec(𝒜(U))` of a square-zero extension of the structure sheaf.**

This is the diagram of affine charts out of which the proof of [Stacks Project, Tag 05ZT] builds
the ambient space of the realizing thickening.  It is covariant on the small étale site: a
morphism `U ⟶ V` of charts restricts sections of `𝒜` from `V` to `U`, and `Spec` turns that
restriction back around into `Spec(𝒜(U)) ⟶ Spec(𝒜(V))`.

Its arrows between affine charts are étale, by
`AlgebraicGeometry.Space.SquareZeroExtension.etale_chartSpec_map_of_isAffine`. -/
def chartSpec : SmallEtale B S hS X.1 ⥤ Scheme.{u} :=
  E.A.obj.rightOp ⋙ Scheme.Spec

/-- The chart diagram over a chart is the spectrum of the sections of `𝒜` there. -/
theorem chartSpec_obj (U : SmallEtale B S hS X.1) :
    (chartSpec B S hS E).obj U = Spec (E.A.obj.obj (op U)) :=
  rfl

/-- The chart diagram on an arrow is `Spec` of the restriction map of `𝒜`. -/
theorem chartSpec_map {U V : SmallEtale B S hS X.1} (h : U ⟶ V) :
    (chartSpec B S hS E).map h = Spec.map (E.A.obj.map h.op) :=
  rfl

/-- **The arrows of the chart diagram between affine charts are étale**, with no hypothesis
beyond the affineness of the two charts.

This is the étaleness asserted in the proof of [Stacks Project, Tag 05ZT]:
`AlgebraicGeometry.Space.SquareZeroExtension.algebraEtale_app_of_isAffine` makes `𝒜(U)` an étale
`𝒜(V)`-algebra, and `AlgebraicGeometry.HasRingHomProperty.Spec_iff` carries that to the morphism
of schemes.  The algebra structure is the one the restriction map of `𝒜` defines, so the
hypothesis `halg` of the algebraic statement holds by
`RingHom.algebraMap_toAlgebra`. -/
theorem etale_chartSpec_map_of_isAffine {U V : SmallEtale B S hS X.1} (h : U ⟶ V)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U)))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V))) :
    Etale ((chartSpec B S hS E).map h) := by
  let : Algebra (E.A.obj.obj (op V)) (E.A.obj.obj (op U)) := (E.A.obj.map h.op).hom.toAlgebra
  have halg : RingHom.Etale (E.A.obj.map h.op).hom :=
    SquareZeroExtension.algebraEtale_app_of_isAffine B S hS E h hU hV
      (RingHom.algebraMap_toAlgebra _)
  show Etale (Spec.map (E.A.obj.map h.op))
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr halg

/-- **The reduction of a square-zero extension, read on the chart diagrams**: the natural
transformation `Spec(𝒪_X(U)) ⟶ Spec(𝒜(U))` induced by `π : 𝒜 ⟶ 𝒪_X`.

Over an affine chart it is a closed immersion, by
`AlgebraicGeometry.Space.SquareZeroExtension.isClosedImmersion_reductionChartSpec_app_of_isAffine`;
it is the chart-level form of the inclusion `X ⊂ X'` of the thickening that
[Stacks Project, Tag 05ZT] produces. -/
def reductionChartSpec : structureSheafChartSpec B S hS X ⟶ chartSpec B S hS E :=
  Functor.whiskerRight (NatTrans.rightOp E.π.hom) Scheme.Spec

/-- The reduction on the chart diagrams, over a single chart. -/
theorem reductionChartSpec_app (U : SmallEtale B S hS X.1) :
    (reductionChartSpec B S hS E).app U = Spec.map (E.π.hom.app (op U)) :=
  rfl

/-- **The reduction is a closed immersion over an affine chart.**  The reduction of a square-zero
extension is surjective on the sections over an affine chart
(`AlgebraicGeometry.Space.SquareZeroExtension.surjective_π_app_of_isAffine`), and the spectrum of
a surjection of rings is a closed immersion. -/
theorem isClosedImmersion_reductionChartSpec_app_of_isAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    _root_.AlgebraicGeometry.IsClosedImmersion ((reductionChartSpec B S hS E).app U) := by
  show _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (E.π.hom.app (op U)))
  exact _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
    (SquareZeroExtension.surjective_π_app_of_isAffine B S hS E U hU)

/-- **Over an affine chart the reduction is a first-order thickening of schemes.**

This is the chart-local form of the conclusion of [Stacks Project, Tag 05ZT]: the closed
immersion `Spec(𝒪_X(U)) ⟶ Spec(𝒜(U))` is defined by an ideal of square zero.  The closed
immersion is
`AlgebraicGeometry.Space.SquareZeroExtension.isClosedImmersion_reductionChartSpec_app_of_isAffine`
and the vanishing of the square of the kernel ideal sheaf is
`AlgebraicGeometry.Space.SquareZeroExtension.ker_pow_two_eq_bot` read through
`AlgebraicGeometry.ker_pow_spec_map_eq_bot_iff`.  Only the closed immersion uses the affineness
of the chart; the square-zero condition holds over every chart. -/
theorem isFirstOrderThickening_reductionChartSpec_app_of_isAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Stacks.Thickenings.IsFirstOrderThickening ((reductionChartSpec B S hS E).app U) := by
  have hker : (Spec.map (E.π.hom.app (op U))).ker ^ 2 = ⊥ :=
    (ker_pow_spec_map_eq_bot_iff (E.π.hom.app (op U)) 2).mpr
      (SquareZeroExtension.ker_pow_two_eq_bot B S hS E (op U))
  exact ⟨isClosedImmersion_reductionChartSpec_app_of_isAffine B S hS E U hU, hker⟩

/-- **An affine chart of `X`, included into its chart of the extension.**  For a chart `U` of
the small étale site of `X` whose underlying scheme is affine, that scheme *is* the spectrum of
its global functions, which are the sections `𝒪_X(U)`; composing the canonical isomorphism with
the reduction gives a morphism `U ⟶ Spec(𝒜(U))`.

This is the arrow [Stacks Project, Tag 05ZT] glues: over each affine chart the ambient space of
the realizing thickening is `Spec(𝒜(U))`, and the thickening restricts to this morphism. -/
def chartThickeningOfIsAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    (SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U ⟶
      (chartSpec B S hS E).obj U :=
  (structureSheafChartSpecIso B S hS X U hU).hom ≫ (reductionChartSpec B S hS E).app U

/-- **Every affine chart of `X` is a first-order thickening inside its chart of the
extension.**  This is the conclusion of [Stacks Project, Tag 05ZT] over a single affine chart:
`U ⊂ Spec(𝒜(U))` is a closed immersion defined by an ideal of square zero.

Precomposing with the isomorphism `U ≅ Spec(𝒪_X(U))` changes neither property: a closed
immersion stays one after an isomorphism, and
`AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso` says the kernel ideal sheaf is unchanged. -/
theorem isFirstOrderThickening_chartThickening_of_isAffine (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U)) :
    Stacks.Thickenings.IsFirstOrderThickening (chartThickeningOfIsAffine B S hS E U hU) := by
  obtain ⟨hclosed, hker⟩ := isFirstOrderThickening_reductionChartSpec_app_of_isAffine B S hS E U hU
  have := hclosed
  refine ⟨?_, ?_⟩
  · show _root_.AlgebraicGeometry.IsClosedImmersion
      ((structureSheafChartSpecIso B S hS X U hU).hom ≫ (reductionChartSpec B S hS E).app U)
    exact _root_.AlgebraicGeometry.IsClosedImmersion.comp _ _
  · show ((structureSheafChartSpecIso B S hS X U hU).hom ≫
      (reductionChartSpec B S hS E).app U).ker ^ 2 = ⊥
    rw [Scheme.Hom.ker_comp_of_isIso]
    exact hker

/-- **The `f^{-1}𝒪_Y`-algebra structure of `𝒜`, read on the chart diagrams**: the natural
transformation `Spec(𝒜(U)) ⟶ Spec((f^{-1}𝒪_Y)(U))` induced by the field `toBase`.

This is the chart-level form of the structure morphism `X' ⟶ Y` of the thickening that
[Stacks Project, Tag 05ZT] produces. -/
def chartSpecToBase : chartSpec B S hS E ⟶ inverseImageChartSpec B S hS f :=
  Functor.whiskerRight (NatTrans.rightOp E.toBase.hom) Scheme.Spec

/-- The structure morphism of the chart diagram, over a single chart. -/
theorem chartSpecToBase_app (U : SmallEtale B S hS X.1) :
    (chartSpecToBase B S hS E).app U = Spec.map (E.toBase.hom.app (op U)) :=
  rfl

/-- **The inclusion of the chart diagram of `𝒪_X` into that of `𝒜` lies over the base**: the
composite `Spec(𝒪_X(U)) ⟶ Spec(𝒜(U)) ⟶ Spec((f^{-1}𝒪_Y)(U))` is `Spec(f^♯)`.

This is the field `toBase_π` of the datum — the statement that `π` is a map of
`f^{-1}𝒪_Y`-algebras — carried through `Spec`, and it is the chart-level form of the
compatibility `X ⟶ X' ⟶ Y = f` that [Stacks Project, Tag 05ZT] asks of the realizing
thickening.  Both sides are whiskerings of `CategoryTheory.NatTrans.rightOp`, which reverses
composition, so the proof is the functoriality of the two operations. -/
theorem reductionChartSpec_comp_chartSpecToBase :
    reductionChartSpec B S hS E ≫ chartSpecToBase B S hS E =
      structureSharpChartSpec B S hS f := by
  have h : E.toBase.hom ≫ E.π.hom =
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage.hom :=
    congrArg (fun α : inverseImageStructureCommRingSheaf B S hS f ⟶
      (smallEtaleRingedTopos B S hS X).O => α.hom) E.toBase_π
  show Functor.whiskerRight (NatTrans.rightOp E.π.hom) Scheme.Spec ≫
      Functor.whiskerRight (NatTrans.rightOp E.toBase.hom) Scheme.Spec = _
  rw [← Functor.whiskerRight_comp, ← NatTrans.rightOp_comp, h]
  rfl

end SquareZeroExtension

end AlgebraicGeometry.Space

end
