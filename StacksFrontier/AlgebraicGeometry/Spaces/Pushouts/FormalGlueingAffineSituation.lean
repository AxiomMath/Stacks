module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRangeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimageIsoCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent

/-!
# The affine formal glueing situation

The proof of Stacks 0AF0 begins with the special case in which `X = Spec(R)` and `Y = Spec(S)`
are affine schemes, `f : Y ⟶ X` comes from a flat ring map `R → S`, and `Z ⊆ X` is cut out by a
finitely generated ideal `I ⊆ R` with `R/I ≅ S/IS`. This file builds that instance of the
standing Situation 0AEV, `AlgebraicGeometry.Space.FormalGlueingSituation`, out of objects of the
big fppf site.

Concretely, let `φ : V ⟶ U` and `ι : W ⟶ U` be morphisms of the big fppf site over `S` with
`U` and `V` affine, `φ` flat and `ι` a closed immersion of finite presentation, and suppose
that some fibre product of `ι` along `φ` has invertible first projection to `W` (in the ring
picture: `R/I → S/IS` is an isomorphism). Then `X := yoneda.obj U`, `Y := yoneda.obj V`,
`f := yoneda.map φ` and `Z := Subfunctor.range (yoneda.map ι)` form a formal glueing situation.

## Main definitions

* `AlgebraicGeometry.Space.affineFormalGlueingSituation`: the formal glueing situation
  attached to the data above.

## Implementation notes

Every field is discharged from a lemma about represented morphisms: the closed-part
hypotheses are `AlgebraicGeometry.Space.isClosedSubspace_range_yoneda_map` and
`AlgebraicGeometry.Space.isFinitePresentation_ι_range_yoneda_map`, quasi-compactness and
quasi-separatedness of `f` come from the underlying morphism of affine schemes, and flatness
at the points of `f⁻¹(Z)` is flatness of `f` everywhere (`isFlat_iff_forall_isFlatAt`).
For the isomorphism over `Z`, the Yoneda image of the given cartesian square is a cartesian
square over `yoneda.map ι`; composing its first projection with the isomorphism of
`yoneda.obj W` onto the range turns it into a cartesian square over the inclusion of `Z`, to
which `CategoryTheory.Subfunctor.isIso_fromPreimage_of_isIso_of_isPullback` applies.

## References

* [Stacks Project, Tag 0AEV](https://stacks.math.columbia.edu/tag/0AEV)
* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The represented closed immersion `yoneda.map ι` is a monomorphism of presheaves. -/
theorem mono_yoneda_map_of_isClosedImmersion {W U : BigFppfOver B S hS} (ι : W ⟶ U)
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι)) :
    Mono (yoneda.map ι) :=
  mono_of_isClosedImmersion B S hS _
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) ι).2 hι)

/-- **The isomorphism over the closed part in the affine situation.** If some fibre product of
the represented closed immersion `ι` along `φ` has invertible first projection, then the
projection from the inverse image of `Subfunctor.range (yoneda.map ι)` along `yoneda.map φ`
onto that range is an isomorphism. -/
theorem isIso_fromPreimage_range_yoneda_map {U V W W' : BigFppfOver B S hS} (φ : V ⟶ U)
    (ι : W ⟶ U)
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    {q : W' ⟶ W} {g : W' ⟶ V} (hsq : IsPullback q g ι φ) [IsIso q] :
    IsIso ((Subfunctor.range (yoneda.map ι)).fromPreimage (yoneda.map φ)) := by
  have := mono_yoneda_map_of_isClosedImmersion ι hι
  have hY : IsPullback (yoneda.map q) (yoneda.map g) (yoneda.map ι) (yoneda.map φ) :=
    hsq.map yoneda
  have hsq' : IsPullback (yoneda.map q ≫ Subfunctor.toRange (yoneda.map ι)) (yoneda.map g)
      (Subfunctor.range (yoneda.map ι)).ι (yoneda.map φ) :=
    IsPullback.of_iso hY (Iso.refl _) (asIso (Subfunctor.toRange (yoneda.map ι)))
      (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact Subfunctor.isIso_fromPreimage_of_isIso_of_isPullback _ _ hsq'

/-- **The affine instance of Stacks Situation 0AEV**, the setting of the first paragraph of the
proof of Stacks 0AF0: `X = yoneda.obj U` and `Y = yoneda.obj V` for affine schemes `U`, `V` of
the big fppf site, `f = yoneda.map φ` for a flat `φ : V ⟶ U`, and `Z` the range of a closed
immersion of finite presentation `ι : W ⟶ U` such that some fibre product of `ι` along `φ` has
invertible first projection (in the ring picture `R/I ≅ S/IS`). -/
noncomputable def affineFormalGlueingSituation {U V W W' : BigFppfOver B S hS} (φ : V ⟶ U)
    (ι : W ⟶ U)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (hφ : Flat ((BigFppfOver.toScheme B S hS).map φ))
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hιfp : AlgebraicGeometry.FinitePresentation ((BigFppfOver.toScheme B S hS).map ι))
    {q : W' ⟶ W} {g : W' ⟶ V} (hsq : IsPullback q g ι φ) [IsIso q] :
    FormalGlueingSituation B S hS where
  X := yoneda.obj U
  Y := yoneda.obj V
  algebraicSpace_X := isAlgebraicSpace_yoneda B S hS U
  algebraicSpace_Y := isAlgebraicSpace_yoneda B S hS V
  f := yoneda.map φ
  quasiCompact_f := isQuasiCompact_yoneda_map_of_quasiCompact B S hS φ inferInstance
  quasiSeparated_f := (isQuasiSeparated_yoneda_map_iff B S hS φ).2 inferInstance
  Z := Subfunctor.range (yoneda.map ι)
  closed_Z := isClosedSubspace_range_yoneda_map B S hS ι hι
  finitePresentation_Z := isFinitePresentation_ι_range_yoneda_map B S hS ι hι hιfp
  iso_over_Z := isIso_fromPreimage_range_yoneda_map φ ι hι hsq
  flat_at_preimage_Z _ :=
    (isFlat_iff_forall_isFlatAt B S hS (yoneda.map φ)).1 (isFlat_yoneda_map B S hS φ hφ) _

section

variable {U V W W' : BigFppfOver B S hS} (φ : V ⟶ U) (ι : W ⟶ U)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    (hφ : Flat ((BigFppfOver.toScheme B S hS).map φ))
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hιfp : AlgebraicGeometry.FinitePresentation ((BigFppfOver.toScheme B S hS).map ι))
    {q : W' ⟶ W} {g : W' ⟶ V} (hsq : IsPullback q g ι φ) [IsIso q]

/-- The space `X` of `affineFormalGlueingSituation φ ι hφ hι hιfp hsq` is `yoneda.obj U`. -/
@[simp]
theorem affineFormalGlueingSituation_X :
    (affineFormalGlueingSituation φ ι hφ hι hιfp hsq).X = yoneda.obj U :=
  rfl

/-- The space `Y` of `affineFormalGlueingSituation φ ι hφ hι hιfp hsq` is `yoneda.obj V`. -/
@[simp]
theorem affineFormalGlueingSituation_Y :
    (affineFormalGlueingSituation φ ι hφ hι hιfp hsq).Y = yoneda.obj V :=
  rfl

/-- The morphism `f` of `affineFormalGlueingSituation φ ι hφ hι hιfp hsq` is `yoneda.map φ`. -/
@[simp]
theorem affineFormalGlueingSituation_f :
    (affineFormalGlueingSituation φ ι hφ hι hιfp hsq).f = yoneda.map φ :=
  rfl

/-- The closed subspace `Z` of `affineFormalGlueingSituation φ ι hφ hι hιfp hsq` is
`Subfunctor.range (yoneda.map ι)`. -/
@[simp]
theorem affineFormalGlueingSituation_Z :
    (affineFormalGlueingSituation φ ι hφ hι hιfp hsq).Z = Subfunctor.range (yoneda.map ι) :=
  rfl

end

end AlgebraicGeometry.Space

end
