module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.EtaleLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SyntomicLocalAtSource
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Etale
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Smooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Syntomic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.DeformationChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Syntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria

/-!
# Properties of morphisms invariant under a flat deformation of algebraic spaces

Let `X ⊂ X'`, `Y ⊂ Y'` and `B ⊂ B'` be thickenings of algebraic spaces over a scheme `S`,
let `f : X ⟶ Y` and `f' : X' ⟶ Y'` be a morphism of the first two thickenings over the
third, and assume that `X'` is flat and locally of finite presentation over `B'`, that `Y'`
is locally of finite type over `B'`, and that `X` and `Y` are the special fibres of `X'` and
`Y'` over `B`. This is `AlgebraicGeometry.Space.FlatDeformationDiagram`. Each of a list of
properties of morphisms then holds for `f` exactly when it holds for `f'`.

This file records nine entries of that list. Six of them — flatness, local quasi-finiteness,
syntomicity, smoothness, unramifiedness and étaleness — are properties which are étale local on
the source and target, and each is deduced from the corresponding statement for flat deformations
of *schemes* — `Stacks.Thickenings.FlatDeformationDiagram.flat_iff` and its five companions — by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_scheme_diagrams`, which transports an
étale-local property of morphisms of schemes from the compatible scheme charts of a flat
deformation diagram of algebraic spaces to the diagram itself.

The seventh, surjectivity, is not étale local on the source: it is a condition on the map of
point sets, and both thickenings of the diagram are bijections there, so the two horizontal
morphisms have the same answer. No hypothesis of the diagram beyond the two thickenings is used.

The last two, universal injectivity and being an isomorphism, reduce to the previous ones: the
first to surjectivity of the relative diagonal, the second to the conjunction of étaleness,
universal injectivity and surjectivity.

## Main results

* `AlgebraicGeometry.Space.isFlat_iff_of_flatDeformationDiagram`: **Stacks 0CGX**, part (2).
* `AlgebraicGeometry.Space.isSurjective_iff_of_flatDeformationDiagram`: **Stacks 0CGX**,
  part (9).
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_of_flatDeformationDiagram`:
  **Stacks 0CGX**, part (12).
* `AlgebraicGeometry.Space.isSyntomic_iff_of_flatDeformationDiagram`: **Stacks 0CGX**,
  part (15).
* `AlgebraicGeometry.Space.isSmooth_iff_of_flatDeformationDiagram`: **Stacks 0CGX**, part (16).
* `AlgebraicGeometry.Space.isUnramified_iff_isUnramified_deformation`: **Stacks 0CGX**,
  part (17).
* `AlgebraicGeometry.Space.isEtale_iff_of_flatDeformationDiagram`: **Stacks 0CGX**, part (18).
* `AlgebraicGeometry.Space.universallyInjective_iff_of_flatDeformationDiagram`:
  **Stacks 0CGX**, part (10).
* `AlgebraicGeometry.Space.isIso_iff_of_flatDeformationDiagram`: **Stacks 0CGX**, part (3).

## Implementation notes

Five of the six properties of morphisms of algebraic spaces used here are defined by the chart
condition `AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Tag 03MJ applied to the
corresponding property of morphisms of schemes, so for them the transport lemma applies
directly. Étaleness is instead Tag 03FR, the condition that composing with an étale morphism
from a representable presheaf stays étale; it agrees with the chart condition by Tag 03XT,
`AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`, which is what the étale statement
below inserts on both sides.

The transport lemma asks for the scheme-level property to be étale local on source and target.
For each of the six properties that is available unconditionally
(`AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget` and its companions, Tag 04R3), the
syntomic one being `AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget`, so all six
statements are unconditional and carry the tag.

The conjunction of local finite type and local quasi-finiteness, rather than local
quasi-finiteness alone, appears for local quasi-finiteness because that is how
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` is defined: a morphism of algebraic spaces is
locally quasi-finite when the morphism in every commuting square of étale scheme charts is both
locally of finite type and locally quasi-finite, the finite-type clause being part of the
definition of local quasi-finiteness for algebraic spaces.

The two thickenings of the diagram are recorded as monomorphisms whose ranges are thickenings of
the ambient spaces, rather than as inclusions of subfunctors, so the surjectivity clause of
Tag 09ZY cannot be instantiated at them directly. The missing step is that such a monomorphism
is a bijection on points, which is `AlgebraicGeometry.Space.pointsMap_injective_of_mono` of
Tag 06RV together with the surjectivity of the inclusion of its range cancelled against the
isomorphism onto that range; it is supplied below.

Universal injectivity is neither étale local on the source nor a condition on the two point
sets alone, so neither of the two arguments above applies to it. It is instead read on the
relative diagonal: a morphism of algebraic spaces is universally injective exactly when its
relative diagonal is surjective on points, which is Tag 040X. The source of the relative
diagonal of `f` is the base change along `X ⟶ X'` of the source of the relative diagonal of
`f'`, because `X = Y ×_{Y'} X'`; the comparison morphism between the two is therefore a
monomorphism and surjective on points, so the surjectivity argument used for Tag 09ZY applies
to the square formed by the two relative diagonals.

Being an isomorphism is the conjunction of étaleness, universal injectivity and surjectivity,
by Tag 05W5 for the one direction and because an isomorphism has all three properties for the
other, so part (3) is the conjunction of parts (18), (10) and (9); the converse direction is
pure base change, the restricted morphism being a base change of the ambient one.

## References

* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
* [Stacks Project, Tag 06RV](https://stacks.math.columbia.edu/tag/06RV)
* [Stacks Project, Tag 09ZY](https://stacks.math.columbia.edu/tag/09ZY)
* [Stacks Project, Tag 0CF4](https://stacks.math.columbia.edu/tag/0CF4)
* [Stacks Project, Tag 0CGX](https://stacks.math.columbia.edu/tag/0CGX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CGX, part (2).** Flatness of a morphism of algebraic spaces is invariant under a
flat deformation. -/
@[stacks 0CGX "part (2): flat"]
theorem isFlat_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsFlat B S hS D.f.hom ↔ IsFlat B S hS D.f'.hom :=
  holdsOnEveryEtaleChart_iff_of_scheme_diagrams B S hS D _ Flat.isEtaleLocalOnSourceAndTarget
    fun E => E.flat_iff

/-- A morphism of presheaves on the big fppf site of `S` which is invertible is surjective on
points. -/
private theorem isSurjective_of_isIso_presheaf {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) [IsIso f] : IsSurjective B S hS f := fun y ↦
  ⟨pointsMap B S hS G (inv f) y, by
    rw [← pointsMap_comp_apply, IsIso.inv_hom_id, pointsMap_id, id_eq]⟩

/-- A monomorphism of algebraic spaces whose range is a thickening of its target is a bijection
on points: it is injective by Tag 06RV, and it is surjective as the composite of the isomorphism
onto its range with the inclusion of the range. -/
private theorem bijective_pointsMap_of_isThickening_range {X X' : AlgebraicSpaces B S hS}
    (i : X ⟶ X') [Mono i.hom]
    (hi : IsThickening B S hS X' (Subfunctor.range i.hom)) :
    Function.Bijective (pointsMap B S hS X.1 i.hom) := by
  refine ⟨pointsMap_injective_of_mono B S hS i.hom, ?_⟩
  rw [← Subfunctor.toRange_ι i.hom, pointsMap_comp]
  exact hi.2.comp (isSurjective_of_isIso_presheaf B S hS _)

/-- Surjectivity on points passes across a commutative square of presheaves on the big fppf
site of `S` whose two vertical morphisms are bijective on points. -/
private theorem isSurjective_iff_of_bijective_pointsMap_square
    {P P' Q Q' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {i : P ⟶ P'} {j : Q ⟶ Q'}
    {u : P ⟶ Q} {u' : P' ⟶ Q'}
    (hi : Function.Bijective (pointsMap B S hS P i))
    (hj : Function.Bijective (pointsMap B S hS Q j))
    (hcomm : i ≫ u' = u ≫ j) :
    IsSurjective B S hS u ↔ IsSurjective B S hS u' := by
  calc
    IsSurjective B S hS u ↔
        Function.Surjective (pointsMap B S hS Q j ∘ pointsMap B S hS P u) :=
      (Function.Surjective.of_comp_iff' hj _).symm
    _ ↔ Function.Surjective (pointsMap B S hS P' u' ∘ pointsMap B S hS P i) := by
      rw [← pointsMap_comp, ← pointsMap_comp, hcomm]
    _ ↔ IsSurjective B S hS u' := Function.Surjective.of_comp_iff _ hi.2

/-- **Stacks 0CGX, part (9).** Surjectivity of a morphism of algebraic spaces is invariant under
a flat deformation. -/
@[stacks 0CGX "part (9): surjective"]
theorem isSurjective_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsSurjective B S hS D.f.hom ↔ IsSurjective B S hS D.f'.hom := by
  have := D.iX_mono
  have := D.iY_mono
  exact isSurjective_iff_of_bijective_pointsMap_square B S hS
    (bijective_pointsMap_of_isThickening_range B S hS D.iX D.iX_thickening)
    (bijective_pointsMap_of_isThickening_range B S hS D.iY D.iY_thickening)
    (congrArg (fun k ↦ k.hom) D.comm_f)

/-- **Stacks 0CGX, part (12).** Local quasi-finiteness of a morphism of algebraic spaces is
invariant under a flat deformation. -/
@[stacks 0CGX "part (12): locally quasi-finite"]
theorem isLocallyQuasiFinite_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsLocallyQuasiFinite B S hS D.f.hom ↔ IsLocallyQuasiFinite B S hS D.f'.hom :=
  holdsOnEveryEtaleChart_iff_of_scheme_diagrams B S hS D _
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    fun E => E.locallyQuasiFinite_conditions_iff

/-- **Stacks 0CGX, part (15).** Syntomicity of a morphism of algebraic spaces is invariant under
a flat deformation. -/
@[stacks 0CGX "part (15): syntomic"]
theorem isSyntomic_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsSyntomic B S hS D.f.hom ↔ IsSyntomic B S hS D.f'.hom :=
  holdsOnEveryEtaleChart_iff_of_scheme_diagrams B S hS D _
    syntomic_isEtaleLocalOnSourceAndTarget fun E => E.syntomic_iff

/-- **Stacks 0CGX, part (16).** Smoothness of a morphism of algebraic spaces is invariant under a
flat deformation. -/
@[stacks 0CGX "part (16): smooth"]
theorem isSmooth_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsSmooth B S hS D.f.hom ↔ IsSmooth B S hS D.f'.hom :=
  holdsOnEveryEtaleChart_iff_of_scheme_diagrams B S hS D _ Smooth.isEtaleLocalOnSourceAndTarget
    fun E => E.smooth_iff

/-- **Stacks 0CGX, part (17).** Unramifiedness of a morphism of algebraic spaces is invariant
under a flat deformation. -/
@[stacks 0CGX "part (17): unramified"]
theorem isUnramified_iff_isUnramified_deformation (D : FlatDeformationDiagram B S hS) :
    IsUnramified B S hS D.f.hom ↔ IsUnramified B S hS D.f'.hom :=
  holdsOnEveryEtaleChart_iff_of_scheme_diagrams B S hS D _
    unramified_isEtaleLocalOnSourceAndTarget fun E => E.unramified_iff

/-- **Stacks 0CGX, part (18).** Étaleness of a morphism of algebraic spaces is invariant under a
flat deformation. -/
@[stacks 0CGX "part (18): étale"]
theorem isEtale_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsEtale B S hS D.f.hom ↔ IsEtale B S hS D.f'.hom :=
  (isEtale_iff_holdsOnEveryEtaleChart B S hS D.X.property D.Y.property D.f.hom).trans
    ((holdsOnEveryEtaleChart_iff_of_scheme_diagrams B S hS D _
        etale_isEtaleLocalOnSourceAndTarget fun E => E.etale_iff).trans
      (isEtale_iff_holdsOnEveryEtaleChart B S hS D.X'.property D.Y'.property D.f'.hom).symm)

/-! ### Universal injectivity and isomorphy -/

/-- A base change of a morphism of presheaves on the big fppf site of `S` which is surjective
on points is surjective on points. -/
private theorem isSurjective_of_isPullback_of_presheaf
    {W Z F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : W ⟶ Z} {q : W ⟶ F} {g : Z ⟶ G} {f : F ⟶ G}
    (sq : IsPullback p q g f) (hg : IsSurjective B S hS g) :
    IsSurjective B S hS q := by
  intro x
  obtain ⟨z, hz⟩ := hg (pointsMap B S hS F f x)
  obtain ⟨w, -, hwq⟩ := exists_point_of_isPullback_presheaf B S hS sq z x hz
  exact ⟨w, hwq⟩

/-- The comparison morphism `X ×_Y X ⟶ X' ×_{Y'} X'` between the sources of the two relative
diagonals of a flat deformation diagram. -/
private noncomputable def diagonalComparison (D : FlatDeformationDiagram B S hS) :
    pullback D.f.hom D.f.hom ⟶ pullback D.f'.hom D.f'.hom :=
  pullback.lift (pullback.fst D.f.hom D.f.hom ≫ D.iX.hom)
    (pullback.snd D.f.hom D.f.hom ≫ D.iX.hom)
    (by
      have h : D.iX.hom ≫ D.f'.hom = D.f.hom ≫ D.iY.hom := congrArg (fun k ↦ k.hom) D.comm_f
      rw [Category.assoc, Category.assoc, h, pullback.condition_assoc])

private theorem diagonalComparison_fst (D : FlatDeformationDiagram B S hS) :
    diagonalComparison B S hS D ≫ pullback.fst D.f'.hom D.f'.hom =
      pullback.fst D.f.hom D.f.hom ≫ D.iX.hom :=
  pullback.lift_fst _ _ _

private theorem diagonalComparison_snd (D : FlatDeformationDiagram B S hS) :
    diagonalComparison B S hS D ≫ pullback.snd D.f'.hom D.f'.hom =
      pullback.snd D.f.hom D.f.hom ≫ D.iX.hom :=
  pullback.lift_snd _ _ _

/-- The square formed by the two relative diagonals and the two source inclusions commutes. -/
private theorem diagonalComparison_comm (D : FlatDeformationDiagram B S hS) :
    D.iX.hom ≫ pullback.diagonal D.f'.hom =
      pullback.diagonal D.f.hom ≫ diagonalComparison B S hS D :=
  pullback.hom_ext (by simp [diagonalComparison_fst]) (by simp [diagonalComparison_snd])

/-- The restricted morphism of a flat deformation diagram is a base change of the ambient
one along the thickening of the target. -/
private theorem isPullback_f_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsPullback D.iX.hom D.f.hom D.f'.hom D.iY.hom :=
  AlgebraicSpaces.isPullback_hom B S hS (D.isPullback_X.of_bot D.comm_f D.isPullback_Y)

/-- `X ×_Y X` is the base change of `X' ×_{Y'} X'` along the thickening of the source: the
rectangle obtained by pasting the defining square of `X ×_Y X` onto the cartesian square of the
two horizontal morphisms is the rectangle obtained by pasting the comparison square onto the
defining square of `X' ×_{Y'} X'`, and the latter is cartesian. -/
private theorem isPullback_diagonalComparison (D : FlatDeformationDiagram B S hS) :
    IsPullback (diagonalComparison B S hS D) (pullback.fst D.f.hom D.f.hom)
      (pullback.fst D.f'.hom D.f'.hom) D.iX.hom := by
  have hcross : D.iX.hom ≫ D.f'.hom = D.f.hom ≫ D.iY.hom := congrArg (fun k ↦ k.hom) D.comm_f
  have hbig : IsPullback
      (diagonalComparison B S hS D ≫ pullback.snd D.f'.hom D.f'.hom)
      (pullback.fst D.f.hom D.f.hom) D.f'.hom (D.iX.hom ≫ D.f'.hom) := by
    rw [diagonalComparison_snd, hcross]
    exact (IsPullback.of_hasPullback D.f.hom D.f.hom).flip.paste_horiz
      (isPullback_f_of_flatDeformationDiagram B S hS D)
  exact hbig.of_right (diagonalComparison_fst B S hS D)
    (IsPullback.of_hasPullback D.f'.hom D.f'.hom).flip

private theorem mono_diagonalComparison (D : FlatDeformationDiagram B S hS) :
    Mono (diagonalComparison B S hS D) := by
  have := D.iX_mono
  refine ⟨fun {T} a b hab ↦ pullback.hom_ext ((cancel_mono D.iX.hom).1 ?_)
    ((cancel_mono D.iX.hom).1 ?_)⟩
  · rw [Category.assoc, Category.assoc, ← diagonalComparison_fst, reassoc_of% hab]
  · rw [Category.assoc, Category.assoc, ← diagonalComparison_snd, reassoc_of% hab]

private theorem bijective_pointsMap_diagonalComparison (D : FlatDeformationDiagram B S hS) :
    Function.Bijective (pointsMap B S hS (pullback D.f.hom D.f.hom)
      (diagonalComparison B S hS D)) := by
  have := D.iX_mono
  have := mono_diagonalComparison B S hS D
  exact ⟨pointsMap_injective_of_mono B S hS (diagonalComparison B S hS D),
    isSurjective_of_isPullback_of_presheaf B S hS
      (isPullback_diagonalComparison B S hS D).flip
      (bijective_pointsMap_of_isThickening_range B S hS D.iX D.iX_thickening).2⟩

/-- **Stacks 0CGX, part (10).** Universal injectivity of a morphism of algebraic spaces is
invariant under a flat deformation. -/
@[stacks 0CGX "part (10): universally injective"]
theorem universallyInjective_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    UniversallyInjective B S hS D.f.hom ↔ UniversallyInjective B S hS D.f'.hom := by
  have := D.iX_mono
  refine ⟨fun hf ↦ universallyInjective_of_isSurjective_diagonal B S hS D.f'.hom ?_,
    fun hf' ↦ universallyInjective_of_isPullback B S hS D.X'.property D.Y.property
      D.Y'.property D.f'.hom D.iY.hom hf'
      (isPullback_f_of_flatDeformationDiagram B S hS D).flip⟩
  exact (isSurjective_iff_of_bijective_pointsMap_square B S hS
      (bijective_pointsMap_of_isThickening_range B S hS D.iX D.iX_thickening)
      (bijective_pointsMap_diagonalComparison B S hS D)
      (diagonalComparison_comm B S hS D)).mp
    (isSurjective_diagonal_of_universallyInjective B S hS D.X.property D.f.hom hf)

/-- **Stacks 0CGX, part (3).** Being an isomorphism is invariant under a flat deformation of
algebraic spaces. -/
@[stacks 0CGX "part (3): isomorphism"]
theorem isIso_iff_of_flatDeformationDiagram (D : FlatDeformationDiagram B S hS) :
    IsIso D.f.hom ↔ IsIso D.f'.hom := by
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · exact isIso_of_isEtale_of_universallyInjective_of_isSurjective B S hS D.X'.property
      D.Y'.property D.f'.hom
      ((isEtale_iff_of_flatDeformationDiagram B S hS D).mp (isEtale_of_isIso B S hS D.f.hom))
      ((universallyInjective_iff_of_flatDeformationDiagram B S hS D).mp
        (universallyInjective_of_isIso B S hS D.f.hom))
      ((isSurjective_iff_of_flatDeformationDiagram B S hS D).mp
        (isSurjective_of_isIso_presheaf B S hS D.f.hom))
  · exact (isPullback_f_of_flatDeformationDiagram B S hS D).flip.isIso_fst_of_isIso

end AlgebraicGeometry.Space

end
