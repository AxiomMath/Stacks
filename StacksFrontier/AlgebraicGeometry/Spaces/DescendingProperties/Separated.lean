module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# Separatedness of an algebraic space through an étale chart and along a limit

An algebraic space over `S` is separated over `S` exactly when, for one surjective étale
chart `U ⟶ F`, the morphism of schemes `U ×_F U ⟶ U ×_S U` carrying the two projections of
the kernel pair is a closed immersion. Along a directed inverse system of algebraic spaces
with affine transition morphisms, separatedness of one stage therefore propagates to every
later stage.

## Main results

* `AlgebraicGeometry.Space.isSeparated_of_isAffineHom`: an affine morphism of algebraic
  spaces is separated.
* `AlgebraicGeometry.Space.isSeparatedOver_iff_isClosedImmersion_kernelPairToProd`: the
  criterion for separatedness over `S` in terms of the kernel pair of a surjective étale
  chart.
* `AlgebraicGeometry.Space.isAbsolutelySeparated_of_le`: separatedness of a stage of a
  descent situation propagates to all later stages.

## Implementation notes

The criterion is stated over an arbitrary base `S` of the ambient site, so the absolute
notion of Stacks 03BS is the case of the terminal scheme; the product `U ×_S U` appearing
in it is the binary product of the site over `S`, which for the terminal scheme is the
absolute product of the source.

Both directions go through the cartesian square of `AlgebraicGeometry.Space.kernelPairToProd`
identifying the kernel pair of a chart with the fibre product of the diagonal and the induced
chart of `F ⨯ F`: the forward direction is base change along it, and the backward direction is
fppf locality on the target, which closed immersions satisfy because they satisfy it for the
coarser fpqc precoverage.

The standing situation of Stacks 084R is taken to be `AlgebraicGeometry.Space.DescentSituation`
rather than `AlgebraicGeometry.Space.LimitSituation`, since the index type of the former is a
parameter and so may be chosen in a universe independent of the universe of the site.

## References

* [Stacks Project, Tag 02X5](https://stacks.math.columbia.edu/tag/02X5)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Affine morphisms are separated -/

/-- An affine morphism of algebraic spaces over `S` is separated: each of its represented
base changes is an affine, hence separated, morphism of schemes. -/
theorem isSeparated_of_isAffineHom {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsAffineHom B S hS f) : IsSeparated B S hS f := by
  obtain ⟨hrep, haff⟩ :=
    ((isAffineHom_tfae_of_isAlgebraicSpace B S hS f hX hY).out 2 1).mp hf
  refine (isSeparated_iff_presheaf B S hS f hX hY hrep).2 ?_
  refine MorphismProperty.relative_monotone (fun V W g hg => ?_) f haff
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map g) := hg
  exact _root_.AlgebraicGeometry.IsSeparated.of_isAffineHom _

/-! ### Separatedness through the kernel pair of a chart -/

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If an algebraic space over `S` is separated over `S`, then the morphism of schemes
`U ×_F U ⟶ U ×_S U` attached to the kernel pair of any chart `U ⟶ F` is a closed
immersion. -/
theorem isClosedImmersion_kernelPairToProd_of_isSeparatedOver
    (hsep : IsSeparatedOver B S hS F) {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F}
    (hq : yoneda.relativelyRepresentable q) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (kernelPairToProd B S hS hq)) := by
  have hker : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map (kernelPairToProd B S hS hq)) :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).of_isPullback
      (isPullback_kernelPairToProd B S hS hq) hsep
  exact MorphismProperty.of_relative_map
    (P := MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda) hker

/-- An algebraic space over `S` is separated over `S` as soon as the morphism of schemes
`U ×_F U ⟶ U ×_S U` attached to the kernel pair of one surjective étale chart `U ⟶ F` is a
closed immersion. -/
theorem isSeparatedOver_of_isClosedImmersion_kernelPairToProd
    (hF : IsAlgebraicSpace B S hS F) {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F}
    (hqSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hR : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map
        (kernelPairToProd B S hS (hF.diagonal_representable.of_diag q)))) :
    IsSeparatedOver B S hS F := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange
  have : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact presheaf_diag_of_kernelPair B S hS _ hF.diagonal_representable
    ((hF.diagonal_representable.of_diag q).isPullback' q) hqSurj hqEtale hR

/-- **Separatedness through a chart.** An algebraic space over `S` is separated over `S`
exactly when the morphism of schemes `U ×_F U ⟶ U ×_S U` attached to the kernel pair of a
surjective étale chart `U ⟶ F` is a closed immersion. -/
theorem isSeparatedOver_iff_isClosedImmersion_kernelPairToProd
    (hF : IsAlgebraicSpace B S hS F) {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F}
    (hqSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q) :
    IsSeparatedOver B S hS F ↔
      _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map
          (kernelPairToProd B S hS (hF.diagonal_representable.of_diag q))) :=
  ⟨fun hsep => isClosedImmersion_kernelPairToProd_of_isSeparatedOver B S hS hsep _,
    isSeparatedOver_of_isClosedImmersion_kernelPairToProd B S hS hF hqSurj hqEtale⟩

/-! ### Propagation along the transition morphisms of a descent situation -/

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Separatedness propagates to later stages.** In the standing situation of Stacks 084R,
if one stage of the inverse system is separated then so is every later stage, because the
transition morphisms are affine and hence separated. -/
theorem isAbsolutelySeparated_of_le {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) {j i : I} (hji : j ≤ i)
    (hj : IsAbsolutelySeparated B S hS hZ (D.system.obj (op j))) :
    IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) :=
  isAbsolutelySeparated_of_isSeparated B S hS hZ hj
    (isSeparated_of_isAffineHom B S hS (D.system.map (homOfLE hji).op)
      (D.algebraicSpace i) (D.algebraicSpace j) (D.transition_affine (homOfLE hji).op))

end AlgebraicGeometry.Space

end
