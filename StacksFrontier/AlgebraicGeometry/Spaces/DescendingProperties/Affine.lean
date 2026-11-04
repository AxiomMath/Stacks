module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent

/-!
# Affineness of the limit of a directed system of algebraic spaces

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and
quasi-separated algebraic spaces over a scheme `S` with affine transition morphisms, the
standing situation of Stacks 084R carried by `AlgebraicGeometry.Space.DescentSituation`. An
affine algebraic space is separated, so an affine limit is a separated limit, and Stacks 084T
then puts a separated stage at a finite level of the system.

## Main definitions

No new definitions are introduced. Affineness of an algebraic space is
`AlgebraicGeometry.Space.IsAffineSpace`, representability by an object of the big fppf site of
`S` whose underlying scheme is affine, and separatedness is the absolute notion of Stacks 03BS
part (1), `AlgebraicGeometry.Space.IsAbsolutelySeparated`.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelySeparated_of_isAffineSpace`: an affine algebraic space
  is a separated algebraic space.
* `AlgebraicGeometry.Space.DescentSituation`'s
  `exists_isAbsolutelySeparated_system_obj_of_isAffineSpace`: in the situation of Stacks 084R,
  if the limit is affine then some stage is separated.

## Implementation notes

*Affine implies separated.* An affine algebraic space is isomorphic to the presheaf represented
by an object of the site with affine underlying scheme, and an isomorphism is a separated
morphism, so `AlgebraicGeometry.Space.isAbsolutelySeparated_of_isSeparated_to_affine` applies
directly. No algebraicity hypothesis is needed, that lemma imposing none; algebraicity of an
affine presheaf is in any case `AlgebraicGeometry.Space.IsAffineSpace.isAlgebraicSpace`.

*The index set.* The size hypothesis `#I < B.cutoff.ord.cof` is the one Stacks 07SF asks for,
inherited unchanged from
`AlgebraicGeometry.Space.DescentSituation.exists_isAbsolutelySeparated_system_obj`: it is what
keeps the limit of the affine charts of the system inside the site.

*What Stacks 07SQ needs beyond this.* Stacks 07SQ strengthens the conclusion from separatedness
of a stage to affineness of a stage, and the strengthening is not formal: the quotient of an
affine scheme by an étale equivalence relation with affine graph need not be affine, the
projective line over a field being covered by the affine scheme `A^1 ⊔ A^1` étale surjectively
and having affine graph. The source's proof instead presents the étale chart ring-theoretically
over a finite stage, and it consumes
`AlgebraicGeometry.Space.LimitSituation.IsSectionsColimit` for the structure sheaf, that is
Stacks 07SI, the identification `Γ(X, 𝒪_X) = colim_i Γ(X_i, 𝒪_{X_i})` which supplies the ring
`A_i` the stage maps to. That identification is stated in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/SectionsColimitDescent.lean` and is not proved
there or anywhere in this development, so the ring `A_i` is unavailable and the Cartesian
square of Stacks 084U cannot be formed. The remaining ingredients of the source's proof are
present: the system of affine charts with its limiting cone of schemes is
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.schemeIsLimit`; the colimit description
of the global sections of a limit of affine schemes is
`AlgebraicGeometry.exists_appTop_eq_of_isAffine_of_isLimit_of_directed` with its vanishing
counterpart; descent of an isomorphism to a finite stage is
`AlgebraicGeometry.Space.MorphismDescentSystem.exists_isIso_mapAt`, which carries Stacks 084S;
and the concluding descent step, that affineness of a morphism of algebraic spaces is fpqc
local on the base, is `AlgebraicGeometry.Space.isLocalAtTarget_isAffineHom_fpqc`, which carries
Stacks 041Z with no hypothesis left.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 084T](https://stacks.math.columbia.edu/tag/084T)
* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **An affine algebraic space is a separated algebraic space.** An affine algebraic space is
isomorphic to the presheaf represented by an object of the site whose underlying scheme is
affine; an isomorphism is a separated morphism, so the source is separated over the terminal
scheme, which is absolute separatedness in the sense of Stacks 03BS part (1). -/
theorem isAbsolutelySeparated_of_isAffineSpace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAffineSpace B S hS F) : IsAbsolutelySeparated B S hS hZ F := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hF
  exact isAbsolutelySeparated_of_isSeparated_to_affine B S hS hZ T hT e.hom
    (isSeparated_of_isIso B S hS e.hom)

/-- **An affine limit has a separated stage.** In the situation of Stacks 084R, if the limit `X`
of the inverse system is affine then `X_i` is separated for some `i` beyond the distinguished
index.

This is Stacks 084T applied to the limit, affineness of an algebraic space implying its
separatedness. Stacks 07SQ asserts more, namely that `X_i` is affine for some `i`. -/
theorem DescentSituation.exists_isAbsolutelySeparated_system_obj_of_isAffineSpace
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
    (hI : #I < B.cutoff.ord.cof) (hX : IsAffineSpace B S hS D.limitCone.pt) :
    ∃ i, D.base ≤ i ∧ IsAbsolutelySeparated B S hS hZ (D.system.obj (op i)) :=
  D.exists_isAbsolutelySeparated_system_obj B S hS hZ hI
    (isAbsolutelySeparated_of_isAffineSpace B S hS hZ hX)

end AlgebraicGeometry.Space

end
