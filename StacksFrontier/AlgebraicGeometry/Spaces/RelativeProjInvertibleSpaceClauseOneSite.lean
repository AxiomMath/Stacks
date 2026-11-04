module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOnePoint

/-!
# The source identification of clause (1) of Stacks 0D2Z at a scheme point of `U(ψ)`

Clause (1) of [Stacks, Tag 0D2Z] on the algebraic space `U(ψ)` is descended from its restriction
to the scheme points `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_pointFamilyDescendedHom_eq`), where it reads: the inverse image
along `w` of the `ψ_P` leg (`…InvertibleTwistingRestriction.clauseOneProjLeg`), followed by the
chart map `χ_w` of `θ` (`…InvertibleTwistingRestriction.chartMap`), is the inverse image along `w`
of the `ψ` leg (`…InvertibleTwistingRestriction.clauseOnePsiLeg`).

Both legs come out of `w^*(π_{U(ψ)}^*𝒜_d)`, and `χ_w` is built from `θ_w` on the scheme `W`
(`…InvertibleTwistingRestriction.chartSchemeTheta`) by conjugating with identifications of its
source and target.  This file provides the **source identification** of that square: the chain
`w^*(π_{U(ψ)}^*𝒜_d) ≅ (c_w^*(π_W^*((f ∘ w)^*𝒜)_d))^a` through the comparisons of Stacks 03LU, the
base change identification of Stacks 084D at `W` and Stacks 03DX (2)
(`…InvertibleTwistingRestriction.clauseOnePointSourceIso`), and the factorisation of `ψ` of
Tag 01NR at a scheme point through the module attached to a morphism of quasi-coherent modules on
the scheme (`…RelativeProjSituation.fibrePsiQcohHom`, `…RelativeProjSituation.fibrePsiHom_eq`),
which is the form in which the two legs of the square are compared.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiQcohHom`: Tag 01NR's `ψ` on the scheme of
  `T ×_X P`, in adjoint form, as a morphism of quasi-coherent modules.
* `…InvertibleTwistingRestriction.clauseOnePointSourceIso`: **the source identification of the
  square of clause (1) at a scheme point `w` of `U(ψ)`.**

## Main results

* `…RelativeProjSituation.fibrePsiHom_eq`: `ψ` of Tag 01NR at a scheme point is the
  identification of its source followed by the module attached to `…fibrePsiQcohHom`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)
open AlgebraicGeometry

universe u m

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **Tag 01NR's `ψ` on the scheme of `T ×_X P`, in adjoint form, as a morphism of quasi-coherent
modules**: the morphism `AlgebraicGeometry.Space.RelativeProjSituation.psiChartSchemeHomOfAdjoint`
read in the full subcategory of quasi-coherent modules, which is the factor of
`…RelativeProjSituation.fibrePsiHom` after the identification of its source. -/
def fibrePsiQcohHom (T : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj T ⟶ s.space.1) (n : ℕ) :
    quasicoherentPullbackObj s.site s.base s.containsBase (s.relativeProjPoints.fibreHom T v)
        (s.pointPieceQcoh T v (n : ℤ)) ⟶
      s.twistPieceQcoh T v (n : ℤ) :=
  ObjectProperty.homMk (s.psiChartSchemeHomOfAdjoint T v n)

/-- **`ψ` of Tag 01NR at a scheme point is the identification of its source followed by the module
attached (Stacks 03DX (2)) to `…RelativeProjSituation.fibrePsiQcohHom`**: the two factors of
`AlgebraicGeometry.Space.RelativeProjSituation.fibrePsiHom`, with the second one named. -/
theorem fibrePsiHom_eq (T : BigFppfOver s.site s.base s.containsBase)
    (v : yoneda.obj T ⟶ s.space.1) (n : ℕ) :
    s.fibrePsiHom T v n =
      (s.fibrePsiSourceIso T v (n : ℤ)).hom ≫
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          (s.relativeProjPoints.fibre T v)).functor.map (s.fibrePsiQcohHom T v n)).hom :=
  rfl

end AlgebraicGeometry.Space.RelativeProjSituation

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {W : BigFppfOver s.site s.base s.containsBase}
  (w : yoneda.obj W ⟶ (locusSpaceOfUnitalHom s f L ψ).obj) (d : ℕ)

/-- **The source identification of the square of clause (1) of Stacks 0D2Z at a scheme point `w`
of `U(ψ)`**: the inverse image along `w` of `π_{U(ψ)}^*𝒜_d`, identified with the module attached
(Stacks 03DX (2)) to the inverse image along the section `c_w` of `π_W^*((f ∘ w)^*𝒜)_d`, through
the comparisons of Stacks 03LU, the identification of the source of `ψ` at the scheme point
(`…RelativeProjSituation.fibrePsiSourceIso`) and Stacks 03DX (2).  This is the identification
through which the inverse image along `w` of `…InvertibleTwistingRestriction.clauseOneProjLeg`,
followed by the identification `…InvertibleTwistingRestriction.chartSourceIso` of the source of
`θ_w`, is the inverse image along `c_w` of `ψ` of Tag 01NR on `W ×_Y Proj_Y(𝒜)`. -/
def clauseOnePointSourceIso :=
  (modulePullback s.site s.base s.containsBase
        (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)).map
      (eqToHom (congrArg (fun k => (modulePullback s.site s.base
            s.containsBase k).obj (s.shrink.algebra.piece (d : ℤ)))
          (invertibleSpaceMorphism_comp_relativeProjSpaceHom s f L ψ).symm) ≫
        ((modulePullbackCompIso s.site s.base s.containsBase
            ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
            s.relativeProjSpaceHom).app (s.shrink.algebra.piece (d : ℤ))).inv) ≫
    (modulePullbackCompTransportIso (pointHom (X := locusSpaceOfUnitalHom s f L ψ) w)
        ((ofUnitalHom s f L ψ).invertibleSpaceMorphism X.property)
        (representedSpaceMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))
        (s.fibreToSpaceHom W (locusPoint w ≫ f.hom))
        (ObjectProperty.hom_ext _
          ((comp_invertibleMorphism w (locusOpen_locusPoint w)).trans
            ((ofUnitalHom s f L ψ).map_chartSection_fibreToSpace _ _).symm))
        (s.psiSourceQcoh (d : ℤ)).obj).hom ≫
    (modulePullback s.site s.base s.containsBase
        (representedSpaceMap s.site s.base s.containsBase
          ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w)))).map
      (s.fibrePsiSourceIso W (locusPoint w ≫ f.hom) (d : ℤ)).hom ≫
    (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase
      ((ofUnitalHom s f L ψ).chartSection (locusPoint w) (locusOpen_locusPoint w))
      (quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.fibreHom W (locusPoint w ≫ f.hom))
        (s.pointPieceQcoh W (locusPoint w ≫ f.hom) (d : ℤ)))).hom

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
