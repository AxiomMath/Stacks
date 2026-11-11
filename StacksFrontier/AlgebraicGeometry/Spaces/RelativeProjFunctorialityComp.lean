module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistComp
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctoriality

/-!
# Composition of the morphisms of relative Proj of an algebraic space

Let `S` be a scheme, `X` an algebraic space over `S`, and `𝒜`, `ℬ`, `𝒞` quasi-coherent graded
`𝒪_X`-algebras with relative Projs `P`, `Q` and `R`.  For maps `φ : 𝒜 ⟶ ℬ` and `ψ : ℬ ⟶ 𝒞`
read over the scheme points of the base (`AlgebraicGeometry.Space.RelativeProjHomPoints`), and a
map `χ : 𝒜 ⟶ 𝒞` equal to their composite, this file expresses the data Tag 085F attaches to `χ`
— the open subspace `U(χ) ⊆ R`, the morphism `r_χ : U(χ) ⟶ P` and the maps `θ_χ` on the twists —
through those of `φ` and `ψ`:

`U(χ) = r_ψ^{-1}(U(φ))`, `r_χ = r_φ ∘ r_ψ|_{U(χ)}` and `θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`.

These are the three assertions of Tag 085G once `χ` is the map attached to the composite of the
algebra maps; that identification, and the statement of Tag 085G for the relative Projs of
Situation 0849, are in `StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.HomPointsComp`.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjHomPoints.compRestrict`: the restriction
  `r_ψ|_{U(χ)}` of `r_ψ` to `U(χ)`, as a morphism into `U(φ)`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSubfunctor_eq_of_eq_comp`:
  `U(χ) = r_ψ^{-1}(U(φ))`, as an equality of subfunctors of `R`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.compRestrict_comp_relativeMapSpaceHom`:
  `r_χ = r_φ ∘ r_ψ|_{U(χ)}`, as an equality of morphisms `U(χ) ⟶ P`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap_comp`: **the third
  assertion of Tag 085G**, `θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`, over every scheme point of the base.

## Implementation notes

**The third assertion is stated where `θ` lives.**  Tag 085F's `θ` is, in this library, the
family `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap` of maps on the
twists over the scheme points `(T, f)` of the base — the restriction of `θ` to `U(ψ) ×_X T`,
which is how the source characterizes `θ`.  So the third assertion is stated at every such point
and every degree `n`, with the inverse-image isomorphisms identifying the source and the target of
the two sides written out, exactly as in the scheme-level Tag 07ZH
(`Stacks.AlgebraicGeometry.Tag07ZGTwistStatement.relativeMapDomain_mapHom_twistMap_comp`); the
restriction of `r_ψ` there is `Stacks.AlgebraicGeometry.Tag07ZGTwist.relativeMapHomRestrict` of
the restricted maps.  It is stated for the composite `hφ.comp hψ` itself: the twists of `χ` live
over the open of `χ` at each point, which is the open of the composite only up to the equation
`χ = hφ.comp hψ`.  The twist `𝒪_P(n)` over `(T, f)` is written `relativeTwist (dP.algebra T f) n`,
which is what `AlgebraicGeometry.Space.RelativeProjPoints.pointTwist` abbreviates: spelled through
the abbreviation, the statement is the same, but the kernel's check of the scheme-level proof
against it exceeds the default limit.

The proof is the source's: all three assertions are local on `X`, so they follow from the case of
schemes, Tag 07ZH, at the scheme points of the base.

## References

* [Stacks Project, Tag 085G](https://stacks.math.columbia.edu/tag/085G)
* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 07ZH](https://stacks.math.columbia.edu/tag/07ZH)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapComp
open Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.Tag07ZGTwist

namespace AlgebraicGeometry.Space.RelativeProjHomPoints

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X} {πQ : Q ⟶ X} {πR : R ⟶ X}
    {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
    {dR : RelativeProjPoints B S hS πR}
    (hφ : RelativeProjHomPoints dP dQ) (hψ : RelativeProjHomPoints dQ dR)
    {hχ : RelativeProjHomPoints dP dR} (e : hχ = hφ.comp hψ)

include e in
/-- The open of a map equal to the composite lies in the open of the outer factor. -/
theorem relativeMapSubfunctor_le_of_eq_comp :
    hχ.relativeMapSubfunctor ≤ hψ.relativeMapSubfunctor := by
  subst e
  exact hφ.comp_relativeMapSubfunctor_le hψ

/-- **The restriction `r_ψ|_{U(χ)}`.**  For `χ` equal to the composite `ψ ∘ φ`, the morphism
`r_ψ : U(ψ) ⟶ Q` restricted to the open subspace `U(χ) ⊆ U(ψ)` lands in `U(φ)`, and this is that
restriction as a morphism `U(χ) ⟶ U(φ)`. -/
def compRestrict :
    hχ.relativeMapSubfunctor.toFunctor ⟶ hφ.relativeMapSubfunctor.toFunctor :=
  Subfunctor.lift (Subfunctor.homOfLe (hφ.relativeMapSubfunctor_le_of_eq_comp hψ e) ≫
      hψ.relativeMapSpaceHom) (by
    subst e
    rintro Y _ ⟨⟨y, hc⟩, rfl⟩
    exact (hφ.mem_comp_relativeMapSubfunctor_iff hψ Y y _).1 hc)

/-- The restriction of `r_ψ` to `U(χ)`, followed by the inclusion of `U(φ)` into `Q`, is the
inclusion of `U(χ)` into `U(ψ)` followed by `r_ψ`. -/
@[reassoc]
theorem compRestrict_ι :
    hφ.compRestrict hψ e ≫ hφ.relativeMapSubfunctor.ι =
      Subfunctor.homOfLe (hφ.relativeMapSubfunctor_le_of_eq_comp hψ e) ≫
        hψ.relativeMapSpaceHom :=
  rfl

include e in
/-- **`U(χ) = r_ψ^{-1}(U(φ))`**, as subfunctors of `R`: the open subspace attached to a map equal
to the composite is the image, under the inclusion of `U(ψ)` into `R`, of the inverse image of
`U(φ)` along `r_ψ`. -/
theorem relativeMapSubfunctor_eq_of_eq_comp :
    hχ.relativeMapSubfunctor =
      (hφ.relativeMapSubfunctor.preimage hψ.relativeMapSpaceHom).image
        hψ.relativeMapSubfunctor.ι := by
  subst e
  refine Subfunctor.ext (funext fun Y => Set.ext fun y => ⟨fun hc => ?_, ?_⟩)
  · have hy : y ∈ hψ.relativeMapSubfunctor.obj Y := hφ.comp_relativeMapSubfunctor_le hψ Y hc
    exact ⟨⟨y, hy⟩, (hφ.mem_comp_relativeMapSubfunctor_iff hψ Y y hy).1 hc, rfl⟩
  · rintro ⟨⟨y', hy⟩, h, rfl⟩
    exact (hφ.mem_comp_relativeMapSubfunctor_iff hψ Y y' hy).2 h

/-- **`r_χ = r_φ ∘ r_ψ|_{U(χ)}`.** -/
theorem compRestrict_comp_relativeMapSpaceHom :
    hφ.compRestrict hψ e ≫ hφ.relativeMapSpaceHom = hχ.relativeMapSpaceHom := by
  subst e
  ext Y ⟨y, hc⟩
  exact (hφ.app_comp_relativeMapSpaceHom hψ Y y _ hc _).symm

/-- **Tag 085G, the third assertion: `θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`**, over a scheme point
`(T, f)` of the base and in degree `n`.  The `n`-th map on twists of the composite is the inverse
image along the restriction of `r_ψ` to `U(ψ ∘ φ)` of the `n`-th map on twists of `φ`, followed
by the inverse image along the inclusion of `U(ψ ∘ φ)` into `U(ψ)` of the `n`-th map on twists of
`ψ`; the remaining factors are the inverse-image isomorphisms that identify the sources and
targets, named by the first two assertions at that point.

The source's "obvious notation" `r_ψ^*θ_φ` is the inverse image of
`θ_φ : r_φ^*𝒪_P(n) ⟶ 𝒪_{U(φ)}(n)` along `r_ψ|_{U(ψ ∘ φ)} : U(ψ ∘ φ) ⟶ U(φ)`, a map
`r_ψ^*r_φ^*𝒪_P(n) ⟶ r_ψ^*𝒪_Q(n)` over `U(ψ ∘ φ)`; it is composed with `θ_ψ` restricted to
`U(ψ ∘ φ)`, and `r_ψ^*r_φ^* = r_{ψ ∘ φ}^*` by the second assertion.  Tag 085F's `θ` is, in this
library, `AlgebraicGeometry.Space.RelativeProjHomPoints.relativeTwistSpaceMap`, its restriction
over every scheme point `(T, f)` of `X`, so this is the assertion over every such point.  The
source's `θ` is a map of `ℤ`-graded algebras, and such a map is determined by its components, so
the degreewise identity is the identity of graded maps. -/
@[stacks 085G "(3): θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}, in every degree n and over every scheme point \
(T, f) of X, where Tag 085F's θ is given: the inverse image of θ_φ along the restriction \
r_ψ|_{U(ψ ∘ φ)} : U(ψ ∘ φ) ⟶ U(φ), followed by the restriction of θ_ψ to U(ψ ∘ φ), is \
θ_{ψ ∘ φ}, up to the canonical inverse-image isomorphisms"]
theorem relativeTwistSpaceMap_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (n : ℤ) :
    (Scheme.Modules.pullbackCongr
          (relativeMapHomRestrict_comp_relativeMapHom (hφ.hom T f) (hψ.hom T f))).inv.app
        (relativeTwist (dP.algebra T f) n) ≫
      (Scheme.Modules.pullbackComp (relativeMapHomRestrict (hφ.hom T f) (hψ.hom T f))
          (relativeMapHom (hφ.hom T f))).inv.app (relativeTwist (dP.algebra T f) n) ≫
      (Scheme.Modules.pullback (relativeMapHomRestrict (hφ.hom T f) (hψ.hom T f))).map
          (hφ.relativeTwistSpaceMap T f n) ≫
      (Scheme.Modules.pullbackComp (relativeMapHomRestrict (hφ.hom T f) (hψ.hom T f))
          (hφ.hom T f).relativeMapDomain.ι).hom.app (relativeTwist (dQ.algebra T f) n) ≫
      (Scheme.Modules.pullbackCongr
          (relativeMapHomRestrict_comp_ι (hφ.hom T f) (hψ.hom T f))).hom.app
        (relativeTwist (dQ.algebra T f) n) ≫
      (Scheme.Modules.pullbackComp
          ((relativeProj (dR.algebra T f)).scheme.homOfLE
            (relativeMapDomain_comp_le (hφ.hom T f) (hψ.hom T f)))
          (relativeMapHom (hψ.hom T f))).inv.app (relativeTwist (dQ.algebra T f) n) ≫
      (Scheme.Modules.pullback ((relativeProj (dR.algebra T f)).scheme.homOfLE
          (relativeMapDomain_comp_le (hφ.hom T f) (hψ.hom T f)))).map
        (hψ.relativeTwistSpaceMap T f n) ≫
      (Scheme.Modules.pullbackComp ((relativeProj (dR.algebra T f)).scheme.homOfLE
            (relativeMapDomain_comp_le (hφ.hom T f) (hψ.hom T f)))
          (hψ.hom T f).relativeMapDomain.ι).hom.app (relativeTwist (dR.algebra T f) n) ≫
      (Scheme.Modules.pullbackCongr (Scheme.homOfLE_ι (relativeProj (dR.algebra T f)).scheme
          (relativeMapDomain_comp_le (hφ.hom T f) (hψ.hom T f)))).hom.app
        (relativeTwist (dR.algebra T f) n) =
      (hφ.comp hψ).relativeTwistSpaceMap T f n :=
  relativeTwistMap_comp (hφ.hom T f) (hψ.hom T f) n

end AlgebraicGeometry.Space.RelativeProjHomPoints

end
