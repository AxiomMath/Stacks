module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.HomPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctorialityComp

/-!
# Composition of the morphisms of relative Proj of an algebraic space (Stacks 085G)

Let `S` be a scheme, `X` an algebraic space over `S`, and `𝒜`, `ℬ`, `𝒞` quasi-coherent graded
`𝒪_X`-algebras, with relative Projs `P = Proj_X(𝒜)`, `Q = Proj_X(ℬ)` and `R = Proj_X(𝒞)` of
Stacks 084C (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor` of the three
situations of Situation 0849). For graded `𝒪_X`-algebra maps `φ : 𝒜 ⟶ ℬ` and `ψ : ℬ ⟶ 𝒞`,
Tag 085F attaches to `φ`, `ψ` and `ψ ∘ φ` the open subspaces `U(-)`, the morphisms `r_-` and the
maps `θ_-` on the twists, through the maps of graded algebras over the scheme points of the base
`AlgebraicGeometry.Space.RelativeProjSituation.homPoints` that the algebra maps define, with
nothing assumed. This file proves Tag 085G for them:

`U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`, `r_{ψ ∘ φ} = r_φ ∘ r_ψ|_{U(ψ ∘ φ)}` and
`θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.homPoints_comp_relativeMap_twist`:
  **Tag 085G.**

## Implementation notes

**The source's typographical slip.**  The source prints the first assertion as
`U(ψ ∘ φ) = r_φ^{-1}(U(ψ))`, which does not typecheck: `r_φ` is defined on the open `U(φ)` of
`Q` and takes values in `P`, whereas `U(ψ)` is an open of `R`.  The names `φ` and `ψ` have been
interchanged; the intended reading, which the second assertion requires (it restricts `r_ψ` to
`U(ψ ∘ φ)` and follows it by `r_φ`, so `r_ψ` must carry `U(ψ ∘ φ)` into `U(φ)`), is
`U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`, and that is what is stated, as an equality of subfunctors of `R`:
the image under the inclusion of `U(ψ)` into `R` of the inverse image of `U(φ)` along `r_ψ`.

**Composition order.**  The composite `ψ ∘ φ : 𝒜 ⟶ 𝒞` of unital homomorphisms of sheaves of
graded algebras is written `φ.comp ψ` (`SheafOfModules.GradedAlgebra.UnitalHom.comp` composes in
diagrammatic order).

**The twists.**  The map `θ_{ψ ∘ φ}` on the twists of `R` is, at a scheme point `(T, f)` of the
base, a map of modules over the open `U((ψ ∘ φ)|_T)` of Tag 07ZG. The first clause of the
statement identifies the map of graded algebras attached to `ψ ∘ φ` with the composite of those
attached to `φ` and `ψ`, and the third assertion is stated for that composite, on which the
scheme-level composite `ψ|_T ∘ φ|_T` and its open are literally the ones the factors give; the
remaining factors are the inverse-image isomorphisms identifying sources and targets, as in the
scheme-level Tag 07ZH.

The proof is the source's: the three assertions are local on `X`, and at the scheme points of the
base they are the case of schemes, Tag 07ZH
(`AlgebraicGeometry.Space.RelativeProjHomPoints.relativeMapSubfunctor_eq_of_eq_comp`,
`…compRestrict_comp_relativeMapSpaceHom` and `…relativeTwistSpaceMap_comp`).  The last of these is
the third assertion for an arbitrary map of graded algebras over the scheme points of the base,
and carries its own Tag 085G registration; the theorem here specializes it to the maps the
algebra maps define.

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

universe u m

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ 𝒜₃ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (h₃c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₃.piece i).val.obj U)
    (b : (𝒜₃.piece j).val.obj U), HEq ((𝒜₃.mul i j).app U a b) ((𝒜₃.mul j i).app U b a))
  (h₃n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₃.piece n))
  (h₃q : ∀ n : ℤ, (𝒜₃.piece n).IsQuasicoherentOnSite)
  (h₃k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₃.piece n).val.obj U) B.cutoff)
  (φ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₂ 𝒜₃)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "𝔰₃" => RelativeProjSituation.mk B S hS X 𝒜₃ h₃c h₃n h₃q h₃k
local notation "𝔡₁" => @RelativeProjPoints.algebra B S hS (ObjectProperty.FullSubcategory.obj X) _ _
  (RelativeProjSituation.relativeProjPoints (𝔰₁))
local notation "𝔡₂" => @RelativeProjPoints.algebra B S hS (ObjectProperty.FullSubcategory.obj X) _ _
  (RelativeProjSituation.relativeProjPoints (𝔰₂))
local notation "𝔡₃" => @RelativeProjPoints.algebra B S hS (ObjectProperty.FullSubcategory.obj X) _ _
  (RelativeProjSituation.relativeProjPoints (𝔰₃))
local notation "𝔥φ" => homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k φ
local notation "𝔥ψ" => homPoints h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k ψ
local notation "𝔥ψφ" => homPoints h₁c h₁n h₁q h₁k h₃c h₃n h₃q h₃k (φ.comp ψ)

/-- **[Stacks, Tag 085G].** Let `S` be a scheme, `X` an algebraic space over `S`, and `𝒜₁`, `𝒜₂`,
`𝒜₃` quasi-coherent graded `𝒪_X`-algebras (Situation 0849), with relative Projs
`P = Proj_X(𝒜₁)`, `Q = Proj_X(𝒜₂)` and `R = Proj_X(𝒜₃)`.  Let `φ : 𝒜₁ ⟶ 𝒜₂` and
`ψ : 𝒜₂ ⟶ 𝒜₃` be graded `𝒪_X`-algebra maps, and write `U(-)`, `r_-` and `θ_-` for the data of
Tag 085F attached to `φ`, `ψ` and `ψ ∘ φ` (`φ.comp ψ`) through
`AlgebraicGeometry.Space.RelativeProjSituation.homPoints`.  Then

0. the map of graded algebras over the scheme points of the base attached to `ψ ∘ φ` is the
  composite of those attached to `φ` and `ψ`;
1. `U(ψ ∘ φ) = r_ψ^{-1}(U(φ))`, as subfunctors of `R` (the image under the inclusion of `U(ψ)` of
  the inverse image of `U(φ)` along `r_ψ`; the source prints `r_φ^{-1}(U(ψ))`, which does not
  typecheck, the names `φ` and `ψ` being interchanged, see the module docstring);
2. `r_{ψ ∘ φ} = r_φ ∘ r_ψ|_{U(ψ ∘ φ)}`, with `r_ψ|_{U(ψ ∘ φ)} : U(ψ ∘ φ) ⟶ U(φ)` the restriction
  `AlgebraicGeometry.Space.RelativeProjHomPoints.compRestrict`;
3. `θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ}`: over every scheme point `(T, f)` of `X` — where Tag 085F's `θ`
  is given — and in every degree `n`, the map on twists of the composite is the inverse image of
  `θ_φ` along the restriction of `r_ψ`, followed by the inverse image of `θ_ψ` along the inclusion
  of `U(ψ ∘ φ)` into `U(ψ)`, up to the inverse-image isomorphisms identifying sources and targets.

There are no hypotheses beyond the data. -/
@[stacks 085G "the tag's three assertions for the relative Projs of Situation 0849 and the data \
of Tag 085F attached to the algebra maps: U(ψ ∘ φ) = r_ψ^{-1}(U(φ)) as subfunctors of R (the \
source prints r_φ^{-1}(U(ψ)), which is type-incorrect, the names φ and ψ being interchanged), \
r_{ψ ∘ φ} = r_φ ∘ r_ψ|_{U(ψ ∘ φ)}, and θ_ψ ∘ r_ψ^*θ_φ = θ_{ψ ∘ φ} at every scheme point of the \
base, where Tag 085F's θ is given"]
theorem homPoints_comp_relativeMap_twist :
    𝔥ψφ = (𝔥φ).comp (𝔥ψ) ∧
      (𝔥ψφ).relativeMapSubfunctor =
        ((𝔥φ).relativeMapSubfunctor.preimage (𝔥ψ).relativeMapSpaceHom).image
          (𝔥ψ).relativeMapSubfunctor.ι ∧
      (𝔥φ).compRestrict (𝔥ψ)
          (homPoints_comp h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k φ ψ) ≫
          (𝔥φ).relativeMapSpaceHom = (𝔥ψφ).relativeMapSpaceHom ∧
      ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X.1) (n : ℤ),
        (Scheme.Modules.pullbackCongr
              (relativeMapHomRestrict_comp_relativeMapHom ((𝔥φ).hom T f) ((𝔥ψ).hom T f))).inv.app
            (relativeTwist (𝔡₁ T f) n) ≫
          (Scheme.Modules.pullbackComp (relativeMapHomRestrict ((𝔥φ).hom T f) ((𝔥ψ).hom T f))
              (relativeMapHom ((𝔥φ).hom T f))).inv.app
            (relativeTwist (𝔡₁ T f) n) ≫
          (Scheme.Modules.pullback (relativeMapHomRestrict ((𝔥φ).hom T f) ((𝔥ψ).hom T f))).map
              ((𝔥φ).relativeTwistSpaceMap T f n) ≫
          (Scheme.Modules.pullbackComp (relativeMapHomRestrict ((𝔥φ).hom T f) ((𝔥ψ).hom T f))
              ((𝔥φ).hom T f).relativeMapDomain.ι).hom.app
            (relativeTwist (𝔡₂ T f) n) ≫
          (Scheme.Modules.pullbackCongr
              (relativeMapHomRestrict_comp_ι ((𝔥φ).hom T f) ((𝔥ψ).hom T f))).hom.app
            (relativeTwist (𝔡₂ T f) n) ≫
          (Scheme.Modules.pullbackComp
              ((relativeProj (𝔡₃ T f)).scheme.homOfLE
                (relativeMapDomain_comp_le ((𝔥φ).hom T f) ((𝔥ψ).hom T f)))
              (relativeMapHom ((𝔥ψ).hom T f))).inv.app
            (relativeTwist (𝔡₂ T f) n) ≫
          (Scheme.Modules.pullback ((relativeProj (𝔡₃ T f)).scheme.homOfLE
              (relativeMapDomain_comp_le ((𝔥φ).hom T f) ((𝔥ψ).hom T f)))).map
            ((𝔥ψ).relativeTwistSpaceMap T f n) ≫
          (Scheme.Modules.pullbackComp
              ((relativeProj (𝔡₃ T f)).scheme.homOfLE
                (relativeMapDomain_comp_le ((𝔥φ).hom T f) ((𝔥ψ).hom T f)))
              ((𝔥ψ).hom T f).relativeMapDomain.ι).hom.app
            (relativeTwist (𝔡₃ T f) n) ≫
          (Scheme.Modules.pullbackCongr
              (Scheme.homOfLE_ι (relativeProj (𝔡₃ T f)).scheme
                (relativeMapDomain_comp_le ((𝔥φ).hom T f) ((𝔥ψ).hom T f)))).hom.app
            (relativeTwist (𝔡₃ T f) n) =
          ((𝔥φ).comp (𝔥ψ)).relativeTwistSpaceMap T f n :=
  by
  have h := homPoints_comp h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k h₃c h₃n h₃q h₃k φ ψ
  exact ⟨h, RelativeProjHomPoints.relativeMapSubfunctor_eq_of_eq_comp _ _ h,
    RelativeProjHomPoints.compRestrict_comp_relativeMapSpaceHom _ _ h,
    fun T f n => RelativeProjHomPoints.relativeTwistSpaceMap_comp (𝔥φ) (𝔥ψ) T f n⟩

end AlgebraicGeometry.Space.RelativeProjSituation

end
