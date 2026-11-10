module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SchemePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.SectionsDescentBaseChange

/-!
# Sections of the projective bundle of a quasi-coherent module on an algebraic space

Let `X` be an algebraic space and `ℰ` a quasi-coherent `𝒪_X`-module, with projective bundle
`π : 𝐏(ℰ) = Proj_X(Sym(ℰ)) ⟶ X`. This file proves Stacks 0B4I: the sections of `π` are in
bijection with the isomorphism classes of invertible quotients of `ℰ`, every section is a closed
immersion, and the bijection is compatible with base change, the base change of `𝐏(ℰ)` along
`g : X' ⟶ X` being `𝐏(g^*ℰ)`.

The constructions are compatible with base change, so the statement is checked étale locally on
`X`, where it is Stacks 0B3V. The points of `𝐏(ℰ)` over a scheme point are identified with
invertible quotients by `pointsEquivInvertibleQuotientClass`, in
`StacksFrontier/AlgebraicGeometry/Spaces/ProjectiveBundle/SchemePoints.lean`, and the descent from
the étale charts is
`StacksFrontier/AlgebraicGeometry/Spaces/ProjectiveBundle/SectionsDescent.lean` and
`SectionsDescentBaseChange.lean`.

## Main definitions

* `AlgebraicGeometry.Space.projectiveBundleSectionsEquiv`: the bijection.
* `AlgebraicGeometry.Space.projectiveBundleBaseChange`: the base-change morphism
  `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`.

## Main results

* `AlgebraicGeometry.Space.projectiveBundle_sections_invertibleQuotients`: Stacks 0B4I, the
  characterization of the bijection at scheme points, every section is a closed immersion, and
  compatibility with base change.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (hb : SymmetricAlgebraBounded X E)

/-- The identification of the points of `𝐏(ℰ)` with invertible quotients is natural in the scheme
point. -/
theorem projectiveBundle_pointsEquiv_natural (T T' : BigFppfOver B S hS) (h : T' ⟶ T)
    (x : yoneda.obj T ⟶ X.1)
    (u : {u : yoneda.obj T ⟶ (relativeProjSymmetricAlgebra X E hE hb).1 //
      u ≫ (projectiveBundleπ X E hE hb).hom = x}) :
    pointsEquivInvertibleQuotientClass X E hE hb T' (yoneda.map h ≫ x)
        ⟨yoneda.map h ≫ u.1, yoneda_map_comp_point_comp (projectiveBundleπ X E hE hb).hom h u⟩ =
      invertibleQuotientBaseChangeClass (yonedaSpaceMap h)
        ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).app E).symm
        (pointsEquivInvertibleQuotientClass X E hE hb T x u) :=
  pointsEquivInvertibleQuotientClass_natural X E hE hb x h u

/-- **The bijection of Stacks 0B4I** between the sections of `π : 𝐏(ℰ) ⟶ X` and the isomorphism
classes of invertible quotients of `ℰ`, characterized in
`projectiveBundle_sections_invertibleQuotients`. -/
@[stacks 0B4I "the bijection between sections of P(E) -> X and invertible quotients of E"]
def projectiveBundleSectionsEquiv :
    {σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb // σ ≫ projectiveBundleπ X E hE hb = 𝟙 X} ≃
      InvertibleQuotientClass X E :=
  sectionsEquivOfPointsEquiv X E (projectiveBundleπ X E hE hb)
    (pointsEquivInvertibleQuotientClass X E hE hb) (projectiveBundle_pointsEquiv_natural X E hE hb)

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)
  (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E))

include hE in
/-- The pullback of a quasi-coherent module along a morphism of algebraic spaces is
quasi-coherent (Stacks 03GA). -/
theorem isQuasicoherentOnSite_modulePullback_projectiveBundle :
    ((modulePullback B S hS g).obj E :
      SheafOfModules.{u} (structureRingSheaf B S hS X')).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g E hE

/-- **The base-change morphism `𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`** over `g : X' ⟶ X`. -/
def projectiveBundleBaseChange :
    relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
        (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' ⟶
      relativeProjSymmetricAlgebra X E hE hb :=
  baseChangeHomOfPointsEquiv g E (projectiveBundleπ X E hE hb)
    (projectiveBundleπ X' ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb')
    (pointsEquivInvertibleQuotientClass X E hE hb) (projectiveBundle_pointsEquiv_natural X E hE hb)
    (pointsEquivInvertibleQuotientClass X' _ _ hb')
    (projectiveBundle_pointsEquiv_natural X' _ _ hb')

/-- **Stacks 0B4I: sections of `𝐏(ℰ) ⟶ X`, invertible quotients of `ℰ`, and base change.**

Let `X` be an algebraic space and `ℰ` a quasi-coherent `𝒪_X`-module, with projective bundle
`π : 𝐏(ℰ) = Proj_X(Sym(ℰ)) ⟶ X` (Stacks 084C).

1. **The bijection** `projectiveBundleSectionsEquiv` between the sections `σ` of `π` and the
   isomorphism classes of surjections `ℰ ⟶ ℒ` onto invertible `𝒪_X`-modules is the canonical one:
   it sends `σ` to `c` exactly when, at every scheme point `x : T ⟶ X`, the point `x ≫ σ` of
   `𝐏(ℰ)` over `x` corresponds to the pullback of `c` to `T` under the identification of the points
   of `𝐏(ℰ)` over `x` with the invertible quotients of `x^*ℰ`
   (`pointsEquivInvertibleQuotientClass`: Stacks 084B, the comparison of `x^*Sym(ℰ)` with
   `Sym(x^*ℰ)`, and Stacks 0B3V on `T`).
2. Every section of `π` is a closed immersion.
3. **Compatibility with base change**: for `g : X' ⟶ X`, the square formed by
   `projectiveBundleBaseChange : 𝐏(g^*ℰ) ⟶ 𝐏(ℰ)`, the two projections and `g` is cartesian, and
   a section `σ'` of `𝐏(g^*ℰ) ⟶ X'` lying over a section `σ` of `𝐏(ℰ) ⟶ X` corresponds to the
   pullback along `g` of the invertible quotient `σ` corresponds to.

The homogeneous sections of `Sym(ℰ)` (and of `Sym(g^*ℰ)`) are bounded by the cutoff of the site
(`SymmetricAlgebraBounded`), the set-theoretic convention of Situation 0849 under which the
relative Proj is an algebraic space over the chosen site. -/
@[stacks 0B4I "the bijection between sections of P(E) -> X and invertible quotients of E, its \
characterization at scheme points, sections are closed immersions, and compatibility with base \
change"]
theorem projectiveBundle_sections_invertibleQuotients :
    (∀ (σ : {σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb //
          σ ≫ projectiveBundleπ X E hE hb = 𝟙 X})
        (c : InvertibleQuotientClass X E),
      projectiveBundleSectionsEquiv X E hE hb σ = c ↔
        ∀ (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ X.1),
          pointsEquivInvertibleQuotientClass X E hE hb T x ⟨x ≫ σ.1.hom,
            comp_section_comp (projectiveBundleπ X E hE hb).hom x
              (congrArg InducedCategory.Hom.hom σ.2)⟩ = pointRestrictClass X E T x c) ∧
    (∀ σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb, σ ≫ projectiveBundleπ X E hE hb = 𝟙 X →
      IsClosedImmersion B S hS σ.hom) ∧
    (∀ (X' : AlgebraicSpaces B S hS) (g : X' ⟶ X)
        (hb' : SymmetricAlgebraBounded X' ((modulePullback B S hS g).obj E)),
      IsPullback (projectiveBundleBaseChange X E hE hb g hb').hom
          (projectiveBundleπ X' _ (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g)
            hb').hom
          (projectiveBundleπ X E hE hb).hom g.hom ∧
        ∀ (σ : {σ : X ⟶ relativeProjSymmetricAlgebra X E hE hb //
            σ ≫ projectiveBundleπ X E hE hb = 𝟙 X})
          (σ' : {σ' : X' ⟶ relativeProjSymmetricAlgebra X' ((modulePullback B S hS g).obj E)
              (isQuasicoherentOnSite_modulePullback_projectiveBundle X E hE g) hb' //
            σ' ≫ projectiveBundleπ X' _ _ hb' = 𝟙 X'}),
          σ'.1 ≫ projectiveBundleBaseChange X E hE hb g hb' = g ≫ σ.1 →
            projectiveBundleSectionsEquiv X' _ _ hb' σ' =
              invertibleQuotientBaseChangeClass g (Iso.refl _)
                (projectiveBundleSectionsEquiv X E hE hb σ)) :=
  ⟨fun σ c => sectionsEquivOfPointsEquiv_eq_iff X E _ _ _ σ c,
    fun σ hσ => isClosedImmersion_of_section_projectiveBundleπ X E hE hb σ hσ,
    fun _ g _ => ⟨isPullback_baseChangeHomOfPointsEquiv g E _ _ _ _ _ _,
      fun σ σ' comm => sectionsEquivOfPointsEquiv_baseChange g E _ _ _ _ _ _ σ σ' comm⟩⟩

end AlgebraicGeometry.Space

end
