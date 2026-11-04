module

public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.DegreeSectionBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheaf
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionConstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The monomial global sections of `𝒪(d)` under the canonical comparison of models

Over a commutative ring `R` the development carries two projective `n`-spaces: the homogeneous
spectrum `Proj R[T₀, …, Tₙ]` and the base-change model
`AlgebraicGeometry.projectiveSpaceOverRing n R`, on which the degree-`d` twist
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n (Spec R) d` is the inverse image of the
integral `𝒪(d)` along the projection to `ℙⁿ_ℤ`. A degree-`d` multidegree `e` names a global
section `T^e` of the twist on each model: on the base-change model it is
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverSection`, the pullback of
the monomial section of the integral model, and on the `Proj` model it is the degree-`d` section
map of [Stacks, Tag 01MY] applied to the monomial `T^e` of `R[T₀, …, Tₙ]`.

This file identifies the two models' `Γ(𝒪(d), ⊤)` by a **canonical** isomorphism and computes the
image of `T^e` under it: it is the section attached to the monomial `T^e` over `R`.

## Main definitions

* `Stacks.ProjectiveCohomology.canonicalPullbackProjModelIsoHomTwistOverIso`: the inverse image
  along `Stacks.ProjectiveCohomology.projModelIso` of the base-change model's `𝒪(d)` is the
  twisting sheaf of `R[T₀, …, Tₙ]`, by the comparison map of [Stacks, Tag 01MY].
* `Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso`: **the canonical identification of
  `Γ(twistOver n (Spec R) d, ⊤)` with `Γ(Proj R[T₀, …, Tₙ], 𝒪(d))`**, in every integer degree and
  over every coefficient ring.
* `Stacks.ProjectiveCohomology.coordMonomialOver`: the monomial `T^e` of `R[T₀, …, Tₙ]`.

## Main results

* `Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso_hom_degreeSection`: the canonical
  identification carries the pullback of the section of a homogeneous element `a` of
  `ℤ[T₀, …, Tₙ]` to the section of the image of `a` in `R[T₀, …, Tₙ]`.
* `Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso_hom_twistOverSection`: **the canonical
  identification carries the monomial section `T^e` of `𝒪(d)` on the base-change model to the
  degree-`d` section of the monomial `T^e` of `R[T₀, …, Tₙ]`.**

## The mathematics

The identification is the composite of two canonical isomorphisms. The first,
`Stacks.ProjectiveCohomology.pullbackProjModelIsoHomProjectiveTwistingSheafIso`, is unconditional
and formal: the base-change model's `𝒪(d)` is an inverse image along the projection to `ℙⁿ_ℤ`, and
`projModelIso` carries that projection to `Stacks.ProjectiveCohomology.projModelMap`, so the two
successive inverse images collapse to one. The second is
`Stacks.ProjectiveCohomology.projModelTwistTransport`, the comparison map of [Stacks, Tag 01MY]
for the coefficient map `ℤ → R`, which is invertible.

Because both legs are canonical the composite can be evaluated. The comparison of global
sections across an isomorphism of schemes is the canonical pullback map on global sections
followed by the identification of the inverse image
(`AlgebraicGeometry.Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply`). On the first leg a
global section pulled back twice is the section pulled back along the composite — this is
`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp` followed by
`AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_congr`. On the second leg
`Stacks.ProjectiveCohomology.projModelTwistTransport_app_top_degreeSection` says that the
comparison carries the section of a homogeneous element `a` to the section of the polynomial
obtained from `a` by applying `ℤ → R` to its coefficients. For `a` the integral monomial `T^e`
with coefficient `1` that polynomial is the monomial `T^e` with coefficient `1` over `R`.

The degree of a monomial is a natural number while the twist is indexed by an integer, so the
statement about `T^e` carries the transport along `(e.degree : ℤ) = d` that
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.monomialSectionAtUniverse` already
carries; the computation itself is done in a natural-number degree.

## Implementation notes

The identification is phrased on `Γ(·, ⊤)` rather than on
`CategoryTheory.SheafOfModules.sections`, because a global section of a twist is produced by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` in that form. The proofs are chains of
`Eq.trans` and `congrArg` rather than rewrites, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.TwistSectionTransport` record: goals mixing
the sections of a twisting sheaf with the sections of a pushforward of one are not type-correct at
the transparency at which `rw` checks a goal.

`Stacks.ProjectiveCohomology.twistSectionsEquiv` is a different identification of the same two
groups, built from an arbitrary witness of
`Stacks.ProjectiveCohomology.HasPolyTwistTransport`; nothing can be computed about it, and it is
left in place because the nonvanishing statements of
`StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.TwistSectionTransport` need no more than a
bijection.

**No tag attribute is attached.** The degree-zero row of [Stacks, Tag 01XW] is the assertion that
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.toPushforwardTwistOver` is an
isomorphism; the computation below is one ingredient of that assertion and not a clause of any
tag.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XV](https://stacks.math.columbia.edu/tag/01XV)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.SectionsEqualizer

universe u

namespace Stacks.ProjectiveCohomology

open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheafModule)

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable (R : Type u) [CommRing R] (n : ℕ)

/-! ### The canonical identification of the two models' `Γ(𝒪(d), ⊤)` -/

/-- **The inverse image of the base-change model's `𝒪(d)` along the comparison of models is the
twisting sheaf of `R[T₀, …, Tₙ]`**, by the canonical comparison of [Stacks, Tag 01MY] for the
coefficient map `ℤ → R`. -/
@[ega "II 3.5.4" "Case Y = Spec ℤ"]
def canonicalPullbackProjModelIsoHomTwistOverIso (d : ℤ) :
    (Scheme.Modules.pullback (projModelIso R n).hom).obj
        (twistOver n (Spec (CommRingCat.of R)) d) ≅
      twistingSheafModule (polyGrading R n) d :=
  pullbackProjModelIsoHomProjectiveTwistingSheafIso R n d ≪≫
    projModelTwistTransport n (fromULiftInt R) d

/-- **The canonical identification of the global sections of `𝒪(d)` on the two models of
`ℙⁿ_R`**, in every integer degree and over every coefficient ring. -/
def canonicalTwistGammaTopIso (d : ℤ) :
    Γ(twistOver n (Spec (CommRingCat.of R)) d, ⊤) ≅
      Γ(twistingSheafModule (polyGrading R n) d, ⊤) :=
  Scheme.Modules.gammaTopIsoOfPullbackIso (projModelIso R n).hom
    (canonicalPullbackProjModelIsoHomTwistOverIso R n d)

/-- The two legs of the inverse-image comparison, read on sections over `⊤`. -/
theorem canonicalPullbackProjModelIsoHomTwistOverIso_hom_app_top (d : ℤ)
    (x : Γ((Scheme.Modules.pullback (projModelIso R n).hom).obj
      (twistOver n (Spec (CommRingCat.of R)) d), ⊤)) :
    (canonicalPullbackProjModelIsoHomTwistOverIso R n d).hom.app ⊤ x =
      (projModelTwistTransport n (fromULiftInt R) d).hom.app ⊤
        (((Scheme.Modules.pullbackCongr
              (projModelIso_hom_toIntegralAtUniverse R n)).hom.app
            (projectiveSpaceAtUniverseTwistingSheaf.{u} n d)).app ⊤
          (((Scheme.Modules.pullbackComp (projModelIso R n).hom
                (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
                  (Spec (CommRingCat.of R)))).hom.app
              (projectiveSpaceAtUniverseTwistingSheaf.{u} n d)).app ⊤ x)) := rfl

/-- The formal leg of the canonical comparison carries a global section of the integral `𝒪(d)`
pulled back along the projection to the integral model and then along
`Stacks.ProjectiveCohomology.projModelIso` to the same section pulled back along
`Stacks.ProjectiveCohomology.projModelMap`. -/
theorem pullbackCongr_pullbackComp_pullbackGlobalSections (d : ℤ)
    (s : Γ(projectiveSpaceAtUniverseTwistingSheaf.{u} n d, ⊤)) :
    ((Scheme.Modules.pullbackCongr (projModelIso_hom_toIntegralAtUniverse R n)).hom.app
          (projectiveSpaceAtUniverseTwistingSheaf.{u} n d)).app ⊤
        (((Scheme.Modules.pullbackComp (projModelIso R n).hom
              (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
                (Spec (CommRingCat.of R)))).hom.app
            (projectiveSpaceAtUniverseTwistingSheaf.{u} n d)).app ⊤
          (pullbackGlobalSections (projModelIso R n).hom
            (twistOver n (Spec (CommRingCat.of R)) d)
            (pullbackGlobalSections
              (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
                (Spec (CommRingCat.of R)))
              (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) s))) =
      pullbackGlobalSections (projModelMap n (fromULiftInt R))
        (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) s :=
  Eq.trans
    (congrArg
      (fun z => ((Scheme.Modules.pullbackCongr
          (projModelIso_hom_toIntegralAtUniverse R n)).hom.app
        (projectiveSpaceAtUniverseTwistingSheaf.{u} n d)).app ⊤ z)
      (pullbackGlobalSections_comp (projModelIso R n).hom
        (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
          (Spec (CommRingCat.of R)))
        (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) s))
    (pullbackGlobalSections_congr (projModelIso_hom_toIntegralAtUniverse R n)
      (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) s)

/-- The canonical identification of the two models' global sections, evaluated on a global
section of the integral `𝒪(d)`, is the comparison of [Stacks, Tag 01MY] for the coefficient map
`ℤ → R` applied to that section. -/
theorem canonicalTwistGammaTopIso_hom_pullbackGlobalSections (d : ℤ)
    (s : Γ(projectiveSpaceAtUniverseTwistingSheaf.{u} n d, ⊤)) :
    (canonicalTwistGammaTopIso R n d).hom
        (pullbackGlobalSections
          (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
            (Spec (CommRingCat.of R)))
          (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) s) =
      (projModelTwistTransport n (fromULiftInt R) d).hom.app ⊤
        (pullbackGlobalSections (projModelMap n (fromULiftInt R))
          (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) s) :=
  Eq.trans
    (Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply (projModelIso R n).hom
      (canonicalPullbackProjModelIsoHomTwistOverIso R n d)
      (pullbackGlobalSections
        (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
          (Spec (CommRingCat.of R)))
        (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) s))
    (Eq.trans
      (canonicalPullbackProjModelIsoHomTwistOverIso_hom_app_top R n d _)
      (congrArg (fun z => (projModelTwistTransport n (fromULiftInt R) d).hom.app ⊤ z)
        (pullbackCongr_pullbackComp_pullbackGlobalSections R n d s)))

/-! ### The image of a monomial section -/

/-- **The canonical identification carries the pullback of the degree-`m` section of a
homogeneous `a ∈ ℤ[T₀, …, Tₙ]` to the degree-`m` section of the image of `a` in
`R[T₀, …, Tₙ]`.** -/
theorem canonicalTwistGammaTopIso_hom_degreeSection (m : ℕ)
    (a : polyGrading (ULift.{u} ℤ) n m) :
    (canonicalTwistGammaTopIso R n (m : ℤ)).hom
        (pullbackGlobalSections
          (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n
            (Spec (CommRingCat.of R)))
          (projectiveSpaceAtUniverseTwistingSheaf.{u} n (m : ℤ))
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
            (polyGrading (ULift.{u} ℤ) n) m a)) =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (polyGrading R n) m
        ⟨MvPolynomial.map (fromULiftInt R) (a : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)),
          (polyGradedMap (Fin (n + 1)) (fromULiftInt R)).map_mem a.2⟩ :=
  Eq.trans
    (canonicalTwistGammaTopIso_hom_pullbackGlobalSections R n (m : ℤ)
      (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
        (polyGrading (ULift.{u} ℤ) n) m a))
    (Eq.trans
      (congrArg (fun z => (projModelTwistTransport n (fromULiftInt R) (m : ℤ)).hom.app ⊤ z)
        (pullbackGlobalSections_unit (projModelMap n (fromULiftInt R))
          (projectiveSpaceAtUniverseTwistingSheaf.{u} n (m : ℤ))
          (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
            (polyGrading (ULift.{u} ℤ) n) m a)))
      (projModelTwistTransport_app_top_degreeSection n (fromULiftInt R) m a))

/-- The monomial `T^e` of `R[T₀, …, Tₙ]` attached to a degree-`d` multidegree `e`. -/
def coordMonomialOver {n : ℕ} {d : ℤ} (e : MonomialIndex.{u} n d) :
    MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.monomial (Finsupp.equivMapDomain Equiv.ulift e.1) 1

/-- `T^e` is homogeneous of degree the total degree of `e`. -/
theorem coordMonomialOver_mem {n : ℕ} {d : ℤ} (e : MonomialIndex.{u} n d) :
    coordMonomialOver R e ∈ polyGrading R n e.1.degree :=
  MvPolynomial.isHomogeneous_monomial 1 (degree_equivMapDomain_ulift e.1)

/-- Applying `ℤ → R` to the coefficients of the integral monomial `T^e` gives the monomial `T^e`
of `R[T₀, …, Tₙ]`. -/
theorem map_fromULiftInt_coordMonomial {n : ℕ} {d : ℤ} (e : MonomialIndex.{u} n d) :
    MvPolynomial.map (fromULiftInt R) (coordMonomial e) = coordMonomialOver R e := by
  rw [coordMonomial, coordMonomialOver, MvPolynomial.map_monomial, map_one]

/-- The image under `ℤ → R` of the integral monomial `T^e` is the monomial `T^e` of
`R[T₀, …, Tₙ]`, as homogeneous elements of degree the total degree of `e`. -/
theorem mapCoordMonomial_eq {n : ℕ} {d : ℤ} (e : MonomialIndex.{u} n d) :
    (⟨MvPolynomial.map (fromULiftInt R) (coordMonomial e),
        (polyGradedMap (Fin (n + 1)) (fromULiftInt R)).map_mem (coordMonomial_mem e)⟩ :
      polyGrading R n e.1.degree) =
      ⟨coordMonomialOver R e, coordMonomialOver_mem R e⟩ :=
  Subtype.ext (map_fromULiftInt_coordMonomial R e)

/-- **The canonical identification carries the monomial section `T^e` of `𝒪(d)` on the
base-change model of `ℙⁿ_R` to the degree-`d` section of the monomial `T^e` of
`R[T₀, …, Tₙ]`.**

Both sides are read in the natural-number degree `e.1.degree`, transported to the integer degree
`d` along `e.2` exactly as
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.monomialSectionAtUniverse` is. -/
theorem canonicalTwistGammaTopIso_hom_twistOverSection (d : ℤ) (e : MonomialIndex.{u} n d) :
    (canonicalTwistGammaTopIso R n d).hom
        (twistOverSection n (Spec (CommRingCat.of R)) d e) =
      (eqToHom (congrArg (twistingSheafModule (polyGrading R n)) e.2)).app ⊤
        (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (polyGrading R n) e.1.degree
          ⟨coordMonomialOver R e, coordMonomialOver_mem R e⟩) := by
  obtain ⟨e, he⟩ := e
  subst he
  simp only [eqToHom_refl, Scheme.Modules.Hom.id_app]
  refine Eq.trans ?_ (congrArg
    (fun b => AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
      (polyGrading R n) e.degree b)
    (mapCoordMonomial_eq R (⟨e, rfl⟩ : MonomialIndex.{u} n _)))
  exact canonicalTwistGammaTopIso_hom_degreeSection R n e.degree
    ⟨coordMonomial (⟨e, rfl⟩ : MonomialIndex.{u} n _),
      coordMonomial_mem (⟨e, rfl⟩ : MonomialIndex.{u} n _)⟩

end Stacks.ProjectiveCohomology

end
