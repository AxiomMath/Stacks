module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionRing
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.BaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Comparison
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.DegreeOneCover

/-!
# Base change of the degree-`d` global sections of `𝒪(d)`

Let `φ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings with `ℬ₊ ≤ 𝒜₊.map φ`, so
that `r = AlgebraicGeometry.Proj.map φ : Proj ℬ ⟶ Proj 𝒜` is defined, and let
`θ : r^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)` be the canonical comparison of twisting sheaves,
`Stacks.ProjTwistComparison.twistMap`. A homogeneous element `a` of degree `n` gives the global
section `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection 𝒜 n a` of `𝒪_{Proj 𝒜}(n)`, the
one whose value at every point is the fraction `a / 1`. This file proves that the map on global
sections determined by `θ`,

`Γ(Proj 𝒜, 𝒪(n)) ⟶ Γ(Proj ℬ, r^* 𝒪(n)) ⟶ Γ(Proj ℬ, 𝒪(n))`,

the first leg being the unit of `r^* ⊣ r_*`, carries `degreeSection 𝒜 n a` to
`degreeSection ℬ n (φ a)`.

For the polynomial grading and a change of coefficient ring `f : R →+* S`, where `r` is
`Stacks.ProjectiveCohomology.projModelMap n f` and `φ a` is `MvPolynomial.map f a`, this is the
compatibility with base change of global sections of twists: the identification of
`H⁰(ℙⁿ_R, 𝒪(d))` with the degree-`d` forms in `T₀, …, Tₙ` is compatible with base change. There
`θ` is moreover invertible, so it is the twist transport of
`Stacks.ProjectiveCohomology.HasPolyTwistTransport` rather than a map in one direction only, and
it is invertible for every coefficient ring map and not only for `ULift ℤ → S`.

## Main definitions

* `Stacks.ProjectiveCohomology.projModelTwistTransport`: **the base-change isomorphism
  `(projModelMap n f)^* 𝒪(d) ≅ 𝒪(d)`** of twisting sheaves on projective `n`-space, for an
  arbitrary ring homomorphism of coefficients and every integer `d`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_val`: the value of the degree-`n`
  section at a point is `a / 1`.
* `Stacks.ProjTwistComparison.sectionsMap_degreeSection` and
  `Stacks.ProjTwistComparison.pushforwardTwistMap_degreeSection`: the adjoint form of `θ` carries
  the degree-`n` section of `a` to the degree-`n` section of `φ a`.
* `Stacks.ProjTwistComparison.twistMap_degreeSection`: **the sheaf-level compatibility of `θ`
  with the degree-`n` section map**, for every homomorphism of nonnegatively graded rings
  satisfying the condition of `AlgebraicGeometry.Proj.map`.
* `Stacks.ProjectiveCohomology.isIso_polyTwistMap`: **the comparison is invertible for a change
  of coefficient ring of a polynomial algebra**, in every degree.
* `Stacks.ProjectiveCohomology.projModelTwistTransport_degreeSection`: **base change on
  global sections of `𝒪(d)`.** The transport carries the global section of `𝒪(d)` on
  `ℙⁿ_R` attached to a degree-`d` form `a` to the one on `ℙⁿ_S` attached to the form obtained
  from `a` by applying `f` to its coefficients.

## The mathematics

`θ` is by construction the adjoint transpose of the explicit morphism
`Stacks.ProjTwistComparison.pushforwardTwistMap : 𝒪_{Proj 𝒜}(n) ⟶ r_* 𝒪_{Proj ℬ}(n)`, which on
sections over an open is the pointwise localization of `φ` on a family of degree-`n` fractions.
So the computation happens on the adjoint side, and there it is a statement about fractions: the
value of `degreeSection 𝒜 n a` at every point is `a / 1`, the fibre comparison sends `m / s` to
`φ m / φ s`, and `φ 1 = 1`. The adjunction identity `CategoryTheory.Adjunction.homEquiv_unit`
then transports the conclusion to `θ` itself; the preimage of `⊤` under `r` is `⊤`, so no
transport of opens intervenes.

Invertibility of `θ` for the polynomial grading is
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison`, whose condition — that
the images of the degree-one part generate the irrelevant ideal of the target — holds for a
coefficient ring map because the coordinate variables of `S[T₀, …, Tₙ]` are the images of those
of `R[T₀, …, Tₙ]`. Nothing there restricts the coefficient ring map.

## Implementation notes

The identity `Γ(r_* M, ⊤) = Γ(M, r ⁻¹ᵁ ⊤) = Γ(M, ⊤)` holds definitionally, which is what lets the
statements compose the two maps on sections without an `eqToHom`. For the same reason the proofs
are chains of `Eq.trans` and `congrArg` rather than rewrites: a goal that mixes the sections of a
twisting sheaf with the sections of a pushforward of one is not type-correct at the transparency
at which `rw` checks a goal, as the sibling files of
`StacksFrontier/AlgebraicGeometry/ProjTwistCompare/` record.

`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection_val` states the value of the degree-`n`
section directly on the underlying family of fractions, which is the shape the comparison of
sections is written in. It restates
`Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply` in the namespace the twist and
the section itself live in.

The development has two comparison maps on twists, and this file is about the second one.
`Stacks.AlgebraicGeometry.ProjTwistTheta.twistMap_degreeSection` is the corresponding statement
for `Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, which is defined for an arbitrary
graded ring homomorphism but only on its domain of definition `U(ψ) ⊆ Proj ℬ`. A twist transport
for a coefficient base change has to be a morphism on all of `Proj ℬ`, which is why this file uses
the second map.

## Relation to the cohomology of projective space

The identification of `H⁰` used here is the canonical degree-`d` section map, which
`Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear_apply` reads as a map of `R`-modules. The
base-change clause of [Stacks, Tag 01XV] for the identifications of [Stacks, Equation 01XU] is
`Stacks.ProjectiveSpace.Cohomology.serreTwistCohomology_degreeZero_baseChange`, whose `f`-map is
built from `Stacks.ProjectiveCohomology.projModelTwistTransport`.

The isomorphism whose existence `Stacks.ProjectiveCohomology.HasPolyTwistTransport` asserts is an
arbitrary one; the compatibility below is about
`Stacks.ProjectiveCohomology.projModelTwistTransport`.

## References

* [Stacks Project, Tag 01XV](https://stacks.math.columbia.edu/tag/01XV)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousIdeal Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj

universe u w

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The value at a point of the global section of `𝒪(n)` attached to a homogeneous element `a`
of degree `n` is the fraction `a / 1`. -/
theorem degreeSection_val (n : ℕ) (a : 𝒮 n) (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒮))) :
    (degreeSection 𝒮 n a).1 x =
      LocalizedModule.mk (a : S) (1 : x.1.asHomogeneousIdeal.toIdeal.primeCompl) :=
  Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply 𝒮 n a x

end AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.ProjTwistComparison

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)

/-! ### The computation on the adjoint side -/

/-- **The pointwise comparison of sections carries the degree-`n` section of `a` to the
degree-`n` section of `φ a`.** Both families are constant: the first has value `a / 1` at every
point and the comparison sends that to `φ a / φ 1`, which is `φ a / 1`. -/
theorem sectionsMap_degreeSection (n : ℕ) (a : 𝒜 n) :
    sectionsMap φ hφ (n : ℤ) ⊤ (degreeSection 𝒜 n a) =
      degreeSection ℬ n ⟨φ (a : A), φ.map_mem a.2⟩ := by
  refine Subtype.ext (funext fun y => ?_)
  have h1 : (sectionsMap φ hφ (n : ℤ) ⊤ (degreeSection 𝒜 n a)).1 y =
      fibreMap φ hφ y.1 ((degreeSection 𝒜 n a).1
        ⟨ProjectiveSpectrum.comapFun φ hφ y.1, trivial⟩) := rfl
  refine h1.trans ?_
  refine Eq.trans (congrArg (fibreMap φ hφ y.1)
    (degreeSection_val 𝒜 n a ⟨ProjectiveSpectrum.comapFun φ hφ y.1, trivial⟩)) ?_
  refine Eq.trans (fibreMap_mk φ hφ y.1 (a : A) 1) ?_
  refine Eq.trans ?_ (degreeSection_val ℬ n ⟨φ (a : A), φ.map_mem a.2⟩ ⟨y.1, trivial⟩).symm
  exact congrArg (fun s => LocalizedModule.mk (M := B) (φ (a : A)) s) (Subtype.ext (map_one φ))

/-- The adjoint transpose of the comparison on the `n`-th twist carries the global section of
`𝒪(n)` on `Proj 𝒜` attached to a homogeneous element `a` of degree `n` to the global section of
`𝒪(n)` on `Proj ℬ` attached to `φ a`. -/
theorem pushforwardTwistMap_degreeSection (n : ℕ) (a : 𝒜 n) :
    ((pushforwardTwistMap φ hφ (n : ℤ)).val.app (op ⊤)).hom' (degreeSection 𝒜 n a) =
      degreeSection ℬ n ⟨φ (a : A), φ.map_mem a.2⟩ :=
  sectionsMap_degreeSection φ hφ n a

/-! ### The comparison itself -/

/-- The unit of `r^* ⊣ r_*` followed by the direct image of the comparison on the `n`-th twist is
the adjoint transpose of that comparison. This is
`CategoryTheory.Adjunction.homEquiv_unit` for the transpose that defines
`Stacks.ProjTwistComparison.twistMap`. -/
theorem unit_comp_map_twistMap (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.map φ hφ)).unit.app
        (twistingSheaf 𝒜 n) ≫
      (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map φ hφ)).map (twistMap φ hφ n) =
      pushforwardTwistMap φ hφ n :=
  (Adjunction.homEquiv_unit
    (Scheme.Modules.pullbackPushforwardAdjunction (AlgebraicGeometry.Proj.map φ hφ)) _ _
    (twistMap φ hφ n)).symm.trans (homEquiv_twistMap φ hφ n)

/-- **The comparison on the `n`-th twist is compatible with the degree-`n` section map.** The
map on global sections determined by `θ : r^* 𝒪_{Proj 𝒜}(n) ⟶ 𝒪_{Proj ℬ}(n)` — the unit of
`r^* ⊣ r_*` followed by `θ` — carries the global section attached to a homogeneous element `a`
of degree `n` to the one attached to `φ a`. -/
theorem twistMap_degreeSection (n : ℕ) (a : 𝒜 n) :
    ((twistMap φ hφ (n : ℤ)).val.app (op ⊤)).hom'
        ((((Scheme.Modules.pullbackPushforwardAdjunction
            (AlgebraicGeometry.Proj.map φ hφ)).unit.app
              (twistingSheaf 𝒜 (n : ℤ))).val.app (op ⊤)).hom' (degreeSection 𝒜 n a)) =
      degreeSection ℬ n ⟨φ (a : A), φ.map_mem a.2⟩ :=
  Eq.trans (congrArg (fun m => ((m : twistingSheaf 𝒜 (n : ℤ) ⟶
      (Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map φ hφ)).obj
        (twistingSheaf ℬ (n : ℤ))).val.app (op ⊤)).hom' (degreeSection 𝒜 n a))
    (unit_comp_map_twistMap φ hφ (n : ℤ))) (pushforwardTwistMap_degreeSection φ hφ n a)

end Stacks.ProjTwistComparison

namespace Stacks.ProjectiveCohomology

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

variable {R S : Type u} [CommRing R] [CommRing S] (n : ℕ)

/-- **The comparison of twisting sheaves across a change of coefficient ring is invertible**, in
every integer degree and for an arbitrary ring homomorphism `f : R →+* S`.

The condition of
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison` holds here because the
coordinate variables of `S[T₀, …, Tₙ]`, which generate its irrelevant ideal, are the images of
the coordinate variables of `R[T₀, …, Tₙ]`, homogeneous of degree one. -/
theorem isIso_polyTwistMap (f : R →+* S) (d : ℤ) :
    IsIso (Stacks.ProjTwistComparison.twistMap (polyGradedMap (Fin (n + 1)) f)
      (irrelevant_le_map_polyGradedMap (Fin (n + 1)) f) d) :=
  Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison
    (polyGrading R n) (polyGrading S n) (polyGradedMap (Fin (n + 1)) f)
    (irrelevant_le_map_polyGradedMap (Fin (n + 1)) f) d
    (Stacks.AlgebraicGeometry.TwistChartLocality.irrelevant_le_span_image_degreeOne_poly
      R S n f)

/-- **The twist transport along a change of coefficient ring**: the inverse image of `𝒪(d)` on
`ℙⁿ_R` along `Stacks.ProjectiveCohomology.projModelMap n f` is `𝒪(d)` on `ℙⁿ_S`, by the
canonical comparison of [Stacks, Tag 01MY]. -/
def projModelTwistTransport (f : R →+* S) (d : ℤ) :
    (Scheme.Modules.pullback (projModelMap n f)).obj (twistingSheaf (polyGrading R n) d) ≅
      twistingSheaf (polyGrading S n) d :=
  @asIso _ _ _ _ _ (isIso_polyTwistMap n f d)

/-- The transport is the comparison map of [Stacks, Tag 01MY], not some other isomorphism with
the same type. -/
theorem projModelTwistTransport_hom (f : R →+* S) (d : ℤ) :
    (projModelTwistTransport n f d).hom =
      Stacks.ProjTwistComparison.twistMap (polyGradedMap (Fin (n + 1)) f)
        (irrelevant_le_map_polyGradedMap (Fin (n + 1)) f) d := rfl

/-- **Base change on global sections of `𝒪(d)`.** The twist transport
along a change of coefficient ring `f : R →+* S` carries the global section of `𝒪(d)` on `ℙⁿ_R`
attached to a form `a` of degree `d` in `T₀, …, Tₙ` to the global section of `𝒪(d)` on `ℙⁿ_S`
attached to the form obtained from `a` by applying `f` to its coefficients.

Both sections are read through the unit of the pullback--pushforward adjunction, which is the
form in which a global section of a twist is compared with a global section of the inverse image
of that twist. -/
theorem projModelTwistTransport_degreeSection (f : R →+* S) (d : ℕ) (a : polyGrading R n d) :
    (((projModelTwistTransport n f (d : ℤ)).hom.val.app (op ⊤)).hom'
        ((((Scheme.Modules.pullbackPushforwardAdjunction (projModelMap n f)).unit.app
            (twistingSheaf (polyGrading R n) (d : ℤ))).val.app (op ⊤)).hom'
          (degreeSection (polyGrading R n) d a))) =
      degreeSection (polyGrading S n) d
        ⟨MvPolynomial.map f (a : MvPolynomial (Fin (n + 1)) R),
          (polyGradedMap (Fin (n + 1)) f).map_mem a.2⟩ :=
  Stacks.ProjTwistComparison.twistMap_degreeSection _ _ d a

/-- **Base change on global sections of `𝒪(d)`**, with the action of a
morphism of sheaves of modules on sections written as
`AlgebraicGeometry.Scheme.Modules.Hom.app`.

This says exactly what `Stacks.ProjectiveCohomology.projModelTwistTransport_degreeSection` says;
the two differ only in how the action on sections is spelled. -/
theorem projModelTwistTransport_app_top_degreeSection (f : R →+* S) (d : ℕ)
    (a : polyGrading R n d) :
    (projModelTwistTransport n f (d : ℤ)).hom.app ⊤
        (((Scheme.Modules.pullbackPushforwardAdjunction (projModelMap n f)).unit.app
            (twistingSheaf (polyGrading R n) (d : ℤ))).app ⊤
          (degreeSection (polyGrading R n) d a)) =
      degreeSection (polyGrading S n) d
        ⟨MvPolynomial.map f (a : MvPolynomial (Fin (n + 1)) R),
          (polyGradedMap (Fin (n + 1)) f).map_mem a.2⟩ :=
  projModelTwistTransport_degreeSection n f d a

end Stacks.ProjectiveCohomology

end
