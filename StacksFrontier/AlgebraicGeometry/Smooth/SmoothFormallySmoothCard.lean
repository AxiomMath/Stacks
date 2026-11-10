module

public import StacksFrontier.AlgebraicGeometry.Smooth.ConormalSeparated
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothGlobal

/-!
# Chart independence of the chart-local difference of two lifts

Let `f : X ⟶ S` be a morphism of schemes locally of finite presentation, let `i : T ⟶ T'` be a
first-order thickening with `T'` affine and let `a : T ⟶ X`, `h : T' ⟶ S` present a lifting problem
for `f`. Step (II) of the proof of the infinitesimal lifting criterion
[Stacks Project, Tag 02H6] compares the local solutions produced by step (I) over the members of a
standard covering of `T'`. On an overlap, two solutions differ by a derivation,
`Stacks.Smooth.liftDiffDerivation`, and
`Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation` reads that derivation as a linear map

`θ : Γ(a^*Ω_{X/S}, i ⁻¹ᵁ U') ⟶ 𝒞_{T_{U'}/T'_{U'}}`

whose source and target mention no chart — but which is *produced* from a chart `(V, W)` of `f`,
and is a priori only characterized by its defining equation in that chart.

This file proves that `θ` does not depend on the chart:
`Stacks.Smooth.liftDiffDerivation_spec_chart_independent`. That is the single statement the
implementation notes of `StacksFrontier.AlgebraicGeometry.Smooth.CechTorsorAssembly` identify as
all that stands between the available material and the Čech cocycle: the Čech differential
compares, at a triple overlap, three pairwise differences formed in the charts attached to two
different indices, and the two formed in one chart combine by
`Stacks.Smooth.liftDiffDerivation_add`, so what is left over is exactly the comparison of two
charts for one and the same pair of solutions.

## Main results

* `Stacks.Smooth.liftDiffDerivation_shrink` and `Stacks.Smooth.liftDiffDerivation_base`: the
  chart-local difference of two solutions of a lifting problem is unchanged when the chart is
  shrunk, and does not depend on the affine open of the base.
* `Stacks.Smooth.liftDiffDerivation_spec_of_shrink`: a linear map inducing the chart-local
  difference in a chart `W₃` induces it in any larger chart `W`.
* `Stacks.Smooth.conormalResLE_liftDiffDerivation`: the chart-local difference restricts along
  `Stacks.Smooth.conormalResLE` to the chart-local difference of the restricted solutions.
* `Stacks.Smooth.exists_basicOpen_refine_chart`: a covering of a basic open of `T'` by basic opens
  over each of which the two charts acquire a common affine refinement containing the image.
* `Stacks.Smooth.liftDiffDerivation_spec_chart_local`: chart independence when a common affine
  refinement exists.
* `Stacks.Smooth.conormalResLE_liftDiffDerivation_spec_chart`: chart independence over one member
  of the covering.
* `Stacks.Smooth.liftDiffDerivation_spec_chart_independent`: **chart independence.**

## Implementation notes

The proof is local-to-global. Two affine charts `W`, `W₂` of `f` both containing the image of the
restricted lifting problem may have no common affine refinement containing that whole image,
so chart independence cannot be deduced from
`Stacks.Smooth.liftDiffDerivation_spec_of_shrink` directly. What is true is that every point of
the thickening has a basic-open neighbourhood over which a common refinement exists, which is
`Stacks.Smooth.exists_basicOpen_refine_chart`; over such a member the comparison follows from
`Stacks.Smooth.liftDiffDerivation_spec_chart_local`, and the members are glued by
`Stacks.Smooth.eq_of_conormalResLE_basicOpen_eq`, the separatedness of the conormal module.

Three points of friction are worth recording.

The covering is indexed by `c * g t` rather than by `g t`, where `D(g t)` is a basic open inside
`D(c)` furnished by `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`. The two opens agree,
because `D(g t) ≤ D(c)`, but `Stacks.Smooth.homCompare_restrictₗ` asks for the image of `c` to
**divide** the image of the section cutting out the member, and `D(g t) ≤ D(c)` only gives a
radical membership. Multiplying by `c` makes the divisibility a one-line computation and changes
neither the covering nor the chart condition.

Restricting `θ` from `D(c)` to a member `D(c * g t)` is not a formal operation: a linear map out
of `Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c))` does not by itself induce one out of the sections over the smaller
open. It does here because the smaller module is a localization of the larger and the conormal
module localizes too, which is the content of
`Stacks.Smooth.homCompare_restrictₗ`; this is the only place where
`AlgebraicGeometry.LocallyOfFinitePresentation f` enters. The restricted map is obtained from that
lemma through an `∃`, rather than by writing `Stacks.Smooth.homCompare` out, so that the twenty-odd
restriction-of-scalars instances its statement carries never have to be reproduced.

Finally, the assembly is split into
`Stacks.Smooth.conormalResLE_liftDiffDerivation_spec_chart` and
`Stacks.Smooth.liftDiffDerivation_spec_chart_independent`, and the chart-local steps are written as
`Eq.trans` chains of explicit terms rather than as `rw` chains. Both are forced by the elaboration
cost: a single `rw` against the defining equation of the restricted map, or a single declaration
holding both halves of the assembly, exhausts the heartbeat budget, because every statement in
sight carries its restriction-of-scalars instances in a `letI` block.

### How the unrestricted Tag 02H6 is assembled

**Tag 02H6 is proved and tagged**, as
`Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth` in
`StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag`. The account below
names, in order, the inputs the
assembly consumes, which is the clearest description of how this file is used.

With chart independence available, the implication
`Smooth f → Stacks.Smooth.FormallySmoothScheme f` — and with it the unrestricted [Stacks Project,
Tag 02H6] — is the Čech assembly, all of whose inputs are available. Over the standard covering of
`T'` furnished by `Stacks.Smooth.exists_fin_basicOpen_chart_lift`, which covers all of `T'` and
exports a chart for each member, the pairwise differences of the local solutions are a family of
elements of the localizations of the `Γ(T, ⊤)`-module `Γ(a^*Ω_{X/S}, ⊤) →ₗ[Γ(T, ⊤)] 𝒞_{T/T'}`
identified by `Stacks.Smooth.isLocalizedModule_homLoc_basicOpen`, whose Čech restriction maps are
restriction of sections by `Stacks.Smooth.homCompare_restrictₗ` and `Stacks.Smooth.homCompare_iso`.
The cocycle identity at a triple overlap is `Stacks.Smooth.liftDiffDerivation_add` once
all three differences have been moved into one chart, which is
`Stacks.Smooth.liftDiffDerivation_spec_chart_independent` here together with
`Stacks.Smooth.le_preimage_of_lift`. Then `Stacks.RingTheory.CechAcyclicity.cech_exact` at `p = 0`
produces a 0-cochain, the `∃!` of `Stacks.Smooth.existsUnique_linearMap_of_leibniz_opensTop`
converts each of its components back into a derivation in the chart of its member,
`Stacks.Smooth.exists_lift_of_derivation` corrects the local solutions by those derivations,
`Stacks.Smooth.eq_of_liftDiffDerivation_eq_zero` shows the corrected solutions agree on the
overlaps and `Stacks.Smooth.exists_lift_of_isOpenCover` glues them.

## References

* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
* [Stacks Project, Tag 02H6](https://stacks.math.columbia.edu/tag/02H6)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.Smooth

/-- **The chart-local difference of two lifts does not change when the chart is shrunk.** Let
`W₃ ≤ W` be two charts of `f` over one affine open `V` of `S`, and let `b₁`, `b₂` be two solutions
of a lifting problem, both mapping into `W₃`. The difference derivation formed in the chart `W₃`,
evaluated at the restriction of a section `x` of `𝒪_X` over `W`, is the difference derivation
formed in the chart `W`, evaluated at `x`.

Both sides are elements of the conormal module, which does not mention the chart, so this is an
honest equation; by `Stacks.Smooth.liftDiffDerivation_apply` it is the compatibility
`AlgebraicGeometry.Scheme.Hom.map_appLE` of `AlgebraicGeometry.Scheme.Hom.appLE` with restriction
of sections. -/
theorem liftDiffDerivation_shrink {X S T T' : Scheme.{u}} (f : X ⟶ S) {V : S.Opens}
    {W W₃ : X.Opens} [IsAffine T'] {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i)
    {a : T ⟶ X} {h : T' ⟶ S} {b₁ b₂ : T' ⟶ X}
    (hWV : W ≤ f ⁻¹ᵁ V) (hW₃V : W₃ ≤ f ⁻¹ᵁ V)
    (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W) (hUW₃ : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W₃)
    (hV' : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ V) (hW₃W : W₃ ≤ W) (hcomm : a ≫ f = i ≫ h)
    (hb₁f : b₁ ≫ f = h) (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a) (hb₂a : i ≫ b₂ = a)
    (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W)
    (hb₁₃ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W₃) (hb₂₃ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W₃) (x : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE f hW₃V
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLE a hUW₃ (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hW₃V hUW₃ (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hW₃V hUW₃ (RingHom.ker i.appTop.hom)
    (liftDiffDerivation f hi hW₃V hUW₃ hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁₃ hb₂₃
        ((X.presheaf.map (homOfLE hW₃W).op).hom x) : RingHom.ker i.appTop.hom)
      = liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x := by
  let := algebraAppLE f hWV
  let := algebraAppLE f hW₃V
  let := thickeningKerModule hi
  let := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLE a hUW₃ (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hW₃V hUW₃ (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hW₃V hUW₃ (RingHom.ker i.appTop.hom)
  refine Subtype.ext ?_
  rw [liftDiffDerivation_apply, liftDiffDerivation_apply, ← CommRingCat.comp_apply,
    ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.map_appLE]

section ShrinkSpec

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {W W₃ : X.Opens} [IsAffine T']
  {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}

omit [IsAffine T'] in
/-- **A solution of the corepresentability problem for a chart solves it for every larger chart.**
Let `U'` be an affine open of `T'` and let `W₃ ≤ W` be two charts of `f` over one affine open `V`
of `S`, both containing the image of the lifting problem restricted to `U'`. A
`Γ(T, i ⁻¹ᵁ U')`-linear map out of `Γ(a^*Ω_{X/S}, i ⁻¹ᵁ U')` inducing the chart-local difference of
two solutions in the chart `W₃` also induces it in the chart `W`.

The two ingredients are `Stacks.Smooth.pullbackD_shrink`, which rewrites a `W`-generator of
`Γ(a^*Ω_{X/S}, i ⁻¹ᵁ U')` as a `W₃`-generator, and `Stacks.Smooth.liftDiffDerivation_shrink`,
which matches the two values of the difference derivation. Together with the uniqueness clause of
`Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation` this is what makes two charts with
a common affine refinement produce the same map. -/
theorem liftDiffDerivation_spec_of_shrink {U' : T'.Opens} [IsAffine (U' : Scheme.{u})]
    (hW₃W : W₃ ≤ W) (hWV : W ≤ f ⁻¹ᵁ V) (hW₃V : W₃ ≤ f ⁻¹ᵁ V)
    (hUW : i ⁻¹ᵁ U' ≤ a ⁻¹ᵁ W) (hUW₃ : i ⁻¹ᵁ U' ≤ a ⁻¹ᵁ W₃)
    (hUWt : (⊤ : ((i ⁻¹ᵁ U' : T.Opens) : Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ U').ι ≫ a) ⁻¹ᵁ W)
    (hUWt₃ : (⊤ : ((i ⁻¹ᵁ U' : T.Opens) : Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ U').ι ≫ a) ⁻¹ᵁ W₃)
    (hV' : (⊤ : (U' : Scheme.{u}).Opens) ≤ (U'.ι ≫ h) ⁻¹ᵁ V)
    (hcomm : ((i ⁻¹ᵁ U').ι ≫ a) ≫ f = (i ∣_ U') ≫ (U'.ι ≫ h))
    {b₁ b₂ : (U' : Scheme.{u}) ⟶ X} (hb₁f : b₁ ≫ f = U'.ι ≫ h) (hb₂f : b₂ ≫ f = U'.ι ≫ h)
    (hb₁a : (i ∣_ U') ≫ b₁ = (i ⁻¹ᵁ U').ι ≫ a) (hb₂a : (i ∣_ U') ≫ b₂ = (i ⁻¹ᵁ U').ι ≫ a)
    (hb₁ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₂ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W)
    (hb₁₃ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W₃)
    (hb₂₃ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W₃)
    (θ : letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
      letI := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
      Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ U') →ₗ[Γ(T, i ⁻¹ᵁ U')]
        RingHom.ker (i ∣_ U').appTop.hom)
    (hθ : letI := algebraAppLE f hW₃V
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
      letI := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt₃ (RingHom.ker (i ∣_ U').appTop.hom)
      letI := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hW₃V hUWt₃
        (RingHom.ker (i ∣_ U').appTop.hom)
      letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hW₃V hUWt₃
        (RingHom.ker (i ∣_ U').appTop.hom)
      letI := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
      ∀ b : Γ(X, W₃), θ (pullbackD f a W₃ hUW₃ b) =
        liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U') hW₃V hUWt₃ hV'
          hcomm hb₁f hb₂f hb₁a hb₂a hb₁₃ hb₂₃ b)
    (b : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
    letI := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt (RingHom.ker (i ∣_ U').appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt
      (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
    θ (pullbackD f a W hUW b) =
      liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U') hWV hUWt hV'
        hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ b := by
  let := algebraAppLE f hWV
  let := algebraAppLE f hW₃V
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
  let := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt₃ (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hW₃V hUWt₃ (RingHom.ker (i ∣_ U').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hW₃V hUWt₃
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
  rw [← pullbackD_shrink f a hW₃W hUW hUW₃ b, hθ]
  exact liftDiffDerivation_shrink f (isFirstOrderThickening_morphismRestrict hi U') hWV hW₃V
    hUWt hUWt₃ hV' hW₃W hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ hb₁₃ hb₂₃ b

end ShrinkSpec


/-- **The chart-local difference of two lifts does not depend on the affine open of the base.**
The difference derivation of two solutions of a lifting problem in a chart `W` lying over two
different affine opens `V` and `V₂` of `S` has the same values, both sides being elements of the
conormal module. This is immediate from `Stacks.Smooth.liftDiffDerivation_apply`, which does not
mention `V`; it is needed because the *type* of the derivation does mention `V`. -/
theorem liftDiffDerivation_base {X S T T' : Scheme.{u}} (f : X ⟶ S) {V V₂ : S.Opens}
    {W : X.Opens} [IsAffine T'] {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i)
    {a : T ⟶ X} {h : T' ⟶ S} {b₁ b₂ : T' ⟶ X}
    (hWV : W ≤ f ⁻¹ᵁ V) (hWV₂ : W ≤ f ⁻¹ᵁ V₂) (hUW : (⊤ : T.Opens) ≤ a ⁻¹ᵁ W)
    (hV' : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ V) (hV'₂ : (⊤ : T'.Opens) ≤ h ⁻¹ᵁ V₂)
    (hcomm : a ≫ f = i ≫ h) (hb₁f : b₁ ≫ f = h) (hb₂f : b₂ ≫ f = h) (hb₁a : i ≫ b₁ = a)
    (hb₂a : i ≫ b₂ = a) (hb₁ : (⊤ : T'.Opens) ≤ b₁ ⁻¹ᵁ W) (hb₂ : (⊤ : T'.Opens) ≤ b₂ ⁻¹ᵁ W)
    (x : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := algebraAppLE f hWV₂
    letI := thickeningKerModule hi
    letI := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := moduleOfAppLEBase f a hWV₂ hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
    letI := isScalarTowerOfAppLEBase f a hWV₂ hUW (RingHom.ker i.appTop.hom)
    (liftDiffDerivation f hi hWV hUW hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x :
        RingHom.ker i.appTop.hom)
      = liftDiffDerivation f hi hWV₂ hUW hV'₂ hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x := by
  let := algebraAppLE f hWV
  let := algebraAppLE f hWV₂
  let := thickeningKerModule hi
  let := moduleOfAppLE a hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := moduleOfAppLEBase f a hWV₂ hUW (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hWV hUW (RingHom.ker i.appTop.hom)
  let := isScalarTowerOfAppLEBase f a hWV₂ hUW (RingHom.ker i.appTop.hom)
  exact Subtype.ext (by rw [liftDiffDerivation_apply, liftDiffDerivation_apply])


variable {X S T T' : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {W : X.Opens} [IsAffine T']
  {i : T ⟶ T'} (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}

/-- **The chart-local difference of two lifts restricts to a smaller open of the thickening.**
Let `U'' ≤ U'` be affine opens of `T'` and let `b₁`, `b₂` solve the lifting problem restricted to
`U'`, both mapping into the chart `W`. Restricting the difference derivation of `b₁` and `b₂`
along `Stacks.Smooth.conormalResLE` gives the difference derivation of the two restricted
solutions over `U''`.

By `Stacks.Smooth.liftDiffDerivation_apply` and `Stacks.Smooth.conormalResLE_apply` this is the
compatibility `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE` of
`AlgebraicGeometry.Scheme.Hom.appLE` with composition, in the form
`Stacks.Smooth.appLE_top_top`. -/
theorem conormalResLE_liftDiffDerivation {U' U'' : T'.Opens} [IsAffine (U' : Scheme.{u})]
    [IsAffine (U'' : Scheme.{u})] (hle : U'' ≤ U') (hWV : W ≤ f ⁻¹ᵁ V)
    (hUW : (⊤ : ((i ⁻¹ᵁ U' : T.Opens) : Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ U').ι ≫ a) ⁻¹ᵁ W)
    (hUW'' : (⊤ : ((i ⁻¹ᵁ U'' : T.Opens) : Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ U'').ι ≫ a) ⁻¹ᵁ W)
    (hV' : (⊤ : (U' : Scheme.{u}).Opens) ≤ (U'.ι ≫ h) ⁻¹ᵁ V)
    (hV'' : (⊤ : (U'' : Scheme.{u}).Opens) ≤ (U''.ι ≫ h) ⁻¹ᵁ V)
    (hcomm : ((i ⁻¹ᵁ U').ι ≫ a) ≫ f = (i ∣_ U') ≫ (U'.ι ≫ h))
    (hcomm'' : ((i ⁻¹ᵁ U'').ι ≫ a) ≫ f = (i ∣_ U'') ≫ (U''.ι ≫ h))
    {b₁ b₂ : (U' : Scheme.{u}) ⟶ X} (hb₁f : b₁ ≫ f = U'.ι ≫ h) (hb₂f : b₂ ≫ f = U'.ι ≫ h)
    (hb₁a : (i ∣_ U') ≫ b₁ = (i ⁻¹ᵁ U').ι ≫ a) (hb₂a : (i ∣_ U') ≫ b₂ = (i ⁻¹ᵁ U').ι ≫ a)
    (hb₁ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₂ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W)
    (hb₁f'' : (T'.homOfLE hle ≫ b₁) ≫ f = U''.ι ≫ h)
    (hb₂f'' : (T'.homOfLE hle ≫ b₂) ≫ f = U''.ι ≫ h)
    (hb₁a'' : (i ∣_ U'') ≫ (T'.homOfLE hle ≫ b₁) = (i ⁻¹ᵁ U'').ι ≫ a)
    (hb₂a'' : (i ∣_ U'') ≫ (T'.homOfLE hle ≫ b₂) = (i ⁻¹ᵁ U'').ι ≫ a)
    (hb₁'' : (⊤ : (U'' : Scheme.{u}).Opens) ≤ (T'.homOfLE hle ≫ b₁) ⁻¹ᵁ W)
    (hb₂'' : (⊤ : (U'' : Scheme.{u}).Opens) ≤ (T'.homOfLE hle ≫ b₂) ⁻¹ᵁ W) (x : Γ(X, W)) :
    letI := algebraAppLE f hWV
    letI := isAffine_preimage_of_isAffine hi U'
    letI := isAffine_preimage_of_isAffine hi U''
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U'')
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfOpensAppTop (i ⁻¹ᵁ U'') (RingHom.ker (i ∣_ U'').appTop.hom)
    letI := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUW (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfAppLE ((i ⁻¹ᵁ U'').ι ≫ a) hUW'' (RingHom.ker (i ∣_ U'').appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUW (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ U'').ι ≫ a) hWV hUW'' (RingHom.ker (i ∣_ U'').appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUW
      (RingHom.ker (i ∣_ U').appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U'').ι ≫ a) hWV hUW''
      (RingHom.ker (i ∣_ U'').appTop.hom)
    conormalResLE hi hle
        (liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U') hWV hUW hV'
          hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ x)
      = liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U'') hWV hUW'' hV''
          hcomm'' hb₁f'' hb₂f'' hb₁a'' hb₂a'' hb₁'' hb₂'' x := by
  let := algebraAppLE f hWV
  let := isAffine_preimage_of_isAffine hi U'
  let := isAffine_preimage_of_isAffine hi U''
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U'')
  let := moduleOfOpensAppTop (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfOpensAppTop (i ⁻¹ᵁ U'') (RingHom.ker (i ∣_ U'').appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUW (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ U'').ι ≫ a) hUW'' (RingHom.ker (i ∣_ U'').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUW (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U'').ι ≫ a) hWV hUW'' (RingHom.ker (i ∣_ U'').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUW
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U'').ι ≫ a) hWV hUW''
    (RingHom.ker (i ∣_ U'').appTop.hom)
  have key : ∀ (b : (U' : Scheme.{u}) ⟶ X) (hb : (⊤ : (U' : Scheme.{u}).Opens) ≤ b ⁻¹ᵁ W)
      (hb'' : (⊤ : (U'' : Scheme.{u}).Opens) ≤ (T'.homOfLE hle ≫ b) ⁻¹ᵁ W),
      (T'.homOfLE hle).appTop.hom ((b.appLE W ⊤ hb).hom x)
        = ((T'.homOfLE hle ≫ b).appLE W ⊤ hb'').hom x := by
    intro b hb hb''
    have e : b.appLE W ⊤ hb ≫ (T'.homOfLE hle).appLE ⊤ ⊤ le_top
        = (T'.homOfLE hle ≫ b).appLE W ⊤ hb'' :=
      Scheme.Hom.appLE_comp_appLE (T'.homOfLE hle) b W ⊤ ⊤ hb le_top
    rw [← appLE_top_top (T'.homOfLE hle), ← CommRingCat.comp_apply, e]
  refine Subtype.ext ?_
  rw [conormalResLE_apply, liftDiffDerivation_apply, liftDiffDerivation_apply, map_sub,
    key b₁ hb₁ hb₁'', key b₂ hb₂ hb₂'']


/-- **A solution of a lifting problem over a basic open is locally carried into a common affine
refinement of two charts.** Let `T'` be affine, `c` a global section of `𝒪_{T'}` and
`b₁ : D(c) ⟶ X` a morphism mapping `D(c)` into two opens `W` and `W₂` of `X` at once. Then there
are global sections `g t` of `𝒪_{T'}`, indexed by the points `t` of `D(c)`, and affine opens
`W₃ t ≤ W ⊓ W₂`, such that the basic opens `D(c * g t)` lie in `D(c)`, cover it, and are carried
by `b₁` into `W₃ t`.

The index `c * g t` rather than `g t` is what makes the covering subordinate to `D(c)` *and*
divisible by `c` in `Γ(T', ⊤)`, which is the hypothesis `hd` of
`Stacks.Smooth.homCompare_restrictₗ`; the two basic opens agree, `D(c * g t) = D(c) ⊓ D(g t)`, by
`AlgebraicGeometry.Scheme.basicOpen_mul`. The charts come from
`AlgebraicGeometry.exists_isAffineOpen_mem_and_subset` and the covering from
`Stacks.Smooth.exists_basicOpen_le_cover`. -/
theorem exists_basicOpen_refine_chart {X T' : Scheme.{u}} [IsAffine T']
    (c : Γ(T', (⊤ : T'.Opens))) {W W₂ : X.Opens}
    {b₁ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}) ⟶ X}
    (hb₁ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₁₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W₂) :
    ∃ (g : ↥(T'.basicOpen c) → Γ(T', (⊤ : T'.Opens))) (W₃ : ↥(T'.basicOpen c) → X.Opens),
      T'.basicOpen c ≤ ⨆ t, T'.basicOpen (c * g t) ∧
      ∀ t, T'.basicOpen (c * g t) ≤ T'.basicOpen c ∧ IsAffineOpen (W₃ t) ∧
        W₃ t ≤ W ∧ W₃ t ≤ W₂ ∧
        ∀ hle : T'.basicOpen (c * g t) ≤ T'.basicOpen c,
          (⊤ : ((T'.basicOpen (c * g t) : T'.Opens) : Scheme.{u}).Opens) ≤
            (T'.homOfLE hle ≫ b₁) ⁻¹ᵁ W₃ t := by
  have hex : ∀ t : ↥(T'.basicOpen c),
      ∃ O : X.Opens, IsAffineOpen O ∧ b₁.base t ∈ O ∧ O ≤ W ⊓ W₂ := fun t ↦
    exists_isAffineOpen_mem_and_subset (U := W ⊓ W₂) (x := b₁.base t)
      ⟨hb₁ (Set.mem_univ t), hb₁₂ (Set.mem_univ t)⟩
  choose W₃ hW₃aff hW₃mem hW₃le using hex
  obtain ⟨g, hg₁, hg₂⟩ := exists_basicOpen_le_cover (T'.basicOpen c)
    (fun t ↦ (T'.basicOpen c).ι ''ᵁ (b₁ ⁻¹ᵁ W₃ t)) (fun t ↦ ⟨t, hW₃mem t, rfl⟩)
  have hmul : ∀ t, T'.basicOpen (c * g t) ≤ T'.basicOpen c := fun t ↦ by
    rw [Scheme.basicOpen_mul]; exact inf_le_left
  refine ⟨g, W₃, fun x hx ↦ ?_, fun t ↦ ⟨hmul t, hW₃aff t, (hW₃le t).trans inf_le_left,
    (hW₃le t).trans inf_le_right, fun hle x _ ↦ ?_⟩⟩
  · obtain ⟨t, ht⟩ := TopologicalSpace.Opens.mem_iSup.mp (hg₂ hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨t, by rw [Scheme.basicOpen_mul]; exact ⟨hx, ht⟩⟩
  · have hmul' : T'.basicOpen (c * g t) ≤ T'.basicOpen (g t) := by
      rw [Scheme.basicOpen_mul]; exact inf_le_right
    obtain ⟨y, hy, hyx⟩ := hg₁ t (hmul' x.2)
    change b₁.base ((T'.homOfLE hle).base x) ∈ W₃ t
    have hbx : (T'.homOfLE hle).base x = y :=
      Subtype.ext ((Scheme.homOfLE_apply hle x).trans hyx.symm)
    rw [hbx]
    exact hy


section Local

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) [IsAffine T'] {i : T ⟶ T'}
  (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}
  {U' : T'.Opens} [IsAffine (U' : Scheme.{u})] {V V₂ : S.Opens} {W W₂ W₃ : X.Opens}
  {b₁ b₂ : (U' : Scheme.{u}) ⟶ X}

omit [IsAffine T'] in
/-- **Chart independence in the presence of a common affine refinement.** Let `U'` be an affine
open of `T'`, let `W`, `W₂` be charts of `f` over the affine opens `V`, `V₂` of `S` and let `W₃`
be an affine open contained in both, all three containing the image of the lifting problem
restricted to `U'`. A `Γ(T, i ⁻¹ᵁ U')`-linear map inducing the chart-local difference of two
solutions in the chart `W` also induces it in the chart `W₂`.

This is the chart-independence statement in the case where a common refinement exists. Its proof
is the solution `θ₃` of the corepresentability problem for the chart `W₃`, supplied by
`Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation`: by
`Stacks.Smooth.liftDiffDerivation_spec_of_shrink` it solves the problem for `W` as well, hence
agrees with the given map by `Stacks.Smooth.hom_ext_pullbackD`, and by the same shrinking lemma —
after `Stacks.Smooth.liftDiffDerivation_base` has moved its defining equation from the base `V` to
the base `V₂` — it solves the problem for `W₂`. -/
theorem liftDiffDerivation_spec_chart_local (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hW₃ : IsAffineOpen W₃) (hWV : W ≤ f ⁻¹ᵁ V) (hW₂V₂ : W₂ ≤ f ⁻¹ᵁ V₂)
    (hW₃W : W₃ ≤ W) (hW₃W₂ : W₃ ≤ W₂)
    (hUW : i ⁻¹ᵁ U' ≤ a ⁻¹ᵁ W) (hUW₂ : i ⁻¹ᵁ U' ≤ a ⁻¹ᵁ W₂) (hUW₃ : i ⁻¹ᵁ U' ≤ a ⁻¹ᵁ W₃)
    (hUWt : (⊤ : ((i ⁻¹ᵁ U' : T.Opens) : Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ U').ι ≫ a) ⁻¹ᵁ W)
    (hUWt₂ : (⊤ : ((i ⁻¹ᵁ U' : T.Opens) : Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ U').ι ≫ a) ⁻¹ᵁ W₂)
    (hUWt₃ : (⊤ : ((i ⁻¹ᵁ U' : T.Opens) : Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ U').ι ≫ a) ⁻¹ᵁ W₃)
    (hV' : (⊤ : (U' : Scheme.{u}).Opens) ≤ (U'.ι ≫ h) ⁻¹ᵁ V)
    (hV'₂ : (⊤ : (U' : Scheme.{u}).Opens) ≤ (U'.ι ≫ h) ⁻¹ᵁ V₂)
    (hcomm : ((i ⁻¹ᵁ U').ι ≫ a) ≫ f = (i ∣_ U') ≫ (U'.ι ≫ h))
    (hb₁f : b₁ ≫ f = U'.ι ≫ h) (hb₂f : b₂ ≫ f = U'.ι ≫ h)
    (hb₁a : (i ∣_ U') ≫ b₁ = (i ⁻¹ᵁ U').ι ≫ a) (hb₂a : (i ∣_ U') ≫ b₂ = (i ⁻¹ᵁ U').ι ≫ a)
    (hb₁ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₂ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W)
    (hb₁₂ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W₂)
    (hb₂₂ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W₂)
    (hb₁₃ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W₃)
    (hb₂₃ : (⊤ : (U' : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W₃)
    (θ : letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
      letI := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
      Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ U') →ₗ[Γ(T, i ⁻¹ᵁ U')]
        RingHom.ker (i ∣_ U').appTop.hom)
    (hθ : letI := algebraAppLE f hWV
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
      letI := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt (RingHom.ker (i ∣_ U').appTop.hom)
      letI := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt
        (RingHom.ker (i ∣_ U').appTop.hom)
      letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt
        (RingHom.ker (i ∣_ U').appTop.hom)
      letI := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
      ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) =
        liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U') hWV hUWt hV'
          hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ b) :
    letI := algebraAppLE f hW₂V₂
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
    letI := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt₂ (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hW₂V₂ hUWt₂
      (RingHom.ker (i ∣_ U').appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hW₂V₂ hUWt₂
      (RingHom.ker (i ∣_ U').appTop.hom)
    letI := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
    ∀ b : Γ(X, W₂), θ (pullbackD f a W₂ hUW₂ b) =
      liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U') hW₂V₂ hUWt₂ hV'₂
        hcomm hb₁f hb₂f hb₁a hb₂a hb₁₂ hb₂₂ b := by
  let := algebraAppLE f hWV
  let := algebraAppLE f hW₂V₂
  let := algebraAppLE f (hW₃W.trans hWV)
  let := algebraAppLE f (hW₃W₂.trans hW₂V₂)
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi U')
  let := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt₂ (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ U').ι ≫ a) hUWt₃ (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hW₂V₂ hUWt₂ (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) (hW₃W.trans hWV) hUWt₃
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) (hW₃W₂.trans hW₂V₂) hUWt₃
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hWV hUWt
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) hW₂V₂ hUWt₂
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) (hW₃W.trans hWV) hUWt₃
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ U').ι ≫ a) (hW₃W₂.trans hW₂V₂) hUWt₃
    (RingHom.ker (i ∣_ U').appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ U') (RingHom.ker (i ∣_ U').appTop.hom)
  obtain ⟨θ₃, hθ₃, -⟩ := existsUnique_linearMap_liftDiffDerivation f hi
    (isAffine_preimage_of_isAffine hi U') hV hW₃ (hW₃W.trans hWV) hUW₃ hUWt₃ hV' hcomm
    hb₁f hb₂f hb₁a hb₂a hb₁₃ hb₂₃
  have hθ₃W := liftDiffDerivation_spec_of_shrink f hi hW₃W hWV (hW₃W.trans hWV) hUW hUW₃
    hUWt hUWt₃ hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ hb₁₃ hb₂₃ θ₃ hθ₃
  have hθθ₃ : θ = θ₃ :=
    hom_ext_pullbackD f a (isAffine_preimage_of_isAffine hi U') hV hW hWV hUW _
      (fun b ↦ (hθ b).trans (hθ₃W b).symm)
  have hθ₃' : ∀ b : Γ(X, W₃), θ₃ (pullbackD f a W₃ hUW₃ b) =
      liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi U')
        (hW₃W₂.trans hW₂V₂) hUWt₃ hV'₂ hcomm hb₁f hb₂f hb₁a hb₂a hb₁₃ hb₂₃ b := fun b ↦
    (hθ₃ b).trans (liftDiffDerivation_base f (isFirstOrderThickening_morphismRestrict hi U')
      (hW₃W.trans hWV) (hW₃W₂.trans hW₂V₂) hUWt₃ hV' hV'₂ hcomm hb₁f hb₂f hb₁a hb₂a
      hb₁₃ hb₂₃ b)
  intro b
  rw [hθθ₃]
  exact liftDiffDerivation_spec_of_shrink f hi hW₃W₂ hW₂V₂ (hW₃W₂.trans hW₂V₂) hUW₂ hUW₃
    hUWt₂ hUWt₃ hV'₂ hcomm hb₁f hb₂f hb₁a hb₂a hb₁₂ hb₂₂ hb₁₃ hb₂₃ θ₃ hθ₃' b


end Local

section Independence

variable {X S T T' : Scheme.{u}} (f : X ⟶ S) [IsAffine T'] {i : T ⟶ T'}
  (hi : Thickenings.IsFirstOrderThickening i) {a : T ⟶ X} {h : T' ⟶ S}
  {V V₂ : S.Opens} {W W₂ : X.Opens}

/-- **Chart independence over one member of the covering.** Let `D(c') ≤ D(c)` be basic opens of
the affine scheme `T'` with the image of `c` dividing the image of `c'` in `Γ(T, ⊤)`, let `W`,
`W₂` be charts of `f` and `W₃` an affine open contained in both, and let `b₁`, `b₂` solve the
lifting problem restricted to `D(c)`, with `b₁` carrying `D(c')` into `W₃`. If a
`Γ(T, i ⁻¹ᵁ D(c))`-linear map `θ` induces the chart-local difference of `b₁` and `b₂` in the chart
`W`, then its difference from the chart-local difference in the chart `W₂` dies on restriction to
`D(c')`.

This is the local half of `Stacks.Smooth.liftDiffDerivation_spec_chart_independent`. The
restriction of `θ` to `D(c')` exists because `Stacks.Smooth.homCompare_restrictₗ` extends `θ`
across the localization — this is the one place where `LocallyOfFinitePresentation f` is used —
and `Stacks.Smooth.conormalResLE_liftDiffDerivation` identifies the restriction of the difference
derivations, so the restricted map induces the chart-local difference over `D(c')` in the chart
`W` and therefore, by `Stacks.Smooth.liftDiffDerivation_spec_chart_local`, in the chart `W₂`. -/
theorem conormalResLE_liftDiffDerivation_spec_chart [LocallyOfFinitePresentation f]
    (c c' : Γ(T', (⊤ : T'.Opens))) (hcc' : T'.basicOpen c' ≤ T'.basicOpen c)
    (hd : i.appTop.hom c ∣ i.appTop.hom c') {W₃ : X.Opens} (hW₃aff : IsAffineOpen W₃)
    (hW₃W : W₃ ≤ W) (hW₃W₂ : W₃ ≤ W₂) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hW₂V₂ : W₂ ≤ f ⁻¹ᵁ V₂)
    (hUW : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W) (hUW₂ : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W₂)
    (hUWt : (⊤ : ((i ⁻¹ᵁ T'.basicOpen c : T.Opens) : Scheme.{u}).Opens) ≤
      ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ⁻¹ᵁ W)
    (hUWt₂ : (⊤ : ((i ⁻¹ᵁ T'.basicOpen c : T.Opens) : Scheme.{u}).Opens) ≤
      ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ⁻¹ᵁ W₂)
    (hV' : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen c).ι ≫ h) ⁻¹ᵁ V)
    (hV'₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen c).ι ≫ h) ⁻¹ᵁ V₂)
    (hcomm : ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ≫ f
      = (i ∣_ T'.basicOpen c) ≫ ((T'.basicOpen c).ι ≫ h))
    {b₁ b₂ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}) ⟶ X}
    (hb₁f : b₁ ≫ f = (T'.basicOpen c).ι ≫ h) (hb₂f : b₂ ≫ f = (T'.basicOpen c).ι ≫ h)
    (hb₁a : (i ∣_ T'.basicOpen c) ≫ b₁ = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a)
    (hb₂a : (i ∣_ T'.basicOpen c) ≫ b₂ = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a)
    (hb₁ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W)
    (hb₁₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W₂)
    (hb₂₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W₂)
    (hb₁₃' : letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c'
      (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens) ≤
        (T'.homOfLE hcc' ≫ b₁) ⁻¹ᵁ W₃)
    (θ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c) →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c)]
        RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    (hθ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI := algebraAppLE f hWV
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
      letI := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) =
        liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
          hWV hUWt hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ b) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI := algebraAppLE f hW₂V₂
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt₂
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hW₂V₂ hUWt₂
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hW₂V₂ hUWt₂
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c'
    ∀ b : Γ(X, W₂), conormalResLE hi hcc' (θ (pullbackD f a W₂ hUW₂ b)) =
      conormalResLE hi hcc'
        (liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
          hW₂V₂ hUWt₂ hV'₂ hcomm hb₁f hb₂f hb₁a hb₂a hb₁₂ hb₂₂ b) := by
  have : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
    (isAffineOpen_top T').basicOpen c
  let := algebraAppLE f hWV
  let := algebraAppLE f hW₂V₂
  let := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
  let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt₂
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hW₂V₂ hUWt₂
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hW₂V₂ hUWt₂
    (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c) (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
  intro b
  have : IsAffine ((T'.basicOpen c' : T'.Opens) : Scheme.{u}) :=
    (isAffineOpen_top T').basicOpen c'
  have hpre : i ⁻¹ᵁ T'.basicOpen c' ≤ i ⁻¹ᵁ T'.basicOpen c := fun _ hx ↦ hcc' hx
  have hsurj : Function.Surjective (i ∣_ T'.basicOpen c').base :=
    (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c')).isThickening.2
  have hbf : ∀ b : ((T'.basicOpen c : T'.Opens) : Scheme.{u}) ⟶ X,
      b ≫ f = (T'.basicOpen c).ι ≫ h → (T'.homOfLE hcc' ≫ b) ≫ f = (T'.basicOpen c').ι ≫ h :=
    fun b hbf ↦ by rw [Category.assoc, hbf, ← Category.assoc, Scheme.homOfLE_ι]
  have hba : ∀ b : ((T'.basicOpen c : T'.Opens) : Scheme.{u}) ⟶ X,
      (i ∣_ T'.basicOpen c) ≫ b = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a →
        (i ∣_ T'.basicOpen c') ≫ (T'.homOfLE hcc' ≫ b) = (i ⁻¹ᵁ T'.basicOpen c').ι ≫ a :=
    fun b hba ↦ by
      rw [← Category.assoc, morphismRestrict_comp_homOfLE, Category.assoc, hba, ← Category.assoc,
        Scheme.homOfLE_ι]
  have hbW : ∀ (b : ((T'.basicOpen c : T'.Opens) : Scheme.{u}) ⟶ X) (W' : X.Opens),
      (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b ⁻¹ᵁ W' →
        (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens) ≤ (T'.homOfLE hcc' ≫ b) ⁻¹ᵁ W' :=
    fun b W' hb x _ ↦ hb (Set.mem_univ _)
  have hb₁f'' := hbf b₁ hb₁f
  have hb₂f'' := hbf b₂ hb₂f
  have hb₁a'' := hba b₁ hb₁a
  have hb₂a'' := hba b₂ hb₂a
  have hb₁'' := hbW b₁ W hb₁
  have hb₂'' := hbW b₂ W hb₂
  have hb₁₂'' := hbW b₁ W₂ hb₁₂
  have hb₂₂'' := hbW b₂ W₂ hb₂₂
  have hb₁₃'' := hb₁₃'
  have hb₂₃'' : (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens)
      ≤ (T'.homOfLE hcc' ≫ b₂) ⁻¹ᵁ W₃ :=
    le_preimage_of_lift hsurj hb₁a'' hb₂a'' hb₁₃''
  have hV''' : ∀ V' : S.Opens, (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen c).ι ≫ h) ⁻¹ᵁ V' →
        (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens) ≤
          ((T'.basicOpen c').ι ≫ h) ⁻¹ᵁ V' :=
    fun V' hV' x _ ↦
      hV' (Set.mem_univ (⟨x.1, hcc' x.2⟩ : ((T'.basicOpen c : T'.Opens) : Scheme.{u})))
  have hV'' := hV''' V hV'
  have hV''₂ := hV''' V₂ hV'₂
  have hcomm'' : ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) ≫ f
      = (i ∣_ T'.basicOpen c') ≫ ((T'.basicOpen c').ι ≫ h) := by
    rw [← hb₁f'', ← Category.assoc, hb₁a'']
  have hUWt''' : ∀ W' : X.Opens, (⊤ : ((T'.basicOpen c' : T'.Opens) : Scheme.{u}).Opens)
      ≤ (T'.homOfLE hcc' ≫ b₁) ⁻¹ᵁ W' → (⊤ : ((i ⁻¹ᵁ T'.basicOpen c' : T.Opens) :
        Scheme.{u}).Opens) ≤ ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) ⁻¹ᵁ W' :=
    fun W' hb x _ ↦ by
      rw [← hb₁a'']
      exact hb (Set.mem_univ _)
  have hUWt'' := hUWt''' W hb₁''
  have hUWt₂'' := hUWt''' W₂ hb₁₂''
  have hUWt₃'' := hUWt''' W₃ hb₁₃''
  have hUW'' : i ⁻¹ᵁ T'.basicOpen c' ≤ a ⁻¹ᵁ W := fun x hx ↦ hUW (hcc' hx)
  have hUW₂'' : i ⁻¹ᵁ T'.basicOpen c' ≤ a ⁻¹ᵁ W₂ := fun x hx ↦ hUW₂ (hcc' hx)
  have hUW₃'' : i ⁻¹ᵁ T'.basicOpen c' ≤ a ⁻¹ᵁ W₃ := fun x hx ↦
    hUWt₃'' (Set.mem_univ (⟨x, hx⟩ : ((i ⁻¹ᵁ T'.basicOpen c' : T.Opens) : Scheme.{u})))
  let := thickeningKerModule
    (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c'))
  let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hUWt''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hUWt₂''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hWV hUWt''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hW₂V₂ hUWt₂''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hWV hUWt''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c').ι ≫ a) hW₂V₂ hUWt₂''
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  let := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c')
    (RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom)
  have hres : ∀ (W' : X.Opens) (e : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W')
      (e' : i ⁻¹ᵁ T'.basicOpen c' ≤ a ⁻¹ᵁ W') (y : Γ(X, W')),
      restrictₗ (pullbackCotangentSheaf f a) hpre (pullbackD f a W' e y)
        = pullbackD f a W' e' y := fun W' e e' y ↦ map_pullbackD f a W' e e' hpre y
  obtain ⟨θ'', hθ''⟩ : ∃ ψ : Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c')
      →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c')]
        RingHom.ker (i ∣_ T'.basicOpen c').appTop.hom,
      ∀ y, ψ (restrictₗ (pullbackCotangentSheaf f a) hpre y) = conormalResLE hi hcc' (θ y) :=
    ⟨_, homCompare_restrictₗ f a hi c c' hcc' hd θ⟩
  have hstep : ∀ (W' : X.Opens) (e : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W')
      (e' : i ⁻¹ᵁ T'.basicOpen c' ≤ a ⁻¹ᵁ W') (y : Γ(X, W')),
      θ'' (pullbackD f a W' e' y) = conormalResLE hi hcc' (θ (pullbackD f a W' e y)) :=
    fun W' e e' y ↦ (congrArg θ'' (hres W' e e' y)).symm.trans (hθ'' (pullbackD f a W' e y))
  have hspecW : ∀ b' : Γ(X, W), θ'' (pullbackD f a W hUW'' b')
      = liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi
          (T'.basicOpen c')) hWV hUWt'' hV'' hcomm'' hb₁f'' hb₂f'' hb₁a'' hb₂a''
          hb₁'' hb₂'' b' := fun b' ↦
    (hstep W hUW hUW'' b').trans
      ((congrArg (fun z ↦ conormalResLE hi hcc' z) (hθ b')).trans
        (conormalResLE_liftDiffDerivation f hi hcc' hWV hUWt hUWt'' hV' hV'' hcomm hcomm''
          hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ hb₁f'' hb₂f'' hb₁a'' hb₂a'' hb₁'' hb₂'' b'))
  refine (hstep W₂ hUW₂ hUW₂'' b).symm.trans ((?_ : θ'' (pullbackD f a W₂ hUW₂'' b) = _).trans
    (conormalResLE_liftDiffDerivation f hi hcc' hW₂V₂ hUWt₂ hUWt₂'' hV'₂ hV''₂ hcomm hcomm''
      hb₁f hb₂f hb₁a hb₂a hb₁₂ hb₂₂ hb₁f'' hb₂f'' hb₁a'' hb₂a'' hb₁₂'' hb₂₂'' b).symm)
  exact liftDiffDerivation_spec_chart_local f hi hV hW hW₃aff hWV hW₂V₂ hW₃W hW₃W₂ hUW''
    hUW₂'' hUW₃'' hUWt'' hUWt₂'' hUWt₃'' hV'' hV''₂ hcomm'' hb₁f'' hb₂f'' hb₁a'' hb₂a''
    hb₁'' hb₂'' hb₁₂'' hb₂₂'' hb₁₃'' hb₂₃'' θ'' hspecW b



/-- **Chart independence of the chart-local difference of two lifts.** Let `f : X ⟶ S` be locally
of finite presentation, let `i : T ⟶ T'` be a first-order thickening with `T'` affine and let
`a : T ⟶ X`, `h : T' ⟶ S` present a lifting problem for `f`. Let `c` be a global section of
`𝒪_{T'}`, let `b₁`, `b₂` solve the lifting problem restricted to `D(c)`, and suppose both map into
two charts `W`, `W₂` of `f`, over the affine opens `V`, `V₂` of `S`. Then a
`Γ(T, i ⁻¹ᵁ D(c))`-linear map out of `Γ(a^*Ω_{X/S}, i ⁻¹ᵁ D(c))` inducing the chart-local
difference of `b₁` and `b₂` in the chart `W` induces it in the chart `W₂` as well.

With the uniqueness clause of `Stacks.Smooth.existsUnique_linearMap_liftDiffDerivation` this says
that the linear map attached to a pair of solutions of a lifting problem **does not depend on the
chart** in which their difference was formed, which is what allows the pairwise differences of the
local solutions of step (I) of [Stacks Project, Tag 02H6] to be compared at a triple overlap and
so to be read as a Čech 1-cocycle.

Two charts may have no common affine refinement containing the whole image of `D(c)`, only
locally; `Stacks.Smooth.exists_basicOpen_refine_chart` produces a covering of `D(c)` by basic
opens over which one exists, `Stacks.Smooth.conormalResLE_liftDiffDerivation_spec_chart` settles
the comparison over each member, and
`Stacks.Smooth.eq_of_conormalResLE_basicOpen_eq` — the separatedness of the conormal module —
glues the members back up. -/
theorem liftDiffDerivation_spec_chart_independent [LocallyOfFinitePresentation f]
    (c : Γ(T', (⊤ : T'.Opens))) (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (hWV : W ≤ f ⁻¹ᵁ V) (hW₂V₂ : W₂ ≤ f ⁻¹ᵁ V₂)
    (hUW : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W) (hUW₂ : i ⁻¹ᵁ T'.basicOpen c ≤ a ⁻¹ᵁ W₂)
    (hUWt : (⊤ : ((i ⁻¹ᵁ T'.basicOpen c : T.Opens) : Scheme.{u}).Opens) ≤
      ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ⁻¹ᵁ W)
    (hUWt₂ : (⊤ : ((i ⁻¹ᵁ T'.basicOpen c : T.Opens) : Scheme.{u}).Opens) ≤
      ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ⁻¹ᵁ W₂)
    (hV' : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen c).ι ≫ h) ⁻¹ᵁ V)
    (hV'₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤
      ((T'.basicOpen c).ι ≫ h) ⁻¹ᵁ V₂)
    (hcomm : ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) ≫ f
      = (i ∣_ T'.basicOpen c) ≫ ((T'.basicOpen c).ι ≫ h))
    {b₁ b₂ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}) ⟶ X}
    (hb₁f : b₁ ≫ f = (T'.basicOpen c).ι ≫ h) (hb₂f : b₂ ≫ f = (T'.basicOpen c).ι ≫ h)
    (hb₁a : (i ∣_ T'.basicOpen c) ≫ b₁ = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a)
    (hb₂a : (i ∣_ T'.basicOpen c) ≫ b₂ = (i ⁻¹ᵁ T'.basicOpen c).ι ≫ a)
    (hb₁ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W)
    (hb₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W)
    (hb₁₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₁ ⁻¹ᵁ W₂)
    (hb₂₂ : (⊤ : ((T'.basicOpen c : T'.Opens) : Scheme.{u}).Opens) ≤ b₂ ⁻¹ᵁ W₂)
    (θ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      Γ(pullbackCotangentSheaf f a, i ⁻¹ᵁ T'.basicOpen c) →ₗ[Γ(T, i ⁻¹ᵁ T'.basicOpen c)]
        RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    (hθ : letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
        (isAffineOpen_top T').basicOpen c
      letI := algebraAppLE f hWV
      letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
      letI := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hWV hUWt
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
        (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
      ∀ b : Γ(X, W), θ (pullbackD f a W hUW b) =
        liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
          hWV hUWt hV' hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ b) :
    letI : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
      (isAffineOpen_top T').basicOpen c
    letI := algebraAppLE f hW₂V₂
    letI := thickeningKerModule (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
    letI := moduleOfAppLE ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hUWt₂
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hW₂V₂ hUWt₂
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := isScalarTowerOfAppLEBase f ((i ⁻¹ᵁ T'.basicOpen c).ι ≫ a) hW₂V₂ hUWt₂
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    letI := moduleOfTopIso (i ⁻¹ᵁ T'.basicOpen c)
      (RingHom.ker (i ∣_ T'.basicOpen c).appTop.hom)
    ∀ b : Γ(X, W₂), θ (pullbackD f a W₂ hUW₂ b) =
      liftDiffDerivation f (isFirstOrderThickening_morphismRestrict hi (T'.basicOpen c))
        hW₂V₂ hUWt₂ hV'₂ hcomm hb₁f hb₂f hb₁a hb₂a hb₁₂ hb₂₂ b := by
  have : IsAffine ((T'.basicOpen c : T'.Opens) : Scheme.{u}) :=
    (isAffineOpen_top T').basicOpen c
  intro b
  obtain ⟨g, W₃, hcov, hdata⟩ := exists_basicOpen_refine_chart c hb₁ hb₁₂
  refine eq_of_conormalResLE_basicOpen_eq hi c (fun t ↦ c * g t) (fun t ↦ (hdata t).1) hcov
    fun t ↦ ?_
  have hd : i.appTop.hom c ∣ i.appTop.hom (c * g t) := ⟨i.appTop.hom (g t), by rw [map_mul]⟩
  exact conormalResLE_liftDiffDerivation_spec_chart f hi c (c * g t) (hdata t).1 hd
    (hdata t).2.1 (hdata t).2.2.1 (hdata t).2.2.2.1 hV hW hWV hW₂V₂ hUW hUW₂ hUWt
    hUWt₂ hV' hV'₂ hcomm hb₁f hb₂f hb₁a hb₂a hb₁ hb₂ hb₁₂ hb₂₂ ((hdata t).2.2.2.2 _) θ hθ b

end Independence

end Stacks.Smooth

end
