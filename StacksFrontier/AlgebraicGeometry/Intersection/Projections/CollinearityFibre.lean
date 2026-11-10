module

public import StacksFrontier.AlgebraicGeometry.AmpleAffineAvoidance.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityLocus
public import StacksFrontier.AlgebraicGeometry.SchemeModulesSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.SectionDivision.TripleTensor
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective

/-!
# The determinant section in a chart of the triple product of projective spaces

Let `V` be a vector space over a field `k` and `𝐏(V) = Proj (Sym_k V)`. On the chart
`pr₁⁻¹D₊(ι u₀) ∩ pr₂⁻¹D₊(ι u₁) ∩ pr₃⁻¹D₊(ι u₂)` of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` the section
`pr₁^*(ι u₀) ⊗ pr₂^*(ι u₁) ⊗ pr₃^*(ι u₂)` of `𝒪(1,1,1)` is nonvanishing, so every section of
`𝒪(1,1,1)` has a well-defined ratio to it, an honest function on the chart. This file computes
that ratio for the determinant sections: the ratio of the determinant section attached to a
triple of vectors `w` is the determinant of the `3 × 3` matrix whose `(i, j)` entry is the
pullback along `prᵢ` of the ratio `ι wⱼ / ι uᵢ`, a function on the `i`-th standard open.

That is the chart description of the collinearity equations: a point of the chart is collinear
exactly when all those determinants of matrices of ratios vanish. The file then reads that
description at a *point*, in the local ring and in its residue field, and spends the reading:
the third projection of a collinear point whose first two projections are distinct closed
points lies on the line joining them.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.tautRatio`: the ratio `ι v / ι u` of two
  tautological sections of `𝒪(1)`, a function on the standard open `D₊(ι u)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartRatio`: its pullback along a projection of the
  triple product, a function on a chart.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartMatrix`: the `3 × 3` matrix of those pullbacks,
  whose determinant is the chart description of the determinant section.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartOpen`: the chart
  `pr₁⁻¹D₊(ι u₀) ∩ pr₂⁻¹D₊(ι u₁) ∩ pr₃⁻¹D₊(ι u₂)` attached to a triple of vectors.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.divBySection_tripleSection`: the ratio of one tensor
  of tautological sections to another is the product of the three ratios of the factors.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.divBySection_tautologicalPullbackSection`: the ratio
  of two pulled-back tautological sections is the pullback of the ratio on the base.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.le_nonvanishingOpen_tripleSection`: the tensor
  `pr₁^*(ι u₀) ⊗ pr₂^*(ι u₁) ⊗ pr₃^*(ι u₂)` is a frame of `𝒪(1,1,1)` on the chart.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.divBySection_tripleSection_eq_chartRatio_mul`: the
  ratio of two tensors of tautological sections written as a product of pulled-back ratios on the
  chart.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.divBySection_detSection`: **the ratio of the
  determinant section to the tensor `pr₁^*(ι u₀) ⊗ pr₂^*(ι u₁) ⊗ pr₃^*(ι u₂)` is the determinant
  of the matrix of pulled-back ratios.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_mem_chartOpen`: every point of the triple
  product lies in a chart, so the chart description applies at every point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isUnit_germ_chartRatio_iff` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.residue_germ_chartRatio_eq_zero_iff`: **the
  pointwise reading of one ratio.** The function `ι v / ι uᵢ` pulled back along `prᵢ` is a unit
  of the local ring at a point of the chart — equivalently has nonzero residue — exactly when
  `ι v` avoids the homogeneous prime of `prᵢ` of that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_detSection_iff_isUnit_germ_det`
  and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_collinearLocus_iff_forall_not_isUnit_germ_det`:
  **the pointwise reading of the determinant identity.** A point of a chart is collinear exactly
  when every determinant of a matrix of ratios is a non-unit of the local ring there.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.lineSubmodule_le_pointSubmodule_of_mem_collinearLocus`
  and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_lineSubmodule_of_mem_collinearLocus`
  say that **a collinear point over a pair of distinct closed points has its third projection on
  the line joining them.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.not_pointSubmodule_le`: distinct closed points of
  `𝐏(V)` have incomparable hyperplanes of degree-one forms, which is what supplies the two
  vectors the determinant is evaluated against.

## Implementation notes

The invertibility of a pullback of the tautological module, of the tensor of the first two
pullbacks and of `𝒪(1,1,1)` are registered as instances, so that
`Stacks.SheafOfModules.divBySection` elaborates without a local `letI` at every use. The
instance for a pullback is stated for an arbitrary morphism to `𝐏(V)`, which covers the three
projections because `AlgebraicGeometry.ProjectiveSpaceOfModule.taut₁` and its companions are
reducible. The instance for `𝒪(1,1,1)` is stated both in the folded spelling
`AlgebraicGeometry.ProjectiveSpaceOfModule.tripleTwistModule` and in the unfolded iterated-tensor
spelling, because the folded one is a plain definition and so is not unfolded by instance
synthesis.

The chart is not taken to be the nonvanishing locus of the tensor itself but an arbitrary open
together with the three containments `U ≤ prᵢ⁻¹D₊(ι uᵢ)`, in that shape rather than a
containment in the nonvanishing locus of the tensor, because that is the shape in which
`Stacks.SheafOfModules.divBySection_modulePullbackSection_of_le` consumes them and in which the
three factors can be treated independently. The containment needed by the denominator is then the
three-factor `Stacks.SheafOfModules.le_nonvanishingOpen_tensorSections₃` of those three, which is
the same term that appears in the statement.

The determinant is reached from the antisymmetrised sum defining the determinant section by
`Stacks.SheafOfModules.divBySection_sum` and `Stacks.SheafOfModules.divBySection_zsmul`, which
turn the quotient of the sum into the sum of the quotients. The sum defining the determinant
section has the `i`-th tensor factor of each term a ratio against `uᵢ`, so it is indexed by the
row of the matrix, while `Matrix.det_apply'` expands along `M (σ i) i`; the two are matched by
`Matrix.det_transpose`.

**The spelling bridge from the identity to the point.** `divBySection_detSection` is an identity
in the ring `Γ(prodThree k V, U)`, and the lemma that turns a ratio of two sections of one
invertible module into a statement about a point is
`Stacks.AmpleAffineAvoidance.mem_nonvanishingLocus_iff_isUnit_of_smul`: where the denominator
does not vanish, the numerator does not vanish exactly where the ratio is a unit of the local
ring. That lemma is stated for the `Stacks.Ample` spelling of the nonvanishing locus on a
scheme, while `AlgebraicGeometry.ProjectiveSpaceOfModule.collinearLocus` is defined in the
`Stacks.SheafOfModules` spelling on the underlying ringed space, so the two have to be matched:
`Stacks.SchemeModulesSpelling.nonvanishingLocus_eq` and
`Stacks.SchemeModulesSpelling.nonvanishingOpen_eq` cross the locus and the open, and
`Stacks.SchemeModulesSpelling.isInvertible_algebraicGeometry` crosses the invertibility class
that the scheme-side statement asks for as an instance. Those crossings are registered here as
the instances `isInvertibleModule_pullbackTaut` and `isInvertibleModule_tripleTwist`, and the
equality of loci is applied through `Set.ext_iff` rather than by `rw`, which cannot retype its
motive across the two spellings.

The hypothesis of the ratio lemma is `t|_U = f • a|_U` for the *global* sections, while
`divBySection` and the chart calculus work with the value of a compatible family on `U`; the two
are matched by `PresheafOfModules.sections_property`, which is exactly the compatibility of the
family. The implicit module of `Stacks.SectionExtension.resTop` has to be given by name, since
`Γ(M, ⊤)` does not reduce to `M.val.obj (op ⊤)` at the transparency unification uses.

**Why the residue field.** "Not a unit" means "in the maximal ideal", not "zero", so the
determinant of a matrix of ratios cannot be expanded against non-units directly. Passing to the
residue field by `IsLocalRing.residue_eq_zero_iff` makes every entry either zero or nonzero, and
then `Matrix.det_fin_three` leaves, for the triple `(v, a, b)` of the containment proof, the
single term `(ι a / ι u₀) · (ι b / ι u₁) · (ι v / ι u₂)` with the first two factors nonzero.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)

## Where the converse containment is

The *converse* containment — that a point of the triple product whose first two projections are
distinct closed points and whose third projection lies on the line joining them is collinear — is
proved in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/CollinearityRatioLinear.lean`, as
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_collinearLocus_of_lineSubmodule_le`, and
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_collinearLocus_iff_mem_linearSubspace_lineSubmodule`
combines the two containments.
What that file supplies, and what the containment direction here does not need, is the
**`k`-linearity of the ratio in its numerator**: the map `v ↦ residue at t of (ι v / ι uᵢ)` is
used above only through its kernel, while the converse needs its *values*. Write `W₁`, `W₂` for
the degree-one forms vanishing at the first two points and `K = W₁ ⊓ W₂`, and take `a ∈ W₂ ∖ W₁`,
`b ∈ W₁ ∖ W₂` as in the containment proof: every vector is then `c + α a + β b` with `c ∈ K` and
`α, β ∈ k`, and `k`-linearity puts the columns of every matrix of ratios in the span of the two
columns of `a` and `b`, so every determinant vanishes.

`k`-linearity is not sheaf theory beyond this file's: additivity is
`Stacks.SheafOfModules.divBySection_add` together with the additivity of the degree-one section
map `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSectionHom`, and the scalar law is
`Stacks.SheafOfModules.divBySection_smul` together with
`Stacks.AlgebraicGeometry.ProjectiveSpaceSections.degreeSection_smul`, which does hold for the
symmetric grading of an arbitrary module over a commutative ring and not only for `ℙⁿ_R` with its
polynomial grading. The one extra ingredient is that the scalar reaching the residue field is the
*same* for all three projections, which is
`Stacks.AlgebraicGeometry.ProjectiveSpaceSections.structureMorphism_appTop_eq` together with the
fact that the three projections are morphisms over `Spec k`. The detour through
`Stacks.ProjTwistSection.divBySection_homogeneousSection` and
`HomogeneousLocalization.Away`, which earlier notes here proposed, is not needed and was not
taken.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### Invertibility of the modules in play -/

/-- The tautological module `𝒪(1)` on `𝐏(V)` is invertible. -/
public instance isInvertible_taut :
    IsInvertible (projectiveSpaceOfModule k V).toRingedSpace.presheaf
      (structureSheafRing (projectiveSpaceOfModule k V).toRingedSpace).property
      (tautologicalModule k V) :=
  isInvertible_tautologicalModule k V

/-- The pullback of the tautological module along any morphism `prodThree k V ⟶ 𝐏(V)` is
invertible; this covers the three projections. -/
public instance isInvertible_pullbackTaut
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) :
    IsInvertible (prodThree k V).toRingedSpace.presheaf
      (structureSheafRing (prodThree k V).toRingedSpace).property
      ((Scheme.Modules.pullback f).obj (tautologicalModule k V)) :=
  Stacks.Modules.isInvertible_pullback f (tautologicalModule k V)

/-- The tensor product of the first two pullbacks of the tautological module is invertible. -/
public instance isInvertible_taut₁₂ : IsInvertible (prodThree k V).toRingedSpace.presheaf
    (structureSheafRing (prodThree k V).toRingedSpace).property
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((prodThree k V).toRingedSpace)).presheaf, (((prodThree k V).toRingedSpace)).IsSheaf⟩).obj
        ((taut₁ k V))).obj ((taut₂ k V)))) :=
  @tensorProduct_isInvertible _ _ _ (prodThree k V).presheaf
    (structureSheafRing (prodThree k V).toRingedSpace).property _ _ (taut₁ k V) (taut₂ k V)
    (Stacks.Modules.isInvertible_pullback _ _) (Stacks.Modules.isInvertible_pullback _ _)

/-- `𝒪(1,1,1)`, in the unfolded iterated-tensor spelling, is invertible. -/
public instance isInvertible_tensorThree : IsInvertible (prodThree k V).toRingedSpace.presheaf
    (structureSheafRing (prodThree k V).toRingedSpace).property
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(((prodThree k V).toRingedSpace)).presheaf, (((prodThree k V).toRingedSpace)).IsSheaf⟩).obj
        (((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((prodThree k V).toRingedSpace)).presheaf,
            (((prodThree k V).toRingedSpace)).IsSheaf⟩).obj ((taut₁ k V))).obj
              ((taut₂ k V)))))).obj ((taut₃ k V)))) :=
  isInvertible_tripleTwistModule k V

/-- `𝒪(1,1,1)`, in the folded spelling `tripleTwistModule`, is invertible. -/
public instance isInvertible_tripleTwist : IsInvertible (prodThree k V).toRingedSpace.presheaf
    (structureSheafRing (prodThree k V).toRingedSpace).property (tripleTwistModule k V) :=
  isInvertible_tripleTwistModule k V

/-! ### The ratio of two tensors of tautological sections -/

/-- **The ratio of one tensor of tautological sections to another is the product of the three
ratios of the factors.** -/
public theorem divBySection_tripleSection (u₀ u₁ u₂ a b c : V) {U : (prodThree k V).Opens}
    (h₁ : U ≤ nonvanishingOpen (taut₁ k V) (tautologicalPullbackSection k V (pr₁ k V) u₀))
    (h₂ : U ≤ nonvanishingOpen (taut₂ k V) (tautologicalPullbackSection k V (pr₂ k V) u₁))
    (h₃ : U ≤ nonvanishingOpen (taut₃ k V) (tautologicalPullbackSection k V (pr₃ k V) u₂)) :
    divBySection (tripleTwistModule k V) (tripleSection k V u₀ u₁ u₂)
        (le_nonvanishingOpen_tensorSections₃ (taut₁ k V) (taut₂ k V) (taut₃ k V)
          (tautologicalPullbackSection k V (pr₁ k V) u₀)
          (tautologicalPullbackSection k V (pr₂ k V) u₁)
          (tautologicalPullbackSection k V (pr₃ k V) u₂) h₁ h₂ h₃)
        ((tripleSection k V a b c).eval (op U))
      = divBySection (taut₁ k V) (tautologicalPullbackSection k V (pr₁ k V) u₀) h₁
            ((tautologicalPullbackSection k V (pr₁ k V) a).eval (op U))
          * divBySection (taut₂ k V) (tautologicalPullbackSection k V (pr₂ k V) u₁) h₂
            ((tautologicalPullbackSection k V (pr₂ k V) b).eval (op U))
          * divBySection (taut₃ k V) (tautologicalPullbackSection k V (pr₃ k V) u₂) h₃
            ((tautologicalPullbackSection k V (pr₃ k V) c).eval (op U)) :=
  divBySection_tensorSections₃ (taut₁ k V) (taut₂ k V) (taut₃ k V)
    (tautologicalPullbackSection k V (pr₁ k V) u₀) (tautologicalPullbackSection k V (pr₁ k V) a)
    (tautologicalPullbackSection k V (pr₂ k V) u₁) (tautologicalPullbackSection k V (pr₂ k V) b)
    (tautologicalPullbackSection k V (pr₃ k V) u₂) (tautologicalPullbackSection k V (pr₃ k V) c)
    h₁ h₂ h₃

/-! ### Ratios of tautological sections as functions on a chart -/

/-- **The ratio `ι v / ι u` of two tautological sections of `𝒪(1)`**, the function on the standard
open `D₊(ι u)` whose product with `ι u / 1` is `ι v / 1`. -/
public def tautRatio (u v : V) :=
  divBySection (tautologicalModule k V) (tautologicalSection k V u) le_rfl
    ((tautologicalSection k V v).eval
      (op (nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))))

/-- An open of the triple product inside the preimage of `D₊(ι u)` under a morphism to `𝐏(V)` is
inside the nonvanishing locus of the pulled-back section. -/
public theorem le_nonvanishingOpen_tautologicalPullbackSection
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u : V) {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u)) :
    U ≤ nonvanishingOpen ((Scheme.Modules.pullback f).obj (tautologicalModule k V))
      (tautologicalPullbackSection k V f u) :=
  hU.trans (le_of_eq (preimage_nonvanishingOpen f (tautologicalModule k V)
    (tautologicalSection k V u)))

/-- **The pullback along a morphism to `𝐏(V)` of the ratio `ι v / ι u`**, a function on an open
of the triple product inside the preimage of `D₊(ι u)`. -/
public def chartRatio (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u v : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u)) :=
  (f.appLE (nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u)) U hU).hom
    (tautRatio k V u v)

/-- **The ratio of two pulled-back tautological sections is the pullback of the ratio.** -/
public theorem divBySection_tautologicalPullbackSection
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u v : V) {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u)) :
    divBySection ((Scheme.Modules.pullback f).obj (tautologicalModule k V))
        (tautologicalPullbackSection k V f u)
        (le_nonvanishingOpen_tautologicalPullbackSection k V f u hU)
        ((tautologicalPullbackSection k V f v).eval (op U))
      = chartRatio k V f u v hU :=
  divBySection_modulePullbackSection_of_le f (tautologicalModule k V)
    (tautologicalSection k V u) (tautologicalSection k V v) le_rfl hU

/-- **A chart lies in the nonvanishing locus of the tensor of three tautological sections**: the
tensor `pr₁^*(ι u₀) ⊗ pr₂^*(ι u₁) ⊗ pr₃^*(ι u₂)` is a frame of `𝒪(1,1,1)` there. -/
public theorem le_nonvanishingOpen_tripleSection (u₀ u₁ u₂ : V) {U : (prodThree k V).Opens}
    (h₁ : U ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V u₀))
    (h₂ : U ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V u₁))
    (h₃ : U ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V u₂)) :
    U ≤ nonvanishingOpen (tripleTwistModule k V) (tripleSection k V u₀ u₁ u₂) :=
  le_nonvanishingOpen_tensorSections₃ (taut₁ k V) (taut₂ k V) (taut₃ k V)
    (tautologicalPullbackSection k V (pr₁ k V) u₀)
    (tautologicalPullbackSection k V (pr₂ k V) u₁)
    (tautologicalPullbackSection k V (pr₃ k V) u₂)
    (le_nonvanishingOpen_tautologicalPullbackSection k V (pr₁ k V) u₀ h₁)
    (le_nonvanishingOpen_tautologicalPullbackSection k V (pr₂ k V) u₁ h₂)
    (le_nonvanishingOpen_tautologicalPullbackSection k V (pr₃ k V) u₂ h₃)

/-- **The ratio of one tensor of tautological sections to another, as a product of pulled-back
ratios on the chart.** -/
public theorem divBySection_tripleSection_eq_chartRatio_mul (u₀ u₁ u₂ a b c : V)
    {U : (prodThree k V).Opens}
    (h₁ : U ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V u₀))
    (h₂ : U ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V u₁))
    (h₃ : U ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V u₂)) :
    divBySection (tripleTwistModule k V) (tripleSection k V u₀ u₁ u₂)
        (le_nonvanishingOpen_tripleSection k V u₀ u₁ u₂ h₁ h₂ h₃)
        ((tripleSection k V a b c).eval (op U))
      = chartRatio k V (pr₁ k V) u₀ a h₁ * chartRatio k V (pr₂ k V) u₁ b h₂
          * chartRatio k V (pr₃ k V) u₂ c h₃ := by
  rw [divBySection_tripleSection k V u₀ u₁ u₂ a b c
      (le_nonvanishingOpen_tautologicalPullbackSection k V (pr₁ k V) u₀ h₁)
      (le_nonvanishingOpen_tautologicalPullbackSection k V (pr₂ k V) u₁ h₂)
      (le_nonvanishingOpen_tautologicalPullbackSection k V (pr₃ k V) u₂ h₃),
    divBySection_tautologicalPullbackSection k V (pr₁ k V) u₀ a h₁,
    divBySection_tautologicalPullbackSection k V (pr₂ k V) u₁ b h₂,
    divBySection_tautologicalPullbackSection k V (pr₃ k V) u₂ c h₃]

/-! ### The determinant section in a chart -/

/-- **The `3 × 3` matrix of pulled-back ratios** on a chart of the triple product: its `(i, j)`
entry is the pullback along `prᵢ` of the ratio `ι wⱼ / ι uᵢ`. -/
public def chartMatrix (u w : Fin 3 → V) {U : (prodThree k V).Opens}
    (h₁ : U ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 0)))
    (h₂ : U ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 1)))
    (h₃ : U ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 2))) :
    Matrix (Fin 3) (Fin 3) Γ(prodThree k V, U) :=
  ![fun j => chartRatio k V (pr₁ k V) (u 0) (w j) h₁,
    fun j => chartRatio k V (pr₂ k V) (u 1) (w j) h₂,
    fun j => chartRatio k V (pr₃ k V) (u 2) (w j) h₃]

/-- **The ratio of the determinant section to the tensor `pr₁^*(ι u₀) ⊗ pr₂^*(ι u₁) ⊗ pr₃^*(ι u₂)`
is the determinant of the matrix of pulled-back ratios.** This is the chart description of the
collinearity equations: on the chart `pr₁⁻¹D₊(ι u₀) ∩ pr₂⁻¹D₊(ι u₁) ∩ pr₃⁻¹D₊(ι u₂)` the
determinant section attached to a triple of vectors `w` becomes, in the trivialisation of
`𝒪(1,1,1)` given by that tensor, the determinant of the `3 × 3` matrix of functions
`prᵢ^♯ (ι wⱼ / ι uᵢ)`. -/
public theorem divBySection_detSection (u w : Fin 3 → V) {U : (prodThree k V).Opens}
    (h₁ : U ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 0)))
    (h₂ : U ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 1)))
    (h₃ : U ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 2))) :
    divBySection (tripleTwistModule k V) (tripleSectionOf k V u)
        (le_nonvanishingOpen_tripleSection k V (u 0) (u 1) (u 2) h₁ h₂ h₃)
        ((detSection k V w).eval (op U))
      = (chartMatrix k V u w h₁ h₂ h₃).det := by
  have hsum := divBySection_sum (tripleTwistModule k V) (tripleSectionOf k V u)
    (le_nonvanishingOpen_tripleSection k V (u 0) (u 1) (u 2) h₁ h₂ h₃)
    (fun σ : Equiv.Perm (Fin 3) => (Equiv.Perm.sign σ : ℤ) •
      (tripleSectionOf k V (w ∘ σ)).eval (op U)) Finset.univ
  rw [detSection_eval, hsum, ← Matrix.det_transpose, Matrix.det_apply']
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [divBySection_zsmul (tripleTwistModule k V) (tripleSectionOf k V u)
      (le_nonvanishingOpen_tripleSection k V (u 0) (u 1) (u 2) h₁ h₂ h₃)
      (Equiv.Perm.sign σ : ℤ) ((tripleSectionOf k V (w ∘ σ)).eval (op U)),
    zsmul_eq_mul, Fin.prod_univ_three]
  congr 1
  exact divBySection_tripleSection_eq_chartRatio_mul k V (u 0) (u 1) (u 2)
    (w (σ 0)) (w (σ 1)) (w (σ 2)) h₁ h₂ h₃

/-! ### A chart around a point, and the ratios there -/

/-- **The chart `pr₁⁻¹D₊(ι u₀) ∩ pr₂⁻¹D₊(ι u₁) ∩ pr₃⁻¹D₊(ι u₂)`** of the triple product
attached to a triple of vectors. -/
public def chartOpen (u : Fin 3 → V) : (prodThree k V).Opens :=
  (pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 0))) ⊓
      (pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 1))) ⊓
    (pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V (u 2)))

/-- The chart lies in the preimage of the first standard open. -/
public theorem chartOpen_le_pr₁ (u : Fin 3 → V) :
    chartOpen k V u ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 0)) := inf_le_left.trans inf_le_left

/-- The chart lies in the preimage of the second standard open. -/
public theorem chartOpen_le_pr₂ (u : Fin 3 → V) :
    chartOpen k V u ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 1)) := inf_le_left.trans inf_le_right

/-- The chart lies in the preimage of the third standard open. -/
public theorem chartOpen_le_pr₃ (u : Fin 3 → V) :
    chartOpen k V u ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 2)) := inf_le_right

/-- A point of the triple product lies in the chart attached to `u` exactly when none of the
three forms `ι uᵢ` lies in the homogeneous prime of the corresponding projection. -/
public theorem mem_chartOpen_iff (u : Fin 3 → V) (x : prodThree k V) :
    x ∈ chartOpen k V u ↔
      SymmetricAlgebra.ι k V (u 0) ∉ ((pr₁ k V).base x).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k V (u 1) ∉ ((pr₂ k V).base x).asHomogeneousIdeal ∧
          SymmetricAlgebra.ι k V (u 2) ∉ ((pr₃ k V).base x).asHomogeneousIdeal := by
  have h : ∀ (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (v : V),
      x ∈ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V v) ↔
        SymmetricAlgebra.ι k V v ∉ (f.base x).asHomogeneousIdeal :=
    fun f v => mem_nonvanishingLocus_tautologicalSection_iff k V v (f.base x)
  rw [chartOpen, TopologicalSpace.Opens.mem_inf, TopologicalSpace.Opens.mem_inf,
    h (pr₁ k V) (u 0), h (pr₂ k V) (u 1), h (pr₃ k V) (u 2)]
  exact and_assoc

/-- **Every point of the triple product lies in a chart.** Each of its three projections omits
some degree-one form, and the three forms chosen give the chart. -/
public theorem exists_mem_chartOpen (x : prodThree k V) :
    ∃ u : Fin 3 → V, x ∈ chartOpen k V u := by
  obtain ⟨a, ha⟩ := exists_ι_notMem k V ((pr₁ k V).base x)
  obtain ⟨b, hb⟩ := exists_ι_notMem k V ((pr₂ k V).base x)
  obtain ⟨c, hc⟩ := exists_ι_notMem k V ((pr₃ k V).base x)
  exact ⟨![a, b, c], (mem_chartOpen_iff k V _ x).mpr ⟨ha, hb, hc⟩⟩

/-- A pullback of `𝒪(1)` is invertible in the scheme spelling of the invertibility class of
Stacks Tag 01CS. -/
public instance isInvertibleModule_pullbackTaut
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) :
    Stacks.Ample.IsInvertibleModule (prodThree k V)
      ((Scheme.Modules.pullback f).obj (tautologicalModule k V)) :=
  Stacks.SchemeModulesSpelling.isInvertible_algebraicGeometry _ _ _
    (isInvertible_pullbackTaut k V f)

/-- Restricting a global section `t` to `U` gives its ratio by `s` times the restriction of `s`,
for `U` inside the nonvanishing locus of `s`. -/
private theorem resTop_eq_divBySection_smul_resTop (M : (prodThree k V).Modules)
    [IsInvertible (prodThree k V).toRingedSpace.presheaf
      (structureSheafRing (prodThree k V).toRingedSpace).property M]
    (s t : M.sections) {U : (prodThree k V).Opens} (hle : U ≤ nonvanishingOpen M s) :
    Stacks.SectionExtension.resTop (M := M) U (t.eval (op ⊤)) =
      divBySection M s hle (t.eval (op U)) •
        Stacks.SectionExtension.resTop (M := M) U (s.eval (op ⊤)) := by
  have hres : ∀ r : M.sections, Stacks.SectionExtension.resTop (M := M) U (r.eval (op ⊤)) =
      r.eval (op U) :=
    fun r => PresheafOfModules.sections_property r (homOfLE (le_top : U ≤ ⊤)).op
  rw [hres, hres]
  exact (smul_divBySection M s hle _).symm

/-- **The ratio `ι v / ι u`, pulled back along a projection, is a unit at a point of the chart
exactly when `ι v` avoids the homogeneous prime of that projection of the point.** So the
function `chartRatio k V f u v` cuts out, inside the chart, the locus where `v` does not vanish
at the image point: it is the pointwise reading of the ratio. -/
public theorem isUnit_germ_chartRatio_iff (f : prodThree k V ⟶ projectiveSpaceOfModule k V)
    (u v : V) {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))
    {x : prodThree k V} (hx : x ∈ U) :
    IsUnit (((prodThree k V).presheaf.germ U x hx).hom (chartRatio k V f u v hU)) ↔
      SymmetricAlgebra.ι k V v ∉ (f.base x).asHomogeneousIdeal := by
  have hle := le_nonvanishingOpen_tautologicalPullbackSection k V f u hU
  have hf := resTop_eq_divBySection_smul_resTop k V
    ((Scheme.Modules.pullback f).obj (tautologicalModule k V))
    (tautologicalPullbackSection k V f u) (tautologicalPullbackSection k V f v) hle
  rw [divBySection_tautologicalPullbackSection k V f u v hU] at hf
  refine Iff.trans (Stacks.AmpleAffineAvoidance.mem_nonvanishingLocus_iff_isUnit_of_smul
    (hle.trans (le_of_eq (Stacks.SchemeModulesSpelling.nonvanishingOpen_eq (prodThree k V)
      ((Scheme.Modules.pullback f).obj (tautologicalModule k V))
      (tautologicalPullbackSection k V f u)))) hf hx).symm ?_
  refine Iff.trans (Set.ext_iff.mp (Stacks.SchemeModulesSpelling.nonvanishingLocus_eq
    (prodThree k V) ((Scheme.Modules.pullback f).obj (tautologicalModule k V))
    (tautologicalPullbackSection k V f v)) x).symm ?_
  refine Iff.trans (Set.ext_iff.mp
    (nonvanishingLocus_tautologicalPullbackSection k V f v) x) ?_
  exact mem_nonvanishingLocus_tautologicalSection_iff k V v (f.base x)

/-! ### The determinant section at a point of the chart -/

/-- `𝒪(1,1,1)` is invertible in the scheme spelling of the invertibility class of Stacks
Tag 01CS, which is the hypothesis the pointwise calculus of the nonvanishing locus is stated
over. -/
public instance isInvertibleModule_tripleTwist :
    Stacks.Ample.IsInvertibleModule (prodThree k V) (tripleTwistModule k V) :=
  Stacks.SchemeModulesSpelling.isInvertible_algebraicGeometry _ _ _
    (isInvertible_tripleTwistModule k V)

/-- **The determinant section does not vanish at a point of the chart exactly when the
determinant of the matrix of ratios is a unit of the local ring there.** This is the pointwise
reading of `divBySection_detSection`: that lemma is an identity in the ring
`Γ(prodThree k V, U)`, and this turns it into a statement about a point of `U`. -/
public theorem mem_nonvanishingLocus_detSection_iff_isUnit_germ_det (u w : Fin 3 → V)
    {U : (prodThree k V).Opens}
    (h₁ : U ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 0)))
    (h₂ : U ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 1)))
    (h₃ : U ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 2)))
    {x : prodThree k V} (hx : x ∈ U) :
    x ∈ nonvanishingLocus (X := (prodThree k V).toRingedSpace) (tripleTwistModule k V)
        (detSection k V w) ↔
      IsUnit (((prodThree k V).presheaf.germ U x hx).hom
        (chartMatrix k V u w h₁ h₂ h₃).det) := by
  have hle := le_nonvanishingOpen_tripleSection k V (u 0) (u 1) (u 2) h₁ h₂ h₃
  have hf := resTop_eq_divBySection_smul_resTop k V (tripleTwistModule k V)
    (tripleSectionOf k V u) (detSection k V w) hle
  rw [divBySection_detSection k V u w h₁ h₂ h₃] at hf
  refine Iff.trans (Set.ext_iff.mp (Stacks.SchemeModulesSpelling.nonvanishingLocus_eq
    (prodThree k V) (tripleTwistModule k V) (detSection k V w)) x) ?_
  exact Stacks.AmpleAffineAvoidance.mem_nonvanishingLocus_iff_isUnit_of_smul
    (hle.trans (le_of_eq (Stacks.SchemeModulesSpelling.nonvanishingOpen_eq (prodThree k V)
      (tripleTwistModule k V) (tripleSectionOf k V u)))) hf hx

/-- **A point of a chart is collinear exactly when every determinant of a matrix of ratios is a
non-unit there.** This is the pointwise form of the collinearity equations: the definition of
`AlgebraicGeometry.ProjectiveSpaceOfModule.collinearLocus` is the vanishing of the determinant
sections, and this says what it asserts at a point, in the ring of germs. -/
public theorem mem_collinearLocus_iff_forall_not_isUnit_germ_det (u : Fin 3 → V)
    {U : (prodThree k V).Opens}
    (h₁ : U ≤ pr₁ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 0)))
    (h₂ : U ≤ pr₂ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 1)))
    (h₃ : U ≤ pr₃ k V ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
      (tautologicalSection k V (u 2)))
    {x : prodThree k V} (hx : x ∈ U) :
    x ∈ collinearLocus k V ↔ ∀ w : Fin 3 → V,
      ¬ IsUnit (((prodThree k V).presheaf.germ U x hx).hom
        (chartMatrix k V u w h₁ h₂ h₃).det) :=
  Iff.trans (mem_collinearLocus_iff k V x) (forall_congr' fun w =>
    not_congr (mem_nonvanishingLocus_detSection_iff_isUnit_germ_det k V u w h₁ h₂ h₃ hx))

/-! ### Collinear triples lie over the line joining the first two points -/

/-- **The residue at a point of the chart of the pulled-back ratio `ι v / ι u` vanishes exactly
when `ι v` lies in the homogeneous prime of that projection of the point.** This is
`isUnit_germ_chartRatio_iff` read in the residue field, where "non-unit" becomes "zero" and the
determinant of the matrix of ratios can be expanded. -/
public theorem residue_germ_chartRatio_eq_zero_iff
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u v : V) {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))
    {x : prodThree k V} (hx : x ∈ U) :
    IsLocalRing.residue ((prodThree k V).presheaf.stalk x)
        (((prodThree k V).presheaf.germ U x hx).hom (chartRatio k V f u v hU)) = 0 ↔
      SymmetricAlgebra.ι k V v ∈ (f.base x).asHomogeneousIdeal := by
  rw [IsLocalRing.residue_eq_zero_iff, ← not_iff_not, IsLocalRing.notMem_maximalIdeal]
  exact isUnit_germ_chartRatio_iff k V f u v hU hx

/-- **A collinear triple whose first two points are in general position has its third point on
the line joining them.** The degree-one forms vanishing at both of the first two projections of
a collinear point vanish at the third as well, provided neither of the first two hyperplanes
contains the other.

In a chart around the point the three rows of the matrix of ratios are the three projections
read in the residue field, and evaluating the determinant of the triple `(v, a, b)` — for `v` a
form vanishing at the first two points, `a` vanishing at the second only and `b` at the first
only — leaves a single term, the product of two units with the value of `v` at the third
point. -/
public theorem lineSubmodule_le_pointSubmodule_of_mem_collinearLocus {x : prodThree k V}
    (hx : x ∈ collinearLocus k V)
    (h12 : ¬ pointSubmodule k V ((pr₁ k V).base x) ≤ pointSubmodule k V ((pr₂ k V).base x))
    (h21 : ¬ pointSubmodule k V ((pr₂ k V).base x) ≤ pointSubmodule k V ((pr₁ k V).base x)) :
    lineSubmodule k V ((pr₁ k V).base x) ((pr₂ k V).base x) ≤
      pointSubmodule k V ((pr₃ k V).base x) := by
  obtain ⟨b, hb₁, hb₂⟩ := IsConcreteLE.not_le_iff_exists.mp h12
  obtain ⟨a, ha₂, ha₁⟩ := IsConcreteLE.not_le_iff_exists.mp h21
  obtain ⟨u, hmem⟩ := exists_mem_chartOpen k V x
  have h₁ := chartOpen_le_pr₁ k V u
  have h₂ := chartOpen_le_pr₂ k V u
  have h₃ := chartOpen_le_pr₃ k V u
  set φ : Γ(prodThree k V, chartOpen k V u) →+*
      IsLocalRing.ResidueField ((prodThree k V).presheaf.stalk x) :=
    (IsLocalRing.residue ((prodThree k V).presheaf.stalk x)).comp
      ((prodThree k V).presheaf.germ (chartOpen k V u) x hmem).hom with hφdef
  have key : ∀ (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (c : V)
      (hc : chartOpen k V u ≤
        f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V c)) (y : V),
      φ (chartRatio k V f c y hc) = 0 ↔
        SymmetricAlgebra.ι k V y ∈ (f.base x).asHomogeneousIdeal :=
    fun f c hc y => residue_germ_chartRatio_eq_zero_iff k V f c y hc hmem
  intro v hv
  obtain ⟨hv₁, hv₂⟩ := Submodule.mem_inf.mp hv
  have hdet := (mem_collinearLocus_iff_forall_not_isUnit_germ_det k V u h₁ h₂ h₃ hmem).mp hx
    ![v, a, b]
  have hzero : φ ((chartMatrix k V u ![v, a, b] h₁ h₂ h₃).det) = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr
      (not_not.mp fun h => hdet (IsLocalRing.notMem_maximalIdeal.mp h))
  have z00 : (φ.mapMatrix (chartMatrix k V u ![v, a, b] h₁ h₂ h₃)) 0 0 = 0 :=
    (key (pr₁ k V) (u 0) h₁ v).mpr hv₁
  have z02 : (φ.mapMatrix (chartMatrix k V u ![v, a, b] h₁ h₂ h₃)) 0 2 = 0 :=
    (key (pr₁ k V) (u 0) h₁ b).mpr hb₁
  have z10 : (φ.mapMatrix (chartMatrix k V u ![v, a, b] h₁ h₂ h₃)) 1 0 = 0 :=
    (key (pr₂ k V) (u 1) h₂ v).mpr hv₂
  have z11 : (φ.mapMatrix (chartMatrix k V u ![v, a, b] h₁ h₂ h₃)) 1 1 = 0 :=
    (key (pr₂ k V) (u 1) h₂ a).mpr ha₂
  have z01 : (φ.mapMatrix (chartMatrix k V u ![v, a, b] h₁ h₂ h₃)) 0 1 ≠ 0 :=
    fun h => ha₁ ((key (pr₁ k V) (u 0) h₁ a).mp h)
  have z12 : (φ.mapMatrix (chartMatrix k V u ![v, a, b] h₁ h₂ h₃)) 1 2 ≠ 0 :=
    fun h => hb₂ ((key (pr₂ k V) (u 1) h₂ b).mp h)
  rw [RingHom.map_det, Matrix.det_fin_three, z00, z02, z10, z11] at hzero
  simp only [zero_mul, mul_zero, sub_zero, add_zero, zero_add] at hzero
  rcases mul_eq_zero.mp hzero with h | h20
  · rcases mul_eq_zero.mp h with h01 | h12'
    · exact absurd h01 z01
    · exact absurd h12' z12
  · exact (key (pr₃ k V) (u 2) h₃ v).mp h20

/-- Distinct closed points of `𝐏(V)` have incomparable hyperplanes of degree-one forms: a
containment of hyperplanes reverses to a containment of the single points they cut out. -/
public theorem not_pointSubmodule_le [IsAlgClosed k] [Module.Finite k V]
    {p q : projectiveSpaceOfModule k V}
    (hp : IsClosed ({p} : Set (projectiveSpaceOfModule k V)))
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k V))) (hpq : p ≠ q) :
    ¬ pointSubmodule k V p ≤ pointSubmodule k V q := fun hle => by
  have h := linearSubspace_antitone k V hle
  rw [linearSubspace_pointSubmodule k V p hp, linearSubspace_pointSubmodule k V q hq] at h
  exact hpq (Set.mem_singleton_iff.mp (Set.singleton_subset_iff.mp h)).symm

/-- **The third point of a collinear triple over a pair of distinct closed points lies on the
line joining them.** This is the containment half of the identification of the fibre of
`AlgebraicGeometry.ProjectiveSpaceOfModule.collinearProj` over a pair of distinct closed points
with that line: the points of the collinearity locus above such a pair are carried by `pr₃` into
`AlgebraicGeometry.ProjectiveSpaceOfModule.linearSubspace` of
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineSubmodule`, whose dimension is one by
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace_lineSubmodule`. -/
public theorem mem_linearSubspace_lineSubmodule_of_mem_collinearLocus [IsAlgClosed k]
    [Module.Finite k V] {x : prodThree k V} (hx : x ∈ collinearLocus k V)
    (h₁ : IsClosed ({(pr₁ k V).base x} : Set (projectiveSpaceOfModule k V)))
    (h₂ : IsClosed ({(pr₂ k V).base x} : Set (projectiveSpaceOfModule k V)))
    (hne : (pr₁ k V).base x ≠ (pr₂ k V).base x) :
    (pr₃ k V).base x ∈
      linearSubspace k V (lineSubmodule k V ((pr₁ k V).base x) ((pr₂ k V).base x)) :=
  (mem_linearSubspace_iff k V _ _).mpr
    (lineSubmodule_le_pointSubmodule_of_mem_collinearLocus k V hx
      (not_pointSubmodule_le k V h₁ h₂ hne) (not_pointSubmodule_le k V h₂ h₁ hne.symm))

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
