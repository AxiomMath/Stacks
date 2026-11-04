module

public import StacksFrontier.AlgebraicGeometry.Constructions.DirectSumQuasiCompactSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorOfInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.FreeModuleSections

/-!
# The sections of the Laurent algebra over a quasi-compact étale chart

In Situation 0EDT let `X/B` be good and `ℒ` an invertible `𝒪_X`-module.  The Laurent algebra
sheaf `𝒜 = ⨁_{n ∈ ℤ} ℒ^{⊗ n}` of
`AlgebraicGeometry.Space.laurentAlgebraSheaf` is the *sheafification* of the ungraded
realization of the graded algebra of integer tensor powers, so over a general étale chart its
sections are strictly larger than the direct sum of the sections of the tensor powers: a section
is only locally a finite sum.  **Over a quasi-compact chart — in particular over an affine one —
the two agree**, and that is what this file proves.

This is the step the registration of Tag 0EQG in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorSpectrum` names as unaccounted
for.  Its tag note on
`AlgebraicGeometry.Space.isAffineHom_multiplicativeTorsorSpectrumProjection` records that the
three remaining properties of clause (1) — `q` surjective, smooth, and of relative dimension one
— are derived in the source from `T ×_X U ≅ 𝐆_m × U` for an étale chart `U` trivializing `ℒ`,
and that of the inputs to that identification "nothing identifies the Laurent algebra's sections
at a trivialising chart `V` with `𝒪(V)[t, t⁻¹]` (the sheafification step is unaccounted for)".
The sheafification step is what is accounted for here: it is what turns
`AlgebraicGeometry.Space.isPullback_affineChartSpec`, which presents `T ×_X V` as `Spec 𝒜(V)`,
into a statement about `⨁_{n ∈ ℤ} Γ(V, ℒ^{⊗ n})`, the ring in which a trivialization of `ℒ`
over `V` exhibits a Laurent coordinate.

This does not by itself open any clause of Tag 0EQG, and the clauses other than (1) do not pass
through it at all: clauses (6) and (7) rest on a commutative-algebra statement about
`A[t, t⁻¹]_{𝔪A[t,t⁻¹]}` which is independent of this computation.

## Main definitions

* `AlgebraicGeometry.Space.laurentDirectSumHom`: the comparison
  `⨁_{n ∈ ℤ} ℒ^{⊗ n} ⟶ 𝒜` from the objectwise direct sum of the integer tensor powers of `ℒ`
  to the module underlying the Laurent algebra sheaf — on sections, the map that reads a finite
  family of homogeneous sections as a section of `𝒜`.
* `AlgebraicGeometry.Space.laurentPieceTrivialization`: **a trivialization of `ℒ` over a chart
  trivializes every integer tensor power of `ℒ` over that chart.**
* `AlgebraicGeometry.Space.laurentPieceSectionsEquiv`: **over a chart `V` trivializing `ℒ` the
  sections of `ℒ^{⊗ n}` over `V` are the functions on `V`**, for every integer `n`.

## Main results

* `AlgebraicGeometry.Space.bijective_laurentDirectSumHom_app`: **the sections of the Laurent
  algebra sheaf over a quasi-compact étale chart `V` are `⨁_{n ∈ ℤ} Γ(V, ℒ^{⊗ n})`.**
* `AlgebraicGeometry.Space.bijective_laurentDirectSumHom_app_of_isAffine`: the same over an
  affine étale chart, an affine chart being a quasi-compact object of the small étale site.
* `AlgebraicGeometry.Space.bijective_laurentPieceTrivialization_app`: the degreewise
  trivialization on sections, over every object of the slice site over the chart.
* `AlgebraicGeometry.Space.exists_trivializing_cover_laurent`: **the charts trivializing `ℒ`
  cover `X`**, so the two results above compute the Laurent algebra over a covering family.

Together these say that over a quasi-compact chart `V` trivializing `ℒ` the sections of `𝒜` are
`⨁_{n ∈ ℤ} Γ(V, 𝒪_V)`, one copy of `Γ(V, 𝒪_V)` in each integer degree, and that such charts
cover `X`.

## What is not here

The identification is additive and degreewise.  It is **not** yet the statement that
`𝒜(V) = Γ(V, 𝒪_V)[t, t⁻¹]` as a *ring*, because nothing here identifies the generator of
`AlgebraicGeometry.Space.laurentPieceSectionsEquiv` in degree `n` with the `n`th power of the
degree-one generator.  The one statement that is missing is therefore:

> for a chart `V` and a trivialization `e` of `ℒ` over `V`, the generator of `ℒ^{⊗ n}` over `V`
> supplied by `AlgebraicGeometry.Space.laurentPieceTrivialization` is the `n`-fold product, under
> the coherent multiplication `Stacks.SheafOfModules.TensorPower.mulBilinear`, of the degree-one
> generator with itself — equivalently, the degree-one generator of a trivialization is a unit of
> `AlgebraicGeometry.Space.laurentCommPresheaf.obj (op V)` whose `n`th power generates the
> degree-`n` part.

At the scheme level that multiplicativity is
`Stacks.AlgebraicGeometry.TwistGenerator.genInt` together with
`Stacks.LineBundle.Situation.LaurentChart.coordinate_zpow_eq` and
`Stacks.LineBundle.Situation.LaurentChart.bijective_smul_genInt`, which is what makes
`Stacks.LineBundle.Situation.LaurentChart.homEquiv` an isomorphism onto
`LaurentPolynomial Γ(X, U)`.  Those are stated for `S : Scheme` and `U : S.Opens` and do not
transfer as they stand; the site-level generator family
`Stacks.SheafOfModules.TensorPower.sliceGeneratorIso` is indexed by `ℕ` and its additivity
`sliceGeneratorIso_add` is recorded as unproved in that file's own implementation notes.  So the
scheme-level identification does **not** transfer: what transfers is the sheafification step,
which is the part this file needed, and the degreewise trivialization, which is site-level
already.

## Corrections to notes elsewhere in the tree

Both concern the tag note on
`AlgebraicGeometry.Space.isAffineHom_multiplicativeTorsorSpectrumProjection`
(`StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorSpectrum`), which is a
registration comment and is not edited from here.

* That note's third gap, "no scheme-level smoothness, surjectivity or relative-dimension
  statement about `multiplicativeGroupBaseChange` exists", is **no longer true**.  Smoothness,
  surjectivity and affineness of `multiplicativeGroupBaseChange X ↘ X` are all available, as is
  a site-level layer — `Space.multiplicativeGroupChart`, `multiplicativeGroupChartHom`, its
  smoothness, surjectivity, affineness and local finite presentation, and the universal property
  `existsUnique_multiplicativeGroupChart_lift` — together with
  `Space.isSmooth_multiplicativeGroupSpace` and `LaurentPolynomial.ringKrullDim_eq_one`.  The
  note is accurate about the tree it was written in and false about the current state of the
  development.
* That note's first gap is the one addressed here, and its parenthetical diagnosis of it — "the
  sheafification step is unaccounted for" — is exactly right.  Its citation of
  `AlgebraicGeometry.Space.isPullback_affineChartSpec` is also correct: that declaration exists
  and does identify the relative spectrum over an affine chart with `Spec` of the algebra's
  sections there.

Taken together with the degreewise trivialization proved here, the remaining gap in clause (1)
of Tag 0EQG is the single multiplicativity statement displayed under "What is not here" above.

## Implementation notes

The three inputs are all in place already and none of them is rebuilt here.

* `Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app` is the site-generic statement
  that the sheafification unit of an objectwise direct sum of sheaves of modules is bijective on
  the sections over a quasi-compact object.  It is stated for an arbitrary Grothendieck topology
  and an arbitrary quasi-compact object, so no new sheaf theory is needed on the small étale
  site of an algebraic space.
* `AlgebraicGeometry.Space.isLocallyInjective_laurentRingUnit` and
  `AlgebraicGeometry.Space.isLocallySurjective_laurentRingUnit`, proved for the Laurent algebra
  in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.LaurentAlgebraQuasicoherence`, are the local
  bijectivity that `Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff` transfers across.
* `AlgebraicGeometry.Space.isQuasiCompactObject_of_isAffine` supplies quasi-compactness of an
  affine chart.

The comparison is phrased through the ring `AlgebraSheaf.ringSheafOfSite 𝒜` and the structure
map `AlgebraSheaf.structureMapOfSite 𝒜` rather than through
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule`, which is the spelling
`Stacks.GradedAlgebra.directSumHom` produces; the two are equal by
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule_eq_restrictScalars`, which is exactly how
`AlgebraicGeometry.Space.laurentDirectSumIsoUnderlyingModule` crosses between them.

The hypothesis is quasi-compactness of the chart and not affineness, even though the consumer
instantiates at an affine chart: quasi-compactness is what the proof uses, and the source's own
trivializing covering may be taken affine, so nothing is lost by stating the weaker hypothesis
and specializing.

Note that no local triviality of `ℒ` is needed for the identification of the sections.  Local
triviality enters one step later, in exhibiting a Laurent coordinate inside
`⨁_{n ∈ ℤ} Γ(V, ℒ^{⊗ n})`, and is therefore not a hypothesis here.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-- The comparison `⨁_{n ∈ ℤ} ℒ^{⊗ n} ⟶ 𝒜` from the objectwise direct sum of the integer tensor
powers of `ℒ` to the module underlying its Laurent algebra sheaf: on the sections over a chart,
the map reading a finite family of homogeneous sections as a section of `𝒜`. -/
def laurentDirectSumHom :=
  (laurentGradedAlgebra D p hp L hL).toPresheafGradedAlgebra.directSumHom
    (AlgebraSheaf.structureMapOfSite (laurentAlgebraSheaf D p hp L hL))
    (laurentRingUnit D p hp L hL) (structureHom_comp_laurentRingUnit D p hp L hL)

/-- **The sections of the Laurent algebra sheaf of `ℒ` over a quasi-compact étale chart `V` are
`⨁_{n ∈ ℤ} Γ(V, ℒ^{⊗ n})`**, the direct sum of the sections of the integer tensor powers of `ℒ`.

The Laurent algebra sheaf is a sheafification, so over a general chart its sections are strictly
larger: a section is only locally a finite sum of homogeneous ones.  Quasi-compactness of the
chart is what makes one covering of it by finitely many members suffice, so that the local
decompositions can be added up to a global one. -/
theorem bijective_laurentDirectSumHom_app (V : SmallEtale D.site D.base D.base_mem X)
    (hV : (SmallEtale.topology D.site D.base D.base_mem X).IsQuasiCompactObject V) :
    Function.Bijective
      (PresheafOfModules.Hom.app (laurentDirectSumHom D p hp L hL) (op V)) :=
  (Stacks.PresheafOfModules.bijective_sheafifyUnit_app_iff
      (𝟙 (tensorStructureSheaf D p hp).obj)
      (AlgebraSheaf.underlyingModule (laurentAlgebraSheaf D p hp L hL))
      (laurentDirectSumHom D p hp L hL)
      (Stacks.GradedAlgebra.isLocallyInjective_toPresheaf_map_directSumHom _ _ _ _
        (isLocallyInjective_laurentRingUnit D p hp L hL))
      (Stacks.GradedAlgebra.isLocallySurjective_toPresheaf_map_directSumHom _ _ _ _
        (isLocallySurjective_laurentRingUnit D p hp L hL))
      (op V)).1
    (Stacks.DirectSumSections.bijective_sheafifyUnit_directSum_app
      (fun n : ℤ => (laurentGradedAlgebra D p hp L hL).piece n) V hV)

/-- **The sections of the Laurent algebra sheaf of `ℒ` over an affine étale chart `V` are
`⨁_{n ∈ ℤ} Γ(V, ℒ^{⊗ n})`**: an affine chart is a quasi-compact object of the small étale
site. -/
theorem bijective_laurentDirectSumHom_app_of_isAffine
    (V : SmallEtale D.site D.base D.base_mem X)
    (hV : IsAffine ((SmallEtale.toOver D.site D.base D.base_mem X ⋙
      BigFppfOver.toScheme D.site D.base D.base_mem).obj V)) :
    Function.Bijective
      (PresheafOfModules.Hom.app (laurentDirectSumHom D p hp L hL) (op V)) :=
  bijective_laurentDirectSumHom_app D p hp L hL V
    (isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X V hV)

/-! ### A trivializing chart -/

section Trivialization

variable {V : SmallEtale D.site D.base D.base_mem X}
    (e : L.over V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over V))

/-- **Over an étale chart trivializing `ℒ`, every integer tensor power of `ℒ` is the structure
sheaf of the chart.**  One trivialization of `ℒ` trivializes every homogeneous piece of the
Laurent algebra at once, which is what makes the degreewise reading of its sections possible. -/
def laurentPieceTrivialization (n : ℤ) :
    ((laurentGradedAlgebra D p hp L hL).piece n).over V ≅
      SheafOfModules.unit ((tensorStructureSheaf D p hp).over V) :=
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  Stacks.SheafOfModules.TensorPower.overTensorPowerUnitIso
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L V e n

/-- **Over a chart trivializing `ℒ`, the sections of the degree-`n` piece `ℒ^{⊗ n}` of the
Laurent algebra are the functions on the chart**, for every integer `n`: the chart's
trivialization is a trivialization of every tensor power. -/
theorem bijective_laurentPieceTrivialization_app (n : ℤ) (W : (Over V)ᵒᵖ) :
    Function.Bijective
      ((laurentPieceTrivialization D p hp L hL e n).hom.val.app W) := by
  set ε := laurentPieceTrivialization D p hp L hL e n with hε
  exact Function.bijective_iff_has_inverse.2 ⟨ε.inv.val.app W,
    fun x => congrFun (congrArg (fun f => (f.val.app W : _ → _)) ε.hom_inv_id) x,
    fun y => congrFun (congrArg (fun f => (f.val.app W : _ → _)) ε.inv_hom_id) y⟩

/-- **Over a chart `V` trivializing `ℒ`, the sections of `ℒ^{⊗ n}` over `V` are the functions on
`V`**, for every integer `n`: `ℒ^{⊗ n}` is free of rank one on `V`.

This is `AlgebraicGeometry.Space.bijective_laurentPieceTrivialization_app` read at the terminal
object `(V, 𝟙 V)` of the slice site over `V`, where the sections of the restriction of a sheaf
of modules to the slice are by definition its sections over `V`. -/
def laurentPieceSectionsEquiv (n : ℤ) :
    ((laurentGradedAlgebra D p hp L hL).piece n).val.obj (op V) ≃
      (tensorStructureRingPresheaf D p hp).obj (op V) :=
  Equiv.ofBijective _
    (bijective_laurentPieceTrivialization_app D p hp L hL e n (op (Over.mk (𝟙 V))))

end Trivialization

include hL in
/-- **The charts trivializing `ℒ` cover `X`**, so that the identification of the sections of the
Laurent algebra sheaf over a trivializing chart is a computation over a covering family.  No
hypothesis beyond invertibility of `ℒ` is needed: local triviality of an invertible module on
the small étale site of an algebraic space is
`AlgebraicGeometry.Space.isLocallyTrivial_of_isInvertibleSheaf`. -/
theorem exists_trivializing_cover_laurent :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale D.site D.base D.base_mem X)
      (_ : (SmallEtale.topology D.site D.base D.base_mem X).CoversTop V),
      ∀ i, Nonempty (L.over (V i) ≅
        SheafOfModules.unit ((tensorStructureSheaf D p hp).over (V i))) :=
  (isLocallyTrivial_of_isInvertibleSheaf D p hp L hL).exists_trivializing_cover

end AlgebraicGeometry.Space

end
