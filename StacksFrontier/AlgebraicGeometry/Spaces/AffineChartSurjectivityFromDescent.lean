module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import
  StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineGeneratedRelations
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.H1Vanishing

/-!
# Surjectivity on affine-chart sections by faithfully flat descent

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let
`q : P ⟶ Q` be an epimorphism of `𝒪_F`-modules.  This file proves that `q` is surjective on the
sections over every affine étale chart as soon as **both** `P` and `Q` are cartesian on affine
charts — in particular, unconditionally, whenever both are quasi-coherent.

No cohomology is used.  An epimorphism of sheaves of modules is locally surjective, so a section
of `Q` over an affine chart `W` is a value of `q` on some covering sieve of `W`; that sieve
contains a finite family of affine étale charts whose restriction maps on regular functions are
jointly faithfully flat, and membership in the image of a map of modules descends along a
faithfully flat base change.  The two base change comparisons the descent consumes are exactly the
two halves of `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`: surjectivity of the comparison
for the *source* and injectivity of the comparison for the *target*.

## Main results

* `AlgebraicGeometry.Space.jointlyDetectsRange_of_isCartesianOnAffineCharts`: a finite jointly
  faithfully flat family of affine étale charts jointly detects the image of `q`, when the source
  and the target of `q` are cartesian on affine charts.
* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isCartesianOnAffineCharts`: **an
  epimorphism of `𝒪_F`-modules with cartesian source and cartesian target is surjective on the
  sections over an affine étale chart.**
* `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite`: **the same for an
  epimorphism of quasi-coherent `𝒪_F`-modules, unconditionally.**

## Implementation notes

**What is proved, and what is not.**  The conclusion is the *restated* form of Descent,
Proposition 03DW: cartesianness is asked of the source and of the target of `q`, not of its
kernel.  The literal uniform hypothesis carried at fifteen binder sites in this tree reads

    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W)))

— five in `StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity`, three in
`StacksFrontier.AlgebraicGeometry.Spaces.CokernelShortExactEssSurj`, three in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentColimitsEssSurj`, three in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison` and one in
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClosureEssSurj` — and **this file does not
discharge it as written.**  Cartesianness of `kernel q` alone does not supply either input of the
descent: the descent needs the base change comparison of the *source* to be surjective and that
of the *target* to be injective, and neither is a consequence of a statement about the kernel.
Routing the literal form through the long exact sequence is what needs the vanishing of a first
cohomology group, and **that vanishing is proved**:
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isCartesianOnAffineCharts_kernel` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromAmitsur` discharges the literal
form with no hypothesis, by computing the first Čech cohomology of the kernel along a finite
affine covering family as the degree-one cohomology of an Amitsur complex.  What is below is the
cheaper statement, with no cohomology at all, and the sites that already hold cartesianness of
the source and the target may keep using it.

The restatement nevertheless serves all fifteen sites, because at every one of them the modules
substituted for `P` and `Q` *are* cartesian on affine charts — that is precisely where the
cartesianness of the kernel comes from there, via
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernel`.  Serving the sites is not the same as
discharging the binder, and only the former is claimed.

**No `@[stacks 03DW]` attribute is claimed.**  The statement proved is not Stacks 03DW, whose
content is the vanishing of the higher étale cohomology of a quasi-coherent module on an affine,
nor the uniform form of its consequence spelled above; tagging a restatement would report a
different theorem as the tag.

**Why this is not circular, and where the strength comes from.**  The hypotheses are not deferred:
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, the forward
implication of Descent, Proposition 03DX(2), is unconditional in this tree, so
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isQuasicoherentOnSite` is an unconditional
theorem about quasi-coherent modules.  The descent route
(`AlgebraicGeometry.Space.SmallEtale.surjective_val_app_mkId_of_epi_of_hasSectionBaseChangeOn`)
could only ever take a coproduct of copies of the structure sheaf as its source, because
`SheafOfModules.bijective_liftBaseChange_of_tautBasis` was its only source of that surjectivity;
03DX(2) replaces it for an arbitrary quasi-coherent source.

**`IsCartesianOnAffineCharts` needs no adapter.**  It is literally the bijectivity of
`AlgebraicGeometry.Space.sectionsBaseChange`, which is
`LinearMap.liftBaseChange (chartRestrictLinear …)`, so its two halves are the hypotheses `hP` and
`hN` of `Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange` as they stand.

The private helper below is the same statement as the private helper of the same name in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeChartSections`, which is sealed there; neither
module imports the other, so the duplication is confined to this file.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### A jointly faithfully flat finite family of affine charts inside a covering sieve -/

variable {B S hS F hF}

/-! ### Joint detection of images along a finite faithfully flat family of charts -/

/-- **A finite jointly faithfully flat family of affine étale charts jointly detects the image of
a morphism whose source and target are cartesian on affine charts.**

A section of the target over the chart which is a value of `q` over every member of the family is
a value of `q` over the chart itself.  The base change along a chart restriction of the sections
of the source is onto the sections of the source over the member, and that of the sections of the
target injects into the sections of the target over the member: these are the surjectivity half
of `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` for the source and the injectivity half of
it for the target.  So `Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange`
applies, the two commuting squares being the naturality of `q`. -/
theorem jointlyDetectsRange_of_isCartesianOnAffineCharts {P Q : Modules.{u, u} B S hS F hF}
    (q : P ⟶ Q) (hP : IsCartesianOnAffineCharts P) (hQ : IsCartesianOnAffineCharts Q)
    {W : SmallEtale B S hS F}
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    {n : ℕ} {z : Fin n → SmallEtale B S hS F} (φ : ∀ i, z i ⟶ W)
    (hz : ∀ i, IsAffine
      ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj (z i)))
    (hff : (RingHom.pi fun i => chartRestrict (hF := hF) (φ i)).FaithfullyFlat) :
    SheafOfModules.JointlyDetectsRange.{0} q φ := by
  intro y hy
  let algI : ∀ i, Algebra (chartRing B S hS F hF W) (chartRing B S hS F hF (z i)) :=
    fun i => chartAlgebra (hF := hF) (φ i)
  let modP : ∀ i, Module (chartRing B S hS F hF W) (P.val.obj (op (z i))) :=
    fun i => chartSectionsModule P (φ i)
  let modQ : ∀ i, Module (chartRing B S hS F hF W) (Q.val.obj (op (z i))) :=
    fun i => chartSectionsModule Q (φ i)
  have towP : ∀ i, IsScalarTower (chartRing B S hS F hF W) (chartRing B S hS F hF (z i))
      (P.val.obj (op (z i))) := fun i => chartSections_isScalarTower P (φ i)
  have towQ : ∀ i, IsScalarTower (chartRing B S hS F hF W) (chartRing B S hS F hF (z i))
      (Q.val.obj (op (z i))) := fun i => chartSections_isScalarTower Q (φ i)
  have hFF : Module.FaithfullyFlat (chartRing B S hS F hF W)
      (∀ i, chartRing B S hS F hF (z i)) := hff
  exact Module.BaseChange.mem_range_of_forall_mem_range_of_liftBaseChange
    (chartRing B S hS F hF W) (fun i => chartRing B S hS F hF (z i))
    (PT := P.val.obj (op W)) (NT := Q.val.obj (op W))
    (PW := fun i => P.val.obj (op (z i))) (NW := fun i => Q.val.obj (op (z i)))
    (q.val.app (op W)).hom (fun i => (q.val.app (op (z i))).hom)
    (fun i => chartRestrictLinear P (φ i)) (fun i => chartRestrictLinear Q (φ i))
    (fun i x => (PresheafOfModules.naturality_apply q.val (φ i).op x).symm)
    (fun i => (hP W (z i) hW (hz i) (φ i)).2)
    (fun i => (hQ W (z i) hW (hz i) (φ i)).1)
    fun i => hy i

/-! ### Surjectivity on the sections over an affine chart -/

/-- **An epimorphism of `𝒪_F`-modules whose source and target are cartesian on affine charts is
surjective on the sections over every affine étale chart.**

An epimorphism of sheaves of modules is locally surjective, so each section of the target over
the chart is a value of `q` on some covering sieve; that sieve contains a finite family of affine
étale charts whose chart restrictions are jointly faithfully flat
(`AlgebraicGeometry.Space.SmallEtale.exists_finite_affine_etale_ofArrows_le`), the family detects
the image by
`AlgebraicGeometry.Space.jointlyDetectsRange_of_isCartesianOnAffineCharts`, and
`SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange` concludes.  No cohomology
vanishing is used.

This is the restated form of the uniform hypothesis `h03DW` of this tree, with cartesianness
asked of the source and the target rather than of the kernel; see the implementation notes for
why the literal form is not discharged here. -/
theorem surjective_val_app_of_epi_of_isCartesianOnAffineCharts
    {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q) (hq : Epi q)
    (hP : IsCartesianOnAffineCharts P) (hQ : IsCartesianOnAffineCharts Q)
    (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (q.val.app (op W)) := by
  refine SheafOfModules.surjective_val_app_of_epi_of_jointlyDetectsRange.{0} q fun Sv hSv => ?_
  obtain ⟨n, z, φ, hzaff, hzT, hff⟩ :=
    exists_finite_affine_faithfullyFlat_pi_le B S hS F hF hW hSv
  exact ⟨Fin n, z, φ, hzT,
    jointlyDetectsRange_of_isCartesianOnAffineCharts q hP hQ hW φ hzaff hff⟩

/-- **An epimorphism of quasi-coherent `𝒪_F`-modules is surjective on the sections over every
affine étale chart.**

This is `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_isCartesianOnAffineCharts` with both
of its hypotheses supplied by the forward implication of Descent, Proposition 03DX(2),
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, which is
unconditional; so this statement is unconditional. -/
theorem surjective_val_app_of_epi_of_isQuasicoherentOnSite
    {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q) (hq : Epi q)
    (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (W : SmallEtale B S hS F)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Surjective (q.val.app (op W)) :=
  surjective_val_app_of_epi_of_isCartesianOnAffineCharts q hq
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF P hP)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF Q hQ) W hW

end AlgebraicGeometry.Space

end
