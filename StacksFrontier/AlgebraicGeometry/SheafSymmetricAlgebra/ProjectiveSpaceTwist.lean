module

public import StacksFrontier.AlgebraicGeometry.AmpleProjectiveImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBundleProjectiveSpace.AffineBase
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.ProjectiveSpaceMorphism

/-!
# The hyperplane sheaf across the comparison of `ℙⁿ_X` with the projective bundle

`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/ProjectiveSpaceMorphism.lean` builds the
isomorphism of [Stacks, Tag 01OE] — projective `n`-space `ℙⁿ_X` over an arbitrary base scheme is
the projective bundle `𝐏(𝒪_X^{n+1}) = Proj_X(Sym(𝒪_X^{n+1}))`, over `X`. That file mentions no
twist. This one carries the hyperplane sheaf across the isomorphism as far as it goes.

The two `𝒪(1)`'s are built along different routes:

* `Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n X` is **defined** as the
  inverse image along `AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n X` of the
  twisting sheaf `𝒪(1)` of the integral model `ℙⁿ_ℤ`;
* `Stacks.Tag01VMVeryAmple.twistOne E` is the **glueing** of the degree-one twists of the affine
  charts of `Proj_X(Sym(E))` along [Stacks, Tag 01NO]'s comparisons.

What is unconditional here is the transport: the inverse image of the first along the Tag 01OE
isomorphism is the inverse image of the *integral* `𝒪(1)` along the descent
`Stacks.SymGraded.projectiveBundleToIntegralModel` of the chart comparisons. That is one
`AlgebraicGeometry.Scheme.Modules.pullbackComp` followed by one
`AlgebraicGeometry.Scheme.Modules.pullbackCongr`, exactly as in
`Stacks.ProjectiveCohomology.pullbackProjModelIsoHomProjectiveTwistingSheafIso` for the other
pair of models, and nothing in it is special to the degree `1`.

What remains — the comparison of that inverse image with the glued twist — is carried as the
named hypothesis `Stacks.SymGraded.HasFreeBundleTwistOne`, and the two readings of the module
half of Tag 01OE are proved equivalent to it. **Over an affine base that hypothesis is exactly
its chartwise form**, because the relative homogeneous spectrum over an affine base is its own
chart over `⊤`: there is nothing to glue. The chartwise form is then a theorem, in
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/ChartTwistOne.lean`, which also discharges
`HasFreeBundleTwistOne` over an affine base.

## Main definitions

* `Stacks.SymGraded.HasFreeBundleTwistOne`: the hypothesis that the inverse image of the integral
  `𝒪(1)` along `Stacks.SymGraded.projectiveBundleToIntegralModel` is `𝒪_{𝐏(𝒪_X^{n+1})}(1)`.
* `Stacks.SymGraded.HasChartTwistOne`: its chartwise form, asserted over each affine open of `X`
  separately.

## Main results

* `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_toIntegralAtUniverse`: the
  Tag 01OE isomorphism carries the projection of `ℙⁿ_X` to the integral model to
  `Stacks.SymGraded.projectiveBundleToIntegralModel`.
* `Stacks.SymGraded.pullbackProjectiveBundleIsoHomTwistingSheafIso`: **unconditionally**, the
  inverse image of `𝒪(1)` on `ℙⁿ_X` along the Tag 01OE isomorphism is the inverse image of the
  integral `𝒪(1)` along `Stacks.SymGraded.projectiveBundleToIntegralModel`.
* `Stacks.SymGraded.pullbackChartTwistingSheafIso`: over the chart of an affine open of `X`, that
  inverse image is the inverse image along the chart comparison, which is
  `AlgebraicGeometry.Proj.map` of the homogeneous coordinates.
* `Stacks.SymGraded.nonempty_pullback_projectiveSpaceTwistingSheaf_iso_twistOne` and
  `Stacks.SymGraded.hasFreeBundleTwistOne_of_nonempty`: the module half of Tag 01OE and
  `Stacks.SymGraded.HasFreeBundleTwistOne` imply one another.
* `Stacks.SymGraded.nonempty_iso_of_nonempty_pullback_iso`: an isomorphism of inverse images
  along an isomorphism of schemes comes from an isomorphism of the modules.
* `Stacks.SymGraded.hasFreeBundleTwistOne_of_hasChartTwistOne`: **over an affine base the
  chartwise comparison is the whole of the module half of Tag 01OE.**

## Implementation notes

**The projective bundle has two spellings and they agree by `rfl`.**
`Stacks.SymGraded.freeProjectiveBundle n` is the relative `Proj` of
`Stacks.SymGraded.freeSymGradedAlgebra (coordIndex n)`, while
`Stacks.Tag01VMVeryAmple.twistOne` is indexed by the relative `Proj` of
`Stacks.Tag01VMRelativeVeryAmple.symAlgebra E`. Both are
`Stacks.SymGraded.schemeSheafGradedAlgebra (freeModule (coordIndex n)) _` with a proof of the
`Prop` `Stacks.SymGraded.IsQuasicoherentPieces`, so they are definitionally equal and
`Stacks.SymGraded.freeProjectiveBundle_eq` records it.

**`HasFreeBundleTwistOne` is a hypothesis in this file, but it is no longer undischarged: both
it and `HasChartTwistOne` are proved in
`StacksFrontier/AlgebraicGeometry/SheafSymmetricAlgebra/ChartTwistOne.lean`**
(`Stacks.SymGraded.hasChartTwistOne` at every scheme and every `n`,
`Stacks.SymGraded.hasFreeBundleTwistOne` over an affine base). It is the module half of
Tag 01OE. Restricted along the chart of an affine open `U` of `X` the glued twist is the absolute
twist `𝒪(1)` of `Proj Γ(U, Sym(𝒪_X^{n+1}))`
(`Stacks.Tag01VMVeryAmple.twistOneChartIso`), and that graded ring is the polynomial ring
`Γ(X, U)[T₀, …, Tₙ]`; the inverse image of the integral `𝒪(1)` restricts on the same chart to the
inverse image along the coefficient change `ULift ℤ → Γ(X, U)`
(`Stacks.SymGraded.chart_comp_projectiveBundleToIntegralModel`). The proof does not route through
`Stacks.ProjectiveCohomology.HasPolyTwistTransport`, which would need the transport of that
statement along the identification of `Γ(U, Sym(𝒪_X^{n+1}))` with the polynomial ring: it inverts
[Stacks, Tag 01MY]'s comparison map at the homogeneous coordinates directly, factoring them
through `Stacks.SymGraded.chartGradedHom`, which **is** that identification and is a graded
isomorphism. Beyond the chartwise statement the hypothesis would need the chart isomorphisms to
be compatible with Tag 01NO's transitions, which is the gluing that
`Stacks.AlgebraicGeometry.ChartCocycleRigidity` performs for the twists themselves and not for a
comparison with an inverse image; that is why only the affine base is discharged.

**Over an affine base only the chartwise statement is owed.** `⊤` is then one of the affine
opens and its chart is an isomorphism
(`Stacks.AlgebraicGeometry.RelativeProjAffineBase.isIso_chart_top`), so
`Stacks.SymGraded.hasFreeBundleTwistOne_of_hasChartTwistOne` discharges
`HasFreeBundleTwistOne` from `HasChartTwistOne` with no compatibility condition at all. Since
[Stacks, Tag 01VT] hypothesises an affine base, that is the form its conditions (3) and (4)
actually need.

**No `stacks` attribute is attached.** The two assertions of Tag 01OE that are theorems already
carry it, on `Stacks.SymGraded.projectiveBundleIsoProjectiveSpace` and
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace_hom_comp_fst`; the module half is a
hypothesis here, so it has no covering set, and the unconditional result below is a comparison of
two inverse images rather than an assertion of the tag.

## References

* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.SymGraded

variable {X : Scheme.{u}} (n : ℕ)

/-! ### The two spellings of the projective bundle of `𝒪_X^{n+1}` -/

/-- **The projective bundle of `𝒪_X^{n+1}` is the relative `Proj` of `Sym(𝒪_X^{n+1})` at the
spelling `Stacks.Tag01VMVeryAmple.twistOne` is indexed by.** Both sides are the relative `Proj`
of `Stacks.SymGraded.schemeSheafGradedAlgebra (freeModule (coordIndex n))`, the two proofs of
quasi-coherence of the pieces being proofs of the same `Prop`. -/
theorem freeProjectiveBundle_eq :
    freeProjectiveBundle (X := X) n =
      Stacks.AlgebraicGeometry.RelativeProj.relativeProj
        (Stacks.Tag01VMRelativeVeryAmple.symAlgebra
          (freeModule (X := X) (coordIndex.{u} n))) :=
  rfl

/-! ### Transporting the hyperplane sheaf along the Tag 01OE isomorphism -/

/-- **The Tag 01OE isomorphism carries the projection of `ℙⁿ_X` to the integral model to the
descent of the chart comparisons.** This is
`Stacks.SymGraded.projectiveBundleToProjectiveSpace_snd` read through
`Stacks.SymGraded.projectiveBundleIsoProjectiveSpace`, whose underlying morphism is the
comparison itself. -/
theorem projectiveBundleIsoProjectiveSpace_hom_comp_toIntegralAtUniverse :
    (projectiveBundleIsoProjectiveSpace (X := X) n).hom ≫
        AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n X =
      projectiveBundleToIntegralModel n :=
  projectiveBundleToProjectiveSpace_snd n

/-- **The inverse image of `𝒪(1)` on `ℙⁿ_X` along the Tag 01OE isomorphism is the inverse image
of the integral `𝒪(1)` along the descent of the chart comparisons.**

Unconditional: `𝒪(1)` on `ℙⁿ_X` is *defined* as the inverse image of the integral model's
twisting sheaf along the projection to it, and the Tag 01OE isomorphism carries that projection
to `Stacks.SymGraded.projectiveBundleToIntegralModel`. Nothing here is specific to the
degree `1`. -/
def pullbackProjectiveBundleIsoHomTwistingSheafIso :
    (Scheme.Modules.pullback (projectiveBundleIsoProjectiveSpace (X := X) n).hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n X) ≅
      (Scheme.Modules.pullback (projectiveBundleToIntegralModel (X := X) n)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) :=
  (Scheme.Modules.pullbackComp (projectiveBundleIsoProjectiveSpace (X := X) n).hom
      (AlgebraicGeometry.projectiveSpaceOver.toIntegralAtUniverse n X)).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (projectiveBundleIsoProjectiveSpace_hom_comp_toIntegralAtUniverse (X := X) n)).app _

/-- **Over a chart, the inverse image of the integral `𝒪(1)` is the inverse image along the
chart comparison.** The chart of an affine open `U` of `X` composed with the descent is the chart
comparison `Stacks.SymGraded.chartToProjectiveSpace`, which is
`AlgebraicGeometry.Proj.map` of the homogeneous coordinates
`Stacks.SymGraded.chartCoordHom n U : ℤ[T₀, …, Tₙ] → Γ(U, Sym(𝒪_X^{n+1}))`.

Together with `Stacks.Tag01VMVeryAmple.twistOneChartIso`, which identifies the restriction of
`𝒪_{𝐏(𝒪_X^{n+1})}(1)` along the same chart with the absolute twist `𝒪(1)` of
`Proj Γ(U, Sym(𝒪_X^{n+1}))`, this exhibits what
`Stacks.SymGraded.HasFreeBundleTwistOne` asks for chartwise: that the inverse image of the
integral `𝒪(1)` along `Proj.map` of the homogeneous coordinates is the degree-one twist of the
target graded ring. -/
def pullbackChartTwistingSheafIso (U : X.Opens) (hU : IsAffineOpen U) :
    (Scheme.Modules.pullback ((freeProjectiveBundle (X := X) n).chart U hU)).obj
        ((Scheme.Modules.pullback (projectiveBundleToIntegralModel (X := X) n)).obj
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n)) ≅
      (Scheme.Modules.pullback (chartToProjectiveSpace n U)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) :=
  (Scheme.Modules.pullbackComp ((freeProjectiveBundle (X := X) n).chart U hU)
      (projectiveBundleToIntegralModel (X := X) n)).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (chart_comp_projectiveBundleToIntegralModel n U hU)).app _

/-! ### The module half of Tag 01OE as a hypothesis -/

/-- **The module half of [Stacks, Tag 01OE]**, as a hypothesis in the form the integral model
leaves it in: the inverse image of the integral `𝒪(1)` along
`Stacks.SymGraded.projectiveBundleToIntegralModel` is the degree-one twist
`𝒪_{𝐏(𝒪_X^{n+1})}(1)` of the projective bundle. -/
def HasFreeBundleTwistOne (X : Scheme.{u}) (n : ℕ) : Prop :=
  Nonempty ((Scheme.Modules.pullback (projectiveBundleToIntegralModel (X := X) n)).obj
      (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅
    Stacks.Tag01VMVeryAmple.twistOne (freeModule (X := X) (coordIndex.{u} n)))

/-- **The module half of [Stacks, Tag 01OE] from
`Stacks.SymGraded.HasFreeBundleTwistOne`**: the inverse image of `𝒪(1)` on `ℙⁿ_X` along the
Tag 01OE isomorphism is `𝒪_{𝐏(𝒪_X^{n+1})}(1)`. -/
theorem nonempty_pullback_projectiveSpaceTwistingSheaf_iso_twistOne
    (h : HasFreeBundleTwistOne X n) :
    Nonempty ((Scheme.Modules.pullback (projectiveBundleIsoProjectiveSpace (X := X) n).hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n X) ≅
      Stacks.Tag01VMVeryAmple.twistOne (freeModule (X := X) (coordIndex.{u} n))) :=
  h.elim fun e => ⟨pullbackProjectiveBundleIsoHomTwistingSheafIso n ≪≫ e⟩

/-- **`Stacks.SymGraded.HasFreeBundleTwistOne` from the module half of [Stacks, Tag 01OE]**, so
that the hypothesis is no stronger than the statement it stands for. -/
theorem hasFreeBundleTwistOne_of_nonempty
    (h : Nonempty ((Scheme.Modules.pullback
        (projectiveBundleIsoProjectiveSpace (X := X) n).hom).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n X) ≅
      Stacks.Tag01VMVeryAmple.twistOne (freeModule (X := X) (coordIndex.{u} n)))) :
    HasFreeBundleTwistOne X n :=
  h.elim fun e => ⟨(pullbackProjectiveBundleIsoHomTwistingSheafIso n).symm ≪≫ e⟩

/-! ### Over an affine base there is nothing to glue -/

/-- **An isomorphism of inverse images along an isomorphism of schemes comes from an isomorphism
of the modules themselves.** The inverse image along the inverse is a quasi-inverse of the
inverse image, by pseudofunctoriality. -/
theorem nonempty_iso_of_nonempty_pullback_iso {Y Z : Scheme.{u}} (c : Y ⟶ Z) [IsIso c]
    (M N : Z.Modules)
    (h : Nonempty ((Scheme.Modules.pullback c).obj M ≅ (Scheme.Modules.pullback c).obj N)) :
    Nonempty (M ≅ N) := by
  obtain ⟨e⟩ := h
  have hid : CategoryTheory.inv c ≫ c = 𝟙 Z := IsIso.inv_hom_id c
  have u : ∀ P : Z.Modules, (Scheme.Modules.pullback (CategoryTheory.inv c)).obj
      ((Scheme.Modules.pullback c).obj P) ≅ P := fun P =>
    (Scheme.Modules.pullbackComp (CategoryTheory.inv c) c).app P ≪≫
      (Scheme.Modules.pullbackCongr hid).app P ≪≫ (Scheme.Modules.pullbackId Z).app P
  exact ⟨(u M).symm ≪≫ (Scheme.Modules.pullback (CategoryTheory.inv c)).mapIso e ≪≫ u N⟩

/-- **The chartwise form of the module half of [Stacks, Tag 01OE]**, as a hypothesis: over every
affine open `U` of `X`, the inverse image of the integral `𝒪(1)` along the chart comparison
`Stacks.SymGraded.chartToProjectiveSpace` — that is, along `AlgebraicGeometry.Proj.map` of the
homogeneous coordinates `ℤ[T₀, …, Tₙ] → Γ(U, Sym(𝒪_X^{n+1}))` — is the degree-one twist of the
target graded ring.

This is [Stacks, Tag 01N2] clause (3) in degree one, at a graded ring homomorphism whose
coefficient part is `ULift ℤ → Γ(X, U)`; compare
`Stacks.ProjectiveCohomology.HasPolyTwistTransport`, which is the same assertion at the
polynomial grading itself. -/
def HasChartTwistOne (X : Scheme.{u}) (n : ℕ) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    Nonempty ((Scheme.Modules.pullback (chartToProjectiveSpace (X := X) n U)).obj
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} n) ≅
      AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf
        ((Stacks.Tag01VMRelativeVeryAmple.symAlgebra
          (freeModule (X := X) (coordIndex.{u} n))).grading U) 1)

/-- **Over an affine base the chartwise comparison is the whole of the module half of
[Stacks, Tag 01OE]**: no glueing is involved.

The relative homogeneous spectrum over an affine base *is* the chart over `⊤`
(`Stacks.AlgebraicGeometry.RelativeProjAffineBase.isIso_chart_top`), so the two modules on the
bundle may be compared after inverse image along that one chart, where
`Stacks.SymGraded.pullbackChartTwistingSheafIso` and
`Stacks.Tag01VMVeryAmple.twistOneChartIso` reduce the question to the hypothesis at `⊤`. -/
theorem hasFreeBundleTwistOne_of_hasChartTwistOne [IsAffine X] (h : HasChartTwistOne X n) :
    HasFreeBundleTwistOne X n := by
  have hS : IsAffineOpen (⊤ : X.Opens) := AlgebraicGeometry.isAffineOpen_top X
  let _ : IsOpenImmersion ((freeProjectiveBundle (X := X) n).chart ⊤ hS) :=
    Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart
      (freeProjectiveBundle (X := X) n) ⊤ hS
  let _ : IsIso ((freeProjectiveBundle (X := X) n).chart ⊤ hS) :=
    Stacks.AlgebraicGeometry.RelativeProjAffineBase.isIso_chart_top
      (freeSymGradedAlgebra (X := X) (coordIndex.{u} n)).toGradedAlgebra hS
  refine nonempty_iso_of_nonempty_pullback_iso
    ((freeProjectiveBundle (X := X) n).chart ⊤ hS) _ _ ?_
  obtain ⟨α⟩ := h ⊤ hS
  exact ⟨pullbackChartTwistingSheafIso n ⊤ hS ≪≫ α ≪≫
    (Stacks.Tag01VMVeryAmple.twistOneChartIso
      (freeModule (X := X) (coordIndex.{u} n)) ⊤ hS).symm ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback
      ((freeProjectiveBundle (X := X) n).chart ⊤ hS)).app _⟩

end Stacks.SymGraded

end
