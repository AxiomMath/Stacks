module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedTargetDifferential
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AbelianOfSmallSite
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.DerivedFunctor

/-!
# The two squares of Section 0FMK, reduced to the step of the filtration

`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSquares` builds
[Stacks, Section 0FMK] at the level of complexes,

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`

for `f : X ⟶ Y` smooth over a base `S`, from two squares against the differentials — the one in
the degree of the cut and the ones above it. **This file replaces each of those squares by a
square on the `k`-th step `F^kΩ^•_{X/S}` of the filtration**, which is where the mathematics
lives: the differential of a graded piece is the differential of the step read modulo the next
step, so nothing about a graded piece's differential can be checked except through the
projection onto it.

That projection, `CategoryTheory.FilteredObject.grMapπ`, is an epimorphism degreewise
(`CategoryTheory.FilteredObject.stepShortComplex_shortExact`), and it carries the differential of
the
step to the differential of the graded piece — its own
`HomologicalComplex.Hom.comm`. So a square on the graded piece follows from the square obtained
by precomposing with it, and that is the whole content of the two reductions below. In the
degree of the cut the projection is moreover *invertible*
(`Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX_inv`, the next step having vanished there), so
the reduction at the cut needs no epimorphism and its square is an equivalent statement rather
than a sufficient one.

Nothing mathematical is proved here. What is left owed after this file is, in both degrees, two
things. One is the **Leibniz rule** `AlgebraicGeometry.SheafOfModules.summandOfEq_d` read on the
step: the term `dω ∧ η` of `d(ω ∧ η)` lies in the next step of the filtration when `ω` is a
pulled-back `k`-form, so modulo that step the differential is `(-1)^k(1 ⊗ d_{X/S})`. That is
available, as
`AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_cokernelπ_prodWedgeHomOfEq`. The other is
that `d_{X/S}` induces `d_{X/Y}` on the quotient, which is the sign and the differential
`Stacks.DeRhamSmooth.gradedTargetComplex_d` carries, and that is not available; see the
docstring of `Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfStepSquares` for what
exactly it needs.

## Main results

* `Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom`: **the comparison at the
  cut, read on the projection onto the graded piece** — the leading
  `Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX` of that comparison is cancelled against the
  projection, leaving the three crossings that are about the step.
* `Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom_comp_d`: the same with
  the differential of the target complex computed by
  `Stacks.DeRhamSmooth.gradedTargetXIso_inv_comp_d`, so that no transport of a degree and no
  differential of the target complex is left in it.
* `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXAtCut_comm_of_step_square`: **the square in
  the degree of the cut, from a square on the step.**
* `Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetX_comm_of_step_square`: **the squares above
  the cut, from squares on the step.**
* `Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfStepSquares`: **Section 0FMK at the
  level of complexes granted only those two squares** — no graded piece of the filtered complex
  and no differential of the target complex is left in either hypothesis.

## Implementation notes

The cancellation of the leading factor is isolated in
`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom`, whose goal carries one
isomorphism and the projection and nothing else — the shape that has paid at these binders,
where the same cancellation inside a goal that also carries two differentials is not free. It
holds because the comparison at the cut is a right-nested `≪≫`, so its `hom` is
right-associated on the nose and `CategoryTheory.Iso.inv_hom_id_assoc` applies with no
reassociation at all.

Every associativity is applied as a term rather than rewritten, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothGradedPieceCut`: these goals are not type-correct at
the `implicit` transparency level that `rw` and `simp` match at.

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.DeRhamDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace Stacks.DeRhamSmooth

/-! The derived-category and abelian structures, pinned rather than restated exactly as in
`StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceFiltered`: resolving them at the
concrete inverse-image ringed space exceeds the default instance-synthesis budget. -/
attribute [local instance] Stacks.SheafOfModules.abelianOfSmallSite
attribute [local instance] AlgebraicGeometry.SheafOfModules.abelianModules

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The comparison of Section 0FMK in the degree of the cut, read on the projection onto the
graded piece.** In that degree the projection is the inverse of
`Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX`
(`Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX_inv`), which is the leading factor of the
comparison, so precomposing with the projection cancels it and leaves the three crossings that
are about the step `F^kΩ^k_{X/S}`.

Isolated in a statement of its own: the goal here carries one isomorphism and the projection,
and the cancellation is free, while the same cancellation inside a square that also carries the
two differentials is not. Because
`Stacks.DeRhamSmooth.gradedPieceXIsoGradedTargetXAtCut` is a right-nested `≪≫`, its `hom` is
right-associated on the nose and `CategoryTheory.Iso.inv_hom_id_assoc` applies with no
reassociation.

Costs 24,651 heartbeats against the default budget of 200,000. -/
theorem grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom [Smooth f] (k : ℕ) :
    (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
          (deRhamSmoothFiltration f g)).f (k : ℤ) ≫
        (gradedPieceXIsoGradedTargetXAtCut f g k).hom =
      (filtrationXIsoCutWedgeSource f g k).hom ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
            (cutWedgeSourceIsoPullbackTensor f g k).hom ≫
          (gradedSourceMixedTensorCoefficientIso f g k
            (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))).inv ≫
            (gradedTargetXIso f g k 0 k (by omega)).inv :=
  Eq.trans
    (congrArg (fun u => u ≫ (gradedPieceXIsoGradedTargetXAtCut f g k).hom)
      (gradedPieceXIsoFiltrationX_inv f g (k : ℤ) (k : ℤ) le_rfl).symm)
    (Iso.inv_hom_id_assoc _ _)

/-- **`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom` against the
differential of the target complex.** The comparison at the cut ends in the inverse of
`Stacks.DeRhamSmooth.gradedTargetXIso` at `j = 0`, `n = k`, so
`Stacks.DeRhamSmooth.gradedTargetXIso_inv_comp_d` computes what follows it: the differential of
the target complex becomes `(-1)^k(1 ⊗ d_{X/Y})` between the degrees `0` and `1` that
Section 50.12 names, followed by the inverse of the comparison one degree up.

No transport of a degree and no differential of the target complex is left, so what the square
at the cut still owes is only the graded-piece side.

Costs 33,620 heartbeats against the default budget of 200,000. -/
theorem grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom_comp_d [Smooth f] (k : ℕ) :
    (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
          (deRhamSmoothFiltration f g)).f (k : ℤ) ≫
        ((gradedPieceXIsoGradedTargetXAtCut f g k).hom ≫
          (gradedTargetComplex f g k).d ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ)) =
      (filtrationXIsoCutWedgeSource f g k).hom ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
            (cutWedgeSourceIsoPullbackTensor f g k).hom ≫
          (gradedSourceMixedTensorCoefficientIso f g k
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))).inv ≫
            ((-1 : ℤ) ^ k • (coefficientRestriction f g).map
                ((pulledBackTargetFormsTensor f g k).map
                  ((deRhamCochainXIso f 0).inv ≫
                    (deRhamCochainComplex f).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) ≫
                      (deRhamCochainXIso f (0 + 1)).hom))) ≫
              (gradedTargetXIso f g k (0 + 1) (k + 1 + 0) (by omega)).inv := by
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun u => u ≫ (gradedTargetComplex f g k).d ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ))
    (grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom f g k)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ u) (Category.assoc _ _ _)) ?_
  refine Eq.trans (congrArg (fun u => _ ≫ _ ≫ u) (Category.assoc _ _ _)) ?_
  exact congrArg (fun u => _ ≫ _ ≫ _ ≫ u)
    (gradedTargetXIso_inv_comp_d f g k 0 k (k + 1 + 0) (by omega) (by omega))

/-- **The square of Section 0FMK in the degree of the cut, from a square on the step of the
filtration.** The hypothesis is the same square with the graded piece replaced by the `k`-th
step: on the left the comparison at the cut read on the projection and with the differential of
the target complex computed
(`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom_comp_d`), on the right the
differential of the step followed by the projection in the target degree.

In this degree the projection onto the graded piece is *invertible* — the next step has already
vanished there (`Stacks.DeRhamSmooth.gradedPieceXIsoFiltrationX_inv`) — so no epimorphism is
cancelled and the hypothesis is an equivalent statement of the conclusion, not merely a
sufficient one. The conclusion is the hypothesis `hcut` of
`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSquares`, in its degrees on the nose.

Costs 26,844 heartbeats against the default budget of 200,000. -/
theorem gradedPieceXIsoGradedTargetXAtCut_comm_of_step_square [Smooth f] (k : ℕ)
    (hsq : (filtrationXIsoCutWedgeSource f g k).hom ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
            (cutWedgeSourceIsoPullbackTensor f g k).hom ≫
          (gradedSourceMixedTensorCoefficientIso f g k
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))).inv ≫
            ((-1 : ℤ) ^ k • (coefficientRestriction f g).map
                ((pulledBackTargetFormsTensor f g k).map
                  ((deRhamCochainXIso f 0).inv ≫
                    (deRhamCochainComplex f).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) ≫
                      (deRhamCochainXIso f (0 + 1)).hom))) ≫
              (gradedTargetXIso f g k (0 + 1) (k + 1 + 0) (by omega)).inv =
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
          ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + 0 : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k 0).hom) :
    (gradedPieceXIsoGradedTargetXAtCut f g k).hom ≫
        (gradedTargetComplex f g k).d ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) =
      (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d
          ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) ≫
        (gradedPieceXIsoGradedTargetX f g k 0).hom := by
  refine (Iso.cancel_iso_inv_left (gradedPieceXIsoFiltrationX f g (k : ℤ) (k : ℤ) le_rfl)
    _ _).1 ?_
  refine Eq.trans (congrArg
    (fun u => u ≫ ((gradedPieceXIsoGradedTargetXAtCut f g k).hom ≫
      (gradedTargetComplex f g k).d ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ)))
    (gradedPieceXIsoFiltrationX_inv f g (k : ℤ) (k : ℤ) le_rfl)) ?_
  refine Eq.trans (grMapπ_f_gradedPieceXIsoGradedTargetXAtCut_hom_comp_d f g k)
    (Eq.trans hsq ?_)
  rw [gradedPieceXIsoFiltrationX_inv]
  exact (HomologicalComplex.Hom.comm_assoc _ _ _ _).symm

/-- **The squares of Section 0FMK above the cut, from squares on the step of the filtration.**
The hypothesis is the same square with both graded pieces reached through the projection out of
the `k`-th step, and the conclusion is the hypothesis `hup` of
`Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSquares` at the offset `j`, in its
degrees on the nose.

Above the cut the projection is only an epimorphism
(`CategoryTheory.FilteredObject.stepShortComplex_shortExact`) and not invertible, so this is a
sufficient condition and not an equivalent one; what makes it sufficient is that the projection
carries the differential of the step to the differential of the graded piece, which is its own
`HomologicalComplex.Hom.comm` and the only thing used here.

Costs 16,274 heartbeats against the default budget of 200,000. -/
theorem gradedPieceXIsoGradedTargetX_comm_of_step_square [Smooth f] (k j : ℕ)
    (hsq : (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + j : ℕ) : ℤ) ≫
        ((gradedPieceXIsoGradedTargetX f g k j).hom ≫
          (gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ)) =
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
          ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k (j + 1)).hom) :
    (gradedPieceXIsoGradedTargetX f g k j).hom ≫
        (gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) =
      (gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g)).d
          ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
        (gradedPieceXIsoGradedTargetX f g k (j + 1)).hom := by
  have : Epi ((FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
      (deRhamSmoothFiltration f g)).f ((k + 1 + j : ℕ) : ℤ)) :=
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).1
      (FilteredObject.stepShortComplex_shortExact (FilteredObject.succHom (k : ℤ))
        (deRhamSmoothFiltration f g)) ((k + 1 + j : ℕ) : ℤ)).epi_g
  refine (cancel_epi ((FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
    (deRhamSmoothFiltration f g)).f ((k + 1 + j : ℕ) : ℤ))).1 (Eq.trans hsq ?_)
  exact (HomologicalComplex.Hom.comm_assoc _ _ _ _).symm

/-- **Stacks Project, Section 0FMK, at the level of complexes, granted only the two squares on
the step of the filtration.** For `f : X ⟶ Y` smooth over a base `S` and a cut `k`,

`gr^kΩ^•_{X/S}  ≅  f^{-1}Ω^k_{Y/S}[-k] ⊗_{f^{-1}𝒪_Y} Ω^•_{X/Y}`.

This is `Stacks.DeRhamSmooth.gradedPieceIsoGradedTargetComplexOfSquares` with both of its
squares reduced by the two results above, so that **no graded piece of the filtered complex and
no differential of the target complex appears in either hypothesis**: each is a square on the
`k`-th step `F^kΩ^•_{X/S}`, read through the projection onto the graded piece, with the
differential of the target already computed to `(-1)^k(1 ⊗ d_{X/Y})` in the degree of the cut.

**What is still owed is exactly these two squares.** The Leibniz rule
`AlgebraicGeometry.SheafOfModules.summandOfEq_d` is one half of each: the differential of the
`(k, j)` summand of the wedge map is the `(k + 1, j)` summand precomposed with `d ⊗ 1`, which
factors through degree `k + 1` of the pulled-back forms and so dies under the projection onto
the graded piece, plus `(-1)^k` times the `(k, j + 1)` summand precomposed with `1 ⊗ d`.

**That half is available, and so is the whole of the graded-piece side of the square.** The
vanishing of the first term is
`AlgebraicGeometry.SheafOfModules.summandOfEq_d_comp_cokernelπ_prodWedgeHomOfEq` of
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeSummandLeibnizModStep`, which reads the rule in the
quotient by the step at `k + 1` and leaves only the signed term; the compatibility of the whole
of `Stacks.DeRhamSmooth.gradedPieceXIsoExteriorGraded` with the projection is
`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoExteriorGraded_hom_comp_arrow`, which assembles the
seven per-step compatibilities; and above the cut the two combine into
`Stacks.DeRhamSmooth.grMapπ_f_gradedPieceXIsoGradedTargetX_hom_comp_toStepQuotient`, which says
that the projection followed by the degreewise comparison and the reading into
`Ω^n_{X/S}/F^{k+1}Ω^n_{X/S}` is the inclusion of the step followed by that quotient's
projection. The reading itself, `Stacks.DeRhamSmooth.gradedTargetXToStepQuotient`, is a
monomorphism (`Stacks.DeRhamSmooth.mono_gradedTargetXToStepQuotient`), so a square above the cut
may be checked after composing with it.

**What the other half of each square needs is that `d_{X/Y}` is induced by `d_{X/S}`, read
through the degreewise comparison.** The Leibniz rule produces `1 ⊗ d_{X/S}` on
`f^{-1}Ω^k_{Y/S} ⊗ Ω^j_{X/S}`, while
`Stacks.DeRhamSmooth.gradedTargetXIso_inv_comp_d` produces `(-1)^k(1 ⊗ d_{X/Y})` on
`f^{-1}Ω^k_{Y/S} ⊗ Ω^j_{X/Y}`, and `d_{X/Y}` cannot be moved to the `𝒪_X`-tensor side at all —
it is `f^{-1}𝒪_Y`-linear and not `𝒪_X`-linear, which is the reason
`Stacks.DeRhamSmooth.gradedSourceMixedTensorCoefficientIso_naturality` cannot be instantiated at
a differential. So the two sides can only be compared by knowing that the surjection
`Ω_{X/S} ⟶ Ω_{X/Y}` (`AlgebraicGeometry.Scheme.Hom.toRelativeDifferentials`, the third map of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsShortComplex`) carries `d_{X/S}` to
`d_{X/Y}` in every degree, together with the compatibility of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison` with it.

**The first of those two is available in every degree**, which is less than this clause used to
say: the extension of the surjection to a homomorphism of sheaves of graded algebras
`⋀Ω_{X/S} ⟶ ⋀Ω_{X/Y}` is `AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom` of
`StacksFrontier.AlgebraicGeometry.DeRham.DeRhamFormsToRelative`, obtained from the universal
property of the exterior algebra rather than from
`AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMap` ([Stacks, Tag 07HX]), and its
commutation with the de Rham differential is
`AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom_comm` on the differential of the graded
algebras and `AlgebraicGeometry.Scheme.Hom.deRhamFormsToRelativeHom_comm_d` on the arrows of the
two relative de Rham complexes, both for every degree `n`. What is not packaged is a
`CategoryTheory.HomologicalComplex.Hom` assembled from those degreewise components; that is an
assembly, not a mathematical input.

**The second is what is genuinely missing.** No statement relates any of
`SheafOfModules.exteriorGradedHom`,
`SheafOfModules.exteriorGradedQuotientComparison`,
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsExteriorGradedComparison` or
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPullbackGradedComparison` to a differential,
so the degreewise comparison onto the graded piece is not yet known to intertwine the two.

Smoothness of `f` is the only hypothesis on `f`, and it is the hypothesis of Section 0FMK.

Costs 30,801 heartbeats against the default budget of 200,000. -/
def gradedPieceIsoGradedTargetComplexOfStepSquares [Smooth f] (k : ℕ)
    (hcut : (filtrationXIsoCutWedgeSource f g k).hom ≫
        (pushforward (toInverseImageBase (f ≫ g))).map
            (cutWedgeSourceIsoPullbackTensor f g k).hom ≫
          (gradedSourceMixedTensorCoefficientIso f g k
              (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms f ((0 : ℕ) : ℤ))).inv ≫
            ((-1 : ℤ) ^ k • (coefficientRestriction f g).map
                ((pulledBackTargetFormsTensor f g k).map
                  ((deRhamCochainXIso f 0).inv ≫
                    (deRhamCochainComplex f).d ((0 : ℕ) : ℤ) ((0 + 1 : ℕ) : ℤ) ≫
                      (deRhamCochainXIso f (0 + 1)).hom))) ≫
              (gradedTargetXIso f g k (0 + 1) (k + 1 + 0) (by omega)).inv =
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
          ((k : ℕ) : ℤ) ((k + 1 + 0 : ℕ) : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + 0 : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k 0).hom)
    (hup : ∀ j : ℕ, (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + j : ℕ) : ℤ) ≫
        ((gradedPieceXIsoGradedTargetX f g k j).hom ≫
          (gradedTargetComplex f g k).d ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ)) =
      ((deRhamSmoothFiltration f g).filtration.obj (op (k : ℤ))).d
          ((k + 1 + j : ℕ) : ℤ) ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
        (FilteredObject.grMapπ (FilteredObject.succHom (k : ℤ))
            (deRhamSmoothFiltration f g)).f ((k + 1 + (j + 1) : ℕ) : ℤ) ≫
          (gradedPieceXIsoGradedTargetX f g k (j + 1)).hom) :
    gradedPiece (inverseImageBase (f ≫ g)) (k : ℤ) (deRhamSmoothFiltration f g) ≅
      gradedTargetComplex f g k :=
  gradedPieceIsoGradedTargetComplexOfSquares f g k
    (gradedPieceXIsoGradedTargetXAtCut_comm_of_step_square f g k hcut)
    (fun j => gradedPieceXIsoGradedTargetX_comm_of_step_square f g k j (hup j))

end Stacks.DeRhamSmooth

end
