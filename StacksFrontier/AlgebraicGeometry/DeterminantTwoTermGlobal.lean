module

public import StacksFrontier.AlgebraicGeometry.AffineOpensDirectedGlueSection
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDeltaSection
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDetOfIso
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartNaturalSheaf
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartPresentation
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlueDatum
public import StacksFrontier.AlgebraicGeometry.RestrictPushforwardCompatible

/-!
# The determinant of a two-term perfect complex on an arbitrary scheme

Let `X` be a scheme and `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`. The
determinants of `L` on the affine opens of `X` are glued by
`AlgebraicGeometry.DeterminantTwoTerm.chartComparison` into a single invertible `𝒪_X`-module, the
determinant of `L`; an isomorphism of perfect two-term objects induces an isomorphism of the glued
determinants, and the assignment is functorial, so the determinant of [Stacks, Tag 0FJX] is a
functor on an arbitrary scheme. On an affine open the glued determinant is the determinant line of
More on Algebra, Section 0FJI of any two-term finite-projective presentation of the chart complex,
which is the affine-local description [Stacks, Tag 0FJX] asserts.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.globalDet`: **the determinant of `L` on an arbitrary
  scheme**, as an object of the groupoid of invertible `𝒪_X`-modules.
* `AlgebraicGeometry.DeterminantTwoTerm.globalDetIso`: the determinant of an isomorphism.
* `AlgebraicGeometry.DeterminantTwoTerm.determinantFunctor`: **the determinant functor of
  [Stacks, Tag 0FJX] on an arbitrary scheme.**
* `AlgebraicGeometry.DeterminantTwoTerm.determinantChartPresentationIso`: **the affine-local
  description of the determinant.**

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.globalDetIso_refl` and
  `AlgebraicGeometry.DeterminantTwoTerm.globalDetIso_trans`: the determinant of an isomorphism is
  functorial.

## Implementation notes

The glued module is `AlgebraicGeometry.AffineOpensGlue.ChartComparison.glued` of the glueing datum,
and the determinant of an isomorphism is
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.glueIso` of the family
`AlgebraicGeometry.DeterminantTwoTerm.chartDetIso`.

Every statement below that mentions the glueing datum is a *theorem* or a definition whose type
mentions only `L`. This is deliberate: the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeterminantTwoTermGlueDatum.lean` record that re-elaborating the
cocycle condition at the determinant's concrete family inside the type of a *definition* exhausts
the kernel's budget, while the same type in a *theorem* is checked in seconds. The glueing datum is
therefore consumed only through the hypothesis-free `chartComparison` and the `rfl` lemmas
`chartComparison_mod` and `chartComparison_comp`.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The glued determinant -/

/-- **The determinant of a perfect two-term object on an arbitrary scheme**, as an object of the
target groupoid of [Stacks, Tag 0FJX]: the invertible `𝒪_X`-module glued from the determinants of
`L` on the affine opens of `X`. -/
def globalDet (L : PerfectTwoTermAmplitude X) : InvertibleModuleCat X :=
  ⟨(chartComparison L).glued, isInvertibleModule_chartComparison_glued L⟩

/-- The glued determinant restricts on the chart of an affine open to the determinant of `L`
there. -/
def globalDetChartIso (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    Scheme.Modules.restrict (globalDet L).obj (AffineOpensGlue.chart X V) ≅ chartDet L V :=
  (chartComparison L).chartIso V

/-! ### The determinant of an isomorphism -/

/-- The family of determinants of an isomorphism on the affine charts is compatible with the
comparisons of the glueing datum. -/
theorem isCompatible_chartDetIso {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj) :
    AffineOpensGlue.ChartComparison.IsCompatible (D := chartComparison L)
      (D' := chartComparison K) (fun V => (chartDetIso a V).hom) :=
  AffineOpensGlue.isCompatible_of_restrictIso (chartDet L) (chartDet K) (chartTheta L)
    (chartTheta_trans L) (chartTheta K) (chartTheta_trans K)
    (fun V => (chartDetIso a V).hom)
    (fun _ _ h => chartDetRestrictIso_natural'
      (fun V => detLinearEquivOfIso (chartComplexIso a V)) h (chartDetModuleIso_natural a h))

/-- **The determinant of an isomorphism of perfect two-term objects on an arbitrary scheme**: the
isomorphism of the glued determinants assembled from the determinants on the affine charts. -/
def globalDetIso {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj) :
    (globalDet L).obj ≅ (globalDet K).obj :=
  (chartComparison L).glueIso (chartComparison K) (fun V => chartDetIso a V)
    (isCompatible_chartDetIso a)

/-- **The determinant of the identity isomorphism is the identity.** -/
theorem globalDetIso_refl (L : PerfectTwoTermAmplitude X) :
    globalDetIso (Iso.refl L.obj) = Iso.refl (globalDet L).obj :=
  (AffineOpensGlue.ChartComparison.glueIso_congr (chartComparison L) (chartComparison L)
      (funext fun V => chartDetIso_refl L V) (isCompatible_chartDetIso (Iso.refl L.obj))
      (AffineOpensGlue.ChartComparison.isCompatible_id (chartComparison L))).trans
    (AffineOpensGlue.ChartComparison.glueIso_refl (chartComparison L)
      (AffineOpensGlue.ChartComparison.isCompatible_id (chartComparison L)))

/-- **The determinant of a composite of isomorphisms is the composite of the determinants.** -/
theorem globalDetIso_trans {L K M : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj)
    (b : K.obj ≅ M.obj) :
    globalDetIso (a ≪≫ b) = globalDetIso a ≪≫ globalDetIso b :=
  (AffineOpensGlue.ChartComparison.glueIso_congr (chartComparison L) (chartComparison M)
      (funext fun V => chartDetIso_trans a b V) (isCompatible_chartDetIso (a ≪≫ b))
      (AffineOpensGlue.ChartComparison.isCompatible_comp (chartComparison L) (chartComparison K)
        (chartComparison M) (isCompatible_chartDetIso a) (isCompatible_chartDetIso b))).trans
    (AffineOpensGlue.ChartComparison.glueIso_trans (chartComparison L) (chartComparison K)
      (chartComparison M) (fun V => chartDetIso a V) (fun V => chartDetIso b V)
      (isCompatible_chartDetIso a) (isCompatible_chartDetIso b)
      (AffineOpensGlue.ChartComparison.isCompatible_comp (chartComparison L) (chartComparison K)
        (chartComparison M) (isCompatible_chartDetIso a) (isCompatible_chartDetIso b)))

/-! ### The determinant functor -/

/-- The promotion of an isomorphism of the source groupoid to an isomorphism of `D(𝒪_X)` carries
the identity to the identity. -/
private theorem ι_mapIso_refl (L : PerfectTwoTermAmplitude X) :
    (IsPerfectTwoTermAmplitude X).ι.mapIso (Iso.refl L) = Iso.refl L.obj := by
  ext
  rfl

/-- The promotion of an isomorphism of the source groupoid to an isomorphism of `D(𝒪_X)` carries a
composite to the composite. -/
private theorem ι_mapIso_trans {L K M : PerfectTwoTermAmplitude X} (a : L ≅ K) (b : K ≅ M) :
    (IsPerfectTwoTermAmplitude X).ι.mapIso (a ≪≫ b) =
      (IsPerfectTwoTermAmplitude X).ι.mapIso a ≪≫ (IsPerfectTwoTermAmplitude X).ι.mapIso b := by
  ext
  rfl

/-- The determinant functor on an arbitrary scheme, from the groupoid of perfect objects of
`D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and their isomorphisms to the groupoid of invertible
`𝒪_X`-modules and their isomorphisms.

The value at `L` is the invertible module glued from the determinants of `L` on the affine opens
of `X`, and the value at an isomorphism is glued from the determinants of its restrictions to the
affine charts. -/
@[stacks 0FJX "part (1): the determinant functor, from the groupoid of perfect objects of Tor
amplitude in [-1, 0] and their isomorphisms to the groupoid of invertible modules and their
isomorphisms, on an arbitrary scheme"]
def determinantFunctor (X : Scheme.{u}) :
    Core (PerfectTwoTermAmplitude X) ⥤ Core (InvertibleModuleCat X) where
  obj L := ⟨globalDet L.of⟩
  map {L K} a := ⟨ObjectProperty.isoMk (IsInvertibleProperty X)
    (globalDetIso ((IsPerfectTwoTermAmplitude X).ι.mapIso a.iso))⟩
  map_id L := by
    refine Core.hom_ext ?_
    refine ObjectProperty.hom_ext _ ?_
    change (globalDetIso ((IsPerfectTwoTermAmplitude X).ι.mapIso (Iso.refl L.of))).hom = _
    rw [ι_mapIso_refl, globalDetIso_refl]
    rfl
  map_comp {L K M} a b := by
    refine Core.hom_ext ?_
    refine ObjectProperty.hom_ext _ ?_
    change (globalDetIso ((IsPerfectTwoTermAmplitude X).ι.mapIso (a.iso ≪≫ b.iso))).hom = _
    rw [ι_mapIso_trans, globalDetIso_trans]
    rfl

/-- The value of the determinant functor is the glued determinant. -/
theorem determinantFunctor_obj (L : PerfectTwoTermAmplitude X) :
    ((determinantFunctor X).obj ⟨L⟩).of = globalDet L :=
  rfl

/-! ### The canonical global section -/

/-- The family of canonical elements of More on Algebra, Section 0FJI on the affine charts is
matched by the comparisons of the glueing datum. -/
theorem isMatched_chartDeltaSection {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L) :
    ∀ {V W : X.affineOpens} (h : V ≤ W),
      localAppFun ((chartComparison L).comp h).hom (V.1 : X.Opens) le_rfl
          (chartDeltaSection hL V) =
        ((Scheme.Modules.pushforward (AffineOpensGlue.chart X W)).obj
            ((chartComparison L).mod W)).val.map
          (homOfLE (show (V.1 : X.Opens) ≤ (W.1 : X.Opens) from h)).op (chartDeltaSection hL W) :=
  fun h => localAppFun_chartDetComp_chartDeltaSection hL h

/-- The canonical global section `δ(L)` of the determinant of a rank-zero perfect object of
`D(𝒪_X)` of Tor-amplitude in `[-1, 0]` on an arbitrary scheme: the global section glued from the
canonical elements of More on Algebra, Section 0FJI on the affine charts, which are matched by the
chart comparisons. -/
@[stacks 0FJX "part (2): the canonical global section δ(L) of the determinant of a rank-zero
object, on an arbitrary scheme"]
def determinantSection {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L) :
    Γ(((determinantFunctor X).obj ⟨L⟩).of.obj, ⊤) :=
  ((chartComparison L).exists_section (chartDeltaSection hL)
    (isMatched_chartDeltaSection hL)).choose

/-- **The canonical global section reads on each affine chart as the canonical element of More on
Algebra, Section 0FJI there.** -/
theorem determinantSection_chartSec {L : PerfectTwoTermAmplitude X} (hL : IsRankZeroOn L)
    (V : X.affineOpens) :
    (chartComparison L).chartSec V (V.1 : X.Opens)
        ((chartComparison L).glued.val.map (homOfLE le_top).op (determinantSection hL)) =
      chartDeltaSection hL V :=
  ((chartComparison L).exists_section (chartDeltaSection hL)
    (isMatched_chartDeltaSection hL)).choose_spec V

/-! ### The affine-local description -/

/-- On an affine open `V` of an arbitrary scheme `X` the determinant of `L` is the sheaf
associated with the determinant line of More on Algebra, Section 0FJI of *any* two-term
finite-projective presentation `P` of the complex of `Γ(X, V)`-modules that `L` restricts to on the
chart of `V`: the restriction of the determinant to `V` is the pullback along
`AlgebraicGeometry.IsAffineOpen.isoSpec` of that associated sheaf.

The isomorphism is the glueing comparison
`AlgebraicGeometry.AffineOpensGlue.ChartComparison.chartIso` of the datum, followed by
`AlgebraicGeometry.DeterminantTwoTerm.chartDetPresentationIso`. -/
@[stacks 0FJX "part (3): the construction is affine locally the one of More on Algebra, Section
0FJI — on an affine open of an arbitrary scheme the determinant is the determinant line of a
two-term finite-projective presentation of the complex the object restricts to there"]
def determinantChartPresentationIso (L : PerfectTwoTermAmplitude X) (V : X.affineOpens)
    (P : TwoTermPresentation (chartComplex L V).obj) :
    letI := P.finite (-1)
    letI := P.projective (-1)
    letI := P.finite 0
    letI := P.projective 0
    Scheme.Modules.restrict ((determinantFunctor X).obj ⟨L⟩).of.obj
        (AffineOpensGlue.chart X V) ≅
      (Scheme.Modules.pullback V.2.isoSpec.hom).obj
        (tilde (ModuleCat.of Γ(X, (V.1 : X.Opens))
          (TwoTermComplex.determinantLine (P.complex.d (-1) 0).hom))) :=
  letI := P.finite (-1)
  letI := P.projective (-1)
  letI := P.finite 0
  letI := P.projective 0
  globalDetChartIso L V ≪≫ chartDetPresentationIso L V P

end AlgebraicGeometry.DeterminantTwoTerm

end
