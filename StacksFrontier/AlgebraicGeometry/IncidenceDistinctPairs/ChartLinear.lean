module

public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreLine
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityRatioLinear
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# The chart coordinate of projective space is a linear functional in its numerator

The chart coordinate of `𝐏(V)` is the ratio `ι v / ι u` of two tautological sections of `𝒪(1)`,
a function on the standard open `D₊(ι u)`. This file proves that it is **additive and
`k`-homogeneous in `v`**: the ratio of `ι (v + v')` is the sum of the two ratios, and the ratio of
`ι (c • v)` is the ratio of `ι v` multiplied by the function on `𝐏(V)` which the structure
morphism `𝐏(V) ⟶ Spec k` attaches to `c`.

That is what putting a triple of collinear points into the collinearity locus needs. The
converse direction, which the dimension theory of the incidence variety consumes, uses the chart
coordinate only through the vanishing of its values and so needs neither
(see `StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreLine`); here the three chart
coordinates of three collinear points have to be seen as *linearly dependent*, and for that they
have to be functionals.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.structureFun`: the function on an open of `𝐏(V)`
  attached to a scalar by the structure morphism over `Spec k`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodStructureFun`: the same for the triple product.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.residueScalarHom`: the induced ring homomorphism
  from `k` to the residue field at a point of the triple product. It does not depend on which
  projection the chart coordinate is taken along, which is exactly what makes the three chart
  functionals of a triple semilinear over *one* homomorphism.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.tautRatio_smul_eq_structureFun_mul`: **the chart
  coordinate is `k`-homogeneous in its numerator**, the scalar acting as `structureFun`; its
  additivity is `AlgebraicGeometry.ProjectiveSpaceOfModule.tautRatio_add` of
  `StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityRatioLinear`.
  The same for its pullback to a chart of the triple product is
  `AlgebraicGeometry.ProjectiveSpaceOfModule.chartRatio_add` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.chartRatio_smul` there; the scalar of the latter is
  definitionally `prodStructureFun`, pulled back from `Spec k` and therefore independent of the
  projection.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartResidue_chartRatio_add` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.chartResidue_chartRatio_smul`: the same for the
  residues at a point, which is the form the determinant argument consumes.

## Implementation notes

Homogeneity is proved on the algebraic side and transported. The global section of `𝒪(1)`
attached to a vector is `AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` of `ι v`, and
that map is bundled as a linear map over the degree-zero part of the grading
(`Stacks.AlgebraicGeometry.ProjStalkGlobalSections.degreeZeroToGlobalSections`), so
`LinearMap.map_smul` gives the degree-zero element `algebraMap k (Sym_k V)₀ c` acting on it. The
`divBySection` uniqueness clause `Stacks.SheafOfModules.divBySection_eq_of_smul_eq` then carries
the identity to the ratio, and `PresheafOfModules.map_smul` to an arbitrary open.

The resulting scalar is the global function `degreeZeroRingToGlobalSections` of the degree-zero
element, and the *whole point* of `structureFun` is that it is also the pullback of `c` along the
structure morphism. Both have the fraction `c / 1` as value at every point —
`Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val` for one and
`degreeZeroRingToGlobalSections_stalk` for the other — and a section of the structure sheaf of a
projective spectrum is a family of homogeneous fractions, so the two are equal. Without that
identification the scalar would depend on which projection of the triple product the chart
coordinate is taken along, and three functionals semilinear over three different homomorphisms
have no reason to be dependent.

The scalar is never written as a module action at a concrete instantiation: a `•` between
`Γ(𝐏(V), U)` and the sections of `𝒪(1)` over `U` does not elaborate there, because instance
search has to identify `Γ(𝐏(V), U)` with the value of the ring sheaf
`Stacks.SheafOfModules.structureSheafRing` and will not unfold the projection. Every statement
below is therefore multiplicative or additive inside one ring of sections, and the module actions
appear only inside proofs, where they come from the general lemmas' own statements.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules AlgebraicGeometry.ProjectiveSpaceOfModule
open Stacks.AlgebraicGeometry.ProjTwistSections Stacks.AlgebraicGeometry.ProjEulerSequence
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
attribute [local implicit_reducible] structureSheafRing

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The scalars, read as functions -/

/-- The global function on `𝐏(V)` attached to a scalar through the degree-zero part of the
symmetric algebra. -/
private def gradedScalar (c : k) :
    (ProjectiveSpectrum.Proj.structureSheaf (symmetricGrading k V)).1.obj (op ⊤) :=
  degreeZeroRingToGlobalSections (symmetricGrading k V)
    (algebraMap k (SymPow.symmetricPower 0 k V) c)

/-- The value of that function at a point is the fraction `c / 1`. -/
private theorem gradedScalar_val (c : k)
    (x : ProjectiveSpectrum.top (symmetricGrading k V)) :
    HomogeneousLocalization.val ((gradedScalar k V c).1 ⟨x, trivial⟩) =
      algebraMap (SymmetricAlgebra k V)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        (algebraMap k (SymmetricAlgebra k V) c) := by
  rw [← Proj.stalkIso'_germ (symmetricGrading k V) ⊤ x trivial (gradedScalar k V c),
    show gradedScalar k V c = degreeZeroRingToGlobalSections (symmetricGrading k V)
      (algebraMap k (SymPow.symmetricPower 0 k V) c) from rfl,
    degreeZeroRingToGlobalSections_stalk]
  show Localization.mk
      ((algebraMap k (SymPow.symmetricPower 0 k V) c : SymPow.symmetricPower 0 k V) :
        SymmetricAlgebra k V)
      (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) = _
  rw [SetLike.GradeZero.coe_algebraMap (symmetricGrading k V) c]
  exact Localization.mk_algebraMap (A := SymmetricAlgebra k V) _

/-- The composite of the identification of `k` with the global functions on `Spec k` with the
structure morphism of `𝐏(V)`, as a map between the naturality square's two spellings. -/
private theorem gamma_naturality :
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (projectiveSpaceOfModuleToSpec k V).appTop =
      CommRingCat.ofHom (algebraMap k (SymPow.symmetricPower 0 k V)) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (SymPow.symmetricPower 0 k V))).inv ≫
          (Proj.toSpecZero (symmetricGrading k V)).appTop := by
  rw [Scheme.ΓSpecIso_inv_naturality_assoc, projectiveSpaceOfModuleToSpec]
  simp only [Scheme.Hom.appTop, Scheme.Hom.comp_app, Scheme.Hom.preimage_top]

/-- The value at a point of the pullback of a scalar along the structure morphism is the
fraction `c / 1`. -/
private theorem toSpec_appTop_val (c : k)
    (x : ProjectiveSpectrum.top (symmetricGrading k V)) :
    HomogeneousLocalization.val
        (((projectiveSpaceOfModuleToSpec k V).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)).1 ⟨x, trivial⟩) =
      algebraMap (SymmetricAlgebra k V)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        (algebraMap k (SymmetricAlgebra k V) c) := by
  have h := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (gamma_naturality k V)) c
  refine Eq.trans (congrArg
    (fun s : Γ(projectiveSpaceOfModule k V, ⊤) =>
      HomogeneousLocalization.val (s.1 ⟨x, trivial⟩)) h) ?_
  refine Eq.trans (toSpecZero_appTop_val (symmetricGrading k V) _ x) ?_
  exact congrArg _ (SetLike.GradeZero.coe_algebraMap (symmetricGrading k V) c)

/-- **The degree-zero scalar and the pullback of the scalar along the structure morphism are the
same global function on `𝐏(V)`.** -/
private theorem gradedScalar_eq_appTop (c : k) :
    gradedScalar k V c =
      (projectiveSpaceOfModuleToSpec k V).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) :=
  Subtype.ext (funext fun x => HomogeneousLocalization.val_injective _
    ((gradedScalar_val k V c x.1).trans (toSpec_appTop_val k V c x.1).symm))

/-- **The function on an open of `𝐏(V)` attached to a scalar by the structure morphism over
`Spec k`.** -/
public def structureFun (c : k) (U : (projectiveSpaceOfModule k V).Opens) :
    Γ(projectiveSpaceOfModule k V, U) :=
  ((projectiveSpaceOfModuleToSpec k V).appLE ⊤ U le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)

/-- **The function on a chart of the triple product attached to a scalar by the structure
morphism over `Spec k`.** -/
public def prodStructureFun (c : k) (U : (prodThree k V).Opens) : Γ(prodThree k V, U) :=
  ((prodThreeToSpec k V).appLE ⊤ U le_top).hom
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)

/-! ### The tautological section is additive and homogeneous in its vector -/

/-- The value over an open of the global section of `𝒪(1)` attached to a vector is the
restriction of the degree-one section. -/
private theorem tautologicalSection_eval (w : V) (U : (projectiveSpaceOfModule k V).Opens) :
    (tautologicalSection k V w).eval (op U) =
      (tautologicalModule k V).val.map (homOfLE (le_top : U ≤ ⊤)).op
        (ProjectiveSpectrum.Proj.degreeSection (symmetricGrading k V) 1
          ⟨SymmetricAlgebra.ι k V w, ι_mem_symmetricPower_one k V w⟩) := by
  refine Eq.trans ?_ (congrArg ((tautologicalModule k V).val.map
    (homOfLE (le_top : U ≤ ⊤)).op) (sectionsOfTop_eval_top _ _))
  exact (PresheafOfModules.sections_property (tautologicalSection k V w)
    (homOfLE (le_top : U ≤ ⊤)).op).symm

/-- The degree-one section attached to `c • v` is the degree-zero scalar `c` times the one
attached to `v`. -/
private theorem degreeSection_ι_smul (c : k) (v : V) :
    ProjectiveSpectrum.Proj.degreeSection (symmetricGrading k V) 1
        ⟨SymmetricAlgebra.ι k V (c • v), ι_mem_symmetricPower_one k V (c • v)⟩
      = gradedScalar k V c • ProjectiveSpectrum.Proj.degreeSection (symmetricGrading k V) 1
        ⟨SymmetricAlgebra.ι k V v, ι_mem_symmetricPower_one k V v⟩ := by
  let _ : Module ((symmetricGrading k V) 0)
      ((ProjectiveSpectrum.Proj.twistingSheaf (symmetricGrading k V)
        ((1 : ℕ) : ℤ)).val.obj (op ⊤)) :=
    Module.compHom _ (degreeZeroRingToGlobalSections (symmetricGrading k V))
  refine Eq.trans ?_ ((degreeZeroToGlobalSections (symmetricGrading k V)
      (ProjectiveSpectrum.Proj.twistGrading (symmetricGrading k V) ((1 : ℕ) : ℤ))).map_smul
        (algebraMap k (SymPow.symmetricPower 0 k V) c)
        ⟨SymmetricAlgebra.ι k V v,
          mem_twistGrading_zero (symmetricGrading k V)
            ⟨SymmetricAlgebra.ι k V v, ι_mem_symmetricPower_one k V v⟩⟩)
  refine congrArg (degreeZeroToGlobalSections (symmetricGrading k V)
    (ProjectiveSpectrum.Proj.twistGrading (symmetricGrading k V) ((1 : ℕ) : ℤ)))
    (Subtype.ext ?_)
  show SymmetricAlgebra.ι k V (c • v) =
    ((algebraMap k (SymPow.symmetricPower 0 k V) c : SymPow.symmetricPower 0 k V) :
      SymmetricAlgebra k V) * SymmetricAlgebra.ι k V v
  rw [SetLike.GradeZero.coe_algebraMap (symmetricGrading k V) c, map_smul, Algebra.smul_def]

/-! ### The chart coordinate -/

/-- **The chart coordinate of `𝐏(V)` is `k`-homogeneous in its numerator**, the scalar being the
function which the structure morphism attaches to it. -/
public theorem tautRatio_smul_eq_structureFun_mul (c : k) (u v : V) :
    tautRatio k V u (c • v) =
      structureFun k V c
          (nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u)) *
        tautRatio k V u v := by
  set D := nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u)
  set g := (homOfLE (le_top : D ≤ ⊤)).op
  have h (w : V) : tautRatio k V u w =
      divBySection (tautologicalModule k V) (tautologicalSection k V u) le_rfl
        ((tautologicalModule k V).val.map g
          (ProjectiveSpectrum.Proj.degreeSection (symmetricGrading k V) 1
            ⟨SymmetricAlgebra.ι k V w, ι_mem_symmetricPower_one k V w⟩)) :=
    congrArg (divBySection (tautologicalModule k V) (tautologicalSection k V u) le_rfl)
      (tautologicalSection_eval k V w D)
  have hmap := PresheafOfModules.map_smul (tautologicalModule k V).val g (gradedScalar k V c)
    (ProjectiveSpectrum.Proj.degreeSection (symmetricGrading k V) 1
      ⟨SymmetricAlgebra.ι k V v, ι_mem_symmetricPower_one k V v⟩)
  rw [h, h, degreeSection_ι_smul]
  refine (congrArg _ hmap).trans ((divBySection_smul (tautologicalModule k V)
    (tautologicalSection k V u) le_rfl _ _).trans ?_)
  exact congrArg (· * _) (congrArg ((projectiveSpaceOfModule k V).presheaf.map g).hom
    (gradedScalar_eq_appTop k V c))

/-! ### The chart coordinate on the triple product -/

/-! ### The chart functional at a point -/

/-- **The ring homomorphism from `k` to the residue field at a point of a chart of the triple
product**, through the structure morphism over `Spec k`. The three chart coordinates at that
point are semilinear over this one homomorphism, whichever projections they are taken along. -/
public def residueScalarHom {U : (prodThree k V).Opens} {t : prodThree k V} (ht : t ∈ U) :
    k →+* IsLocalRing.ResidueField ((prodThree k V).presheaf.stalk t) :=
  (chartResidue k V ht).comp
    (((prodThreeToSpec k V).appLE ⊤ U le_top).hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom))

/-- The residue of the pulled-back scalar is its image under `residueScalarHom`. -/
private theorem chartResidue_prodStructureFun (c : k) {U : (prodThree k V).Opens}
    {t : prodThree k V} (ht : t ∈ U) :
    chartResidue k V ht (prodStructureFun k V c U) = residueScalarHom k V ht c :=
  rfl

/-- **The chart functional at a point of the triple product is additive.** -/
public theorem chartResidue_chartRatio_add
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u v v' : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))
    {t : prodThree k V} (ht : t ∈ U) :
    chartResidue k V ht (chartRatio k V f u (v + v') hU) =
      chartResidue k V ht (chartRatio k V f u v hU) +
        chartResidue k V ht (chartRatio k V f u v' hU) := by
  rw [chartRatio_add, _root_.map_add]

/-- **The chart functional at a point of the triple product is `k`-semilinear** over
`AlgebraicGeometry.ProjectiveSpaceOfModule.residueScalarHom`, which does not depend on the
projection. -/
public theorem chartResidue_chartRatio_smul
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V)
    (hf : f ≫ projectiveSpaceOfModuleToSpec k V = prodThreeToSpec k V) (c : k) (u v : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))
    {t : prodThree k V} (ht : t ∈ U) :
    chartResidue k V ht (chartRatio k V f u (c • v) hU) =
      residueScalarHom k V ht c * chartResidue k V ht (chartRatio k V f u v hU) := by
  rw [show chartRatio k V f u (c • v) hU = prodStructureFun k V c U * chartRatio k V f u v hU from
    chartRatio_smul k V f hf u c v hU, _root_.map_mul, chartResidue_prodStructureFun]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
