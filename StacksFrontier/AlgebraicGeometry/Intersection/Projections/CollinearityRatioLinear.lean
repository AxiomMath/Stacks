module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityFibre
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.UniversalFamilyOverProjectiveSpace

/-!
# The ratio of two tautological sections is `k`-linear, and the fibre of the collinearity locus

Let `V` be a vector space over a field `k` and `𝐏(V) = Proj (Sym_k V)`. On the standard open
`D₊(ι u)` the ratio `ι v / ι u` of two tautological sections of `𝒪(1)` is an honest function
(`AlgebraicGeometry.ProjectiveSpaceOfModule.tautRatio`), and this file proves that it is
**`k`-linear in its numerator `v`**: additive, and homogeneous for the scalar action of `k`
through the structure morphism `𝐏(V) ⟶ Spec k`. Pulled back along a projection of the triple
product `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` and read in the residue field at a point of a chart, the three
resulting maps `V → κ(x)` are `k`-linear *against one and the same map* `k → κ(x)`, because the
three projections are morphisms over `Spec k`.

That is exactly what the converse of the fibre containment of Tag 0B1R needs. With
`W₁ = W_{pr₁ x}`, `W₂ = W_{pr₂ x}` the hyperplanes of two distinct closed points and
`K = W₁ ⊓ W₂` the submodule of the line joining them, every vector is `c + α a + β b` with
`c ∈ K`, `α, β ∈ k`, `a` vanishing at the second point only and `b` at the first only. If `K` is
contained in the hyperplane of the third projection as well, `k`-linearity puts every column of
every matrix of ratios in the span of the two columns of `a` and `b`, so every determinant
vanishes in the residue field and the point is collinear. Together with the containment proved in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/CollinearityFibre.lean` this identifies
the collinear triples over a pair of distinct closed points as those whose third projection lies
on the line joining the pair.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarSectionProj` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarSectionProdThree`: the global function a
  scalar becomes on `𝐏(V)`, and on the triple product, along the structure morphism over
  `Spec k`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarResidue`: the induced map
  `k →+* κ(x)` at a point of the triple product — the one scalar map all three rows of a matrix
  of ratios are homogeneous against.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.pr₁_comp_toSpec`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pr₂_comp_toSpec` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pr₃_comp_toSpec`: **the three projections of the
  triple product are morphisms over `Spec k`**, so
  `AlgebraicGeometry.ProjectiveSpaceOfModule.appTop_scalarSectionProj`: a scalar pulled back
  along any of them is the same global function.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.tautRatio_add` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.tautRatio_smul`: **the ratio `ι v / ι u` is
  `k`-linear in `v`.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.chartRatio_add` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.chartRatio_smul`: the same for its pullback along a
  projection over `Spec k`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.residue_germ_chartRatio_add` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.residue_germ_chartRatio_smul`: **the same at a point
  of a chart, in the residue field**, the scalar acting through
  `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarResidue`, which does not depend on the
  projection.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_collinearLocus_of_lineSubmodule_le`: **a triple
  over a pair of distinct closed points whose third projection lies on the line joining them is
  collinear** — the converse containment.
* `ProjectiveSpaceOfModule.mem_collinearLocus_iff_mem_linearSubspace_lineSubmodule`:
  **the two containments together**, the identification of the collinear triples over a pair of
  distinct closed points.

## Implementation notes

The scalar law of the degree-one section map is
`Stacks.AlgebraicGeometry.ProjectiveSpaceSections.degreeSection_smul`, available for the
symmetric grading of an arbitrary module over a commutative ring, and the identification of the
two scalar actions on global sections of `Proj` that makes it usable is
`Stacks.AlgebraicGeometry.ProjectiveSpaceSections.structureMorphism_appTop_eq`; both live in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/UniversalFamilyOverProjectiveSpace.lean`,
which is why this file is where it is rather than beside `tautRatio`. From the section map the
law travels to the ratio through the uniqueness of `Stacks.SheafOfModules.divBySection`
(`Stacks.SheafOfModules.divBySection_smul` and `Stacks.SheafOfModules.divBySection_add`), and
then to the chart and to the point through ring maps only — `Scheme.Hom.appLE`, the germ and the
residue — so no further sheaf-module algebra is needed downstream.

The genuine obstacle is spelling, not mathematics. The ring of functions on an open of `Proj`
has three presentations in play — `Γ(X, U)` for `X` a scheme, `X.presheaf.obj (op U)` for `X` a
ringed space, and the structure sheaf of `Proj` — and the scalar action of each on the sections of
a module is registered at one of them only. Three consequences shape the proofs here. The scalar
multiple of a section is written at the mathlib spelling `Γ(X, U) • Γ(M, U)`, which is the one
carrying `AlgebraicGeometry.Scheme.Modules.map_smul`, and the element of `Γ(M, U)` is produced by
`Stacks.SectionExtension.resTop` rather than by a type ascription, since an ascription unifies
away and leaves the module-side spelling untouched. The step from that spelling to the
`Stacks.SheafOfModules.divBySection` one is taken by `exact` and `congrArg`, never by `rw`: the
intermediate goals are not type-correct at the `instances` transparency `rw` typechecks its motive
at, because `AlgebraicGeometry.Scheme.Modules` does not unfold to
`SheafOfModules (structureSheafRing _)` there. And `map_add`, `map_mul` have to be written
`_root_.map_add`, `_root_.map_mul`, because `AlgebraicGeometry.ProjectiveSpaceOfModule` has its
own `map`.

The determinant computation is the one of
`AlgebraicGeometry.ProjectiveSpaceOfModule.lineSubmodule_le_pointSubmodule_of_mem_collinearLocus`
run in the other direction: all nine entries of the residue matrix are expanded as
`α_j · ψᵢ(a) + β_j · ψᵢ(b)`, and `Matrix.det_fin_three` followed by `ring` sees that the
determinant of a matrix of that shape is identically zero.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)

## Where this is used

The whole of [Stacks, Tag 0B1R] — the decomposition
`Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E` together with the bound
`dim E ≤ dim Y + dim Z + 1 - n` — is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq` in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/ProjectionConeDimension.lean`, which
carries the attribute. The fibre identification proved here is one of the inputs to its count: it
is carried to the scheme-theoretic fibre of
`AlgebraicGeometry.ProjectiveSpaceOfModule.collinearProj` by
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_fiber_collinearProj` in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/CollinearityFibreScheme.lean`, and it is
also what turns a collinear triple of closed points into a point of the incidence variety.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The three projections of the triple product are morphisms over `Spec k` -/

/-- The projection of the triple product to the product of the first two factors is a morphism
over `Spec k`. -/
public theorem prFst_comp_prodTwoToSpec :
    prFst k V ≫ prodTwoToSpec k V = prodThreeToSpec k V :=
  pullback.condition

/-- The first projection of the triple product is a morphism over `Spec k`. -/
public theorem pr₁_comp_toSpec :
    pr₁ k V ≫ projectiveSpaceOfModuleToSpec k V = prodThreeToSpec k V := by
  change (prFst k V ≫ pullback.fst _ _) ≫ projectiveSpaceOfModuleToSpec k V = _
  rw [Category.assoc]
  exact pullback.condition

/-- The second projection of the triple product is a morphism over `Spec k`. -/
public theorem pr₂_comp_toSpec :
    pr₂ k V ≫ projectiveSpaceOfModuleToSpec k V = prodThreeToSpec k V := by
  change (prFst k V ≫ pullback.snd _ _) ≫ projectiveSpaceOfModuleToSpec k V = _
  rw [Category.assoc, ← pullback.condition]
  exact pullback.condition

/-- The third projection of the triple product is a morphism over `Spec k`. -/
public theorem pr₃_comp_toSpec :
    pr₃ k V ≫ projectiveSpaceOfModuleToSpec k V = prodThreeToSpec k V := rfl

/-! ### A scalar as a global function -/

/-- The global function on `𝐏(V)` attached to a scalar: the global section of Tag 01M7 of its
image in `Sym⁰_k(V)`. By
`Stacks.AlgebraicGeometry.ProjectiveSpaceSections.structureMorphism_appTop_eq` this is the
function the scalar becomes along the structure morphism `𝐏(V) ⟶ Spec k`, which is what makes it
the same on all three factors of the triple product. -/
public def scalarSectionProj (c : k) : Γ(projectiveSpaceOfModule k V, ⊤) :=
  degreeZeroRingToGlobalSections (symmetricGrading k V)
    (algebraMap k (symmetricGrading k V 0) c)

/-- The global function a scalar becomes on `𝐏(V)` along the structure morphism. -/
public theorem scalarSectionProj_eq (c : k) :
    scalarSectionProj k V c
      = (projectiveSpaceOfModuleToSpec k V).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) :=
  (Stacks.AlgebraicGeometry.ProjectiveSpaceSections.structureMorphism_appTop_eq k V c).symm

/-- The global function on the triple product a scalar becomes along the structure morphism. -/
public def scalarSectionProdThree (c : k) : Γ(prodThree k V, ⊤) :=
  (prodThreeToSpec k V).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)

/-- **A scalar pulled back along any of the three projections is the same global function on the
triple product**, because all three are morphisms over `Spec k`. -/
public theorem appTop_scalarSectionProj
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V)
    (hf : f ≫ projectiveSpaceOfModuleToSpec k V = prodThreeToSpec k V) (c : k) :
    f.appTop (scalarSectionProj k V c) = scalarSectionProdThree k V c := by
  rw [scalarSectionProj_eq, scalarSectionProdThree, ← hf]
  rfl

/-! ### The tautological section is `k`-linear in its vector -/

/-- The value over `⊤` of the global section of `𝒪(1)` attached to a vector is the degree-one
section map of Tag 01MP applied to that vector. -/
private theorem eval_top_tautologicalSection (v : V) :
    (tautologicalSection k V v).eval (op ⊤)
      = AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (symmetricGrading k V) 1
          ⟨SymmetricAlgebra.ι k V v, ι_mem_symmetricPower_one k V v⟩ :=
  sectionsOfTop_eval_top _ _

/-- A section of `𝒪(1)` over an open of `𝐏(V)` is the restriction of its value over `⊤`. -/
private theorem eval_eq_secRestr (s : (tautologicalModule k V).sections)
    (U : (projectiveSpaceOfModule k V).Opens) :
    s.eval (op U) = (tautologicalModule k V).val.restrictₛₗ
      (homOfLE (le_top : U ≤ ⊤)).op (s.eval (op ⊤)) :=
  (secRestr_sections_eval (tautologicalModule k V) s (le_top : U ≤ ⊤)).symm

/-- **The global section of `𝒪(1)` attached to a vector is additive in the vector**, over every
open of `𝐏(V)`. -/
public theorem eval_tautologicalSection_add (v w : V)
    (U : (projectiveSpaceOfModule k V).Opens) :
    (tautologicalSection k V (v + w)).eval (op U)
      = (tautologicalSection k V v).eval (op U) + (tautologicalSection k V w).eval (op U) := by
  rw [eval_eq_secRestr k V (tautologicalSection k V (v + w)) U,
    eval_eq_secRestr k V (tautologicalSection k V v) U,
    eval_eq_secRestr k V (tautologicalSection k V w) U, ← map_add]
  congr 1
  rw [eval_top_tautologicalSection, eval_top_tautologicalSection, eval_top_tautologicalSection,
    show (⟨SymmetricAlgebra.ι k V (v + w), ι_mem_symmetricPower_one k V (v + w)⟩ :
          symmetricGrading k V 1)
        = ⟨SymmetricAlgebra.ι k V v, ι_mem_symmetricPower_one k V v⟩
          + ⟨SymmetricAlgebra.ι k V w, ι_mem_symmetricPower_one k V w⟩ from
      Subtype.ext (map_add (SymmetricAlgebra.ι k V) v w)]
  exact map_add
    (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSectionHom (symmetricGrading k V) 1) _ _

/-! ### The ratio of two tautological sections is `k`-linear in its numerator -/

/-- **The ratio `ι v / ι u` is additive in its numerator.** -/
public theorem tautRatio_add (u v w : V) :
    tautRatio k V u (v + w) = tautRatio k V u v + tautRatio k V u w :=
  (congrArg (divBySection (tautologicalModule k V) (tautologicalSection k V u) le_rfl)
      (eval_tautologicalSection_add k V v w _)).trans
    (divBySection_add (tautologicalModule k V) (tautologicalSection k V u) le_rfl _ _)

/-- Restricting a global section of `𝒪(1)` to an open is evaluating it there. -/
private theorem resTop_eval_top (s : (tautologicalModule k V).sections)
    (U : (projectiveSpaceOfModule k V).Opens) :
    Stacks.SectionExtension.resTop (M := tautologicalModule k V) U (s.eval (op ⊤))
      = s.eval (op U) :=
  PresheafOfModules.sections_property s (homOfLE (le_top : U ≤ ⊤)).op

/-- **The global section of `𝒪(1)` attached to `c • v` is the scalar times the one attached to
`v`**, over every open of `𝐏(V)`. -/
public theorem resTop_tautologicalSection_smul (c : k) (v : V)
    (U : (projectiveSpaceOfModule k V).Opens) :
    Stacks.SectionExtension.resTop (M := tautologicalModule k V) U
        ((tautologicalSection k V (c • v)).eval (op ⊤))
      = ((projectiveSpaceOfModule k V).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
            (scalarSectionProj k V c)
        • Stacks.SectionExtension.resTop (M := tautologicalModule k V) U
            ((tautologicalSection k V v).eval (op ⊤)) := by
  have htop : Stacks.SectionExtension.resTop (M := tautologicalModule k V) ⊤
        ((tautologicalSection k V (c • v)).eval (op ⊤))
      = scalarSectionProj k V c
        • Stacks.SectionExtension.resTop (M := tautologicalModule k V) ⊤
            ((tautologicalSection k V v).eval (op ⊤)) := by
    rw [resTop_eval_top, resTop_eval_top]
    exact (eval_top_tautologicalSection k V (c • v)).trans
      (((congrArg
            (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection (symmetricGrading k V) 1)
            (show (⟨SymmetricAlgebra.ι k V (c • v), ι_mem_symmetricPower_one k V (c • v)⟩ :
                  symmetricGrading k V 1)
                = c • ⟨SymmetricAlgebra.ι k V v, ι_mem_symmetricPower_one k V v⟩ from
              Subtype.ext (map_smul (SymmetricAlgebra.ι k V) c v))).trans
          (Stacks.AlgebraicGeometry.ProjectiveSpaceSections.degreeSection_smul k V 1 c _)).trans
        (congrArg _ (eval_top_tautologicalSection k V v).symm))
  have hmap := congrArg
    ((tautologicalModule k V).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) htop
  rwa [Scheme.Modules.map_smul] at hmap

/-- **The ratio `ι v / ι u` is `k`-homogeneous in its numerator**, the scalar acting as the
global function it becomes along the structure morphism of `𝐏(V)`. -/
public theorem tautRatio_smul (u : V) (c : k) (v : V) :
    tautRatio k V u (c • v)
      = ((projectiveSpaceOfModule k V).presheaf.map
            (homOfLE (le_top : nonvanishingOpen (tautologicalModule k V)
              (tautologicalSection k V u) ≤ ⊤)).op) (scalarSectionProj k V c)
        * tautRatio k V u v :=
  (congrArg (divBySection (tautologicalModule k V) (tautologicalSection k V u) le_rfl)
      (((resTop_eval_top k V (tautologicalSection k V (c • v)) _).symm.trans
          (resTop_tautologicalSection_smul k V c v _)).trans
        (congrArg _ (resTop_eval_top k V (tautologicalSection k V v) _)))).trans
    (divBySection_smul (tautologicalModule k V) (tautologicalSection k V u) le_rfl _ _)

/-! ### The pulled-back ratio is `k`-linear in its numerator -/

/-- **The pullback of the ratio `ι v / ι u` along a projection is additive in `v`.** -/
public theorem chartRatio_add (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u v w : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u)) :
    chartRatio k V f u (v + w) hU = chartRatio k V f u v hU + chartRatio k V f u w hU := by
  simp only [chartRatio]
  rw [tautRatio_add]
  exact map_add _ _ _

/-- **The pullback of the ratio `ι v / ι u` along a projection over `Spec k` is `k`-homogeneous
in `v`**, the scalar acting as the global function it becomes along the structure morphism of the
triple product — the same function for all three projections. -/
public theorem chartRatio_smul (f : prodThree k V ⟶ projectiveSpaceOfModule k V)
    (hf : f ≫ projectiveSpaceOfModuleToSpec k V = prodThreeToSpec k V) (u : V) (c : k) (v : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u)) :
    chartRatio k V f u (c • v) hU
      = ((prodThree k V).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
          (scalarSectionProdThree k V c) * chartRatio k V f u v hU := by
  simp only [chartRatio]
  rw [tautRatio_smul, _root_.map_mul]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← appTop_scalarSectionProj k V f hf]
  rfl

/-! ### The ratio at a point of a chart, read in the residue field -/

/-- **A scalar as an element of the residue field at a point of the triple product**, through the
structure morphism over `Spec k`. This is the one map `k → κ(x)` against which all three of the
pulled-back ratios are homogeneous. -/
public def scalarResidue (x : prodThree k V) :
    k →+* IsLocalRing.ResidueField ((prodThree k V).presheaf.stalk x) :=
  (IsLocalRing.residue ((prodThree k V).presheaf.stalk x)).comp
    ((((prodThree k V).presheaf.germ ⊤ x trivial).hom).comp
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (prodThreeToSpec k V).appTop).hom))

/-- The residue at a point of the global function attached to a scalar, restricted to an open
containing the point, is the image of the scalar in the residue field. -/
public theorem residue_germ_scalarSection (c : k) {U : (prodThree k V).Opens}
    {x : prodThree k V} (hx : x ∈ U) :
    IsLocalRing.residue ((prodThree k V).presheaf.stalk x)
        (((prodThree k V).presheaf.germ U x hx).hom
          (((prodThree k V).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)
            (scalarSectionProdThree k V c)))
      = scalarResidue k V x c := by
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- **The residue at a point of the chart of the pulled-back ratio is additive in the
numerator.** -/
public theorem residue_germ_chartRatio_add
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V) (u v w : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))
    {x : prodThree k V} (hx : x ∈ U) :
    IsLocalRing.residue ((prodThree k V).presheaf.stalk x)
        (((prodThree k V).presheaf.germ U x hx).hom (chartRatio k V f u (v + w) hU))
      = IsLocalRing.residue ((prodThree k V).presheaf.stalk x)
            (((prodThree k V).presheaf.germ U x hx).hom (chartRatio k V f u v hU))
        + IsLocalRing.residue ((prodThree k V).presheaf.stalk x)
            (((prodThree k V).presheaf.germ U x hx).hom (chartRatio k V f u w hU)) := by
  rw [chartRatio_add, _root_.map_add, _root_.map_add]

/-- **The residue at a point of the chart of the pulled-back ratio is `k`-homogeneous in the
numerator**, against the map `AlgebraicGeometry.ProjectiveSpaceOfModule.scalarResidue`, which
does not depend on the projection. -/
public theorem residue_germ_chartRatio_smul
    (f : prodThree k V ⟶ projectiveSpaceOfModule k V)
    (hf : f ≫ projectiveSpaceOfModuleToSpec k V = prodThreeToSpec k V) (u : V) (c : k) (v : V)
    {U : (prodThree k V).Opens}
    (hU : U ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V) (tautologicalSection k V u))
    {x : prodThree k V} (hx : x ∈ U) :
    IsLocalRing.residue ((prodThree k V).presheaf.stalk x)
        (((prodThree k V).presheaf.germ U x hx).hom (chartRatio k V f u (c • v) hU))
      = scalarResidue k V x c
        * IsLocalRing.residue ((prodThree k V).presheaf.stalk x)
            (((prodThree k V).presheaf.germ U x hx).hom (chartRatio k V f u v hU)) := by
  rw [chartRatio_smul k V f hf, _root_.map_mul, _root_.map_mul,
    residue_germ_scalarSection k V c hx]

/-! ### Collinearity of a triple over a pair of distinct closed points on the line -/

/-- **A triple whose first two projections are distinct closed points and whose third projection
lies on the line joining them is collinear.** This is the converse of
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_linearSubspace_lineSubmodule_of_mem_collinearLocus`.

Choose a chart around the point and linear functionals `g₁`, `g₂` cutting out the hyperplanes of
the first two projections; take `a` vanishing at the second point only and `b` at the first only.
Every vector `y` is `c + α a + β b` with `c` in the line's submodule `W₁ ⊓ W₂` and
`α = g₁ y / g₁ a`, `β = g₂ y / g₂ b` in `k`. Since `W₁ ⊓ W₂` is contained in all three
hyperplanes — in the third by hypothesis — the `k`-linearity of the ratio
(`AlgebraicGeometry.ProjectiveSpaceOfModule.residue_germ_chartRatio_add` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.residue_germ_chartRatio_smul`) puts every column of
every matrix of ratios in the span of the two columns of `a` and `b`, so every determinant
vanishes in the residue field and is a non-unit of the local ring. -/
public theorem mem_collinearLocus_of_lineSubmodule_le [IsAlgClosed k] [Module.Finite k V]
    {x : prodThree k V}
    (hcl₁ : IsClosed ({(pr₁ k V).base x} : Set (projectiveSpaceOfModule k V)))
    (hcl₂ : IsClosed ({(pr₂ k V).base x} : Set (projectiveSpaceOfModule k V)))
    (hne : (pr₁ k V).base x ≠ (pr₂ k V).base x)
    (hle : lineSubmodule k V ((pr₁ k V).base x) ((pr₂ k V).base x) ≤
      pointSubmodule k V ((pr₃ k V).base x)) :
    x ∈ collinearLocus k V := by
  obtain ⟨b, hb₁, hb₂⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_pointSubmodule_le k V hcl₁ hcl₂ hne)
  obtain ⟨a, ha₂, ha₁⟩ := IsConcreteLE.not_le_iff_exists.mp
    (not_pointSubmodule_le k V hcl₂ hcl₁ hne.symm)
  obtain ⟨g₁, hg₁ne, hg₁eq⟩ := exists_eq_linearFunctionalPoint k V _ hcl₁
  obtain ⟨g₂, hg₂ne, hg₂eq⟩ := exists_eq_linearFunctionalPoint k V _ hcl₂
  have hk₁ : pointSubmodule k V ((pr₁ k V).base x) = LinearMap.ker g₁ := by
    rw [hg₁eq, pointSubmodule_linearFunctionalPoint]
  have hk₂ : pointSubmodule k V ((pr₂ k V).base x) = LinearMap.ker g₂ := by
    rw [hg₂eq, pointSubmodule_linearFunctionalPoint]
  have hga : g₁ a ≠ 0 := fun h => ha₁ (hk₁ ▸ LinearMap.mem_ker.mpr h)
  have hgb : g₂ b ≠ 0 := fun h => hb₂ (hk₂ ▸ LinearMap.mem_ker.mpr h)
  have hg₁b : g₁ b = 0 := LinearMap.mem_ker.mp (hk₁ ▸ hb₁)
  have hg₂a : g₂ a = 0 := LinearMap.mem_ker.mp (hk₂ ▸ ha₂)
  have hdecomp : ∀ y : V, y - (g₁ y / g₁ a) • a - (g₂ y / g₂ b) • b ∈
      lineSubmodule k V ((pr₁ k V).base x) ((pr₂ k V).base x) := fun y => by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hk₁, LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, hg₁b]
      simp only [smul_eq_mul, mul_zero, sub_zero]
      field_simp
      ring
    · rw [hk₂, LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, hg₂a]
      simp only [smul_eq_mul, mul_zero, sub_zero]
      field_simp
      ring
  obtain ⟨uu, hmem⟩ := exists_mem_chartOpen k V x
  have h₁ := chartOpen_le_pr₁ k V uu
  have h₂ := chartOpen_le_pr₂ k V uu
  have h₃ := chartOpen_le_pr₃ k V uu
  set φ : Γ(prodThree k V, chartOpen k V uu) →+*
      IsLocalRing.ResidueField ((prodThree k V).presheaf.stalk x) :=
    (IsLocalRing.residue ((prodThree k V).presheaf.stalk x)).comp
      ((prodThree k V).presheaf.germ (chartOpen k V uu) x hmem).hom with hφdef
  have hrow : ∀ (f : prodThree k V ⟶ projectiveSpaceOfModule k V)
      (_ : f ≫ projectiveSpaceOfModuleToSpec k V = prodThreeToSpec k V) (e : V)
      (he : chartOpen k V uu ≤ f ⁻¹ᵁ nonvanishingOpen (tautologicalModule k V)
        (tautologicalSection k V e))
      (_ : lineSubmodule k V ((pr₁ k V).base x) ((pr₂ k V).base x) ≤
        pointSubmodule k V (f.base x)) (y : V),
      φ (chartRatio k V f e y he)
        = scalarResidue k V x (g₁ y / g₁ a) * φ (chartRatio k V f e a he)
          + scalarResidue k V x (g₂ y / g₂ b) * φ (chartRatio k V f e b he) := by
    intro f hf e he hker y
    set α := g₁ y / g₁ a
    set β := g₂ y / g₂ b
    have hz := (residue_germ_chartRatio_eq_zero_iff k V f e _ he hmem).mpr (hker (hdecomp y))
    simp only [hφdef, RingHom.comp_apply] at hz ⊢
    conv_lhs => rw [← show y - α • a - β • b + (α • a + β • b) = y by abel]
    rw [residue_germ_chartRatio_add, residue_germ_chartRatio_add,
      residue_germ_chartRatio_smul k V f hf, residue_germ_chartRatio_smul k V f hf, hz, zero_add]
  have hrow₁ := hrow (pr₁ k V) (pr₁_comp_toSpec k V) (uu 0) h₁ inf_le_left
  have hrow₂ := hrow (pr₂ k V) (pr₂_comp_toSpec k V) (uu 1) h₂ inf_le_right
  have hrow₃ := hrow (pr₃ k V) (pr₃_comp_toSpec k V) (uu 2) h₃ hle
  refine (mem_collinearLocus_iff_forall_not_isUnit_germ_det k V uu h₁ h₂ h₃ hmem).mpr
    fun w hunit => ?_
  have hdet : φ ((chartMatrix k V uu w h₁ h₂ h₃).det) = 0 := by
    rw [RingHom.map_det, Matrix.det_fin_three,
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 0 0 = _ from hrow₁ (w 0),
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 0 1 = _ from hrow₁ (w 1),
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 0 2 = _ from hrow₁ (w 2),
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 1 0 = _ from hrow₂ (w 0),
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 1 1 = _ from hrow₂ (w 1),
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 1 2 = _ from hrow₂ (w 2),
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 2 0 = _ from hrow₃ (w 0),
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 2 1 = _ from hrow₃ (w 1),
      show (φ.mapMatrix (chartMatrix k V uu w h₁ h₂ h₃)) 2 2 = _ from hrow₃ (w 2)]
    ring
  exact IsLocalRing.notMem_maximalIdeal.mpr hunit
    ((IsLocalRing.residue_eq_zero_iff _).mp hdet)

/-- **The collinear triples over a pair of distinct closed points are exactly those whose third
projection lies on the line joining the pair.** -/
public theorem mem_collinearLocus_iff_mem_linearSubspace_lineSubmodule [IsAlgClosed k]
    [Module.Finite k V] {x : prodThree k V}
    (hcl₁ : IsClosed ({(pr₁ k V).base x} : Set (projectiveSpaceOfModule k V)))
    (hcl₂ : IsClosed ({(pr₂ k V).base x} : Set (projectiveSpaceOfModule k V)))
    (hne : (pr₁ k V).base x ≠ (pr₂ k V).base x) :
    x ∈ collinearLocus k V ↔
      (pr₃ k V).base x ∈
        linearSubspace k V (lineSubmodule k V ((pr₁ k V).base x) ((pr₂ k V).base x)) :=
  ⟨fun hx => mem_linearSubspace_lineSubmodule_of_mem_collinearLocus k V hx hcl₁ hcl₂ hne,
    fun hx => mem_collinearLocus_of_lineSubmodule_le k V hcl₁ hcl₂ hne
      ((mem_linearSubspace_iff k V _ _).mp hx)⟩

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
