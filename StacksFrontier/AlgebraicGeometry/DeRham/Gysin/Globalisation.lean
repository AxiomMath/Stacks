module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.MapOnSections
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.EquationWedge
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.HomGlue

/-!
# Globalising the Gysin maps of a closed immersion

Let `π : X ⟶ S` be a morphism of schemes and let `i : Z ⟶ X` be a closed immersion of finite
presentation whose conormal sheaf is locally free of rank `c`. Then `Z` is, locally on `X`, cut
out by `c` equations `f₁, …, f_c`, and each such family of equations carries a Gysin map

`γ^p_{f₁, …, f_c} : Ω^p_{Z/S} ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})`.

**Tag 0G86 is the assertion that these local maps glue**: there is one canonical map
`γ^p : Ω^p_{Z/S} ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})` which restricts to `γ^p_{f₁, …, f_c}` over every open
on which `f₁, …, f_c` cut out `Z`. That is what is proved here, and the conclusion says exactly
that: `Stacks.Gysin.GysinChartData.gysinHom_app` is the statement that the glued map agrees with
the given local map on the sections over every open contained in an equation chart, and
`Stacks.Gysin.GysinChartData.gysinHom_app_subschemeFormPullback` spells this out as the Gysin
formula of [Stacks, Tag 0G83] for the *global* map.

Both sheaves are read on the ambient scheme: the source as the direct image `i_*Ω^p_{Z/S}` and
the target as the direct image of the local cohomology sheaf. That is forced, and is the shape
the local maps come in: the target is not annihilated by the equations — already for one
equation on the affine line, multiplication by the equation on the degree-one local cohomology of
the structure sheaf is invertible — so the Gysin map is a map of `i⁻¹𝒪_X`-modules and not of
`𝒪_Z`-modules, and `i_*` is the faithful functor in which both sides become `𝒪_X`-modules.

## Main definitions

* `Stacks.Gysin.equationsWedgeOn` and `Stacks.Gysin.gysinWedgeOn`: the ordered wedge
  `d f₁ ∧ ⋯ ∧ d f_c` of the differentials of functions defined only on an open `W` of `X`, and
  right multiplication by it, on the sections over an open `V ≤ W`. These generalise
  `AlgebraicGeometry.Scheme.Hom.equationsWedge` and
  `AlgebraicGeometry.Scheme.Hom.gysinWedgeHom` from global functions to functions on a chart;
  `Stacks.Gysin.equationsWedgeOn_top` and `Stacks.Gysin.gysinWedgeOn_top` identify them with
  those over `W = ⊤`.
* `Stacks.Gysin.subschemeFormPullback`: restriction `ω̃ ↦ ω̃|_Z` of an ambient relative
  differential form to the closed subscheme, on sections.
* `Stacks.Gysin.ChartComparison`: the comparison of two equation charts over a common open — the
  change-of-equations matrix, the determinant rule of [Stacks, Tag 0G7S] for the classes
  `c_{f₁, …, f_c}`, the matching congruence for the equation wedges, and the liftability of
  relative forms from `Z`.
* `Stacks.Gysin.GysinChartData`: the local Gysin maps of [Stacks, Tag 0G83] together with the
  chart comparisons, which is the input of the globalisation.
* `Stacks.Gysin.GysinChartData.gysinHom`: **the canonical Gysin map of [Stacks, Tag 0G86].**

## Main results

* `Stacks.Gysin.GysinChartData.locAgreeOn`: **independence of the chosen equations**, over an
  open carrying a chart comparison. This is the computation of [Stacks, Tag 0G86]: lift the form
  to the ambient scheme, use the Gysin formula on both sides, replace the equation wedge of one
  chart by the determinant multiple of the other's plus a combination of the equations, and
  observe that the class map kills the latter.
* `Stacks.Gysin.GysinChartData.locAgree`: the local Gysin maps of two charts agree on the
  sections over *every* open contained in both — the previous result spread over a covering by
  opens carrying a comparison, using that the target is a sheaf.
* `Stacks.Gysin.GysinChartData.gysinHom_app`: **the Gysin map is locally the Gysin map of the
  equations**, and `Stacks.Gysin.GysinChartData.existsUnique_gysinHom`: it is the unique map with
  that property, which is the sense in which it is canonical.
* `Stacks.Gysin.GysinChartData.gysinHom_app_subschemeFormPullback`: the Gysin formula for the
  glued map: on the restriction `ω̃|_Z` of an ambient `p`-form over an open of a chart, its value
  is `c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`.

## Implementation notes

`GysinChartData` is the input of the gluing. Its fields are the equation charts and the fact that
they cover `X`; on each chart, the target `i_*ℋ^c_Z(Ω^{p+c}_{X/S})`, the class map
`c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] and the local Gysin map of [Stacks, Tag 0G83] with its
Gysin formula, all on sections; and, over a covering of each open contained in two charts, a
`ChartComparison`: the change-of-equations matrix, the determinant rule of [Stacks, Tag 0G7S] for
the two class maps, the matching congruence for the equation wedges, and the liftability of
relative forms from `Z`. The agreement of the local maps is not a field: it is
`GysinChartData.locAgree`, proved from the comparisons.

Every field is constructed from the hypotheses of Tag 0G86 by
`Stacks.Gysin.gysinChartDataOfClsDet` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/ChartDataComparison.lean`, with the determinant rule
across two charts given by `Stacks.Gysin.clsDetAcrossCharts`;
`Stacks.Gysin.exists_gysinChartData` is that assembly, and
`Stacks.Gysin.existsUnique_gysinHom_of_conormalRank` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinConormalRankAny.lean` states the whole of
Tag 0G86. The results in this file are the gluing itself, stated for a `GysinChartData`. The
fields are constructed as follows:

* `target` is `Stacks.Gysin.gysinTarget`, the degree-`c` cohomology sheaf of `i_*R𝓗_Z(ℱ[0])` in
  the spelling `Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`;
* `cls` is `Stacks.Gysin.chartCls`, the class map of a chart's own equations carried into
  `gysinTarget` by the derived excision `Stacks.Gysin.supportCohomologyRestrictIso`, and
  `cls_vanish` is `Stacks.Gysin.chartCls_vanish`;
* `ambient`, `equations`, `equations_vanish` and `ambient_cover` are
  `Stacks.Gysin.exists_gysinCharts`, from a rank-`c` conormal sheaf;
* `loc`, `loc_add`, `loc_smul` and `loc_res` are `Stacks.Gysin.chartLoc` with `chartLoc_add`,
  `chartLoc_smul` and `chartLoc_res`, and `loc_subschemeFormPullback` is
  `Stacks.Gysin.chartLoc_subschemeFormPullback`;
* `ChartComparison.cls_det` is `Stacks.Gysin.chartCls_det`, `ChartComparison.wedge_det` is
  `Stacks.Gysin.chartWedgeDet`, and `ChartComparison.lift` is
  `Stacks.Gysin.exists_subschemeFormPullback_of_isAffineOpen`.

The target is the derived spelling rather than
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyOn`: both are right derived functors of the
same degree-zero functor, and with the derived spelling the chart transport is the derived
excision itself, so no coherence between two independently constructed excision isomorphisms is
needed.

`GysinChartData.comparison` is stated over a covering of each open contained in two charts, rather
than over the overlap of the two charts, because agreement of two local maps over an open does not
imply agreement over a smaller one: a section over the smaller open is only locally the
restriction of one from above. This is what the gluing consumes, since
`Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover` asks for agreement over every
open contained in two members of the covering.

The gluing is `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover` and the
uniqueness is `Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_eq_of_cover`. The equation
wedge is `SheafOfModules.GradedAlgebra.prodDegOne` and
`AlgebraicGeometry.Scheme.Hom.exactOneForm` of
`StacksFrontier.AlgebraicGeometry.DeRham.Gysin.EquationWedge`, with that file's `prodDegOne_map` and
`exactOneForm_map` giving `equationsWedgeOn_map`. Restriction of forms to the subscheme is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback` at the square with `𝟙 S` on the
base.

## References

* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Tag 0G7I](https://stacks.math.columbia.edu/tag/0G7I)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G72](https://stacks.math.columbia.edu/tag/0G72)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.Gysin

variable {Z X S : Scheme.{u}}

/-! ### The equation wedge of functions defined on a chart -/

/-- The ordered wedge `d f₁ ∧ ⋯ ∧ d f_c` of the relative differentials of a family of functions
defined on an open `W` of `X`, as a section of `Ω^c_{X/S}` over an open `V ≤ W`. For `W = ⊤`
this is the global section `AlgebraicGeometry.Scheme.Hom.equationsWedge` evaluated at `V`. -/
def equationsWedgeOn (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W))
    {V : X.Opens} (hV : V ≤ W) : Γ(relativeDifferentialForms π (c : ℤ), V) :=
  (relativeDifferentialFormsAlgebra π).prodDegOne (op V) c fun j =>
    exactOneForm π (op V) (X.presheaf.map (homOfLE hV).op (f j))

/-- Over the whole scheme the equation wedge of a chart is the global section
`AlgebraicGeometry.Scheme.Hom.equationsWedge`. -/
theorem equationsWedgeOn_top (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (V : X.Opens) :
    equationsWedgeOn π f (le_top : V ≤ ⊤) = (equationsWedge π f).eval (op V) :=
  rfl

/-- Restricting along `V' ≤ V` and then `V ≤ W` is restricting along `V' ≤ W`. -/
private theorem presheaf_map_homOfLE_map_homOfLE {W V V' : X.Opens} (h : V' ≤ V) (hV : V ≤ W)
    (h' : V' ≤ W) (s : Γ(X, W)) :
    X.presheaf.map (homOfLE h).op (X.presheaf.map (homOfLE hV).op s) =
      X.presheaf.map (homOfLE h').op s := by
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp, ← op_comp]
  rfl

/-- The equation wedge of a chart commutes with restriction. -/
theorem equationsWedgeOn_map (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W))
    {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ V) :
    (relativeDifferentialForms π (c : ℤ)).presheaf.map (homOfLE hV').op
        (equationsWedgeOn π f hV) =
      equationsWedgeOn π f (hV'.trans hV) := by
  refine ((relativeDifferentialFormsAlgebra π).prodDegOne_map (homOfLE hV').op c _).trans ?_
  refine congrArg ((relativeDifferentialFormsAlgebra π).prodDegOne (op V') c) (funext fun j => ?_)
  refine (exactOneForm_map π (homOfLE hV').op _).trans (congrArg (exactOneForm π (op V')) ?_)
  exact presheaf_map_homOfLE_map_homOfLE hV' hV _ _

/-- The equation wedge of a chart depends only on the restrictions of the functions. -/
theorem equationsWedgeOn_restrict (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W))
    {V : X.Opens} (hV : V ≤ W) :
    equationsWedgeOn π (fun j => X.presheaf.map (homOfLE hV).op (f j)) (le_refl V) =
      equationsWedgeOn π f hV := by
  refine congrArg ((relativeDifferentialFormsAlgebra π).prodDegOne (op V) c) (funext fun j => ?_)
  exact congrArg (exactOneForm π (op V)) (presheaf_map_homOfLE_map_homOfLE le_rfl hV _ _)

/-- Right multiplication by the equation wedge `d f₁ ∧ ⋯ ∧ d f_c` of functions defined on an open
`W` of `X`, on the sections over an open `V ≤ W`. For `W = ⊤` this is
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom` on sections. -/
def gysinWedgeOn (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W)) (p : ℤ)
    {V : X.Opens} (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π p, V)) :
    Γ(relativeDifferentialForms π (p + (c : ℤ)), V) :=
  ((relativeDifferentialFormsAlgebra π).mul p (c : ℤ)).app (op V) ω (equationsWedgeOn π f hV)

/-- Over the whole scheme the local wedge map of a chart is
`AlgebraicGeometry.Scheme.Hom.gysinWedgeHom` on sections. -/
theorem gysinWedgeOn_top (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℤ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π p, V)) :
    gysinWedgeOn π f p (le_top : V ≤ ⊤) ω = (gysinWedgeHom π f p).val.app (op V) ω :=
  rfl

/-- The local wedge map of a chart is additive. -/
theorem gysinWedgeOn_add (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W)) (p : ℤ)
    {V : X.Opens} (hV : V ≤ W) (ω ω' : Γ(relativeDifferentialForms π p, V)) :
    gysinWedgeOn π f p hV (ω + ω') = gysinWedgeOn π f p hV ω + gysinWedgeOn π f p hV ω' :=
  ((relativeDifferentialFormsAlgebra π).mul p (c : ℤ)).map_add_left (op V) ω ω'
    (equationsWedgeOn π f hV)

/-- The local wedge map of a chart is homogeneous. -/
theorem gysinWedgeOn_smul (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W)) (p : ℤ)
    {V : X.Opens} (hV : V ≤ W) (r : Γ(X, V)) (ω : Γ(relativeDifferentialForms π p, V)) :
    gysinWedgeOn π f p hV (r • ω) = r • gysinWedgeOn π f p hV ω :=
  ((relativeDifferentialFormsAlgebra π).mul p (c : ℤ)).map_smul_left (op V) r ω
    (equationsWedgeOn π f hV)

/-- The local wedge map of a chart commutes with restriction. -/
theorem gysinWedgeOn_map (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W)) (p : ℤ)
    {V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ V) (ω : Γ(relativeDifferentialForms π p, V)) :
    (relativeDifferentialForms π (p + (c : ℤ))).presheaf.map (homOfLE hV').op
        (gysinWedgeOn π f p hV ω) =
      gysinWedgeOn π f p (hV'.trans hV)
        ((relativeDifferentialForms π p).presheaf.map (homOfLE hV').op ω) :=
  (((relativeDifferentialFormsAlgebra π).mul p (c : ℤ)).naturality (homOfLE hV').op ω
      (equationsWedgeOn π f hV)).trans
    (congrArg
      (((relativeDifferentialFormsAlgebra π).mul p (c : ℤ)).app (op V')
        ((relativeDifferentialForms π p).presheaf.map (homOfLE hV').op ω))
      (equationsWedgeOn_map π f hV hV'))

/-- The local wedge map of a chart depends only on the restrictions of the functions. -/
theorem gysinWedgeOn_restrict (π : X ⟶ S) {W : X.Opens} {c : ℕ} (f : Fin c → Γ(X, W)) (p : ℤ)
    {V : X.Opens} (hV : V ≤ W) (ω : Γ(relativeDifferentialForms π p, V)) :
    gysinWedgeOn π (fun j => X.presheaf.map (homOfLE hV).op (f j)) p (le_refl V) ω =
      gysinWedgeOn π f p hV ω :=
  congrArg (((relativeDifferentialFormsAlgebra π).mul p (c : ℤ)).app (op V) ω)
    (equationsWedgeOn_restrict π f hV)

/-! ### Restriction of relative differential forms to the closed subscheme -/

/-- The direct image `i_*Ω^n_{Z/S}` of the relative differential forms of the closed subscheme:
the source of the Gysin map, read on the ambient scheme. -/
abbrev pushforwardRelativeForms (i : Z ⟶ X) (π : X ⟶ S) (n : ℤ) : X.Modules :=
  (Scheme.Modules.pushforward i).obj (relativeDifferentialForms (i ≫ π) n)

/-- Restriction `ω̃ ↦ ω̃|_Z` of an ambient relative differential form to the closed subscheme, on
the sections over an open `V` of `X`. This is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsPullback` at the square with `𝟙 S` on the
base, whose target `Γ(Ω^n_{Z/S}, i⁻¹V)` is the sections of `i_*Ω^n_{Z/S}` over `V`. -/
def subschemeFormPullback (i : Z ⟶ X) (π : X ⟶ S) (n : ℤ) (V : X.Opens)
    (ω : Γ(relativeDifferentialForms π n, V)) : Γ(pushforwardRelativeForms i π n, V) :=
  relativeDifferentialFormsPullback i π (i ≫ π) (𝟙 S) (Category.comp_id (i ≫ π)).symm n V ω

/-! ### Comparison of two equation charts -/

/-- **The comparison of two families of equations over a common open `V` of `X`.** The data is
the one the proof of [Stacks, Tag 0G86] shrinks `V` to obtain: a matrix expressing the second
family in terms of the first, the determinant rule of [Stacks, Tag 0G7S] relating the two class
maps `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q], the matching congruence for the two equation
wedges, and the liftability of relative `p`-forms on `Z` to the ambient scheme over `V`.

`clsa` and `clsb` are the class maps of the two families over `V`, and `f` and `g` are the two
families. -/
structure ChartComparison (i : Z ⟶ X) (π : X ⟶ S) (c p : ℕ) {V : X.Opens} {T : X.Modules}
    (clsa clsb : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V) →+ Γ(T, V))
    (f g : Fin c → Γ(X, V)) where
  /-- The change-of-equations matrix `(a_{jl})`. -/
  matrix : Matrix (Fin c) (Fin c) Γ(X, V)
  /-- The second family is the matrix applied to the first: `g_j = ∑_l a_{jl} f_l`. -/
  equations_eq : ∀ j, g j = ∑ l, matrix j l * f l
  /-- **[Stacks, Tag 0G7S].** The two class maps differ by the determinant of the matrix:
  `c_{f₁, …, f_c} = det(a_{jl}) c_{g₁, …, g_c}`, written with the scalar moved inside the second
  class map, which is `𝒪_X`-linear. -/
  cls_det : ∀ y, clsa y = clsb (matrix.det • y)
  /-- The two equation wedges differ by the determinant of the matrix modulo the equations:
  `ω ∧ d g₁ ∧ ⋯ ∧ d g_c = det(a_{jl}) (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) + ∑_l f_l η_l`. -/
  wedge_det : ∀ ω : Γ(relativeDifferentialForms π (p : ℤ), V),
    ∃ η : Fin c → Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V),
      gysinWedgeOn π g (p : ℤ) (le_refl V) ω =
        matrix.det • gysinWedgeOn π f (p : ℤ) (le_refl V) ω + ∑ l, f l • η l
  /-- Every relative `p`-form on `Z` over the preimage of `V` is the restriction of an ambient
  one over `V`. -/
  lift : ∀ x : Γ(pushforwardRelativeForms i π (p : ℤ), V),
    ∃ ω, subschemeFormPullback i π (p : ℤ) V ω = x

/-! ### The input of the globalisation -/

/-- **The local Gysin maps of [Stacks, Tag 0G83] on a family of equation charts, together with
the chart comparisons.** This is the input of the gluing of [Stacks, Tag 0G86]. The agreement of
the local maps is *not* among the fields: it is `GysinChartData.locAgree`, proved from
`GysinChartData.comparison`. -/
structure GysinChartData (i : Z ⟶ X) (π : X ⟶ S) (c p : ℕ) where
  /-- The target `i_*ℋ^c_Z(Ω^{p+c}_{X/S})` of the Gysin map, read on the ambient scheme. -/
  target : X.Modules
  /-- The index type of the equation charts. -/
  Chart : Type u
  /-- The open of `X` on which a chart is defined. -/
  ambient : Chart → X.Opens
  /-- The `c` equations cutting out `Z` on that open. -/
  equations : (a : Chart) → Fin c → Γ(X, ambient a)
  /-- The equations vanish on `Z`: they lie in the ideal of the closed subscheme. -/
  equations_vanish : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) (j : Fin c),
    (i.app V).hom (X.presheaf.map (homOfLE hV).op (equations a j)) = 0
  /-- The charts cover the ambient scheme. -/
  ambient_cover : ∀ x : X, ∃ a, x ∈ ambient a
  /-- The class map `c_{f₁, …, f_c}` of [Stacks, Tag 0G7Q] of a chart, on sections. -/
  cls : (a : Chart) → (V : X.Opens) → V ≤ ambient a →
    Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V) →+ Γ(target, V)
  /-- The class map kills a form with a coefficient vanishing on `Z`, because it factors through
  the restriction `i^*Ω^{p+c}_{X/S}` of the forms to the closed subscheme. -/
  cls_vanish : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) (r : Γ(X, V))
    (ω : Γ(relativeDifferentialForms π ((p : ℤ) + (c : ℤ)), V)),
    (i.app V).hom r = 0 → cls a V hV (r • ω) = 0
  /-- The Gysin map `γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] of a chart, on sections. -/
  loc : (a : Chart) → (V : X.Opens) → V ≤ ambient a →
    Γ(pushforwardRelativeForms i π (p : ℤ), V) → Γ(target, V)
  /-- The local Gysin map is additive. -/
  loc_add : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a)
    (x y : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
    loc a V hV (x + y) = loc a V hV x + loc a V hV y
  /-- The local Gysin map is homogeneous. -/
  loc_smul : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a) (r : Γ(X, V))
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
    loc a V hV (r • x) = r • loc a V hV x
  /-- The local Gysin map commutes with restriction. -/
  loc_res : ∀ (a : Chart) (V V' : X.Opens) (hV' : V' ≤ V) (hV : V ≤ ambient a)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)),
    loc a V' (hV'.trans hV) ((pushforwardRelativeForms i π (p : ℤ)).presheaf.map (homOfLE hV').op x)
      = target.presheaf.map (homOfLE hV').op (loc a V hV x)
  /-- **The Gysin formula of [Stacks, Tag 0G83].** On the restriction `ω̃|_Z` of an ambient
  `p`-form, the local Gysin map takes the value `c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`. -/
  loc_subschemeFormPullback : ∀ (a : Chart) (V : X.Opens) (hV : V ≤ ambient a)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)),
    loc a V hV (subschemeFormPullback i π (p : ℤ) V ω) =
      cls a V hV (gysinWedgeOn π (equations a) (p : ℤ) hV ω)
  /-- **The chart comparisons.** Every open contained in two charts is covered by opens over
  which the two families of equations are comparable in the sense of `ChartComparison`. -/
  comparison : ∀ (a b : Chart) (V : X.Opens) (ha : V ≤ ambient a) (hb : V ≤ ambient b),
    ∃ (J : Type u) (V' : J → X.Opens) (hle : ∀ k, V' k ≤ V)
        (_ : ∀ k, ChartComparison i π c p
          (cls a (V' k) ((hle k).trans ha)) (cls b (V' k) ((hle k).trans hb))
          (fun j => X.presheaf.map (homOfLE ((hle k).trans ha)).op (equations a j))
          (fun j => X.presheaf.map (homOfLE ((hle k).trans hb)).op (equations b j))),
      V ≤ ⨆ k, V' k

namespace GysinChartData

variable {i : Z ⟶ X} {π : X ⟶ S} {c p : ℕ} (D : GysinChartData i π c p)

/-- **Independence of the chosen equations, over an open carrying a chart comparison.** This is
the computation of [Stacks, Tag 0G86]. Lift the form on `Z` to an ambient form `ω̃` over `V`; by
the Gysin formula the two values are `c_{f₁, …, f_c}(ω̃ ∧ d f₁ ∧ ⋯ ∧ d f_c)` and
`c_{g₁, …, g_c}(ω̃ ∧ d g₁ ∧ ⋯ ∧ d g_c)`. The second equation wedge is the determinant multiple of
the first plus a combination of the equations; the class map is additive and kills the latter,
because the equations vanish on `Z`; and the determinant rule of [Stacks, Tag 0G7S] turns what is
left into the first value. -/
theorem locAgreeOn (a b : D.Chart) (V : X.Opens) (ha : V ≤ D.ambient a) (hb : V ≤ D.ambient b)
    (cmp : ChartComparison i π c p (D.cls a V ha) (D.cls b V hb)
      (fun j => X.presheaf.map (homOfLE ha).op (D.equations a j))
      (fun j => X.presheaf.map (homOfLE hb).op (D.equations b j)))
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    D.loc a V ha x = D.loc b V hb x := by
  obtain ⟨ω, hω⟩ := cmp.lift x
  subst hω
  obtain ⟨η, hη⟩ := cmp.wedge_det ω
  have hzero : D.cls b V hb
      (∑ l, X.presheaf.map (homOfLE ha).op (D.equations a l) • η l) = 0 := by
    rw [map_sum]
    exact Finset.sum_eq_zero fun l _ =>
      D.cls_vanish b V hb _ (η l) (D.equations_vanish a V ha l)
  rw [D.loc_subschemeFormPullback a V ha ω, D.loc_subschemeFormPullback b V hb ω,
    ← gysinWedgeOn_restrict π (D.equations a) (p : ℤ) ha ω,
    ← gysinWedgeOn_restrict π (D.equations b) (p : ℤ) hb ω, hη, map_add, hzero, add_zero]
  exact cmp.cls_det _

/-- **The local Gysin maps of two charts agree on the sections over every open contained in
both.** The previous result holds over the members of a covering of such an open, and the target
is a sheaf, so it holds over the open itself. -/
theorem locAgree (a b : D.Chart) (V : X.Opens) (ha : V ≤ D.ambient a) (hb : V ≤ D.ambient b)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    D.loc a V ha x = D.loc b V hb x := by
  obtain ⟨J, V', hle, hcmp, hcov⟩ := D.comparison a b V ha hb
  refine TopCat.Sheaf.eq_of_locally_eq'
    (F := (⟨D.target.presheaf, D.target.isSheaf⟩ : TopCat.Sheaf Ab.{u} X)) V'
    V (fun k => homOfLE (hle k)) hcov _ _ fun k => ?_
  rw [← D.loc_res a V (V' k) (hle k) ha x, ← D.loc_res b V (V' k) (hle k) hb x]
  exact D.locAgreeOn a b (V' k) ((hle k).trans ha) ((hle k).trans hb) (hcmp k) _

/-- **Stacks Project, Tag 0G86: the canonical Gysin map of a closed immersion.** The local Gysin
maps `γ^p_{f₁, …, f_c}` of [Stacks, Tag 0G83] of the equation charts agree on the overlaps, by
`locAgree`, and therefore glue to one map

`γ^p : Ω^p_{Z/S} ⟶ ℋ^c_Z(Ω^{p+c}_{X/S})`,

read here as a map `i_*Ω^p_{Z/S} ⟶ i_*ℋ^c_Z(Ω^{p+c}_{X/S})` of sheaves of `𝒪_X`-modules. That it
is locally given by the maps `γ^p_{f₁, …, f_c}` is `gysinHom_app`, and that it is the only such
map — the sense in which it is canonical — is `existsUnique_gysinHom`. -/
def gysinHom : pushforwardRelativeForms i π (p : ℤ) ⟶ D.target :=
  (Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover D.ambient D.ambient_cover
    D.loc D.loc_add D.loc_smul
    (fun a U V hUV hV m => D.loc_res a V U hUV hV m)
    fun a b V hVa hVb x => D.locAgree a b V hVa hVb x).choose

/-- **Stacks Project, Tag 0G86: the Gysin map is locally the Gysin map of the equations.** On the
sections over an open contained in an equation chart, the canonical map of `gysinHom` is the
local Gysin map `γ^p_{f₁, …, f_c}` of that chart. This is the clause "locally given by the maps
`γ^p_{f₁, …, f_c}`" of the statement. -/
theorem gysinHom_app (a : D.Chart) (V : X.Opens) (hV : V ≤ D.ambient a)
    (x : Γ(pushforwardRelativeForms i π (p : ℤ), V)) :
    D.gysinHom.app V x = D.loc a V hV x :=
  (Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_eq_of_cover D.ambient D.ambient_cover
    D.loc D.loc_add D.loc_smul
    (fun a U V hUV hV m => D.loc_res a V U hUV hV m)
    fun a b V hVa hVb x => D.locAgree a b V hVa hVb x).choose_spec a V hV x

/-- **The Gysin formula for the global map.** On the restriction `ω̃|_Z` of an ambient `p`-form
over an open of a chart, the canonical Gysin map takes the value
`c_{f₁, …, f_c}(ω̃|_Z) ∧ d f₁ ∧ ⋯ ∧ d f_c`. -/
theorem gysinHom_app_subschemeFormPullback (a : D.Chart) (V : X.Opens) (hV : V ≤ D.ambient a)
    (ω : Γ(relativeDifferentialForms π (p : ℤ), V)) :
    D.gysinHom.app V (subschemeFormPullback i π (p : ℤ) V ω) =
      D.cls a V hV (gysinWedgeOn π (D.equations a) (p : ℤ) hV ω) :=
  (D.gysinHom_app a V hV _).trans (D.loc_subschemeFormPullback a V hV ω)

/-- Two maps that are locally the Gysin maps of the equations are equal. -/
theorem eq_of_app_eq_loc {φ ψ : pushforwardRelativeForms i π (p : ℤ) ⟶ D.target}
    (hφ : ∀ (a : D.Chart) (V : X.Opens) (hV : V ≤ D.ambient a) (x), φ.app V x = D.loc a V hV x)
    (hψ : ∀ (a : D.Chart) (V : X.Opens) (hV : V ≤ D.ambient a) (x), ψ.app V x = D.loc a V hV x) :
    φ = ψ := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_app_eq_of_cover D.ambient
    D.ambient_cover fun a V hV => ?_
  ext x
  exact (hφ a V hV x).trans (hψ a V hV x).symm

/-- **Stacks Project, Tag 0G86: the Gysin map is the unique map that is locally the Gysin map of
the equations.** This is the precise sense in which it is *canonical*. -/
theorem existsUnique_gysinHom :
    ∃! φ : pushforwardRelativeForms i π (p : ℤ) ⟶ D.target,
      ∀ (a : D.Chart) (V : X.Opens) (hV : V ≤ D.ambient a) (x), φ.app V x = D.loc a V hV x :=
  ⟨D.gysinHom, fun a V hV x => D.gysinHom_app a V hV x,
    fun _ hφ => D.eq_of_app_eq_loc hφ fun a V hV x => D.gysinHom_app a V hV x⟩

end GysinChartData

end Stacks.Gysin

end
