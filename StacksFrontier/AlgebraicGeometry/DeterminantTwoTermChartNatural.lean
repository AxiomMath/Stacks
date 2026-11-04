module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartGlue

/-!
# The chart comparison of the determinant is natural in the complex

Let `X` be a scheme and let `L` and `K` be perfect objects of `D(𝒪_X)` of Tor-amplitude in
`[-1, 0]`. An isomorphism `a : L ≅ K` restricts to every affine chart, and the chart complex
`AlgebraicGeometry.DeterminantTwoTerm.chartComplex` of an affine open `V` is therefore functorial
in the complex. This file constructs that functoriality and proves that the chart comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` of determinants over the rings is
**natural** in the complex: for affine opens `V ≤ W` the square formed by the two comparisons and
by the determinants of the restrictions of `a` to the charts of `V` and of `W` commutes.

Together with the transitivity of
`StacksFrontier/AlgebraicGeometry/DeterminantTwoTermChartTrans.lean` this is what makes the family of
determinants on the charts a functor of `L`, which is the last structural input the determinant of
Stacks 0FJX on an arbitrary scheme needs from the affine case.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.chartComplexIso`: **the chart complex is functorial in the
  complex.** The derived pullback of an isomorphism `L ≅ K` to the chart of an affine open `V`,
  carried across the derived sheafification equivalence of [Stacks, Tag 06Z0].

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartComplexIso_refl` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartComplexIso_trans`: that functoriality — the identity
  goes to the identity and a composite to the composite.
* `AlgebraicGeometry.DeterminantTwoTerm.tildeChartComplexIso_natural` and
  `AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso_natural`: the two structural
  comparisons behind the chart-restriction comparison are natural in the complex, the first being
  the naturality of the counit of [Stacks, Tag 06Z0] and the second that of the composition
  isomorphism of [Stacks, Tag 0D5S].
* `AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso_natural`: **the
  chart-restriction comparison is natural in the complex.**
* `TwoTermDeterminant.detBaseChangeIso_natural`: the ring-level shape of the chart comparison of
  determinants is natural in the complex, given the naturality of the identification of the
  complexes.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso_natural`: **the chart comparison of
  determinants over the rings is natural in the complex.**

## Implementation notes

*The spelling obstruction.* Two obstructions of the kind described in the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeterminantTwoTermChartGlue.lean` occur here. First,
`AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso` is built from
`Stacks.DerivedPullback.schemeFactorIso`, a statement about ringed spaces, so its derived pullback
is spelled `derivedPullback (Spec ρ).toLRSHom.toShHom` with the derived categories in the
`SheafOfModules (structureSheafRing _)` form, while
`AlgebraicGeometry.DeterminantTwoTerm.mapDerivedCategory_map_sourceComplexRestrictionIso` spells
the same functor `AlgebraicGeometry.StandardModel.specDerivedPullback`, in the `Scheme.Modules`
form. Second, the target of
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso` is a value of
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars` while
`TwoTermDeterminant.PerfectTwoTermComplex.baseChangeIso` is an isomorphism of values of
`TwoTermDeterminant.PerfectTwoTermComplex.baseChange`. Both pairs are definitionally equal but not
syntactically equal, so a goal mixing them is type-correct only at default transparency and `rw`
and `simp` refuse to fire on it.

What fixes it: every chase is run in a `private` lemma —
`AlgebraicGeometry.DeterminantTwoTerm.naturalChase` for the four naturality squares and
`TwoTermDeterminant.transSymmEqSymmTrans` for the one inversion — in which every category,
functor, object and morphism is a variable, so that `rw` and `simp` only ever meet one spelling;
the concrete inputs are handed to it and the defeq slack is absorbed by the plain definitional
check of `exact`. `AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso_natural` is stated in
the `AlgebraicGeometry.StandardModel.specDerivedPullback` spelling and proved by the naturality of
`AlgebraicGeometry.DeterminantTwoTerm.chartFactorIso`, which is in the other one; writing the type
out is what retypes the term. For the same reason `rw [Functor.map_comp]` at top level is replaced
by `AlgebraicGeometry.DeterminantTwoTerm.mapCompTwo`, and inside the chase `Functor.map_comp` is
written `CategoryTheory.Functor.map_comp`, the unqualified name resolving to the `Monad` lemma.

*Functoriality is read off a composite of three functors.* `chartComplexIso` is the derived
pullback of `a` promoted to the source category by `CategoryTheory.ObjectProperty.isoMk` and then
carried by the inverse of `AlgebraicGeometry.DeterminantTwoTerm.tildeSourceEquivalence` and by the
inclusion of the ring-level source category. Promotion along `isoMk` preserves identities and
composites definitionally, the morphisms of a full subcategory being those of the ambient
category, so both functoriality statements are three applications of `CategoryTheory.Functor.`
`mapIso_refl` and `CategoryTheory.Functor.mapIso_trans`, again on variables.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open AlgebraicGeometry.StandardModel (specDerivedPullback)
open scoped TensorProduct

universe u

namespace TwoTermDeterminant

attribute [local instance 10000] HasDerivedCategory.standard

/-- Transposing a square of isomorphisms: if `e.hom ≫ g = f ≫ e'.hom` then
`g ≫ e'.inv = e.inv ≫ f`. -/
private theorem comp_inv_eq_inv_comp_of_hom_comp {C : Type*} [Category C] {p q r s : C}
    (e : p ≅ q) (e' : r ≅ s) (f : p ⟶ r) (g : q ⟶ s) (h : e.hom ≫ g = f ≫ e'.hom) :
    g ≫ e'.inv = e.inv ≫ f := by
  rw [eq_comm, Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **Transposing a naturality square into the two inverse directions.** If `eL.hom ≫ t.hom` is
`cV.hom ≫ eK.hom`, then reading `eL` and `eK` backwards turns `t` followed by `eK` inverted into
`eL` inverted followed by `cV`. Every object and morphism is a variable, so that the composite is
never written at two spellings of one category. -/
private theorem transSymmEqSymmTrans {C : Type*} [Category C] {p q r s : C}
    (eL : p ≅ q) (cV : p ≅ r) (eK : r ≅ s) (t : q ≅ s)
    (hn : eL.hom ≫ t.hom = cV.hom ≫ eK.hom) :
    t ≪≫ eK.symm = eL.symm ≪≫ cV :=
  Iso.ext (comp_inv_eq_inv_comp_of_hom_comp eL eK cV.hom t.hom hn)

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A]

/-- **The shape of the chart comparison of determinants over the rings is natural in the
complex.** Let `φ : R →+* A` be flat, let `K₁` and `K₂` be perfect objects of `D(R)` of
Tor-amplitude in `[-1, 0]` and `K₁'`, `K₂'` perfect objects of `D(A)` of Tor-amplitude in
`[-1, 0]`, identified by `e₁` and `e₂` with the derived extensions of scalars of `K₁` and `K₂`.
An isomorphism `c : K₁ ≅ K₂` upstairs and an isomorphism `c' : K₁' ≅ K₂'` downstairs that is
compatible with it through `e₁` and `e₂` then make the comparisons
`TwoTermDeterminant.detBaseChangeIso` for `K₁` and for `K₂` into a commuting square with the
determinant of `c`, base changed, and the determinant of `c'`.

The base-change half of the comparison is natural by
`TwoTermDeterminant.detBaseChange_detIsoEquiv`, the determinant of an isomorphism commuting with
flat base change; the remaining half is the determinant of the identity
`TwoTermDeterminant.transSymmEqSymmTrans` of isomorphisms, read through
`TwoTermDeterminant.detIsoEquiv_trans`. -/
theorem detBaseChangeIso_natural (φ : R →+* A)
    (hφ : letI : Algebra R A := φ.toAlgebra; Module.Flat R A)
    (K₁ K₂ : PerfectTwoTermComplex R) (K₁' K₂' : PerfectTwoTermComplex A)
    (e₁ : K₁'.obj ≅ (PerfectTwoTermComplex.baseChange φ K₁).obj)
    (e₂ : K₂'.obj ≅ (PerfectTwoTermComplex.baseChange φ K₂).obj)
    (c : K₁.obj ≅ K₂.obj) (c' : K₁'.obj ≅ K₂'.obj)
    (hc : c'.hom ≫ e₂.hom = e₁.hom ≫ (PerfectTwoTermComplex.baseChangeIso φ c).hom) :
    letI : Algebra R A := φ.toAlgebra
    haveI : Module.Flat R A := hφ
    (detBaseChangeIso φ hφ K₂ K₂' e₂).toLinearMap ∘ₗ
        LinearMap.baseChange A (detIsoEquiv c).toLinearMap =
      (detIsoEquiv c').toLinearMap ∘ₗ (detBaseChangeIso φ hφ K₁ K₁' e₁).toLinearMap := by
  let : Algebra R A := φ.toAlgebra
  have : Module.Flat R A := hφ
  have hiso : PerfectTwoTermComplex.baseChangeIso φ c ≪≫ e₂.symm = e₁.symm ≪≫ c' :=
    transSymmEqSymmTrans e₁ c' e₂ (PerfectTwoTermComplex.baseChangeIso φ c) hc.symm
  refine LinearMap.ext fun t => ?_
  have hbase := LinearMap.congr_fun (detBaseChange_detIsoEquiv φ hφ c) t
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hbase
  show detIsoEquiv e₂.symm
      (detBaseChange φ hφ K₂ (LinearMap.baseChange A (detIsoEquiv c).toLinearMap t)) =
    detIsoEquiv c' (detIsoEquiv e₁.symm (detBaseChange φ hφ K₁ t))
  rw [← hbase, ← LinearEquiv.trans_apply, ← detIsoEquiv_trans, hiso, detIsoEquiv_trans,
    LinearEquiv.trans_apply]

end TwoTermDeterminant

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

open TwoTermDeterminant

variable {X : Scheme.{u}}

/-! ### The chart complex is functorial in the complex -/

/-- Promotion of the identity to a full subcategory is the identity. -/
private theorem isoMk_refl {C : Type*} [Category C] (P : ObjectProperty C) (x : C) (hx : P x) :
    ObjectProperty.isoMk P (Iso.refl x) = Iso.refl (⟨x, hx⟩ : P.FullSubcategory) :=
  rfl

/-- Promotion of a composite to a full subcategory is the composite of the promotions. -/
private theorem isoMk_trans {C : Type*} [Category C] (P : ObjectProperty C) {x y z : C}
    (hx : P x) (hy : P y) (hz : P z) (i : x ≅ y) (j : y ≅ z) :
    (ObjectProperty.isoMk P (i ≪≫ j) : (⟨x, hx⟩ : P.FullSubcategory) ≅ ⟨z, hz⟩) =
      (ObjectProperty.isoMk P i : (⟨x, hx⟩ : P.FullSubcategory) ≅ ⟨y, hy⟩) ≪≫
        ObjectProperty.isoMk P j :=
  rfl

/-- **The identity, pushed through a functor, promoted to a full subcategory and pushed through
two more functors, is the identity.** Every category, functor and object is a variable, so the
three applications of `CategoryTheory.Functor.mapIso_refl` meet a single spelling. -/
private theorem liftIso_refl {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] (G : C ⥤ D) (P : ObjectProperty D) (H : P.FullSubcategory ⥤ E) (I : E ⥤ F)
    (x : C) (hx : P (G.obj x)) :
    I.mapIso (H.mapIso (ObjectProperty.isoMk P (G.mapIso (Iso.refl x)) :
        (⟨G.obj x, hx⟩ : P.FullSubcategory) ≅ ⟨G.obj x, hx⟩)) =
      Iso.refl (I.obj (H.obj ⟨G.obj x, hx⟩)) := by
  rw [Functor.mapIso_refl, isoMk_refl, Functor.mapIso_refl, Functor.mapIso_refl]

/-- **A composite, pushed through a functor, promoted to a full subcategory and pushed through two
more functors, is the composite of the images.** The variable-only companion of
`AlgebraicGeometry.DeterminantTwoTerm.liftIso_refl`. -/
private theorem liftIso_trans {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] (G : C ⥤ D) (P : ObjectProperty D) (H : P.FullSubcategory ⥤ E) (I : E ⥤ F)
    {x y z : C} (hx : P (G.obj x)) (hy : P (G.obj y)) (hz : P (G.obj z))
    (i : x ≅ y) (j : y ≅ z) :
    I.mapIso (H.mapIso (ObjectProperty.isoMk P (G.mapIso (i ≪≫ j)) :
        (⟨G.obj x, hx⟩ : P.FullSubcategory) ≅ ⟨G.obj z, hz⟩)) =
      I.mapIso (H.mapIso (ObjectProperty.isoMk P (G.mapIso i) :
          (⟨G.obj x, hx⟩ : P.FullSubcategory) ≅ ⟨G.obj y, hy⟩)) ≪≫
        I.mapIso (H.mapIso (ObjectProperty.isoMk P (G.mapIso j) :
          (⟨G.obj y, hy⟩ : P.FullSubcategory) ≅ ⟨G.obj z, hz⟩)) := by
  rw [Functor.mapIso_trans, isoMk_trans (hy := hy), Functor.mapIso_trans, Functor.mapIso_trans]

/-- **The chart complex of a two-term perfect object is functorial in the object.** For an
isomorphism `a : L ≅ K` of perfect objects of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and an affine
open `V` of `X`, the derived restriction of `a` to the chart of `V`, read through the derived
sheafification equivalence of [Stacks, Tag 06Z0] as an isomorphism of the complexes of
`Γ(X, V)`-modules the two objects correspond to.

The derived pullback of `a` along the chart is an isomorphism of the source category there by
`AlgebraicGeometry.DeterminantTwoTerm.isPerfectTwoTermAmplitude_derivedPullback`, the morphisms of
a full subcategory being those of the ambient category, and
`AlgebraicGeometry.DeterminantTwoTerm.tildeSourceEquivalence` carries it to the ring level. -/
def chartComplexIso {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj) (V : X.affineOpens) :
    (chartComplex L V).obj ≅ (chartComplex K V).obj :=
  let e : chartObj L V ≅ chartObj K V :=
    ObjectProperty.isoMk _ ((derivedPullback V.2.fromSpec.toLRSHom.toShHom).mapIso a)
  (perfectTwoTermComplexProperty Γ(X, (V.1 : X.Opens))).ι.mapIso
    ((tildeSourceEquivalence Γ(X, (V.1 : X.Opens))).inverse.mapIso e)

/-- **The chart complex of the identity isomorphism is the identity.** -/
theorem chartComplexIso_refl (L : PerfectTwoTermAmplitude X) (V : X.affineOpens) :
    chartComplexIso (Iso.refl L.obj) V = Iso.refl _ :=
  liftIso_refl (derivedPullback V.2.fromSpec.toLRSHom.toShHom)
    (IsPerfectTwoTermAmplitude (Spec Γ(X, (V.1 : X.Opens))))
    (tildeSourceEquivalence Γ(X, (V.1 : X.Opens))).inverse
    (perfectTwoTermComplexProperty Γ(X, (V.1 : X.Opens))).ι
    L.obj (derivedPullbackObj V.2.fromSpec L).property

/-- **The chart complex of a composite of isomorphisms is the composite of the chart
complexes.** -/
theorem chartComplexIso_trans {L K M : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj)
    (b : K.obj ≅ M.obj) (V : X.affineOpens) :
    chartComplexIso (a ≪≫ b) V = chartComplexIso a V ≪≫ chartComplexIso b V :=
  liftIso_trans (derivedPullback V.2.fromSpec.toLRSHom.toShHom)
    (IsPerfectTwoTermAmplitude (Spec Γ(X, (V.1 : X.Opens))))
    (tildeSourceEquivalence Γ(X, (V.1 : X.Opens))).inverse
    (perfectTwoTermComplexProperty Γ(X, (V.1 : X.Opens))).ι
    (derivedPullbackObj V.2.fromSpec L).property
    (derivedPullbackObj V.2.fromSpec K).property
    (derivedPullbackObj V.2.fromSpec M).property a b

/-! ### The structural comparisons are natural in the complex -/

/-- **The sheafified chart complex is natural in the complex.** For an affine open `V` of `X` and
an isomorphism `a : L ≅ K`, derived sheafification of
`AlgebraicGeometry.DeterminantTwoTerm.chartComplexIso` is the derived restriction of `a` to the
chart of `V`, read through
`AlgebraicGeometry.DeterminantTwoTerm.tildeChartComplexIso` at the two ends.

This is the naturality of the counit of the affine derived equivalence of [Stacks, Tag 06Z0],
pushed into the derived category by the inclusion of the source category; the inclusion of a full
subcategory sends a composite to the composite definitionally, so no splitting step is needed. -/
theorem tildeChartComplexIso_natural {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj)
    (V : X.affineOpens) :
    (tilde.functor Γ(X, (V.1 : X.Opens))).mapDerivedCategory.map (chartComplexIso a V).hom ≫
        (tildeChartComplexIso V.2 K).hom =
      (tildeChartComplexIso V.2 L).hom ≫
        (derivedPullback V.2.fromSpec.toLRSHom.toShHom).map a.hom :=
  let e : chartObj L V ≅ chartObj K V :=
    ObjectProperty.isoMk _ ((derivedPullback V.2.fromSpec.toLRSHom.toShHom).mapIso a)
  (IsPerfectTwoTermAmplitude (Spec Γ(X, (V.1 : X.Opens)))).ι.congr_map
    ((tildeSourceEquivalence Γ(X, (V.1 : X.Opens))).counitIso.hom.naturality e.hom)

/-- **The factorisation of the restriction to a chart through a larger chart is natural in the
complex.** For affine opens `V ≤ W` of `X`,
`AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso` is a component of the inverse of the
natural isomorphism `AlgebraicGeometry.DeterminantTwoTerm.chartFactorIso`, so it is natural in the
object of `D(𝒪_X)`.

The statement is written in the `AlgebraicGeometry.StandardModel.specDerivedPullback` spelling of
derived pullback along `Spec ρ`, which is the one
`AlgebraicGeometry.DeterminantTwoTerm.mapDerivedCategory_map_sourceComplexRestrictionIso` uses,
while the naturality discharging it is in the ringed-space spelling; the two are definitionally
equal and writing the type out is what retypes the term. -/
theorem chartPullbackObjIso_natural {V W : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen W)
    (h : V ≤ W) {K K' : DerivedCategory X.Modules} (a : K ⟶ K') :
    (chartPullbackObjIso hV hW h K).hom ≫
        (specDerivedPullback (chartRestriction X h)).map
          ((derivedPullback hW.fromSpec.toLRSHom.toShHom).map a) =
      (derivedPullback hV.fromSpec.toLRSHom.toShHom).map a ≫
        (chartPullbackObjIso hV hW h K').hom :=
  ((chartFactorIso hV hW h).inv.naturality a).symm

/-! ### The chart-restriction comparison is natural in the complex -/

/-- A functor applied to a two-fold composite. Isolated so that the splitting happens on
variables, `rw [Functor.map_comp]` being liable to fail at top level on a goal that mixes two
spellings of one category. -/
private theorem mapCompTwo {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {p q r : C}
    (f : p ⟶ q) (g : q ⟶ r) : G.map (f ≫ g) = G.map f ≫ G.map g :=
  G.map_comp f g

/-- **The associativity chase behind
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso_natural`,** with every category,
functor, object and morphism a variable.

Read `Dg` as derived pullback along the comparison map of the two charts, `m₀` and `n₁` as the
derived sheafifications of the chart-restriction comparisons at the two complexes, `m₁` as the
derived sheafification of the derived extension of scalars of the comparison upstairs, `n₀` as the
derived sheafification of the comparison downstairs, `aVL` and `aVK` as the identifications of a
sheafified chart complex with a restriction of the complex, `PVL` and `PVK` as the factorisations
of a restriction through the larger chart, `aWL` and `aWK` as the same identifications over the
larger chart, and `cgL`, `cgiL`, `cgK` as components of the affine comparison square.

The chase is: the pair `cgL`, `cgiL` cancels, `hC` moves the isomorphism of the complexes past the
identifications over the larger chart under `Dg`, `hB` moves it past the factorisations, and `hA`
moves it past the identifications over the smaller chart. -/
private theorem naturalChase {F D : Type*} [Category F] [Category D] (Dg : F ⥤ D)
    {x₀ x₀' x₁ x₁' d₀ d₁ : D} {b₁ b₁' b₂ b₂' : F}
    {aVL : x₀ ⟶ x₁} {aVK : x₀' ⟶ x₁'}
    {PVL : x₁ ⟶ Dg.obj b₁} {PVK : x₁' ⟶ Dg.obj b₁'}
    {aWL : b₂ ≅ b₁} {aWK : b₂' ≅ b₁'}
    {w : b₂ ⟶ b₂'} {v : b₁ ⟶ b₁'} {u : x₁ ⟶ x₁'}
    {cgL : Dg.obj b₂ ⟶ d₀} {cgiL : d₀ ⟶ Dg.obj b₂} {cgK : Dg.obj b₂' ⟶ d₁}
    {m₀ : x₀ ⟶ d₀} {m₁ : d₀ ⟶ d₁} {n₀ : x₀ ⟶ x₀'} {n₁ : x₀' ⟶ d₁}
    (hm₀ : m₀ = aVL ≫ PVL ≫ Dg.map aWL.inv ≫ cgL)
    (hm₁ : m₁ = cgiL ≫ Dg.map w ≫ cgK)
    (hn₁ : n₁ = aVK ≫ PVK ≫ Dg.map aWK.inv ≫ cgK)
    (hA : n₀ ≫ aVK = aVL ≫ u)
    (hB : PVL ≫ Dg.map v = u ≫ PVK)
    (hC : w ≫ aWK.hom = aWL.hom ≫ v)
    (hD : cgL ≫ cgiL = 𝟙 (Dg.obj b₂)) :
    m₀ ≫ m₁ = n₀ ≫ n₁ := by
  subst hm₀
  subst hm₁
  subst hn₁
  have hC' : aWL.inv ≫ w = v ≫ aWK.inv :=
    (comp_inv_eq_inv_comp_of_hom_comp aWL aWK w v hC.symm).symm
  have hDg : Dg.map aWL.inv ≫ Dg.map w = Dg.map v ≫ Dg.map aWK.inv := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hC']
  simp only [Category.assoc, reassoc_of% hD]
  rw [reassoc_of% hDg, reassoc_of% hB, ← reassoc_of% hA]

/-- **The chart-restriction comparison is natural in the complex.** Let `X` be a scheme, `V ≤ W`
affine opens of `X` and `a : L ≅ K` an isomorphism of perfect objects of `D(𝒪_X)` of Tor-amplitude
in `[-1, 0]`. The identification
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso` of the chart complex of `V`
with the derived extension of scalars of the chart complex of `W` carries
`AlgebraicGeometry.DeterminantTwoTerm.chartComplexIso` at `V` to the derived extension of scalars
of `AlgebraicGeometry.DeterminantTwoTerm.chartComplexIso` at `W`.

Both sides are morphisms between complexes of associated sheaves, so derived sheafification,
fully faithful by [Stacks, Tag 06Z0], reduces the identity to an identity in
`D(𝒪_{Spec Γ(X, V)})`. There
`AlgebraicGeometry.DeterminantTwoTerm.mapDerivedCategory_map_sourceComplexRestrictionIso` expands
the two comparisons and
`AlgebraicGeometry.DeterminantTwoTerm.mapDerivedCategory_map_totalDerivedExtensionScalars_map`
expands the derived extension of scalars, so the identity becomes the chase
`AlgebraicGeometry.DeterminantTwoTerm.naturalChase` on four naturality squares: the two
identifications of `AlgebraicGeometry.DeterminantTwoTerm.tildeChartComplexIso_natural`, the
factorisation of `AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso_natural`, and the
affine comparison square of [Stacks, Tag 08DW] part (2), which cancels. -/
theorem sourceComplexRestrictionIso_natural {L K : PerfectTwoTermAmplitude X}
    (a : L.obj ≅ K.obj) {V W : X.affineOpens} (h : V ≤ W) :
    (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) L).hom ≫
        (totalDerivedExtensionScalars.{u, u, u} (affineRestriction X h).hom).functor.map
          (chartComplexIso a W).hom =
      (chartComplexIso a V).hom ≫
        (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) K).hom := by
  refine (AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful
    Γ(X, (V.1 : X.Opens))).map_injective ?_
  refine (mapCompTwo (tilde.functor Γ(X, (V.1 : X.Opens))).mapDerivedCategory _ _).trans
    (Eq.trans ?_
      (mapCompTwo (tilde.functor Γ(X, (V.1 : X.Opens))).mapDerivedCategory _ _).symm)
  exact naturalChase (specDerivedPullback (affineRestriction X h))
    (mapDerivedCategory_map_sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) L)
    (mapDerivedCategory_map_totalDerivedExtensionScalars_map (affineRestriction X h)
      (chartComplexIso a W).hom)
    (mapDerivedCategory_map_sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) K)
    (tildeChartComplexIso_natural a V)
    (chartPullbackObjIso_natural V.2 W.2 (AffineOpensGlue.coe_le_coe h) a.hom)
    (tildeChartComplexIso_natural a W)
    ((AlgebraicGeometry.StandardModel.affinePullbackComparison Γ(X, (W.1 : X.Opens))
      Γ(X, (V.1 : X.Opens)) (affineRestriction X h)).hom_inv_id_app
        (chartComplex L W).obj)

/-! ### The chart comparison of determinants is natural in the complex -/

/-- **The chart comparison of the determinant over the rings is natural in the complex.** Let `X`
be a scheme, `V ≤ W` affine opens of `X` and `a : L ≅ K` an isomorphism of perfect objects of
`D(𝒪_X)` of Tor-amplitude in `[-1, 0]`. The base change along the restriction of functions
`ρ : Γ(X, W) ⟶ Γ(X, V)` of the determinant of the restriction of `a` to the chart of `W`,
followed by the chart comparison for `K`, is the chart comparison for `L` followed by the
determinant of the restriction of `a` to the chart of `V`.

This is `TwoTermDeterminant.detBaseChangeIso_natural` at the restriction of functions, whose
compatibility hypothesis on the identifications of the chart complexes is
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso_natural`. -/
theorem chartDetModuleIso_natural {L K : PerfectTwoTermAmplitude X} (a : L.obj ≅ K.obj)
    {V W : X.affineOpens} (h : V ≤ W) :
    letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
      (affineRestriction X h).hom.toAlgebra
    haveI : Module.Flat Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
      V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h)
    (chartDetModuleIso K h).toLinearMap ∘ₗ
        LinearMap.baseChange Γ(X, (V.1 : X.Opens))
          (detLinearEquivOfIso (chartComplexIso a W)).toLinearMap =
      (detLinearEquivOfIso (chartComplexIso a V)).toLinearMap ∘ₗ
        (chartDetModuleIso L h).toLinearMap :=
  detBaseChangeIso_natural (affineRestriction X h).hom
    (V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h))
    (chartComplex L W) (chartComplex K W) (chartComplex L V) (chartComplex K V)
    (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) L)
    (sourceComplexRestrictionIso V.2 W.2 (AffineOpensGlue.coe_le_coe h) K)
    (chartComplexIso a W) (chartComplexIso a V)
    (sourceComplexRestrictionIso_natural a h).symm

end AlgebraicGeometry.DeterminantTwoTerm

end
