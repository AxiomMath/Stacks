module

public import StacksFrontier.AlgebraicGeometry.AffinePullbackComparisonComp
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartCocycle
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackCoherence

/-!
# The chart cocycle of the chart complex of a two-term perfect complex

Let `X` be a scheme, `L` a perfect object of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and
`V ≤ V' ≤ W` affine opens of `X`. The chart comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` of determinants over the rings is
`TwoTermDeterminant.detBaseChangeIso` at the restriction of functions `Γ(X, W) ⟶ Γ(X, V)` and at
the identification `AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso` of the chart
complex of `V` with the derived extension of scalars of the chart complex of `W`, so by
`TwoTermDeterminant.detBaseChangeIso_trans` its cocycle condition along a chain of two inclusions
reduces to the cocycle condition for that family of identifications.

This file proves that cocycle condition, `sourceComplexRestrictionIso_trans`, together with the
inputs it needs: the composition compatibility of the affine comparison square of
[Stacks, Tag 08DW] part (2) read along a *factorisation* `f ≫ g = k` of ring maps rather than at a
composite, which is the form an inclusion of affine opens produces, and the description of the
chart-restriction comparison after derived sheafification, under which the cocycle is checked.

## Main definitions

* `AlgebraicGeometry.DeterminantTwoTerm.specDerivedPullbackCompOf` and
  `AlgebraicGeometry.DeterminantTwoTerm.totalDerivedExtensionScalarsCompOf`: the composition
  isomorphisms of [Stacks, Tag 0D5S] for derived pullback along `Spec` and of [Stacks, Tag 06Y5]
  for derived extension of scalars, attached to a factorisation `f ≫ g = k` of ring maps rather
  than to the composite itself.
* `AlgebraicGeometry.DeterminantTwoTerm.tildeChartComplexIso`: the sheafified chart complex of an
  affine open is the restriction of `L` to its chart.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso_trans`: **the chart-restriction
  comparison is transitive**, which is the cocycle condition the chart comparison of determinants
  reduces to.
* `totalDerivedExtensionScalarsCompOf_app_eq_baseChangeCompIsoOf`: the transport of the
  composition isomorphism of derived extension of scalars along an equality of morphisms of
  `CommRingCat` agrees, at a perfect two-term object, with
  `TwoTermDeterminant.baseChangeCompIsoOf`.
* `AlgebraicGeometry.DeterminantTwoTerm.StandardModel.affinePullbackComparison_comp_of_eq`:
  **the composition compatibility of the affine comparison square of [Stacks, Tag 08DW] part (2),
  read along a factorisation.**
* `AlgebraicGeometry.DeterminantTwoTerm.mapDerivedCategory_map_totalDerivedExtensionScalars_map`:
  derived sheafification of a derived extension of scalars is the derived pullback along `Spec ρ`
  of the derived sheafification, conjugated by the affine comparison square.
* `AlgebraicGeometry.DeterminantTwoTerm.mapDerivedCategory_map_sourceComplexRestrictionIso`:
  **the chart-restriction comparison, after derived sheafification**, is the two identifications of
  the chart complexes, the factorisation
  `AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso` of the restriction to the smaller
  chart through the larger one, and the affine comparison square.

## Implementation notes

The ring map attached to an inclusion `V ≤ W` of affine opens is the restriction of functions
`Γ(X, W) ⟶ Γ(X, V)`, and the one attached to `V ≤ W` is only *propositionally* the composite of
those attached to `V ≤ V'` and `V' ≤ W`, restriction of functions being a functor. Every
composition isomorphism is therefore taken in the form indexed by a factorisation `f ≫ g = k`,
which is what `TwoTermDeterminant.baseChangeCompIsoOf` and `Stacks.DerivedPullback.schemeFactorIso`
already do; `specDerivedPullbackCompOf` and `totalDerivedExtensionScalarsCompOf` supply the same
for the two composition isomorphisms used here, and
`totalDerivedExtensionScalarsCompOf_app_eq_baseChangeCompIsoOf` identifies the two transports of
the second.

Both composition isomorphisms are also *ascribed*: `Stacks.DerivedPullback.schemeFactorIso` is a
statement about ringed spaces, so its derived categories are spelled
`SheafOfModules (structureSheafRing _)` while the determinant development spells them
`Scheme.Modules`. The two are equal but carry different `CategoryTheory.Category` and
`CategoryTheory.Abelian` instances, so a composite written both ways is not type-correct at the
transparency `simp` and `rw` check their results at. Ascribing each functor once, as
`AlgebraicGeometry.StandardModel.specDerivedPullback` does for derived pullback, keeps every
statement below at one spelling.

`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso` is the preimage, under the fully
faithful derived sheafification of [Stacks, Tag 06Z0], of a four-fold composite, and
`mapDerivedCategory_map_sourceComplexRestrictionIso` names that composite: it holds by
`CategoryTheory.Functor.FullyFaithful.map_preimage`, and it is stated right-associated because the
composite inside the preimage is.

The cocycle condition is therefore an identity between two composites in
`D(𝒪_{Spec Γ(X, V)})`, and one of them mixes the two spellings above. The chase is run on
`glueChase`, where every category, functor, object and morphism is a variable, so that `simp` and
`rw` only ever see a goal at a single spelling; `map_comp_three`, `comp_map_comp_congr` and
`map_congr` play the same role for the three steps that have to happen at the concrete terms.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Section 15.124 (Tag 0FJI)](https://stacks.math.columbia.edu/tag/0FJI)
* [Stacks Project, Lemma 15.124.4 (Tag 0FJM)](https://stacks.math.columbia.edu/tag/0FJM)
* [Stacks Project, Section 6.33 (Tag 00AM)](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Lemma 36.9.2 (Tag 08DW)](https://stacks.math.columbia.edu/tag/08DW)
-/

@[expose] public noncomputable section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback (schemeFactorIso)
open AlgebraicGeometry.StandardModel (specDerivedPullback)

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The composition isomorphisms along a factorisation -/

/-- **The composition isomorphism of [Stacks, Tag 0D5S] along a factorisation.** For ring maps
`f : R ⟶ S`, `g : S ⟶ T` and `k : R ⟶ T` whose spectra factor as
`Spec g ≫ Spec f = Spec k`, derived pullback along `Spec f` followed by derived pullback along
`Spec g` is derived pullback along `Spec k`. -/
def specDerivedPullbackCompOf {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T)
    (hs : Spec.map g ≫ Spec.map f = Spec.map k) :
    specDerivedPullback f ⋙ specDerivedPullback g ≅ specDerivedPullback k :=
  schemeFactorIso (Spec.map g) (Spec.map f) (Spec.map k) hs

/-- **The composition isomorphism of derived extension of scalars along a factorisation.** For
ring maps `f : R ⟶ S`, `g : S ⟶ T` and `k : R ⟶ T` with `f ≫ g = k`, extending scalars along `f`
and then along `g` is extending scalars along `k`. This is
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp`, transported along the
factorisation. -/
def totalDerivedExtensionScalarsCompOf {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (k : R ⟶ T) (hk : f ≫ g = k) :
    (totalDerivedExtensionScalars.{u, u, u} f.hom).functor ⋙
        (totalDerivedExtensionScalars.{u, u, u} g.hom).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} k.hom).functor := by
  subst hk
  exact totalDerivedExtensionScalarsComp.{u, u} f.hom g.hom

/-- **The two transports of the composition isomorphism of derived extension of scalars agree.**
`TwoTermDeterminant.baseChangeCompIsoOf` transports it along an equality of ring homomorphisms and
`AlgebraicGeometry.DeterminantTwoTerm.totalDerivedExtensionScalarsCompOf` along the underlying
equality of morphisms of `CommRingCat`; at a perfect two-term object the two agree. -/
theorem totalDerivedExtensionScalarsCompOf_app_eq_baseChangeCompIsoOf {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T) (hk : f ≫ g = k)
    (K : TwoTermDeterminant.PerfectTwoTermComplex R) :
    (totalDerivedExtensionScalarsCompOf f g k hk).hom.app K.obj =
      (TwoTermDeterminant.baseChangeCompIsoOf f.hom g.hom k.hom
        (congrArg CommRingCat.Hom.hom hk) K).hom := by
  subst hk
  rfl

/-- **The affine comparison square of [Stacks, Tag 08DW] part (2) composes along a
factorisation.** For ring maps `f : R ⟶ S`, `g : S ⟶ T` and `k : R ⟶ T` with `f ≫ g = k`, the
comparison for `k` at an object of `D(R)` is the comparison for `f` pushed along `Lg^*`, followed
by the comparison for `g`, read through the composition isomorphisms
`AlgebraicGeometry.DeterminantTwoTerm.specDerivedPullbackCompOf` and
`AlgebraicGeometry.DeterminantTwoTerm.totalDerivedExtensionScalarsCompOf` at the factorisation.

This is `AlgebraicGeometry.affinePullbackComparison_comp`, which is the case `k = f ≫ g`. -/
theorem StandardModel.affinePullbackComparison_comp_of_eq {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (k : R ⟶ T) (hk : f ≫ g = k)
    (hs : Spec.map g ≫ Spec.map f = Spec.map k)
    (Y : DerivedCategory (ModuleCat.{u} R)) :
    (AlgebraicGeometry.StandardModel.affinePullbackComparison R T k).hom.app Y =
      (specDerivedPullbackCompOf f g k hs).inv.app
          ((tilde.functor R).mapDerivedCategory.obj Y) ≫
        (specDerivedPullback g).map
          ((AlgebraicGeometry.StandardModel.affinePullbackComparison R S f).hom.app Y) ≫
        (AlgebraicGeometry.StandardModel.affinePullbackComparison S T g).hom.app
          ((totalDerivedExtensionScalars.{u, u, u} f.hom).functor.obj Y) ≫
        (tilde.functor T).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsCompOf f g k hk).hom.app Y) := by
  subst hk
  exact affinePullbackComparison_comp R S T f g Y

/-- **Derived sheafification of a derived extension of scalars is a conjugate of a derived
pullback.** For a ring map `ρ : A ⟶ B` and a morphism of `D(A)`, derived sheafification over `B`
of the derived extension of scalars of that morphism is, conjugated by the affine comparison
square of [Stacks, Tag 08DW] part (2), the derived pullback along `Spec ρ` of its derived
sheafification over `A`. This is the naturality of that square. -/
theorem mapDerivedCategory_map_totalDerivedExtensionScalars_map {A B : CommRingCat.{u}}
    (ρ : A ⟶ B) {K K' : DerivedCategory (ModuleCat.{u} A)} (x : K ⟶ K') :
    (tilde.functor B).mapDerivedCategory.map
        ((totalDerivedExtensionScalars.{u, u, u} ρ.hom).functor.map x) =
      (AlgebraicGeometry.StandardModel.affinePullbackComparison A B ρ).inv.app K ≫
        (specDerivedPullback ρ).map ((tilde.functor A).mapDerivedCategory.map x) ≫
        (AlgebraicGeometry.StandardModel.affinePullbackComparison A B ρ).hom.app K' := by
  have hnat := (AlgebraicGeometry.StandardModel.affinePullbackComparison A B ρ).hom.naturality x
  dsimp only [Functor.comp_map] at hnat
  rw [hnat, Iso.inv_hom_id_app_assoc]

/-! ### The chart-restriction comparison after derived sheafification -/

variable {X : Scheme.{u}} {V V' W : X.Opens}

/-- **The sheafified chart complex of an affine open is the restriction of `L` to its chart.**
For an affine open `V` of `X` and `L` a perfect object of `D(𝒪_X)` of Tor amplitude in `[-1, 0]`,
this is the counit `AlgebraicGeometry.DeterminantTwoTerm.tildeSourceComplexIso` of the affine
derived equivalence of [Stacks, Tag 06Z0], read in `D(𝒪_{Spec Γ(X, V)})`. -/
def tildeChartComplexIso (hV : IsAffineOpen V) (L : PerfectTwoTermAmplitude X) :
    (tilde.functor Γ(X, V)).mapDerivedCategory.obj
        (sourceComplex Γ(X, V) (derivedPullbackObj hV.fromSpec L)).obj ≅
      (derivedPullback hV.fromSpec.toLRSHom.toShHom).obj L.obj :=
  (IsPerfectTwoTermAmplitude (Spec Γ(X, V))).ι.mapIso
    (tildeSourceComplexIso Γ(X, V) (derivedPullbackObj hV.fromSpec L))

/-- **The chart-restriction comparison, after derived sheafification.** Derived sheafification of
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso` is the identification of the
sheafified chart complex of `V` with the restriction of `L` there, the factorisation
`AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso` of that restriction through the chart of
`W`, the identification of the restriction of `L` to the chart of `W` with the sheafified chart
complex of `W`, and the affine comparison square of [Stacks, Tag 08DW] part (2); derived
sheafification is fully faithful by [Stacks, Tag 06Z0]. -/
theorem mapDerivedCategory_map_sourceComplexRestrictionIso (hV : IsAffineOpen V)
    (hW : IsAffineOpen W) (h : V ≤ W) (L : PerfectTwoTermAmplitude X) :
    (tilde.functor Γ(X, V)).mapDerivedCategory.map
        (sourceComplexRestrictionIso hV hW h L).hom =
      (tildeChartComplexIso hV L).hom ≫
        (chartPullbackObjIso hV hW h L.obj).hom ≫
        (specDerivedPullback (chartRestriction X h)).map (tildeChartComplexIso hW L).inv ≫
        (AlgebraicGeometry.StandardModel.affinePullbackComparison Γ(X, W) Γ(X, V)
            (chartRestriction X h)).hom.app
          ((sourceComplex Γ(X, W) (derivedPullbackObj hW.fromSpec L)).obj) :=
  (AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful Γ(X, V)).map_preimage _

/-! ### The chart-restriction comparison is transitive -/

/-- A functor applied to an equal pair of morphisms, between two fixed morphisms. Isolated so
that the equality is transported with no rewriting inside a composite. -/
private theorem comp_map_comp_congr {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {p q : C} {a b : D} (u : a ⟶ G.obj p) (v : G.obj q ⟶ b) {m m' : p ⟶ q} (hm : m = m') :
    u ≫ G.map m ≫ v = u ≫ G.map m' ≫ v :=
  congrArg (fun z => u ≫ G.map z ≫ v) hm

/-- A functor applied to an equal pair of morphisms. -/
private theorem map_congr {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {p q : C}
    {m m' : p ⟶ q} (hm : m = m') : G.map m = G.map m' :=
  congrArg (fun z => G.map z) hm

/-- A functor applied to a three-fold composite. Isolated so that the splitting happens on
variables. -/
private theorem map_comp_three {C D : Type*} [Category C] [Category D] (G : C ⥤ D) {p q r s : C}
    (a : p ⟶ q) (b : q ⟶ r) (c : r ⟶ s) :
    G.map (a ≫ b ≫ c) = G.map a ≫ G.map b ≫ G.map c := by
  rw [G.map_comp, G.map_comp]

/-- **The associativity chase behind
`AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso_trans`,** with every category,
functor, object and morphism a variable.

Read `Dk`, `Df` and `Dg` as derived pullback along the charts' comparison maps for `V ≤ W`,
`V' ≤ W` and `V ≤ V'`, the `m`'s as the derived sheafifications of the four morphisms the
statement compares, `σ₁` and `σ₂` as two components of the composition isomorphism `Dk ≅ Df ⋙ Dg`,
`cf`, `cg`, `cg'` and `cgi` as components of the affine comparison squares, and `aW`, `aWi` as the
two directions of the identification of a sheafified chart complex with a restriction of `L`.

The chase is: the pair `cg`, `cgi` cancels, the pair `aWi`, `aW` cancels under `Dg`, `hPV` turns
`P1 ≫ Dg.map P2` into `PV ≫ σ₁`, and the naturality `hσ` of the composition isomorphism moves
`Dk.map w` to the front, which is the shape `hck` expands `ck` into. -/
private theorem glueChase {E F D : Type*} [Category E] [Category F] [Category D]
    (Df : E ⥤ F) (Dg : F ⥤ D) (Dk : E ⥤ D)
    {e₁ e₂ : E} {b₁ b₂ b₃ : F} {x₀ x₁ d₁ d₂ x₄ : D}
    {w : e₁ ⟶ e₂} {aV : x₀ ⟶ x₁} {PV : x₁ ⟶ Dk.obj e₁} {ck : Dk.obj e₂ ⟶ x₄}
    {σ₁ : Dk.obj e₁ ⟶ Dg.obj (Df.obj e₁)} {σ₂ : Dk.obj e₂ ⟶ Dg.obj (Df.obj e₂)}
    {P1 : x₁ ⟶ Dg.obj b₁} {aWi : b₁ ⟶ b₂} {aW : b₂ ⟶ b₁} {P2 : b₁ ⟶ Df.obj e₁}
    {cf : Df.obj e₂ ⟶ b₃} {cg : Dg.obj b₂ ⟶ d₁} {cgi : d₁ ⟶ Dg.obj b₂}
    {cg' : Dg.obj b₃ ⟶ d₂} {τ : d₂ ⟶ x₄}
    {m₀ : x₀ ⟶ x₄} {m₁ : x₀ ⟶ d₁} {m₂ : d₁ ⟶ d₂} {m₃ : d₂ ⟶ x₄}
    (hm₀ : m₀ = aV ≫ PV ≫ Dk.map w ≫ ck)
    (hm₁ : m₁ = aV ≫ P1 ≫ Dg.map aWi ≫ cg)
    (hm₂ : m₂ = cgi ≫ Dg.map (aW ≫ P2 ≫ Df.map w ≫ cf) ≫ cg')
    (hm₃ : m₃ = τ)
    (hσ : Dk.map w ≫ σ₂ = σ₁ ≫ Dg.map (Df.map w))
    (hck : ck = σ₂ ≫ Dg.map cf ≫ cg' ≫ τ)
    (hPV : PV ≫ σ₁ = P1 ≫ Dg.map P2)
    (hcancel : aWi ≫ aW = 𝟙 b₁) (hcg : cg ≫ cgi = 𝟙 (Dg.obj b₂)) :
    m₀ = m₁ ≫ m₂ ≫ m₃ := by
  subst hm₀
  subst hm₁
  subst hm₂
  subst hm₃
  subst hck
  have hcancelg : Dg.map aWi ≫ Dg.map aW = 𝟙 (Dg.obj b₁) := by
    rw [← Functor.map_comp, hcancel, CategoryTheory.Functor.map_id]
  simp only [Functor.map_comp, Category.assoc, reassoc_of% hcg, reassoc_of% hcancelg]
  rw [← reassoc_of% hPV, ← reassoc_of% hσ]

/-- **The chart-restriction comparison is transitive.** Let `X` be a scheme, `L` a perfect object
of `D(𝒪_X)` of Tor amplitude in `[-1, 0]` and `V ≤ V' ≤ W` affine opens of `X`. The
identification `AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso` of the chart
complex of `V` with the derived extension of scalars of the chart complex of `W` is the one for
`V ≤ V'`, followed by the extension of scalars to `Γ(X, V)` of the one for `V' ≤ W`, followed by
the composition isomorphism `TwoTermDeterminant.baseChangeCompIsoOf` of the two extensions of
scalars at the factorisation of the restriction of functions.

Both sides are morphisms between complexes of associated sheaves, so derived sheafification,
fully faithful by [Stacks, Tag 06Z0], reduces the identity to an identity in
`D(𝒪_{Spec Γ(X, V)})`. There
`AlgebraicGeometry.DeterminantTwoTerm.mapDerivedCategory_map_sourceComplexRestrictionIso` expands
each of the three comparisons, so the identity becomes the associativity chase
`AlgebraicGeometry.DeterminantTwoTerm.glueChase` on three inputs: the cocycle
`AlgebraicGeometry.DeterminantTwoTerm.chartPullbackObjIso_trans` of the chart factorisations, the
naturality of the composition isomorphism of [Stacks, Tag 0D5S], and the composition
compatibility
`AlgebraicGeometry.DeterminantTwoTerm.StandardModel.affinePullbackComparison_comp_of_eq` of the
affine comparison square of [Stacks, Tag 08DW] part (2). -/
theorem sourceComplexRestrictionIso_trans (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hW : IsAffineOpen W) (h₁ : V ≤ V') (h₂ : V' ≤ W) (L : PerfectTwoTermAmplitude X) :
    (sourceComplexRestrictionIso hV hW (h₁.trans h₂) L).hom =
      (sourceComplexRestrictionIso hV hV' h₁ L).hom ≫
        (totalDerivedExtensionScalars.{u, u, u} (chartRestriction X h₁).hom).functor.map
          (sourceComplexRestrictionIso hV' hW h₂ L).hom ≫
        (TwoTermDeterminant.baseChangeCompIsoOf (chartRestriction X h₂).hom
            (chartRestriction X h₁).hom (chartRestriction X (h₁.trans h₂)).hom
            (congrArg CommRingCat.Hom.hom (chartRestriction_comp h₁ h₂))
            (sourceComplex Γ(X, W) (derivedPullbackObj hW.fromSpec L))).hom := by
  refine (AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful
    Γ(X, V)).map_injective ?_
  refine Eq.trans ?_
    (map_comp_three (tilde.functor Γ(X, V)).mapDerivedCategory _ _ _).symm
  have hσ : (specDerivedPullback (chartRestriction X (h₁.trans h₂))).map
          (tildeChartComplexIso hW L).inv ≫
        (specDerivedPullbackCompOf (chartRestriction X h₂) (chartRestriction X h₁)
            (chartRestriction X (h₁.trans h₂))
            (specMap_chartRestriction_comp h₁ h₂)).inv.app
          ((tilde.functor Γ(X, W)).mapDerivedCategory.obj
            (sourceComplex Γ(X, W) (derivedPullbackObj hW.fromSpec L)).obj) =
      (specDerivedPullbackCompOf (chartRestriction X h₂) (chartRestriction X h₁)
            (chartRestriction X (h₁.trans h₂))
            (specMap_chartRestriction_comp h₁ h₂)).inv.app
          ((derivedPullback hW.fromSpec.toLRSHom.toShHom).obj L.obj) ≫
        (specDerivedPullback (chartRestriction X h₁)).map
          ((specDerivedPullback (chartRestriction X h₂)).map
            (tildeChartComplexIso hW L).inv) :=
    (specDerivedPullbackCompOf (chartRestriction X h₂) (chartRestriction X h₁)
      (chartRestriction X (h₁.trans h₂))
      (specMap_chartRestriction_comp h₁ h₂)).inv.naturality (tildeChartComplexIso hW L).inv
  have hPV : (chartPullbackObjIso hV hW (h₁.trans h₂) L.obj).hom ≫
        (specDerivedPullbackCompOf (chartRestriction X h₂) (chartRestriction X h₁)
            (chartRestriction X (h₁.trans h₂))
            (specMap_chartRestriction_comp h₁ h₂)).inv.app
          ((derivedPullback hW.fromSpec.toLRSHom.toShHom).obj L.obj) =
      (chartPullbackObjIso hV hV' h₁ L.obj).hom ≫
        (specDerivedPullback (chartRestriction X h₁)).map
          (chartPullbackObjIso hV' hW h₂ L.obj).hom :=
    congrArg Iso.hom (chartPullbackObjIso_trans hV hV' hW h₁ h₂ L.obj)
  exact glueChase (specDerivedPullback (chartRestriction X h₂))
    (specDerivedPullback (chartRestriction X h₁))
    (specDerivedPullback (chartRestriction X (h₁.trans h₂)))
    (mapDerivedCategory_map_sourceComplexRestrictionIso hV hW (h₁.trans h₂) L)
    (mapDerivedCategory_map_sourceComplexRestrictionIso hV hV' h₁ L)
    ((mapDerivedCategory_map_totalDerivedExtensionScalars_map (chartRestriction X h₁)
        (sourceComplexRestrictionIso hV' hW h₂ L).hom).trans
      (comp_map_comp_congr (specDerivedPullback (chartRestriction X h₁)) _ _
        (mapDerivedCategory_map_sourceComplexRestrictionIso hV' hW h₂ L)))
    (map_congr (tilde.functor Γ(X, V)).mapDerivedCategory
      (totalDerivedExtensionScalarsCompOf_app_eq_baseChangeCompIsoOf (chartRestriction X h₂)
        (chartRestriction X h₁) (chartRestriction X (h₁.trans h₂)) (chartRestriction_comp h₁ h₂)
        (sourceComplex Γ(X, W) (derivedPullbackObj hW.fromSpec L))).symm)
    hσ
    (StandardModel.affinePullbackComparison_comp_of_eq (chartRestriction X h₂)
      (chartRestriction X h₁) (chartRestriction X (h₁.trans h₂)) (chartRestriction_comp h₁ h₂)
      (specMap_chartRestriction_comp h₁ h₂)
      (sourceComplex Γ(X, W) (derivedPullbackObj hW.fromSpec L)).obj)
    hPV (tildeChartComplexIso hV' L).inv_hom_id
    ((AlgebraicGeometry.StandardModel.affinePullbackComparison Γ(X, V') Γ(X, V)
      (chartRestriction X h₁)).hom_inv_id_app
        (sourceComplex Γ(X, V') (derivedPullbackObj hV'.fromSpec L)).obj)

/-- **The chart-restriction comparison is transitive, in the uniform derived-extension-of-scalars
spelling.** This is `AlgebraicGeometry.DeterminantTwoTerm.sourceComplexRestrictionIso_trans` with
the last factor written as the composition isomorphism
`AlgebraicGeometry.DeterminantTwoTerm.totalDerivedExtensionScalarsCompOf` of derived extensions of
scalars rather than as `TwoTermDeterminant.baseChangeCompIsoOf`; the two agree by
`totalDerivedExtensionScalarsCompOf_app_eq_baseChangeCompIsoOf`.

In this spelling every object in the composite is a value of `totalDerivedExtensionScalars`, which
is what the chart comparison of determinants on the spectra needs. -/
theorem sourceComplexRestrictionIso_trans' (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (hW : IsAffineOpen W) (h₁ : V ≤ V') (h₂ : V' ≤ W) (L : PerfectTwoTermAmplitude X) :
    (sourceComplexRestrictionIso hV hW (h₁.trans h₂) L).hom =
      (sourceComplexRestrictionIso hV hV' h₁ L).hom ≫
        (totalDerivedExtensionScalars.{u, u, u} (chartRestriction X h₁).hom).functor.map
          (sourceComplexRestrictionIso hV' hW h₂ L).hom ≫
        (totalDerivedExtensionScalarsCompOf (chartRestriction X h₂) (chartRestriction X h₁)
            (chartRestriction X (h₁.trans h₂)) (chartRestriction_comp h₁ h₂)).hom.app
          (sourceComplex Γ(X, W) (derivedPullbackObj hW.fromSpec L)).obj :=
  (sourceComplexRestrictionIso_trans hV hV' hW h₁ h₂ L).trans <| by
    rw [totalDerivedExtensionScalarsCompOf_app_eq_baseChangeCompIsoOf]
    rfl

end AlgebraicGeometry.DeterminantTwoTerm

end
