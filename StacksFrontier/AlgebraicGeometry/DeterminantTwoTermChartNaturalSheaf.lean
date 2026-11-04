module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartDetIso
public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermChartTrans

/-!
# The chart comparison of the determinant is natural in the complex

Let `X` be a scheme, `L` and `K` perfect objects of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]` and
`V ≤ W` affine opens of `X`. A family of linear equivalences of the determinant modules of the
chart complexes, one for each affine open, induces on each chart an isomorphism of the determinants
by `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecOfEquiv` and `chartDetOfEquiv`, while the
chart comparison of
`StacksFrontier/AlgebraicGeometry/DeterminantTwoTermChartComparison.lean` identifies the determinant
on the chart of `V` with the restriction to `V` of the determinant on the chart of `W`. This file
proves that the two commute: **the chart comparison is natural in the complex**, provided the
family is natural over the rings.

The ring-level naturality square is taken as a hypothesis, so the two results below hold for an
arbitrary family of linear equivalences and can be instantiated at any family that satisfies it.

## Main results

* `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso_natural`: **the chart comparison
  on the spectra is natural in the complex**, given the ring-level square.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_natural`: **the chart comparison on
  the open subschemes is natural in the complex**, given the square on the spectra.
* `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso_natural'`: the two chained, so that
  the ring-level square alone implies the square on the open subschemes.

## Implementation notes

The squares are proved on variables (`tildeChase`, `fiveChaseIso`) and only then instantiated. The
obstruction is at the third of the five factors of
`AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso`:
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is `CategoryTheory.eqToIso` of a transported
`rfl`, and `chartDetRestrictIso` uses it in the form `(pullbackCongr h).app M`, whose `hom` is
*definitionally* but not syntactically `CategoryTheory.NatTrans.app (pullbackCongr h).hom M`, which
is the form `CategoryTheory.NatTrans.naturality` produces. Writing that one naturality square out
at the concrete terms — in either spelling — makes the kernel attempt the reconciliation and fail
with `(kernel) deterministic timeout`, and the same happens to any `rfl` that expands the five
factors into their `hom`s. Hence no square is ever stated at the concrete terms: `isoApp_square`
(applied to inverses too) states the naturality square for a *variable* natural isomorphism, where
the reconciliation is a single iota reduction, and the concrete squares are then instances of a
closed lemma, so nothing has to be reduced; `chartDetRestrictIso_eq` keeps the five factors as
isomorphisms rather than as their `hom`s, so its `rfl` is a plain unfolding.

## References

* [Stacks Project, Lemma 36.39.1 (Tag 0FJX)](https://stacks.math.columbia.edu/tag/0FJX)
* [Stacks Project, Lemma 26.7.3 (Tag 01I9)](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory TwoTermDeterminant

universe u

namespace AlgebraicGeometry.DeterminantTwoTerm

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### The comparison on the spectra -/

/-- Given a natural isomorphism `P : tW ⋙ pb ≅ E ⋙ tV` and a commuting square
`E.map ψ ≫ mK = mL ≫ φ`, the square formed by `pb.map (tW.map ψ)`, the composites
`P.hom.app _ ≫ tV.map _` and `tV.map φ` commutes. -/
private theorem tildeChase {C SW SV D : Type*} [Category C] [Category SW] [Category SV]
    [Category D] {tW : C ⥤ SW} {pb : SW ⥤ SV} {E : C ⥤ D} {tV : D ⥤ SV}
    (P : tW ⋙ pb ≅ E ⋙ tV) {cL cK : C} {dL dK : D} (ψ : cL ⟶ cK)
    (mL : E.obj cL ⟶ dL) (mK : E.obj cK ⟶ dK) (φ : dL ⟶ dK)
    (hsq : E.map ψ ≫ mK = mL ≫ φ) :
    pb.map (tW.map ψ) ≫ P.hom.app cK ≫ tV.map mK =
      (P.hom.app cL ≫ tV.map mL) ≫ tV.map φ := by
  have hnat := P.hom.naturality ψ
  dsimp only [Functor.comp_map] at hnat
  rw [Category.assoc, reassoc_of% hnat, ← tV.map_comp, ← tV.map_comp, hsq]

/-- **The chart comparison of the determinant on the spectra is natural in the complex.** Let `X`
be a scheme, `L` and `K` perfect objects of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`, and `e` a
family of linear equivalences of the determinant modules of the chart complexes of `L` and of `K`,
one for each affine open. If, for an inclusion `V ≤ W` of affine opens, the members of `e` at `V`
and at `W` commute with the chart comparison
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` over the rings — the hypothesis `he`,
the base change to `Γ(X, V)` of the member at `W` being `TensorProduct`'s
`LinearMap.baseChange` — then the isomorphisms
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecOfEquiv` induced by `e` commute with the chart
comparison `AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso` on the spectra. -/
theorem chartDetSpecPullbackIso_natural {L K : PerfectTwoTermAmplitude X}
    (e : ∀ V : X.affineOpens,
      chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule K V)
    {V W : X.affineOpens} (h : V ≤ W)
    (he : letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
            (affineRestriction X h).hom.toAlgebra
          haveI : Module.Flat Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
            V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h)
          (chartDetModuleIso K h).toLinearMap ∘ₗ
              LinearMap.baseChange Γ(X, (V.1 : X.Opens)) (e W).toLinearMap =
            (e V).toLinearMap ∘ₗ (chartDetModuleIso L h).toLinearMap) :
    (Scheme.Modules.pullback (Spec.map (affineRestriction X h))).map
          (chartDetSpecOfEquiv W (e W)).hom ≫
        (chartDetSpecPullbackIso K h).hom =
      (chartDetSpecPullbackIso L h).hom ≫ (chartDetSpecOfEquiv V (e V)).hom :=
  tildeChase
    (pullbackTildeIso Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) (affineRestriction X h))
    (e W).toModuleIso.hom (chartDetModuleIso L h).toModuleIso.hom
    (chartDetModuleIso K h).toModuleIso.hom (e V).toModuleIso.hom
    (ModuleCat.hom_ext he)

/-! ### The comparison on the open subschemes -/

/-- A commuting square whose two horizontal arrows are isomorphisms, read with both of them
reversed. -/
private theorem symm_square {D : Type*} [Category D] {a b c d : D} (i : a ≅ c) (j : b ≅ d)
    {φ : a ⟶ b} {ψ : c ⟶ d} (hsq : φ ≫ j.hom = i.hom ≫ ψ) :
    ψ ≫ j.symm.hom = i.symm.hom ≫ φ := by
  rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact hsq.symm

/-- A functor carries a commuting square whose two horizontal arrows are isomorphisms to a
commuting square whose two horizontal arrows are their images under
`CategoryTheory.Functor.mapIso`. -/
private theorem mapIso_square {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {p q r s : C} (i : p ≅ r) (j : q ≅ s) {a : p ⟶ q} {b : r ⟶ s}
    (hsq : a ≫ j.hom = i.hom ≫ b) :
    G.map a ≫ (G.mapIso j).hom = (G.mapIso i).hom ≫ G.map b := by
  simp only [Functor.mapIso_hom, ← G.map_comp, hsq]

/-- The naturality square of a natural isomorphism, with its two components written as
`CategoryTheory.Iso.app` rather than as the components of its `hom`. -/
private theorem isoApp_square {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α : F ≅ G) {x y : C} (f : x ⟶ y) :
    F.map f ≫ (α.app y).hom = (α.app x).hom ≫ G.map f :=
  α.hom.naturality f

/-- Five commuting squares `wₖ₋₁ ≫ jₖ.hom = iₖ.hom ≫ wₖ` between two chains of five isomorphisms
compose to a commuting square between the composites `i₁ ≪≫ ⋯ ≪≫ i₅` and `j₁ ≪≫ ⋯ ≪≫ j₅`. -/
private theorem fiveChaseIso {D : Type*} [Category D]
    {a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ b₅ : D}
    (i₁ : a₀ ≅ a₁) (i₂ : a₁ ≅ a₂) (i₃ : a₂ ≅ a₃) (i₄ : a₃ ≅ a₄) (i₅ : a₄ ≅ a₅)
    (j₁ : b₀ ≅ b₁) (j₂ : b₁ ≅ b₂) (j₃ : b₂ ≅ b₃) (j₄ : b₃ ≅ b₄) (j₅ : b₄ ≅ b₅)
    {w₀ : a₀ ⟶ b₀} {w₁ : a₁ ⟶ b₁} {w₂ : a₂ ⟶ b₂} {w₃ : a₃ ⟶ b₃} {w₄ : a₄ ⟶ b₄}
    {w₅ : a₅ ⟶ b₅}
    (h₁ : w₀ ≫ j₁.hom = i₁.hom ≫ w₁) (h₂ : w₁ ≫ j₂.hom = i₂.hom ≫ w₂)
    (h₃ : w₂ ≫ j₃.hom = i₃.hom ≫ w₃) (h₄ : w₃ ≫ j₄.hom = i₄.hom ≫ w₄)
    (h₅ : w₄ ≫ j₅.hom = i₅.hom ≫ w₅) :
    (i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅).hom ≫ w₅ =
      w₀ ≫ (j₁ ≪≫ j₂ ≪≫ j₃ ≪≫ j₄ ≪≫ j₅).hom := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [← h₅, ← reassoc_of% h₄, ← reassoc_of% h₃, ← reassoc_of% h₂, ← reassoc_of% h₁]

/-- `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` as the composite of its five
factors, as an equality of isomorphisms. -/
private theorem chartDetRestrictIso_eq (L : PerfectTwoTermAmplitude X) {V W : X.affineOpens}
    (h : V ≤ W) :
    chartDetRestrictIso L h =
      (Scheme.Modules.pullback V.2.isoSpec.hom).mapIso (chartDetSpecPullbackIso L h).symm ≪≫
        (Scheme.Modules.pullbackComp V.2.isoSpec.hom
            (Spec.map (affineRestriction X h))).app (chartDetSpec L W) ≪≫
          (Scheme.Modules.pullbackCongr
              (isoSpec_hom_specMap_chartRestriction h)).app (chartDetSpec L W) ≪≫
            ((Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
                W.2.isoSpec.hom).app (chartDetSpec L W)).symm ≪≫
              ((Scheme.Modules.restrictFunctorIsoPullback
                  (X.homOfLE (AffineOpensGlue.coe_le_coe h))).app (chartDet L W)).symm :=
  rfl

/-- **The chart comparison of the determinant on the open subschemes is natural in the complex.**
Let `X` be a scheme, `L` and `K` perfect objects of `D(𝒪_X)` of Tor-amplitude in `[-1, 0]`, and
`e` a family of linear equivalences of the determinant modules of the chart complexes, one for
each affine open. For an inclusion `V ≤ W` of affine opens, if the isomorphisms induced by `e`
commute with the chart comparison on the spectra — the hypothesis `hspec`, which is
`AlgebraicGeometry.DeterminantTwoTerm.chartDetSpecPullbackIso_natural` — then the isomorphisms
`AlgebraicGeometry.DeterminantTwoTerm.chartDetOfEquiv` induced by `e` commute with the chart
comparison `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso` on the open subschemes. -/
theorem chartDetRestrictIso_natural {L K : PerfectTwoTermAmplitude X}
    (e : ∀ V : X.affineOpens,
      chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule K V)
    {V W : X.affineOpens} (h : V ≤ W)
    (hspec : (Scheme.Modules.pullback (Spec.map (affineRestriction X h))).map
          (chartDetSpecOfEquiv W (e W)).hom ≫ (chartDetSpecPullbackIso K h).hom =
        (chartDetSpecPullbackIso L h).hom ≫ (chartDetSpecOfEquiv V (e V)).hom) :
    (chartDetRestrictIso L h).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).map
          (chartDetOfEquiv W (e W)).hom =
      (chartDetOfEquiv V (e V)).hom ≫ (chartDetRestrictIso K h).hom := by
  rw [chartDetRestrictIso_eq L h, chartDetRestrictIso_eq K h]
  exact fiveChaseIso _ _ _ _ _ _ _ _ _ _
    (mapIso_square (Scheme.Modules.pullback V.2.isoSpec.hom)
      (chartDetSpecPullbackIso L h).symm (chartDetSpecPullbackIso K h).symm
      (symm_square (chartDetSpecPullbackIso L h) (chartDetSpecPullbackIso K h) hspec))
    (isoApp_square (Scheme.Modules.pullbackComp V.2.isoSpec.hom
      (Spec.map (affineRestriction X h))) (chartDetSpecOfEquiv W (e W)).hom)
    (isoApp_square (Scheme.Modules.pullbackCongr
      (isoSpec_hom_specMap_chartRestriction h)) (chartDetSpecOfEquiv W (e W)).hom)
    (isoApp_square (Scheme.Modules.pullbackComp (X.homOfLE (AffineOpensGlue.coe_le_coe h))
      W.2.isoSpec.hom).symm (chartDetSpecOfEquiv W (e W)).hom)
    (isoApp_square (Scheme.Modules.restrictFunctorIsoPullback
      (X.homOfLE (AffineOpensGlue.coe_le_coe h))).symm (chartDetOfEquiv W (e W)).hom)

/-- **The chart comparison on the open subschemes is natural in the complex, from the ring-level
square alone.** If the family `e` commutes with
`AlgebraicGeometry.DeterminantTwoTerm.chartDetModuleIso` over the rings (the hypothesis `he`),
then the isomorphisms `AlgebraicGeometry.DeterminantTwoTerm.chartDetOfEquiv` induced by `e`
commute with `AlgebraicGeometry.DeterminantTwoTerm.chartDetRestrictIso`. -/
theorem chartDetRestrictIso_natural' {L K : PerfectTwoTermAmplitude X}
    (e : ∀ V : X.affineOpens,
      chartDetModule L V ≃ₗ[Γ(X, (V.1 : X.Opens))] chartDetModule K V)
    {V W : X.affineOpens} (h : V ≤ W)
    (he : letI : Algebra Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
            (affineRestriction X h).hom.toAlgebra
          haveI : Module.Flat Γ(X, (W.1 : X.Opens)) Γ(X, (V.1 : X.Opens)) :=
            V.2.moduleFlat_presheaf_map W.2 (AffineOpensGlue.coe_le_coe h)
          (chartDetModuleIso K h).toLinearMap ∘ₗ
              LinearMap.baseChange Γ(X, (V.1 : X.Opens)) (e W).toLinearMap =
            (e V).toLinearMap ∘ₗ (chartDetModuleIso L h).toLinearMap) :
    (chartDetRestrictIso L h).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE (AffineOpensGlue.coe_le_coe h))).map
          (chartDetOfEquiv W (e W)).hom =
      (chartDetOfEquiv V (e V)).hom ≫ (chartDetRestrictIso K h).hom :=
  chartDetRestrictIso_natural e h (chartDetSpecPullbackIso_natural e h he)

end AlgebraicGeometry.DeterminantTwoTerm

end
