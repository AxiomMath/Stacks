module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.ReconstructionChartUnit

/-!
# The reconstruction chart comparison, normalised at the structure sheaf

The glueing of the per-chart comparisons of [Stacks, Tag 0GPJ]
(`AlgebraicGeometry.exists_natIso_of_chartComparison`) needs each of them to agree, at the
structure sheaf, with the canonical and chart-free
`AlgebraicGeometry.pullbackTensorFunctorObjUnitIso`.  This file computes the two sides of a
chart there.

## Why there is anything to prove

`AlgebraicGeometry.chartComparisonIso` is the left-hand side of a chart composed with the
inverse of the right-hand side, and the invertible sheaf identification it is fed is
`AlgebraicGeometry.restrictMapUnitIsoOfChartIso`, built from the very same `α` and `β`.  So at
`𝒪_X` the chart data does cancel against itself — but the two occurrences are separated by the
right unitor `L ⊗ 𝒪_V ≅ L` and by the transport of the tensor functor along the identification,
so the cancellation is not `CategoryTheory.Iso.hom_inv_id`.  The coherences that bridge the gap
are in
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/ReconstructionChartUnit.lean`; what is left here is
the bookkeeping, and the only chart-level input is
`AlgebraicGeometry.chartUnitChain`.

## Main results

* `AlgebraicGeometry.chartPullbackIso_hom_app_unit` — the left-hand side of a chart at `𝒪_X`:
  it is `AlgebraicGeometry.restrictMapUnitIsoOfChartIso` followed by the inverse of the right
  unitor and the canonical identification of `(f ≫ U.ι)^*𝒪_X` with `𝒪_V`.
* `AlgebraicGeometry.moduleChartPullbackIso_hom_app_unit` — the right-hand side of a chart at
  `𝒪_X`, preceded by the canonical identification of `g^*𝒪_X ⊗ M` with `M`: the same morphism.
* `AlgebraicGeometry.chartComparisonIso_hom_app_quasicoherentUnit` — **the normalisation**: the
  comparison of functors over a chart agrees at `𝒪_X` with the restriction of the chart-free
  `AlgebraicGeometry.pullbackTensorFunctorObjUnitIso`.

## Implementation notes

Every comparison isomorphism occurring here reads at an object by `rfl`, so the normalisation is
reached by a single `show` that writes the goal out and one application of a purely
category-theoretic cancellation lemma.  `rw` and `simp` on the whole goal exceed the heartbeat
budget because the terms are large and the local `implicit_reducible` attributes
make every unification unfold the two chains of definitions naming the structure sheaf.  The
`show` is pinned to the current unfolding of `AlgebraicGeometry.chartPullbackIso`,
`AlgebraicGeometry.restrictMapUnitIsoOfChartIso` and
`AlgebraicGeometry.pullbackTensorFunctorQuasicoherentRestrictIso`; if one of those is
restructured, re-read its `_hom_app` lemma rather than touching the cancellation lemma, which is
independent of all of it.

## References

* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

/- One object is named through two chains of definitions — the structure sheaf of a scheme as
`AlgebraicGeometry.Scheme.ringCatSheaf` and as
`Stacks.SheafOfModules.TensorSheafification.structureSheaf` of its structure presheaf — and
instance search, which works at `reducible` transparency, sees through neither;
`AlgebraicGeometry.Scheme.unitModule` is a third such chain. -/
attribute [local implicit_reducible] Stacks.SheafOfModules.TensorSheafification.structureSheaf
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  CategoryTheory.sheafCompose TopCat.Sheaf TopCat.Presheaf.IsSheaf
  AlgebraicGeometry.Scheme.unitModule

section Abstract

universe v₁ u₁ v₂ u₂

/-- The pure category algebra behind `AlgebraicGeometry.chartPullbackIso_hom_app_unit`: a
composite ending in `T.map ξ₁ ≫ T.map ξ₂` agrees with the same composite rerouted through an
isomorphism `υ`, provided `ξ₁ ≫ ξ₂` becomes `η` after the isomorphism `ν`. -/
private theorem comp_map_cancel_aux {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] (T : C ⥤ D) {A₀ A₁ A₂ A₃ : C} (ν : A₂ ≅ A₃) {B₀ B₁ B₂ B₃ : D}
    {ξ₁ : A₀ ⟶ A₁} {ξ₂ : A₁ ⟶ A₂} {η : A₀ ⟶ A₃}
    (c : B₀ ⟶ B₁) (a₁ : B₁ ⟶ B₂) (a₂ : B₂ ⟶ T.obj A₀) {e : T.obj A₀ ⟶ T.obj A₀}
    (υ : T.obj A₃ ≅ B₃) (he : e = 𝟙 (T.obj A₀)) (h : ξ₁ ≫ ξ₂ ≫ ν.hom = η) :
    c ≫ a₁ ≫ a₂ ≫ e ≫ T.map ξ₁ ≫ T.map ξ₂ =
      (c ≫ a₁ ≫ a₂ ≫ T.map η ≫ υ.hom) ≫ υ.inv ≫ T.map ν.inv := by
  have key : T.map ξ₁ ≫ T.map ξ₂ = T.map η ≫ T.map ν.inv := by
    rw [← h]
    simp
  rw [he, Category.id_comp, key]
  simp

end Abstract

section ModuleAbstract

variable {A B : Type*} [Category A] [Category B]

/-- The chart computation at the structure sheaf, with every object abstracted away.  Read
`P` as inverse image along `V.ι`, `TM`, `TN`, `TL` as the three tensor functors, `C` as the
comparison of [Stacks, Tag 01CD] and `τ` as the transport of the tensor functor along
`e : P.obj M ≅ L`; `H2` says `C` is compatible with the right unitor, `H3` that the chart's
identification of `(f ≫ U.ι)^*𝒪_X` with `𝒪_V` is the canonical one, and `H6` that the right
unitor is natural in the twisting sheaf.  Stating it with variables keeps the terms small
enough for `rw` to elaborate; the real objects enter once, by application. -/
private theorem chart_unit_aux (P : A ⥤ B) (TM : A ⥤ A) (TN TL : B ⥤ B)
    (C : TM ⋙ P ≅ P ⋙ TN) (τ : TN ≅ TL)
    {OY Z M : A} {OV ZK W2 L : B}
    (pg : Z ≅ OY) (b : P.obj OY ≅ OV) (γ : P.obj Z ≅ W2) (δ : W2 ≅ ZK) (pk : ZK ≅ OV)
    (υM : TM.obj OY ≅ M) (υN : TN.obj OV ≅ P.obj M) (υL : TL.obj OV ≅ L)
    (e : P.obj M ≅ L)
    (H2 : C.hom.app OY ≫ TN.map b.hom ≫ υN.hom = P.map υM.hom)
    (H3 : δ.inv ≫ γ.inv ≫ P.map pg.hom ≫ b.hom = pk.hom)
    (H6 : τ.hom.app OV ≫ υL.hom = υN.hom ≫ e.hom) :
    P.map (υM.inv ≫ TM.map pg.inv) ≫ (C.hom.app Z ≫ TN.map γ.hom) ≫
        TN.map δ.hom ≫ τ.hom.app ZK =
      e.hom ≫ υL.inv ≫ TL.map pk.inv := by
  have nat1 : P.map (TM.map pg.inv) ≫ C.hom.app Z = C.hom.app OY ≫ TN.map (P.map pg.inv) :=
    C.hom.naturality pg.inv
  have nat5 : TN.map pk.inv ≫ τ.hom.app ZK = τ.hom.app OV ≫ TL.map pk.inv :=
    τ.hom.naturality pk.inv
  have hC : C.hom.app OY = P.map υM.hom ≫ υN.inv ≫ TN.map b.inv :=
    (Iso.eq_comp_inv (TN.mapIso b ≪≫ υN)).2 H2
  have h2' : P.map υM.inv ≫ C.hom.app OY = υN.inv ≫ TN.map b.inv := by
    rw [hC, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  have hpk : b.inv ≫ P.map pg.inv ≫ γ.hom ≫ δ.hom = pk.inv := by
    have hw : pk = δ.symm ≪≫ γ.symm ≪≫ P.mapIso pg ≪≫ b := Iso.ext H3.symm
    rw [hw]
    simp
  have h3' : TN.map b.inv ≫ TN.map (P.map pg.inv) ≫ TN.map γ.hom ≫ TN.map δ.hom =
      TN.map pk.inv := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hpk]
  have hτ : τ.hom.app OV = (υN.hom ≫ e.hom) ≫ υL.inv := (Iso.eq_comp_inv υL).2 H6
  have h6' : υN.inv ≫ τ.hom.app OV = e.hom ≫ υL.inv := by
    rw [hτ, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Functor.map_comp, Category.assoc, Category.assoc, reassoc_of% nat1, reassoc_of% h2',
    reassoc_of% h3', nat5, reassoc_of% h6']

end ModuleAbstract

/-- Abstract cancellation: if `x` and `y ≫ qh` are the same morphism and `qh` has the right
inverse `qi`, then `x ≫ qi = y`.  This is how the two halves of a chart, each computed at the
structure sheaf, are composed into the comparison over the chart. -/
private theorem eq_of_comp_hom_eq {C : Type*} [Category* C] {P Q R : C} {qh : Q ⟶ R} {qi : R ⟶ Q}
    (hqi : qh ≫ qi = 𝟙 Q) {x : P ⟶ R} {y : P ⟶ Q} {w : P ⟶ R} (hA : x = w) (hB : y ≫ qh = w) :
    x ≫ qi = y := by
  rw [hA, ← hB, Category.assoc, hqi, Category.comp_id]


/-- The right-hand side of a chart, read at the structure sheaf. -/
theorem moduleChartPullbackIso_hom_app_unit {X Y : Scheme.{u}} (g : Y ≅ X) (M : Y.Modules)
    {V : Y.Opens} {U : X.Opens} (f : V.toScheme ≅ U.toScheme)
    (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
    (hg : V.ι ≫ g.hom = f.hom ≫ U.ι) (hres : Scheme.Modules.restrict M V.ι ≅ L) :
    (Scheme.Modules.pullback V.ι).map (pullbackTensorFunctorObjUnitIso g.hom M).inv ≫
        (moduleChartPullbackIso g M f L hg hres).hom.app (quasicoherentUnit X) =
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ hres).hom ≫
        (tensorLeftFunctorObjUnitSchemeIso L).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj L).map
          (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι)).inv := by
  have H2 := tensorLeftFunctorCompPullback_hom_app_unit V.ι M
  have H3 : ((Scheme.Modules.pullbackCongr hg).app (Scheme.unitModule X)).inv ≫
      ((Scheme.Modules.pullbackComp V.ι g.hom).app (Scheme.unitModule X)).inv ≫
      (Scheme.Modules.pullback V.ι).map (Scheme.Modules.pullbackUnitIso g.hom).hom ≫
      (Scheme.Modules.pullbackUnitIso V.ι).hom =
      (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι)).hom :=
    Scheme.Modules.pullbackUnitIso_comp_eq V.ι g.hom (f.hom ≫ U.ι) hg
  have H6 := tensorLeftFunctorObjUnitSchemeIso_naturality
    (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ hres)
  exact chart_unit_aux (Scheme.Modules.pullback V.ι)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj M)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
      ((Scheme.Modules.pullback V.ι).obj M))
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj L)
    (tensorLeftFunctorCompPullback V.ι.toLRSHom.toShHom V.toScheme.ringCatSheaf.2
      Y.ringCatSheaf.2 M)
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).mapIso
      (X := (Scheme.Modules.pullback V.ι).obj M) (Y := L)
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ hres))
    (Scheme.Modules.pullbackUnitIso g.hom) (Scheme.Modules.pullbackUnitIso V.ι)
    ((Scheme.Modules.pullbackComp V.ι g.hom).app (Scheme.unitModule X))
    ((Scheme.Modules.pullbackCongr hg).app (Scheme.unitModule X))
    (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι))
    (tensorLeftFunctorObjUnitSchemeIso M)
    (tensorLeftFunctorObjUnitSchemeIso ((Scheme.Modules.pullback V.ι).obj M))
    (tensorLeftFunctorObjUnitSchemeIso L)
    (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm ≪≫ hres)
    H2 H3 H6


/-- `AlgebraicGeometry.chartUnitChain` read at `(quasicoherentUnit X).obj` rather than at
`SheafOfModules.unit X.ringCatSheaf`. -/
private theorem chartUnitChain_unit {X Y : Scheme.{u}} {V : Y.Opens} {U : X.Opens}
    (f : V.toScheme ≅ U.toScheme) :
    (Scheme.Modules.pullback f.hom).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app (quasicoherentUnit X).obj) ≫
        (Scheme.Modules.pullbackComp f.hom U.ι).hom.app (quasicoherentUnit X).obj ≫
        (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι)).hom =
      (Scheme.Modules.pullback f.hom).map (Scheme.Modules.restrictUnitIso U.ι).hom ≫
        (Scheme.Modules.pullbackUnitIso f.hom).hom :=
  chartUnitChain f

section Chart

variable {X Y : Scheme.{u}}
  (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
  (g : Y ≅ X) {V : Y.Opens} {U : X.Opens}
  {F : (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).FullSubcategory ⥤
    (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf).FullSubcategory}
  (f : V.toScheme ≅ U.toScheme) (L : SheafOfModules.{u} V.toScheme.ringCatSheaf)
  (α : E ⋙ quasicoherentRestriction V.ι ≅ quasicoherentRestriction U.ι ⋙ F)
  (β : F ⋙ ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf) ≅
    pullbackTensorFunctor f.hom L)
  (hg : V.ι ≫ g.hom = f.hom ≫ U.ι)

/-- The left-hand side of a chart, read at the structure sheaf. -/
theorem chartPullbackIso_hom_app_unit :
    (chartPullbackIso E f L α β).hom.app (quasicoherentUnit X) =
      ((((Scheme.Modules.restrictFunctorIsoPullback V.ι).app
              (E.obj (quasicoherentUnit X)).obj).symm ≪≫
          restrictMapUnitIsoOfChartIso E f L α β)).hom ≫
        (tensorLeftFunctorObjUnitSchemeIso L).inv ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj L).map
          (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι)).inv := by
  show (Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app
          (E.obj (quasicoherentUnit X)).obj ≫
        (ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf)).map
            (α.app (quasicoherentUnit X)).hom ≫
          (β.app ((quasicoherentRestriction U.ι).obj (quasicoherentUnit X))).hom ≫
            ((Scheme.Modules.pullback f.hom ⋙
                  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
                    L).map
                (𝟙 ((Scheme.Modules.restrictFunctor U.ι).obj (quasicoherentUnit X).obj)) ≫
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
                  L).map
                  ((Scheme.Modules.pullback f.hom).map
                    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
                      (quasicoherentUnit X).obj)) ≫
                ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
                    L).map
                  ((Scheme.Modules.pullbackComp f.hom U.ι).hom.app
                    (quasicoherentUnit X).obj)) =
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app
            (E.obj (quasicoherentUnit X)).obj ≫
          (ObjectProperty.ι (SheafOfModules.isQuasicoherent V.toScheme.ringCatSheaf)).map
              (α.app (quasicoherentUnit X)).hom ≫
            (β.app ((quasicoherentRestriction U.ι).obj (quasicoherentUnit X))).hom ≫
              ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj
                  L).map
                  ((Scheme.Modules.pullback f.hom).map
                      (Scheme.Modules.restrictUnitIso U.ι).hom ≫
                    (Scheme.Modules.pullbackUnitIso f.hom).hom) ≫
                (tensorLeftFunctorObjUnitSchemeIso L).hom) ≫
        (tensorLeftFunctorObjUnitSchemeIso L).inv ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj L).map
            (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι)).inv
  exact comp_map_cancel_aux _ (Scheme.Modules.pullbackUnitIso (f.hom ≫ U.ι)) _ _ _ _
    ((Scheme.Modules.pullback f.hom ⋙
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} V.toScheme.sheaf).obj L).map_id
      ((Scheme.Modules.restrictFunctor U.ι).obj (quasicoherentUnit X).obj))
    (chartUnitChain_unit f)


/-- **The comparison over a chart, read at the structure sheaf**, with the restriction written
as the inverse image.  Both halves of the chart compute to the same morphism there
(`AlgebraicGeometry.chartPullbackIso_hom_app_unit` and
`AlgebraicGeometry.moduleChartPullbackIso_hom_app_unit`), so composing one with the inverse of
the other leaves the canonical, chart-free
`AlgebraicGeometry.pullbackTensorFunctorObjUnitIso`. -/
theorem chartComparisonPullbackIso_hom_app_quasicoherentUnit :
    (chartComparisonPullbackIso E g (E.obj (quasicoherentUnit X)).obj f L α β hg
        (restrictMapUnitIsoOfChartIso E f L α β)).hom.app (quasicoherentUnit X) =
      (Scheme.Modules.pullback V.ι).map
        (pullbackTensorFunctorObjUnitIso g.hom (E.obj (quasicoherentUnit X)).obj).inv :=
  (chartComparisonPullbackIso_hom_app E g _ f L α β hg _ (quasicoherentUnit X)).trans
    (eq_of_comp_hom_eq
      (Iso.hom_inv_id_app
        (moduleChartPullbackIso g (E.obj (quasicoherentUnit X)).obj f L hg
          (restrictMapUnitIsoOfChartIso E f L α β)) (quasicoherentUnit X))
      (chartPullbackIso_hom_app_unit E f L α β)
      (moduleChartPullbackIso_hom_app_unit g (E.obj (quasicoherentUnit X)).obj f L hg
        (restrictMapUnitIsoOfChartIso E f L α β)))

/-- **The normalisation at the structure sheaf: the comparison of functors of
[Stacks, Tag 0GPJ] over one chart agrees at `𝒪_X` with the canonical identification of
`g^*𝒪_X ⊗ M` with `M`.**  No chart occurs on the right-hand side, so the per-chart comparisons
of a whole reconstruction cover agree at `𝒪_X`, which is the hypothesis
`AlgebraicGeometry.exists_natIso_of_chartComparison` consumes and the one the rigidity statement
`AlgebraicGeometry.natIso_eq_of_app_unit_eq_of_iso` needs.

No action of the units of `Γ(V, 𝒪)` on natural transformations is involved: the invertible
module is `E(𝒪_X)` and the identification of its restriction with `L` is
`AlgebraicGeometry.restrictMapUnitIsoOfChartIso`, built from the very `α` and `β` the comparison
is assembled from, so at `𝒪_X` the chart data cancels against itself. -/
theorem chartComparisonIso_hom_app_quasicoherentUnit :
    (chartComparisonIso E g (E.obj (quasicoherentUnit X)).obj f L α β hg
        (restrictMapUnitIsoOfChartIso E f L α β)).hom.app (quasicoherentUnit X) =
      (Scheme.Modules.restrictFunctor V.ι).map
        (pullbackTensorFunctorObjUnitIso g.hom (E.obj (quasicoherentUnit X)).obj).inv :=
  (chartComparisonIso_hom_app E g _ f L α β hg _ (quasicoherentUnit X)).trans
    ((congrArg (fun z => (Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app
          (E.obj (quasicoherentUnit X)).obj ≫ z ≫
        (Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app
          ((pullbackTensorFunctor g.hom (E.obj (quasicoherentUnit X)).obj).obj
            (quasicoherentUnit X)))
        (chartComparisonPullbackIso_hom_app_quasicoherentUnit E g f L α β hg)).trans
      (NatIso.naturality_2 (Scheme.Modules.restrictFunctorIsoPullback V.ι) _))


end Chart

end AlgebraicGeometry

end
