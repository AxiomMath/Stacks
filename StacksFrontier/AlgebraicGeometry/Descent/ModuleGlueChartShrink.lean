module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart

/-!
# The comparison isomorphisms of a glued module, compared on two nested charts

`AlgebraicGeometry.RestrictIsoGlueData.chartIso` identifies the restriction of the glued module
along the `i`-th chart with the module the `i`-th chart carried.  When the `j`-th chart factors
through the `i`-th one, `b ≫ f i = f j`, the two comparison isomorphisms are related:  restricting
the `i`-th one further along `b` and following it with an identification
`σ : (mod i)|_b ≅ mod j` gives the `j`-th one, provided `σ` is the identification the glueing
datum already carries over the range of the `j`-th chart.

That compatibility is what a construction which glues over a *family of opens closed under
intersection* needs:  there the chart of a smaller open factors through the chart of a larger
one, and the comparison of the glued module with the module on the larger chart has to agree,
after shrinking, with the comparison on the smaller chart.

## Main results

* `AlgebraicGeometry.Scheme.Modules.faithful_restrictFunctor_of_isIso`: restriction along an
  isomorphism is faithful.
* `AlgebraicGeometry.isIso_openLift_opensRange`: the factorisation of the range of an open
  immersion through that immersion is an isomorphism.
* `AlgebraicGeometry.RestrictIsoGlueData.restrictFunctor_map_chartAdjunct_comp_iso`: over the
  range of the `j`-th chart, the comparison datum of the glueing intertwines the transposed
  comparison isomorphisms of the `i`-th and the `j`-th chart.
* `AlgebraicGeometry.RestrictIsoGlueData.restrictChartIso_chartIso`: **the comparison
  isomorphisms of two nested charts agree.**

## Implementation notes

The proof has three steps.  Both isomorphisms in question are first written as the transposed
comparison `Stacks.SheafOfModules.ModulesGlueData.chartAdjunct` -- a morphism of modules on the
ambient scheme, so independent of the chart -- restricted along the `j`-th chart and followed by
a comparison; the two comparisons are then identified over the *range* of the `j`-th chart, which
is an open of the ambient scheme and therefore within reach of
`AlgebraicGeometry.restrictFunctor_map_comp_eq` and the section-level identity
`Stacks.SheafOfModules.ModulesGlueData.trans_chartAdjunct`; finally the identity over the range
is transported back to the chart along `AlgebraicGeometry.openLift`, which is an isomorphism, by
faithfulness of restriction along an isomorphism.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-! ### Restriction along an isomorphism -/

/-- **Restriction along an isomorphism is faithful.**  Restriction along the inverse is a
quasi-inverse, by pseudo-functoriality of restriction. -/
theorem Scheme.Modules.faithful_restrictFunctor_of_isIso {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsOpenImmersion g] [IsIso g] : (Scheme.Modules.restrictFunctor g).Faithful :=
  Functor.Faithful.of_comp_iso (G := Scheme.Modules.restrictFunctor (inv g))
    (H := 𝟭 Y.Modules)
    ((Scheme.Modules.restrictFunctorComp (inv g) g).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (IsIso.inv_hom_id g) ≪≫
      Scheme.Modules.restrictFunctorId)

/-- **The factorisation of the range of an open immersion through that immersion is an
isomorphism**:  it is the comparison of the source with its image. -/
instance isIso_openLift_opensRange {S A : Scheme.{u}} (a : A ⟶ S) [IsOpenImmersion a] :
    IsIso (openLift a (le_refl a.opensRange)) := by
  rw [show openLift a (le_refl a.opensRange) = a.isoOpensRange.inv from
    (eq_openLift a _ _ (Scheme.Hom.isoOpensRange_inv_comp a)).symm]
  infer_instance

/-! ### Reading a chart identification back on the inverse images -/

/-- **`AlgebraicGeometry.restrictChartIso_pullback_trans` read backwards.**  If the two
identifications of the restriction of `M` along `b ≫ a` with `M''` -- the iterated one and the
direct one `ρ''` -- agree, then the comparisons `ρ`, `ρ'`, `ρ''` of the *inverse images* satisfy
the cocycle condition on the inverse image along the composite.  Everything in the chain is an
isomorphism, so the implication proved there is reversible, and the proof is that one with the
three isomorphisms cancelled on the other side. -/
theorem pullbackCompIsoOfEq_hom_comp_of_restrictChartIso {Q P P' : Scheme.{u}} (a : P ⟶ Q)
    (b : P' ⟶ P) [IsOpenImmersion a] [IsOpenImmersion b] {k : P' ⟶ Q} (hk : b ≫ a = k)
    [IsOpenImmersion k] {M : Q.Modules} {M' : P.Modules} {M'' : P'.Modules}
    (ρ : (Scheme.Modules.pullback a).obj M ≅ M')
    (ρ' : (Scheme.Modules.pullback b).obj M' ≅ M'')
    (ρ'' : (Scheme.Modules.pullback k).obj M ≅ M'')
    (h : restrictChartIso a ((Scheme.Modules.restrictFunctorIsoPullback a).app M ≪≫ ρ) b hk ≪≫
        ((Scheme.Modules.restrictFunctorIsoPullback b).app M' ≪≫ ρ') =
      (Scheme.Modules.restrictFunctorIsoPullback k).app M ≪≫ ρ'') :
    (pullbackCompIsoOfEq b a hk M).hom ≫ ρ''.hom =
      (Scheme.Modules.pullback b).map ρ.hom ≫ ρ'.hom := by
  have hcoh := NatTrans.congr_app
    (Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_comp_of_eq b a hk) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hcoh
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback b).hom.naturality ρ.hom
  have key : (Scheme.Modules.restrictFunctor b).map
        ((Scheme.Modules.restrictFunctorIsoPullback a).hom.app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback b).hom.app
          ((Scheme.Modules.pullback a).obj M) ≫ (pullbackCompIsoOfEq b a hk M).hom =
      (restrictCompIso b a hk M).inv ≫
        (Scheme.Modules.restrictFunctorIsoPullback k).hom.app M := by
    rw [show (restrictCompIso b a hk M).inv =
        (Scheme.Modules.restrictFunctorComp b a).inv.app M ≫
          (Scheme.Modules.restrictFunctorCongr hk).hom.app M from rfl, pullbackCompIsoOfEq]
    simp only [Iso.trans_hom, Iso.app_hom, Category.assoc]
    exact hcoh.symm
  have key2 := congrArg (fun z => (restrictCompIso b a hk M).hom ≫ z ≫ ρ''.hom) key
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at key2
  have hh := congrArg Iso.hom h
  simp only [restrictChartIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc] at hh
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor b).map ρ.hom), hnat,
    Category.assoc] at hh
  refine (cancel_epi ((restrictCompIso b a hk M).hom ≫
    (Scheme.Modules.restrictFunctor b).map
        ((Scheme.Modules.restrictFunctorIsoPullback a).hom.app M) ≫
      (Scheme.Modules.restrictFunctorIsoPullback b).hom.app
        ((Scheme.Modules.pullback a).obj M))).mp ?_
  simp only [Category.assoc]
  exact key2.trans hh.symm

namespace RestrictIsoGlueData

attribute [local implicit_reducible] AlgebraicGeometry.RestrictIsoGlueData.toModulesGlueData

variable {S : Scheme.{u}} {ι : Type u} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ S}
  [∀ i, IsOpenImmersion (f i)] (D : RestrictIsoGlueData S f) (i j : ι)

/-- **Over the range of the `j`-th chart the comparison datum of the glueing intertwines the
transposed comparison isomorphisms of the `i`-th and the `j`-th chart.**  This is
`Stacks.SheafOfModules.ModulesGlueData.trans_chartAdjunct`, read through
`AlgebraicGeometry.RestrictIsoGlueData.trans_eq_localAppFun_le`. -/
theorem restrictFunctor_map_chartAdjunct_comp_iso
    (hij : (f j).opensRange ≤ (f i).opensRange) :
    (Scheme.Modules.restrictFunctor ((f j).opensRange).ι).map
          (D.toModulesGlueData.chartAdjunct i) ≫
        (D.iso i j hij le_rfl).hom =
      (Scheme.Modules.restrictFunctor ((f j).opensRange).ι).map
        (D.toModulesGlueData.chartAdjunct j) :=
  restrictFunctor_map_comp_eq _ _ _ fun _ hW =>
    app_comp_localApp hW _ _ _ fun s =>
      (D.trans_eq_localAppFun_le i j hij le_rfl hW _).symm.trans
        (D.toModulesGlueData.trans_chartAdjunct i j (hW.trans hij) hW s)

section Nested

variable {b : Z j ⟶ Z i} [IsOpenImmersion b] (hb : b ≫ f i = f j)
  (σ : Scheme.Modules.restrict (D.mod i) b ≅ D.mod j)

/-- The chart comparison of the `i`-th chart, restricted along `b` and followed by `σ`:  the
comparison of the direct image of the `i`-th module, restricted along the `j`-th chart, with the
`j`-th module. -/
private def nestedComparison :
    Scheme.Modules.restrict
        ((Scheme.Modules.pushforward (f i)).obj (D.mod i)) (f j) ≅ D.mod j :=
  restrictChartIso (f i) ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i)) b
    hb ≪≫ σ

/-- The restriction along `b` of the `i`-th comparison isomorphism of the glued module, followed
by `σ`, is the transposed `i`-th comparison restricted along the `j`-th chart, followed by
`AlgebraicGeometry.RestrictIsoGlueData.nestedComparison`. -/
private theorem restrictChartIso_chartIso_hom_eq :
    (restrictChartIso (f i) (D.chartIso i) b hb ≪≫ σ).hom =
      (Scheme.Modules.restrictFunctor (f j)).map (D.toModulesGlueData.chartAdjunct i) ≫
        (D.nestedComparison i j hb σ).hom := by
  have hci : (D.chartIso i).hom =
      (Scheme.Modules.restrictFunctor (f i)).map (D.toModulesGlueData.chartAdjunct i) ≫
        ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i)).hom :=
    (D.toModulesGlueData.restrictFunctor_map_chartAdjunct i).symm
  have hmc := (Scheme.Modules.restrictFunctor b).map_comp
    ((Scheme.Modules.restrictFunctor (f i)).map (D.toModulesGlueData.chartAdjunct i))
    ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i)).hom
  have hnat : (Scheme.Modules.restrictFunctor (f j)).map (D.toModulesGlueData.chartAdjunct i) ≫
        (restrictCompIso b (f i) hb ((Scheme.Modules.pushforward (f i)).obj (D.mod i))).hom =
      (restrictCompIso b (f i) hb D.glued).hom ≫ (Scheme.Modules.restrictFunctor b).map
        ((Scheme.Modules.restrictFunctor (f i)).map (D.toModulesGlueData.chartAdjunct i)) :=
    restrictCompIso_naturality b (f i) hb (D.toModulesGlueData.chartAdjunct i)
  have key : (restrictChartIso (f i) (D.chartIso i) b hb).hom =
      (Scheme.Modules.restrictFunctor (f j)).map (D.toModulesGlueData.chartAdjunct i) ≫
        (restrictChartIso (f i)
          ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i)) b hb).hom := by
    show (restrictCompIso b (f i) hb D.glued).hom ≫
        (Scheme.Modules.restrictFunctor b).map (D.chartIso i).hom =
      (Scheme.Modules.restrictFunctor (f j)).map (D.toModulesGlueData.chartAdjunct i) ≫
        (restrictCompIso b (f i) hb ((Scheme.Modules.pushforward (f i)).obj (D.mod i))).hom ≫
          (Scheme.Modules.restrictFunctor b).map
            ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i)).hom
    rw [hci, hmc, ← Category.assoc,  ← hnat, Category.assoc]
  show (restrictChartIso (f i) (D.chartIso i) b hb).hom ≫ σ.hom =
    (Scheme.Modules.restrictFunctor (f j)).map (D.toModulesGlueData.chartAdjunct i) ≫
      (restrictChartIso (f i)
        ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i)) b hb).hom ≫ σ.hom
  rw [key, Category.assoc]

/-- The comparison of the glueing datum over the range of the `j`-th chart, read through the two
chart comparisons, is `AlgebraicGeometry.RestrictIsoGlueData.nestedComparison` restricted along
the factorisation of that range.  This is
`AlgebraicGeometry.restrictChartIso_trans` at the factorisation. -/
private theorem restrictChartIso_nestedComparison :
    restrictChartIso (f j) (D.nestedComparison i j hb σ)
        (openLift (f j) (le_refl (f j).opensRange))
        (openLift_comp (f j) (le_refl (f j).opensRange)) =
      openLiftRestrictIso (f i) (D.mod i) (opensRange_le_of_comp (f i) hb) ≪≫
        restrictChartIso b σ (openLift (f j) (le_refl (f j).opensRange))
          (openLift_comp_eq (f i) hb (le_refl (f j).opensRange)) :=
  restrictChartIso_trans (f i) b hb
    ((Scheme.Modules.restrictFunctorAdjCounitIso (f i)).app (D.mod i)) σ
    (openLift (f j) (le_refl (f j).opensRange))
    (openLift_comp (f j) (le_refl (f j).opensRange))
    (openLift_comp_eq (f i) hb (le_refl (f j).opensRange))

/-- **The comparison isomorphisms of two nested charts agree.**  Let the `j`-th chart factor
through the `i`-th one, `b ≫ f i = f j`, and let `σ` identify the restriction of the `i`-th
module along `b` with the `j`-th module.  If `σ` is -- through the chart comparisons
`AlgebraicGeometry.openLiftRestrictIso` -- the identification the glueing datum carries over the
range of the `j`-th chart, then restricting the `i`-th comparison isomorphism of the glued module
along `b` and following it with `σ` gives the `j`-th comparison isomorphism. -/
theorem restrictChartIso_chartIso
    (hσ : D.iso i j (opensRange_le_of_comp (f i) hb) le_rfl =
      restrictPushforwardIsoOfRestrictIso (f i) (f j) (D.mod i) (D.mod j)
        (opensRange_le_of_comp (f i) hb) le_rfl
        (restrictChartIso b σ (openLift (f j) (le_refl (f j).opensRange))
          (openLift_comp_eq (f i) hb (le_refl (f j).opensRange)))) :
    restrictChartIso (f i) (D.chartIso i) b hb ≪≫ σ = D.chartIso j := by
  have hk : openLift (f j) (le_refl (f j).opensRange) ≫ f j = ((f j).opensRange).ι :=
    openLift_comp (f j) (le_refl (f j).opensRange)
  have hij : (f j).opensRange ≤ (f i).opensRange := opensRange_le_of_comp (f i) hb
  -- the glueing datum over the range of the `j`-th chart, after the `j`-th chart comparison
  have hmid : (D.iso i j hij le_rfl).hom ≫
        (openLiftRestrictIso (f j) (D.mod j) (le_refl (f j).opensRange)).hom =
      (restrictChartIso (f j) (D.nestedComparison i j hb σ)
        (openLift (f j) (le_refl (f j).opensRange)) hk).hom := by
    rw [D.restrictChartIso_nestedComparison i j hb σ, hσ,
      restrictPushforwardIsoOfRestrictIso]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  -- the identity over the range of the `j`-th chart
  have hrange : (Scheme.Modules.restrictFunctor ((f j).opensRange).ι).map
          (D.toModulesGlueData.chartAdjunct i) ≫
        (restrictChartIso (f j) (D.nestedComparison i j hb σ)
          (openLift (f j) (le_refl (f j).opensRange)) hk).hom =
      (Scheme.Modules.restrictFunctor ((f j).opensRange).ι).map
          (D.toModulesGlueData.chartAdjunct j) ≫
        (openLiftRestrictIso (f j) (D.mod j) (le_refl (f j).opensRange)).hom := by
    rw [← hmid, ← Category.assoc,
      D.restrictFunctor_map_chartAdjunct_comp_iso i j hij]
  -- transport the identity back along the factorisation, which is an isomorphism
  have := Scheme.Modules.faithful_restrictFunctor_of_isIso
    (openLift (f j) (le_refl (f j).opensRange))
  refine Iso.ext ((D.restrictChartIso_chartIso_hom_eq i j hb σ).trans
    (Eq.trans ?_ (D.toModulesGlueData.restrictFunctor_map_chartAdjunct j)))
  refine (Scheme.Modules.restrictFunctor
    (openLift (f j) (le_refl (f j).opensRange))).map_injective ?_
  refine (cancel_epi (restrictCompIso (openLift (f j) (le_refl (f j).opensRange)) (f j) hk
    D.glued).hom).mp ?_
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    ← restrictCompIso_naturality _ _ hk, ← restrictCompIso_naturality _ _ hk, Category.assoc,
    Category.assoc]
  exact hrange

end Nested

end RestrictIsoGlueData

end AlgebraicGeometry

end
