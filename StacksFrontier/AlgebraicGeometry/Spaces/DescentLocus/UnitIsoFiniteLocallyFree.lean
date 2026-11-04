module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardPushforwardUnitIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleEtaleBaseChangeHFace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedIsoLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleSliceComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# The unit `N ⟶ g_*g^*N` at a finite locally free module

Let `g : W ⟶ V` be a morphism of algebraic spaces whose structure map `𝒪_V ⟶ g_*𝒪_W` is an
isomorphism, and let `N` be a finite locally free `𝒪_V`-module.  The proof of Stacks 0D23 uses
that the canonical map `N ⟶ g_*g^*N`, the unit of the adjunction `g^* ⊣ g_*` of Stacks 03LU, is
then an isomorphism (the projection formula for a finite locally free module).  This file proves
it, together with the consequence used there: a module `M ≅ g^*N` has `g_*M ≅ N`, finite
locally free.

## Main results

All in the namespace `AlgebraicGeometry.Space.DescentStratum`:

* `isIso_modulePullback_map_unit_app_iff`: across an étale base change `h : U ⟶ V`, the unit of
  `g` at `N` is invertible after `h^*` exactly when the unit of the base change of `g` is
  invertible at `h^*N`.
* `isIso_modulePullback_chartToSpace_map_unit_app`: the unit is invertible after pullback to a
  chart on which `N` is free on a finite basis.
* `isIso_modulePullbackAdjunction_unit_app_of_isFiniteLocallyFree`: the unit is an isomorphism at
  every finite locally free module.
* `isFiniteLocallyFree_modulePushforward_of_iso_modulePullback`: if `M ≅ g^*N`, then `g_*M` is
  finite locally free and isomorphic to `N`.

## Implementation notes

The argument is étale local on `V`.  Isomorphisms of `𝒪_V`-modules are detected after pullback
to the members of an étale covering by scheme charts
(`AlgebraicGeometry.Space.isIso_of_isIso_modulePullback_chartToSpace`), so take a covering on
whose members `N` is free on a finite basis.  For a chart `h : U ⟶ V` with base change
`g' : W ×_V U ⟶ U`, the unit of `g'^* ⊣ g'_*` at `h^*N`, followed by `g'_*` of the comparison of
composite inverse images, is `h^*` of the unit at `N` followed by the base change map
`h^*g_* ⟶ g'_*h'^*` (`CategoryTheory.unit_mateEquiv`, the base change map being a mate by
`AlgebraicGeometry.Space.moduleBaseChangeMap_eq_mateEquiv`); the base change map is invertible
for étale `h` (`AlgebraicGeometry.Space.isIso_moduleBaseChangeMap_of_isEtale`).  So the unit at
`N` is invertible after `h^*` exactly when the unit of `g'` is invertible at `h^*N`.  Applied to
`𝒪_V`, whose unit is invertible by
`AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_unit_app_unit`, this gives the unit of
`g'` at `h^*𝒪_V`; and `h^*N` is a finite coproduct of copies of `h^*𝒪_V` (read through the
slice comparison `AlgebraicGeometry.Space.chartModuleRestrictionSliceIso`), at which the unit is
invertible because `g'^*` preserves colimits and `g'_*` is additive.  No flat base change and no
local computation of `g_*` is used.

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space.DescentStratum

universe u

section Generic

/-- For an adjunction `L ⊣ R` and a colimit cocone `c` whose image under `L` and then `R` is
again a colimit, the unit is invertible at the colimit point as soon as it is invertible at every
object of the diagram. -/
private theorem isIso_unit_app_of_isColimit {C D J : Type*} [Category C] [Category D]
    [Category J] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {K : J ⥤ C} {c : Cocone K}
    (hc : IsColimit c) (hd : IsColimit (R.mapCocone (L.mapCocone c)))
    (h : ∀ j, IsIso (adj.unit.app (K.obj j))) : IsIso (adj.unit.app c.pt) := by
  let w : K ≅ (K ⋙ L) ⋙ R :=
    NatIso.ofComponents (fun j => asIso (adj.unit.app (K.obj j)))
      (fun f => adj.unit.naturality (K.map f))
  have e : adj.unit.app c.pt = (IsColimit.coconePointsIsoOfNatIso hc hd w).hom := by
    refine hc.hom_ext fun j => ?_
    rw [IsColimit.comp_coconePointsIsoOfNatIso_hom]
    exact adj.unit.naturality (c.ι.app j)
  rw [e]
  infer_instance

/-- **Units across a mate.**  For adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and a 2-square
`α : G ⋙ L₂ ⟶ L₁ ⋙ H` invertible at `c` whose mate is invertible at `L₁ c`, the image under `G`
of the unit of the first adjunction at `c` is invertible exactly when the unit of the second
adjunction at `G c` is. -/
private theorem isIso_map_unit_app_iff_of_mate {C D C' D' : Type*} [Category C] [Category D]
    [Category C'] [Category D'] {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : C' ⥤ D'} {R₂ : D' ⥤ C'}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {G : C ⥤ C'} {H : D ⥤ D'} (α : TwoSquare G L₁ L₂ H)
    (c : C) (hα : IsIso (α.app c)) (hβ : IsIso ((mateEquiv adj₁ adj₂ α).app (L₁.obj c))) :
    IsIso (G.map (adj₁.unit.app c)) ↔ IsIso (adj₂.unit.app (G.obj c)) := by
  have e := unit_mateEquiv adj₁ adj₂ α c
  simp only [Functor.id_obj] at e
  exact ⟨fun _ => IsIso.of_isIso_fac_right e.symm, fun _ => IsIso.of_isIso_fac_right e⟩

/-- Finite local freeness depends only on the isomorphism class: an isomorphism carries a local
free presentation to one over the same cover with the same finite bases. -/
theorem isFiniteLocallyFree_of_iso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat}
    [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat]
    [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat]
    {M N : _root_.SheafOfModules R} (e : M ≅ N) (h : SheafOfModules.IsFiniteLocallyFree M) :
    SheafOfModules.IsFiniteLocallyFree N := by
  obtain ⟨q, hq, hfin⟩ := h.exists_isFiniteLocallyFreeData
  let q' : _root_.SheafOfModules.LocalGeneratorsData N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi
        ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom }
  refine ⟨q', ⟨fun i ↦ ?_⟩, ⟨fun i ↦ ?_⟩⟩
  · have h₀ : IsIso (q.generators i).π := hq.isIso i
    have h₁ : IsIso ((q.generators i).π ≫
        ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom) := inferInstance
    exact Eq.mpr (congrArg IsIso (_root_.SheafOfModules.GeneratingSections.ofEpi_π
      (q.generators i) ((_root_.SheafOfModules.overFunctor R (q.X i)).mapIso e).hom)) h₁
  · have := hfin.isFiniteType i
    exact ⟨inferInstanceAs (Finite (q.generators i).I)⟩

end Generic

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The unit across an étale base change.**  For `g : W ⟶ V`, an étale `h : U ⟶ V` and the base
change `g' : W ×_V U ⟶ U`, the pullback `h^*` of the unit of `g^* ⊣ g_*` at `N` is invertible
exactly when the unit of `g'^* ⊣ g'_*` at `h^*N` is. -/
theorem isIso_modulePullback_map_unit_app_iff {V W U : AlgebraicSpaces B S hS} (g : W ⟶ V)
    (h : U ⟶ V) (hh : IsEtale B S hS h.hom) (N : Modules.{u, u} B S hS V.1 V.2) :
    IsIso ((modulePullback B S hS h).map ((modulePullbackAdjunction B S hS g).unit.app N)) ↔
      IsIso ((modulePullbackAdjunction B S hS (pullback.snd g h)).unit.app
        ((modulePullback B S hS h).obj N)) := by
  have sq : IsPullback (pullback.fst g h) (pullback.snd g h) g h := IsPullback.of_hasPullback g h
  have hβ := isIso_moduleBaseChangeMap_of_isEtale B S hS (pullback.fst g h) (pullback.snd g h)
    g h sq hh
  rw [moduleBaseChangeMap_eq_mateEquiv] at hβ
  exact isIso_map_unit_app_iff_of_mate (modulePullbackAdjunction B S hS g)
    (modulePullbackAdjunction B S hS (pullback.snd g h))
    (TwoSquare.mk (modulePullback B S hS h) (modulePullback B S hS g)
      (modulePullback B S hS (pullback.snd g h)) (modulePullback B S hS (pullback.fst g h))
      (modulePullbackSquareComparison g h (pullback.snd g h) (pullback.fst g h) sq.w).inv)
    N inferInstance (NatIso.isIso_app_of_isIso _ _)

/-- **The unit at a module free on a finite basis over a chart.**  If the structure map of
`g : W ⟶ V` is an isomorphism and the restriction of `N` to the slice at an étale chart `U` of `V`
is free on a finite basis, then the pullback of the unit `N ⟶ g_*g^*N` to `U` is an
isomorphism. -/
theorem isIso_modulePullback_chartToSpace_map_unit_app {V W : AlgebraicSpaces B S hS}
    (g : W ⟶ V) (hg : IsIso (structureSharp B S hS g)) (N : Modules.{u, u} B S hS V.1 V.2)
    (U : SmallEtale B S hS V.1)
    (σ : ((SheafOfModules.overFunctor (structureRingSheaf B S hS V) U).obj N).GeneratingSections)
    (hσ : IsIso σ.π)
    (hfin : Finite σ.I) :
    IsIso ((modulePullback B S hS (chartToSpace B S hS V U)).map
      ((modulePullbackAdjunction B S hS g).unit.app N)) := by
  have hh := isEtale_chartToSpace B S hS V U
  rw [isIso_modulePullback_map_unit_app_iff g _ hh N]
  let adj := modulePullbackAdjunction B S hS (pullback.snd g (chartToSpace B S hS V U))
  have hiso : ∀ {M M' : Modules.{u, u} B S hS (chartSpace B S hS V U).1
      (chartSpace B S hS V U).2} (_ : M ≅ M'), IsIso (adj.unit.app M) →
        IsIso (adj.unit.app M') := by
    intro M M' e hM
    exact IsIso.of_isIso_fac_left (adj.unit.naturality e.hom)
  have := isIso_modulePullbackAdjunction_unit_app_unit g hg
  have hO := (isIso_modulePullback_map_unit_app_iff g _ hh
    (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V.1 V.2).O))).1
    inferInstance
  have hunit : IsIso (adj.unit.app ((chartModuleSliceReindex B S hS V U).obj
      (SheafOfModules.unit ((structureRingSheaf B S hS V).over U)))) :=
    hiso ((chartModuleRestrictionSliceIso B S hS V U).app _) hO
  have := hσ
  have hc0 : IsColimit (Cofan.mk
      ((SheafOfModules.overFunctor (structureRingSheaf B S hS V) U).obj N)
      (fun j : σ.I => SheafOfModules.ιFree j ≫ σ.π)) :=
    IsColimit.ofIsoColimit (SheafOfModules.isColimitFreeCofan σ.I)
      (Cocone.ext (@asIso _ _ _ _ _ hσ) (by rintro ⟨j⟩; rfl))
  have hF : PreservesColimitsOfShape (Discrete σ.I) (chartModuleSliceReindex B S hS V U) :=
    (chartModuleSliceEquiv B S hS V U).toAdjunction.leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have hc1 := (hF.preservesColimit.preserves hc0).some
  have hL : PreservesColimitsOfShape (Discrete σ.I)
      (modulePullback B S hS (pullback.snd g (chartToSpace B S hS V U))) :=
    adj.leftAdjoint_preservesColimits.preservesColimitsOfShape
  have hc2 := (hL.preservesColimit.preserves hc1).some
  have : PreservesFiniteCoproducts
      (modulePushforward B S hS (pullback.snd g (chartToSpace B S hS V U))) :=
    Functor.preservesFiniteCoproductsOfAdditive _
  have hR : PreservesColimitsOfShape (Discrete σ.I)
      (modulePushforward B S hS (pullback.snd g (chartToSpace B S hS V U))) := inferInstance
  have hc3 := (hR.preservesColimit.preserves hc2).some
  have hpt := isIso_unit_app_of_isColimit adj hc1 hc3 (fun _ => hunit)
  exact hiso ((chartModuleRestrictionSliceIso B S hS V U).app N).symm hpt

/-- **The projection formula step of Stacks 0D23.**  Let `g : W ⟶ V` be a morphism of algebraic
spaces whose structure map `𝒪_V ⟶ g_*𝒪_W` is an isomorphism.  Then for every finite locally free
`𝒪_V`-module `N` the unit `N ⟶ g_*g^*N` of the adjunction `g^* ⊣ g_*` of Stacks 03LU is an
isomorphism. -/
theorem isIso_modulePullbackAdjunction_unit_app_of_isFiniteLocallyFree
    {V W : AlgebraicSpaces B S hS} (g : W ⟶ V) (hg : IsIso (structureSharp B S hS g))
    (N : Modules.{u, u} B S hS V.1 V.2) (hN : SheafOfModules.IsFiniteLocallyFree N) :
    IsIso ((modulePullbackAdjunction B S hS g).unit.app N) := by
  obtain ⟨q, hq, hfin⟩ := hN.exists_isFiniteLocallyFreeData
  exact isIso_of_isIso_modulePullback_chartToSpace B S hS q.coversTop _ fun i =>
    isIso_modulePullback_chartToSpace_map_unit_app g hg N (q.X i) (q.generators i)
      (hq.isIso i) (hfin.isFiniteType i).finite

/-- **The descended module of Stacks 0D23.**  Let `g : W ⟶ V` be a morphism of algebraic spaces
whose structure map `𝒪_V ⟶ g_*𝒪_W` is an isomorphism, `N` a finite locally free `𝒪_V`-module and
`M` an `𝒪_W`-module with `M ≅ g^*N`.  Then `g_*M` is finite locally free and isomorphic to `N`. -/
theorem isFiniteLocallyFree_modulePushforward_of_iso_modulePullback
    {V W : AlgebraicSpaces B S hS} (g : W ⟶ V) (hg : IsIso (structureSharp B S hS g))
    (N : Modules.{u, u} B S hS V.1 V.2) (hN : SheafOfModules.IsFiniteLocallyFree N)
    (M : Modules.{u, u} B S hS W.1 W.2) (e : M ≅ (modulePullback B S hS g).obj N) :
    SheafOfModules.IsFiniteLocallyFree ((modulePushforward B S hS g).obj M) ∧
      Nonempty ((modulePushforward B S hS g).obj M ≅ N) := by
  have := isIso_modulePullbackAdjunction_unit_app_of_isFiniteLocallyFree g hg N hN
  let e' : (modulePushforward B S hS g).obj M ≅ N :=
    (modulePushforward B S hS g).mapIso e ≪≫
      (asIso ((modulePullbackAdjunction B S hS g).unit.app N)).symm
  exact ⟨isFiniteLocallyFree_of_iso e'.symm hN, ⟨e'⟩⟩

end AlgebraicGeometry.Space.DescentStratum

end
