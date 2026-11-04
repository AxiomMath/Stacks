module

public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueChartAdjunct
public import StacksFrontier.AlgebraicGeometry.Descent.ZariskiModuleChartComparison

/-!
# The glueing datum of a descent datum along an open covering

For a covering of a scheme `S` by open subschemes `W i`, a descent datum for the pullback
pseudofunctor of sheaves of modules is turned here into a glueing datum of sheaves of
`O_S`-modules in the sense of Stacks 00AM, namely
`Stacks.SheafOfModules.ModulesGlueData`.  Its glued module is the candidate for the effectivity
assertion of Stacks 023E, whose reduction to the single statement
`AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens` is in
`StacksFrontier/AlgebraicGeometry/Descent/ZariskiQuasicoherentDescent.lean`.

The transition of the glueing datum over an open `V` contained in two members of the covering is
the sections map of `AlgebraicGeometry.descentTransRestrict`, the transition of the descent datum
read on the restrictions to `V` of the pushed-forward components.  That it is an isomorphism, and
that it satisfies the cocycle condition, come from `DescentData.hom_self` and
`DescentData.hom_comp`; that it commutes with restriction to a smaller open comes from
`DescentData.pullHom_hom` through `AlgebraicGeometry.restrictLocal_descentTransRestrict`.

## Main definitions

* `AlgebraicGeometry.descentTransRestrictIso`: the transition over `V`, as an isomorphism of the
  restrictions to `V` of the pushed-forward components.
* `AlgebraicGeometry.descentTransEquiv`: the same, read on sections over `V` as a linear
  equivalence.
* `AlgebraicGeometry.descentGlueTrans`: that linear equivalence with the overlap hypotheses
  phrased by the ranges of the charts, which is the shape the glueing datum asks for.
* `AlgebraicGeometry.modulesGlueDataOfDescentData`: **the glueing datum of a descent datum along
  a covering by open subschemes**.

## Main results

* `AlgebraicGeometry.localAppFun_descentTransRestrict_chartAdjunct`: **the chart comparisons of
  the glued module are compatible with the transitions of the descent datum**, on sections.  This
  is the compatibility that an isomorphism `toDescentData.obj glued ≅ D` requires, read on
  sections over the opens contained in two members of the covering.
* `AlgebraicGeometry.descentTransPullback_chartAdjunct`: the same compatibility **as morphisms of
  sheaves of modules**.
* `AlgebraicGeometry.gluedDescentDataIso`: **the canonical descent datum of the glued module is
  the given descent datum**.
* `AlgebraicGeometry.essSurj_toDescentData_opens`: **descent of sheaves of modules along a family
  of open subschemes is effective** — `CategoryTheory.Pseudofunctor.toDescentData` of the pullback
  pseudofunctor is essentially surjective for such a family.  This is the statement that
  `AlgebraicGeometry.ZariskiEssSurjToDescentDataOpens` asks for.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Limits
open Stacks.SheafOfModules Pseudofunctor.LocallyDiscreteOpToCat
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {ιt : Type u} {W : ιt → S.Opens}
  (D : modulePullbackPseudofunctor.DescentData (fun i ↦ (W i).ι))

/-- An open contained in the range of the inclusion of an open subscheme is contained in that
open subscheme.  `Stacks.SheafOfModules.ModulesGlueData` is stated for a family of open
immersions and so phrases its overlaps as `V ≤ (f i).opensRange`, whereas the transitions of a
descent datum along a family of opens are phrased as `V ≤ W i`; the two are equal, but only
propositionally, so the passage between them is spelled out. -/
lemma le_of_le_opensRange_ι {V U : S.Opens} (hV : V ≤ U.ι.opensRange) : V ≤ U := by
  rwa [Scheme.Opens.opensRange_ι] at hV

/-- The converse of `AlgebraicGeometry.le_of_le_opensRange_ι`. -/
private lemma le_opensRange_ι_of_le {V U : S.Opens} (hV : V ≤ U) : V ≤ U.ι.opensRange := by
  rwa [Scheme.Opens.opensRange_ι]

/-- The transition of a descent datum over an open `V` contained in two members of the covering,
as an isomorphism of the restrictions to `V` of the pushed-forward components.  It is an
isomorphism because the transitions compose and the transition from a member to itself is the
identity. -/
noncomputable def descentTransRestrictIso (i j : ιt) {V : S.Opens} (hi : V ≤ W i)
    (hj : V ≤ W j) :
    Scheme.Modules.restrict ((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)) V.ι ≅
      Scheme.Modules.restrict ((Scheme.Modules.pushforward (W j).ι).obj (D.obj j)) V.ι where
  hom := descentTransRestrict D i j hi hj
  inv := descentTransRestrict D j i hj hi
  hom_inv_id :=
    (descentTransRestrict_comp D i j i hi hj hi).trans (descentTransRestrict_self D i hi hi)
  inv_hom_id :=
    (descentTransRestrict_comp D j i j hj hi hj).trans (descentTransRestrict_self D j hj hj)

/-- The transition of a descent datum over `V`, read on sections over `V` as a linear
equivalence.  This is the `trans` field of the glueing datum. -/
noncomputable def descentTransEquiv (i j : ιt) {V : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j) :
    openSections (W i).ι (D.obj i) V ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (W j).ι (D.obj j) V :=
  localAppEquiv (descentTransRestrictIso D i j hi hj) V le_rfl

/-- Equal sections maps are equal on every section. -/
private lemma localAppFun_eq_of_localApp_eq {A B : S.Modules} {W₀ W₁ : S.Opens}
    {φ : Scheme.Modules.restrict A W₀.ι ⟶ Scheme.Modules.restrict B W₀.ι}
    {ψ : Scheme.Modules.restrict A W₁.ι ⟶ Scheme.Modules.restrict B W₁.ι} {V : S.Opens}
    {hV : V ≤ W₀} {hV' : V ≤ W₁} (h : localApp φ V hV = localApp ψ V hV')
    (s : ToType (A.val.obj (op V))) :
    localAppFun φ V hV s = localAppFun ψ V hV' s :=
  ConcreteCategory.congr_hom h s

/-- The sections map over `V'` of the transition over `V'` is the sections map over `V'` of the
transition over the larger open `V`. -/
lemma localApp_descentTransRestrict_le (i j : ιt) {V V' : S.Opens} (hi : V ≤ W i)
    (hj : V ≤ W j) (hV' : V' ≤ V) :
    localApp (descentTransRestrict D i j (hV'.trans hi) (hV'.trans hj)) V' le_rfl =
      localApp (descentTransRestrict D i j hi hj) V' hV' :=
  ((localApp_restrictLocal (descentTransRestrict D i j hi hj) hV').trans
    (congrArg (fun ψ ↦ localApp ψ V' le_rfl)
      (restrictLocal_descentTransRestrict D i j hi hj hV'))).symm

/-- `AlgebraicGeometry.localApp_descentTransRestrict_le`, read on an individual section. -/
lemma localAppFun_descentTransRestrict_le (i j : ιt) {V V' : S.Opens} (hi : V ≤ W i)
    (hj : V ≤ W j) (hV' : V' ≤ V)
    (s : ToType (((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)).val.obj (op V'))) :
    localAppFun (descentTransRestrict D i j (hV'.trans hi) (hV'.trans hj)) V' le_rfl s =
      localAppFun (descentTransRestrict D i j hi hj) V' hV' s :=
  localAppFun_eq_of_localApp_eq
    (localApp_descentTransRestrict_le D i j hi hj hV') s

/-- **The transitions commute with restriction of sections.**  This is the `trans_map` field of
the glueing datum. -/
lemma localAppFun_descentTransRestrict_map (i j : ιt) {V V' : S.Opens} (hi : V ≤ W i)
    (hj : V ≤ W j) (hV' : V' ≤ V)
    (s : ToType (((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)).val.obj (op V))) :
    localAppFun (descentTransRestrict D i j (hV'.trans hi) (hV'.trans hj)) V' le_rfl
        (((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)).val.map (homOfLE hV').op s) =
      ((Scheme.Modules.pushforward (W j).ι).obj (D.obj j)).val.map (homOfLE hV').op
        (localAppFun (descentTransRestrict D i j hi hj) V le_rfl s) :=
  (localAppFun_descentTransRestrict_le D i j hi hj hV'
      (((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)).val.map (homOfLE hV').op s)).trans
    (localAppFun_naturality (descentTransRestrict D i j hi hj) le_rfl hV' (homOfLE hV') s).symm

/-- **The cocycle condition for the transitions, read on sections.**  This is the `trans_trans`
field of the glueing datum. -/
lemma localAppFun_descentTransRestrict_comp (i j k : ιt) {V : S.Opens} (hi : V ≤ W i)
    (hj : V ≤ W j) (hk : V ≤ W k)
    (s : ToType (((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)).val.obj (op V))) :
    localAppFun (descentTransRestrict D j k hj hk) V le_rfl
        (localAppFun (descentTransRestrict D i j hi hj) V le_rfl s) =
      localAppFun (descentTransRestrict D i k hi hk) V le_rfl s :=
  (localAppFun_comp (descentTransRestrict D i j hi hj)
      (descentTransRestrict D j k hj hk) V le_rfl s).symm.trans
    (localAppFun_eq_of_localApp_eq (congrArg (fun ψ ↦ localApp ψ V le_rfl)
      (descentTransRestrict_comp D i j k hi hj hk)) s)

/-- `AlgebraicGeometry.descentTransEquiv` is the sections map of the transition. -/
lemma descentTransEquiv_apply (i j : ιt) {V : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j)
    (s : ToType (openSections (W i).ι (D.obj i) V)) :
    descentTransEquiv D i j hi hj s =
      localAppFun (descentTransRestrict D i j hi hj) V le_rfl s := rfl

/-- The transition of a descent datum over an open `V`, with the overlap hypotheses in the form
`Stacks.SheafOfModules.ModulesGlueData.trans` asks for: a bound by the range of a chart rather
than by the member of the covering itself. -/
noncomputable def descentGlueTrans (i j : ιt) {V : S.Opens}
    (hi : V ≤ (W i).ι.opensRange) (hj : V ≤ (W j).ι.opensRange) :
    openSections (W i).ι (D.obj i) V ≃ₗ[ToType (S.ringCatSheaf.obj.obj (op V))]
      openSections (W j).ι (D.obj j) V :=
  descentTransEquiv D i j (le_of_le_opensRange_ι hi) (le_of_le_opensRange_ι hj)

/-- `AlgebraicGeometry.descentGlueTrans` is the sections map of the transition. -/
@[simp] lemma descentGlueTrans_apply (i j : ιt) {V : S.Opens}
    (hi : V ≤ (W i).ι.opensRange) (hj : V ≤ (W j).ι.opensRange)
    (s : ToType (openSections (W i).ι (D.obj i) V)) :
    descentGlueTrans D i j hi hj s =
      localAppFun (descentTransRestrict D i j (le_of_le_opensRange_ι hi)
        (le_of_le_opensRange_ι hj)) V le_rfl s :=
  descentTransEquiv_apply D i j (le_of_le_opensRange_ι hi) (le_of_le_opensRange_ι hj) s

/-- **The transitions commute with restriction of sections**, in the form that
`Stacks.SheafOfModules.ModulesGlueData.trans_map` asks for. -/
lemma descentGlueTrans_map (i j : ιt) {V V' : S.Opens} (hi : V ≤ (W i).ι.opensRange)
    (hj : V ≤ (W j).ι.opensRange) (hV' : V' ≤ V)
    (s : ToType (openSections (W i).ι (D.obj i) V)) :
    descentGlueTrans D i j (hV'.trans hi) (hV'.trans hj)
        (((Scheme.Modules.pushforward (W i).ι).obj (D.obj i)).val.map (homOfLE hV').op s) =
      ((Scheme.Modules.pushforward (W j).ι).obj (D.obj j)).val.map (homOfLE hV').op
        (descentGlueTrans D i j hi hj s) :=
  (descentGlueTrans_apply D i j (hV'.trans hi) (hV'.trans hj) _).trans
    ((localAppFun_descentTransRestrict_map D i j (le_of_le_opensRange_ι hi)
        (le_of_le_opensRange_ι hj) hV' s).trans
      (congrArg (fun x ↦ ((Scheme.Modules.pushforward (W j).ι).obj (D.obj j)).val.map
        (homOfLE hV').op x) (descentGlueTrans_apply D i j hi hj s).symm))

/-- **The cocycle condition for the transitions**, in the form that
`Stacks.SheafOfModules.ModulesGlueData.trans_trans` asks for. -/
lemma descentGlueTrans_trans (i j k : ιt) {V : S.Opens} (hi : V ≤ (W i).ι.opensRange)
    (hj : V ≤ (W j).ι.opensRange) (hk : V ≤ (W k).ι.opensRange)
    (s : ToType (openSections (W i).ι (D.obj i) V)) :
    descentGlueTrans D j k hj hk (descentGlueTrans D i j hi hj s) =
      descentGlueTrans D i k hi hk s :=
  (congrArg (fun x ↦ descentGlueTrans D j k hj hk x)
      (descentGlueTrans_apply D i j hi hj s)).trans
    ((descentGlueTrans_apply D j k hj hk _).trans
      ((localAppFun_descentTransRestrict_comp D i j k (le_of_le_opensRange_ι hi)
          (le_of_le_opensRange_ι hj) (le_of_le_opensRange_ι hk) s).trans
        (descentGlueTrans_apply D i k hi hk s).symm))

/-- **The glueing datum of a descent datum along a covering by open subschemes.**  The members
are the components of the descent datum, and the comparison isomorphism over an open `V`
contained in two members is the transition of the descent datum over `V`, read on sections.

Its glued module, `Stacks.SheafOfModules.ModulesGlueData.glued`, is the module that the
effectivity assertion of Stacks 023E asks for, and
`Stacks.SheafOfModules.ModulesGlueData.chartAdjunct` compares it with the components. -/
noncomputable def modulesGlueDataOfDescentData :
    ModulesGlueData S (fun i ↦ (W i).ι) where
  mod := D.obj
  trans := descentGlueTrans D
  trans_map := descentGlueTrans_map D
  trans_trans := descentGlueTrans_trans D

/-- The transition of the glueing datum, as a sections map. -/
@[simp] lemma modulesGlueDataOfDescentData_trans (i j : ιt) {V : S.Opens}
    (hi : V ≤ (W i).ι.opensRange) (hj : V ≤ (W j).ι.opensRange)
    (s : ToType (openSections (W i).ι (D.obj i) V)) :
    (modulesGlueDataOfDescentData D).trans i j hi hj s =
      localAppFun (descentTransRestrict D i j (le_of_le_opensRange_ι hi)
        (le_of_le_opensRange_ι hj)) V le_rfl s :=
  descentGlueTrans_apply D i j hi hj s

/-- **The chart comparisons of the glued module are compatible with the transitions**, on
sections over an open `V'` contained in an open `V` contained in two members of the covering. -/
lemma localAppFun_descentTransRestrict_chartAdjunct (i j : ιt) {V V' : S.Opens} (hi : V ≤ W i)
    (hj : V ≤ W j) (hV' : V' ≤ V)
    (s : ToType ((modulesGlueDataOfDescentData D).glued.val.obj (op V'))) :
    localAppFun (descentTransRestrict D i j hi hj) V' hV'
        (((modulesGlueDataOfDescentData D).chartAdjunct i).app V' s) =
      ((modulesGlueDataOfDescentData D).chartAdjunct j).app V' s :=
  (localAppFun_descentTransRestrict_le D i j hi hj hV' _).symm.trans
    ((modulesGlueDataOfDescentData_trans D i j (le_opensRange_ι_of_le (hV'.trans hi))
        (le_opensRange_ι_of_le (hV'.trans hj)) _).symm.trans
      ((modulesGlueDataOfDescentData D).trans_chartAdjunct i j
        (le_opensRange_ι_of_le (hV'.trans hi)) (le_opensRange_ι_of_le (hV'.trans hj)) s))

/-- **The chart comparisons of the glued module are compatible with the transitions of the
descent datum, as morphisms of sheaves of modules.**  Over an open `V` contained in two members
of the covering, the pullback to `V` of the `i`-th chart comparison, followed by the transition
of the descent datum from `i` to `j`, is the pullback to `V` of the `j`-th chart comparison.

This is the morphism-level form of
`AlgebraicGeometry.localAppFun_descentTransRestrict_chartAdjunct`, obtained from it in three
steps: `AlgebraicGeometry.pullback_map_comp_eq` reduces an identity of morphisms of pullbacks to
one of morphisms of restrictions, `AlgebraicGeometry.restrictFunctor_map_comp_eq` reduces that to
the identities of the sections maps over the opens contained in `V`, and
`AlgebraicGeometry.app_comp_localApp` reduces each of those to the identity on sections. -/
lemma descentTransPullback_chartAdjunct (i j : ιt) {V : S.Opens} (hi : V ≤ W i)
    (hj : V ≤ W j) :
    (Scheme.Modules.pullback V.ι).map ((modulesGlueDataOfDescentData D).chartAdjunct i) ≫
        descentTransPullback D i j hi hj =
      (Scheme.Modules.pullback V.ι).map ((modulesGlueDataOfDescentData D).chartAdjunct j) :=
  pullback_map_comp_eq V.ι _ _ _
    (restrictFunctor_map_comp_eq _ _ _ fun _V' hV' ↦
      app_comp_localApp hV' _ _ _
        (localAppFun_descentTransRestrict_chartAdjunct D i j hi hj hV'))

/-- **The chart comparison of the glued module on a member of the covering.**  The pullback of
the glued module along the inclusion of `W i` is the `i`-th component of the descent datum.  This
is `Stacks.SheafOfModules.ModulesGlueData.chartIso` carried from restriction to pullback. -/
noncomputable def gluedChartIso (i : ιt) :
    (modulePullbackPseudofunctor.map (W i).ι.op.toLoc).toFunctor.obj
        (modulesGlueDataOfDescentData D).glued ≅ D.obj i :=
  ((Scheme.Modules.restrictFunctorIsoPullback (W i).ι).app
      (modulesGlueDataOfDescentData D).glued).symm ≪≫
    (modulesGlueDataOfDescentData D).chartIso i

/-- The chart comparison is the pullback of the transposed comparison
`Stacks.SheafOfModules.ModulesGlueData.chartAdjunct` followed by the counit comparison. -/
lemma gluedChartIso_hom (i : ιt) :
    (gluedChartIso D i).hom =
      (modulePullbackPseudofunctor.map (W i).ι.op.toLoc).toFunctor.map
          ((modulesGlueDataOfDescentData D).chartAdjunct i) ≫
        (pushforwardCounitIso (W i) (D.obj i)).hom :=
  restrictFunctorIsoPullback_symm_trans_hom (W i) _ _
    ((modulesGlueDataOfDescentData D).restrictFunctor_map_chartAdjunct i)

/-- **The chart comparisons form a morphism of descent data over an open contained in two
members of the covering.**  This is the compatibility condition of
`CategoryTheory.Pseudofunctor.DescentData.isoMk` at the object `V`, with the gluing morphism of
the canonical descent datum of the glued module written out. -/
lemma gluedChartIso_comm (i j : ιt) {V : S.Opens} (hi : V ≤ W i) (hj : V ≤ W j) :
    (modulePullbackPseudofunctor.map (S.homOfLE hi).op.toLoc).toFunctor.map
          (gluedChartIso D i).hom ≫
        D.hom V.ι (S.homOfLE hi) (S.homOfLE hj)
          (Scheme.homOfLE_ι S hi) (Scheme.homOfLE_ι S hj) =
      ((mapCompIso (F := modulePullbackPseudofunctor) (Scheme.homOfLE_ι S hi)
            (modulesGlueDataOfDescentData D).glued).inv ≫
          (mapCompIso (F := modulePullbackPseudofunctor) (Scheme.homOfLE_ι S hj)
            (modulesGlueDataOfDescentData D).glued).hom) ≫
        (modulePullbackPseudofunctor.map (S.homOfLE hj).op.toLoc).toFunctor.map
          (gluedChartIso D j).hom := by
  rw [gluedChartIso_hom, gluedChartIso_hom]
  exact comm_of_mapCompIso (F := modulePullbackPseudofunctor)
    (h₁ := Scheme.homOfLE_ι S hi) (h₂ := Scheme.homOfLE_ι S hj)
    (χ₁ := (modulesGlueDataOfDescentData D).chartAdjunct i)
    (χ₂ := (modulesGlueDataOfDescentData D).chartAdjunct j)
    (c₁ := (pushforwardCounitIso (W i) (D.obj i)).hom)
    (c₂ := (pushforwardCounitIso (W j) (D.obj j)).hom)
    (d := D.hom V.ι (S.homOfLE hi) (S.homOfLE hj)
      (Scheme.homOfLE_ι S hi) (Scheme.homOfLE_ι S hj))
    (t := descentTransPullback D i j hi hj)
    (O₁ := (openChartIso (Scheme.homOfLE_ι S hi) (D.obj i)).hom)
    (O₂ := (openChartIso (Scheme.homOfLE_ι S hj) (D.obj j)).hom)
    (hO₁ := openChartIso_hom_eq (Scheme.homOfLE_ι S hi) (D.obj i))
    (hO₂ := openChartIso_hom_eq (Scheme.homOfLE_ι S hj) (D.obj j))
    (ht := openChartIso_hom_comp_hom D i j hi hj)
    (hχ := descentTransPullback_chartAdjunct D i j hi hj)

/-- **The canonical descent datum of the glued module is the given descent datum.**  The chart
comparisons `AlgebraicGeometry.gluedChartIso` assemble into an isomorphism of descent data.

The compatibility condition over an arbitrary scheme mapping to two members of the covering is
reduced by `CategoryTheory.Pseudofunctor.DescentData.comm_of_chosenPullback` to the condition
over the chosen fibre products, which for two open subschemes are their intersections
(`AlgebraicGeometry.opensChosenPullback`); there it is `AlgebraicGeometry.gluedChartIso_comm`. -/
noncomputable def gluedDescentDataIso :
    (modulePullbackPseudofunctor.toDescentData (fun i ↦ (W i).ι)).obj
        (modulesGlueDataOfDescentData D).glued ≅ D := by
  refine Pseudofunctor.DescentData.isoMk (gluedChartIso D) ?_
  refine Pseudofunctor.DescentData.comm_of_chosenPullback
    (D₁ := (modulePullbackPseudofunctor.toDescentData (fun i ↦ (W i).ι)).obj
      (modulesGlueDataOfDescentData D).glued) (D₂ := D)
    (fun i j ↦ opensChosenPullback (W i) (W j)) (fun i ↦ (gluedChartIso D i).hom) ?_
  intro i j
  exact gluedChartIso_comm D i j inf_le_left inf_le_right

/-- **Descent of sheaves of modules along a family of open subschemes is effective.**  For every
family of open subschemes of a scheme, indexed in the scheme's own universe, the functor
`CategoryTheory.Pseudofunctor.toDescentData` of the pullback pseudofunctor of sheaves of modules
is essentially surjective: every descent datum is the canonical datum of the module glued from
it.  No hypothesis that the family covers is needed. -/
instance essSurj_toDescentData_opens :
    (modulePullbackPseudofunctor.toDescentData (fun i ↦ (W i).ι)).EssSurj where
  mem_essImage D := ⟨(modulesGlueDataOfDescentData D).glued, ⟨gluedDescentDataIso D⟩⟩

end AlgebraicGeometry

end
