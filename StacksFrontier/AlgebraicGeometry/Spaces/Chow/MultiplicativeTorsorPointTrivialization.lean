module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackCompChartSection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapChartHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitIsoComp

/-!
# The trivialization of `t^*ℒ` attached to a morphism into the multiplicative torsor

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T ⟶ X` be its multiplicative torsor, with the trivialization `α : q^*ℒ ≅ 𝒪_T` of clause (2)
of Stacks 0EQG.  A morphism of algebraic spaces `t : Z ⟶ T` gives the trivialization
`t^*α : (t ≫ q)^*ℒ ≅ 𝒪_Z`.  This file computes it on chart sections: over a commuting square of
étale charts `U ⟶ V` over `t ≫ q`, the pullback of a section `s` of `ℒ` over `V` goes to the
value at the degree-one part of `s` of the point of `T` that `U ⟶ Z ⟶ T` is.

## Main definitions

* `AlgebraicGeometry.Space.torsorPointAt`: the point of `T` with values in an étale chart of `Z`
  given by `t`.
* `AlgebraicGeometry.Space.torsorPointFMap`: the linear map of sections along `t ≫ q` reading the
  degree-one piece of the Laurent algebra through those points.

The trivialization `(t ≫ q)^*ℒ ⟶ 𝒪_Z` itself — the pullback of `α` along `t` composed with the
comparison isomorphisms — is not given a name; it is written out as a composite in the
statements below.

## Main results

* `AlgebraicGeometry.Space.torsorTrivialization_fmap`: the chart formula.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-! ### Locality of sections on the small étale site -/

section Locality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Sections of a sheaf of modules on the small étale site are determined locally around every
point**: two sections over a chart `V` agree as soon as every point of `V` lies in the image of
a chart over `V` on which their restrictions agree. -/
theorem modules_eq_of_forall_point {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} (M : Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F)
    (x y : M.val.obj (op V))
    (h : ∀ z : chartScheme V, ∃ (W : SmallEtale B S hS F) (a : W ⟶ V),
      z ∈ Set.range ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map a)) ∧
        M.val.map a.op x = M.val.map a.op y) :
    x = y := by
  choose W a hz hxy using h
  have hcov : Sieve.ofArrows W a ∈ SmallEtale.topology B S hS F V :=
    (SmallEtale.mem_topology_iff_exists_mem_range B S hS _ _).2 fun z =>
      ⟨_, a z, Sieve.ofArrows_mk _ _ z, hz z⟩
  set LP := M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u}
  have hLsheaf : Presheaf.IsSheaf (SmallEtale.topology B S hS F) LP :=
    GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf
  refine ((isSheaf_iff_isSheaf_of_type (SmallEtale.topology B S hS F) LP).1 hLsheaf
    (Sieve.ofArrows W a) hcov).isSeparatedFor.ext ?_
  rintro Z g ⟨Z', p, q, ⟨i⟩, rfl⟩
  have hcomp : ∀ w : M.val.obj (op V),
      (M.val.map (p ≫ a i).op).hom w = (M.val.map p.op).hom ((M.val.map (a i).op).hom w) :=
    fun w ↦ congrArg (fun φ => φ.hom w) (M.val.map_comp (a i).op p.op)
  show (M.val.map (p ≫ a i).op).hom x = (M.val.map (p ≫ a i).op).hom y
  rw [hcomp, hcomp]
  exact congrArg _ (hxy i)

/-- **`h^*𝒪 ≅ 𝒪` on chart sections**: the chart section of a function `r` goes to its pullback
along the vertical morphism of the chart diagram. -/
theorem modulePullbackUnitIso_hom_chartSection {A A' : AlgebraicSpaces B S hS} (h : A ⟶ A')
    (d : ChartDiagram B S hS A.1 A'.1 h.hom) (r : (structureRingSheaf B S hS A').obj.obj (op d.V)) :
    (modulePullbackUnitIso B S hS h).hom.val.app (op d.U)
        (modulePullbackChartSection B S hS h (SheafOfModules.unit (structureRingSheaf B S hS A'))
          d r) = chartDiagramPullback B S hS h d r := by
  let ξ := modulePullbackHomFMap B S hS h
    (SheafOfModules.unit (structureRingSheaf B S hS A'))
    (SheafOfModules.unit (structureRingSheaf B S hS A)) (modulePullbackUnitIso B S hS h).hom
  have hξ : ∀ r' : (structureRingSheaf B S hS A').obj.obj (op d.V), ξ.app d r' =
      (modulePullbackUnitIso B S hS h).hom.val.app (op d.U)
        (modulePullbackChartSection B S hS h (SheafOfModules.unit (structureRingSheaf B S hS A'))
          d r') := fun r' =>
    (modulePullbackHomFMap_app B S hS h _ _ _ d _).trans
      (congrArg (fun z => (modulePullbackUnitIso B S hS h).hom.val.app (op d.U) z)
        (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS h _ d _))
  have h1 : ξ.app d (1 : (structureRingSheaf B S hS A').obj.obj (op d.V)) =
      (1 : (structureRingSheaf B S hS A).obj.obj (op d.U)) :=
    (hξ 1).trans (modulePullbackUnitIso_hom_val_app_modulePullbackChartSection B S hS h d)
  let one : (SheafOfModules.unit (structureRingSheaf B S hS A')).val.obj (op d.V) :=
    (1 : (structureRingSheaf B S hS A').obj.obj (op d.V))
  have hr : r • one = r := mul_one r
  exact (hξ r).symm.trans ((congrArg (ξ.app d) hr.symm).trans ((ξ.map_smul d r one).trans
    ((congrArg (fun z => chartDiagramPullback B S hS h d r • z) h1).trans
      (mul_one ((chartDiagramPullback B S hS h d).hom r)))))

/-- The chartwise transpose of a morphism out of a module pullback, on chart sections. -/
theorem modulePullbackHomFMap_app_chartSection {A A' : AlgebraicSpaces B S hS} (g : A ⟶ A')
    (M : Modules.{u, u} B S hS A'.1 A'.2) (N : Modules.{u, u} B S hS A.1 A.2)
    (u : (modulePullback B S hS g).obj M ⟶ N) (d : ChartDiagram B S hS A.1 A'.1 g.hom)
    (s : M.val.obj (op d.V)) :
    (modulePullbackHomFMap B S hS g M N u).app d s =
      u.val.app (op d.U) (modulePullbackChartSection B S hS g M d s) :=
  (modulePullbackHomFMap_app B S hS g M N u d s).trans
    (congrArg (fun z => u.val.app (op d.U) z)
      (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS g M d s))

/-- **Two linear maps of sections agreeing on the chart diagrams with affine chart of the target
agree everywhere.** -/
theorem moduleFMap_app_eq_of_isAffine {A A' : AlgebraicSpaces B S hS} (g : A ⟶ A')
    {N : Modules.{u, u} B S hS A.1 A.2} {M M' : Modules.{u, u} B S hS A'.1 A'.2}
    (φ : ModuleFMap B S hS g N M) (ψ : ModuleFMap B S hS g N M') (τ : M ⟶ M')
    (h : ∀ (d : ChartDiagram B S hS A.1 A'.1 g.hom), IsAffine (chartScheme d.V) →
      ∀ s : M.val.obj (op d.V), φ.app d s = ψ.app d (τ.val.app (op d.V) s))
    (d : ChartDiagram B S hS A.1 A'.1 g.hom) (s : M.val.obj (op d.V)) :
    φ.app d s = ψ.app d (τ.val.app (op d.V) s) := by
  refine modules_eq_of_forall_point B S hS _ d.U _ _ fun z => ?_
  obtain ⟨P, hP, hzP, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (Scheme.isBasis_affineOpens ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS A'.1).obj d.V)))
    (show (BigFppfOver.toScheme B S hS).map d.g z ∈ (⊤ : _) from trivial)
  let O := (BigFppfOver.toScheme B S hS).map d.g ⁻¹ᵁ P
  let d₁ := d.restrictOpens O P le_rfl
  have hij : (SmallEtale.toOver B S hS A.1).map (openChartInclusion B S hS A.1 d.U O) ≫ d.g =
      d₁.g ≫ (SmallEtale.toOver B S hS A'.1).map (openChartInclusion B S hS A'.1 d.V P) :=
    (openSubMap_comp_openSubHom d.g O P le_rfl).symm
  refine ⟨_, openChartInclusion B S hS A.1 d.U O, ?_, ?_⟩
  · refine ⟨⟨z, hzP⟩, ?_⟩
    rw [toScheme_map_toOver_map_openChartInclusion]
    rfl
  · have e3 : τ.val.app (op d₁.V) (M.val.map (openChartInclusion B S hS A'.1 d.V P).op s) =
        M'.val.map (openChartInclusion B S hS A'.1 d.V P).op (τ.val.app (op d.V) s) :=
      congrArg (fun φ => (ConcreteCategory.hom φ : _ → _) s)
        (τ.val.naturality (openChartInclusion B S hS A'.1 d.V P).op)
    exact (φ.naturality d d₁ _ _ hij s).symm.trans ((h d₁ hP _).trans
      ((congrArg (ψ.app d₁) e3).trans (ψ.naturality d d₁ _ _ hij (τ.val.app (op d.V) s))))

/-- A linear map of sections takes the same values on two chart diagrams with the same charts and
the same vertical morphism. -/
theorem moduleFMap_app_eq_of_g_eq {A A' : AlgebraicSpaces B S hS} {g : A ⟶ A'}
    {N : Modules.{u, u} B S hS A.1 A.2} {M : Modules.{u, u} B S hS A'.1 A'.2}
    (φ : ModuleFMap B S hS g N M) {U : SmallEtale B S hS A.1} {V : SmallEtale B S hS A'.1}
    (g₁ g₂ : (SmallEtale.toOver B S hS A.1).obj U ⟶ (SmallEtale.toOver B S hS A'.1).obj V)
    (h₁ : U.1.hom ≫ g.hom = yoneda.map g₁ ≫ V.1.hom)
    (h₂ : U.1.hom ≫ g.hom = yoneda.map g₂ ≫ V.1.hom) (hg : g₁ = g₂) (s : M.val.obj (op V)) :
    φ.app ⟨U, V, g₁, h₁⟩ s = φ.app ⟨U, V, g₂, h₂⟩ s := by
  subst hg
  rfl

/-- **The pullback of a trivialization along an étale morphism, on chart sections.**  For
`u : f^*M ⟶ 𝒪_Z` and an étale `p : X' ⟶ Z`, the comparison `(p ≫ f)^*M ≅ p^*f^*M`, then
`p^*u`, then `p^*𝒪_Z ≅ 𝒪_{X'}`, has as chartwise transpose at a chart diagram over `p ≫ f` the
chartwise transpose of `u` at the same diagram with its chart of `X'` read as a chart of `Z`. -/
theorem modulePullbackHomFMap_etaleRestriction {X' Z₀ X₀ : AlgebraicSpaces B S hS}
    (pU : X' ⟶ Z₀) (f : Z₀ ⟶ X₀) (hU : IsEtale B S hS pU.hom) (M : Modules.{u, u} B S hS X₀.1 X₀.2)
    (u : (modulePullback B S hS f).obj M ⟶ SheafOfModules.unit (structureRingSheaf B S hS Z₀))
    (e : ChartDiagram B S hS X'.1 X₀.1 (pU ≫ f).hom) (s : M.val.obj (op e.V)) :
    (modulePullbackHomFMap B S hS (pU ≫ f) M _
      ((modulePullbackCompIso B S hS pU f).inv.app M ≫
        ((modulePullback B S hS pU).map u ≫ (modulePullbackUnitIso B S hS pU).hom))).app e s =
      (modulePullbackHomFMap B S hS f M _ u).app
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s := by
  have hc' := (ChartDiagram.comp B S hS pU f
    (ChartDiagram.etaleUnit B S hS pU hU e.U).g e.g
    (ChartDiagram.etaleUnit B S hS pU hU e.U).comm
    (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).comm).comm
  have h0 := moduleFMap_app_eq_of_g_eq B S hS (A := X') (A' := X₀) (g := pU ≫ f)
    (modulePullbackHomFMap B S hS (pU ≫ f) M _
      ((modulePullbackCompIso B S hS pU f).inv.app M ≫
        ((modulePullback B S hS pU).map u ≫ (modulePullbackUnitIso B S hS pU).hom))) e.g
    ((ChartDiagram.etaleUnit B S hS pU hU e.U).g ≫ e.g) e.comm hc' (Category.id_comp _).symm s
  refine h0.trans ((modulePullbackHomFMap_app_chartSection B S hS (pU ≫ f) M _ _ _ s).trans ?_)
  have e1 := modulePullbackCompIso_inv_chartSection B S hS pU f M
    (ChartDiagram.etaleUnit B S hS pU hU e.U).g e.g
    (ChartDiagram.etaleUnit B S hS pU hU e.U).comm
    (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).comm s
  have e2 := modulePullbackChartSection_map B S hS pU _ u (ChartDiagram.etaleUnit B S hS pU hU e.U)
    (modulePullbackChartSection B S hS f M
      (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s)
  have e3 := modulePullbackUnitIso_hom_chartSection B S hS pU
    (ChartDiagram.etaleUnit B S hS pU hU e.U)
    (u.val.app (op ((smallEtalePostcomp B S hS pU hU).obj e.U))
      (modulePullbackChartSection B S hS f M
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s))
  have e4 := chartDiagramPullback_etaleUnit_apply B S hS pU hU e.U
    (u.val.app (op ((smallEtalePostcomp B S hS pU hU).obj e.U))
      (modulePullbackChartSection B S hS f M
        (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s))
  have key : ((modulePullbackCompIso B S hS pU f).inv.app M ≫
        ((modulePullback B S hS pU).map u ≫ (modulePullbackUnitIso B S hS pU).hom)).val.app
          (op e.U) (modulePullbackChartSection B S hS (pU ≫ f) M
            (ChartDiagram.comp B S hS pU f (ChartDiagram.etaleUnit B S hS pU hU e.U).g e.g
              (ChartDiagram.etaleUnit B S hS pU hU e.U).comm
              (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).comm) s) =
      (modulePullbackUnitIso B S hS pU).hom.val.app (op e.U)
        (((modulePullback B S hS pU).map u).val.app (op e.U)
          (((modulePullbackCompIso B S hS pU f).inv.app M).val.app (op e.U)
            (modulePullbackChartSection B S hS (pU ≫ f) M
              (ChartDiagram.comp B S hS pU f (ChartDiagram.etaleUnit B S hS pU hU e.U).g e.g
                (ChartDiagram.etaleUnit B S hS pU hU e.U).comm
                (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e).comm) s))) := rfl
  refine key.trans ?_
  refine (congrArg (fun z => (modulePullbackUnitIso B S hS pU).hom.val.app (op e.U)
    (((modulePullback B S hS pU).map u).val.app (op e.U) z)) e1).trans ?_
  refine (congrArg (fun z => (modulePullbackUnitIso B S hS pU).hom.val.app (op e.U) z) e2).trans ?_
  refine e3.trans (e4.trans ?_)
  exact (modulePullbackHomFMap_app_chartSection B S hS f M
    (SheafOfModules.unit (structureRingSheaf B S hS Z₀)) u
    (ChartDiagram.postcompSource B S hS pU f hU (pU ≫ f) rfl e) s).symm

/-- **The pullback of a trivialization along a composite, through the coherence of Stacks
03LU.**  For `α₀ : q₀^*M ⟶ 𝒪`, the trivialization of `x'^*M` obtained from `α₀` along `g ≫ t`
is the pullback along `g` of the one obtained along `t`. -/
theorem modulePullbackTriangle_comp_unitIso {Z' Z₀ T₀ X₀ : AlgebraicSpaces B S hS}
    (g : Z' ⟶ Z₀) (t : Z₀ ⟶ T₀) (q₀ : T₀ ⟶ X₀) (M : Modules.{u, u} B S hS X₀.1 X₀.2)
    (α₀ : (modulePullback B S hS q₀).obj M ⟶ SheafOfModules.unit (structureRingSheaf B S hS T₀))
    {x : Z₀ ⟶ X₀} (h : t ≫ q₀ = x) {x' : Z' ⟶ X₀} (h' : g ≫ x = x') (hh : (g ≫ t) ≫ q₀ = x') :
    (modulePullbackTriangle B S hS hh).hom.app M ≫
        (((modulePullback B S hS (g ≫ t)).map α₀) ≫ (modulePullbackUnitIso B S hS (g ≫ t)).hom) =
      (modulePullbackTriangle B S hS h').hom.app M ≫
        ((modulePullback B S hS g).map ((modulePullbackTriangle B S hS h).hom.app M ≫
          ((modulePullback B S hS t).map α₀ ≫ (modulePullbackUnitIso B S hS t).hom)) ≫
          (modulePullbackUnitIso B S hS g).hom) := by
  subst h h'
  have hcoh := congrArg (fun e => e.hom.app M)
    ((modulePushforwardCoherence B S hS).modulePullbackTriangle_comp (f := g) (g := t)
      (p := q₀) (k := g ≫ t) (q := t ≫ q₀) (r := g ≫ t ≫ q₀) rfl rfl rfl hh)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app,
    Category.comp_id] at hcoh
  have hunit := modulePullbackCompIso_hom_app_comp_modulePullbackUnitIso_hom B S hS g t
  have hunit' : (modulePullbackUnitIso B S hS (g ≫ t)).hom =
      (modulePullbackCompIso B S hS g t).inv.app
          (SheafOfModules.unit (structureRingSheaf B S hS T₀)) ≫
        (modulePullback B S hS g).map (modulePullbackUnitIso B S hS t).hom ≫
          (modulePullbackUnitIso B S hS g).hom :=
    (Iso.eq_inv_comp ((modulePullbackCompIso B S hS g t).app
      (SheafOfModules.unit (structureRingSheaf B S hS T₀)))).2 hunit
  have hnat := (modulePullbackCompIso B S hS g t).inv.naturality α₀
  have hgt : (modulePullbackTriangle B S hS (rfl : g ≫ t = g ≫ t)).hom.app
      ((modulePullback B S hS q₀).obj M) =
      (modulePullbackCompIso B S hS g t).inv.app ((modulePullback B S hS q₀).obj M) := by
    rw [modulePullbackTriangle_rfl]
    rfl
  have s1 : (modulePullback B S hS (g ≫ t)).map α₀ ≫ (modulePullbackUnitIso B S hS (g ≫ t)).hom =
      (modulePullbackTriangle B S hS (rfl : g ≫ t = g ≫ t)).hom.app
        ((modulePullback B S hS q₀).obj M) ≫
        ((modulePullback B S hS g).map ((modulePullback B S hS t).map α₀) ≫
          ((modulePullback B S hS g).map (modulePullbackUnitIso B S hS t).hom ≫
            (modulePullbackUnitIso B S hS g).hom)) := by
    rw [hgt, hunit', ← Category.assoc, hnat, Category.assoc]
    rfl
  have s2 : (modulePullback B S hS g).map ((modulePullbackTriangle B S hS
        (rfl : t ≫ q₀ = t ≫ q₀)).hom.app M ≫
        ((modulePullback B S hS t).map α₀ ≫ (modulePullbackUnitIso B S hS t).hom)) =
      (modulePullback B S hS g).map ((modulePullbackTriangle B S hS
        (rfl : t ≫ q₀ = t ≫ q₀)).hom.app M) ≫
        ((modulePullback B S hS g).map ((modulePullback B S hS t).map α₀) ≫
          (modulePullback B S hS g).map (modulePullbackUnitIso B S hS t).hom) :=
    ((modulePullback B S hS g).map_comp _ _).trans
      (congrArg (fun z => (modulePullback B S hS g).map ((modulePullbackTriangle B S hS
        (rfl : t ≫ q₀ = t ≫ q₀)).hom.app M) ≫ z) ((modulePullback B S hS g).map_comp _ _))
  rw [s1, s2]
  have key := congrArg (fun z => z ≫
    ((modulePullback B S hS g).map ((modulePullback B S hS t).map α₀) ≫
      ((modulePullback B S hS g).map (modulePullbackUnitIso B S hS t).hom ≫
        (modulePullbackUnitIso B S hS g).hom))) hcoh
  simpa only [Category.assoc] using key

end Locality

/-! ### The chart of `T` over an affine chart of `X` -/

section AffineChart

variable (V : SmallEtale D.site D.base D.base_mem X) [IsAffine (chartScheme V)]

/-- The étale chart `Spec 𝒜(V) ⟶ T` of `T` over an affine étale chart `V` of `X`. -/
def torsorAffineChart :
    SmallEtale D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj :=
  ⟨CostructuredArrow.mk (torsorOfInvertibleChartToSpace D p hp L hL V),
    (isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem _).1
      (isEtale_of_isPullback_yoneda D.site D.base D.base_mem
        (isPullback_torsorOfInvertible_chart D p hp L hL V).flip
        ((isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem _).2 V.property))⟩

/-- The chart `torsorAffineChart V` lies over `V`: its structure morphism followed by the
projection `T ⟶ X` equals the morphism `Spec 𝒜(V) ⟶ V` followed by the structure morphism of
`V`. -/
theorem torsorAffineChart_comm :
    (torsorAffineChart D p hp L hL V).1.hom ≫ (torsorOfInvertibleProjection D p hp L hL).hom =
      yoneda.map (torsorOfInvertibleChartHom D p hp L hL V) ≫ V.1.hom :=
  (isPullback_torsorOfInvertible_chart D p hp L hL V).w

end AffineChart

section Point

variable {Z : AlgebraicSpaces D.site D.base D.base_mem}
    (t : Z ⟶ torsorOfInvertibleSpace D p hp L hL)

/-- The point of `T` with values in an étale chart `U` of `Z` given by `t`. -/
def torsorPointAt (U : SmallEtale D.site D.base D.base_mem Z.1) :
    RelativeSpecPoint D.site D.base D.base_mem (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL)
      U.obj.left :=
  relativeSpecPointsEquiv D.site D.base D.base_mem _ U.obj.left (yonedaEquiv (U.obj.hom ≫ t.hom))

/-- For a chart diagram `d` of `t ≫ q` with `q : T ⟶ X` the projection, the underlying morphism of
the point `torsorPointAt t d.U` is `d.g` followed by the structure morphism of `d.V`. -/
theorem torsorPointAt_pt (d : ChartDiagram D.site D.base D.base_mem Z.1 X
    (t ≫ torsorOfInvertibleProjection D p hp L hL).hom) :
    yonedaEquiv.symm (torsorPointAt D p hp L hL t d.U).pt = yoneda.map d.g ≫ d.V.obj.hom := by
  rw [← d.comm]
  exact (congrArg yonedaEquiv.symm (yonedaEquiv_comp (d.U.obj.hom ≫ t.hom)
    (torsorOfInvertibleProjection D p hp L hL).hom).symm).trans (Equiv.symm_apply_apply _ _)

/-- The point of `T` attached to `ψ = yoneda.map a ≫ φ` is the pullback along `a` of the point
attached to `φ`. -/
private theorem relativeSpecPointsEquiv_yonedaEquiv_of_comp_eq
    {T T' : BigFppfOver D.site D.base D.base_mem} (a : T' ⟶ T)
    (φ : yoneda.obj T ⟶ (torsorOfInvertibleSpace D p hp L hL).obj)
    (ψ : yoneda.obj T' ⟶ (torsorOfInvertibleSpace D p hp L hL).obj)
    (h : yoneda.map a ≫ φ = ψ) :
    relativeSpecPointsEquiv D.site D.base D.base_mem _ T' (yonedaEquiv ψ) =
      (relativeSpecPointsEquiv D.site D.base D.base_mem _ T (yonedaEquiv φ)).map D.site D.base
        D.base_mem a :=
  (congrArg (relativeSpecPointsEquiv D.site D.base D.base_mem _ T')
    ((congrArg yonedaEquiv h).symm.trans (yonedaEquiv_naturality _ _).symm)).trans
    (relativeSpecPointsEquiv_map D.site D.base D.base_mem _ _ _)

/-- The points attached to `t` are compatible with morphisms of charts. -/
theorem torsorPointAt_map {U U' : SmallEtale D.site D.base D.base_mem Z.1} (i : U' ⟶ U) :
    torsorPointAt D p hp L hL t U' =
      (torsorPointAt D p hp L hL t U).map D.site D.base D.base_mem
        ((SmallEtale.toOver D.site D.base D.base_mem _).map i) := by
  have hw : yoneda.map ((SmallEtale.toOver D.site D.base D.base_mem _).map i) ≫
      (U.obj.hom ≫ t.hom) = U'.obj.hom ≫ t.hom := by
    have hi : yoneda.map ((SmallEtale.toOver D.site D.base D.base_mem _).map i) ≫ U.obj.hom =
        U'.obj.hom := ((SmallEtale.inclusion D.site D.base D.base_mem _).map i).w
    rw [← Category.assoc, hi]
  exact relativeSpecPointsEquiv_yonedaEquiv_of_comp_eq D p hp L hL _ _ _ hw

/-- **The linear map of sections along `t ≫ q` given by `t`**: over a commuting square of étale
charts `U ⟶ V` over `t ≫ q`, a section of `ℒ^{⊗ 1}` over `V` goes to the value on `U` of its
image in the Laurent algebra under the point of `T` that `U ⟶ Z ⟶ T` is. -/
def torsorPointFMap :
    ModuleFMap D.site D.base D.base_mem (t ≫ torsorOfInvertibleProjection D p hp L hL)
      (SheafOfModules.unit _) (laurentPieceOne D p hp L hL) where
  app d s := (torsorPointAt D p hp L hL t d.U).chartEval D.site D.base D.base_mem d.V d.g
    (torsorPointAt_pt D p hp L hL t d) (laurentPieceOneIncl D p hp L hL d.V s)
  naturality d d' i j h s := by
    rw [laurentPieceOneIncl_map]
    have hj : yoneda.map ((SmallEtale.toOver D.site D.base D.base_mem X).map j) ≫ d.V.obj.hom =
        d'.V.obj.hom :=
      ((SmallEtale.inclusion D.site D.base D.base_mem X).map j).w
    have h2 : yonedaEquiv.symm (torsorPointAt D p hp L hL t d'.U).pt =
        yoneda.map (d'.g ≫ (SmallEtale.toOver D.site D.base D.base_mem X).map j) ≫
          d.V.obj.hom := by
      rw [torsorPointAt_pt, Functor.map_comp, Category.assoc, hj]
    have e1 := RelativeSpecPoint.map_comp_chartEval D.site D.base D.base_mem j d'.g
      (torsorPointAt D p hp L hL t d'.U) (torsorPointAt_pt D p hp L hL t d') h2
    have e2 := congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)
      (laurentPieceOneIncl D p hp L hL d.V s)) e1
    refine e2.trans ?_
    have hi : (torsorPointAt D p hp L hL t d'.U) =
        (torsorPointAt D p hp L hL t d.U).map D.site D.base D.base_mem
          ((SmallEtale.toOver D.site D.base D.base_mem _).map i) :=
      torsorPointAt_map D p hp L hL t i
    have h3 : yonedaEquiv.symm ((torsorPointAt D p hp L hL t d.U).map D.site D.base D.base_mem
        ((SmallEtale.toOver D.site D.base D.base_mem _).map i)).pt =
        yoneda.map ((SmallEtale.toOver D.site D.base D.base_mem _).map i ≫ d.g) ≫ d.V.obj.hom := by
      rw [← hi, h, h2]
    have e3 := RelativeSpecPoint.chartEval_congr D.site D.base D.base_mem d.V h.symm hi h2 h3
    have e4 := RelativeSpecPoint.chartEval_map D.site D.base D.base_mem d.V
      ((SmallEtale.toOver D.site D.base D.base_mem _).map i) d.g (torsorPointAt D p hp L hL t d.U)
      (torsorPointAt_pt D p hp L hL t d) h3
    refine Eq.trans (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)
      (laurentPieceOneIncl D p hp L hL d.V s)) e3) ?_
    refine Eq.trans (congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)
      (laurentPieceOneIncl D p hp L hL d.V s)) e4) ?_
    rfl
  map_add d s t := by
    dsimp only
    rw [map_add, map_add]
    rfl
  map_smul d r s := by
    dsimp only
    rw [laurentPieceOneIncl_smul, map_mul]
    exact congrArg (· * _) (RelativeSpecPoint.chartEval_algebraMap D.site D.base D.base_mem d.V
      d.g (torsorPointAt D p hp L hL t d.U) (torsorPointAt_pt D p hp L hL t d) r)

/-! ### The trivialization along `t` -/

/-- The identification `ℒ ≅ ℒ^{⊗ 1}` of `ℒ` with the degree-one piece of its Laurent algebra. -/
def laurentPieceOneIso : L ≅ laurentPieceOne D p hp L hL :=
  have : Stacks.SheafOfModules.IsInvertible (tensorStructureRingPresheaf D p hp)
      (isSheaf_tensorStructureRingPresheaf D p hp) L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  have := Stacks.SheafOfModules.TensorPower.isEquivalence_tensorRightFunctor
    (tensorStructureRingPresheaf D p hp) (isSheaf_tensorStructureRingPresheaf D p hp) L
  (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso (tensorStructureRingPresheaf D p hp)
    (isSheaf_tensorStructureRingPresheaf D p hp) L).symm

/-- The trivialization of the pullback of `ℒ` to the torsor `T` is the pullback of
`laurentPieceOneIso` followed by the tautological morphism `torsorTautologicalHom`. -/
theorem torsorOfInvertibleTrivialization_hom :
    (torsorOfInvertibleTrivialization D p hp L hL).hom =
      (modulePullback D.site D.base D.base_mem (torsorOfInvertibleProjection D p hp L hL)).map
        (laurentPieceOneIso D p hp L hL).hom ≫ torsorTautologicalHom D p hp L hL :=
  rfl



section Comp

variable {U : SmallEtale D.site D.base D.base_mem Z.1}
    {W : SmallEtale D.site D.base D.base_mem (torsorOfInvertibleSpace D p hp L hL).obj}
    {V : SmallEtale D.site D.base D.base_mem X}
    (a : (SmallEtale.toOver D.site D.base D.base_mem Z.1).obj U ⟶
      (SmallEtale.toOver D.site D.base D.base_mem _).obj W)
    (b : (SmallEtale.toOver D.site D.base D.base_mem _).obj W ⟶
      (SmallEtale.toOver D.site D.base D.base_mem X).obj V)
    (ha : U.1.hom ≫ t.hom = yoneda.map a ≫ W.1.hom)
    (hb : W.1.hom ≫ (torsorOfInvertibleProjection D p hp L hL).hom = yoneda.map b ≫ V.1.hom)

/-- The pullback along `U ⟶ W` of the tautological map of sections on `W ⟶ V` is the map of
sections given by `t` on the composite square. -/
theorem chartDiagramPullback_torsorTautologicalFMap
    (σ : (laurentPieceOne D p hp L hL).val.obj (op V)) :
    chartDiagramPullback D.site D.base D.base_mem t ⟨U, W, a, ha⟩
        ((torsorTautologicalFMap D p hp L hL).app ⟨W, V, b, hb⟩ σ) =
      (torsorPointFMap D p hp L hL t).app
        (ChartDiagram.comp D.site D.base D.base_mem t (torsorOfInvertibleProjection D p hp L hL)
          a b ha hb) σ := by
  have hpt : torsorPointAt D p hp L hL t U =
      (torsorChartPoint D p hp L hL W).map D.site D.base D.base_mem a := by
    exact relativeSpecPointsEquiv_yonedaEquiv_of_comp_eq D p hp L hL _ _ _ ha.symm
  have h3 : yonedaEquiv.symm ((torsorChartPoint D p hp L hL W).map D.site D.base D.base_mem
      a).pt = yoneda.map (a ≫ b) ≫ V.obj.hom := by
    rw [← hpt]
    exact torsorPointAt_pt D p hp L hL t (ChartDiagram.comp D.site D.base D.base_mem t
      (torsorOfInvertibleProjection D p hp L hL) a b ha hb)
  have hb' := torsorChartPoint_pt D p hp L hL ⟨W, V, b, hb⟩
  have e4 := RelativeSpecPoint.chartEval_map D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
    (T := W.obj.left) (T' := U.obj.left) V a b (torsorChartPoint D p hp L hL W) hb' h3
  have e3 := RelativeSpecPoint.chartEval_congr D.site D.base D.base_mem (X := ⟨X, hp.1⟩) V rfl
    hpt.symm h3 (torsorPointAt_pt D p hp L hL t (ChartDiagram.comp D.site D.base D.base_mem t
      (torsorOfInvertibleProjection D p hp L hL) a b ha hb))
  have e5 := congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)
    (laurentPieceOneIncl D p hp L hL V σ)) (e4.symm.trans e3)
  refine Eq.trans ?_ e5
  exact congrFun (congrArg DFunLike.coe (chartDiagramPullback_hom D.site D.base D.base_mem t
    ⟨U, W, a, ha⟩)) _

/-- **The pullback of `α` along `t` on a chart diagram factoring through a chart of `T`**: the
comparison `(t ≫ q)^*ℒ ≅ t^*q^*ℒ`, then `t^*α`, then `t^*𝒪_T ≅ 𝒪_Z`, carries the chart section
of `s` to the value of the map of sections given by `t` on the degree-one part of `s`. -/
theorem torsorTrivialization_chartSection_comp (s : L.val.obj (op V)) :
    (((modulePullbackCompIso D.site D.base D.base_mem t
      (torsorOfInvertibleProjection D p hp L hL)).inv.app L) ≫
    (((modulePullback D.site D.base D.base_mem t).map
        (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
      (modulePullbackUnitIso D.site D.base D.base_mem t).hom)).val.app (op U)
        (modulePullbackChartSection D.site D.base D.base_mem
          (t ≫ torsorOfInvertibleProjection D p hp L hL) L
          (ChartDiagram.comp D.site D.base D.base_mem t (torsorOfInvertibleProjection D p hp L hL)
            a b ha hb) s) =
      (torsorPointFMap D p hp L hL t).app
        (ChartDiagram.comp D.site D.base D.base_mem t (torsorOfInvertibleProjection D p hp L hL)
          a b ha hb) ((laurentPieceOneIso D p hp L hL).hom.val.app (op V) s) := by
  have e1 := modulePullbackCompIso_inv_chartSection D.site D.base D.base_mem t
    (torsorOfInvertibleProjection D p hp L hL) L a b ha hb s
  have e2 := modulePullbackChartSection_map D.site D.base D.base_mem t _
    (torsorOfInvertibleTrivialization D p hp L hL).hom ⟨U, W, a, ha⟩
    (modulePullbackChartSection D.site D.base D.base_mem
      (torsorOfInvertibleProjection D p hp L hL) L ⟨W, V, b, hb⟩ s)
  have e3 : (torsorOfInvertibleTrivialization D p hp L hL).hom.val.app (op W)
      (modulePullbackChartSection D.site D.base D.base_mem
        (torsorOfInvertibleProjection D p hp L hL) L ⟨W, V, b, hb⟩ s) =
      (torsorTautologicalFMap D p hp L hL).app ⟨W, V, b, hb⟩
        ((laurentPieceOneIso D p hp L hL).hom.val.app (op V) s) := by
    rw [torsorOfInvertibleTrivialization_hom]
    refine (congrArg (fun z => (torsorTautologicalHom D p hp L hL).val.app (op W) z)
      (modulePullbackChartSection_map D.site D.base D.base_mem
        (torsorOfInvertibleProjection D p hp L hL) _ (laurentPieceOneIso D p hp L hL).hom
        ⟨W, V, b, hb⟩ s)).trans ?_
    rw [← modulePullbackUnitSection_eq_modulePullbackChartSection]
    exact torsorTautologicalHom_unitSection D p hp L hL ⟨W, V, b, hb⟩ _
  have e4 := modulePullbackUnitIso_hom_chartSection D.site D.base D.base_mem t ⟨U, W, a, ha⟩
    ((torsorTautologicalFMap D p hp L hL).app ⟨W, V, b, hb⟩
      ((laurentPieceOneIso D p hp L hL).hom.val.app (op V) s))
  refine (congrArg (fun z => (modulePullbackUnitIso D.site D.base D.base_mem t).hom.val.app (op U)
    (((modulePullback D.site D.base D.base_mem t).map
      (torsorOfInvertibleTrivialization D p hp L hL).hom).val.app (op U) z)) e1).trans ?_
  refine (congrArg (fun z => (modulePullbackUnitIso D.site D.base D.base_mem t).hom.val.app (op U)
    z) e2).trans ?_
  refine (congrArg (fun z => (modulePullbackUnitIso D.site D.base D.base_mem t).hom.val.app (op U)
    (modulePullbackChartSection D.site D.base D.base_mem t _ ⟨U, W, a, ha⟩ z)) e3).trans ?_
  exact e4.trans (chartDiagramPullback_torsorTautologicalFMap D p hp L hL t a b ha hb _)

end Comp

/-- **Every chart diagram over `t ≫ q` with affine chart of `X` factors through the chart of `T`
over that chart.** -/
theorem exists_eq_comp_torsorAffineChart (d : ChartDiagram D.site D.base D.base_mem Z.1 X
    (t ≫ torsorOfInvertibleProjection D p hp L hL).hom) [IsAffine (chartScheme d.V)] :
    ∃ (a : (SmallEtale.toOver D.site D.base D.base_mem Z.1).obj d.U ⟶
        (SmallEtale.toOver D.site D.base D.base_mem _).obj (torsorAffineChart D p hp L hL d.V))
      (_ : d.U.1.hom ≫ t.hom = yoneda.map a ≫ (torsorAffineChart D p hp L hL d.V).1.hom),
      d.g = a ≫ torsorOfInvertibleChartHom D p hp L hL d.V := by
  have sq := isPullback_torsorOfInvertible_chart D p hp L hL d.V
  have hc : (d.U.1.hom ≫ t.hom) ≫ (torsorOfInvertibleProjection D p hp L hL).hom =
      yoneda.map d.g ≫ d.V.1.hom := (Category.assoc _ _ _).trans d.comm
  let l := sq.lift (d.U.1.hom ≫ t.hom) (yoneda.map d.g) hc
  let a : (SmallEtale.toOver D.site D.base D.base_mem Z.1).obj d.U ⟶
      (SmallEtale.toOver D.site D.base D.base_mem _).obj (torsorAffineChart D p hp L hL d.V) :=
    yoneda.preimage l
  have hl : yoneda.map a = l := Functor.map_preimage _ _
  refine ⟨a, ?_, ?_⟩
  · rw [hl]
    exact (sq.lift_fst _ _ hc).symm
  · apply yoneda.map_injective
    refine (sq.lift_snd _ _ hc).symm.trans ?_
    refine Eq.trans ?_ (yoneda.map_comp a (torsorOfInvertibleChartHom D p hp L hL d.V)).symm
    rw [hl]
    rfl


/-- The pullback of `α` along `t` on chart sections, over a chart diagram whose chart of `X` is
affine. -/
theorem torsorTrivialization_fmap_of_isAffine (d : ChartDiagram D.site D.base D.base_mem Z.1 X
    (t ≫ torsorOfInvertibleProjection D p hp L hL).hom) [IsAffine (chartScheme d.V)]
    (s : L.val.obj (op d.V)) :
    (modulePullbackHomFMap D.site D.base D.base_mem
      (t ≫ torsorOfInvertibleProjection D p hp L hL) L _
      (((modulePullbackCompIso D.site D.base D.base_mem t
        (torsorOfInvertibleProjection D p hp L hL)).inv.app L) ≫
      (((modulePullback D.site D.base D.base_mem t).map
          (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
        (modulePullbackUnitIso D.site D.base D.base_mem t).hom))).app d s =
      (torsorPointFMap D p hp L hL t).app d
        ((laurentPieceOneIso D p hp L hL).hom.val.app (op d.V) s) := by
  obtain ⟨a, ha, hg⟩ := exists_eq_comp_torsorAffineChart D p hp L hL t d
  have hc' := (ChartDiagram.comp D.site D.base D.base_mem t
    (torsorOfInvertibleProjection D p hp L hL) a (torsorOfInvertibleChartHom D p hp L hL d.V) ha
    (torsorAffineChart_comm D p hp L hL d.V)).comm
  have hcs := torsorTrivialization_chartSection_comp D p hp L hL t a
    (torsorOfInvertibleChartHom D p hp L hL d.V) ha (torsorAffineChart_comm D p hp L hL d.V) s
  have h1 := modulePullbackHomFMap_app_chartSection D.site D.base D.base_mem
    (t ≫ torsorOfInvertibleProjection D p hp L hL) L _
    (((modulePullbackCompIso D.site D.base D.base_mem t
        (torsorOfInvertibleProjection D p hp L hL)).inv.app L) ≫
      (((modulePullback D.site D.base D.base_mem t).map
          (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
        (modulePullbackUnitIso D.site D.base D.base_mem t).hom))
    (ChartDiagram.comp D.site D.base D.base_mem t
    (torsorOfInvertibleProjection D p hp L hL) a (torsorOfInvertibleChartHom D p hp L hL d.V) ha
    (torsorAffineChart_comm D p hp L hL d.V)) s
  have h0 := moduleFMap_app_eq_of_g_eq D.site D.base D.base_mem (A := Z) (A' := ⟨X, hp.1⟩)
    (g := t ≫ torsorOfInvertibleProjection D p hp L hL) (modulePullbackHomFMap D.site D.base
      D.base_mem (t ≫ torsorOfInvertibleProjection D p hp L hL) L _
      (((modulePullbackCompIso D.site D.base D.base_mem t
        (torsorOfInvertibleProjection D p hp L hL)).inv.app L) ≫
      (((modulePullback D.site D.base D.base_mem t).map
          (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
        (modulePullbackUnitIso D.site D.base D.base_mem t).hom))) d.g
    (a ≫ torsorOfInvertibleChartHom D p hp L hL d.V) d.comm hc' hg s
  have h2 := moduleFMap_app_eq_of_g_eq D.site D.base D.base_mem (A := Z) (A' := ⟨X, hp.1⟩)
    (g := t ≫ torsorOfInvertibleProjection D p hp L hL) (torsorPointFMap D p hp L hL t) d.g
    (a ≫ torsorOfInvertibleChartHom D p hp L hL d.V) d.comm hc' hg
    ((laurentPieceOneIso D p hp L hL).hom.val.app (op d.V) s)
  exact h0.trans (h1.trans (hcs.trans h2.symm))

/-- **The pullback of `α` along `t` on chart sections**, in the form of the chartwise
transpose.  Over every commuting square of étale charts `U ⟶ V` over `t ≫ q`, the comparison
`(t ≫ q)^*ℒ ≅ t^*q^*ℒ`, then `t^*α`, then `t^*𝒪_T ≅ 𝒪_Z`, carries the chart section of `s` to
the value of the map of sections given by `t` on the degree-one part of `s`. -/
theorem torsorTrivialization_fmap (d : ChartDiagram D.site D.base D.base_mem Z.1 X
    (t ≫ torsorOfInvertibleProjection D p hp L hL).hom) (s : L.val.obj (op d.V)) :
    (modulePullbackHomFMap D.site D.base D.base_mem
      (t ≫ torsorOfInvertibleProjection D p hp L hL) L _
      (((modulePullbackCompIso D.site D.base D.base_mem t
        (torsorOfInvertibleProjection D p hp L hL)).inv.app L) ≫
      (((modulePullback D.site D.base D.base_mem t).map
          (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
        (modulePullbackUnitIso D.site D.base D.base_mem t).hom))).app d s =
      (torsorPointFMap D p hp L hL t).app d
        ((laurentPieceOneIso D p hp L hL).hom.val.app (op d.V) s) :=
  moduleFMap_app_eq_of_isAffine D.site D.base D.base_mem (A := Z) (A' := ⟨X, hp.1⟩)
    (t ≫ torsorOfInvertibleProjection D p hp L hL) _ (torsorPointFMap D p hp L hL t)
    (laurentPieceOneIso D p hp L hL).hom
    (fun d' hd' s' => @torsorTrivialization_fmap_of_isAffine D X p hp L hL Z t d' hd' s') d s

/-- For a chart diagram `d` of any morphism `x` equal to `t ≫ q`, the underlying morphism of the
point `torsorPointAt t d.U` is `d.g` followed by the structure morphism of `d.V`. -/
theorem torsorPointAt_pt_of_eq {x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (h : t ≫ torsorOfInvertibleProjection D p hp L hL = x)
    (d : ChartDiagram D.site D.base D.base_mem Z.1 X x.hom) :
    yonedaEquiv.symm (torsorPointAt D p hp L hL t d.U).pt = yoneda.map d.g ≫ d.V.obj.hom := by
  subst h
  exact torsorPointAt_pt D p hp L hL t d

/-- **The trivialization along `t`, read along any morphism equal to `t ≫ q`.** -/
theorem torsorTrivialization_fmap_of_eq
    {x : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (h : t ≫ torsorOfInvertibleProjection D p hp L hL = x)
    (d : ChartDiagram D.site D.base D.base_mem Z.1 X x.hom) (s : L.val.obj (op d.V)) :
    (modulePullbackHomFMap D.site D.base D.base_mem x L _
      ((modulePullbackTriangle D.site D.base D.base_mem h).hom.app L ≫
      (((modulePullback D.site D.base D.base_mem t).map
          (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
        (modulePullbackUnitIso D.site D.base D.base_mem t).hom))).app d s =
      (torsorPointAt D p hp L hL t d.U).chartEval D.site D.base D.base_mem d.V d.g
        (torsorPointAt_pt_of_eq D p hp L hL t h d)
        (laurentPieceOneIncl D p hp L hL d.V
          ((laurentPieceOneIso D p hp L hL).hom.val.app (op d.V) s)) := by
  subst h
  rw [modulePullbackTriangle_rfl, Iso.symm_hom]
  exact torsorTrivialization_fmap D p hp L hL t d s

end Point

end AlgebraicGeometry.Space

end
