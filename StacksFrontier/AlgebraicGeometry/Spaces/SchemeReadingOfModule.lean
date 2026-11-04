module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionIdChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction

/-!
# The reading of a module on an algebraic space on a scheme over it

Let `X` be an algebraic space over a scheme `S` and `ℰ` a quasi-coherent `𝒪_X`-module.  A
morphism `ψ : T ⟶ X` from (the algebraic space represented by) an object `T` of the big fppf
site gives a quasi-coherent module on the *scheme* underlying `T`: the inverse image `ψ^*ℰ` of
Stacks 03LU, read on the small Zariski site of the scheme through Stacks 03DX (2).  This is the
quasi-coherent module `ℰ_T` of the scheme `T`, and the point of this file is that it is a
**pseudofunctor** in `(T, ψ)`: a morphism `g : T' ⟶ T` with `g ≫ ψ = ψ'` gives an isomorphism

`c_g : g^* ℰ_T ≅ ℰ_{T'}`,

and the isomorphisms compose, `c_h ∘ h^* c_g = c_{h ≫ g}` up to the comparison of iterated
pullbacks.  This is the coherence which glueing a scheme-level construction over the charts of
`X` asks for.

## Main definitions

* `AlgebraicGeometry.Space.schemeReading`: the module `ℰ_T = (ψ^*ℰ)|_{T_Zar}` on the scheme
  underlying `T`.
* `AlgebraicGeometry.Space.schemeReadingPullbackIso`: the comparison `g^* ℰ_T ≅ ℰ_{T'}`.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherent_schemeReading`: the reading is quasi-coherent.
* `AlgebraicGeometry.Space.schemeReadingPullbackIso_comp`: **the comparisons compose.**

## Implementation notes

The comparison is the composite of the base change of the Zariski reading,
`AlgebraicGeometry.Space.representedZariskiModulePullbackIso`, with the reading of the
comparison `(g^*ψ^*ℰ ≅ ψ'^*ℰ)` of iterated inverse images,
`AlgebraicGeometry.Space.modulePullbackTriangle`.  Its composition law is the composition law
of the first, `AlgebraicGeometry.Space.representedZariskiModulePullbackIso_comp_iso`, together
with its naturality and the associativity of the second,
`AlgebraicGeometry.Space.modulePullbackTriangle_inv_app_assoc`.  Every equation is stated
between isomorphisms, as the implementation notes of the module
`StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.RepresentedZariskiTransitionSquare`
recommend.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2)

/-- The reading `ℰ_T = (ψ^*ℰ)|_{T_Zar}` of a module on `X` on the scheme underlying an object `T`
of the big fppf site, along a morphism `ψ : T ⟶ X`. -/
abbrev schemeReading {T : BigFppfOver B S hS} (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    ((BigFppfOver.toScheme B S hS).obj T).Modules :=
  representedZariskiModule B S hS T ((modulePullback B S hS ψ).obj E)

variable (hE : E.IsQuasicoherentOnSite)
include hE

/-- The inverse image of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_modulePullback_schemeReading {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    ((modulePullback B S hS ψ).obj E).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS ψ E hE

/-- **The reading of a quasi-coherent module is quasi-coherent.** -/
theorem isQuasicoherent_schemeReading {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X) :
    (schemeReading E ψ).IsQuasicoherent :=
  QuasiCoherentDescent.isQuasicoherent_representedZariskiModule B S hS _
    (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ)

/-- **The comparison `g^* ℰ_T ≅ ℰ_{T'}`** of the readings along a morphism `g : T' ⟶ T` of the
big fppf site with `g ≫ ψ = ψ'`. -/
def schemeReadingPullbackIso {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left)).obj
        (schemeReading E ψ) ≅ schemeReading E ψ' :=
  representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
      ((modulePullback B S hS ψ).obj E)
      (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ) ≪≫
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
          E).symm)

/-- `AlgebraicGeometry.Space.schemeReadingPullbackIso` written out. -/
theorem schemeReadingPullbackIso_eq {T' T : BigFppfOver B S hS} (g : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') :
    schemeReadingPullbackIso E hE g w =
      representedZariskiModulePullbackIso B S hS g (relativelyRepresentable_yoneda_map B S hS g)
          ((modulePullback B S hS ψ).obj E)
          (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ) ≪≫
        (SmallEtale.restrictModule (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
          ((representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso
            (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
              E).symm) :=
  rfl

/-! ### At an étale chart the reading is the chart restriction -/

omit hE in
/-- **At an étale chart `V` of `X` the reading of `ℰ` is the restriction `ℰ|_V` of `ℰ` to the
scheme of the chart**, `AlgebraicGeometry.Space.restrictToChartScheme`.  The restriction is the
restriction at the identity chart of the étale pullback to the chart space
(`AlgebraicGeometry.Space.restrictToChartScheme_eq_atIdEtaleChart`), the restriction at an
identity chart is the Zariski reading
(`AlgebraicGeometry.Space.restrictToChartSchemeIdEtaleChartIso`), and the étale pullback is the
inverse image (Stacks 03LW). -/
def schemeReadingChartIso (V : SmallEtale B S hS X.1) :
    schemeReading E (chartToSpace B S hS X V) ≅ restrictToChartScheme B S hS X.1 X.2 E V :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj (chartFppfObject B S hS X V))
      (chartFppfObject B S hS X V).left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X V)).inverse.mapIso
      ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).app E)) ≪≫
    (restrictToChartSchemeIdEtaleChartIso B S hS (chartFppfObject B S hS X V)
      ((etaleModulePullback B S hS (chartToSpace B S hS X V)
        (isEtale_chartToSpace B S hS X V)).obj E)).symm ≪≫
    eqToIso (restrictToChartScheme_eq_atIdEtaleChart B S hS X V E).symm

/-- **The comparison depends only on the morphism**: at two equal morphisms the comparisons
differ by the transport `AlgebraicGeometry.Scheme.Modules.pullbackCongr`. -/
theorem pullbackCongr_hom_app_schemeReadingPullbackIso {T' T : BigFppfOver B S hS}
    {g₁ g₂ : T' ⟶ T} (hg : g₁ = g₂) {ψ : representedAlgebraicSpace B S hS T ⟶ X}
    {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    (w₁ : representedSpaceMap B S hS g₁ ≫ ψ = ψ') (w₂ : representedSpaceMap B S hS g₂ ≫ ψ = ψ') :
    (Scheme.Modules.pullbackCongr
          (congrArg (fun x : T' ⟶ T =>
            _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) x.left)
            hg)).hom.app (schemeReading E ψ) ≫
        (schemeReadingPullbackIso E hE g₂ w₂).hom =
      (schemeReadingPullbackIso E hE g₁ w₁).hom := by
  subst hg
  exact Category.id_comp _

section Comp

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

omit hE in
/-- **The associativity of the comparisons of iterated inverse images, in the shape of the
composition law of the readings.** -/
theorem pullbackComparison_symm_assoc_representedSpaceMap {T'' T' T : BigFppfOver B S hS}
    (h : T'' ⟶ T') (g : T' ⟶ T) {ψ : representedAlgebraicSpace B S hS T ⟶ X}
    {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    {ψ'' : representedAlgebraicSpace B S hS T'' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') (w' : representedSpaceMap B S hS h ≫ ψ' = ψ'')
    (w'' : representedSpaceMap B S hS (h ≫ g) ≫ ψ = ψ'') :
    (modulePullback B S hS (representedSpaceMap B S hS h)).mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
          E).symm ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS h) ψ' ψ'' w'
          E).symm =
      (representedModulePullbackCompIso B S hS h g).app ((modulePullback B S hS ψ).obj E) ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS (h ≫ g)) ψ ψ''
          w'' E).symm := by
  have key := congrArg Iso.symm (QuasiCoherentDescent.pullbackComparison_trans B S hS
    (representedSpaceMap B S hS h) (representedSpaceMap B S hS g) ψ ψ' w
    (representedSpaceMap B S hS (h ≫ g)) (representedSpaceMap_comp B S hS h g) ψ'' w' w'' E)
  rw [Iso.trans_symm, Iso.trans_symm, ← Functor.mapIso_symm,
    QuasiCoherentDescent.pullbackComparison_representedSpaceMap_comp, Iso.symm_symm_eq] at key
  exact key

omit hE in
/-- **The abstract shape of the composition law.** -/
private theorem comp_law_shape {C₀ : Type*} [Category C₀] {o1 o2 o3 o4 o5 o6 o7 o8 : C₀}
    (A : o1 ≅ o2) (Bθ : o2 ≅ o3) (T2h' : o3 ≅ o4) (Rθ' : o4 ≅ o5) (T2h : o2 ≅ o6)
    (Rhθ : o6 ≅ o4) (Pc : o1 ≅ o7) (T2hg : o7 ≅ o8) (Rcomp : o6 ≅ o8) (Rθ'' : o8 ≅ o5)
    (nat : Bθ ≪≫ T2h' = T2h ≪≫ Rhθ) (compiso : A ≪≫ T2h ≪≫ Rcomp = Pc ≪≫ T2hg)
    (assoc : Rhθ ≪≫ Rθ' = Rcomp ≪≫ Rθ'') :
    (A ≪≫ Bθ) ≪≫ T2h' ≪≫ Rθ' = Pc ≪≫ T2hg ≪≫ Rθ'' := by
  rw [Iso.trans_assoc, ← Iso.trans_assoc Bθ, nat, Iso.trans_assoc, assoc, ← Iso.trans_assoc,
    ← Iso.trans_assoc, Iso.trans_assoc A, compiso, Iso.trans_assoc]

/-- **The comparisons of the readings compose**: for `h : T'' ⟶ T'` and `g : T' ⟶ T` over `X`,
`c_h ∘ h^* c_g` is `c_{h ≫ g}` after the contraction of the two pullbacks of modules on the
schemes. -/
theorem schemeReadingPullbackIso_comp {T'' T' T : BigFppfOver B S hS} (h : T'' ⟶ T')
    (g : T' ⟶ T) {ψ : representedAlgebraicSpace B S hS T ⟶ X}
    {ψ' : representedAlgebraicSpace B S hS T' ⟶ X}
    {ψ'' : representedAlgebraicSpace B S hS T'' ⟶ X}
    (w : representedSpaceMap B S hS g ≫ ψ = ψ') (w' : representedSpaceMap B S hS h ≫ ψ' = ψ'')
    (w'' : representedSpaceMap B S hS (h ≫ g) ≫ ψ = ψ'') :
    (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)).mapIso
        (schemeReadingPullbackIso E hE g w) ≪≫ schemeReadingPullbackIso E hE h w' =
      (Scheme.Modules.pullbackComp
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) h.left)
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              g.left)).app (schemeReading E ψ) ≪≫
        schemeReadingPullbackIso E hE (h ≫ g) w'' := by
  rw [schemeReadingPullbackIso_eq, schemeReadingPullbackIso_eq, schemeReadingPullbackIso_eq,
    Functor.mapIso_trans]
  refine comp_law_shape (nat := representedZariskiModulePullbackIso_naturality_iso B S hS h
      (relativelyRepresentable_yoneda_map B S hS h)
      (isQuasicoherentOnSite_modulePullback_representedSpaceMap B S hS g
        (relativelyRepresentable_yoneda_map B S hS g) _
        (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ))
      (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ')
      (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS g) ψ ψ' w
        E).symm)
    (compiso := representedZariskiModulePullbackIso_comp_iso B S hS h g
      (relativelyRepresentable_yoneda_map B S hS h) (relativelyRepresentable_yoneda_map B S hS g)
      (relativelyRepresentable_yoneda_map B S hS (h ≫ g)) _
      (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψ)) (assoc := ?_)
  rw [← Functor.mapIso_trans, ← Functor.mapIso_trans, ← Functor.mapIso_trans,
    ← Functor.mapIso_trans, pullbackComparison_symm_assoc_representedSpaceMap E h g w w' w'']

omit hE in
/-- The abstract shape of the square law. -/
private theorem square_shape {C₀ : Type*} [Category C₀] {o1 o2 o3 o4 o5 o6 : C₀}
    (A : o1 ≅ o2) (Cg : o2 ≅ o3) (D : o3 ≅ o4) (Pc : o5 ≅ o3) (M : o5 ≅ o6) (N : o6 ≅ o4)
    (h : M ≪≫ N = Pc ≪≫ D) :
    A ≪≫ Cg ≪≫ D = A ≪≫ Cg ≪≫ Pc.symm ≪≫ M ≪≫ N := by
  rw [h, ← Iso.trans_assoc Pc.symm, Iso.symm_self_id, Iso.refl_trans]

/-- **The comparisons of the readings along a commutative square**: for `t ≫ ρ = ρ' ≫ t'` over
`X`, the comparison along `t` after the pullback of the one along `ρ` is the comparison along
`ρ'` after the pullback of the one along `t'`, up to the contractions of the iterated pullbacks
of modules on the schemes and the transport along the square. -/
theorem schemeReadingPullbackIso_square {P' P Y' Y : BigFppfOver B S hS} {t : P' ⟶ P}
    {ρ : P ⟶ Y} {ρ' : P' ⟶ Y'} {t' : Y' ⟶ Y} (heq : t ≫ ρ = ρ' ≫ t')
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} {ψY' : representedAlgebraicSpace B S hS Y' ⟶ X}
    {ψP : representedAlgebraicSpace B S hS P ⟶ X} {ψP' : representedAlgebraicSpace B S hS P' ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψP) (wt : representedSpaceMap B S hS t ≫ ψP = ψP')
    (wt' : representedSpaceMap B S hS t' ≫ ψY = ψY')
    (wρ' : representedSpaceMap B S hS ρ' ≫ ψY' = ψP') :
    (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) t.left)).mapIso
        (schemeReadingPullbackIso E hE ρ wρ) ≪≫ schemeReadingPullbackIso E hE t wt =
      (Scheme.Modules.pullbackComp
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) t.left)
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              ρ.left)).app (schemeReading E ψY) ≪≫
        (Scheme.Modules.pullbackCongr
          (f := _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) t.left ≫
            _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)
          (g := _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left ≫
            _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) t'.left)
          (congrArg (fun x : P' ⟶ Y =>
            _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) x.left)
            heq)).app (schemeReading E ψY) ≪≫
        ((Scheme.Modules.pullbackComp
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left)
            (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
              t'.left)).app (schemeReading E ψY)).symm ≪≫
        (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left)).mapIso
          (schemeReadingPullbackIso E hE t' wt') ≪≫
        schemeReadingPullbackIso E hE ρ' wρ' := by
  have w₁ : representedSpaceMap B S hS (t ≫ ρ) ≫ ψY = ψP' := by
    rw [← representedSpaceMap_comp, Category.assoc, wρ, wt]
  have w₂ : representedSpaceMap B S hS (ρ' ≫ t') ≫ ψY = ψP' := heq ▸ w₁
  have c₁ := schemeReadingPullbackIso_comp E hE t ρ wρ wt w₁
  have c₂ := schemeReadingPullbackIso_comp E hE ρ' t' wt' wρ' w₂
  have hcongr : schemeReadingPullbackIso E hE (t ≫ ρ) w₁ =
      (Scheme.Modules.pullbackCongr
          (congrArg (fun x : P' ⟶ Y =>
            _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) x.left)
            heq)).app (schemeReading E ψY) ≪≫ schemeReadingPullbackIso E hE (ρ' ≫ t') w₂ :=
    Iso.ext (pullbackCongr_hom_app_schemeReadingPullbackIso E hE heq w₁ w₂).symm
  rw [c₁, hcongr]
  exact square_shape _ _ _ _ _ _ c₂

end Comp

end AlgebraicGeometry.Space

end
