module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleQuotientFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleTwistCharts
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SurjectivePoints
import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas

/-!
# Readings of quotients on represented algebraic spaces

The reading statements `AlgebraicGeometry.Space.QuotientReadingHyp` used for the twist of the
projective bundle of an inverse image: they are preserved by inverse images along a morphism of
the site (`AlgebraicGeometry.Space.quotientReadingHyp_modulePullback`), pass between a module and
its inverse image (`AlgebraicGeometry.Space.quotientReadingHyp_modulePullback_obj`), and two
quotients with the same reading are isomorphic
(`AlgebraicGeometry.Space.exists_iso_comp_eq_of_quotientReadingHyp`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`, by which an
-- arrow `M ⟶ N` of modules written in a statement would not match the arrows of the inverse-image
-- functors without unfolding them.
attribute [-instance] CategoryTheory.catToReflQuiver

/-! ### Abstract shapes -/

section Shape

/-- The abstract shape of the inverse image of a reading. -/
private theorem pullback_reading_shape {C₀ C₁ : Type*} [Category C₀] [Category C₁]
    (G : C₀ ⥤ C₁) {a b k ρE TU : C₀} {a' b' k' m ρE' TR : C₁}
    (q : a ⟶ b) (K : a ≅ k) (Sρ : ρE ≅ k) (univ : ρE ⟶ TU) (εL : b ≅ TU)
    (q' : a' ⟶ b') (ZN : G.obj a ≅ a') (ZL : G.obj b ≅ b') (K' : a' ≅ k') (Sg : G.obj k ≅ k')
    (Sq : G.obj ρE ≅ m) (St : m ≅ ρE') (Sρ' : ρE' ≅ k') (univ' : ρE' ⟶ TR)
    (θ : G.obj TU ≅ TR)
    (hq : q = K.hom ≫ Sρ.inv ≫ univ ≫ εL.inv)
    (nat : G.map q ≫ ZL.hom = ZN.hom ≫ q')
    (h₁ : G.mapIso K ≪≫ Sg = ZN ≪≫ K')
    (h₂ : G.mapIso Sρ ≪≫ Sg = Sq ≪≫ St ≪≫ Sρ')
    (hspec : G.map univ ≫ θ.hom = Sq.hom ≫ St.hom ≫ univ') :
    q' = K'.hom ≫ Sρ'.inv ≫ univ' ≫ (ZL.symm ≪≫ G.mapIso εL ≪≫ θ).inv := by
  have hq' : q' = ZN.inv ≫ G.map q ≫ ZL.hom := (Iso.eq_inv_comp ZN).2 nat.symm
  have hu : G.map univ = (Sq.hom ≫ St.hom ≫ univ') ≫ θ.inv := (Iso.eq_comp_inv θ).2 hspec
  have e₁ : ZN.inv ≫ G.map K.hom = K'.hom ≫ Sg.inv := by
    have := congrArg Iso.hom h₁
    simp only [Iso.trans_hom, Functor.mapIso_hom] at this
    rw [Iso.inv_comp_eq, ← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have e₂ : G.map Sρ.inv ≫ Sq.hom ≫ St.hom = Sg.hom ≫ Sρ'.inv := by
    have := congrArg Iso.hom h₂
    simp only [Iso.trans_hom, Functor.mapIso_hom] at this
    rw [← cancel_epi (G.map Sρ.hom), ← Category.assoc, ← G.map_comp, Iso.hom_inv_id,
      G.map_id, Category.id_comp, ← Category.assoc, this]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hq', hq]
  simp only [Functor.map_comp, Category.assoc, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  rw [hu]
  simp only [Category.assoc]
  rw [reassoc_of% e₂, reassoc_of% e₁, Iso.inv_hom_id_assoc]

/-- The abstract shape of the reading of a quotient of an inverse image of modules. -/
private theorem modulePullback_reading_shape {C₀ : Type*} [Category C₀]
    {a k k₀ ρE ρE₀ TU b : C₀} (K : a ≅ k) (M : k₀ ≅ k) (SEinv : k ⟶ ρE) (Mρinv : ρE ⟶ ρE₀)
    (S'inv : k₀ ⟶ ρE₀) (univ : ρE₀ ⟶ TU) (εL : b ≅ TU) (e : SEinv ≫ Mρinv = M.inv ≫ S'inv) :
    K.hom ≫ SEinv ≫ (Mρinv ≫ univ) ≫ εL.inv = (K ≪≫ M.symm).hom ≫ S'inv ≫ univ ≫ εL.inv := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% e]


end Shape

/-! ### Readings of quotients on represented algebraic spaces -/

section Generic

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  (E : Modules.{u, u} B S hS X.1 X.2) (hE : E.IsQuasicoherentOnSite)

/-- **The reading of a quotient is preserved by inverse images along a morphism of the site.**
Let `q : N ⟶ L` on `T` read as `univ` through `ρ : T ⟶ Y`, and let `k : T' ⟶ T` sit in a
commutative square `k ≫ ρ = ρ' ≫ t`.  If the pullback of `univ` along `k` is `univ'` up to the
comparison of the readings along the square and an isomorphism `θ` of targets, then the inverse
image `k^*q` reads as `univ'` through `ρ'`. -/
theorem quotientReadingHyp_modulePullback {T' T Y' Y : BigFppfOver B S hS} (k : T' ⟶ T)
    {ρ : T ⟶ Y} {ρ' : T' ⟶ Y'} {t : Y' ⟶ Y} (heq : k ≫ ρ = ρ' ≫ t)
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} {ψY' : representedAlgebraicSpace B S hS Y' ⟶ X}
    {ψU : representedAlgebraicSpace B S hS T ⟶ X} {ψR : representedAlgebraicSpace B S hS T' ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU) (wk : representedSpaceMap B S hS k ≫ ψU = ψR)
    (wt : representedSpaceMap B S hS t ≫ ψY = ψY')
    (wρ' : representedSpaceMap B S hS ρ' ≫ ψY' = ψR)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    {TR : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    (univ' : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left)).obj
        (schemeReading E ψY') ⟶ TR)
    (θ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).obj TU ≅
        TR)
    (hspec : (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).map
          univ ≫ θ.hom =
      (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            ρ.left)).hom.app (schemeReading E ψY) ≫
        (Scheme.Modules.pullbackCongr (schemeHom_comp_eq_of_eq heq)).hom.app
          (schemeReading E ψY) ≫
        (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            t.left)).inv.app (schemeReading E ψY) ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) ρ'.left)).map (schemeReadingPullbackIso E hE t wt).hom ≫
        univ')
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (hL : L.IsQuasicoherentOnSite)
    (εL : representedZariskiModule B S hS T L ≅ TU) (q : N ⟶ L)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E)
    (hq : QuotientReadingHyp E hE wρ univ εL q κ₀) :
    QuotientReadingHyp E hE wρ' univ'
      ((representedZariskiModulePullbackIso B S hS k
          (relativelyRepresentable_yoneda_map B S hS k) L hL).symm ≪≫
        (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).mapIso
          εL ≪≫ θ)
      ((modulePullback B S hS (representedSpaceMap B S hS k)).map q)
      ((modulePullback B S hS (representedSpaceMap B S hS k)).mapIso κ₀ ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS k) ψU ψR wk
          E).symm) := by
  unfold QuotientReadingHyp quotientReadingOf at hq ⊢
  refine pullback_reading_shape (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left))
    _ _ _ univ εL _
    (representedZariskiModulePullbackIso B S hS k (relativelyRepresentable_yoneda_map B S hS k)
      N hN)
    (representedZariskiModulePullbackIso B S hS k (relativelyRepresentable_yoneda_map B S hS k)
      L hL) _ (schemeReadingPullbackIso E hE k wk)
    (squarePullbackIso (EU := schemeReading E ψY) (schemeHom_comp_eq_of_eq heq))
    ((Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) ρ'.left)).mapIso (schemeReadingPullbackIso E hE t wt))
    (schemeReadingPullbackIso E hE ρ' wρ') univ' θ hq
    (representedZariskiModulePullbackIso_naturality B S hS k
      (relativelyRepresentable_yoneda_map B S hS k) hN hL q) ?_ ?_
    (hspec.trans (by
      simp only [squarePullbackIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
        Functor.mapIso_hom, Category.assoc]))
  · rw [schemeReadingPullbackIso_eq, ← Iso.trans_assoc,
      representedZariskiModulePullbackIso_naturality_iso B S hS k
        (relativelyRepresentable_yoneda_map B S hS k) hN
        (isQuasicoherentOnSite_modulePullback_schemeReading E hE ψU) κ₀,
      Iso.trans_assoc, Functor.mapIso_trans, Functor.mapIso_trans]
  · rw [schemeReadingPullbackIso_square E hE heq wρ wk wt wρ']
    simp only [squarePullbackIso, Iso.trans_assoc]

/-- `AlgebraicGeometry.Space.quotientReadingHyp_modulePullback`, with the comparison of the
readings along `t` followed by a further morphism `v`, given as the inverse of an isomorphism `c`
inside one inverse image. -/
theorem quotientReadingHyp_modulePullback_of_comp {T' T Y' Y : BigFppfOver B S hS} (k : T' ⟶ T)
    {ρ : T ⟶ Y} {ρ' : T' ⟶ Y'} {t : Y' ⟶ Y} (heq : k ≫ ρ = ρ' ≫ t)
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} {ψY' : representedAlgebraicSpace B S hS Y' ⟶ X}
    {ψU : representedAlgebraicSpace B S hS T ⟶ X} {ψR : representedAlgebraicSpace B S hS T' ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU) (wk : representedSpaceMap B S hS k ≫ ψU = ψR)
    (wt : representedSpaceMap B S hS t ≫ ψY = ψY')
    (wρ' : representedSpaceMap B S hS ρ' ≫ ψY' = ψR)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    {TR : ((BigFppfOver.toScheme B S hS).obj T').Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    {M' : ((BigFppfOver.toScheme B S hS).obj Y').Modules}
    (v : schemeReading E ψY' ⟶ M')
    (c : M' ≅ (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) t.left)).obj
        (schemeReading E ψY))
    (hc : c.inv = (schemeReadingPullbackIso E hE t wt).hom ≫ v)
    (univ₀ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left)).obj M' ⟶
        TR)
    (θ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).obj TU ≅
        TR)
    (hspec : (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).map
          univ ≫ θ.hom =
      (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            ρ.left)).hom.app (schemeReading E ψY) ≫
        (Scheme.Modules.pullbackCongr (schemeHom_comp_eq_of_eq heq)).hom.app
          (schemeReading E ψY) ≫
        (Scheme.Modules.pullbackComp
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left)
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B)
            t.left)).inv.app (schemeReading E ψY) ≫
        (Scheme.Modules.pullback (_root_.AlgebraicGeometry.SmallEtale.schemeHom
          (associatedBigEtaleSite B) ρ'.left)).map c.inv ≫ univ₀)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (hN : N.IsQuasicoherentOnSite) (hL : L.IsQuasicoherentOnSite)
    (εL : representedZariskiModule B S hS T L ≅ TU) (q : N ⟶ L)
    (κ₀ : N ≅ (modulePullback B S hS ψU).obj E)
    (hq : QuotientReadingHyp E hE wρ univ εL q κ₀) :
    QuotientReadingHyp E hE wρ' ((Scheme.Modules.pullback
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ'.left)).map v ≫
        univ₀)
      ((representedZariskiModulePullbackIso B S hS k
          (relativelyRepresentable_yoneda_map B S hS k) L hL).symm ≪≫
        (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).mapIso
          εL ≪≫ θ)
      ((modulePullback B S hS (representedSpaceMap B S hS k)).map q)
      ((modulePullback B S hS (representedSpaceMap B S hS k)).mapIso κ₀ ≪≫
        (QuasiCoherentDescent.pullbackComparison B S hS (representedSpaceMap B S hS k) ψU ψR wk
          E).symm) := by
  refine quotientReadingHyp_modulePullback E hE k heq wρ wk wt wρ' univ _ θ ?_ hN hL εL q κ₀ hq
  rw [hspec, hc, CategoryTheory.Functor.map_comp, Category.assoc]

variable {X' : AlgebraicSpaces B S hS} (g : X' ⟶ X)

/-- The reading of the comparison `(ψ ≫ g)^*ℰ ≅ ψ^*g^*ℰ` is the inverse of
`AlgebraicGeometry.Space.schemeReadingModulePullbackIso`. -/
theorem mapIso_pullbackComparison_eq_schemeReadingModulePullbackIso_symm {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X') :
    (SmallEtale.restrictModule (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
      ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso
        (QuasiCoherentDescent.pullbackComparison B S hS ψ g (ψ ≫ g) rfl E)) =
      (schemeReadingModulePullbackIso g E ψ).symm := by
  rw [schemeReadingModulePullbackIso, ← Functor.mapIso_symm, ← Functor.mapIso_symm,
    Iso.symm_symm_eq]

/-- `AlgebraicGeometry.Space.schemeReadingModulePullbackIso_naturality`, on the inverses. -/
theorem schemeReadingPullbackIso_inv_comp_schemeReadingModulePullbackIso_inv
    {T Y : BigFppfOver B S hS} (ρ : T ⟶ Y)
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X'} {ψU : representedAlgebraicSpace B S hS T ⟶ X'}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    (wρg : representedSpaceMap B S hS ρ ≫ (ψY ≫ g) = ψU ≫ g) :
    (schemeReadingPullbackIso E hE (ψ := ψY ≫ g) (ψ' := ψU ≫ g) ρ wρg).inv ≫
        (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).map
          (schemeReadingModulePullbackIso g E ψY).inv =
      (schemeReadingModulePullbackIso g E ψU).inv ≫
        (schemeReadingPullbackIso ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE) ρ wρ).inv := by
  have e : (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).mapIso
        (schemeReadingModulePullbackIso g E ψY) ≪≫ schemeReadingPullbackIso E hE ρ wρg =
      schemeReadingPullbackIso ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE) ρ wρ ≪≫
        schemeReadingModulePullbackIso g E ψU :=
    schemeReadingModulePullbackIso_naturality g E hE ρ wρ wρg
  have e' := congrArg Iso.inv e
  simp only [Iso.trans_inv, Functor.mapIso_inv] at e'
  exact e'

/-- **A reading of a quotient of an inverse image along `g`, as a reading for `ℰ`, is a reading
for `g^*ℰ`**: the reading of `ℰ` along `ψ_Y ≫ g` is that of `g^*ℰ` along `ψ_Y`
(`AlgebraicGeometry.Space.schemeReadingModulePullbackIso`), compatibly with the comparisons of
readings. -/
theorem quotientReadingHyp_modulePullback_obj {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X'} {ψU : representedAlgebraicSpace B S hS T ⟶ X'}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    (wρg : representedSpaceMap B S hS ρ ≫ (ψY ≫ g) = ψU ≫ g)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading ((modulePullback B S hS g).obj E) ψY) ⟶ TU)
    {N L : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    (εL : representedZariskiModule B S hS T L ≅ TU) (q : N ⟶ L)
    (κ : N ≅ (modulePullback B S hS (ψU ≫ g)).obj E)
    (hq : QuotientReadingHyp E hE (ψY := ψY ≫ g) (ψU := ψU ≫ g) wρg
      ((Scheme.Modules.pullback
        (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).map
          (schemeReadingModulePullbackIso g E ψY).inv ≫ univ) εL q κ) :
    QuotientReadingHyp ((modulePullback B S hS g).obj E)
      (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE) wρ univ εL q
      (κ ≪≫ QuasiCoherentDescent.pullbackComparison B S hS ψU g (ψU ≫ g) rfl E) := by
  unfold QuotientReadingHyp quotientReadingOf at hq ⊢
  rw [hq, Functor.mapIso_trans, Functor.mapIso_trans,
    mapIso_pullbackComparison_eq_schemeReadingModulePullbackIso_symm]
  exact modulePullback_reading_shape _ _ _ _ _ univ εL
    (schemeReadingPullbackIso_inv_comp_schemeReadingModulePullbackIso_inv E hE g ρ wρ wρg)

/-- **Two quotients with the same reading are isomorphic**: two morphisms `q₁ : N₁ ⟶ L₁` and
`q₂ : N₂ ⟶ L₂` of modules on a represented algebraic space `T` whose readings are one morphism
`univ` through `ρ : T ⟶ Y` are isomorphic as quotients, through the identification
`N₁ ≅ ψ_U^*ℰ ≅ N₂` of their sources. -/
theorem exists_iso_comp_eq_of_quotientReadingHyp {T Y : BigFppfOver B S hS} {ρ : T ⟶ Y}
    {ψY : representedAlgebraicSpace B S hS Y ⟶ X} {ψU : representedAlgebraicSpace B S hS T ⟶ X}
    (wρ : representedSpaceMap B S hS ρ ≫ ψY = ψU)
    {TU : ((BigFppfOver.toScheme B S hS).obj T).Modules}
    (univ : (Scheme.Modules.pullback
      (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) ρ.left)).obj
        (schemeReading E ψY) ⟶ TU)
    {N₁ L₁ N₂ L₂ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
    {ε₁ : representedZariskiModule B S hS T L₁ ≅ TU}
    {ε₂ : representedZariskiModule B S hS T L₂ ≅ TU} {q₁ : N₁ ⟶ L₁} {q₂ : N₂ ⟶ L₂}
    {κ₁ : N₁ ≅ (modulePullback B S hS ψU).obj E} {κ₂ : N₂ ≅ (modulePullback B S hS ψU).obj E}
    (h₁ : QuotientReadingHyp E hE wρ univ ε₁ q₁ κ₁)
    (h₂ : QuotientReadingHyp E hE wρ univ ε₂ q₂ κ₂)
    (hN₁ : N₁.IsQuasicoherentOnSite) (hL₁ : L₁.IsQuasicoherentOnSite)
    (hL₂ : L₂.IsQuasicoherentOnSite) :
    ∃ β : L₁ ≅ L₂, q₁ ≫ β.hom = (κ₁ ≪≫ κ₂.symm).hom ≫ q₂ := by
  unfold QuotientReadingHyp quotientReadingOf at h₁ h₂
  obtain ⟨u, hu⟩ := (QuasiCoherentDescent.bijective_representedZariski_map B S hS L₁ L₂ hL₁).2
    (ε₁.hom ≫ ε₂.inv)
  obtain ⟨v, hv⟩ := (QuasiCoherentDescent.bijective_representedZariski_map B S hS L₂ L₁ hL₂).2
    (ε₂.hom ≫ ε₁.inv)
  dsimp only at hu hv
  let F := (representedSmallEtaleModuleEquivalence B S hS T).inverse ⋙
    SmallEtale.restrictModule (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj T)
      T.left.property
  have inv_comp : ∀ {P Q : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)}
      (hP : P.IsQuasicoherentOnSite) (a : P ⟶ Q) (b : Q ⟶ P)
      (εP : representedZariskiModule B S hS T P ≅ TU)
      (εQ : representedZariskiModule B S hS T Q ≅ TU),
      F.map a = εP.hom ≫ εQ.inv → F.map b = εQ.hom ≫ εP.inv → a ≫ b = 𝟙 P :=
    fun {P Q} hP a b εP εQ ha hb =>
    (QuasiCoherentDescent.bijective_representedZariski_map B S hS P P hP).1 (by
      change F.map (a ≫ b) = F.map (𝟙 P)
      simp [ha, hb])
  refine ⟨⟨u, v, inv_comp hL₁ u v ε₁ ε₂ hu hv, inv_comp hL₂ v u ε₂ ε₁ hv hu⟩, ?_⟩
  refine (QuasiCoherentDescent.bijective_representedZariski_map B S hS N₁ L₂ hN₁).1 ?_
  dsimp only
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [h₁, h₂, hu]
  simp [← CategoryTheory.Functor.map_comp_assoc]

end Generic

end AlgebraicGeometry.Space

end
