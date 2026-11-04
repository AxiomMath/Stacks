module

public import StacksFrontier.AlgebraicGeometry.Groupoids.DescentIso
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointPresentation

/-!
# The twists `𝒪_P(n)` restricted to a scheme point of the base

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B and
`𝒪_P(n)` the twist of Stacks 084D (`AlgebraicGeometry.Space.RelativeProjSituation.twistModule`),
descended from a presentation `X = U/R`.  For **every** scheme point `f : T ⟶ X` (an object `T` of
the site, not only the atlas), the inverse image of `𝒪_P(n)` along the base change
`T ×_X P = Proj_T(f^*𝒜) ⟶ P` is the twist `𝒪(n)` of Stacks 01NR on `Proj_T(f^*𝒜)`: this is the
base change clause of Stacks 084D, degree by degree.  This file supplies its scheme-level
ingredients.

As in the source, the identification is computed on an étale cover: over `T_U = T ×_X U` both
sides become the twist of Stacks 01NR on `T_U ×_X P = Proj_{T_U}(f^*𝒜|_{T_U})`, through the
comparisons of twists of Tag 01O3 along `T_U ×_X P ⟶ U ×_X P` and along `T_U ×_X P ⟶ T ×_X P`;
these comparisons carry the two transitions on `T_R ×_X P` into each other (the cocycle of the
comparisons, Module B4), so the identification descends along the presentation
`T ×_X P = (T_U ×_X P)/(T_R ×_X P)` (Stacks 03M3).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.pointFibreTwistTransition`: the transition of the
  twists on the presentation of `T ×_X P`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointFibreChartTwistComparison`,
  `…pointFibreAtlasTwistComparison`: the comparisons of twists along `T_U ×_X P ⟶ U ×_X P` and
  along `T_U ×_X P ⟶ T ×_X P`.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.twistPieceComparison_comp_hom`: the cocycle of
  the comparisons of twists, as quasi-coherent modules.
* `AlgebraicGeometry.Space.RelativeProjSituation.schemePairTransition_twistPieceComparison` and
  `…canonicalSchemeTransition_twistPieceComparison`: the comparisons of twists carry the
  pulled-back transitions to the transition of the twists, at variable points.
* `…canonicalSchemeTransition_pointFibreAtlasTwistComparison` (in the same namespace): the
  comparison along the atlas of `T ×_X P` carries the canonical transition of the pulled-back
  twist to the transition of the twists of `T ×_X P`.

The descent of the identification itself
(`AlgebraicGeometry.Space.presentationIsoOfChartIsos` along
`AlgebraicGeometry.Space.RelativeProjPoints.pointFibrePresentation`) is not carried out in this
file.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-- The telescoping of a pulled-back transition through comparisons to a common module, at
variables. -/
theorem pairTransition_telescope_of_comparisons {C : Type*} [Category C]
    {At As Bt Bs Ct Cs Dt Ds E : C} (ct : At ≅ Bt) (cs : As ≅ Bs) (et : Bt ⟶ Ct) (es : Cs ⟶ Bs)
    (ρ : Ct ⟶ Cs) (mt : At ⟶ Dt) (ms : As ⟶ Ds) (Tt : Dt ≅ E) (Ts : Ds ≅ E) (ΘBt : Bt ≅ E)
    (ΘBs : Bs ≅ E) (ΘCt : Ct ≅ E) (ΘCs : Cs ≅ E)
    (hρ : ρ = ΘCt.hom ≫ ΘCs.inv) (hBt : ΘBt.hom = ct.inv ≫ mt ≫ Tt.hom)
    (hBs : ΘBs.hom = cs.inv ≫ ms ≫ Ts.hom) (het : et ≫ ΘCt.hom = ΘBt.hom)
    (hes : es ≫ ΘBs.hom = ΘCs.hom) :
    (ct.hom ≫ (et ≫ ρ ≫ es) ≫ cs.inv) ≫ ms = mt ≫ Tt.hom ≫ Ts.inv := by
  rw [← cancel_mono Ts.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← hBs, hes, hρ, Category.assoc, Iso.inv_hom_id, Category.comp_id, het, hBt,
    Iso.hom_inv_id_assoc]

/-- The canonical transition through comparisons to a common module, at variables. -/
theorem canonicalTransition_of_comparisons {C : Type*} [Category C]
    {At As Bt Bs Dt Ds E : C} (ct : At ≅ Bt) (cs : As ≅ Bs) (e : Bt ⟶ Bs) (mt : At ⟶ Dt)
    (ms : As ⟶ Ds) (Tt : Dt ≅ E) (Ts : Ds ≅ E) (Θt : Bt ≅ E) (Θs : Bs ≅ E)
    (hΘt : Θt.hom = ct.inv ≫ mt ≫ Tt.hom) (hΘs : Θs.hom = cs.inv ≫ ms ≫ Ts.hom)
    (he : e ≫ Θs.hom = Θt.hom) :
    (ct.hom ≫ e ≫ cs.inv) ≫ ms = mt ≫ Tt.hom ≫ Ts.inv := by
  rw [← cancel_mono Ts.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h : cs.inv ≫ ms ≫ Ts.hom = Θs.hom := hΘs.symm
  rw [h, he, hΘt, Iso.hom_inv_id_assoc]

/-- An isomorphism of pullbacks along a composite whose underlying morphism of sheaves is the
contraction followed by the pullback of `αt` and by `αx` is, as a morphism of quasi-coherent
modules, the inverse contraction followed by the pullback of `αt` and by `αx`. -/
theorem quasicoherentPullback_comp_hom_of_sheaf_eq (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W V U : BigFppfOver B S hS} (x : W ⟶ V) (t : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    {N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf).FullSubcategory}
    {E : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory}
    (αt : quasicoherentPullbackObj B S hS t M ≅ N) (αx : quasicoherentPullbackObj B S hS x N ≅ E)
    (αtt : quasicoherentPullbackObj B S hS (x ≫ t) M ≅ E)
    (βt : (quasicoherentPullbackObj B S hS t M).obj ⟶ N.obj) (hβt : αt.hom.hom = βt)
    (βx : (quasicoherentPullbackObj B S hS x N).obj ⟶ E.obj) (hβx : αx.hom.hom = βx)
    (βtt : (quasicoherentPullbackObj B S hS (x ≫ t) M).obj ⟶ E.obj) (hβtt : αtt.hom.hom = βtt)
    (h : βtt =
      (Scheme.Modules.pullbackCongr ((BigFppfOver.toScheme B S hS).map_comp x t)).hom.app M.obj ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map x)
          ((BigFppfOver.toScheme B S hS).map t)).inv.app M.obj ≫
          (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map x)).map βt ≫ βx) :
    αtt.hom = (quasicoherentPullbackCompIso B S hS x t M).inv ≫
      quasicoherentPullbackMap B S hS x αt.hom ≫ αx.hom := by
  subst hβt hβx hβtt
  exact ObjectProperty.hom_ext _ (h.trans ((congrArg (· ≫ _)
    (Stacks.Groupoids.pullbackCongr_hom_app_self _ _)).trans (Category.id_comp _)))

/-- A functor sends a composite to the composite of the maps, so compatibility with a point
passes to composites. -/
private theorem map_comp_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} {A : D} (a : X ⟶ Y) (b : Y ⟶ Z) {u : F.obj Z ⟶ A} {v : F.obj Y ⟶ A}
    {w : F.obj X ⟶ A} (hb : F.map b ≫ u = v) (ha : F.map a ≫ v = w) :
    F.map (a ≫ b) ≫ u = w := by
  rw [Functor.map_comp, Category.assoc, hb, ha]

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-! ### The comparisons of twists at variable points -/

section VariablePoints

/-- **The cocycle of the comparisons of the twists, as quasi-coherent modules**: along a composite
`y' ≫ y` lying over `k' ≫ k`, the comparison is the comparison along `y`, pulled back along `y'`
and contracted, followed by the comparison along `y'`. -/
theorem twistPieceComparison_comp_hom {U V W : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1}
    {w : yoneda.obj W ⟶ s.space.1} (k : V ⟶ U) (k' : W ⟶ V)
    (hv : yoneda.map k ≫ u = v) (hw : yoneda.map k' ≫ v = w)
    (hw'' : yoneda.map (k' ≫ k) ≫ u = w)
    (y : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (y' : s.relativeProjPoints.fibre W w ⟶ s.relativeProjPoints.fibre V v)
    (hy : s.relativeProjPoints.LiesOver y k) (hy' : s.relativeProjPoints.LiesOver y' k') (n : ℤ) :
    (s.twistPieceComparison (k' ≫ k) hw'' (y' ≫ y) (hy.comp hy') n).hom =
      (quasicoherentPullbackCompIso s.site s.base s.containsBase y' y
          (s.twistPieceQcoh U u n)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase y'
          (s.twistPieceComparison k hv y hy n).hom ≫
          (s.twistPieceComparison k' hw y' hy' n).hom :=
  quasicoherentPullback_comp_hom_of_sheaf_eq s.site s.base s.containsBase y' y
    (s.twistPieceQcoh U u n) (s.twistPieceComparison k hv y hy n)
    (s.twistPieceComparison k' hw y' hy' n)
    (s.twistPieceComparison (k' ≫ k) hw'' (y' ≫ y) (hy.comp hy') n) _
    (s.twistPieceComparison_hom_hom _ _ _ _ n) _ (s.twistPieceComparison_hom_hom _ _ _ _ n) _
    (s.twistPieceComparison_hom_hom _ _ _ _ n)
    (s.twistPieceComparison_comp k k' hv hw hw'' y y' hy hy' n)

/-- The comparisons of twists along two equal morphisms lying over equal morphisms agree, through
the identification of the pullbacks. -/
theorem quasicoherentPullbackEqToHom_comp_twistPieceComparison_hom
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {k₁ k₂ : V ⟶ U}
    {hv₁ : yoneda.map k₁ ≫ u = v} {hv₂ : yoneda.map k₂ ≫ u = v}
    {y₁ y₂ : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u}
    {hy₁ : s.relativeProjPoints.LiesOver y₁ k₁} {hy₂ : s.relativeProjPoints.LiesOver y₂ k₂}
    (e : y₁ = y₂) (hk : k₁ = k₂) (n : ℤ) :
    quasicoherentPullbackEqToHom s.site s.base s.containsBase e (s.twistPieceQcoh U u n) ≫
        (s.twistPieceComparison k₂ hv₂ y₂ hy₂ n).hom =
      (s.twistPieceComparison k₁ hv₁ y₁ hy₁ n).hom := by
  subst e hk
  exact (congrArg (· ≫ _) (quasicoherentPullbackEqToHom_rfl s.site s.base s.containsBase _)).trans
    (Category.id_comp _)

/-- **The comparison of twists along a morphism of the presenting schemes carries the pulled-back
transition of the twists to the transition of the twists**, at variable points: for projections
`tR, sR : R ×_X P ⇉ U ×_X P` and `tR'', sR'' : R'' ×_X P ⇉ U'' ×_X P` lying over `kt, ks` and
`kt'', ks''`, and morphisms `yU`, `yR` lying over `ℓ`, `ℓR` compatible with the projections. -/
theorem schemePairTransition_twistPieceComparison
    {U R U'' R'' : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {r : yoneda.obj R ⟶ s.space.1}
    {u'' : yoneda.obj U'' ⟶ s.space.1} {r'' : yoneda.obj R'' ⟶ s.space.1}
    (kt ks : R ⟶ U) (hrt : yoneda.map kt ≫ u = r) (hrs : yoneda.map ks ≫ u = r)
    (tR sR : s.relativeProjPoints.fibre R r ⟶ s.relativeProjPoints.fibre U u)
    (htR : s.relativeProjPoints.LiesOver tR kt) (hsR : s.relativeProjPoints.LiesOver sR ks)
    (kt'' ks'' : R'' ⟶ U'') (hrt'' : yoneda.map kt'' ≫ u'' = r'')
    (hrs'' : yoneda.map ks'' ≫ u'' = r'')
    (tR'' sR'' : s.relativeProjPoints.fibre R'' r'' ⟶ s.relativeProjPoints.fibre U'' u'')
    (htR'' : s.relativeProjPoints.LiesOver tR'' kt'')
    (hsR'' : s.relativeProjPoints.LiesOver sR'' ks'')
    (ℓ : U'' ⟶ U) (hℓ : yoneda.map ℓ ≫ u = u'')
    (yU : s.relativeProjPoints.fibre U'' u'' ⟶ s.relativeProjPoints.fibre U u)
    (hyU : s.relativeProjPoints.LiesOver yU ℓ)
    (ℓR : R'' ⟶ R) (hℓR : yoneda.map ℓR ≫ r = r'')
    (yR : s.relativeProjPoints.fibre R'' r'' ⟶ s.relativeProjPoints.fibre R r)
    (hyR : s.relativeProjPoints.LiesOver yR ℓR)
    (hta : tR'' ≫ yU = yR ≫ tR) (hsb : yR ≫ sR = sR'' ≫ yU)
    (hbt : kt'' ≫ ℓ = ℓR ≫ kt) (hbs : ℓR ≫ ks = ks'' ≫ ℓ) (n : ℤ) :
    schemePairTransition s.site s.base s.containsBase yU yR hta hsb (s.twistPieceQcoh U u n)
        ((s.twistPieceComparison kt hrt tR htR n).hom ≫
          (s.twistPieceComparison ks hrs sR hsR n).inv) ≫
      quasicoherentPullbackMap s.site s.base s.containsBase sR''
        (s.twistPieceComparison ℓ hℓ yU hyU n).hom =
    quasicoherentPullbackMap s.site s.base s.containsBase tR''
        (s.twistPieceComparison ℓ hℓ yU hyU n).hom ≫
      (s.twistPieceComparison kt'' hrt'' tR'' htR'' n).hom ≫
        (s.twistPieceComparison ks'' hrs'' sR'' hsR'' n).inv := by
  have pt := map_comp_comp_eq yoneda ℓR kt hrt hℓR
  have ps := map_comp_comp_eq yoneda ℓR ks hrs hℓR
  have pt'' := map_comp_comp_eq yoneda kt'' ℓ hℓ hrt''
  have ps'' := map_comp_comp_eq yoneda ks'' ℓ hℓ hrs''
  exact pairTransition_telescope_of_comparisons
    (quasicoherentPullbackCompIso s.site s.base s.containsBase tR'' yU (s.twistPieceQcoh U u n))
    (quasicoherentPullbackCompIso s.site s.base s.containsBase sR'' yU (s.twistPieceQcoh U u n))
    (quasicoherentPullbackEqToHom s.site s.base s.containsBase hta (s.twistPieceQcoh U u n))
    (quasicoherentPullbackEqToHom s.site s.base s.containsBase hsb (s.twistPieceQcoh U u n))
    (schemeTransitionReindex s.site s.base s.containsBase tR sR (s.twistPieceQcoh U u n)
      ((s.twistPieceComparison kt hrt tR htR n).hom ≫
        (s.twistPieceComparison ks hrs sR hsR n).inv) yR)
    (quasicoherentPullbackMap s.site s.base s.containsBase tR''
      (s.twistPieceComparison ℓ hℓ yU hyU n).hom)
    (quasicoherentPullbackMap s.site s.base s.containsBase sR''
      (s.twistPieceComparison ℓ hℓ yU hyU n).hom)
    (s.twistPieceComparison kt'' hrt'' tR'' htR'' n)
    (s.twistPieceComparison ks'' hrs'' sR'' hsR'' n)
    (s.twistPieceComparison (kt'' ≫ ℓ) pt'' (tR'' ≫ yU) (hyU.comp htR'') n)
    (s.twistPieceComparison (ks'' ≫ ℓ) ps'' (sR'' ≫ yU) (hyU.comp hsR'') n)
    (s.twistPieceComparison (ℓR ≫ kt) pt (yR ≫ tR) (htR.comp hyR) n)
    (s.twistPieceComparison (ℓR ≫ ks) ps (yR ≫ sR) (hsR.comp hyR) n)
    (s.schemeTransitionReindex_twistPieceComparison kt ks hrt hrs tR sR htR hsR ℓR hℓR yR hyR pt
      ps n)
    (s.twistPieceComparison_comp_hom ℓ kt'' hℓ hrt'' pt'' yU tR'' hyU htR'' n)
    (s.twistPieceComparison_comp_hom ℓ ks'' hℓ hrs'' ps'' yU sR'' hyU hsR'' n)
    (s.quasicoherentPullbackEqToHom_comp_twistPieceComparison_hom hta hbt n)
    (s.quasicoherentPullbackEqToHom_comp_twistPieceComparison_hom hsb hbs n)

/-- **The comparison of twists along a morphism `q` carries the canonical transition of the
pulled-back twist to the transition of the twists**, at variable points: for projections
`t, s : R ×_X P ⇉ V ×_X P` lying over `kt, ks` with `t ≫ q = s ≫ q` and `kt ≫ kq = ks ≫ kq`, and
`q : V ×_X P ⟶ W ×_X P` lying over `kq`. -/
theorem canonicalSchemeTransition_twistPieceComparison
    {W V R : BigFppfOver s.site s.base s.containsBase}
    {w : yoneda.obj W ⟶ s.space.1} {v : yoneda.obj V ⟶ s.space.1} {r : yoneda.obj R ⟶ s.space.1}
    (kq : V ⟶ W) (hv : yoneda.map kq ≫ w = v)
    (q : s.relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre W w)
    (hq : s.relativeProjPoints.LiesOver q kq)
    (kt ks : R ⟶ V) (hrt : yoneda.map kt ≫ v = r) (hrs : yoneda.map ks ≫ v = r)
    (t' s' : s.relativeProjPoints.fibre R r ⟶ s.relativeProjPoints.fibre V v)
    (ht' : s.relativeProjPoints.LiesOver t' kt) (hs' : s.relativeProjPoints.LiesOver s' ks)
    (hts : t' ≫ q = s' ≫ q) (hk : kt ≫ kq = ks ≫ kq) (n : ℤ) :
    canonicalSchemeTransition s.site s.base s.containsBase t' s' q hts (s.twistPieceQcoh W w n) ≫
      quasicoherentPullbackMap s.site s.base s.containsBase s'
        (s.twistPieceComparison kq hv q hq n).hom =
    quasicoherentPullbackMap s.site s.base s.containsBase t'
        (s.twistPieceComparison kq hv q hq n).hom ≫
      (s.twistPieceComparison kt hrt t' ht' n).hom ≫
        (s.twistPieceComparison ks hrs s' hs' n).inv := by
  have pt := map_comp_comp_eq yoneda kt kq hv hrt
  have ps := map_comp_comp_eq yoneda ks kq hv hrs
  exact canonicalTransition_of_comparisons
    (quasicoherentPullbackCompIso s.site s.base s.containsBase t' q (s.twistPieceQcoh W w n))
    (quasicoherentPullbackCompIso s.site s.base s.containsBase s' q (s.twistPieceQcoh W w n))
    (quasicoherentPullbackEqToHom s.site s.base s.containsBase hts (s.twistPieceQcoh W w n))
    (quasicoherentPullbackMap s.site s.base s.containsBase t'
      (s.twistPieceComparison kq hv q hq n).hom)
    (quasicoherentPullbackMap s.site s.base s.containsBase s'
      (s.twistPieceComparison kq hv q hq n).hom)
    (s.twistPieceComparison kt hrt t' ht' n) (s.twistPieceComparison ks hrs s' hs' n)
    (s.twistPieceComparison (kt ≫ kq) pt (t' ≫ q) (hq.comp ht') n)
    (s.twistPieceComparison (ks ≫ kq) ps (s' ≫ q) (hq.comp hs') n)
    (s.twistPieceComparison_comp_hom kq kt hv hrt pt q t' hq ht' n)
    (s.twistPieceComparison_comp_hom kq ks hv hrs ps q s' hq hs' n)
    (s.quasicoherentPullbackEqToHom_comp_twistPieceComparison_hom hts hk n)

end VariablePoints

/-! ### The identification over a scheme point of the base -/

section Point

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- The target projection of `T_R ⇉ T_U` is compatible with the points of `X`. -/
theorem alongPointTarget_point :
    yoneda.map (Px.alongPointTarget f) ≫ ((Px.alongPoint f).toSpace ≫ f) =
      RelativeProjPoints.relationPoint (Px.alongPoint f) ≫ f :=
  (Category.assoc _ _ _).symm

/-- The source projection of `T_R ⇉ T_U` is compatible with the points of `X`. -/
theorem alongPointSource_point :
    yoneda.map (Px.alongPointSource f) ≫ ((Px.alongPoint f).toSpace ≫ f) =
      RelativeProjPoints.relationPoint (Px.alongPoint f) ≫ f :=
  (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) (Px.alongPoint f).isPullback.w.symm)

/-- **The scheme transition of the twist `𝒪(n)` on the presentation
`T ×_X P = (T_U ×_X P)/(T_R ×_X P)`**: the comparison of twists along the target projection
followed by the inverse of the comparison along the source projection. -/
abbrev pointFibreTwistTransition (n : ℤ) :
    quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.pointFibreTargetMap (X := s.space) Px T f)
        (s.twistPieceQcoh (Px.alongPoint f).U ((Px.alongPoint f).toSpace ≫ f) n) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase
        (s.relativeProjPoints.pointFibreSourceMap (X := s.space) Px T f)
        (s.twistPieceQcoh (Px.alongPoint f).U ((Px.alongPoint f).toSpace ≫ f) n) :=
  (s.twistPieceComparison (Px.alongPointTarget f) (s.alongPointTarget_point Px T f)
      (s.relativeProjPoints.pointFibreTargetMap (X := s.space) Px T f)
      (s.relativeProjPoints.liesOver_pointFibreTarget (X := s.space) Px T f) n).hom ≫
    (s.twistPieceComparison (Px.alongPointSource f) (s.alongPointSource_point Px T f)
      (s.relativeProjPoints.pointFibreSourceMap (X := s.space) Px T f)
      (s.relativeProjPoints.liesOver_pointFibreSource (X := s.space) Px T f) n).inv

/-- The comparison `(T_U ×_X P ⟶ U ×_X P)^*𝒪(n) ≅ 𝒪(n)` of the twists along the morphism of the
presenting schemes. -/
abbrev pointFibreChartTwistComparison (n : ℤ) :=
  s.twistPieceComparison (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
    (s.relativeProjPoints.pointFibreChartMap (X := s.space) Px T f)
    (s.relativeProjPoints.liesOver_fibreMapOver _ _) n

/-- The comparison `(T_U ×_X P ⟶ T ×_X P)^*𝒪(n) ≅ 𝒪(n)` of the twists along the atlas of the
presentation of `T ×_X P`. -/
abbrev pointFibreAtlasTwistComparison (n : ℤ) :=
  s.twistPieceComparison (u := f) (v := (Px.alongPoint f).toSpace ≫ f) (Px.alongPointToPoint f) rfl
    (s.relativeProjPoints.pointFibreAtlasMap (X := s.space) Px T f)
    (s.relativeProjPoints.liesOver_pointFibreAtlasMap (X := s.space) Px T f) n

/-- The comparison along the atlas of the presentation of `T ×_X P` carries the canonical
transition of the pulled-back twist of `T ×_X P` to the transition of the twists. -/
theorem canonicalSchemeTransition_pointFibreAtlasTwistComparison (n : ℤ) :
    canonicalSchemeTransition s.site s.base s.containsBase
        (s.relativeProjPoints.pointFibreTargetMap (X := s.space) Px T f)
        (s.relativeProjPoints.pointFibreSourceMap (X := s.space) Px T f)
        (s.relativeProjPoints.pointFibreAtlasMap (X := s.space) Px T f)
        (s.relativeProjPoints.pointFibreTarget_comp_atlasMap (X := s.space) Px T f)
        (s.twistPieceQcoh T f n) ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        (s.relativeProjPoints.pointFibreSourceMap (X := s.space) Px T f)
        (s.pointFibreAtlasTwistComparison Px T f n).hom =
    quasicoherentPullbackMap s.site s.base s.containsBase
        (s.relativeProjPoints.pointFibreTargetMap (X := s.space) Px T f)
        (s.pointFibreAtlasTwistComparison Px T f n).hom ≫ s.pointFibreTwistTransition Px T f n :=
  s.canonicalSchemeTransition_twistPieceComparison (w := f)
    (v := (Px.alongPoint f).toSpace ≫ f)
    (r := RelativeProjPoints.relationPoint (Px.alongPoint f) ≫ f)
    (Px.alongPointToPoint f) rfl (s.relativeProjPoints.pointFibreAtlasMap (X := s.space) Px T f)
    (s.relativeProjPoints.liesOver_pointFibreAtlasMap (X := s.space) Px T f)
    (Px.alongPointTarget f) (Px.alongPointSource f) (s.alongPointTarget_point Px T f)
    (s.alongPointSource_point Px T f)
    (s.relativeProjPoints.pointFibreTargetMap (X := s.space) Px T f)
    (s.relativeProjPoints.pointFibreSourceMap (X := s.space) Px T f)
    (s.relativeProjPoints.liesOver_pointFibreTarget (X := s.space) Px T f)
    (s.relativeProjPoints.liesOver_pointFibreSource (X := s.space) Px T f)
    (s.relativeProjPoints.pointFibreTarget_comp_atlasMap (X := s.space) Px T f)
    (Px.alongPointTarget_comp_toPoint f) n

end Point

end RelativeProjSituation

end AlgebraicGeometry.Space

end
