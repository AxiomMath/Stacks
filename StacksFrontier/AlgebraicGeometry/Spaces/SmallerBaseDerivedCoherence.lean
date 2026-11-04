module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardAssoc
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquareMates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesCompAssoc

/-!
# Coherence of the change of base with composition

Let `h : W ⟶ S` be a morphism of a big fppf site and let `f : Z₁ ⟶ Z₂`, `f' : Z₂ ⟶ Z₃` over `W`
and `g : Y₁ ⟶ Y₂`, `g' : Y₂ ⟶ Y₃` over `S` be representable morphisms of algebraic spaces matched
by identifications `Λ_h Zᵢ ≅ Yᵢ` (Stacks 04SG).
`StacksFrontier/AlgebraicGeometry/Spaces/SmallerBaseDerived.lean` compares the pullbacks of modules
along `g` and along `f` through the change of base
(`AlgebraicGeometry.Space.smallerBasePullbackIso`), and derives the compatibility of the derived
comparison with the composition isomorphisms of Stacks 0D6D from a module-level coherence, the
proposition `AlgebraicGeometry.Space.SmallerBasePullbackIsoCoherent`. This file proves that
proposition.

The comparison of pullbacks is the inverse of the mate of the comparison of direct images
`AlgebraicGeometry.Space.smallerBasePushforwardIso`, and the composition isomorphisms of pullbacks
are conjugate to those of direct images. So the coherence is the coherence of the direct images
(`AlgebraicGeometry.Space.isCompSquareCoherent_of_mates`). The comparison of direct images is,
through the chart comparisons `AlgebraicGeometry.Space.modulePushforwardChartIso`, a comparison of
base-change direct images (`AlgebraicGeometry.Space.isCompSquareCoherent_transport`); those are
pushforwards along squares of functors of small étale sites, and their coherence is the identity
of charts `AlgebraicGeometry.Space.relocalizeBaseChangeNatIso_comp`, checked on the cartesian
projections.

## Main results

* `AlgebraicGeometry.Space.smallerBasePullbackIsoCoherent`: the module-level coherence.
* `AlgebraicGeometry.Space.smallerBaseDerivedPullbackIso_comp`: the derived comparison of
  Stacks 04SG is compatible with the composition isomorphisms of Stacks 0D6D.

Nothing here is registered; it is internal to the change of base of Stacks 0DIQ.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

/-! ### Coherence of mates with composition -/

section CompMates

variable {C₁ C₂ C₃ C₁' C₂' C₃' : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₁'] [Category* C₂'] [Category* C₃']
  {Lg : C₂ ⥤ C₁} {Rg : C₁ ⥤ C₂} {Lg' : C₃ ⥤ C₂} {Rg' : C₂ ⥤ C₃} {Lgg : C₃ ⥤ C₁}
  {Rgg : C₁ ⥤ C₃} {Lf : C₂' ⥤ C₁'} {Rf : C₁' ⥤ C₂'} {Lf' : C₃' ⥤ C₂'} {Rf' : C₂' ⥤ C₃'}
  {Lff : C₃' ⥤ C₁'} {Rff : C₁' ⥤ C₃'} {Φ₁ : C₁ ⥤ C₁'} {Φ₂ : C₂ ⥤ C₂'} {Φ₃ : C₃ ⥤ C₃'}

/-- The mate of the square given by the inverse of `κ` is `σ` when `κ.inv` is the inverse mate
of `σ`. -/
private theorem mateEquiv_mk_inv_eq (ag : Lg ⊣ Rg) (af : Lf ⊣ Rf) (κ : Lg ⋙ Φ₁ ≅ Φ₂ ⋙ Lf)
    (σ : Rg ⋙ Φ₂ ≅ Φ₁ ⋙ Rf) (h : κ.inv = ((mateEquiv ag af).symm σ.hom).natTrans) :
    mateEquiv ag af (TwoSquare.mk _ _ _ _ κ.inv) = σ.hom := by
  rw [h]; exact Equiv.apply_symm_apply _ _

open TwoSquare in
/-- **Mates of coherent squares are coherent.** Let `κ` be squares of left adjoints whose
inverses are the mates of squares `σ` of the right adjoints, and let the composition isomorphisms
`c, c'` of the left adjoints be conjugate to the composition isomorphisms `d, d'` of the right
adjoints. If the `σ` are coherent with `d, d'`, the `κ` are coherent with `c, c'`: the mates of
the two sides agree by `CategoryTheory.mateEquiv_hcomp` and the compatibility of mates with
conjugates. -/
theorem isCompSquareCoherent_of_mates (ag : Lg ⊣ Rg) (ag' : Lg' ⊣ Rg') (agg : Lgg ⊣ Rgg)
    (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (aff : Lff ⊣ Rff)
    (c : Lg' ⋙ Lg ≅ Lgg) (c' : Lf' ⋙ Lf ≅ Lff) (d : Rg ⋙ Rg' ≅ Rgg) (d' : Rf ⋙ Rf' ≅ Rff)
    (hd : conjugateEquiv (ag'.comp ag) agg c.inv = d.hom)
    (hd' : conjugateEquiv (af'.comp af) aff c'.inv = d'.hom)
    (σg : Rg ⋙ Φ₂ ≅ Φ₁ ⋙ Rf) (σg' : Rg' ⋙ Φ₃ ≅ Φ₂ ⋙ Rf') (σgg : Rgg ⋙ Φ₃ ≅ Φ₁ ⋙ Rff)
    (κg : Lg ⋙ Φ₁ ≅ Φ₂ ⋙ Lf) (κg' : Lg' ⋙ Φ₂ ≅ Φ₃ ⋙ Lf') (κgg : Lgg ⋙ Φ₁ ≅ Φ₃ ⋙ Lff)
    (hκg : κg.inv = ((mateEquiv ag af).symm σg.hom).natTrans)
    (hκg' : κg'.inv = ((mateEquiv ag' af').symm σg'.hom).natTrans)
    (hκgg : κgg.inv = ((mateEquiv agg aff).symm σgg.hom).natTrans)
    (hσ : IsCompSquareCoherent d d' σg' σg σgg) :
    IsCompSquareCoherent c c' κg κg' κgg := by
  have key : ((TwoSquare.mk _ _ _ _ κg'.inv ≫ᵥ TwoSquare.mk _ _ _ _ κg.inv).whiskerRight
      c'.inv : TwoSquare Φ₃ (Lg' ⋙ Lg) Lff Φ₁) =
      (TwoSquare.mk _ _ _ _ κgg.inv).whiskerLeft c.inv := by
    apply (mateEquiv (ag'.comp ag) aff).injective
    rw [mateEquiv_conjugateEquiv_vcomp (ag'.comp ag) (af'.comp af) aff, mateEquiv_hcomp,
      conjugateEquiv_mateEquiv_vcomp (ag'.comp ag) agg aff, hd, hd',
      mateEquiv_mk_inv_eq ag af κg σg hκg, mateEquiv_mk_inv_eq ag' af' κg' σg' hκg',
      mateEquiv_mk_inv_eq agg aff κgg σgg hκgg]
    ext N
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp, TwoSquare.mk,
      TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Functor.comp_obj, Category.assoc]
    exact hσ N
  intro M
  have k := NatTrans.congr_app key M
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, TwoSquare.mk, TwoSquare.natTrans] at k
  have e : (κg.app (Lg'.obj M) ≪≫ Lf.mapIso (κg'.app M) ≪≫ c'.app (Φ₃.obj M)).symm =
      (Φ₁.mapIso (c.app M) ≪≫ κgg.app M).symm := by
    ext
    simpa using k
  exact congrArg (fun i => i.symm.hom) e

end CompMates

/-! ### Transport of the coherence along isomorphisms of the functors -/

section CompTransport

variable {C₁ C₂ C₃ C₁' C₂' C₃' : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₁'] [Category* C₂'] [Category* C₃']
  {pg : C₂ ⥤ C₁} {pg' : C₃ ⥤ C₂} {pgg : C₃ ⥤ C₁} {pf : C₂' ⥤ C₁'} {pf' : C₃' ⥤ C₂'}
  {pff : C₃' ⥤ C₁'} {qg : C₂ ⥤ C₁} {qg' : C₃ ⥤ C₂} {qgg : C₃ ⥤ C₁} {qf : C₂' ⥤ C₁'}
  {qf' : C₃' ⥤ C₂'} {qff : C₃' ⥤ C₁'} {Φ₁ : C₁ ⥤ C₁'} {Φ₂ : C₂ ⥤ C₂'} {Φ₃ : C₃ ⥤ C₃'}

/-- **Coherence transported along isomorphisms of the functors.** If the squares `κ` relating
functors `q` are coherent with composition isomorphisms `e, e'`, and isomorphisms `θ : p ≅ q`
carry composition isomorphisms `c, c'` of the `p` to `e, e'`, then the squares conjugated by the
`θ` are coherent with `c, c'`. -/
theorem isCompSquareCoherent_transport (c : pg' ⋙ pg ≅ pgg) (c' : pf' ⋙ pf ≅ pff)
    (e : qg' ⋙ qg ≅ qgg) (e' : qf' ⋙ qf ≅ qff) (θg : pg ≅ qg) (θg' : pg' ≅ qg')
    (θgg : pgg ≅ qgg) (θf : pf ≅ qf) (θf' : pf' ≅ qf') (θff : pff ≅ qff)
    (hc : c ≪≫ θgg = Functor.isoWhiskerRight θg' pg ≪≫ Functor.isoWhiskerLeft qg' θg ≪≫ e)
    (hc' : c' ≪≫ θff = Functor.isoWhiskerRight θf' pf ≪≫ Functor.isoWhiskerLeft qf' θf ≪≫ e')
    (κg : qg ⋙ Φ₁ ≅ Φ₂ ⋙ qf) (κg' : qg' ⋙ Φ₂ ≅ Φ₃ ⋙ qf') (κgg : qgg ⋙ Φ₁ ≅ Φ₃ ⋙ qff)
    (h : IsCompSquareCoherent e e' κg κg' κgg) :
    IsCompSquareCoherent c c'
      (Functor.isoWhiskerRight θg Φ₁ ≪≫ κg ≪≫ Functor.isoWhiskerLeft Φ₂ θf.symm)
      (Functor.isoWhiskerRight θg' Φ₂ ≪≫ κg' ≪≫ Functor.isoWhiskerLeft Φ₃ θf'.symm)
      (Functor.isoWhiskerRight θgg Φ₁ ≪≫ κgg ≪≫ Functor.isoWhiskerLeft Φ₃ θff.symm) := by
  intro M
  have h1 := h M
  have h2 := NatTrans.congr_app (congrArg Iso.hom hc) M
  have h3 := NatTrans.congr_app (congrArg Iso.hom hc') (Φ₃.obj M)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom] at h2 h3 ⊢
  have h3' : e'.hom.app (Φ₃.obj M) ≫ θff.inv.app (Φ₃.obj M) =
      θf.inv.app (qf'.obj (Φ₃.obj M)) ≫ pf.map (θf'.inv.app (Φ₃.obj M)) ≫
        c'.hom.app (Φ₃.obj M) := by
    rw [← cancel_mono (θff.hom.app (Φ₃.obj M))]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [h3, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id_app_assoc]
  have n1 := θf.inv.naturality (Φ₂.map (θg'.hom.app M) ≫ κg'.hom.app M)
  have n2 := κg.hom.naturality (θg'.hom.app M)
  have n3 := θg.hom.naturality (θg'.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc] at n1 n2 n3
  rw [← Functor.map_comp_assoc, h2, reassoc_of% n3]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% n1, ← reassoc_of% h1, reassoc_of% n2, h3']

end CompTransport

/-! ### The composition isomorphisms of pullbacks and of direct images are conjugate -/

section Conjugate

variable (B : BigFppfSite.{u}) {T : Scheme.{u}} {hT : B.Contains T}

/-- **The composition isomorphism of pullbacks is conjugate to that of direct images**: the
compositor of Stacks 03D6 followed by `AlgebraicGeometry.Space.pullbackModulesCompTransport`, read
under the adjunctions `g^* ⊣ g_*`, is
`AlgebraicGeometry.Space.pushforwardModulesCompAt`. -/
theorem conjugateEquiv_pullbackModulesCompTransport_inv {X X' X'' : AlgebraicSpaces B T hT}
    (a : X ⟶ X') (b : X' ⟶ X'') :
    conjugateEquiv
        ((RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B T hT b)).comp
          (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B T hT a)))
        (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B T hT (a ≫ b)))
        ((RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B T hT a)
          (smallEtaleRingedToposHom B T hT b)).symm ≪≫
            pullbackModulesCompTransport B T hT a b).inv =
      (pushforwardModulesCompAt B T hT a b).hom := by
  refine (conjugateEquiv_comp _
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B T hT a b)) _
    (RingedToposHom.pullbackModulesCompIso (smallEtaleRingedToposHom B T hT a)
      (smallEtaleRingedToposHom B T hT b)).hom
    (pullbackModulesCompTransport B T hT a b).inv).symm.trans ?_
  have h₁ := RingedToposHom.conjugateEquiv_pullbackModulesCompIso_hom
    (smallEtaleRingedToposHom B T hT a) (smallEtaleRingedToposHom B T hT b)
  have h₂ := (congrArg (conjugateEquiv
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHomComp B T hT a b))
      (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B T hT (a ≫ b))))
    (Stacks.CategoryTheory.leftAdjointUniq_inv _ _)).trans
    (Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _
      (pushforwardModulesCompTransport B T hT a b).symm _)
  exact congrArg₂ (· ≫ ·) h₁ h₂

end Conjugate

/-! ### Composition isomorphisms through two identifications of the functors -/

section CompFactor

variable {A₀ A₁ A₂ : Type*} [Category* A₀] [Category* A₁] [Category* A₂]

/-- `CategoryTheory.Functor.compIsoCongr` written with the transports of the two factors
whiskered. -/
theorem compIsoCongr_eq_isoWhisker {p p' : A₀ ⥤ A₁} {q q' : A₁ ⥤ A₂} {pq pq' : A₀ ⥤ A₂}
    (hp : p = p') (hq : q = q') (hpq : pq = pq') (P : p ⋙ q ≅ pq) :
    Functor.compIsoCongr hp hq hpq P =
      Functor.isoWhiskerRight (eqToIso hp).symm q' ≪≫ Functor.isoWhiskerLeft p (eqToIso hq).symm ≪≫
        P ≪≫ eqToIso hpq := by
  subst hp hq hpq
  ext
  simp [Functor.compIsoCongr]

/-- Composition isomorphisms read through two successive identifications of the functors: if `m`
is `c` read through `P` and `χ` carries `m` to `e`, then `P ≪≫ χ` carries `c` to `e`. -/
theorem compIso_trans_eq_of_factor {pa ma qa : A₀ ⥤ A₁} {pb mb qb : A₁ ⥤ A₂}
    {pab mab qab : A₀ ⥤ A₂} (Pa : pa ≅ ma) (Pb : pb ≅ mb) (Pab : pab ≅ mab) (χa : ma ≅ qa)
    (χb : mb ≅ qb) (χab : mab ≅ qab) (c : pa ⋙ pb ≅ pab) (m : ma ⋙ mb ≅ mab)
    (e : qa ⋙ qb ≅ qab)
    (hm : m = Functor.isoWhiskerRight Pa.symm mb ≪≫ Functor.isoWhiskerLeft pa Pb.symm ≪≫ c ≪≫ Pab)
    (hχ : Functor.isoWhiskerRight χa mb ≪≫ Functor.isoWhiskerLeft qa χb ≪≫ e = m ≪≫ χab) :
    c ≪≫ Pab ≪≫ χab =
      Functor.isoWhiskerRight (Pa ≪≫ χa) pb ≪≫ Functor.isoWhiskerLeft qa (Pb ≪≫ χb) ≪≫ e := by
  subst hm
  ext N
  have k := NatTrans.congr_app (congrArg Iso.hom hχ) N
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.symm_hom, Category.assoc] at k ⊢
  have n1 := Pb.hom.naturality (χa.hom.app N)
  have n2 := Pb.hom.naturality (Pa.hom.app N)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, k, reassoc_of% n2, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]

end CompFactor

/-! ### The chart comparisons of direct images and the composition isomorphisms -/

section ChartComp

variable (B : BigFppfSite.{u}) {T : Scheme.{u}} {hT : B.Contains T}
  {X X' X'' : AlgebraicSpaces B T hT} (a : X ⟶ X') (b : X' ⟶ X'')

/-- The composition isomorphism of direct images of Stacks 03LU is
`AlgebraicGeometry.Space.pushforwardModulesCompAt` read through the identifications
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`. -/
theorem modulePushforwardCompIso_eq_pushforwardModulesCompAt :
    modulePushforwardCompIso B T hT a b =
      Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B T hT a).symm
          (modulePushforward B T hT b) ≪≫
        Functor.isoWhiskerLeft (smallEtaleRingedToposHom B T hT a).pushforwardModules
          (pushforwardModulesIsoModulePushforward B T hT b).symm ≪≫
        pushforwardModulesCompAt B T hT a b ≪≫
          pushforwardModulesIsoModulePushforward B T hT (a ≫ b) := by
  refine (modulePushforwardCompIso_eq_compIsoCongr B T hT a b).trans
    ((compIsoCongr_eq_isoWhisker _ _ _ _).trans ?_)
  simp only [pushforwardModulesIsoModulePushforward_eq_eqToIso]
  rfl

variable (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom)
  (hab : yoneda.relativelyRepresentable (a ≫ b).hom)

/-- **The chart comparisons carry the composition isomorphism of direct images to the
contraction of base-change direct images**
(`AlgebraicGeometry.Space.modulePushforwardChartIso_comp`, read through
`AlgebraicGeometry.Space.pushforwardModulesIsoModulePushforward`). -/
theorem pushforwardModulesCompAt_trans_chartIso :
    pushforwardModulesCompAt B T hT a b ≪≫ (pushforwardModulesIsoModulePushforward B T hT (a ≫ b) ≪≫
        modulePushforwardChartIso B T hT (a ≫ b) hab) =
      Functor.isoWhiskerRight (pushforwardModulesIsoModulePushforward B T hT a ≪≫
          modulePushforwardChartIso B T hT a ha)
          (smallEtaleRingedToposHom B T hT b).pushforwardModules ≪≫
        Functor.isoWhiskerLeft (smallBaseChangeModulePushforward.{u, u} B T hT a ha)
          (pushforwardModulesIsoModulePushforward B T hT b ≪≫
            modulePushforwardChartIso B T hT b hb) ≪≫
        smallBaseChangeChartPushforwardCompIso B T hT a b ha hb hab :=
  compIso_trans_eq_of_factor _ _ _ _ _ _ _ _ _
    (modulePushforwardCompIso_eq_pushforwardModulesCompAt B a b)
    (modulePushforwardChartIso_comp B T hT a b ha hb hab)

end ChartComp

/-! ### Coherence of pushforwards along squares of site functors -/

section PushforwardSquares

universe w v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {𝒴₁ : Type u₁} {𝒴₂ : Type u₂} {𝒴₃ : Type u₃} {𝒵₁ : Type u₄} {𝒵₂ : Type u₅}
  {𝒵₃ : Type u₆} [Category.{v₁} 𝒴₁] [Category.{v₂} 𝒴₂] [Category.{v₃} 𝒴₃] [Category.{v₄} 𝒵₁]
  [Category.{v₅} 𝒵₂] [Category.{v₆} 𝒵₃]
  {J₁ : GrothendieckTopology 𝒴₁} {J₂ : GrothendieckTopology 𝒴₂} {J₃ : GrothendieckTopology 𝒴₃}
  {K₁ : GrothendieckTopology 𝒵₁} {K₂ : GrothendieckTopology 𝒵₂} {K₃ : GrothendieckTopology 𝒵₃}
  {R₁ : Sheaf J₁ RingCat.{w}} {R₂ : Sheaf J₂ RingCat.{w}} {R₃ : Sheaf J₃ RingCat.{w}}
  {R'₁ : Sheaf K₁ RingCat.{w}} {R'₂ : Sheaf K₂ RingCat.{w}} {R'₃ : Sheaf K₃ RingCat.{w}}
  {s : 𝒴₂ ⥤ 𝒴₁} {s' : 𝒴₃ ⥤ 𝒴₂} {s'' : 𝒴₃ ⥤ 𝒴₁} {t : 𝒵₂ ⥤ 𝒵₁} {t' : 𝒵₃ ⥤ 𝒵₂}
  {t'' : 𝒵₃ ⥤ 𝒵₁} {E₁ : 𝒵₁ ⥤ 𝒴₁} {E₂ : 𝒵₂ ⥤ 𝒴₂} {E₃ : 𝒵₃ ⥤ 𝒴₃}
  [s.IsContinuous J₂ J₁] [s'.IsContinuous J₃ J₂] [s''.IsContinuous J₃ J₁]
  [t.IsContinuous K₂ K₁] [t'.IsContinuous K₃ K₂] [t''.IsContinuous K₃ K₁]
  [E₁.IsContinuous K₁ J₁] [E₂.IsContinuous K₂ J₂] [E₃.IsContinuous K₃ J₃]
  [(s' ⋙ s).IsContinuous J₃ J₁] [(t' ⋙ t).IsContinuous K₃ K₁]
  [(t ⋙ E₁).IsContinuous K₂ J₁] [(E₂ ⋙ s).IsContinuous K₂ J₁]
  [(t' ⋙ E₂).IsContinuous K₃ J₂] [(E₃ ⋙ s').IsContinuous K₃ J₂]
  [(t'' ⋙ E₁).IsContinuous K₃ J₁] [(E₃ ⋙ s'').IsContinuous K₃ J₁]
  {φs : R₂ ⟶ (s.sheafPushforwardContinuous RingCat.{w} J₂ J₁).obj R₁}
  {φs' : R₃ ⟶ (s'.sheafPushforwardContinuous RingCat.{w} J₃ J₂).obj R₂}
  {φs'' : R₃ ⟶ (s''.sheafPushforwardContinuous RingCat.{w} J₃ J₁).obj R₁}
  {φt : R'₂ ⟶ (t.sheafPushforwardContinuous RingCat.{w} K₂ K₁).obj R'₁}
  {φt' : R'₃ ⟶ (t'.sheafPushforwardContinuous RingCat.{w} K₃ K₂).obj R'₂}
  {φt'' : R'₃ ⟶ (t''.sheafPushforwardContinuous RingCat.{w} K₃ K₁).obj R'₁}
  {ψ₁ : R'₁ ⟶ (E₁.sheafPushforwardContinuous RingCat.{w} K₁ J₁).obj R₁}
  {ψ₂ : R'₂ ⟶ (E₂.sheafPushforwardContinuous RingCat.{w} K₂ J₂).obj R₂}
  {ψ₃ : R'₃ ⟶ (E₃.sheafPushforwardContinuous RingCat.{w} K₃ J₃).obj R₃}

/-- **Pushforwards along squares of site functors are coherent with composition when the squares
are.** Each of the isomorphisms is a contraction of pushforwards followed by a restriction along
a natural isomorphism of site functors, so on sections it is a restriction map, and the claim is
the identity `hchart` of the morphisms of the sites it restricts along. -/
theorem isCompSquareCoherent_pushforward (κg : s'' ≅ s' ⋙ s) (κf : t'' ≅ t' ⋙ t)
    (ρ : t ⋙ E₁ ≅ E₂ ⋙ s) (ρ' : t' ⋙ E₂ ≅ E₃ ⋙ s') (ρ'' : t'' ⋙ E₁ ≅ E₃ ⋙ s'')
    (hκg : (φs' ≫ (s'.sheafPushforwardContinuous RingCat.{w} J₃ J₂).map φs) ≫
      (Functor.sheafPushforwardContinuousNatTrans κg.hom RingCat.{w} J₃ J₁).app R₁ = φs'')
    (hκf : (φt' ≫ (t'.sheafPushforwardContinuous RingCat.{w} K₃ K₂).map φt) ≫
      (Functor.sheafPushforwardContinuousNatTrans κf.hom RingCat.{w} K₃ K₁).app R'₁ = φt'')
    (hρ : (ψ₂ ≫ (E₂.sheafPushforwardContinuous RingCat.{w} K₂ J₂).map φs) ≫
      (Functor.sheafPushforwardContinuousNatTrans ρ.hom RingCat.{w} K₂ J₁).app R₁ =
        φt ≫ (t.sheafPushforwardContinuous RingCat.{w} K₂ K₁).map ψ₁)
    (hρ' : (ψ₃ ≫ (E₃.sheafPushforwardContinuous RingCat.{w} K₃ J₃).map φs') ≫
      (Functor.sheafPushforwardContinuousNatTrans ρ'.hom RingCat.{w} K₃ J₂).app R₂ =
        φt' ≫ (t'.sheafPushforwardContinuous RingCat.{w} K₃ K₂).map ψ₂)
    (hρ'' : (ψ₃ ≫ (E₃.sheafPushforwardContinuous RingCat.{w} K₃ J₃).map φs'') ≫
      (Functor.sheafPushforwardContinuousNatTrans ρ''.hom RingCat.{w} K₃ J₁).app R₁ =
        φt'' ≫ (t''.sheafPushforwardContinuous RingCat.{w} K₃ K₁).map ψ₁)
    (hchart : ∀ V, E₁.map (κf.hom.app V) ≫ ρ.hom.app (t'.obj V) ≫ s.map (ρ'.hom.app V) =
      ρ''.hom.app V ≫ κg.hom.app (E₃.obj V)) :
    IsCompSquareCoherent
      (SheafOfModules.pushforwardComp.{w} φs' φs ≪≫ SheafOfModules.pushforwardCongr₂.{w} _ κg hκg)
      (SheafOfModules.pushforwardComp.{w} φt' φt ≪≫ SheafOfModules.pushforwardCongr₂.{w} _ κf hκf)
      (SheafOfModules.pushforwardComp.{w} ψ₃ φs' ≪≫ SheafOfModules.pushforwardCongr₂.{w} _ ρ' hρ' ≪≫
        (SheafOfModules.pushforwardComp.{w} φt' ψ₂).symm)
      (SheafOfModules.pushforwardComp.{w} ψ₂ φs ≪≫ SheafOfModules.pushforwardCongr₂.{w} _ ρ hρ ≪≫
        (SheafOfModules.pushforwardComp.{w} φt ψ₁).symm)
      (SheafOfModules.pushforwardComp.{w} ψ₃ φs'' ≪≫
        SheafOfModules.pushforwardCongr₂.{w} _ ρ'' hρ'' ≪≫
        (SheafOfModules.pushforwardComp.{w} φt'' ψ₁).symm) := by
  intro M
  apply Stacks.ChartUnitTransport.hom_ext_val_app_apply_unop
  intro V x
  have k : ∀ y : M.val.obj (op (s.obj (s'.obj (E₃.obj V)))),
      M.val.map (E₁.map (κf.hom.app V)).op (M.val.map (ρ.hom.app (t'.obj V)).op
        (M.val.map (s.map (ρ'.hom.app V)).op y)) =
      M.val.map (ρ''.hom.app V).op (M.val.map (κg.hom.app (E₃.obj V)).op y) := by
    intro y
    rw [← M.val.map_comp_apply, ← M.val.map_comp_apply, ← M.val.map_comp_apply, ← op_comp,
      ← op_comp, ← op_comp, hchart V]
  exact k x

end PushforwardSquares

/-! ### The base change of charts and the change of base, with composition -/

section ChartsComp

variable (B : BigFppfSite.{u}) {W S : Scheme.{u}} {hW : B.Contains W} {hS : B.Contains S}

/-- The inverse of the comparison of iterated base-changed charts is compatible with the
projections to the chart. -/
theorem smallBaseChangeChartCompIso_inv_app_hom_left_snd {A C D : AlgebraicSpaces B S hS}
    (a : D ⟶ A) (b : A ⟶ C) (ha : yoneda.relativelyRepresentable a.hom)
    (hb : yoneda.relativelyRepresentable b.hom) (hab : yoneda.relativelyRepresentable (a ≫ b).hom)
    (V : SmallEtale B S hS C.1) :
    ((smallBaseChangeChartCompIso B S hS a b ha hb hab).inv.app V).hom.left ≫ hab.snd V.1.hom =
      ha.snd ((smallBaseChange B S hS b hb).obj V).1.hom ≫ hb.snd V.1.hom := by
  have e := toOver_map_chartBaseChangeCompComparison_comp_snd B S hS a b ha hb hab V
  have i := congrArg (fun k => k.hom.left)
    ((smallBaseChangeChartCompIso B S hS a b ha hb hab).inv_hom_id_app V)
  simp only [ObjectProperty.FullSubcategory.comp_hom, CostructuredArrow.comp_left,
    ObjectProperty.FullSubcategory.id_hom, CostructuredArrow.id_left] at i
  rw [← e]
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (· ≫ _) i).trans (Category.id_comp _)

variable (h : B.obj hW ⟶ B.obj hS) {Z₁ Z₂ Z₃ : AlgebraicSpaces B W hW}
  {Y₁ Y₂ Y₃ : AlgebraicSpaces B S hS}
  (ε₁ : (OverShriek.relocalizePresheafFunctor h).obj Z₁.1 ≅ Y₁.1)
  (ε₂ : (OverShriek.relocalizePresheafFunctor h).obj Z₂.1 ≅ Y₂.1)
  (ε₃ : (OverShriek.relocalizePresheafFunctor h).obj Z₃.1 ≅ Y₃.1)
  {f : Z₁ ⟶ Z₂} {f' : Z₂ ⟶ Z₃} {g : Y₁ ⟶ Y₂} {g' : Y₂ ⟶ Y₃}
  (hfg : ε₁.hom ≫ g.hom = (OverShriek.relocalizePresheafFunctor h).map f.hom ≫ ε₂.hom)
  (hf : yoneda.relativelyRepresentable f.hom) (hg : yoneda.relativelyRepresentable g.hom)
  (hfg' : ε₂.hom ≫ g'.hom = (OverShriek.relocalizePresheafFunctor h).map f'.hom ≫ ε₃.hom)
  (hf' : yoneda.relativelyRepresentable f'.hom) (hg' : yoneda.relativelyRepresentable g'.hom)
  (hfg'' : ε₁.hom ≫ (g ≫ g').hom =
    (OverShriek.relocalizePresheafFunctor h).map (f ≫ f').hom ≫ ε₃.hom)
  (hf'' : yoneda.relativelyRepresentable (f ≫ f').hom)
  (hg'' : yoneda.relativelyRepresentable (g ≫ g').hom)

/-- **Base change of charts commutes with the change of base compatibly with composition**: the
comparison `AlgebraicGeometry.Space.relocalizeBaseChangeNatIso` of the composite is the pasting of
the comparisons, read through `AlgebraicGeometry.Space.smallBaseChangeChartCompIso` on both
sides. Both sides are morphisms into a base-changed chart, so they agree when their cartesian
projections do. -/
theorem relocalizeBaseChangeNatIso_comp (V : SmallEtale B W hW Z₃.1) :
    (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.map
        ((smallBaseChangeChartCompIso B W hW f f' hf hf' hf'').hom.app V) ≫
      (relocalizeBaseChangeNatIso B h ε₁ ε₂ hfg hf hg).hom.app
        ((smallBaseChange B W hW f' hf').obj V) ≫
      (smallBaseChange B S hS g hg).map
        ((relocalizeBaseChangeNatIso B h ε₂ ε₃ hfg' hf' hg').hom.app V) =
    (relocalizeBaseChangeNatIso B h ε₁ ε₃ hfg'' hf'' hg'').hom.app V ≫
      (smallBaseChangeChartCompIso B S hS g g' hg hg' hg'').hom.app
        ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor.obj V) := by
  refine (Iso.comp_inv_eq ((smallBaseChangeChartCompIso B S hS g g' hg hg' hg'').app _)).1 ?_
  refine smallBaseChange_hom_ext B hg'' _ _ ?_
  have e₁ := smallBaseChangeChartCompIso_inv_app_hom_left_snd B g g' hg hg' hg''
    ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor.obj V)
  have e₂ : ((smallBaseChange B S hS g hg).map
        ((relocalizeBaseChangeNatIso B h ε₂ ε₃ hfg' hf' hg').hom.app V)).hom.left ≫
      hg.snd ((smallBaseChange B S hS g' hg').obj
        ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor.obj V)).1.hom =
      hg.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj
        ((smallBaseChange B W hW f' hf').obj V)).1.hom ≫
      ((relocalizeBaseChangeNatIso B h ε₂ ε₃ hfg' hf' hg').hom.app V).hom.left :=
    smallBaseChange_map_snd B S hS g hg _
  have e₃ : ((relocalizeBaseChangeNatIso B h ε₁ ε₂ hfg hf hg).hom.app
        ((smallBaseChange B W hW f' hf').obj V)).hom.left ≫
      hg.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor.obj
        ((smallBaseChange B W hW f' hf').obj V)).1.hom =
      (Over.map h).map (hf.snd ((smallBaseChange B W hW f' hf').obj V).1.hom) :=
    relocalizeBaseChangeChartIso_hom_snd B h ε₁ ε₂ hfg hf hg _
  have e₄ : ((relocalizeBaseChangeNatIso B h ε₂ ε₃ hfg' hf' hg').hom.app V).hom.left ≫
      hg'.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor.obj V).1.hom =
      (Over.map h).map (hf'.snd V.1.hom) :=
    relocalizeBaseChangeChartIso_hom_snd B h ε₂ ε₃ hfg' hf' hg' V
  have e₅ : ((relocalizeBaseChangeNatIso B h ε₁ ε₃ hfg'' hf'' hg'').hom.app V).hom.left ≫
      hg''.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor.obj V).1.hom =
      (Over.map h).map (hf''.snd V.1.hom) :=
    relocalizeBaseChangeChartIso_hom_snd B h ε₁ ε₃ hfg'' hf'' hg'' V
  have e₆ : ((smallBaseChangeChartCompIso B W hW f f' hf hf' hf'').hom.app V).hom.left ≫
      hf.snd ((smallBaseChange B W hW f' hf').obj V).1.hom ≫ hf'.snd V.1.hom = hf''.snd V.1.hom :=
    toOver_map_chartBaseChangeCompComparison_comp_snd B W hW f f' hf hf' hf'' V
  show ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.map
        ((smallBaseChangeChartCompIso B W hW f f' hf hf' hf'').hom.app V)).hom.left ≫
      ((relocalizeBaseChangeNatIso B h ε₁ ε₂ hfg hf hg).hom.app
        ((smallBaseChange B W hW f' hf').obj V)).hom.left ≫
      ((smallBaseChange B S hS g hg).map
        ((relocalizeBaseChangeNatIso B h ε₂ ε₃ hfg' hf' hg').hom.app V)).hom.left ≫
      ((smallBaseChangeChartCompIso B S hS g g' hg hg' hg'').inv.app
        ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor.obj V)).hom.left ≫
      hg''.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor.obj V).1.hom =
    ((relocalizeBaseChangeNatIso B h ε₁ ε₃ hfg'' hf'' hg'').hom.app V).hom.left ≫
      hg''.snd ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor.obj V).1.hom
  rw [e₁, e₅]
  refine Eq.trans (congrArg (fun k => _ ≫ _ ≫ k) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _)))) ?_
  refine Eq.trans (congrArg (fun k => _ ≫ k) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) e₃))) ?_
  refine Eq.trans (congrArg (fun k => _ ≫ _ ≫ k) e₄) ?_
  refine Eq.trans ?_ (congrArg (fun k => (Over.map h).map k) e₆)
  rw [Functor.map_comp]
  exact congrArg (fun k => ((smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor.map
    ((smallBaseChangeChartCompIso B W hW f f' hf hf' hf'').hom.app V)).hom.left ≫ k)
    ((Over.map h).map_comp _ _).symm

/-- **The base-change direct images commute with the change of base compatibly with
composition**: `AlgebraicGeometry.Space.smallerBaseChartPushforwardIso` is coherent with the
contractions `AlgebraicGeometry.Space.smallBaseChangeChartPushforwardCompIso`. -/
theorem smallerBaseChartPushforwardIso_isCompSquareCoherent :
    IsCompSquareCoherent (smallBaseChangeChartPushforwardCompIso B S hS g g' hg hg' hg'')
      (smallBaseChangeChartPushforwardCompIso B W hW f f' hf hf' hf'')
      (smallerBaseChartPushforwardIso B h ε₂ ε₃ hfg' hf' hg')
      (smallerBaseChartPushforwardIso B h ε₁ ε₂ hfg hf hg)
      (smallerBaseChartPushforwardIso B h ε₁ ε₃ hfg'' hf'' hg'') := by
  apply isCompSquareCoherent_pushforward (s := smallBaseChange B S hS g hg)
    (s' := smallBaseChange B S hS g' hg') (s'' := smallBaseChange B S hS (g ≫ g') hg'')
    (t := smallBaseChange B W hW f hf) (t' := smallBaseChange B W hW f' hf')
    (t'' := smallBaseChange B W hW (f ≫ f') hf'')
    (E₁ := (smallerBaseSmallEtaleEquivalenceOfIso B h ε₁).functor)
    (E₂ := (smallerBaseSmallEtaleEquivalenceOfIso B h ε₂).functor)
    (E₃ := (smallerBaseSmallEtaleEquivalenceOfIso B h ε₃).functor)
    (φs := smallBaseChangeSharp B S hS g hg) (φs' := smallBaseChangeSharp B S hS g' hg')
    (φs'' := smallBaseChangeSharp B S hS (g ≫ g') hg'')
    (φt := smallBaseChangeSharp B W hW f hf) (φt' := smallBaseChangeSharp B W hW f' hf')
    (φt'' := smallBaseChangeSharp B W hW (f ≫ f') hf'') (ψ₁ := 𝟙 _) (ψ₂ := 𝟙 _) (ψ₃ := 𝟙 _)
    (smallBaseChangeChartCompIso B S hS g g' hg hg' hg'')
    (smallBaseChangeChartCompIso B W hW f f' hf hf' hf'')
    (relocalizeBaseChangeNatIso B h ε₁ ε₂ hfg hf hg)
    (relocalizeBaseChangeNatIso B h ε₂ ε₃ hfg' hf' hg')
    (relocalizeBaseChangeNatIso B h ε₁ ε₃ hfg'' hf'' hg'')
  exact relocalizeBaseChangeNatIso_comp B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg''

/-- **The direct images of modules commute with the change of base compatibly with
composition**, read through the composition isomorphisms
`AlgebraicGeometry.Space.pushforwardModulesCompAt` of direct images on both sides. -/
theorem smallerBasePushforwardIso_isCompSquareCoherent :
    IsCompSquareCoherent (pushforwardModulesCompAt B S hS g g')
      (pushforwardModulesCompAt B W hW f f')
      (smallerBasePushforwardIso B h ε₂ ε₃ hfg' hf' hg')
      (smallerBasePushforwardIso B h ε₁ ε₂ hfg hf hg)
      (smallerBasePushforwardIso B h ε₁ ε₃ hfg'' hf'' hg'') := by
  apply isCompSquareCoherent_transport
    (e := smallBaseChangeChartPushforwardCompIso B S hS g g' hg hg' hg'')
    (e' := smallBaseChangeChartPushforwardCompIso B W hW f f' hf hf' hf'')
    (θg := pushforwardModulesIsoModulePushforward B S hS g' ≪≫
      modulePushforwardChartIso B S hS g' hg')
    (θg' := pushforwardModulesIsoModulePushforward B S hS g ≪≫
      modulePushforwardChartIso B S hS g hg)
    (θgg := pushforwardModulesIsoModulePushforward B S hS (g ≫ g') ≪≫
      modulePushforwardChartIso B S hS (g ≫ g') hg'')
    (θf := pushforwardModulesIsoModulePushforward B W hW f' ≪≫
      modulePushforwardChartIso B W hW f' hf')
    (θf' := pushforwardModulesIsoModulePushforward B W hW f ≪≫
      modulePushforwardChartIso B W hW f hf)
    (θff := pushforwardModulesIsoModulePushforward B W hW (f ≫ f') ≪≫
      modulePushforwardChartIso B W hW (f ≫ f') hf'')
  · exact pushforwardModulesCompAt_trans_chartIso B g g' hg hg' hg''
  · exact pushforwardModulesCompAt_trans_chartIso B f f' hf hf' hf''
  · exact smallerBaseChartPushforwardIso_isCompSquareCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg'
      hfg'' hf'' hg''

/-- **The degreewise comparisons are compatible with Stacks 03D6, on modules**: the module-level
coherence `AlgebraicGeometry.Space.SmallerBasePullbackIsoCoherent`. -/
theorem smallerBasePullbackIsoCoherent :
    SmallerBasePullbackIsoCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg'' := by
  apply isCompSquareCoherent_of_mates
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS g'))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B S hS (g ≫ g')))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B W hW f))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B W hW f'))
    (RingedToposHom.pullbackAdjPushforwardModules (smallEtaleRingedToposHom B W hW (f ≫ f')))
    _ _ (pushforwardModulesCompAt B S hS g g') (pushforwardModulesCompAt B W hW f f')
    (conjugateEquiv_pullbackModulesCompTransport_inv B g g')
    (conjugateEquiv_pullbackModulesCompTransport_inv B f f')
    (smallerBasePushforwardIso B h ε₁ ε₂ hfg hf hg)
    (smallerBasePushforwardIso B h ε₂ ε₃ hfg' hf' hg')
    (smallerBasePushforwardIso B h ε₁ ε₃ hfg'' hf'' hg'')
  · rfl
  · rfl
  · rfl
  · exact smallerBasePushforwardIso_isCompSquareCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg'
      hfg'' hf'' hg''

section DerivedComp

open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

attribute [local instance] HasDerivedCategory.standard

include hfg hf hg hfg' hf' hg' hfg'' hf'' hg'' in
/-- **The derived comparison is compatible with Stacks 0D6D, in the ringed-topos spelling**:
`AlgebraicGeometry.Space.smallerBaseToposDerivedPullbackIso_comp_of_isCoherent` with its
hypothesis discharged by `AlgebraicGeometry.Space.smallerBasePullbackIsoCoherent`. -/
theorem smallerBaseToposDerivedPullbackIso_comp
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y₃))) :
    (smallerBaseToposModulesEquivalence B h ε₁).functor.mapDerivedCategory.map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g g').hom.app K) ≫
      (smallerBaseToposDerivedPullbackIso B h ε₁ ε₃ hfg'' hf'' hg'').hom.app K =
    (smallerBaseToposDerivedPullbackIso B h ε₁ ε₂ hfg hf hg).hom.app
        ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
      (smallEtaleDerivedModulePullback B W hW f).map
        ((smallerBaseToposDerivedPullbackIso B h ε₂ ε₃ hfg' hf' hg').hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompIso B W hW f f').hom.app
        ((smallerBaseToposModulesEquivalence B h ε₃).functor.mapDerivedCategory.obj K) :=
  smallerBaseToposDerivedPullbackIso_comp_of_isCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg'
    hfg'' hf'' hg''
    (smallerBaseHomotopyPullbackIsoCoherent_of B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg''
      (smallerBasePullbackIsoCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg'')) K

include hfg hf hg hfg' hf' hg' hfg'' hf'' hg'' in
/-- **The derived comparison of Stacks 04SG is compatible with Stacks 0D6D**: for composable
representable `f, f'` over `W` and `g, g'` over `S` matched by `Λ_h Zᵢ ≅ Yᵢ`, the comparison
`AlgebraicGeometry.Space.smallerBaseDerivedPullbackIso` of the composite is the composite of the
comparisons, read through the composition isomorphisms
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCompIso` on both sides. -/
theorem smallerBaseDerivedPullbackIso_comp
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y₃))) :
    (smallerBaseDerivedEquivalence B h ε₁).functor.map
        ((smallEtaleDerivedModulePullbackCompIso B S hS g g').hom.app K) ≫
      (smallerBaseDerivedPullbackIso B h ε₁ ε₃ hfg'' hf'' hg'').hom.app K =
    (smallerBaseDerivedPullbackIso B h ε₁ ε₂ hfg hf hg).hom.app
        ((smallEtaleDerivedModulePullback B S hS g').obj K) ≫
      (smallEtaleDerivedModulePullback B W hW f).map
        ((smallerBaseDerivedPullbackIso B h ε₂ ε₃ hfg' hf' hg').hom.app K) ≫
      (smallEtaleDerivedModulePullbackCompIso B W hW f f').hom.app
        ((smallerBaseDerivedEquivalence B h ε₃).functor.obj K) :=
  smallerBaseDerivedPullbackIso_comp_of_isCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg'
    hfg'' hf'' hg''
    (smallerBasePullbackIsoCoherent B h ε₁ ε₂ ε₃ hfg hf hg hfg' hf' hg' hfg'' hf'' hg'') K

end DerivedComp

end ChartsComp

end AlgebraicGeometry.Space

end
