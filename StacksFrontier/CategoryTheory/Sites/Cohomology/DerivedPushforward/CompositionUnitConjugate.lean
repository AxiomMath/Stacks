module

public import StacksFrontier.CategoryTheory.Adjunction.CounitMatesComposition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackModulesIsoDerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfToposHomUnconditional

/-!
# The units of derived direct images along a composite, and the conjugate composition map

Let `f : X ⟶ Y`, `g : Y ⟶ Z` and `χ : X ⟶ Z` be morphisms of ringed topoi, with `χ` 2-isomorphic
to `g ∘ f`: an isomorphism `τ : (g ∘ f)_* ≅ χ_*` of direct images of modules, and the induced
isomorphism `σ : (g ∘ f)^* ≅ χ^*` of pullbacks. The derived pullbacks compose by
`Lg^* ⋙ Lf^* ≅ L(g ∘ f)^* ≅ Lχ^*` (Stacks 0D6D, then the action of `σ`), and the conjugate of
the inverse of this isomorphism under the derived adjunctions (Stacks 07A6) is a map
`c : Rf_* ⋙ Rg_* ⟶ Rχ_*`. The units `f_* ⟶ Rf_*`, `g_* ⟶ Rg_*` and `χ_* ⟶ Rχ_*` are
compatible with `c` and with the composition isomorphism `f_* ⋙ g_* ≅ (g ∘ f)_* ≅ χ_*` of direct
images.

## Main results

* `Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_conjugateEquiv_of_adjunctions`:
  the abstract statement, for the conjugate map of a composition isomorphism of left adjoints
  that is a composite of two isomorphisms each induced by an underived one.
* `Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.compUnit_comp_conjugateEquiv_app`:
  the statement for morphisms of ringed topoi.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0FPI](https://stacks.math.columbia.edu/tag/0FPI)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.DerivedPushforwardComposition

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {KX : Type u₁} [Category.{v₁} KX] {KY : Type u₂} [Category.{v₂} KY]
  {KZ : Type u₃} [Category.{v₃} KZ] {DX : Type u₄} [Category.{v₄} DX]
  {DY : Type u₅} [Category.{v₅} DY] {DZ : Type u₆} [Category.{v₆} DZ]
  {QX : KX ⥤ DX} {QY : KY ⥤ DY} {QZ : KZ ⥤ DZ}
  {pf : KX ⥤ KY} {pg : KY ⥤ KZ} {pgf : KX ⥤ KZ}
  {ppf : KY ⥤ KX} {ppg : KZ ⥤ KY} {ppgf ppgf' : KZ ⥤ KX}
  {Rf : DX ⥤ DY} {Rg : DY ⥤ DZ} {Rgf : DX ⥤ DZ}
  {Lf : DY ⥤ DX} {Lg : DZ ⥤ DY} {Lgf Lgf' : DZ ⥤ DX}
  (af : ppf ⊣ pf) (ag : ppg ⊣ pg) (agf : ppgf ⊣ pgf)
  (Af : Lf ⊣ Rf) (Ag : Lg ⊣ Rg) (Agf : Lgf ⊣ Rgf)
  {ηf : pf ⋙ QY ⟶ QX ⋙ Rf} {ηg : pg ⋙ QZ ⟶ QY ⋙ Rg} {ηgf : pgf ⋙ QZ ⟶ QX ⋙ Rgf}
  {εf : QY ⋙ Lf ⟶ ppf ⋙ QX} {εg : QZ ⋙ Lg ⟶ ppg ⋙ QY} {εgf : QZ ⋙ Lgf ⟶ ppgf ⋙ QX}
  {εgf' : QZ ⋙ Lgf' ⟶ ppgf' ⋙ QX}
  (c : pf ⋙ pg ≅ pgf) (d₁ : ppg ⋙ ppf ≅ ppgf') (d₂ : ppgf' ≅ ppgf)
  (Dpb₁ : Lg ⋙ Lf ≅ Lgf') (Dpb₂ : Lgf' ≅ Lgf)

/-- **The composite unit followed by the conjugate composition map is the unit.** In the setting
of `Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_compIso_of_adjunctions`, with
the composition isomorphism of the left adjoints given as a composite `Dpb₁ ≪≫ Dpb₂`, each factor
induced by an underived isomorphism through the comparisons (`hDpb₁`, `hDpb₂`): the composite unit
followed by the map `Rf ⋙ Rg ⟶ Rgf` conjugate to the inverse of `Dpb₁ ≪≫ Dpb₂` is the unit
`ηgf`. -/
theorem compUnit_comp_conjugateEquiv_of_adjunctions
    (hf : ∀ K : KX, Lf.map (ηf.app K) ≫ Af.counit.app (QX.obj K) =
      εf.app (pf.obj K) ≫ QX.map (af.counit.app K))
    (hg : ∀ M : KY, Lg.map (ηg.app M) ≫ Ag.counit.app (QY.obj M) =
      εg.app (pg.obj M) ≫ QY.map (ag.counit.app M))
    (hgf : ∀ K : KX, Lgf.map (ηgf.app K) ≫ Agf.counit.app (QX.obj K) =
      εgf.app (pgf.obj K) ≫ QX.map (agf.counit.app K))
    (hDpb₁ : ∀ W : KZ, Dpb₁.hom.app (QZ.obj W) ≫ εgf'.app W =
      Lf.map (εg.app W) ≫ εf.app (ppg.obj W) ≫ QX.map (d₁.hom.app W))
    (hDpb₂ : ∀ W : KZ, Dpb₂.hom.app (QZ.obj W) ≫ εgf.app W =
      εgf'.app W ≫ QX.map (d₂.hom.app W))
    (hdeg : ∀ K : KX, ppf.map (ppg.map (c.inv.app K) ≫ ag.counit.app (pf.obj K)) ≫
      af.counit.app K = (d₁ ≪≫ d₂).hom.app (pgf.obj K) ≫ agf.counit.app K)
    (K : KX) :
    (QZ.map (c.inv.app K) ≫ ηg.app (pf.obj K) ≫ Rg.map (ηf.app K)) ≫
        (conjugateEquiv (Ag.comp Af) Agf (Dpb₁ ≪≫ Dpb₂).inv).app (QX.obj K) = ηgf.app K := by
  have hconj : ∀ {M : DZ} {N : DX} (f : M ⟶ (Rf ⋙ Rg).obj N),
      (Agf.homEquiv _ _).symm (f ≫ (conjugateEquiv (Ag.comp Af) Agf (Dpb₁ ≪≫ Dpb₂).inv).app N) =
        (Dpb₁ ≪≫ Dpb₂).inv.app M ≫ ((Ag.comp Af).homEquiv _ _).symm f := by
    intro M N f
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      conjugateEquiv_counit, ← Category.assoc, NatTrans.naturality, Category.assoc]
  refine compUnit_comp_compIso_of_adjunctions af ag agf Af Ag Agf c (d₁ ≪≫ d₂) (Dpb₁ ≪≫ Dpb₂)
    (conjugateIsoEquiv Agf (Ag.comp Af) (Dpb₁ ≪≫ Dpb₂)).symm hf hg hgf (fun W => ?_)
    (fun M N φ => ?_) hdeg K
  · simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, hDpb₂, reassoc_of% (hDpb₁ W),
      Functor.map_comp]
  · have h := hconj (((Ag.comp Af).homEquiv _ _) ((Dpb₁ ≪≫ Dpb₂).hom.app M ≫ φ))
    rwa [Equiv.symm_apply_apply, Iso.inv_hom_id_app_assoc, Equiv.symm_apply_eq,
      Adjunction.comp_homEquiv, Equiv.trans_apply] at h

end Stacks.Cohomology.DerivedPushforwardComposition

namespace Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom

open AlgebraicGeometry AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

universe v u w v' u' w' v'' u'' w''

attribute [local instance] HasDerivedCategory.standard hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Z.J AddCommGrpCat.{w''}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w''}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] [HasSheafify Z.J (Type w'')]
  [IsGrothendieckAbelian.{w} X.Modules] [IsGrothendieckAbelian.{w'} Y.Modules]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

/-- **The units of derived direct images along a composite are compatible with the conjugate
composition map.** Let `χ : X ⟶ Z` be a morphism of ringed topoi with an isomorphism
`τ : (g ∘ f)_* ≅ χ_*` of direct images of modules, and let `σ : (g ∘ f)^* ≅ χ^*` be the induced
isomorphism of pullbacks (`hσ`). Then the composition isomorphism `f_* ⋙ g_* ≅ χ_*` of direct
images on homotopy categories, followed by the unit of `Rg_*` at `f_*K` and by `Rg_*` of the unit
of `Rf_*` at `K`, and then by the map `Rf_* ⋙ Rg_* ⟶ Rχ_*` conjugate to the inverse of
`Lg^* ⋙ Lf^* ≅ L(g ∘ f)^* ≅ Lχ^*`, is the unit of `Rχ_*` at `K`. -/
theorem compUnit_comp_conjugateEquiv_app (χ : RingedToposHom X Z)
    (τ : (g.comp f).pushforwardModules ≅ χ.pushforwardModules)
    (σ : (g.comp f).toModulesHom.pullbackModules ≅ χ.toModulesHom.pullbackModules)
    (hσ : σ = (pullbackAdjPushforwardModules (g.comp f)).leftAdjointUniq
      ((pullbackAdjPushforwardModules χ).ofNatIsoRight τ.symm))
    (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
        ((pushforwardModulesCompIso f g).symm ≪≫ τ) (ComplexShape.up ℤ)).inv.app K) ≫
      (derivedPushforwardUnit g).app ((pushforwardMapHomotopy f).obj K) ≫
        (derivedPushforward g).map ((derivedPushforwardUnit f).app K)) ≫
      (conjugateEquiv ((derivedAdjunction g).comp (derivedAdjunction f)) (derivedAdjunction χ)
        (derivedPullbackCompIso f g ≪≫ derivedPullbackIsoOfPullbackModulesIso σ).inv).app
        (DerivedCategory.Qh.obj K) =
      (derivedPushforwardUnit χ).app K := by
  have k := CategoryTheory.Adjunction.counit_comp_of_eq_leftAdjointUniq
    (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules g)
    (pullbackAdjPushforwardModules (g.comp f)) (pullbackModulesCompIso f g)
    (pushforwardModulesCompIso f g) rfl
  have ht := CategoryTheory.Adjunction.counit_comp_of_eq_leftAdjointUniq_ofNatIsoRight
    (pullbackAdjPushforwardModules (g.comp f)) (pullbackAdjPushforwardModules χ) τ σ hσ
  have hdeg := CategoryTheory.Adjunction.mapHomotopyCategory_counit_mates_of_eq
    (c := (pushforwardModulesCompIso f g).symm ≪≫ τ)
    (AF := pullbackAdjPushforwardMapHomotopy f) (AG := pullbackAdjPushforwardMapHomotopy g)
    (AH := pullbackAdjPushforwardMapHomotopy χ)
    (e' := pullbackMapHomotopyCompIso f g ≪≫
      Stacks.Homology.mapHomotopyCategoryIso σ (ComplexShape.up ℤ))
    rfl k ht rfl rfl rfl rfl
  exact Stacks.Cohomology.DerivedPushforwardComposition.compUnit_comp_conjugateEquiv_of_adjunctions
    (pullbackAdjPushforwardMapHomotopy f) (pullbackAdjPushforwardMapHomotopy g)
    (pullbackAdjPushforwardMapHomotopy χ) (derivedAdjunction f) (derivedAdjunction g)
    (derivedAdjunction χ)
    (Functor.mapHomotopyCategoryCompIso ((pushforwardModulesCompIso f g).symm ≪≫ τ)
      (ComplexShape.up ℤ))
    (pullbackMapHomotopyCompIso f g) (Stacks.Homology.mapHomotopyCategoryIso σ (ComplexShape.up ℤ))
    (derivedPullbackCompIso f g) (derivedPullbackIsoOfPullbackModulesIso σ)
    (derivedAdjunction_counit_fac f) (derivedAdjunction_counit_fac g)
    (derivedAdjunction_counit_fac χ)
    (derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app f g)
    (derivedPullbackIsoOfPullbackModulesIso_hom_app σ) hdeg K

end Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom
