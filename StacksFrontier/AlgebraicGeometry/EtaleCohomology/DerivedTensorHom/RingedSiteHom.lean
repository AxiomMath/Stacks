module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ConstantRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites

/-!
# The morphism of constant ringed sites induced by a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes and `Λ` a commutative ring. Base change along `f` is a
morphism of small étale sites `X_étale ⟶ Y_étale`; together with the canonical map
`Λ̲ ⟶ f_*Λ̲` of constant sheaves of rings it is a morphism of ringed sites
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)`, here between the small models
`Stacks.EtaleCohomology.etaleRingedSite`.

## Main definitions

* `Stacks.EtaleCohomology.etaleSmallModelBaseChange`: base change on the small models.
* `Stacks.EtaleCohomology.etaleRingedSiteFSharp`: the structure map `Λ̲ ⟶ f_*Λ̲`.
* `Stacks.EtaleCohomology.etaleRingedSiteHom`: the morphism of ringed sites.

## Main results

* `Stacks.EtaleCohomology.etaleSmallModelBaseChange_isMorphismOfSites`: base change is a
  morphism of sites.
* `Stacks.EtaleCohomology.etaleRingedSiteFSharp_toSheafify`: the structure map sends the image of
  a constant to the image of the same constant.
* `Stacks.EtaleCohomology.constantRingedSiteRingMap_app_apply`: the map out of the constant
  presheaf of rings used to read sheaves of modules over `Λ̲` as sheaves of `Λ`-modules is, on
  sections, the sheafification map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u r

namespace Stacks.EtaleCohomology

section ConstantRingMap

variable {C : Type w} [SmallCategory C] (J : GrothendieckTopology C) (Λ : Type w) [CommRing Λ]
  [HasWeakSheafify J CommRingCat.{w}] [HasWeakSheafify J RingCat.{w}]
  [J.PreservesSheafification (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- **The map out of the constant presheaf of rings of the constant ringed site is, on sections,
the sheafification map of commutative rings.** -/
theorem constantRingedSiteRingMap_app_apply (U : Cᵒᵖ) (a : Λ) :
    ((Stacks.ConstantRingModules.constantRingedSiteRingMap J Λ).app U).hom a =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))).app U).hom a := by
  have h₁ := sheafComposeIso_inv_fac J (forget₂ CommRingCat.{w} RingCat.{w})
    ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))
  have h₂ := toSheafify_naturality J
    (Functor.constComp Cᵒᵖ (CommRingCat.of Λ) (forget₂ CommRingCat.{w} RingCat.{w})).hom
  have h₃ : (Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ)))
      (forget₂ CommRingCat.{w} RingCat.{w})) ≫
        ((RingedSite.constantRingSheafIso_general J Λ).hom).hom =
      (Functor.constComp Cᵒᵖ (CommRingCat.of Λ) (forget₂ CommRingCat.{w} RingCat.{w})).hom ≫
        Stacks.ConstantRingModules.constantRingMap Λ J := by
    show _ ≫ ((sheafifyComposeIso J (forget₂ CommRingCat.{w} RingCat.{w})
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))).inv ≫ sheafifyMap J
        (Functor.constComp Cᵒᵖ (CommRingCat.of Λ) (forget₂ CommRingCat.{w} RingCat.{w})).hom) = _
    rw [reassoc_of% h₁, ← h₂]
    rfl
  have he : ((RingedSite.constantRingSheafIso_general J Λ).hom).hom ≫
      ((RingedSite.constantRingSheafIso_general J Λ).inv).hom = 𝟙 _ :=
    congrArg (fun φ => φ.hom) (RingedSite.constantRingSheafIso_general J Λ).hom_inv_id
  have h₅ := congrArg (fun φ => (φ.app U).hom a) h₃
  have h₆ := congrArg (fun φ => (φ.app U).hom
    (((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))).app U).hom a)) he
  refine Eq.trans ?_ h₆
  exact (congrArg (fun x => (((RingedSite.constantRingSheafIso_general J Λ).inv.hom).app U).hom x)
    h₅).symm

end ConstantRingMap

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Base change along `f`, on the small models of the small étale sites.** -/
abbrev etaleSmallModelBaseChange :
    AsSmall.{max (u + 1) r} Y.Etale ⥤ AsSmall.{max (u + 1) r} X.Etale :=
  AsSmall.down ⋙ smallEtaleBaseChange f ⋙ AsSmall.up

/-- Base change on the small models is representably flat. -/
instance etaleSmallModelBaseChange_representablyFlat :
    RepresentablyFlat (etaleSmallModelBaseChange.{u, r} f) := by
  have : (AsSmall.down : AsSmall.{max (u + 1) r} Y.Etale ⥤ Y.Etale).IsRightAdjoint :=
    (AsSmall.equiv : Y.Etale ≌ AsSmall.{max (u + 1) r} Y.Etale).toAdjunction.isRightAdjoint
  have : (AsSmall.up : X.Etale ⥤ AsSmall.{max (u + 1) r} X.Etale).IsRightAdjoint :=
    (AsSmall.equiv : X.Etale ≌ AsSmall.{max (u + 1) r} X.Etale).symm.toAdjunction.isRightAdjoint
  exact RepresentablyFlat.comp _ _

/-- Base change on the small models is continuous. -/
instance etaleSmallModelBaseChange_isContinuous :
    (etaleSmallModelBaseChange.{u, r} f).IsContinuous (etaleSmallModelTopology.{u, r} Y)
      (etaleSmallModelTopology.{u, r} X) := by
  have := Functor.isContinuous_comp (smallEtaleBaseChange f)
    (AsSmall.up : X.Etale ⥤ AsSmall.{max (u + 1) r} X.Etale) Y.smallEtaleTopology
    X.smallEtaleTopology (etaleSmallModelTopology.{u, r} X)
  exact Functor.isContinuous_comp (AsSmall.down : AsSmall.{max (u + 1) r} Y.Etale ⥤ Y.Etale) _
    (etaleSmallModelTopology.{u, r} Y) Y.smallEtaleTopology (etaleSmallModelTopology.{u, r} X)

/-- **Base change is a morphism of small étale sites** (on the small models). -/
theorem etaleSmallModelBaseChange_isMorphismOfSites :
    (etaleSmallModelBaseChange.{u, r} f).IsMorphismOfSites (etaleSmallModelTopology.{u, r} Y)
      (etaleSmallModelTopology.{u, r} X) := by
  rw [Functor.isMorphismOfSites_iff_preservesFiniteLimits]
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    _ _ _ _

/-- The presheaf map `Λ ⟶ Γ(u V, Λ̲)` of which the structure map of the morphism of constant
ringed sites is the sheafification. -/
abbrev etaleRingedSitePresheafFSharp :
    (Functor.const (AsSmall.{max (u + 1) r} Y.Etale)ᵒᵖ).obj
        (CommRingCat.of (ULift.{max (u + 1) r} Λ)) ⟶
      (etaleSmallModelBaseChange.{u, r} f).op ⋙ (etaleRingedSite.{u, r} Λ X).O.obj :=
  Functor.whiskerLeft (etaleSmallModelBaseChange.{u, r} f).op
    (toSheafify (etaleSmallModelTopology.{u, r} X)
      ((Functor.const (AsSmall.{max (u + 1) r} X.Etale)ᵒᵖ).obj
        (CommRingCat.of (ULift.{max (u + 1) r} Λ))))

/-- **The structure map `Λ̲ ⟶ f_*Λ̲`** of constant sheaves of rings: the sheafification of the
map sending a constant to the same constant. -/
def etaleRingedSiteFSharp :
    (etaleRingedSite.{u, r} Λ Y).O ⟶
      ((etaleSmallModelBaseChange.{u, r} f).sheafPushforwardContinuous CommRingCat.{max (u + 1) r}
        (etaleSmallModelTopology.{u, r} Y) (etaleSmallModelTopology.{u, r} X)).obj
        (etaleRingedSite.{u, r} Λ X).O :=
  ObjectProperty.homMk (sheafifyLift (etaleSmallModelTopology.{u, r} Y)
    (etaleRingedSitePresheafFSharp.{u, r} Λ f)
    (((etaleSmallModelBaseChange.{u, r} f).sheafPushforwardContinuous CommRingCat.{max (u + 1) r}
        (etaleSmallModelTopology.{u, r} Y) (etaleSmallModelTopology.{u, r} X)).obj
        (etaleRingedSite.{u, r} Λ X).O).property)

/-- **The structure map sends a constant to the same constant.** -/
theorem etaleRingedSiteFSharp_toSheafify :
    toSheafify (etaleSmallModelTopology.{u, r} Y)
        ((Functor.const (AsSmall.{max (u + 1) r} Y.Etale)ᵒᵖ).obj
          (CommRingCat.of (ULift.{max (u + 1) r} Λ))) ≫
      (etaleRingedSiteFSharp.{u, r} Λ f).hom = etaleRingedSitePresheafFSharp.{u, r} Λ f :=
  toSheafify_sheafifyLift _ _ _

/-- **The morphism of ringed sites `(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` induced by `f : X ⟶ Y`.** -/
def etaleRingedSiteHom : RingedSite.Hom (etaleRingedSite.{u, r} Λ X) (etaleRingedSite.{u, r} Λ Y)
    where
  u := etaleSmallModelBaseChange.{u, r} f
  isMorphismOfSites := etaleSmallModelBaseChange_isMorphismOfSites.{u, r} f
  fsharp := etaleRingedSiteFSharp.{u, r} Λ f

end Stacks.EtaleCohomology

end
