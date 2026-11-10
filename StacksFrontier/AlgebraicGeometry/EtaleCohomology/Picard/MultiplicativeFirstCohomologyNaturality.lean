module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.EtaleGeneratorTorsor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.MultiplicativeFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.InverseImage
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Picard.RootsOfUnityFirstCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.RootsOfUnityPullbackDegree

/-!
# Naturality of the étale identification `H¹(X_étale, 𝐆_m) = Pic(X)`

The identification `H¹(X_étale, 𝐆_m) = Pic(X)` of Stacks 03P8 sends the class of the torsor of
local generators of an invertible module `L` to the class of `L`. It is natural in `X`: for a
morphism of schemes `π : X ⟶ Y`, pulling a class of `H¹(Y_étale, 𝐆_m)` back to `X` corresponds to
pulling back invertible modules. The same holds for the maps `H¹(X_étale, μ_n) → Pic(X)` and
`H¹(X_étale, μ_n) ≅ Pic(X)[n]`.

## Main results

* `Stacks.EtaleGenerators.etaleH1MultiplicativeAddEquivPicard_generatorTorsorOn`: the class of the
  torsor of local generators of `L` is sent to the class of `L`.
* `Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard_naturality`: naturality of
  `H¹(X_étale, 𝐆_m) = Pic(X)` under pullback.
* `Stacks.Kummer.h1RootsOfUnityToPicard_naturality`: naturality of `H¹(X_étale, μ_n) → Pic(X)`.
* `Stacks.Kummer.h1RootsOfUnityAddEquivPicardTorsion_naturality`: naturality of
  `H¹(X_étale, μ_n) ≅ Pic(X)[n]`.

## References

* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Cohomology.Torsors

universe w v u

namespace Stacks.EtaleGenerators

variable (S : Scheme.{u})

/-- The sections of `𝐆_m` are the invertible global functions. -/
def multiplicativeUnitsEquiv :
    GlobalUnitsEquiv S.smallEtaleTopology (𝟭 S.Etale)
      (Stacks.Kummer.multiplicativeSheaf.{u, v} S) where
  equiv _ := AddEquiv.ulift
  naturality _ _ := rfl

/-- The sections of the universe lift of `𝐆_m` are the invertible global functions. -/
def uliftMultiplicativeUnitsEquiv :
    GlobalUnitsEquiv S.smallEtaleTopology (𝟭 S.Etale)
      ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{max (u + 1) v, u + 1}
        S.smallEtaleTopology).obj (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} S)) where
  equiv _ := AddEquiv.ulift.trans AddEquiv.ulift
  naturality _ _ := rfl

variable (B : BigEtaleSite.{u}) (hS : B.Contains S)

/-- The sections of the restriction of `𝐆_m` to a size-bounded small étale site. -/
def restrictedMultiplicativeUnitsEquiv :
    GlobalUnitsEquiv (SmallEtale.topology B S hS) (SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale)
      (((SmallEtale.toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallEtale.topology B S hS) S.smallEtaleTopology).obj
          (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} S)) where
  equiv _ := AddEquiv.ulift
  naturality _ _ := rfl

/-- The sections of the units of the small étale ringed site are the invertible global
functions. -/
def smallEtaleUnitsEquiv :
    GlobalUnitsEquiv (SmallEtale.topology B S hS) (SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale)
      (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS)) where
  equiv _ := AddEquiv.refl _
  naturality _ _ := rfl

/-- The sections of the universe lift of the units of the small étale ringed site are the
invertible global functions. -/
def uliftSmallEtaleUnitsEquiv :
    GlobalUnitsEquiv (SmallEtale.topology B S hS) (SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale)
      ((Stacks.Sheaves.UniverseLift.uliftSheafFunctor.{u + 1, u} (SmallEtale.topology B S hS)).obj
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS))) where
  equiv _ := AddEquiv.ulift
  naturality _ _ := rfl

variable {S} (L : S.Modules)
  (hL : Stacks.SheafOfModules.IsInvertible S.presheaf
    (Stacks.RingedSpace.structureRingSheaf S.toRingedSpace).property L)

/-- The first two identifications of Tag 03P8 on Mathlib's small étale site — the coefficient
isomorphism `𝐆_m ≅ ULift 𝐆_m` and the universe lift of `H¹` — carry the class of the torsor of
generators of `L` with coefficients in any universe to its class with coefficients at `u + 1`. -/
theorem sheafHOneAddEquiv_symm_extPostcomp_generatorTorsorOn
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    letI := Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology S
    (Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv.{u + 1, w, max (u + 1) v, u + 1, u, u + 1}
        S.smallEtaleTopology (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} S)).symm
      ((SmallEtale.extPostcompIsoAddEquiv.{w}
          (Stacks.Kummer.multiplicativeSheafUliftIso.{v, u} S) 1)
        (torsorIsoClassesEquivH1 _ (Quotient.mk _
          (generatorTorsorOn.{max (u + 1) v} L hL (multiplicativeUnitsEquiv.{v} S))))) =
      torsorIsoClassesEquivH1 _ (Quotient.mk _
        (generatorTorsorOn.{u + 1} L hL (multiplicativeUnitsEquiv.{u + 1} S))) := by
  let := Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology S
  rw [AddEquiv.symm_apply_eq]
  refine (sheafHMap_generatorTorsorOn.{w, max (u + 1) v, u, u + 1, u} L hL
    (Stacks.Kummer.multiplicativeSheafUliftIso.{v, u} S).hom
    (multiplicativeUnitsEquiv.{v} S) (uliftMultiplicativeUnitsEquiv.{v} S)
    (fun _ _ => rfl)).trans ?_
  exact (sheafHOneAddEquiv_generatorTorsorOn.{u + 1, w, max (u + 1) v, u + 1, u, u + 1, u} L hL _
    (multiplicativeUnitsEquiv.{u + 1} S) (uliftMultiplicativeUnitsEquiv.{v} S)
    (fun _ _ => rfl)).symm

/-- The inclusion of the size-bounded small étale site is continuous. -/
theorem isContinuous_toEtaleSite_comp_id :
    (SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale).IsContinuous (SmallEtale.topology B S hS)
      S.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ S.smallEtaleTopology _

/-- The inclusion of the size-bounded small étale site is cocontinuous. -/
theorem isCocontinuous_toEtaleSite_comp_id :
    (SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale).IsCocontinuous (SmallEtale.topology B S hS)
      S.smallEtaleTopology :=
  isCocontinuous_comp _ _ _ S.smallEtaleTopology

attribute [local instance] isContinuous_toEtaleSite_comp_id isCocontinuous_toEtaleSite_comp_id

/-- The size-bounded part of Tag 03P8 carries the class of the torsor of generators of `L` on
Mathlib's small étale site to the class, on the size-bounded small étale ringed site, of the
torsor of generators under its units. -/
theorem h1MultiplicativeAddEquivOfContains_generatorTorsorOn :
    letI := Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology S
    SmallEtale.h1MultiplicativeAddEquivOfContains B S hS
        (torsorIsoClassesEquivH1 _ (Quotient.mk _
          (generatorTorsorOn.{u + 1} L hL (multiplicativeUnitsEquiv.{u + 1} S)))) =
      SmallEtale.h1UnitsAddEquivOfScheme B S hS (torsorIsoClassesEquivH1 _ (Quotient.mk _
        (generatorTorsorOn.{0} L hL (smallEtaleUnitsEquiv S B hS)))) := by
  let := Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology S
  have : ∀ T : (S.Etale)ᵒᵖ, Limits.HasLimitsOfShape
      (StructuredArrow T (SmallEtale.toEtaleSite B S hS).op) AddCommGrpCat.{u + 1} :=
    fun _ => Limits.hasLimitsOfShape_of_essentiallySmall.{u} _ _
  have : HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  have : HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite.{u} _ _
  have : (SmallEtale.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have : IsGrothendieckAbelian.{u + 1} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
    smallEtaleSheaf_isGrothendieckAbelian B ⟨S, hS⟩
  have : HasExt.{u + 1} (Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasExt _
  refine congrArg (SmallEtale.h1UnitsAddEquivOfScheme B S hS)
    (?_ : (Stacks.Sheaves.UniverseLift.sheafHOneAddEquiv.{u + 1, u + 1, u + 1, u, u, u + 1}
      (SmallEtale.topology B S hS)
        (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS))).symm
      ((SmallEtale.extPostcompIsoAddEquiv (SmallEtale.multiplicativeSheafRestrictionIso B S hS) 1)
        (Stacks.Cohomology.DenseSubsite.hAddEquiv (SmallEtale.topology B S hS) S.smallEtaleTopology
          (SmallEtale.toEtaleSite B S hS) (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} S) 1
            (torsorIsoClassesEquivH1 _ (Quotient.mk _
              (generatorTorsorOn.{u + 1} L hL (multiplicativeUnitsEquiv.{u + 1} S)))))) = _)
  rw [AddEquiv.symm_apply_eq]
  have h1 := hAddEquiv_generatorTorsorOn.{u + 1, u + 1, u, u + 1, u, u + 1, u} L hL
    (SmallEtale.topology B S hS) (SmallEtale.toEtaleSite B S hS)
    (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} S) (multiplicativeUnitsEquiv.{u + 1} S)
    (restrictedMultiplicativeUnitsEquiv S B hS) (fun _ _ => rfl)
  have h2 := sheafHMap_generatorTorsorOn.{u + 1, u + 1, u, u + 1, u} L hL
    (SmallEtale.multiplicativeSheafRestrictionIso B S hS).hom
    (restrictedMultiplicativeUnitsEquiv S B hS) (uliftSmallEtaleUnitsEquiv S B hS)
    (fun _ _ => rfl)
  have h3 := sheafHOneAddEquiv_generatorTorsorOn.{u + 1, u + 1, u + 1, 0, u, u + 1, u} L hL
    (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS))
    (smallEtaleUnitsEquiv S B hS) (uliftSmallEtaleUnitsEquiv S B hS) (fun _ _ => rfl)
  exact ((congrArg _ h1).trans h2).trans h3.symm

/-! ### The small model of the size-bounded small étale ringed site -/

section SmallModel

open RingedSite

/-- The associated module `L^a` on the size-bounded small étale ringed site, restricted to a
small model. -/
abbrev smallModelModule :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
        (smallEtaleRingedSite B S hS)).O) :=
  (denseRestrictModules (smallTopology (smallEtaleRingedSite B S hS)) (smallEtaleRingedSite B S hS)
    (smallFunctor (smallEtaleRingedSite B S hS))).obj ((SmallEtale.associatedModule B S hS).obj L)

/-- The section of `L^a` attached to a section of the pullback of `L`. -/
def smallModelSection (U : SmallModel.{u} (smallEtaleRingedSite B S hS).C)
    (x : Γ((Scheme.Modules.pullback ((Scheme.Etale.forget S).obj
      ((smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale).obj
        U)).hom).obj L, ⊤)) :
    (smallModelModule B hS L).val.obj (op U) :=
  haveI : L.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible L hL
  (SmallEtale.associatedModuleIsoSectionsSheaf B S hS L).inv.val.app
    (op ((smallFunctor (smallEtaleRingedSite B S hS)).obj U)) x

/-- `smallModelSection` commutes with restriction along a morphism of the small model. -/
theorem smallModelSection_restrict {U V : SmallModel.{u} (smallEtaleRingedSite B S hS).C}
    (f : V ⟶ U) (x : Γ((Scheme.Modules.pullback ((Scheme.Etale.forget S).obj
      ((smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale).obj
        U)).hom).obj L, ⊤)) :
    (smallModelModule B hS L).val.map f.op (smallModelSection B hS L hL U x) =
      smallModelSection B hS L hL V (pullbackSectionsMap L ((Scheme.Etale.forget S).map
        ((smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙
          𝟭 S.Etale).map f)) x) := by
  have : L.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible L hL
  exact (PresheafOfModules.naturality_apply
    (SmallEtale.associatedModuleIsoSectionsSheaf B S hS L).inv.val
    ((smallFunctor (smallEtaleRingedSite B S hS)).map f).op x).symm

/-- `smallModelSection` commutes with multiplication by a function. -/
theorem smallModelSection_smul (U : SmallModel.{u} (smallEtaleRingedSite B S hS).C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
        (smallEtaleRingedSite B S hS)).O).obj.obj (op U))
    (x : Γ((Scheme.Modules.pullback ((Scheme.Etale.forget S).obj
      ((smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale).obj
        U)).hom).obj L, ⊤)) :
    r • smallModelSection B hS L hL U x =
      smallModelSection B hS L hL U ((show Γ(((Scheme.Etale.forget S).obj
        ((smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙
          𝟭 S.Etale).obj U)).left, ⊤) from r) • x) := by
  have : L.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible L hL
  exact ((((SmallEtale.associatedModuleIsoSectionsSheaf B S hS L).inv.val.app
    (op ((smallFunctor (smallEtaleRingedSite B S hS)).obj U))).hom.map_smul r x)).symm

/-- `smallModelSection` is bijective. -/
theorem smallModelSection_bijective (U : SmallModel.{u} (smallEtaleRingedSite B S hS).C) :
    Function.Bijective (smallModelSection B hS L hL U) := by
  have : L.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible L hL
  exact ConcreteCategory.bijective_of_isIso
    ((_root_.SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _
      (op ((smallFunctor (smallEtaleRingedSite B S hS)).obj U))).mapIso
        (SmallEtale.associatedModuleIsoSectionsSheaf B S hS L)).inv

/-- The units of the small model of the size-bounded small étale ringed site are the invertible
global functions. -/
def smallModelUnitsEquiv :
    GlobalUnitsEquiv (smallTopology (smallEtaleRingedSite B S hS))
      (smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale)
      (((smallFunctor (smallEtaleRingedSite B S hS)).sheafPushforwardContinuous AddCommGrpCat.{u}
        (smallTopology (smallEtaleRingedSite B S hS)) (smallEtaleRingedSite B S hS).J).obj
          (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS))) where
  equiv _ := AddEquiv.refl _
  naturality _ _ := rfl

include hL in
/-- The associated module of `L`, restricted to the small model, is invertible. -/
theorem isInvertible_smallModelModule :
    Stacks.SheafOfModules.IsInvertible
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
        (smallEtaleRingedSite B S hS)).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
          (smallEtaleRingedSite B S hS)).O).property
      (smallModelModule B hS L) :=
  isInvertible_denseRestrictModules_obj _ _ _ _
    (SmallEtale.isInvertible_ringSheaf_associatedModule B S hS L hL)

/-- The generator torsor of Tag 040E for the restriction of `L^a` to the small model. -/
abbrev smallModelGeneratorTorsor :=
  Stacks.Cohomology.Torsors.Generators.generatorTorsor
    (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite (smallEtaleRingedSite B S hS))
    (isLocallyRinged_denseRestrict _ _ _ (smallEtaleRingedSite_isLocallyRinged B S hS))
    (smallModelModule B hS L) (isInvertible_smallModelModule B hS L hL)

/-- The inclusion of the small model into Mathlib's small étale site is continuous. -/
theorem isContinuous_smallModel :
    (smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙
      𝟭 S.Etale).IsContinuous
      (smallTopology (smallEtaleRingedSite B S hS)) S.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ (SmallEtale.topology B S hS) _

/-- The inclusion of the small model into Mathlib's small étale site is cocontinuous. -/
theorem isCocontinuous_smallModel :
    (smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙
      𝟭 S.Etale).IsCocontinuous
      (smallTopology (smallEtaleRingedSite B S hS)) S.smallEtaleTopology :=
  isCocontinuous_comp _ _ _ (SmallEtale.topology B S hS)

attribute [local instance] isContinuous_smallModel isCocontinuous_smallModel

/-- A universal generator of the pullback of `L` gives a local generator of `L^a` on the small
model. -/
def smallModelGenerator (U : SmallModel.{u} (smallEtaleRingedSite B S hS).C)
    (x : (generatorPresheaf L).obj (op ((smallFunctor (smallEtaleRingedSite B S hS) ⋙
      SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale).obj U))) :
    Stacks.Cohomology.Torsors.Generators.GeneratorSections
      (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite (smallEtaleRingedSite B S hS))
      (smallModelModule B hS L) U := by
  refine ⟨smallModelSection B hS L hL U (sec L x), fun V f => ?_⟩
  have h := (smallModelSection_bijective B hS L hL V).comp (x.2 ((Scheme.Etale.forget S).map
    ((smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙
      𝟭 S.Etale).map f)))
  refine (congrArg Function.Bijective (funext fun r => ?_)).mp h
  change smallModelSection B hS L hL V _ =
    r • (smallModelModule B hS L).val.map f.op (smallModelSection B hS L hL U (sec L x))
  exact ((congrArg (fun y : (smallModelModule B hS L).val.obj (op V) => r • y)
    (smallModelSection_restrict B hS L hL f (sec L x))).trans
    (smallModelSection_smul B hS L hL V r _)).symm

/-- The section underlying `smallModelGenerator` commutes with restriction along a morphism of the
small model. -/
theorem smallModelGenerator_restrict {U V : SmallModel.{u} (smallEtaleRingedSite B S hS).C}
    (f : V ⟶ U) (x : (generatorPresheaf L).obj (op ((smallFunctor (smallEtaleRingedSite B S hS) ⋙
      SmallEtale.toEtaleSite B S hS ⋙ 𝟭 S.Etale).obj U))) :
    (smallModelGenerator B hS L hL V ((generatorPresheaf L).map
      ((smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙
        𝟭 S.Etale).map f).op x)).val =
      (smallModelModule B hS L).val.map f.op (smallModelGenerator B hS L hL U x).val :=
  (smallModelSection_restrict B hS L hL f (sec L x)).symm

/-- The comparison of the torsor of universal generators on the small model with the generator
torsor of Tag 040E of the restriction of `L^a`. -/
def smallModelTorsorHom :
    (generatorTorsorOn.{0} L hL (smallModelUnitsEquiv B hS)).1.Hom
      (smallModelGeneratorTorsor B hS L hL).torsor.1 where
  hom :=
    { app U := TypeCat.ofHom fun x => ((smallModelGeneratorTorsor B hS L hL).sectionsEquiv U).symm
        (smallModelGenerator B hS L hL U.unop x.down)
      naturality {U V} f := by
        ext x
        apply ((smallModelGeneratorTorsor B hS L hL).sectionsEquiv V).injective
        apply Subtype.ext
        change (((smallModelGeneratorTorsor B hS L hL).sectionsEquiv V)
            (((smallModelGeneratorTorsor B hS L hL).sectionsEquiv V).symm
              (smallModelGenerator B hS L hL V.unop ((generatorPresheaf L).map
                ((smallFunctor (smallEtaleRingedSite B S hS) ⋙ SmallEtale.toEtaleSite B S hS ⋙
                  𝟭 S.Etale).map f.unop).op x.down)))).val =
          (((smallModelGeneratorTorsor B hS L hL).sectionsEquiv V)
            ((smallModelGeneratorTorsor B hS L hL).torsor.1.presheaf.map f
              (((smallModelGeneratorTorsor B hS L hL).sectionsEquiv U).symm
                (smallModelGenerator B hS L hL U.unop x.down)))).val
        rw [Equiv.apply_symm_apply, smallModelGenerator_restrict]
        exact (congrArg (fun z : Stacks.Cohomology.Torsors.Generators.GeneratorSections
            (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
              (smallEtaleRingedSite B S hS))
            (smallModelModule B hS L) U.unop => (smallModelModule B hS L).val.restrictₛₗ f z.val)
          (Equiv.apply_symm_apply ((smallModelGeneratorTorsor B hS L hL).sectionsEquiv U)
            (smallModelGenerator B hS L hL U.unop x.down))).symm.trans
          ((smallModelGeneratorTorsor B hS L hL).sectionsEquiv_restrict f _).symm }
  map_act U g x := by
    let a : ((Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
      (smallEtaleRingedSite B S hS)).O.obj.obj U)ˣ := Additive.toMul (Multiplicative.toAdd g)
    apply ((smallModelGeneratorTorsor B hS L hL).sectionsEquiv U).injective
    apply Subtype.ext
    refine (congrArg Subtype.val (Equiv.apply_symm_apply _ _)).trans ?_
    refine Eq.trans ?_ ((smallModelGeneratorTorsor B hS L hL).sectionsEquiv_smul U a _).symm
    refine (smallModelSection_smul B hS L hL U.unop a.val _).symm.trans ?_
    exact congrArg (fun z : Stacks.Cohomology.Torsors.Generators.GeneratorSections
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite (smallEtaleRingedSite B S hS))
        (smallModelModule B hS L) U.unop =>
          @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf
            (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
              (smallEtaleRingedSite B S hS)).O).obj.obj (op U.unop)) _ _ a.val z.val)
      (Equiv.apply_symm_apply ((smallModelGeneratorTorsor B hS L hL).sectionsEquiv U)
        (smallModelGenerator B hS L hL U.unop x.down)).symm

/-- The torsor of universal generators on the small model and the generator torsor of
Tag 040E have the same class. -/
theorem torsorClass_smallModel :
    Quotient.mk (torsorSetoid _) (generatorTorsorOn.{0} L hL (smallModelUnitsEquiv B hS)) =
      Quotient.mk (torsorSetoid _) (smallModelGeneratorTorsor B hS L hL).torsor :=
  Quotient.sound ⟨smallModelTorsorHom B hS L hL,
    Stacks.Cohomology.Torsors.Generators.torsorHom_isIso
      (generatorTorsorOn.{0} L hL (smallModelUnitsEquiv B hS)).2 _⟩

/-- **The identification `H¹(S_étale, 𝒪^*) = Pic(S)` on the size-bounded small étale site
sends the class of the torsor of local generators of `L` to the class of `L`.** -/
theorem h1UnitsAddEquivOfScheme_generatorTorsorOn :
    SmallEtale.h1UnitsAddEquivOfScheme B S hS (torsorIsoClassesEquivH1 _ (Quotient.mk _
        (generatorTorsorOn.{0} L hL (smallEtaleUnitsEquiv S B hS)))) =
      Stacks.SheafOfModules.picardClass S.presheaf
        (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L hL := by
  simp only [SmallEtale.h1UnitsAddEquivOfScheme, AddEquiv.trans_apply,
    Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroupSkeleton,
    Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroupOfEssentiallySmall]
  have := isEquivalence_sheafPushforward_smallFunctor (smallEtaleRingedSite B S hS)
  have := smallEtaleRingedSite_essentiallySmall B S hS
  have : HasExt.{u + 1} (Sheaf (smallTopology (smallEtaleRingedSite B S hS)) AddCommGrpCat.{u}) :=
    HasExt.standard _
  have : HasExt.{u + 1} (Sheaf (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite
      (smallEtaleRingedSite B S hS)).J AddCommGrpCat.{u}) := HasExt.standard _
  have hLa := SmallEtale.isInvertible_ringSheaf_associatedModule B S hS L hL
  let := Stacks.Cohomology.Torsors.Generators.picardGroupAddCommGroup (smallEtaleRingedSite B S hS)
  have s5 : (SmallEtale.picardGroupAssociatedModuleAddEquiv B S hS).symm
      (Stacks.SheafOfModules.picardClass (smallEtaleRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property
        ((SmallEtale.associatedModule B S hS).obj L) hLa) =
      Stacks.SheafOfModules.picardClass S.presheaf
        (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L hL :=
    (AddEquiv.symm_apply_eq _).2
      (SmallEtale.picardGroupAssociatedModuleEquiv_picardClass B S hS L hL).symm
  have s4 : (Stacks.SheafOfModules.picardGroupShrinkAddEquiv (smallEtaleRingedSite B S hS).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property).symm
      (Stacks.SheafOfModules.Picard.classOf _ _ ((SmallEtale.associatedModule B S hS).obj L) hLa) =
      Stacks.SheafOfModules.picardClass (smallEtaleRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property
        ((SmallEtale.associatedModule B S hS).obj L) hLa :=
    (AddEquiv.symm_apply_eq _).2
      (Stacks.SheafOfModules.picardGroupShrinkAddEquiv_picardClass _ _ _ _).symm
  have s3 : (picardGroupDenseRestrictAddEquiv (smallTopology (smallEtaleRingedSite B S hS))
      (smallEtaleRingedSite B S hS) (smallFunctor (smallEtaleRingedSite B S hS))).symm
      (Stacks.SheafOfModules.Picard.classOf _ _ (smallModelModule B hS L)
        (isInvertible_smallModelModule B hS L hL)) =
      Stacks.SheafOfModules.Picard.classOf (smallEtaleRingedSite B S hS).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS).O).property
        ((SmallEtale.associatedModule B S hS).obj L) hLa :=
    (AddEquiv.symm_apply_eq _).2 (picardGroupDenseRestrictAddEquiv_classOf _ _ _ _ _).symm
  have s1 := hAddEquiv_generatorTorsorOn.{u + 1, 0, u, u + 1, u, u, u} L hL
    (smallTopology (smallEtaleRingedSite B S hS)) (smallFunctor (smallEtaleRingedSite B S hS))
    (Stacks.Cohomology.Torsors.Generators.unitsAddSheaf (smallEtaleRingedSite B S hS))
    (smallEtaleUnitsEquiv S B hS) (smallModelUnitsEquiv B hS) (fun _ _ => rfl)
  rw [torsorClass_smallModel] at s1
  have s2 := Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup_symm_classOf
    (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite (smallEtaleRingedSite B S hS))
    (isLocallyRinged_denseRestrict _ _ _ (smallEtaleRingedSite_isLocallyRinged B S hS))
    (smallModelModule B hS L) (isInvertible_smallModelModule B hS L hL)
  refine (congrArg (SmallEtale.picardGroupAssociatedModuleAddEquiv B S hS).symm ?_).trans s5
  refine (congrArg (Stacks.SheafOfModules.picardGroupShrinkAddEquiv _ _).symm ?_).trans s4
  refine (congrArg (picardGroupDenseRestrictAddEquiv _ _ _).symm ?_).trans s3
  refine (congrArg (Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup _ _)
    s1).trans ?_
  exact (congrArg (Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup _ _)
    s2.symm).trans (AddEquiv.apply_symm_apply _ _)

end SmallModel





/-- **The étale identification of Tag 03P8 sends the class of the torsor of local generators
of an invertible module `L` to the class of `L` in `Pic(S)`.** -/
theorem etaleH1MultiplicativeAddEquivPicard_generatorTorsorOn
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] :
    Stacks.Kummer.etaleH1MultiplicativeAddEquivPicard.{w, v, u} S
        (torsorIsoClassesEquivH1 _ (Quotient.mk _
          (generatorTorsorOn.{max (u + 1) v} L hL (multiplicativeUnitsEquiv.{v} S)))) =
      Stacks.SheafOfModules.picardClass S.presheaf
        (Stacks.RingedSpace.structureIsSheaf S.toRingedSpace) L hL := by
  have hS : (BigEtaleSite.ofSet {S}).Contains S := BigEtaleSite.contains_ofSet _ (by simp)
  exact ((congrArg (SmallEtale.h1MultiplicativeAddEquivOfContains (BigEtaleSite.ofSet {S}) S hS)
    (sheafHOneAddEquiv_symm_extPostcomp_generatorTorsorOn.{w, v, u} L hL)).trans
    (h1MultiplicativeAddEquivOfContains_generatorTorsorOn (BigEtaleSite.ofSet {S}) hS L hL)).trans
    (h1UnitsAddEquivOfScheme_generatorTorsorOn (BigEtaleSite.ofSet {S}) hS L hL)

/-! ### Pullback of local generators along a morphism of schemes -/

section Pullback

variable {X Y : Scheme.{u}} (π : X ⟶ Y) (L : Y.Modules)
  (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
    (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).property L)

/-- The pullback of sections of Tag 03DS from a scheme over `Y` to a scheme over `X`, through a
morphism over `Y`, read in the sections of the pullback `π^*L`. -/
def baseChangeSectionsMap {A : Over X} {T : Over Y} (p : (Over.map π).obj A ⟶ T)
    (s : Γ((Scheme.Modules.pullback T.hom).obj L, ⊤)) :
    Γ((Scheme.Modules.pullback A.hom).obj ((Scheme.Modules.pullback π).obj L), ⊤) :=
  (Stacks.Sites.baseChangeSectionsIso L (Over.mk π) A).hom (pullbackSectionsMap L p s)

/-- Pulling back a section `baseChangeSectionsMap π L p s` along `g : B ⟶ A` gives
`baseChangeSectionsMap` of `s` along the composite `(Over.map π).map g ≫ p`. -/
theorem pullbackSectionsMap_baseChangeSectionsMap {A B : Over X} {T : Over Y} (g : B ⟶ A)
    (p : (Over.map π).obj A ⟶ T) (s : Γ((Scheme.Modules.pullback T.hom).obj L, ⊤)) :
    pullbackSectionsMap ((Scheme.Modules.pullback π).obj L) g (baseChangeSectionsMap π L p s) =
      baseChangeSectionsMap π L ((Over.map π).map g ≫ p) s := by
  refine (congrArg (fun φ => φ (pullbackSectionsMap L p s))
    (Stacks.Sites.pullbackSectionsMap_baseChange L (Over.mk π) g)).symm.trans ?_
  change (Stacks.Sites.baseChangeSectionsIso L (Over.mk π) B).hom
    (pullbackSectionsMap L ((Over.map π).map g) (pullbackSectionsMap L p s)) = _
  rw [← pullbackSectionsMap_comp_apply]
  rfl

/-- Multiplication by a function on `A` commutes with `baseChangeSectionsMap`. -/
theorem baseChangeSectionsMap_smul {A : Over X} {T : Over Y} (p : (Over.map π).obj A ⟶ T)
    (r : Γ(A.left, ⊤)) (s : Γ((Scheme.Modules.pullback T.hom).obj L, ⊤)) :
    r • baseChangeSectionsMap π L p s =
      (Stacks.Sites.baseChangeSectionsIso L (Over.mk π) A).hom (r • pullbackSectionsMap L p s) :=
  (Scheme.Modules.Hom.app_smul _ r _).symm

/-- The base change isomorphism of sections is bijective. -/
theorem baseChangeSectionsIso_bijective (A : Over X) :
    Function.Bijective (Stacks.Sites.baseChangeSectionsIso L (Over.mk π) A).hom :=
  ConcreteCategory.bijective_of_isIso _

/-- **The pullback of a universal generator is a universal generator.** -/
theorem IsUniversalGenerator.baseChangeSectionsMap {A : Over X} {T : Over Y}
    (p : (Over.map π).obj A ⟶ T) {s : Γ((Scheme.Modules.pullback T.hom).obj L, ⊤)}
    (hs : IsUniversalGenerator L s) :
    IsUniversalGenerator ((Scheme.Modules.pullback π).obj L) (baseChangeSectionsMap π L p s) := by
  intro W g
  rw [pullbackSectionsMap_baseChangeSectionsMap]
  refine (congrArg Function.Bijective (funext fun r => ?_)).mp
    ((baseChangeSectionsIso_bijective π L W).comp (hs ((Over.map π).map g ≫ p)))
  exact (baseChangeSectionsMap_smul π L _ r s).symm

/-- The projection `U ×_Y X ⟶ U`, as a morphism of schemes over `Y`. -/
def baseChangeProjection (U : Y.Etale) :
    (Over.map π).obj ((Scheme.Etale.forget X).obj
        ((Stacks.EtaleCohomology.smallEtaleBaseChange π).obj U)) ⟶
      (Scheme.Etale.forget Y).obj U :=
  Over.homMk (pullback.fst U.hom π) pullback.condition

/-- `baseChangeProjection` is natural in the étale scheme over `Y`. -/
theorem baseChangeProjection_naturality {U U' : Y.Etale} (f : U' ⟶ U) :
    baseChangeProjection π U' ≫ (Scheme.Etale.forget Y).map f =
      (Over.map π).map ((Scheme.Etale.forget X).map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange π).map f)) ≫ baseChangeProjection π U := by
  ext
  exact (pullback.lift_fst _ _ _).symm

/-- **The pullback of a local generator**: a universal generator of `U^*L` pulls back to a
universal generator of `(U ×_Y X)^*(π^*L)`. -/
def generatorPullback (U : Y.Etale) (s : (generatorPresheaf L).obj (op U)) :
    (generatorPresheaf ((Scheme.Modules.pullback π).obj L)).obj
      (op ((Stacks.EtaleCohomology.smallEtaleBaseChange π).obj U)) :=
  ⟨baseChangeSectionsMap π L (baseChangeProjection π U) (sec L s),
    IsUniversalGenerator.baseChangeSectionsMap π L (baseChangeProjection π U) s.2⟩

/-- The section underlying the pullback of a local generator is the pullback of its section. -/
theorem sec_generatorPullback (U : Y.Etale) (s : (generatorPresheaf L).obj (op U)) :
    sec ((Scheme.Modules.pullback π).obj L) (generatorPullback π L U s) =
      baseChangeSectionsMap π L (baseChangeProjection π U) (sec L s) :=
  rfl

/-- `generatorPullback` commutes with restriction along a morphism of `Y_étale`. -/
theorem generatorPullback_naturality {U U' : Y.Etale} (f : U' ⟶ U)
    (s : (generatorPresheaf L).obj (op U)) :
    generatorPullback π L U' ((generatorPresheaf L).map f.op s) =
      (generatorPresheaf ((Scheme.Modules.pullback π).obj L)).map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange π).map f).op (generatorPullback π L U s) := by
  apply Subtype.ext
  change sec ((Scheme.Modules.pullback π).obj L) (generatorPullback π L U'
      ((generatorPresheaf L).map f.op s)) =
    sec ((Scheme.Modules.pullback π).obj L)
      ((generatorPresheaf ((Scheme.Modules.pullback π).obj L)).map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange π).map f).op (generatorPullback π L U s))
  rw [sec_generatorPullback, sec_map, sec_map, sec_generatorPullback]
  refine Eq.trans ?_ (pullbackSectionsMap_baseChangeSectionsMap π L _ _ (sec L s)).symm
  exact (congrArg (Stacks.Sites.baseChangeSectionsIso L (Over.mk π) _).hom
    (pullbackSectionsMap_comp_apply L _ _ (sec L s)).symm).trans
    (congrArg (fun p => baseChangeSectionsMap π L p (sec L s))
      (baseChangeProjection_naturality π f))

/-- `generatorPullback` carries the action of a unit `a` to the action of the pullback of `a`. -/
theorem generatorPullback_unitSmul (U : Y.Etale) (a : (Γ(U.left, ⊤))ˣ)
    (s : (generatorPresheaf L).obj (op U)) :
    generatorPullback π L U (unitSmul L a s) =
      unitSmul ((Scheme.Modules.pullback π).obj L)
        (Units.map (pullback.fst U.hom π).appTop.hom.toMonoidHom a)
        (generatorPullback π L U s) := by
  apply Subtype.ext
  change sec ((Scheme.Modules.pullback π).obj L) (generatorPullback π L U (unitSmul L a s)) =
    sec ((Scheme.Modules.pullback π).obj L) (unitSmul ((Scheme.Modules.pullback π).obj L)
        (Units.map (pullback.fst U.hom π).appTop.hom.toMonoidHom a) (generatorPullback π L U s))
  rw [sec_generatorPullback, sec_unitSmul]
  exact (congrArg (Stacks.Sites.baseChangeSectionsIso L (Over.mk π) _).hom
    (pullbackSectionsMap_smul L (baseChangeProjection π U) (a : Γ(U.left, ⊤)) (sec L s))).trans
    (baseChangeSectionsMap_smul π L (baseChangeProjection π U) _ (sec L s)).symm

/-- Restriction in `liftedGeneratorPresheaf` is restriction in `generatorPresheaf`, read through
`ULift.up`. -/
theorem liftedGeneratorPresheaf_up_map {Z : Scheme.{u}} (M : Z.Modules) {U U' : Z.Etaleᵒᵖ}
    (f : U ⟶ U') (y : (generatorPresheaf M).obj (op U.unop)) :
    (ULift.up ((generatorPresheaf M).map f.unop.op y) : ULift.{max (u + 1) v} _) =
      (liftedGeneratorPresheaf.{max (u + 1) v} M (𝟭 Z.Etale)).map f (ULift.up y) :=
  rfl

/-- `generatorPullback`, read through `ULift.up`, commutes with restriction in the lifted
generator presheaves. -/
theorem liftedGeneratorPresheaf_generatorPullback {U U' : Y.Etaleᵒᵖ} (f : U ⟶ U')
    (x : (liftedGeneratorPresheaf.{max (u + 1) v} L (𝟭 Y.Etale)).obj U) :
    (ULift.up (generatorPullback π L U'.unop
        ((liftedGeneratorPresheaf.{max (u + 1) v} L (𝟭 Y.Etale)).map f x).down) :
      ULift.{max (u + 1) v} _) =
      (liftedGeneratorPresheaf.{max (u + 1) v} ((Scheme.Modules.pullback π).obj L) (𝟭 X.Etale)).map
        ((Stacks.EtaleCohomology.smallEtaleBaseChange π).op.map f)
        (ULift.up (generatorPullback π L U.unop x.down)) := by
  rw [← liftedGeneratorPresheaf_up_map]
  exact congrArg ULift.up (generatorPullback_naturality π L f.unop x.down)

/-- The pullback of local generators, as a morphism from the torsor of generators of `L` on
`Y_étale` to the direct image of the torsor of generators of `π^*L` on `X_étale`. -/
def generatorTorsorPullback :
    (generatorTorsorOn.{max (u + 1) v} L hL (multiplicativeUnitsEquiv.{v} Y)).1.presheaf ⟶
      (Stacks.EtaleCohomology.smallEtaleBaseChange π).op ⋙
        (generatorTorsorOn.{max (u + 1) v} ((Scheme.Modules.pullback π).obj L)
          (isInvertible_pullback L hL π) (multiplicativeUnitsEquiv.{v} X)).1.presheaf where
  app U := TypeCat.ofHom fun x => ULift.up (generatorPullback π L U.unop x.down)
  naturality {U U'} f := by
    apply ConcreteCategory.hom_ext
    intro x
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    exact liftedGeneratorPresheaf_generatorPullback π L f x

end Pullback

end Stacks.EtaleGenerators

namespace Stacks.Kummer

open Stacks.EtaleGenerators

/-- **Naturality of the étale identification `H¹(X_étale, 𝐆_m) = Pic(X)` of Tag 03P8.** For a
morphism of schemes `π : X ⟶ Y`, pulling a class of `H¹(Y_étale, 𝐆_m)` back to `X` (restriction
along `π` followed by `π^{-1} 𝐆_{m,Y} ⟶ 𝐆_{m,X}`) corresponds to pulling back invertible modules:
`e_X(π^*x) = π^*(e_Y x)`. -/
theorem etaleH1MultiplicativeAddEquivPicard_naturality {X Y : Scheme.{u}} (π : X ⟶ Y)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (x : Sheaf.H.{w} (multiplicativeSheaf.{u, v} Y) 1) :
    etaleH1MultiplicativeAddEquivPicard.{w, v, u} X
        (Sheaf.H.map (multiplicativeInverseImageComparison.{u, v} π) 1
          (Stacks.EtaleCohomology.etaleCohomologyRestrictionMap.{u, v, w} π _ 1 x)) =
      Stacks.Picard.schemePullbackClassHom π
        (etaleH1MultiplicativeAddEquivPicard.{w, v, u} Y x) := by
  obtain ⟨L, hL, hLx⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _
    (etaleH1MultiplicativeAddEquivPicard.{w, v, u} Y x)
  have hx : x = torsorIsoClassesEquivH1 _ (Quotient.mk _
      (generatorTorsorOn.{max (u + 1) v} L hL (multiplicativeUnitsEquiv.{v} Y))) :=
    (etaleH1MultiplicativeAddEquivPicard.{w, v, u} Y).injective
      (hLx.symm.trans (etaleH1MultiplicativeAddEquivPicard_generatorTorsorOn.{w, v, u} L hL).symm)
  subst hx
  rw [etaleH1MultiplicativeAddEquivPicard_generatorTorsorOn.{w, v, u} L hL,
    Stacks.EtaleCohomology.sheafHMap_etaleCohomologyRestrictionMap_torsorClass π _ _
    (multiplicativeInverseImageComparison.{u, v} π) _
    (generatorTorsorOn.{max (u + 1) v} ((Scheme.Modules.pullback π).obj L)
      (isInvertible_pullback L hL π) (multiplicativeUnitsEquiv.{v} X))
    (generatorTorsorPullback π L hL) ?_]
  · rw [etaleH1MultiplicativeAddEquivPicard_generatorTorsorOn.{w, v, u}]
    exact (Stacks.Picard.pullbackClass_classOf π.toLRSHom.toShHom L hL).symm
  · intro U h s
    rw [multiplicativeInverseImageComparison_transpose]
    exact ULift.ext (generatorPullback_unitSmul π L U.unop _ s.down)

/-- Restriction of étale cohomology along a morphism of schemes commutes with morphisms of
coefficient sheaves. -/
theorem etaleCohomologyRestrictionMap_sheafHMap {X Y : Scheme.{u}} (π : X ⟶ Y)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    {F G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (φ : F ⟶ G) (q : ℕ)
    (x : Sheaf.H.{w} F q) :
    Stacks.EtaleCohomology.etaleCohomologyRestrictionMap.{u, v, w} π G q (Sheaf.H.map φ q x) =
      Sheaf.H.map ((Stacks.EtaleCohomology.etaleAbelianInverseImage.{u, v} π).map φ) q
        (Stacks.EtaleCohomology.etaleCohomologyRestrictionMap.{u, v, w} π F q x) := by
  rw [Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_apply,
    Stacks.EtaleCohomology.etaleCohomologyRestrictionMap_apply, Sheaf.H.map_apply,
    Sheaf.H.map_apply, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- **Naturality of `H¹(X_étale, μ_n) → Pic(X)`** (the inclusion `μ_n ⊆ 𝐆_m` followed by
Tag 03P8) under pullback along an arbitrary morphism of schemes. -/
theorem h1RootsOfUnityToPicard_naturality {X Y : Scheme.{u}} (π : X ⟶ Y)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (n : ℕ)
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) 1) :
    h1RootsOfUnityToPicard.{w, v, u} X n
        (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, v, w} π n 1 x) =
      Stacks.Picard.schemePullbackClassHom π (h1RootsOfUnityToPicard.{w, v, u} Y n x) := by
  have key : Sheaf.H.map (rootsOfUnityι.{u, v} X n) 1
      (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, v, w} π n 1 x) =
      Sheaf.H.map (multiplicativeInverseImageComparison.{u, v} π) 1
        (Stacks.EtaleCohomology.etaleCohomologyRestrictionMap.{u, v, w} π _ 1
          (Sheaf.H.map (rootsOfUnityι.{u, v} Y n) 1 x)) := by
    rw [Stacks.EtaleCohomology.rootsOfUnityPullbackMap_apply, ← Sheaf.H.map_comp_apply,
      rootsOfUnityInverseImageComparison_comp_rootsOfUnityι, Sheaf.H.map_comp_apply,
      etaleCohomologyRestrictionMap_sheafHMap]
  change etaleH1MultiplicativeAddEquivPicard.{w, v, u} X
    (Sheaf.H.map (rootsOfUnityι.{u, v} X n) 1
      (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, v, w} π n 1 x)) = _
  rw [key, etaleH1MultiplicativeAddEquivPicard_naturality]
  rfl

/-- **Naturality of `H¹(X_étale, μ_n) ≅ Pic(X)[n]`** under pullback along an arbitrary morphism
of schemes, read in `Pic(X)`. -/
theorem h1RootsOfUnityAddEquivPicardTorsion_naturality {X Y : Scheme.{u}} (π : X ⟶ Y)
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})] (n : ℕ)
    (hn0 : n ≠ 0) (hX : IsUnit ((n : ℕ) : Γ(X, ⊤))) (hY : IsUnit ((n : ℕ) : Γ(Y, ⊤)))
    (hsurjX : Function.Surjective (Sheaf.H.map.{w} (powMap.{u, v} X n) 0))
    (hsurjY : Function.Surjective (Sheaf.H.map.{w} (powMap.{u, v} Y n) 0))
    (x : Sheaf.H.{w} (rootsOfUnitySheaf.{u, v} Y n) 1) :
    ((h1RootsOfUnityAddEquivPicardTorsion.{w, v, u} X n hn0 hX hsurjX
        (Stacks.EtaleCohomology.rootsOfUnityPullbackMap.{u, v, w} π n 1 x) :
        Stacks.Picard.ofScheme X)) =
      Stacks.Picard.schemePullbackClassHom π
        (h1RootsOfUnityAddEquivPicardTorsion.{w, v, u} Y n hn0 hY hsurjY x) :=
  h1RootsOfUnityToPicard_naturality.{w, v, u} π n x

end Stacks.Kummer


end
