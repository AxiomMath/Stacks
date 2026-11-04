module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageStalkTowerNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicHigherDirectImageShriekLeray
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.OfStrictTowerHom
public import StacksFrontier.CategoryTheory.Abelian.TowerStableImageLiftComp

/-!
# The base change morphisms of `R^r g_!` of an ℓ-adic sheaf

Let `g : U ⟶ W` be separated of finite type with a compactification, `jV : V ⟶ W` a morphism of
the big étale site with `V` Noetherian, `U' = U ×_W V` with `g' : U' ⟶ V`, `jU : U' ⟶ U` and any
compactification of `g'`, and `K` an ℓ-adic sheaf on `U`. Proper base change for `R^r g_!` of
torsion sheaves ([Tag 0F7L](https://stacks.math.columbia.edu/tag/0F7L),
`Stacks.EtaleCohomology.lowerShriekHomologyBaseChangeIso`) along the levels of the torsion-free
models gives morphisms of ℓ-adic sheaves

`χ : (R^r g_! K)|_V ⟶ R^r g'_!(K|_{U'})` and `χ' : R^r g'_!(K|_{U'}) ⟶ (R^r g_! K)|_V`

(`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeHom` and
`Stacks.EtaleCohomology.LAdicSheaf.higherDirectImageShriekBaseChangeInv`), through the
factorisations of maps of towers through the stable images. The torsion-free models of `K` and of
`K|_{U'}` are taken at their own torsion bounds, so the two morphisms are inverse up to the
isogeny between the two models.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.LAdicTower
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {U W U' V : B.Scheme} [IsNoetherian U.1] [IsNoetherian W.1] [IsNoetherian U'.1]
  [IsNoetherian V.1] (g : U ⟶ W)
  [LocallyOfFiniteType (B.inclusion.map g)] [QuasiCompact (B.inclusion.map g)]
  [IsSeparated (B.inclusion.map g)] (jg : CompactificationOf (Over.mk (B.inclusion.map g)))
  (g' : U' ⟶ V) [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
  [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g')))
  (jU : U' ⟶ U) (jV : V ⟶ W)
  (hpb : IsPullback (B.inclusion.map jU) (B.inclusion.map g') (B.inclusion.map g)
    (B.inclusion.map jV))
  (K : LAdicSheaf.{u, u + 1} B U ℓ)

/-! ### The base change maps of the towers -/

/-- Proper base change (Tag 0F7L) for `R^r g_!` of ℓ-power torsion sheaves along the square. -/
def lowerShriekHomologyTorsionBaseChangeIso (r : ℤ) :
    (IsLPowerTorsion ℓ U.1).ι ⋙ etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU) ⋙
        lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r ≅
      (IsLPowerTorsion ℓ U.1).ι ⋙ lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g) jg r ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) :=
  haveI : CompactSpace (B.inclusion.obj V) := (inferInstance : CompactSpace V.1)
  haveI : QuasiSeparatedSpace (B.inclusion.obj V) :=
    @IsLocallyNoetherian.quasiSeparatedSpace V.1 IsNoetherian.toIsLocallyNoetherian
  lowerShriekHomologyBaseChangeIso ℤ_[ℓ] hpb jg jg' (IsLPowerTorsion ℓ U.1)
    (fun _ ⟨N, hN⟩ => ⟨ℓ ^ N, pow_pos (Fact.out : ℓ.Prime).pos N, hN⟩) r

/-- An isomorphism `P.ι ⋙ F₁ ⋙ F₂ ≅ P.ι ⋙ G₁ ⋙ G₂` of functors on a full subcategory, read
along a functor `T` with values in the subcategory: the isomorphism
`(T ⋙ F₁) ⋙ F₂ ≅ (T ⋙ G₁) ⋙ G₂` through the associators and the lift of `T`. -/
def _root_.CategoryTheory.ObjectProperty.liftWhiskerIso {C C₁ C₂ D J : Type*} [Category* C]
    [Category* C₁] [Category* C₂] [Category* D] [Category* J] (P : ObjectProperty C) (T : J ⥤ C)
    (hT : ∀ j, P (T.obj j)) {F₁ : C ⥤ C₁} {F₂ : C₁ ⥤ D} {G₁ : C ⥤ C₂} {G₂ : C₂ ⥤ D}
    (β : P.ι ⋙ F₁ ⋙ F₂ ≅ P.ι ⋙ G₁ ⋙ G₂) : (T ⋙ F₁) ⋙ F₂ ≅ (T ⋙ G₁) ⋙ G₂ :=
  Functor.associator T F₁ F₂ ≪≫
    Functor.isoWhiskerRight (P.liftCompιIso T hT).symm (F₁ ⋙ F₂) ≪≫
    Functor.associator (P.lift T hT) P.ι (F₁ ⋙ F₂) ≪≫
    Functor.isoWhiskerLeft (P.lift T hT) β ≪≫
    (Functor.associator (P.lift T hT) P.ι (G₁ ⋙ G₂)).symm ≪≫
    Functor.isoWhiskerRight (P.liftCompιIso T hT) (G₁ ⋙ G₂) ≪≫
    (Functor.associator T G₁ G₂).symm

/-- **Proper base change read between the towers of levels**: the inverse image along `jV` of
the tower `n ↦ R^r g_! K'ₙ` of the torsion-free model `K'` of `K` is the tower
`n ↦ R^r g'_!(jU⁻¹ K'ₙ)`. This is Tag 0F7L on the levels of `K'`, which are ℓ-power torsion,
read along the tower of levels (`CategoryTheory.ObjectProperty.liftWhiskerIso`). -/
def LAdicSheaf.lowerShriekTowerBaseChangeIso (r : ℤ) :
    (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ K) ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)) ⋙
        lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r ≅
      LAdicSheaf.lowerShriekTower B ℓ g jg K r ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) :=
  (IsLPowerTorsion ℓ U.1).liftWhiskerIso
    (LAdicSheaf.padicTower B U ℓ (LAdicSheaf.flatModel B ℓ K))
    (fun m => ⟨m.unop + 1, LAdicSheaf.padicTower_annihilated B U ℓ _ m.unop⟩)
    (lowerShriekHomologyTorsionBaseChangeIso B ℓ g jg g' jg' jU jV hpb r)

/-- **The base change map of the towers `n ↦ R^r g_! K'ₙ`**: restricted to `V`, the tower of the
torsion-free model `K'` of `K` maps to the tower of the torsion-free model of `K|_{U'}`, through
proper base change and the isogeny `K'|_{U'} ⟶ K|_{U'} ⟶ (K|_{U'})'`. -/
def LAdicSheaf.lowerShriekTowerBaseChange (r : ℤ) :
    LAdicSheaf.lowerShriekTower B ℓ g jg K r ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) ⟶
      LAdicSheaf.lowerShriekTower B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r :=
  (LAdicSheaf.lowerShriekTowerBaseChangeIso B ℓ g jg g' jg' jU jV hpb K r).inv ≫
    Functor.whiskerRight
      (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ K)).hom
      (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
    Functor.whiskerRight (LAdicSheaf.padicTowerMap (LAdicSheaf.inverseImageMap jU
        (LAdicSheaf.fromTorsionFreeModel K (LAdicSheaf.torsionBound K)) ≫
        LAdicSheaf.toTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K))))
      (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r)

/-- **The base change map of the towers in the other direction.** -/
def LAdicSheaf.lowerShriekTowerBaseChangeInv (r : ℤ) :
    LAdicSheaf.lowerShriekTower B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r ⟶
      LAdicSheaf.lowerShriekTower B ℓ g jg K r ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) :=
  Functor.whiskerRight (LAdicSheaf.padicTowerMap
      (LAdicSheaf.fromTorsionFreeModel (LAdicSheaf.inverseImage jU K)
          (LAdicSheaf.torsionBound (LAdicSheaf.inverseImage jU K)) ≫
        LAdicSheaf.inverseImageMap jU
          (LAdicSheaf.toTorsionFreeModel K (LAdicSheaf.torsionBound K))))
      (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
    Functor.whiskerRight
      (LAdicSheaf.padicTowerInverseImageIso B ℓ jU (LAdicSheaf.flatModel B ℓ K)).inv
      (lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' r) ≫
    (LAdicSheaf.lowerShriekTowerBaseChangeIso B ℓ g jg g' jg' jU jV hpb K r).hom

/-! ### The base change morphisms of ℓ-adic sheaves -/

variable (r : ℕ) (hcond : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g jg K r)
  (hcond' : LAdicSheaf.HigherDirectImageShriekCondition B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r)

/-- The map of towers from the levels of `(R^r g_! K)|_V` to `n ↦ R^r g'_! (K|_{U'})'ₙ`: the
levels of `R^r g_! K` are the stable images of `n ↦ R^r g_! K'ₙ`, restricted to `V`, followed by
the base change map of the towers. -/
def LAdicSheaf.higherDirectImageShriekBaseChangeTower :
    LAdicSheaf.padicTower B V ℓ
        (LAdicSheaf.inverseImage jV (LAdicSheaf.higherDirectImageShriek B ℓ g jg K r)) ⟶
      LAdicSheaf.lowerShriekTower B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r :=
  haveI := hcond.fst
  (LAdicSheaf.padicTowerInverseImageIso B ℓ jV
      (LAdicSheaf.higherDirectImageShriek B ℓ g jg K r)).inv ≫
    Functor.whiskerRight ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg K r hcond).hom ≫
      (LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).stableImageι)
      (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
    LAdicSheaf.lowerShriekTowerBaseChange B ℓ g jg g' jg' jU jV hpb K r

/-- **The base change morphism `χ : (R^r g_! K)|_V ⟶ R^r g'_!(K|_{U'})`** (Tag 0F7L along the
levels): the factorisation of the base change map of the towers through the stable images. -/
def LAdicSheaf.higherDirectImageShriekBaseChangeHom :
    LAdicSheaf.inverseImage jV (LAdicSheaf.higherDirectImageShriek B ℓ g jg K r) ⟶
      LAdicSheaf.higherDirectImageShriek B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r :=
  haveI := hcond'.fst
  LAdicSheaf.higherDirectImageShriekHom g' jg' (LAdicSheaf.inverseImage jU K) r hcond'
    ((LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).liftStableImage
      (LAdicSheaf.padicTower_isStrict B V ℓ _).epi
      (LAdicSheaf.higherDirectImageShriekBaseChangeTower B ℓ g jg g' jg' jU jV hpb K r hcond))

/-- The map of towers from the levels of `R^r g'_!(K|_{U'})` to the restriction to `V` of the
stable images of `n ↦ R^r g_! K'ₙ`. -/
def LAdicSheaf.higherDirectImageShriekBaseChangeInvTower :
    haveI := hcond.fst
    LAdicSheaf.padicTower B V ℓ
        (LAdicSheaf.higherDirectImageShriek B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r) ⟶
      (LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).stableImageTower ⋙
        etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV) :=
  haveI := hcond.fst
  haveI := hcond'.fst
  (LAdicSheaf.lowerShriekTowerLES B ℓ g jg K r).liftStableImageComp
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV))
    (LAdicSheaf.padicTower_isStrict B V ℓ _).epi
    ((LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r
        hcond').hom ≫
      (LAdicSheaf.lowerShriekTowerLES B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r).stableImageι ≫
      LAdicSheaf.lowerShriekTowerBaseChangeInv B ℓ g jg g' jg' jU jV hpb K r)

/-- **The base change morphism in the other direction**,
`χ' : R^r g'_!(K|_{U'}) ⟶ (R^r g_! K)|_V`. -/
def LAdicSheaf.higherDirectImageShriekBaseChangeInv :
    LAdicSheaf.higherDirectImageShriek B ℓ g' jg' (LAdicSheaf.inverseImage jU K) r ⟶
      LAdicSheaf.inverseImage jV (LAdicSheaf.higherDirectImageShriek B ℓ g jg K r) :=
  haveI := hcond.fst
  LAdicSheaf.homOfPadicTower
    (LAdicSheaf.higherDirectImageShriekBaseChangeInvTower B ℓ g jg g' jg' jU jV hpb K r hcond
        hcond' ≫
      Functor.whiskerRight (LAdicSheaf.padicTowerHigherDirectImageShriekIso B ℓ g jg K r hcond).inv
        (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jV)) ≫
      (LAdicSheaf.padicTowerInverseImageIso B ℓ jV
        (LAdicSheaf.higherDirectImageShriek B ℓ g jg K r)).hom)

end Stacks.EtaleCohomology
