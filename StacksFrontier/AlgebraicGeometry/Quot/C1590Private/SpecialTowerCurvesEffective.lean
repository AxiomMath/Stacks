module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurvesDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerClasses
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerCurveCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerDescent
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerEtaleCompatible
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.SpecialTowerSpecTower
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift

/-!
# Special towers are effective for the stack of curves

The special-tower case of condition (4) of Stacks 0CXU for the small model of `Curves`
(`AlgebraicGeometry.C1590Private.IsSpecialSquareZeroTowerEffectiveOnClasses`), the input
`hspecial` of `AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory_of_diagonal`.

Lift classes reduce to towers of objects
(`AlgebraicGeometry.C1590Private.isSpecialSquareZeroTowerEffectiveOnClasses_of_objects`). A tower
of objects of the small model over the levels `Spec Rₙ` of a special tower is a tower of families
of curves; the levels `Spec Rₙ ⟶ Spec (lim Rₙ)` form an étale limit tower by (B)
(`AlgebraicGeometry.C1590Private.isEtaleCompatibleTower_of_isSpecialTower`,
`AlgebraicGeometry.C1590Private.isEtaleLimitTower_specSite`); on an étale covering of
`Spec (lim Rₙ)` the tower is effective by (C) and (E)
(`AlgebraicGeometry.C1590Private.nonempty_towerChartData_curves`), and the local limit objects
descend by (G)
(`AlgebraicGeometry.C1590Private.TowerChartData.towerIsEffective`), using the stack property of
`Curves` (Stacks 0D52) and its diagonal (Stacks 0D53).

## Main results

* `AlgebraicGeometry.C1590Private.IsEtaleLimitTower.ofIso`: étale limit towers are invariant under
  isomorphisms of towers.
* `AlgebraicGeometry.C1590Private.specialTowerObjectsEffective_curvesSmall`.
* `AlgebraicGeometry.C1590Private.isSpecialSquareZeroTowerEffectiveOnClasses_curvesSmall`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation.Artin
open Deformation.Artin.SquareZeroTower

universe u

namespace AlgebraicGeometry.C1590Private

/-! ### Étale limit towers along isomorphisms -/

section Iso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- A morphism of schemes conjugate by isomorphisms to a thickening is a thickening. -/
theorem isThickening_of_comm_iso {X X' Y Y' : Scheme.{u}} {g : X ⟶ Y} {g' : X' ⟶ Y'}
    (i : X' ≅ X) (j : Y' ≅ Y) (h : g' ≫ j.hom = i.hom ≫ g)
    (hg : Stacks.Thickenings.IsThickening g) : Stacks.Thickenings.IsThickening g' := by
  rw [(Iso.eq_comp_inv j).2 h, Category.assoc]
  exact Stacks.Thickenings.isThickening_comp (Stacks.Thickenings.isThickening_of_isIso _)
    (Stacks.Thickenings.isThickening_comp hg (Stacks.Thickenings.isThickening_of_isIso _))

variable {V V' : BigFppfOver B S hS} {W W' : ℕ → BigFppfOver B S hS} {κ : ∀ n, W n ⟶ V}
  {ℓ : ∀ n, W n ⟶ W (n + 1)} {κ' : ∀ n, W' n ⟶ V'} {ℓ' : ∀ n, W' n ⟶ W' (n + 1)}

/-- **Étale limit towers are invariant under isomorphisms of towers.** -/
theorem IsEtaleLimitTower.ofIso (hW : IsEtaleLimitTower W κ ℓ) (eV : V' ≅ V)
    (e : ∀ n, W' n ≅ W n) (hκ : ∀ n, κ' n ≫ eV.hom = (e n).hom ≫ κ n)
    (hℓ : ∀ n, ℓ' n ≫ (e (n + 1)).hom = (e n).hom ≫ ℓ n) : IsEtaleLimitTower W' κ' ℓ' where
  comp n := by
    rw [← cancel_mono eV.hom, Category.assoc, hκ, ← Category.assoc, hℓ, Category.assoc, hW.comp,
      hκ]
  isThickening_zero := isThickening_of_comm_iso ((𝒯).mapIso (e 0)) ((𝒯).mapIso eV)
    (by simp only [Functor.mapIso_hom, ← Functor.map_comp, hκ]) hW.isThickening_zero
  isThickening_ℓ n := isThickening_of_comm_iso ((𝒯).mapIso (e n)) ((𝒯).mapIso (e (n + 1)))
    (by simp only [Functor.mapIso_hom, ← Functor.map_comp, hℓ]) (hW.isThickening_ℓ n)
  isAffine := by
    have := hW.isAffine
    exact .of_isIso ((𝒯).map eV.hom)
  existsUnique P e' he' hP Q a b c hpb hca hcb s hs := by
    have : Etale ((𝒯).map e') := he'
    refine hW.existsUnique (e' ≫ eV.hom) (by rw [Functor.map_comp]; infer_instance) hP Q a
      (fun n => b n ≫ (e n).hom) c (fun n => ?_) hca (fun n => ?_) s hs
    · refine (hpb n).of_iso (Iso.refl _) (Iso.refl _) ((𝒯).mapIso (e n)) ((𝒯).mapIso eV)
        (by simp) (by simp) (by simp) ?_
      simp only [Functor.mapIso_hom, ← Functor.map_comp, hκ]
    · rw [← Category.assoc, hcb, Category.assoc, hℓ, Category.assoc]

end Iso

/-! ### Kernels of the maps of global sections -/

/-- Composing a ring map with injective ring maps on both sides keeps its kernel square-zero. -/
theorem ker_comp_sq_eq_bot {A A' C C' : Type*} [CommRing A] [CommRing A'] [CommRing C]
    [CommRing C'] (φ : A →+* C) (w : C →+* C') (v : A' →+* A) (hw : Function.Injective w)
    (hv : Function.Injective v) (h : RingHom.ker φ ^ 2 = ⊥) :
    RingHom.ker (w.comp (φ.comp v)) ^ 2 = ⊥ := by
  rw [RingHom.ker_comp_of_injective _ hw, ← RingHom.comap_ker]
  refine eq_bot_iff.2 ((Ideal.le_comap_pow _ 2).trans ?_)
  rw [h, Ideal.comap_bot_of_injective v hv]

/-- Composing a ring map with isomorphisms on both sides keeps its kernel square-zero. -/
private theorem ker_comp_sq_eq_bot_of_isIso {A A' C C' : CommRingCat.{u}} (v : A' ⟶ A)
    (φ : A ⟶ C) (w : C ⟶ C') [IsIso v] [IsIso w] (h : RingHom.ker φ.hom ^ 2 = ⊥) :
    RingHom.ker (v ≫ φ ≫ w).hom ^ 2 = ⊥ :=
  ker_comp_sq_eq_bot _ _ _ (ConcreteCategory.bijective_of_isIso w).1
    (ConcreteCategory.bijective_of_isIso v).1 h

/-- The kernel of the map of global sections is square-zero for a morphism conjugate by
isomorphisms to one with that property. -/
theorem ker_appTop_sq_eq_bot_of_comm_iso {X X' Y Y' : Scheme.{u}} {g : X ⟶ Y} {g' : X' ⟶ Y'}
    (i : X' ≅ X) (j : Y' ≅ Y) (h : g' ≫ j.hom = i.hom ≫ g)
    (hg : RingHom.ker g.appTop.hom ^ 2 = ⊥) : RingHom.ker g'.appTop.hom ^ 2 = ⊥ := by
  obtain rfl := (Iso.eq_comp_inv j).2 h
  have : IsIso i.hom.appTop := inferInstanceAs (IsIso (i.hom.app ⊤))
  have : IsIso j.inv.appTop := inferInstanceAs (IsIso (j.inv.app ⊤))
  rw [Category.assoc, Scheme.Hom.comp_appTop]
  exact ker_comp_sq_eq_bot_of_isIso _ _ _ hg

/-- The kernel of `Γ(Spec φ)` is square-zero when the kernel of `φ` is. -/
theorem ker_appTop_specMap_sq_eq_bot {A A' : CommRingCat.{u}} (φ : A ⟶ A')
    (h : RingHom.ker φ.hom ^ 2 = ⊥) : RingHom.ker (Spec.map φ).appTop.hom ^ 2 = ⊥ := by
  rw [(Iso.eq_comp_inv _).2 (Scheme.ΓSpecIso_naturality φ)]
  exact ker_comp_sq_eq_bot_of_isIso (Scheme.ΓSpecIso A).hom φ (Scheme.ΓSpecIso A').inv h

/-! ### The curves statement -/

section Curves

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

variable {B hZ} in
/-- The isomorphism of objects of the site over the integers given by an isomorphism of their
schemes. -/
def isoOfIntegers {V W : BigFppfOver B integerBase hZ} (g : (𝒯).obj V ≅ (𝒯).obj W) : V ≅ W where
  hom := BigFppfOver.liftOfIntegers g.hom
  inv := BigFppfOver.liftOfIntegers g.inv
  hom_inv_id := (𝒯).map_injective (by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_liftOfIntegers,
      BigFppfOver.toScheme_map_liftOfIntegers, Iso.hom_inv_id, CategoryTheory.Functor.map_id])
  inv_hom_id := (𝒯).map_injective (by
    rw [Functor.map_comp, BigFppfOver.toScheme_map_liftOfIntegers,
      BigFppfOver.toScheme_map_liftOfIntegers, Iso.inv_hom_id, CategoryTheory.Functor.map_id])

/-- `Spec` of the composite ring map `Rₙ → R₀` of a tower is the composite of the transition maps
of the tower of spectra. -/
theorem toScheme_map_towerToLevel_specSiteMap {R : ℕ → Type u} [∀ n, CommRing (R n)]
    (f : ∀ n, R (n + 1) →+* R n) (hR : ∀ n, B.Contains (Spec (.of (R n)))) (n : ℕ) :
    (𝒯).map (towerToLevel (fun n => (specSiteMap (f n) :
      specSite B hZ (R n) (hR n) ⟶ specSite B hZ (R (n + 1)) (hR (n + 1)))) n) =
      Spec.map (CommRingCat.ofHom (toBase f n)) := by
  induction n with
  | zero =>
    rw [towerToLevel, CategoryTheory.Functor.map_id]
    exact (Spec.map_id _).symm
  | succ n ih =>
    rw [towerToLevel, Functor.map_comp, ih]
    exact (Spec.map_comp (CommRingCat.ofHom (f n)) (CommRingCat.ofHom (toBase f n))).symm

/-- **Special towers of objects are effective for the small model of `Curves`.** The local
effectivity data on étale charts come from (C) and (E)
(`AlgebraicGeometry.C1590Private.nonempty_towerChartData_curves`), and they descend by (G) through
the diagonal of `Curves` (Stacks 0D53, from the Hilbert functors of projective spaces). -/
theorem specialTowerObjectsEffective_curvesSmall :
    SpecialTowerObjectsEffective B integerBase hZ (curvesSmall B hZ).val.p := by
  intro R _ f hf hsq hsp toS hA Λ β hβ hβ0 hR y hy t ht
  let := locallySmall_curveFamily B hZ
  have hfib : (curvesProjectionOver B hZ).IsFibered :=
    (curvesFiberedCategory B hZ).isFiberedInGroupoids.isFibered
  have : (curvesFiberedCategory B hZ).val.p.IsFibered := hfib
  let G := curvesProjectionOver B hZ
  let I := ShrinkHoms.inverse (CurveFamily B hZ)
  let y' : ℕ → CurveFamily B hZ := fun n => I.obj (y n)
  let L := fun n => (limitProj f Λ β hβ hβ0 hR n).toHom.right
  let T := fun n => (transition f Λ β hβ hβ0 hR n).toHom.right
  let κ' : ∀ n, (y' n).base ⟶ (limitRing f Λ β hβ hβ0 hR).siteOver :=
    fun n => eqToHom (hy n) ≫ L n
  let ℓ' : ∀ n, (y' n).base ⟶ (y' (n + 1)).base :=
    fun n => eqToHom (hy n) ≫ T n ≫ eqToHom (hy (n + 1)).symm
  -- the tower, compared with the spectra of the rings of the tower
  let ℓs : ∀ n, specSite B hZ (R n) (hR n) ⟶ specSite B hZ (R (n + 1)) (hR (n + 1)) :=
    fun n => specSiteMap (f n)
  let κs : ∀ n, specSite B hZ (R n) (hR n) ⟶ specSite B hZ (limit f) (contains_limit f hR) :=
    fun n => specSiteMap (towerLimitProj f n)
  let eL : ∀ n, (level f Λ β hβ hβ0 hR n).siteOver ≅ specSite B hZ (R n) (hR n) :=
    fun n => isoOfIntegers (Iso.refl _)
  let e : ∀ n, (y' n).base ≅ specSite B hZ (R n) (hR n) := fun n => eqToIso (hy n) ≪≫ eL n
  let eV : (limitRing f Λ β hβ hβ0 hR).siteOver ≅ specSite B hZ (limit f) (contains_limit f hR) :=
    isoOfIntegers (Iso.refl _)
  have hκ : ∀ n, κ' n ≫ eV.hom = (e n).hom ≫ κs n := fun n => by
    show (eqToHom (hy n) ≫ L n) ≫ eV.hom = (eqToHom (hy n) ≫ (eL n).hom) ≫ κs n
    rw [Category.assoc, Category.assoc]
    congr 1
  have hℓ : ∀ n, ℓ' n ≫ (e (n + 1)).hom = (e n).hom ≫ ℓs n := fun n => by
    show (eqToHom (hy n) ≫ T n ≫ eqToHom (hy (n + 1)).symm) ≫ eqToHom (hy (n + 1)) ≫
        (eL (n + 1)).hom = (eqToHom (hy n) ≫ (eL n).hom) ≫ ℓs n
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    congr 1
  have hW : IsEtaleLimitTower (fun n => (y' n).base) κ' ℓ' :=
    (isEtaleLimitTower_specSite B hZ f hf hsq (isEtaleCompatibleTower_of_isSpecialTower f hf hsp)
      hR).ofIso eV e hκ hℓ
  -- the transition morphisms, as morphisms of families of curves
  let t' : ∀ n, y' n ⟶ y' (n + 1) := fun n => I.map (t n)
  have ht' : ∀ n, G.IsHomLift (ℓ' n) (t' n) := fun n => by
    have : G.IsHomLift (T n) (t' n) :=
      (Functor.isHomLift_comp_iff I G (T n) (t n)).1 (ht n)
    exact inferInstanceAs (G.IsHomLift (eqToHom (hy n) ≫ T n ≫ eqToHom (hy (n + 1)).symm) _)
  -- the kernels of the composites `Γ(Wₙ) → Γ(W₀)`
  have htl : ∀ n, towerToLevel ℓ' n ≫ (e n).hom =
      (e 0).hom ≫ towerToLevel ℓs n :=
    TowerCharts.towerToLevel_comm (fun n => (e n).hom) hℓ
  have hspec : ∀ n, (𝒯).map (towerToLevel ℓs n) = Spec.map (CommRingCat.ofHom (toBase f n)) :=
    toScheme_map_towerToLevel_specSiteMap B hZ f hR
  have hsq' : ∀ n, RingHom.ker ((𝒯).map (towerToLevel ℓ' n)).appTop.hom ^ 2 = ⊥ := fun n => by
    refine ker_appTop_sq_eq_bot_of_comm_iso (g := (𝒯).map (towerToLevel ℓs n))
      ((𝒯).mapIso (e 0)) ((𝒯).mapIso (e n)) ?_ ?_
    · simp only [Functor.mapIso_hom, ← Functor.map_comp, htl]
    · rw [hspec]
      exact ker_appTop_specMap_sq_eq_bot _ (hsq n)
  have hnoeth : IsLocallyNoetherian ((𝒯).obj (y' 0).base) := by
    have := hsp.isNoetherianRing
    show IsLocallyNoetherian ((𝒯).obj ((curvesSmall B hZ).val.p.obj (y 0)))
    rw [hy 0]
    exact inferInstanceAs (IsLocallyNoetherian (Spec (.of (R 0))))
  -- descent of the local limit objects
  obtain ⟨D⟩ := nonempty_towerChartData_curves hW t' ht' hsq' hnoeth
  have hI := (Stack.hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B integerBase hZ
    (curvesFiberedCategory B hZ)).mp (hasRepresentableDiagonal_curvesFiberedCategory B hZ)
  obtain ⟨ŷ, hŷ, ψ, hψ, hcomp⟩ := D.towerIsEffective (𝒳 := curvesFiberedCategory B hZ)
    (curvesProjectionOver_isStack B hZ) hI ht'
  let ψs : ∀ n, y n ⟶ ShrinkHoms.toShrinkHoms ŷ := fun n =>
    (ShrinkHoms.functor (CurveFamily B hZ)).map (ψ n)
  have hIψ : ∀ n, I.map (ψs n) = ψ n := fun n =>
    Equiv.symm_apply_apply _ (ψ n)
  refine ⟨ShrinkHoms.toShrinkHoms ŷ, hŷ, ψs, fun n => ?_, fun n => ?_⟩
  · refine (Functor.isHomLift_comp_iff I G (L n) (ψs n)).2 ?_
    rw [hIψ]
    exact (IsHomLift.lift_eqToHom_comp_iff G (L n) (ψ n) (hy n)).1 (hψ n)
  · apply (equivShrink _).symm.injective
    exact ((I.map_comp (t n) (ψs (n + 1))).trans (by rw [hIψ]; exact hcomp n)).trans (hIψ n).symm

/-- **Special towers are effective on lift classes for the small model of `Curves`**: the
input `hspecial` of
`AlgebraicGeometry.C1590Private.isAlgebraicStack_curvesFiberedCategory_of_diagonal`. -/
theorem isSpecialSquareZeroTowerEffectiveOnClasses_curvesSmall :
    IsSpecialSquareZeroTowerEffectiveOnClasses B integerBase hZ (curvesSmall B hZ).val.p
      (curvesSmall B hZ).isFiberedInGroupoids :=
  isSpecialSquareZeroTowerEffectiveOnClasses_of_objects (curvesSmall B hZ).isFiberedInGroupoids
    (specialTowerObjectsEffective_curvesSmall B hZ)

end Curves

end AlgebraicGeometry.C1590Private

end
