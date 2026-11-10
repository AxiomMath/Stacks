module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StrictHenselizationDependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections

/-!
# The stalk at a geometric point is the sections over the strict henselization

Let `x` be a geometric point of a scheme `X`, let `p : Spec 𝒪^{sh}_{X,x} ⟶ X` be the structure
morphism of the strict henselization at `x`, and let `x̃` be the canonical lift of `x` to
`Spec 𝒪^{sh}_{X,x}`. Global sections over `Spec 𝒪^{sh}_{X,x}` are the stalk at `x̃`, and for an
abelian sheaf `F` on the small étale site of `X` the canonical map

`F_x ⟶ Γ(Spec 𝒪^{sh}_{X,x}, p⁻¹F)`

of `AlgebraicGeometry.etaleStalkToSectionsAb` (at the identity of the strict henselization),
followed by the germ at `x̃`, is the identification `F_x = F_{x̃ ≫ p} ⟶ (p⁻¹F)_{x̃}`. Its extension
`K_x ⟶ RΓ(Spec 𝒪^{sh}_{X,x}, K)` to the unbounded derived category,
`AlgebraicGeometry.vanishingCyclesMap`, is an isomorphism.

## Main definitions

* `AlgebraicGeometry.strictHenselizationSectionsToStalkAb` — the germ at `x̃` of a global section
  over the strict henselization.

## Main results

* `AlgebraicGeometry.isIso_strictHenselizationSectionsToStalkAb` — over the strict
  henselization, the germ at `x̃` of a global section is an isomorphism `Γ(-) ≅ (-)_{x̃}`.
* `AlgebraicGeometry.etaleStalkToSectionsAb_id_comp_strictHenselizationSectionsToStalkAb` —
  `F_x ⟶ Γ(Spec 𝒪^{sh}_{X,x}, p⁻¹F)` followed by the germ at `x̃` is
  `F_x = F_{x̃ ≫ p} ⟶ (p⁻¹F)_{x̃}`.
* `AlgebraicGeometry.isIso_smallEtaleDerivedGlobalSectionsUnit_strictHenselization` — the unit
  of unbounded derived global sections over the strict henselization is an isomorphism.
* `AlgebraicGeometry.isIso_vanishingCyclesMap_id` — `K_x ⟶ RΓ(Spec 𝒪^{sh}_{X,x}, K)` is an
  isomorphism for every object `K` of the unbounded derived category.

## References

* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 0GJ4](https://stacks.math.columbia.edu/tag/0GJ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-- A germ at a geometric point, transported along an equality of geometric points, is the germ
at the other point at the lift with the same underlying morphism. -/
private theorem toPresheafFiber_comp_eqToHom {X : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] {y y' : Spec (.of Ω) ⟶ X} (e : y = y')
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale y).fiber.obj W) (hv : v.left ≫ W.hom = y') :
    (Scheme.pointSmallEtale y).toPresheafFiber W v F.obj ≫
        eqToHom (congrArg (fun z => (smallEtaleStalkAb z).obj F) e) =
      (Scheme.pointSmallEtale y').toPresheafFiber W (Over.homMk v.left hv) F.obj := by
  subst e
  change _ ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact congrArg (fun w => (Scheme.pointSmallEtale y).toPresheafFiber W w F.obj)
    (Over.OverMorphism.ext rfl)

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- The canonical lift of a geometric point to the strict henselization there lies over the
closed point, read at the point `default` of the spectrum of its residue field. -/
theorem geometricPointToStrictHenselization_default :
    geometricPointToStrictHenselization B X hX x (default : x.source) =
      IsLocalRing.closedPoint ↥(etaleLocalRing B X hX x) := by
  rw [Subsingleton.elim (default : x.source) (IsLocalRing.closedPoint x.residueField)]
  exact geometricPointToStrictHenselization_closedPoint B X hX x

/-- The germ at the canonical geometric point `x̃` of the strict henselization at `x` of a global
section of an abelian sheaf on the small étale site of the strict henselization. -/
def strictHenselizationSectionsToStalkAb :
    Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1} ⟶
      smallEtaleStalkAb (geometricPointToStrictHenselization B X hX x) :=
  (Sheaf.ΓNatIsoSheafSections _ _ (isTerminalEtaleMkId _)).hom ≫
    Functor.whiskerLeft (sheafToPresheaf _ _)
      (GrothendieckTopology.Point.toPresheafFiberNatTrans
        (Scheme.pointSmallEtale (geometricPointToStrictHenselization B X hX x))
        _ (pointSmallEtaleClosedPointElement (geometricPointToStrictHenselization B X hX x)))

/-- **Global sections over the strict henselization are the stalk at its canonical geometric
point.** -/
theorem isIso_strictHenselizationSectionsToStalkAb :
    IsIso (strictHenselizationSectionsToStalkAb B X hX x) := by
  have := etaleLocalRing_strictHenselian B X hX x
  suffices ∀ G, IsIso ((strictHenselizationSectionsToStalkAb B X hX x).app G) from
    NatIso.isIso_of_isIso_app _
  intro G
  have hι : IsIso (GrothendieckTopology.Point.toPresheafFiber
      (Scheme.pointSmallEtale (geometricPointToStrictHenselization B X hX x))
      _ (pointSmallEtaleClosedPointElement (geometricPointToStrictHenselization B X hX x)) G.obj) :=
    ((Scheme.pointSmallEtale _).isColimitPresheafFiberCocone G.obj).isIso_ι_app_of_isTerminal _
      (isInitialPointSmallEtaleClosedPointElement _
        (geometricPointToStrictHenselization_default B X hX x)).op
  exact IsIso.comp_isIso' inferInstance hι

/-- The canonical lift of `x` to the strict henselization, followed by the structure morphism
read as a composite with the identity, is `x`. -/
theorem geometricPointToStrictHenselization_id_comp :
    x.hom = geometricPointToStrictHenselization B X hX x ≫
      𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x := by
  rw [Category.id_comp, geometricPointToStrictHenselization_comp]

/-- A composite through a pair of mutually inverse maps contracted, in an abstract category. -/
private theorem comp_cancel_middle {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ : C} (a : A₀ ⟶ A₁)
    (m : A₁ ⟶ A₂) (i : A₂ ⟶ A₃) (h : A₃ ⟶ A₂) (k : A₂ ⟶ A₄) (hih : i ≫ h = 𝟙 A₂) :
    ((a ≫ m) ≫ i) ≫ h ≫ k = a ≫ m ≫ k := by
  simp only [Category.assoc, reassoc_of% hih]

/-- On the germ at `x` of a section over an étale neighbourhood `(W, v)`, restriction to the
strict henselization followed by the germ at its canonical geometric point `x̃` is the unit of the
inverse-image adjunction followed by the germ at the lift of `x̃` to `W ×_X Spec 𝒪^{sh}_{X,x}`
corresponding to `v`. -/
theorem etaleStalkSectionsStage_id_comp_strictHenselizationSectionsToStalkAb
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale x.hom).fiber.obj W)
    (hv : v.left ≫ W.hom = geometricPointToStrictHenselization B X hX x ≫
      𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x) :
    etaleStalkSectionsStage B X hX x (𝟙 (strictHenselization B X hX x)) F W v ≫
        (strictHenselizationSectionsToStalkAb B X hX x).app
          ((smallEtalePullbackAb
            (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x)).obj F) =
      ((smallEtaleAdjunctionAb
          (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x)).unit.app
            F).hom.app (op W) ≫
        (Scheme.pointSmallEtale (geometricPointToStrictHenselization B X hX x)).toPresheafFiber
          ((Stacks.EtaleCohomology.smallEtaleBaseChange
            (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x)).obj W)
          ((pointSmallEtaleComapFiberIso
              (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x)
              (geometricPointToStrictHenselization B X hX x)).hom.app W (Over.homMk v.left hv))
          ((smallEtalePullbackAb
            (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x)).obj
              F).obj := by
  have hr : (𝟙 (strictHenselization B X hX x) ≫
      strictHenselizationNeighborhoodLift B X hX x W v) ≫ W.hom =
        𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x := by
    rw [Category.assoc, strictHenselizationNeighborhoodLift_comp]
  have hel : (Scheme.pointSmallEtale (geometricPointToStrictHenselization B X hX x)).fiber.map
      (smallEtaleBaseChangeLift
        (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x) W
        (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationNeighborhoodLift B X hX x W v)
        hr)
      (pointSmallEtaleClosedPointElement (geometricPointToStrictHenselization B X hX x)) =
      (pointSmallEtaleComapFiberIso
          (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x)
          (geometricPointToStrictHenselization B X hX x)).hom.app W (Over.homMk v.left hv) := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · refine Eq.trans ?_ (pointSmallEtaleComapFiberIso_hom_app_left_fst _ _ W
        (Over.homMk v.left hv)).symm
      change (geometricPointToStrictHenselization B X hX x ≫ pullback.lift
          (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationNeighborhoodLift B X hX x W v)
          (𝟙 _) (hr.trans (Category.id_comp _).symm)) ≫ pullback.fst W.hom _ = v.left
      rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      exact geometricPointToStrictHenselization_comp_neighborhoodLift B X hX x W v
    · refine Eq.trans ?_ (Over.w ((pointSmallEtaleComapFiberIso
          (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x)
          (geometricPointToStrictHenselization B X hX x)).hom.app W (Over.homMk v.left hv))).symm
      change (geometricPointToStrictHenselization B X hX x ≫ pullback.lift
          (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationNeighborhoodLift B X hX x W v)
          (𝟙 _) (hr.trans (Category.id_comp _).symm)) ≫ pullback.snd W.hom _ =
        geometricPointToStrictHenselization B X hX x
      rw [Category.assoc, pullback.lift_snd, Category.comp_id]
  let g := 𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x
  let G := (smallEtalePullbackAb g).obj F
  let γ := Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (strictHenselization B X hX x))
    Ab.{u + 1} (isTerminalEtaleMkId (strictHenselization B X hX x))
  let L := smallEtaleBaseChangeLift g W
    (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationNeighborhoodLift B X hX x W v) hr
  let Φ := Scheme.pointSmallEtale (geometricPointToStrictHenselization B X hX x)
  let e := pointSmallEtaleClosedPointElement (geometricPointToStrictHenselization B X hX x)
  have h1 : ((((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫ G.obj.map L.op) ≫
        γ.inv.app G) ≫ γ.hom.app G ≫ Φ.toPresheafFiber _ e G.obj =
      ((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫ G.obj.map L.op ≫
        Φ.toPresheafFiber _ e G.obj :=
    comp_cancel_middle _ _ _ _ _ (γ.inv_hom_id_app G)
  have h2 : G.obj.map L.op ≫ Φ.toPresheafFiber _ e G.obj =
      Φ.toPresheafFiber _ ((pointSmallEtaleComapFiberIso g
        (geometricPointToStrictHenselization B X hX x)).hom.app W (Over.homMk v.left hv)) G.obj :=
    (GrothendieckTopology.Point.toPresheafFiber_w Φ L e G.obj).trans
      (congrArg (fun a => Φ.toPresheafFiber _ a G.obj) hel)
  exact h1.trans (congrArg (((smallEtaleAdjunctionAb g).unit.app F).hom.app (op W) ≫ ·) h2)

/-- **On germs, `F_x ⟶ Γ(Spec 𝒪^{sh}_{X,x}, p⁻¹F)` is the comparison of Stacks 03Q1.** The map
from the stalk at `x` to the sections over the strict henselization, followed by the germ at the
canonical geometric point `x̃` of the strict henselization, is the identification
`F_x = F_{x̃ ≫ p} ⟶ (p⁻¹F)_{x̃}` of the stalk of an inverse image. -/
theorem etaleStalkToSectionsAb_id_comp_strictHenselizationSectionsToStalkAb :
    etaleStalkToSectionsAb B X hX x (𝟙 (strictHenselization B X hX x)) ≫
        Functor.whiskerLeft
          (smallEtalePullbackAb
            (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x))
          (strictHenselizationSectionsToStalkAb B X hX x) =
      eqToHom (congrArg smallEtaleStalkAb (geometricPointToStrictHenselization_id_comp B X hX x)) ≫
        (smallEtaleStalkPullbackAbIso
          (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x)
          (geometricPointToStrictHenselization B X hX x)).inv := by
  ext F : 2
  refine (Scheme.pointSmallEtale x.hom).presheafFiber_hom_ext fun W v => ?_
  have hv : v.left ≫ W.hom = geometricPointToStrictHenselization B X hX x ≫
      𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x :=
    (Over.w v).trans (geometricPointToStrictHenselization_id_comp B X hX x)
  exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) (etaleStalkToSectionsAb_toPresheafFiber B X hX x _ F W v)).trans
        (etaleStalkSectionsStage_id_comp_strictHenselizationSectionsToStalkAb B X hX x F W v
          hv))).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) ((congrArg (_ ≫ ·) (eqToHom_app _ F)).trans
          (toPresheafFiber_comp_eqToHom (geometricPointToStrictHenselization_id_comp B X hX x)
            F W v hv))).trans
        (toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv _ _ F W
          (Over.homMk v.left hv)))).symm

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- An isomorphism of additive functors induces an isomorphism on homotopy categories of
complexes. -/
private theorem isIso_mapHomotopyCategory_of_isIso {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    [IsIso α] : IsIso (NatTrans.mapHomotopyCategory α (.up ℤ)) :=
  ⟨NatTrans.mapHomotopyCategory (inv α) (.up ℤ), by
    rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id, NatTrans.mapHomotopyCategory_id],
    by rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id, NatTrans.mapHomotopyCategory_id]⟩

/-- **Unbounded derived global sections over the strict henselization are computed degreewise**:
the unit of their total right derived functor is an isomorphism. -/
theorem isIso_smallEtaleDerivedGlobalSectionsUnit_strictHenselization
    [((Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}).mapHomotopyCategory
        (.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}) (.up ℤ))] :
    IsIso (smallEtaleDerivedGlobalSectionsUnit (strictHenselization B X hX x)) := by
  have := isIso_strictHenselizationSectionsToStalkAb B X hX x
  let γ := strictHenselizationSectionsToStalkAb B X hX x
  have := isIso_mapHomotopyCategory_of_isIso γ
  have e : (Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ≅
      DerivedCategory.Qh ⋙
        (smallEtaleStalkAb (geometricPointToStrictHenselization B X hX x)).mapDerivedCategory :=
    Functor.isoWhiskerRight (asIso (NatTrans.mapHomotopyCategory γ (.up ℤ)))
        DerivedCategory.Qh ≪≫
      Iso.symm (Functor.mapDerivedCategoryFactorsh
        (smallEtaleStalkAb (geometricPointToStrictHenselization B X hX x)))
  exact Functor.isIso_of_isRightDerivedFunctor_of_inverts (L := DerivedCategory.Qh)
    (smallEtaleDerivedGlobalSections (strictHenselization B X hX x))
    (smallEtaleDerivedGlobalSectionsUnit (strictHenselization B X hX x))
    ((MorphismProperty.IsInvertedBy.iff_of_iso _ e).2
      (MorphismProperty.IsInvertedBy.of_comp _ _ (Localization.inverts DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (.up ℤ))) _))

/-- **The derived stalk at a geometric point is the derived sections over the strict
henselization.** For every object `K` of the unbounded derived category of abelian sheaves on the
small étale site of `X`, the canonical map `K_x ⟶ RΓ(Spec 𝒪^{sh}_{X,x}, p⁻¹K)` is an
isomorphism. -/
theorem isIso_vanishingCyclesMap_id
    [((Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}).mapHomotopyCategory
        (.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}) (.up ℤ))] :
    IsIso (vanishingCyclesMap B X hX x (𝟙 (strictHenselization B X hX x))) := by
  have := isIso_etaleStalkToSectionsAb_id B X hX x
  have := isIso_smallEtaleDerivedGlobalSectionsUnit_strictHenselization B X hX x
  have := isIso_mapHomotopyCategory_of_isIso
    (etaleStalkToSectionsAb B X hX x (𝟙 (strictHenselization B X hX x)))
  suffices h : ∀ J, IsIso ((vanishingCyclesMap B X hX x
      (𝟙 (strictHenselization B X hX x))).app (DerivedCategory.Qh.obj J)) by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun K => ?_
    rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Qh.objObjPreimageIso K)]
    exact h _
  intro J
  have : IsIso ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
      (smallEtaleStalkAb x.hom)
      (smallEtalePullbackAb
        (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x))
      (Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1})
      (etaleStalkToSectionsAb B X hX x (𝟙 (strictHenselization B X hX x)))).app J) := by
    rw [Stacks.DerivedFunctor.mapHomotopyCategoryOfComp, NatTrans.comp_app]
    infer_instance
  have : IsIso ((smallEtaleStalkAb x.hom).mapDerivedCategoryFactorsh.inv.app J ≫
      (vanishingCyclesMap B X hX x
        (𝟙 (strictHenselization B X hX x))).app (DerivedCategory.Qh.obj J)) := by
    rw [vanishingCyclesMap_fac_app B X hX x (𝟙 (strictHenselization B X hX x)) J]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((smallEtaleStalkAb x.hom).mapDerivedCategoryFactorsh.inv.app J) _

end Derived

end AlgebraicGeometry
