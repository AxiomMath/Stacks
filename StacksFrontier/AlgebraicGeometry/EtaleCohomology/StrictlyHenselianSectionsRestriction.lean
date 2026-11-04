module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.GeometricFibreSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsAlongIsomorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitComposition

/-!
# Restriction to the closed point of a strictly henselian local scheme

Let `R` be a strictly henselian local ring and let `x : Spec Ω ⟶ Spec R` be a geometric point
over the closed point, `Ω` algebraically closed. Restriction of sections along `x`,

`Γ(Spec R, F) ⟶ Γ(Spec Ω, x⁻¹F)`,

is an isomorphism for every abelian sheaf `F` on the small étale site of `Spec R`, and the
canonical map `RΓ(Spec R, N) ⟶ RΓ(Spec Ω, x⁻¹N)` on unbounded derived categories is an
isomorphism for every object `N`.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleGlobalSectionsRestrictionAb_of_strictlyHenselian` —
  restriction of sections to a geometric point over the closed point of a strictly henselian
  local scheme is an isomorphism.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction_of_strictlyHenselian`
  — so is the derived restriction map, on the whole unbounded derived category.

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R))
  (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint R)

include hx in
/-- **Restriction of sections to a geometric point over the closed point of a strictly henselian
local scheme is an isomorphism.** For `R` strictly henselian local, `x : Spec Ω ⟶ Spec R` over
the closed point and `F` an abelian sheaf on the small étale site of `Spec R`, the restriction
`Γ(Spec R, F) ⟶ Γ(Spec Ω, x⁻¹F)` is an isomorphism. -/
theorem isIso_smallEtaleGlobalSectionsRestrictionAb_of_strictlyHenselian
    (F : Sheaf (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}) :
    IsIso ((smallEtaleGlobalSectionsRestrictionAb x).app F) := by
  let P := Spec (.of Ω)
  let x' : P ⟶ Spec (.of R) := 𝟙 P ≫ x
  have hx' : x' (default : P) = IsLocalRing.closedPoint R := by
    simpa only [x', Category.id_comp] using hx
  let ΦT := Scheme.pointSmallEtale x'
  let ΦP := Scheme.pointSmallEtale (𝟙 P)
  let G := (smallEtalePullbackAb x).obj F
  let hTt : IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of R)))) := isTerminalEtaleMkId _
  let hPt : IsTerminal (Scheme.Etale.mk (𝟙 P)) := isTerminalEtaleMkId P
  let vT : ΦT.fiber.obj (Scheme.Etale.mk (𝟙 (Spec (.of R)))) :=
    pointSmallEtaleClosedPointElement x'
  let vP : ΦP.fiber.obj (Scheme.Etale.mk (𝟙 P)) := pointSmallEtaleIdElement Ω
  let ℓ : Scheme.Etale.mk (𝟙 P) ⟶
      (smallEtaleBaseChange x).obj (Scheme.Etale.mk (𝟙 (Spec (.of R)))) :=
    smallEtaleBaseChangeLift x (Scheme.Etale.mk (𝟙 (Spec (.of R)))) x (Category.comp_id x)
  have hgT : IsIso (ΦT.toPresheafFiber _ vT F.obj) :=
    (ΦT.isColimitPresheafFiberCocone F.obj).isIso_ι_app_of_isTerminal
      (op ⟨_, vT⟩) (isInitialPointSmallEtaleClosedPointElement x' hx').op
  have hgP : IsIso (ΦP.toPresheafFiber _ vP G.obj) :=
    (ΦP.isColimitPresheafFiberCocone G.obj).isIso_ι_app_of_isTerminal
      (op ⟨_, vP⟩) (isInitialPointSmallEtaleIdElement Ω).op
  have hsub : Subsingleton (ΦP.fiber.obj
      ((smallEtaleBaseChange x).obj (Scheme.Etale.mk (𝟙 (Spec (.of R)))))) :=
    ΦP.subsingleton_fiber_obj (𝟙 _) (isTerminalSmallEtaleBaseChangeObj x hTt)
  have hv : ΦP.fiber.map ℓ vP = (pointSmallEtaleComapFiberIso x (𝟙 P)).hom.app _ vT :=
    Subsingleton.elim _ _
  have hgerm := toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv x (𝟙 P) F
    (Scheme.Etale.mk (𝟙 (Spec (.of R)))) vT
  let B := ((smallEtaleAdjunctionAb x).unit.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 (Spec (.of R)))))
  have hw := ΦP.toPresheafFiber_w ℓ vP G.obj
  have key : (B ≫ G.obj.map ℓ.op) ≫ ΦP.toPresheafFiber _ vP G.obj =
      ΦT.toPresheafFiber _ vT F.obj ≫ (smallEtaleStalkPullbackAbIso x (𝟙 P)).inv.app F :=
    (Category.assoc B _ _).trans ((congrArg (B ≫ ·) (hw.trans (congrArg
      (fun v => ΦP.toPresheafFiber _ v G.obj) hv))).trans hgerm.symm)
  have hBC : IsIso (B ≫ G.obj.map ℓ.op) := by
    rw [← isIso_comp_right_iff _ (ΦP.toPresheafFiber _ vP G.obj), key]
    exact IsIso.comp_isIso' hgT
      (inferInstanceAs (IsIso (((smallEtaleStalkPullbackAbIso x (𝟙 P)).app F).inv)))
  show IsIso
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology (Spec (.of R))) Ab.{u + 1} hTt).hom.app F ≫
      (B ≫ G.obj.map ℓ.op) ≫
        (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology P) Ab.{u + 1} hPt).inv.app G)
  infer_instance

include hx in
/-- **Restriction of derived sections to a geometric point over the closed point of a strictly
henselian local scheme is an isomorphism.** For `R` strictly henselian local, `x : Spec Ω ⟶ Spec R`
over the closed point and every object `N` of the unbounded derived category of abelian sheaves
on the small étale site of `Spec R`, the canonical map `RΓ(Spec R, N) ⟶ RΓ(Spec Ω, x⁻¹N)` is an
isomorphism. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_of_strictlyHenselian
    (N : smallEtaleDerivedCategory (Spec (.of R))) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction x).app N) := by
  have : ∀ F, IsIso ((smallEtaleGlobalSectionsRestrictionAb x).app F) :=
    isIso_smallEtaleGlobalSectionsRestrictionAb_of_strictlyHenselian x hx
  have : IsIso (smallEtaleGlobalSectionsRestrictionAb x) := NatIso.isIso_of_isIso_app _
  have : (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}).IsEquivalence :=
    isEquivalence_globalSections_of_isSepClosed Ω Ab.{u + 1}
  have : PreservesFiniteColimits (Sheaf.Γ (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}) :=
    preservesFiniteColimits_of_natIso (asIso (smallEtaleGlobalSectionsRestrictionAb x)).symm
  have := Localization.essSurj DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}) (.up ℤ))
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Qh.objObjPreimageIso N)]
  obtain ⟨M⟩ := DerivedCategory.Qh.objPreimage N
  have hfac := smallEtaleDerivedGlobalSectionsRestriction_fac_app x
    ((HomotopyCategory.quotient _ (.up ℤ)).obj M)
  have hT := Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_of_exact
    (Sheaf.Γ (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}) M
  have hP := Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_of_exact
    (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1})
    (((smallEtalePullbackAb x).mapHomologicalComplex (.up ℤ)).obj M)
  have hc : IsIso ((smallEtaleDerivedGlobalSectionsUnit (Spec (.of R))).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj M) ≫
      (smallEtaleDerivedGlobalSectionsRestriction x).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj M))) := by
    rw [hfac]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hP inferInstance)
  have hT' : IsIso ((smallEtaleDerivedGlobalSectionsUnit (Spec (.of R))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj M)) := hT
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hT' hc

end Stacks.EtaleCohomology

end
