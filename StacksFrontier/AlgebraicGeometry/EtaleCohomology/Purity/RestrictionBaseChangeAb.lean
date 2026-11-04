module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AbelianBaseChangeRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveUnitIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleForgetBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.PurityComplexBaseChange

/-!
# The base change maps of `j_*(j⁻¹ H)` in degree zero and in vanishing degrees

Let
```
U₀' --u₀--> U₀
|j'         |j
v           v
U'  --u'--> U
```
be a cartesian square of schemes with `j` (hence `j'`) an open immersion. The underived base change
map `u'⁻¹ j_* F ⟶ j'_* u₀⁻¹ F` of abelian sheaves on the small étale sites
(`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`) becomes invertible after `j'⁻¹`: pasted with
the base change of `j'` along itself it is the base change of `j` along `u₀ ≫ j`, which is the
base change of `j` along itself pasted with that of the identity of `U₀` along `u₀`, and these
three are invertible (open immersions, and the finite identity). Since `j'_*` is fully faithful,
the base change map is therefore invertible as soon as the unit of `j'⁻¹ ⊣ j'_*` is invertible at
its source.

For a sheaf of `Λ`-modules `H` on `U` such that the units `H ⟶ j_* j⁻¹ H` and
`u'⁻¹ H ⟶ j'_* j'⁻¹ u'⁻¹ H` are invertible (`(P0)` of relative purity on `U` and on `U'`), the
source is `u'⁻¹ j_* j⁻¹ H ≅ u'⁻¹ H`, so the degree-zero base change map of the underlying abelian
sheaf of `j⁻¹ H` (`Stacks.EtaleCohomology.higherBaseChangeMapAb` in degree `0`) is invertible.
In a degree `q` where `R^q j_*(j⁻¹ H)` and `R^q j'_*(j'⁻¹ u'⁻¹ H)` vanish (`(P2)` on `U` and on
`U'`) the base change map is invertible because both of its sides vanish.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleAdjunctionAb_counit_of_etale_of_mono`.
* `Stacks.EtaleCohomology.isIso_smallEtalePullbackAb_map_smallEtaleBaseChangeAb_app`.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_app_of_isIso_unit`.
* `Stacks.EtaleCohomology.isIso_smallEtaleAdjunctionAb_unit_app_forget`.
* `Stacks.EtaleCohomology.smallEtalePullbackDirectImageRestrictionIso`.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_zero_restriction`.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_restriction_of_isZero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

/- The base instance
`Stacks.Cohomology.DerivedLowerShriek.preservesZeroMorphisms_abelianLowerShriek` (reachable
through `ProperBaseChange.LowerShriekCompactification`) leaves the searches for
`(smallEtalePullbackAb _).PreservesZeroMorphisms` below stuck at a universe constraint. -/
attribute [-instance] Stacks.Cohomology.DerivedLowerShriek.preservesZeroMorphisms_abelianLowerShriek

universe u

namespace Stacks.EtaleCohomology

/-- The counit of the inverse-image/direct-image adjunction of abelian sheaves along an étale
monomorphism is invertible. -/
theorem isIso_smallEtaleAdjunctionAb_counit_of_etale_of_mono {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] [Mono j] : IsIso (smallEtaleAdjunctionAb j).counit := by
  have := isIso_smallEtaleRestrictionAdjunctionAb_counit j
  have : ∀ P, IsIso ((smallEtaleAdjunctionAb j).counit.app P) := fun P => by
    rw [← Adjunction.leftAdjointUniq_hom_app_counit (smallEtaleAdjunctionAb j)
      ((smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous (E := Ab.{u + 1})
        (smallEtaleTopology U) (smallEtaleTopology X)) P]
    have : IsIso (((smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous
        (E := Ab.{u + 1}) (smallEtaleTopology U) (smallEtaleTopology X)).counit.app P) :=
      NatIso.isIso_app_of_isIso _ _
    exact IsIso.comp_isIso' (Iso.isIso_hom (((smallEtaleAdjunctionAb j).leftAdjointUniq
      ((smallEtaleComposeBaseChangeAdj j).sheafPushforwardContinuous (E := Ab.{u + 1})
        (smallEtaleTopology U) (smallEtaleTopology X))).app _)) this
  exact NatIso.isIso_of_isIso_app _

variable {U U₀ U' U₀' : Scheme.{u}} (j : U₀ ⟶ U) [IsOpenImmersion j]
  (j' : U₀' ⟶ U') [IsOpenImmersion j'] (u' : U' ⟶ U) (u₀ : U₀' ⟶ U₀)

/-- **The inverse image along `j'` of the underived base change map of a cartesian square along
open immersions is invertible.** -/
theorem isIso_smallEtalePullbackAb_map_smallEtaleBaseChangeAb_app (sq : IsPullback u₀ j' j u')
    (F : Sheaf (smallEtaleTopology U₀) Ab.{u + 1}) :
    IsIso ((smallEtalePullbackAb j').map
      ((smallEtaleBaseChangeAb u' j j' u₀ sq.w.symm).app F)) := by
  have hsq₁ : IsPullback (𝟙 U₀) (𝟙 U₀) j j := IsKernelPair.id_of_mono j
  have hsq₂ : IsPullback (𝟙 U₀') u₀ u₀ (𝟙 U₀) := IsPullback.of_horiz_isIso ⟨by simp⟩
  have hsq₃ : IsPullback (𝟙 U₀') (𝟙 U₀') j' j' := IsKernelPair.id_of_mono j'
  have h₁ : IsIso ((smallEtaleBaseChangeAb j j (𝟙 U₀) (𝟙 U₀) hsq₁.w).app F) :=
    (isIso_higherBaseChangeMapAb_zero_app_iff j j (𝟙 U₀) (𝟙 U₀) hsq₁.w F).1
      (isIso_higherBaseChangeMapAb_app_of_isOpenImmersion hsq₁ 0 F)
  have h₂ : IsIso (smallEtaleBaseChangeAb u₀ (𝟙 U₀) (𝟙 U₀') u₀ hsq₂.w) :=
    isIso_smallEtaleBaseChangeAb_of_isFinite u₀ (𝟙 U₀) (𝟙 U₀') u₀ hsq₂
  have h₃ : IsIso ((smallEtaleBaseChangeAb j' j' (𝟙 U₀') (𝟙 U₀') hsq₃.w).app
      ((smallEtalePullbackAb u₀).obj F)) :=
    (isIso_higherBaseChangeMapAb_zero_app_iff j' j' (𝟙 U₀') (𝟙 U₀') hsq₃.w _).1
      (isIso_higherBaseChangeMapAb_app_of_isOpenImmersion hsq₃ 0 _)
  have hO : IsIso ((smallEtaleBaseChangeAb (u₀ ≫ j) j (𝟙 U₀') (u₀ ≫ 𝟙 U₀)
      (smallEtaleRectangle_comm j (𝟙 U₀) (𝟙 U₀') j u₀ (𝟙 U₀) u₀ hsq₁.w hsq₂.w)).app F) := by
    rw [smallEtaleBaseChangeAb_paste_app j (𝟙 U₀) (𝟙 U₀') j u₀ (𝟙 U₀) u₀ hsq₁.w hsq₂.w F]
    infer_instance
  have hR : IsIso ((smallEtaleBaseChangeAb (j' ≫ u') j (𝟙 U₀') (𝟙 U₀' ≫ u₀)
      (smallEtaleRectangle_comm j j' (𝟙 U₀') u' j' u₀ (𝟙 U₀') sq.w.symm hsq₃.w)).app F) :=
    (isIso_higherBaseChangeMapAb_zero_app_iff _ _ _ _ _ F).1
      ((isIso_higherBaseChangeMapAb_app_congr j (𝟙 U₀') sq.w.symm (by simp) _ _ 0 F).2
        ((isIso_higherBaseChangeMapAb_zero_app_iff _ _ _ _ _ F).2 hO))
  rw [smallEtaleBaseChangeAb_paste_app j j' (𝟙 U₀') u' j' u₀ (𝟙 U₀') sq.w.symm hsq₃.w F] at hR
  have h₄ := IsIso.of_isIso_comp_left
    ((smallEtalePullbackAbCompIso j' u').inv.app ((smallEtalePushforwardAb j).obj F))
    ((smallEtalePullbackAb j').map ((smallEtaleBaseChangeAb u' j j' u₀ sq.w.symm).app F) ≫
      (smallEtaleBaseChangeAb j' j' (𝟙 U₀') (𝟙 U₀') hsq₃.w).app ((smallEtalePullbackAb u₀).obj F) ≫
        (smallEtalePushforwardAb (𝟙 U₀')).map ((smallEtalePullbackAbCompIso (𝟙 U₀') u₀).hom.app F))
  exact IsIso.of_isIso_comp_right _
    ((smallEtaleBaseChangeAb j' j' (𝟙 U₀') (𝟙 U₀') hsq₃.w).app ((smallEtalePullbackAb u₀).obj F) ≫
      (smallEtalePushforwardAb (𝟙 U₀')).map ((smallEtalePullbackAbCompIso (𝟙 U₀') u₀).hom.app F))

/-- **The underived base change map along open immersions, at a sheaf whose direct image is local
for `j'`.** For a cartesian square along the open immersion `j`, the base change map
`u'⁻¹ j_* F ⟶ j'_* u₀⁻¹ F` is invertible as soon as the unit of `j'⁻¹ ⊣ j'_*` is invertible at
`u'⁻¹ j_* F`. -/
theorem isIso_smallEtaleBaseChangeAb_app_of_isIso_unit (sq : IsPullback u₀ j' j u')
    (F : Sheaf (smallEtaleTopology U₀) Ab.{u + 1})
    (hA : IsIso ((smallEtaleAdjunctionAb j').unit.app
      ((smallEtalePullbackAb u').obj ((smallEtalePushforwardAb j).obj F)))) :
    IsIso ((smallEtaleBaseChangeAb u' j j' u₀ sq.w.symm).app F) :=
  have := isIso_smallEtaleAdjunctionAb_counit_of_etale_of_mono j'
  isIso_of_isIso_unit_app_of_isIso_leftAdjoint_map (smallEtaleAdjunctionAb j') _ hA
    (isIso_smallEtalePullbackAb_map_smallEtaleBaseChangeAb_app j j' u' u₀ sq F)

section Modules

variable (Λ : Type) [Ring Λ]

/-- The unit of `j'⁻¹ ⊣ j'_*` on abelian sheaves is invertible at the underlying abelian sheaf of
`M` when the unit of restriction along `j'` of sheaves of modules is invertible at `M`. -/
theorem isIso_smallEtaleAdjunctionAb_unit_app_forget (M : EtaleModules.{u, 0} Λ U')
    (h0 : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j').unit.app M)) :
    IsIso ((smallEtaleAdjunctionAb j').unit.app ((etaleModuleForgetAb.{u, 0} Λ U').obj M)) := by
  set Ma := (etaleModuleForgetAb.{u, 0} Λ U').obj M
  have h1 : IsIso ((Purity.etaleRestrictionAbAdj j').unit.app Ma) := by
    rw [← Purity.etaleModuleForgetUniv_map_restrictionDirectImageUnit]
    exact Functor.map_isIso _ _
  have hκ : (smallEtaleAdjunctionAb j').unit.app Ma ≫ (smallEtalePushforwardAb j').map
      ((smallEtalePullbackAbIsoEtaleRestriction j').hom.app Ma) =
      (Purity.etaleRestrictionAbAdj j').unit.app Ma :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ Ma
  rw [← hκ] at h1
  have h2 : IsIso ((smallEtalePushforwardAb j').map
      ((smallEtalePullbackAbIsoEtaleRestriction j').hom.app Ma)) :=
    Iso.isIso_hom ((smallEtalePushforwardAb j').mapIso
      ((smallEtalePullbackAbIsoEtaleRestriction j').app Ma))
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ h2 h1

/-- `u'⁻¹ j_*(j⁻¹ H) ≅ U(u'⁻¹ H)` when the unit `H ⟶ j_* j⁻¹ H` is invertible. -/
def smallEtalePullbackDirectImageRestrictionIso (H : EtaleModules.{u, 0} Λ U)
    (h0 : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app H)) :
    (smallEtalePullbackAb u').obj ((smallEtalePushforwardAb j).obj
        ((etaleModuleForgetAb.{u, 0} Λ U₀).obj ((etaleModuleRestriction.{u, 0} Λ j).obj H))) ≅
      (etaleModuleForgetAb.{u, 0} Λ U').obj ((etaleModuleInverseImage.{u, 0} Λ u').obj H) :=
  (smallEtalePullbackAb u').mapIso ((etaleModuleForgetAb.{u, 0} Λ U).mapIso
      (asIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app H)).symm) ≪≫
    (smallEtalePullbackAbIsoInverseImage u').app _ ≪≫
    (etaleModuleForgetInverseImageIso.{u, 0} Λ u').app H

/-- **The degree-zero base change map of `j_*(j⁻¹ H)`, from `(P0)` on `U` and on `U'`.** For a
cartesian square along the open immersion `j`, if the units `H ⟶ j_* j⁻¹ H` and
`u'⁻¹ H ⟶ j'_* j'⁻¹ u'⁻¹ H` are invertible, so is the degree-zero base change map
`u'⁻¹ j_*(j⁻¹ H) ⟶ j'_* u₀⁻¹(j⁻¹ H)` of the underlying abelian sheaves. -/
theorem isIso_higherBaseChangeMapAb_zero_restriction (sq : IsPullback u₀ j' j u')
    (H : EtaleModules.{u, 0} Λ U)
    (h0 : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).unit.app H))
    (h0' : IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j').unit.app
      ((etaleModuleInverseImage.{u, 0} Λ u').obj H))) :
    IsIso ((higherBaseChangeMapAb u' j j' u₀ sq.w.symm 0).app
      ((etaleModuleForgetAb.{u, 0} Λ U₀).obj ((etaleModuleRestriction.{u, 0} Λ j).obj H))) := by
  rw [isIso_higherBaseChangeMapAb_zero_app_iff]
  refine isIso_smallEtaleBaseChangeAb_app_of_isIso_unit j j' u' u₀ sq _ ?_
  exact (NatTrans.isIso_app_iff_of_iso (smallEtaleAdjunctionAb j').unit
    (smallEtalePullbackDirectImageRestrictionIso j u' Λ H h0)).2
    (isIso_smallEtaleAdjunctionAb_unit_app_forget j' Λ _ h0')

/-- **The higher base change maps of `j_*(j⁻¹ H)` in degrees where both sides vanish.** If
`R^q j_*(j⁻¹ H) = 0` and `R^q j'_*(j'⁻¹ u'⁻¹ H) = 0` (`(P2)` on `U` and on `U'`), the base change
map `u'⁻¹ R^q j_*(j⁻¹ H) ⟶ R^q j'_* u₀⁻¹(j⁻¹ H)` of the underlying abelian sheaves is
invertible. -/
theorem isIso_higherBaseChangeMapAb_restriction_of_isZero (sq : IsPullback u₀ j' j u')
    (H : EtaleModules.{u, 0} Λ U) (q : ℕ)
    (h2 : IsZero (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ j).obj H)))
    (h2' : IsZero (((etaleModuleDirectImage.{u, 0} Λ j').rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} Λ j').obj ((etaleModuleInverseImage.{u, 0} Λ u').obj H)))) :
    IsIso ((higherBaseChangeMapAb u' j j' u₀ sq.w.symm q).app
      ((etaleModuleForgetAb.{u, 0} Λ U₀).obj ((etaleModuleRestriction.{u, 0} Λ j).obj H))) := by
  have hs : IsZero ((smallEtalePullbackAb u').obj (((smallEtalePushforwardAb j).rightDerived q).obj
      ((etaleModuleForgetAb.{u, 0} Λ U₀).obj ((etaleModuleRestriction.{u, 0} Λ j).obj H)))) :=
    Functor.map_isZero _ ((Functor.map_isZero (etaleModuleForgetAb.{u, 0} Λ U) h2).of_iso
      (etaleModuleForgetRightDerivedDirectImageIso Λ j _ q).symm)
  have ht : IsZero (((smallEtalePushforwardAb j').rightDerived q).obj
      ((smallEtalePullbackAb u₀).obj
        ((etaleModuleForgetAb.{u, 0} Λ U₀).obj ((etaleModuleRestriction.{u, 0} Λ j).obj H)))) :=
    ((Functor.map_isZero (etaleModuleForgetAb.{u, 0} Λ U') h2').of_iso
      (etaleModuleForgetRightDerivedDirectImageIso Λ j' _ q).symm).of_iso
      (((smallEtalePushforwardAb j').rightDerived q).mapIso
        ((smallEtalePullbackAbIsoInverseImage u₀).app _ ≪≫
          (etaleModuleForgetInverseImageIso.{u, 0} Λ u₀).app _ ≪≫
          (etaleModuleForgetAb.{u, 0} Λ U₀').mapIso
            (etaleModuleInverseImageRestrictionSquareIso Λ j j' u' u₀ sq.w.symm H)))
  exact ⟨⟨ht.to_ _, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩

end Modules

end Stacks.EtaleCohomology

end
