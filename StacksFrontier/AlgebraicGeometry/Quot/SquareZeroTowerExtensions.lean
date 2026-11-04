module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedCoherator
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionModulePullback

/-!
# The extensions of the structure sheaf of `X₀` in a square-zero tower

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerSpace` — a system `Xₙ ⟶ Yₙ` of
finitely presented, flat and proper algebraic spaces over the spectra of a tower of rings `(Rₙ)`
with surjective, square-zero transition maps — the body of the proof of
[Stacks Project, Tag 0D3X] uses that "the structure sheaf of `Xₙ` is an extension
`0 → 𝒪_{X₁} ⊗_{R₁} Iₙ → 𝒪_{Xₙ} → 𝒪_{X₁} → 0` over `0 → Iₙ → Rₙ → R₁`" (06BH). This file
produces that extension on the small étale site of `X₀`: the extension of the first order
thickening `g⁻¹(Y₀) ⊆ Xₙ` (`AlgebraicGeometry.Space.firstOrderAlgebraExtension`) restricted to
`X₀` along the identification `X₀ ≅ g⁻¹(Y₀)`, with its ideal identified with `𝒪_{X₀} ⊗_{R₀} Iₙ`.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerExtension`: the extension of `(aₙ ≫ h)⁻¹𝒪`-algebras of
  `𝒪_{X₀}` by the restricted conormal module, for any `h : Xₙ ⟶ Y`.
* `AlgebraicGeometry.ProperFlatFibre.towerExtensionIdealIso`: its ideal is `𝒪_{X₀} ⊗_{R₀} Iₙ`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)

/-- The conormal module of `g⁻¹(Y₀) ⊆ Xₙ`, restricted to `X₀` along `X₀ ≅ g⁻¹(Y₀)`. -/
abbrev towerExtensionIdeal (n : ℕ) :
    SheafOfModules.{u} ((sheafCompose (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (Space.smallEtaleRingedTopos B S hS (towerSpace ξ 0)).O) :=
  (Space.etaleRestrictionModule B S hS (towerFibreIso ξ hsurj hsq e he n).hom
    (Space.isEtale_hom_of_iso B S hS _)).obj
    (Space.conormalModule B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))

/-- **The extension `0 → 𝒪_{X₀} ⊗ Iₙ → 𝒪_{Xₙ} → 𝒪_{X₀} → 0` on `X₀`.** For a morphism
`h : Xₙ ⟶ Y`, the structure sheaf of `Xₙ` read on the small étale site of `X₀` through
`X₀ ≅ g⁻¹(Y₀) ⊆ Xₙ` is an extension of `(aₙ ≫ h)⁻¹𝒪_Y`-algebras of `𝒪_{X₀}` by the restricted
conormal module of `g⁻¹(Y₀) ⊆ Xₙ`, `aₙ : X₀ ⟶ Xₙ` the transition morphism. -/
def towerExtension (n : ℕ) {Y : AlgebraicSpaces B S hS} (h : towerSpace ξ n ⟶ Y) :
    Deformation.AlgebraExtension (J := Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      (Space.structureSharpInverseImage B S hS (towerInclusion ξ n ≫ h))
      (towerExtensionIdeal ξ hsurj hsq e he n) :=
  Space.castBase B S hS
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ h)
      (towerFibreIso_hom_comp_subspaceInclusion ξ hsurj hsq e he n))))
    ((Space.etaleRestrictionFunctor B S hS (towerFibreIso ξ hsurj hsq e he n).hom
      (Space.isEtale_hom_of_iso B S hS _) _ _).obj
      (Space.firstOrderAlgebraExtension B S hS (towerFibre ξ hsurj hsq e he n)
        (isFirstOrderThickening_towerFibre ξ hsurj hsq e he n) h))

/-- `X₀ ≅ g⁻¹(Y₀)` followed by the projection `g⁻¹(Y₀) ⟶ Y₀` is the structure morphism of `X₀`. -/
theorem towerFibreIso_hom_comp_preimageRangeProjection (n : ℕ) :
    (towerFibreIso ξ hsurj hsq e he n).hom ≫
        Space.preimageRangeProjection B S hS (towerStructureMap ξ n) _
          (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n))) =
      towerStructureMap ξ 0 :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- **The ideal of the extension is `𝒪_{X₀} ⊗_{Γ(Y₀)} Iₙ`**, `Iₙ = Ker(Γ(Yₙ) → Γ(Y₀))`, the
base ring acting through the structure morphism `X₀ ⟶ Y₀`. -/
def towerExtensionIdealIso (n : ℕ) :
    towerExtensionIdeal ξ hsurj hsq e he n ≅
      (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj
        (RingHom.squareZeroKer _
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).1
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).2) :=
  ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (towerFibreIso ξ hsurj hsq e he n).hom
      (Space.isEtale_hom_of_iso B S hS _)).app _).symm ≪≫
    (Space.modulePullback B S hS (towerFibreIso ξ hsurj hsq e he n).hom).mapIso
      (towerFibreConormalIso ξ hsurj hsq e he n) ≪≫
    (Space.baseRingTensorModulePullbackCompIso B S hS (towerFibreIso ξ hsurj hsq e he n).hom
      _).app _ ≪≫
    eqToIso (congrArg (fun φ => (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap φ)).obj _)
      (towerFibreIso_hom_comp_preimageRangeProjection ξ hsurj hsq e he n))

section RingSystem

variable (n : ℕ) {Y : AlgebraicSpaces B S hS} (h : towerSpace ξ n ⟶ Y)

/-- Postcomposition with `X₀ ≅ g⁻¹(Y₀)` is continuous for the small étale topologies of
`towerSpace` and `towerFibreSpace` (Stacks 03LP). -/
theorem towerFibreIso_smallEtalePostcomp_isContinuous :
    (Space.smallEtalePostcomp B S hS (towerFibreIso ξ hsurj hsq e he n).hom
      (Space.isEtale_hom_of_iso B S hS _)).IsContinuous
      (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
      (Space.SmallEtale.topology B S hS (towerFibreSpace ξ hsurj hsq e he n).1) :=
  Space.smallEtalePostcomp_isContinuous B S hS _ _

attribute [local instance] towerFibreIso_smallEtalePostcomp_isContinuous

/-- The middle term of `towerExtension` is the restriction of `ι⁻¹𝒪_{Xₙ}` along
`X₀ ≅ g⁻¹(Y₀)`, `ι : g⁻¹(Y₀) ⟶ Xₙ` the inclusion. -/
theorem towerExtension_extension :
    (towerExtension ξ hsurj hsq e he n h).extension =
      (Deformation.AlgebraExtension.ringRes (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
        (J := Space.SmallEtale.topology B S hS (towerFibreSpace ξ hsurj hsq e he n).1)
        (Space.smallEtalePostcomp B S hS (towerFibreIso ξ hsurj hsq e he n).hom
          (Space.isEtale_hom_of_iso B S hS _))).obj
        (Space.inverseImageStructureSheaf B S hS
          (Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))) :=
  rfl

/-- The reduction of `towerExtension` is the restriction of `ι^♯`, read through `a⁻¹𝒪 ≅ 𝒪`. -/
theorem towerExtension_reduction :
    (towerExtension ξ hsurj hsq e he n h).reduction =
        (Deformation.AlgebraExtension.ringRes
          (Space.SmallEtale.topology B S hS (towerSpace ξ 0).1)
          (J := Space.SmallEtale.topology B S hS (towerFibreSpace ξ hsurj hsq e he n).1)
          (Space.smallEtalePostcomp B S hS (towerFibreIso ξ hsurj hsq e he n).hom
            (Space.isEtale_hom_of_iso B S hS _))).map
          (Space.structureSharpInverseImage B S hS
            (Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))) ≫
        (Space.etaleRestrictionRingComparison B S hS (towerFibreIso ξ hsurj hsq e he n).hom
          (Space.isEtale_hom_of_iso B S hS _)
          (Space.subspaceInclusion B S hS (towerSpace ξ n)
            (towerFibre ξ hsurj hsq e he n))).ω.inv :=
  rfl

/-- **The middle term of the extension is `Aₙ = aₙ⁻¹𝒪_{Xₙ}`.** Through `aₙ = (X₀ ≅ g⁻¹(Y₀)) ≫ ι`,
`aₙ⁻¹𝒪_{Xₙ}` is the restriction of `ι⁻¹𝒪_{Xₙ}` along `X₀ ≅ g⁻¹(Y₀)` (Stacks 03G8). -/
def towerRingSystemExtensionIso :
    (towerRingSystem ξ).obj (op n) ≅ (towerExtension ξ hsurj hsq e he n h).extension :=
  eqToIso (congrArg (Space.inverseImageStructureSheaf B S hS)
      (towerFibreIso_hom_comp_subspaceInclusion ξ hsurj hsq e he n).symm) ≪≫
    (Space.etaleRestrictionRingComparison B S hS (towerFibreIso ξ hsurj hsq e he n).hom
      (Space.isEtale_hom_of_iso B S hS _)
      (Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))).α

/-- The identification `Aₙ ≅ 𝒪'` carries the reduction of the extension to the reduction
`aₙ^♯ : Aₙ ⟶ 𝒪_{X₀}`. -/
@[reassoc (attr := simp)]
theorem towerRingSystemExtensionIso_hom_comp_reduction :
    (towerRingSystemExtensionIso ξ hsurj hsq e he n h).hom ≫
        (towerExtension ξ hsurj hsq e he n h).reduction =
      (towerRingReduction ξ).app (op n) := by
  have hc := (Space.etaleRestrictionRingComparison B S hS (towerFibreIso ξ hsurj hsq e he n).hom
      (Space.isEtale_hom_of_iso B S hS _)
      (Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))).comm
  have hc' := (Category.assoc _ _ _).symm.trans ((Iso.comp_inv_eq _).mpr hc.symm)
  rw [towerRingReduction_app, towerExtension_reduction]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hc').trans
    (Space.structureSharpInverseImage_eqToHom B S hS
      (towerFibreIso_hom_comp_subspaceInclusion ξ hsurj hsq e he n).symm))

end RingSystem

end AlgebraicGeometry.ProperFlatFibre

end
