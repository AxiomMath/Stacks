module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerExtensions
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModulePreimageSections

/-!
# The sections `1 ⊗ m` of the ideal of the extensions of a square-zero tower

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerExtension`, the ideal of the
extension `0 → 𝒪_{X₀} ⊗_{R₀} Iₙ → 𝒪_{Xₙ} → 𝒪_{X₀} → 0` is the conormal module of
`g⁻¹(Y₀) ⊆ Xₙ`, restricted to `X₀` along `X₀ ≅ g⁻¹(Y₀)`, and it is identified with
`𝒪_{X₀} ⊗_{Γ(Y₀)} Iₙ` by `AlgebraicGeometry.ProperFlatFibre.towerExtensionIdealIso`. This file
computes that identification on the sections `1 ⊗ m`: the section `1 ⊗ m` is the restriction to
`X₀` of the class of the section `g^♯m` of the ideal of `g⁻¹(Y₀)`. This is the module half of the
identification, in the body of the proof of [Stacks Project, Tag 0D3X], of the map
`φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` with the canonical map of [Stacks Project, Tag 0D3F].

## Main results

* `AlgebraicGeometry.ProperFlatFibre.baseRingTensorSection_towerExtensionIdealIso_inv`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory

/-- **A section read through the inverse of `C ≅ H(D) ≅ H(F(M)) ≅ G_{φ₀}(M) = G_φ(M)`**, the
first isomorphism the inverse of `e₁`, the second the image of `e₂`, the third a component of
`c : F ⋙ H ≅ G_{φ₀}` and the last the transport along `φ₀ = φ`, computed one isomorphism at a
time. Stated for an abstract family of functors, with the sections `y φ` given as a family, so
that it is checked without unfolding concrete functors. -/
theorem comp_inv_eq_of_eq_symm_trans_mapIso_trans_app_trans_eqToIso {𝒜 𝒟 ℰ Φ : Type*}
    [Category 𝒜] [Category 𝒟] [Category ℰ] (G : Φ → 𝒜 ⥤ ℰ) {φ₀ φ : Φ} (hφ : φ₀ = φ)
    {F : 𝒜 ⥤ 𝒟} {H : 𝒟 ⥤ ℰ} (c : F ⋙ H ≅ G φ₀) {M : 𝒜} {D : 𝒟} {C : ℰ} (e₁ : H.obj D ≅ C)
    (e₂ : D ≅ F.obj M) {U : ℰ} (y : ∀ φ, U ⟶ (G φ).obj M) (x : U ⟶ H.obj (F.obj M))
    (w : U ⟶ H.obj D) (z : U ⟶ C) (h₁ : y φ₀ ≫ c.inv.app M = x) (h₂ : x ≫ H.map e₂.inv = w)
    (h₃ : w ≫ e₁.hom = z) (e : C ≅ (G φ).obj M)
    (he : e = e₁.symm ≪≫ H.mapIso e₂ ≪≫ c.app M ≪≫
      eqToIso (congrArg (fun φ => (G φ).obj M) hφ)) :
    y φ ≫ e.inv = z := by
  subst hφ h₁ h₂ h₃ he
  simp

end CategoryTheory

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

/-- **The section `1 ⊗ m` of `𝒪_{X₀} ⊗_{Γ(Y₀)} Iₙ` is the restriction of the class of `g^♯m`**:
through `AlgebraicGeometry.ProperFlatFibre.towerExtensionIdealIso` it is the restriction to `X₀`,
along `X₀ ≅ g⁻¹(Y₀)`, of the pullback to `g⁻¹(Y₀)` of the section `g^♯m` of the ideal of
`g⁻¹(Y₀) ⊆ Xₙ`, for `m ∈ Iₙ = Ker(Γ(Yₙ) → Γ(Y₀))`. -/
theorem baseRingTensorSection_towerExtensionIdealIso_inv (n : ℕ)
    (m : RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((ξ ⋙ cartesianProperFlatProjection B S hS).map (homOfLE (Nat.zero_le n)))).op).hom) :
    Space.baseRingTensorSection B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))
        (RingHom.squareZeroKer _
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).1
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).2) m ≫
        (towerExtensionIdealIso ξ hsurj hsq e he n).inv =
      Space.modulePullbackGlobalSection B S hS (towerFibreIso ξ hsurj hsq e he n).hom
          (Space.modulePullbackGlobalSection B S hS
            (Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))
            (Space.preimageIdealSection B S hS (towerStructureMap ξ n)
              (Space.rangeSubspace B S hS _ (isClosedImmersion_towerBase_map ξ hsurj hsq e he
                (homOfLE (Nat.zero_le n))))
              ⟨m.1, (Space.closedSubspaceBaseIdeal_rangeSubspace B S hS _
                (isClosedImmersion_towerBase_map ξ hsurj hsq e he
                  (homOfLE (Nat.zero_le n)))).symm ▸ m.2⟩)) ≫
        ((Space.modulePullbackIsoEtaleRestrictionModule B S hS
          (towerFibreIso ξ hsurj hsq e he n).hom (Space.isEtale_hom_of_iso B S hS _)).app
          (Space.conormalModule B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))).hom := by
  have hSZ : Space.baseRingTensorSection B S hS (towerFibreSpace ξ hsurj hsq e he n)
      (Space.baseRingHomOfMap (Space.preimageRangeProjection B S hS (towerStructureMap ξ n) _
        (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n)))))
      (RingHom.squareZeroKer _
        (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n))).1
        (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n))).2) m ≫
        (towerFibreConormalIso ξ hsurj hsq e he n).inv =
      Space.modulePullbackGlobalSection B S hS
        (Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))
        (Space.preimageIdealSection B S hS (towerStructureMap ξ n)
          (Space.rangeSubspace B S hS _ (isClosedImmersion_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))))
          ⟨m.1, (Space.closedSubspaceBaseIdeal_rangeSubspace B S hS _
            (isClosedImmersion_towerBase_map ξ hsurj hsq e he
              (homOfLE (Nat.zero_le n)))).symm ▸ m.2⟩) := by
    rw [show towerFibreConormalIso ξ hsurj hsq e he n =
        Space.conormalModulePreimageSquareZeroIso B S hS (towerStructureMap ξ n)
          ((ξ ⋙ cartesianProperFlatProjection B S hS).map (homOfLE (Nat.zero_le n)))
          (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n)))
          (isFlat_towerStructureMap ξ n) (isAffine_towerBase ξ e n)
          (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))).2 from rfl]
    exact Space.baseRingTensorSection_conormalModulePreimageSquareZeroIso_inv B S hS
      (towerStructureMap ξ n)
      ((ξ ⋙ cartesianProperFlatProjection B S hS).map (homOfLE (Nat.zero_le n)))
      (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n)))
      (isFlat_towerStructureMap ξ n) (isAffine_towerBase ξ e n)
      (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
        (homOfLE (Nat.zero_le n))).2 m
  exact CategoryTheory.comp_inv_eq_of_eq_symm_trans_mapIso_trans_app_trans_eqToIso
    (fun φ => Space.baseRingTensorModule B S hS (towerSpace ξ 0) (Space.baseRingHomOfMap φ))
    (towerFibreIso_hom_comp_preimageRangeProjection ξ hsurj hsq e he n)
    (Space.baseRingTensorModulePullbackCompIso B S hS (towerFibreIso ξ hsurj hsq e he n).hom _)
    ((Space.modulePullbackIsoEtaleRestrictionModule B S hS
      (towerFibreIso ξ hsurj hsq e he n).hom (Space.isEtale_hom_of_iso B S hS _)).app
      (Space.conormalModule B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n)))
    (towerFibreConormalIso ξ hsurj hsq e he n)
    (fun φ => Space.baseRingTensorSection B S hS (towerSpace ξ 0) (Space.baseRingHomOfMap φ)
      (RingHom.squareZeroKer _
        (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n))).1
        (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n))).2) m)
    _
    (Space.modulePullbackGlobalSection B S hS (towerFibreIso ξ hsurj hsq e he n).hom
      (Space.modulePullbackGlobalSection B S hS
        (Space.subspaceInclusion B S hS (towerSpace ξ n) (towerFibre ξ hsurj hsq e he n))
        (Space.preimageIdealSection B S hS (towerStructureMap ξ n)
          (Space.rangeSubspace B S hS _ (isClosedImmersion_towerBase_map ξ hsurj hsq e he
            (homOfLE (Nat.zero_le n))))
          ⟨m.1, (Space.closedSubspaceBaseIdeal_rangeSubspace B S hS _
            (isClosedImmersion_towerBase_map ξ hsurj hsq e he
              (homOfLE (Nat.zero_le n)))).symm ▸ m.2⟩)))
    _
    (Space.baseRingTensorSection_comp_pullbackCompIso_inv B S hS
      (towerFibreIso ξ hsurj hsq e he n).hom
      (Space.preimageRangeProjection B S hS (towerStructureMap ξ n) _
        (isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n))))
      (RingHom.squareZeroKer _
        (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n))).1
        (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n))).2) m)
    ((Space.modulePullbackGlobalSection_comp B S hS _ _ _).symm.trans
      (congrArg (Space.modulePullbackGlobalSection B S hS
        (towerFibreIso ξ hsurj hsq e he n).hom) hSZ))
    rfl (towerExtensionIdealIso ξ hsurj hsq e he n) rfl

end AlgebraicGeometry.ProperFlatFibre

end
