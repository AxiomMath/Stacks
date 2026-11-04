module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisInverseImageVanishing07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.PerOpenData07Q9

/-!
# The levels of `f_cris^*ℱ` along a system of thickenings mapping to `Cris(X'/S')`

Let `f : X/S ⟶ X'/S'` be a morphism of global crystalline situations, `ℱ` a locally quasi-coherent
crystal on `Cris(X'/S')` and `ℱ' = f_cris^*ℱ` its module pullback, an abelian sheaf on `Cris(X/S)`
at the coefficient universe `u + 1`.  Let `Φ : T ⟶ T'` be a morphism over `f` from a system of
thickenings `T` of `Cris(X/S)` to a system `T'` of `Cris(X'/S')` (`CechSystemHom`), both with
affine levels.  This file proves that the restriction maps

`ℱ'(T(n)_{e + 1}) ⟶ ℱ'(T(n)_e)`

are surjective as soon as the tower maps of `T` are surjective on global sections of the ambient
schemes and the transition maps of `ℱ` along the towers of `T'` are surjective
(`hasSurjectiveLevelTransitions_crisModuleInverseImage07Q9`).  By the base change formula
`bijective_crisInverseImageBaseChange` at the level maps `Φ.τ`, compatible with the tower maps by
`CechSystemHom.naturality_level` and `crisInverseImageRestrict_naturality`, the restriction map is
the tensor product of the two surjections

`Γ(T(n)_{e + 1}) ⊗ ℱ(T'(n)_{e + 1 + k}) ⟶ Γ(T(n)_e) ⊗ ℱ(T'(n)_{e + k})`.

The two inputs of the comparison of [Stacks, Tag 0133] for the local step of [Stacks, Tag 07Q9]
on the side of `f⁻¹(W)` are then supplied for the Čech system of `f⁻¹(W)` attached to a chain
normal form: `vanishingOnLevels07Q9_chainCechSystem` and
`hasSurjectiveLevelTransitions_chainCechSystem07Q9`.

## Main results

* `surjective_levelMap_of_hasSurjectiveLevelTransitions07Q9` — surjective transitions between any
  two levels.
* `hasSurjectiveLevelTransitions_crisModuleInverseImage07Q9` — the surjectivity for `ℱ'`.
* `vanishingOnLevels07Q9_chainCechSystem`, `hasSurjectiveLevelTransitions_chainCechSystem07Q9` —
  the two hypotheses on `ℱ'` along the Čech system of `f⁻¹(W)`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Simplicial

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-- **Surjective transitions between any two levels**: if the restriction maps of `H` along the
tower maps `T(n)_e ⟶ T(n)_{e + 1}` are surjective, so are those along `T(n)_a ⟶ T(n)_b` for every
`a ≤ b`, the composites of the former. -/
theorem surjective_levelMap_of_hasSurjectiveLevelTransitions07Q9
    {S : GlobalCrystallineSituation.{u}} {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {H : Sheaf (smallTopology S) AddCommGrpCat.{u + 1}} (hH : HasSurjectiveLevelTransitions T H)
    (n : ℕ) {a b : ℕ} (hab : a ≤ b) :
    Function.Surjective (ConcreteCategory.hom
      (H.obj.map ((T.obj (op ⦋n⦌)).map (homOfLE hab)).op)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Subsingleton.elim (homOfLE _) (𝟙 a), (T.obj (op ⦋n⦌)).map_id, op_id, H.obj.map_id]
    exact (ConcreteCategory.bijective_of_isIso _).2
  | succ b hab ih =>
    rw [← homOfLE_comp hab (Nat.le_succ b), (T.obj (op ⦋n⦌)).map_comp, op_comp, H.obj.map_comp]
    exact ih.comp (hH n b)

section General

variable {S S' : GlobalCrystallineSituation.{u}} {f : S.S ⟶ S'.S} {g : S.X ⟶ S'.X}
  {h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber}

/-- **The restriction maps of `f_cris^*ℱ` along the towers of a system mapping to `Cris(X'/S')` are
surjective.**  Let `Φ : T ⟶ T'` be a morphism of systems of thickenings over `f`, both with affine
levels, such that the tower maps of `T` are surjective on global sections of the ambient schemes
and the transition maps of the locally quasi-coherent crystal `ℱ` along the towers of `T'` are
surjective.  Then the restriction maps of `f_cris^*ℱ` along the towers of `T` are surjective: by
the base change formula at the level maps of `Φ` they are tensor products of surjections. -/
theorem hasSurjectiveLevelTransitions_crisModuleInverseImage07Q9
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (Φ : CechSystemHom f g h T T')
    (hT : HasAffineMonoLevels T) (hT' : HasAffineMonoLevels T')
    (hring : ∀ n e : ℕ, Function.Surjective
      ((structureSheaf S).obj.map ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op).hom)
    (F : SheafOfModules.{u} (structureSheaf S')) (hF : IsLocallyQuasiCoherent F)
    (hcrys : IsSheafCrystal F) (hFs : HasSurjectiveLevelTransitions T' (abelianSheaf F)) :
    HasSurjectiveLevelTransitions T ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
      ((moduleULift S').obj F))) := by
  intro n e
  have := hT.isAffine n e
  have := hT'.isAffine n (e + Φ.k)
  have hle : e + Φ.k ≤ e + 1 + Φ.k := by omega
  have w := Φ.naturality_level ⦋n⦌ (e := e) (e' := e + 1) (homOfLE (Nat.le_succ e))
  have hsF := surjective_levelMap_of_hasSurjectiveLevelTransitions07Q9 hFs n hle
  let K : AddSubgroup ((ModuleCat.extendScalars (tauRing (Φ.τ ⦋n⦌ e)).hom).obj
      (sectionsOver F ((T'.obj (op ⦋n⦌)).obj (e + Φ.k)))) :=
    (ConcreteCategory.hom (((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
      ((moduleULift S').obj F))).obj.map
        ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op)).range.comap
      (crisInverseImageBaseChange f g h F (Φ.τ ⦋n⦌ e))
  have hK : ∀ q, q ∈ K := by
    intro q
    refine TensorProduct.induction_on (motive := fun q ↦ q ∈ K) q (zero_mem K)
      (fun t s ↦ ?_) (fun q q' hq hq' ↦ add_mem hq hq')
    obtain ⟨t₀, ht₀⟩ := hring n e t
    obtain ⟨s₀, hs₀⟩ := hsF (ULift.up s)
    let s₁ : F.val.obj (op ((T'.obj (op ⦋n⦌)).obj (e + 1 + Φ.k))) := s₀.down
    have hs₁ : F.val.restrictₛₗ ((T'.obj (op ⦋n⦌)).map (homOfLE hle)).op s₁ = s :=
      congrArg ULift.down hs₀
    refine ⟨(show (structureSheaf S).obj.obj (op ((T.obj (op ⦋n⦌)).obj (e + 1))) from t₀) •
      crisInverseImageRestrict f g h F (Φ.τ ⦋n⦌ (e + 1)) s₁, ?_⟩
    show ((crisModuleInverseImage f g h).obj ((moduleULift S').obj F)).val.restrictₛₗ
        ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op (t₀ •
          crisInverseImageRestrict f g h F (Φ.τ ⦋n⦌ (e + 1)) s₁) =
      crisInverseImageBaseChange f g h F (Φ.τ ⦋n⦌ e)
        (Stacks.PullbackModel.tmul (tauRing (Φ.τ ⦋n⦌ e)).hom t s)
    rw [map_smulₛₗ, crisInverseImageRestrict_naturality f g h F _ _ _ _ w, hs₁]
    exact (congrArg (· • crisInverseImageRestrict f g h F (Φ.τ ⦋n⦌ e) s) ht₀).trans
      (crisInverseImageBaseChange_tmul f g h F (Φ.τ ⦋n⦌ e) t s).symm
  intro y
  obtain ⟨q, rfl⟩ := (bijective_crisInverseImageBaseChange f g h F (Φ.τ ⦋n⦌ e) hF hcrys).2 y
  exact hK q

/-- `hasSurjectiveLevelTransitions_crisModuleInverseImage07Q9` for a crystal in quasi-coherent
modules. -/
theorem hasSurjectiveLevelTransitions_crisModuleInverseImage07Q9_of_isQuasiCoherentCrystal
    {T : SimplicialObject (ℕ ⥤ CrystallineThickening S)}
    {T' : SimplicialObject (ℕ ⥤ CrystallineThickening S')} (Φ : CechSystemHom f g h T T')
    (hT : HasAffineMonoLevels T) (hT' : HasAffineMonoLevels T')
    (hring : ∀ n e : ℕ, Function.Surjective
      ((structureSheaf S).obj.map ((T.obj (op ⦋n⦌)).map (homOfLE (Nat.le_succ e))).op).hom)
    (F : SheafOfModules.{u} (structureSheaf S')) (hF : IsQuasiCoherentCrystal S' F)
    (hFs : HasSurjectiveLevelTransitions T' (abelianSheaf F)) :
    HasSurjectiveLevelTransitions T ((toAbelianSheaf S).obj ((crisModuleInverseImage f g h).obj
      ((moduleULift S').obj F))) :=
  hasSurjectiveLevelTransitions_crisModuleInverseImage07Q9 Φ hT hT' hring F
    ((isQuasicoherentOnSite_iff F).1 hF.1).1 hF.2 hFs

end General

/-! ### The Čech system of `f⁻¹(W)` attached to a chain normal form -/

section Chain

variable (S : GlobalCrystallineSituation.{u}) {V : S.S.scheme.Opens} {W : S.X.Opens}
  (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hVW : W ≤ sourceToBase S ⁻¹ᵁ V)
  {X' : Scheme.{u}} (f : X' ⟶ S.X) (hW₂ : IsAffineOpen (f ⁻¹ᵁ W)) {p n : ℕ}
  (ch : AlphaPChain p Γ(S.X, W) n) (e : Γ(X', f ⁻¹ᵁ W) ≅ ch.top)
  (he : f.app W ≫ e.hom = ch.toTop)

/-- **The higher cohomology of `f_cris^*ℱ` vanishes at the levels of the Čech system of `f⁻¹(W)`
attached to a chain normal form**, by `vanishingOnLevels07Q9_crisModuleInverseImage` along the
morphism of Čech systems `chainCechSystemHom07Q9`. -/
theorem vanishingOnLevels07Q9_chainCechSystem (F : SheafOfModules.{u} (structureSheaf S))
    (hF : IsQuasiCoherentCrystal S F) :
    VanishingOnLevels07Q9
      (openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he))
      ((toAbelianSheaf (overSituation S f)).obj
        ((crisModuleInverseImage (S := overSituation S f) (S' := S) (𝟙 S.S) f
          (overSituation_compat S f)).obj
          ((moduleULift S).obj F))) :=
  vanishingOnLevels07Q9_crisModuleInverseImage_of_isQuasiCoherentCrystal
    (chainCechSystemHom07Q9 S hV hW hVW f hW₂ ch e he)
    (hasAffineMonoLevels_openSystem07Q9 (overSituation S f) hV hW₂ _ _ _)
    (hasAffineMonoLevels_openSystem07Q9 S hV hW hVW _ _) F hF

/-- **The restriction maps of `f_cris^*ℱ` along the towers of the Čech system of `f⁻¹(W)` attached
to a chain normal form are surjective.**  The tower maps of that system are closed immersions of
affine schemes, hence surjective on global sections, and the transition maps of `ℱ` along the
towers of the Čech system of `W` are surjective (`hasSurjectiveLevelTransitions_openSystem07Q9`),
so `hasSurjectiveLevelTransitions_crisModuleInverseImage07Q9` applies along
`chainCechSystemHom07Q9`. -/
theorem hasSurjectiveLevelTransitions_chainCechSystem07Q9
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : IsQuasiCoherentCrystal S F) :
    HasSurjectiveLevelTransitions
      (openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
        (chainPresentation07Q9 S hW hVW f hW₂ ch e)
        (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he))
      ((toAbelianSheaf (overSituation S f)).obj
        ((crisModuleInverseImage (S := overSituation S f) (S' := S) (𝟙 S.S) f
          (overSituation_compat S f)).obj
          ((moduleULift S).obj F))) := by
  refine hasSurjectiveLevelTransitions_crisModuleInverseImage07Q9_of_isQuasiCoherentCrystal
    (chainCechSystemHom07Q9 S hV hW hVW f hW₂ ch e he)
    (hasAffineMonoLevels_openSystem07Q9 (overSituation S f) hV hW₂ _ _ _)
    (hasAffineMonoLevels_openSystem07Q9 S hV hW hVW _ _) (fun m k ↦ ?_) F hF
    (hasSurjectiveLevelTransitions_openSystem07Q9 S hV hW hVW _ _ F hF)
  have := isAffine_target_openSystem07Q9 (overSituation S f) hV hW₂
    (preimage_le_overSituation07Q9 S hVW f) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
    (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) m (k + 1)
  have := isClosedImmersion_openSystem07Q9_map (overSituation S f) hV hW₂
    (preimage_le_overSituation07Q9 S hVW f) (chainPresentation07Q9 S hW hVW f hW₂ ch e)
    (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he) m (Nat.le_succ k)
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    (((openSystem07Q9 (overSituation S f) hV hW₂ (preimage_le_overSituation07Q9 S hVW f)
      (chainPresentation07Q9 S hW hVW f hW₂ ch e)
      (surjective_chainPresentation07Q9 S hW hVW f hW₂ ch e he)).obj (op ⦋m⦌)).map
        (homOfLE (Nat.le_succ k))).hom.targetHom.hom).2

end Chain

end Crystalline.GlobalCrystallineSituation.SmallSite

end
