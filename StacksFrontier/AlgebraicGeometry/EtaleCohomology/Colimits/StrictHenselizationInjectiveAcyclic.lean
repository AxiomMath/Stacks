module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyQcqsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationDirectedSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CohomologyVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationExists

/-!
# Inverse images of injective sheaves to the strict henselization are acyclic

Let `f : X ⟶ Y` be quasi-compact and quasi-separated, `s` a geometric point of `Y` and
`p : X ×_Y Spec 𝒪^{sh}_{Y,s} ⟶ X` the projection. For an injective abelian sheaf `I` on
`X_étale`, `H^q(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹I) = 0` for `q > 0`. The base change is the limit of
the quasi-compact quasi-separated schemes `X ×_Y V` over the affine étale neighbourhoods `V` of
`s`, with affine transition morphisms, so by Stacks 09YQ every class comes from some
`X ×_Y V`; there the inverse image of `I` is injective, `X ×_Y V ⟶ X` being étale. This is the
vanishing input of the proof of Stacks 03Q9 in positive degrees.

## Main results

* `Stacks.EtaleCohomology.LimitExt.subsingleton_H_strictHenselization_of_injective`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- Inverse image along an étale morphism preserves injective abelian sheaves. -/
theorem injective_etaleAbelianInverseImage_of_etale {X Y : Scheme.{u}} (j : Y ⟶ X) [Etale j]
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] :
    Injective ((etaleAbelianInverseImage.{u, 0} j).obj I) := by
  have := Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms (extAdj j)
  exact (etaleAbelianInverseImage.{u, 0} j).injective_obj_of_injective inferInstance

/-- Cohomology in positive degree of an injective sheaf vanishes. -/
theorem subsingleton_H_of_injective {X : Scheme.{u}}
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} I q) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  exact Ext.subsingleton_of_injective _ _ n

/-- **The vanishing input of Stacks 03Q9.** For `f` quasi-compact and quasi-separated and `I`
injective on `X_étale`, `H^q(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹I) = 0` for `q > 0`. -/
theorem subsingleton_H_strictHenselization_of_injective (B : BigEtaleSite.{u}) {X Y : Scheme.{u}}
    (hY : B.Contains Y) (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (s : GeometricPoint Y)
    (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (strictHenselizationBaseChangeToSource B hY f s)).obj I) q) := by
  obtain ⟨α, _, _, ⟨a₀⟩, G, _⟩ := exists_directed_nbhd B Y hY s
  let N := nbhdSystem B Y hY s G a₀
  let E : (nbhdIndex a₀)ᵒᵖ ⥤ Scheme.{u} := N ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y
  let c := nbhdCone B Y hY s G a₀
  have hc : IsLimit c := nbhdConeIsLimit B Y hY s G a₀
  have : ∀ {i j : (nbhdIndex a₀)ᵒᵖ} (a : i ⟶ j), IsAffineHom (E.map a) := fun a =>
    inferInstanceAs (IsAffineHom (N.map a).left)
  have : ∀ {i j : (nbhdIndex a₀)ᵒᵖ} (a : i ⟶ j), Etale (E.map a) := fun a =>
    inferInstanceAs (Etale (N.map a).left)
  -- the base change `W = V_⊥ ×_Y X` and the restricted system `X ×_Y V_i`
  let v₀ : E.obj (op ⊥) ⟶ Y := (N.obj (op ⊥)).hom
  have : Etale v₀ := (N.obj (op ⊥)).prop
  let ι : pullback v₀ f ⟶ E.obj (op ⊥) := pullback.fst v₀ f
  let w : pullback v₀ f ⟶ X := pullback.snd v₀ f
  let D := restrictSystem E ι
  let cD := restrictCone E ι c
  have hcD : IsLimit cD := isLimitRestrictCone E c ι hc
  have := isIso_toBot_bot E
  have : IsAffine (E.obj (op ⊥)) := inferInstanceAs (IsAffine (N.obj (op ⊥)).left)
  have : CompactSpace (D.obj (op ⊥)) :=
    QuasiCompact.compactSpace_of_compactSpace (rsnd E ι ⊥ ≫ ι)
  have : QuasiSeparatedSpace (D.obj (op ⊥)) :=
    quasiSeparatedSpace_of_quasiSeparated (rsnd E ι ⊥ ≫ ι)
  -- the limit of the restricted system is the base change to the strict henselization
  have hπ : c.π.app (op ⊥) ≫ v₀ = strictHenselizationToBase B Y hY s :=
    nbhdCone_π_comp_hom B Y hY s G a₀ _
  let e : cD.pt ≅ strictHenselizationBaseChange B hY f s :=
    pullbackRightPullbackFstIso v₀ f (c.π.app (op ⊥)) ≪≫
      pullback.congrHom hπ rfl ≪≫ pullbackSymmetry _ _
  have he : rsndL E c ι ≫ w = e.hom ≫ strictHenselizationBaseChangeToSource B hY f s := by
    simp only [e, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_fst,
      pullback.congrHom_hom]
    rw [pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd]
  refine (subsingleton_H_inverseImage_iff_of_isIso I q _ _ e.hom he).1 ?_
  refine (subsingleton_H_iff_of_iso ((K ((restrictCone E ι c).π.app (op ⊥)) (rsnd E ι ⊥ ≫ w)
    (rsndL E c ι ≫ w) (by rw [← Category.assoc, restrictCone_π_snd])).app I) q).2 ?_
  suffices h : ∀ z : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      ((restrictCone E ι c).π.app (op ⊥))).obj ((etaleAbelianInverseImage.{u, 0}
        (rsnd E ι ⊥ ≫ w)).obj I)) q, z = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro z
  obtain ⟨i, h, y, hy⟩ := exists_le_restriction_eq_of_qcqs D cD hcD ⊥ _ q z
  have hrs : D.map (homOfLE h).op ≫ rsnd E ι ⊥ ≫ w = rsnd E ι i ≫ w := by
    rw [← Category.assoc, restrictSystem_map_snd]
  have : Etale (rsnd E ι i ≫ w) := inferInstance
  have := injective_etaleAbelianInverseImage_of_etale (rsnd E ι i ≫ w) I
  have : Injective ((etaleAbelianInverseImage.{u, 0} (D.map (homOfLE h).op)).obj
      ((etaleAbelianInverseImage.{u, 0} (rsnd E ι ⊥ ≫ w)).obj I)) :=
    Injective.of_iso ((K (D.map (homOfLE h).op) (rsnd E ι ⊥ ≫ w) (rsnd E ι i ≫ w)
      hrs.symm).app I) inferInstance
  have hy0 : y = 0 := (subsingleton_H_of_injective _ q hq).elim y 0
  rw [← hy, hy0, map_zero, Ext.zero_comp]

end Stacks.EtaleCohomology.LimitExt
