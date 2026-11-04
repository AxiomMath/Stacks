module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineRootsOfUnity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.CurveHigherDirectImageVanishing
public import StacksFrontier.Algebra.Homology.RightDerivedSecondEdgeMono
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Unconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologyWithSupportDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointDirectSumCohomology

/-!
# The first higher direct image of `μ_ℓ` along `𝐆_m ⟶ 𝐀¹`

Let `k` be an algebraically closed field, `ℓ` invertible in `k` and `j : 𝐆_m ⟶ 𝐀¹_k` the
inclusion of the punctured affine line. For `F = j⁻¹ μ_ℓ`:

* `R^q j_* F` vanishes on `𝐆_m` for `q ≥ 1` (smooth base change along the open immersion `j`);
* `Γ(𝐀¹, R¹j_* F)` has `ℓ` elements: the co-edge map `H¹(𝐆_m, F) ⟶ Γ(𝐀¹, R¹j_* F)` is
  bijective because `H¹(𝐀¹, j_* F) = H¹(𝐀¹, μ_ℓ) = 0` and `H²(𝐀¹, j_* F) = 0`, and
  `H¹(𝐆_m, μ_ℓ) ≅ ℤ/ℓ`.

## Main results

* `Stacks.EtaleCohomology.Purity.isZero_restriction_rightDerived_punctured`.
* `Stacks.EtaleCohomology.Purity.natCard_sections_rightDerived_one_rootsOfUnity`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

/-- **Higher direct images along an open immersion vanish on the open**, for torsion sheaves of
orders invertible on the target: smooth base change along `j` itself. -/
theorem isZero_restriction_rightDerived_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : ∀ (t : GeometricPoint U) (a : (smallEtaleStalkAb t.hom).obj F),
      ∃ n : ℕ, 0 < n ∧ IsUnit ((n : ℤ) : Γ(X, ⊤)) ∧ n • a = 0) (q : ℕ) (hq : 0 < q) :
    IsZero ((etaleRestriction.{u, 0} j).obj
      (((smallEtalePushforwardAb j).rightDerived q).obj F)) := by
  have sq : IsPullback (𝟙 U) (𝟙 U) j j := by
    have : Mono j := inferInstance
    exact IsKernelPair.id_of_mono j
  have : Smooth j := inferInstance
  have : IsSeparated j := IsSeparated.isSeparated_of_mono j
  have : QuasiSeparated j := AlgebraicGeometry.IsSeparated.instQuasiSeparated j
  have hbc := @SmoothBaseChange.isIso_higherBaseChangeMapAb_app_of_smooth U U X U j (𝟙 U) (𝟙 U) j
    sq ‹_› ‹_› ‹_› F hF q
  have hz : IsZero (((smallEtalePushforwardAb (𝟙 U)).rightDerived q).obj
      ((smallEtalePullbackAb (𝟙 U)).obj F)) := by
    obtain ⟨q', rfl⟩ := Nat.exists_eq_add_of_lt hq
    exact (CategoryTheory.isZero_rightDerived_id_obj _ (0 + q')).of_iso
      ((Functor.rightDerivedIsoOfNatIso (smallEtalePushforwardAbIdOf (𝟙 U) rfl) _).app _)
  exact (hz.of_iso (asIso ((higherBaseChangeMapAb j j (𝟙 U) (𝟙 U) sq.w q).app F))).of_iso
    ((smallEtalePullbackAbIsoEtaleRestriction j).app _).symm

section AffineLine

variable (k : Type u) [Field k] [IsAlgClosed k] {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓ : IsUnit (ℓ : k))

/-- The restriction `j⁻¹ μ_ℓ` of `μ_ℓ` to the punctured affine line. -/
abbrev rootsOfUnityPunctured :
    Sheaf (punctured k).toScheme.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (etaleRestriction.{u, 0} (punctured k).ι).obj
    (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ)

include hℓ0 hℓ in
/-- **`Γ(𝐀¹, R¹j_* j⁻¹ μ_ℓ)` has `ℓ` elements.** -/
theorem natCard_sections_rightDerived_one_rootsOfUnity :
    Nat.card ((Sheaf.Γ (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (((smallEtalePushforwardAb (punctured k).ι).rightDerived 1).obj
        (rootsOfUnityPunctured k (ℓ := ℓ)))) = ℓ := by
  let P := smallEtalePushforwardAb (punctured k).ι
  let Q := Sheaf.Γ (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1}
  have : Q.Additive := Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1} _
  have : PreservesLimitsOfSize.{0, 0} Q :=
    (constantSheafΓAdj (affineLine k).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightAdjoint_preservesLimits
  have : PreservesLimitsOfSize.{0, 0} P :=
    (smallEtaleAdjunctionAb (punctured k).ι).rightAdjoint_preservesLimits
  have hθ := isIso_rootsOfUnityUnit k hℓ0 hℓ
  let e : P.obj (rootsOfUnityPunctured k (ℓ := ℓ)) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ :=
    (asIso (rootsOfUnityUnit k (ℓ := ℓ))).symm
  have hz : ∀ n, Subsingleton (Sheaf.H.{u + 1}
      (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ) n) →
      IsZero ((Q.rightDerived n).obj (P.obj (rootsOfUnityPunctured k (ℓ := ℓ)))) := fun n hs => by
    refine (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
      _ _ _).1 ?_
    refine Function.Injective.subsingleton (f := Sheaf.H.map e.hom n) fun a b h => ?_
    have := congrArg (Sheaf.H.map e.inv n) h
    rwa [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply,
      Sheaf.H.map_id_apply] at this
  have h1 := hz 1 (subsingleton_sheafH_one_rootsOfUnity_affineLine k hℓ0 hℓ)
  have h2 := hz 2 (subsingleton_sheafH_two_rootsOfUnity_affineLine k hℓ0 hℓ)
  have hiso := Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_one_of_isZero P Q
    (rootsOfUnityPunctured k (ℓ := ℓ)) h1 h2
  let E : Q.obj ((P.rightDerived 1).obj (rootsOfUnityPunctured k (ℓ := ℓ))) ≅
      (Sheaf.functorH.{u + 1} (punctured k).toScheme.smallEtaleTopology 1).obj
        (rootsOfUnityPunctured k (ℓ := ℓ)) :=
    (asIso ((Stacks.Cohomology.RightDerivedCoEdge.secondEdge P Q 1).app _)).symm ≪≫
      (Functor.rightDerivedIsoOfNatIso (etaleAbelianDirectImageGammaIso.{u, 0} (punctured k).ι)
        1).app _ ≪≫
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1} _ 1).app _
  rw [Nat.card_congr E.addCommGroupIsoToAddEquiv.toEquiv]
  show Nat.card (Sheaf.H.{u + 1} (rootsOfUnityPunctured k (ℓ := ℓ)) 1) = ℓ
  rw [natCard_sheafH_congr (restrictionRootsOfUnityIso (punctured k).ι ℓ) 1]
  exact natCard_sheafH_one_rootsOfUnity_punctured k hℓ0 hℓ

omit [IsAlgClosed k] in
/-- Isomorphic sheaves have isomorphic cohomology. -/
def sheafHAddEquivOfIso {X : Scheme.{u}} {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (e : F ≅ G) (n : ℕ) : Sheaf.H.{u + 1} F n ≃+ Sheaf.H.{u + 1} G n where
  toFun := Sheaf.H.map e.hom n
  invFun := Sheaf.H.map e.inv n
  left_inv x := by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply]
  right_inv x := by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]
  map_add' := map_add _

include hℓ0 hℓ in
/-- **`Γ(𝐀¹, R¹j_* j⁻¹ μ_ℓ) ≅ ℤ/ℓ`**: by the second edge map it is `H¹(𝐆_m, μ_ℓ)`, since
`H¹(𝐀¹, μ_ℓ) = H²(𝐀¹, μ_ℓ) = 0`, and that is `ℤ/ℓ` by the Kummer sequence. -/
def sectionsRightDerivedOneRootsOfUnityEquiv :
    (Sheaf.Γ (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (((smallEtalePushforwardAb (punctured k).ι).rightDerived 1).obj
        (rootsOfUnityPunctured k (ℓ := ℓ))) ≃+ ZMod ℓ := by
  let P := smallEtalePushforwardAb (punctured k).ι
  let Q := Sheaf.Γ (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1}
  haveI : Q.Additive := Stacks.Cohomology.GlobalSections.additive_Γ.{u + 1} _
  haveI : PreservesLimitsOfSize.{0, 0} Q :=
    (constantSheafΓAdj (affineLine k).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightAdjoint_preservesLimits
  haveI : PreservesLimitsOfSize.{0, 0} P :=
    (smallEtaleAdjunctionAb (punctured k).ι).rightAdjoint_preservesLimits
  have hθ := isIso_rootsOfUnityUnit k hℓ0 hℓ
  let e : P.obj (rootsOfUnityPunctured k (ℓ := ℓ)) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ :=
    (asIso (rootsOfUnityUnit k (ℓ := ℓ))).symm
  have h1 : IsZero ((Q.rightDerived 1).obj (P.obj (rootsOfUnityPunctured k (ℓ := ℓ)))) := by
    refine (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
      _ _ _).1 ?_
    have := subsingleton_sheafH_one_rootsOfUnity_affineLine k hℓ0 hℓ
    refine Function.Injective.subsingleton (f := Sheaf.H.map e.hom 1) fun a b h => ?_
    have := congrArg (Sheaf.H.map e.inv 1) h
    rwa [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply,
      Sheaf.H.map_id_apply] at this
  have h2 : IsZero ((Q.rightDerived 2).obj (P.obj (rootsOfUnityPunctured k (ℓ := ℓ)))) := by
    refine (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{u + 1}
      _ _ _).1 ?_
    have := subsingleton_sheafH_two_rootsOfUnity_affineLine k hℓ0 hℓ
    refine Function.Injective.subsingleton (f := Sheaf.H.map e.hom 2) fun a b h => ?_
    have := congrArg (Sheaf.H.map e.inv 2) h
    rwa [← Sheaf.H.map_comp_apply, ← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply,
      Sheaf.H.map_id_apply] at this
  have hiso := Stacks.Cohomology.RightDerivedCoEdge.isIso_secondEdge_app_one_of_isZero P Q
    (rootsOfUnityPunctured k (ℓ := ℓ)) h1 h2
  let E : Q.obj ((P.rightDerived 1).obj (rootsOfUnityPunctured k (ℓ := ℓ))) ≅
      (Sheaf.functorH.{u + 1} (punctured k).toScheme.smallEtaleTopology 1).obj
        (rootsOfUnityPunctured k (ℓ := ℓ)) :=
    (asIso ((Stacks.Cohomology.RightDerivedCoEdge.secondEdge P Q 1).app _)).symm ≪≫
      (Functor.rightDerivedIsoOfNatIso (etaleAbelianDirectImageGammaIso.{u, 0} (punctured k).ι)
        1).app _ ≪≫
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1} _ 1).app _
  exact E.addCommGroupIsoToAddEquiv.trans
    ((sheafHAddEquivOfIso (restrictionRootsOfUnityIso (punctured k).ι ℓ) 1).trans
      (sheafHOneRootsOfUnityPuncturedEquiv k hℓ0 hℓ))

end AffineLine

end Stacks.EtaleCohomology.Purity

end
