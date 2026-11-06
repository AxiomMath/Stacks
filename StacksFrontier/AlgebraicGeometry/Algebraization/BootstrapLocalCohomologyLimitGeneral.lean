module

public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapLocalCohomologyLimitCone
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationComparison
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorProjections
public import StacksFrontier.RingTheory.Dualizing.Ext
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.Composition
public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantConsequences
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Comparison
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian

/-!
# Local cohomology of `I`-power-torsion modules, and the limit cones of Stacks 0EG0

Let `A` be a Noetherian ring and `I`, `J` ideals of `A`. For an object `K` of `D(A)` with
`I`-power-torsion cohomology, the map `RΓ_{V(I + J)}(K) ⟶ RΓ_{V(J)}(K)` induced by the inclusion of
supports is an isomorphism. Consequently, if `V(J) ∩ V(I) = V(𝔞) ∩ V(I)` then the towers
`{H^k_{V(J)}(M/IⁿM)}` and `{H^k_{V(𝔞)}(M/IⁿM)}` of local cohomology of the adic quotients of a
module are isomorphic, and Stacks 0EG0 holds in cone form at an admissible shrinking of the ideal
of Stacks 0EFL.

## Main results

* `Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInInclusion_app_of_torsion` — for `K`
  with `I`-power-torsion cohomology, `RΓ_{V(I + J)}(K) ⟶ RΓ_{V(J)}(K)` is an isomorphism.
* `Stacks.LocalCohomology.localCohomologyAdicTowerAddIso` — the towers `{H^k_{V(I + J)}(M/IⁿM)}`
  and `{H^k_{V(J)}(M/IⁿM)}` are isomorphic, compatibly with the cones
  (`Stacks.LocalCohomology.localCohomologyAdicCone_π_comp_localCohomologyAdicTowerAddIso_hom`).
* `Stacks.LocalCohomology.localCohomologyAdicTowerIsoOfZeroLocusInter` — if
  `V(J) ∩ V(I) = V(𝔞) ∩ V(I)` then `{H^k_{V(J)}(M/IⁿM)} ≅ {H^k_{V(𝔞)}(M/IⁿM)}`.
* `Stacks.LocalCohomology.isMittagLefflerCategorical_localCohomologyAdicTower_of_zeroLocus_inter` —
  so the Mittag-Leffler property passes from one support to the other.
* `Stacks.LocalCohomology.nonempty_isLimit_localCohomologyAdicCone_of_isAlgebraizationIdeal` —
  Stacks 0EG0 in cone form at an admissible shrinking `J` of the ideal of Stacks 0EFL:
  `Hⁱ_{V(J)}(M) = lim Hⁱ_{V(J)}(M/IⁿM)` through the quotient maps, given the Mittag-Leffler
  property of `{H^{i-1}_{V(𝔞)}(M/IⁿM)}`.

## References

* [Stacks Project, Tag 0EG4](https://stacks.math.columbia.edu/tag/0EG4)
* [Stacks Project, Tag 0EG0](https://stacks.math.columbia.edu/tag/0EG0)
* [Stacks Project, Tag 0EEW](https://stacks.math.columbia.edu/tag/0EEW)
* [Stacks Project, Tag 0BJC](https://stacks.math.columbia.edu/tag/0BJC)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
/-- The zero locus of `I + J` lies in that of `J`. -/
theorem zeroLocus_add_subset_right (I J : Ideal A) :
    PrimeSpectrum.zeroLocus ((I + J : Ideal A) : Set A) ⊆ PrimeSpectrum.zeroLocus (J : Set A) :=
  PrimeSpectrum.zeroLocus_anti_mono (SetLike.coe_subset_coe.2 le_sup_right)

/-- Over a Noetherian ring, for an object `K` of `D(A)` with `I`-power-torsion cohomology, the map
`RΓ_{V(I + J)}(K) ⟶ RΓ_{V(J)}(K)` induced by the inclusion `V(I + J) ⊆ V(J)` is an isomorphism. -/
theorem isIso_derivedSectionsWithSupportInInclusion_app_of_torsion (I J : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : Dualizing.derivedPowerTorsionProperty A I I.fg_of_isNoetherianRing K) :
    IsIso ((derivedSectionsWithSupportInInclusion.{u, u} A
      (zeroLocus_add_subset_right I J)).app K) := by
  have hI : I.FG := I.fg_of_isNoetherianRing
  have hJ : J.FG := J.fg_of_isNoetherianRing
  have hIJ : (I + J).FG := Submodule.FG.sup hI hJ
  let cJ := (compareSectionsWithSupportLocalCohomology.{u, u} A J hJ).app K
  let cIJ := (compareSectionsWithSupportLocalCohomology.{u, u} A (I + J) hIJ).app K
  have : IsIso cJ := isIso_compareSectionsWithSupportLocalCohomology_app.{u, u} A J hJ K
  have : IsIso cIJ := isIso_compareSectionsWithSupportLocalCohomology_app.{u, u} A (I + J) hIJ K
  let εJ : (Dualizing.localCohomologyFunctor A J hJ ⋙
      (Dualizing.derivedPowerTorsionProperty A J hJ).ι).obj K ⟶ K :=
    (Dualizing.localCohomologyAdjunction.{u, u} A J hJ).counit.app K
  let εIJ : (Dualizing.localCohomologyFunctor A (I + J) hIJ ⋙
      (Dualizing.derivedPowerTorsionProperty A (I + J) hIJ).ι).obj K ⟶ K :=
    (Dualizing.localCohomologyAdjunction.{u, u} A (I + J) hIJ).counit.app K
  have hcJ : cJ ≫ εJ = (derivedSectionsWithSupportInAugmentation.{u, u} A
      (PrimeSpectrum.zeroLocus (J : Set A))).app K :=
    NatTrans.congr_app (compareSectionsWithSupportLocalCohomology_comp_counit.{u, u} A J hJ) K
  have hcIJ : cIJ ≫ εIJ = (derivedSectionsWithSupportInAugmentation.{u, u} A
      (PrimeSpectrum.zeroLocus ((I + J : Ideal A) : Set A))).app K :=
    NatTrans.congr_app
      (compareSectionsWithSupportLocalCohomology_comp_counit.{u, u} A (I + J) hIJ) K
  have hinc := NatTrans.congr_app (derivedSectionsWithSupportInInclusion_comp_augmentation.{u, u}
    A (zeroLocus_add_subset_right I J)) K
  simp only [NatTrans.comp_app] at hinc
  let incl := (derivedSectionsWithSupportInInclusion.{u, u} A
    (zeroLocus_add_subset_right I J)).app K
  let β := inv cIJ ≫ incl ≫ cJ
  have hβ : β ≫ εJ = εIJ :=
    calc β ≫ εJ = inv cIJ ≫ incl ≫ cJ ≫ εJ := by simp only [β, Category.assoc]
      _ = inv cIJ ≫ incl ≫ (derivedSectionsWithSupportInAugmentation.{u, u} A
            (PrimeSpectrum.zeroLocus (J : Set A))).app K := by rw [hcJ]
      _ = inv cIJ ≫ cIJ ≫ εIJ := by rw [hcIJ]; exact congrArg (inv cIJ ≫ ·) hinc
      _ = εIJ := IsIso.inv_hom_id_assoc _ _
  have hWJ : Dualizing.derivedPowerTorsionProperty A (I + J) hIJ
      ((Dualizing.derivedPowerTorsionProperty A J hJ).ι.obj
        ((Dualizing.localCohomologyFunctor A J hJ).obj K)) :=
    Dualizing.localCohomology_comp_torsion A I J hI hJ ⟨K, hK⟩
  obtain ⟨γ, hγ⟩ := (bijective_comp_localCohomologyCounit.{u, u} (I + J) hIJ K _ hWJ).2 εJ
  have hγ' : γ ≫ εIJ = εJ := hγ
  have key : ∀ (L : Ideal A) (hL : L.FG)
      (ε : (Dualizing.localCohomologyFunctor A L hL ⋙
        (Dualizing.derivedPowerTorsionProperty A L hL).ι).obj K ⟶ K)
      (hε : ε = (Dualizing.localCohomologyAdjunction.{u, u} A L hL).counit.app K)
      (f : _ ⟶ _), f ≫ ε = ε → f = 𝟙 _ :=
    fun L hL ε hε f hf =>
      (bijective_comp_localCohomologyCounit.{u, u} L hL K _
        ((Dualizing.localCohomologyFunctor A L hL).obj K).property).1
        ((hε ▸ hf).trans (Category.id_comp _).symm)
  have hγβ : γ ≫ β = 𝟙 _ := key J hJ εJ rfl _ (by rw [Category.assoc, hβ, hγ'])
  have hβγ : β ≫ γ = 𝟙 _ := key (I + J) hIJ εIJ rfl _ (by rw [Category.assoc, hγ', hβ])
  have : IsIso β := ⟨γ, hβγ, hγβ⟩
  have hincl : incl = cIJ ≫ β ≫ inv cJ := by
    simp only [β, Category.assoc, IsIso.hom_inv_id, Category.comp_id, IsIso.hom_inv_id_assoc]
  show IsIso incl
  rw [hincl]
  infer_instance

variable (A) in
/-- The isomorphism `{H^k_{V(I + J)}(M/IⁿM)} ≅ {H^k_{V(J)}(M/IⁿM)}` of towers induced by the
inclusion of supports `V(I + J) ⊆ V(J)`. -/
def localCohomologyAdicTowerAddIso (I J : Ideal A) (k : ℤ) (M : ModuleCat.{u} A) :
    localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus ((I + J : Ideal A) : Set A)) I k M ≅
      localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I k M :=
  let τ : localCohomologyAdicTower.{u, u} A
        (PrimeSpectrum.zeroLocus ((I + J : Ideal A) : Set A)) I k M ⟶
      localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I k M :=
    Functor.whiskerRight (Functor.whiskerLeft
      (idealPowerQuotientTower.{u, u} I M ⋙ DerivedCategory.singleFunctor (ModuleCat.{u} A) 0)
      (derivedSectionsWithSupportInInclusion.{u, u} A (zeroLocus_add_subset_right I J)))
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k)
  have : IsIso τ := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n => ?_
    have h := isIso_derivedSectionsWithSupportInInclusion_app_of_torsion I J
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((idealPowerQuotientTower.{u, u} I M).obj n))
      (Dualizing.PowerTorsionBaseChange.derivedPowerTorsionProperty_singleFunctor I
        I.fg_of_isNoetherianRing _ fun m => ⟨n.unop + 1, Nat.succ_pos _, fun a ha =>
          congrArg (fun f => (ModuleCat.Hom.hom f) m)
            (smul_id_idealPowerQuotientTower_eq_zero.{u, u} I M n
              (Ideal.pow_le_pow_right (Nat.le_succ _) ha))⟩)
    exact (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map_isIso
      ((derivedSectionsWithSupportInInclusion.{u, u} A (zeroLocus_add_subset_right I J)).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((idealPowerQuotientTower.{u, u} I M).obj n)))
  asIso τ

/-- Under `Stacks.LocalCohomology.localCohomologyAdicTowerAddIso`, the projection
`H^k_{V(I + J)}(M) ⟶ H^k_{V(I + J)}(M/IⁿM)` is carried to the projection
`H^k_{V(J)}(M) ⟶ H^k_{V(J)}(M/IⁿM)` preceded by the change of support at `M`. -/
theorem localCohomologyAdicCone_π_comp_localCohomologyAdicTowerAddIso_hom (I J : Ideal A) (k : ℤ)
    (M : ModuleCat.{u} A) (n : ℕᵒᵖ) :
    (localCohomologyAdicCone.{u, u} A (PrimeSpectrum.zeroLocus ((I + J : Ideal A) : Set A))
        I k M).π.app n ≫ (localCohomologyAdicTowerAddIso A I J k M).hom.app n =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map
          ((derivedSectionsWithSupportInInclusion.{u, u} A (zeroLocus_add_subset_right I J)).app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≫
        (localCohomologyAdicCone.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I k M).π.app n := by
  show (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map _ ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map _ =
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map _ ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map _
  exact ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map_comp _ _).symm.trans
    ((congrArg (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map
      ((derivedSectionsWithSupportInInclusion.{u, u} A (zeroLocus_add_subset_right I J)).naturality
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
          ((idealPowerQuotientCone.{u, u} I M).π.app n)))).trans
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) k).map_comp _ _))

omit [IsNoetherianRing A] in
/-- If `V(J) ∩ V(I) = V(J') ∩ V(I)` then `V(I + J) = V(I + J')`. -/
theorem zeroLocus_add_eq_of_zeroLocus_inter_eq {I J J' : Ideal A}
    (h : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A)) :
    PrimeSpectrum.zeroLocus ((I + J : Ideal A) : Set A) =
      PrimeSpectrum.zeroLocus ((I + J' : Ideal A) : Set A) := by
  rw [Ideal.add_eq_sup, Ideal.add_eq_sup, PrimeSpectrum.zeroLocus_sup,
    PrimeSpectrum.zeroLocus_sup, Set.inter_comm, h, Set.inter_comm]

variable (A) in
/-- The isomorphism `{H^k_{V(J)}(M/IⁿM)} ≅ {H^k_{V(J')}(M/IⁿM)}` of towers when
`V(J) ∩ V(I) = V(J') ∩ V(I)`, through `{H^k_{V(I + J)}(M/IⁿM)} = {H^k_{V(I + J')}(M/IⁿM)}`. -/
def localCohomologyAdicTowerIsoOfZeroLocusInter {I J J' : Ideal A}
    (h : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (k : ℤ) (M : ModuleCat.{u} A) :
    localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I k M ≅
      localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus (J' : Set A)) I k M :=
  (localCohomologyAdicTowerAddIso A I J k M).symm ≪≫
    eqToIso (congrArg (fun T => localCohomologyAdicTower.{u, u} A T I k M)
      (zeroLocus_add_eq_of_zeroLocus_inter_eq h)) ≪≫
    localCohomologyAdicTowerAddIso A I J' k M

/-- If `V(J) ∩ V(I) = V(J') ∩ V(I)` and the tower `{H^k_{V(J')}(M/IⁿM)}` is Mittag-Leffler, so is
`{H^k_{V(J)}(M/IⁿM)}`. -/
theorem isMittagLefflerCategorical_localCohomologyAdicTower_of_zeroLocus_inter {I J J' : Ideal A}
    (h : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (J' : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A))
    (k : ℤ) (M : ModuleCat.{u} A)
    (hML : IsMittagLefflerCategorical
      (localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus (J' : Set A)) I k M)) :
    IsMittagLefflerCategorical
      (localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) I k M) :=
  hML.of_natIso (localCohomologyAdicTowerIsoOfZeroLocusInter A h k M)

/-! ### The limit cones of Stacks 0EG0 at an admissible shrinking -/

/-- Stacks 0EG0 in cone form at an admissible shrinking of the ideal of Stacks 0EFL. Let `A` be
Noetherian, `I ⊆ 𝔞` ideals, `M` a finite `A`-module and `J₀` an ideal as in the conclusion of
Stacks 0EFL for `M`, `𝔞` and `t`. Let `J ⊆ J₀` with `V(J) ∩ V(I) = V(𝔞)` and `i ≤ t`, and assume
the tower `{H^{i-1}_{V(𝔞)}(M/IⁿM)}` is Mittag-Leffler. Then the cone
`Hⁱ_{V(J)}(M) ⟶ Hⁱ_{V(J)}(M/IⁿM)` given by the quotient maps is a limit cone. -/
theorem nonempty_isLimit_localCohomologyAdicCone_of_isAlgebraizationIdeal {I a : Ideal A}
    (hIa : I ≤ a) (M : ModuleCat.{u} A) [Module.Finite A M] (t : ℤ) (J₀ : Ideal A)
    (h : Stacks.Algebraization.IsAlgebraizationIdeal (M := M) I a t J₀) (J : Ideal A)
    (hJ : J ≤ J₀)
    (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A))
    (i : ℤ) (hi : i ≤ t)
    (hML : IsMittagLefflerCategorical
      (localCohomologyAdicTower.{u, u} A (PrimeSpectrum.zeroLocus (a : Set A)) I (i - 1) M)) :
    Nonempty (IsLimit (localCohomologyAdicCone.{u, u} A
      (PrimeSpectrum.zeroLocus (J : Set A)) I i M)) := by
  have hI : I.FG := I.fg_of_isNoetherianRing
  have hJfg : J.FG := J.fg_of_isNoetherianRing
  have haI : PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) :=
    Set.inter_eq_left.2 (PrimeSpectrum.zeroLocus_anti_mono (SetLike.coe_subset_coe.2 hIa))
  have hV' : PrimeSpectrum.zeroLocus (J : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) =
      PrimeSpectrum.zeroLocus (a : Set A) ∩ PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [hV, haI]
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let G := localCohomologyDerived A J hJfg
  let X := G.obj (S.obj M)
  let un : X ⟶ Dualizing.completedLocalCohomology A I J hI hJfg M :=
    (Dualizing.derivedCompletionReflection A I hI).2.unit.app X
  have hun : IsIso (H.map un) := by
    have h0 := h.isIso J hJ hV' i hi
    have e := H.map_comp un
      (Stacks.Algebraization.completedLocalCohomologyShrinkIso A I a J hI
        a.fg_of_isNoetherianRing hJfg (ModuleCat.of A M) hV').hom
    exact (isIso_comp_right_iff _ _).mp (Eq.mp (congrArg IsIso e) h0)
  let p := Dualizing.completedLocalCohomologyProjection A I J hI hJfg M
  have hp :=
    Dualizing.isDerivedLimitWithProjections_completedLocalCohomologyProjection_of_finite A I J hI
      hJfg M
  have hpunit := Dualizing.completedLocalCohomologyUnit_comp_projection A I J hI hJfg M
  let F := Dualizing.adicQuotientLocalCohomologySystem A I J hJfg M
  let Φ := S ⋙ G ⋙ H
  let Φ' := S ⋙ G ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i - 1)
  have hcmp : IsIso (compareSectionsWithSupportLocalCohomology.{u, u} A J hJfg) :=
    isIso_compareSectionsWithSupportLocalCohomology.{u, u} A J hJfg
  let β : ∀ k : ℤ, S ⋙ G ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) k ≅
      localCohomologyWithSupportInModuleFunctor.{u, u} A (PrimeSpectrum.zeroLocus (J : Set A)) k :=
    fun k => Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (asIso (compareSectionsWithSupportLocalCohomology.{u, u} A J hJfg)).symm
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) k))
  let eT : idealPowerQuotientTower.{u, u} I M ⋙ Φ ≅ F ⋙ H :=
    Functor.isoWhiskerRight (Stacks.Algebraization.idealPowerQuotientTowerIso I M) Φ
  have hML' : IsMittagLefflerCategorical
      (F ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i - 1)) :=
    (isMittagLefflerCategorical_localCohomologyAdicTower_of_zeroLocus_inter hV' (i - 1) M
      hML).of_natIso <|
        (Functor.isoWhiskerRight (Stacks.Algebraization.idealPowerQuotientTowerIso I M) Φ').symm ≪≫
          Functor.isoWhiskerLeft (idealPowerQuotientTower.{u, u} I M) (β (i - 1))
  obtain ⟨hlimp⟩ := hp.nonempty_isLimit_mapCone_homology i hML'
  let c := (Cone.postcompose eT.hom).obj (Φ.mapCone (idealPowerQuotientCone.{u, u} I M))
  have hc : ∀ n : ℕ, c.π.app (op n) = H.map un ≫ H.map (p n) := by
    intro n
    have h3 : H.map un ≫ H.map (p n) = H.map (G.map (S.map
        (ModuleCat.ofHom (I ^ n • ⊤ : Submodule A M).mkQ))) :=
      (H.map_comp _ _).symm.trans (congrArg H.map (hpunit n))
    refine Eq.trans ?_ h3.symm
    show Φ.map ((idealPowerQuotientCone.{u, u} I M).π.app (op n)) ≫ Φ.map (𝟙 _) = _
    rw [Φ.map_id, Category.comp_id]
    rfl
  let ec : (H.mapCone hp.cone) ≅ c :=
    Cone.ext (asIso (H.map un)).symm (fun n => by
      induction n using Opposite.rec with
      | op n =>
        show H.map (p n) = inv (H.map un) ≫ c.π.app (op n)
        rw [hc n, IsIso.inv_hom_id_assoc])
  exact ⟨IsLimit.mapConeEquiv (β i)
    ((IsLimit.postcomposeHomEquiv eT (Φ.mapCone (idealPowerQuotientCone.{u, u} I M))).1
      (hlimp.ofIsoLimit ec))⟩

end Stacks.LocalCohomology

end
