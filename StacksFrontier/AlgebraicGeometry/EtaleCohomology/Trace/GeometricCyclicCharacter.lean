module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricRepresentationComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveFirstCohomologyOrder
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SelfMapCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantModuleCohomology
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.TrivialDegreeOneHom

/-!
# Cyclic quotients of the geometric fundamental group of a curve of positive genus

Let `X` be a quasi-compact quasi-separated connected scheme over `k`, `K` an algebraic closure of
`k`, and suppose `X_K` is a smooth proper connected curve of genus `≥ 1`. For `ℓ` invertible in
`K` and every `j`, the fundamental group `π₁(X_K, y)` has a continuous surjection onto `ℤ/ℓ^j`.

`H¹(X_K, ℤ/ℓ^j)` has a class of order `ℓ^j`
(`Stacks.EtaleCohomology.exists_sheafH_one_etaleConstantSheaf_dvd_of_nsmul_eq_zero`). It is
`H¹(X_K, ℱ_{ℤ/ℓ^j})` for the trivial representation (Tag 03VL's `ℱ_{triv} = ` constant), which the
comparison `H¹(π₁(X_K), M) ≅ H¹(X_K, ℱ_M)`
(`AlgebraicGeometry.bijective_geometricComparison_app_one`) identifies with group cohomology; a
class of maximal order in `H¹(π₁(X_K), ℤ/ℓ^j)` with trivial coefficients is a surjective
homomorphism with open kernel
(`Stacks.ContinuousCohomology.exists_surjective_hom_of_trivial_of_degreeOne`).

## Main results

* `AlgebraicGeometry.geometricRepresentationCohomologyOneTrivialAddEquiv` —
  `H¹(X_K, ℱ_{ℤ/N}) ≃ H¹(X_K, ℤ/N)` for the trivial representation.
* `AlgebraicGeometry.exists_surjective_geometricFundamentalGroup_zmod` — the surjection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology Stacks.ContinuousCohomology
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

/-- Enough injectives for continuous discrete modules at the module universe of the group. -/
local instance (priority := 3000) enoughInjectives_continuousModule_groupUniverse_cyclic (Λ : Type)
    [CommRing Λ] (G : Type (u + 1)) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, u + 1, u + 1} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, u + 1, 0} Λ G

/-- Sheafification of presheaves of `Λ`-modules on the small étale site, pinned at `u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_objectUniverse_cyclic (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at `u + 1`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_objectUniverse_cyclic
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1] {k : Type u} [Field k]
  (f : X.1 ⟶ Spec (.of k)) (K : Type u) [Field K] [Algebra k K]
  (hK : B.Contains (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))
  [ConnectedSpace (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)]
  (y : GeometricPoint (Stacks.Frobenius.fieldBaseChange (Over.mk f) K))

/-- **`H¹(X_K, ℱ_E)` for a trivial representation is `H¹(X_K, ℤ/ℓ^j)`** with `E = ℤ/ℓ^j`. -/
def geometricRepresentationCohomologyOneTrivialAddEquiv (N : ℕ) [NeZero N] :
    ((geometricRepresentationCohomology.{u, 0} B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
        (ZMod N) f K).functor 1).obj
      ((finiteTypeContinuousModuleTrivial (ZMod N)
        (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj
          ⟨ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)), Module.Finite.of_finite⟩) ≃+
      Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
        (ZMod N)) 1 :=
  let i' := pullback.fst (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)
  let E : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} (ZMod N)) :=
    ⟨ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)), Module.Finite.of_finite⟩
  let E' := (ModuleCat.uliftFunctor.{0, u + 1} (ZMod N)).obj E.obj
  let eSh := (etaleModuleInverseImage.{u, 0} (ZMod N) i').mapIso
      ((representationSheafTrivialIsoConstant B X (y.map (fieldBaseChangeObjProj B X f K hK).hom)
        (ZMod N)).app E) ≪≫ (etaleModuleInverseImageConstantIso.{u, 0} (ZMod N) i').app E'
  let eAb : (etaleModuleUnderlyingAbelian (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)
      (ZMod N)).obj ((constantSheaf
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K).smallEtaleTopology
        (ModuleCat.{u + 1} (ZMod N))).obj E') ≅
      etaleConstantSheaf.{u, 0} (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) (ZMod N) :=
    (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1, 0, u + 1, u} (ZMod N) _).app E' ≪≫
      (constantSheaf _ AddCommGrpCat.{u + 1}).mapIso
        (AddEquiv.ulift.trans (AddEquiv.ulift.trans AddEquiv.ulift.symm)).toAddCommGrpIso
  ((forget₂ (ModuleCat.{u + 1} (ZMod N)) AddCommGrpCat.{u + 1}).mapIso
      (((etaleModuleGlobalSections.{u, 0} (ZMod N)
        (Stacks.Frobenius.fieldBaseChange (Over.mk f) K)).rightDerived 1).mapIso eSh) ≪≫
    (etaleModuleCohomologyIsoFunctorH (ZMod N) 1).app _).addCommGroupIsoToAddEquiv.trans
    (sheafHAddEquivOfIso eAb 1)

include hK in
/-- **`π₁(X_K, y)` surjects continuously onto `ℤ/ℓ^j`** when `X_K` is a smooth proper connected
curve of genus `≥ 1` over an algebraic closure `K` of `k` and `ℓ` is invertible in `K`. -/
theorem exists_surjective_geometricFundamentalGroup_zmod [IsAlgClosure k K] [CompactSpace X.1]
    [QuasiSeparatedSpace X.1]
    [IsCurve K (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    [Smooth (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    [IsProper (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K))]
    (hg : 1 ≤ genus (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)))
    (ℓ j : ℕ) [NeZero ℓ] (hℓ : IsUnit (ℓ : K)) :
    ∃ χ : EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y →*
        Multiplicative (ZMod (ℓ ^ j)),
      IsOpen (χ.ker : Set (EtaleFundamentalGroup _ y)) ∧ Function.Surjective χ := by
  have : NeZero (ℓ ^ j) := ⟨pow_ne_zero _ (NeZero.ne ℓ)⟩
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  have := forall_finite_finiteEtaleFiberFunctor_obj y
  have := forall_finite_finiteEtaleFiberFunctor_obj (y.map (fieldBaseChangeObjProj B X f K hK).hom)
  obtain ⟨z₀, hz₀⟩ := exists_sheafH_one_etaleConstantSheaf_dvd_of_nsmul_eq_zero
    (pullback.snd (Over.mk f).hom (Stacks.Frobenius.specAlgebraMap k K)) hg ℓ j hℓ
  let triv := (finiteTypeContinuousModuleTrivial (ZMod (ℓ ^ j))
    (EtaleFundamentalGroup X.1 (y.map (fieldBaseChangeObjProj B X f K hK).hom))).obj
      ⟨ModuleCat.of (ZMod (ℓ ^ j)) (ULift.{u + 1} (ZMod (ℓ ^ j))), Module.Finite.of_finite⟩
  let Ψ := geometricRepresentationCohomologyOneTrivialAddEquiv B X f K hK y (ℓ ^ j)
  let γ := ((geometricComparison B X (ZMod (ℓ ^ j)) f K hK y).app 1).app triv
  have hγ := bijective_geometricComparison_app_one B X (ZMod (ℓ ^ j)) f K hK y triv
  obtain ⟨z₁, hz₁⟩ := hγ.2 (Ψ.symm z₀)
  have hz : ∀ m : ℕ, m • z₁ = 0 → ℓ ^ j ∣ m := by
    intro m hm
    refine hz₀ m (Ψ.symm.injective ?_)
    rw [map_nsmul, map_zero, ← hz₁, ← map_nsmul, hm, map_zero]
  let φ := geometricFundamentalGroupMap B X f K hK y
  let A := (finiteTypeContinuousModuleToRes (ZMod (ℓ ^ j)) φ).obj triv
  have : Finite A.obj.obj.V := inferInstanceAs (Finite (ULift.{u + 1} (ZMod (ℓ ^ j))))
  have hcard : Nat.card A.obj.obj.V = ℓ ^ j := by
    show Nat.card (ULift.{u + 1} (ZMod (ℓ ^ j))) = ℓ ^ j
    rw [Nat.card_ulift, Nat.card_zmod]
  obtain ⟨c, hc, hopen, hsurj⟩ := exists_surjective_hom_of_trivial_of_degreeOne.{0, u + 1, u + 1}
    (ZMod (ℓ ^ j)) A (fun _ _ => rfl) z₁ (fun m hm => by rw [hcard]; exact hz m hm)
  let χ : EtaleFundamentalGroup (Stacks.Frobenius.fieldBaseChange (Over.mk f) K) y →*
      Multiplicative (ZMod (ℓ ^ j)) :=
    { toFun := fun g => Multiplicative.ofAdd (show ULift.{u + 1} (ZMod (ℓ ^ j)) from c g).down
      map_one' := by
        have h := hc 1 1
        rw [mul_one, left_eq_add] at h
        rw [h]
        rfl
      map_mul' := fun g h => by
        rw [hc g h]
        rfl }
  refine ⟨χ, ?_, fun t => ?_⟩
  · convert hopen using 1
    ext g
    show Multiplicative.ofAdd _ = 1 ↔ c g = 0
    rw [ofAdd_eq_one]
    exact ⟨fun h => ULift.ext h, fun h => congrArg ULift.down h⟩
  · obtain ⟨g, hg⟩ := hsurj (show A.obj.obj.V from ULift.up (Multiplicative.toAdd t))
    exact ⟨g, by
      show Multiplicative.ofAdd (show ULift.{u + 1} (ZMod (ℓ ^ j)) from c g).down = t
      rw [hg]
      rfl⟩

end AlgebraicGeometry

end
