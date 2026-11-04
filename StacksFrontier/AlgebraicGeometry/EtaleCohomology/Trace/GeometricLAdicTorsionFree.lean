module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportVanishingReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicIsogeny
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` through the torsion-free model of `F`

An isogeny `F ⟶ G ⟶ F` of ℓ-adic sheaves induces an isomorphism
`Hⁱ_c(X_k̄, F ⊗ Q_ℓ) ≅ Hⁱ_c(X_k̄, G ⊗ Q_ℓ)` commuting with every endomorphism of `RΓ_c(X_k̄, -)`,
in particular with `π_X^*`. Applied to the torsion-free model `ℓᴺ F` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.TorsionFreeModel`, whose levels are
flat once `N` is beyond the torsion bound, this gives the finiteness, the finite support and the
trace formula for `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` of an arbitrary ℓ-adic sheaf `F`, under the sole hypothesis
that the complexes `RΓ_c(X_k̄, F'ₙ)` of the levels of the model are perfect.

## Main results

* `LAdicSheaf.powExact_etaleLevel_torsionFreeModel`: the levels of the model, read on Mathlib's
  small étale site, are flat.
* `LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso`: the isomorphism
  `Hⁱ_c(X_k̄, F ⊗ Q_ℓ) ≅ Hⁱ_c(X_k̄, G ⊗ Q_ℓ)` induced by an isogeny.
* `LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback`: this
  isomorphism commutes with the endomorphisms of `RΓ_c(X_k̄, -)`.
* `LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_perfect`:
  `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is finite-dimensional.
* `LAdicSheaf.finite_nontrivial_rationalGeometricCompactlySupportedCohomology_of_perfect`:
  `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes in all but finitely many degrees.
* `LAdicSheaf.alternating_trace_rationalGeometricCompactlySupportedFrobenius_of_perfect`: the
  alternating trace of `π_X^*` is the ℓ-adic trace of the tower `RΓ_c(X_k̄, F'ₙ)`.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-- **The levels of the torsion-free model are flat**, read on Mathlib's small étale site. -/
theorem LAdicSheaf.powExact_etaleLevel_torsionFreeModel (F : LAdicSheaf B X ℓ) {N : ℕ}
    (hN : LAdicSheaf.torsionBound F ≤ N) (n : ℕ) :
    PowExact ℓ (n + 1) (LAdicSheaf.etaleLevel B X ℓ (LAdicSheaf.torsionFreeModel F N) n) := by
  let e := SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  exact (LAdicSheaf.powExact_torsionFreeModel_level F hN n).map e.functor
    (zmodSheaf_nsmul_id (SmallEtale.topology B X.1 X.property) (ℓ ^ (n + 1)) _)

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The isomorphism `Hⁱ_c(X_k̄, F ⊗ Q_ℓ) ≅ Hⁱ_c(X_k̄, G ⊗ Q_ℓ)` induced by an isogeny** `φ`, `ψ`
with `φ ≫ ψ` and `ψ ≫ φ` multiplication by `ℓᴺ`. -/
def LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso {F G : LAdicSheaf B X ℓ}
    (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F) (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G)
    (i : ℤ) :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G i :=
  @asIso _ _ _ _ ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
    (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i))
    (LAdicSheaf.isIso_rationalGeometricCompactlySupportedCohomologyMap f j kbar φ ψ N h₁ h₂ i)

/-- The forward map of `LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso` is the
map induced by `φ` on `Hⁱ_c(X_k̄, -)`, extended to `Q_ℓ`. -/
theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (i : ℤ) :
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁ h₂
        i).hom = (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap f j kbar φ i) := rfl

/-- The isomorphism induced by an isogeny commutes with every endomorphism of `RΓ_c(X_k̄, -)`, in
particular with `π_X^*`. -/
theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (i : ℤ)
    (θ : compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⟶
      compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar) :
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N h₁ h₂
        i).hom ≫
        LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar G i θ =
      LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i θ ≫
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
          h₁ h₂ i).hom :=
  ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map_comp _ _).symm.trans
    ((congrArg (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
      (LAdicSheaf.geometricCompactlySupportedCohomologyMap_pullback f j kbar φ i θ)).trans
      ((ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map_comp _ _))

/-- **Traces are invariant under isogeny**: the trace of an endomorphism of `RΓ_c(X_k̄, -)` on
`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is its trace on `Hⁱ_c(X_k̄, G ⊗ Q_ℓ)`. -/
theorem LAdicSheaf.trace_rationalGeometricCompactlySupportedCohomologyPullback_of_isogeny
    {F G : LAdicSheaf B X ℓ} (φ : F ⟶ G) (ψ : G ⟶ F) (N : ℕ) (h₁ : φ ≫ ψ = (ℓ ^ N) • 𝟙 F)
    (h₂ : ψ ≫ φ = (ℓ ^ N) • 𝟙 G) (i : ℤ)
    (θ : compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⟶
      compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar) :
    LinearMap.trace ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
          θ).hom =
      LinearMap.trace ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar G i)
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar G i
          θ).hom := by
  let e := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar φ ψ N
    h₁ h₂ i
  have h : LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar G i θ =
      e.inv ≫
        LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i θ ≫
          e.hom :=
    (Iso.eq_inv_comp e).2
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso_hom_pullback B X ℓ f j
        kbar φ ψ N h₁ h₂ i θ)
  have hc : (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar G i
      θ).hom = e.toLinearEquiv.conj
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
          θ).hom := by
    rw [h, LinearEquiv.conj_apply]
    rfl
  rw [hc, LinearMap.trace_conj']

/-- The isomorphism `Hⁱ_c(X_k̄, F ⊗ Q_ℓ) ≅ Hⁱ_c(X_k̄, F' ⊗ Q_ℓ)` for the torsion-free model `F'`. -/
private def torsionFreeModelIsogenyIso (F : LAdicSheaf B X ℓ) (i : ℤ) :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar
        (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) i :=
  LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIsogenyIso B X ℓ f j kbar
    (LAdicSheaf.toTorsionFreeModel F (LAdicSheaf.torsionBound F))
    (LAdicSheaf.fromTorsionFreeModel F (LAdicSheaf.torsionBound F)) (LAdicSheaf.torsionBound F)
    (LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel F (LAdicSheaf.torsionBound F))
    (LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel F (LAdicSheaf.torsionBound F)) i

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is finite-dimensional** for an ℓ-adic sheaf whose torsion-free model
has perfect `RΓ_c(X_k̄, F'ₙ)`. -/
@[sga "4½ Rapport 4.11" "partial"]
theorem LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_perfect
    (F : LAdicSheaf B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ
          (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) n)))) (i : ℤ) :
    Module.Finite ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  have := LAdicSheaf.finite_rationalGeometricCompactlySupportedCohomology_of_flat B X ℓ f j kbar p q
    hcard (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F))
    (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F (le_refl (LAdicSheaf.torsionBound F)))
    hP i
  exact Module.Finite.equiv
    (torsionFreeModelIsogenyIso B X ℓ f j kbar F i).symm.toLinearEquiv

include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes in all but finitely many degrees** for an ℓ-adic sheaf whose
torsion-free model has perfect `RΓ_c(X_k̄, F'ₙ)`. -/
theorem LAdicSheaf.finite_nontrivial_rationalGeometricCompactlySupportedCohomology_of_perfect
    (F : LAdicSheaf B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ
          (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) n)))) :
    {i : ℤ | Nontrivial
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)}.Finite := by
  refine (LAdicSheaf.finite_nontrivial_rationalGeometricCompactlySupportedCohomology_of_flat B X ℓ
    f j kbar p q hcard (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F))
    (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F (le_refl (LAdicSheaf.torsionBound F)))
    hP).subset fun i hi => ?_
  exact @Equiv.nontrivial _ _
    (torsionFreeModelIsogenyIso B X ℓ f j kbar F i).symm.toLinearEquiv.toEquiv hi

/-- **The alternating trace of `π_X^*` on `Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` is the ℓ-adic trace of the tower
`Kₙ = RΓ_c(X_k̄, F'ₙ)` of the torsion-free model**, whenever the `Kₙ` are perfect. -/
theorem LAdicSheaf.alternating_trace_rationalGeometricCompactlySupportedFrobenius_of_perfect
    (F : LAdicSheaf B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ
          (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) n)))) :
    ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyPullback B X ℓ f j kbar F i
            (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] f j kbar p q hcard)).hom =
      (padicTrace (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard
        (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F))
        (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F
          (le_refl (LAdicSheaf.torsionBound F))) hP) : ℚ_[ℓ]) := by
  rw [← LAdicSheaf.alternating_trace_rationalGeometricCompactlySupportedFrobenius_of_flat]
  refine finsum_congr fun i => ?_
  rw [LAdicSheaf.trace_rationalGeometricCompactlySupportedCohomologyPullback_of_isogeny B X ℓ f j
    kbar (LAdicSheaf.toTorsionFreeModel F (LAdicSheaf.torsionBound F))
      (LAdicSheaf.fromTorsionFreeModel F (LAdicSheaf.torsionBound F)) (LAdicSheaf.torsionBound F)
    (LAdicSheaf.toTorsionFreeModel_comp_fromTorsionFreeModel F (LAdicSheaf.torsionBound F))
    (LAdicSheaf.fromTorsionFreeModel_comp_toTorsionFreeModel F (LAdicSheaf.torsionBound F))]

/-! ### From the cohomology of the reductions modulo `ℓ` of the levels of the model

The two inputs on the reductions `Gₙ = (j_! F'ₙ)|_{X̄_k̄} / ℓ` of the levels of the torsion-free
model, on the proper scheme `X̄_k̄`: finiteness of `Hⁱ(X̄_k̄, Gₙ)` (the finiteness theorem for
proper schemes over a separably closed field, Tag 03SC (5) for curves), and its vanishing above
`b` (Tag 095U, with `b = 2 dim X`). -/

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- **`RΓ_c(X_k̄, F'ₙ)` is perfect** for the levels `F'ₙ` of the torsion-free model, as soon as the
reductions modulo `ℓ` have finite cohomology on `X̄_k̄` vanishing above some `b`. -/
theorem LAdicSheaf.isPerfect_levelComplex_torsionFreeModel [Finite k] (F : LAdicSheaf B X ℓ)
    (b : ℤ)
    (hb : (∀ n i, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod ℓ)) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (ZMod ℓ) ((etaleModuleCoextendScalars (torsionCoeff ℓ (n + 1)) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) n))))))))
    (hf : (∀ n i, Module.Finite (ZMod ℓ)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod ℓ)) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (ZMod ℓ) ((etaleModuleCoextendScalars (torsionCoeff ℓ (n + 1)) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) n)))))))) (n : ℕ) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ
          (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) n))) := by
  have := Fintype.ofFinite k
  exact isPerfect_compactSupportFrobeniusCohomology_single_of_reduction f j kbar ℓ (n + 1) _
    (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F (le_refl _) n) b (hb n) (hf n)

include p q hcard in
/-- **`Hⁱ_c(X_k̄, F ⊗ Q_ℓ)` vanishes above `b`** as soon as the reductions modulo `ℓ` of the levels
of the torsion-free model have finite cohomology on `X̄_k̄` vanishing above `b`. -/
theorem LAdicSheaf.isZero_rationalGeometricCompactlySupportedCohomology_of_reduction
    (F : LAdicSheaf B X ℓ) (b : ℤ)
    (hb : (∀ n i, b < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod ℓ)) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (ZMod ℓ) ((etaleModuleCoextendScalars (torsionCoeff ℓ (n + 1)) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) n))))))))
    (hf : (∀ n i, Module.Finite (ZMod ℓ)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ZMod ℓ)) i).obj
      (derivedDirectImageSections (pullback.snd (Over.mk j.toBase).hom (specAlgebraMap k kbar))
        (ZMod ℓ) ((etaleModuleCoextendScalars (torsionCoeff ℓ (n + 1)) _).obj
          ((etaleModuleInverseImage.{u, 0} _ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
            ((etaleModuleExtensionByZero.{u, 0} _ j.immersion).obj
              (LAdicSheaf.etaleLevel B X ℓ
                (LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)) n))))))))
    (i : ℤ) (hi : b < i) :
    IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) := by
  let M := LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)
  have hM := LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F
    (le_refl (LAdicSheaf.torsionBound F))
  have hP := LAdicSheaf.isPerfect_levelComplex_torsionFreeModel B X ℓ f j kbar F b hb hf
  have hlev : ∀ n : ℕ, IsZero
      ((LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ f j kbar M i).obj
        (Opposite.op n)) := fun n => by
    have h := isZero_homology_compactSupportFrobeniusCohomology_single_of_reduction f j kbar ℓ
      (n + 1) (LAdicSheaf.etaleLevel B X ℓ M n) (hM n) b (hb n) i hi
    have hs := ModuleCat.subsingleton_of_isZero h
    have h' : IsZero ((levelCohomologySystem
        (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard M hM hP) i).obj
          (Opposite.op n)) := @ModuleCat.isZero_of_subsingleton _ _ _ hs
    exact h'.of_iso (LAdicSheaf.geometricLevelCohomologyIso B X ℓ f j kbar p q hcard M hM hP i n)
  have hlim : IsZero (LAdicSheaf.geometricCompactlySupportedCohomology B X ℓ f j kbar M i) := by
    rw [IsZero.iff_id_eq_zero]
    exact limit.hom_ext fun n => (hlev n.unop).eq_of_tgt _ _
  have hrat :
      IsZero (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar M i) :=
    (ModuleCat.extendScalars.{0, 0, u + 1} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map_isZero hlim
  exact hrat.of_iso (torsionFreeModelIsogenyIso B X ℓ f j kbar F i)

end Stacks.EtaleCohomology
