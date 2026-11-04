module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperPushforwardTwistTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperBaseChangeQuasiIso

/-!
# The Leray step of the trace formula along a proper morphism, Frobenius-equivariantly

Let `π : W' ⟶ W` be a proper morphism of schemes over a finite field `k`, `k̄` an extension of
`k`, `Λ` a finite commutative ring, and `M` a bounded below complex of injective sheaves of
`Λ`-modules on `W'_étale`, so that `π_* M` computes `Rπ_* M`. Then

`RΓ(W_k̄, (π_* M)|_{W_k̄}) ≅ RΓ(W'_k̄, M|_{W'_k̄})`,

and the canonical geometric Frobenius endomorphisms of the two sides
(`Stacks.EtaleCohomology.frobeniusRestrictionCohomologyEndo`) have the same trace: one side is
perfect exactly when the other is, and then `T''(W, π_* M) = T''(W', M)`.

The identification is Leray, `RΓ(W'_k̄, -) = RΓ(W_k̄, R(π_k̄)_* -)`, together with proper base
change `(Rπ_* M)|_{W_k̄} ≅ R(π_k̄)_*(M|_{W'_k̄})` for the base change along `W_k̄ ⟶ W` ([Stacks,
Tag 0DDE] for sheaves of `Λ`-modules). The base change map carries the Frobenius twist of `W` to
`(π_k̄)_*` of that of `W'`
(`Stacks.EtaleCohomology.etaleModuleBaseChange_comp_frobeniusBaseChangeTwist`), and
`CategoryTheory.Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_baseChange_quasiIso` compares
the two traces on one chain model.

This is the step "`RΓ_c(X) = RΓ_c(Y, Rf_! K)` with Frobenius" of the reduction of the trace
formula of [Stacks, Tag 03V3] in any dimension to dimension one.

Proper base change for sheaves of `Λ`-modules ([Stacks, Tag 0DDE]), read on injective
resolutions (`CategoryTheory.Functor.BaseChangeQuasiIsoAt`), is
`Stacks.EtaleCohomology.quasiIso_etaleModuleBaseChange_comp_of_isProper`.

The standard model `HasDerivedCategory.standard` is used because the traced objects
(`frobeniusRestrictionCohomologyEndo`, `perfectDerivedTrace`) are defined there.

## Main results

All in the namespace `Stacks.EtaleCohomology`:

* `isTorsionPlus_of_finite`: over a finite ring every object is torsion.
* `isPerfect_frobeniusRestriction_directImage_iff_of_isProper`: the Frobenius restriction of
  `π_* M` is perfect if and only if that of `M` is.
* `perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper`: the traces of
  the Frobenius endomorphisms agree, `T''(W, π_* M) = T''(W', M)`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/- The abstract twisted-trace lemmas read the zero morphisms of the categories of sheaves off
their `Abelian` structure; the statements here are elaborated with the same spelling, so that the
kernel compares them without unfolding two presentations of the zero morphisms of a category of
sheaves. -/
attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

section Torsion

variable (Λ : Type) [Ring Λ] [Finite Λ]

/-- **A sheaf of modules over a finite ring is torsion**: every section is killed by `#Λ`. -/
theorem isTorsionEtaleModule_of_finite (X : Scheme.{u}) (F : EtaleModules.{u, 0} Λ X) :
    IsTorsionEtaleModule.{u, 0} Λ X F := by
  intro V x
  have := Fintype.ofFinite Λ
  refine ⟨⊤, X.smallEtaleTopology.top_mem V, fun W g _ => ⟨Nat.card Λ, Nat.card_pos, ?_⟩⟩
  rw [← Nat.cast_smul_eq_nsmul Λ, Nat.card_eq_fintype_card, Nat.cast_card_eq_zero, zero_smul]

/-- **Over a finite ring every bounded below complex is torsion.** -/
theorem isTorsionPlus_of_finite (X : Scheme.{u})
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) : isTorsionPlus.{u, 0} Λ X K :=
  fun _ => isTorsionEtaleModule_of_finite Λ X _

end Torsion

variable (Λ : Type) [Ring Λ] [Finite Λ] {k : Type u} [Field k] [Fintype k]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)
  {W' W : Over (Spec (.of k))} (π : W' ⟶ W) [IsProper π.left]

/-- **Perfectness along a proper morphism over `k`**: `RΓ(W_k̄, (π_* M)|_{W_k̄})` is perfect
exactly when `RΓ(W'_k̄, M|_{W'_k̄})` is, for a bounded below complex of injectives `M`. -/
theorem isPerfect_frobeniusRestriction_directImage_iff_of_isProper
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ W'.left)) [∀ n, Injective (M.obj.X n)] :
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd W.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ W kbar
            ((etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj M))))) ↔
    StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd W'.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ W' kbar M)))) :=
  Functor.isPerfect_iff_of_baseChange_quasiIso_app
    (F₁ := etaleModuleDirectImage.{u, 0} Λ (pullback.snd W.hom (specAlgebraMap k kbar)))
    (F₁' := etaleModuleDirectImage.{u, 0} Λ (pullback.snd W'.hom (specAlgebraMap k kbar)))
    (F₂ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (G := etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap π kbar))
    (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap π kbar)
      (pullback.snd W.hom (specAlgebraMap k kbar)) (pullback.snd W'.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd π kbar).symm)
    (etaleModuleDirectImage.{u, 0} Λ π.left)
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj W kbar))
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj W' kbar))
    (etaleModuleBaseChange Λ π.left (fieldBaseChangeMap π kbar) (fieldBaseChangeProj W kbar)
      (fieldBaseChangeProj W' kbar) (fieldBaseChangeMap_comp_fst π kbar)) M
    (quasiIso_etaleModuleBaseChange_comp_of_isProper Λ π.left
      (isPullback_fieldBaseChangeMap π kbar).flip (fieldBaseChangeMap_comp_fst π kbar) M
      (isTorsionPlus_of_finite Λ _ _))

/-- **The Leray step of the trace formula along a proper morphism over `k`.**  For a proper
morphism `π : W' ⟶ W` over the finite field `k` and a bounded below complex `M` of injective
sheaves of `Λ`-modules on `W'_étale` (so that `π_* M = Rπ_* M`), the trace of the geometric
Frobenius on `RΓ(W_k̄, (π_* M)|_{W_k̄})` is its trace on `RΓ(W'_k̄, M|_{W'_k̄})`:
`T''(W, Rπ_* M) = T''(W', M)`. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ W'.left)) [∀ n, Injective (M.obj.X n)]
    (hW : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd W.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ W kbar
            ((etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj M)))))) :
    perfectDerivedTrace.{0, u + 1} Λ ⟨_, hW⟩ (DerivedCategory.Plus.ι.map
        (frobeniusRestrictionCohomologyEndo.{u, 0} Λ W kbar p q hcard
          ((etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj M))) =
      perfectDerivedTrace.{0, u + 1} Λ
          ⟨_, (isPerfect_frobeniusRestriction_directImage_iff_of_isProper Λ kbar π M).1 hW⟩
        (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ W' kbar p q hcard M)) :=
  Functor.perfectDerivedTrace_derivedTwistEndo_eq_of_baseChange_quasiIso_app (R := Λ)
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange W kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd W.hom (specAlgebraMap k kbar)))
    (etaleModuleDirectImage.{u, 0} Λ (geometricFrobeniusBaseChange W' kbar p q hcard))
    (etaleModuleDirectImage.{u, 0} Λ (pullback.snd W'.hom (specAlgebraMap k kbar)))
    (etaleModuleGlobalSections.{u, 0} Λ (Spec (.of kbar)))
    (etaleModuleDirectImage.{u, 0} Λ (fieldBaseChangeMap π kbar))
    (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange W kbar p q hcard)
      (pullback.snd W.hom (specAlgebraMap k kbar)) (pullback.snd W.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase W kbar p q hcard).symm)
    (etaleModuleDirectImageComp.{u, 0} Λ (geometricFrobeniusBaseChange W' kbar p q hcard)
      (pullback.snd W'.hom (specAlgebraMap k kbar)) (pullback.snd W'.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_toBase W' kbar p q hcard).symm)
    (etaleModuleDirectImageComp.{u, 0} Λ (fieldBaseChangeMap π kbar)
      (pullback.snd W.hom (specAlgebraMap k kbar)) (pullback.snd W'.hom (specAlgebraMap k kbar))
      (fieldBaseChangeMap_comp_snd π kbar).symm)
    (directImageTwistTransfer Λ (fieldBaseChangeMap π kbar)
      (geometricFrobeniusBaseChange W' kbar p q hcard)
      (geometricFrobeniusBaseChange W kbar p q hcard)
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap π p q hcard kbar))
    (directImageTwistTransfer_compat Λ (fieldBaseChangeMap π kbar)
      (geometricFrobeniusBaseChange W' kbar p q hcard)
      (geometricFrobeniusBaseChange W kbar p q hcard)
      (pullback.snd W.hom (specAlgebraMap k kbar)) (pullback.snd W'.hom (specAlgebraMap k kbar))
      (geometricFrobeniusBaseChange_comp_fieldBaseChangeMap π p q hcard kbar)
      (fieldBaseChangeMap_comp_snd π kbar).symm
      (geometricFrobeniusBaseChange_comp_toBase W kbar p q hcard).symm
      (geometricFrobeniusBaseChange_comp_toBase W' kbar p q hcard).symm)
    (etaleModuleDirectImage.{u, 0} Λ π.left)
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj W kbar))
    (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj W' kbar))
    (etaleModuleBaseChange Λ π.left (fieldBaseChangeMap π kbar) (fieldBaseChangeProj W kbar)
      (fieldBaseChangeProj W' kbar) (fieldBaseChangeMap_comp_fst π kbar))
    (frobeniusBaseChangeTwist.{u, 0} Λ W kbar p q hcard)
    (frobeniusBaseChangeTwist.{u, 0} Λ W' kbar p q hcard)
    (etaleModuleBaseChange_comp_frobeniusBaseChangeTwist Λ π p q hcard kbar) M
    (quasiIso_etaleModuleBaseChange_comp_of_isProper Λ π.left
      (isPullback_fieldBaseChangeMap π kbar).flip (fieldBaseChangeMap_comp_fst π kbar) M
      (isTorsionPlus_of_finite Λ _ _)) hW _

end Stacks.EtaleCohomology

end
