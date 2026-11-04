module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.Homology.HomComplex.Basic

/-!
# Deriving the torsion functor: the objects involved

Fix a commutative ring `R` and an ideal `I`. This module introduces the complexes and direct
systems used to compute local cohomology with support in `I`: the termwise `I`-power-torsion
subcomplex of a chosen K-injective representative, and the system of derived Hom objects (and of
Ext modules) coming from the quotients `R / I ^ n`.

## Main definitions

* `Dualizing.powerTorsionSubmodule` — the submodule of elements killed by a power of `I`.
* `Dualizing.powerTorsionComplex` — the same construction applied termwise to a complex.
* `Dualizing.kInjectiveRepresentative`, `Dualizing.kInjectiveRepresentativeIso` — a chosen
  K-injective complex representing an object of the derived category, and the isomorphism
  witnessing that it does.
* `Dualizing.localCohomology` — local cohomology of an arbitrary derived object.
* `Dualizing.quotientSingle`, `Dualizing.quotientPowerSucc` — the single complex on `R / I ^ n`
  and the transition maps between these quotients.
* `Dualizing.derivedHomPowers`, `Dualizing.derivedHomPowersOf` — the system
  `n ↦ RHom_R(R / I ^ n, -)`.
* `Dualizing.extPowers` — the direct system of the corresponding Ext modules.

## Implementation notes

A K-injective representative is chosen for each `K ∈ D(R)`, so that `RHom(R / I ^ n, K)` is
represented by the ordinary Hom complex into that representative and `RΓ_I(K)` by its termwise
subcomplex of elements killed by some power of `I`. The Ext groups live one universe above the
cohomology objects in the standard unbounded derived category, which is why `extPowers` takes
values in `ModuleCat.{u + 1} R`.

## References

* [Stacks Project, Tag 0954](https://stacks.math.columbia.edu/tag/0954)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable (R : Type u) [CommRing R]

/-- The submodule of elements annihilated by some power of `I`. -/
def powerTorsionSubmodule (I : Ideal R) (M : Type u) [AddCommGroup M] [Module R M] :
    Submodule R M :=
  ⨆ n : ℕ, Submodule.torsionBySet R M ↑(I ^ n)

/-- The termwise `I`-power-torsion subcomplex of a complex of `R`-modules. -/
noncomputable def powerTorsionComplex (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} R) ℤ where
  X n := ModuleCat.of R (powerTorsionSubmodule R I (J.X n))
  d i j := ModuleCat.ofHom ((J.d i j).hom.restrict fun x hx ↦ by
    refine Submodule.iSup_induction _ (motive := fun y ↦
      (J.d i j).hom y ∈ powerTorsionSubmodule R I (J.X j)) hx ?_
      (by simp) ?_
    · intro n x hx
      apply Submodule.mem_iSup_of_mem n
      rw [Submodule.mem_torsionBySet_iff] at hx ⊢
      intro a
      rw [← (J.d i j).hom.map_smul, hx a, map_zero]
    · intro x y hx hy
      simpa using Submodule.add_mem _ hx hy)
  shape i j hij := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (J.d i j).hom x.1 = 0
    rw [J.shape i j hij]
    rfl
  d_comp_d' i j k hij hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change ((J.d i j ≫ J.d j k).hom : J.X i → J.X k) x.1 = 0
    rw [J.d_comp_d]
    rfl

/-- A chosen K-injective complex representing `K`. -/
noncomputable def kInjectiveRepresentative
    (K : DerivedCategory (ModuleCat.{u} R)) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (Stacks.Injectives.kInjectiveResolutionFunctor (ModuleCat.{u} R)).obj
    (DerivedCategory.Q.objPreimage K)

/-- The chosen representative of `K` is K-injective. -/
noncomputable instance kInjectiveRepresentative_isKInjective
    (K : DerivedCategory (ModuleCat.{u} R)) :
    (kInjectiveRepresentative R K).IsKInjective := by
  dsimp [kInjectiveRepresentative]
  infer_instance

/-- The chosen K-injective complex indeed represents `K`. -/
noncomputable def kInjectiveRepresentativeIso (K : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory.Q.obj (kInjectiveRepresentative R K) ≅ K :=
  (asIso (DerivedCategory.Q.map
      ((Stacks.Injectives.kInjectiveResolutionInclusion (ModuleCat.{u} R)).app
        (DerivedCategory.Q.objPreimage K)))).symm ≪≫
    DerivedCategory.Q.objObjPreimageIso K

/-- Local cohomology of an arbitrary derived object, computed using a chosen K-injective
representative and termwise `I`-power torsion. -/
noncomputable def localCohomology (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R)) : DerivedCategory (ModuleCat.{u} R) :=
  DerivedCategory.Q.obj (powerTorsionComplex R I (kInjectiveRepresentative R K))

/-- The single complex on `R/I^n`, in degree zero. -/
noncomputable abbrev quotientSingle (I : Ideal R) (n : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (R ⧸ I ^ n))

/-- The quotient map `R/I^(n+1) → R/I^n`, regarded as an `R`-linear map. -/
noncomputable def quotientPowerSucc (I : Ideal R) (n : ℕ) :
    ModuleCat.of R (R ⧸ I ^ (n + 1)) ⟶ ModuleCat.of R (R ⧸ I ^ n) :=
  ModuleCat.ofHom
    { toFun := Ideal.Quotient.factorPowSucc I n
      map_add' := map_add _
      map_smul' := by
        intro r x
        change Ideal.Quotient.factorPowSucc I n
            (Ideal.Quotient.mk (I ^ (n + 1)) r * x) =
          Ideal.Quotient.mk (I ^ n) r * Ideal.Quotient.factorPowSucc I n x
        rw [map_mul, Ideal.Quotient.factor_mk] }

/-- The system `n ↦ RHom_R(R/I^n,J)`, computed on a K-injective complex `J`. -/
noncomputable def derivedHomPowers (I : Ideal R)
    (J : CochainComplex (ModuleCat.{u} R) ℤ) : ℕ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  Functor.ofSequence (X := fun n ↦ DerivedCategory.Q.obj
      (CochainComplex.HomComplexR R (quotientSingle R I n) J))
    (fun n ↦ DerivedCategory.Q.map (Stacks.HomComplex.TensorHomMap.precomp R
      (quotientSingle R I (n + 1)) (quotientSingle R I n) J
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map
        (quotientPowerSucc R I n))))

/-- The system `n ↦ RHom_R(R/I^n,K)` for an arbitrary object `K` of the derived category. -/
noncomputable def derivedHomPowersOf (I : Ideal R)
    (K : DerivedCategory (ModuleCat.{u} R)) : ℕ ⥤ DerivedCategory (ModuleCat.{u} R) :=
  derivedHomPowers R I (kInjectiveRepresentative R K)

/-- The direct system whose `n`-th term is the actual module `Ext^q_R(R/I^n,K)`. -/
noncomputable def extPowers (I : Ideal R) (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) :
    ℕ ⥤ ModuleCat.{u + 1} R :=
  Functor.ofSequence
    (X := fun n ↦ ModuleCat.of R (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (R ⧸ I ^ n))) K q))
    (fun n ↦ ModuleCat.ofHom
      { toFun := fun x ↦
          (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map
            (quotientPowerSucc R I n) ≫ x
        map_add' := fun x y ↦ by simp
        map_smul' := fun r x ↦ by simp })

/-- The transition map of the `Ext` system is precomposition with the quotient map
`R/I^{n+1} → R/I^n`. -/
lemma extPowers_map_succ_apply (I : Ideal R) (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ)
    (n : ℕ)
    (x : DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R (R ⧸ I ^ n))) K q) :
    (extPowers R I K q).map (homOfLE (Nat.le_succ n)) x =
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).map (quotientPowerSucc R I n) ≫ x := by
  dsimp only [extPowers]
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

end Dualizing
