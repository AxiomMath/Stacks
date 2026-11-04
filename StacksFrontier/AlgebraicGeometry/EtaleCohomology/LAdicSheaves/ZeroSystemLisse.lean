module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom

/-!
# The zero ℓ-adic sheaf is lisse

A zero sheaf on a site is locally constant: over every object its restriction is zero, hence the
constant sheaf on `0`. So the zero ℓ-adic sheaf `Stacks.EtaleCohomology.LAdicSheaf.zeroSystem`,
whose levels are all zero, is lisse.

## Main results

* `Stacks.ConstantSheaf.isLocallyConstant_of_isZero`: a zero sheaf is locally constant.
* `Stacks.EtaleCohomology.LAdicSheaf.isLisse_zeroSystem`: the zero ℓ-adic sheaf is lisse.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.ConstantSheaf

variable {C : Type*} [Category* C] (J : GrothendieckTopology C) {D : Type*} [Category* D]
  [HasZeroMorphisms D] [HasZeroObject D] [∀ U : C, HasWeakSheafify (J.over U) D]

/-- **A zero sheaf is locally constant**: over every object of the site its restriction is zero,
hence the constant sheaf on `0`. -/
theorem isLocallyConstant_of_isZero
    [∀ U : C, (constantSheaf (J.over U) D).PreservesZeroMorphisms]
    [∀ U : C, (J.overPullback D U).PreservesZeroMorphisms]
    {F : Sheaf J D} (hF : IsZero F) : IsLocallyConstant J F where
  exists_cover U := by
    refine ⟨PUnit, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ?_⟩
    · rw [(Sieve.id_mem_iff_eq_top).1 (Sieve.ofArrows_mk (fun _ : PUnit => U) (fun _ => 𝟙 U)
        PUnit.unit)]
      exact J.top_mem U
    · exact Sheaf.isConstant_of_iso _
        ((Functor.map_isZero _ hF).iso (Functor.map_isZero _ (isZero_zero D)))

end Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ n : ℕ, HasWeakSheafify
    (SmallEtale.topology B X.1 X.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] [IsNoetherian X.1]

/-- **The zero ℓ-adic sheaf is lisse**: every level is zero, hence locally constant. -/
theorem LAdicSheaf.isLisse_zeroSystem : (LAdicSheaf.zeroSystem B X ℓ).IsLisse := by
  intro n
  let J := SmallEtale.topology B X.1 X.property
  have : ∀ V, HasSheafify (J.over V) (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) := fun V =>
    Stacks.ConstantSheaf.hasSheafify_moduleCat.{u + 1, u, 0, 0} _ _
  have : ∀ V, (constantSheaf (J.over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))).PreservesZeroMorphisms := fun V => by
    have := (constantSheafAdj (J.over V) (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (Over.mkIdTerminal (X := V))).isLeftAdjoint
    infer_instance
  have : ∀ V, (J.overPullback (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) V).PreservesZeroMorphisms :=
    fun V => by
      have := ((Over.forget V).sheafAdjunctionCocontinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1)))) (J.over V) J).isLeftAdjoint
      infer_instance
  exact Stacks.ConstantSheaf.isLocallyConstant_of_isZero J (isZero_zero _)

end Stacks.EtaleCohomology
