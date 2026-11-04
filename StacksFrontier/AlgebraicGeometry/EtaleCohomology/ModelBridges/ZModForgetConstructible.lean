module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.LocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ZModConstructible

/-!
# The underlying abelian sheaf of a constructible sheaf of `ℤ/nℤ`-modules is constructible

This is the converse of
`AlgebraicGeometry.isConstructibleModuleSheaf_zmod_of_isConstructibleAbelianSheaf`: for `n > 0`, a
constructible sheaf of `ℤ/nℤ`-modules ([Stacks, Tag 03RW] (3)) has a constructible underlying
abelian sheaf ([Stacks, Tag 03RW] (2)). On a stratum the sheaf is locally constant with finitely
generated, hence finite, values, and forgetting the module structure commutes with constant sheaves
and with inverse images.

## Main results

* `Stacks.ConstantSheaf.isFiniteLocallyConstant_forget_of_isFiniteTypeLocallyConstant`: the
  statement on a stratum.
* `AlgebraicGeometry.isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_zmod`: the
  statement on the small étale site of Tag 021B.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v c u r

namespace Stacks.ConstantSheaf

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ) [NeZero n]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, HasWeakSheafify (J.over V) (ModuleCat.{w} (ZMod n))]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]
  [∀ V : C, (J.over V).HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]

/-- **A locally constant sheaf of `ℤ/nℤ`-modules with finitely generated values has a finite
locally constant underlying abelian sheaf**, for `n > 0`: the same trivializing covering works,
forgetting the module structure commutes with constant sheaves, and a finitely generated
`ℤ/nℤ`-module is finite. -/
theorem isFiniteLocallyConstant_forget_of_isFiniteTypeLocallyConstant
    (M : Sheaf J (ModuleCat.{w} (ZMod n))) (hM : IsFiniteTypeLocallyConstant (ZMod n) J M) :
    IsFiniteLocallyConstant J
      ((sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj M) := by
  constructor
  intro U
  obtain ⟨I, V, f, hf, h⟩ := hM U
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨φ⟩⟩ := h i
  have := preservesSheafification_forget₂_zmod.{w} (J.over (V i)) n
  have : Module.Finite (ZMod n) E := (ModuleCat.isFG_iff _).1 hE
  exact ⟨(forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w}).obj E,
    (Module.finite_of_finite (ZMod n) : Finite E),
    ⟨((constantCommuteCompose (J.over (V i))
      (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).app E).symm ≪≫
      (sheafCompose (J.over (V i)) (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).mapIso φ⟩⟩

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat

variable (B : BigEtaleSite.{u}) (n : ℕ) [NeZero n]

/-- **The underlying abelian sheaf of a constructible sheaf of `ℤ/nℤ`-modules is constructible**
([Stacks, Tag 03RW], parts (3) and (2)), on the small étale site of Tag 021B, for `n > 0`. -/
theorem isConstructibleAbelianSheaf_of_isConstructibleModuleSheaf_zmod (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) r} (ZMod n)))
    (hF : IsConstructibleModuleSheaf B X (ZMod n) F) :
    IsConstructibleAbelianSheaf B X
      ((sheafCompose _
        (forget₂ (ModuleCat.{max (u + 1) r} (ZMod n)) AddCommGrpCat.{max (u + 1) r})).obj F) := by
  intro U
  obtain ⟨s, hs⟩ := hF U
  exact ⟨s, fun i ↦ Stacks.ConstantSheaf.IsFiniteLocallyConstant.of_iso _
    (smallEtaleZModPullbackForgetIso B n (s.inclusion i) F).symm
    (Stacks.ConstantSheaf.isFiniteLocallyConstant_forget_of_isFiniteTypeLocallyConstant.{
      max (u + 1) r} _ n _ (hs i))⟩

end AlgebraicGeometry

end
