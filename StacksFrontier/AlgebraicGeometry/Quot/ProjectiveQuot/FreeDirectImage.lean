module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Twist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZeroRow
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeRow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorAction

/-!
# The direct image of `𝒪(m)^{⊕ r}` on `ℙⁿ_T` is free

For every scheme `T` and every `m ≥ 0`, the direct image of `𝒪(m)^{⊕ r}` along `π : ℙⁿ_T ⟶ T` is
the free `𝒪_T`-module on `r` copies of the degree-`m` monomials in `n + 1` variables: the twist
commutes with finite direct sums, the direct image is additive, and
`π_* 𝒪(m) = (𝒪_T[T₀, …, Tₙ])_m` over an arbitrary base, by
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.baseDegreeSheafIsoPushforwardTwistOver`.
This is the free module `W ⊗ 𝒪_T` of the proof of Stacks 0DPA, whose quotients of rank `P(m)` make
up the Grassmannian into which `Quot^P` embeds.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.twistFunctor`: `ℱ ↦ ℱ(d)` as a functor.
* `AlgebraicGeometry.ProjectiveQuot.twistFreeModuleIso`: `𝒪^{⊕ r}(d) ≅ 𝒪(d)^{⊕ r}`.
* `AlgebraicGeometry.ProjectiveQuot.freeRank n r m`: the number of degree-`m` monomials in `r`
  copies of `n + 1` variables.
* `AlgebraicGeometry.ProjectiveQuot.pushforwardTwistFreeModuleIso`:
  `π_*(𝒪^{⊕ r}(m)) ≅ 𝒪_T^{⊕ freeRank n r m}`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable (n r : ℕ)

/-- **The twist `ℱ ↦ ℱ(d)` as a functor** of modules on `ℙⁿ_T`: tensoring on the right with
`𝒪(d)`. Its value at `ℱ` is `AlgebraicGeometry.ProjectiveQuot.twist d ℱ` by definition. -/
abbrev twistFunctor (T : Scheme.{u}) (d : ℤ) :
    (projectiveSpaceOver n T).Modules ⥤ (projectiveSpaceOver n T).Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨(projectiveSpaceOver n T).toSheafedSpace.presheaf,
      (projectiveSpaceOver n T).toSheafedSpace.IsSheaf⟩).flip.obj (twistingSheaf n T d)

/-- The value of `twistFunctor n T d` at `F` is the twist `twist d F`. -/
theorem twistFunctor_obj (T : Scheme.{u}) (d : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    (twistFunctor n T d).obj F = twist d F :=
  rfl

/-- The twist preserves colimits ([Stacks, Tag 05NB]). -/
instance (T : Scheme.{u}) (d : ℤ) : PreservesColimitsOfSize.{u, u} (twistFunctor n T d) :=
  Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj _ _

/-- **`𝒪^{⊕ r}(d) ≅ 𝒪(d)^{⊕ r}`.** -/
def twistFreeModuleIso (T : Scheme.{u}) (d : ℤ) :
    twist d (freeModule n r T) ≅ ∐ fun _ : Fin r => twistingSheaf n T d :=
  PreservesCoproduct.iso (twistFunctor n T d) _ ≪≫
    Sigma.mapIso fun _ => Scheme.Modules.tensorLeftUnitor _ (twistingSheaf n T d)

/-- The number of degree-`m` monomials in `r` copies of `n + 1` variables, the rank of
`π_*(𝒪^{⊕ r}(m))`. -/
def freeRank (m : ℕ) : ℕ :=
  Nat.card (Σ _ : Fin r, MonomialIndex.{u} n (m : ℤ))

/-- The index type of the free module `π_*(𝒪^{⊕ r}(m))` is `ULift (Fin (freeRank n r m))`. -/
def freeRankEquiv (m : ℕ) :
    ULift.{u} (Fin (freeRank.{u} n r m)) ≃ Σ _ : Fin r, MonomialIndex.{u} n (m : ℤ) :=
  Equiv.ulift.trans (Finite.equivFin _).symm

variable {n r} in
/-- **`π_*(𝒪^{⊕ r}(m))` is free** of rank `freeRank n r m` over an arbitrary scheme `T`, for
`m ≥ 0`: the twist commutes with the direct sum, the direct image is additive, and
`π_* 𝒪(m) = (𝒪_T[T₀, …, Tₙ])_m` is free on the degree-`m` monomials. -/
def pushforwardTwistFreeModuleIso (T : Scheme.{u}) (m : ℕ) :
    (Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).obj
        (twist (m : ℤ) (freeModule n r T)) ≅
      SheafOfModules.free (R := T.ringCatSheaf) (ULift.{u} (Fin (freeRank.{u} n r m))) :=
  (Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)).mapIso
      (twistFreeModuleIso n r T m) ≪≫
    PreservesCoproduct.iso (Scheme.Modules.pushforward (projectiveSpaceOver n T ↘ T)) _ ≪≫
    Sigma.mapIso (fun _ => (baseDegreeSheafIsoPushforwardTwistOver n T
      (Or.inl (Int.natCast_nonneg m))).symm) ≪≫
    (sigmaSigmaIso (fun _ : Fin r => MonomialIndex.{u} n (m : ℤ))
      (fun _ _ => SheafOfModules.unit T.ringCatSheaf) :
        (∐ fun _ : Fin r => baseDegreeSheaf n T (m : ℤ)) ≅
          SheafOfModules.free (R := T.ringCatSheaf) (Σ _ : Fin r, MonomialIndex.{u} n (m : ℤ))) ≪≫
    (SheafOfModules.freeFunctor.mapIso (freeRankEquiv n r m).toIso).symm

end AlgebraicGeometry.ProjectiveQuot

end
