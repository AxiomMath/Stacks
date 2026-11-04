module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SeparatorUnivLE
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.WeakSerreAcrossTopologies
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ModuleHigherDirectImageSheafification
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The first conclusion of Stacks 07A8 at the source's hypotheses

Let `C` be a category carrying two Grothendieck topologies, a finer one `J` (the topology `τ`
of the source) and a coarser one `J'` (the topology `τ'`), let `R` be a sheaf of rings for `J`
and let `ε : (C_τ, R_τ) ⟶ (C_τ', R_τ')` be the comparison morphism, whose direct image `ε_*`
reads a `J`-sheaf of modules as a `J'`-sheaf of modules.  Let `A` be a weak Serre subcategory of
`Mod(R_τ)` and `B` a set of objects of `C` such that every object of `C` has a `J'`-covering by
members of `B` and `H^p_τ(U, F) = 0` for `p > 0`, `U` in `B` and `F` in `A`.  Then the image `A'`
of `A` under `ε_*` is a weak Serre subcategory of `Mod(R_τ')`.

This is the first conclusion of Stacks 07A8.  The five lemma argument of the source is
`Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE`, which takes as its hypothesis
`hdev` that `ε_*` carries an exact short complex with terms in `A` to an exact short complex;
this file proves that step from the source's assumptions, by Stacks 072W and a dévissage, and
so states the conclusion without it.

## Main results

* `Stacks.Cohomology.CompareTopologies.exact_map_pushforward_of_prop`: the dévissage step —
  `ε_*` carries an exact short complex with terms in `A` to an exact short complex.
* `Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE_of_univLE`: **Stacks 07A8**,
  the first conclusion — `A'` is a weak Serre subcategory of `Mod(R_τ')`.
* `Stacks.Cohomology.CompareTopologies.isWeakSerreClass_imageOfLE_of_univLE`: the same
  conclusion in the closure form `CategoryTheory.ObjectProperty.IsWeakSerreClass` of Stacks 0754.
* `Stacks.WeakSerre.isWeakSerreClass_of_isWeakSerre`: the five term exactness form of a weak
  Serre subcategory (Stacks 02MO) gives the closure form (Stacks 0754).

## The argument

By Stacks 072W the higher direct image `R^pε_*F` is the `τ'`-sheafification of
`U ↦ H^p_τ(U, F)`, so it vanishes for `p > 0` and `F` in `A` because each of its sections dies on
a `τ'`-covering by members of `B`; by the criterion of Stacks 015C for the left exact functor
`ε_*` that says every object of `A` is right acyclic for `ε_*`.  Stacks 015D propagates right
acyclicity along the two short exact sequences which dévissage an exact short complex — the
kernel/image sequence of its first map and the image/cycles/homology sequence — and the second
of them, mapped by `ε_*`, exhibits `ε_*` of the homology as the cokernel it has to be for `ε_*`
to preserve the left homology of the complex.  Closure of `A` under kernels, which a weak Serre
subcategory has in the form of Stacks 0754, places the objects appearing in the dévissage in
`A`.

## Universes

The objects of `C`, its morphisms, the sections of `R` and the modules have independent
universes.  The final statements ask the module universe to contain the other three; in it
sheafification exists for both topologies and inverts exactly the locally bijective morphisms,
and sheaves of `R`-modules have enough injectives, so that `H^p_τ(U, -)` is defined.

## References

* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.WeakSerre

/-- **A weak Serre subcategory in the five term exactness form of Stacks 02MO is one in the
closure form of Stacks 0754**, which is the converse of
`Stacks.WeakSerre.isWeakSerre_of_isWeakSerreClass`. -/
theorem isWeakSerreClass_of_isWeakSerre {D : Type*} [Category D] [Abelian D]
    (P : ObjectProperty D) (hP : WeakSerre.IsWeakSerre P) : P.IsWeakSerreClass :=
  (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact P).2 ⟨hP.nonempty,
    fun S hS h₀ h₁ h₃ h₄ ↦ hP.mem_of_exact5
      { obj₀ := S.obj' 0, obj₁ := S.obj' 1, obj₂ := S.obj' 2, obj₃ := S.obj' 3, obj₄ := S.obj' 4
        f₀ := S.map' 0 1, f₁ := S.map' 1 2, f₂ := S.map' 2 3, f₃ := S.map' 3 4
        zero₀ := hS.toIsComplex.zero' 0 1 2
        zero₁ := hS.toIsComplex.zero' 1 2 3
        zero₂ := hS.toIsComplex.zero' 2 3 4
        exact₁ := hS.exact' 0 1 2
        exact₂ := hS.exact' 1 2 3
        exact₃ := hS.exact' 2 3 4 } h₀ h₁ h₃ h₄⟩

end Stacks.WeakSerre

namespace Stacks.Cohomology.CompareTopologies

universe u v r m

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}
    (h : J' ≤ J) (R : Sheaf J RingCat.{r})

/-- `ε_*` preserves finite limits, being a right adjoint; in particular it is left exact, which is
what the dévissage of the proof of Stacks 07A8 consumes. -/
instance preservesFiniteLimits_pushforward_of_hasSheafify
    [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}] :
    PreservesFiniteLimits (pushforward.{u, v, r, m} h R) :=
  have : PreservesLimitsOfSize.{0, 0} (pushforward.{u, v, r, m} h R) :=
    (adjunction.{u, v, r, m} h R).rightAdjoint_preservesLimits
  inferInstance

variable (A : ObjectProperty (_root_.SheafOfModules.{m} R))

section Devissage

variable [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **`ε_*` carries an exact short complex with terms in `A` to an exact short complex.**
This is the dévissage step of the proof of Stacks 07A8.  Under assumptions (2) and (3) of that
tag — every object of `C` has a `J'`-covering by members of `B`, and `H^p_τ(U, F)` vanishes for
`p > 0`, `U` in `B` and `F` in `A` — Stacks 072W gives `R^pε_*F = 0` for `p > 0` and `F` in `A`,
so every object of `A` is right acyclic for `ε_*` by the criterion of Stacks 015C for a left
exact functor.  Stacks 015D then propagates acyclicity along the two short exact sequences

`0 ⟶ ker(X₁ ⟶ Z) ⟶ X₁ ⟶ im(X₁ ⟶ Z) ⟶ 0`  and  `0 ⟶ im(X₁ ⟶ Z) ⟶ Z ⟶ H ⟶ 0`,

where `Z` is the cycle object `ker(X₂ ⟶ X₃)` and `H` the homology, and exhibits `ε_*H` as the
cokernel of `ε_*(X₁ ⟶ Z)`; that is exactly the statement that `ε_*` preserves the left homology
of the complex, whence it preserves its exactness.  The kernel of `X₁ ⟶ X₂` lies in `A` because a
weak Serre subcategory is closed under kernels, and the homology lies in `A` because it is a zero
object; the third term `X₃` is not needed. -/
theorem exact_map_pushforward_of_prop [HasSheafify J' AddCommGrpCat.{m}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [EnoughInjectives (_root_.SheafOfModules.{m} R)]
    (hA : WeakSerre.IsWeakSerre A) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : _root_.SheafOfModules.{m} R, A F →
      IsZero (Stacks.Cohomology.moduleCohomology R U p F))
    (S : ShortComplex (_root_.SheafOfModules.{m} R)) (hS : S.Exact)
    (h₁ : A S.X₁) (h₂ : A S.X₂) :
    (S.map (pushforward.{u, v, r, m} h R)).Exact := by
  have := WeakSerre.isWeakSerreClass_of_isWeakSerre A hA
  -- Every object of `A` is right acyclic for `ε_*`: Stacks 072W, read through Stacks 015C.
  have hacy : ∀ F : _root_.SheafOfModules.{m} R, A F →
      (pushforward.{u, v, r, m} h R).rightAcyclic F := fun F hF ↦ by
    refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
      (pushforward.{u, v, r, m} h R) F).2 inferInstance).mpr fun i hi ↦ ?_
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = (p : ℤ) := ⟨i.toNat, by omega⟩
    exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ p F).1
      (Stacks.Cohomology.ModuleHigherDirectImage.isZero_rightDerived_ofLE_obj_of_weakSerre
        h R A B hB hvan p (by exact_mod_cast hi) F hF)
  -- The kernel of `S.f` is the kernel of `S.toCycles`, since `S.iCycles` is a monomorphism.
  have w : kernel.ι S.f ≫ S.toCycles = 0 := by
    rw [← cancel_mono S.iCycles, Category.assoc, S.toCycles_i, zero_comp, kernel.condition]
  have hk : IsLimit (KernelFork.ofι (kernel.ι S.f) w) :=
    isKernelOfComp S.iCycles S.f (kernelIsKernel S.f) w S.toCycles_i
  have := ((pushforward.{u, v, r, m} h R).rightAcyclic_cycles_and_preservesLeftHomologyOf S
    (kernel.ι S.f) w hk (hacy _ (A.prop_kernel S.f h₁ h₂)) (hacy _ h₁)
    (hacy _ (A.prop_of_isZero ((ShortComplex.exact_iff_isZero_homology S).1 hS)))).2
  exact hS.map_of_preservesLeftHomologyOf (pushforward.{u, v, r, m} h R)

end Devissage

section Unconditional

variable [UnivLE.{u, m}] [UnivLE.{v, m}] [UnivLE.{r, m}]

attribute [local instance] Stacks.SheafOfModules.siteHasSheafify
  Stacks.SheafOfModules.siteWEqualsLocallyBijective SheafOfModules.enoughInjectives_of_univLE

/-- **Stacks 07A8, first conclusion.**  Let `J' ≤ J` be two topologies on `C` and let `R` be a
sheaf of rings for the finer topology `J`, so that the identity functor of `C` is the comparison
morphism of ringed sites `ε : (C_τ, R_τ) ⟶ (C_τ', R_τ')`.  Let `A` be a class of sheaves of
`R`-modules for `J` — the source's assumption (1), that every object of `A` is a sheaf for the
finer topology, is this — and let `B` be a set of objects of `C`.  Assume

1. `A` is a weak Serre subcategory of `Mod(R_τ)`,
2. every object of `C` has a `J'`-covering whose members lie in `B`,
3. for every `U` in `B` the cohomology `H^p_τ(U, F)` vanishes for `p > 0` and `F` in `A`.

Then the image `A'` of `A` under `ε_*` is a weak Serre subcategory of `Mod(R_τ')`.

The modules live in a universe containing those of the objects and morphisms of `C` and of the
rings; in it sheafification exists for both topologies, inverts exactly the locally bijective
morphisms, and sheaves of `R`-modules have enough injectives, so that `H^p_τ(U, -)` is defined.
Assumptions 2 and 3 enter through
`Stacks.Cohomology.CompareTopologies.exact_map_pushforward_of_prop`, which proves from them that
`ε_*` carries an exact short complex with terms in `A` to an exact short complex. -/
@[stacks 07A8 "first conclusion: the image of `A` is a weak Serre subcategory of
`Mod(𝒪_τ')`"]
theorem isWeakSerre_imageOfLE_of_univLE (hA : WeakSerre.IsWeakSerre A) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : _root_.SheafOfModules.{m} R, A F →
      IsZero (Stacks.Cohomology.moduleCohomology R U p F)) :
    WeakSerre.IsWeakSerre (imageOfLE.{u, v, r, m} h R A) :=
  isWeakSerre_imageOfLE h R A hA B hB hvan fun hB hvan S hS h₁ h₂ _ ↦
    exact_map_pushforward_of_prop h R A hA B hB hvan S hS h₁ h₂

/-- **Stacks 07A8, first conclusion, in the closure form of Stacks 0754.**  The same statement as
`Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE_of_univLE`, with the conclusion
phrased as `CategoryTheory.ObjectProperty.IsWeakSerreClass`, the form in which the derived
category results consume it. -/
@[stacks 07A8 "first conclusion, in the closure form of Stacks 0754"]
theorem isWeakSerreClass_imageOfLE_of_univLE (hA : WeakSerre.IsWeakSerre A) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : _root_.SheafOfModules.{m} R, A F →
      IsZero (Stacks.Cohomology.moduleCohomology R U p F)) :
    (imageOfLE.{u, v, r, m} h R A).IsWeakSerreClass :=
  WeakSerre.isWeakSerreClass_of_isWeakSerre _ (isWeakSerre_imageOfLE_of_univLE h R A hA B hB hvan)


end Unconditional

end Stacks.Cohomology.CompareTopologies

end
