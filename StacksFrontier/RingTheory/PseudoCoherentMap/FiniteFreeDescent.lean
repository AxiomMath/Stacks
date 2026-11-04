module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.Homology.PseudoCoherent.Relative.Finite
public import StacksFrontier.Homology.PseudoCoherent.Relative.Summand
public import StacksFrontier.RingTheory.PseudoCoherentMap.Locality

/-!
# Descent of pseudo-coherence along a finite free ring map of positive rank

Let `R → A → A'` be ring maps and suppose that `A'` is free of finite positive rank as an
`A`-module. If `R → A'` is pseudo-coherent, then so is `R → A`.

This is the finite locally free case of the descent of pseudo-coherence, the last step of the
proof that pseudo-coherence of a morphism of schemes is fppf local on the source: an fppf
covering is refined by Zariski open covers together with surjective finite locally free
morphisms, and on affines such a morphism is precisely a finite free ring map of positive rank.

The argument is short. A finite free module of positive rank is faithfully flat and finitely
presented, so finite type of `R → A` descends along `A → A'`. Pseudo-coherence of `R → A'` says
that `A'` is pseudo-coherent relative to `R` as a module over itself; since `A → A'` is finite,
restriction of scalars reflects relative pseudo-coherence, so `A'` is pseudo-coherent relative
to `R` as an `A`-module. Freeness of positive rank exhibits `A'` as `A ⊕ A^{r}` as an
`A`-module, and relative pseudo-coherence passes to a direct summand, so `A` is pseudo-coherent
relative to `R` as a module over itself. That is pseudo-coherence of `R → A`.

## Main definitions

No new definitions are introduced; the isomorphisms used along the way are interior to the
proofs.

## Main results

* `Algebra.PseudoCoherent.of_linearEquiv_fin_succ`: descent of pseudo-coherence along a ring map
  that is free of rank `r + 1` as a module.
* `Algebra.PseudoCoherent.of_finite_free`: the same statement with the hypothesis in the form
  "finite, free and nontrivial".
* `Algebra.PseudoCoherent.of_finite_free_faithfullyFlat`: the same statement with the hypothesis
  in the form "finite, free and faithfully flat".

## Implementation notes

The module-level decomposition is stated for the object
`(ModuleCat.restrictScalars (algebraMap A A')).obj (ModuleCat.of A' A')` rather than for
`ModuleCat.of A A'`. The two carry the same `A`-module structure, but the first is the one that
appears in Stacks 0673, and the propositionally equal descriptions of the scalar multiplication
are not syntactically equal; mediating once, inside `restrictScalarsSelfEquiv`, keeps the rest
of the argument free of transports.

Positive rank is recorded as `r + 1` rather than as a hypothesis `0 < r`, which lets the
splitting off of one basis vector be `Fin.cons` and `Fin.tail`.

## References

* [The Stacks Project, Lemma 37.60.14 (0699)](https://stacks.math.columbia.edu/tag/0699)
* [The Stacks Project, Lemma 15.82.13 (0673)](https://stacks.math.columbia.edu/tag/0673)
* [The Stacks Project, Lemma 15.82.8 (0676)](https://stacks.math.columbia.edu/tag/0676)
* [The Stacks Project, Lemma 10.126.1 (0367)](https://stacks.math.columbia.edu/tag/0367)
* [The Stacks Project, Definition 15.83.1 (067H)](https://stacks.math.columbia.edu/tag/067H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open PseudoCoherence

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.PseudoCoherent

/-- Splitting off the first coordinate of a free module of rank `r + 1`. -/
private def piFinSuccSplit (A : Type u) [CommRing A] (r : ℕ) :
    ((Fin (r + 1)) → A) ≃ₗ[A] A × (Fin r → A) where
  toFun f := (f 0, fun i => f i.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun p := Fin.cons p.1 p.2
  left_inv f := Fin.cons_self_tail f
  right_inv _ := by ext <;> simp

/-- A ring `A'` that is an algebra over `A`, viewed as an `A`-module by restriction of scalars
along `A → A'`, is `A'` with its own `A`-module structure: both scalar multiplications are
multiplication by the image of the scalar. -/
private def restrictScalarsSelfEquiv {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] :
    A' ≃ₗ[A] (ModuleCat.restrictScalars.{u} (algebraMap A A')).obj (ModuleCat.of A' A') :=
  { AddEquiv.refl A' with map_smul' := fun a x => Algebra.smul_def a x }

/-- If `A'` is free of rank `r + 1` as an `A`-module, then `A'`, viewed as an `A`-module by
restriction of scalars, is the biproduct of `A` and a free module of rank `r`. In particular
`A` is a direct summand of `A'` as an `A`-module. -/
private def restrictScalarsSelfBiprodIso {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] {r : ℕ} (b : A' ≃ₗ[A] (Fin (r + 1) → A)) :
    (ModuleCat.restrictScalars.{u} (algebraMap A A')).obj (ModuleCat.of A' A') ≅
      ModuleCat.of A A ⊞ ModuleCat.of A (Fin r → A) :=
  LinearEquiv.toModuleIso
      (restrictScalarsSelfEquiv.symm.trans (b.trans (piFinSuccSplit A r))) ≪≫
    (ModuleCat.biprodIsoProd (ModuleCat.of A A) (ModuleCat.of A (Fin r → A))).symm

/-- The decomposition of `restrictScalarsSelfBiprodIso` in the derived category of `A`-modules:
the restriction of scalars of `A'`, placed in degree zero, is the biproduct of `A` and of a free
module of rank `r`, both placed in degree zero. Restriction of scalars is exact and the
degree-zero single-object functor is additive, so each takes the decomposition of the previous
step along. -/
private def singleRestrictScalarsBiprodIso {A A' : Type u} [CommRing A] [CommRing A']
    [Algebra A A'] {r : ℕ} (b : A' ≃ₗ[A] (Fin (r + 1) → A)) :
    (ModuleCat.restrictScalars.{u} (algebraMap A A')).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A') 0).obj (ModuleCat.of A' A')) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⊞
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Fin r → A)) := by
  let G := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let : G.Additive := inferInstance
  let : PreservesFiniteBiproducts G := Functor.preservesFiniteBiproductsOfAdditive G
  let : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  exact ((ModuleCat.restrictScalars.{u} (algebraMap A A')).mapDerivedCategorySingleFunctor
      0).app (ModuleCat.of A' A') ≪≫ G.mapIso (restrictScalarsSelfBiprodIso b) ≪≫
    G.mapBiprod (ModuleCat.of A A) (ModuleCat.of A (Fin r → A))

/-- **Descent of pseudo-coherence along a finite free ring map of positive rank.** Let
`R → A → A'` be ring maps and suppose `A'` is free of rank `r + 1` as an `A`-module. If `R → A'`
is pseudo-coherent, then so is `R → A`.

A free module of positive rank is faithfully flat, and a finite free module is finitely
presented, so finite type of `R → A` descends along `A → A'` by Stacks 0367. Pseudo-coherence of
`R → A'` is relative pseudo-coherence of `A'` over `R` as a module over itself; as `A → A'` is
finite, Stacks 0673 turns it into relative pseudo-coherence of `A'` over `R` as an `A`-module.
Freeness of rank `r + 1` makes `A'` the biproduct of `A` and a free module of rank `r`, so
Stacks 0676 passes relative pseudo-coherence to the summand `A`, which is pseudo-coherence of
`R → A`. -/
theorem _root_.Algebra.PseudoCoherent.of_linearEquiv_fin_succ
    {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [h : Algebra.PseudoCoherent R A'] {r : ℕ} (b : A' ≃ₗ[A] (Fin (r + 1) → A)) :
    Algebra.PseudoCoherent R A := by
  have hfree : Module.Free A A' := Module.Free.of_equiv b.symm
  have hmfp : Module.FinitePresentation A A' := Module.FinitePresentation.of_equiv b.symm
  have hfin : Module.Finite A A' := inferInstance
  have hafp : Algebra.FinitePresentation A A' := inferInstance
  -- `R → A` is of finite type, by descent along the faithfully flat `A → A'`.
  have hft : Algebra.FiniteType R A := by
    rcases subsingleton_or_nontrivial A with _ | _
    · exact Algebra.FiniteType.of_surjective (Algebra.ofId R A)
        fun _ => ⟨0, Subsingleton.elim _ _⟩
    · have : Nontrivial A' := b.toEquiv.nontrivial
      have hc : ((algebraMap A A').comp (algebraMap R A)).FiniteType := by
        rw [← IsScalarTower.algebraMap_eq R A A']
        exact RingHom.finiteType_algebraMap.mpr inferInstance
      exact RingHom.finiteType_algebraMap.mp
        (RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation hc
          (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
          (RingHom.finitePresentation_algebraMap.mpr hafp))
  obtain ⟨_, hrel⟩ :=
    Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp h
  refine Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr ?_
  -- Restrict scalars to `A` and split off the summand `A`.
  have hbip : IsRelativelyPseudoCoherent (R := R)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A) ⊞
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (Fin r → A))) := fun m =>
    RingHom.isRelativelyPseudoCoherentFrom_of_iso (singleRestrictScalarsBiprodIso b) m
      ((isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
        (R := R) (A := A) (B := A')
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A') 0).obj (ModuleCat.of A' A'))
        0).2.mp hrel m)
  exact (isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_of_biproduct
    (R := R) _ _ 0).2 hbip |>.1

/-- **Descent of pseudo-coherence along a finite free ring map of positive rank.** Let
`R → A → A'` be ring maps with `A'` finite, free and nonzero as an `A`-module. If `R → A'` is
pseudo-coherent, then so is `R → A`.

A finite free nonzero module has a basis indexed by a nonempty finite type, hence by `Fin (r + 1)`
for some `r`, which is the hypothesis of
`Algebra.PseudoCoherent.of_linearEquiv_fin_succ`. -/
theorem _root_.Algebra.PseudoCoherent.of_finite_free
    {R A : Type u} (A' : Type u) [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [Module.Free A A'] [Module.Finite A A'] [Nontrivial A']
    [Algebra.PseudoCoherent R A'] : Algebra.PseudoCoherent R A := by
  classical
  let b : Module.Basis (Module.Free.ChooseBasisIndex A A') A A' := Module.Free.chooseBasis A A'
  have : Nonempty (Module.Free.ChooseBasisIndex A A') := b.index_nonempty
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero
    (Fintype.card_ne_zero (α := Module.Free.ChooseBasisIndex A A'))
  exact Algebra.PseudoCoherent.of_linearEquiv_fin_succ
    (b.reindex (Fintype.equivFinOfCardEq hr)).equivFun

/-- **Descent of pseudo-coherence along a finite free faithfully flat ring map.** Let
`R → A → A'` be ring maps with `A'` finite, free and faithfully flat as an `A`-module. If
`R → A'` is pseudo-coherent, then so is `R → A`.

Faithful flatness is what rules out the zero rank: a faithfully flat module cannot be zero over
a nonzero ring, since a maximal ideal of the ring would then satisfy `m · M = M`. Over the zero
ring there is nothing to rule out, because `A'` is then zero as well and is the biproduct of `A`
and the free module of rank zero. -/
theorem _root_.Algebra.PseudoCoherent.of_finite_free_faithfullyFlat
    {R A : Type u} (A' : Type u) [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [Module.Free A A'] [Module.Finite A A'] [Module.FaithfullyFlat A A']
    [Algebra.PseudoCoherent R A'] : Algebra.PseudoCoherent R A := by
  rcases subsingleton_or_nontrivial A with _ | _
  · have : Subsingleton A' := ⟨fun x y => by
      have h1 : (1 : A) = 0 := Subsingleton.elim _ _
      have hz : ∀ z : A', z = 0 := fun z => by
        rw [← one_smul A z, h1, zero_smul]
      rw [hz x, hz y]⟩
    have : Subsingleton (Fin 1 → A) := Pi.instSubsingleton
    exact Algebra.PseudoCoherent.of_linearEquiv_fin_succ (A' := A') (r := 0)
      { toFun := fun _ => 0, invFun := fun _ => 0
        map_add' := fun _ _ => by simp
        map_smul' := fun _ _ => by simp
        left_inv := fun _ => Subsingleton.elim _ _
        right_inv := fun _ => Subsingleton.elim _ _ }
  · have : Nontrivial A' := by
      rcases subsingleton_or_nontrivial A' with _ | hn
      · obtain ⟨m, hm⟩ := Ideal.exists_maximal A
        exact absurd (le_antisymm le_top fun x _ => by
            rw [Subsingleton.elim x 0]; exact Submodule.zero_mem _)
          (Module.FaithfullyFlat.submodule_ne_top (R := A) (M := A') hm)
      · exact hn
    exact Algebra.PseudoCoherent.of_finite_free A'

end Stacks.PseudoCoherent

end
