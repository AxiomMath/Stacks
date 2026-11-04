module

public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulExtDegreeOneGenerated

/-!
# The degree-one generator of the self-Ext algebra of a Koszul-regular quotient squares to zero

Let `(X, O♯)` be a ringed space, let `φ : (O♯)ʳ ⟶ O♯` be a morphism of sheaves of modules whose
Koszul complex `K` resolves the quotient `O♯/I`, and read `K` as a cochain complex. The
cohomology sheaves of the internal endomorphism complex `SheafHom^•(K, K)` carry the composition
product, which makes them a sheaf of graded `O♯`-algebras
(`Stacks.SheafOfModules.homologyGradedAlgebra`); for a resolution they are the self-Ext sheaves
of `O♯/I`, so that algebra is the self-Ext algebra of the quotient. This file proves that its
degree-one piece has **square zero**: the product of any local section of
`H¹(SheafHom(K, K))` with itself vanishes.

This is the hypothesis `SheafOfModules.GradedAlgebra.SquareZero` of the universal property of an
exterior algebra, for the tautological degree-one generator, and it is the point at which the
exterior-algebra description of the self-Ext algebra of a Koszul-regular quotient becomes
available.

**Why it is not formal.** A degree-one class is represented by a cocycle `m` of
`SheafHom^•(K, K)`, and `m ∘ m` is a perfectly good degree-two cocycle; nothing in the formalism
makes it a coboundary. Graded commutativity of the composition product would give only that
*twice* the square vanishes, which over a base in which `2` is not invertible says nothing. What
does make the square vanish is Koszul-specific and is assembled from two inputs, each proved
elsewhere:

* **the local structure of degree-one classes** -- every local section of `H¹(SheafHom(K, K))`
  is, on a covering of its domain, an `O♯`-linear combination `Σⱼ aⱼ [δⱼ]` of the classes of the
  coordinate contractions
  (`Stacks.RegularSequence.KoszulChainData.isLocallySurjective_extGenerator`);
* **the exact vanishing of such a combination's square** -- the diagonal terms die because the
  square of a single contraction is zero and the off-diagonal ones cancel in pairs because two
  contractions anticommute, both already at the level of cocycles
  (`Stacks.RegularSequence.KoszulChainData.homologyMul_contraction_combination`).

Vanishing of a section of a sheaf is a local condition, so the two combine: the product of a
local section with itself vanishes after restriction along the arrows of a covering sieve, hence
vanishes.

## Main results

* `Stacks.RegularSequence.KoszulChainData.squareZero_id_homologyGradedAlgebra`: **the
  tautological degree-one generator of the self-Ext algebra has square zero.**
* `Stacks.RegularSequence.KoszulChainData.squareZero_extGenerator`: the same for the generator
  `(O♯)ʳ ⟶ H¹(SheafHom(K, K))` carrying the `j`-th tautological section to `[δⱼ]`.

## Implementation notes

The descent is `Stacks.eq_of_forall_lift` along the locally surjective morphism
`Stacks.RegularSequence.KoszulChainData.extGenerator`: two sections of a separated presheaf agree
as soon as they agree after restriction along every local lift of a given section. Taking the
given section to be the degree-one class and the two sections to be its square and zero, the
hypothesis to check is exactly that the square of a combination of the classes of the
contractions vanishes.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry HomologicalComplex
open Stacks.ChainComplex Stacks.SheafOfModules

universe u

namespace Stacks.RegularSequence.KoszulChainData

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Rc r)}
  {φ : koszulFreeSheaf Rc r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Rc)}
  (K : KoszulChainData.{u, u, u} A φ)

/-- **The tautological degree-one generator of the self-Ext algebra of a Koszul-regular quotient
has square zero**: for every open set `U` and every local section `s` of the first cohomology
sheaf of `SheafHom^•(K, K)` over `U`, the composition product of `s` with itself vanishes.

The class `s` is, on a covering of `U`, a combination `Σⱼ aⱼ [δⱼ]` of the classes of the
coordinate contractions, and the square of such a combination is zero; vanishing of a section of
a sheaf is local, so the square of `s` itself is zero. -/
theorem squareZero_id_homologyGradedAlgebra [QuasiIso K.augmentation] :
    SheafOfModules.GradedAlgebra.SquareZero
      (A := homologyGradedAlgebra Rc (cochain Rc K))
      (𝟙 ((endComplex Rc (cochain Rc K)).homology 1)) := by
  intro U s
  refine Stacks.eq_of_forall_lift (R := (structureSheaf Rc).obj)
    (((endComplex Rc (cochain Rc K)).homology (1 + 1)).isSheaf.isSeparated)
    (extGenerator Rc K).val s _ _ ?_
  intro Y f m hm
  refine Eq.trans ((homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).naturality
    f s s) ?_
  refine Eq.trans ?_ (map_zero _).symm
  refine Eq.trans (congrArg (fun z =>
    (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app Y z z) hm.symm) ?_
  refine Eq.trans (congrArg (fun z =>
    (homologyMul Rc (cochain Rc K) (cochain Rc K) (cochain Rc K) 1 1).app Y z z)
    (extGenerator_val_app Rc K Y m)) ?_
  exact homologyMul_contraction_combination Rc K Y.unop (koszulCoord Rc Y m)

/-- **The degree-one generator `(O♯)ʳ ⟶ H¹(SheafHom(K, K))` has square zero**, the generator
carrying the `j`-th tautological section to the class of the contraction `δⱼ`. This is the
previous statement composed with that morphism. -/
theorem squareZero_extGenerator [QuasiIso K.augmentation] :
    SheafOfModules.GradedAlgebra.SquareZero
      (A := homologyGradedAlgebra Rc (cochain Rc K)) (extGenerator Rc K) :=
  fun U s => squareZero_id_homologyGradedAlgebra Rc K U
    ((extGenerator Rc K).val.app U s)

end Stacks.RegularSequence.KoszulChainData

end
