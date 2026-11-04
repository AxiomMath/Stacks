module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistActionMorphism
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwist
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.TerminalOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.TensorPowerInvariant
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Twist
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPointsDepth
public import StacksFrontier.AlgebraicGeometry.EnriquesSeveriZariski.Multiplication
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.Topology.Sheaves.Modules.StalkCokernel

/-!
# Multiplication of a twist by a global section of a tensor power

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `F` a coherent `𝒪_X`-module and `s` a
global section of `L^{⊗ n}`. Multiplication by `s` is the morphism
`F ⊗ L^{⊗ j} ⟶ F ⊗ L^{⊗ (n + j)}` of `Stacks.SheafOfModules.TwistAction.actionOf`. This file
collects what can be said about that morphism being a monomorphism, about the short exact
sequence it sits in, and about the depth of the stalks of its cokernel.

The organising principle is that all three questions reduce to the behaviour of the **stalk
maps** of `actionOf`, and those reductions are what is proved here; the one remaining input,
injectivity of the stalk map at an associated point, appears as an explicit hypothesis. See the
implementation notes for what is and is not discharged.

## Main results

* `Stacks.Divisors.associatedPoints_twist_eq`: **the associated points of a twist are the
  associated points of the module**, read at the spelling of the twist that
  `Stacks.SheafOfModules.TwistAction.actionOf` is stated over. This is what makes a hypothesis
  about `Ass(F)` suffice for a statement about `F ⊗ L^{⊗ j}`, in every degree `j` at once.
* `Stacks.Divisors.isCoherent_twistPow` and `Stacks.Divisors.isQuasicoherent_twistPow`: the
  twists of a coherent module by an invertible one are coherent, hence quasi-coherent. These
  discharge the side conditions of the monomorphism criterion below.
* `Stacks.Divisors.mono_actionOf_of_forall_stalk_injective`: **multiplication by `s` is a
  monomorphism as soon as its stalk map is injective at every associated point of `F`.** This
  is [Stacks, Tag 0AVL] applied to `actionOf`, with the twist-invariance of the associated
  points folded in so that the hypothesis is about `Ass(F)` and not about `Ass(F ⊗ L^{⊗ j})`.
* `Stacks.Divisors.shortExact_actionOf_of_mono`: **the sequence
  `0 ⟶ F ⊗ L^{⊗ j} ⟶ F ⊗ L^{⊗ (n + j)} ⟶ coker ⟶ 0` is short exact**, for `coker` the
  cokernel of multiplication by `s`, as soon as that multiplication is a monomorphism.
* `Stacks.Divisors.isCoherent_cokernel_actionOf`: **the cokernel is coherent.**
* `Stacks.Divisors.stalkCokernelActionOfIso`: **the stalk of the cokernel is the cokernel of
  the stalk map**, the exactness-of-stalks half of the depth statement.
* `Stacks.Divisors.one_le_depth_quotSMulTop_of_two_le_depth` and
  `Stacks.Divisors.one_le_depth_of_linearEquiv_quotSMulTop`: the ring-level input for the depth
  of the cokernel. If `r ∈ I` is a nonzerodivisor on a finite module `M` of depth at least `2`,
  then `M / rM` — and anything linearly equivalent to it — has depth at least `1`. This is the
  first conjunct of [Stacks, Tag 090R] turned into the inequality a geometric caller needs.
* `Stacks.Divisors.one_le_depth_of_subsingleton`: the complementary case, where the stalk of
  the cokernel vanishes and the depth is `⊤`.

## Implementation notes

**What is not proved here.** The stalk map of `Stacks.SheafOfModules.TwistAction.actionOf` is
*not* computed. The expected formula is that, after trivialising `L^{⊗ n}` at `x`, the stalk map
is multiplication by the resulting coordinate `r` of the germ of `s`; with that formula the
hypothesis of `mono_actionOf_of_forall_stalk_injective` becomes the non-vanishing condition
`(L^{⊗ n}).presheaf.Γgerm x s ∉ Stacks.ModuleStalk.maximalSmul (L^{⊗ n}) x` of
[Stacks, Tag 0AYL], and `stalkCokernelActionOfIso` turns the stalk of the cokernel into
`QuotSMulTop r` of the stalk of the twist, which is what
`one_le_depth_of_linearEquiv_quotSMulTop` consumes.

That computation is a development in its own right and is not carried out here.
`Stacks.SheafOfModules.TwistAction.actionOf` is built as an insertion morphism followed by a
braiding, an associator and two reindexing comparisons
(`Stacks.SheafOfModules.twistActionHom`), so identifying it with `𝟙_F ⊗ ψ` for a multiplication
morphism `ψ : L^{⊗ j} ⟶ L^{⊗ (n + j)}` is a prerequisite, and nothing in the tree computes a
germ of `Stacks.SheafOfModules.tensorPowerMulSectionAt` or of an integer tensor power — every
existing consumer of `actionOf` is cohomological and never touches a stalk. The statements below
are therefore phrased with stalk injectivity as a hypothesis, which is exactly the interface
that computation would supply.

**Why the associated-points identity needs no bridge.** The twist that `actionOf` is stated
over, `Stacks.SheafOfModules.TensorSheafification.tensorSheaf`, and the one
`Stacks.Divisors.associatedPoints_tensorObj_tensorPowScheme_eq` is stated over,
`AlgebraicGeometry.Scheme.Modules.tensorObj`, are the same object: both are the sheafification
of the objectwise tensor product along the identity of the ring presheaf. So no bridging
isomorphism is needed and `associatedPoints_twist_eq` is the existing lemma restated.

**The coherence predicate.** Inside a namespace beginning with `Stacks.` the name
`SheafOfModules.IsCoherent` resolves to `Stacks.SheafOfModules.IsCoherent`, which is a second
constant with the same fields as the root `SheafOfModules.IsCoherent` that `X.Modules` is
stated over and that the closure theory of
`StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic` is proved for. Every coherence statement
here is written with dot notation on a term of type `X.Modules`, which resolves through the
type's head symbol to the root predicate, so the two are never crossed.

## References

* [Stacks Project, Tag 0AYL](https://stacks.math.columbia.edu/tag/0AYL)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
* [Stacks Project, Tag 090R](https://stacks.math.columbia.edu/tag/090R)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules
open Stacks.SheafOfModules.TwistAction
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- The twist `F ⊗ L^{⊗ j}`, at the spelling of the tensor product and of the integer tensor
powers that `Stacks.SheafOfModules.TwistAction.actionOf` is stated over. -/
abbrev twistPow (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (j : ℤ) : X.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
    Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
      ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj (F)).obj
    ((Stacks.Algebraization.tensorPowScheme X L j)))

/-- The type of global sections of `L^{⊗ n}` that
`Stacks.SheafOfModules.TwistAction.actionOf` multiplies by. -/
abbrev powSection (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) : Type u :=
  (Stacks.Algebraization.tensorPowScheme X L n).val.obj (op (⊤_ (Opens X)))

/-- **Multiplication of the twist `F ⊗ L^{⊗ j}` by a global section `s` of `L^{⊗ n}`**, read at
the scheme spelling: `Stacks.SheafOfModules.TwistAction.actionOf` with the site data of `X`
supplied. -/
abbrev actionPow (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n j : ℤ)
    (s : powSection L n) : twistPow L F j ⟶ twistPow L F (n + j) :=
  actionOf X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L F n j s

/-! ### The twist: associated points and coherence -/

/-- **The associated points of a twist by an invertible module are the associated points of the
module**, in every integer degree. This is
`Stacks.Divisors.associatedPoints_tensorObj_tensorPowScheme_eq` restated at the twist spelling
of `Stacks.SheafOfModules.TwistAction.actionOf`; the two tensor products are the same object, so
nothing is transported. -/
theorem associatedPoints_twist_eq (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (j : ℤ) : associatedPoints (twistPow L F j) = associatedPoints F :=
  associatedPoints_tensorObj_tensorPowScheme_eq F L j

/-- **A twist of a coherent module by an invertible module is coherent**, in every integer
degree. Every integer tensor power of an invertible module is invertible
(`Stacks.Algebraization.isInvertibleModule_tensorPowScheme`), so this is
`AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible`. -/
instance isCoherent_twistPow (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    [F.IsCoherent] (j : ℤ) : (twistPow L F j).IsCoherent :=
  haveI := Stacks.Algebraization.isInvertibleModule_tensorPowScheme X L j
  AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F
    (Stacks.Algebraization.tensorPowScheme X L j)

/-- **A twist of a coherent module by an invertible module is quasi-coherent.** Coherence
implies quasi-coherence, and the twist is coherent by
`Stacks.Divisors.isCoherent_twistPow`. -/
instance isQuasicoherent_twistPow (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    [F.IsCoherent] (j : ℤ) : (twistPow L F j).IsQuasicoherent :=
  _root_.isQuasicoherent_of_isCoherent (twistPow L F j)

/-! ### Monicity and the short exact sequence -/

/-- **Multiplication by a global section of `L^{⊗ n}` is a monomorphism as soon as its stalk map
is injective at every associated point of `F`.**

This is [Stacks, Tag 0AVL]
(`Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints`)
applied to `Stacks.SheafOfModules.TwistAction.actionOf`. The tag asks for injectivity at the
associated points of the *source* `F ⊗ L^{⊗ j}`, and `Stacks.Divisors.associatedPoints_twist_eq`
identifies those with the associated points of `F`, so the hypothesis can be — and is — stated
about `Ass(F)` alone, with no reference to `j`. -/
theorem mono_actionOf_of_forall_stalk_injective [AlgebraicGeometry.IsLocallyNoetherian X]
    (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] [F.IsCoherent] (n j : ℤ)
    (s : powSection L n)
    (hs : ∀ x ∈ associatedPoints F,
      Function.Injective (Stacks.ModuleStalk.mapFun (actionPow L F n j s) x)) :
    Mono (actionPow L F n j s) := by
  refine Stacks.AlgebraicGeometry.AssociatedPointsMono.mono_of_stalk_injective_on_associatedPoints
    (actionPow L F n j s) fun x => ?_
  by_cases hx : x ∈ associatedPoints (twistPow L F j)
  · exact Or.inl (hs x ((associatedPoints_twist_eq L F j).subset hx))
  · exact Or.inr hx

/-- **The sequence `0 ⟶ F ⊗ L^{⊗ j} ⟶ F ⊗ L^{⊗ (n + j)} ⟶ coker ⟶ 0` is short exact**, for
`coker` the cokernel of multiplication by the global section `s` of `L^{⊗ n}`, as soon as that
multiplication is a monomorphism.

This is `CategoryTheory.ShortComplex.shortExact_mk_cokernel_π`: a monomorphism followed by the
projection to its cokernel is a short exact sequence in any category with homology, and the
category of `𝒪_X`-modules is abelian. -/
theorem shortExact_actionOf_of_mono (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (n j : ℤ) (s : powSection L n) [Mono (actionPow L F n j s)] :
    (ShortComplex.mk (actionPow L F n j s) (cokernel.π (actionPow L F n j s))
      (by simp)).ShortExact :=
  ShortComplex.shortExact_mk_cokernel_π (C := X.Modules) (actionPow L F n j s)

/-- **The cokernel of multiplication by a global section of `L^{⊗ n}` is coherent.** The two
twists it connects are coherent by `Stacks.Divisors.isCoherent_twistPow`, and coherent modules
are closed under cokernels — [Stacks, Tag 01BY] (3). -/
theorem isCoherent_cokernel_actionOf (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    [F.IsCoherent] (n j : ℤ) (s : powSection L n) :
    (cokernel (actionPow L F n j s)).IsCoherent :=
  AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel (R := X.ringCatSheaf)
    (actionPow L F n j s)

/-! ### The stalks of the cokernel

The depth statement about the cokernel needs its stalk, and the stalk functor on sheaves of
modules is exact, so it carries the cokernel to the cokernel of the stalk map. Once the stalk
map of `Stacks.SheafOfModules.TwistAction.actionOf` is known to be multiplication by an element
`r`, the isomorphism below exhibits the stalk of the cokernel as `QuotSMulTop r` of the stalk of
the twist, which is what the depth lemmas consume. -/

/-- **The stalk of the cokernel of multiplication by `s` is the cokernel of its stalk map.**
The stalk functor preserves colimits, hence cokernels; this is
`AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso` at `actionOf`. -/
def stalkCokernelActionOfIso (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n j : ℤ)
    (s : powSection L n) (x : X) :
    AlgebraicGeometry.SheafOfModules.stalkObj X.ringCatSheaf x
        (cokernel (actionPow L F n j s)) ≅
      cokernel (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x
        (actionPow L F n j s)) :=
  AlgebraicGeometry.SheafOfModules.stalkObjCokernelIso X.ringCatSheaf x (actionPow L F n j s)

/-! ### The ring-level depth input

The geometric statement that the depth of the stalk of the cokernel drops by exactly one is,
after identifying that stalk with a quotient `M / rM`, the first conjunct of
[Stacks, Tag 090R]. These lemmas package that conjunct, and the complementary vanishing case,
in the inequality form a geometric caller uses. -/

/-- **A nonzerodivisor cuts the depth down by exactly one, in the inequality form.** If `r ∈ I`
is a nonzerodivisor on a finite module `M` over a Noetherian ring and `M` has depth at least `2`
along `I`, then `M / rM` has depth at least `1`.

This is the first conjunct of [Stacks, Tag 090R]
(`Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append`), which gives
`depth(M/rM) + 1 = depth(M)`: were the left summand zero the depth of `M` would be `1`, against
the hypothesis. -/
theorem one_le_depth_quotSMulTop_of_two_le_depth {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] {r : R}
    (hrI : r ∈ I) (hreg : IsSMulRegular M r) (h2 : (2 : ℕ∞) ≤ Module.depth R I M) :
    (1 : ℕ∞) ≤ Module.depth R I (QuotSMulTop r M) := by
  have h := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).1 r hrI hreg
  rcases eq_or_ne (Module.depth R I (QuotSMulTop r M)) 0 with h0 | h0
  · rw [h0, zero_add] at h
    rw [← h] at h2
    norm_num at h2
  · exact Order.one_le_iff_ne_zero.mpr h0

/-- **The depth bound transported along a linear equivalence**, the shape a geometric caller
needs: a module linearly equivalent to `M / rM`, for `r ∈ I` a nonzerodivisor on a finite module
`M` of depth at least `2`, has depth at least `1`. Depth is invariant under a linear equivalence
(`Module.depth_eq_depth_of_linearEquiv`), so this is
`Stacks.Divisors.one_le_depth_quotSMulTop_of_two_le_depth` moved across `e`. -/
theorem one_le_depth_of_linearEquiv_quotSMulTop {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) {M Q : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup Q] [Module R Q] {r : R} (e : Q ≃ₗ[R] QuotSMulTop r M) (hrI : r ∈ I)
    (hreg : IsSMulRegular M r) (h2 : (2 : ℕ∞) ≤ Module.depth R I M) :
    (1 : ℕ∞) ≤ Module.depth R I Q := by
  rw [Module.depth_eq_depth_of_linearEquiv I e]
  exact one_le_depth_quotSMulTop_of_two_le_depth I M hrI hreg h2

/-- **The depth of a vanishing module is `⊤`**, so the bound `1 ≤ depth` holds trivially. This
is the case of the depth statement at a point where the section does *not* vanish: there the
germ of `s` is a unit after trivialisation, so multiplication by it is onto and the stalk of the
cokernel is zero. -/
theorem one_le_depth_of_subsingleton {R : Type*} [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] [Subsingleton M] : (1 : ℕ∞) ≤ Module.depth R I M := by
  rw [Module.depth_eq_top_of_subsingleton I]
  exact le_top

/-! ### The factorisation of `actionOf` through multiplication in the left factor

`Stacks.SheafOfModules.TwistAction.actionOf` is, by its definition through
`Stacks.SheafOfModules.tensorInsertHom`, the composite of the inverse left unit constraint,
multiplication of the *left* tensor factor by `s`, and a structural isomorphism.  That
factorisation is what computes both the cokernel and the stalk maps below: the middle map is
`AlgebraicGeometry.Scheme.Modules.tensorRightMap`, about which the tree already knows how stalks
and cokernels behave. -/

/-- The structural comparison that `Stacks.SheafOfModules.TwistAction.actionOf` applies after
inserting the multiplying factor: braid it past `ℱ`, reassociate, multiply the two tensor powers
together and commute their degrees. -/
def actionTail (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n j : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (X.presheaf) (forget₂ CommRingCat RingCat)
        ((Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X))⟩).obj
      ((Stacks.Algebraization.tensorPowScheme X L n))).obj ((twistPow L F j))) ≅
      twistPow L F (n + j) :=
  letI := Stacks.RelativeVeryAmple.isEquivalence_tensorRightFunctor_of_isInvertibleModule X L
  Invertible.tensorProductBraiding X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ _ ≪≫
    Invertible.tensorProductAssociator X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F _ _ ≪≫
    Invertible.tensorProductIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (Iso.refl F)
      (TensorPower.coherentMulIso X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L j n) ≪≫
    Invertible.tensorProductIso X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (Iso.refl F)
      (TensorPower.tensorPowerReindex X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L (Int.add_comm j n))

/-- A global section of `L^{⊗ n}`, read as the morphism `𝒪_X ⟶ L^{⊗ n}` of multiplication by
it. -/
abbrev powSectionHom (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n : ℤ)
    (s : powSection L n) :
    SheafOfModules.unit X.ringCatSheaf ⟶ Stacks.Algebraization.tensorPowScheme X L n :=
  globalSectionHom X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) _ s

/-- **Multiplication by a global section of `L^{⊗ n}` is multiplication by that section in the
left tensor factor, followed by a structural isomorphism.**  This is the definition of
`Stacks.SheafOfModules.TwistAction.actionOf` unfolded through
`Stacks.SheafOfModules.tensorInsertHom`, so it holds by `rfl`. -/
theorem actionPow_eq (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n j : ℤ)
    (s : powSection L n) :
    actionPow L F n j s =
      (Invertible.tensorProductLeftUnitor X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (twistPow L F j)).inv ≫
        Scheme.Modules.tensorRightMap (powSectionHom L n s) (twistPow L F j) ≫
          (actionTail L F n j).hom := rfl

/-! ### The cokernel is a twist of one fixed module -/

/-- `- ⊗ ℳ` on the modules of a scheme. -/
abbrev tensorRightOf (M : X.Modules) : X.Modules ⥤ X.Modules :=
  TensorLocalProperties.tensorSheafLeft (Opens.grothendieckTopology X) X.sheaf M

/-- **Tensoring on the right by an arbitrary `𝒪_X`-module is right exact**, [Stacks, Tag 05NB];
the shape-universe of the colimits is lowered so that cokernels are covered. -/
theorem preservesFiniteColimits_tensorRightOf (M : X.Modules) :
    PreservesFiniteColimits (tensorRightOf M) := by
  have h : PreservesColimitsOfSize.{u, u} (tensorRightOf M) :=
    TensorLocalProperties.preservesColimits_tensorSheafLeft
      (Opens.grothendieckTopology X) X.sheaf M
  have h0 : PreservesColimitsOfSize.{0, 0} (tensorRightOf M) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  exact PreservesColimitsOfSize.preservesFiniteColimits _

/-- **The cokernel of multiplication by a global section of `L^{⊗ n}` is a twist of one module
that does not depend on the twist degree.**  Writing `𝒞` for the cokernel of
`s : 𝒪_X ⟶ L^{⊗ n}`, the cokernel of multiplication by `s` on `ℱ ⊗ L^{⊗ j}` is
`(𝒞 ⊗ ℱ) ⊗ L^{⊗ j}`.

This is what makes **one** application of [Stacks, Tag 0FD7] cover every sufficiently negative
`j` at once: by `Stacks.Divisors.actionPow_eq` the multiplication is, up to isomorphisms,
`tensorRightMap` of `s`, and tensoring on the right is right exact, so it carries the cokernel
of `s` to the cokernel of the multiplication. -/
def cokernelActionPowIso (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (n j : ℤ)
    (s : powSection L n) :
    cokernel (actionPow L F n j s) ≅
      twistPow L (Scheme.Modules.tensorObj (cokernel (powSectionHom L n s)) F) j :=
  haveI := preservesFiniteColimits_tensorRightOf (twistPow L F j)
  have hcomm : actionPow L F n j s ≫ (actionTail L F n j).inv =
      (Invertible.tensorProductLeftUnitor X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (twistPow L F j)).inv ≫
        Scheme.Modules.tensorRightMap (powSectionHom L n s) (twistPow L F j) :=
    (Iso.comp_inv_eq _).2 ((actionPow_eq L F n j s).trans (Category.assoc _ _ _).symm)
  cokernel.mapIso (actionPow L F n j s)
      (Scheme.Modules.tensorRightMap (powSectionHom L n s) (twistPow L F j))
      (Invertible.tensorProductLeftUnitor X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (twistPow L F j)).symm
      (actionTail L F n j).symm hcomm ≪≫
    (PreservesCokernel.iso (tensorRightOf (twistPow L F j)) (powSectionHom L n s)).symm ≪≫
    (Invertible.tensorProductAssociator X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)
      (cokernel (powSectionHom L n s)) F
      (Stacks.Algebraization.tensorPowScheme X L j)).symm

/-! ### Monicity from nonvanishing at the associated points

With the factorisation in hand the stalk map of `actionOf` is computed: the two outer factors are
isomorphisms, and the middle one is `tensorRightMap` of multiplication by the section, whose
stalk map is bijective wherever the section does not vanish.  That discharges the hypothesis of
`Stacks.Divisors.mono_actionOf_of_forall_stalk_injective`. -/

/-- **`Stacks.SheafOfModules.globalSectionHom` is multiplication by the restriction of its
section to the whole space.**  Both constructions are `unitHomEquiv.symm` applied to the family
of restrictions of one global section; the comparison of the two spellings of the total open is
`AlgebraicGeometry.restrictTerminalTopEquiv`, and the two restriction morphisms agree because
`Opens X` is a partial order. -/
theorem globalSectionHom_eq_sectionHom (M : X.Modules) (σ : Γ(M, ⊤_ (Opens X))) :
    globalSectionHom X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M σ =
      Stacks.EnriquesSeveriZariski.sectionHom M
        (AlgebraicGeometry.restrictTerminalTopEquiv M σ) := by
  refine congrArg M.unitHomEquiv.symm (Subtype.ext (funext fun U => ?_))
  show M.val.map (terminal.from U.unop).op σ =
    M.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op
      (M.presheaf.map (terminal.from (⊤ : X.Opens)).op σ)
  rw [← ConcreteCategory.comp_apply, ← M.presheaf.map_comp]
  exact congrArg (fun i => (ConcreteCategory.hom (M.presheaf.map i)) σ) (Subsingleton.elim _ _)

/-- **At a point where the section does not vanish, multiplication by it is bijective on the
stalk of the tensor power.**  This is clause 2 of [Stacks, Tag 01CY]. -/
theorem bijective_stalkLinearMap_powSectionHom (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n : ℤ) (s : powSection L n) {y : X}
    (hy : y ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L n)
      (AlgebraicGeometry.restrictTerminalTopEquiv _ s)) :
    Function.Bijective (AlgebraicGeometry.stalkLinearMap _ _ (powSectionHom L n s) y) := by
  have := Stacks.Algebraization.isInvertibleModule_tensorPowScheme X L n
  rw [show powSectionHom L n s = Stacks.EnriquesSeveriZariski.sectionHom _
    (AlgebraicGeometry.restrictTerminalTopEquiv _ s) from globalSectionHom_eq_sectionHom _ s]
  exact Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_sectionHom _ _ hy

/-- **At a point where the section does not vanish, multiplication by it is injective on the
stalk of the twist.**  Tensoring a bijection of stalks on the right keeps it injective. -/
theorem injective_stalkLinearMap_actionPow (L F : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (n j : ℤ) (s : powSection L n) {y : X}
    (hy : y ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L n)
      (AlgebraicGeometry.restrictTerminalTopEquiv _ s)) :
    Function.Injective (AlgebraicGeometry.stalkLinearMap _ _ (actionPow L F n j s) y) := by
  set u := (Invertible.tensorProductLeftUnitor X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (twistPow L F j)).inv with hu'
  set v := Scheme.Modules.tensorRightMap (powSectionHom L n s) (twistPow L F j) with hv'
  have hiso : ∀ {A B : X.Modules} (e : A ≅ B),
      Function.Bijective (AlgebraicGeometry.stalkLinearMap _ _ e.hom y) := fun e =>
    Stacks.EnriquesSeveriZariski.bijective_stalkLinearMap_of_inverse _ _
      e.hom_inv_id e.inv_hom_id y
  have hu := hiso (Invertible.tensorProductLeftUnitor X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) (twistPow L F j)).symm
  have hw := hiso (actionTail L F n j)
  have hv : Function.Injective (AlgebraicGeometry.stalkLinearMap _ _ v y) :=
    AlgebraicGeometry.injective_stalkLinearMap_tensorRightMap _ _ y
      (bijective_stalkLinearMap_powSectionHom L n s hy)
  have key : ∀ z, AlgebraicGeometry.stalkLinearMap _ _ (actionPow L F n j s) y z =
      AlgebraicGeometry.stalkLinearMap _ _ (actionTail L F n j).hom y
        (AlgebraicGeometry.stalkLinearMap _ _ v y
          (AlgebraicGeometry.stalkLinearMap _ _ u y z)) := fun z =>
    (Scheme.Modules.stalkLinearMap_comp u (v ≫ (actionTail L F n j).hom) y z).trans
      (Scheme.Modules.stalkLinearMap_comp v (actionTail L F n j).hom y _)
  exact fun a b hab =>
    hu.injective (hv (hw.injective ((key a).symm.trans (hab.trans (key b)))))

/-- **Multiplication by a global section of `L^{⊗ n}` that does not vanish at any associated
point of `ℱ` is a monomorphism**, in every twist degree.  This discharges the hypothesis of
`Stacks.Divisors.mono_actionOf_of_forall_stalk_injective`, which was left open when that
criterion was stated. -/
theorem mono_actionPow_of_nonvanishing [AlgebraicGeometry.IsLocallyNoetherian X]
    (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] [F.IsCoherent] (n j : ℤ)
    (s : powSection L n)
    (hs : ∀ x ∈ associatedPoints F,
      x ∈ Stacks.Ample.nonvanishingLocus (Stacks.Algebraization.tensorPowScheme X L n)
        (AlgebraicGeometry.restrictTerminalTopEquiv _ s)) :
    Mono (actionPow L F n j s) :=
  mono_actionOf_of_forall_stalk_injective L F n j s fun x hx =>
    injective_stalkLinearMap_actionPow L F n j s (hs x hx)

/-! ### The depth of the cokernel

The stalk functor on sheaves of modules is exact, so a short exact sequence of modules gives a
short exact sequence of stalks; the two outer terms of the sequence of a monic multiplication are
twists of `ℱ`, hence have the depth of `ℱ_y`, and [Stacks, Tag 00LX] loses at most one from it.
No stalk-level formula for the multiplication is needed, and in particular no nonzerodivisor has
to be exhibited. -/

/-- **The stalk of a tensor product with an invertible module has the depth of the stalk of the
other factor**: the stalk of an invertible module is free of rank one, so the two stalks are
linearly isomorphic. -/
theorem depth_stalk_tensorObj_eq (F A : X.Modules) [hA : Stacks.Ample.IsInvertibleModule X A]
    (y : X) :
    Module.depth (X.presheaf.stalk y) (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
        ((Scheme.Modules.tensorObj F A).presheaf.stalk y) =
      Module.depth (X.presheaf.stalk y) (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
        (F.presheaf.stalk y) :=
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property A :=
    hA.toAlgebraicGeometry
  Module.depth_eq_depth_of_linearEquiv _ (tensorInvertibleStalkEquiv F A y)

/-- **The stalk of a twist has the depth of the stalk of the module**, in every degree. -/
theorem depth_stalk_twistPow_eq (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (j : ℤ)
    (y : X) :
    Module.depth (X.presheaf.stalk y) (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
        ((twistPow L F j).presheaf.stalk y) =
      Module.depth (X.presheaf.stalk y) (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
        (F.presheaf.stalk y) :=
  @depth_stalk_tensorObj_eq X F (Stacks.Algebraization.tensorPowScheme X L j)
    (Stacks.Algebraization.isInvertibleModule_tensorPowScheme X L j) y

/-- **The cokernel of a monic multiplication has positive depth at every point where `ℱ` has
depth at least two.**  The stalks of the short exact sequence of
`Stacks.Divisors.shortExact_actionOf_of_mono` form a short exact sequence of finite modules over
the local ring, whose two outer terms have the depth of `ℱ_y`; the middle inequality of
[Stacks, Tag 00LX] then gives `depth ≥ min(2, 2 - 1) = 1` for the quotient. -/
theorem one_le_depth_stalk_cokernel_actionPow [AlgebraicGeometry.IsLocallyNoetherian X]
    (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] [F.IsCoherent] (n j : ℤ)
    (s : powSection L n) (hmono : Mono (actionPow L F n j s)) {y : X}
    (h2 : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (F.presheaf.stalk y)) :
    (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      ((cokernel (actionPow L F n j s)).presheaf.stalk y) := by
  have := hmono
  have : Module.Finite (X.presheaf.stalk y) ((twistPow L F (n + j)).presheaf.stalk y) :=
    AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent (twistPow L F (n + j)) y
  obtain ⟨f, g, hf, hfg, hg⟩ := Stacks.SheafOfModules.FlatShortExact.stalkShortExact
    (X := X.toRingedSpace) _ (shortExact_actionOf_of_mono L F n j s) y
  let f' : ↥((twistPow L F j).presheaf.stalk y) →ₗ[↥(X.presheaf.stalk y)]
      ↥((twistPow L F (n + j)).presheaf.stalk y) := f
  let g' : ↥((twistPow L F (n + j)).presheaf.stalk y) →ₗ[↥(X.presheaf.stalk y)]
      ↥((cokernel (actionPow L F n j s)).presheaf.stalk y) := g
  have hf' : Function.Injective f' := hf
  have hg' : Function.Surjective g' := hg
  have hfg' : Function.Exact f' g' := hfg
  have hquot := (Module.min_depth_le_depth_of_exact
    (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) hfg' hf' hg').2.1
  have hd : ∀ k, (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) ((twistPow L F k).presheaf.stalk y) :=
    fun k => h2.trans_eq (depth_stalk_twistPow_eq L F k y).symm
  refine le_trans (le_min (le_trans (by norm_num) (hd (n + j))) ?_) hquot
  refine Order.one_le_iff_ne_zero.mpr fun h0 => ?_
  rw [tsub_eq_zero_iff_le] at h0
  exact absurd (le_trans (hd j) h0) (by norm_num)

/-- **No closed point is an associated point of the cokernel of a monic multiplication**, when
`ℱ` has depth at least two at every closed point.  This is the hypothesis of
[Stacks, Tag 0FD7] for the cokernel. -/
theorem notMem_associatedPoints_cokernel_actionPow [AlgebraicGeometry.IsLocallyNoetherian X]
    (L F : X.Modules) [Stacks.Ample.IsInvertibleModule X L] [F.IsCoherent] (n j : ℤ)
    (s : powSection L n) (hmono : Mono (actionPow L F n j s)) {y : X}
    (h2 : (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (F.presheaf.stalk y)) :
    y ∉ associatedPoints (cokernel (actionPow L F n j s)) :=
  have := isCoherent_cokernel_actionOf L F n j s
  notMem_associatedPoints_of_one_le_depth _ y
    (one_le_depth_stalk_cokernel_actionPow L F n j s hmono h2)

end Stacks.Divisors

end
