module

public import StacksFrontier.Homology.ExtendScalars.DerivedHomology
public import StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Examples.Completion.CompleteModulesEquivAdicSystems
public import StacksFrontier.RingTheory.AdicCompletion.ShortExact
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.ExtCompletionComparison
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
import all StacksFrontier.RingTheory.AdicCompletion.ShortExact
import all StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
import all StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality
import all StacksFrontier.RingTheory.Dualizing.FiniteLengthMatlisDuality.DerivedHomHeart
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of `Ext` along a flat map, and along localise-then-complete

Let `A → S` be a flat homomorphism of Noetherian rings, let `M` be a finite `A`-module and let
`K` be a bounded below object of `D(A)`.  Then

`Ext^i_S(S ⊗_A M, K ⊗ᴸ_A S) ≅ S ⊗_A Ext^i_A(M, K)`.

The case this file is written for is `S = A^∧`, the completion of `A` along an ideal `I`, with
`M` running through an adic system `(M_n)` of finite `A`-modules along `I` -- surjective
transitions with kernel `Iⁿ⁺¹ M_{n+1}`, the condition `Stacks.Examples.IsAdicModuleSystem`.
Such a system determines one finite module `M = (lim M_n)^∧` over `A^∧` whose adic quotients
`M / Iⁿ⁺¹ M` are its terms, and for a dualizing complex `ω` over `A` the base change collapses:

`Ext^i_{A^∧}(M / Iⁿ⁺¹ M, ω ⊗ᴸ_A A^∧) ≅ Ext^i_A(M_n, ω)`,

because `M_n` and `Ext^i_A(M_n, ω)` are both killed by `Iⁿ⁺¹` and so are already complete.

Read at `A = A[1/f]` with `I` the extension of an ideal of the original ring, this is the
comparison along *localise, then complete* that [Stacks, Tag 0EHK] uses: the source over
`A[1/f]` is the derived localization of a dualizing complex, which is dualizing by
[Stacks, Tag 0A7G] (`Dualizing.isDualizingComplex_localizationAway`), and the target over the
completion is its derived base change, which is dualizing by [Stacks, Tag 0DWD]
(`Dualizing.isDualizingComplex_adicCompletion`).

## Main definitions

* `Dualizing.adicSystemQuot` — the adic quotient `M / Iⁿ⁺¹ M` of the finite module over `A^∧`
  attached to an adic system.

## Main results

* `Dualizing.isIso_derivedHomBaseChange_single` — the derived-Hom base-change map of
  [Stacks, Tag 0E1X] out of a finite module placed in degree zero is invertible along a flat map
  of Noetherian rings.
* `Dualizing.extBaseChangeLinearEquiv` — flat base change for `Ext`, `S`-linearly.
* `Dualizing.finite_adicCompletion_limit` and `Dualizing.adicCompletionLimitQuotEquiv` — the
  finite module over `A^∧` attached to an adic system, and the identification of its adic
  quotients with the terms of the system.  These are the algebraic forms of
  `Stacks.Algebraization.finite_completedStalk` ([Stacks, Tag 0EJE]) and
  `Stacks.Algebraization.completedStalkQuotientEquivStalk`, which say the same about the stalk of
  a coherent adic system on a scheme and are instances of them; the two geometric statements are
  a dedup target against these, not reproved here because the first carries a `stacks`
  attribute.
* `Dualizing.adicSystemQuotNatIso` — the same identification as an isomorphism of *systems*,
  with `Dualizing.adicCompletionLimitQuotEquiv` as its component
  (`Dualizing.adicSystemQuotNatIso_app`); the compatibility with the transition maps that it
  needs is `Dualizing.adicCompletionLimitQuotEquiv_comp`.
* `Dualizing.extendScalarsAdicSystemIso` — base change of a term of the system to `A^∧` is the
  corresponding adic quotient.  This is the `A^∧`-linear form of one component of
  `Dualizing.adicSystemQuotNatIso`.
* `Dualizing.extendScalarsAdicSystemNatIso` — the same `A^∧`-linearly at every index *at once*,
  an isomorphism of systems whose component is `Dualizing.extendScalarsAdicSystemIso`
  (`Dualizing.extendScalarsAdicSystemNatIso_app`).  Its construction inserts
  `Dualizing.tensorAdicCompletionEquivOfPowSMulTopEqBot`, for which no compatibility with the
  transition maps is available, and the naturality does not need one: a map out of an extension
  of scalars is determined by its values on the elements `1 ⊗ x`, and there the tensor
  equivalence is the identity (`Dualizing.tensorAdicCompletionEquivOfPowSMulTopEqBot_one_tmul`),
  leaving the `A`-linear `Dualizing.adicCompletionLimitQuotEquiv_naturality` to do the work.
* `Dualizing.tensorAdicCompletionEquivOfPowSMulTopEqBot` and
  `Dualizing.tensorAdicCompletionExtEquiv` — a finite module killed by a power of `I`, and `Ext`
  into a dualizing complex out of such a module, do not change under base change to `A^∧`.
* `Dualizing.extAdicSystemCompletionAddEquiv` — the displayed comparison of the two `Ext`
  modules.

## Implementation notes

The derived extension of scalars is left as an arbitrary total left derived functor of termwise
extension of scalars, as in [Stacks, Tag 0A6A]: a consumer whose base change is
`(ModuleCat.extendScalars _).mapDerivedCategory` -- which is the shape in which
`Dualizing.isDualizingComplex_adicCompletion` provides the dualizing complex of the completion
-- may use these statements at that functor directly, with no comparison of functors.

`Dualizing.localizedExtLinearEquiv` and `Dualizing.localized_ext_nontrivial_iff` are the
localization case of `Dualizing.extBaseChangeLinearEquiv`, assembled from the same comparisons
before it existed; they are a dedup target against it, the localization of a module being its
base change to the localized ring.  (`Dualizing.localizedExtLinearEquiv` is in turn duplicated by
a `private` copy in
`StacksFrontier/RingTheory/Dualizing/UpperShriek/CompleteIntersectionLocal.lean`.)

`Dualizing.extAdicSystemCompletionAddEquiv` is stated additively because its two halves are
linear over different rings: flat base change for `Ext` is linear over `A^∧` and the collapse of
the base change is linear over `A`.  Both halves are exported separately.

The base change of a finite module to its completion (Mathlib's
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`) is available only for a module in the
universe of the ring, while `Ext` lives one universe higher; the collapse is therefore carried
out on `H^i(RHom_A(M, ω))`, which does lie in the module universe, and transported to `Ext`
along `Dualizing.extDerivedHomLinearEquiv`.

Three facts used here are `private` where they are proved and are reached by `import all` rather
than restated: `Stacks.AdicCompletion.PowerTorsionQuotient.isAdicComplete_of_pow_smul_top_eq_bot`
(a module killed by a power of `I` is `I`-adically complete),
`Dualizing.annihilator_le_ext_annihilator` (an ideal killing `M` kills `Ext^i_A(M, K)`) and
`Dualizing.moduleFinite_ext` (finiteness of `Ext` into a dualizing complex out of a finite
module).  A private name may appear in a proof but not in an exposed definition body, which is
why the definitions that depend on them carry `@[no_expose]`.

No `@[stacks]` attribute appears below: nothing here is a tagged assertion of the source, the
statements being the base-change inputs to the proof of [Stacks, Tag 0EHK].

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD)
* [Stacks Project, Tag 09B8](https://stacks.math.columbia.edu/tag/09B8)
* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

section FlatExt

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
  (F : DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} S))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]

/-- Base change of derived Hom out of a finite module and into a bounded below complex is an
isomorphism along a flat map of Noetherian rings: this is the third disjunct of
[Stacks, Tag 0A6A], the source being pseudo-coherent because it is a finite module over a
Noetherian ring. -/
public theorem isIso_derivedHomBaseChange_single [IsNoetherianRing A] (hflat : Module.Flat A S)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (L : DerivedCategory (ModuleCat.{u} A)) (hL : ∃ b : ℤ, L.IsGE b) :
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u} (algebraMap A S)
      F comparison
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) L) := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)
  have hXpc : StacksDraft.PseudoCoherence.IsPseudoCoherent X := by
    change StacksDraft.PseudoCoherence.IsModulePseudoCoherent (R := A) M
    exact (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
      X 0 M).2.2.mpr inferInstance
  exact Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, u} (algebraMap A S)
    F comparison X L
    (Or.inr (Or.inr (Or.inl ⟨RingHom.flat_algebraMap_iff.mpr hflat, hXpc, hL⟩)))

/-- **Flat base change for `Ext` out of a finite module.**  For a flat map `A → S` of Noetherian
rings, a finite `A`-module `M` and a bounded below `K ∈ D(A)`, the `S`-module
`Ext^i_S(S ⊗_A M, K ⊗ᴸ_A S)` is `S ⊗_A Ext^i_A(M, K)`. -/
public def extBaseChangeLinearEquiv [IsNoetherianRing A] (hflat : Module.Flat A S)
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{u} A)) (hKge : ∃ b : ℤ, K.IsGE b) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj
          ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).obj (ModuleCat.of A M)))
        (F.obj K) i ≃ₗ[S]
      S ⊗[A] DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) K i := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A S)
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)
  let cmpD : DerivedCategory.Q ⋙ D.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  let : D.functor.IsLeftDerivedFunctor cmpD
    (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := D.isLeftDerived
  let : D.functor.CommShift ℤ := D.commShift
  let hFD : F ≅ D.functor :=
    Functor.leftDerivedUnique D.functor F comparison cmpD
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
  have hKi : ∃ b : ℤ, (K⟦i⟧).IsGE b := by
    obtain ⟨b, _⟩ := hKge
    exact ⟨b - i, DerivedCategory.TStructure.t.isGE_shift K b i (b - i) (by omega)⟩
  let eX : F.obj X ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap A S)).obj (ModuleCat.of A M)) :=
    hFD.app X ≪≫ CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsSingleIso.{u, u, u}
      (algebraMap A S) (RingHom.flat_algebraMap_iff.mpr hflat) (ModuleCat.of A M)
  let eK : (F.obj K)⟦i⟧ ≅ F.obj (K⟦i⟧) :=
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} S)) i).mapIso (hFD.app K) ≪≫
      ((D.functor.commShiftIso i).app K).symm ≪≫ (hFD.app (K⟦i⟧)).symm
  exact (StacksDraft.DerivedHom.HomModuleBaseChange.homCongrLinearEquiv S eX eK).trans
    (StacksDraft.DerivedHom.HomModuleBaseChange.homBaseChangeLinearEquiv hflat F comparison X
      (K⟦i⟧) (isIso_derivedHomBaseChange_single F comparison hflat M (K⟦i⟧) hKi))

end FlatExt

/-! ### The finite module over the completion attached to an adic system -/

section AdicSystem

open CategoryTheory.Limits Opposite Stacks.Coherent Stacks.Examples

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)

/-- **An adic system of `A`-modules with finite bottom term has a finite module over `A^∧` as its
limit.**  The limit of the system is `I`-adically complete, and its completion -- which is what
carries the module structure over `A^∧` -- is a finite `A^∧`-module. -/
public theorem finite_adicCompletion_limit {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) (hfin : Module.Finite A (S.obj (op 0))) :
    Module.Finite (AdicCompletion I A) (AdicCompletion I (limit S : ModuleCat.{u} A)) :=
  finite_adicCompletion_of_finite_reduction I.fg_of_isNoetherianRing _
    (moduleLimit_zeroQuotient_finite S hS.1 hS.2 I.fg_of_isNoetherianRing hfin)

/-- `M / Iⁿ⁺¹ M` for `M = (lim S_m)^∧` the finite module over `A^∧` attached to the adic system
`S`; it is identified with `S_n` by `Dualizing.adicCompletionLimitQuotEquiv`. -/
public abbrev adicSystemQuot (S : ℕᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ) : Type u :=
  AdicCompletion I (limit S : ModuleCat.{u} A) ⧸
    ((I.map (algebraMap A (AdicCompletion I A))) ^ (n + 1) •
      (⊤ : Submodule (AdicCompletion I A) (AdicCompletion I (limit S : ModuleCat.{u} A))))

/-- **The reduction of the completed limit of an adic system recovers the system.**  For an adic
system `(S_n)` of `A`-modules, the quotient of `(lim S_n)^∧` by the `(n+1)`-st power of the
extended ideal is `S_n`.  The left-hand side is a module over `A^∧`, which is how the terms of
the system acquire a module structure over the completion. -/
public def adicCompletionLimitQuotEquiv {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) (n : ℕ) : adicSystemQuot I S n ≃ₗ[A] S.obj (op n) := by
  have hsub : ((I.map (algebraMap A (AdicCompletion I A))) ^ (n + 1) •
      (⊤ : Submodule (AdicCompletion I A)
        (AdicCompletion I (limit S : ModuleCat.{u} A)))).restrictScalars A =
      I ^ (n + 1) • (⊤ : Submodule A (AdicCompletion I (limit S : ModuleCat.{u} A))) := by
    rw [← Ideal.map_pow, Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top]
  exact (Submodule.Quotient.restrictScalarsEquiv A _).symm.trans
    ((Submodule.quotEquivOfEq _ _ hsub).trans
      ((AdicCompletion.quotPowSMulTopEquiv I.fg_of_isNoetherianRing
          (limit S : ModuleCat.{u} A) (n + 1)).trans
        (limitQuotientEquiv I.fg_of_isNoetherianRing ⟨S, hS⟩ n)))

/-- `Dualizing.adicCompletionLimitQuotEquiv` on a class: the class of `x` in `M / Iⁿ⁺¹ M` goes
to the `(n+1)`-st component of `x` read through the limit projection. Every step of the
composite is the identity on classes, so this is `rfl`; it is the identity the naturality below
is proved from. -/
public theorem adicCompletionLimitQuotEquiv_mk {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) (n : ℕ)
    (x : AdicCompletion I (limit S : ModuleCat.{u} A)) :
    adicCompletionLimitQuotEquiv I hS n (Submodule.Quotient.mk x) =
      limitQuotientEquiv I.fg_of_isNoetherianRing ⟨S, hS⟩ n (x.val (n + 1)) := rfl

/-- **`Dualizing.adicCompletionLimitQuotEquiv` is compatible with the transition maps.** The
transition of the tower of adic quotients fixes the class of `x`, so what has to be matched is
the `(n+1)`-st component of `x` against its `(m+1)`-st, and that is exactly the compatibility
condition carried by an element of the completion. -/
public theorem adicCompletionLimitQuotEquiv_comp {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion I (limit S : ModuleCat.{u} A)) :
    (S.map (homOfLE h).op).hom
        (adicCompletionLimitQuotEquiv I hS n (Submodule.Quotient.mk x)) =
      adicCompletionLimitQuotEquiv I hS m (Submodule.Quotient.mk x) := by
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
  rw [adicCompletionLimitQuotEquiv_mk, adicCompletionLimitQuotEquiv_mk, ← hy,
    limitQuotientEquiv_mk]
  have hx : x.val (m + 1) = Submodule.Quotient.mk y := by
    rw [← x.property (Nat.add_le_add_right h 1), ← hy]
    rfl
  rw [hx, limitQuotientEquiv_mk]
  exact congrArg (fun φ : (limit S : ModuleCat.{u} A) ⟶ S.obj (op m) => φ.hom y)
    (limit.w S (homOfLE h).op)

/-- `Dualizing.adicCompletionLimitQuotEquiv_comp` against an arbitrary morphism of the index
category: the homs of `ℕᵒᵖ` form a subsingleton, so any one of them is the `homOfLE` of its own
underlying inequality. -/
public theorem adicCompletionLimitQuotEquiv_naturality {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) {X Y : ℕᵒᵖ} (a : X ⟶ Y)
    (x : AdicCompletion I (limit S : ModuleCat.{u} A)) :
    (S.map a).hom (adicCompletionLimitQuotEquiv I hS X.unop (Submodule.Quotient.mk x)) =
      adicCompletionLimitQuotEquiv I hS Y.unop (Submodule.Quotient.mk x) := by
  rw [show a = (homOfLE (leOfHom a.unop)).op from Subsingleton.elim _ _]
  exact adicCompletionLimitQuotEquiv_comp I hS (leOfHom a.unop) x

/-- **An adic system is the tower of adic quotients of the finite module over `A^∧` attached to
it, as an isomorphism of systems.** The functor-level form of
`Dualizing.adicCompletionLimitQuotEquiv`, which is its component
(`Dualizing.adicSystemQuotNatIso_app`), so nothing is restated here and nothing downstream
changes.

The three things the per-object equivalence leaves open are settled as follows. The *indexing*
is `Stacks.Examples.adicQuotientTower`'s, `n ↦ N / Iⁿ⁺¹ N`, which is the one the terms of an
adic system match on the nose -- `AlgebraicGeometry.ProEtale.adicQuotientModuleSystem` uses
`n ↦ N / Iⁿ N` instead, and the two conventions differ by a shift of one. The *naturality* is
`Dualizing.adicCompletionLimitQuotEquiv_naturality`. The *ring* the identification is linear
over is `A` here, as it is for the component; an `A`-linear map between modules over `A^∧` is
automatically `A^∧`-linear by `Stacks.Coherent.completion_linearMap_smul`, and naturality is an
equation between maps, so it is inherited by the `A^∧`-linear upgrade of each component --
`Dualizing.extendScalarsAdicSystemIso` performs exactly that upgrade at one index. -/
public def adicSystemQuotNatIso {S : ℕᵒᵖ ⥤ ModuleCat.{u} A} (hS : IsAdicModuleSystem I S) :
    Stacks.Examples.adicQuotientTower (I.map (algebraMap A (AdicCompletion I A)))
        (ModuleCat.of (AdicCompletion I A)
          (AdicCompletion I (limit S : ModuleCat.{u} A))) ⋙
      ModuleCat.restrictScalars (algebraMap A (AdicCompletion I A)) ≅ S :=
  NatIso.ofComponents (fun n => (adicCompletionLimitQuotEquiv I hS n.unop).toModuleIso)
    fun {X Y} a => by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (adicCompletionLimitQuotEquiv_naturality I hS a y).symm

/-- The components of `Dualizing.adicSystemQuotNatIso` are
`Dualizing.adicCompletionLimitQuotEquiv`. -/
public theorem adicSystemQuotNatIso_app {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) (n : ℕᵒᵖ) :
    (adicSystemQuotNatIso I hS).app n =
      (adicCompletionLimitQuotEquiv I hS n.unop).toModuleIso := rfl

/-- **A finite module annihilated by a power of `I` is unchanged by base change to the
completion.**  Base change of a finite module to `A^∧` is its `I`-adic completion, and a module
annihilated by a power of `I` is already complete. -/
@[no_expose] public def tensorAdicCompletionEquivOfPowSMulTopEqBot (N : Type u)
    [AddCommGroup N] [Module A N] [Module.Finite A N] {k : ℕ}
    (hN : I ^ k • (⊤ : Submodule A N) = ⊥) : AdicCompletion I A ⊗[A] N ≃ₗ[A] N :=
  letI : IsAdicComplete I N :=
    Stacks.AdicCompletion.PowerTorsionQuotient.isAdicComplete_of_pow_smul_top_eq_bot hN
  ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I N).restrictScalars A).trans
    (LinearEquiv.ofBijective (AdicCompletion.of I N) (AdicCompletion.of_bijective I N)).symm

/-- **The terms of an adic system, as modules over the completion.**  For an adic system `(S_m)`
of finite `A`-modules, the base change of `S_n` to `A^∧` is `M / Iⁿ⁺¹ M` for `M` the finite
`A^∧`-module attached to the system. -/
@[no_expose] public def extendScalarsAdicSystemIso
    {S : ℕᵒᵖ ⥤ ModuleCat.{u} A} (hS : IsAdicModuleSystem I S)
    (hfin : ∀ m : ℕ, Module.Finite A (S.obj (op m))) (n : ℕ) :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion I A))).obj
        (S.obj (op n)) ≅
      ModuleCat.of (AdicCompletion I A) (adicSystemQuot I S n) := by
  letI := hfin n
  letI hc : IsAdicComplete I (S.obj (op n) : Type u) :=
    Stacks.AdicCompletion.PowerTorsionQuotient.isAdicComplete_of_pow_smul_top_eq_bot
      (hS.pow_smul_top_eq_bot n)
  let e3 : (S.obj (op n) : Type u) ≃ₗ[A] adicSystemQuot I S n :=
    (adicCompletionLimitQuotEquiv I hS n).symm
  letI : IsAdicComplete I (adicSystemQuot I S n) := isAdicComplete_of_linearEquiv I e3.symm hc
  let eA : AdicCompletion I A ⊗[A] (S.obj (op n) : Type u) ≃ₗ[A] adicSystemQuot I S n :=
    (tensorAdicCompletionEquivOfPowSMulTopEqBot I (S.obj (op n) : Type u)
      (hS.pow_smul_top_eq_bot n)).trans e3
  let eB : AdicCompletion I A ⊗[A] (S.obj (op n) : Type u) ≃ₗ[AdicCompletion I A]
      adicSystemQuot I S n :=
    { eA.toAddEquiv with
      map_smul' := completion_linearMap_smul I I.fg_of_isNoetherianRing eA.toLinearMap }
  exact ((StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv
    (A := AdicCompletion I A) (S.obj (op n))).trans eB).toModuleIso

/-- **`Dualizing.tensorAdicCompletionEquivOfPowSMulTopEqBot` is the identity on `1 ⊗ x`.**
`AdicCompletion.ofTensorProduct` sends `1 ⊗ x` to the image of `x` under `AdicCompletion.of`,
and for a module killed by a power of `I` that map is the bijection the equivalence inverts.

The equivalence is `no_expose`, so this is the only handle on it from outside its definition, and
it is what makes the isomorphism of systems below provable: a morphism out of an extension of
scalars is determined by its values on the elements `1 ⊗ x`
(`ModuleCat.ExtendScalars.hom_ext`). -/
@[sga "2 IV 4.5" "special case"]
public theorem tensorAdicCompletionEquivOfPowSMulTopEqBot_one_tmul (N : Type u)
    [AddCommGroup N] [Module A N] [Module.Finite A N] {k : ℕ}
    (hN : I ^ k • (⊤ : Submodule A N) = ⊥) (x : N) :
    tensorAdicCompletionEquivOfPowSMulTopEqBot I N hN ((1 : AdicCompletion I A) ⊗ₜ x) = x := by
  let : IsAdicComplete I N :=
    Stacks.AdicCompletion.PowerTorsionQuotient.isAdicComplete_of_pow_smul_top_eq_bot hN
  change (LinearEquiv.ofBijective (AdicCompletion.of I N)
      (AdicCompletion.of_bijective I N)).symm
    ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I N)
      ((1 : AdicCompletion I A) ⊗ₜ x)) = x
  rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply,
    AdicCompletion.ofTensorProduct_tmul, one_smul]
  exact (LinearEquiv.ofBijective (AdicCompletion.of I N)
    (AdicCompletion.of_bijective I N)).symm_apply_apply x

/-- **`Dualizing.extendScalarsAdicSystemIso` on `1 ⊗ x`.** The `A^∧`-linear identification of the
base change of `S_n` with `M / Iⁿ⁺¹ M` agrees on `1 ⊗ x` with the `A`-linear identification
`Dualizing.adicCompletionLimitQuotEquiv` of the same two modules, read backwards.

Both of the equivalences the construction inserts are the identity on such an element: the
underlying-module comparison
`StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv` only moves the
`A`-action carried by `A^∧`, and
`Dualizing.tensorAdicCompletionEquivOfPowSMulTopEqBot_one_tmul` is the statement above. -/
public theorem extendScalarsAdicSystemIso_hom_one_tmul
    {S : ℕᵒᵖ ⥤ ModuleCat.{u} A} (hS : IsAdicModuleSystem I S)
    (hfin : ∀ m : ℕ, Module.Finite A (S.obj (op m))) (n : ℕ) (x : (S.obj (op n) : Type u)) :
    (extendScalarsAdicSystemIso I hS hfin n).hom.hom
        ((1 : AdicCompletion I A) ⊗ₜ[A, algebraMap A (AdicCompletion I A)] x) =
      (adicCompletionLimitQuotEquiv I hS n).symm x := by
  let := hfin n
  exact congrArg (adicCompletionLimitQuotEquiv I hS n).symm
    (tensorAdicCompletionEquivOfPowSMulTopEqBot_one_tmul I _ (hS.pow_smul_top_eq_bot n) x)

/-- **The transition maps of `Dualizing.adicCompletionLimitQuotEquiv` read backwards.** The
inverse identifications carry the transition map of the system to the exponent-lowering map of the
tower of adic quotients.  This is `Dualizing.adicCompletionLimitQuotEquiv_naturality` with both
equivalences inverted; the transition of the tower fixes the class of an element, which is why no
further computation appears. -/
public theorem adicCompletionLimitQuotEquiv_symm_naturality {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) {X Y : ℕᵒᵖ} (a : X ⟶ Y) (x : (S.obj X : Type u)) :
    (adicCompletionLimitQuotEquiv I hS Y.unop).symm ((S.map a).hom x) =
      ((Stacks.Examples.adicQuotientTower (I.map (algebraMap A (AdicCompletion I A)))
        (ModuleCat.of (AdicCompletion I A)
          (AdicCompletion I (limit S : ModuleCat.{u} A)))).map a).hom
        ((adicCompletionLimitQuotEquiv I hS X.unop).symm x) := by
  obtain ⟨q, rfl⟩ := (adicCompletionLimitQuotEquiv I hS X.unop).surjective x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [LinearEquiv.symm_apply_apply, adicCompletionLimitQuotEquiv_naturality I hS a y,
    LinearEquiv.symm_apply_apply,
    show a = (homOfLE (leOfHom a.unop)).op from Subsingleton.elim _ _,
    Stacks.Examples.adicQuotientTower_map]
  exact (Submodule.factor_mk _ y).symm

/-- **An adic system of finite `A`-modules base-changed to `A^∧` is the tower of adic quotients of
the finite `A^∧`-module attached to it, as an isomorphism of systems.** The `A^∧`-linear,
functor-level form of `Dualizing.adicSystemQuotNatIso`, whose component at one index is
`Dualizing.extendScalarsAdicSystemIso` (`Dualizing.extendScalarsAdicSystemNatIso_app`), so
nothing is restated and the existing per-object equivalence is untouched.

*Why this is available although
`Dualizing.tensorAdicCompletionEquivOfPowSMulTopEqBot` carries no compatibility with the
transition maps.* Naturality is an equation between two `A^∧`-linear maps out of an extension of
scalars, and such a map is determined by its values on the elements `1 ⊗ x`
(`ModuleCat.ExtendScalars.hom_ext`). On those elements the component is the `A`-linear
`Dualizing.adicCompletionLimitQuotEquiv` read backwards
(`Dualizing.extendScalarsAdicSystemIso_hom_one_tmul`), whose compatibility with the transitions
*is* available -- it is `Dualizing.adicCompletionLimitQuotEquiv_naturality`, the same fact that
makes `Dualizing.adicSystemQuotNatIso` natural. So the missing compatibility is never needed: the
tensor equivalence is only ever evaluated at `1 ⊗ x`, where it is the identity. -/
public def extendScalarsAdicSystemNatIso {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) (hfin : ∀ m : ℕ, Module.Finite A (S.obj (op m))) :
    S ⋙ ModuleCat.extendScalars.{u, u, u} (algebraMap A (AdicCompletion I A)) ≅
      Stacks.Examples.adicQuotientTower (I.map (algebraMap A (AdicCompletion I A)))
        (ModuleCat.of (AdicCompletion I A)
          (AdicCompletion I (limit S : ModuleCat.{u} A))) :=
  NatIso.ofComponents (fun n => extendScalarsAdicSystemIso I hS hfin n.unop)
    fun {X Y} a => ModuleCat.ExtendScalars.hom_ext fun x => by
      change (extendScalarsAdicSystemIso I hS hfin Y.unop).hom.hom
          ((1 : AdicCompletion I A) ⊗ₜ[A, algebraMap A (AdicCompletion I A)]
            ((S.map a).hom x)) =
        ((Stacks.Examples.adicQuotientTower (I.map (algebraMap A (AdicCompletion I A)))
          (ModuleCat.of (AdicCompletion I A)
            (AdicCompletion I (limit S : ModuleCat.{u} A)))).map a).hom
          ((extendScalarsAdicSystemIso I hS hfin X.unop).hom.hom
            ((1 : AdicCompletion I A) ⊗ₜ[A, algebraMap A (AdicCompletion I A)] x))
      rw [extendScalarsAdicSystemIso_hom_one_tmul, extendScalarsAdicSystemIso_hom_one_tmul]
      exact adicCompletionLimitQuotEquiv_symm_naturality I hS a x

/-- The components of `Dualizing.extendScalarsAdicSystemNatIso` are
`Dualizing.extendScalarsAdicSystemIso`. -/
public theorem extendScalarsAdicSystemNatIso_app {S : ℕᵒᵖ ⥤ ModuleCat.{u} A}
    (hS : IsAdicModuleSystem I S) (hfin : ∀ m : ℕ, Module.Finite A (S.obj (op m))) (n : ℕᵒᵖ) :
    (extendScalarsAdicSystemNatIso I hS hfin).app n =
      extendScalarsAdicSystemIso I hS hfin n.unop := rfl

/-! ### `Ext` into a dualizing complex and the completion -/

omit [IsNoetherianRing A] in
/-- **`Ext^i_A(M, ω)` is annihilated by every ideal annihilating `M`**: multiplication by `a` on
`Ext` is precomposition with `a • 𝟙`, which is zero on the module placed in degree zero. -/
public theorem smul_top_ext_eq_bot (M : Type u) [AddCommGroup M] [Module A M]
    {J : Ideal A} (hM : J • (⊤ : Submodule A M) = ⊥)
    (ω : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    J • (⊤ : Submodule A (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) ω i)) = ⊥ := by
  have hMann : J ≤ Module.annihilator A M :=
    Submodule.annihilator_top (R := A) (M := M) ▸ Submodule.le_annihilator_iff.mpr hM
  refine Submodule.le_annihilator_iff.mp ?_
  rw [Submodule.annihilator_top]
  exact hMann.trans (annihilator_le_ext_annihilator A M ω i)

/-- **`Ext` into a dualizing complex out of a module killed by a power of `I` is unchanged by
base change to the completion.**  `Ext^i_A(M, ω)` is a finite `A`-module killed by the same power
of `I` as `M`, hence already `I`-adically complete, so tensoring with `A^∧` does nothing to it.

The identification is made on `H^i(RHom_A(M, ω))` rather than on `Ext^i_A(M, ω)` itself, the two
being identified by `Dualizing.extDerivedHomLinearEquiv`: the base change of a finite module to
its completion is available only for modules in the universe of the ring, and `Ext` lives one
universe higher. -/
@[no_expose] public def tensorAdicCompletionExtEquiv (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] {k : ℕ} (hM : I ^ k • (⊤ : Submodule A M) = ⊥)
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) (i : ℤ) :
    AdicCompletion I A ⊗[A] DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) ω i ≃ₗ[A]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) ω i := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)
  let e := extDerivedHomLinearEquiv A ω i X
  letI : Module.Finite A (DerivedCategory.Ext X ω i) := moduleFinite_ext (M := M) ω hω i
  letI : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((dualizingDerivedHomFunctor A ω).obj (.op X))) := Module.Finite.equiv e
  have hH : I ^ k • (⊤ : Submodule A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((dualizingDerivedHomFunctor A ω).obj (.op X)))) = ⊥ := by
    have hEann : I ^ k ≤ Module.annihilator A (DerivedCategory.Ext X ω i) :=
      Submodule.annihilator_top (R := A) (M := DerivedCategory.Ext X ω i) ▸
        Submodule.le_annihilator_iff.mpr (smul_top_ext_eq_bot M hM ω i)
    refine Submodule.le_annihilator_iff.mp ?_
    rw [Submodule.annihilator_top]
    intro a ha
    refine Module.mem_annihilator.mpr fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← e.map_smul, Module.mem_annihilator.mp (hEann ha) y, map_zero]
  exact (TensorProduct.congr (LinearEquiv.refl A (AdicCompletion I A)) e).trans
    ((tensorAdicCompletionEquivOfPowSMulTopEqBot I _ hH).trans e.symm)

/-- **`Ext` into the dualizing complex, before and after completing.**  Let `A` be Noetherian
with a dualizing complex `ω`, let `(S_n)` be an adic system of finite `A`-modules along an ideal
`I`, and let `M = (lim S_n)^∧` be the finite module over `B = A^∧` it determines.  Then

`Ext^i_B(M / Iⁿ⁺¹ M, ω ⊗ᴸ_A B) ≅ Ext^i_A(S_n, ω)`.

The two steps are flat base change for `Ext` along `A → B` -- `B` is flat over `A` and `S_n` is
finite, so `Dualizing.extBaseChangeLinearEquiv` applies -- and the fact that neither `S_n` nor
`Ext^i_A(S_n, ω)` changes under base change to `B`, both being killed by `Iⁿ⁺¹`.  The derived
base change `ω ⊗ᴸ_A B` is read at an arbitrary total left derived functor of termwise extension
of scalars; taking `(ModuleCat.extendScalars _).mapDerivedCategory` gives the dualizing complex
of `B` provided by `Dualizing.isDualizingComplex_adicCompletion`.

The first step is `B`-linear and the second `A`-linear, so the composite is stated additively;
`Dualizing.extBaseChangeLinearEquiv` and `Dualizing.tensorAdicCompletionExtEquiv` are the two
linear halves. -/
public def extAdicSystemCompletionAddEquiv
    (F : DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (AdicCompletion I A)))
    (comparison : DerivedCategory.Q ⋙ F ⟶
      (ModuleCat.extendScalars.{u, u, u}
          (algebraMap A (AdicCompletion I A))).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [F.IsLeftDerivedFunctor comparison
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))]
    {S : ℕᵒᵖ ⥤ ModuleCat.{u} A} (hS : IsAdicModuleSystem I S)
    (hfin : ∀ m : ℕ, Module.Finite A (S.obj (op m)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) (n : ℕ) (i : ℤ) :
    DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (AdicCompletion I A)) 0).obj
          (ModuleCat.of (AdicCompletion I A) (adicSystemQuot I S n)))
        (F.obj ω) i ≃+
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (S.obj (op n) : Type u))) ω i := by
  letI := hfin n
  have hωge : ∃ b : ℤ, ω.IsGE b := hω.bounded.1
  let eS := (DerivedCategory.singleFunctor (ModuleCat.{u} (AdicCompletion I A)) 0).mapIso
    (extendScalarsAdicSystemIso I hS hfin n)
  let e0 := StacksDraft.DerivedHom.HomModuleBaseChange.homCongrLinearEquiv
    (AdicCompletion I A) eS (Iso.refl ((F.obj ω)⟦i⟧))
  let e1 := extBaseChangeLinearEquiv F comparison (AdicCompletion.flat_of_isNoetherian I)
    (S.obj (op n) : Type u) ω hωge i
  let e2 := tensorAdicCompletionExtEquiv I (S.obj (op n) : Type u)
    (hS.pow_smul_top_eq_bot n) ω hω i
  exact (e0.toAddEquiv.trans e1.toAddEquiv).trans e2.toAddEquiv

end AdicSystem

end Dualizing

end
