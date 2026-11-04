module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.PseudoCoherent
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.AdicSystem
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleRlimTensorLimit
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.LiftAcyclicComplex
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor

@[expose] public noncomputable section

/-!
# Adic cohomology of a pseudo-coherent complex

Let `I` be an ideal in a Noetherian ring `A` and let `K` be a pseudo-coherent object of
`D(A)`. The cohomology modules of the derived reductions `K ⊗ᴸ[A] A/Iⁿ` form
Mittag--Leffler inverse systems, and their inverse limits agree with the adic completions of
the cohomology modules of `K`.

## Main definitions

There are no new definitions.

## Main results

* `pseudoCoherent_mittagLeffler_and_adicCompletion_iso_limit_derivedReduction`:
  the Kollár--Kovács Mittag--Leffler and completion theorem for a pseudo-coherent object.

## Implementation notes

Positive powers of `I` are indexed by `n : ℕ` using `I ^ (n + 1)`, as in
`NoetherianAdicCompletion.idealPowerQuotientSystem`. Equality of inverse limits is expressed as
an isomorphism of `A`-modules. A derived tensor product is supplied together with its canonical
comparison to tensor products of K-flat representatives.

A bounded-above complex of finite free modules is K-flat, so its derived reductions are computed
by degreewise reduction. The resulting inverse system of homology modules is the one whose
Artin--Rees behaviour Stacks 0EGU controls, which is where the Mittag--Leffler condition comes
from; feeding it to Stacks 0EGS identifies the limit with the adic completion.

## References

* [Stacks Project, Tag 0EGV](https://stacks.math.columbia.edu/tag/0EGV)
* Email from Sándor Kovács, 23 February 2018.
-/

open CategoryTheory CategoryTheory.Limits Opposite LiftAcyclic

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.PseudoCoherent.AdicCompletion

open Stacks.AdicSystem.DerivedReductionProIso (reductionNatTrans
  reducedHomologyConcreteEquiv reducedHomologyConcreteEquiv_ideal_naturality
  reductionCyclesMapOfIdealLE concreteHomologyIdealTransition quotientModuleMap
  extendedSingleQuotientTensorIsoReduction
  extendedSingleQuotientTensorIsoReduction_naturality)

/-! ### Mittag--Leffler transport -/

private theorem isMittagLeffler_of_natIso {C : Type v} [Category C]
    {F G : C ⥤ Type w} (e : F ≅ G) (h : F.IsMittagLeffler) : G.IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := h j
  refine ⟨i, f, ?_⟩
  rintro k g x ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hf g ⟨e.inv.app i y, rfl⟩
  refine ⟨e.hom.app k z, ?_⟩
  have hn {a b : C} (t : a ⟶ b) (x : F.obj a) :
      e.hom.app b (F.map t x) = G.map t (e.hom.app a x) :=
    congrArg (fun t => t x) (e.hom.naturality t)
  rw [← hn, hz, hn]
  congr 1
  exact congrArg (fun t => t y) (e.inv_hom_id_app i)

private theorem isMittagLeffler_successor (F : ℕᵒᵖ ⥤ Type u)
    (h : F.IsMittagLeffler) :
    (Stacks.AdicSystem.DerivedReductionProIso.successorOp ⋙ F).IsMittagLeffler := by
  intro j
  obtain ⟨i, f, hf⟩ := h (Stacks.AdicSystem.DerivedReductionProIso.successorOp.obj j)
  let t : Stacks.AdicSystem.DerivedReductionProIso.successorOp.obj i ⟶ i :=
    (homOfLE (Nat.le_succ i.unop)).op
  let s : i ⟶ j := (homOfLE (Nat.le_trans (Nat.le_succ j.unop)
    (leOfHom f.unop))).op
  refine ⟨i, s, ?_⟩
  rintro k g x ⟨y, rfl⟩
  apply hf (Stacks.AdicSystem.DerivedReductionProIso.successorOp.map g)
  refine ⟨F.map t y, ?_⟩
  show (F.map t ≫ F.map f) y =
    F.map (Stacks.AdicSystem.DerivedReductionProIso.successorOp.map s) y
  rw [← F.map_comp]
  rfl

section

variable {A : Type u} [CommRing A]

open CategoryTheory.MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

/-- The inverse system of degreewise reductions of `P` modulo the positive powers of `I`. -/
def degreewiseReductionSystem (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  Functor.ofOpSequence (X := fun n => (reduceComplex (I ^ (n + 1))).obj P)
    (fun n => (NatTrans.mapHomologicalComplex
      (reductionNatTrans (Ideal.pow_le_pow_right
        (Nat.add_le_add_right (Nat.le_succ n) 1))) (ComplexShape.up ℤ)).app P)

/-- A natural isomorphism of `ℕᵒᵖ`-indexed diagrams built from componentwise isomorphisms
compatible with the successor transitions. -/
private def natIsoOfOpSequence
    {C : Type*} [Category C] {F G : ℕᵒᵖ ⥤ C}
    (e : ∀ n : ℕ, F.obj (op n) ≅ G.obj (op n))
    (h : ∀ n, F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
      (e (n + 1)).hom ≫ G.map (homOfLE (Nat.le_succ n)).op) : F ≅ G :=
  NatIso.ofComponents (fun n => e n.unop)
    (fun {_ _} f => (NatTrans.ofOpSequence (fun n => (e n).hom) h).naturality f)

/-- For a K-flat complex, the derived tensor product with `A/I` is its degreewise reduction. -/
private def derivedQuotientTensorIsoReduction
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) (I : Ideal A) :
    (T.tensor.obj (DerivedCategory.Q.obj P)).obj
      (DerivedCategory.Q.obj (((ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A (A ⧸ I))).extend ComplexShape.embeddingDownNat)) ≅
      DerivedCategory.Q.obj ((reduceComplex I).obj P) := by
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory A).choose
  let E := ((ChainComplex.single₀ (ModuleCat.{u} A)).obj
    (ModuleCat.of A (A ⧸ I))).extend ComplexShape.embeddingDownNat
  exact (ModuleSystemRlimTensor.derivedTensorComplexComparison A T P hP).app E ≪≫
    DerivedCategory.Q.mapIso
      ((β_ P E) ≪≫ extendedSingleQuotientTensorIsoReduction I P)

private lemma derivedQuotientTensorIsoReduction_naturality
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)
    {I J : Ideal A} (h : I ≤ J) :
    (T.tensor.obj (DerivedCategory.Q.obj P)).map
      (DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((ChainComplex.single₀ (ModuleCat.{u} A)).map (quotientModuleMap h))
        ComplexShape.embeddingDownNat)) ≫
        (derivedQuotientTensorIsoReduction T P hP J).hom =
      (derivedQuotientTensorIsoReduction T P hP I).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (reductionNatTrans h) (ComplexShape.up ℤ)).app P) := by
  let := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory A).choose
  let f := HomologicalComplex.extendMap
    ((ChainComplex.single₀ (ModuleCat.{u} A)).map (quotientModuleMap h))
    ComplexShape.embeddingDownNat
  have hn :=
    (ModuleSystemRlimTensor.derivedTensorComplexComparison A T P hP).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  dsimp only [derivedQuotientTensorIsoReduction, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [← Category.assoc, hn, Category.assoc]
  simp only [Category.assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  have hbraid : (TleftCochain P).map f ≫ (β_ P _).hom =
      (β_ P _).hom ≫ (TrightCochain P).map f :=
    BraidedCategory.braiding_naturality_right P f
  rw [← Category.assoc, hbraid, Category.assoc,
    extendedSingleQuotientTensorIsoReduction_naturality]
  simp only [Category.assoc]

private lemma quotientFactor_eq_quotientModuleMap {I J : Ideal A} (h : I ≤ J) :
    NoetherianAdicCompletion.quotientFactor h = quotientModuleMap h := rfl

/-- For a K-flat complex, the inverse system of derived reductions is the inverse system of
degreewise reductions. -/
@[no_expose]
def derivedReductionSystemIsoDegreewise (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj (DerivedCategory.Q.obj P) ≅
      degreewiseReductionSystem I P ⋙ DerivedCategory.Q := by
  refine natIsoOfOpSequence
    (fun n => derivedQuotientTensorIsoReduction T P hP (I ^ (n + 1))) ?_
  intro n
  simp only [Functor.comp_map, NoetherianAdicCompletion.idealPowerQuotientSystem_map,
    degreewiseReductionSystem, Functor.ofOpSequence_map_homOfLE_succ,
    NoetherianAdicCompletion.derivedQuotientFactor, quotientFactor_eq_quotientModuleMap]
  exact derivedQuotientTensorIsoReduction_naturality T P hP _

/-! ### The Mittag--Leffler condition -/

/-- The concrete homology of a reduced two-term complex. -/
abbrev degreewiseReductionHomologyModule (I : Ideal A) (S : ShortComplex (ModuleCat.{u} A)) :=
  ((I • (⊤ : Submodule A S.X₃)).comap S.g.hom) ⧸
    (LinearMap.range S.f.hom ⊔ I • (⊤ : Submodule A S.X₂)).comap
      ((I • (⊤ : Submodule A S.X₃)).comap S.g.hom).subtype

/-- The inverse system of concrete homology modules of the reductions of `P` modulo the powers
of `I`. -/
def degreewiseReductionHomologySystem (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  Functor.ofOpSequence
    (X := fun n => ModuleCat.of A (degreewiseReductionHomologyModule (I ^ n) (P.sc i)))
    (fun n => ModuleCat.ofHom (concreteHomologyIdealTransition
      (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
      (P.sc i).f (P.sc i).g (P.sc i).zero))

/-- The inverse system of homology modules of the degreewise reductions of `P`, read along the
successor reindexing, is the concrete homology system `degreewiseReductionHomologySystem`. -/
@[no_expose]
def degreewiseReductionHomologySystemIso (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    Stacks.AdicSystem.DerivedReductionProIso.successorOp ⋙
        degreewiseReductionHomologySystem I P i ≅
      degreewiseReductionSystem I P ⋙ HomologicalComplex.homologyFunctor
        (ModuleCat.{u} A) (ComplexShape.up ℤ) i := by
  refine natIsoOfOpSequence
    (fun n => (reducedHomologyConcreteEquiv (I ^ (n + 1)) P i).toModuleIso) ?_
  intro n
  change (degreewiseReductionHomologySystem I P i).map
    (homOfLE (Nat.le_succ (n + 1))).op ≫ _ = _
  simp only [degreewiseReductionHomologySystem, degreewiseReductionSystem, Functor.comp_map,
    Functor.ofOpSequence_map_homOfLE_succ]
  exact ModuleCat.hom_ext (LinearMap.ext fun x =>
    (reducedHomologyConcreteEquiv_ideal_naturality
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)) : I ^ (n + 1 + 1) ≤ I ^ (n + 1))
      P i x).symm)

/-! ### The base names of the degreewise reduction systems -/

/-- The inverse system of degreewise reductions of `P` modulo the positive powers of `I`. -/
private def reductionSystem (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  degreewiseReductionSystem I P

/-- For a K-flat complex, the inverse system of derived reductions is the inverse system of
degreewise reductions. -/
private def derivedReductionSystemIso (I : Ideal A)
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj (DerivedCategory.Q.obj P) ≅
      reductionSystem I P ⋙ DerivedCategory.Q :=
  derivedReductionSystemIsoDegreewise I T P hP

/-- The concrete homology of a reduced two-term complex. -/
private abbrev reductionHomologyModule (I : Ideal A) (S : ShortComplex (ModuleCat.{u} A)) :=
  degreewiseReductionHomologyModule I S

/-- The inverse system of concrete homology modules of the reductions of `P` modulo the powers
of `I`. -/
private def concreteReductionHomologySystem (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  degreewiseReductionHomologySystem I P i

private def reductionHomologySystemIso (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    Stacks.AdicSystem.DerivedReductionProIso.successorOp ⋙ concreteReductionHomologySystem I P i ≅
      reductionSystem I P ⋙ HomologicalComplex.homologyFunctor
        (ModuleCat.{u} A) (ComplexShape.up ℤ) i :=
  degreewiseReductionHomologySystemIso I P i

private lemma exists_homologyTransition_mittagLeffler [IsNoetherianRing A]
    (I : Ideal A) {K L M : ModuleCat.{u} A}
    [Module.Finite A K] [Module.Finite A L] [Module.Finite A M]
    (α : K ⟶ L) (β : L ⟶ M) (hcomplex : α ≫ β = 0) :
    let cycles : ℕ → Submodule A L := fun n => (I ^ n • (⊤ : Submodule A M)).comap β.hom
    let boundaries : ℕ → Submodule A L := fun n => LinearMap.range α.hom ⊔ I ^ n • ⊤
    let Hn : ℕ → Type u := fun n => cycles n ⧸ (boundaries n).comap (cycles n).subtype
    ∃ transition : ∀ n, Hn (n + 1) →ₗ[A] Hn n,
      (∀ n (x : cycles (n + 1)) (y : cycles n), (y : L) = x →
        transition n (Submodule.Quotient.mk x) = Submodule.Quotient.mk y) ∧
      ((Functor.ofOpSequence (X := fun n => ModuleCat.of A (Hn n))
        (fun n => ModuleCat.ofHom (transition n))) ⋙
          forget (ModuleCat.{u} A)).IsMittagLeffler := by
  obtain ⟨toLevel, transition, quotTransition, fromQuotient, hh⟩ :=
    Stacks.AdicSystem.ArtinReesHomology.exists_uniform_adic_homology_comparison I α.hom β.hom
      (congrArg ModuleCat.Hom.hom hcomplex)
  refine ⟨transition, hh.2.1, ?_⟩
  obtain ⟨c, hc, back, hb⟩ := hh.2.2.2.2.2
  exact hb.2.2.2.2.1

private lemma concreteReductionHomologySystem_mittagLeffler [IsNoetherianRing A]
    (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ n, Module.Finite A (P.X n)) (i : ℤ) :
    (concreteReductionHomologySystem I P i ⋙ forget (ModuleCat.{u} A)).IsMittagLeffler := by
  have : Module.Finite A (P.sc i).X₁ := hP _
  have : Module.Finite A (P.sc i).X₂ := hP _
  have : Module.Finite A (P.sc i).X₃ := hP _
  obtain ⟨transition, htransition, hML⟩ :=
    exists_homologyTransition_mittagLeffler I (P.sc i).f (P.sc i).g (P.sc i).zero
  have ht : transition = fun n => concreteHomologyIdealTransition
      (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
      (P.sc i).f (P.sc i).g (P.sc i).zero := by
    funext n
    refine LinearMap.ext fun x => ?_
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact htransition n x (reductionCyclesMapOfIdealLE
      (Ideal.pow_le_pow_right (Nat.le_succ n)) (P.sc i).g x) rfl
  subst transition
  exact hML

/-- **Mittag--Leffler for the concrete cohomology of the adic reductions of a complex of finite
modules.** For a complex `P` of finite modules over a Noetherian ring `A`, an ideal `I` and a
degree `i`, the inverse system `n ↦ Zⁱ(P/IⁿP) / Bⁱ(P/IⁿP)`, written through the cycles
`d⁻¹(Iⁿ P^{i+1})` of `P^i` and the boundaries `im d + Iⁿ P^i`, with the transition maps induced
by `Iⁿ⁺¹ ≤ Iⁿ`, satisfies the Mittag--Leffler condition. -/
theorem isMittagLeffler_concreteReductionHomology [IsNoetherianRing A]
    (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ n, Module.Finite A (P.X n)) (i : ℤ) :
    ((Functor.ofOpSequence
      (X := fun n => ModuleCat.of A
        (((I ^ n • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom) ⧸
          (LinearMap.range (P.sc i).f.hom ⊔ I ^ n • (⊤ : Submodule A (P.sc i).X₂)).comap
            ((I ^ n • (⊤ : Submodule A (P.sc i).X₃)).comap (P.sc i).g.hom).subtype))
      (fun n => ModuleCat.ofHom (concreteHomologyIdealTransition
        (Ideal.pow_le_pow_right (Nat.le_succ n) : I ^ (n + 1) ≤ I ^ n)
        (P.sc i).f (P.sc i).g (P.sc i).zero))) ⋙
        forget (ModuleCat.{u} A)).IsMittagLeffler :=
  concreteReductionHomologySystem_mittagLeffler I P hP i

private lemma reductionHomology_mittagLeffler [IsNoetherianRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∀ n, Module.Finite A (P.X n)) (i : ℤ) :
    ((reductionSystem I P ⋙ HomologicalComplex.homologyFunctor
      (ModuleCat.{u} A) (ComplexShape.up ℤ) i) ⋙
        forget (ModuleCat.{u} A)).IsMittagLeffler :=
  isMittagLeffler_of_natIso
    (Functor.isoWhiskerRight (reductionHomologySystemIso I P i) (forget (ModuleCat.{u} A)))
    (isMittagLeffler_successor _ (concreteReductionHomologySystem_mittagLeffler I P hP i))

private lemma finite_homology_of_pseudoCoherent [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{u} A))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (i : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  have : Module.Finite A (P.sc i).X₂ := (hP.finiteFree i).1
  have : Module.Finite A (LinearMap.ker (P.sc i).g.hom) := inferInstance
  have : Module.Finite A (P.sc i).moduleCatLeftHomologyData.H :=
    Module.Finite.quotient A (LinearMap.range (P.sc i).moduleCatToCycles)
  let d := (P.sc i).moduleCatHomologyIso.symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i).symm.app P ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso e
  exact Module.Finite.equiv d.toLinearEquiv

end

section

open CategoryTheory.MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

/-- **Stacks 0EGV (Kollár--Kovács).** If `K` is a pseudo-coherent object of `D(A)` for a
Noetherian ring `A`, then in every degree the cohomology of its reductions modulo the positive
powers of `I` is Mittag--Leffler, and its inverse limit is the `I`-adic completion of the
cohomology of `K`. -/
@[stacks 0EGV]
theorem pseudoCoherent_mittagLeffler_and_adicCompletion_iso_limit_derivedReduction
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    ∀ i : ℤ,
      (((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ⋙
        forget (ModuleCat.{u} A)).IsMittagLeffler ∧
      Nonempty
        (ModuleCat.of A
            (AdicCompletion I
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ≅
          limit ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hP.upperBound
  have : P.IsStrictlyLE b := hb
  have : ∀ n, Module.Flat A (P.X n) := fun n => by
    have : Module.Free A (P.X n) := (hP.finiteFree n).2
    infer_instance
  have hflat : P.KFlat := CochainComplex.KFlat.kFlat_of_flat P b
  have hML : ∀ i : ℤ,
      (((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ⋙
          forget (ModuleCat.{u} A)).IsMittagLeffler := by
    intro i
    let d : (NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙
        T.tensor.obj (DerivedCategory.Q.obj P)) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ≅
        reductionSystem I P ⋙ HomologicalComplex.homologyFunctor
          (ModuleCat.{u} A) (ComplexShape.up ℤ) i :=
      Functor.isoWhiskerRight (derivedReductionSystemIso I T P hflat)
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ≪≫
      Functor.isoWhiskerLeft (reductionSystem I P)
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) i)
    exact isMittagLeffler_of_natIso
      (Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft (NoetherianAdicCompletion.idealPowerQuotientSystem I)
          (T.tensor.mapIso e))
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i ⋙ forget (ModuleCat.{u} A)))
      (isMittagLeffler_of_natIso (Functor.isoWhiskerRight d.symm (forget (ModuleCat.{u} A)))
        (reductionHomology_mittagLeffler I P (fun n => (hP.finiteFree n).1) i))
  exact fun i => ⟨hML i,
    Stacks.InverseSystem.AdicCompletionCohomology.adicCompletion_homology_iso_limit_derivedReduction
      A I K T (finite_homology_of_pseudoCoherent K ⟨P, hP, ⟨e⟩⟩) hML i⟩

end

end Stacks.PseudoCoherent.AdicCompletion

end
