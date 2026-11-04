module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriplePreparation
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TwoIdealAdicQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AnnihilatedCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.CompletionProjectionQuotient
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.RestrictionToClosedSubscheme

/-!
# The `𝒦 ᵉ`-reduction of a completion is the completion of the `𝒦 ᵉ`-reduction

Let `X` be a locally Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves, let `e`
be a natural number and let `H` be a coherent `𝒪_X`-module. Dividing the `ℐ`-adic completion of
`H` by `𝒦 ᵉ` termwise gives the same inverse system as completing the quotient `H / 𝒦 ᵉ H`:

`(H / ℐ ⁿ H) / 𝒦 ᵉ (…) ≅ (H / 𝒦 ᵉ H) / ℐ ⁿ (…)`,

both being `H / (ℐ ⁿ + 𝒦 ᵉ) H`. This file assembles those identifications into an isomorphism of
inverse systems and records its compatibility with the projections out of `H`. It is the step at
which the proof of [Stacks, Tag 088A] reads the reduction of `α : (F_n) ⟶ H ^∧` modulo `𝒦 ᵉ` as a
map into the completion of a single coherent module, so that hypothesis (1) applies to it.

## Main definitions

* `Stacks.Coherent.reductionCompletionIso` — **the isomorphism of inverse systems**
  `(H / 𝒦 ᵉ H) ^∧ ≅ H ^∧ ⋙ (𝒦 ᵉ-reduction)`.

## Main results

* `Stacks.Coherent.reductionCompletionHom_projection` — the component at `n` carries the
  projection of `H` onto `(H / 𝒦 ᵉ H) / ℐ ⁿ⁺¹ (…)` to its projection onto
  `(H / ℐ ⁿ⁺¹ H) / 𝒦 ᵉ (…)`; the projections being epimorphisms, this determines it.

## Implementation notes

The component at `n` is `Stacks.Algebraization.idealPowerQuotientCommMap`, conjugated by the two
instances of `Stacks.Algebraization.completionFunctor_obj` which name the terms of the two
completions. Everything about it is read off
`Stacks.Algebraization.idealPowerQuotientCommMap_π`: the comparison carries one composite
projection out of `H` to the other. Both composite projections are epimorphisms, so the
naturality squares in `n` are checked by cancelling them, and
`CategoryTheory.NatTrans.ofOpSequence` assembles the components into a morphism of systems from
the successor-step squares alone.

Associativity is rearranged by explicit `Category.assoc` and `congrArg` chains rather than by
`rw`: the quotient projections are typed at `SheafOfModules X.ringCatSheaf` while the terms of a
completion are typed at `X.Modules`, and a rewrite motive mixing the two is not type correct at
the transparency `rw` builds it at.

## References

* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization

variable {X : Scheme.{u}} [IsLocallyNoetherian X] (I K : X.IdealSheafData) (e : ℕ)
  (H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)

/-- The `𝒦 ᵉ`-reduction of a coherent module, as a coherent module. -/
public def reductionCoherentObj :
    AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  haveI : H.obj.IsCoherent := H.property
  haveI : H.obj.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent H.obj
  ⟨idealPowerQuotient K e H.obj, isCoherent_idealPowerQuotient K e H.obj⟩

/-- Its underlying module is the quotient. -/
public theorem reductionCoherentObj_obj :
    (reductionCoherentObj K e H).obj = idealPowerQuotient K e H.obj :=
  rfl

/-- The comparison of the `n`-th term of the completion of `H / 𝒦 ᵉ H` with the `𝒦 ᵉ`-reduction
of the `n`-th term of the completion of `H`, as an isomorphism. -/
public def reductionCompletionComponentIso (n : ℕ) :
    ((completionFunctor X I).obj (reductionCoherentObj K e H)).obj.obj (op n) ≅
      (((completionFunctor X I).obj H).obj ⋙ idealPowerQuotientFunctor K e).obj (op n) :=
  haveI : H.obj.IsCoherent := H.property
  haveI : H.obj.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent H.obj
  eqToIso (completionFunctor_obj X I (reductionCoherentObj K e H) n) ≪≫
    idealPowerQuotientCommIso I K (n + 1) e H.obj ≪≫
      (idealPowerQuotientFunctor K e).mapIso
        (eqToIso (completionFunctor_obj X I H n).symm)

/-- The component at `n` of the comparison of the completion of `H / 𝒦 ᵉ H` with the
`𝒦 ᵉ`-reduction of the completion of `H`. -/
public def reductionCompletionHom (n : ℕ) :
    ((completionFunctor X I).obj (reductionCoherentObj K e H)).obj.obj (op n) ⟶
      (((completionFunctor X I).obj H).obj ⋙ idealPowerQuotientFunctor K e).obj (op n) :=
  (reductionCompletionComponentIso I K e H n).hom

/-- The composite projection out of `H` onto the `n`-th term of the completion of `H / 𝒦 ᵉ H`. -/
public def reductionProjection (n : ℕ) :
    H.obj ⟶ ((completionFunctor X I).obj (reductionCoherentObj K e H)).obj.obj (op n) :=
  cokernel.π (C := X.Modules) (idealPowerMultiple K e H.obj).ι ≫
    completionProjection X I (reductionCoherentObj K e H) n

/-- The composite projection out of `H` onto the `𝒦 ᵉ`-reduction of the `n`-th term of the
completion of `H`. -/
public def completionReductionProjection (n : ℕ) :
    H.obj ⟶ (((completionFunctor X I).obj H).obj ⋙ idealPowerQuotientFunctor K e).obj (op n) :=
  completionProjection X I H n ≫ cokernel.π (C := X.Modules)
    (idealPowerMultiple K e (((completionFunctor X I).obj H).obj.obj (op n))).ι

/-- Reassociating a triple composite and replacing its last two factors by an equal morphism. -/
private theorem comp_comp_eq_comp {C : Type*} [Category C] {A B D E : C} (a : A ⟶ B) (b : B ⟶ D)
    (c : D ⟶ E) {d : B ⟶ E} (h : b ≫ c = d) : (a ≫ b) ≫ c = a ≫ d :=
  (Category.assoc _ _ _).trans (congrArg (a ≫ ·) h)

/-- The first composite projection is an epimorphism. -/
public theorem epi_reductionProjection (n : ℕ) :
    Epi (C := X.Modules) (reductionProjection I K e H n) := by
  have h1 : Epi (C := X.Modules)
    (cokernel.π (C := X.Modules) (idealPowerMultiple K e H.obj).ι) := coequalizer.π_epi
  have h2 := Stacks.Algebraization.epi_completionProjection X I (reductionCoherentObj K e H) n
  exact epi_comp' h1 h2

/-- **The comparison carries one composite projection to the other.** -/
public theorem reductionCompletionHom_projection (n : ℕ) :
    reductionProjection I K e H n ≫ reductionCompletionHom I K e H n =
      completionReductionProjection I K e H n := by
  have hHcoh : H.obj.IsCoherent := H.property
  have hHq : H.obj.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent H.obj
  have hA : reductionProjection I K e H n ≫
      eqToHom (completionFunctor_obj X I (reductionCoherentObj K e H) n) =
      doubleIdealPowerQuotientProjection I K (n + 1) e H.obj :=
    comp_comp_eq_comp _ _ _ (completionProjection_comp_eqToHom_cokernelπ I
      (reductionCoherentObj K e H) n)
  have hB : doubleIdealPowerQuotientProjection K I e (n + 1) H.obj ≫
      (idealPowerQuotientFunctor K e).map
        (eqToHom (completionFunctor_obj X I H n).symm) =
      completionReductionProjection I K e H n :=
    (comp_comp_eq_comp _ _ _ (idealPowerQuotientMap_π K K e e le_rfl
      (eqToHom (completionFunctor_obj X I H n).symm))).trans (Category.assoc _ _ _).symm
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (idealPowerQuotientCommMap I K (n + 1) e H.obj ≫
          (idealPowerQuotientFunctor K e).map
            (eqToHom (completionFunctor_obj X I H n).symm))) hA).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (idealPowerQuotientFunctor K e).map
              (eqToHom (completionFunctor_obj X I H n).symm))
            (idealPowerQuotientCommMap_π I K (n + 1) e H.obj)).trans hB)))

/-- The components of the comparison are isomorphisms. -/
public instance isIso_reductionCompletionHom (n : ℕ) :
    IsIso (C := X.Modules) (reductionCompletionHom I K e H n) :=
  inferInstanceAs (IsIso (C := X.Modules) (reductionCompletionComponentIso I K e H n).hom)

/-- The comparison components are compatible with the transition maps. -/
public theorem reductionCompletionHom_naturality (n : ℕ) :
    ((completionFunctor X I).obj (reductionCoherentObj K e H)).obj.map
        (homOfLE (n.le_add_right 1)).op ≫ reductionCompletionHom I K e H n =
      reductionCompletionHom I K e H (n + 1) ≫
        (((completionFunctor X I).obj H).obj ⋙
          idealPowerQuotientFunctor K e).map (homOfLE (n.le_add_right 1)).op := by
  have hepi := epi_reductionProjection I K e H (n + 1)
  refine (@cancel_epi _ _ _ _ _ (reductionProjection I K e H (n + 1)) hepi _ _).mp ?_
  have hL : reductionProjection I K e H (n + 1) ≫
      (((completionFunctor X I).obj (reductionCoherentObj K e H)).obj.map
          (homOfLE (n.le_add_right 1)).op ≫ reductionCompletionHom I K e H n) =
      completionReductionProjection I K e H n :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ reductionCompletionHom I K e H n)
          (comp_comp_eq_comp _ _ _
            (completionProjection_transition X I (reductionCoherentObj K e H) n))).trans
        (reductionCompletionHom_projection I K e H n))
  have hR : reductionProjection I K e H (n + 1) ≫
      (reductionCompletionHom I K e H (n + 1) ≫
        (((completionFunctor X I).obj H).obj ⋙
          idealPowerQuotientFunctor K e).map (homOfLE (n.le_add_right 1)).op) =
      completionReductionProjection I K e H n := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ (((completionFunctor X I).obj H).obj ⋙
      idealPowerQuotientFunctor K e).map (homOfLE (n.le_add_right 1)).op)
      (reductionCompletionHom_projection I K e H (n + 1))).trans ?_
    refine (comp_comp_eq_comp _ _ _ (idealPowerQuotientMap_π K K e e le_rfl
      (((completionFunctor X I).obj H).obj.map (homOfLE (n.le_add_right 1)).op))).trans ?_
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ cokernel.π (C := X.Modules)
          (idealPowerMultiple K e (((completionFunctor X I).obj H).obj.obj (op n))).ι)
        (completionProjection_transition X I H n))
  exact hL.trans hR.symm

/-- **The completion of `H / 𝒦 ᵉ H` is the `𝒦 ᵉ`-reduction of the completion of `H`.** -/
public def reductionCompletionIso :
    ((completionFunctor X I).obj (reductionCoherentObj K e H)).obj ≅
      ((completionFunctor X I).obj H).obj ⋙ idealPowerQuotientFunctor K e :=
  haveI : ∀ n : ℕᵒᵖ, IsIso (C := X.Modules)
      ((NatTrans.ofOpSequence (reductionCompletionHom I K e H)
        (reductionCompletionHom_naturality I K e H)).app n) := fun n =>
    isIso_reductionCompletionHom I K e H n.unop
  @asIso _ _ _ _ (NatTrans.ofOpSequence (reductionCompletionHom I K e H)
    (reductionCompletionHom_naturality I K e H)) (NatIso.isIso_of_isIso_app _)

/-- Its components are the comparison components. -/
@[simp]
public theorem reductionCompletionIso_hom_app (n : ℕ) :
    (reductionCompletionIso I K e H).hom.app (op n) = reductionCompletionHom I K e H n :=
  rfl

end Stacks.Coherent

end
