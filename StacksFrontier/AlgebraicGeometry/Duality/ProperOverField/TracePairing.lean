module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Duality
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessUnconditional
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# The trace pairing of a proper scheme over a field

Let `X` be a proper scheme over a field `k`, with structure morphism `f : X ⟶ Spec k`, and let
`ω_X^• = a(𝒪_{Spec k})` be as in [Stacks, Tag 0FVV]. Part (5) of that lemma identifies
`Ext^i_X(K, ω_X^•)` with `Hom_k(H^{-i}(X, K), k)` for `K` in `D_QCoh(𝒪_X)`
(`Stacks.Duality.dualityEquiv`). [Stacks, Tag 0FVW] makes this explicit:

* the identity of `ω_X^•` corresponds to a map `t : H⁰(X, ω_X^•) ⟶ k`, the trace;
* the identification is the pairing `(α, β) ↦ t(α(β))` of `Ext^i_X(K, ω_X^•)` with
  `H^{-i}(X, K)`, where `α` is regarded as a morphism `K[-i] ⟶ ω_X^•` and `β` as an element of
  `H⁰(X, K[-i])`;
* the pairing identifies `Ext^i_X(K, ω_X^•)` with the dual of `H^{-i}(X, K)`, but in general
  not vice versa: the other-side map `H^{-i}(X, K) ⟶ Ext^i_X(K, ω_X^•)^∨` need not be bijective;
* for `K` in `D^b_Coh(𝒪_X)` all these spaces are finite dimensional ([Stacks, Tag 0D0C],
  [Stacks, Tag 0D0B]) and the pairings are perfect.

## Main results

* `Stacks.Duality.dualityEquiv_id_eq_traceOverField` — the identity corresponds to the trace.
* `Stacks.Duality.dualityEquiv_mk₀_apply`, `Stacks.Duality.dualityEquiv_apply_eq_traceOverField`
  — the identification is `(α, β) ↦ t(α(β))`, in degree zero and in degree `i`.
* `Stacks.Duality.bijective_dualityLinearMap` — nondegeneracy on the side of `Ext`.
* `Stacks.Duality.bijective_dualityLinearMap_flip_iff` — the other side is nondegenerate exactly
  when `H^{-i}(X, K)` is finite dimensional, and
  `Stacks.Duality.exists_not_bijective_dualityLinearMap_flip` — on `X = Spec k` it fails for some
  `K` ("not vice versa").
* `Stacks.Duality.finiteDimensional_and_isPerfPair_of_coherent` — the coherent case.
* `Stacks.Duality.finiteDimensional_homology_derivedGlobalSectionsOver` — `H^n(X, K)` is finite
  dimensional for `K` in `D^+_Coh(𝒪_X)`, at any model of the derived categories.

## Implementation notes

The finiteness of hypercohomology is
`moduleFinite_homologyZero_derivedGlobalSections_of_proper` in
`Stacks.AlgebraicGeometry.ProperSupportCoherent` (which rests on [Stacks, Tag 0D0B]), stated at
the standard models; it is carried to arbitrary models by
`Stacks.Duality.derivedGlobalSectionsOverModelIso`, the comparison of the two total right derived
functors of global sections along `StacksDraft.DerivedModel.modelEquiv`. The finiteness of
`Ext^i_X(K, ω_X^•)` then follows from the duality itself.

## References

* [Stacks Project, Tag 0FVW](https://stacks.math.columbia.edu/tag/0FVW)
* [Stacks Project, Tag 0FVV](https://stacks.math.columbia.edu/tag/0FVV)
* [Stacks Project, Tag 0D0B](https://stacks.math.columbia.edu/tag/0D0B)
* [Stacks Project, Tag 0D0C](https://stacks.math.columbia.edu/tag/0D0C)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w₁ w₂ u

namespace Stacks.Duality

/-! ### Finite dimensionality of the hypercohomology of a coherent complex -/

section Finiteness

open StacksDraft.DerivedModel
open Stacks.AlgebraicGeometry.ProperSupportCoherent
  (moduleFinite_homologyZero_derivedGlobalSections_of_proper)

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
  [h₁ : HasDerivedCategory.{w₁} X.Modules] [h₂ : HasDerivedCategory.{w₂} (ModuleCat.{u} k)]

/-- **Derived global sections read at two models.** `RΓ(X, -)` at the standard models of `D(𝒪_X)`
and `D(k)` and `RΓ(X, -)` at arbitrary models agree up to the comparison equivalences: both are
total right derived functors of `k`-linear global sections. -/
def derivedGlobalSectionsOverModelIso :
    @derivedGlobalSectionsOver k _ X f (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _) ⋙
      (modelEquiv (HasDerivedCategory.standard (ModuleCat.{u} k)) h₂).functor ≅
    (modelEquiv (HasDerivedCategory.standard X.Modules) h₁).functor ⋙
      derivedGlobalSectionsOver f :=
  rightDerivedModelIso (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))
    (@derivedGlobalSectionsOverUnit k _ X f (HasDerivedCategory.standard _)
      (HasDerivedCategory.standard _))
    (derivedGlobalSectionsOverUnit f)
    (Localization.compUniqFunctor _ _ (HomotopyCategory.subcategoryAcyclic X.Modules).trW)
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Localization.compUniqFunctor _ _
        (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} k)).trW))

/-- **The degree-zero hypercohomology of an object of `D^+_Coh(𝒪_X)` on a proper scheme over a
field is finite dimensional**, at any model of the derived categories. This is
[Stacks, Tag 0D0B] through `Stacks.AlgebraicGeometry.ProperSupportCoherent.
moduleFinite_homologyZero_derivedGlobalSections_of_proper`, carried across the comparison of
models. -/
theorem finiteDimensional_homologyZero_derivedGlobalSectionsOver (K : DerivedCategory X.Modules)
    (hK : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent) K) :
    FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
      ((derivedGlobalSectionsOver f).obj K)) := by
  let G := modelEquiv (HasDerivedCategory.standard X.Modules) h₁
  let K' := G.inverse.obj K
  have eH : ∀ m : ℤ, (@DerivedCategory.homologyFunctor X.Modules _ _
      (HasDerivedCategory.standard _) m).obj K' ≅
      (DerivedCategory.homologyFunctor X.Modules m).obj K := fun m =>
    ((modelHomologyFunctorIso (HasDerivedCategory.standard X.Modules) h₁ m).app K').symm ≪≫
      (DerivedCategory.homologyFunctor X.Modules m).mapIso (G.counitIso.app K)
  have hK' : @DerivedCategoryB.derivedCategoryBPlus X.Modules _ _
      (HasDerivedCategory.standard _) (fun M : X.Modules => M.IsCoherent) K' := by
    obtain ⟨⟨n₀, hn₀⟩, hcoh⟩ := hK
    exact ⟨⟨n₀, fun n hn => (hn₀ n hn).of_iso (eH n)⟩,
      fun m => _root_.AlgebraicGeometry.isCoherent_of_modulesIso (eH m).symm (hcoh m)⟩
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
      ((derivedGlobalSectionsOver f).obj K) ≅
      (@DerivedCategory.homologyFunctor (ModuleCat.{u} k) _ _
        (HasDerivedCategory.standard _) 0).obj
        (@derivedGlobalSectionsOver k _ X f (HasDerivedCategory.standard _)
          (HasDerivedCategory.standard _) |>.obj K') :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
        ((derivedGlobalSectionsOver f).mapIso (G.counitIso.app K).symm ≪≫
          ((derivedGlobalSectionsOverModelIso f).app K').symm) ≪≫
      (modelHomologyFunctorIso (HasDerivedCategory.standard (ModuleCat.{u} k)) h₂ 0).app _
  exact (Module.Finite.equiv_iff e.toLinearEquiv).2
    (moduleFinite_homologyZero_derivedGlobalSections_of_proper (Over.mk f) K' hK')

/-- **The hypercohomology of an object of `D^+_Coh(𝒪_X)` on a proper scheme over a field is
finite dimensional in every degree**, at any model of the derived categories:
`H^n(X, K) = H^0(X, K⟦n⟧)` and `K⟦n⟧` again lies in `D^+_Coh(𝒪_X)`. -/
theorem finiteDimensional_homology_derivedGlobalSectionsOver (K : DerivedCategory X.Modules)
    (hK : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent) K) (n : ℤ) :
    FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj
      ((derivedGlobalSectionsOver f).obj K)) := by
  have hKn : DerivedCategoryB.derivedCategoryBPlus (fun M : X.Modules => M.IsCoherent)
      (K⟦n⟧) := by
    refine ⟨DerivedCategoryB.isBoundedBelow_shift n hK.1, fun i => ?_⟩
    have e : (DerivedCategory.homologyFunctor X.Modules i).obj (K⟦n⟧) ≅
        (DerivedCategory.homologyFunctor X.Modules (n + i)).obj K :=
      ((DerivedCategory.homologyFunctor X.Modules 0).shiftIso n i (n + i) rfl).app K
    exact _root_.AlgebraicGeometry.isCoherent_of_modulesIso e.symm (hK.2 (n + i))
  let e : (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).obj
      ((derivedGlobalSectionsOver f).obj (K⟦n⟧)) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj
        ((derivedGlobalSectionsOver f).obj K) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).mapIso
        (((derivedGlobalSectionsOver f).commShiftIso n).app K) ≪≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 0).shiftIso n 0 n (add_zero n)).app _
  exact (Module.Finite.equiv_iff e.toLinearEquiv).1
    (finiteDimensional_homologyZero_derivedGlobalSectionsOver f _ hKn)

end Finiteness

/-! ### The trace and the duality pairing -/

section Pairing

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The relative dualizing complex `ω_X^• = a(𝒪_{Spec k})` of `f : X ⟶ Spec k`. -/
local notation "ωX" =>
  relativeDualizingComplex f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))

/-- Degree-zero cohomology on `D(k)`. -/
local notation "H⁰" => DerivedCategory.homologyFunctor (ModuleCat k) 0

/-- `H⁰(X, -) = H⁰ ∘ RΓ(X, -)`, whose shift sequence is `H^n(X, -)`. -/
local notation "HX" => derivedGlobalSectionsOver f ⋙ DerivedCategory.homologyFunctor (ModuleCat k) 0

/-- **An element of `Ext^i(K, Z)` as a morphism `K⟦-i⟧ ⟶ Z`.** An element `α : K ⟶ Z⟦i⟧`
shifted by `-i`, followed by `Z⟦i⟧⟦-i⟧ ≅ Z`. -/
def extShiftHom {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K Z : DerivedCategory C} {i : ℤ} (α : DerivedCategory.Ext K Z i) : K⟦-i⟧ ⟶ Z :=
  α⟦-i⟧' ≫ (shiftFunctorCompIsoId (DerivedCategory C) i (-i) (add_neg_cancel i)).hom.app Z

/-- **The identity of `ω_X^•` corresponds to the trace.** Under the isomorphism of part (5) of
[Stacks, Tag 0FVV] in degree zero, `Hom(ω_X^•, ω_X^•) ≅ Hom_k(H⁰(X, ω_X^•), k)`, the identity
of `ω_X^•` is sent to the trace `t : H⁰(X, ω_X^•) ⟶ k`. -/
@[stacks 0FVW "the identity of ω_X^• corresponds via 0FVV (5) to the trace t : H^0(X, ω_X^•) → k"]
theorem dualityEquiv_id_eq_traceOverField :
    letI := Scheme.linearOver f
    dualityEquiv f ωX 0 (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 (ωX).obj)) = (traceOverField f).hom := by
  ext x
  rw [dualityEquiv_apply, dualityPairing_mk₀]
  simp

/-- **The degree-zero pairing.** For `K` in `D_QCoh(𝒪_X)`, the identification
`Hom(K, ω_X^•) ≅ H⁰(X, K)^∨` of part (5) of [Stacks, Tag 0FVV] is the pairing
`(α, β) ↦ t(α(β))`, where `α(β)` is the image of `β ∈ H⁰(X, K)` under the map
`H⁰(X, K) ⟶ H⁰(X, ω_X^•)` induced by `α`. -/
@[stacks 0FVW "the degree-zero pairing Hom_X(K, ω_X^•) × H^0(X, K) → k, (α, β) ↦ t(α(β))"]
theorem dualityEquiv_mk₀_apply (K : quasiCoherentDerivedCategory X) (α : K.obj ⟶ (ωX).obj)
    (β : (H⁰).obj ((derivedGlobalSectionsOver f).obj K.obj)) :
    letI := Scheme.linearOver f
    dualityEquiv f K 0 (ShiftedHom.mk₀ (0 : ℤ) rfl α) β =
      (traceOverField f).hom (((H⁰).map ((derivedGlobalSectionsOver f).map α)).hom β) := by
  rw [dualityEquiv_apply, dualityPairing_mk₀]
  rfl

/-- **The pairing in degree `i`.** For `K` in `D_QCoh(𝒪_X)` and `i ∈ ℤ`, the identification
`Ext^i_X(K, ω_X^•) ≅ H^{-i}(X, K)^∨` of part (5) of [Stacks, Tag 0FVV] is the pairing
`(α, β) ↦ t(α(β))`: here `α` is regarded as a morphism `K⟦-i⟧ ⟶ ω_X^•` (`extShiftHom`), `β` as an
element of `H⁰(X, K⟦-i⟧) ≅ H^{-i}(X, K)`, and `α(β) ∈ H⁰(X, ω_X^•)` is the image of `β` under
the map that `α` induces on `H⁰(X, -)`. -/
@[stacks 0FVW "the pairing Ext^i_X(K, ω_X^•) × H^{-i}(X, K) → k, (α, β) ↦ t(α(β)), with α a \
  morphism K[-i] → ω_X^• and β in H^0(X, K[-i])"]
theorem dualityEquiv_apply_eq_traceOverField (K : quasiCoherentDerivedCategory X) (i : ℤ)
    (α : DerivedCategory.Ext K.obj (ωX).obj i)
    (β : (DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
      ((derivedGlobalSectionsOver f).obj K.obj)) :
    letI := Scheme.linearOver f
    dualityEquiv f K i α β =
      (traceOverField f).hom (((H⁰).map ((derivedGlobalSectionsOver f).map (extShiftHom α))).hom
        ((((HX).shiftIso (-i) 0 (-i) (add_zero _)).inv.app K.obj).hom β)) := by
  let := Scheme.linearOver f
  rw [dualityEquiv_apply]
  have hcomp : ShiftedHom.comp (𝟙 (K.obj⟦-i⟧) : ShiftedHom (K.obj⟦-i⟧) K.obj (-i)) α
      (add_neg_cancel i) =
      ShiftedHom.mk₀ (0 : ℤ) rfl (extShiftHom α) := by
    simp [ShiftedHom.comp, ShiftedHom.mk₀, extShiftHom, shiftFunctorCompIsoId,
      shiftFunctorZero']
  have h := dualityPairing_shiftedHomComp f (L := K.obj⟦-i⟧)
    (𝟙 (K.obj⟦-i⟧) : ShiftedHom (K.obj⟦-i⟧) K.obj (-i)) α (add_neg_cancel i)
  rw [Functor.shiftMap_id, hcomp, dualityPairing_mk₀] at h
  change _ = ((HX).shiftIso (-i) 0 (-i) (add_zero _)).hom.app K.obj ≫ _ at h
  have h' : dualityPairing f K.obj i α =
      (((HX).shiftIso (-i) 0 (-i) (add_zero _)).app K.obj).inv ≫
        (H⁰).map ((derivedGlobalSectionsOver f).map (extShiftHom α)) ≫ traceOverField f :=
    (Iso.eq_inv_comp _).2 h.symm
  rw [h']
  rfl

/-- **The pairing is nondegenerate on one side.** For `K` in `D_QCoh(𝒪_X)` and every `i`, the
pairing `(α, β) ↦ t(α(β))` of `Ext^i_X(K, ω_X^•)` with `H^{-i}(X, K)` identifies
`Ext^i_X(K, ω_X^•)` with the `k`-linear dual of `H^{-i}(X, K)`. -/
@[stacks 0FVW "the pairing identifies Ext^i_X(K, ω_X^•) with the k-linear dual of H^{-i}(X, K)"]
theorem bijective_dualityLinearMap (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    letI := Scheme.linearOver f
    Function.Bijective (dualityLinearMap f K.obj i) :=
  let := Scheme.linearOver f
  (dualityEquiv f K i).bijective

/-- **When the pairing is nondegenerate on the other side.** For `K` in `D_QCoh(𝒪_X)` and `i ∈ ℤ`,
the other-side map `H^{-i}(X, K) ⟶ Ext^i_X(K, ω_X^•)^∨`, `β ↦ (α ↦ t(α(β)))`, is bijective if
and only if `H^{-i}(X, K)` is finite dimensional: through the isomorphism of part (5) of
[Stacks, Tag 0FVV] it is the evaluation map of `H^{-i}(X, K)` into its double dual. -/
theorem bijective_dualityLinearMap_flip_iff (K : quasiCoherentDerivedCategory X) (i : ℤ) :
    letI := Scheme.linearOver f
    Function.Bijective (dualityLinearMap f K.obj i).flip ↔
      FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat k) (-i)).obj
        ((derivedGlobalSectionsOver f).obj K.obj)) := by
  let := Scheme.linearOver f
  let e := dualityEquiv f K i
  have hflip : (dualityLinearMap f K.obj i).flip =
      e.dualMap.toLinearMap ∘ₗ Module.Dual.eval k _ := by
    ext β α
    rfl
  rw [hflip, LinearMap.coe_comp]
  refine (Function.Bijective.of_comp_iff' e.dualMap.bijective _).trans
    ⟨fun h => ?_, fun _ => Module.bijective_dual_eval _ _⟩
  have : Module.IsReflexive k _ := ⟨h⟩
  infer_instance

/-- **The pairing is in general not nondegenerate on the other side** (the clause "but in general
not vice versa" of [Stacks, Tag 0FVW]). For every field `k`, on the proper scheme `X = Spec k`
there is an object `K` of `D_QCoh(𝒪_X)` for which the other-side map
`H⁰(X, K) ⟶ Hom_X(K, ω_X^•)^∨`, `β ↦ (α ↦ t(α(β)))`, is not bijective: take for `K` the object
with `RΓ(X, K) = k^{(ℕ)}[0]` ([Stacks, Tag 06Z0]), whose `H⁰(X, K) = k^{(ℕ)}` is infinite
dimensional, so that the evaluation map into its double dual is not surjective. -/
@[stacks 0FVW "the 'not vice versa' clause: on X = Spec k some K in D_QCoh has \
  H^0(X, K) → Hom_X(K, ω_X^•)^∨ not bijective"]
theorem exists_not_bijective_dualityLinearMap_flip (k : Type u) [Field k] :
    ∃ K : quasiCoherentDerivedCategory (Spec (.of k)),
      letI := Scheme.linearOver (𝟙 (Spec (.of k)))
      ¬ Function.Bijective (dualityLinearMap (𝟙 (Spec (.of k))) K.obj 0).flip := by
  let Φ := derivedGlobalSectionsQuasicoherent (CommRingCat.of k)
  have := derivedGlobalSectionsQuasicoherent_isEquivalence (CommRingCat.of k)
  let M := (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k (ℕ →₀ k))
  refine ⟨Φ.objPreimage M, ?_⟩
  rw [bijective_dualityLinearMap_flip_iff]
  intro hfin
  let e : (DerivedCategory.homologyFunctor (ModuleCat k) 0).obj
      ((derivedGlobalSectionsOver (𝟙 (Spec (.of k)))).obj (Φ.objPreimage M).obj) ≅
      ModuleCat.of k (ℕ →₀ k) :=
    (DerivedCategory.homologyFunctor (ModuleCat k) 0).mapIso (Φ.objObjPreimageIso M) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} k) 0).app _
  have : Module.Finite k (ℕ →₀ k) := (Module.Finite.equiv_iff e.toLinearEquiv).1 hfin
  have := Module.Finite.finite_basis (Finsupp.basisSingleOne (R := k) (ι := ℕ))
  exact not_finite ℕ

/-- An object of `D_Coh(𝒪_X)` as an object of `D_QCoh(𝒪_X)`: coherent modules are
quasi-coherent. -/
abbrev quasiCoherentOfCoherent (K : DerivedCategory X.Modules)
    (hK : DerivedCategoryB.derivedCategoryB (fun M : X.Modules => M.IsCoherent) K) :
    quasiCoherentDerivedCategory X :=
  ⟨K, fun n => by
    have := hK n
    exact (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1⟩

/-- **The coherent case.** For `K` in `D^b_Coh(𝒪_X)`, the `k`-vector spaces
`Hom_X(K, ω_X^•)`, `Ext^i_X(K, ω_X^•)` and `H^n(X, K)` are finite dimensional, and for every `i`
the pairing `Ext^i_X(K, ω_X^•) × H^{-i}(X, K) ⟶ k`, `(α, β) ↦ t(α(β))`, is perfect. -/
@[stacks 0FVW "K in D^b_Coh: Hom_X(K, ω_X^•), Ext^i_X(K, ω_X^•), H^i(X, K) are finite dimensional \
  and the pairings are perfect"]
theorem finiteDimensional_and_isPerfPair_of_coherent (K : DerivedCategory X.Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded (fun M : X.Modules => M.IsCoherent) K) :
    letI := Scheme.linearOver f
    FiniteDimensional k (K ⟶ (ωX).obj) ∧
      (∀ i : ℤ, FiniteDimensional k (DerivedCategory.Ext K (ωX).obj i)) ∧
      (∀ n : ℤ, FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat k) n).obj
        ((derivedGlobalSectionsOver f).obj K))) ∧
      ∀ i : ℤ, (dualityLinearMap f K i).IsPerfPair := by
  let := Scheme.linearOver f
  have hH : ∀ n : ℤ, FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat k) n).obj
      ((derivedGlobalSectionsOver f).obj K)) := fun n =>
    finiteDimensional_homology_derivedGlobalSectionsOver f K ⟨hK.1.1, hK.2⟩ n
  have hExt : ∀ i : ℤ, FiniteDimensional k (DerivedCategory.Ext K (ωX).obj i) := fun i => by
    have := hH (-i)
    exact (Module.Finite.equiv_iff (dualityEquiv f (quasiCoherentOfCoherent K hK.2) i)).2
      inferInstance
  refine ⟨(Module.Finite.equiv_iff (Linear.homCongr k (Iso.refl K)
      ((shiftFunctorZero (DerivedCategory X.Modules) ℤ).app (ωX).obj).symm)).2 (hExt 0),
    hExt, hH, fun i => ?_⟩
  have := hH (-i)
  exact LinearMap.IsPerfPair.of_bijective _
    (bijective_dualityLinearMap f (quasiCoherentOfCoherent K hK.2) i)

end Pairing

end Stacks.Duality
