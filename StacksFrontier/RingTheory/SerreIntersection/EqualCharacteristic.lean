module

public import StacksFrontier.RingTheory.SerreIntersection.PowerSeriesSerre
public import StacksFrontier.RingTheory.SerreIntersection.FlatLocalTransfer
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Serre's intersection theorems for a regular local ring containing a field

Let `A` be a regular local ring containing a field. Its completion is isomorphic to a power series
ring over its residue field, and the map from `A` to this power series ring is flat and local.
This reduces Serre's dimension inequality over `A` to the case of a power series ring over a
field.

## Main definitions

* `Stacks.SerreIntersection.Completion`: the completion of `A` at its maximal ideal.
* `Stacks.SerreIntersection.Model`: the power series ring over the residue field of the
  completion, in as many variables as its embedding dimension.
* `Stacks.SerreIntersection.modelMap`: the map `A → Model A` given by the completion followed by
  an isomorphism with `Model A`.

## Main results

* `Stacks.SerreIntersection.nonempty_completion_ringEquiv`: the completion of a regular local ring
  containing a field is isomorphic to a power series ring over its residue field.
* `Stacks.SerreIntersection.supportDim_add_supportDim_le_of_field`: for nonzero finite modules
  `M`, `N` over `A` with `M ⊗_A N` supported in the closed point,
  `dim Supp M + dim Supp N ≤ dim A`.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace Stacks.SerreIntersection

section Completion

variable (A : Type u) [CommRing A] [IsRegularLocalRing A]

/-- The completion of `A`. -/
abbrev Completion : Type u := AdicCompletion (maximalIdeal A) A

/-- The completion of a regular local ring is a regular local ring. -/
instance : IsRegularLocalRing (Completion A) :=
  isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp ‹_›

/-- The embedding dimension of the completion. -/
abbrev completionDim : ℕ :=
  Module.finrank (ResidueField (Completion A)) (CotangentSpace (Completion A))

/-- The power series ring over the residue field of the completion, in as many variables as the
dimension. -/
abbrev PowerSeriesModel : Type u :=
  MvPowerSeries (Fin (completionDim A)) (ResidueField (Completion A))

/-- **Cohen structure theorem (Stacks 0C0S)**: the completion of a regular local ring containing
a field is a power series ring over its residue field. -/
theorem nonempty_completion_ringEquiv (F : Type v) [Field F] [Algebra F A] :
    Nonempty (Completion A ≃+* PowerSeriesModel A) := by
  let : Algebra F (Completion A) :=
    ((algebraMap A (Completion A)).comp (algebraMap F A)).toAlgebra
  exact (IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries.{u, v, 0} (Completion A)
    (completionDim A) rfl).1 F

/-- The power series model of the completion, as a type synonym carrying no module structure
over `A` other than the one given by the completion map (`MvPowerSeries` has a coefficientwise
one, which is a different structure). -/
def Model : Type u := PowerSeriesModel A

/-- The ring structure on `Model A`, that of the power series ring. -/
instance : CommRing (Model A) := inferInstanceAs (CommRing (PowerSeriesModel A))
/-- `Model A` is a local ring. -/
instance : IsLocalRing (Model A) := inferInstanceAs (IsLocalRing (PowerSeriesModel A))
/-- `Model A` is a Noetherian ring. -/
instance : IsNoetherianRing (Model A) := inferInstanceAs (IsNoetherianRing (PowerSeriesModel A))

/-- The flat local map `A → K[[x]]`: the completion followed by an isomorphism with the power
series model. -/
def modelMap (e : Completion A ≃+* Model A) : A →+* Model A :=
  e.toRingHom.comp (algebraMap A (Completion A))

/-- The map `modelMap A e` makes `Model A` a flat `A`-algebra. -/
theorem flat_modelMap (e : Completion A ≃+* Model A) :
    letI := (modelMap A e).toAlgebra; Module.Flat A (Model A) := by
  let := (modelMap A e).toAlgebra
  let e' : Completion A ≃ₗ[A] Model A :=
    { e with
      map_smul' := fun a x => by
        change e (algebraMap A (Completion A) a * x) = e (algebraMap A (Completion A) a) * e x
        rw [map_mul] }
  exact Module.Flat.of_linearEquiv e'.symm

/-- The maximal ideal of `A` generates the maximal ideal of `Model A` under `modelMap A e`. -/
theorem map_modelMap_maximalIdeal (e : Completion A ≃+* Model A) :
    Ideal.map (modelMap A e) (maximalIdeal A) = maximalIdeal (Model A) := by
  rw [modelMap, ← Ideal.map_map, ← AdicCompletion.maximalIdeal_eq_map]
  exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e)

/-- `Model A` has the same Krull dimension as `A`. -/
theorem ringKrullDim_model (e : Completion A ≃+* Model A) :
    ringKrullDim (Model A) = ringKrullDim A := by
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact (ringKrullDim_adicCompletion_maximalIdeal (A := A)).symm

/-- If `A` contains a field, then the completion of `A` is isomorphic to `Model A`. -/
theorem nonempty_completion_ringEquiv_model (F : Type v) [Field F] [Algebra F A] :
    Nonempty (Completion A ≃+* Model A) := by
  obtain ⟨e⟩ := nonempty_completion_ringEquiv A F
  exact ⟨e⟩

end Completion

section Field

variable {A : Type u} [CommRing A] [IsRegularLocalRing A]

/-- **Serre's dimension inequality for a regular local ring containing a field.** Let `A` be a
regular local ring containing a field and let `M`, `N` be nonzero finite `A`-modules with
`M ⊗_A N` supported in the closed point. Then `dim Supp M + dim Supp N ≤ dim A`. -/
theorem supportDim_add_supportDim_le_of_field (F : Type v) [Field F] [Algebra F A]
    (M N : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N]
    (hMN : Module.support A (M ⊗[A] N) ⊆ {closedPoint A}) :
    Module.supportDim A M + Module.supportDim A N ≤ ringKrullDim A := by
  obtain ⟨e⟩ := nonempty_completion_ringEquiv_model A F
  let : Algebra A (Model A) := (modelMap A e).toAlgebra
  have : Module.Flat A (Model A) := flat_modelMap A e
  have hm : Ideal.map (algebraMap A (Model A)) (maximalIdeal A) = maximalIdeal (Model A) :=
    map_modelMap_maximalIdeal A e
  have := nontrivial_baseChange hm M
  have := nontrivial_baseChange hm N
  have hsupp := support_subset_closedPoint_tensor hm M N hMN
  let modM (X : Type u) [AddCommGroup X] [Module A X] :
      Module (PowerSeriesModel A) (Model A ⊗[A] X) :=
    inferInstanceAs (Module (Model A) (Model A ⊗[A] X))
  have finM (X : Type u) [AddCommGroup X] [Module A X] [Module.Finite A X] :
      Module.Finite (PowerSeriesModel A) (Model A ⊗[A] X) :=
    inferInstanceAs (Module.Finite (Model A) (Model A ⊗[A] X))
  have key := (@PowerSeriesDiagonal.serre_mvPowerSeries _ _ _ (Model A ⊗[A] M) (Model A ⊗[A] N)
    _ (modM M) (finM M) _ _ (modM N) (finM N) _ hsupp).1
  have hM : Module.supportDim (PowerSeriesModel A) (Model A ⊗[A] M) = Module.supportDim A M :=
    supportDim_baseChange hm M
  have hN : Module.supportDim (PowerSeriesModel A) (Model A ⊗[A] N) = Module.supportDim A N :=
    supportDim_baseChange hm N
  have hR : ringKrullDim (PowerSeriesModel A) = ringKrullDim A := ringKrullDim_model A e
  rw [hM, hN, hR] at key
  exact key

end Field

end Stacks.SerreIntersection
