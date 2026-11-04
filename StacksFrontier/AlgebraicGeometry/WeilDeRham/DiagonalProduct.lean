module

public import StacksFrontier.AlgebraicGeometry.WeilDeRham.GysinPushforwardFundamental
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullbackComp
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalGysinPoint
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.KunnethOfIsPullback
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.PushforwardCalculus.IsoTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.TensorAssociativity

/-!
# Proper pushforward of fundamental classes on `CH_*(-) ⊗ 𝐐`

The class in `CH_*(Y) ⊗ 𝐐` of the pushforward of a fundamental class, used by the computation of
trace maps in `Stacks.WeilDeRham.TraceAxiomAlgClosedProjectiveSpacePointClass`.

(The class of the diagonal of a product and the cohomological identity
`γ([Δ_{X × Y}]) = r^*γ([Δ_X]) ∪ s^*γ([Δ_Y])` of the proof of Lemma 0FIL are
`Stacks.WeilCohomology.SmoothProjectiveScheme.diagonalClass_prod` and
`IsCohomologicalChernCharacter.untwistClass_diagonalClass_prod` in
`Stacks.WeilCohomology.FirstChernClassData`.)

## Main results

* `Stacks.WeilDeRham.codimensionToRationalChow_chowCodimPushforward_chowCodimFundamental`: the
  class of `f_*[X]` in `CH_*(Y) ⊗ 𝐐` is the pushforward of `[X]`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Chow Stacks.WeilCohomology Stacks.WeilCohomology.SmoothProjectiveScheme

universe u w

namespace Stacks.WeilDeRham

/-! ### Proper pushforward on `CH_*(-) ⊗ 𝐐` is functorial -/

section Functorial

variable (C : ChowSituation.{u}) {A B D : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] (sD : D ⟶ C.S) [LocallyOfFiniteType sD]

end Functorial

/-! ### The class of a pushforward of a fundamental class -/

section Codimension

variable {k : Type u} [Field k]

/-- **The class of `f_*[X]` in `CH_*(Y) ⊗ 𝐐`.** For `f : X ⟶ Y` a morphism of smooth projective
schemes over `k`, `X` and `Y` equidimensional of dimensions `a` and `b = a + c`, the class in
`CH_*(Y) ⊗ 𝐐` of the codimension `c` part of `f_*[X]` is the pushforward of `[X]`. -/
theorem codimensionToRationalChow_chowCodimPushforward_chowCodimFundamental
    {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) {a b c : ℕ}
    (hX : RelativeDimension X.obj.hom a) (hY : RelativeDimension Y.obj.hom b) (hc : a + c = b) :
    codimensionToRationalChow k Y.obj.hom c
        (chowCodimPushforward k X.obj.hom Y.obj.hom ((toScheme k).map f) (w f) 0 c
          (chowCodimFundamental k X.obj.hom)) =
      rationalProperChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom
        (f := (toScheme k).map f) (w f)
        (rationalFundamentalClass (fieldChowSituation k) X.obj.hom) := by
  rw [codimensionToRationalChow_apply]
  refine (Finset.sum_congr rfl fun e he ↦ ?_).trans
    (sum_rationalIncludePart_rationalRestrictPart k Y.obj.hom _)
  obtain ⟨y, hy⟩ := (mem_nonemptyDimParts k Y.obj.hom).1 he
  obtain rfl := eq_of_mem_dimPart Y.obj.hom hY hy
  congr 1
  rw [rationalFundamentalClass_eq_of_relativeDimension k X.obj.hom hX,
    rationalProperChowPushforward_of_tmul, rationalChowMap_of_tmul]
  simp only [chowCodimPushforward, chowCodimPart]
  rw [chowCodimTotal_chowCodimFundamental X.obj.hom hX]
  subst hc
  have hac : ((a + c : ℕ) : ℤ) - ((c : ℕ) : ℤ) = (a : ℤ) := by push_cast; ring
  have key : ∀ n m : ℤ, n = m →
      chowGroupRestrict (fieldChowSituation k) Y.obj.hom (partBase Y.obj.hom (a + c))
          (dimPart Y.obj.hom (a + c)).ι rfl n
          (properChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom ((toScheme k).map f)
            (w f) n (properPushforwardDescends _ _ _ _ _ _)
            (fundamentalChowClass (fieldChowSituation k) X.obj.hom n)) ≍
        chowGroupRestrict (fieldChowSituation k) Y.obj.hom (partBase Y.obj.hom (a + c))
          (dimPart Y.obj.hom (a + c)).ι rfl m
          (properChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom ((toScheme k).map f)
            (w f) m (properPushforwardDescends _ _ _ _ _ _)
            (fundamentalChowClass (fieldChowSituation k) X.obj.hom m)) := by
    rintro n m rfl
    rfl
  exact of_tmul_eq_of_tmul_of_heq _ _ hac 1 (key _ _ hac)

end Codimension

/-! ### `δ` over a field -/

section Smooth

variable (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  [AlgebraicGeometry.IsNoetherian X]

end Smooth

end Stacks.WeilDeRham

end
