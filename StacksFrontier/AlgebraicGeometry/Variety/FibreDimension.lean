module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.FieldTheory.FinTrdeg
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction
public import StacksFrontier.AlgebraicGeometry.LimitFibreDimensionBound.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.HigherCodimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.Data.ENat.WithBotNatCast

/-!
# The dimension of the fibres of a morphism of varieties

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over a field `k` with `X`
irreducible, let `Z ⊆ Y` be the reduced induced structure on the closure of the image of `f`,
and set `d = dim X - dim Z`. Then every fibre of `f` has local dimension at least `d`, the locus
where that dimension is exactly `d` is dense open, and over a point of `Z` whose local ring has
dimension `e ≥ 1` the fibre dimension is at most `d + e - 1` — in particular exactly `d` when
`e = 1`. Without any irreducibility hypothesis, the fibre of `f` through `x` has local dimension
at least `dim_x(X) - dim_{f x}(Y)`.

## Main results

All five are parts of **Stacks Tag 0B2L**.

* `AlgebraicGeometry.topologicalKrullDim_le_fiber_add_imageClosure` is part (2a), the lower
  bound `dim_x(X_{f(x)}) ≥ d`.
* `AlgebraicGeometry.isOpen_and_dense_setOf_topologicalKrullDimAt_fiber_eq` is part (2b): the
  locus where the bound is attained is dense open.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_add_one_le_of_one_le_ringKrullDim_imageClosure`
  is part (2c), the upper bound over a point of higher codimension in `Z`.
* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_ringKrullDim_imageClosure_eq_one` is
  part (2d), the equality over a point of codimension one in `Z`.
* `AlgebraicGeometry.topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target` is
  part (3), the local form with no irreducibility hypothesis.

Two further results:

* `AlgebraicGeometry.isGenericPoint_asFiber_of_isGenericPoint`: the generic point of an
  irreducible source is a generic point of the fibre through it.
* `AlgebraicGeometry.topologicalKrullDim_fiber_genericPoint_eq_imageClosure_sub`: the generic
  fibre has dimension exactly `d`.

## Implementation notes

Dimensions take values in `WithBot ℕ∞`, which has no subtraction, so every bound is stated in
additive form: `dim X ≤ dim_x(X_{f(x)}) + dim Z` for (2a), `dim_x(X_{f(x)}) + 1 ≤ d + e` for
(2c), and `dim_x(X) ≤ dim_x(X_{f(x)}) + dim_{f x}(Y)` for (3). The number `d` of parts (2b),
(2c) and (2d) is a natural number, pinned down by the hypothesis that it is the difference of
the two dimensions computed in `ℕ`; both dimensions are finite, so this says `d = dim X - dim Z`.
The reduced induced structure on the closure of the image is Mathlib's
`Scheme.IdealSheafData.vanishingIdeal` subscheme, and the point of `Z` above `f x` is supplied as
an argument together with the equation identifying it.

The proof of (2a) first computes the local dimension of the fibre through the generic point `η`
of `X`: the fibre through `η` is irreducible with generic point `f.asFiber η`, so its dimension
is the transcendence degree of its residue field there over the residue field of `f η`, and that
residue field is the one of `X` at `η` by
`AlgebraicGeometry.Scheme.Hom.trdeg_residueField_fiber`. The tower formula for transcendence
degrees over `κ(f η)` then gives `dim X - dim Z` on the nose. Since the locus where the local
fibre dimension is at most a given natural number is open (Tag 02FZ) and `η` is in the closure
of every point, the value at `η` is a lower bound at every point; the same two facts give (2b),
the locus in question being the open locus where the dimension is at most `d`.

Parts (2c) and (2d) are Tags 0B2K and 0B2I applied to a morphism whose *target* is `Z`, since
those tags speak about the local rings of the target. A non-reduced `X` admits no morphism to the
reduced subscheme `Z`, so the morphism used is the one out of the reduction `X_red`, which exists
by Tag 0356; it has the same local fibre dimensions as `f`, because `X_red ⟶ X` is a
homeomorphism on points and `Z ⟶ Y` is injective. Part (3) applies (2a) to each irreducible
component of `X` through `x` with its reduced induced structure: the fibre of such a component
is a closed subspace of the fibre of `f`, and the reduced closure of the image of the component
lies in an irreducible component of `Y` through `f x`.

## References

* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2I](https://stacks.math.columbia.edu/tag/0B2I)
* [Stacks Project, Tag 0B2K](https://stacks.math.columbia.edu/tag/0B2K)
* [Stacks Project, Tag 0356](https://stacks.math.columbia.edu/tag/0356)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The generic point of a generic fibre.** The generic point of an irreducible source is the
generic point of the fibre through it: every point of that fibre is a specialization of it, and
the fibre carries the subspace topology. -/
public theorem isGenericPoint_asFiber_of_isGenericPoint {X Y : Scheme.{u}}
    (f : X ⟶ Y) (η : X)
    (hη : IsGenericPoint η (Set.univ : Set X)) :
    IsGenericPoint (f.asFiber η) (Set.univ : Set (f.fiber (f η))) := by
  refine isGenericPoint_iff_specializes.mpr fun y => ?_
  have hηspec : ∀ x : X, η ⤳ x := fun x =>
    (isGenericPoint_iff_specializes.mp hη x).2 (Set.mem_univ x)
  have hsub : f.fiberHomeo (f η) (f.asFiber η) ⤳ f.fiberHomeo (f η) y := by
    apply Topology.IsInducing.subtypeVal.specializes_iff.mp
    simpa [Scheme.Hom.fiberι_asFiber] using hηspec (f.fiberHomeo (f η) y).1
  exact iff_of_true ((f.fiberHomeo (f η)).isInducing.specializes_iff.mp hsub) (Set.mem_univ y)

/-- A morphism of schemes is locally of finite type if its composite with a morphism to a base
is, with the composite equal to a given structure morphism. -/
private theorem locallyOfFiniteType_of_comp_eq_left {X Y S : Scheme.{u}} (pX : X ⟶ S)
    (pY : Y ⟶ S) [LocallyOfFiniteType pX] (f : X ⟶ Y) (hf : f ≫ pY = pX) :
    LocallyOfFiniteType f :=
  have : LocallyOfFiniteType (f ≫ pY) := hf.symm ▸ inferInstance
  locallyOfFiniteType_of_comp f pY

/-- A space with a generic point of the whole space is irreducible. -/
private theorem irreducibleSpace_of_isGenericPoint {T : Type*} [TopologicalSpace T] {t : T}
    (h : IsGenericPoint t (Set.univ : Set T)) : IrreducibleSpace T :=
  irreducibleSpace_def T |>.mpr h.isIrreducible

/-- The closure of the range of a continuous map out of a space with generic point `η` is the
closure of `{f η}`. -/
private theorem closure_range_eq_closure_singleton_of_isGenericPoint {T U : Type*}
    [TopologicalSpace T] [TopologicalSpace U] (f : T → U) (hf : Continuous f) {η : T}
    (hη : IsGenericPoint η (Set.univ : Set T)) :
    closure (Set.range f) = closure {f η} := by
  rw [← Set.image_univ, ← (hη.image hf).def]

private theorem topologicalKrullDimAt_fiber_genericPoint_eq_imageClosure_sub
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IrreducibleSpace X]
    (η : X) (hη : IsGenericPoint η Set.univ) :
    topologicalKrullDimAt (f.fiber (f η)) (f.asFiber η) =
      ((((topologicalKrullDim X).unbotD 0).toNat -
        ((topologicalKrullDim
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure (Set.range f.base))).subscheme).unbotD 0).toNat : ℕ) :
        WithBot ℕ∞) := by
  let ξ : Y := f η
  let C : Closeds Y := Closeds.closure (Set.range f.base)
  let I : Y.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal C
  let Z : Scheme.{u} := I.subscheme
  have hCeq : (C : Set Y) = closure ({ξ} : Set Y) :=
    closure_range_eq_closure_singleton_of_isGenericPoint f.base f.continuous hη
  have hξC : ξ ∈ (C : Set Y) := by
    rw [hCeq]
    exact subset_closure (Set.mem_singleton ξ)
  have hCirr : IsIrreducible (C : Set Y) := by
    rw [hCeq]
    exact isIrreducible_singleton.closure
  have hIsupp : (I.support : Set Y) = (C : Set Y) := by
    simp [I, C]
  let z : Z := ⟨ξ, by
    show ξ ∈ (I.support : Set Y)
    rw [hIsupp]
    exact hξC⟩
  have hz : IsGenericPoint z (Set.univ : Set Z) := by
    apply isGenericPoint_iff_specializes.mpr
    intro w
    have hwC : w.1 ∈ (C : Set Y) := hIsupp ▸ w.2
    exact iff_of_true
      (Topology.IsInducing.subtypeVal.specializes_iff.mp
        (show ξ ⤳ w.1 from specializes_iff_mem_closure.mpr (hCeq ▸ hwC)))
      (Set.mem_univ w)
  let eZ : Z ≃ₜ (C : Set Y) :=
    I.subschemeIso.hom.homeomorph.trans <|
      I.gluedHomeo.trans (Homeomorph.setCongr hIsupp)
  let : IrreducibleSpace Z :=
    eZ.irreducibleSpace_iff.mpr (Subtype.irreducibleSpace hCirr)
  have := locallyOfFiniteType_of_comp_eq_left pX pY f hf
  let : Algebra k (X.residueField η) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η).hom.toAlgebra
  have hdimX := topologicalKrullDim_eq_trdeg_residueField k X pX η hη
  let pZ : Z ⟶ Spec (.of k) := I.subschemeι ≫ pY
  let : LocallyOfFiniteType pZ := inferInstance
  have hdimZ := topologicalKrullDim_eq_trdeg_residueField k Z pZ z hz
  have htrdegZ := trdeg_residueField_of_surjectiveOnStalks k pY I.subschemeι z
  rw [← htrdegZ] at hdimZ
  have hηtrdeg : Algebra.trdeg k (X.residueField η) < Cardinal.aleph0 := by
    let : FinTrdeg k (X.residueField η) := residueField_finTrdeg k pX η
    exact trdeg_lt_aleph0 k _
  let : Algebra k (Y.residueField ξ) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation ξ).hom.toAlgebra
  have hξtrdeg : Algebra.trdeg k (Y.residueField ξ) < Cardinal.aleph0 := by
    let : FinTrdeg k (Y.residueField ξ) := residueField_finTrdeg k pY ξ
    exact trdeg_lt_aleph0 k _
  let : Algebra (Y.residueField ξ) (X.residueField η) :=
    (f.residueFieldMap η).hom.toAlgebra
  let : IsScalarTower k (Y.residueField ξ) (X.residueField η) := by
    apply IsScalarTower.of_algebraMap_eq'
    show ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η).hom =
      (f.residueFieldMap η).hom.comp
        ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation ξ).hom
    have hcat : (Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η =
        ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation ξ) ≫
          f.residueFieldMap η := by
      rw [← hf, Scheme.Hom.comp_appTop, Category.assoc,
        ← Scheme.Γevaluation_naturality f η]
      rfl
    simpa [CommRingCat.hom_comp, RingHom.comp_assoc] using
      congrArg CommRingCat.Hom.hom hcat
  have htrdegTower :
      Algebra.trdeg k (Y.residueField ξ) +
          Algebra.trdeg (Y.residueField ξ) (X.residueField η) =
        Algebra.trdeg k (X.residueField η) :=
    trdeg_add_eq k (Y.residueField ξ)
  have hreltrdeg : Algebra.trdeg (Y.residueField ξ) (X.residueField η) < Cardinal.aleph0 := by
    apply lt_of_le_of_lt _ hηtrdeg
    rw [← htrdegTower]
    exact le_add_of_nonneg_left zero_le
  let F : Scheme.{u} := f.fiber ξ
  let xF : F := f.asFiber η
  let pF : F ⟶ Spec (.of (Y.residueField ξ)) := f.fiberToSpecResidueField ξ
  let : LocallyOfFiniteType pF :=
    locallyOfFiniteType_fiberToSpecResidueField k pX pY f hf ξ
  have hFgeneric : IsGenericPoint xF (Set.univ : Set F) :=
    isGenericPoint_asFiber_of_isGenericPoint f η hη
  have := irreducibleSpace_of_isGenericPoint hFgeneric
  let : Algebra (Y.residueField ξ) (F.residueField xF) :=
    ((Scheme.ΓSpecIso (.of (Y.residueField ξ))).inv ≫ pF.appTop ≫
      F.Γevaluation xF).hom.toAlgebra
  have hdimF :=
    topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible (Y.residueField ξ) F pF xF
  have htrdegF :=
    topologicalKrullDim_eq_trdeg_residueField (Y.residueField ξ) F pF xF hFgeneric
  have htrdegFη : Algebra.trdeg (Y.residueField ξ) (F.residueField xF) =
      Algebra.trdeg (Y.residueField ξ) (X.residueField η) :=
    f.trdeg_residueField_fiber η
  rw [← hdimF, htrdegF, htrdegFη]
  have hNat := congrArg Cardinal.toNat htrdegTower
  rw [Cardinal.toNat_add hξtrdeg hreltrdeg] at hNat
  have hdimXNat : ((topologicalKrullDim X).unbotD 0).toNat =
      Cardinal.toNat (Algebra.trdeg k (X.residueField η)) := by
    rw [hdimX, WithBot.unbotD_coe]
    rfl
  have hdimZNat : ((topologicalKrullDim Z).unbotD 0).toNat =
      Cardinal.toNat (Algebra.trdeg k (Y.residueField ξ)) := by
    rw [hdimZ, WithBot.unbotD_coe]
    rfl
  rw [hdimXNat, hdimZNat]
  rw [show Cardinal.toNat (Algebra.trdeg k (X.residueField η)) -
      Cardinal.toNat (Algebra.trdeg k (Y.residueField ξ)) =
      Cardinal.toNat (Algebra.trdeg (Y.residueField ξ) (X.residueField η)) by omega]
  have hrelCast : (Cardinal.toNat (Algebra.trdeg (Y.residueField ξ) (X.residueField η)) :
      WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg (Y.residueField ξ) (X.residueField η)) :
        WithBot ℕ∞) := by
    simpa only [Cardinal.toNat_toENat, ENat.WithBot.coe_eq_natCast] using
      congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞))
        (ENat.natCast_toNat (Cardinal.toENat_ne_top.mpr hreltrdeg))
  exact hrelCast.symm

/-- **The dimension of the generic fibre.** For a morphism `f : X ⟶ Y` of schemes locally of
finite type over a field with `X` irreducible, the fibre of `f` over the image of the generic
point of `X` has dimension `dim X - dim Z`, where `Z` is the reduced closure of the image of `f`.
The generic point of `X` is a generic point of that fibre, so the fibre is irreducible and its
dimension is its local dimension there. This is the dimension of the generic fibre read by
`AlgebraicGeometry.Scheme.Hom.fiberDimension`, which is `topologicalKrullDim` of the fibre. -/
public theorem topologicalKrullDim_fiber_genericPoint_eq_imageClosure_sub
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) [IrreducibleSpace X]
    (η : X) (hη : IsGenericPoint η Set.univ) :
    topologicalKrullDim (f.fiber (f η)) =
      ((((topologicalKrullDim X).unbotD 0).toNat -
        ((topologicalKrullDim
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure (Set.range f.base))).subscheme).unbotD 0).toNat : ℕ) :
        WithBot ℕ∞) := by
  have := locallyOfFiniteType_of_comp_eq_left pX pY f hf
  have := irreducibleSpace_of_isGenericPoint (isGenericPoint_asFiber_of_isGenericPoint f η hη)
  let : LocallyOfFiniteType (f.fiberToSpecResidueField (f η)) :=
    locallyOfFiniteType_fiberToSpecResidueField k pX pY f hf (f η)
  rw [topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible (Y.residueField (f η))
    (f.fiber (f η)) (f.fiberToSpecResidueField (f η)) (f.asFiber η)]
  exact topologicalKrullDimAt_fiber_genericPoint_eq_imageClosure_sub k pX pY f hf η hη

/-- The local fibre dimension at the generic point of an irreducible source is a lower bound for
the local fibre dimension at every point, because the locus where the local fibre dimension is
at most a given natural number is open. -/
private lemma fiberDimension_lower_bound_of_genericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [IrreducibleSpace X]
    (η : X) (hη : IsGenericPoint η Set.univ) (d : ℕ)
    (hgeneric : topologicalKrullDimAt (f.fiber (f η)) (f.asFiber η) = (d : WithBot ℕ∞))
    (x : X) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
  by_cases hd : d = 0
  · subst d
    exact topologicalKrullDimAt_nonneg (x := f.asFiber x)
  · by_contra hle
    have hlt : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) < (d : WithBot ℕ∞) :=
      lt_of_not_ge hle
    have hsmall : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤
        ((d - 1 : ℕ) : WithBot ℕ∞) := by
      rcases (WithBot.lt_iff_exists.mp hlt) with ⟨e, heq, he⟩
      have hed : e = (d : ℕ∞) := (WithBot.coe_injective heq).symm
      subst e
      cases hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) with
      | bot => exact bot_le
      | coe a =>
        apply WithBot.coe_le_coe.mpr
        have ha : a < (d : ℕ∞) := he a hdim
        lift a to ℕ using ne_top_of_lt ha with n
        have hn : n < d := by simpa using ha
        exact_mod_cast (Nat.le_pred_of_lt hn)
    have hηsmall : topologicalKrullDimAt (f.fiber (f η)) (f.asFiber η) ≤
        ((d - 1 : ℕ) : WithBot ℕ∞) :=
      (hη.mem_open_set_iff (isOpen_setOf_fiberDimensionAt_le f (d - 1))).2
        ⟨x, by simpa using hsmall⟩
    rw [hgeneric] at hηsmall
    exact (not_le_of_gt (by exact_mod_cast (show d - 1 < d by omega))) hηsmall

/-- **Lower bound for the fibre dimension.** For a morphism `f : X ⟶ Y` of schemes locally of
finite type over a field with `X` irreducible, the local dimension of every fibre of `f` is at
least the dimension of `X` minus the dimension of the reduced closure of the image of `f`. The
bound is stated additively, since `WithBot ℕ∞` has no subtraction. -/
@[stacks 0B2L "part (2a): dim_x(X_{f(x)}) ≥ d", ega "IV 10.6.1" "(iii), special case"]
public theorem topologicalKrullDim_le_fiber_add_imageClosure
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [IrreducibleSpace X]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) :
    topologicalKrullDim X ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) +
        topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure (Set.range (fun x : X => f x)))).subscheme := by
  have := locallyOfFiniteType_of_comp_eq_left pX pY f hf
  let η : X := genericPoint X
  have hη : IsGenericPoint η Set.univ := genericPoint_spec X
  have hgeneric :=
    topologicalKrullDimAt_fiber_genericPoint_eq_imageClosure_sub k pX pY f hf η hη
  let Z := (Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure (Set.range (fun x : X => f x)))).subscheme
  let A := topologicalKrullDim X
  let B := topologicalKrullDim Z
  have hAfinite : A ≠ ⊤ := by
    let : Algebra k (X.residueField η) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ pX.appTop ≫ X.Γevaluation η).hom.toAlgebra
    let : FinTrdeg k (X.residueField η) := residueField_finTrdeg k pX η
    show topologicalKrullDim X ≠ ⊤
    rw [topologicalKrullDim_eq_trdeg_residueField k X pX η hη]
    exact fun h ↦ (Cardinal.toENat_ne_top.mpr (trdeg_lt_aleph0 k _))
      (WithBot.coe_injective h)
  have hAnonbot : A ≠ ⊥ := fun h ↦
    ((topologicalKrullDim_eq_bot_iff_isEmpty X).mp h).false η
  have hA_nat := eq_natCast_unbotD_toNat hAnonbot hAfinite
  have hfiber := fiberDimension_lower_bound_of_genericPoint f η hη
    ((((A.unbotD 0).toNat - (B.unbotD 0).toNat : ℕ))) hgeneric x
  show A ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) + B
  have hF0 : (0 : WithBot ℕ∞) ≤ topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) :=
    topologicalKrullDimAt_nonneg (x := f.asFiber x)
  by_cases hBtop : B = ⊤
  · have hFbot : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≠ ⊥ := by
      intro h; rw [h] at hF0; exact (not_le_of_gt (WithBot.bot_lt_coe 0)) hF0
    cases hF : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) with
    | bot => exact (hFbot hF).elim
    | coe a =>
      have hsum : (a : WithBot ℕ∞) + (⊤ : WithBot ℕ∞) = ⊤ := by
        rw [← WithBot.coe_top, ← WithBot.coe_add]
        simp
      rw [hBtop, hsum]
      exact le_top
  · have hBbot : B ≠ ⊥ := by
      have hZne : Nonempty Z := by
        refine ⟨⟨f η, ?_⟩⟩
        have hsupp : ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure (Set.range (fun x : X => f x)))).support : Set Y) =
              closure (Set.range (fun x : X => f x)) :=
          Scheme.IdealSheafData.coe_support_vanishingIdeal _
        show f η ∈ ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (Set.range (fun x : X => f x)))).support : Set Y)
        rw [hsupp]
        exact subset_closure ⟨η, rfl⟩
      exact fun h ↦ ((topologicalKrullDim_eq_bot_iff_isEmpty Z).mp h).false hZne.some
    have hB_nat := eq_natCast_unbotD_toNat hBbot hBtop
    let n := (A.unbotD 0).toNat
    let m := (B.unbotD 0).toNat
    rw [hA_nat, hB_nat]
    by_cases hmn : m ≤ n
    · have hcast : (n : WithBot ℕ∞) = ((n - m : ℕ) : WithBot ℕ∞) + (m : WithBot ℕ∞) :=
        congrArg (fun q : ℕ ↦ (q : WithBot ℕ∞)) (Nat.sub_add_cancel hmn).symm
      rw [hcast]
      change ((n - m : ℕ) : WithBot ℕ∞) ≤
        topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) at hfiber
      exact add_le_add hfiber (le_refl (m : WithBot ℕ∞))
    · have hnm : n ≤ m := Nat.le_of_not_ge hmn
      exact (WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hnm)).trans
        (le_add_of_nonneg_left hF0)

/-- **The fibre dimension is generically the expected one.** For a morphism `f : X ⟶ Y` of schemes
locally of finite type over a field with `X` irreducible, the set of points at which the local
fibre dimension attains the value `d = dim X - dim Z` is a dense open subset of `X`. Here `Z` is
the reduced closure of the image of `f`, and `d` is the difference of the two dimensions taken in
`ℕ`, since `WithBot ℕ∞` has no subtraction. -/
@[stacks 0B2L "part (2b): {x | dim_x(X_{f(x)}) = d} is dense open"]
public theorem isOpen_and_dense_setOf_topologicalKrullDimAt_fiber_eq
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [IrreducibleSpace X]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (d : ℕ)
    (hd : d = ((topologicalKrullDim X).unbotD 0).toNat -
      ((topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (Set.range (fun x : X => f x)))).subscheme).unbotD 0).toNat) :
    IsOpen {x : X | topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)} ∧
      Dense {x : X |
        topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)} := by
  have := locallyOfFiniteType_of_comp_eq_left pX pY f hf
  let η : X := genericPoint X
  have hη : IsGenericPoint η Set.univ := genericPoint_spec X
  have hgeneric : topologicalKrullDimAt (f.fiber (f η)) (f.asFiber η) = (d : WithBot ℕ∞) := by
    rw [hd]
    exact topologicalKrullDimAt_fiber_genericPoint_eq_imageClosure_sub k pX pY f hf η hη
  have hlb : ∀ x : X, (d : WithBot ℕ∞) ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) :=
    fiberDimension_lower_bound_of_genericPoint f η hη d hgeneric
  have hset : {x : X | topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)} =
      {x : X | topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ (d : WithBot ℕ∞)} :=
    Set.ext fun x => ⟨le_of_eq, fun h => le_antisymm h (hlb x)⟩
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact isOpen_setOf_fiberDimensionAt_le f d
  · rw [dense_iff_closure_eq]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hη]
    exact closure_mono (Set.singleton_subset_iff.mpr hgeneric)

/-- The local dimension of a fibre is unchanged when the source is replaced by a scheme mapping
homeomorphically onto it: the two set-theoretic fibres correspond under the homeomorphism. -/
private lemma fiberDimensionAt_comp_isHomeomorph {X' X S : Scheme.{u}}
    (ρ : X' ⟶ X) (hρ : IsHomeomorph ρ.base) (f : X ⟶ S) (x' : X') :
    topologicalKrullDimAt ((ρ ≫ f).fiber ((ρ ≫ f) x')) ((ρ ≫ f).asFiber x') =
      topologicalKrullDimAt (f.fiber (f (ρ x'))) (f.asFiber (ρ x')) := by
  let eρ : X' ≃ₜ X := hρ.homeomorph
  let A : Set X' := (ρ ≫ f) ⁻¹' {(ρ ≫ f) x'}
  let B : Set X := f ⁻¹' {f (ρ x')}
  have hmem : ∀ y : X', y ∈ A ↔ eρ y ∈ B := by
    intro y
    simp only [A, B, Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
    exact Iff.rfl
  rw [topologicalKrullDimAt_eq_of_homeomorph ((ρ ≫ f).fiberHomeo _) _,
    topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo _) _]
  have hpA : ((ρ ≫ f).fiberHomeo _) ((ρ ≫ f).asFiber x') = (⟨x', by simp [A]⟩ : A) := by
    ext; exact (ρ ≫ f).fiberι_asFiber x'
  have hpB : (f.fiberHomeo _) (f.asFiber (ρ x')) = (⟨ρ x', by simp [B]⟩ : B) := by
    ext; exact f.fiberι_asFiber (ρ x')
  rw [hpA, hpB, topologicalKrullDimAt_eq_of_homeomorph (eρ.subtype hmem) ⟨x', by simp [A]⟩]
  rfl

/-- The reduction map `X_red ⟶ X` carries a generic point of `X_red` to a generic point of `X`. -/
private theorem isGenericPoint_reductionι {X : Scheme.{u}} [IrreducibleSpace X]
    {η : X.reduction} (hη : IsGenericPoint η (Set.univ : Set X.reduction)) :
    IsGenericPoint (X.reductionι η) (Set.univ : Set X) := by
  rw [hη.eq (genericPoint_spec X.reduction), Scheme.reductionι_genericPoint X]
  exact genericPoint_spec X

/-- **The factorization of a morphism through the reduced closure of its image.** The reduction
of the source is reduced, so it factors through the reduced induced structure `Z` on the closure
of the image (Tag 0356); the resulting morphism `X_red ⟶ Z` has the same local fibre dimensions
as `f`, and it carries a generic point of `X_red` to a generic point of `Z`.

This is what lets parts (2c) and (2d) of Tag 0B2L be read off Tags 0B2K and 0B2I, whose
hypotheses and conclusions are about the local rings of the *target*: those local rings have to
be the local rings of `Z`, not of `Y`. -/
private theorem exists_lift_reduction_imageClosure {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IrreducibleSpace X] :
    ∃ g : X.reduction ⟶ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (Set.range (fun x : X => f x)))).subscheme,
      LocallyOfFiniteType g ∧
      (∀ w : X.reduction,
        (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure (Set.range (fun x : X => f x)))).subschemeι (g w) =
          f (X.reductionι w)) ∧
      (∀ w : X.reduction,
        topologicalKrullDimAt (g.fiber (g w)) (g.asFiber w) =
          topologicalKrullDimAt (f.fiber (f (X.reductionι w)))
            (f.asFiber (X.reductionι w))) ∧
      (∀ η : X.reduction, IsGenericPoint η (Set.univ : Set X.reduction) →
        g η ∈ genericPoints (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (Set.range (fun x : X => f x)))).subscheme) := by
  set I : Y.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range (fun x : X => f x)))
    with hIdef
  have hIsupp : (I.support : Set Y) = closure (Set.range (fun x : X => f x)) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hιinj : Function.Injective (I.subschemeι).base :=
    (Scheme.Hom.isClosedEmbedding I.subschemeι).injective
  have hrange : Set.range (X.reductionι ≫ f) ⊆ (I.support : Set Y) := by
    rw [hIsupp]
    rintro y ⟨w, rfl⟩
    exact subset_closure ⟨X.reductionι w, by simp⟩
  obtain ⟨g, hg⟩ := (Scheme.IdealSheafData.exists_lift_subschemeι_iff_range_subset_support I
    (X.reductionι ≫ f)).2 hrange
  have hgι : ∀ w : X.reduction, I.subschemeι (g w) = f (X.reductionι w) := by
    intro w
    have h := congrArg (fun m : X.reduction ⟶ Y => m w) hg
    simpa using h
  have hgft : LocallyOfFiniteType g := by
    have : LocallyOfFiniteType (g ≫ I.subschemeι) := by rw [hg]; infer_instance
    exact locallyOfFiniteType_of_comp g I.subschemeι
  refine ⟨g, hgft, hgι, ?_, ?_⟩
  · intro w
    calc topologicalKrullDimAt (g.fiber (g w)) (g.asFiber w)
        = topologicalKrullDimAt ((g ≫ I.subschemeι).fiber ((g ≫ I.subschemeι) w))
            ((g ≫ I.subschemeι).asFiber w) :=
          (fiberDimensionAt_comp_embedding g I.subschemeι hιinj w).symm
      _ = topologicalKrullDimAt ((X.reductionι ≫ f).fiber ((X.reductionι ≫ f) w))
            ((X.reductionι ≫ f).asFiber w) := by rw [hg]
      _ = topologicalKrullDimAt (f.fiber (f (X.reductionι w))) (f.asFiber (X.reductionι w)) :=
          fiberDimensionAt_comp_isHomeomorph X.reductionι (Scheme.isHomeomorph_reductionι X) f w
  · intro η hη
    have hcl : closure ({f (X.reductionι η)} : Set Y) =
        closure (Set.range (fun x : X => f x)) :=
      (closure_range_eq_closure_singleton_of_isGenericPoint (fun x : X => f x) f.continuous
        (isGenericPoint_reductionι hη)).symm
    have hgen : IsGenericPoint (g η) (Set.univ : Set I.subscheme) := by
      have hind : Topology.IsInducing (I.subschemeι).base :=
        (Scheme.Hom.isClosedEmbedding I.subschemeι).isEmbedding.isInducing
      show closure ({g η} : Set I.subscheme) = Set.univ
      rw [hind.closure_eq_preimage_closure_image, Set.image_singleton, hgι η, hcl, ← hIsupp]
      refine Set.eq_univ_of_forall fun p => ?_
      rw [Set.mem_preimage, ← I.range_subschemeι]
      exact ⟨p, rfl⟩
    have := irreducibleSpace_of_isGenericPoint hgen
    exact mem_genericPoints_of_isGenericPoint_univ hgen

/-- The factorization `g : X_red ⟶ Z` of `f` has fibre dimension `dim X - dim Z` at every
generic point of `X_red`. -/
private theorem topologicalKrullDimAt_fiber_reduction_genericPoint
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [IrreducibleSpace X]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (g : X.reduction ⟶ Z)
    (hgdim : ∀ w : X.reduction, topologicalKrullDimAt (g.fiber (g w)) (g.asFiber w) =
      topologicalKrullDimAt (f.fiber (f (X.reductionι w))) (f.asFiber (X.reductionι w)))
    (η : X.reduction) (hη : IsGenericPoint η (Set.univ : Set X.reduction)) :
    topologicalKrullDimAt (g.fiber (g η)) (g.asFiber η) =
      ((((topologicalKrullDim X).unbotD 0).toNat -
        ((topologicalKrullDim
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure (Set.range f.base))).subscheme).unbotD 0).toNat : ℕ) :
        WithBot ℕ∞) := by
  rw [hgdim η]
  exact topologicalKrullDimAt_fiber_genericPoint_eq_imageClosure_sub k pX pY f hf _
    (isGenericPoint_reductionι hη)

/-- A scheme locally of finite type over a field has Noetherian stalks. -/
private theorem isNoetherianRing_stalk_of_locallyOfFiniteType {k : Type u} [Field k]
    {Z : Scheme.{u}} (pZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType pZ] (z : Z) :
    IsNoetherianRing (Z.presheaf.stalk z) :=
  have := LocallyOfFiniteType.isLocallyNoetherian pZ
  inferInstance

/-- **Upper bound for the fibre dimension over a point of higher codimension.** For a morphism
`f : X ⟶ Y` of schemes locally of finite type over a field with `X` irreducible, if the local ring
of the reduced closure `Z` of the image of `f` at `f x` has dimension at least one, then

`dim_x(X_{f(x)}) ≤ d + dim 𝒪_{Z, f(x)} - 1`,

where `d = dim X - dim Z`. Since `WithBot ℕ∞` has no subtraction, the bound is stated by adding
one to the left-hand side, as in Tag 0B2K. The point of `Z` over `f x` is given by `z`. -/
@[stacks 0B2L "part (2c): dim_x(X_{f(x)}) ≤ d + dim O_{Z,f(x)} - 1"]
public theorem topologicalKrullDimAt_fiber_add_one_le_of_one_le_ringKrullDim_imageClosure
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [IrreducibleSpace X]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (d : ℕ)
    (hd : d = ((topologicalKrullDim X).unbotD 0).toNat -
      ((topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (Set.range (fun x : X => f x)))).subscheme).unbotD 0).toNat)
    (x : X)
    (z : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range (fun x : X => f x)))).subscheme)
    (hz : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range (fun x : X => f x)))).subschemeι z = f x)
    (h1 : 1 ≤ ringKrullDim
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (Set.range (fun x : X => f x)))).subscheme.presheaf.stalk z)) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) + 1 ≤
      (d : WithBot ℕ∞) + ringKrullDim
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (Set.range (fun x : X => f x)))).subscheme.presheaf.stalk z) := by
  have := locallyOfFiniteType_of_comp_eq_left pX pY f hf
  obtain ⟨g, hgft, hgι, hgdim, hggen⟩ := exists_lift_reduction_imageClosure f
  obtain ⟨w, rfl⟩ := X.surjective_reductionι x
  have hgw : g w = z :=
    (Scheme.Hom.isClosedEmbedding (Scheme.IdealSheafData.subschemeι _)).injective
      (by rw [hgι w, hz])
  have := isNoetherianRing_stalk_of_locallyOfFiniteType
    (Scheme.IdealSheafData.subschemeι _ ≫ pY) (g w)
  have hhyp : ∀ C ∈ irreducibleComponents X.reduction, w ∈ C → ∀ η : X.reduction,
      IsGenericPoint η C →
        (g η ≠ g w ∧ topologicalKrullDimAt (g.fiber (g η)) (g.asFiber η) = (d : WithBot ℕ∞)) := by
    intro C hC _ η hηC
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hC
    subst hC
    refine ⟨?_, ?_⟩
    · intro hcontra
      rw [← hgw, ← hcontra, ringKrullDim_stalk_eq_zero_of_mem_genericPoints _ (g η)
        (hggen η hηC)] at h1
      exact absurd h1 (by simp)
    · rw [hd]
      exact topologicalKrullDimAt_fiber_reduction_genericPoint k pX pY f hf g hgdim η hηC
  have key := topologicalKrullDimAt_fiber_add_one_le_of_genericPoints g w d hhyp
  rwa [hgdim w, hgw] at key

/-- **The fibre dimension over a point of codimension one.** For a morphism `f : X ⟶ Y` of schemes
locally of finite type over a field with `X` irreducible, if the local ring of the reduced closure
`Z` of the image of `f` at `f x` has dimension exactly one, then `dim_x(X_{f(x)}) = d`, where
`d = dim X - dim Z`. The point of `Z` over `f x` is given by `z`. -/
@[stacks 0B2L "part (2d): dim O_{Z,f(x)} = 1 implies dim_x(X_{f(x)}) = d"]
public theorem topologicalKrullDimAt_fiber_eq_of_ringKrullDim_imageClosure_eq_one
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY] [IrreducibleSpace X]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (d : ℕ)
    (hd : d = ((topologicalKrullDim X).unbotD 0).toNat -
      ((topologicalKrullDim
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure (Set.range (fun x : X => f x)))).subscheme).unbotD 0).toNat)
    (x : X)
    (z : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range (fun x : X => f x)))).subscheme)
    (hz : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range (fun x : X => f x)))).subschemeι z = f x)
    (h1 : ringKrullDim
      ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (Set.range (fun x : X => f x)))).subscheme.presheaf.stalk z) = 1) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  have := locallyOfFiniteType_of_comp_eq_left pX pY f hf
  obtain ⟨g, hgft, hgι, hgdim, hggen⟩ := exists_lift_reduction_imageClosure f
  obtain ⟨w, rfl⟩ := X.surjective_reductionι x
  have hgw : g w = z :=
    (Scheme.Hom.isClosedEmbedding (Scheme.IdealSheafData.subschemeι _)).injective
      (by rw [hgι w, hz])
  have hnoeth := isNoetherianRing_stalk_of_locallyOfFiniteType
    (Scheme.IdealSheafData.subschemeι _ ≫ pY) (g w)
  have hle : ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range (fun x : X => f x)))).subscheme.presheaf.stalk (g w)) ≤ 1 := by
    rw [hgw, h1]
  have hhyp : ∀ η : X.reduction, closure ({η} : Set X.reduction) ∈
      irreducibleComponents X.reduction → w ∈ closure ({η} : Set X.reduction) →
      topologicalKrullDimAt (g.fiber (g η)) (g.asFiber η) = (d : WithBot ℕ∞) := by
    intro η hηC _
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hηC
    rw [hd]
    exact topologicalKrullDimAt_fiber_reduction_genericPoint k pX pY f hf g hgdim η hηC
  have key := topologicalKrullDimAt_fiber_eq_of_target_dim_le_one g w hnoeth hle d hhyp
  rwa [hgdim w] at key

/-- The reduced induced subscheme on a closed subset is homeomorphic to that subset: its
inclusion is a closed embedding with image the subset. -/
private noncomputable def homeomorphSubschemeVanishingIdeal {T : Scheme.{u}} (C : Closeds T) :
    (Scheme.IdealSheafData.vanishingIdeal C).subscheme ≃ₜ (C : Set T) :=
  (Scheme.Hom.isClosedEmbedding
      (Scheme.IdealSheafData.vanishingIdeal C).subschemeι).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.coe_support_vanishingIdeal]))

/-- The reduced induced subscheme on a closed subset has the dimension of that subset. -/
private lemma topologicalKrullDim_subscheme_vanishingIdeal {T : Scheme.{u}} (C : Closeds T) :
    topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal C).subscheme =
      topologicalKrullDim (C : Set T) :=
  (homeomorphSubschemeVanishingIdeal C).isHomeomorph.topologicalKrullDim_eq

open Stacks.AlgebraicGeometry.LimitFibreDimensionBound in
/-- **Local lower bound for the fibre dimension.** For a morphism `f : X ⟶ Y` of schemes locally of
finite type over a field and any point `x` of `X` with image `y = f x`,

`dim_x(X_y) ≥ dim_x(X) - dim_y(Y)`.

The source is not assumed irreducible: the bound is obtained by applying part (2a) to each
irreducible component of `X` through `x`, carrying the reduced induced structure. As elsewhere,
the statement is additive because `WithBot ℕ∞` has no subtraction. -/
@[stacks 0B2L "part (3): dim_x(X_y) ≥ dim_x(X) - dim_y(Y)"]
public theorem topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX) (x : X) :
    topologicalKrullDimAt X x ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) + topologicalKrullDimAt Y (f x) := by
  have := locallyOfFiniteType_of_comp_eq_left pX pY f hf
  have hmono : ∀ {s t : Set Y}, s ⊆ t →
      topologicalKrullDim s ≤ topologicalKrullDim t := fun h =>
    (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDimAt_eq_iSup_irreducibleComponents k X pX x]
  refine iSup_le fun C => iSup_le fun hC => ?_
  obtain ⟨hCcomp, hxC⟩ := hC
  let CC : Closeds X := ⟨C, isClosed_of_mem_irreducibleComponents C hCcomp⟩
  let J : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal CC
  let ι : J.subscheme ⟶ X := J.subschemeι
  have hJsupp : (J.support : Set X) = C :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal CC
  let : IrreducibleSpace J.subscheme :=
    (homeomorphSubschemeVanishingIdeal CC).irreducibleSpace_iff.mpr
      (Subtype.irreducibleSpace hCcomp.1)
  let pW : J.subscheme ⟶ Spec (.of k) := ι ≫ pX
  let : LocallyOfFiniteType pW := inferInstance
  let g : J.subscheme ⟶ Y := ι ≫ f
  have hg : g ≫ pY = pW := by
    show (ι ≫ f) ≫ pY = ι ≫ pX
    rw [Category.assoc, hf]
  let xW : J.subscheme := ⟨x, by
    show x ∈ (J.support : Set X)
    rw [hJsupp]
    exact hxC⟩
  have hιxW : ι xW = x := rfl
  have key := topologicalKrullDim_le_fiber_add_imageClosure k pW pY g hg xW
  have hdimC : topologicalKrullDim C = topologicalKrullDim J.subscheme :=
    (topologicalKrullDim_subscheme_vanishingIdeal CC).symm
  have hfib : topologicalKrullDimAt (g.fiber (g xW)) (g.asFiber xW) ≤
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) := by
    rw [← hιxW]
    exact fiberDimensionAt_le_of_isClosedImmersion ι f g rfl xW
  have hVirr : IsIrreducible (closure (Set.range (fun w : J.subscheme => g w))) := by
    refine IsIrreducible.closure ?_
    rw [← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ J.subscheme).image _ g.continuous.continuousOn
  obtain ⟨C', hC', hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hVirr
  have hfxV : f x ∈ closure (Set.range (fun w : J.subscheme => g w)) :=
    subset_closure ⟨xW, hιxW ▸ rfl⟩
  have himg : topologicalKrullDim
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure (Set.range (fun w : J.subscheme => g w)))).subscheme ≤
      topologicalKrullDimAt Y (f x) := by
    rw [topologicalKrullDim_subscheme_vanishingIdeal,
      topologicalKrullDimAt_eq_iSup_irreducibleComponents k Y pY (f x)]
    refine le_trans (hmono (show
      (Closeds.closure (Set.range (fun w : J.subscheme => g w)) : Set Y) ⊆ C' from hsub)) ?_
    exact le_iSup_of_le C' (le_iSup_of_le ⟨hC', hsub hfxV⟩ le_rfl)
  rw [hdimC]
  exact key.trans (add_le_add hfib himg)

end AlgebraicGeometry

end
