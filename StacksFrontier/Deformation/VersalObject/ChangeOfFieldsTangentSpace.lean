module

public import Mathlib.Algebra.DualNumber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.PredeformationTangent.TangentVectorSpace
public import StacksFrontier.Deformation.ResidueField.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.VersalObject.ChangeOfFieldsConditionS2
import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentTensor

/-!
# The tangent space after a change of residue field

Let `Λ → k → l` be the standing finite tower of a Noetherian base ring and two residue fields,
and let `𝓕` be a predeformation category over `𝒞_{Λ,k}` whose associated functor of fibrewise
isomorphism classes satisfies Schlessinger's condition (S2). Writing `𝓖` for the
change-of-residue-field category over `𝒞_{Λ,l}`, this file produces a canonical `l`-linear
equivalence

`l ⊗_k T𝓕 ≃ₗ[l] T𝓖`

between the scalar extension of the tangent space of `𝓕` and the tangent space of `𝓖`, and
pins it down on pure tensors.

The tangent space of a predeformation category is the vector space structure of Tag 06IH on
the value of its associated functor at the dual numbers, so both sides are values of functors
on finite-dimensional vector spaces and the equivalence is produced from a natural bijection.
Three steps build that bijection.

First, the comparison functor `G : B ↦ B ×_l k` carries the square-zero extension `l[V]` of an
`l`-vector space `V` to the square-zero extension `k[V]` of `V` restricted along `k → l`: on
underlying rings both are the same set of pairs, and the identification respects the algebra
and residue structures, so it is an isomorphism of `𝒞_{Λ,k}` natural in `V`.

Second, the fibrewise isomorphism classes of `𝓖` over `B` are those of `𝓕` over `G B`
(Tag 07WA), and the associated functor of `𝓖` therefore satisfies (S2): the category of
elements of the composite `G ⋙ (classes of 𝓕)` is the categorical pullback of the category of
elements of the classes of `𝓕` along `G`, (S2) transports along that equivalence by the
change-of-fields result for (S2), and a pointwise bijection of set-valued functors carries
(S2) between their categories of elements.

Combining the two gives, for each `l`-vector space `V`, a bijection from `V ⊗_k T𝓕` to the
value at `l[V]` of the associated functor of `𝓖`, natural in `V`. Evaluating at `V = l` and
using that a natural bijection of additive, linear functors into modules is linear — proved by
testing on a biproduct — yields the asserted `l`-linear equivalence. The tensor factors are
written `V ⊗_k T` so that the left-module instance supplies the `l`-linear structure.

The pure-tensor formula pins the equivalence to the canonical inclusion `k[ε] → k[lε]`: a
tangent vector tensored with `1` is pushed forward along that inclusion and then carried by
the change-of-fields map on fibrewise isomorphism classes. Since pure tensors generate, this
determines the equivalence.

## Main definitions

* `Deformation.tangentSpaceChangeOfFields`: the `l`-linear equivalence from the scalar
  extension of the tangent space of `𝓕` to the tangent space of its change of residue field.
* `Deformation.canonicalDualNumberInclusion`: the morphism `k[ε] → k[lε]` of `𝒞_{Λ,k}` whose
  first pullback coordinate extends both coefficients along `k → l` and whose second
  coordinate is the original residue, together with those coordinate formulas.

## Main results

* `Deformation.associatedSchlessingerConditionS2_changeOfFields`: the associated functor of
  the changed predeformation category satisfies (S2) whenever the original one does.
* `Deformation.tangentSpaceChangeOfFields_tmul_one`: the value of the equivalence on a tangent
  vector tensored with `1`.

## Implementation notes

The fields and the carriers of the Artinian algebras are taken in a common universe, as the
tangent-space construction of Tag 06IH requires.

Because a vector space over a field carries a unique compatible right action, the
opposite-module and central-scalar instances needed to form the square-zero extensions are
supplied as named local instances rather than being sought by synthesis.

## References

* [Stacks Project, Tag 07WB](https://stacks.math.columbia.edu/tag/07WB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w y z

namespace Deformation

private abbrev kDualNumbers (S : ChangeOfFieldsSituation.{u, v, v}) :=
  (artinianSquareZeroExtensionFunctor S.Λ S.k).obj
    (FGModuleCat.of S.k S.k)

private abbrev lDualNumbers (S : ChangeOfFieldsSituation.{u, v, v}) :=
  (artinianSquareZeroExtensionFunctor S.Λ S.l).obj
    (FGModuleCat.of S.l S.l)

private abbrev comparedLDualNumbers
    (S : ChangeOfFieldsSituation.{u, v, v}) :=
  (comparisonFunctor S).functor.obj (lDualNumbers S)

local instance changeOfFieldsResidueOppModule
    (S : ChangeOfFieldsSituation.{u, v, v}) : Module S.kᵐᵒᵖ S.l :=
  Module.oppositeOfCommSemiring S.k S.l

local instance changeOfFieldsResidueCentralScalar
    (S : ChangeOfFieldsSituation.{u, v, v}) : IsCentralScalar S.k S.l :=
  Module.isCentralScalar_oppositeOfCommSemiring S.k S.l

/-- Extending both coordinates of a dual number along `k → l` is a ring map. -/
private def dualNumberScalarMap (S : ChangeOfFieldsSituation.{u, v, v}) :
    TrivSqZeroExt S.k S.l →+* TrivSqZeroExt S.l S.l where
  toFun a := (⟨algebraMap S.k S.l a.fst, a.snd⟩ : TrivSqZeroExt S.l S.l)
  map_one' := by ext <;> simp
  map_mul' a b := by
    apply Prod.ext
    · change algebraMap S.k S.l (a.fst * b.fst) =
        algebraMap S.k S.l a.fst * algebraMap S.k S.l b.fst
      exact map_mul (algebraMap S.k S.l) _ _
    · change (a * b).snd =
        (algebraMap S.k S.l a.fst) • b.snd +
          MulOpposite.op (algebraMap S.k S.l b.fst) • a.snd
      rw [TrivSqZeroExt.snd_mul]
      simp [Algebra.smul_def, mul_comm]
  map_zero' := by ext <;> simp
  map_add' a b := by
    apply Prod.ext
    · change algebraMap S.k S.l (a.fst + b.fst) =
        algebraMap S.k S.l a.fst + algebraMap S.k S.l b.fst
      exact map_add (algebraMap S.k S.l) _ _
    · rfl

private def dualNumberModuleInclusion
    (S : ChangeOfFieldsSituation.{u, v, v}) :
    TrivSqZeroExt S.k S.k →+* TrivSqZeroExt S.k S.l :=
  (TrivSqZeroExt.map (Algebra.linearMap S.k S.l)).toRingHom

local instance changeFieldsSquareZeroKModule
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : Module S.k V :=
  Module.compHom V (algebraMap S.k S.l)

local instance changeFieldsSquareZeroKOppModule
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : Module S.kᵐᵒᵖ V :=
  Module.compHom V {
    toFun := fun a => algebraMap S.k S.l (MulOpposite.unop a)
    map_one' := by simp
    map_mul' := by intro a b; simp [mul_comm]
    map_zero' := by simp
    map_add' := by intro a b; simp }

local instance changeFieldsSquareZeroLOppModule
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : Module S.lᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring S.l V

local instance changeFieldsSquareZeroLCentral
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : IsCentralScalar S.l V :=
  Module.isCentralScalar_oppositeOfCommSemiring S.l V

local instance changeFieldsSquareZeroKCentral
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : IsCentralScalar S.k V := ⟨fun _ _ => rfl⟩

local instance changeFieldsSquareZeroLRing
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : CommRing (TrivSqZeroExt S.l V) :=
  TrivSqZeroExt.commRing

local instance changeFieldsSquareZeroKRing
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : CommRing (TrivSqZeroExt S.k V) :=
  TrivSqZeroExt.commRing

local instance changeFieldsSquareZeroKLTower
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : IsScalarTower S.k S.l V :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

local instance changeFieldsSquareZeroKFinite
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : Module.Finite S.k V :=
  Module.Finite.trans S.l V

private noncomputable def squareZeroExtensionScalarMap
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) : TrivSqZeroExt S.k V →+* TrivSqZeroExt S.l V := by
  letI : Module S.k V := Module.compHom V (algebraMap S.k S.l)
  letI : Module S.kᵐᵒᵖ V := Module.compHom V
    { toFun := fun a => algebraMap S.k S.l (MulOpposite.unop a)
      map_one' := by simp
      map_mul' := by intro a b; simp [mul_comm]
      map_zero' := by simp
      map_add' := by intro a b; simp }
  letI : IsCentralScalar S.k V := ⟨fun _ _ => rfl⟩
  letI : CommRing (TrivSqZeroExt S.k V) := TrivSqZeroExt.commRing
  letI : CommRing (TrivSqZeroExt S.l V) := TrivSqZeroExt.commRing
  exact {
    toFun := fun a => ⟨algebraMap S.k S.l a.fst, a.snd⟩
    map_one' := by ext <;> simp
    map_mul' := by
      intro a b
      apply Prod.ext
      · exact map_mul (algebraMap S.k S.l) _ _
      · change (a * b).snd =
          ((TrivSqZeroExt.commRing.toMul).mul
            (⟨algebraMap S.k S.l a.fst, a.snd⟩ : TrivSqZeroExt S.l V)
            (⟨algebraMap S.k S.l b.fst, b.snd⟩ : TrivSqZeroExt S.l V)).snd
        rw [TrivSqZeroExt.snd_mul]
        rfl
    map_zero' := by ext <;> simp
    map_add' := by
      intro a b
      apply Prod.ext
      · exact map_add (algebraMap S.k S.l) _ _
      · rfl }

private noncomputable def squareZeroExtensionPullbackEquiv
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) :
    TrivSqZeroExt S.k V ≃+*
      RingHom.pullback (residueMap S
        ((artinianSquareZeroExtensionFunctor S.Λ S.l).obj V))
        (algebraMap S.k S.l) := by
  let B := (artinianSquareZeroExtensionFunctor S.Λ S.l).obj V
  let P := RingHom.pullback
    (residueMap S B) (algebraMap S.k S.l)
  let m := squareZeroExtensionScalarMap S V
  let g : TrivSqZeroExt S.k V →+* S.k :=
    (TrivSqZeroExt.fstHom S.k S.k V).toRingHom
  let φ : TrivSqZeroExt S.k V →+* P :=
    RingHom.codRestrict (RingHom.prod m g) P (by
      intro a
      change residueMap S B (m a) = algebraMap S.k S.l (g a)
      rfl)
  refine RingEquiv.ofBijective φ ⟨?_, ?_⟩
  · intro a b h
    have h₂ := congrArg (RingHom.pullbackSnd
      (residueMap S B) (algebraMap S.k S.l)) h
    have h₁ := congrArg (fun x : P => TrivSqZeroExt.snd
      (RingHom.pullbackFst (residueMap S B)
        (algebraMap S.k S.l) x)) h
    have hfst : a.fst = b.fst := by
      dsimp [φ, g, TrivSqZeroExt.fstHom] at h₂
      exact h₂
    have hsnd : a.snd = b.snd := by
      change (m a).snd = (m b).snd at h₁
      dsimp [m, squareZeroExtensionScalarMap] at h₁
      exact h₁
    exact Prod.ext hfst hsnd
  · intro x
    rcases x with ⟨⟨b, c⟩, hx⟩
    change b.fst = algebraMap S.k S.l c at hx
    refine ⟨⟨c, b.snd⟩, ?_⟩
    apply Subtype.ext
    change (m ⟨c, b.snd⟩, g ⟨c, b.snd⟩) = (b, c)
    apply Prod.ext
    · change (algebraMap S.k S.l c, b.snd) = b
      apply Prod.ext
      · exact hx.symm
      · rfl
    · rfl

private theorem squareZeroExtensionPullbackEquiv_coordinates
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) (x : TrivSqZeroExt S.k V) :
    (squareZeroExtensionPullbackEquiv S V x).val =
      ((algebraMap S.k S.l x.fst, x.snd), x.fst) := rfl

private noncomputable def squareZeroExtensionComparisonIso
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) :
    ((artinianSquareZeroExtensionFunctor S.Λ S.k).obj
      (FGModuleCat.of S.k V)) ≅
    (comparisonFunctor S).functor.obj
      ((artinianSquareZeroExtensionFunctor S.Λ S.l).obj V) := by
  let A := (artinianSquareZeroExtensionFunctor S.Λ S.k).obj
    (FGModuleCat.of S.k V)
  let B := (artinianSquareZeroExtensionFunctor S.Λ S.l).obj V
  let C := (comparisonFunctor S).functor.obj B
  let R := squareZeroExtensionPullbackEquiv S V
  let e : TrivSqZeroExt S.k V ≃+* ↑C :=
    R.trans ((comparisonFunctor S).pullbackEquiv B).symm
  have heAlg : ∀ r : S.Λ, e (algebraMap S.Λ A r) = algebraMap S.Λ C r := by
    intro r
    apply (comparisonFunctor S).pullbackEquiv B |>.injective
    apply Subtype.ext
    have hA : algebraMap S.Λ A r = TrivSqZeroExt.inl (algebraMap S.Λ S.k r) := by rfl
    have hB : algebraMap S.Λ B r = TrivSqZeroExt.inl (algebraMap S.Λ S.l r) := by rfl
    rw [hA]
    change ((comparisonFunctor S).pullbackEquiv B
      (e (TrivSqZeroExt.inl (algebraMap S.Λ S.k r)))).val = _
    simp only [e, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
    rw [squareZeroExtensionPullbackEquiv_coordinates]
    apply Prod.ext
    · rw [(comparisonFunctor S).algebraMap_fst B r, hB]
      apply Prod.ext
      · change algebraMap S.k S.l (algebraMap S.Λ S.k r) = algebraMap S.Λ S.l r
        exact (IsScalarTower.algebraMap_apply S.Λ S.k S.l r).symm
      · rfl
    · rw [(comparisonFunctor S).algebraMap_snd B r]
      rfl
  let E : A ≃ₐ[S.Λ] C := by
    dsimp [A, artinianSquareZeroExtensionFunctor]
    exact AlgEquiv.ofRingEquiv (f := e) heAlg
  refine {
    hom := {
      hom := E.toAlgHom
      isLocal := ⟨fun a hu => by
        have h : IsUnit (E.symm (E a)) := hu.map E.symm.toMonoidHom
        simpa only [AlgEquiv.symm_apply_apply] using h⟩
      residue_comm := ?_ }
    inv := {
      hom := E.symm.toAlgHom
      isLocal := ⟨fun a hu => by
        have h : IsUnit (E (E.symm a)) := hu.map E.toMonoidHom
        simpa only [AlgEquiv.apply_symm_apply] using h⟩
      residue_comm := ?_ }
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · intro a
    rw [(comparisonFunctor S).residue_snd]
    let Q := (comparisonFunctor S).pullbackEquiv B
    change ((comparisonFunctor S).pullbackEquiv B
      (E (a : TrivSqZeroExt S.k V))).val.2 = a.fst
    change ((comparisonFunctor S).pullbackEquiv B
      (e (a : TrivSqZeroExt S.k V))).val.2 = a.fst
    change (Q (Q.symm (R (a : TrivSqZeroExt S.k V)))).val.2 = a.fst
    rw [Q.apply_symm_apply]
    exact congrArg Prod.snd (squareZeroExtensionPullbackEquiv_coordinates S V a)
  · intro a
    rw [(comparisonFunctor S).residue_snd]
    change (E.symm a).fst =
      ((comparisonFunctor S).pullbackEquiv B a).val.2
    let x : TrivSqZeroExt S.k V := E.symm a
    have hx : E (E.symm a) = e x := rfl
    have hcoord :
        ((comparisonFunctor S).pullbackEquiv B
          (E (E.symm a))).val.2 = x.fst := by
      rw [hx]
      let Q := (comparisonFunctor S).pullbackEquiv B
      change (Q (Q.symm (R x))).val.2 = x.fst
      rw [Q.apply_symm_apply]
      exact congrArg Prod.snd (squareZeroExtensionPullbackEquiv_coordinates S V x)
    rw [E.apply_symm_apply] at hcoord
    simpa [x] using hcoord.symm
  · apply ArtinianLocalAlgCat.hom_ext
    ext a
    simp
  · apply ArtinianLocalAlgCat.hom_ext
    ext a
    simp

private theorem lDualNumbers_residue_fst_carrier
    (S : ChangeOfFieldsSituation.{u, v, v})
    (x : ↑(lDualNumbers S)) :
    residueMap S (lDualNumbers S) x = TrivSqZeroExt.fst x := by
  rfl

/-- The dual numbers `K[ε]` as an Artinian local `Λ`-algebra. -/
private abbrev dualNumbersOf (Λ : Type u) (K : Type v) [CommRing Λ] [Field K] [Algebra Λ K] :=
  (artinianSquareZeroExtensionFunctor Λ K).obj (FGModuleCat.of K K)

private theorem dualNumbers_fst_mul
    (Λ : Type u) (K : Type v) [CommRing Λ] [Field K] [Algebra Λ K]
    (x y : TrivSqZeroExt K K) :
    (((dualNumbersOf Λ K).commRing.toMul).mul x y).fst = x.fst * y.fst := by
  let V := (forget₂ (FGModuleCat K) (ModuleCat K)).obj (FGModuleCat.of K K)
  let : Module Kᵐᵒᵖ V := Module.compHom V
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by intros; simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  let : IsCentralScalar K V := ⟨fun _ _ => rfl⟩
  have hcomm : (dualNumbersOf Λ K).commRing = TrivSqZeroExt.commRing := by rfl
  rw [hcomm]
  exact TrivSqZeroExt.fst_mul x y

private theorem dualNumbers_snd_mul
    (Λ : Type u) (K : Type v) [CommRing Λ] [Field K] [Algebra Λ K]
    (x y : TrivSqZeroExt K K) :
    (((dualNumbersOf Λ K).commRing.toMul).mul x y).snd =
      x.fst • y.snd + MulOpposite.op y.fst • x.snd := by
  let V := (forget₂ (FGModuleCat K) (ModuleCat K)).obj (FGModuleCat.of K K)
  let xt : TrivSqZeroExt K ↑V := x
  let yt : TrivSqZeroExt K ↑V := y
  let : Module Kᵐᵒᵖ V := Module.compHom V
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by intros; simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  let : IsCentralScalar K V := ⟨fun _ _ => rfl⟩
  have hcomm : (dualNumbersOf Λ K).commRing = TrivSqZeroExt.commRing := by rfl
  have hright : (((dualNumbersOf Λ K).commRing.toMul).mul xt yt).snd =
      xt.fst • yt.snd + MulOpposite.op yt.fst • xt.snd := by
    rw [hcomm]
    exact TrivSqZeroExt.snd_mul xt yt
  simpa [xt, yt, mul_comm] using hright

private def dualNumbersCarrierRingEquiv
    (Λ : Type u) (K : Type v) [CommRing Λ] [Field K] [Algebra Λ K] :
    TrivSqZeroExt K K ≃+* ↑(dualNumbersOf Λ K) where
  toFun x := ⟨x.fst, x.snd⟩
  invFun x := ⟨x.fst, x.snd⟩
  left_inv x := by apply TrivSqZeroExt.ext <;> rfl
  right_inv x := by apply TrivSqZeroExt.ext <;> rfl
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact (dualNumbers_fst_mul Λ K x y).symm
    · exact (dualNumbers_snd_mul Λ K x y).symm
  map_add' x y := by
    dsimp [artinianSquareZeroExtensionFunctor,
      squareZeroExtensionRestriction, squareZeroExtensionFunctor,
      trivSqZeroExtFunctor, FGModuleCat.of]
    apply TrivSqZeroExt.ext
    · rfl
    · rfl

private theorem dualNumbers_algebraMap_coordinates
    (Λ : Type u) (K : Type v) [CommRing Λ] [Field K] [Algebra Λ K] (r : Λ) :
    (dualNumbersCarrierRingEquiv Λ K).symm (algebraMap Λ ↑(dualNumbersOf Λ K) r) =
      (algebraMap Λ K r, 0) := by
  let V := (forget₂ (FGModuleCat K) (ModuleCat K)).obj (FGModuleCat.of K K)
  let : Module Kᵐᵒᵖ V := Module.compHom V
    { toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by intros; simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  let : IsCentralScalar K V := ⟨fun _ _ => rfl⟩
  let : Module Λ V := Module.compHom V (algebraMap Λ K)
  let : IsScalarTower Λ K V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower Λ Kᵐᵒᵖ V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply (dualNumbersCarrierRingEquiv Λ K).injective
  rw [(dualNumbersCarrierRingEquiv Λ K).apply_symm_apply]
  apply TrivSqZeroExt.ext
  · change (TrivSqZeroExt.inl (algebraMap Λ K r)).fst = _
    rfl
  · change (TrivSqZeroExt.inl (algebraMap Λ K r)).snd = _
    rfl

private abbrev kDualNumbersCarrierRingEquiv (S : ChangeOfFieldsSituation.{u, v, v}) :=
  dualNumbersCarrierRingEquiv S.Λ S.k

private abbrev lDualNumbersCarrierRingEquiv (S : ChangeOfFieldsSituation.{u, v, v}) :=
  dualNumbersCarrierRingEquiv S.Λ S.l

private theorem kDualNumbers_algebraMap_coordinates
    (S : ChangeOfFieldsSituation.{u, v, v}) (r : S.Λ) :
    (kDualNumbersCarrierRingEquiv S).symm (algebraMap S.Λ ↑(kDualNumbers S) r) =
      (algebraMap S.Λ S.k r, 0) :=
  dualNumbers_algebraMap_coordinates S.Λ S.k r

private theorem lDualNumbers_algebraMap_coordinates
    (S : ChangeOfFieldsSituation.{u, v, v}) (r : S.Λ) :
    (lDualNumbersCarrierRingEquiv S).symm (algebraMap S.Λ ↑(lDualNumbers S) r) =
      (algebraMap S.Λ S.l r, 0) :=
  dualNumbers_algebraMap_coordinates S.Λ S.l r

private theorem kDualNumbers_residue_fst
    (S : ChangeOfFieldsSituation.{u, v, v}) (a : ↑(kDualNumbers S)) :
    (kDualNumbers S).residueEquiv (IsLocalRing.residue (kDualNumbers S) a) =
      TrivSqZeroExt.fst ((kDualNumbersCarrierRingEquiv S).symm a) := by
  have hobj :
      (squareZeroExtensionArtinian S.Λ S.k).obj (FGModuleCat.of S.k S.k) =
        kDualNumbers S := by
    simpa [kDualNumbers] using congrArg
      (fun F => F.obj (FGModuleCat.of S.k S.k))
      (squareZeroExtensionArtinian_eq S.Λ S.k)
  cases hobj
  exact squareZeroExtensionArtinian_residue S.Λ S.k
    (FGModuleCat.of S.k S.k) ((kDualNumbersCarrierRingEquiv S).symm a)

/-- The coordinate realization of `k[l ε]` as the pullback used by the
change-of-fields comparison. -/
private noncomputable def dualNumberPullbackEquiv
    (S : ChangeOfFieldsSituation.{u, v, v}) :
    TrivSqZeroExt S.k S.l ≃+*
      RingHom.pullback (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom
        (algebraMap S.k S.l) := by
  let P := RingHom.pullback (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom
    (algebraMap S.k S.l)
  let f := dualNumberScalarMap S
  let g : TrivSqZeroExt S.k S.l →+* S.k :=
    (TrivSqZeroExt.fstHom S.k S.k S.l).toRingHom
  let φ : TrivSqZeroExt S.k S.l →+* P :=
    RingHom.codRestrict (RingHom.prod f g) P (by
      intro a
      change (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom (f a) =
        algebraMap S.k S.l (g a)
      rfl)
  refine RingEquiv.ofBijective φ ⟨?_, ?_⟩
  · intro a b h
    have hsnd := congrArg (RingHom.pullbackSnd
      (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom (algebraMap S.k S.l)) h
    have hnil := congrArg (fun x : P ↦ TrivSqZeroExt.snd
      (RingHom.pullbackFst
        (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom (algebraMap S.k S.l) x)) h
    have hsnd' : a.fst = b.fst := by
      dsimp [g, TrivSqZeroExt.fstHom] at hsnd
      exact hsnd
    have hnil' : a.snd = b.snd := by
      change (f a).snd = (f b).snd at hnil
      dsimp [f, dualNumberScalarMap] at hnil
      exact hnil
    exact Prod.ext hsnd' hnil'
  · intro z
    rcases z with ⟨⟨b, c⟩, hz⟩
    change b.fst = algebraMap S.k S.l c at hz
    refine ⟨⟨c, b.snd⟩, ?_⟩
    apply Subtype.ext
    change (f ⟨c, b.snd⟩, g ⟨c, b.snd⟩) = (b, c)
    apply Prod.ext
    · change (algebraMap S.k S.l c, b.snd) = b
      apply Prod.ext
      · exact hz.symm
      · rfl
    · rfl

private theorem dualNumberPullbackEquiv_coordinates
    (S : ChangeOfFieldsSituation.{u, v, v})
    (x : TrivSqZeroExt S.k S.l) :
    (dualNumberPullbackEquiv S x).val =
      ((algebraMap S.k S.l x.fst, x.snd), x.fst) := by
  rfl

private noncomputable def standardPullbackToComparisonEquiv
    (S : ChangeOfFieldsSituation.{u, v, v}) :
    RingHom.pullback (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom
        (algebraMap S.k S.l) ≃+*
      RingHom.pullback (residueMap S (lDualNumbers S))
        (algebraMap S.k S.l) := by
  let P := RingHom.pullback (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom
    (algebraMap S.k S.l)
  let Q := RingHom.pullback (residueMap S (lDualNumbers S))
    (algebraMap S.k S.l)
  let e := lDualNumbersCarrierRingEquiv S
  let eprod := RingEquiv.prodCongr e (RingEquiv.refl S.k)
  let f : P →+* Q := RingHom.codRestrict
    (eprod.toRingHom.comp P.subtype) Q (by
    intro z
    change residueMap S (lDualNumbers S) (e z.val.1) =
      algebraMap S.k S.l z.val.2
    have hz : TrivSqZeroExt.fst z.val.1 = algebraMap S.k S.l z.val.2 := by
      have hmem := z.property
      change (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom z.val.1 =
        algebraMap S.k S.l z.val.2 at hmem
      exact hmem
    have hr : residueMap S (lDualNumbers S) (e z.val.1) =
        TrivSqZeroExt.fst (e z.val.1) := lDualNumbers_residue_fst_carrier S _
    calc
      residueMap S (lDualNumbers S) (e z.val.1) =
          TrivSqZeroExt.fst (e z.val.1) := hr
      _ = TrivSqZeroExt.fst z.val.1 := by
        rfl
      _ = algebraMap S.k S.l z.val.2 := hz)
  refine RingEquiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    change eprod x.val = eprod y.val at h'
    exact eprod.injective h'
  · intro y
    rcases y with ⟨⟨b, c⟩, hy⟩
    have hval : (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom (e.symm b) =
      algebraMap S.k S.l c := by
      change residueMap S (lDualNumbers S) b = algebraMap S.k S.l c at hy
      have hres : residueMap S (lDualNumbers S) b =
          TrivSqZeroExt.fst (e.symm b) := by
        calc
          residueMap S (lDualNumbers S) b = TrivSqZeroExt.fst b :=
            lDualNumbers_residue_fst_carrier S b
          _ = TrivSqZeroExt.fst (e.symm b) := by
            rfl
      have hy' : TrivSqZeroExt.fst (e.symm b) = algebraMap S.k S.l c :=
        hres.symm.trans hy
      change TrivSqZeroExt.fst (e.symm b) = _
      exact hy'
    refine ⟨⟨(e.symm b, c), hval⟩, ?_⟩
    apply Subtype.ext
    change eprod (e.symm b, c) = (b, c)
    simp [eprod, e]

private theorem standardPullbackToComparisonEquiv_coordinates
    (S : ChangeOfFieldsSituation.{u, v, v})
    (z : RingHom.pullback (TrivSqZeroExt.fstHom S.l S.l S.l).toRingHom
      (algebraMap S.k S.l)) :
    (standardPullbackToComparisonEquiv S z).val =
      (lDualNumbersCarrierRingEquiv S z.val.1, z.val.2) := by
  rfl

private noncomputable def dualNumberExtensionComparisonEquiv
    (S : ChangeOfFieldsSituation.{u, v, v}) :
    TrivSqZeroExt S.k S.l ≃+* ↑(comparedLDualNumbers S) :=
  (dualNumberPullbackEquiv S).trans <|
    (standardPullbackToComparisonEquiv S).trans <|
      (comparisonFunctor S).pullbackEquiv (lDualNumbers S) |>.symm

private theorem dualNumberExtensionComparisonEquiv_coordinates
    (S : ChangeOfFieldsSituation.{u, v, v})
    (x : TrivSqZeroExt S.k S.l) :
    ((comparisonFunctor S).pullbackEquiv (lDualNumbers S)
      (dualNumberExtensionComparisonEquiv S x)).val =
        ((algebraMap S.k S.l x.fst, x.snd), x.fst) := by
  rw [dualNumberExtensionComparisonEquiv]
  simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rw [standardPullbackToComparisonEquiv_coordinates,
    dualNumberPullbackEquiv_coordinates]
  rfl

private def changePullbackToElements
    {C : Type u} [Category.{v} C] {D : Type z} [Category.{w} D]
    (F : C ⥤ Type y) (G : D ⥤ C) :
    CategoricalPullback (Functor.Elements.π F) G ⥤ (G ⋙ F).Elements where
  obj x := (G ⋙ F).elementsMk x.snd (F.map x.iso.hom x.fst.2)
  map {x x'} f := Functor.Elements.homMk f.snd (by
    change F.map (G.map f.snd) (F.map x.iso.hom x.fst.2) =
      F.map x'.iso.hom x'.fst.2
    calc F.map (G.map f.snd) (F.map x.iso.hom x.fst.2)
        = F.map (x.iso.hom ≫ G.map f.snd) x.fst.2 := by rw [F.map_comp]; rfl
      _ = F.map ((Functor.Elements.π F).map f.fst ≫ x'.iso.hom) x.fst.2 :=
          congrArg (fun φ => F.map φ x.fst.2) f.w.symm
      _ = F.map x'.iso.hom x'.fst.2 := by
          rw [F.map_comp]
          exact congrArg (F.map x'.iso.hom) f.fst.map_val)
  map_id x := by apply Functor.Elements.hom_ext; rfl
  map_comp f g := by apply Functor.Elements.hom_ext; rfl

private def elementsToChangePullback
    {C : Type u} [Category.{v} C] {D : Type z} [Category.{w} D]
    (F : C ⥤ Type y) (G : D ⥤ C) :
    (G ⋙ F).Elements ⥤ CategoricalPullback (Functor.Elements.π F) G where
  obj x := ⟨F.elementsMk (G.obj x.1) x.2, x.1, Iso.refl _⟩
  map {x x'} f :=
    { fst := Functor.Elements.homMk (G.map f.hom) (by simpa using f.map_val)
      snd := f.hom
      w := by
        change G.map f.hom ≫ 𝟙 _ = 𝟙 _ ≫ G.map f.hom
        simp }
  map_id x := by
    apply CategoricalPullback.hom_ext
    · apply Functor.Elements.hom_ext
      change G.map (𝟙 _) = 𝟙 _
      simp
    · rfl
  map_comp f g := by
    apply CategoricalPullback.hom_ext
    · apply Functor.Elements.hom_ext
      change G.map (f.hom ≫ g.hom) = G.map f.hom ≫ G.map g.hom
      simp
    · rfl

private def changePullbackElementsEquivalence
    {C : Type u} [Category.{v} C] {D : Type z} [Category.{w} D]
    (F : C ⥤ Type y) (G : D ⥤ C) :
    CategoricalPullback (Functor.Elements.π F) G ≌ (G ⋙ F).Elements where
  functor := changePullbackToElements F G
  inverse := elementsToChangePullback F G
  unitIso := NatIso.ofComponents (fun x =>
    CategoricalPullback.mkIso
      (Functor.Elements.isoMk x.iso (by rfl)) (Iso.refl _)
      (by
        change x.iso.hom ≫ 𝟙 _ = x.iso.hom ≫ G.map (𝟙 _)
        simp)) (by
    intro x y f
    apply CategoricalPullback.hom_ext
    · apply Functor.Elements.hom_ext
      change f.fst.hom ≫ y.iso.hom = x.iso.hom ≫ G.map f.snd
      exact f.w
    · change f.snd ≫ 𝟙 _ = 𝟙 _ ≫ f.snd
      simp)
  counitIso := NatIso.ofComponents (fun x =>
    Functor.Elements.isoMk (Iso.refl _)
      (by
        change F.map (G.map (𝟙 x.1)) (F.map (𝟙 (G.obj x.1)) x.2) = x.2
        simp)) (by
    intro x y f
    apply Functor.Elements.hom_ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  functor_unitIso_comp x := by
    apply Functor.Elements.hom_ext
    change 𝟙 x.snd ≫ 𝟙 _ = 𝟙 _
    simp

/-- A completion over `Φ ⋙ p` of a square gives a completion over `p` of its image under `Φ`. -/
private def pullbackCompletionOfComp {X Y C : Type*} [Category X] [Category Y] [Category C]
    (Φ : Y ⥤ X) (p : X ⥤ C) {y₁ y₂ y : Y} {d : y₁ ⟶ y} {e : y₂ ⟶ y} {A : C}
    {g₁ : A ⟶ p.obj (Φ.obj y₁)} {g₂ : A ⟶ p.obj (Φ.obj y₂)}
    (P : PullbackCompletion (Φ ⋙ p) d e g₁ g₂) :
    PullbackCompletion p (Φ.map d) (Φ.map e) g₁ g₂ where
  apex := Φ.obj P.apex
  apex_eq := P.apex_eq
  toFirst := Φ.map P.toFirst
  toSecond := Φ.map P.toSecond
  comm := by simpa using congrArg Φ.map P.comm
  map_toFirst := P.map_toFirst
  map_toSecond := P.map_toSecond

/-- The counit of an equivalence carries a commuting square in the source to a commuting square
in the target. -/
private theorem equivalence_counit_comm {X Y : Type*} [Category X] [Category Y] (E : X ≌ Y)
    {a : X} {x xε x₀ : Y} {d : x ⟶ x₀} {e : xε ⟶ x₀} {s : a ⟶ E.inverse.obj x}
    {t : a ⟶ E.inverse.obj xε} (h : t ≫ E.inverse.map e = s ≫ E.inverse.map d) :
    (E.functor.map t ≫ E.counitIso.hom.app xε) ≫ e =
      (E.functor.map s ≫ E.counitIso.hom.app x) ≫ d := by
  have hn {A B : Y} (f : A ⟶ B) :
      E.functor.map (E.inverse.map f) ≫ E.counitIso.hom.app B = E.counitIso.hom.app A ≫ f :=
    E.counit_naturality f
  rw [Category.assoc, Category.assoc, ← hn, ← hn, ← Category.assoc, ← Category.assoc,
    ← E.functor.map_comp, ← E.functor.map_comp, h]

/-- A factorization after applying the inverse of an equivalence descends along the counit. -/
private theorem equivalence_counit_factor {X Y : Type*} [Category X] [Category Y] (E : X ≌ Y)
    {a a' x : Y} {s : a ⟶ x} {s' : a' ⟶ x} {b : E.inverse.obj a ⟶ E.inverse.obj a'}
    (h : E.inverse.map s = b ≫ E.inverse.map s') :
    s = (E.counitIso.inv.app a ≫ E.functor.map b ≫ E.counitIso.hom.app a') ≫ s' := by
  have hn {A B : Y} (f : A ⟶ B) :
      E.functor.map (E.inverse.map f) ≫ E.counitIso.hom.app B = E.counitIso.hom.app A ≫ f :=
    E.counit_naturality f
  rw [Category.assoc, Category.assoc, ← hn s', ← Category.assoc (E.functor.map b),
    ← E.functor.map_comp, ← h, hn, Iso.inv_hom_id_app_assoc]

private theorem schlessingerS2_changePullbackElements
    (S : ChangeOfFieldsSituation.{u, v, v})
    (F : ArtinianLocalAlgCat.{u, v, v} S.Λ S.k ⥤ Type y)
    (h : SchlessingerConditionS2
      (CategoricalPullback.π₂ (Functor.Elements.π F)
        (comparisonFunctor S).functor)) :
    SchlessingerConditionS2
      (Functor.Elements.π ((comparisonFunctor S).functor ⋙ F)) := by
  let e := changePullbackElementsEquivalence F (comparisonFunctor S).functor
  let p := CategoricalPullback.π₂ (Functor.Elements.π F)
    (comparisonFunctor S).functor
  let q := Functor.Elements.π ((comparisonFunctor S).functor ⋙ F)
  constructor
  · intro x xε x₀ d e' hdual Aε g gε hpull
    obtain ⟨P⟩ := h.completion (e.inverse.map d) (e.inverse.map e') hdual g gε hpull
    exact ⟨{
      apex := e.functor.obj P.apex
      apex_eq := P.apex_eq
      toFirst := e.functor.map P.toFirst ≫ e.counitIso.hom.app x
      toSecond := e.functor.map P.toSecond ≫ e.counitIso.hom.app xε
      comm := equivalence_counit_comm e P.comm
      map_toFirst := P.map_toFirst
      map_toSecond := P.map_toSecond }⟩
  · intro x xε x₀ d e' hdual Aε g gε hpull P Q
    obtain ⟨b, hb, hbp⟩ := h.comparison (e.inverse.map d) (e.inverse.map e') hdual g gε hpull
      (pullbackCompletionOfComp e.inverse p P) (pullbackCompletionOfComp e.inverse p Q)
    refine ⟨_, equivalence_counit_factor e hb, ?_⟩
    have hcInv (A : ((comparisonFunctor S).functor ⋙ F).Elements) :
        q.map (e.counitIso.inv.app A) = 𝟙 (q.obj A) := rfl
    have hcHom (A : ((comparisonFunctor S).functor ⋙ F).Elements) :
        q.map (e.counitIso.hom.app A) = 𝟙 (q.obj A) := rfl
    rw [Functor.map_comp, Functor.map_comp, hcInv, hcHom]
    exact hbp

private def elementsEquivalenceOfPointwiseEquiv
    (S : ChangeOfFieldsSituation.{u, v, v})
    (F : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l ⥤ Type y)
    (G : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l ⥤ Type z)
    (e : ∀ A, F.obj A ≃ G.obj A)
    (hnat : ∀ {A B} (f : A ⟶ B) (x : F.obj A),
      e B (F.map f x) = G.map f (e A x)) :
    F.Elements ≌ G.Elements where
  functor := {
    obj := fun x => G.elementsMk x.1 (e x.1 x.2)
    map := fun {x x'} f => Functor.Elements.homMk f.hom (by
      calc
        G.map f.hom (e x.1 x.2) = e x'.1 (F.map f.hom x.2) := (hnat f.hom x.2).symm
        _ = e x'.1 x'.2 := congrArg (e x'.1) f.map_val)
    map_id := by intros; apply Functor.Elements.hom_ext; rfl
    map_comp := by intros; apply Functor.Elements.hom_ext; rfl }
  inverse := {
    obj := fun x => F.elementsMk x.1 ((e x.1).symm x.2)
    map := fun {x x'} f => Functor.Elements.homMk f.hom (by
      apply (e x'.1).injective
      calc
        e x'.1 (F.map f.hom ((e x.1).symm x.2)) =
            G.map f.hom (e x.1 ((e x.1).symm x.2)) := hnat f.hom _
        _ = G.map f.hom x.2 := by simp
        _ = x'.2 := f.map_val
        _ = e x'.1 ((e x'.1).symm x'.2) := by simp)
    map_id := by intros; apply Functor.Elements.hom_ext; rfl
    map_comp := by intros; apply Functor.Elements.hom_ext; rfl }
  unitIso := NatIso.ofComponents (fun x =>
    Functor.Elements.isoMk (Iso.refl _) (by simp)) (by
    intro x x' f
    apply Functor.Elements.hom_ext
    rfl)
  counitIso := NatIso.ofComponents (fun x =>
    Functor.Elements.isoMk (Iso.refl _) (by simp)) (by
    intro x x' f
    apply Functor.Elements.hom_ext
    rfl)
  functor_unitIso_comp x := by
    apply Functor.Elements.hom_ext
    rfl

private theorem schlessingerS2_of_pointwiseEquiv
    (S : ChangeOfFieldsSituation.{u, v, v})
    (F : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l ⥤ Type y)
    (G : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l ⥤ Type z)
    (e : ∀ A, F.obj A ≃ G.obj A)
    (hnat : ∀ {A B} (f : A ⟶ B) (x : F.obj A),
      e B (F.map f x) = G.map f (e A x))
    (h : SchlessingerConditionS2 (Functor.Elements.π F)) :
    SchlessingerConditionS2 (Functor.Elements.π G) := by
  let E := elementsEquivalenceOfPointwiseEquiv S F G e hnat
  let p := Functor.Elements.π F
  let q := Functor.Elements.π G
  constructor
  · intro x xε x₀ d e' hdual Aε g gε hpull
    obtain ⟨P⟩ := h.completion (E.inverse.map d) (E.inverse.map e') hdual g gε hpull
    exact ⟨{
      apex := E.functor.obj P.apex
      apex_eq := P.apex_eq
      toFirst := E.functor.map P.toFirst ≫ E.counitIso.hom.app x
      toSecond := E.functor.map P.toSecond ≫ E.counitIso.hom.app xε
      comm := equivalence_counit_comm E P.comm
      map_toFirst := P.map_toFirst
      map_toSecond := P.map_toSecond }⟩
  · intro x xε x₀ d e' hdual Aε g gε hpull P Q
    obtain ⟨b, hb, hbp⟩ := h.comparison (E.inverse.map d) (E.inverse.map e') hdual g gε hpull
      (pullbackCompletionOfComp E.inverse p P) (pullbackCompletionOfComp E.inverse p Q)
    refine ⟨_, equivalence_counit_factor E hb, ?_⟩
    have hcInv (A : G.Elements) : q.map (E.counitIso.inv.app A) = 𝟙 (q.obj A) := rfl
    have hcHom (A : G.Elements) : q.map (E.counitIso.hom.app A) = 𝟙 (q.obj A) := rfl
    rw [Functor.map_comp, Functor.map_comp, hcInv, hcHom]
    exact hbp

/-- The associated functor of the changed predeformation category satisfies
(S2) whenever the original associated functor does. -/
private noncomputable def associatedClassesChangeOfFieldsEquiv
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (B : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :
    let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
    let hq := changeOfFieldsProjection_isPredeformationCategory
      S 𝓕.p hp
    let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
      ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
    ((comparisonFunctor S).functor ⋙
      isomorphismClasses 𝓕 hp.cofibered).obj B ≃
        (isomorphismClasses 𝓖 hq.cofibered).obj B := by
  let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
  let hq := changeOfFieldsProjection_isPredeformationCategory
    S 𝓕.p hp
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
    (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
  let comp := (comparisonFunctor S).functor
  let oldClasses := isomorphismClasses 𝓕 hp.cofibered
  let newClasses := isomorphismClasses 𝓖 hq.cofibered
  exact (Equiv.cast (isomorphismClasses_obj 𝓕 hp.cofibered (comp.obj B))).trans <|
    (changeOfFieldsIsoClassEquiv
      S 𝓕.p hp.cofibered B).trans <|
        (Equiv.cast (isomorphismClasses_obj 𝓖 hq.cofibered B)).symm

private theorem associatedClassesChangeOfFields_naturality
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    {B C : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l}
    (f : B ⟶ C)
    (x : ((comparisonFunctor S).functor ⋙
      isomorphismClasses 𝓕 hp.cofibered).obj B) :
    let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
    let hq := changeOfFieldsProjection_isPredeformationCategory
      S 𝓕.p hp
    let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
        (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
      ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
    associatedClassesChangeOfFieldsEquiv S 𝓕 hp C
      (((comparisonFunctor S).functor ⋙
        isomorphismClasses 𝓕 hp.cofibered).map f x) =
      (isomorphismClasses 𝓖 hq.cofibered).map f
        (associatedClassesChangeOfFieldsEquiv S 𝓕 hp B x) := by
  let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
  let hq := changeOfFieldsProjection_isPredeformationCategory
    S 𝓕.p hp
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
  let comp := (comparisonFunctor S).functor
  let oldClasses := isomorphismClasses 𝓕 hp.cofibered
  let newClasses := isomorphismClasses 𝓖 hq.cofibered
  let classEquiv (D : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    associatedClassesChangeOfFieldsEquiv S 𝓕 hp D
  obtain ⟨a, ha⟩ := classOf_surjective 𝓕 hp.cofibered
    (comp.obj B) x
  rw [← ha]
  let : 𝓕.p.op.IsFibered := hp.cofibered.isFibered
  let incB := (changeOfFieldsFiberInclusion S 𝓕.p B).obj a
  let oldFiberOp : 𝓕.p.op.Fiber (Opposite.op (comp.obj B)) :=
    ⟨Opposite.op a.1, congrArg Opposite.op a.2⟩
  let oldPBop := 𝓕.p.op.pullbackFiber oldFiberOp (comp.map f).op
  let a' : 𝓕.p.Fiber (comp.obj C) :=
    ⟨Opposite.unop oldPBop.1, congrArg Opposite.unop oldPBop.2⟩
  let oldArrow := (Functor.IsPreFibered.pullbackMap oldFiberOp.2
    (comp.map f).op).unop
  have hOldLift : 𝓕.p.IsHomLift (comp.map f) oldArrow := by
    refine IsHomLift.of_fac 𝓕.p (comp.map f) oldArrow a.2 a'.2 ?_
    simpa [oldArrow, oldPBop, oldFiberOp, Functor.op, op_comp] using
      congrArg Quiver.Hom.unop
        (IsHomLift.fac 𝓕.p.op (comp.map f).op
          (Functor.IsPreFibered.pullbackMap oldFiberOp.2 (comp.map f).op))
  have hOldMap : oldClasses.map (comp.map f)
      (classOf 𝓕 hp.cofibered a) =
      classOf 𝓕 hp.cofibered a' := by
    let := hOldLift
    exact map_classOf 𝓕 hp.cofibered (comp.map f) a a' oldArrow
  have hClassOf (D : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l)
      (b : 𝓕.p.Fiber (comp.obj D)) :
      classEquiv D (classOf 𝓕 hp.cofibered b) =
        classOf 𝓖 hq.cofibered
          ((changeOfFieldsFiberInclusion S 𝓕.p D).obj b) := by
    let e := Equiv.cast (isomorphismClasses_obj 𝓖 hq.cofibered D)
    change e.symm (changeOfFieldsIsoClassMap
      S 𝓕.p D (Equiv.cast
        (isomorphismClasses_obj 𝓕 hp.cofibered (comp.obj D))
        (classOf 𝓕 hp.cofibered b))) = _
    have hmap : changeOfFieldsIsoClassMap
        S 𝓕.p D (Equiv.cast
          (isomorphismClasses_obj 𝓕 hp.cofibered (comp.obj D))
          (classOf 𝓕 hp.cofibered b)) =
        e (classOf 𝓖 hq.cofibered
          ((changeOfFieldsFiberInclusion S 𝓕.p D).obj b)) := by
      let inc := (changeOfFieldsFiberInclusion S 𝓕.p D).obj b
      change changeOfFieldsIsoClassMap S 𝓕.p D
          (cast (isomorphismClasses_obj 𝓕 hp.cofibered (comp.obj D))
            (classOf 𝓕 hp.cofibered b)) =
        cast (isomorphismClasses_obj 𝓖 hq.cofibered D)
          (classOf 𝓖 hq.cofibered inc)
      rw [classOf_eq 𝓕 hp.cofibered b,
        classOf_eq 𝓖 hq.cofibered inc]
      simp only [changeOfFieldsIsoClassMap]
      exact Quotient.map_mk _ _ _
    calc
      e.symm (changeOfFieldsIsoClassMap
          S 𝓕.p D (Equiv.cast
            (isomorphismClasses_obj 𝓕 hp.cofibered (comp.obj D))
            (classOf 𝓕 hp.cofibered b))) =
          e.symm (e (classOf 𝓖 hq.cofibered
            ((changeOfFieldsFiberInclusion S 𝓕.p D).obj b))) :=
        congrArg e.symm hmap
      _ = _ := e.symm_apply_apply _
  let : q.op.IsFibered := hq.cofibered.isFibered
  let newFiberOp : q.op.Fiber (Opposite.op B) :=
    ⟨Opposite.op incB.1, congrArg Opposite.op incB.2⟩
  let newPBop := q.op.pullbackFiber newFiberOp f.op
  let b : q.Fiber C :=
    ⟨Opposite.unop newPBop.1, congrArg Opposite.unop newPBop.2⟩
  let newArrow := (Functor.IsPreFibered.pullbackMap newFiberOp.2 f.op).unop
  have hNewLift : q.IsHomLift f newArrow := by
    refine IsHomLift.of_fac q f newArrow incB.2 b.2 ?_
    simpa [newArrow, newPBop, newFiberOp, Functor.op, op_comp] using
      congrArg Quiver.Hom.unop
        (IsHomLift.fac q.op f.op
          (Functor.IsPreFibered.pullbackMap newFiberOp.2 f.op))
  have hNewMap : newClasses.map f
      (classOf 𝓖 hq.cofibered incB) =
      classOf 𝓖 hq.cofibered b := by
    let := hNewLift
    exact map_classOf 𝓖 hq.cofibered f incB b newArrow
  have hWA := changeOfFieldsIsoClassMap_naturality
    S 𝓕.p hp.cofibered f a
  have hClassPush : classOf 𝓖 hq.cofibered b =
      classOf 𝓖 hq.cofibered
        ((changeOfFieldsFiberInclusion S 𝓕.p C).obj a') := by
    apply (Equiv.cast (isomorphismClasses_obj 𝓖 hq.cofibered C)).injective
    simp only [Equiv.cast_apply]
    rw [classOf_eq 𝓖 hq.cofibered b,
      classOf_eq 𝓖 hq.cofibered
        ((changeOfFieldsFiberInclusion S 𝓕.p C).obj a')]
    let incC := (changeOfFieldsFiberInclusion S 𝓕.p C).obj a'
    have hPB : q.op.isoClassPresheaf.map f.op.op (q.op.isoClassMk newFiberOp) =
        q.op.isoClassMk newPBop :=
      Functor.isoClassPresheaf_map_isoClassMk (p := q.op) f.op newFiberOp
    have hWA' : q.op.isoClassMk newPBop = q.op.isoClassMk
        (⟨Opposite.op incC.1, congrArg Opposite.op incC.2⟩ :
          q.op.Fiber (Opposite.op C)) := by
      exact hPB.symm.trans hWA
    have hClassRep : Quotient.mk (isIsomorphicSetoid (q.Fiber C)) b =
        Quotient.mk (isIsomorphicSetoid (q.Fiber C)) incC := by
      obtain ⟨i⟩ := Quotient.exact hWA'
      let i' : b.1 ≅ incC.1 := {
        hom := by simpa [b, incC] using i.inv.val.unop
        inv := by simpa [b, incC] using i.hom.val.unop
        hom_inv_id := by
          change i.inv.val.unop ≫ i.hom.val.unop = 𝟙 _
          calc
            i.inv.val.unop ≫ i.hom.val.unop =
                (i.hom.val ≫ i.inv.val).unop :=
                  (CategoryTheory.unop_comp (f := i.hom.val) (g := i.inv.val)).symm
            _ = (𝟙 _).unop := congrArg Quiver.Hom.unop
              (congrArg (fun g => g.val) i.hom_inv_id)
            _ = _ := rfl
        inv_hom_id := by
          change i.hom.val.unop ≫ i.inv.val.unop = 𝟙 _
          calc
            i.hom.val.unop ≫ i.inv.val.unop =
                (i.inv.val ≫ i.hom.val).unop :=
                  (CategoryTheory.unop_comp (f := i.inv.val) (g := i.hom.val)).symm
            _ = (𝟙 _).unop := congrArg Quiver.Hom.unop
              (congrArg (fun g => g.val) i.inv_hom_id)
            _ = _ := rfl }
      have hHom : q.IsHomLift (𝟙 C) i'.hom := by
        let : q.op.IsHomLift (𝟙 (Opposite.op C)) i.inv.val := i.inv.property
        simpa [i'] using isHomLift_unop q (𝟙 (Opposite.op C)) i.inv.val
      have hInv : q.IsHomLift (𝟙 C) i'.inv := by
        let : q.op.IsHomLift (𝟙 (Opposite.op C)) i.hom.val := i.hom.property
        simpa [i'] using isHomLift_unop q (𝟙 (Opposite.op C)) i.hom.val
      let := hHom
      let := hInv
      let j : b ≅ incC := {
        hom := Functor.Fiber.homMk q C i'.hom
        inv := Functor.Fiber.homMk q C i'.inv
        hom_inv_id := by apply Functor.Fiber.hom_ext; exact i'.hom_inv_id
        inv_hom_id := by apply Functor.Fiber.hom_ext; exact i'.inv_hom_id }
      exact Quotient.sound ⟨j⟩
    exact hClassRep
  change classEquiv C (oldClasses.map (comp.map f)
    (classOf 𝓕 hp.cofibered a)) = _
  rw [hOldMap, hClassOf, hClassOf, hNewMap]
  exact hClassPush.symm

public theorem associatedSchlessingerConditionS2_changeOfFields
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) :
    let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
    let hq := changeOfFieldsProjection_isPredeformationCategory
      S 𝓕.p hp
    let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
        (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
      ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
    SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓖 hq.cofibered)) := by
  let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
  let hq := changeOfFieldsProjection_isPredeformationCategory
    S 𝓕.p hp
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
  change SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓖 hq.cofibered))
  let oldClasses := isomorphismClasses 𝓕 hp.cofibered
  let newClasses := isomorphismClasses 𝓖 hq.cofibered
  let comp := (comparisonFunctor S).functor
  have hChanged := schlessingerConditionS2_changeOfFields
    S (Functor.Elements.π oldClasses)
    (categoryOfElements_π_isCofibered oldClasses) hS2
  have hPulled := schlessingerS2_changePullbackElements S oldClasses hChanged
  let classEquiv (B : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :
      (comp ⋙ oldClasses).obj B ≃ newClasses.obj B :=
    associatedClassesChangeOfFieldsEquiv S 𝓕 hp B
  have hNat : ∀ {B C : ArtinianLocalAlgCat.{u, v, v} S.Λ S.l}
      (f : B ⟶ C) (x : (comp ⋙ oldClasses).obj B),
      classEquiv C ((comp ⋙ oldClasses).map f x) =
        newClasses.map f (classEquiv B x) := fun f x =>
    associatedClassesChangeOfFields_naturality S 𝓕 hp f x
  exact schlessingerS2_of_pointwiseEquiv S (comp ⋙ oldClasses) newClasses
    classEquiv hNat hPulled

/-- Transporting along an isomorphism of the source with a set-valued functor is a bijection
of values. -/
private def functorMapIsoEquiv
    {C : Type u} [Category.{v} C] (H : C ⥤ Type w)
    {A B : C} (i : A ≅ B) : H.obj A ≃ H.obj B where
  toFun := H.map i.hom
  invFun := H.map i.inv
  left_inv x := by
    calc
      H.map i.inv (H.map i.hom x) = (H.map i.hom ≫ H.map i.inv) x := rfl
      _ = H.map (i.hom ≫ i.inv) x := by rw [Functor.map_comp]
      _ = x := by simp
  right_inv x := by
    calc
      H.map i.hom (H.map i.inv x) = (H.map i.inv ≫ H.map i.hom) x := rfl
      _ = H.map (i.inv ≫ i.hom) x := by rw [Functor.map_comp]
      _ = x := by simp

private theorem squareZeroExtensionComparisonIso_hom_coordinates
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l)
    (x : (artinianSquareZeroExtensionFunctor S.Λ S.k).obj
      (FGModuleCat.of S.k V)) :
    ((comparisonFunctor S).pullbackEquiv
      ((artinianSquareZeroExtensionFunctor S.Λ S.l).obj V)
      ((squareZeroExtensionComparisonIso S V).hom.hom x)).val =
        ((algebraMap S.k S.l x.fst, x.snd), x.fst) := by
  let B := (artinianSquareZeroExtensionFunctor S.Λ S.l).obj V
  let Q := (comparisonFunctor S).pullbackEquiv B
  let R := squareZeroExtensionPullbackEquiv S V
  let x' : TrivSqZeroExt S.k V := x
  change (Q (Q.symm (R x'))).val = _
  rw [Q.apply_symm_apply]
  simpa [x'] using squareZeroExtensionPullbackEquiv_coordinates S V x'

private theorem squareZeroExtensionComparisonIso_naturality
    (S : ChangeOfFieldsSituation.{u, v, v})
    {V W : FGModuleCat S.l} (f : V ⟶ W) :
    (artinianSquareZeroExtensionFunctor S.Λ S.k).map
        (FGModuleCat.ofHom (f.hom.hom.restrictScalars S.k)) ≫
      (squareZeroExtensionComparisonIso S W).hom =
    (squareZeroExtensionComparisonIso S V).hom ≫
      (comparisonFunctor S).functor.map
        ((artinianSquareZeroExtensionFunctor S.Λ S.l).map f) := by
  apply ArtinianLocalAlgCat.hom_ext
  ext x
  let B := (artinianSquareZeroExtensionFunctor S.Λ S.l).obj W
  let Q := (comparisonFunctor S).pullbackEquiv B
  let fₖ : FGModuleCat.of S.k V ⟶ FGModuleCat.of S.k W :=
    FGModuleCat.ofHom (f.hom.hom.restrictScalars S.k)
  apply Q.injective
  apply Subtype.ext
  let xK : TrivSqZeroExt S.k V := x
  have hfstK : TrivSqZeroExt.fst
      (((artinianSquareZeroExtensionFunctor S.Λ S.k).map fₖ).hom x) = xK.fst := by
    change TrivSqZeroExt.fst
      (TrivSqZeroExt.map (f.hom.hom.restrictScalars S.k) xK) = xK.fst
    exact TrivSqZeroExt.fst_map _ _
  have hsndK : TrivSqZeroExt.snd
      (((artinianSquareZeroExtensionFunctor S.Λ S.k).map fₖ).hom x) =
        f.hom.hom xK.snd := by
    change TrivSqZeroExt.snd
      (TrivSqZeroExt.map (f.hom.hom.restrictScalars S.k) xK) = _
    exact TrivSqZeroExt.snd_map _ _
  change ((comparisonFunctor S).pullbackEquiv B
      ((squareZeroExtensionComparisonIso S W).hom.hom
        (((artinianSquareZeroExtensionFunctor S.Λ S.k).map fₖ).hom x))).val = _
  rw [squareZeroExtensionComparisonIso_hom_coordinates]
  rw [hfstK, hsndK]
  let VArt := (artinianSquareZeroExtensionFunctor S.Λ S.l).obj V
  let fL := (artinianSquareZeroExtensionFunctor S.Λ S.l).map f
  have hcoords : ((comparisonFunctor S).pullbackEquiv VArt
      ((squareZeroExtensionComparisonIso S V).hom.hom x)).val =
        ((algebraMap S.k S.l x.fst, x.snd), x.fst) :=
    squareZeroExtensionComparisonIso_hom_coordinates S V x
  change ((algebraMap S.k S.l xK.fst, f.hom.hom xK.snd), xK.fst) = _
  change ((algebraMap S.k S.l xK.fst, f.hom.hom xK.snd), xK.fst) =
    ((comparisonFunctor S).pullbackEquiv B
      (((comparisonFunctor S).functor.map fL).hom
        ((squareZeroExtensionComparisonIso S V).hom.hom x))).val
  apply Prod.ext
  · rw [(comparisonFunctor S).map_fst fL, hcoords]
    apply Prod.ext
    · change (algebraMap S.k S.l) xK.fst =
        (TrivSqZeroExt.map f.hom.hom
          (⟨algebraMap S.k S.l xK.fst, xK.snd⟩ : TrivSqZeroExt S.l V)).fst
      exact (TrivSqZeroExt.fst_map f.hom.hom
        (⟨algebraMap S.k S.l xK.fst, xK.snd⟩ : TrivSqZeroExt S.l V)).symm
    · change f.hom.hom xK.snd =
        (TrivSqZeroExt.map f.hom.hom
          (⟨algebraMap S.k S.l xK.fst, xK.snd⟩ : TrivSqZeroExt S.l V)).snd
      exact (TrivSqZeroExt.snd_map f.hom.hom
        (⟨algebraMap S.k S.l xK.fst, xK.snd⟩ : TrivSqZeroExt S.l V)).symm
  · rw [(comparisonFunctor S).map_snd fL, hcoords]

private noncomputable def associatedTangentChangeOfFieldsAt
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (V : FGModuleCat S.l) :
    let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
    let hq := changeOfFieldsProjection_isPredeformationCategory
      S 𝓕.p hp
    let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
        (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
      ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
    (isomorphismClasses 𝓕 hp.cofibered).obj
      ((artinianSquareZeroExtensionFunctor S.Λ S.k).obj
        (FGModuleCat.of S.k V)) ≃
    (isomorphismClasses 𝓖 hq.cofibered).obj
      ((artinianSquareZeroExtensionFunctor S.Λ S.l).obj V) := by
  let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
  let hq := changeOfFieldsProjection_isPredeformationCategory
    S 𝓕.p hp
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
  let oldClasses := isomorphismClasses 𝓕 hp.cofibered
  let A := (artinianSquareZeroExtensionFunctor S.Λ S.k).obj
    (FGModuleCat.of S.k V)
  let B := (artinianSquareZeroExtensionFunctor S.Λ S.l).obj V
  let E := squareZeroExtensionComparisonIso S V
  exact (functorMapIsoEquiv oldClasses E).trans
    (associatedClassesChangeOfFieldsEquiv S 𝓕 hp B)

private noncomputable def tangentTensorToChangedAt
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered)))
    (V : FGModuleCat S.l) :
    let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
    let hq := changeOfFieldsProjection_isPredeformationCategory
      S 𝓕.p hp
    let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
        (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
      ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses
        𝓕 hp.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 hp.cofibered)
    TensorProduct S.k (V : Type v) T ≃
      (isomorphismClasses 𝓖 hq.cofibered).obj
        ((artinianSquareZeroExtensionFunctor S.Λ S.l).obj V) := by
  let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
  let hq := changeOfFieldsProjection_isPredeformationCategory
    S 𝓕.p hp
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses
      𝓕 hp.cofibered))) := ⟨hS2⟩
  let T := artinianTangentSpace S.Λ S.k
    (isomorphismClasses 𝓕 hp.cofibered)
  let Vk : FGModuleCat S.k := FGModuleCat.of S.k V
  letI : AddCommGroup T := associatedTangentSpaceAddCommGroupUnlifted 𝓕
  letI : Module S.k T := associatedTangentSpaceModuleUnlifted 𝓕
  let oldL := associatedTangentSpaceModuleStructureUnlifted 𝓕 hp hS2
  let oldSet := tangentSpaceSetFunctor S.Λ S.k
    (artinianLocalOver S.Λ S.k)
    (squareZeroExtension_mem_artinianLocalOver S.Λ S.k)
    (artinianLocalOverToArtinian S.Λ S.k ⋙
      isomorphismClasses 𝓕 hp.cofibered)
  let hcarrier := congrArg (fun H => H.obj Vk) oldL.forget_comp
  let oldTensor := associatedTangentSpaceFunctor_iso_tensorLeftUnlifted
    𝓕 hp hS2 Vk
  exact (TensorProduct.comm S.k T Vk).symm.toEquiv.trans <|
    (oldTensor.toEquiv.trans (Equiv.cast hcarrier)).trans <|
      associatedTangentChangeOfFieldsAt S 𝓕 hp V

private def tangentTensorMap
    (S : ChangeOfFieldsSituation.{u, v, v})
    (T : ModuleCat.{y} S.k) {V W : FGModuleCat S.l} (f : V ⟶ W) :
    TensorProduct S.k (V : Type v) (T : Type y) →ₗ[S.l]
      TensorProduct S.k (W : Type v) (T : Type y) := {
  toFun := TensorProduct.map (f.hom.hom.restrictScalars S.k)
    (LinearMap.id : (T : Type y) →ₗ[S.k] (T : Type y))
  map_add' := by
    intro x y
    exact (TensorProduct.map (f.hom.hom.restrictScalars S.k)
      (LinearMap.id : (T : Type y) →ₗ[S.k] (T : Type y))).map_add x y
  map_smul' := by
    intro a x
    induction x using TensorProduct.inductionOn with
    | tmul v t => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp [hx, hy] }

private def tangentTensorFunctor
    (S : ChangeOfFieldsSituation.{u, v, v})
    (T : ModuleCat.{y} S.k) : FGModuleCat S.l ⥤ ModuleCat S.l where
  obj V := ModuleCat.of S.l (TensorProduct S.k (V : Type v) (T : Type y))
  map f := ModuleCat.ofHom (tangentTensorMap S T f)
  map_id V := by
    apply ModuleCat.hom_ext
    change tangentTensorMap S T (𝟙 V) = LinearMap.id
    apply LinearMap.ext
    intro x
    exact TensorProduct.inductionOn x
      (fun a t => by simp [tangentTensorMap])
      (fun x y _ _ => by simp [tangentTensorMap])
  map_comp f g := by
    apply ModuleCat.hom_ext
    change tangentTensorMap S T (f ≫ g) =
      (tangentTensorMap S T g).comp (tangentTensorMap S T f)
    apply LinearMap.ext
    intro x
    exact TensorProduct.inductionOn x
      (fun a t => by simp [tangentTensorMap])
      (fun x y hx hy => by
        rw [LinearMap.map_add, LinearMap.map_add, hx, hy])

private instance tangentTensorFunctor_additive
    (S : ChangeOfFieldsSituation.{u, v, v})
    (T : ModuleCat.{y} S.k) : (tangentTensorFunctor S T).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    change tangentTensorMap S T (f + g) =
      tangentTensorMap S T f + tangentTensorMap S T g
    apply LinearMap.ext
    intro x
    exact TensorProduct.inductionOn x
      (fun a t => by
        change (f.hom.hom a + g.hom.hom a) ⊗ₜ[S.k] t = _
        rw [TensorProduct.add_tmul]
        simp [tangentTensorMap])
      (fun x y hx hy => by
        rw [LinearMap.map_add, LinearMap.map_add, hx, hy])

private instance tangentTensorFunctor_linear
    (S : ChangeOfFieldsSituation.{u, v, v})
    (T : ModuleCat.{y} S.k) : (tangentTensorFunctor S T).Linear S.l := by
  rw [Functor.linear_iff]
  intro X a
  apply ModuleCat.hom_ext
  ext x
  simp only [ModuleCat.hom_smul, ModuleCat.hom_id]
  change tangentTensorMap S T (a • (𝟙 X)) x = a • x
  exact TensorProduct.inductionOn x
    (fun v t => by
      change (a • v) ⊗ₜ[S.k] t = a • (v ⊗ₜ[S.k] t)
      simp [TensorProduct.smul_tmul'])
    (fun x y hx hy => by
      calc
        tangentTensorMap S T (a • (𝟙 X)) (x + y) =
            tangentTensorMap S T (a • (𝟙 X)) x +
              tangentTensorMap S T (a • (𝟙 X)) y :=
          (tangentTensorMap S T (a • (𝟙 X))).map_add x y
        _ = a • x + a • y := by rw [hx, hy]; rfl
        _ = a • (x + y) := by simp only [smul_add]
      )

private def restrictedScalarsModule
    (S : ChangeOfFieldsSituation.{u, v, v}) (V : FGModuleCat S.l) :
    ModuleCat S.k := ModuleCat.of S.k V

private def tangentTensorPure
    (S : ChangeOfFieldsSituation.{u, v, v}) (T : ModuleCat.{y} S.k)
    (V : FGModuleCat S.l) (a : V) (t : T) : (tangentTensorFunctor S T).obj V :=
  a ⊗ₜ[S.k] t

private def squareZeroVectorMap
    (S : ChangeOfFieldsSituation.{u, v, v}) (V : FGModuleCat S.l) (a : V) :
    FGModuleCat.of S.k S.k ⟶ FGModuleCat.of S.k V :=
  FGModuleCat.ofHom (LinearMap.smulRight (LinearMap.id : S.k →ₗ[S.k] S.k) a)

private def tangentTensorUnitEquiv
    (S : ChangeOfFieldsSituation.{u, v, v}) (T : ModuleCat.{y} S.k) :
    TensorProduct S.k S.l (T : Type y) ≃ₗ[S.l]
      ((tangentTensorFunctor S T).obj (FGModuleCat.of S.l S.l) : Type (max v y)) := by
  let e : S.l ≃ₗ[S.k] (restrictedScalarsModule S (FGModuleCat.of S.l S.l) : Type v) := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a b => Algebra.smul_def a b }
  letI : Module S.l (restrictedScalarsModule S (FGModuleCat.of S.l S.l)) :=
    (inferInstance : Module S.l S.l)
  letI : IsScalarTower S.k S.l (restrictedScalarsModule S (FGModuleCat.of S.l S.l)) :=
    changeFieldsSquareZeroKLTower S (FGModuleCat.of S.l S.l)
  let E := TensorProduct.congr e (LinearEquiv.refl S.k (T : Type y))
  exact {
    E.toEquiv with
    map_add' := E.map_add
    map_smul' := by
      intro a x
      change E (a • x) = a • E x
      induction x using TensorProduct.inductionOn with
      | tmul b t =>
          simp only [E, TensorProduct.congr_tmul]
          rfl
      | add x y hx hy => simp only [smul_add, map_add, hx, hy] }

private theorem tangentTensorUnitEquiv_tmul
    (S : ChangeOfFieldsSituation.{u, v, v}) (T : ModuleCat.{y} S.k)
    (a : S.l) (t : T) :
    tangentTensorUnitEquiv S T (a ⊗ₜ[S.k] t) =
      tangentTensorPure S T (FGModuleCat.of S.l S.l) a t := by
  change TensorProduct.congr _ _ (a ⊗ₜ[S.k] t) = _
  rw [TensorProduct.congr_tmul]
  rfl

private def linearEquivOfNaturalEquiv
    {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [CategoryTheory.Linear R C]
    [HasBinaryBiproducts C]
    (F : C ⥤ ModuleCat.{y} R) (G : C ⥤ ModuleCat.{z} R)
    [F.Additive] [G.Additive] [F.Linear R] [G.Linear R]
    (e : ∀ X, (F.obj X : Type y) ≃ (G.obj X : Type z))
    (he : ∀ {X Y} (f : X ⟶ Y) (x : F.obj X),
      e Y ((F.map f).hom x) = (G.map f).hom (e X x))
    (X : C) : (F.obj X : Type y) ≃ₗ[R] (G.obj X : Type z) :=
  { e X with
    map_add' := by
      intro x y
      let i : X ⟶ X ⊞ X := biprod.inl
      let j : X ⟶ X ⊞ X := biprod.inr
      let p : X ⊞ X ⟶ X := biprod.fst
      let q : X ⊞ X ⟶ X := biprod.snd
      let t := (F.map i).hom x + (F.map j).hom y
      have hp : (F.map p).hom t = x := by
        dsimp [t]
        rw [map_add]
        change (F.map i ≫ F.map p).hom x + (F.map j ≫ F.map p).hom y = x
        rw [← F.map_comp, ← F.map_comp]
        simp [i, j, p]
      have hq : (F.map q).hom t = y := by
        dsimp [t]
        rw [map_add]
        change (F.map i ≫ F.map q).hom x + (F.map j ≫ F.map q).hom y = y
        rw [← F.map_comp, ← F.map_comp]
        simp [i, j, q]
      calc
        e X (x + y) = e X ((F.map (p + q)).hom t) := by
          rw [F.map_add, ModuleCat.hom_add, LinearMap.add_apply, hp, hq]
        _ = (G.map (p + q)).hom (e (X ⊞ X) t) := he _ _
        _ = (G.map p).hom (e (X ⊞ X) t) + (G.map q).hom (e (X ⊞ X) t) := by
          rw [G.map_add, ModuleCat.hom_add, LinearMap.add_apply]
        _ = e X x + e X y := by rw [← he p, ← he q, hp, hq]
    map_smul' := by
      intro r x
      simpa using he (r • 𝟙 X) x }

private theorem linearLift_cast_map
    {R : Type u} [CommRing R]
    {C : Type v} [Category.{w} C] [Preadditive C] [CategoryTheory.Linear R C]
    {H : C ⥤ Type y} (L : LinearFunctorLift R H)
    {X Y : C} (f : X ⟶ Y) (x : L.functor.obj X) :
    cast (congrArg (fun H => H.obj Y) L.forget_comp) ((L.functor.map f).hom x) =
      H.map f (cast (congrArg (fun H => H.obj X) L.forget_comp) x) :=
  cast_functor_map L.forget_comp f x

private def moduleCastEquiv {R : Type u} [Ring R] (M : ModuleCat.{v} R)
    {N : Type v} (h : (M : Type v) = N) :
    let d : Σ G : AddCommGroup N, @Module R N _ G.toAddCommMonoid :=
      h.rec ⟨inferInstance, inferInstance⟩
    letI := d.1
    letI := d.2
    (M : Type v) ≃ₗ[R] N := by
  subst N
  exact LinearEquiv.refl R M

private theorem moduleCastEquiv_apply {R : Type u} [Ring R] (M : ModuleCat.{v} R)
    {N : Type v} (h : (M : Type v) = N) (x : M) :
    moduleCastEquiv M h x = cast h x := by
  subst N
  rfl

private theorem associatedTangentChangeOfFieldsAt_naturality
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    {V W : FGModuleCat S.l} (f : V ⟶ W)
    (x : (isomorphismClasses 𝓕 hp.cofibered).obj
      ((artinianSquareZeroExtensionFunctor S.Λ S.k).obj
        (FGModuleCat.of S.k V))) :
    associatedTangentChangeOfFieldsAt S 𝓕 hp W
      ((isomorphismClasses 𝓕 hp.cofibered).map
        ((artinianSquareZeroExtensionFunctor S.Λ S.k).map
          (FGModuleCat.ofHom (f.hom.hom.restrictScalars S.k))) x) =
      (isomorphismClasses
        ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance,
          changeOfFieldsProjection S 𝓕.p⟩
        (changeOfFieldsProjection_isPredeformationCategory
          S 𝓕.p hp).cofibered).map
        ((artinianSquareZeroExtensionFunctor S.Λ S.l).map f)
        (associatedTangentChangeOfFieldsAt S 𝓕 hp V x) := by
  let H := isomorphismClasses 𝓕 hp.cofibered
  let K := artinianSquareZeroExtensionFunctor S.Λ S.k
  let L := artinianSquareZeroExtensionFunctor S.Λ S.l
  let fk := FGModuleCat.ofHom (f.hom.hom.restrictScalars S.k)
  change associatedClassesChangeOfFieldsEquiv S 𝓕 hp (L.obj W)
    (H.map (squareZeroExtensionComparisonIso S W).hom (H.map (K.map fk) x)) = _
  have h := congrArg (fun g => H.map g x)
    (squareZeroExtensionComparisonIso_naturality S f)
  simp only [Functor.map_comp, types_comp_apply] at h
  rw [h]
  exact associatedClassesChangeOfFields_naturality S 𝓕 hp (L.map f)
    (H.map (squareZeroExtensionComparisonIso S V).hom x)

private theorem tangentTensorToChangedAt_naturality
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 hp.cofibered)
    ∀ {V W : FGModuleCat S.l} (f : V ⟶ W) (x : TensorProduct S.k (V : Type v) T),
    tangentTensorToChangedAt S 𝓕 hp hS2 W
      (TensorProduct.map (f.hom.hom.restrictScalars S.k) (LinearMap.id : T →ₗ[S.k] T) x) =
      (isomorphismClasses
        ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance,
          changeOfFieldsProjection S 𝓕.p⟩
        (changeOfFieldsProjection_isPredeformationCategory
          S 𝓕.p hp).cofibered).map
        ((artinianSquareZeroExtensionFunctor S.Λ S.l).map f)
        (tangentTensorToChangedAt S 𝓕 hp hS2 V x) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
  let T := artinianTangentSpace S.Λ S.k
    (isomorphismClasses 𝓕 hp.cofibered)
  dsimp only
  intro V W f x
  let L := associatedTangentSpaceModuleStructureUnlifted 𝓕 hp hS2
  let Vk := FGModuleCat.of S.k V
  let Wk := FGModuleCat.of S.k W
  let fk : Vk ⟶ Wk := FGModuleCat.ofHom (f.hom.hom.restrictScalars S.k)
  let e := associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓕 hp hS2
  have hc : (TensorProduct.comm S.k T Wk).symm
      (TensorProduct.map (f.hom.hom.restrictScalars S.k) (LinearMap.id : T →ₗ[S.k] T) x) =
      TensorProduct.map (LinearMap.id : T →ₗ[S.k] T) fk.hom.hom
        ((TensorProduct.comm S.k T Vk).symm x) := by
    induction x using TensorProduct.inductionOn with
    | tmul a t => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  change associatedTangentChangeOfFieldsAt S 𝓕 hp W
    (cast (congrArg (fun H => H.obj Wk) L.forget_comp)
      (e Wk ((TensorProduct.comm S.k T Wk).symm _))) = _
  rw [hc, ← associatedTangentSpaceFunctor_iso_tensorLeft_naturalityUnlifted
    𝓕 hp hS2 Vk Wk fk]
  rw [linearLift_cast_map L fk]
  exact associatedTangentChangeOfFieldsAt_naturality S 𝓕 hp f _

private theorem tangentTensorToChangedAt_tmul
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) :
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
    let T := artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 hp.cofibered)
    ∀ (V : FGModuleCat S.l) (a : V) (t : T),
      tangentTensorToChangedAt S 𝓕 hp hS2 V (a ⊗ₜ[S.k] t) =
        associatedTangentChangeOfFieldsAt S 𝓕 hp V
          ((isomorphismClasses 𝓕 hp.cofibered).map
            ((artinianSquareZeroExtensionFunctor S.Λ S.k).map
              (squareZeroVectorMap S V a)) t) := by
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
  dsimp only
  intro V a t
  let L := associatedTangentSpaceModuleStructureUnlifted 𝓕 hp hS2
  let Vk := FGModuleCat.of S.k V
  change associatedTangentChangeOfFieldsAt S 𝓕 hp V
    (cast (congrArg (fun H => H.obj Vk) L.forget_comp)
      (associatedTangentSpaceFunctor_iso_tensorLeftUnlifted 𝓕 hp hS2 Vk
        (t ⊗ₜ[S.k] a))) = _
  rw [associatedTangentSpaceFunctor_iso_tensorLeft_pureUnlifted]
  rw [linearLift_cast_map L]
  simp only [cast_cast]
  rfl

@[stacks 07WB]
public noncomputable def tangentSpaceChangeOfFields
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) :
    let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
    let hq := changeOfFieldsProjection_isPredeformationCategory
      S 𝓕.p hp
    let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
        (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
      ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses
        𝓕 hp.cofibered))) := ⟨hS2⟩
    letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨hq⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses
        𝓖 hq.cofibered))) :=
      ⟨associatedSchlessingerConditionS2_changeOfFields S 𝓕 hp hS2⟩
    letI : AddCommGroup (artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 hp.cofibered)) :=
      associatedTangentSpaceAddCommGroupUnlifted 𝓕
    letI : Module S.k (artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 hp.cofibered)) :=
      associatedTangentSpaceModuleUnlifted 𝓕
    letI : AddCommGroup (artinianTangentSpace S.Λ S.l
      (isomorphismClasses 𝓖 hq.cofibered)) :=
      associatedTangentSpaceAddCommGroupUnlifted 𝓖
    letI : Module S.l (artinianTangentSpace S.Λ S.l
      (isomorphismClasses 𝓖 hq.cofibered)) :=
      associatedTangentSpaceModuleUnlifted 𝓖
    TensorProduct S.k S.l
      (artinianTangentSpace S.Λ S.k
        (isomorphismClasses 𝓕 hp.cofibered)) ≃ₗ[S.l]
      artinianTangentSpace S.Λ S.l
        (isomorphismClasses 𝓖 hq.cofibered) := private_decl% (by
  let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
  let hq := changeOfFieldsProjection_isPredeformationCategory
    S 𝓕.p hp
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
  letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
  letI : Fact (IsPredeformationCategory 𝓖.p) := ⟨hq⟩
  let hS2' := associatedSchlessingerConditionS2_changeOfFields S 𝓕 hp hS2
  letI : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓖 hq.cofibered))) := ⟨hS2'⟩
  let T := artinianTangentSpace S.Λ S.k
    (isomorphismClasses 𝓕 hp.cofibered)
  let F := tangentTensorFunctor S (ModuleCat.of S.k T)
  let L := associatedTangentSpaceModuleStructureUnlifted 𝓖 hq hS2'
  let e (V : FGModuleCat S.l) : (F.obj V : Type (max v y)) ≃
      (L.functor.obj V : Type (max (max u (v + 1)) y)) :=
    (tangentTensorToChangedAt S 𝓕 hp hS2 V).trans
      (Equiv.cast (congrArg (fun H => H.obj V) L.forget_comp)).symm
  -- Elaborate this proof as a term so the private naturality lemmas remain visible.
  have he {V W : FGModuleCat S.l} (f : V ⟶ W) (x : F.obj V) :
      e W ((F.map f).hom x) = (L.functor.map f).hom (e V x) := (by
    apply (Equiv.cast (congrArg (fun H => H.obj W) L.forget_comp)).injective
    change cast _ (cast _ (tangentTensorToChangedAt S 𝓕 hp hS2 W _)) = _
    simp only [cast_cast, cast_eq]
    change _ = cast (congrArg (fun H => H.obj W) L.forget_comp)
      ((L.functor.map f).hom (e V x))
    rw [linearLift_cast_map L f]
    have hx : cast (congrArg (fun H => H.obj V) L.forget_comp) (e V x) =
        tangentTensorToChangedAt S 𝓕 hp hS2 V x := by
      change cast _ (cast _ _) = _
      simp only [cast_cast, cast_eq]
    rw [hx]
    exact tangentTensorToChangedAt_naturality S 𝓕 hp hS2 f x)
  exact (tangentTensorUnitEquiv S (ModuleCat.of S.k T)).trans <|
    (linearEquivOfNaturalEquiv F L.functor e he (FGModuleCat.of S.l S.l)).trans
    (moduleCastEquiv (L.functor.obj (FGModuleCat.of S.l S.l))
      (associatedTangentSpaceModuleStructure_carrierUnlifted 𝓖 hq hS2')))

/-- The canonical map from `k[ε]` to the restricted-residue-field algebra
`k[lε]`. Its first pullback coordinate extends both coefficients to `l`,
while its second coordinate is the original residue in `k`. -/
public noncomputable def canonicalDualNumberInclusion
    (S : ChangeOfFieldsSituation.{u, v, v}) :
    let A := (artinianSquareZeroExtensionFunctor S.Λ S.k).obj
      (FGModuleCat.of S.k S.k)
    let B := (artinianSquareZeroExtensionFunctor S.Λ S.l).obj
      (FGModuleCat.of S.l S.l)
    let C := (comparisonFunctor S).functor.obj B
    {j : A ⟶ C // ∀ a : A,
      ((((comparisonFunctor S).pullbackEquiv B) (j.hom a)).val.1).fst =
        algebraMap S.k S.l a.fst ∧
      ((((comparisonFunctor S).pullbackEquiv B) (j.hom a)).val.1).snd =
        algebraMap S.k S.l a.snd ∧
      (((comparisonFunctor S).pullbackEquiv B) (j.hom a)).val.2 = a.fst} :=
    private_decl% (by
  let A := kDualNumbers S
  let B := lDualNumbers S
  let C := (comparisonFunctor S).functor.obj B
  let e := dualNumberExtensionComparisonEquiv S
  let m := dualNumberModuleInclusion S
  let ek := kDualNumbersCarrierRingEquiv S
  let mA := m.comp ek.symm.toRingHom
  let el := lDualNumbersCarrierRingEquiv S
  let f : A →ₐ[S.Λ] C :=
    { toRingHom := e.toRingHom.comp mA
      commutes' := by
        intro r
        apply (comparisonFunctor S).pullbackEquiv B |>.injective
        apply Subtype.ext
        have hA := kDualNumbers_algebraMap_coordinates S r
        have hB := lDualNumbers_algebraMap_coordinates S r
        have hA' : ek.symm (algebraMap S.Λ A r) =
            TrivSqZeroExt.inl (algebraMap S.Λ S.k r) := by
          rw [hA]
          rfl
        have hB' : algebraMap S.Λ B r = el (algebraMap S.Λ S.l r, 0) := by
          calc
            algebraMap S.Λ B r = el (el.symm (algebraMap S.Λ B r)) :=
              (el.apply_symm_apply _).symm
            _ = el (algebraMap S.Λ S.l r, 0) := congrArg el hB
        have hmapfst :
            TrivSqZeroExt.fst (m (ek.symm (algebraMap S.Λ A r))) =
              algebraMap S.Λ S.k r := by
          rw [hA']
          exact TrivSqZeroExt.fst_map (Algebra.linearMap S.k S.l)
            (TrivSqZeroExt.inl (algebraMap S.Λ S.k r))
        have hmapsnd :
            TrivSqZeroExt.snd (m (ek.symm (algebraMap S.Λ A r))) = 0 := by
          rw [hA']
          simp [m, dualNumberModuleInclusion]
        have hBfst : TrivSqZeroExt.fst (algebraMap S.Λ B r) =
            algebraMap S.Λ S.l r := by rw [hB']; rfl
        have hBsnd : TrivSqZeroExt.snd (algebraMap S.Λ B r) = 0 := by
          rw [hB']; rfl
        apply Prod.ext
        · apply Prod.ext
          · rw [(comparisonFunctor S).algebraMap_fst B r]
            change (((comparisonFunctor S).pullbackEquiv B
              (dualNumberExtensionComparisonEquiv S
                (m (ek.symm (algebraMap S.Λ A r))))).val.1).1 = _
            rw [dualNumberExtensionComparisonEquiv_coordinates, hA, hB']
            change algebraMap S.k S.l
                (TrivSqZeroExt.fst (m (ek.symm (algebraMap S.Λ A r)))) =
              TrivSqZeroExt.fst (algebraMap S.Λ B r)
            rw [hmapfst, hBfst]
            exact (IsScalarTower.algebraMap_apply S.Λ S.k S.l r).symm
          · rw [(comparisonFunctor S).algebraMap_fst B r]
            change (((comparisonFunctor S).pullbackEquiv B
              (dualNumberExtensionComparisonEquiv S
                (m (ek.symm (algebraMap S.Λ A r))))).val.1).2 = _
            rw [dualNumberExtensionComparisonEquiv_coordinates, hA, hB']
            change TrivSqZeroExt.snd (m (ek.symm (algebraMap S.Λ A r))) =
              TrivSqZeroExt.snd (algebraMap S.Λ B r)
            rw [hmapsnd, hBsnd]
        · rw [(comparisonFunctor S).algebraMap_snd B r]
          change (((comparisonFunctor S).pullbackEquiv B
            (dualNumberExtensionComparisonEquiv S
              (m (ek.symm (algebraMap S.Λ A r))))).val).2 = _
          rw [dualNumberExtensionComparisonEquiv_coordinates, hA]
          change TrivSqZeroExt.fst (m (ek.symm (algebraMap S.Λ A r))) =
            algebraMap S.Λ S.k r
          exact hmapfst
      }
  let j : A ⟶ C :=
    { hom := f
      isLocal := by
        refine ⟨fun a ha => ?_⟩
        have hu : IsUnit (e.symm (f a)) := ha.map e.symm.toMonoidHom
        have hu' : IsUnit (m (ek.symm a)) := by simpa [f, mA] using hu
        have hfstL : IsUnit (TrivSqZeroExt.fst (m (ek.symm a))) :=
          (TrivSqZeroExt.isUnit_iff_isUnit_fst).mp hu'
        have hfst : IsUnit (TrivSqZeroExt.fst (ek.symm a)) := by
          simpa [m, dualNumberModuleInclusion] using hfstL
        have hne : TrivSqZeroExt.fst (ek.symm a) ≠ 0 := by
          intro hz
          apply (isUnit_iff_ne_zero.mp hfst)
          simp [hz]
        have hunit : IsUnit (ek.symm a) :=
          (TrivSqZeroExt.isUnit_iff_isUnit_fst).mpr
            (isUnit_iff_ne_zero.mpr hne)
        exact hunit.map ek.toMonoidHom
      residue_comm := by
        intro a
        rw [(comparisonFunctor S).residue_snd]
        have hcoords :
            ((comparisonFunctor S).pullbackEquiv B (f a)).val =
              ((algebraMap S.k S.l a.fst, algebraMap S.k S.l a.snd), a.fst) := by
          have hfst : TrivSqZeroExt.fst (ek.symm a) = TrivSqZeroExt.fst a := rfl
          have hsnd : TrivSqZeroExt.snd (ek.symm a) = TrivSqZeroExt.snd a := rfl
          calc
            _ = ((algebraMap S.k S.l (TrivSqZeroExt.fst (ek.symm a)),
                TrivSqZeroExt.snd (m (ek.symm a))),
                TrivSqZeroExt.fst (m (ek.symm a))) := by
              change ((comparisonFunctor S).pullbackEquiv B
                (dualNumberExtensionComparisonEquiv S (m (ek.symm a)))).val = _
              rw [dualNumberExtensionComparisonEquiv_coordinates]
              simp [m, dualNumberModuleInclusion]
              rfl
            _ = ((algebraMap S.k S.l a.fst, algebraMap S.k S.l a.snd), a.fst) := by
              have hmsnd : (m (ek.symm a)).snd =
                  Algebra.linearMap S.k S.l ((ek.symm a).snd) := by
                change TrivSqZeroExt.snd
                  ((TrivSqZeroExt.map (Algebra.linearMap S.k S.l)) (ek.symm a)) = _
                exact TrivSqZeroExt.snd_map _ _
              have hmst : (m (ek.symm a)).fst = (ek.symm a).fst := by
                change TrivSqZeroExt.fst
                  ((TrivSqZeroExt.map (Algebra.linearMap S.k S.l)) (ek.symm a)) = _
                exact TrivSqZeroExt.fst_map _ _
              rw [hmst, hfst, hmsnd, hsnd]
              rfl
        rw [hcoords]
        exact (kDualNumbers_residue_fst S a).symm }
  refine ⟨j, ?_⟩
  intro a
  have hcoords :
      ((comparisonFunctor S).pullbackEquiv B (j.hom a)).val =
        ((algebraMap S.k S.l a.fst, algebraMap S.k S.l a.snd), a.fst) := by
    have hfst : TrivSqZeroExt.fst (ek.symm a) = TrivSqZeroExt.fst a := rfl
    have hsnd : TrivSqZeroExt.snd (ek.symm a) = TrivSqZeroExt.snd a := rfl
    calc
      _ = ((algebraMap S.k S.l (TrivSqZeroExt.fst (ek.symm a)),
          TrivSqZeroExt.snd (m (ek.symm a))),
          TrivSqZeroExt.fst (m (ek.symm a))) := by
        change ((comparisonFunctor S).pullbackEquiv B
          (dualNumberExtensionComparisonEquiv S (m (ek.symm a)))).val = _
        rw [dualNumberExtensionComparisonEquiv_coordinates]
        simp [m, dualNumberModuleInclusion]
        rfl
      _ = ((algebraMap S.k S.l a.fst, algebraMap S.k S.l a.snd), a.fst) := by
        have hmsnd : (m (ek.symm a)).snd =
            Algebra.linearMap S.k S.l ((ek.symm a).snd) := by
          change TrivSqZeroExt.snd
            ((TrivSqZeroExt.map (Algebra.linearMap S.k S.l)) (ek.symm a)) = _
          exact TrivSqZeroExt.snd_map _ _
        have hmst : (m (ek.symm a)).fst = (ek.symm a).fst := by
          change TrivSqZeroExt.fst
            ((TrivSqZeroExt.map (Algebra.linearMap S.k S.l)) (ek.symm a)) = _
          exact TrivSqZeroExt.fst_map _ _
        rw [hmst, hfst, hmsnd, hsnd]
        rfl
  exact ⟨congrArg TrivSqZeroExt.fst (congrArg Prod.fst hcoords),
    congrArg TrivSqZeroExt.snd (congrArg Prod.fst hcoords),
    congrArg Prod.snd hcoords⟩)

private theorem squareZeroVectorMap_coordinates
    (S : ChangeOfFieldsSituation.{u, v, v})
    (V : FGModuleCat S.l) (b : V)
    (a : (artinianSquareZeroExtensionFunctor S.Λ S.k).obj (FGModuleCat.of S.k S.k)) :
    (((artinianSquareZeroExtensionFunctor S.Λ S.k).map
      (squareZeroVectorMap S V b)).hom a).fst = a.fst ∧
    (((artinianSquareZeroExtensionFunctor S.Λ S.k).map
      (squareZeroVectorMap S V b)).hom a).snd =
      (TrivSqZeroExt.snd (R := S.k) (M := S.k) a) • b := by
  constructor
  · change (TrivSqZeroExt.map
      (LinearMap.smulRight (LinearMap.id : S.k →ₗ[S.k] S.k) b) a).fst = a.fst
    exact TrivSqZeroExt.fst_map _ _
  · change (TrivSqZeroExt.map
      (LinearMap.smulRight (LinearMap.id : S.k →ₗ[S.k] S.k) b) a).snd = _
    exact TrivSqZeroExt.snd_map _ _

private theorem canonicalDualNumberInclusion_eq
    (S : ChangeOfFieldsSituation.{u, v, v}) :
    (canonicalDualNumberInclusion S).val =
      (artinianSquareZeroExtensionFunctor S.Λ S.k).map
        (squareZeroVectorMap S (FGModuleCat.of S.l S.l) 1) ≫
        (squareZeroExtensionComparisonIso S (FGModuleCat.of S.l S.l)).hom := by
  apply ArtinianLocalAlgCat.hom_ext
  ext a
  apply ((comparisonFunctor S).pullbackEquiv (lDualNumbers S)).injective
  apply Subtype.ext
  have ha := (canonicalDualNumberInclusion S).property a
  change _ = ((comparisonFunctor S).pullbackEquiv (lDualNumbers S)
    ((squareZeroExtensionComparisonIso S (FGModuleCat.of S.l S.l)).hom.hom
      (((artinianSquareZeroExtensionFunctor S.Λ S.k).map
        (squareZeroVectorMap S (FGModuleCat.of S.l S.l) 1)).hom a))).val
  rw [squareZeroExtensionComparisonIso_hom_coordinates]
  rw [(squareZeroVectorMap_coordinates S (FGModuleCat.of S.l S.l) 1 a).1,
    (squareZeroVectorMap_coordinates S (FGModuleCat.of S.l S.l) 1 a).2]
  apply Prod.ext
  · apply Prod.ext
    · exact ha.1
    · change _ = algebraMap S.k S.l a.snd * 1
      rw [mul_one]
      exact ha.2.1
  · exact ha.2.2

/-- The scalar-extension equivalence sends a tangent vector tensored with `1`
to its image under the canonical map on square-zero extensions and the
change-of-field identification of fibrewise isomorphism classes. -/
@[stacks 07WB "canonical pure-tensor formula"]
public theorem tangentSpaceChangeOfFields_tmul_one
    (S : ChangeOfFieldsSituation.{u, v, v})
    (𝓕 : BasedCategory.{z, y} (ArtinianLocalAlgCat.{u, v, v} S.Λ S.k))
    (hp : IsPredeformationCategory 𝓕.p)
    (hS2 : SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) :
    let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
    let hq := changeOfFieldsProjection_isPredeformationCategory
      S 𝓕.p hp
    let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
        (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
      ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
    let A := (artinianSquareZeroExtensionFunctor S.Λ S.k).obj
      (FGModuleCat.of S.k S.k)
    let B := (artinianSquareZeroExtensionFunctor S.Λ S.l).obj
      (FGModuleCat.of S.l S.l)
    let C := (comparisonFunctor S).functor.obj B
    let j : A ⟶ C := (canonicalDualNumberInclusion S).val
    letI : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
    letI : Fact (SchlessingerConditionS2
      (Functor.Elements.π (isomorphismClasses
        𝓕 hp.cofibered))) := ⟨hS2⟩
    letI : AddCommGroup (artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 hp.cofibered)) :=
      associatedTangentSpaceAddCommGroupUnlifted 𝓕
    letI : Module S.k (artinianTangentSpace S.Λ S.k
      (isomorphismClasses 𝓕 hp.cofibered)) :=
      associatedTangentSpaceModuleUnlifted 𝓕
    ∀ (t : artinianTangentSpace S.Λ S.k
        (isomorphismClasses 𝓕 hp.cofibered)),
      (tangentSpaceChangeOfFields S 𝓕 hp hS2) (1 ⊗ₜ[S.k] t) =
        cast (isomorphismClasses_obj 𝓖 hq.cofibered B).symm
          (changeOfFieldsIsoClassMap S 𝓕.p B
            (cast (isomorphismClasses_obj 𝓕 hp.cofibered C)
              ((isomorphismClasses 𝓕 hp.cofibered).map j t)))  := by
  let q := changeOfFieldsProjection.{u, v, v, v, y, z} S 𝓕.p
  let hq := changeOfFieldsProjection_isPredeformationCategory
    S 𝓕.p hp
  let 𝓖 : BasedCategory.{max v z, max (max u (v + 1)) y}
      (ArtinianLocalAlgCat.{u, v, v} S.Λ S.l) :=
    ⟨ChangeOfFieldsCategory S 𝓕.p, inferInstance, q⟩
  let : Fact (IsPredeformationCategory 𝓕.p) := ⟨hp⟩
  let : Fact (SchlessingerConditionS2
    (Functor.Elements.π (isomorphismClasses 𝓕 hp.cofibered))) := ⟨hS2⟩
  dsimp only
  intro t
  have he : tangentSpaceChangeOfFields S 𝓕 hp hS2 (1 ⊗ₜ[S.k] t) =
      tangentTensorToChangedAt S 𝓕 hp hS2 (FGModuleCat.of S.l S.l)
        (tangentTensorPure S (ModuleCat.of S.k _) (FGModuleCat.of S.l S.l) 1 t) := by
    unfold tangentSpaceChangeOfFields
    change moduleCastEquiv _ _ _ = _
    rw [moduleCastEquiv_apply]
    change cast _ (cast _
      (tangentTensorToChangedAt S 𝓕 hp hS2 (FGModuleCat.of S.l S.l)
        (tangentTensorUnitEquiv S (ModuleCat.of S.k _)
          (1 ⊗ₜ[S.k] t)))) = _
    rw [tangentTensorUnitEquiv_tmul]
    simp only [cast_cast]
    rfl
  rw [he]
  refine (tangentTensorToChangedAt_tmul S 𝓕 hp hS2 (FGModuleCat.of S.l S.l) 1 t).trans ?_
  let H := isomorphismClasses 𝓕 hp.cofibered
  change associatedClassesChangeOfFieldsEquiv S 𝓕 hp (lDualNumbers S)
    (H.map (squareZeroExtensionComparisonIso S (FGModuleCat.of S.l S.l)).hom
      (H.map ((artinianSquareZeroExtensionFunctor S.Λ S.k).map
        (squareZeroVectorMap S (FGModuleCat.of S.l S.l) 1)) t)) =
      associatedClassesChangeOfFieldsEquiv S 𝓕 hp (lDualNumbers S)
        (H.map (canonicalDualNumberInclusion S).val t)
  simp only [canonicalDualNumberInclusion_eq, Functor.map_comp]
  rfl

end Deformation
