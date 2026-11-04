module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.OppositeOfCommSemiring
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.BaseCategory.IdealQuotient
public import StacksFrontier.Deformation.Schlessinger.Basic
public import StacksFrontier.Deformation.SchlessingerConditions.CofiberedLifts

/-!
# Schlessinger's condition (S2) for finite-dimensional square-zero extensions

Condition (S2) is stated for the dual-number projection `k[ε] → k`. For a category cofibered
in groupoids over `𝒞_Λ` it holds just as well for the projection `k[V] → k` of the trivial
square-zero extension by any finite-dimensional `k`-vector space `V` (Stacks 06HZ): both the
existence of a completion and the comparison of two completions.

The proof is an induction on `dim_k V`. In dimension `0` the projection is an isomorphism, so
the completion is produced by transporting along the pushforward of the inverse. In dimension
`1` the projection is the dual-number projection and (S2) applies verbatim. Above that, a
choice of splitting `V ≅ k × W` factors the projection as `k[V] → k[W] → k` and as
`k[V] → k[ε] → k`, and exhibits `k[V]` as the fibre product `k[W] ×_k k[ε]`. Base-changing the
prescribed square along `k[V] → k[W]` gives a square over `k[W] → k` to which the inductive
hypothesis applies, and the remaining corner is a square over the dual-number projection to
which (S2) applies. The comparison clause descends the two completions along the same
factorization and compares them in dimension one.

## Main definitions

* `Deformation.IsSquareZeroProjection`: the assertion that a morphism of `𝒞_Λ` is the
  projection `k[V] → k`, up to compatible `Λ`-algebra coordinates on source and target.

## Main results

* `Deformation.schlessingerConditionS2_completion_squareZero`: the existence clause of (S2)
  for `k[V] → k`.
* `Deformation.schlessingerConditionS2_comparison_squareZero`: the comparison clause of (S2)
  for `k[V] → k`.

## Implementation notes

The two clauses of (S2) are stated separately, since the source uses them separately. As in
condition (S2) itself, a comparison morphism is required to respect the arrow to the first
object only; the source does not require it to respect the arrow to `k[V]`.

The square-zero projection is specified up to coordinates rather than by choosing an object of
`𝒞_Λ` called `k[V]`: the category has no distinguished such object, and all the arguments use
only the existence of coordinates. The `Λ`-module structure on `V` used to form `k[V]` as a
`Λ`-algebra is the one restricted along `Λ → k`, supplied inside `IsSquareZeroProjection`.
Because a vector space over a field has a unique compatible right action, the opposite-module
and central-scalar instances needed to form `k[V]` are supplied once as local instances; the
two declarations preceding them take those data explicitly, since they are used with the
standard instances on `DualNumber k`.

The truncation `k[k × W] → k[W]` is built as a quotient of the source by the kernel of the
coordinate map, using the ideal-quotient construction of
`StacksFrontier.Deformation.BaseCategory.IdealQuotient`; this avoids choosing an object for
`k[W]` and makes the truncation a morphism of `𝒞_Λ` by construction.

## References

* [Stacks Project, Tag 06HZ](https://stacks.math.columbia.edu/tag/06HZ)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory IsLocalRing
universe u v w u₁ v₁ u₂ v₂ z z₁

/-- A linear equivalence of vector spaces induces an isomorphism of their trivial square-zero
extensions. -/
private noncomputable def trivSqZeroExtAlgEquivOfLinearEquiv
    {k : Type w} [Field k] {V : Type z} {W : Type z₁}
    [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    [AddCommGroup W] [Module k W] [Module kᵐᵒᵖ W] [IsCentralScalar k W]
    (e : V ≃ₗ[k] W) : TrivSqZeroExt k V ≃ₐ[k] TrivSqZeroExt k W := by
  apply AlgEquiv.ofBijective (TrivSqZeroExt.map e.toLinearMap)
  constructor
  · intro x y h
    apply TrivSqZeroExt.ext
    · have hfst := congrArg TrivSqZeroExt.fst h
      simpa only [TrivSqZeroExt.fst_map] using hfst
    · have hsnd := congrArg TrivSqZeroExt.snd h
      have hcoord : e.toLinearMap x.snd = e.toLinearMap y.snd := by
        simpa only [TrivSqZeroExt.snd_map] using hsnd
      exact e.injective hcoord
  · intro x
    obtain ⟨vv, hv⟩ := e.surjective x.snd
    let a : TrivSqZeroExt k V := (x.fst, vv)
    refine ⟨a, ?_⟩
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_map]
      rfl
    · change (TrivSqZeroExt.map e.toLinearMap a).snd = x.snd
      rw [TrivSqZeroExt.snd_map]
      exact hv

/-- Coordinates identifying a morphism with `k[V] → k`, together with a linear equivalence
`V ≃ W`, give coordinates identifying it with `k[W] → k`. -/
private theorem exists_algEquiv_comp_fstHom_of_linearEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} {W : Type z₁}
    [AddCommGroup V] [Module k V] [Module kᵐᵒᵖ V] [IsCentralScalar k V]
    [Module Λ V] [IsScalarTower Λ k V]
    [AddCommGroup W] [Module k W] [Module kᵐᵒᵖ W] [IsCentralScalar k W]
    [Module Λ W] [IsScalarTower Λ k W]
    {AV A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : AV ⟶ A₀)
    (i₀ : A₀ ≃ₐ[Λ] k) (iV : AV ≃ₐ[Λ] TrivSqZeroExt k V)
    (hi : i₀.toAlgHom.comp e.hom = (TrivSqZeroExt.fstHom Λ k V).comp iV.toAlgHom)
    (b : V ≃ₗ[k] W) :
    ∃ iW : AV ≃ₐ[Λ] TrivSqZeroExt k W,
      i₀.toAlgHom.comp e.hom = (TrivSqZeroExt.fstHom Λ k W).comp iW.toAlgHom := by
  let j := (trivSqZeroExtAlgEquivOfLinearEquiv b).restrictScalars Λ
  have hj : (TrivSqZeroExt.fstHom Λ k W).comp j.toAlgHom = TrivSqZeroExt.fstHom Λ k V := by
    ext x
    · change (TrivSqZeroExt.map b.toLinearMap (TrivSqZeroExt.inl x)).fst = x
      rw [TrivSqZeroExt.fst_map]
      rfl
    · change (TrivSqZeroExt.map b.toLinearMap (TrivSqZeroExt.inr x)).fst = 0
      rw [TrivSqZeroExt.fst_map]
      rfl
  exact ⟨iV.trans j, by rw [hi, ← hj]; rfl⟩

/-- Coordinates identifying a morphism with `k[V] → k`, together with a linear identification
of `V` with `k`, exhibit it as the dual-number projection. -/
private theorem isDualNumberProjection_of_coordinates
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V]
    [Module kᵐᵒᵖ V] [IsCentralScalar k V] [Module Λ V] [IsScalarTower Λ k V]
    {AV A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : AV ⟶ A₀)
    (i₀ : A₀ ≃ₐ[Λ] k) (iV : AV ≃ₐ[Λ] TrivSqZeroExt k V)
    (hi : i₀.toAlgHom.comp e.hom = (TrivSqZeroExt.fstHom Λ k V).comp iV.toAlgHom)
    (b : V ≃ₗ[k] k) :
    IsDualNumberProjection e :=
  (exists_algEquiv_comp_fstHom_of_linearEquiv e i₀ iV hi b).elim fun iW h => ⟨i₀, iW, h⟩

/-- The opposite-module structure on a vector space over a field, by commutativity. -/
local instance moduleMulOppositeOfSquareZeroVectorSpace
    (k : Type w) [Field k] (V : Type z) [AddCommGroup V]
    [Module k V] : Module kᵐᵒᵖ V :=
  Module.oppositeOfCommSemiring k V

/-- Left and right scalar multiplication on a vector space over a field agree. -/
local instance isCentralScalarOfSquareZeroVectorSpace
    (k : Type w) [Field k] (V : Type z) [AddCommGroup V]
    [Module k V] : IsCentralScalar k V :=
  Module.isCentralScalar_oppositeOfCommSemiring k V

/-- `k[V × W]` is the fibre product of `k[V] → k` and `k[W] → k`. -/
private noncomputable def trivSqZeroExtProductAlgEquiv
    {k : Type w} [Field k] {V : Type z} {W : Type z₁}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] :
    TrivSqZeroExt k (V × W) ≃ₐ[k]
      AlgHom.pullback (TrivSqZeroExt.fstHom k k V) (TrivSqZeroExt.fstHom k k W) := by
  let f := TrivSqZeroExt.map (LinearMap.fst k V W)
  let g := TrivSqZeroExt.map (LinearMap.snd k V W)
  let fg := AlgHom.prod f g
  have hfg (x : TrivSqZeroExt k (V × W)) :
      fg x ∈ AlgHom.pullback (TrivSqZeroExt.fstHom k k V)
        (TrivSqZeroExt.fstHom k k W) := by
    change (f x).fst = (g x).fst
    simp [f, g, TrivSqZeroExt.fst_map]
  let m := AlgHom.codRestrict fg _ hfg
  apply AlgEquiv.ofBijective m
  constructor
  · intro x y h
    have hval := congrArg Subtype.val h
    change fg x = fg y at hval
    change (f x, g x) = (f y, g y) at hval
    have hfst : x.fst = y.fst := by
      simpa only [f, TrivSqZeroExt.fst_map] using
        congrArg (fun q : _ × _ => q.1.fst) hval
    have hsndV : x.snd.1 = y.snd.1 := by
      simpa only [f, TrivSqZeroExt.snd_map, LinearMap.fst_apply] using
        congrArg (fun q : _ × _ => q.1.snd) hval
    have hsndW : x.snd.2 = y.snd.2 := by
      simpa only [g, TrivSqZeroExt.snd_map, LinearMap.snd_apply] using
        congrArg (fun q : _ × _ => q.2.snd) hval
    apply TrivSqZeroExt.ext
    · exact hfst
    · exact Prod.ext hsndV hsndW
  · intro y
    let a : TrivSqZeroExt k (V × W) := (y.1.1.fst, (y.1.1.snd, y.1.2.snd))
    have hy : y.1.1.fst = y.1.2.fst := by
      change (TrivSqZeroExt.fstHom k k V) y.1.1 =
        (TrivSqZeroExt.fstHom k k W) y.1.2
      exact y.2
    refine ⟨a, ?_⟩
    apply Subtype.ext
    change (f a, g a) = y.1
    apply Prod.ext
    · apply TrivSqZeroExt.ext
      · rw [TrivSqZeroExt.fst_map]
        rfl
      · rw [TrivSqZeroExt.snd_map]
        rfl
    · apply TrivSqZeroExt.ext
      · rw [TrivSqZeroExt.fst_map]
        exact hy
      · rw [TrivSqZeroExt.snd_map]
        rfl

/-- A morphism of `𝒞_Λ` is the projection `k[V] → k`, up to compatible
`Λ`-algebra coordinates on its source and target. -/
def IsSquareZeroProjection
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V]
    {AV A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : AV ⟶ A₀) : Prop :=
  letI : Module Λ V := Module.compHom V (algebraMap Λ k)
  letI : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  ∃ (i₀ : A₀ ≃ₐ[Λ] k) (iV : AV ≃ₐ[Λ] TrivSqZeroExt k V),
    i₀.toAlgHom.comp e.hom =
      (TrivSqZeroExt.fstHom Λ k V).comp iV.toAlgHom

/-- The property of being the projection `k[V] → k` only depends on `V` up to linear
equivalence. -/
private theorem isSquareZeroProjection_of_linearEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} {W : Type z₁} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    {AV A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : AV ⟶ A₀)
    (he : IsSquareZeroProjection (V := V) e) (b : V ≃ₗ[k] W) :
    IsSquareZeroProjection (V := W) e := by
  let _ : Module Λ V := Module.compHom V (algebraMap Λ k)
  let _ : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module Λ W := Module.compHom W (algebraMap Λ k)
  let _ : IsScalarTower Λ k W := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨i₀, iV, hi⟩ := he
  obtain ⟨iW, hiW⟩ := exists_algEquiv_comp_fstHom_of_linearEquiv e i₀ iV hi b
  exact ⟨i₀, iW, hiW⟩

/-- The projection `k[V] → k` is surjective. -/
private theorem isSquareZeroProjection_surjective
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V]
    {AV A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : AV ⟶ A₀)
    (he : IsSquareZeroProjection (V := V) e) : Function.Surjective e.hom := by
  let _ : Module Λ V := Module.compHom V (algebraMap Λ k)
  let _ : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rcases he with ⟨i₀, iV, hi⟩
  intro a
  let zz : TrivSqZeroExt k V := (i₀ a, 0)
  refine ⟨iV.symm zz, ?_⟩
  have h := congrArg (fun f : AV →ₐ[Λ] k => f (iV.symm zz)) hi
  change i₀ (e.hom (iV.symm zz)) =
    (TrivSqZeroExt.fstHom Λ k V) (iV.toAlgHom (iV.symm zz)) at h
  have hcoord : (TrivSqZeroExt.fstHom Λ k V) (iV.toAlgHom (iV.symm zz)) = i₀ a := by
    change (iV (iV.symm zz)).fst = i₀ a
    rw [iV.apply_symm_apply]
    rfl
  exact i₀.injective (h.trans hcoord)

/-- Truncating `k[k × W] → k` along a surjection of coordinate spaces: the quotient of the
source by the kernel of the composite coordinate map is again a square-zero extension, the
projection factors through it, and its coordinates are the image coordinates. -/
private theorem exists_squareZeroTruncationAlongOfCoords
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {W : Type z} [AddCommGroup W] [Module k W]
    {U : Type z₁} [AddCommGroup U] [Module k U]
    {B A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : B ⟶ A₀) :
    (letI : Module Λ (k × W) := Module.compHom (k × W) (algebraMap Λ k)
     letI : IsScalarTower Λ k (k × W) :=
       IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
     letI : Algebra Λ (TrivSqZeroExt k (k × W)) :=
       TrivSqZeroExt.algebra' Λ k (k × W)
     letI : IsScalarTower Λ k (TrivSqZeroExt k (k × W)) := inferInstance
     (i₀ : A₀ ≃ₐ[Λ] k) →
     (iB : B ≃ₐ[Λ] TrivSqZeroExt k (k × W)) →
     (hie : i₀.toAlgHom.comp e.hom =
       (TrivSqZeroExt.fstHom Λ k (k × W)).comp iB.toAlgHom) →
     (r : k × W →ₗ[k] U) → (hr : Function.Surjective r) →
    (letI : Module Λ U := Module.compHom U (algebraMap Λ k)
     letI : IsScalarTower Λ k U :=
       IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
     letI : Algebra Λ (TrivSqZeroExt k U) := TrivSqZeroExt.algebra' Λ k U
     letI : IsScalarTower Λ k (TrivSqZeroExt k U) := inferInstance
     ∃ (B' : ArtinianLocalAlgCat.{u, v, w} Λ k) (q : B ⟶ B')
       (e' : B' ⟶ A₀) (iU : B' ≃ₐ[Λ] TrivSqZeroExt k U),
       q ≫ e' = e ∧ IsSquareZeroProjection (V := U) e' ∧
       i₀.toAlgHom.comp e'.hom =
         (TrivSqZeroExt.fstHom Λ k U).comp iU.toAlgHom ∧
       (∀ b, iU (q.hom b) = (TrivSqZeroExt.map r) (iB b)))) := by
  let _ : Module Λ (k × W) := Module.compHom (k × W) (algebraMap Λ k)
  let _ : SMul Λ (k × W) := (inferInstance : Module Λ (k × W)).toSMul
  let _ : SMul k (k × W) := (inferInstance : Module k (k × W)).toSMul
  let _ : IsScalarTower Λ k (k × W) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Algebra Λ (TrivSqZeroExt k (k × W)) :=
    TrivSqZeroExt.algebra' Λ k (k × W)
  let _ : IsScalarTower Λ k (TrivSqZeroExt k (k × W)) := inferInstance
  intro i₀ iB hie r hr
  let _ : Module Λ W := Module.compHom W (algebraMap Λ k)
  let _ : IsScalarTower Λ k W := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module Λ U := Module.compHom U (algebraMap Λ k)
  let _ : IsScalarTower Λ k U := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Algebra Λ (TrivSqZeroExt k U) := TrivSqZeroExt.algebra' Λ k U
  let _ : IsScalarTower Λ k (TrivSqZeroExt k U) := inferInstance
  let _ : IsScalarTower Λ k k := IsScalarTower.of_algebraMap_smul fun _ _ ↦ by
    simp [Algebra.smul_def]
  let _ : Algebra Λ kᵐᵒᵖ :=
    Algebra.compHom kᵐᵒᵖ
      (RingHom.comp (RingEquiv.toOpposite k).toRingHom (algebraMap Λ k))
  let _ : IsScalarTower Λ kᵐᵒᵖ W := inferInstance
  let _ : IsScalarTower Λ kᵐᵒᵖ U := inferInstance
  let _ : IsScalarTower Λ kᵐᵒᵖ k := inferInstance
  let f : TrivSqZeroExt k (k × W) →ₐ[k] TrivSqZeroExt k U :=
    TrivSqZeroExt.map r
  let qW : B →ₐ[Λ] TrivSqZeroExt k U := (f.restrictScalars Λ).comp iB.toAlgHom
  have heSurj : Function.Surjective e.hom := isSquareZeroProjection_surjective e ⟨i₀, iB, hie⟩
  have hqW : Function.Surjective qW := by
    intro y
    obtain ⟨x, hx⟩ := hr y.snd
    let a : TrivSqZeroExt k (k × W) := (y.fst, x)
    have hmap : f a = y := by
      apply TrivSqZeroExt.ext
      · rw [TrivSqZeroExt.fst_map]
        rfl
      · change (TrivSqZeroExt.map r a).snd = y.snd
        rw [TrivSqZeroExt.snd_map]
        exact hx
    refine ⟨iB.symm a, ?_⟩
    simpa [qW, AlgHom.comp_apply] using hmap
  have hfst : (TrivSqZeroExt.fstHom Λ k U).comp qW =
      (TrivSqZeroExt.fstHom Λ k (k × W)).comp iB.toAlgHom := by
    ext b
    change (TrivSqZeroExt.fstHom k k U)
        ((TrivSqZeroExt.map r) (iB b)) =
      (TrivSqZeroExt.fstHom k k (k × W)) (iB b)
    exact TrivSqZeroExt.fst_map r (iB b)
  let J : Ideal B := RingHom.ker qW.toRingHom
  have hJker : J ≤ RingHom.ker e.hom.toRingHom := by
    intro b hb
    have hzero : qW b = 0 := hb
    have hfstzero :
        (TrivSqZeroExt.fstHom Λ k (k × W)) (iB.toAlgHom b) = 0 := by
      have hh := congrArg (fun g : B →ₐ[Λ] k => g b) hfst
      have hh' : (TrivSqZeroExt.fstHom Λ k U) (qW b) =
          (TrivSqZeroExt.fstHom Λ k (k × W)) (iB.toAlgHom b) := by
        simpa only [AlgHom.comp_apply] using hh
      rw [hzero] at hh'
      simpa using hh'.symm
    have hiezero : i₀.toAlgHom (e.hom b) = 0 := by
      have hh := congrArg (fun g : B →ₐ[Λ] k => g b) hie
      exact hh.trans hfstzero
    exact i₀.injective (by simpa using hiezero)
  have hJmax : J ≤ maximalIdeal B :=
    hJker.trans (ArtinianLocalAlgCat.ker_le_maximalIdeal e)
  let B' := ArtinianLocalAlgCat.idealQuotientObj B J hJmax
  let q := ArtinianLocalAlgCat.idealQuotientProjection B J hJmax
  let e' := ArtinianLocalAlgCat.idealQuotientFactor e heSurj J hJker hJmax
  have hcomp : q ≫ e' = e :=
    ArtinianLocalAlgCat.idealQuotientProjection_comp_idealQuotientFactor
      e heSurj J hJker hJmax
  let iW : B' ≃ₐ[Λ] TrivSqZeroExt k U :=
    Ideal.quotientKerAlgEquivOfSurjective hqW
  have hqcoord (b : B) : iW (q.hom b) = qW b := by
    change iW (Ideal.Quotient.mk J b) = qW b
    exact Ideal.quotientKerAlgEquivOfSurjective_apply (f := qW) hqW b
  have hcoord : i₀.toAlgHom.comp e'.hom =
      (TrivSqZeroExt.fstHom Λ k U).comp iW.toAlgHom := by
    apply AlgHom.ext
    intro b
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective b
    calc
      i₀.toAlgHom (e'.hom (q.hom x)) = i₀.toAlgHom (e.hom x) := by
        have hx := congrArg (fun g : B ⟶ A₀ => g.hom x) hcomp
        have hx' : e'.hom (q.hom x) = e.hom x := by simpa using hx
        rw [hx']
      _ = (TrivSqZeroExt.fstHom Λ k (k × W)) (iB x) :=
        congrArg (fun g : B →ₐ[Λ] k => g x) hie
      _ = (TrivSqZeroExt.fstHom Λ k U) (qW x) :=
        (congrArg (fun g : B →ₐ[Λ] k => g x) hfst).symm
      _ = (TrivSqZeroExt.fstHom Λ k U) (iW (q.hom x)) := by rw [hqcoord]
  have hqcoord' (b : B) : iW (q.hom b) = (TrivSqZeroExt.map r) (iB b) := by
    rw [hqcoord]
    simp [qW, f, AlgHom.comp_apply]
  exact ⟨B', q, e', iW, hcomp, ⟨i₀, iW, hcoord⟩, hcoord, hqcoord'⟩

/-- Transport a factorization of the base projection to a factorization in the total
category. -/
private theorem exists_squareZero_objectMap
    {F : Type u₁} [Category.{v₁} F]
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    {W : Type z} [AddCommGroup W] [Module k W]
    {xV x₀ : F} (e : xV ⟶ x₀)
    (B' : ArtinianLocalAlgCat.{u, v, w} Λ k)
    (q : p.obj xV ⟶ B') (e' : B' ⟶ p.obj x₀)
    (hcomp : q ≫ e' = p.map e)
    (he' : IsSquareZeroProjection (V := W) e') :
    ∃ (xV' : F) (r : xV ⟶ xV') (eV' : xV' ⟶ x₀),
      p.IsHomLift q r ∧ p.IsHomLift e' eV' ∧ r ≫ eV' = e ∧
        IsSquareZeroProjection (V := W) (p.map eV') := by
  obtain ⟨xV', r, hr⟩ := exists_pushforward hp q xV rfl
  obtain ⟨eV', heV', hfac⟩ :=
    exists_factor_through_pushforward hp q r hr e' e hcomp.symm
  have hB' : p.obj xV' = B' := IsHomLift.codomain_eq p q r
  cases hB'
  let _ : p.IsHomLift e' eV' := heV'
  have hmap : p.map eV' = e' := (IsHomLift.eq_of_isHomLift p e' eV').symm
  refine ⟨xV', r, eV', hr, heV', hfac, ?_⟩
  rw [hmap]
  exact he'

/-- A splitting `V ≅ k × W` yields the two truncations of `k[V] → k`, with their
coordinates. -/
private theorem exists_squareZero_coordinateTruncationsData
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} {W : Type z₁} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    {B A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : B ⟶ A₀)
    (he : IsSquareZeroProjection (V := V) e) (b : V ≃ₗ[k] k × W) :
    (letI : Module Λ W := Module.compHom W (algebraMap Λ k)
     letI : IsScalarTower Λ k W := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
     letI : Algebra Λ (TrivSqZeroExt k W) := TrivSqZeroExt.algebra' Λ k W
     letI : Module Λ (k × W) := Module.compHom (k × W) (algebraMap Λ k)
     letI : SMul Λ (k × W) := (inferInstance : Module Λ (k × W)).toSMul
     letI : SMul k (k × W) := (inferInstance : Module k (k × W)).toSMul
     letI : IsScalarTower Λ k (k × W) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
     letI : Algebra Λ (TrivSqZeroExt k (k × W)) := TrivSqZeroExt.algebra' Λ k (k × W)
     letI : Module Λ k := Module.compHom k (algebraMap Λ k)
     letI := @IsScalarTower.of_algebraMap_smul Λ k k _ _ _
       (inferInstance : MulAction k k) (Module.compHom k (algebraMap Λ k)).toSMul
       (fun _ _ ↦ rfl)
     letI : Algebra Λ (TrivSqZeroExt k k) := TrivSqZeroExt.algebra' Λ k k
    ∃ (BW Bε : ArtinianLocalAlgCat.{u, v, w} Λ k)
      (qW : B ⟶ BW) (qε : B ⟶ Bε) (eW : BW ⟶ A₀) (eε : Bε ⟶ A₀)
      (i₀ : A₀ ≃ₐ[Λ] k)
      (iB : B ≃ₐ[Λ] TrivSqZeroExt k (k × W))
      (iW : BW ≃ₐ[Λ] TrivSqZeroExt k W)
      (iε : Bε ≃ₐ[Λ] TrivSqZeroExt k k),
      qW ≫ eW = e ∧ qε ≫ eε = e ∧
      IsSquareZeroProjection (V := W) eW ∧
      IsSquareZeroProjection (V := k) eε ∧
      i₀.toAlgHom.comp eW.hom =
        (TrivSqZeroExt.fstHom Λ k W).comp iW.toAlgHom ∧
      i₀.toAlgHom.comp eε.hom =
        (TrivSqZeroExt.fstHom Λ k k).comp iε.toAlgHom ∧
      (∀ a, iW (qW.hom a) =
        (TrivSqZeroExt.map (LinearMap.snd k k W)) (iB a)) ∧
      (∀ a, iε (qε.hom a) =
        (TrivSqZeroExt.map (LinearMap.fst k k W)) (iB a))) := by
  let _ : Module Λ W := Module.compHom W (algebraMap Λ k)
  let _ : IsScalarTower Λ k W := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Algebra Λ (TrivSqZeroExt k W) := TrivSqZeroExt.algebra' Λ k W
  let _ : Module Λ (k × W) := Module.compHom (k × W) (algebraMap Λ k)
  let _ : SMul Λ (k × W) := (inferInstance : Module Λ (k × W)).toSMul
  let _ : SMul k (k × W) := (inferInstance : Module k (k × W)).toSMul
  let _ : IsScalarTower Λ k (k × W) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Algebra Λ (TrivSqZeroExt k (k × W)) := TrivSqZeroExt.algebra' Λ k (k × W)
  let _ : Module Λ k := Module.compHom k (algebraMap Λ k)
  let _ := @IsScalarTower.of_algebraMap_smul Λ k k _ _ _
    (inferInstance : MulAction k k) (Module.compHom k (algebraMap Λ k)).toSMul
    (fun _ _ ↦ rfl)
  let _ : Algebra Λ (TrivSqZeroExt k k) := TrivSqZeroExt.algebra' Λ k k
  have he' : IsSquareZeroProjection (V := k × W) e :=
    isSquareZeroProjection_of_linearEquiv e he b
  rcases he' with ⟨i₀, iB, hie⟩
  obtain ⟨BW, qW, eW, iW, hW, heW, hcoordW, hqWcoord⟩ :=
    exists_squareZeroTruncationAlongOfCoords e i₀ iB hie
      (LinearMap.snd k k W) (by intro ww; exact ⟨(0, ww), rfl⟩)
  obtain ⟨Bε, qε, eε, iε, hε, heε, hcoordε, hqεcoord⟩ :=
    exists_squareZeroTruncationAlongOfCoords e i₀ iB hie
      (LinearMap.fst k k W) (by intro a; exact ⟨(a, 0), rfl⟩)
  exact ⟨BW, Bε, qW, qε, eW, eε, i₀, iB, iW, iε,
    hW, hε, heW, heε, hcoordW, hcoordε, hqWcoord, hqεcoord⟩

/-- The two truncations of `k[k × W] → k` exhibit it as the fibre product of `k[W] → k` and
`k[ε] → k`. -/
private theorem split_squareZero_base_isPullback
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {W : Type z} [AddCommGroup W] [Module k W]
    {B BW Bε A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (qW : B ⟶ BW) (qε : B ⟶ Bε) (eW : BW ⟶ A₀) (eε : Bε ⟶ A₀) :
    (letI : Module Λ W := Module.compHom W (algebraMap Λ k)
     letI : IsScalarTower Λ k W := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
     letI : Algebra Λ (TrivSqZeroExt k W) := TrivSqZeroExt.algebra' Λ k W
     letI : Module Λ (k × W) := Module.compHom (k × W) (algebraMap Λ k)
     letI : SMul Λ (k × W) := (inferInstance : Module Λ (k × W)).toSMul
     letI : SMul k (k × W) := (inferInstance : Module k (k × W)).toSMul
     letI : IsScalarTower Λ k (k × W) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
     letI : Algebra Λ (TrivSqZeroExt k (k × W)) := TrivSqZeroExt.algebra' Λ k (k × W)
     letI : Module Λ k := Module.compHom k (algebraMap Λ k)
     letI := @IsScalarTower.of_algebraMap_smul Λ k k _ _ _
       (inferInstance : MulAction k k) (Module.compHom k (algebraMap Λ k)).toSMul
       (fun _ _ ↦ rfl)
     letI : Algebra Λ (TrivSqZeroExt k k) := TrivSqZeroExt.algebra' Λ k k
     (i₀ : A₀ ≃ₐ[Λ] k) →
     (iB : B ≃ₐ[Λ] TrivSqZeroExt k (k × W)) →
     (iW : BW ≃ₐ[Λ] TrivSqZeroExt k W) →
     (iε : Bε ≃ₐ[Λ] TrivSqZeroExt k k) →
     (hW : qW ≫ eW = qε ≫ eε) →
     (hcoordW : i₀.toAlgHom.comp eW.hom =
       (TrivSqZeroExt.fstHom Λ k W).comp iW.toAlgHom) →
     (hcoordε : i₀.toAlgHom.comp eε.hom =
      (TrivSqZeroExt.fstHom Λ k k).comp iε.toAlgHom) →
     (hqW : ∀ a, iW (qW.hom a) =
       (TrivSqZeroExt.map (LinearMap.snd k k W)) (iB a)) →
     (hqε : ∀ a, iε (qε.hom a) =
       (TrivSqZeroExt.map (LinearMap.fst k k W)) (iB a)) →
     IsPullback qε qW eε eW) := by
  let _ : Module Λ W := Module.compHom W (algebraMap Λ k)
  let _ : IsScalarTower Λ k W := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Algebra Λ (TrivSqZeroExt k W) := TrivSqZeroExt.algebra' Λ k W
  let _ : Module Λ (k × W) := Module.compHom (k × W) (algebraMap Λ k)
  let _ : SMul Λ (k × W) := (inferInstance : Module Λ (k × W)).toSMul
  let _ : SMul k (k × W) := (inferInstance : Module k (k × W)).toSMul
  let _ : IsScalarTower Λ k (k × W) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Algebra Λ (TrivSqZeroExt k (k × W)) := TrivSqZeroExt.algebra' Λ k (k × W)
  let _ : Module Λ k := Module.compHom k (algebraMap Λ k)
  let _ := @IsScalarTower.of_algebraMap_smul Λ k k _ _ _
    (inferInstance : MulAction k k) (Module.compHom k (algebraMap Λ k)).toSMul
    (fun _ _ ↦ rfl)
  let _ : Algebra Λ (TrivSqZeroExt k k) := TrivSqZeroExt.algebra' Λ k k
  intro i₀ iB iW iε hW hcoordW hcoordε hqW hqε
  let stdFst := TrivSqZeroExt.fstHom Λ k k
  let stdSnd := TrivSqZeroExt.fstHom Λ k W
  let iProd : TrivSqZeroExt k (k × W) ≃ₐ[Λ]
      AlgHom.pullback (TrivSqZeroExt.fstHom k k k) (TrivSqZeroExt.fstHom k k W) :=
    (trivSqZeroExtProductAlgEquiv (k := k) (V := k) (W := W)).restrictScalars Λ
  exact IsPullback.mk' (P := B) (X := Bε) (Y := BW) (Z := A₀)
    (fst := qε) (snd := qW) (f := eε) (g := eW) hW.symm (by
      intro T m m' hmε hmW
      apply ArtinianLocalAlgCat.hom_ext
      apply AlgHom.ext
      intro t
      exact iB.injective <| TrivSqZeroExt.ext
        (by
          have h := congrArg (fun g : T ⟶ Bε => iε (g.hom t)) hmε
          simpa only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, hqε,
            TrivSqZeroExt.fst_map] using congrArg TrivSqZeroExt.fst h)
        (Prod.ext
          (by
            have h := congrArg (fun g : T ⟶ Bε => iε (g.hom t)) hmε
            simpa only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, hqε,
              TrivSqZeroExt.snd_map, LinearMap.fst_apply] using
              congrArg TrivSqZeroExt.snd h)
          (by
            have h := congrArg (fun g : T ⟶ BW => iW (g.hom t)) hmW
            simpa only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply, hqW,
              TrivSqZeroExt.snd_map, LinearMap.snd_apply] using
              congrArg TrivSqZeroExt.snd h))) (by
    intro T a b hab
    let cε : T →ₐ[Λ] TrivSqZeroExt k k := iε.toAlgHom.comp a.hom
    let cW : T →ₐ[Λ] TrivSqZeroExt k W := iW.toAlgHom.comp b.hom
    have hcompat : stdFst.comp cε = stdSnd.comp cW := by
      ext t
      have hbase : i₀ (eε.hom (a.hom t)) = i₀ (eW.hom (b.hom t)) :=
        congrArg (fun g : T ⟶ A₀ => i₀ (g.hom t)) hab
      calc
        stdFst (cε t) = i₀ (eε.hom (a.hom t)) :=
          (congrArg (fun g : Bε →ₐ[Λ] k => g (a.hom t)) hcoordε).symm
        _ = i₀ (eW.hom (b.hom t)) := hbase
        _ = stdSnd (cW t) :=
          congrArg (fun g : BW →ₐ[Λ] k => g (b.hom t)) hcoordW
    let pairRaw := AlgHom.prod cε cW
    let pair : T →ₐ[Λ] AlgHom.pullback stdFst stdSnd :=
      pairRaw.codRestrict _ (fun t => DFunLike.congr_fun hcompat t)
    let liftAlg : T →ₐ[Λ] B :=
      iB.symm.toAlgHom.comp (iProd.symm.toAlgHom.comp pair)
    have hliftε : qε.hom.comp liftAlg = a.hom := by
      ext t : 1
      apply iε.injective
      change iε (qε.hom (iB.symm (iProd.symm (pair t)))) = iε (a.hom t)
      rw [hqε, iB.apply_symm_apply]
      exact congrArg (fun zz => zz.val.1) (iProd.apply_symm_apply (pair t))
    have hliftW : qW.hom.comp liftAlg = b.hom := by
      ext t : 1
      apply iW.injective
      change iW (qW.hom (iB.symm (iProd.symm (pair t)))) = iW (b.hom t)
      rw [hqW, iB.apply_symm_apply]
      exact congrArg (fun zz => zz.val.2) (iProd.apply_symm_apply (pair t))
    let lift : T ⟶ B :=
      { hom := liftAlg
        isLocal := by
          refine ⟨fun t ht => ?_⟩
          have hu : IsUnit (a.hom t) := by
            have hu' := ht.map qε.hom.toRingHom
            change IsUnit (qε.hom (liftAlg t)) at hu'
            have hh : qε.hom (liftAlg t) = a.hom t := DFunLike.congr_fun hliftε t
            rwa [hh] at hu'
          exact a.isLocal.map_nonunit t hu
        residue_comm := by
          intro t
          calc
            B.residueEquiv (residue B (liftAlg t)) =
                Bε.residueEquiv (residue Bε (qε.hom (liftAlg t))) :=
              (qε.residue_comm (liftAlg t)).symm
            _ = T.residueEquiv (residue T t) := by
              have hh : qε.hom (liftAlg t) = a.hom t := DFunLike.congr_fun hliftε t
              rw [hh]
              exact a.residue_comm t }
    exact ⟨lift, ArtinianLocalAlgCat.hom_ext hliftε,
      ArtinianLocalAlgCat.hom_ext hliftW⟩)

section
variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Base change of the prescribed square along the truncation `k[V] → k[W]`. -/
private theorem exists_lower_base_pullback
    {A B BW A₀ AV : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (d : A ⟶ A₀) (e : B ⟶ A₀)
    (qW : B ⟶ BW) (eW : BW ⟶ A₀) (he : qW ≫ eW = e)
    (hsurj : Function.Surjective eW.hom)
    (g : AV ⟶ A) (gV : AV ⟶ B) (hpb : IsPullback gV g e d) :
    ∃ (AV' : ArtinianLocalAlgCat.{u, v, w} Λ k)
      (fst : AV' ⟶ A) (snd : AV' ⟶ BW) (q : AV ⟶ AV'),
      IsPullback snd fst eW d ∧ q ≫ fst = g ∧ q ≫ snd = gV ≫ qW := by
  let hs : Function.Surjective d.hom ∨ Function.Surjective eW.hom := Or.inr hsurj
  let fst := ArtinianLocalAlgCat.pullbackFst_of_surjective d eW hs
  let snd := ArtinianLocalAlgCat.pullbackSnd_of_surjective d eW hs
  have hpb' := ArtinianLocalAlgCat.isPullback_of_surjective d eW hs
  have hw : g ≫ d = (gV ≫ qW) ≫ eW := by
    calc
      g ≫ d = gV ≫ e := hpb.w.symm
      _ = gV ≫ (qW ≫ eW) := by rw [he]
      _ = (gV ≫ qW) ≫ eW := by simp [Category.assoc]
  exact ⟨_, fst, snd, hpb'.lift g (gV ≫ qW) hw, hpb'.flip,
    hpb'.lift_fst g (gV ≫ qW) hw, hpb'.lift_snd g (gV ≫ qW) hw⟩

/-- The square comparing the original prescribed square with its base change is a pullback. -/
private theorem lower_base_composite_pullback
    {A B BW A₀ AV AV' : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (d : A ⟶ A₀) (e : B ⟶ A₀)
    (qW : B ⟶ BW) (eW : BW ⟶ A₀) (he : qW ≫ eW = e)
    (g : AV ⟶ A) (gV : AV ⟶ B)
    (hpb : IsPullback gV g e d)
    (fst : AV' ⟶ A) (snd : AV' ⟶ BW) (q : AV ⟶ AV')
    (hpb' : IsPullback snd fst eW d)
    (hqf : q ≫ fst = g) (hqs : q ≫ snd = gV ≫ qW) :
    IsPullback q gV snd qW := by
  refine IsPullback.mk' (P := AV) (X := AV') (Y := B) (Z := BW)
    (fst := q) (snd := gV) (f := snd) (g := qW) hqs ?_ ?_
  · intro T m m' hmq hmgV
    refine hpb.hom_ext hmgV ?_
    calc
      m ≫ g = m ≫ (q ≫ fst) := by rw [hqf]
      _ = (m ≫ q) ≫ fst := by simp [Category.assoc]
      _ = (m' ≫ q) ≫ fst := by rw [hmq]
      _ = m' ≫ (q ≫ fst) := by simp [Category.assoc]
      _ = m' ≫ g := by rw [hqf]
  · intro T a b hab
    have hcompat : b ≫ e = (a ≫ fst) ≫ d := by
      calc
        b ≫ e = b ≫ (qW ≫ eW) := by rw [he]
        _ = (b ≫ qW) ≫ eW := by simp [Category.assoc]
        _ = (a ≫ snd) ≫ eW := by rw [hab]
        _ = a ≫ (snd ≫ eW) := by simp [Category.assoc]
        _ = a ≫ (fst ≫ d) := by rw [hpb'.w]
        _ = (a ≫ fst) ≫ d := by simp [Category.assoc]
    let m : T ⟶ AV := hpb.lift b (a ≫ fst) hcompat
    refine ⟨m, ?_, hpb.lift_fst b (a ≫ fst) hcompat⟩
    refine hpb'.hom_ext ?_ ?_
    · calc
        (m ≫ q) ≫ snd = m ≫ (q ≫ snd) := by simp [Category.assoc]
        _ = m ≫ (gV ≫ qW) := by rw [hqs]
        _ = (m ≫ gV) ≫ qW := by simp [Category.assoc]
        _ = b ≫ qW := by
          simpa only [m] using congrArg (fun f : T ⟶ B => f ≫ qW)
            (hpb.lift_fst b (a ≫ fst) hcompat)
        _ = a ≫ snd := hab.symm
    · calc
        (m ≫ q) ≫ fst = m ≫ (q ≫ fst) := by simp [Category.assoc]
        _ = m ≫ g := by rw [hqf]
        _ = a ≫ fst := by simpa only [m] using hpb.lift_snd b (a ≫ fst) hcompat

/-- The remaining corner of the base change is a square over the dual-number projection. -/
private theorem lower_base_epsilon_pullback
    {A B BW Bε A₀ AV AV' : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (d : A ⟶ A₀) (e : B ⟶ A₀)
    (qW : B ⟶ BW) (qε : B ⟶ Bε)
    (eW : BW ⟶ A₀) (eε : Bε ⟶ A₀) (he : qW ≫ eW = e)
    (g : AV ⟶ A) (gV : AV ⟶ B) (hpb : IsPullback gV g e d)
    (fst : AV' ⟶ A) (snd : AV' ⟶ BW) (q : AV ⟶ AV')
    (hpb' : IsPullback snd fst eW d)
    (hqf : q ≫ fst = g) (hqs : q ≫ snd = gV ≫ qW)
    (hcoord : IsPullback qε qW eε eW) :
    IsPullback (gV ≫ qε) q eε (snd ≫ eW) :=
  (lower_base_composite_pullback d e qW eW he g gV hpb
    fst snd q hpb' hqf hqs).flip.paste_horiz hcoord

/-- In dimension one the projection `k[V] → k` is the dual-number projection. -/
private theorem isDualNumberProjection_of_linearEquiv
    {V : Type z} [AddCommGroup V] [Module k V]
    {AV A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : AV ⟶ A₀)
    (he : IsSquareZeroProjection (V := V) e) (b : V ≃ₗ[k] k) :
    IsDualNumberProjection e := by
  let _ : Module Λ V := Module.compHom V (algebraMap Λ k)
  let _ : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rcases he with ⟨i₀, iV, hi⟩
  exact isDualNumberProjection_of_coordinates e i₀ iV hi b

/-- A one-dimensional space is linearly equivalent to `k`. -/
private noncomputable def linearEquivOfFinrankOne {V : Type z} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hV : Module.finrank k V = 1) : V ≃ₗ[k] k :=
  (Module.nonempty_linearEquiv_of_finrank_eq_one hV).some.symm

/-- In dimension one the projection `k[V] → k` is the dual-number projection. -/
private theorem isDualNumberProjection_of_finrank_one
    {V : Type z} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {AV A₀ : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : AV ⟶ A₀)
    (he : IsSquareZeroProjection (V := V) e)
    (hV : Module.finrank k V = 1) : IsDualNumberProjection e :=
  isDualNumberProjection_of_linearEquiv e he (linearEquivOfFinrankOne hV)

/-- In dimension zero the projection `k[V] → k` is an isomorphism. -/
private theorem isIso_squareZeroProjection_of_finrank_zero
    {V : Type z} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (e : B ⟶ A)
    (he : IsSquareZeroProjection (V := V) e) (hV : Module.finrank k V = 0) :
    IsIso e := by
  apply ArtinianLocalAlgCat.isIso_of_bijective_hom e
  refine ⟨?_, isSquareZeroProjection_surjective e he⟩
  let _ : Module Λ V := Module.compHom V (algebraMap Λ k)
  let _ : IsScalarTower Λ k V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨i₀, iV, hie⟩ := he
  intro a b hab
  apply iV.injective
  apply TrivSqZeroExt.ext
  · have ha := DFunLike.congr_fun hie a
    have hb := DFunLike.congr_fun hie b
    exact ha.symm.trans ((congrArg i₀ hab).trans hb)
  · exact (finrank_zero_iff_forall_zero.mp hV _).trans
      (finrank_zero_iff_forall_zero.mp hV _).symm

/-- A space of dimension more than one splits off a line. -/
private theorem exists_squareZero_splitting {V : Type z} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (n : ℕ) (hV : Module.finrank k V = n) (hn : 1 < n) :
    ∃ (W : Submodule k V) (_b : V ≃ₗ[k] k × W), Module.finrank k W = n - 1 := by
  let i : Fin n := ⟨0, by omega⟩
  let β := Module.finBasisOfFinrankEq k V hV
  let ℓ : V →ₗ[k] k := (Finsupp.lapply i).comp β.repr.toLinearMap
  let s : k →ₗ[k] V := β.repr.symm.toLinearMap.comp (Finsupp.lsingle i)
  have hℓs : ℓ.comp s = LinearMap.id := by
    ext
    simp [ℓ, s, β, i, LinearMap.comp_apply]
  have hs (a : k) : ℓ (s a) = a := by
    simpa [LinearMap.comp_apply] using congrArg (fun f : k →ₗ[k] k => f a) hℓs
  let proj : V →ₗ[k] V := (LinearMap.id : V →ₗ[k] V) - s.comp ℓ
  let W : Submodule k V := LinearMap.ker ℓ
  let r : V →ₗ[k] W := LinearMap.codRestrict W proj fun vv => by
      change ℓ (proj vv) = 0
      simp [proj, LinearMap.sub_apply, LinearMap.comp_apply, hs]
  let f : V →ₗ[k] k × W := LinearMap.prod ℓ r
  have hinj : Function.Injective f := by
    intro vv vv' h
    have hℓ : ℓ vv = ℓ vv' := congrArg Prod.fst h
    have hr : proj vv = proj vv' := congrArg Subtype.val (congrArg Prod.snd h)
    have hr' : vv - s (ℓ vv) = vv' - s (ℓ vv') := by
      simpa [proj, LinearMap.sub_apply, LinearMap.comp_apply] using hr
    calc
      vv = (vv - s (ℓ vv)) + s (ℓ vv) := by simp
      _ = (vv' - s (ℓ vv')) + s (ℓ vv) := by rw [hr']
      _ = (vv' - s (ℓ vv')) + s (ℓ vv') := by rw [hℓ]
      _ = vv' := by simp
  have hsurj : Function.Surjective f := by
    rintro ⟨a, ww⟩
    refine ⟨s a + ww.1, ?_⟩
    apply Prod.ext
    · simpa [f, LinearMap.prod_apply, LinearMap.comp_apply] using
        congrArg (fun g : k →ₗ[k] k => g a) hℓs
    · apply Subtype.ext
      have hw : ℓ ww.1 = 0 := ww.2
      change proj (s a + ww.1) = ww.1
      simp [proj, LinearMap.sub_apply, LinearMap.comp_apply, hs, hw]
  have hsurjℓ : Function.Surjective ℓ := fun a =>
    ⟨s a, by simpa [LinearMap.comp_apply] using congrArg (fun g : k →ₗ[k] k => g a) hℓs⟩
  have hdimrange : Module.finrank k (LinearMap.range ℓ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurjℓ, finrank_top]
    exact CommSemiring.finrank_self k
  have hdimker : Module.finrank k (LinearMap.ker ℓ) = n - 1 := by
    have hnull := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hdimrange, hV] at hnull
    omega
  exact ⟨W, LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, hdimker⟩

end

/-- A completion in dimension zero: the projection is invertible, so pushing forward the
inverse of the prescribed projection produces the apex. -/
private theorem completion_of_finrank_zero
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p)
    {x xV x₀ : F} (d : x ⟶ x₀) (e : xV ⟶ x₀)
    (he : IsSquareZeroProjection (V := V) (p.map e))
    (hV : Module.finrank k V = 0)
    {AV : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : AV ⟶ p.obj x) (gV : AV ⟶ p.obj xV)
    (hpb : IsPullback gV g (p.map e) (p.map d)) :
    Nonempty (PullbackCompletion p d e g gV) := by
  let _ : IsIso (p.map e) := isIso_squareZeroProjection_of_finrank_zero (p.map e) he hV
  let _ : IsIso e := isIso_of_isIso_map hp e
  let _ : IsIso g := hpb.flip.isIso_fst_of_isIso
  obtain ⟨y, i, hi⟩ := exists_pushforward hp (inv g) x rfl
  have hy : p.obj y = AV := IsHomLift.codomain_eq p (inv g) i
  cases hy
  have hpi : p.map i = inv g := (IsHomLift.eq_of_isHomLift p (inv g) i).symm
  let _ : IsIso (p.map i) := by rw [hpi]; infer_instance
  let _ : IsIso i := isIso_of_isIso_map hp i
  have hinvMap : p.map (inv i) = g := by simp [hpi]
  refine ⟨{
    apex := y
    apex_eq := rfl
    toFirst := inv i
    toSecond := inv i ≫ d ≫ inv e
    comm := ?_
    map_toFirst := ?_
    map_toSecond := ?_ }⟩
  · simp [Category.assoc]
  · simp [hpi]
  · rw [Functor.map_comp, Functor.map_comp, hinvMap, Functor.map_inv]
    calc
      g ≫ p.map d ≫ inv (p.map e) = (gV ≫ p.map e) ≫ inv (p.map e) := by
        simpa only [Category.assoc] using
          (congrArg (fun a => a ≫ inv (p.map e)) hpb.w).symm
      _ = gV := by simp [Category.assoc]

/-- The comparison clause in dimension one is condition (S2) itself. -/
private theorem comparison_of_finrank_one
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hS2 : SchlessingerConditionS2 p)
    {x xV x₀ : F} (d : x ⟶ x₀) (e : xV ⟶ x₀)
    (he : IsSquareZeroProjection (V := V) (p.map e))
    (hV : Module.finrank k V = 1)
    {AV : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : AV ⟶ p.obj x) (gV : AV ⟶ p.obj xV)
    (hpb : IsPullback gV g (p.map e) (p.map d))
    (P Q : PullbackCompletion p d e g gV) :
    ∃ b : P.apex ⟶ Q.apex,
      P.toFirst = b ≫ Q.toFirst ∧
        p.map b = eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm :=
  hS2.comparison d e (isDualNumberProjection_of_finrank_one (p.map e) he hV) g gV hpb P Q

/-- A completion whose first projection is invertible is comparable to any other. -/
private theorem comparison_of_isIso_first {C : Type u₂} [Category.{v₂} C]
    {F : Type u₁} [Category.{v₁} F] {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {x xV x₀ : F} (d : x ⟶ x₀) (e : xV ⟶ x₀)
    {B : C} (g : B ⟶ p.obj x) (gV : B ⟶ p.obj xV) [IsIso g]
    (P Q : PullbackCompletion p d e g gV) :
    ∃ b : P.apex ⟶ Q.apex, P.toFirst = b ≫ Q.toFirst ∧
      p.map b = eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm := by
  have _ : IsIso (p.map Q.toFirst) := by rw [Q.map_toFirst]; infer_instance
  have _ : IsIso Q.toFirst := isIso_of_isIso_map hp Q.toFirst
  refine ⟨P.toFirst ≫ inv Q.toFirst, by simp, ?_⟩
  apply (cancel_mono (p.map Q.toFirst)).mp
  simp only [← Functor.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [P.map_toFirst, Q.map_toFirst]
  simp

/-- Pushing a commuting square in the total category forward along a map of its base apex
produces a completion of the pushed-forward square. -/
private theorem pushforward_completion {C : Type u₂} [Category.{v₂} C]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p)
    {x xV x₀ y : F} (d : x ⟶ x₀) (e : xV ⟶ x₀)
    {B : C} (g : B ⟶ p.obj x) (gV : B ⟶ p.obj xV)
    (hw : gV ≫ p.map e = g ≫ p.map d)
    (f : y ⟶ x) (fV : y ⟶ xV) (hc : fV ≫ e = f ≫ d)
    (q : p.obj y ⟶ B) (hf : p.map f = q ≫ g) (hfV : p.map fV = q ≫ gV) :
    ∃ (P : PullbackCompletion p d e g gV) (i : y ⟶ P.apex),
      p.map i = q ≫ eqToHom P.apex_eq.symm ∧
      i ≫ P.toFirst = f ∧ i ≫ P.toSecond = fV := by
  obtain ⟨zz, i, hi⟩ := exists_pushforward hp q y rfl
  have hz := IsHomLift.codomain_eq p q i
  cases hz
  have hpi : p.map i = q := (IsHomLift.eq_of_isHomLift p q i).symm
  obtain ⟨a, ha, hia⟩ := exists_factor_through_pushforward hp q i hi g f hf
  obtain ⟨b, hb, hib⟩ := exists_factor_through_pushforward hp q i hi gV fV hfV
  have hpa : p.map a = g := (IsHomLift.eq_of_isHomLift p g a).symm
  have hpb : p.map b = gV := (IsHomLift.eq_of_isHomLift p gV b).symm
  have hab : b ≫ e = a ≫ d := by
    apply eq_of_factor_through_pushforward hp (p.map i) i (IsHomLift.map p i)
      (p.map (a ≫ d)) (φ := f ≫ d)
    · rw [Functor.map_comp, hf, Functor.map_comp, hpa, hpi, Category.assoc]
    · apply IsHomLift.of_fac' p _ _ rfl rfl
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rw [Functor.map_comp, Functor.map_comp, hpb, hpa, hw]
    · exact IsHomLift.map p (a ≫ d)
    · simpa [← Category.assoc, hib] using hc
    · simp [← Category.assoc, hia]
  let P : PullbackCompletion p d e g gV :=
    { apex := zz
      apex_eq := rfl
      toFirst := a
      toSecond := b
      comm := hab
      map_toFirst := by simpa using hpa
      map_toSecond := by simpa using hpb }
  refine ⟨P, i, ?_, hia, hib⟩
  simpa using hpi

/-- The two truncations of `k[V] → k` in the total category, over the splitting of `V`. -/
private theorem exists_squareZero_split
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} {W : Type z₁} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    {F : Type u₁} [Category.{v₁} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p) {xV x₀ : F} (e : xV ⟶ x₀)
    (he : IsSquareZeroProjection (V := V) (p.map e)) (b : V ≃ₗ[k] k × W) :
    ∃ (xW xε : F) (rW : xV ⟶ xW) (rε : xV ⟶ xε)
      (eW : xW ⟶ x₀) (eε : xε ⟶ x₀),
      rW ≫ eW = e ∧ rε ≫ eε = e ∧
      IsSquareZeroProjection (V := W) (p.map eW) ∧
      IsSquareZeroProjection (V := k) (p.map eε) ∧
      IsPullback (p.map rε) (p.map rW) (p.map eε) (p.map eW) := by
  obtain ⟨BW, Bε, qW, qε, eWB, eεB, i₀, iB, iW, iε,
      hqWeW, hqεeε, heWB, heεB, hcoordW, hcoordε, hqWcoord, hqεcoord⟩ :=
    exists_squareZero_coordinateTruncationsData (p.map e) he b
  obtain ⟨xW, rW, eW, hrW, hliftW, hcompW, heW⟩ :=
    exists_squareZero_objectMap hp e BW qW eWB hqWeW heWB
  obtain ⟨xε, rε, eε, hrε, hliftε, hcompε, heε⟩ :=
    exists_squareZero_objectMap hp e Bε qε eεB hqεeε heεB
  have hcodW := IsHomLift.codomain_eq p qW rW
  cases hcodW
  have hcodε := IsHomLift.codomain_eq p qε rε
  cases hcodε
  have hprW : p.map rW = qW := (IsHomLift.eq_of_isHomLift p qW rW).symm
  have hprε : p.map rε = qε := (IsHomLift.eq_of_isHomLift p qε rε).symm
  have hpeW : p.map eW = eWB := (IsHomLift.eq_of_isHomLift p eWB eW).symm
  have hpeε : p.map eε = eεB := (IsHomLift.eq_of_isHomLift p eεB eε).symm
  have hsplit := split_squareZero_base_isPullback qW qε eWB eεB i₀ iB iW iε
    (hqWeW.trans hqεeε.symm) hcoordW hcoordε hqWcoord hqεcoord
  refine ⟨xW, xε, rW, rε, eW, eε, hcompW, hcompε, heW, heε, ?_⟩
  simpa [hprε, hprW, hpeε, hpeW] using hsplit

/-- The existence clause, by induction on `dim_k V`. -/
private theorem completion_squareZero_finrank (n : ℕ)
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (hS2 : SchlessingerConditionS2 p)
    {x xV x₀ : F} (d : x ⟶ x₀) (e : xV ⟶ x₀)
    (he : IsSquareZeroProjection (V := V) (p.map e))
    (hV : Module.finrank k V = n)
    {AV : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : AV ⟶ p.obj x) (gV : AV ⟶ p.obj xV)
    (hpb : IsPullback gV g (p.map e) (p.map d)) :
    Nonempty (PullbackCompletion p d e g gV) := by
  induction n using Nat.strong_induction_on
      generalizing V xV e he AV g gV hpb with
  | h n ih =>
    by_cases hn0 : n = 0
    · subst n
      exact completion_of_finrank_zero p hp d e he (by omega) g gV hpb
    · by_cases hn1 : n = 1
      · subst n
        exact hS2.completion d e
          (isDualNumberProjection_of_finrank_one (p.map e) he (by omega)) g gV hpb
      · have hn : 1 < n := by omega
        obtain ⟨W, b, hdimW⟩ := exists_squareZero_splitting n hV hn
        obtain ⟨xW, xε, rW, rε, eW, eε, hcompW, hcompε, heW, heε, hsplit'⟩ :=
          exists_squareZero_split hp e he b
        have hcompW' : p.map rW ≫ p.map eW = p.map e := by
          rw [← Functor.map_comp, hcompW]
        obtain ⟨AV', fst, snd, q, hpb', hqf, hqs⟩ :=
          exists_lower_base_pullback (p.map d) (p.map e) (p.map rW) (p.map eW)
            hcompW' (isSquareZeroProjection_surjective (p.map eW) heW) g gV hpb
        have hpbR := lower_base_epsilon_pullback (p.map d) (p.map e)
          (p.map rW) (p.map rε) (p.map eW) (p.map eε) hcompW'
          g gV hpb fst snd q hpb' hqf hqs hsplit'
        obtain ⟨P⟩ := ih (n - 1) (by omega)
          (V := W) (xV := xW) (e := eW) (he := heW) (hV := hdimW)
          (AV := AV') (g := fst) (gV := snd) (hpb := hpb')
        let gP : AV ⟶ p.obj P.apex := q ≫ eqToHom P.apex_eq.symm
        let iP : AV' ≅ p.obj P.apex := eqToIso P.apex_eq.symm
        have hpbRankOne :
            IsPullback (gV ≫ p.map rε) gP (p.map eε)
              (p.map (P.toSecond ≫ eW)) := by
          apply hpbR.of_iso (Iso.refl AV) (Iso.refl _) iP (Iso.refl _)
          · simp
          · simp [gP, iP]
          · simp
          · rw [Functor.map_comp, P.map_toSecond]
            simp [iP, Category.assoc]
        obtain ⟨R⟩ := hS2.completion (P.toSecond ≫ eW) eε
          (isDualNumberProjection_of_finrank_one (p.map eε) heε (by simp))
          gP (gV ≫ p.map rε) hpbRankOne
        let gVR : p.obj R.apex ⟶ p.obj xV := eqToHom R.apex_eq ≫ gV
        obtain ⟨zz, i, hi⟩ := exists_pushforward hp gVR R.apex rfl
        have hz : p.obj zz = p.obj xV := IsHomLift.codomain_eq p gVR i
        have hpi : p.map i = gVR ≫ eqToHom hz.symm := by
          let _ : p.IsHomLift gVR i := hi
          simpa using IsHomLift.fac' p gVR i
        have hbaseW : p.map (R.toFirst ≫ P.toSecond) = gVR ≫ p.map rW := by
          calc
            p.map (R.toFirst ≫ P.toSecond) =
                p.map R.toFirst ≫ p.map P.toSecond := Functor.map_comp p _ _
            _ = (eqToHom R.apex_eq ≫ gP) ≫
                (eqToHom P.apex_eq ≫ snd) := by
                  rw [R.map_toFirst, P.map_toSecond]
            _ = eqToHom R.apex_eq ≫ (q ≫ snd) := by
              simp [gP, Category.assoc]
            _ = eqToHom R.apex_eq ≫ (gV ≫ p.map rW) := by rw [hqs]
            _ = gVR ≫ p.map rW := by simp [gVR, Category.assoc]
        have hbaseε : p.map R.toSecond = gVR ≫ p.map rε := by
          rw [R.map_toSecond]
          simp [gVR, Category.assoc]
        obtain ⟨ψW, hψW, hfacW⟩ :=
          exists_factor_through_pushforward hp gVR i hi (p.map rW)
            (R.toFirst ≫ P.toSecond) hbaseW
        obtain ⟨ψε, hψε, hfacε⟩ :=
          exists_factor_through_pushforward hp gVR i hi (p.map rε) R.toSecond hbaseε
        have hbaseε0 : p.map rε ≫ p.map eε = p.map e := by
          rw [← Functor.map_comp, hcompε]
        let k₀ := p.map rW ≫ p.map eW
        have hbaseR : p.map (R.toSecond ≫ eε) = gVR ≫ k₀ := by
          rw [Functor.map_comp, hbaseε]
          dsimp [k₀]
          rw [Category.assoc, hbaseε0, hcompW']
        have hmapψ {y : F} {t : p.obj xV ⟶ p.obj y} {ψ : zz ⟶ y} (h : p.IsHomLift t ψ) :
            p.map ψ = eqToHom hz ≫ t := by
          let _ := h
          simpa using IsHomLift.fac' p t ψ
        let kZ := eqToHom hz ≫ k₀
        have hbase : p.map (R.toSecond ≫ eε) = p.map i ≫ kZ := by
          rw [hbaseR, hpi]
          simp [kZ, Category.assoc]
        have hthetaW : p.IsHomLift kZ (ψW ≫ eW) := by
          apply IsHomLift.of_fac' p kZ (ψW ≫ eW) rfl rfl
          change p.map (ψW ≫ eW) = kZ
          rw [Functor.map_comp]
          rw [hmapψ hψW]
          simp [kZ, k₀, Category.assoc]
        have hthetaε : p.IsHomLift kZ (ψε ≫ eε) := by
          apply IsHomLift.of_fac' p kZ (ψε ≫ eε) rfl rfl
          change p.map (ψε ≫ eε) = kZ
          rw [Functor.map_comp]
          rw [hmapψ hψε]
          simp [kZ, k₀, Category.assoc, hbaseε0, hcompW']
        have hfacε' : i ≫ (ψε ≫ eε) = R.toSecond ≫ eε := by
          calc
            i ≫ (ψε ≫ eε) = (i ≫ ψε) ≫ eε := by simp [Category.assoc]
            _ = R.toSecond ≫ eε := by rw [hfacε]
        have hfacW' : i ≫ (ψW ≫ eW) = R.toSecond ≫ eε := by
          calc
            i ≫ (ψW ≫ eW) = (i ≫ ψW) ≫ eW := by simp [Category.assoc]
            _ = (R.toFirst ≫ P.toSecond) ≫ eW := by rw [hfacW]
            _ = R.toFirst ≫ (P.toSecond ≫ eW) := by simp [Category.assoc]
            _ = R.toSecond ≫ eε := R.comm.symm
        have hcommZ := eq_of_factor_through_pushforward hp (p.map i) i
          (IsHomLift.map p i) kZ
          (φ := R.toSecond ≫ eε) hbase (ψW ≫ eW) (ψε ≫ eε)
          hthetaW hthetaε hfacW' hfacε'
        let Qz : PullbackCompletion p eW eε (p.map rW) (p.map rε) :=
          { apex := zz
            apex_eq := hz
            toFirst := ψW
            toSecond := ψε
            comm := hcommZ.symm
            map_toFirst := hmapψ hψW
            map_toSecond := hmapψ hψε }
        let Qx : PullbackCompletion p eW eε (p.map rW) (p.map rε) :=
          { apex := xV
            apex_eq := rfl
            toFirst := rW
            toSecond := rε
            comm := hcompε.trans hcompW.symm
            map_toFirst := rfl
            map_toSecond := rfl }
        obtain ⟨b', hbfirst, hbbase⟩ :=
          comparison_of_finrank_one p hS2 eW eε heε (by simp)
            (p.map rW) (p.map rε) hsplit' Qz Qx
        refine ⟨{
          apex := R.apex
          apex_eq := R.apex_eq
          toFirst := R.toFirst ≫ P.toFirst
          toSecond := i ≫ b'
          comm := ?_
          map_toFirst := ?_
          map_toSecond := ?_ }⟩
        · calc
            (i ≫ b') ≫ e = (i ≫ b') ≫ (rW ≫ eW) := by rw [hcompW]
            _ = (i ≫ (b' ≫ rW)) ≫ eW := by simp [Category.assoc]
            _ = (i ≫ ψW) ≫ eW := by rw [← hbfirst]
            _ = (R.toFirst ≫ P.toSecond) ≫ eW := by rw [hfacW]
            _ = R.toFirst ≫ (P.toSecond ≫ eW) := by simp [Category.assoc]
            _ = R.toFirst ≫ (P.toFirst ≫ d) :=
              congrArg (fun f => R.toFirst ≫ f) P.comm
            _ = (R.toFirst ≫ P.toFirst) ≫ d := by simp [Category.assoc]
        · rw [Functor.map_comp, R.map_toFirst, P.map_toFirst]
          simp [gP, hqf, Category.assoc]
        · rw [Functor.map_comp, hpi, hbbase]
          simp [gVR, Category.assoc]

/-- The comparison clause, by induction on `dim_k V`. -/
private theorem comparison_squareZero_finrank (n : ℕ)
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (hS2 : SchlessingerConditionS2 p)
    {x xV x₀ : F} (d : x ⟶ x₀) (e : xV ⟶ x₀)
    (he : IsSquareZeroProjection (V := V) (p.map e))
    (hV : Module.finrank k V = n)
    {AV : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : AV ⟶ p.obj x) (gV : AV ⟶ p.obj xV)
    (hpb : IsPullback gV g (p.map e) (p.map d))
    (P Q : PullbackCompletion p d e g gV) :
    ∃ b : P.apex ⟶ Q.apex, P.toFirst = b ≫ Q.toFirst ∧
      p.map b = eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm := by
  induction n using Nat.strong_induction_on generalizing V xV AV with
  | h n ih =>
    by_cases hn0 : n = 0
    · have _ : IsIso (p.map e) := isIso_squareZeroProjection_of_finrank_zero
        (p.map e) he (hV.trans hn0)
      have _ : IsIso g := hpb.flip.isIso_fst_of_isIso
      exact comparison_of_isIso_first hp d e g gV P Q
    by_cases hn1 : n = 1
    · exact comparison_of_finrank_one p hS2 d e he (hV.trans hn1) g gV hpb P Q
    have hn : 1 < n := by omega
    obtain ⟨W, b, hdimW⟩ := exists_squareZero_splitting n hV hn
    obtain ⟨xW, xε, rW, rε, eW, eε, hcompW, hcompε, heW, heε, hsplit⟩ :=
      exists_squareZero_split hp e he b
    have hcompW' : p.map rW ≫ p.map eW = p.map e := by
      rw [← Functor.map_comp, hcompW]
    obtain ⟨AW, fst, snd, q, hpbW, hqf, hqs⟩ :=
      exists_lower_base_pullback (p.map d) (p.map e) (p.map rW) (p.map eW)
        hcompW' (isSquareZeroProjection_surjective (p.map eW) heW) g gV hpb
    have hpbR := lower_base_epsilon_pullback (p.map d) (p.map e)
      (p.map rW) (p.map rε) (p.map eW) (p.map eε) hcompW'
      g gV hpb fst snd q hpbW hqf hqs hsplit
    have hdesc (T : PullbackCompletion p d e g gV) :
        ∃ (TW : PullbackCompletion p d eW fst snd) (i : T.apex ⟶ TW.apex),
          p.map i = eqToHom T.apex_eq ≫ q ≫ eqToHom TW.apex_eq.symm ∧
          i ≫ TW.toFirst = T.toFirst ∧ i ≫ TW.toSecond = T.toSecond ≫ rW := by
      apply pushforward_completion hp d eW fst snd hpbW.w
        T.toFirst (T.toSecond ≫ rW) (by simpa [Category.assoc, hcompW] using T.comm)
        (eqToHom T.apex_eq ≫ q)
      · rw [T.map_toFirst, Category.assoc, hqf]
      · rw [Functor.map_comp, T.map_toSecond, Category.assoc, ← hqs]
        simp [Category.assoc]
    obtain ⟨PW, iP, hiP, hiPf, -⟩ := hdesc P
    obtain ⟨QW, iQ, hiQ, hiQf, -⟩ := hdesc Q
    obtain ⟨bW, hbWf, hbWmap⟩ := ih (n - 1) (by omega) (V := W)
      eW heW hdimW fst snd hpbW PW QW
    let gQ : AV ⟶ p.obj QW.apex := q ≫ eqToHom QW.apex_eq.symm
    have hpbε : IsPullback (gV ≫ p.map rε) gQ (p.map eε)
        (p.map (QW.toFirst ≫ d)) := by
      apply hpbR.of_iso (Iso.refl AV) (Iso.refl _)
        (eqToIso QW.apex_eq.symm) (Iso.refl _)
      · simp
      · simp [gQ]
      · simp
      · rw [Functor.map_comp, QW.map_toFirst]
        simpa [Category.assoc] using hpbW.w
    let Pε : PullbackCompletion p (QW.toFirst ≫ d) eε gQ (gV ≫ p.map rε) :=
      { apex := P.apex
        apex_eq := P.apex_eq
        toFirst := iP ≫ bW
        toSecond := P.toSecond ≫ rε
        comm := by
          calc
            (P.toSecond ≫ rε) ≫ eε = P.toFirst ≫ d := by
              simpa [Category.assoc, hcompε] using P.comm
            _ = (iP ≫ PW.toFirst) ≫ d := by rw [hiPf]
            _ = (iP ≫ bW) ≫ (QW.toFirst ≫ d) := by rw [hbWf]; simp [Category.assoc]
        map_toFirst := by
          rw [Functor.map_comp, hiP, hbWmap]
          simp [gQ, Category.assoc]
        map_toSecond := by rw [Functor.map_comp, P.map_toSecond, Category.assoc] }
    let Qε : PullbackCompletion p (QW.toFirst ≫ d) eε gQ (gV ≫ p.map rε) :=
      { apex := Q.apex
        apex_eq := Q.apex_eq
        toFirst := iQ
        toSecond := Q.toSecond ≫ rε
        comm := by simpa [Category.assoc, hcompε, ← hiQf] using Q.comm
        map_toFirst := hiQ
        map_toSecond := by rw [Functor.map_comp, Q.map_toSecond, Category.assoc] }
    obtain ⟨c, hcf, hcmap⟩ := comparison_of_finrank_one p hS2
      (QW.toFirst ≫ d) eε heε (by simp) gQ (gV ≫ p.map rε) hpbε Pε Qε
    change iP ≫ bW = c ≫ iQ at hcf
    refine ⟨c, ?_, hcmap⟩
    calc
      P.toFirst = iP ≫ PW.toFirst := hiPf.symm
      _ = (iP ≫ bW) ≫ QW.toFirst := by rw [hbWf]; simp [Category.assoc]
      _ = (c ≫ iQ) ≫ QW.toFirst := by rw [hcf]
      _ = c ≫ Q.toFirst := by rw [Category.assoc, hiQf]

/-- The existence clause of (S2) extends from dual numbers to `k[V]` for
finite-dimensional `V`. -/
@[stacks 06HZ "existence of completions"]
theorem schlessingerConditionS2_completion_squareZero
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (hS2 : SchlessingerConditionS2 p)
    {x xV x₀ : F} (d : x ⟶ x₀) (e : xV ⟶ x₀)
    (he : IsSquareZeroProjection (V := V) (p.map e))
    {AV : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : AV ⟶ p.obj x) (gV : AV ⟶ p.obj xV)
    (hpb : IsPullback gV g (p.map e) (p.map d)) :
    Nonempty (PullbackCompletion p d e g gV) :=
  completion_squareZero_finrank (Module.finrank k V) p hp hS2 d e he rfl g gV hpb

/-- The comparison clause of (S2) extends from dual numbers to `k[V]` for
finite-dimensional `V`. -/
@[stacks 06HZ "comparison of completions"]
theorem schlessingerConditionS2_comparison_squareZero
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {V : Type z} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {F : Type u₁} [Category.{v₁} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (hS2 : SchlessingerConditionS2 p)
    {x xV x₀ : F} (d : x ⟶ x₀) (e : xV ⟶ x₀)
    (he : IsSquareZeroProjection (V := V) (p.map e))
    {AV : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (g : AV ⟶ p.obj x) (gV : AV ⟶ p.obj xV)
    (hpb : IsPullback gV g (p.map e) (p.map d))
    (P Q : PullbackCompletion p d e g gV) :
    ∃ b : P.apex ⟶ Q.apex,
      (P.toFirst = b ≫ Q.toFirst) ∧
        (p.map b = eqToHom P.apex_eq ≫ eqToHom Q.apex_eq.symm) :=
  comparison_squareZero_finrank (Module.finrank k V) p hp hS2 d e he rfl g gV hpb P Q

end

end Deformation

end
