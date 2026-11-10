module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Derivation.ToSquareZero
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Smooth.Locus
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Geometric.LocalizedSplitting
public import StacksFrontier.Deformation.SquareZero.AlgebraExtensions
public import StacksFrontier.Deformation.Examples.Geometric.LocalizationFirstOrder.LocalizedExtension
import all StacksFrontier.Deformation.Examples.Geometric.LocalizationFirstOrder.LocalizedExtension

/-!
# Relation maps of square-zero extensions

For a presentation `P` of a `k`-algebra `B` and a square-zero extension of `B` by `N`, this file
adjusts lifts from `P` by functionals on its cotangent space, maps the trivial square-zero
extension of `P` to the extension, shows that the relation map on the conormal module determines
the extension up to isomorphism, and builds the quotient of the trivial square-zero extension by
the graph of a relation map.

## Main results

* `Deformation.Examples.exists_lift_adjusted_by_cotangentSpaceMap`: a functional on the
  cotangent space changes a lift by its associated derivation.

## Implementation notes

Projecting a field out of `Stacks.Deformation.algebraExtensionProblem` needs that definition to
be unfolded, which `implicit` transparency does not do, so instance synthesis and the `rfl`
closing `rw` decline on goals that print as `X = X`. The single local attribute below opens that
definition up for the whole file.

## References

* [Stacks Project, Tag 0DZ8](https://stacks.math.columbia.edu/tag/0DZ8)
-/

@[expose] public section

namespace Deformation.Examples

open Stacks.Deformation

attribute [local implicit_reducible] Stacks.Deformation.algebraExtensionProblem

/-- A functional on the cotangent space changes a lift by its associated derivation. -/
theorem exists_lift_adjusted_by_cotangentSpaceMap
    {k B C N : Type*} [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra B C] [Algebra k C] [IsScalarTower k B C]
    [AddCommGroup N] [Module C N] [Module B N] [IsScalarTower B C N]
    (P : Algebra.Extension k B)
    (X : (algebraExtensionProblem k C N).CompatibleExtension) :
    letI : Algebra k X.B' := X.algebraA'B'
    ∀ (f : P.Ring →ₐ[k] X.B')
      (_ : ∀ p, X.toB (f p) = algebraMap B C (algebraMap P.Ring B p))
      (t : P.CotangentSpace →ₗ[B] N),
    ∃ g : P.Ring →ₐ[k] X.B',
      (∀ p, X.toB (g p) = algebraMap B C (algebraMap P.Ring B p)) ∧
      ∀ p : P.Ring,
        g p = f p +
          (X.kernelEquiv (t (1 ⊗ₜ[P.Ring] KaehlerDifferential.D k P.Ring p)) : X.B') := by
  classical
  let : Algebra k X.B' := X.algebraA'B'
  intro f hf t
  let : Algebra P.Ring X.B' := f.toRingHom.toAlgebra
  let : IsScalarTower k P.Ring X.B' :=
    IsScalarTower.of_algebraMap_eq' (by ext a; exact (f.commutes a).symm)
  let I : Ideal X.B' := RingHom.ker X.toB.toRingHom
  let : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  let : IsScalarTower P.Ring B N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module k N := Module.compHom N (algebraMap k B)
  let : IsScalarTower k P.Ring N := IsScalarTower.of_algebraMap_smul (by
    intro a n
    change (algebraMap P.Ring B (algebraMap k P.Ring a)) • n =
      (algebraMap k B a) • n
    rw [← IsScalarTower.algebraMap_apply k P.Ring B])
  let eLin : N →ₗ[P.Ring] I :=
    { toFun := X.kernelEquiv
      map_add' := X.kernelEquiv.map_add
      map_smul' := by
        intro r n
        apply Subtype.ext
        change (X.kernelEquiv ((algebraMap P.Ring B r) • n) : X.B') =
          f r * (X.kernelEquiv n : X.B')
        rw [← IsScalarTower.algebraMap_smul (R := B) (A := C)
          (algebraMap P.Ring B r) n, ← hf, kernelEquiv_smul_toB] }
  let u : Ω[P.Ring⁄k] →ₗ[P.Ring] N :=
    (t.restrictScalars P.Ring).comp (TensorProduct.mk P.Ring B Ω[P.Ring⁄k] 1)
  let dN : Derivation k P.Ring N := u.compDer (KaehlerDifferential.D k P.Ring)
  let dI : Derivation k P.Ring I := eLin.compDer dN
  let g : P.Ring →ₐ[k] X.B' := liftOfDerivationToSquareZero I X.sq_zero dI
  refine ⟨g, ?_, ?_⟩
  · intro p
    change X.toB ((dI p : X.B') + f p) = _
    have hd : X.toB (dI p : X.B') = 0 := (dI p).property
    rw [map_add, hd, zero_add, hf]
  · intro p
    change (dI p : X.B') + f p =
      f p + (X.kernelEquiv (u (KaehlerDifferential.D k P.Ring p)) : X.B')
    rw [add_comm]
    rfl

/-- The presentation map into an extension after base change, with a specified map on
kernels. -/
private theorem exists_presentationExtensionMap_baseChange
    {k B C N M : Type*} [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra B C] [Algebra k C] [IsScalarTower k B C]
    [AddCommGroup N] [Module B N] [AddCommGroup M] [Module C M]
    [Module B M] [IsScalarTower B C M]
    (P : Algebra.Extension k B)
    (Y : (algebraExtensionProblem k C M).CompatibleExtension) :
    letI : Algebra k Y.B' := Y.algebraA'B'
    letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
    letI : Module k N := Module.compHom N (algebraMap k B)
    letI : IsScalarTower k P.Ring N := IsScalarTower.of_algebraMap_smul (by
      intro a n
      change (algebraMap P.Ring B (algebraMap k P.Ring a)) • n =
        (algebraMap k B a) • n
      rw [IsScalarTower.algebraMap_apply k P.Ring B])
    letI : Module P.Ringᵐᵒᵖ N := Module.compHom N
      ({ toFun := MulOpposite.unop
         map_one' := rfl
         map_mul' := by intro x y; exact mul_comm _ _
         map_zero' := rfl
         map_add' := by intro x y; rfl } : P.Ringᵐᵒᵖ →+* P.Ring)
    letI : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
    letI : Algebra k (TrivSqZeroExt P.Ring N) := TrivSqZeroExt.algebra' k P.Ring N
    ∀ (j : N →ₗ[B] M) (f : P.Ring →ₐ[k] Y.B')
      (_ : ∀ p, Y.toB (f p) = algebraMap B C (algebraMap P.Ring B p)),
    ∃ h : TrivSqZeroExt P.Ring N →ₐ[k] Y.B',
      (∀ p, h (TrivSqZeroExt.inl p) = f p) ∧
      (∀ n, h (TrivSqZeroExt.inr n) = (Y.kernelEquiv (j n) : Y.B')) := by
  let : Algebra k Y.B' := Y.algebraA'B'
  let : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  let : Module k N := Module.compHom N (algebraMap k B)
  let : IsScalarTower k P.Ring N := IsScalarTower.of_algebraMap_smul (by
    intro a n
    change (algebraMap P.Ring B (algebraMap k P.Ring a)) • n =
      (algebraMap k B a) • n
    rw [IsScalarTower.algebraMap_apply k P.Ring B])
  let : Module P.Ringᵐᵒᵖ N := Module.compHom N
    ({ toFun := MulOpposite.unop
       map_one' := rfl
       map_mul' := by intro x y; exact mul_comm _ _
       map_zero' := rfl
       map_add' := by intro x y; rfl } : P.Ringᵐᵒᵖ →+* P.Ring)
  let : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  let : Algebra k (TrivSqZeroExt P.Ring N) := TrivSqZeroExt.algebra' k P.Ring N
  intro j f hf
  let g : N →ₗ[k] Y.B' :=
    { toFun := fun n ↦ (Y.kernelEquiv (j n) : Y.B')
      map_add' := by
        intro x y
        rw [map_add]
        exact congrArg Subtype.val (Y.kernelEquiv.map_add (j x) (j y))
      map_smul' := by
        intro a n
        change (Y.kernelEquiv (j ((algebraMap k B a) • n)) : Y.B') = _
        rw [map_smul]
        have h := kernelEquiv_smul_toB Y (algebraMap k Y.B' a) (j n)
        have ha : Y.toB (algebraMap k Y.B' a) = algebraMap k C a := Y.toB.commutes a
        rw [ha] at h
        change (Y.kernelEquiv ((algebraMap k B a) • j n) : Y.B') = _
        rw [← IsScalarTower.algebraMap_smul (R := B) (A := C)
          (algebraMap k B a) (j n)]
        rw [← IsScalarTower.algebraMap_apply k B C]
        simpa only [RingHom.id_apply, smul_eq_mul, Algebra.smul_def] using h }
  have hg (x y : N) : g x * g y = 0 := by
    have hx : (g x : Y.B') ∈ RingHom.ker Y.toB.toRingHom :=
      (Y.kernelEquiv (j x)).property
    have hy : (g y : Y.B') ∈ RingHom.ker Y.toB.toRingHom :=
      (Y.kernelEquiv (j y)).property
    have hxy := Ideal.mul_mem_mul hx hy
    rw [← pow_two, Y.sq_zero] at hxy
    exact hxy
  have hfg (p : P.Ring) (n : N) : g (p • n) = f p * g n := by
    change (Y.kernelEquiv (j ((algebraMap P.Ring B p) • n)) : Y.B') = _
    rw [map_smul]
    change (Y.kernelEquiv ((algebraMap P.Ring B p) • j n) : Y.B') = _
    rw [← IsScalarTower.algebraMap_smul (R := B) (A := C)
      (algebraMap P.Ring B p) (j n)]
    rw [← hf, kernelEquiv_smul_toB]
    rfl
  have hgf (p : P.Ring) (n : N) : g (MulOpposite.op p • n) = g n * f p := by
    rw [mul_comm]
    exact hfg p n
  let h := TrivSqZeroExt.lift f g hg hfg hgf
  exact ⟨h, fun p ↦ TrivSqZeroExt.lift_apply_inl f g hg hfg hgf p,
    fun n ↦ TrivSqZeroExt.lift_apply_inr f g hg hfg hgf n⟩

/-- Every extension admits a relation map from a formally smooth presentation. -/
private theorem exists_lift_and_cotangentMap
    {k B N : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N]
    (P : Algebra.Extension k B) [Algebra.FormallySmooth k P.Ring]
    (X : (algebraExtensionProblem k B N).CompatibleExtension) :
    letI : Algebra k X.B' := X.algebraA'B'
    ∃ (f : P.Ring →ₐ[k] X.B') (l : P.Cotangent →ₗ[B] N),
      (∀ p, X.toB (f p) = algebraMap P.Ring B p) ∧
      ∀ p : P.ker, (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X.B') = f p := by
  let : Algebra k X.B' := X.algebraA'B'
  let f : P.Ring →ₐ[k] X.B' := Algebra.FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom k P.Ring B) X.toB X.surjective ⟨2, X.sq_zero⟩
  have hf (p : P.Ring) : X.toB (f p) = algebraMap P.Ring B p :=
    Algebra.FormallySmooth.liftOfSurjective_apply
      (IsScalarTower.toAlgHom k P.Ring B) X.toB X.surjective ⟨2, X.sq_zero⟩ p
  obtain ⟨l, hl⟩ := exists_cotangentMap_of_lift P X f hf
  exact ⟨f, l, hf, hl⟩

/-- A map of relation modules gives a map of the corresponding extensions. -/
private theorem exists_compatibleAlgHom_of_cotangentMap
    {k B C N M : Type*} [CommRing k] [CommRing B] [CommRing C]
    [Algebra k B] [Algebra B C] [Algebra k C] [IsScalarTower k B C]
    [AddCommGroup N] [Module B N] [AddCommGroup M] [Module C M]
    [Module B M] [IsScalarTower B C M]
    (P : Algebra.Extension k B)
    (X : (algebraExtensionProblem k B N).CompatibleExtension)
    (Y : (algebraExtensionProblem k C M).CompatibleExtension) :
    letI : Algebra k X.B' := X.algebraA'B'
    letI : Algebra k Y.B' := Y.algebraA'B'
    ∀ (j : N →ₗ[B] M) (fX : P.Ring →ₐ[k] X.B')
      (fY : P.Ring →ₐ[k] Y.B')
      (_ : ∀ p, X.toB (fX p) = algebraMap P.Ring B p)
      (_ : ∀ p, Y.toB (fY p) = algebraMap B C (algebraMap P.Ring B p))
      (l : P.Cotangent →ₗ[B] N)
      (_ : ∀ p : P.ker,
        (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X.B') = fX p)
      (_ : ∀ p : P.ker,
        (Y.kernelEquiv (j (l (Algebra.Extension.Cotangent.mk p))) : Y.B') = fY p),
    ∃ F : X.B' →ₐ[k] Y.B',
      (∀ c, Y.toB (F c) = algebraMap B C (X.toB c)) ∧
      ∀ n, F (X.kernelEquiv n) = (Y.kernelEquiv (j n) : Y.B') := by
  classical
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k Y.B' := Y.algebraA'B'
  let : Module P.Ring N := Module.compHom N (algebraMap P.Ring B)
  let : Module k N := Module.compHom N (algebraMap k B)
  let : IsScalarTower k P.Ring N := IsScalarTower.of_algebraMap_smul (by
    intro a n
    change (algebraMap P.Ring B (algebraMap k P.Ring a)) • n =
      (algebraMap k B a) • n
    rw [IsScalarTower.algebraMap_apply k P.Ring B])
  let : Module P.Ringᵐᵒᵖ N := Module.compHom N
    ({ toFun := MulOpposite.unop
       map_one' := rfl
       map_mul' := by intro x y; exact mul_comm _ _
       map_zero' := rfl
       map_add' := by intro x y; rfl } : P.Ringᵐᵒᵖ →+* P.Ring)
  let : IsCentralScalar P.Ring N := ⟨fun _ _ ↦ rfl⟩
  let : Algebra k (TrivSqZeroExt P.Ring N) := TrivSqZeroExt.algebra' k P.Ring N
  intro j fX fY hfX hfY l hlX hlY
  obtain ⟨gX, hgX₁, hgX₂⟩ := exists_presentationExtensionMap_baseChange P X LinearMap.id fX
    (by simpa using hfX)
  replace hgX₂ : ∀ n, gX (TrivSqZeroExt.inr n) = (X.kernelEquiv n : X.B') := hgX₂
  obtain ⟨gY, hgY₁, hgY₂⟩ := exists_presentationExtensionMap_baseChange P Y j fY hfY
  have hsurj : Function.Surjective gX := by
    intro x
    obtain ⟨p, hp⟩ := P.algebraMap_surjective (X.toB x)
    have hm : x - fX p ∈ RingHom.ker X.toB.toRingHom := by
      change X.toB (x - fX p) = 0
      rw [map_sub, hfX, hp, sub_self]
    let n := X.kernelEquiv.symm ⟨x - fX p, hm⟩
    refine ⟨TrivSqZeroExt.inl p + TrivSqZeroExt.inr n, ?_⟩
    rw [map_add, hgX₁, hgX₂]
    have hn : (X.kernelEquiv n : X.B') = x - fX p :=
      congrArg Subtype.val (X.kernelEquiv.apply_symm_apply ⟨x - fX p, hm⟩)
    rw [hn]
    abel
  have hker : RingHom.ker gX.toRingHom ≤ RingHom.ker gY.toRingHom := by
    intro t ht
    have htX : gX t = 0 := ht
    have hfst : algebraMap P.Ring B t.fst = 0 := by
      have h := congrArg X.toB htX
      rw [map_zero, ← t.inl_fst_add_inr_snd_eq, map_add, hgX₁, hgX₂,
        map_add, hfX] at h
      have hk : X.toB (X.kernelEquiv t.snd : X.B') = 0 :=
        (X.kernelEquiv t.snd).property
      rwa [hk, add_zero] at h
    let p : P.ker := ⟨t.fst, hfst⟩
    have hsum : l (Algebra.Extension.Cotangent.mk p) + t.snd = 0 := by
      have hadd := congrArg Subtype.val
        (X.kernelEquiv.map_add (l (Algebra.Extension.Cotangent.mk p)) t.snd)
      change (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p) + t.snd) : X.B') =
        (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X.B') +
        (X.kernelEquiv t.snd : X.B') at hadd
      have hx := hlX p
      change (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X.B') = fX t.fst at hx
      have hsplit := congrArg gX (t.inl_fst_add_inr_snd_eq).symm
      have h : gX t = fX t.fst + (X.kernelEquiv t.snd : X.B') := by
        rw [hsplit, map_add, hgX₁, hgX₂]
      rw [hx] at hadd
      have hz : (X.kernelEquiv
          (l (Algebra.Extension.Cotangent.mk p) + t.snd) : X.B') = 0 :=
        hadd.trans (h.symm.trans htX)
      exact X.kernelEquiv.map_eq_zero_iff.mp (Subtype.ext hz)
    change gY t = 0
    rw [← t.inl_fst_add_inr_snd_eq, map_add, hgY₁, hgY₂]
    have hy := hlY p
    change (Y.kernelEquiv (j (l (Algebra.Extension.Cotangent.mk p))) : Y.B') =
      fY t.fst at hy
    rw [← hy]
    have hz : j (l (Algebra.Extension.Cotangent.mk p)) + j t.snd = 0 := by
      rw [← map_add, hsum, map_zero]
    have hadd := congrArg Subtype.val
      (Y.kernelEquiv.map_add (j (l (Algebra.Extension.Cotangent.mk p))) (j t.snd))
    rw [hz, map_zero] at hadd
    exact hadd.symm
  let F : X.B' →ₐ[k] Y.B' := AlgHom.liftOfSurjective gX hsurj gY hker
  have hq : ∀ c, Y.toB (F c) = algebraMap B C (X.toB c) := by
    intro c
    obtain ⟨t, rfl⟩ := hsurj c
    rw [AlgHom.liftOfSurjective_apply, ← t.inl_fst_add_inr_snd_eq]
    simp only [map_add, hgX₁, hgX₂, hgY₁, hgY₂, hfX, hfY]
    have hx : X.toB (X.kernelEquiv t.snd : X.B') = 0 :=
      (X.kernelEquiv t.snd).property
    have hy : Y.toB (Y.kernelEquiv (j t.snd) : Y.B') = 0 :=
      (Y.kernelEquiv (j t.snd)).property
    rw [hx, hy, map_zero]
  have hn (n : N) : F (X.kernelEquiv n) = (Y.kernelEquiv (j n) : Y.B') := by
    rw [← hgX₂ n, AlgHom.liftOfSurjective_apply, hgY₂]
  exact ⟨F, hq, hn⟩

/-- Two extensions with the same relation map for lifts from a common presentation are
isomorphic. -/
private theorem isomorphic_of_equal_cotangentMap
    {k B N : Type*} [CommRing k] [CommRing B] [Algebra k B]
    [AddCommGroup N] [Module B N]
    (P : Algebra.Extension k B)
    (X Y : (algebraExtensionProblem k B N).CompatibleExtension) :
    letI : Algebra k X.B' := X.algebraA'B'
    letI : Algebra k Y.B' := Y.algebraA'B'
    ∀ (fX : P.Ring →ₐ[k] X.B') (fY : P.Ring →ₐ[k] Y.B')
    (_ : ∀ p, X.toB (fX p) = algebraMap P.Ring B p)
    (_ : ∀ p, Y.toB (fY p) = algebraMap P.Ring B p)
    (l : P.Cotangent →ₗ[B] N)
    (_ : ∀ p : P.ker,
      (X.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : X.B') = fX p)
    (_ : ∀ p : P.ker,
      (Y.kernelEquiv (l (Algebra.Extension.Cotangent.mk p)) : Y.B') = fY p),
    SquareZeroExtensionProblem.CompatibleExtension.Isomorphic X Y := by
  let : Algebra k X.B' := X.algebraA'B'
  let : Algebra k Y.B' := Y.algebraA'B'
  intro fX fY hfX hfY l hlX hlY
  obtain ⟨F, hq, hn⟩ := exists_compatibleAlgHom_of_cotangentMap P X Y LinearMap.id fX fY hfX
    (by simpa using hfY) l hlX hlY
  exact isomorphic_of_compatibleAlgHom X Y F (AlgHom.ext fun c ↦ by simpa using hq c) hn

/-- The graph of a relation map is an ideal in the trivial square-zero extension. -/
private def squareZeroRelationIdeal
    {R N : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0) :
    Ideal (TrivSqZeroExt R N) where
  carrier := {t | ∃ i : I, t = ⟨(i : R), -l i⟩}
  zero_mem' := by
    refine ⟨0, ?_⟩
    ext <;> simp
  add_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    refine ⟨i + j, ?_⟩
    apply TrivSqZeroExt.ext
    · rfl
    · change -l i + -l j = -(l (i + j))
      rw [map_add]
      abel
  smul_mem' := by
    rintro a _ ⟨i, rfl⟩
    refine ⟨a.fst • i, ?_⟩
    apply TrivSqZeroExt.ext
    · change a.fst * i = _
      rfl
    · change a.fst • (-l i) + MulOpposite.op (i : R) • a.snd =
        -(l (a.fst • i))
      rw [hIop i i.property a.snd, add_zero, map_smul]
      simp

/-- The graph of a relation map lies in the kernel of the first projection composed with a
map killing the ideal. -/
private theorem squareZeroRelationIdeal_le_ker
    {R B N : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0)
    (f : R →+* B) (hf : I ≤ RingHom.ker f) :
    squareZeroRelationIdeal I l hIop ≤
      RingHom.ker (f.comp (TrivSqZeroExt.fstHom R R N).toRingHom) := by
  rintro _ ⟨i, rfl⟩
  change f i = 0
  exact hf i.property

/-- The quotient of the trivial square-zero extension by the graph of a relation map, mapped
to `B` by the first projection. -/
private def squareZeroRelationQuotientMap
    {R B N : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0)
    (f : R →+* B) (hf : I ≤ RingHom.ker f) :
    (TrivSqZeroExt R N ⧸ squareZeroRelationIdeal I l hIop) →+* B :=
  Ideal.Quotient.lift (squareZeroRelationIdeal I l hIop)
    (f.comp (TrivSqZeroExt.fstHom R R N).toRingHom)
    (fun _ ht ↦ squareZeroRelationIdeal_le_ker I l hIop f hf ht)

/-- The second summand lands in the kernel of
`Deformation.Examples.squareZeroRelationQuotientMap`. -/
private def squareZeroRelationKernelMap
    {R B N : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0)
    (f : R →+* B) (hf : I ≤ RingHom.ker f) :
    N →+ RingHom.ker (squareZeroRelationQuotientMap I l hIop f hf) where
  toFun n := ⟨Ideal.Quotient.mk _ (TrivSqZeroExt.inr n), by
    simp [squareZeroRelationQuotientMap]⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp

/-- The second summand identifies `N` with the kernel of
`Deformation.Examples.squareZeroRelationQuotientMap`. -/
private theorem squareZeroRelationKernelMap_bijective
    {R B N : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0)
    (f : R →+* B) (hf : I = RingHom.ker f) :
    Function.Bijective
      (squareZeroRelationKernelMap I l hIop f hf.le) := by
  constructor
  · intro n m hnm
    have h : TrivSqZeroExt.inr n - TrivSqZeroExt.inr m ∈
        squareZeroRelationIdeal I l hIop :=
      Ideal.Quotient.eq.mp (congrArg Subtype.val hnm)
    obtain ⟨i, hi⟩ := h
    have hi0 : (i : R) = 0 := by
      have hfst := congrArg TrivSqZeroExt.fst hi
      simpa using hfst.symm
    have hn : n - m = -l i := by
      have hsnd := congrArg TrivSqZeroExt.snd hi
      simpa using hsnd
    have : i = 0 := Subtype.ext hi0
    subst i
    simpa using sub_eq_zero.mp (by simpa using hn)
  · intro x
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective x.1
    have hmem : t.fst ∈ I := by
      rw [hf]
      change f t.fst = 0
      have hx := x.property
      rw [← ht] at hx
      exact hx
    let i : I := ⟨t.fst, hmem⟩
    refine ⟨t.snd + l i, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk _ (TrivSqZeroExt.inr (t.snd + l i)) = x.1
    rw [← ht]
    apply Ideal.Quotient.eq.mpr
    change TrivSqZeroExt.inr (t.snd + l i) - t ∈
      squareZeroRelationIdeal I l hIop
    refine ⟨-i, ?_⟩
    apply TrivSqZeroExt.ext
    · simp [i]
    · simp [i]

/-- The kernel of `Deformation.Examples.squareZeroRelationQuotientMap` is square zero. -/
private theorem squareZeroRelationQuotientMap_sq_zero
    {R B N : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hI : ∀ i ∈ I, ∀ n : N, i • n = 0)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0)
    (f : R →+* B) (hf : I = RingHom.ker f) :
    RingHom.ker (squareZeroRelationQuotientMap I l hIop f hf.le) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  simp only [Ideal.mem_bot]
  intro x hx y hy
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective y
  have ht : t.fst ∈ I := by
    rw [hf]
    exact hx
  have hu : u.fst ∈ I := by
    rw [hf]
    exact hy
  let j : I := ⟨u.fst, hu⟩
  change Ideal.Quotient.mk _ (t * u) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  refine ⟨t.fst • j, ?_⟩
  apply TrivSqZeroExt.ext
  · rfl
  · change t.fst • u.snd + MulOpposite.op u.fst • t.snd = -(l (t.fst • j))
    rw [hI t.fst ht u.snd, hIop u.fst hu t.snd, map_smul,
      hI t.fst ht (l j)]
    simp

/-- The identification of `N` with the kernel of
`Deformation.Examples.squareZeroRelationQuotientMap`. -/
private noncomputable def squareZeroRelationKernelAddEquiv
    {R B N : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0)
    (f : R →+* B) (hf : I = RingHom.ker f) :
    N ≃+ RingHom.ker (squareZeroRelationQuotientMap I l hIop f hf.le) :=
  AddEquiv.ofBijective (squareZeroRelationKernelMap I l hIop f hf.le)
    (squareZeroRelationKernelMap_bijective I l hIop f hf)

/-- `Deformation.Examples.squareZeroRelationQuotientMap` is surjective when `f` is. -/
private theorem squareZeroRelationQuotientMap_surjective
    {R B N : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0)
    (f : R →+* B) (hf : I ≤ RingHom.ker f) (hsurj : Function.Surjective f) :
    Function.Surjective (squareZeroRelationQuotientMap I l hIop f hf) := by
  intro b
  obtain ⟨r, rfl⟩ := hsurj b
  exact ⟨Ideal.Quotient.mk _ (TrivSqZeroExt.inl r), rfl⟩

/-- On the kernel of `Deformation.Examples.squareZeroRelationQuotientMap`, scalar
multiplication by the quotient ring agrees with multiplication by any lift. -/
private theorem squareZeroRelationKernel_smul
    {R B N : Type*} [CommRing R] [CommRing B] [AddCommGroup N]
    [Module R N] [Module B N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
    (I : Ideal R) (l : I →ₗ[R] N)
    (hIop : ∀ i ∈ I, ∀ n : N, MulOpposite.op i • n = 0)
    (f : R →+* B) (hf : I = RingHom.ker f)
    (hscalar : ∀ r : R, ∀ n : N, r • n = f r • n) :
    let q := squareZeroRelationQuotientMap I l hIop f hf.le
    let e := squareZeroRelationKernelAddEquiv I l hIop f hf
    let : Module B (RingHom.ker q) := e.symm.module B
    ∀ (c : TrivSqZeroExt R N ⧸ squareZeroRelationIdeal I l hIop) (n : N),
      q c • e n = c • e n := by
  intro q e _
  let J := squareZeroRelationIdeal I l hIop
  intro c n
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective c
  apply Subtype.ext
  change (e ((q (Ideal.Quotient.mk J t)) • e.symm (e n))).val =
    ((Ideal.Quotient.mk J t) • e n).val
  rw [e.symm_apply_apply]
  change Ideal.Quotient.mk J (TrivSqZeroExt.inr (f t.fst • n)) =
    Ideal.Quotient.mk J t * Ideal.Quotient.mk J (TrivSqZeroExt.inr n)
  rw [← map_mul]
  congr 1
  apply TrivSqZeroExt.ext
  · simp
  · change f t.fst • n = t.fst • n + MulOpposite.op (0 : R) • t.snd
    rw [← hscalar t.fst n]
    simp

end Deformation.Examples

end
