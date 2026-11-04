module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.Basic
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.AnnihilatorBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Basic

/-!
# Localization of the Noether different

Let `A → B'` be of finite type and let `B' → B` be a ring map whose induced morphism of spectra
is an open immersion. Then the diagonal annihilator of `B/A` is obtained from that of `B'/A` by
base change along `B' → B`: the canonical map `B ⊗[B'] J' → B ⊗[A] B` is injective with image
exactly the diagonal annihilator of `B/A`. Consequently the Noether different of `B/A` is the
extension of the Noether different of `B'/A`.

## Main definitions

* `Stacks.Discriminant.diagonalAnnihilatorBaseChange` is the canonical map from the base change
  of the diagonal annihilator of `B'/A` to the enveloping algebra of `B/A`.

## Main results

* `Stacks.Discriminant.diagonalAnnihilatorBaseChange_injective` and
  `Stacks.Discriminant.range_diagonalAnnihilatorBaseChange` identify the diagonal annihilator of
  `B/A` with the base change of that of `B'/A`.
* `Stacks.Discriminant.noetherDifferent_eq_map` states that the Noether different commutes with
  the given open localization.

## Implementation notes

The identification is expressed by the injectivity and the range of the canonical map
`B ⊗[B'] J' → B ⊗[A] B`; together these identify `J` canonically with `B ⊗[B'] J'`, which is the
type-correct form of the source's equality. The open-immersion hypothesis is used twice: it makes
`B'` → `B` flat, and it makes it a ring epimorphism, the latter being what identifies the two
Kähler differential ideals.

## References

* [Stacks Project, Tag 0BVN](https://stacks.math.columbia.edu/tag/0BVN)
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory

namespace Stacks.Discriminant

universe u v w

/-- The canonical map from the base change of the diagonal annihilator for `B'/A` to the
enveloping algebra of `B/A`. On pure tensors it sends `b ⊗ j` to the product of `b ⊗ 1`
with the image of `j`. -/
def diagonalAnnihilatorBaseChange (A : Type u) (B' : Type v) (B : Type w)
    [CommRing A] [CommRing B'] [CommRing B]
    [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B] :
    B ⊗[B'] (↑(diagonalAnnihilator A B')) →ₗ[B] B ⊗[A] B := by
  let g : ↑(diagonalAnnihilator A B') →ₗ[B'] B ⊗[A] B :=
    { toFun := fun j ↦ Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom A B' B) (IsScalarTower.toAlgHom A B' B) j.1
      map_add' := by intro; simp
      map_smul' := by
        intro
        simp [Algebra.smul_def, mul_comm] }
  exact TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton B _ g)

variable (A : Type u) (B' : Type v) (B : Type w)
  [CommRing A] [CommRing B'] [CommRing B]
  [Algebra A B'] [Algebra B' B] [Algebra A B] [IsScalarTower A B' B]

private theorem flat_of_openImmersion
    (h : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap B' B).ulift.{max v w, max v w}))) :
    Module.Flat B' B := by
  let _ := h
  have : AlgebraicGeometry.Flat
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap B' B).ulift.{max v w, max v w})) := inferInstance
  exact RingHom.flat_algebraMap_iff.mp
    (RingHom.Flat.ulift_iff.mp (AlgebraicGeometry.Flat.SpecMap_iff.mp this))

private theorem finite_diagonalIdeal [Algebra.FiniteType A B'] :
    Module.Finite (B' ⊗[A] B')
      ↥(RingHom.ker (Algebra.TensorProduct.lmul' A :
        B' ⊗[A] B' →ₐ[A] B').toRingHom) :=
  Module.Finite.of_fg (KaehlerDifferential.ideal_fg A B')

private theorem epi_of_openImmersion
    (h : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap B' B).ulift.{max v w, max v w}))) :
    Algebra.IsEpi B' B := by
  let _ := h
  let f : ULift.{max v w} B' →+* ULift.{max v w} B := (algebraMap B' B).ulift
  have hm : CategoryTheory.Mono
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f)) := inferInstance
  have he : CategoryTheory.Epi (CommRingCat.ofHom f) :=
    (CategoryTheory.op_mono_iff _).mp
      ((AlgebraicGeometry.Scheme.Spec).mono_of_mono_map (by simpa using hm))
  let p : B →+* B ⊗[B'] B :=
    (Algebra.TensorProduct.includeLeft : B →ₐ[B'] B ⊗[B'] B).toRingHom
  let q : B →+* B ⊗[B'] B :=
    (Algebra.TensorProduct.includeRight : B →ₐ[B'] B ⊗[B'] B).toRingHom
  have hpc : CommRingCat.ofHom f ≫ CommRingCat.ofHom p.ulift.{max v w, max v w} =
      CommRingCat.ofHom f ≫ CommRingCat.ofHom q.ulift.{max v w, max v w} := by
    ext x
    simp [f, p, q]
  have hpq : CommRingCat.ofHom p.ulift.{max v w, max v w} =
      CommRingCat.ofHom q.ulift.{max v w, max v w} :=
    (CategoryTheory.cancel_epi _).mp hpc
  refine (Algebra.isEpi_iff_forall_one_tmul_eq B' B).mpr fun b => ?_
  have hb : ULift.up (b ⊗ₜ[B'] (1 : B)) = ULift.up ((1 : B) ⊗ₜ[B'] b) :=
    congrArg (fun z : ULift.{max v w} B →+* ULift.{max v w} (B ⊗[B'] B) => z (ULift.up b))
      (congrArg CommRingCat.Hom.hom hpq)
  exact ULift.up_injective hb.symm

private theorem flat_tensorSquare [Module.Flat B' B] :
    (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom A B' B)
      (IsScalarTower.toAlgHom A B' B)).toRingHom.Flat := by
  apply RingHom.Flat.tensorProductMap <;> exact RingHom.flat_algebraMap_iff.mpr inferInstance

private theorem ringHom_ext_of_isEpi
    {R : Type*} {S : Type*} {T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra.IsEpi R S]
    (p q : S →+* T)
    (h : p.comp (algebraMap R S) = q.comp (algebraMap R S)) : p = q := by
  let _ : Algebra R T := (p.comp (algebraMap R S)).toAlgebra
  let pa : S →ₐ[R] T := { toRingHom := p, commutes' := fun _ => rfl }
  let qa : S →ₐ[R] T :=
    { toRingHom := q, commutes' := fun r => congrFun (congrArg DFunLike.coe h.symm) r }
  let f : S ⊗[R] S →ₐ[R] T :=
    Algebra.TensorProduct.lift pa qa (fun _ _ => mul_comm _ _)
  ext s
  calc
    p s = f (s ⊗ₜ[R] 1) := by
      show p s = pa s * qa 1
      simp [pa, qa]
    _ = f (1 ⊗ₜ[R] s) :=
      congrArg f ((Algebra.isEpi_iff_forall_one_tmul_eq R S).mp inferInstance s).symm
    _ = q s := by
      show pa 1 * qa s = q s
      simp [pa, qa]

private theorem mul_diagonal_tensor_map (x : B' ⊗[A] B') :
    (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B)
        (Algebra.TensorProduct.map
          (IsScalarTower.toAlgHom A B' B) (IsScalarTower.toAlgHom A B' B) x) =
      algebraMap B' B ((Algebra.TensorProduct.lmul' A :
        B' ⊗[A] B' →ₐ[A] B') x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.lmul'_apply_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem diagonalIdeal_map_eq [Algebra.IsEpi B' B] :
    Ideal.map (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom A B' B) (IsScalarTower.toAlgHom A B' B))
        (KaehlerDifferential.ideal A B') = KaehlerDifferential.ideal A B := by
  let g : (B' ⊗[A] B') →ₐ[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom A B' B) (IsScalarTower.toAlgHom A B' B)
  let K : Ideal (B ⊗[A] B) := Ideal.map g (KaehlerDifferential.ideal A B')
  show K = KaehlerDifferential.ideal A B
  apply le_antisymm
  · refine Ideal.map_le_iff_le_comap.mpr fun x hx => ?_
    show (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B) (g x) = 0
    rw [mul_diagonal_tensor_map A B' B x]
    exact map_zero (algebraMap B' B) ▸ congrArg (algebraMap B' B)
      (RingHom.mem_ker.mp hx)
  · rw [← KaehlerDifferential.span_range_eq_ideal A B, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    let Q : Type _ := (B ⊗[A] B) ⧸ K
    let q₀ : (B ⊗[A] B) →+* Q := Ideal.Quotient.mk K
    let p : B →+* Q := q₀.comp (Algebra.TensorProduct.includeRight :
      B →ₐ[A] B ⊗[A] B).toRingHom
    let q : B →+* Q := q₀.comp (Algebra.TensorProduct.includeLeft :
      B →ₐ[A] B ⊗[A] B).toRingHom
    have hpq' : p.comp (algebraMap B' B) = q.comp (algebraMap B' B) := by
      ext r
      refine Ideal.Quotient.eq.mpr ?_
      have hrK : g ((1 : B') ⊗ₜ[A] r - r ⊗ₜ[A] (1 : B')) ∈ K :=
        Ideal.mem_map_of_mem g (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal A r)
      simpa [g, p, q, q₀] using hrK
    exact Ideal.Quotient.eq.mp (congrArg (fun z : B →+* Q => z b) (ringHom_ext_of_isEpi p q hpq'))

private theorem diagonalAnnihilator_map_eq
    [Algebra.FiniteType A B'] [Module.Flat B' B] [Algebra.IsEpi B' B] :
    Ideal.map (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom A B' B) (IsScalarTower.toAlgHom A B' B))
        (diagonalAnnihilator A B') =
      diagonalAnnihilator A B := by
  let g : (B' ⊗[A] B') →ₐ[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom A B' B) (IsScalarTower.toAlgHom A B' B)
  let _ : Algebra (B' ⊗[A] B') (B ⊗[A] B) := g.toRingHom.toAlgebra
  have : Module.Flat (B' ⊗[A] B') (B ⊗[A] B) :=
    RingHom.flat_algebraMap_iff.mp (flat_tensorSquare A B' B)
  have : Module.Finite (B' ⊗[A] B')
      ↥(KaehlerDifferential.ideal A B') := finite_diagonalIdeal A B'
  show Ideal.map g (KaehlerDifferential.ideal A B').annihilator =
    (KaehlerDifferential.ideal A B).annihilator
  rw [← diagonalIdeal_map_eq A B' B]
  exact annihilator_map_eq_of_flat (S := B ⊗[A] B)
    (KaehlerDifferential.ideal A B')

/-- Elements of the diagonal annihilator absorb `r` as `(lmul' r) ⊗ 1`. -/
private theorem mul_eq_lmul'_tmul_one_mul {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : S ⊗[R] S) {j : S ⊗[R] S} (hj : j ∈ diagonalAnnihilator R S) :
    r * j = ((Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S) r ⊗ₜ[R] (1 : S)) * j := by
  have hr : r - (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S) r ⊗ₜ[R] (1 : S) ∈
      KaehlerDifferential.ideal R S := by
    show (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S)
      (r - (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S) r ⊗ₜ[R] (1 : S)) = 0
    simp [Algebra.TensorProduct.lmul'_apply_tmul]
  linear_combination (Submodule.mem_annihilator.mp hj) _ hr

private theorem diagonalAnnihilator_smul
    (r : B' ⊗[A] B')
    (j : ↥(diagonalAnnihilator A B')) :
    r • j = (Algebra.TensorProduct.lmul' A :
      B' ⊗[A] B' →ₐ[A] B') r • j := by
  apply Subtype.ext
  show r * j.1 =
    (Algebra.TensorProduct.lmul' A : B' ⊗[A] B' →ₐ[A] B') r • j.1
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  exact mul_eq_lmul'_tmul_one_mul r j.2

/-- The `B' ⊗[A] B'`-algebra structure on `B ⊗[A] B` given by the tensor square of the
structure map `B' → B`. -/
local instance diagonalTensorSquareAlgebra :
    Algebra (B' ⊗[A] B') (B ⊗[A] B) :=
  (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom A B' B)
    (IsScalarTower.toAlgHom A B' B)).toRingHom.toAlgebra

private def diagonalBaseChangeToFull :
    B ⊗[B'] ↥(diagonalAnnihilator A B') →ₗ[B]
      (B ⊗[A] B) ⊗[B' ⊗[A] B']
        ↥(diagonalAnnihilator A B') := by
  let R := B' ⊗[A] B'
  let C := B ⊗[A] B
  let M := ↥(diagonalAnnihilator A B')
  let l : M →ₗ[B'] C ⊗[R] M := {
    toFun := fun j => (1 : C) ⊗ₜ[R] j
    map_add' := by intro x y; simp only [TensorProduct.tmul_add]
    map_smul' := by
      intro r j
      have haction : ((r ⊗ₜ[A] (1 : B') : R) • j) = r • j := by
        simpa [Algebra.TensorProduct.lmul'_apply_tmul] using
          (diagonalAnnihilator_smul A B' (r ⊗ₜ[A] (1 : B')) j)
      calc
        (1 : C) ⊗ₜ[R] (r • j) =
            (1 : C) ⊗ₜ[R] ((r ⊗ₜ[A] (1 : B') : R) • j) := by rw [haction]
        _ = ((r ⊗ₜ[A] (1 : B') : R) • (1 : C)) ⊗ₜ[R] j :=
          (TensorProduct.smul_tmul _ _ _).symm
        _ = r • ((1 : C) ⊗ₜ[R] j) := by
          congr 1
          simp only [Algebra.smul_def, mul_one]
          change (Algebra.TensorProduct.map
            (IsScalarTower.toAlgHom A B' B)
            (IsScalarTower.toAlgHom A B' B)) (r ⊗ₜ[A] (1 : B')) =
              (algebraMap B' B r) ⊗ₜ[A] (1 : B)
          rw [Algebra.TensorProduct.map_tmul]
          simp
  }
  exact TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton B _ l)

private def diagonalBaseChangeFromFull :
    ((B ⊗[A] B) ⊗[B' ⊗[A] B']
      ↥(diagonalAnnihilator A B')) →
      B ⊗[B'] ↥(diagonalAnnihilator A B') := by
  let R := B' ⊗[A] B'
  let C := B ⊗[A] B
  let M := ↥(diagonalAnnihilator A B')
  let m₀ : R →+* B' := (Algebra.TensorProduct.lmul' A).toRingHom
  let m : C →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  let π : R →+* B := (algebraMap B' B).comp m₀
  let _ : Module R B := Module.compHom B π
  let _ : SMulCommClass B' R B := SMul.comp.smulCommClass' π
  let _ : SMulCommClass R B' B := SMul.comp.smulCommClass π
  let _ : TensorProduct.CompatibleSMul B' R B M := ⟨by
    intro r b j
    have hr : r • j = m₀ r • j := diagonalAnnihilator_smul A B' r j
    rw [hr]
    change ((π r) * b) ⊗ₜ[B'] j = b ⊗ₜ[B'] (m₀ r • j)
    change ((algebraMap B' B (m₀ r)) * b) ⊗ₜ[B'] j = _
    simpa only [Algebra.smul_def] using (TensorProduct.smul_tmul (m₀ r) b j)⟩
  let ml : C →ₗ[R] B := {
    toFun := m
    map_add' := by intro; simp
    map_smul' := by
      intro r c
      change m ((algebraMap R C r) * c) = π r * m c
      rw [map_mul]
      congr 1
      exact mul_diagonal_tensor_map A B' B r
  }
  exact fun y => (TensorProduct.mapOfCompatibleSMul B' R B' B M)
    ((TensorProduct.map ml (LinearMap.id : M →ₗ[R] M)) y)

private theorem diagonalBaseChangeFromFull_leftInverse :
    Function.LeftInverse (diagonalBaseChangeFromFull A B' B)
      (diagonalBaseChangeToFull A B' B) := by
  let R := B' ⊗[A] B'
  let m₀ : R →+* B' := (Algebra.TensorProduct.lmul' A).toRingHom
  let π : R →+* B := (algebraMap B' B).comp m₀
  let _ : Module R B := Module.compHom B π
  let _ : SMulCommClass B' R B := SMul.comp.smulCommClass' π
  let _ : SMulCommClass R B' B := SMul.comp.smulCommClass π
  let _ : TensorProduct.CompatibleSMul B' R B
      ↥(diagonalAnnihilator A B') := ⟨by
    intro r b j
    rw [diagonalAnnihilator_smul A B' r j]
    show ((algebraMap B' B (m₀ r)) * b) ⊗ₜ[B'] j = b ⊗ₜ[B'] (m₀ r • j)
    simpa only [Algebra.smul_def] using (TensorProduct.smul_tmul (m₀ r) b j)⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
    show (TensorProduct.mapOfCompatibleSMul B' (B' ⊗[A] B') B' B
      ↥(diagonalAnnihilator A B')) 0 = 0
    exact map_zero _
  | tmul b j =>
    have hv : diagonalBaseChangeToFull A B' B (b ⊗ₜ[B'] j) =
        ((b ⊗ₜ[A] (1 : B)) : B ⊗[A] B) ⊗ₜ[R] j := by
      simp only [diagonalBaseChangeToFull, LinearMap.toSpanSingleton_apply,
        TensorProduct.AlgebraTensorModule.lift_tmul]
      show b • ((1 : B ⊗[A] B) ⊗ₜ[R] j) = _
      rw [TensorProduct.smul_tmul']
      congr 1
      simp [Algebra.smul_def]
    rw [hv]
    unfold diagonalBaseChangeFromFull
    rw [TensorProduct.map_tmul, TensorProduct.mapOfCompatibleSMul_tmul]
    show ((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B)
      (b ⊗ₜ[A] (1 : B))) ⊗ₜ[B'] j = b ⊗ₜ[B'] j
    simp [Algebra.TensorProduct.lmul'_apply_tmul]
  | add x y hx hy =>
    show (TensorProduct.mapOfCompatibleSMul B' (B' ⊗[A] B') B' B
      ↥(diagonalAnnihilator A B'))
      ((TensorProduct.map _ (LinearMap.id : _ →ₗ[B' ⊗[A] B'] _))
        ((diagonalBaseChangeToFull A B' B) (x + y))) = x + y
    simp only [map_add]
    exact congrArg₂ (· + ·) hx hy

private theorem idealBaseChangeMap_diagonalBaseChangeToFull
    [Module.Flat B' B] (x : B ⊗[B'] ↥(diagonalAnnihilator A B')) :
    idealBaseChangeMap (S := B ⊗[A] B)
      (diagonalAnnihilator A B')
      (diagonalBaseChangeToFull A B' B x) =
        diagonalAnnihilatorBaseChange A B' B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b j =>
    simp [diagonalBaseChangeToFull, idealBaseChangeMap,
      diagonalAnnihilatorBaseChange, LinearMap.toSpanSingleton,
      TensorProduct.AlgebraTensorModule.rid]
    simp only [Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy => simp [map_add, hx, hy]

/-- The canonical base-change map on diagonal annihilators is injective under the open
localization hypotheses. This is the injectivity implicit in the identification in part (1). -/
@[stacks 0BVN "part (1), injectivity"]
theorem diagonalAnnihilatorBaseChange_injective
    [Algebra.FiniteType A B']
    (h : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap B' B).ulift.{max v w, max v w}))) :
    Function.Injective (diagonalAnnihilatorBaseChange A B' B) := by
  let _ : Module.Flat B' B := flat_of_openImmersion B' B h
  let _ : Algebra.IsEpi B' B := epi_of_openImmersion B' B h
  let _ : Module.Flat (B' ⊗[A] B') (B ⊗[A] B) :=
    RingHom.flat_algebraMap_iff.mp (flat_tensorSquare A B' B)
  intro x y hxy
  refine (diagonalBaseChangeFromFull_leftInverse A B' B).injective
    (idealBaseChangeMap_injective (S := B ⊗[A] B) (diagonalAnnihilator A B') ?_)
  simpa only [idealBaseChangeMap_diagonalBaseChangeToFull] using hxy

/-- Under the open localization hypotheses, the image of `B ⊗[B'] J'` under the canonical
map is exactly the diagonal annihilator `J` for `B/A`. -/
@[stacks 0BVN "part (1), image"]
theorem range_diagonalAnnihilatorBaseChange
    [Algebra.FiniteType A B']
    (h : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap B' B).ulift.{max v w, max v w}))) :
    LinearMap.range (diagonalAnnihilatorBaseChange A B' B) =
      (diagonalAnnihilator A B).restrictScalars B := by
  let _ : Module.Flat B' B := flat_of_openImmersion B' B h
  let _ : Algebra.IsEpi B' B := epi_of_openImmersion B' B h
  let f := diagonalAnnihilatorBaseChange A B' B
  let g : (B' ⊗[A] B') →ₐ[A] (B ⊗[A] B) :=
    Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom A B' B) (IsScalarTower.toAlgHom A B' B)
  let m : B ⊗[A] B →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  let J' : Ideal (B' ⊗[A] B') := diagonalAnnihilator A B'
  let J : Ideal (B ⊗[A] B) := diagonalAnnihilator A B
  have hle : f.range ≤ J.restrictScalars B := by
    have hall : ∀ y : B ⊗[B'] ↥J', f y ∈ J := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact J.zero_mem
      | tmul b j =>
        have hj : g j.1 ∈ J := by
          show g j.1 ∈ diagonalAnnihilator A B
          rw [← diagonalAnnihilator_map_eq A B' B]
          exact Ideal.mem_map_of_mem g j.2
        simpa [f, diagonalAnnihilatorBaseChange, LinearMap.toSpanSingleton]
          using (J.restrictScalars B).smul_mem b hj
      | add x y hx hy => simpa only [map_add] using J.add_mem hx hy
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    exact hall y
  let K : Ideal (B ⊗[A] B) := {
    carrier := f.range
    zero_mem' := f.range.zero_mem
    add_mem' := fun hx hy => f.range.add_mem hx hy
    smul_mem' := by
      intro c x hx
      have hxJ : x ∈ J := hle hx
      have hc' : c * x = ((m c) ⊗ₜ[A] (1 : B)) * x := by
        exact mul_eq_lmul'_tmul_one_mul c hxJ
      rw [smul_eq_mul, hc']
      simpa [Algebra.smul_def] using f.range.smul_mem (m c) hx
  }
  refine le_antisymm hle ?_
  show diagonalAnnihilator A B ≤ K
  rw [← diagonalAnnihilator_map_eq A B' B]
  refine Ideal.map_le_iff_le_comap.mpr fun j hj => ?_
  show g j ∈ f.range
  refine ⟨(1 : B) ⊗ₜ[B'] (⟨j, hj⟩ : ↥J'), ?_⟩
  simp [f, g, diagonalAnnihilatorBaseChange, LinearMap.toSpanSingleton]

/-- Under the open localization hypotheses, the Noether different of `B/A` is the extension
to `B` of the Noether different of `B'/A`. -/
@[stacks 0BVN "part (2)"]
theorem noetherDifferent_eq_map
    [Algebra.FiniteType A B']
    (h : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap B' B).ulift.{max v w, max v w}))) :
    noetherDifferent A B =
      Ideal.map (algebraMap B' B)
        (noetherDifferent A B') := by
  let _ : Module.Flat B' B := flat_of_openImmersion B' B h
  let _ : Algebra.IsEpi B' B := epi_of_openImmersion B' B h
  show Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
      (diagonalAnnihilator A B) =
    Ideal.map (algebraMap B' B)
      (Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
        (diagonalAnnihilator A B'))
  rw [← diagonalAnnihilator_map_eq A B' B]
  show Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
      (Ideal.map (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom A B' B)
        (IsScalarTower.toAlgHom A B' B)).toRingHom
        (diagonalAnnihilator A B')) = _
  rw [Ideal.map_map, Ideal.map_map]
  have hm : (Algebra.TensorProduct.lmul' A).toRingHom.comp
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A B' B)
        (IsScalarTower.toAlgHom A B' B)).toRingHom =
      (algebraMap B' B).comp (Algebra.TensorProduct.lmul' A).toRingHom :=
    RingHom.ext (fun x => mul_diagonal_tensor_map A B' B x)
  exact congrArg (fun f : (B' ⊗[A] B') →+* B =>
    Ideal.map f (diagonalAnnihilator A B')) hm

end Stacks.Discriminant
