module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.AnnihilatorBaseChange
public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.Basic

/-!
# Flat base change for the Noether different

For an algebra `B` of finite type over `A` and a flat extension `A → A'`, both the diagonal
annihilator and the Noether different commute with the base change `A → A'`: extending the
diagonal annihilator of `B/A` along the canonical map of enveloping algebras gives the diagonal
annihilator of `A' ⊗[A] B` over `A'`, and extending the Noether different of `B/A` to
`A' ⊗[A] B` gives the Noether different of `A' ⊗[A] B` over `A'`.

## Main definitions

* `Stacks.Discriminant.envelopingBaseChange` is the canonical map from the enveloping algebra of
  `B/A` to the enveloping algebra of `A' ⊗[A] B` over `A'`.

## Main results

* `Stacks.Discriminant.map_diagonalAnnihilator_eq` states flat base change for the diagonal
  annihilator.
* `Stacks.Discriminant.map_noetherDifferent_eq` states flat base change for the Noether
  different.

## Implementation notes

The base-changed algebra is written `A' ⊗[A] B`, which is canonically isomorphic to the source's
`B ⊗[A] A'`. Finite type of `B` over `A` is what makes the kernel of the multiplication map
finitely generated — it is the Kähler differential ideal — and that finiteness is what the flat
base change of annihilators needs.

## References

* [Stacks Project, Tag 0BVM](https://stacks.math.columbia.edu/tag/0BVM)
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v w

private noncomputable def envelopingTensorEquiv (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] :
    A' ⊗[A] (B ⊗[A] B) ≃ₐ[A']
      ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)) := by
  let C := A' ⊗[A] B
  exact (Algebra.TensorProduct.assoc A A A' A' B B).symm.trans
    (Algebra.TensorProduct.cancelBaseChange A A' A' C B).symm

/-- The canonical map from the enveloping algebra of `B/A` to the enveloping
algebra after the base change `A → A'`. -/
def envelopingBaseChange (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] :
    (B ⊗[A] B) →ₐ[A] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)) :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft :
        (A' ⊗[A] B) →ₐ[A'] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B))).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B))
    (((Algebra.TensorProduct.includeRight :
        (A' ⊗[A] B) →ₐ[A'] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B))).restrictScalars A).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B))
    fun _ _ ↦ mul_comm _ _

/-- The canonical map of enveloping algebras sends a pure tensor `b₁ ⊗ b₂` to the pure tensor of
the images of `b₁` and `b₂` in the base-changed algebra. -/
lemma envelopingBaseChange_tmul (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] (b₁ b₂ : B) :
    envelopingBaseChange A B A' (b₁ ⊗ₜ[A] b₂) =
      ((1 : A') ⊗ₜ[A] b₁) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] b₂) := by
  have hsplit : envelopingBaseChange A B A' (b₁ ⊗ₜ[A] b₂) =
      (((1 : A') ⊗ₜ[A] b₁) ⊗ₜ[A'] (1 : A' ⊗[A] B)) *
        ((1 : A' ⊗[A] B) ⊗ₜ[A'] ((1 : A') ⊗ₜ[A] b₂)) := rfl
  rw [hsplit, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Multiplying out the image of a pure tensor under the canonical map of enveloping algebras
recovers the image of the product. This is the compatibility of `envelopingBaseChange` with
multiplication, stated on generators. -/
lemma lmul'_envelopingBaseChange_tmul (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] (b₁ b₂ : B) :
    (Algebra.TensorProduct.lmul' A') (envelopingBaseChange A B A' (b₁ ⊗ₜ[A] b₂)) =
      (1 : A') ⊗ₜ[A] (b₁ * b₂) := by
  rw [envelopingBaseChange_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private def envelopingBaseChangeCanonical (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] :
    (B ⊗[A] B) →ₐ[A] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)) := by
  let C := A' ⊗[A] B
  exact (((Algebra.TensorProduct.assoc A A A' A' B B).symm.trans
      (Algebra.TensorProduct.cancelBaseChange A A' A' C B).symm).toAlgHom.restrictScalars
        A).comp Algebra.TensorProduct.includeRight

private lemma envelopingBaseChange_eq_canonical (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] :
    envelopingBaseChange A B A' = envelopingBaseChangeCanonical A B A' := by
  apply Algebra.TensorProduct.ext
  · show (Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft.restrictScalars A).comp
        Algebra.TensorProduct.includeRight)
      ((Algebra.TensorProduct.includeRight.restrictScalars A).comp
        Algebra.TensorProduct.includeRight)
      (fun x y => Commute.all _ _)).comp Algebra.TensorProduct.includeLeft = _
    rw [Algebra.TensorProduct.lift_comp_includeLeft]
    refine AlgHom.ext fun b => ?_
    simp [envelopingBaseChangeCanonical,
      Algebra.TensorProduct.assoc_symm_tmul,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.one_def]
  · show (AlgHom.restrictScalars A (Algebra.TensorProduct.lift
      ((Algebra.TensorProduct.includeLeft.restrictScalars A).comp
        Algebra.TensorProduct.includeRight)
      ((Algebra.TensorProduct.includeRight.restrictScalars A).comp
        Algebra.TensorProduct.includeRight)
      (fun x y => Commute.all _ _))).comp
      Algebra.TensorProduct.includeRight = _
    rw [Algebra.TensorProduct.lift_comp_includeRight]
    refine AlgHom.ext fun b => ?_
    simp [envelopingBaseChangeCanonical,
      Algebra.TensorProduct.assoc_symm_tmul,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.one_def]

private lemma map_annihilator_ringEquiv {R S : Type*}
    [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R) :
    Ideal.map e.toRingHom I.annihilator =
      (Ideal.map e.toRingHom I).annihilator := by
  ext y
  rw [Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Submodule.mem_annihilator] at hx ⊢
    intro z hz
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp hz
    simpa [smul_eq_mul, ← map_mul] using congrArg e.toRingHom (hx a ha)
  · intro hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, Submodule.mem_annihilator.mpr fun a ha => e.injective ?_, rfl⟩
    simpa [smul_eq_mul, ← map_mul] using
      (Submodule.mem_annihilator.mp hy) (e a) (Ideal.mem_map_of_mem e.toRingHom ha)

private lemma map_ker_equiv {R S T : Type*} [CommRing R] [CommRing S]
    [Semiring T] (e : R ≃+* S) (f : S →+* T) :
    Ideal.map e.toRingHom (RingHom.ker (f.comp e.toRingHom)) = RingHom.ker f := by
  have h : RingHom.ker (f.comp e.toRingHom) = (RingHom.ker f).comap e.toRingHom := by
    ext x
    simp [RingHom.mem_ker]
  rw [h]
  exact (RingHom.ker f).map_comap_of_surjective e.toRingHom e.surjective

private lemma envelopingBaseChange_flat (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    [Module.Flat A A'] :
    (Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[A]
      (A' ⊗[A] (B ⊗[A] B))).toRingHom.Flat := by
  let R := B ⊗[A] B
  let f : R →+* (A' ⊗[A] R) := Algebra.TensorProduct.includeRight.toRingHom
  let : Algebra R (A' ⊗[A] R) := f.toAlgebra
  let : Algebra R (R ⊗[A] A') := Algebra.TensorProduct.leftAlgebra
  let e : (A' ⊗[A] R) ≃ₐ[R] R ⊗[A] A' :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm A A' R).toRingEquiv) (by
      intro r
      show Algebra.TensorProduct.comm A A' R (1 ⊗ₜ[A] r) = r ⊗ₜ[A] (1 : A')
      simp [Algebra.TensorProduct.comm_tmul])
  let : Module.Flat R (R ⊗[A] A') := Module.Flat.baseChange A R A'
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

private def envelopingBaseChangeMul (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] :
    A' ⊗[A] (B ⊗[A] B) →ₐ[A'] A' ⊗[A] B :=
  Algebra.TensorProduct.map (AlgHom.id A' A') (Algebra.TensorProduct.lmul' A)

private lemma map_diagonalKernel_baseChange (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    [Module.Flat A A'] :
    Ideal.map (Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[A]
      A' ⊗[A] (B ⊗[A] B)).toRingHom
      (RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom) =
    RingHom.ker (envelopingBaseChangeMul A B A').toRingHom := by
  let R := B ⊗[A] B
  let C := A' ⊗[A] B
  let : Algebra A' (A' ⊗[A] R) := Algebra.TensorProduct.leftAlgebra
  let μ : R →ₐ[A] B := Algebra.TensorProduct.lmul' A
  let ψ : A' ⊗[A] R →ₐ[A'] C := envelopingBaseChangeMul A B A'
  let I : Ideal R := RingHom.ker μ.toRingHom
  have hsurj : Function.Surjective μ := by
    intro b
    refine ⟨(Algebra.TensorProduct.includeLeft : B →ₐ[A] R) b, ?_⟩
    show (Algebra.TensorProduct.lmul' A) (Algebra.TensorProduct.includeLeft b) = b
    simp
  exact (Algebra.TensorProduct.lTensor_ker (R := A) (A := A') (C := R) (D := B) μ hsurj).symm

private lemma envelopingBaseChangeMul_compat (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A'] :
    (Algebra.TensorProduct.lmul' (R := A') (S := A' ⊗[A] B)).comp
      (envelopingTensorEquiv A B A').toAlgHom = envelopingBaseChangeMul A B A' := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro a
    simp [envelopingTensorEquiv, envelopingBaseChangeMul,
      Algebra.TensorProduct.assoc_symm_tmul,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.one_def]
  · apply AlgHom.ext
    intro x
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp [envelopingTensorEquiv, envelopingBaseChangeMul]
    · intro b₁ b₂
      simp [envelopingTensorEquiv, envelopingBaseChangeMul,
        Algebra.TensorProduct.assoc_symm_tmul,
        Algebra.TensorProduct.cancelBaseChange_symm_tmul]
    · intro x y hx hy
      rw [map_add, map_add, hx, hy]

/-- The annihilator of the diagonal ideal commutes with flat base change. -/
@[stacks 0BVM "part (1)"]
theorem map_diagonalAnnihilator_eq (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    [Algebra.FiniteType A B] [Module.Flat A A'] :
    (diagonalAnnihilator A B).map (envelopingBaseChange A B A') =
      diagonalAnnihilator A' (A' ⊗[A] B) := by
  let R := B ⊗[A] B
  let C := A' ⊗[A] B
  let S := A' ⊗[A] R
  let inc : R →ₐ[A] S := Algebra.TensorProduct.includeRight
  let : Algebra R S := inc.toRingHom.toAlgebra
  have : Module.Flat R S := envelopingBaseChange_flat A B A'
  let μ : R →ₐ[A] B := Algebra.TensorProduct.lmul' A
  let I : Ideal R := RingHom.ker μ.toRingHom
  have hIeq : I = KaehlerDifferential.ideal A B := by
    ext x
    simp [I, μ, KaehlerDifferential.ideal, RingHom.mem_ker]
  have hfg : I.FG := hIeq ▸ KaehlerDifferential.ideal_fg A B
  have : Module.Finite R ↥I := Module.Finite.of_fg hfg
  have hann := annihilator_map_eq_of_flat (R := R) (S := S) I
  let e : S ≃ₐ[A'] ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)) :=
    envelopingTensorEquiv A B A'
  let μ' : ((A' ⊗[A] B) ⊗[A'] (A' ⊗[A] B)) →ₐ[A'] C :=
    Algebra.TensorProduct.lmul' (R := A') (S := C)
  have htransport :
      Ideal.map e.toRingEquiv.toRingHom (Ideal.map inc.toRingHom I) =
        RingHom.ker μ'.toRingHom := by
    rw [map_diagonalKernel_baseChange A B A', ← envelopingBaseChangeMul_compat A B A']
    exact map_ker_equiv e.toRingEquiv μ'.toRingHom
  have hring :
      (((e.toAlgHom.restrictScalars A).comp inc).toRingHom) =
        e.toRingEquiv.toRingHom.comp inc.toRingHom := rfl
  have hinc : (algebraMap R S : R →+* S) = inc.toRingHom := rfl
  show Ideal.map (envelopingBaseChange A B A').toRingHom I.annihilator =
    (RingHom.ker μ'.toRingHom).annihilator
  rw [envelopingBaseChange_eq_canonical A B A',
    show envelopingBaseChangeCanonical A B A' =
      ((e.toAlgHom.restrictScalars A).comp inc) from rfl, hring,
    ← Ideal.map_map inc.toRingHom e.toRingEquiv.toRingHom]
  calc
    Ideal.map e.toRingEquiv.toRingHom (Ideal.map inc.toRingHom I.annihilator) =
        Ideal.map e.toRingEquiv.toRingHom
          ((Ideal.map inc.toRingHom I).annihilator) := by
      simpa only [hinc] using congrArg (Ideal.map e.toRingEquiv.toRingHom) hann
    _ = (Ideal.map e.toRingEquiv.toRingHom
        (Ideal.map inc.toRingHom I)).annihilator :=
      map_annihilator_ringEquiv e.toRingEquiv (Ideal.map inc.toRingHom I)
    _ = (RingHom.ker μ'.toRingHom).annihilator :=
      congrArg (fun J : Ideal _ => J.annihilator) htransport

/-- The Noether different commutes with flat base change. -/
@[stacks 0BVM "part (2)"]
theorem map_noetherDifferent_eq (A : Type u) (B : Type v) (A' : Type w)
    [CommRing A] [CommRing B] [CommRing A'] [Algebra A B] [Algebra A A']
    [Algebra.FiniteType A B] [Module.Flat A A'] :
    (noetherDifferent A B).map
        (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B) =
      noetherDifferent A' (A' ⊗[A] B) := by
  show _ = Ideal.map (Algebra.TensorProduct.lmul' A').toRingHom
    (diagonalAnnihilator A' (A' ⊗[A] B))
  rw [← map_diagonalAnnihilator_eq]
  show (Ideal.map (Algebra.TensorProduct.lmul' A).toRingHom
      (diagonalAnnihilator A B)).map
        Algebra.TensorProduct.includeRight.toRingHom =
    Ideal.map (Algebra.TensorProduct.lmul' A').toRingHom
      (Ideal.map (envelopingBaseChange A B A').toRingHom (diagonalAnnihilator A B))
  rw [Ideal.map_map (Algebra.TensorProduct.lmul' A).toRingHom
      Algebra.TensorProduct.includeRight.toRingHom,
    Ideal.map_map (envelopingBaseChange A B A').toRingHom
      (Algebra.TensorProduct.lmul' A').toRingHom]
  apply congrArg (fun f : (B ⊗[A] B) →+* (A' ⊗[A] B) =>
    Ideal.map f (diagonalAnnihilator A B))
  refine RingHom.ext fun x => TensorProduct.induction_on x ?_ ?_ ?_
  · simp
  · intro b₁ b₂
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [lmul'_envelopingBaseChange_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
      Algebra.TensorProduct.includeRight_apply]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]

end Stacks.Discriminant
