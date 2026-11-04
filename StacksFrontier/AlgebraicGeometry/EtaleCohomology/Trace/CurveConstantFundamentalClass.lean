module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.CurveTraceNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantCoefficientTrace

/-!
# The fundamental class of a smooth proper curve and `H²` with constant coefficients

Let `C` be a smooth proper curve over an algebraically closed field `K`, let `n` be invertible
in `K` and let `ζ ∈ K` be a primitive `n`-th root of unity.  The trace
`H²(C, μ_n) ≅ ℤ/n` (`Stacks.Kummer.smoothProperCurveTrace`) and `ℤ/n ≅ μ_n`, `m ↦ ζ^m`
(`Stacks.Kummer.rootsOfUnityConstantIso`) give a generator

`η = [C] ∈ H²(C, ℤ/n)`,

the class of trace `1`.  An additive map `φ : ℤ/n → A` is a morphism of constant sheaves, and
pushing `η` along it gives the class `Θ_A(φ) ∈ H²(C, A)`.  The map `Θ_A` is additive and natural
in `A`, and for `A = ℤ/n` the trace of `Θ(φ)` is `φ(1)`.  The bijectivity of `Θ_A` for every
finite `A` killed by `n` is the computation `H²(C, A) = A` of the proof of Tag 03VK.

## Main definitions

* `Stacks.EtaleCohomology.etaleConstantSheafMap` — the morphism `A_C ⟶ B_C` of an additive map.
* `Stacks.EtaleCohomology.curveFundamentalClass` — `η ∈ H²(C, ℤ/n)`.
* `Stacks.EtaleCohomology.curveConstantClass` — `Θ_A : (ℤ/n →+ A) →+ H²(C, A)`.

## Main results

* `Stacks.EtaleCohomology.curveConstantClass_naturality` — `Θ` is natural in `A`.
* `Stacks.EtaleCohomology.curveConstantTrace_curveConstantClass_zmod` — for `A = ℤ/n` the trace
  of `Θ(φ)` is `φ(1)`.
* `Stacks.EtaleCohomology.bijective_curveConstantClass_zmod` — `Θ_{ℤ/n}` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

section Map

variable (C : Scheme.{u})

/-- The morphism of constant abelian sheaves `A_C ⟶ B_C` induced by an additive map. -/
def etaleConstantSheafMap {A B : Type} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) :
    etaleConstantSheaf.{u, 0} C A ⟶ etaleConstantSheaf.{u, 0} C B :=
  (constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}).map
    (AddCommGrpCat.ofHom ((AddEquiv.ulift.{0, u + 1} (α := B)).symm.toAddMonoidHom.comp
      (φ.comp (AddEquiv.ulift.{0, u + 1} (α := A)).toAddMonoidHom)))

/-- The morphism of constant sheaves induced by `φ + ψ` is the sum of those of `φ` and `ψ`. -/
lemma etaleConstantSheafMap_add {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (φ ψ : A →+ B) :
    etaleConstantSheafMap C (φ + ψ) = etaleConstantSheafMap C φ + etaleConstantSheafMap C ψ := by
  rw [etaleConstantSheafMap, etaleConstantSheafMap, etaleConstantSheafMap, ← Functor.map_add]
  congr 1

/-- The morphism of constant sheaves induced by `ψ.comp φ` is the composite of those of `φ` and
`ψ`. -/
lemma etaleConstantSheafMap_comp {A B D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (φ : A →+ B) (ψ : B →+ D) :
    etaleConstantSheafMap C (ψ.comp φ) = etaleConstantSheafMap C φ ≫ etaleConstantSheafMap C ψ := by
  rw [etaleConstantSheafMap, etaleConstantSheafMap, etaleConstantSheafMap, ← Functor.map_comp]
  congr 1

/-- The identity of `A` induces the identity of the constant sheaf `A_C`. -/
lemma etaleConstantSheafMap_id {A : Type} [AddCommGroup A] :
    etaleConstantSheafMap C (AddMonoidHom.id A) = 𝟙 _ := by
  have h : AddCommGrpCat.ofHom ((AddEquiv.ulift.{0, u + 1} (α := A)).symm.toAddMonoidHom.comp
      ((AddMonoidHom.id A).comp (AddEquiv.ulift.{0, u + 1} (α := A)).toAddMonoidHom)) =
      𝟙 (AddCommGrpCat.of (ULift.{u + 1} A)) := by
    ext x; rfl
  rw [etaleConstantSheafMap, h, CategoryTheory.Functor.map_id]

/-- The morphism of constant sheaves induced by `k • φ` is `k` times the one induced by `φ`. -/
lemma etaleConstantSheafMap_nsmul {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (φ : A →+ B) (k : ℕ) :
    etaleConstantSheafMap C (k • φ) = k • etaleConstantSheafMap C φ := by
  induction k with
  | zero =>
    have h : AddCommGrpCat.ofHom ((AddEquiv.ulift.{0, u + 1} (α := B)).symm.toAddMonoidHom.comp
        ((0 : A →+ B).comp (AddEquiv.ulift.{0, u + 1} (α := A)).toAddMonoidHom)) = 0 := by
      ext x; simp
    simp only [zero_smul]
    rw [etaleConstantSheafMap, h, CategoryTheory.Functor.map_zero]
  | succ k ih => rw [succ_nsmul, etaleConstantSheafMap_add, ih, succ_nsmul]

end Map

/-- The zero morphism of abelian sheaves induces the zero map on cohomology. -/
lemma sheafH_map_zero {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (m : ℕ) (x : Sheaf.H.{u + 1} F m) :
    Sheaf.H.map (0 : F ⟶ G) m x = 0 := by
  have h := Sheaf.H.map_add_apply (0 : F ⟶ G) 0 x
  rw [add_zero] at h
  have h2 := congrArg (fun y => y - Sheaf.H.map (0 : F ⟶ G) m x) h
  simp only [sub_self, add_sub_cancel_right] at h2
  exact h2.symm

/-- The map on cohomology induced by `k • f` is `k` times the map induced by `f`. -/
lemma sheafH_map_nsmul {C : Type*} [Category C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})]
    {F G : Sheaf J AddCommGrpCat.{u + 1}} (f : F ⟶ G) (k : ℕ) (m : ℕ) (x : Sheaf.H.{u + 1} F m) :
    Sheaf.H.map (k • f) m x = k • Sheaf.H.map f m x := by
  induction k with
  | zero => rw [zero_smul, zero_smul, sheafH_map_zero]
  | succ k ih => rw [succ_nsmul, Sheaf.H.map_add_apply, ih, succ_nsmul]

section Class

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] {n : ℕ} (hn : IsUnit (n : K)) {ζ : K}
  (hζ : IsPrimitiveRoot ζ n)

/-- **The trace of a class of `H²(C, ℤ/n)`**, through `m ↦ ζ^m`: the composite
`H²(C, ℤ/n) ≅ H²(C, μ_n) ≅ ℤ/n`. -/
def curveConstantTrace :
    Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod n)) 2 ≃+ ZMod n :=
  (sheafHRootsOfUnityConstantAddEquiv q hζ (Stacks.Kummer.neZero_of_isUnit hn) 2).trans
    (Stacks.Kummer.smoothProperCurveTrace q hn)

/-- **The fundamental class `η = [C] ∈ H²(C, ℤ/n)`**: the class whose image in `H²(C, μ_n)` under
`m ↦ ζ^m` has trace `1`. -/
def curveFundamentalClass : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C (ZMod n)) 2 :=
  (curveConstantTrace q hn hζ).symm 1

/-- The fundamental class `η = [C]` has trace `1`. -/
lemma curveConstantTrace_curveFundamentalClass :
    curveConstantTrace q hn hζ (curveFundamentalClass q hn hζ) = 1 :=
  (curveConstantTrace q hn hζ).apply_symm_apply 1

/-- **`Θ_A : (ℤ/n →+ A) →+ H²(C, A)`**, pushing the fundamental class along `φ : ℤ/n → A`. -/
def curveConstantClass (A : Type) [AddCommGroup A] :
    (ZMod n →+ A) →+ Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C A) 2 where
  toFun φ := Sheaf.H.map (etaleConstantSheafMap C φ) 2 (curveFundamentalClass q hn hζ)
  map_zero' := by
    have h : etaleConstantSheafMap C (0 : ZMod n →+ A) = 0 := by
      simpa using etaleConstantSheafMap_nsmul C (0 : ZMod n →+ A) 0
    rw [h, sheafH_map_zero]
  map_add' φ ψ := by rw [etaleConstantSheafMap_add, Sheaf.H.map_add_apply]

/-- **`Θ` is natural in the coefficient group.** -/
lemma curveConstantClass_naturality {A B : Type} [AddCommGroup A] [AddCommGroup B] (g : A →+ B)
    (φ : ZMod n →+ A) :
    curveConstantClass q hn hζ B (g.comp φ) =
      Sheaf.H.map (etaleConstantSheafMap C g) 2 (curveConstantClass q hn hζ A φ) := by
  change Sheaf.H.map _ 2 _ = Sheaf.H.map _ 2 (Sheaf.H.map _ 2 _)
  rw [etaleConstantSheafMap_comp, Sheaf.H.map_comp_apply]

/-- Additive maps out of `ZMod n` are determined by their value at `1`. -/
private theorem addMonoidHom_zmod_ext {n : ℕ} {A : Type*} [AddCommGroup A] {φ ψ : ZMod n →+ A}
    (h : φ 1 = ψ 1) : φ = ψ := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [show ((k : ZMod n)) = (k : ℤ) • (1 : ZMod n) by simp, map_zsmul, map_zsmul, h]

/-- **For `A = ℤ/n` the trace of `Θ(φ)` is `φ(1)`.** -/
lemma curveConstantTrace_curveConstantClass_zmod (φ : ZMod n →+ ZMod n) :
    curveConstantTrace q hn hζ (curveConstantClass q hn hζ (ZMod n) φ) = φ 1 := by
  have : NeZero n := ⟨Stacks.Kummer.neZero_of_isUnit hn⟩
  have hφ : φ = (φ 1).val • AddMonoidHom.id (ZMod n) := addMonoidHom_zmod_ext (by simp)
  change curveConstantTrace q hn hζ (Sheaf.H.map (etaleConstantSheafMap C φ) 2 _) = _
  rw [hφ, etaleConstantSheafMap_nsmul, etaleConstantSheafMap_id, sheafH_map_nsmul,
    Sheaf.H.map_id_apply, map_nsmul, curveConstantTrace_curveFundamentalClass]
  simp

/-- **`Θ_{ℤ/n}` is bijective**: composed with the trace it is evaluation at `1`. -/
theorem bijective_curveConstantClass_zmod :
    Function.Bijective (curveConstantClass q hn hζ (ZMod n)) := by
  have : NeZero n := ⟨Stacks.Kummer.neZero_of_isUnit hn⟩
  have hev : Function.Bijective (fun φ : ZMod n →+ ZMod n => φ 1) := by
    exact ⟨fun φ ψ h => addMonoidHom_zmod_ext h,
      fun c => ⟨c.val • AddMonoidHom.id (ZMod n), by simp⟩⟩
  have hcomp : (curveConstantTrace q hn hζ) ∘ (curveConstantClass q hn hζ (ZMod n)) =
      (fun φ : ZMod n →+ ZMod n => φ 1) :=
    funext (curveConstantTrace_curveConstantClass_zmod q hn hζ)
  exact (Function.Bijective.of_comp_iff' (curveConstantTrace q hn hζ).bijective _).1
    (hcomp ▸ hev)

end Class

end Stacks.EtaleCohomology

end
