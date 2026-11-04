module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveConstantFundamentalClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.TorsionOfConstructible

/-!
# `H²(C, A) = A` for a smooth proper curve and a finite group `A` killed by `n`

Let `C` be a smooth proper curve over an algebraically closed field `K`, `n` invertible in `K`,
`ζ` a primitive `n`-th root of unity and `A` a finite abelian group killed by `n`.  The class map
`Θ_A : Hom(ℤ/n, A) → H²(C, A)`, `φ ↦ φ_*[C]` (`Stacks.EtaleCohomology.curveConstantClass`), is
bijective.

It is bijective for `A = ℤ/n` (`Stacks.EtaleCohomology.bijective_curveConstantClass_zmod`), hence
for `(ℤ/n)^m` by additivity.  For a general `A` choose a presentation
`0 → K → (ℤ/n)^m → A → 0`; the constant sheaf functor is exact, and `H³(C, K) = 0` by Tag 03SC
(Situation 0A52, statement (1)), so `H²(C, -)` is right exact on it.  Since `Hom(ℤ/n, -)` is exact
on groups killed by `n`, a four-lemma chase gives the claim.

## Main results

* `Stacks.EtaleCohomology.bijective_curveConstantClass` — `Θ_A` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] {n : ℕ} (hn : IsUnit (n : K)) {ζ : K}
  (hζ : IsPrimitiveRoot ζ n)

omit [IsAlgClosed K] [IsCurve K q] [Smooth q] [IsProper q] in
/-- The map on `Hᵐ` induced by `ψ ∘ φ` on constant sheaves is the composite of the maps induced by
`φ` and by `ψ`. -/
lemma sheafH_map_etaleConstantSheafMap_comp_apply {A B D : Type} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup D] (φ : A →+ B) (ψ : B →+ D) (m : ℕ)
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C A) m) :
    Sheaf.H.map (etaleConstantSheafMap C ψ) m (Sheaf.H.map (etaleConstantSheafMap C φ) m x) =
      Sheaf.H.map (etaleConstantSheafMap C (ψ.comp φ)) m x := by
  rw [etaleConstantSheafMap_comp, Sheaf.H.map_comp_apply]

omit [IsAlgClosed K] [IsCurve K q] [Smooth q] [IsProper q] in
/-- The identity of `A` induces the identity on `Hᵐ(C, A)`. -/
lemma sheafH_map_etaleConstantSheafMap_id_apply {A : Type} [AddCommGroup A] (m : ℕ)
    (x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C A) m) :
    Sheaf.H.map (etaleConstantSheafMap C (AddMonoidHom.id A)) m x = x := by
  rw [etaleConstantSheafMap_id, Sheaf.H.map_id_apply]

/-- `Θ` bijective transports along an additive equivalence. -/
theorem bijective_curveConstantClass_of_addEquiv {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (h : Function.Bijective (curveConstantClass q hn hζ A)) :
    Function.Bijective (curveConstantClass q hn hζ B) := by
  have key : ∀ ψ : ZMod n →+ B, curveConstantClass q hn hζ B ψ =
      Sheaf.H.map (etaleConstantSheafMap C e.toAddMonoidHom) 2
        (curveConstantClass q hn hζ A (e.symm.toAddMonoidHom.comp ψ)) := by
    intro ψ
    rw [← curveConstantClass_naturality]
    congr 1
    ext x
    simp
  have hinv : ∀ y : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C B) 2,
      Sheaf.H.map (etaleConstantSheafMap C e.toAddMonoidHom) 2
        (Sheaf.H.map (etaleConstantSheafMap C e.symm.toAddMonoidHom) 2 y) = y := by
    intro y
    rw [sheafH_map_etaleConstantSheafMap_comp_apply]
    convert sheafH_map_etaleConstantSheafMap_id_apply 2 y
    ext x
    simp
  have hinv' : ∀ x : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C A) 2,
      Sheaf.H.map (etaleConstantSheafMap C e.symm.toAddMonoidHom) 2
        (Sheaf.H.map (etaleConstantSheafMap C e.toAddMonoidHom) 2 x) = x := by
    intro x
    rw [sheafH_map_etaleConstantSheafMap_comp_apply]
    convert sheafH_map_etaleConstantSheafMap_id_apply 2 x
    ext a
    simp
  refine ⟨fun ψ ψ' hψ => ?_, fun y => ?_⟩
  · rw [key, key] at hψ
    have h2 := congrArg (Sheaf.H.map (etaleConstantSheafMap C e.symm.toAddMonoidHom) 2) hψ
    rw [hinv', hinv'] at h2
    ext x
    simpa using congrArg (fun φ : ZMod n →+ A => e (φ x)) (h.1 h2)
  · obtain ⟨φ, hφ⟩ := h.2 (Sheaf.H.map (etaleConstantSheafMap C e.symm.toAddMonoidHom) 2 y)
    refine ⟨e.toAddMonoidHom.comp φ, ?_⟩
    rw [curveConstantClass_naturality, hφ, hinv]

/-- `Θ` bijective for `A` and `B` gives `Θ` bijective for `A × B`. -/
theorem bijective_curveConstantClass_prod {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (hA : Function.Bijective (curveConstantClass q hn hζ A))
    (hB : Function.Bijective (curveConstantClass q hn hζ B)) :
    Function.Bijective (curveConstantClass q hn hζ (A × B)) := by
  have hid : (AddMonoidHom.inl A B).comp (AddMonoidHom.fst A B) +
      (AddMonoidHom.inr A B).comp (AddMonoidHom.snd A B) = AddMonoidHom.id (A × B) := by
    ext x <;> simp
  refine ⟨fun φ φ' h => ?_, fun y => ?_⟩
  · have h1 := hA.1 (by
      rw [curveConstantClass_naturality, curveConstantClass_naturality, h] :
        curveConstantClass q hn hζ A ((AddMonoidHom.fst A B).comp φ) =
          curveConstantClass q hn hζ A ((AddMonoidHom.fst A B).comp φ'))
    have h2 := hB.1 (by
      rw [curveConstantClass_naturality, curveConstantClass_naturality, h] :
        curveConstantClass q hn hζ B ((AddMonoidHom.snd A B).comp φ) =
          curveConstantClass q hn hζ B ((AddMonoidHom.snd A B).comp φ'))
    ext x
    · exact DFunLike.congr_fun h1 x
    · exact DFunLike.congr_fun h2 x
  · obtain ⟨a, ha⟩ := hA.2 (Sheaf.H.map (etaleConstantSheafMap C (AddMonoidHom.fst A B)) 2 y)
    obtain ⟨b, hb⟩ := hB.2 (Sheaf.H.map (etaleConstantSheafMap C (AddMonoidHom.snd A B)) 2 y)
    refine ⟨(AddMonoidHom.inl A B).comp a + (AddMonoidHom.inr A B).comp b, ?_⟩
    rw [map_add, curveConstantClass_naturality, curveConstantClass_naturality, ha, hb,
      sheafH_map_etaleConstantSheafMap_comp_apply, sheafH_map_etaleConstantSheafMap_comp_apply,
      ← Sheaf.H.map_add_apply, ← etaleConstantSheafMap_add, hid,
      sheafH_map_etaleConstantSheafMap_id_apply]

/-- `Θ` is bijective for a trivial group. -/
theorem bijective_curveConstantClass_of_subsingleton {A : Type} [AddCommGroup A]
    [Subsingleton A] : Function.Bijective (curveConstantClass q hn hζ A) := by
  have hzero : ∀ y : Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C A) 2, y = 0 := by
    intro y
    rw [← sheafH_map_etaleConstantSheafMap_id_apply 2 y,
      show AddMonoidHom.id A = 0 from AddMonoidHom.ext fun _ => Subsingleton.elim _ _]
    have h0 : etaleConstantSheafMap C (0 : A →+ A) = 0 := by
      simpa using etaleConstantSheafMap_nsmul C (0 : A →+ A) 0
    rw [h0, sheafH_map_zero]
  refine ⟨fun φ φ' _ => AddMonoidHom.ext fun _ => Subsingleton.elim _ _, fun y => ⟨0, ?_⟩⟩
  rw [hzero y, map_zero]

/-- The additive equivalence `ℤ/n × (ℤ/n)^m ≃ (ℤ/n)^{m + 1}`. -/
def zmodPiSuccAddEquiv (m : ℕ) : (ZMod n × (Fin m → ZMod n)) ≃+ (Fin (m + 1) → ZMod n) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, Fin.tail f)
  left_inv p := by simp
  right_inv f := by simp
  map_add' p p' := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- `Θ` is bijective for `(ℤ/n)^m`. -/
theorem bijective_curveConstantClass_pi (m : ℕ) :
    Function.Bijective (curveConstantClass q hn hζ (Fin m → ZMod n)) := by
  induction m with
  | zero => exact bijective_curveConstantClass_of_subsingleton q hn hζ
  | succ m ih =>
    exact bijective_curveConstantClass_of_addEquiv q hn hζ (zmodPiSuccAddEquiv m)
      (bijective_curveConstantClass_prod q hn hζ (bijective_curveConstantClass_zmod q hn hζ) ih)

include q in
omit [Smooth q] [IsProper q] in
/-- **`H³(C, A) = 0`** for a finite abelian group `A`: the constant sheaf is torsion, and a torsion
sheaf on a curve over an algebraically closed field has no cohomology above degree two
(Tag 03SC, statement (1) of Situation 0A52). -/
theorem subsingleton_sheafH_three_etaleConstantSheaf (A : Type) [AddCommGroup A] [Finite A] :
    Subsingleton (Sheaf.H.{u + 1} (etaleConstantSheaf.{u, 0} C A) 3) := by
  have : Finite (AddCommGrpCat.of (ULift.{u + 1} A)) :=
    inferInstanceAs (Finite (ULift.{u + 1} A))
  let S : TorsionSheafSituation.{u, 0} :=
    { k := K
      X := C
      structureMorphism := q
      dimension_le_one := (IsCurve.topologicalKrullDim_eq_one (f := q)).le
      F := etaleConstantSheaf.{u, 0} C A
      isTorsion := Stacks.Torsion.torsionSheafProperty_constantSheaf _ _ }
  exact S.isVanishingAboveDegreeTwo 3 (by norm_num)

omit [IsAlgClosed K] [IsCurve K q] [Smooth q] [IsProper q] in
/-- **The constant sheaf functor is exact** on abelian groups: a short exact sequence of groups
gives a short exact sequence of constant sheaves on `C_étale`. -/
theorem shortExact_etaleConstantSheaf {A B D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (f : A →+ B) (g : B →+ D) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : ∀ b, g b = 0 ↔ ∃ a, f a = b) :
    (ShortComplex.mk (etaleConstantSheafMap C f) (etaleConstantSheafMap C g) (by
      rw [← etaleConstantSheafMap_comp]
      have h0 : g.comp f = 0 := AddMonoidHom.ext fun a => (hfg (f a)).2 ⟨a, rfl⟩
      rw [h0]
      simpa using etaleConstantSheafMap_nsmul C (0 : A →+ D) 0)).ShortExact := by
  let F := constantSheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}
  have : PreservesFiniteLimits F :=
    comp_preservesFiniteLimits (Functor.const _) (presheafToSheaf _ _)
  have : PreservesFiniteColimits F :=
    comp_preservesFiniteColimits (Functor.const _) (presheafToSheaf _ _)
  let fU : AddCommGrpCat.of (ULift.{u + 1} A) ⟶ AddCommGrpCat.of (ULift.{u + 1} B) :=
    AddCommGrpCat.ofHom ((AddEquiv.ulift.{0, u + 1} (α := B)).symm.toAddMonoidHom.comp
      (f.comp (AddEquiv.ulift.{0, u + 1} (α := A)).toAddMonoidHom))
  let gU : AddCommGrpCat.of (ULift.{u + 1} B) ⟶ AddCommGrpCat.of (ULift.{u + 1} D) :=
    AddCommGrpCat.ofHom ((AddEquiv.ulift.{0, u + 1} (α := D)).symm.toAddMonoidHom.comp
      (g.comp (AddEquiv.ulift.{0, u + 1} (α := B)).toAddMonoidHom))
  have hz : fU ≫ gU = 0 := by
    ext x
    exact (hfg (f x.down)).2 ⟨x.down, rfl⟩
  have hS : (ShortComplex.mk fU gU hz).ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.ab_exact_iff]
      intro y hy
      obtain ⟨a, ha⟩ := (hfg y.down).1 (congrArg ULift.down hy)
      exact ⟨ULift.up a, congrArg ULift.up ha⟩
    · rw [AddCommGrpCat.mono_iff_injective]
      intro x y h
      exact ULift.ext _ _ (hf (congrArg ULift.down h))
    · rw [AddCommGrpCat.epi_iff_surjective]
      intro y
      obtain ⟨b, hb⟩ := hg y.down
      exact ⟨ULift.up b, congrArg ULift.up hb⟩
  exact hS.map_of_exact F

section Presentation

variable {A : Type} [AddCommGroup A] (hA : ∀ a : A, n • a = 0)

/-- The additive map `ℤ/n → A`, `1 ↦ a`, for `a` in a group killed by `n`. -/
def zmodHomOfTorsion (a : A) : ZMod n →+ A :=
  ZMod.lift n ⟨zmultiplesHom A a, by simp [hA a]⟩

omit [IsAlgClosed K] [IsCurve K q] [Smooth q] [IsProper q] in
include hA in
/-- The map `zmodHomOfTorsion hA a` sends `1` to `a`. -/
lemma zmodHomOfTorsion_one (a : A) : zmodHomOfTorsion hA a 1 = a := by
  rw [show (1 : ZMod n) = ((1 : ℤ) : ZMod n) by simp, zmodHomOfTorsion, ZMod.lift_coe]
  simp

omit [IsAlgClosed K] [IsCurve K q] [Smooth q] [IsProper q] in
/-- Two additive maps out of `ℤ/n` agreeing at `1` are equal. -/
lemma zmod_addMonoidHom_ext {B : Type} [AddCommGroup B] {φ ψ : ZMod n →+ B} (h : φ 1 = ψ 1) :
    φ = ψ := by
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
  rw [show ((k : ZMod n)) = k • (1 : ZMod n) by simp, map_zsmul, map_zsmul, h]

/-- The surjection `(ℤ/n)^m → A`, `m = #A`, from a chosen enumeration of a finite `A`. -/
def zmodPresentation [Finite A] : (Fin (Nat.card A) → ZMod n) →+ A :=
  ∑ i, (zmodHomOfTorsion hA ((Finite.equivFin A).symm i)).comp (Pi.evalAddMonoidHom _ i)

omit [IsAlgClosed K] [IsCurve K q] [Smooth q] [IsProper q] in
include hA in
/-- The map `zmodPresentation hA : (ℤ/n)^{#A} → A` is surjective. -/
lemma surjective_zmodPresentation [Finite A] [NeZero n] :
    Function.Surjective (zmodPresentation hA) := by
  intro a
  refine ⟨Pi.single (Finite.equivFin A a) 1, ?_⟩
  rw [zmodPresentation, AddMonoidHom.finset_sum_apply,
    Finset.sum_eq_single (Finite.equivFin A a)]
  · simp [zmodHomOfTorsion_one hA]
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

include hA in
/-- **`Θ_A` is surjective** for every finite abelian group `A` killed by `n`: `A` is a quotient of
`(ℤ/n)^m`, `H²` is right exact on constant sheaves because `H³` vanishes, and `Θ` is surjective
on `(ℤ/n)^m`. -/
theorem surjective_curveConstantClass [Finite A] :
    Function.Surjective (curveConstantClass q hn hζ A) := by
  have : NeZero n := ⟨Stacks.Kummer.neZero_of_isUnit hn⟩
  let g := zmodPresentation (n := n) hA
  let Kr := g.ker
  have : Finite Kr := Subtype.finite
  have hS := shortExact_etaleConstantSheaf (C := C) Kr.subtype g Subtype.val_injective
    (surjective_zmodPresentation hA) (fun b => ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩,
      fun ⟨a, ha⟩ => ha ▸ a.2⟩)
  intro y
  have := subsingleton_sheafH_three_etaleConstantSheaf q Kr
  obtain ⟨x₂, hx₂⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hS y (show 2 + 1 = 3 from rfl)
    (Subsingleton.elim _ _)
  obtain ⟨φ, hφ⟩ := (bijective_curveConstantClass_pi q hn hζ (Nat.card A)).2 x₂
  refine ⟨g.comp φ, ?_⟩
  rwa [curveConstantClass_naturality, hφ, Sheaf.H.map_apply]

include hA in
/-- **`Θ_A` is bijective** for every finite abelian group `A` killed by `n`:
`H²(C, A) = Hom(ℤ/n, A)` through the fundamental class. -/
theorem bijective_curveConstantClass [Finite A] :
    Function.Bijective (curveConstantClass q hn hζ A) := by
  have : NeZero n := ⟨Stacks.Kummer.neZero_of_isUnit hn⟩
  refine ⟨(injective_iff_map_eq_zero _).2 fun χ h => ?_,
    surjective_curveConstantClass q hn hζ hA⟩
  let g := zmodPresentation (n := n) hA
  let Kr := g.ker
  have : Finite Kr := Subtype.finite
  have hS := shortExact_etaleConstantSheaf (C := C) Kr.subtype g Subtype.val_injective
    (surjective_zmodPresentation hA) (fun b => ⟨fun hb => ⟨⟨b, hb⟩, rfl⟩,
      fun ⟨a, ha⟩ => ha ▸ a.2⟩)
  have hF : ∀ b : Fin (Nat.card A) → ZMod n, n • b = 0 := fun _ => funext fun _ => by simp
  obtain ⟨b, hb⟩ := surjective_zmodPresentation hA (χ 1)
  let χt := zmodHomOfTorsion hF b
  have hχ : g.comp χt = χ := zmod_addMonoidHom_ext (by
    rwa [AddMonoidHom.comp_apply, zmodHomOfTorsion_one hF])
  have h0 : (curveConstantClass q hn hζ _ χt).comp
      (Ext.mk₀ (etaleConstantSheafMap C g)) (add_zero 2) = 0 := by
    rwa [← Sheaf.H.map_apply, ← curveConstantClass_naturality, hχ]
  obtain ⟨x₁, hx₁⟩ := Abelian.Ext.covariant_sequence_exact₂ _ hS _ h0
  have hKr : ∀ k : Kr, n • k = 0 := fun k => Subtype.ext (hF k.1)
  obtain ⟨ψt, hψt⟩ := surjective_curveConstantClass q hn hζ hKr x₁
  have hlift : χt = Kr.subtype.comp ψt := by
    apply (bijective_curveConstantClass_pi q hn hζ (Nat.card A)).1
    rw [curveConstantClass_naturality, hψt, Sheaf.H.map_apply]
    exact hx₁.symm
  rw [← hχ, hlift]
  ext x
  exact (ψt x).2

end Presentation

end Stacks.EtaleCohomology

end
