module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.AffineChart
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderGlobalFunctionsAffineBase.SquareZeroCocycle

/-!
# Correcting a lift of a regular function along a first-order thickening of a Čech nerve

Let `W ⇇ R ⇚ R₃` be a truncated Čech nerve of schemes — in the application `W` is an étale chart
of an algebraic space `U`, `R = W ×_U W` and `R₃ = W ×_U R` — and let `W₀ ⇇ R₀ ⇚ R₃₀` be its base
change along a first-order thickening, with `W₀ ⟶ X₀` faithfully flat onto an affine scheme over
which `R₀ = W₀ ×_{X₀} W₀` and `R₃₀ = W₀ ×_{X₀} R₀`.  Then a regular function on `W` whose
restriction to `W₀` is equalized by the two projections `R₀ ⇉ W₀` can be changed, by a function
vanishing on `W₀`, into one equalized by the two projections `R ⇉ W`.

This is `SquareZeroCech.Data.exists_sub_mem_ker_eq` read on rings of global sections: every
square of affine schemes here is cartesian, so its square of rings is a pushout, which supplies
the tensor-product and kernel conditions of `SquareZeroCech.Data`.

## Main results

* `SquareZeroCech.bijective_productMap_of_isPushout`: in a pushout square of commutative rings the
  comparison map from the tensor product is bijective.
* `AlgebraicGeometry.Space.FirstOrderGlobalFunctions.exists_sub_appTop_eq_of_isPullback`: the
  correction, for schemes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace SquareZeroCech

/-- **The comparison from the tensor product to a pushout of commutative rings is bijective.** -/
theorem bijective_productMap_of_isPushout {C A Bb P : CommRingCat.{u}} {f : C ⟶ A} {g : C ⟶ Bb}
    {inl : A ⟶ P} {inr : Bb ⟶ P} (h : IsPushout f g inl inr) :
    letI : Algebra C A := f.hom.toAlgebra
    letI : Algebra C Bb := g.hom.toAlgebra
    letI : Algebra C P := (f ≫ inl).hom.toAlgebra
    Function.Bijective (Algebra.TensorProduct.productMap
      (⟨inl.hom, fun _ => rfl⟩ : A →ₐ[C] P)
      (⟨inr.hom, fun c => by
        change inr.hom (g.hom c) = inl.hom (f.hom c)
        exact (congrArg (fun φ => φ.hom c) h.w).symm⟩ : Bb →ₐ[C] P)) := by
  let : Algebra C A := f.hom.toAlgebra
  let : Algebra C Bb := g.hom.toAlgebra
  let : Algebra C P := (f ≫ inl).hom.toAlgebra
  let : Algebra A P := inl.hom.toAlgebra
  let : Algebra Bb P := inr.hom.toAlgebra
  have : IsScalarTower C A P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower C Bb P := IsScalarTower.of_algebraMap_eq fun c =>
    (congrArg (fun φ => φ.hom c) h.w)
  have : Algebra.IsPushout C A Bb P := CommRingCat.isPushout_iff_isPushout.mp h
  convert (Algebra.IsPushout.equiv C A Bb P).bijective using 1
  refine funext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.productMap_apply_tmul, Algebra.IsPushout.equiv_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end SquareZeroCech

namespace AlgebraicGeometry.Space.FirstOrderGlobalFunctions

variable {X₀ W W₀ R R₀ R₃ R₃₀ : Scheme.{u}}
  {πW : W₀ ⟶ W} {πR : R₀ ⟶ R} {πR₃ : R₃₀ ⟶ R₃}
  {s t : R ⟶ W} {d₀ d₁ d₂ : R₃ ⟶ R} {q : R₃ ⟶ W}
  {sL tL : R₀ ⟶ W₀} {d₀L : R₃₀ ⟶ R₀} {qL : R₃₀ ⟶ W₀} {αW : W₀ ⟶ X₀}

/-- **Correction of a lift along a first-order thickening of a truncated Čech nerve, for
schemes.**  With `πW : W₀ ⟶ W` a first-order thickening of an affine scheme, `R₀ = R ×_W W₀`
along `t`, `R₃₀ = R₃ ×_R R₀` along `d₀`, `R₀ = W₀ ×_{X₀} W₀` and `R₃₀ = W₀ ×_{X₀} R₀` over an
affine `X₀` with `W₀ ⟶ X₀` flat and surjective, and `d₀` flat: a regular function `a` on `W`
whose restriction to `W₀` is equalized by `sL, tL : R₀ ⇉ W₀` becomes equalized by `s, t : R ⇉ W`
after subtracting a function `m` vanishing on `W₀`. -/
theorem exists_sub_appTop_eq_of_isPullback [IsAffine W] [IsAffine X₀]
    (hπW : Stacks.Thickenings.IsFirstOrderThickening πW)
    (hA : IsPullback πR tL t πW) (hB : IsPullback πR₃ d₀L d₀ πR)
    (hC : IsPullback sL tL αW αW) (hD : IsPullback qL d₀L αW (sL ≫ αW))
    (hsL : sL ≫ πW = πR ≫ s) (hqL : qL ≫ πW = πR₃ ≫ q)
    (h₁s : d₁ ≫ s = q) (h₂s : d₂ ≫ s = q) (h₁t : d₁ ≫ t = d₀ ≫ t) (h₂t : d₂ ≫ t = d₀ ≫ s)
    (hd₀ : Flat d₀) (hαF : Flat αW) (hαS : Surjective αW)
    (a : Γ(W, ⊤)) (ha : sL.appTop (πW.appTop a) = tL.appTop (πW.appTop a)) :
    ∃ m : Γ(W, ⊤), πW.appTop m = 0 ∧ s.appTop (a - m) = t.appTop (a - m) := by
  -- affineness of every scheme of the two nerves
  have := hπW.1
  have hW₀ : IsAffine W₀ := (IsClosedImmersion.isAffine_surjective_of_isAffine πW).1
  have hR₀ : IsAffine R₀ := IsAffine.of_isPullback hC
  have hπR : Stacks.Thickenings.IsThickening πR :=
    Stacks.Thickenings.isThickening_of_isPullback hA hπW.isThickening
  have hR : IsAffine R := Stacks.Thickenings.isAffine_of_isThickening hπR
  have hR₃₀ : IsAffine R₃₀ := IsAffine.of_isPullback hD
  have hπR₃ : Stacks.Thickenings.IsThickening πR₃ :=
    Stacks.Thickenings.isThickening_of_isPullback hB hπR
  have hR₃ : IsAffine R₃ := Stacks.Thickenings.isAffine_of_isThickening hπR₃
  have := hπR.1
  -- the rings
  let : Algebra Γ(X₀, ⊤) Γ(W₀, ⊤) := αW.appTop.hom.toAlgebra
  let : Algebra Γ(X₀, ⊤) Γ(R₀, ⊤) := (sL ≫ αW).appTop.hom.toAlgebra
  let : Algebra Γ(X₀, ⊤) Γ(R₃₀, ⊤) := (qL ≫ αW).appTop.hom.toAlgebra
  have hC' := isPushout_appTop_of_isPullback hC
  have hD' := isPushout_appTop_of_isPullback hD
  have hgen := SquareZeroCech.bijective_productMap_of_isPushout hC'
  have hpush := SquareZeroCech.bijective_productMap_of_isPushout hD'
  have hsq : ∀ x ∈ RingHom.ker πW.appTop.hom, ∀ y ∈ RingHom.ker πW.appTop.hom, x * y = 0 := by
    intro x hx y hy
    have h2 := Stacks.Smooth.ker_appTop_sq_eq_bot hπW
    have : x * y ∈ RingHom.ker πW.appTop.hom ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [h2] at this
    exact (Submodule.mem_bot _).1 this
  let X : SquareZeroCech.Data Γ(X₀, ⊤) Γ(W, ⊤) Γ(R, ⊤) Γ(R₃, ⊤) Γ(W₀, ⊤) Γ(R₀, ⊤) Γ(R₃₀, ⊤) :=
    { πD := πW.appTop.hom
      πE := πR.appTop.hom
      πE₂ := πR₃.appTop.hom
      surj_πD := (IsClosedImmersion.isAffine_surjective_of_isAffine πW).2
      surj_πE := (IsClosedImmersion.isAffine_surjective_of_isAffine πR).2
      s := s.appTop.hom
      t := t.appTop.hom
      d₀ := d₀.appTop.hom
      d₁ := d₁.appTop.hom
      d₂ := d₂.appTop.hom
      q := q.appTop.hom
      s₀ := ⟨sL.appTop.hom, fun _ => rfl⟩
      t₀ := ⟨tL.appTop.hom, fun c => by
        change tL.appTop.hom (αW.appTop.hom c) = (sL ≫ αW).appTop.hom c
        rw [hC.w]; rfl⟩
      q₀ := ⟨qL.appTop.hom, fun _ => rfl⟩
      e₀ := ⟨d₀L.appTop.hom, fun c => by
        change d₀L.appTop.hom ((sL ≫ αW).appTop.hom c) = (qL ≫ αW).appTop.hom c
        rw [hD.w]; rfl⟩
      πE_s := fun x => by
        change (πR ≫ s).appTop.hom x = (sL ≫ πW).appTop.hom x
        rw [hsL]
      πE_t := fun x => by
        change (πR ≫ t).appTop.hom x = (tL ≫ πW).appTop.hom x
        rw [hA.w]
      πE₂_q := fun x => by
        change (πR₃ ≫ q).appTop.hom x = (qL ≫ πW).appTop.hom x
        rw [hqL]
      πE₂_d₀ := fun x => by
        change (πR₃ ≫ d₀).appTop.hom x = (d₀L ≫ πR).appTop.hom x
        rw [hB.w]
      d₁_s := fun x => by
        change (d₁ ≫ s).appTop.hom x = q.appTop.hom x
        rw [h₁s]
      d₂_s := fun x => by
        change (d₂ ≫ s).appTop.hom x = q.appTop.hom x
        rw [h₂s]
      d₁_t := fun x => by
        change (d₁ ≫ t).appTop.hom x = (d₀ ≫ t).appTop.hom x
        rw [h₁t]
      d₂_t := fun x => by
        change (d₂ ≫ t).appTop.hom x = (d₀ ≫ s).appTop.hom x
        rw [h₂t]
      sq_zero := hsq
      ker_πE := le_of_eq (CommRingCat.ker_eq_map_of_isPushout_of_surjective _ _ _ _
        (isPushout_appTop_of_isPullback hA)
        (IsClosedImmersion.isAffine_surjective_of_isAffine πW).2)
      ker_πE₂ := le_of_eq (CommRingCat.ker_eq_map_of_isPushout_of_surjective _ _ _ _
        (isPushout_appTop_of_isPullback hB)
        (IsClosedImmersion.isAffine_surjective_of_isAffine πR).2)
      flat := Scheme.Hom.flat_appTop d₀
      gen := hgen.2
      push := hpush }
  have : Module.FaithfullyFlat Γ(X₀, ⊤) Γ(W₀, ⊤) :=
    (AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine αW).1 ⟨hαF, hαS⟩
  obtain ⟨m, hm, hmeq⟩ := X.exists_sub_mem_ker_eq a ha
  exact ⟨m, hm, hmeq.symm⟩

end AlgebraicGeometry.Space.FirstOrderGlobalFunctions

end
