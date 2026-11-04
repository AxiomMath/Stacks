module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Lift
public import StacksFrontier.Deformation.LiftsOfObjects.Basic
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.RimSchlessinger.Basic

/-!
# Lifts across the difference isomorphism

Let `f : A' → A` be a surjection of Artinian local algebras whose kernel `I` is annihilated by
the maximal ideal of `A'`. The self-fibre product `A' ×_A A'` is then canonically isomorphic to
the fibre product `A' ×_k k[I]` of `A'` with the square-zero extension of the residue field by
`I`, the isomorphism being `(a₁, a₂) ↦ (a₁, (ā₁, a₂ - a₁))`. This file constructs that
isomorphism and the resulting bijection between isomorphism classes of lifts of an object over
the two fibre products.

## Main definitions

* `Deformation.DifferenceLiftEquiv`: the difference isomorphism of the two fibre products
  together with the transport of isomorphism classes of lifts that it induces, specified on
  both coordinates and on representatives.

## Main results

* `Deformation.liftClassesEquivSquareZeroPullback`: such data exists for a deformation
  category.

## Implementation notes

The object denoted `k[I]` is presented by a ring equivalence `coord` with `TrivSqZeroExt k I`
compatible with the `Λ`-algebra structure and with the chosen residue-field identification: its
first coordinate is the residue map to `k`. The `k`-module structure on `I` is the one induced
by the residue map of `A'`, and the hypothesis `hmodule` says so explicitly. The two chosen
pullback objects merely present the two fibre products, and the comparison isomorphism is
specified on both coordinates, so the resulting bijection of lift classes is canonical rather
than arbitrary.

The tag `06TB` is recorded here against `Deformation.liftClassesProdEquivPullback`: applying the
product bijection to the two maps `A' → A` of a self-pullback square is exactly the statement
that pairs of lift classes over `A'` correspond to lift classes over `A' ×_A A'`, with the class
of a pair represented by its fibre product.

## References

* [Stacks Project, Tag 06TA](https://stacks.math.columbia.edu/tag/06TA)
* [Stacks Project, Tag 06TB](https://stacks.math.columbia.edu/tag/06TB)
-/

@[expose] public section

namespace Deformation

/-! ### The difference isomorphism of the two fibre products -/

section
open CategoryTheory CategoryTheory.Limits

universe u v w uF vF

private lemma kernel_mul_eq_zero
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    (i j : RingHom.ker f.hom.toRingHom) :
    (i : A') * (j : A') = 0 :=
  hann i (kernel_mem_maximalIdeal f i) j

private noncomputable def residueRingHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (A' : ArtinianLocalAlgCat.{u, max v w, w} Λ k) : A' →+* k :=
  A'.residueEquiv.toRingEquiv.toRingHom.comp (IsLocalRing.residue A')

private noncomputable def differenceRingHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A P : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (p₁ p₂ : P ⟶ A') (hP : IsPullback p₁ p₂ f f) :
    P →+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom) := by
  let d : P → RingHom.ker f.hom.toRingHom := fun t =>
    ⟨p₂.hom t - p₁.hom t, by
      rw [RingHom.mem_ker]
      have h := congrArg (fun g : P ⟶ A => g.hom t) hP.w
      have h' : f.hom (p₂.hom t) = f.hom (p₁.hom t) := by
        change f.hom (p₁.hom t) = f.hom (p₂.hom t) at h
        exact h.symm
      change f.hom.toRingHom (p₂.hom t - p₁.hom t) = 0
      rw [map_sub]
      change f.hom (p₂.hom t) - f.hom (p₁.hom t) = 0
      rw [h']
      ring⟩
  refine {
    toFun := fun t => TrivSqZeroExt.inl (residueRingHom A' (p₁.hom t)) +
      TrivSqZeroExt.inr (d t)
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  · have hd : d (1 : P) = 0 := Subtype.ext (by simp [d])
    have hr : residueRingHom A' (p₁.hom 1) = 1 := by simp [residueRingHom]
    rw [hd, TrivSqZeroExt.inr_zero, hr, TrivSqZeroExt.inl_one, add_zero]
  · intro x y
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_mul, add_zero]
      change residueRingHom A' (p₁.hom (x * y)) =
        residueRingHom A' (p₁.hom x) * residueRingHom A' (p₁.hom y)
      rw [map_mul, map_mul]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_mul,
        TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, zero_add, add_zero]
      change d (x * y) =
        (residueRingHom A' (p₁.hom x)) • d y +
          MulOpposite.op (residueRingHom A' (p₁.hom y)) • d x
      have hx : p₂.hom x = p₁.hom x + (d x : A') := by simp [d]
      have hy : p₂.hom y = p₁.hom y + (d y : A') := by simp [d]
      have hresx := hmodule (p₁.hom x) (d y)
      have hresy := hmodule (p₁.hom y) (d x)
      have hrx : residueRingHom A' (p₁.hom x) =
          A'.residueEquiv (IsLocalRing.residue A' (p₁.hom x)) := rfl
      have hry : residueRingHom A' (p₁.hom y) =
          A'.residueEquiv (IsLocalRing.residue A' (p₁.hom y)) := rfl
      rw [hrx, hresx, op_smul_eq_smul, hry, hresy]
      apply Subtype.ext
      change (p₂.hom (x * y) - p₁.hom (x * y)) =
        p₁.hom x • d y + p₁.hom y • d x
      rw [map_mul, map_mul, hx, hy, show p₁.hom x • d y = p₁.hom x * (d y : A') by rfl,
        show p₁.hom y • d x = p₁.hom y * (d x : A') by rfl]
      linear_combination kernel_mul_eq_zero f hann (d x) (d y)
  · have hd : d (0 : P) = 0 := Subtype.ext (by simp [d])
    have hr : residueRingHom A' (p₁.hom 0) = 0 := by simp [residueRingHom]
    rw [hd, TrivSqZeroExt.inr_zero, hr, TrivSqZeroExt.inl_zero, add_zero]
  · intro x y
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
        TrivSqZeroExt.fst_inr, add_zero]
      change residueRingHom A' (p₁.hom (x + y)) =
        residueRingHom A' (p₁.hom x) + residueRingHom A' (p₁.hom y)
      rw [map_add, map_add]
    · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
        TrivSqZeroExt.snd_inr, zero_add]
      apply Subtype.ext
      change (d (x + y) : A') = (d x : A') + (d y : A')
      simp [d, map_add]
      ring

private theorem differenceRingHom_fst
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A P : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (p₁ p₂ : P ⟶ A') (hP : IsPullback p₁ p₂ f f) (t : P) :
    (differenceRingHom f hann hmodule p₁ p₂ hP t).fst =
      residueRingHom A' (p₁.hom t) := by
  simp only [differenceRingHom, TrivSqZeroExt.fst, TrivSqZeroExt.inl,
    TrivSqZeroExt.inr]
  exact add_zero _

private theorem differenceRingHom_snd_coe
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A P : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (p₁ p₂ : P ⟶ A') (hP : IsPullback p₁ p₂ f f) (t : P) :
    ((differenceRingHom f hann hmodule p₁ p₂ hP t).snd : A') =
      p₂.hom t - p₁.hom t := by
  simp only [differenceRingHom, TrivSqZeroExt.snd, TrivSqZeroExt.inl,
    TrivSqZeroExt.inr]
  exact zero_add _

private noncomputable def differenceAlgHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A S P : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (hcoordΛ : ∀ a : Λ, coord (algebraMap Λ S a) =
      TrivSqZeroExt.inl (algebraMap Λ k a))
    (p₁ p₂ : P ⟶ A') (hP : IsPullback p₁ p₂ f f) : P →ₐ[Λ] S := by
  let g := differenceRingHom f hann hmodule p₁ p₂ hP
  let gS : P →+* S := coord.symm.toRingHom.comp g
  refine AlgHom.mk' gS ?_
  intro a x
  simp only [Algebra.smul_def]
  change coord.symm (g (algebraMap Λ P a * x)) =
    algebraMap Λ S a * coord.symm (g x)
  apply coord.injective
  calc
    coord (coord.symm (g (algebraMap Λ P a * x))) =
        TrivSqZeroExt.inl (algebraMap Λ k a) * g x := by
      rw [RingEquiv.apply_symm_apply, map_mul]
      have hga : g (algebraMap Λ P a) =
          TrivSqZeroExt.inl (algebraMap Λ k a) := by
        have hp₁ := p₁.hom.commutes a
        have hp₂ := p₂.hom.commutes a
        have hd : (differenceRingHom f hann hmodule p₁ p₂ hP
            (algebraMap Λ P a)).snd = 0 := by
          apply Subtype.ext
          rw [differenceRingHom_snd_coe]
          rw [hp₂, hp₁]
          simp
        have hr : (differenceRingHom f hann hmodule p₁ p₂ hP
            (algebraMap Λ P a)).fst = algebraMap Λ k a := by
          rw [differenceRingHom_fst]
          rw [hp₁]
          change A'.residueEquiv
            (IsLocalRing.residue A' (algebraMap Λ A' a)) = _
          rw [IsLocalRing.residue_def, Ideal.Quotient.mk_algebraMap]
          exact A'.residueEquiv.commutes a
        apply TrivSqZeroExt.ext
        · exact hr
        · exact hd.trans (by rfl)
      rw [hga]
    _ = coord (algebraMap Λ S a * coord.symm (g x)) := by
      rw [map_mul, hcoordΛ]
      rw [RingEquiv.apply_symm_apply]

private theorem coord_differenceAlgHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A S P : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (hcoordΛ : ∀ a : Λ, coord (algebraMap Λ S a) =
      TrivSqZeroExt.inl (algebraMap Λ k a))
    (p₁ p₂ : P ⟶ A') (hP : IsPullback p₁ p₂ f f) (t : P) :
    coord (differenceAlgHom f hann hmodule coord hcoordΛ p₁ p₂ hP t) =
      differenceRingHom f hann hmodule p₁ p₂ hP t :=
  RingEquiv.apply_symm_apply _ _

private theorem differenceAlgHom_residue
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A S P : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (hcoordΛ : ∀ a : Λ, coord (algebraMap Λ S a) =
      TrivSqZeroExt.inl (algebraMap Λ k a))
    (hcoordResidue : ∀ s : S,
      (coord s).fst = S.residueEquiv (IsLocalRing.residue S s))
    (p₁ p₂ : P ⟶ A') (hP : IsPullback p₁ p₂ f f) (t : P) :
    S.residueEquiv (IsLocalRing.residue S
      (differenceAlgHom f hann hmodule coord hcoordΛ p₁ p₂ hP t)) =
      P.residueEquiv (IsLocalRing.residue P t) := by
  rw [← hcoordResidue]
  rw [coord_differenceAlgHom, differenceRingHom_fst]
  exact p₁.residue_comm t

private noncomputable def homOfResidueCompatible
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {X Y : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (g : X →ₐ[Λ] Y)
    (hres : ∀ a : X,
      Y.residueEquiv (IsLocalRing.residue Y (g a)) =
        X.residueEquiv (IsLocalRing.residue X a)) : X ⟶ Y := by
  refine ⟨g, ?_, hres⟩
  refine ⟨fun a ha ↦ ?_⟩
  have hunitY : IsUnit (Y.residueEquiv (IsLocalRing.residue Y (g a))) :=
    IsUnit.map Y.residueEquiv.toRingEquiv.toRingHom
      (IsUnit.map (IsLocalRing.residue Y) ha)
  rw [hres a] at hunitY
  have hunitX : IsUnit (IsLocalRing.residue X a) := by
    simpa using IsUnit.map X.residueEquiv.symm.toRingHom hunitY
  exact IsLocalHom.map_nonunit (f := IsLocalRing.residue X) a hunitX

private noncomputable def differenceHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A S P : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (hcoordΛ : ∀ a : Λ, coord (algebraMap Λ S a) =
      TrivSqZeroExt.inl (algebraMap Λ k a))
    (hcoordResidue : ∀ s : S,
      (coord s).fst = S.residueEquiv (IsLocalRing.residue S s))
    (p₁ p₂ : P ⟶ A') (hP : IsPullback p₁ p₂ f f) : P ⟶ S :=
  homOfResidueCompatible
    (differenceAlgHom f hann hmodule coord hcoordΛ p₁ p₂ hP)
    (differenceAlgHom_residue f hann hmodule coord hcoordΛ hcoordResidue p₁ p₂ hP)

private theorem hom_to_iso_residueField_unique
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {X K : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hK : K ≅ residueFieldObject.{u, v, w} Λ k)
    (g h : X ⟶ K) : g = h :=
  (cancel_mono hK.hom).1
    (homToResidueFieldObject_unique (g ≫ hK.hom) (h ≫ hK.hom))

private theorem pullback_residue_coord
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A S K Q : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (hcoordResidue : ∀ s : S,
      (coord s).fst = S.residueEquiv (IsLocalRing.residue S s))
    (rA : A' ⟶ K) (rS : S ⟶ K)
    (q₁ : Q ⟶ A') (q₂ : Q ⟶ S)
    (hQ : IsPullback q₁ q₂ rA rS) (t : Q) :
    A'.residueEquiv (IsLocalRing.residue A' (q₁.hom t)) =
      (coord (q₂.hom t)).fst := by
  have hw := congrArg (fun g : Q ⟶ K => g.hom t) hQ.w
  change rA.hom (q₁.hom t) = rS.hom (q₂.hom t) at hw
  calc
    A'.residueEquiv (IsLocalRing.residue A' (q₁.hom t)) =
        K.residueEquiv (IsLocalRing.residue K (rA.hom (q₁.hom t))) :=
      (rA.residue_comm (q₁.hom t)).symm
    _ = K.residueEquiv (IsLocalRing.residue K (rS.hom (q₂.hom t))) := by rw [hw]
    _ = S.residueEquiv (IsLocalRing.residue S (q₂.hom t)) :=
      rS.residue_comm (q₂.hom t)
    _ = (coord (q₂.hom t)).fst := (hcoordResidue (q₂.hom t)).symm

private def castLift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {f g : A ⟶ B}
    {x : p.Fiber B} (h : f = g) (z : Lift p f x) : Lift p g x := by
  refine { obj := z.obj, hom := z.hom, isHomLift := ?_ }
  cases h
  exact z.isHomLift

private noncomputable def castLiftClasses
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {f g : A ⟶ B}
    (x : p.Fiber B) (h : f = g) :
    LiftClasses p f x → LiftClasses p g x := by
  classical
  refine Quotient.map (castLift h) ?_
  intro a b hab
  cases h
  exact hab

private theorem castLiftClassesEquiv_symm_apply_mk
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {A B : ArtinianLocalAlgCat.{u, max v w, w} Λ k} {f g : A ⟶ B}
    (x : p.Fiber B) (h : f = g) (z : Lift p g x) :
    (Equiv.cast (congrArg (fun q : A ⟶ B => LiftClasses p q x) h)).symm
      (ThinSkeleton.mk z) = ThinSkeleton.mk (castLift h.symm z) := by
  cases h
  rfl

private noncomputable def chosenLiftFactor
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    {A₀ A₁ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (hp : IsPredeformationCategory p) (e : A₀ ≅ A₁)
    (f : A₁ ⟶ A) (x : p.Fiber A) (z : Lift p (e.hom ≫ f) x) :
    {a : Lift p f x // ∃ h : z.obj ⟶ a.obj,
      p.IsHomLift e.hom h ∧ h ≫ a.hom = z.hom} :=
  ⟨(lift_factor hp.cofibered e.hom f x z).choose,
    (lift_factor hp.cofibered e.hom f x z).choose_spec⟩

private noncomputable def exactTransportLiftClasses
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    {A₀ A₁ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (e : A₀ ≅ A₁) (f : A₁ ⟶ A) (x : p.Fiber A) :
    LiftClasses p (e.hom ≫ f) x → LiftClasses p f x := by
  classical
  refine Quotient.map (fun z => (chosenLiftFactor hp e f x z).val) ?_
  intro a b hab
  obtain ⟨i⟩ := hab
  obtain ⟨ta, hta₁, hta₂⟩ := (chosenLiftFactor hp e f x a).property
  obtain ⟨tb, htb₁, htb₂⟩ := (chosenLiftFactor hp e f x b).property
  have := i.hom.isHomLift
  exact nonempty_iso_of_liftFactorizations hp.cofibered e.hom f x a
    (chosenLiftFactor hp e f x a).val (chosenLiftFactor hp e f x b).val
    ta (i.hom.hom ≫ tb) hta₁ inferInstance hta₂ (by rw [Category.assoc, htb₂, i.hom.fac])

private noncomputable def transportLiftClasses
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    {A₀ A₁ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (e : A₀ ≅ A₁) (f : A₁ ⟶ A) (g : A₀ ⟶ A) (h : e.hom ≫ f = g)
    (x : p.Fiber A) : LiftClasses p g x → LiftClasses p f x :=
  exactTransportLiftClasses p hp e f x ∘ castLiftClasses p x h.symm

private theorem exactTransportLiftClasses_mk
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    {A₀ A₁ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (e : A₀ ≅ A₁) (f : A₁ ⟶ A) (x : p.Fiber A)
    (z : Lift p (e.hom ≫ f) x) :
    exactTransportLiftClasses p hp e f x (ThinSkeleton.mk z) =
      ThinSkeleton.mk (chosenLiftFactor hp e f x z).val := by
  change Quotient.map (fun z => (chosenLiftFactor hp e f x z).val) _
      (Quotient.mk _ z) = Quotient.mk _ (chosenLiftFactor hp e f x z).val
  rw [Quotient.map_mk]

private noncomputable def liftClassesIsoTransport
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    {A₀ A₁ A : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (e : A₀ ≅ A₁) (f : A₁ ⟶ A) (x : p.Fiber A) :
    LiftClasses p (e.hom ≫ f) x ≃ LiftClasses p f x := by
  classical
  let e' : A₁ ≅ A₀ := e.symm
  have hrev : e'.hom ≫ (e.hom ≫ f) = f := by simp [e']
  refine {
    toFun := exactTransportLiftClasses p hp e f x
    invFun := transportLiftClasses p hp e' (e.hom ≫ f) f hrev x
    left_inv := ?_
    right_inv := ?_ }
  · intro c
    refine Quotient.inductionOn c ?_
    intro z
    dsimp only [transportLiftClasses, exactTransportLiftClasses, Function.comp_apply]
    simp only [castLiftClasses, Quotient.map_mk]
    let a := chosenLiftFactor hp e f x z
    let t := a.property.choose
    let ht := a.property.choose_spec
    let z' : Lift p (e'.hom ≫ (e.hom ≫ f)) x := castLift hrev.symm a.val
    let b := chosenLiftFactor hp e' (e.hom ≫ f) x z'
    let s := b.property.choose
    let hs := b.property.choose_spec
    dsimp [z', castLift] at s hs
    have hcomp : p.IsHomLift (e.hom ≫ e'.hom) (t ≫ s) := by
      let : p.IsHomLift e.hom t := ht.1
      let : p.IsHomLift e'.hom s := hs.1
      infer_instance
    have hcomp' : p.IsHomLift (𝟙 A₀) (t ≫ s) := e.hom_inv_id ▸ hcomp
    let m : (z : Lift p (e.hom ≫ f) x) ⟶ b.val :=
      { hom := t ≫ s
        isHomLift := hcomp'
        fac := (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) hs.2).trans ht.2) }
    have : IsIso m := isIso_liftHom hp.cofibered m
    exact Quotient.sound ⟨(asIso m).symm⟩
  · intro c
    refine Quotient.inductionOn c ?_
    intro z
    dsimp only [transportLiftClasses, exactTransportLiftClasses, Function.comp_apply]
    simp only [castLiftClasses, Quotient.map_mk]
    let z' : Lift p (e'.hom ≫ (e.hom ≫ f)) x := castLift hrev.symm z
    let a := chosenLiftFactor hp e' (e.hom ≫ f) x z'
    let t := a.property.choose
    let ht := a.property.choose_spec
    let b := chosenLiftFactor hp e f x a.val
    let s := b.property.choose
    let hs := b.property.choose_spec
    dsimp [z', castLift] at t ht
    have hcomp : p.IsHomLift (e'.hom ≫ e.hom) (t ≫ s) := by
      let : p.IsHomLift e'.hom t := ht.1
      let : p.IsHomLift e.hom s := hs.1
      infer_instance
    have hcomp' : p.IsHomLift (𝟙 A₁) (t ≫ s) := by
      simpa [e'] using hcomp
    let m : (z : Lift p f x) ⟶ b.val :=
      { hom := t ≫ s
        isHomLift := hcomp'
        fac := (Category.assoc _ _ _).trans ((congrArg (t ≫ ·) hs.2).trans ht.2) }
    have : IsIso m := isIso_liftHom hp.cofibered m
    exact Quotient.sound ⟨(asIso m).symm⟩

private noncomputable def reconstructAlgHom
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A S Q : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (hcoordΛ : ∀ a : Λ, coord (algebraMap Λ S a) =
      TrivSqZeroExt.inl (algebraMap Λ k a))
    (q₁ : Q ⟶ A') (q₂ : Q ⟶ S)
    (hresq : ∀ t : Q,
      A'.residueEquiv (IsLocalRing.residue A' (q₁.hom t)) =
        (coord (q₂.hom t)).fst) : Q →ₐ[Λ] A' := by
  let δ : Q → RingHom.ker f.hom.toRingHom := fun t => (coord (q₂.hom t)).snd
  let g : Q →+* A' := {
    toFun := fun t => q₁.hom t + (δ t : A')
    map_one' := by
      have hδ : δ (1 : Q) = 0 := by
        change (coord (q₂.hom (1 : Q))).snd = 0
        rw [show q₂.hom (1 : Q) = 1 by simp,
          map_one coord]
        rfl
      rw [map_one, hδ]
      simp
    map_mul' := by
      intro x y
      have hδmul : δ (x * y) = q₁.hom x • δ y + q₁.hom y • δ x := by
        change (coord (q₂.hom (x * y))).snd = _
        rw [map_mul q₂.hom x y, map_mul coord, TrivSqZeroExt.snd_mul, ← hresq x, ← hresq y,
          op_smul_eq_smul, hmodule, hmodule]
      have hδmulVal := congrArg (fun i : RingHom.ker f.hom.toRingHom => (i : A')) hδmul
      have hxy : (δ x : A') * (δ y : A') = 0 :=
        kernel_mul_eq_zero f hann (δ x) (δ y)
      rw [map_mul, hδmulVal]
      change q₁.hom x * q₁.hom y +
          (q₁.hom x * (δ y : A') + q₁.hom y * (δ x : A')) = _
      rw [add_mul, mul_add, mul_add, hxy]
      ring
    map_zero' := by
      have hδ : δ (0 : Q) = 0 := by
        change (coord (q₂.hom (0 : Q))).snd = 0
        rw [show q₂.hom (0 : Q) = 0 by simp,
          map_zero coord]
        rfl
      rw [map_zero, hδ]
      simp
    map_add' := by
      intro x y
      have hδ : δ (x + y) = δ x + δ y := by
        change (coord (q₂.hom (x + y))).snd = _
        rw [map_add q₂.hom x y, map_add coord, TrivSqZeroExt.snd_add]
      have hδval := congrArg (fun i : RingHom.ker f.hom.toRingHom => (i : A')) hδ
      rw [map_add, hδval, Submodule.coe_add]
      ring
  }
  have hAlgMap : ∀ a : Λ, g (algebraMap Λ Q a) = algebraMap Λ A' a := by
    intro a
    have hδ : δ (algebraMap Λ Q a) = 0 := by
      change (coord (q₂.hom (algebraMap Λ Q a))).snd = 0
      rw [show q₂.hom (algebraMap Λ Q a) = algebraMap Λ S a from q₂.hom.commutes a, hcoordΛ]
      rfl
    change q₁.hom (algebraMap Λ Q a) + (δ (algebraMap Λ Q a) : A') = _
    rw [q₁.hom.commutes, hδ]
    simp
  refine AlgHom.mk' g ?_
  intro a x
  simp only [Algebra.smul_def]
  rw [map_mul, hAlgMap]

private theorem reconstructAlgHom_residue
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {A' A S Q : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (hcoordΛ : ∀ a : Λ, coord (algebraMap Λ S a) =
      TrivSqZeroExt.inl (algebraMap Λ k a))
    (q₁ : Q ⟶ A') (q₂ : Q ⟶ S)
    (hresq : ∀ t : Q,
      A'.residueEquiv (IsLocalRing.residue A' (q₁.hom t)) =
        (coord (q₂.hom t)).fst) (t : Q) :
    A'.residueEquiv (IsLocalRing.residue A'
      (reconstructAlgHom f hann hmodule coord hcoordΛ q₁ q₂ hresq t)) =
      Q.residueEquiv (IsLocalRing.residue Q t) := by
  let δ : Q → RingHom.ker f.hom.toRingHom := fun t => (coord (q₂.hom t)).snd
  have hδres : IsLocalRing.residue A' (δ t : A') = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).2 (kernel_mem_maximalIdeal f (δ t))
  rw [show reconstructAlgHom f hann hmodule coord hcoordΛ q₁ q₂ hresq t =
      q₁.hom t + (δ t : A') by rfl, map_add, hδres, add_zero]
  exact q₁.residue_comm t

/-- The difference isomorphism of the two pullbacks, together with its induced
transport of isomorphism classes of lifts. -/
public structure DifferenceLiftEquiv
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    {A' A S K P Q : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A) (rA : A' ⟶ K) (rS : S ⟶ K)
    (p₁ p₂ : P ⟶ A') (q₁ : Q ⟶ A') (q₂ : Q ⟶ S)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (x : p.Fiber A) where
  /-- The ring isomorphism given by the first coordinate and the difference of
  the second from the first. -/
  baseEquiv : P ≅ Q
  first : baseEquiv.hom ≫ q₁ = p₁
  residue : ∀ t : P,
    (coord (q₂.hom (baseEquiv.hom.hom t))).fst =
      A'.residueEquiv (IsLocalRing.residue A' (p₁.hom t))
  difference : ∀ t : P,
    ((coord (q₂.hom (baseEquiv.hom.hom t))).snd : A') =
      p₂.hom t - p₁.hom t
  /-- The induced bijection on isomorphism classes of lifts. -/
  equiv : LiftClasses p (p₁ ≫ f) x ≃ LiftClasses p (q₁ ≫ f) x
  /-- A representative maps to its pushforward along the difference isomorphism. -/
  maps_lift : ∀ z : Lift p (p₁ ≫ f) x,
    ∃ z' : Lift p (q₁ ≫ f) x,
      equiv (ThinSkeleton.mk z) = ThinSkeleton.mk z' ∧
        ∃ t : z.obj ⟶ z'.obj,
          p.IsHomLift baseEquiv.hom t ∧ t ≫ z'.hom = z.hom

/-- The canonical difference isomorphism
`A' ×_A A' ≅ A' ×_k k[I]` induces a bijection of lifts of `x` over these
two objects, compatible with pushforward of each representative. The presentation
`coord` of `k[I]` respects its `Λ`-algebra map and its chosen residue-field
identification, as required for an identification in `𝒞_Λ`. -/
@[stacks 06TA]
public theorem liftClassesEquivSquareZeroPullback
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsDeformationCategory p)
    {A' A S K P Q : ArtinianLocalAlgCat.{u, max v w, w} Λ k}
    (f : A' ⟶ A) (_hf : Function.Surjective f.hom)
    (hann : ∀ a : A', a ∈ IsLocalRing.maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)
    [Module k (RingHom.ker f.hom.toRingHom)]
    [Module kᵐᵒᵖ (RingHom.ker f.hom.toRingHom)]
    [IsCentralScalar k (RingHom.ker f.hom.toRingHom)]
    (hmodule : ∀ (a : A') (i : RingHom.ker f.hom.toRingHom),
      (A'.residueEquiv (IsLocalRing.residue A' a)) • i = a • i)
    (coord : S ≃+* TrivSqZeroExt k (RingHom.ker f.hom.toRingHom))
    (hcoordΛ : ∀ a : Λ, coord (algebraMap Λ S a) =
      TrivSqZeroExt.inl (algebraMap Λ k a))
    (hcoordResidue : ∀ s : S,
      (coord s).fst = S.residueEquiv (IsLocalRing.residue S s))
    (hK : K ≅ residueFieldObject.{u, v, w} Λ k)
    (rA : A' ⟶ K) (rS : S ⟶ K)
    (p₁ p₂ : P ⟶ A') (hP : IsPullback p₁ p₂ f f)
    (q₁ : Q ⟶ A') (q₂ : Q ⟶ S) (hQ : IsPullback q₁ q₂ rA rS)
    (x : p.Fiber A) :
    Nonempty (DifferenceLiftEquiv p f rA rS p₁ p₂ q₁ q₂ coord x) := by
  classical
  let d : P ⟶ S := differenceHom f hann hmodule coord hcoordΛ hcoordResidue p₁ p₂ hP
  have hresq : ∀ t : Q,
      A'.residueEquiv (IsLocalRing.residue A' (q₁.hom t)) =
        (coord (q₂.hom t)).fst :=
    pullback_residue_coord f coord hcoordResidue rA rS q₁ q₂ hQ
  let δ : Q → RingHom.ker f.hom.toRingHom := fun t => (coord (q₂.hom t)).snd
  let s : Q ⟶ A' := homOfResidueCompatible
    (reconstructAlgHom f hann hmodule coord hcoordΛ q₁ q₂ hresq)
    (reconstructAlgHom_residue f hann hmodule coord hcoordΛ q₁ q₂ hresq)
  have hev : ∀ {X Y Z : ArtinianLocalAlgCat.{u, max v w, w} Λ k} (a : X ⟶ Y) (b : Y ⟶ Z)
      (c : X ⟶ Z), a ≫ b = c → ∀ t, b.hom (a.hom t) = c.hom t := fun a b c h t => by
    simpa [ArtinianLocalAlgCat.comp_hom] using congrArg (fun g => g.hom t) h
  have hcd : ∀ t, coord (d.hom t) = differenceRingHom f hann hmodule p₁ p₂ hP t :=
    coord_differenceAlgHom f hann hmodule coord hcoordΛ p₁ p₂ hP
  have hαcompat : p₁ ≫ rA = d ≫ rS := hom_to_iso_residueField_unique hK _ _
  let α : P ⟶ Q := IsPullback.lift hQ p₁ d hαcompat
  have hα₁ : α ≫ q₁ = p₁ := IsPullback.lift_fst hQ p₁ d hαcompat
  have hα₂ : α ≫ q₂ = d := IsPullback.lift_snd hQ p₁ d hαcompat
  have hα₂t := hev α q₂ d hα₂
  have hs (t : Q) : s.hom t = q₁.hom t + (δ t : A') := rfl
  have hβcompat : q₁ ≫ f = s ≫ f := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro t
    change f.hom (q₁.hom t) = f.hom (s.hom t)
    rw [hs]
    change f.hom.toRingHom (q₁.hom t) =
      f.hom.toRingHom (q₁.hom t + (δ t : A'))
    rw [map_add]
    have hker : f.hom.toRingHom (δ t : A') = 0 := (RingHom.mem_ker).mp (δ t).property
    rw [hker]
    simp
  let β : Q ⟶ P := IsPullback.lift hP q₁ s hβcompat
  have hβ₁ : β ≫ p₁ = q₁ := IsPullback.lift_fst hP q₁ s hβcompat
  have hβ₂ : β ≫ p₂ = s := IsPullback.lift_snd hP q₁ s hβcompat
  have hαs : α ≫ s = p₂ := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro t
    have h₁ := hev α q₁ p₁ hα₁ t
    have hδ : ((coord (q₂.hom (α.hom t))).snd : A') =
        p₂.hom t - p₁.hom t := by
      rw [hα₂t, hcd]
      exact differenceRingHom_snd_coe f hann hmodule p₁ p₂ hP t
    change q₁.hom (α.hom t) + (δ (α.hom t) : A') = p₂.hom t
    rw [h₁]
    change p₁.hom t + ((coord (q₂.hom (α.hom t))).snd : A') = _
    rw [hδ]
    ring
  have hβd : β ≫ d = q₂ := by
    apply ArtinianLocalAlgCat.hom_ext
    apply AlgHom.ext
    intro t
    apply coord.injective
    have h₁ := hev β p₁ q₁ hβ₁ t
    have h₂ := hev β p₂ s hβ₂ t
    change coord (d.hom (β.hom t)) = coord (q₂.hom t)
    rw [hcd]
    apply TrivSqZeroExt.ext
    · rw [differenceRingHom_fst, h₁]
      exact hresq t
    · apply Subtype.ext
      rw [differenceRingHom_snd_coe, h₂]
      rw [hs, h₁]
      ring
  have hαβ : α ≫ β = 𝟙 P := hP.hom_ext (by rw [Category.assoc, hβ₁, hα₁]; simp)
    (by rw [Category.assoc, hβ₂, hαs]; simp)
  have hβα : β ≫ α = 𝟙 Q := hQ.hom_ext (by rw [Category.assoc, hα₁, hβ₁]; simp)
    (by rw [Category.assoc, hα₂, hβd]; simp)
  let e : P ≅ Q := ⟨α, β, hαβ, hβα⟩
  have hebase : e.hom ≫ (q₁ ≫ f) = p₁ ≫ f :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) hα₁)
  let classCast := Equiv.cast
    (congrArg (fun g : P ⟶ A => LiftClasses p g x) hebase)
  let transport := liftClassesIsoTransport p hp.predeformation e (q₁ ≫ f) x
  refine ⟨{
    baseEquiv := e
    first := hα₁
    residue := ?_
    difference := ?_
    equiv := classCast.symm.trans transport
    maps_lift := ?_ }⟩
  · intro t
    rw [hα₂t, hcoordResidue]
    change S.residueEquiv (IsLocalRing.residue S
      (differenceAlgHom f hann hmodule coord hcoordΛ p₁ p₂ hP t)) = _
    exact (differenceAlgHom_residue f hann hmodule coord hcoordΛ hcoordResidue
      p₁ p₂ hP t).trans (p₁.residue_comm t).symm
  · intro t
    rw [hα₂t]
    rw [hcd]
    exact differenceRingHom_snd_coe f hann hmodule p₁ p₂ hP t
  · intro z
    let zcast : Lift p (e.hom ≫ (q₁ ≫ f)) x := castLift hebase.symm z
    let w := chosenLiftFactor hp.predeformation e (q₁ ≫ f) x zcast
    refine ⟨w.val, ?_, ?_⟩
    · simp only [Equiv.trans_apply]
      rw [castLiftClassesEquiv_symm_apply_mk p x hebase z]
      change exactTransportLiftClasses p hp.predeformation e (q₁ ≫ f) x
        (ThinSkeleton.mk zcast) = ThinSkeleton.mk w.val
      rw [exactTransportLiftClasses_mk p hp.predeformation e (q₁ ≫ f) x zcast]
    · exact w.property

end

/-! ### Pairs of lifts over a self-fibre product -/

section

add_to_stacks 06TB liftClassesProdEquivPullback

end

end Deformation
