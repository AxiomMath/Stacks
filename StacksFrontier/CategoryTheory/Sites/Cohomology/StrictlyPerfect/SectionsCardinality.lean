module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism

/-!
# The sections of a strictly perfect complex are bounded by the sections of the ring

Let `R` be a sheaf of rings on a site.  The sections of the finite free module
`SheafOfModules.free (ULift (Fin n))` over an object are the `n`-tuples of sections of `R`
there, so they are bounded by any infinite cardinal bounding the sections of `R`.  A direct
summand of such a module injects into it on sections, so the same bound holds for every term of
a strictly perfect complex (Stacks 08FL).

## Main results

* `SheafOfModules.mk_free_sections_le`: the bound for a finite free module.
* `mk_sections_le_of_isStrictlyPerfect`: the bound for the terms of a strictly perfect complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe t v u'

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasWeakSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

namespace SheafOfModules

/-- **The sections of a finite free module are bounded by the sections of the ring.** -/
theorem mk_free_sections_le (n : ℕ) (Y : Cᵒᵖ) {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν)
    (hR : #(R.obj.obj Y) ≤ ν) :
    #((SheafOfModules.free (R := R) (ULift.{t} (Fin n))).val.obj Y) ≤ ν := by
  have : HasFiniteBiproducts (SheafOfModules.{t} R) := HasFiniteBiproducts.of_hasFiniteProducts
  let f : Fin n → SheafOfModules.{t} R := fun _ => SheafOfModules.unit R
  let E : SheafOfModules.{t} R ⥤ ModuleCat.{t} (R.obj.obj Y) :=
    SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj Y
  have : E.Additive := by dsimp only [E]; infer_instance
  let e : E.obj (SheafOfModules.free (R := R) (ULift.{t} (Fin n))) ≅ E.obj (⨁ f) :=
    E.mapIso (Sigma.whiskerEquiv (f := fun _ : ULift.{t} (Fin n) => SheafOfModules.unit R)
      (g := f) Equiv.ulift (fun _ => Iso.refl _) ≪≫ (biproduct.isoCoproduct f).symm)
  have hinj : Function.Injective (fun x : E.obj (⨁ f) => fun j => E.map (biproduct.π f j) x) := by
    intro x y hxy
    have key : ∀ z : E.obj (⨁ f),
        z = ∑ j, E.map (biproduct.ι f j) (E.map (biproduct.π f j) z) := by
      intro z
      have h := congrArg (fun φ => (E.map φ).hom z)
        (biproduct.total : ∑ j, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f))
      simp only [Functor.map_sum, Functor.map_comp, ModuleCat.hom_sum, ModuleCat.hom_comp] at h
      rw [LinearMap.sum_apply] at h
      simpa using h.symm
    rw [key x, key y]
    exact Finset.sum_congr rfl (fun j _ => congrArg _ (congrFun hxy j))
  calc #((SheafOfModules.free (R := R) (ULift.{t} (Fin n))).val.obj Y)
      = #(E.obj (⨁ f)) := Cardinal.mk_congr e.toLinearEquiv.toEquiv
    _ ≤ #(Fin n → R.obj.obj Y) := Cardinal.mk_le_of_injective hinj
    _ ≤ ν := by
      rw [Cardinal.mk_pi, Cardinal.prod_const, Cardinal.mk_fin, Cardinal.lift_uzero,
        Cardinal.lift_natCast]
      exact (Cardinal.power_le_power_right hR).trans (Cardinal.power_nat_le hν)

end SheafOfModules

/-- **The sections of the terms of a strictly perfect complex are bounded by the sections of
the ring.** -/
theorem mk_sections_le_of_isStrictlyPerfect {P : CochainComplex (SheafOfModules.{t} R) ℤ}
    (hP : IsStrictlyPerfect R P) (d : ℤ) (Y : Cᵒᵖ) {ν : Cardinal.{t}} (hν : ℵ₀ ≤ ν)
    (hR : #(R.obj.obj Y) ≤ ν) : #((P.X d).val.obj Y) ≤ ν := by
  obtain ⟨n, i, r, hir⟩ := (isDirectSummandOfFiniteFree_iff_free R (P.X d)).1
    (hP.termDirectSummand d)
  refine (Cardinal.mk_le_of_injective (f := fun x => i.val.app Y x) ?_).trans
    (SheafOfModules.mk_free_sections_le n Y hν hR)
  have h : ∀ x, r.val.app Y (i.val.app Y x) = x := fun x => by
    change (i ≫ r).val.app Y x = x
    rw [hir]; rfl
  exact fun x y hxy => by rw [← h x, ← h y]; exact congrArg (r.val.app Y) hxy
