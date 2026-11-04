module

public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections.DualBasisOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOneLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover

/-!
# A locally trivial sheaf of modules is invertible

Let `𝒪` be a presheaf of commutative rings on a site whose underlying presheaf of rings is a
sheaf, and let `L` be a sheaf of `𝒪`-modules which is locally isomorphic to the structure sheaf.
Then `L` is invertible; no hypothesis on the stalks is needed.

## Main results

* `Stacks.SheafOfModules.exists_smulSectionMap_bijective_of_over_iso_unit`: a trivialization of
  `L` over `U` provides a section of `L` over `U` by which multiplication is bijective over the
  whole slice site.
* `Stacks.SheafOfModules.isInvertible_of_isLocallyTrivial`: a locally trivial sheaf of modules is
  invertible.

## References

* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
  {h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪)}
  {L : SheafOfModules.{max u v} (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)}

/-- A ring section, read as a section of the structure sheaf viewed as a module over itself, is
its own multiple of the unit section. -/
theorem toUnit_eq_smul_unitOne {S : Sheaf J RingCat.{max u v}} (V : Cᵒᵖ)
    (c : ToType (S.obj.obj V)) :
    toUnit (S := S) V c = c • unitOne (S := S) V := by
  rw [show unitOne (S := S) V = toUnit (S := S) V 1 from rfl, toUnit_smul, mul_one]

/-- Two morphisms of sheaves of modules composing to the identity compose to the identity on
sections over every object. -/
theorem app_hom_left_inverse {U : C}
    {A B : SheafOfModules ((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U)}
    (f : A ⟶ B) (g : B ⟶ A) (h : f ≫ g = 𝟙 A) (W : (Over U)ᵒᵖ) (x : ToType (A.val.obj W)) :
    (g.val.app W).hom ((f.val.app W).hom x) = x := by
  simpa using congrArg (fun (ν : A ⟶ A) => (ν.val.app W).hom x) h

/-- **A trivialization of `L` over `U` is multiplication by a section.** If `L|_U` is isomorphic
to the structure sheaf of the slice site, then there is a section `e` of `L` over `U` for which
`c ↦ c • e|_V` is bijective over every object `V` of `C/U`. -/
theorem exists_smulSectionMap_bijective_of_over_iso_unit {U : C}
    (ε : L.over U ≅ SheafOfModules.unit ((Stacks.SheafOfModules.TensorSheafification.structureSheaf
      𝒪 h𝒪).over U)) :
    ∃ e : L.val.obj (op U), ∀ V : (Over U)ᵒᵖ,
      Function.Bijective (smulSectionMap (resSection (L := L) V e)) := by
  set t : (L.over U).sections := (L.over U).unitHomEquiv ε.inv with ht
  refine ⟨t.eval (op (Over.mk (𝟙 U))), fun V => ?_⟩
  have hinv : ε.inv = (L.over U).unitHomEquiv.symm t := by rw [ht, Equiv.symm_apply_apply]
  have hone : (ε.inv.val.app V).hom
      (unitOne (S := (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over U) V) =
        t.eval V := by
    rw [hinv, unitHomEquiv_symm_app_unitOne]
  have hres : resSection (L := L) V (t.eval (op (Over.mk (𝟙 U)))) = t.eval V :=
    PresheafOfModules.sections_property t
      (Quiver.Hom.op (Over.homMk V.unop.hom (by simp) : V.unop ⟶ Over.mk (𝟙 U)))
  have hbij : Function.Bijective (fun c => (ε.inv.val.app V).hom c) :=
    Function.bijective_iff_has_inverse.mpr ⟨fun x => (ε.hom.val.app V).hom x,
      fun c => app_hom_left_inverse ε.inv ε.hom ε.inv_hom_id V c,
      fun x => app_hom_left_inverse ε.hom ε.inv ε.hom_inv_id V x⟩
  have heq : ∀ c : ToType (((Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪).over
    U).obj.obj V),
      (ε.inv.val.app V).hom (toUnit V c)
        = smulSectionMap (resSection (L := L) V (t.eval (op (Over.mk (𝟙 U))))) c := fun c => by
    rw [toUnit_eq_smul_unitOne, map_smul, hone, ← hres]
    exact (smulSectionMap_apply _ c).symm
  refine ⟨fun a b hab => hbij.injective ((heq a).trans (hab.trans (heq b).symm)), fun x => ?_⟩
  obtain ⟨c, hc⟩ := hbij.surjective x
  exact ⟨c, (heq c).symm.trans hc⟩

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

/-- A locally trivial sheaf of modules is invertible. -/
theorem isInvertible_of_isLocallyTrivial (L : SheafOfModules.{max u v}
    (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)) [h :
      Invertible.IsLocallyTrivial L] :
    IsInvertible 𝒪 h𝒪 L := by
  classical
  obtain ⟨I, X, hX, hiso⟩ := h.exists_trivializing_cover
  have hb : ∀ i, DualBasisOne 𝒪 h𝒪 L (X i) := fun i =>
    DualBasisOne.ofSmulBijective (X i)
      (exists_smulSectionMap_bijective_of_over_iso_unit (hiso i).some).choose
      (exists_smulSectionMap_bijective_of_over_iso_unit (hiso i).some).choose_spec
  exact isInvertible_of_dualBasisOne 𝒪 h𝒪 hX hb

section FiniteLocallyFree

variable [∀ A : C, HasWeakSheafify (J.over A) AddCommGrpCat.{max u v}]
  [∀ A : C, (J.over A).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

end FiniteLocallyFree

end Stacks.SheafOfModules

end
