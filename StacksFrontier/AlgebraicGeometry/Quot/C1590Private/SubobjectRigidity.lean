module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiImageSubsheaf
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Basic

/-!
# The automorphisms of `𝒪` fix every submodule

An object `G` of a category is *subobject-rigid*
(`AlgebraicGeometry.C1590Private.IsSubobjectRigid`) when every automorphism of `G` fixes every
subobject of `G`. The structure sheaf of a ringed site with commutative rings of sections, read as
a sheaf of modules over itself, is subobject-rigid: an endomorphism `φ` of `𝒪` is multiplication
by the section `φ(1)` over each object, and a submodule of `𝒪` is stable under multiplication by
sections. Hence so is `𝒪^{⊕ 1}` on `ℙⁿ_T` (`AlgebraicGeometry.ProjectiveQuot.freeModule n 1 T`).

The point of the notion is
`AlgebraicGeometry.C1590Private.kernelSubobject_comp_eq_of_isSubobjectRigid`: for a subobject-rigid
`G`, the kernel of `β ≫ q` does not depend on the isomorphism `β : G ≅ H`.
So a submodule of a module `H` isomorphic to `𝒪` is transported to a submodule of `𝒪` in a way
which does not depend on the chosen isomorphism, and no coherence between chosen isomorphisms is
ever needed.

## Main definitions

* `AlgebraicGeometry.C1590Private.IsSubobjectRigid`.

## Main results

* `AlgebraicGeometry.C1590Private.isSubobjectRigid_unit`: the structure sheaf is
  subobject-rigid.
* `AlgebraicGeometry.C1590Private.isSubobjectRigid_freeModule_one`: so is `𝒪^{⊕ 1}` on `ℙⁿ_T`.
* `AlgebraicGeometry.C1590Private.kernelSubobject_comp_eq_of_isSubobjectRigid`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe v u

section Rigid

variable {C : Type u} [Category.{v} C]

/-- An object of a category is *subobject-rigid* when every automorphism of it fixes every
subobject. -/
def IsSubobjectRigid (G : C) : Prop :=
  ∀ ⦃A : C⦄ (m : A ⟶ G) [Mono m] (φ : G ⟶ G) [IsIso φ], Subobject.mk (m ≫ φ) = Subobject.mk m

/-- Two monomorphisms defining the same subobject still do after composing with a further
monomorphism. -/
theorem mk_comp_eq_mk_comp {G H A A' : C} {a : A ⟶ G} {b : A' ⟶ G} [Mono a] [Mono b]
    (h : Subobject.mk a = Subobject.mk b) (f : G ⟶ H) [Mono f] :
    Subobject.mk (a ≫ f) = Subobject.mk (b ≫ f) :=
  Subobject.mk_eq_mk_of_comm _ _ (Subobject.isoOfMkEqMk a b h) (by
    rw [Subobject.isoOfMkEqMk_hom, ← Category.assoc, Subobject.ofMkLEMk_comp])

/-- Subobject-rigidity is invariant under isomorphism. -/
theorem IsSubobjectRigid.of_iso {G G' : C} (hG : IsSubobjectRigid G) (e : G ≅ G') :
    IsSubobjectRigid G' := by
  intro A m _ φ _
  have h := mk_comp_eq_mk_comp (hG (m ≫ e.inv) (e.hom ≫ φ ≫ e.inv)) e.hom
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

/-- **For a subobject-rigid object the kernel of `β ≫ q` does not depend on the isomorphism
`β`.** -/
theorem kernelSubobject_comp_eq_of_isSubobjectRigid [Preadditive C] [HasKernels C]
    {G H Q : C} (hG : IsSubobjectRigid G) (β β' : G ⟶ H) [IsIso β] [IsIso β'] (q : H ⟶ Q) :
    kernelSubobject (β ≫ q) = kernelSubobject (β' ≫ q) := by
  let γ : G ⟶ G := β' ≫ inv β
  have hγ : kernelSubobject (β' ≫ q) = kernelSubobject (γ ≫ β ≫ q) := by
    congr 1
    simp [γ]
  rw [hγ]
  have h₁ : kernelSubobject (γ ≫ β ≫ q) =
      Subobject.mk ((kernelSubobject (β ≫ q)).arrow ≫ inv γ) := by
    refine (Subobject.mk_arrow _).symm.trans (Subobject.mk_eq_mk_of_comm _ _
      (kernelSubobjectIsoComp γ (β ≫ q)) ?_)
    have h := kernelSubobjectIsoComp_hom_arrow γ (β ≫ q)
    exact (Category.assoc _ _ _).symm.trans (by rw [h]; simp)
  rw [h₁, hG, Subobject.mk_arrow]

end Rigid

section Unit

open Stacks.SheafOfModules.ImageSubsheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

variable (R) in
/-- The sections of the unit module over `X` are the sections of the ring sheaf over `X`. -/
def unitSectionEquiv (X : Cᵒᵖ) : (SheafOfModules.unit R).val.obj X ≃ R.obj.obj X :=
  Equiv.refl _

/-- An endomorphism of the unit module is, over each object, multiplication by the image of `1`:
for a section `y`, `φ y = y • φ 1`. -/
theorem unit_endo_apply (φ : SheafOfModules.unit R ⟶ SheafOfModules.unit R)
    (X : Cᵒᵖ) (y : (SheafOfModules.unit R).val.obj X) :
    φ.val.app X y = unitSectionEquiv R X y • φ.val.app X ((unitSectionEquiv R X).symm 1) := by
  have hy : y = unitSectionEquiv R X y • (unitSectionEquiv R X).symm 1 := by
    show y = unitSectionEquiv R X y * (1 : R.obj.obj X)
    exact (mul_one (unitSectionEquiv R X y)).symm
  conv_lhs => rw [hy]
  exact (φ.val.app X).hom.map_smul _ _

/-- Sections of the unit module of a sheaf of commutative rings commute. -/
theorem unit_smul_comm (hR : ∀ (X : Cᵒᵖ) (a b : R.obj.obj X), a * b = b * a) (X : Cᵒᵖ)
    (y z : (SheafOfModules.unit R).val.obj X) :
    unitSectionEquiv R X y • z = unitSectionEquiv R X z • y :=
  hR X (unitSectionEquiv R X y) (unitSectionEquiv R X z)

/-- The range of `m ≫ φ` is contained in the range of `m`, for an endomorphism `φ` of the unit
module of a sheaf of commutative rings. -/
theorem rangeSubmodule_comp_le (hR : ∀ (X : Cᵒᵖ) (a b : R.obj.obj X), a * b = b * a)
    {A : SheafOfModules R} (m : A ⟶ SheafOfModules.unit R)
    (φ : SheafOfModules.unit R ⟶ SheafOfModules.unit R) (X : Cᵒᵖ) :
    (rangeSubmodule (m ≫ φ)).obj X ≤ (rangeSubmodule m).obj X := by
  rintro s ⟨a, rfl⟩
  refine ⟨unitSectionEquiv R X (φ.val.app X ((unitSectionEquiv R X).symm 1)) • a, ?_⟩
  show (m.val.app X).hom (_ • a) = φ.val.app X (m.val.app X a)
  rw [(m.val.app X).hom.map_smul, unit_endo_apply φ X (m.val.app X a), unit_smul_comm hR]

/-- **The structure sheaf of a sheaf of commutative rings is subobject-rigid.** -/
theorem isSubobjectRigid_unit (hR : ∀ (X : Cᵒᵖ) (a b : R.obj.obj X), a * b = b * a) :
    IsSubobjectRigid (SheafOfModules.unit R) := by
  intro A m _ φ _
  have hmk : ∀ {B : SheafOfModules R} (n : B ⟶ SheafOfModules.unit R) [Mono n],
      Subobject.mk n = Subobject.mk (monoRangeSubmodule n).ι := fun n _ =>
    Subobject.mk_eq_mk_of_comm _ _ (monoRangeSubmoduleIso n) (monoRangeSubmoduleIso_hom_comp_ι n)
  have heq : monoRangeSubmodule (m ≫ φ) = monoRangeSubmodule m := by
    refine le_antisymm ((SheafOfModules.Submodule.le_iff).2
      ((PresheafOfModules.Submodule.le_iff).2 fun X => rangeSubmodule_comp_le hR m φ X))
      ((SheafOfModules.Submodule.le_iff).2 ((PresheafOfModules.Submodule.le_iff).2 fun X => ?_))
    have h := rangeSubmodule_comp_le hR (m ≫ φ) (inv φ) X
    have hc : m ≫ φ ≫ inv φ = m := by simp
    rw [Category.assoc, hc] at h
    exact h
  rw [hmk m, hmk (m ≫ φ), heq]

end Unit

/-- The structure sheaf of a scheme, read as a module over itself, is subobject-rigid. -/
theorem isSubobjectRigid_unitModule (X : Scheme.{u}) :
    IsSubobjectRigid (Scheme.unitModule X) :=
  isSubobjectRigid_unit fun U a b => mul_comm (G := ↑(X.presheaf.obj U)) a b

/-- **`𝒪^{⊕ 1}` on `ℙⁿ_T` is subobject-rigid.** -/
theorem isSubobjectRigid_freeModule_one (n : ℕ) (T : Scheme.{u}) :
    IsSubobjectRigid (ProjectiveQuot.freeModule n 1 T) :=
  (isSubobjectRigid_unitModule _).of_iso
    (coproductUniqueIso fun _ : Fin 1 => Scheme.unitModule (projectiveSpaceOver n T)).symm

end AlgebraicGeometry.C1590Private

end
