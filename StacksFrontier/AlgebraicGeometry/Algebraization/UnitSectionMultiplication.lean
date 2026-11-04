module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleMonoPunctured

/-!
# Multiplication by a section on the tensor powers of the structure sheaf

An endomorphism `σ : 𝒪_X ⟶ 𝒪_X` is a global section of `𝒪_X`, every integer tensor power
`𝒪_X^{⊗ k}` is again `𝒪_X`, and multiplication by `σ` on the `k`-th power is `σ` itself,
conjugated by two such identifications. This is proved for
`Stacks.Algebraization.mulSectionPowScheme` and for it tensored on the left with the structure
sheaf.

## Main definitions

* `Stacks.Algebraization.unitTensorPowSchemeIso`: **every integer tensor power of the structure
  sheaf of a scheme is the structure sheaf** ([Stacks, Tag 01CU]), at the spelling
  `Stacks.Algebraization.tensorPowScheme`.

## Main results

* `Stacks.Algebraization.whiskerLeft_unit_eq_leftUnitor_conj`: left whiskering by the monoidal
  unit is conjugation by the left unit constraint.
* `Stacks.Algebraization.whiskerLeft_eq_whiskerRight_conj`: an endomorphism of the unit whiskered
  into a module isomorphic to the unit is, up to conjugation by that isomorphism whiskered on the
  right, the same endomorphism whiskered into the unit.
* `Stacks.Algebraization.rightUnitor_inv_whiskerLeft_comp_eq_conj`: the body of
  `Stacks.SheafOfModules.TensorPower.mulSectionPow` at a module isomorphic to the unit, written as
  a conjugate of the section.
* `Stacks.Algebraization.whiskerLeft_unit_conj_of_eq`: a morphism conjugate to `σ` stays
  conjugate to `σ` after whiskering with the unit.
* `Stacks.Algebraization.exists_iso_mulSectionPowScheme_unit`: **multiplication by a global
  section on the integer tensor powers of the structure sheaf is that section, up to an
  isomorphism on each side, in every degree.**
* `Stacks.Algebraization.exists_iso_tensorModulesMap_id_mulSectionPowScheme_unit`: the same after
  tensoring on the left with the structure sheaf.

## Implementation notes

The two existence statements assert only that the two conjugating isomorphisms exist, with no
relation between the ones chosen in different degrees.

The monoidal structure is `Stacks.Algebraization.strictModulesMonoidal`, registered here as a
`local instance`: its tensor product is `Stacks.RelativeVeryAmple.tensorModules` and its unit is
`Stacks.Ample.unitModule`, both on the nose, so nothing has to be transported between the
statements below and those spellings.

The rearrangements are nevertheless stated at `𝟙_ X.Modules` rather than at
`Stacks.Ample.unitModule X`, and they are reached by `exact` rather than by `rw`. The two
spellings of the unit are definitionally equal but not syntactically so, and a composite built
out of both — which is what `Stacks.Algebraization.mulSectionPowScheme` unfolds to, its right unit
constraint contributing the `𝟙_` spelling and its section the `Stacks.Ample.unitModule` one — is
not type-correct at the reducible transparency at which `rw` checks its motive. Inside a statement
written wholly at `𝟙_` the whole chase happens in one spelling, and the single defeq between the
two is then discharged once, by the `exact` that applies it.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open Stacks.RelativeVeryAmple

universe u

namespace Stacks.Algebraization

attribute [local instance] strictModulesMonoidal

/-! ### The tensor powers of the structure sheaf -/

/-- **Every integer tensor power of the structure sheaf of a scheme is the structure sheaf.**
This is `Stacks.SheafOfModules.TensorPower.unitTensorPowerIso` with its hypothesis supplied from
`Stacks.Ample.isInvertibleModule_unit`, at the spelling `Stacks.Algebraization.tensorPowScheme`. -/
def unitTensorPowSchemeIso (X : Scheme.{u}) (k : ℤ) :
    tensorPowScheme X (Stacks.Ample.unitModule X) k ≅ Stacks.Ample.unitModule X :=
  letI := isEquivalence_tensorRightFunctor_of_isInvertibleModule X (Stacks.Ample.unitModule X)
  Stacks.SheafOfModules.TensorPower.unitTensorPowerIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) k

/-! ### Three monoidal rearrangements -/

/-- **Left whiskering by the monoidal unit is conjugation by the left unit constraint.** -/
theorem whiskerLeft_unit_eq_leftUnitor_conj (X : Scheme.{u}) {M N : X.Modules} (φ : M ⟶ N) :
    𝟙_ X.Modules ◁ φ = (λ_ M).hom ≫ φ ≫ (λ_ N).inv := by
  rw [← Category.assoc, ← leftUnitor_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- **An endomorphism of the unit whiskered into a module isomorphic to the unit is conjugate to
that endomorphism whiskered into the unit**, the conjugating isomorphism being the given one
whiskered on the right. -/
theorem whiskerLeft_eq_whiskerRight_conj (X : Scheme.{u}) {P : X.Modules}
    (e : P ≅ 𝟙_ X.Modules) (σ : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    P ◁ σ =
      e.hom ▷ 𝟙_ X.Modules ≫ 𝟙_ X.Modules ◁ σ ≫ e.inv ▷ 𝟙_ X.Modules := by
  rw [← Category.assoc, ← whisker_exchange, Category.assoc, ← comp_whiskerRight,
    Iso.hom_inv_id, id_whiskerRight, Category.comp_id]

/-- **Multiplication by a global section, at a module isomorphic to the structure sheaf, is that
section up to an isomorphism on each side.** The left-hand side is the body of
`Stacks.SheafOfModules.TensorPower.mulSectionPow`: the right unit constraint, the section
whiskered into `P`, and an arbitrary isomorphism `w` out of `P ⊗ 𝟙_`.

Both conjugating isomorphisms are built from the same three pieces: the isomorphism `P ≅ 𝟙_`
whiskered on the right, the left unit constraint of the unit, and one of the two unitors. -/
theorem rightUnitor_inv_whiskerLeft_comp_eq_conj (X : Scheme.{u}) {P Q : X.Modules}
    (e : P ≅ 𝟙_ X.Modules) (w : P ⊗ 𝟙_ X.Modules ≅ Q)
    (σ : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) :
    (ρ_ P).inv ≫ P ◁ σ ≫ w.hom =
      ((ρ_ P).symm ≪≫ whiskerRightIso e (𝟙_ X.Modules) ≪≫ λ_ (𝟙_ X.Modules)).hom ≫ σ ≫
        (w.symm ≪≫ whiskerRightIso e (𝟙_ X.Modules) ≪≫ λ_ (𝟙_ X.Modules)).inv := by
  rw [whiskerLeft_eq_whiskerRight_conj X e σ, whiskerLeft_unit_eq_leftUnitor_conj]
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, whiskerRightIso_hom,
    whiskerRightIso_inv, Category.assoc]

/-- **A morphism conjugate to an endomorphism `σ` of the unit stays conjugate to `σ` after
whiskering with the unit**, the two conjugating isomorphisms gaining a left unit constraint. -/
theorem whiskerLeft_unit_conj_of_eq (X : Scheme.{u}) {M N : X.Modules} (u : M ≅ 𝟙_ X.Modules)
    (v : N ≅ 𝟙_ X.Modules) (σ : 𝟙_ X.Modules ⟶ 𝟙_ X.Modules) {φ : M ⟶ N}
    (h : φ = u.hom ≫ σ ≫ v.inv) :
    𝟙_ X.Modules ◁ φ = (λ_ M ≪≫ u).hom ≫ σ ≫ (λ_ N ≪≫ v).inv := by
  rw [whiskerLeft_unit_eq_leftUnitor_conj, h]
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]

/-! ### Multiplication by a section, in every degree -/

/-- **Multiplication by a global section on the integer tensor powers of the structure sheaf is
that section, up to isomorphism on both sides, in every degree.** No relation between the
isomorphisms in different degrees is asserted. -/
theorem exists_iso_mulSectionPowScheme_unit (X : Scheme.{u})
    (σ : Stacks.Ample.unitModule X ⟶ Stacks.Ample.unitModule X) (k : ℤ) :
    ∃ (u : tensorPowScheme X (Stacks.Ample.unitModule X) k ≅ Stacks.Ample.unitModule X)
      (v : tensorPowScheme X (Stacks.Ample.unitModule X) (k + 1) ≅ Stacks.Ample.unitModule X),
      mulSectionPowScheme X (Stacks.Ample.unitModule X) σ k = u.hom ≫ σ ≫ v.inv :=
  ⟨_, _, rightUnitor_inv_whiskerLeft_comp_eq_conj X (unitTensorPowSchemeIso X k)
    (tensorPowSchemeSuccIso X (Stacks.Ample.unitModule X) k) σ⟩

/-- **Multiplication by a global section on the integer tensor powers of the structure sheaf,
tensored on the left with the structure sheaf, is that section, up to isomorphism on both sides,
in every degree.** -/
theorem exists_iso_tensorModulesMap_id_mulSectionPowScheme_unit (X : Scheme.{u})
    (σ : Stacks.Ample.unitModule X ⟶ Stacks.Ample.unitModule X) (k : ℤ) :
    ∃ (u : tensorModules X (Stacks.Ample.unitModule X)
            (tensorPowScheme X (Stacks.Ample.unitModule X) k) ≅ Stacks.Ample.unitModule X)
      (v : tensorModules X (Stacks.Ample.unitModule X)
            (tensorPowScheme X (Stacks.Ample.unitModule X) (k + 1)) ≅ Stacks.Ample.unitModule X),
      tensorModulesMap X (𝟙 (Stacks.Ample.unitModule X))
          (mulSectionPowScheme X (Stacks.Ample.unitModule X) σ k) = u.hom ≫ σ ≫ v.inv := by
  obtain ⟨u, v, h⟩ := exists_iso_mulSectionPowScheme_unit X σ k
  refine ⟨λ_ (tensorPowScheme X (Stacks.Ample.unitModule X) k) ≪≫ u,
    λ_ (tensorPowScheme X (Stacks.Ample.unitModule X) (k + 1)) ≪≫ v, ?_⟩
  rw [tensorModulesMap_id_eq_whiskerLeft]
  exact whiskerLeft_unit_conj_of_eq X u v σ h

end Stacks.Algebraization

end
