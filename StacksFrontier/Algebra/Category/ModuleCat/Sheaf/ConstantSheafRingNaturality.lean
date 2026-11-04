module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafRingComparison

/-!
# Naturality in the ring of the constant sheaf of modules on the ring itself

Let `(C, J)` be a site and `Λ` a commutative ring. `Stacks.ConstantSheaf.constantRingScalar`
is the section of the constant sheaf of rings `Λ̲` over an object `U` by which `a : Λ` acts on
the sections of the constant sheaf of `Λ`-modules on `Λ`, under the comparison
`Stacks.ConstantSheaf.constantRingSectionsAddEquiv`.

This file shows that `constantRingScalar J U a` is the image of `a` under the canonical map from
the constant presheaf of rings to its sheafification, and hence that it is natural in the ring:
for any ring homomorphism `π : Λ → Λ'` the map of constant sheaves of rings induced by `π` carries
`constantRingScalar J U a` to `constantRingScalar J U (π a)`.

## Main results

* `Stacks.ConstantSheaf.unitIsoConstantModuleSheaf_hom_app_one`: the unit iso carries the unit
  section of `Λ̲` to the constant section with value `1`.
* `Stacks.ConstantSheaf.constantRingScalar_eq_toSheafify`: `constantRingScalar J U a` is the
  image of `a` under `CategoryTheory.toSheafify`.
* `Stacks.ConstantSheaf.constantRingScalar_naturality`: `constantRingScalar` commutes with the
  map of constant sheaves of rings induced by a ring homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules.Constant

universe u v w

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section Unit

variable {R : Type w} [Ring R]
  [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The global section of the constant sheaf of modules on `R` which corepresents the identity
is the constant section with value `1`. -/
lemma constantUnitHomEquiv_id_val (U : C) :
    (constantUnitHomEquiv J (constantModuleSheaf J (ModuleCat.of R R))
        (𝟙 (constantModuleSheaf J (ModuleCat.of R R)))).val (op U) =
      constantValue J (ModuleCat.of R R) U 1 := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))
    (𝟙 (constantModuleSheaf J (ModuleCat.of R R)))
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op U)) (1 : R)

/-- **The unit iso on the unit section.** The isomorphism
`Stacks.SheafOfModules.Constant.unitIsoConstantModuleSheaf` carries the unit section of the
constant sheaf of rings over `U` to the constant section of the constant sheaf of modules with
value `1`. -/
lemma unitIsoConstantModuleSheaf_hom_app_one (U : C) :
    ((unitIsoConstantModuleSheaf J (R := R)).hom.val.app (op U)).hom
        (1 : ((constantSheaf J RingCat.{w}).obj (RingCat.of R)).obj.obj (op U)) =
      constantValue J (ModuleCat.of R R) U 1 := by
  have h1 : SheafOfModules.unitHomEquiv (constantModuleSheaf J (ModuleCat.of R R))
      (unitIsoConstantModuleSheaf J (R := R)).hom =
      constantUnitHomEquiv J (constantModuleSheaf J (ModuleCat.of R R))
        (𝟙 (constantModuleSheaf J (ModuleCat.of R R))) :=
    (SheafOfModules.unitHomEquiv _).apply_symm_apply _
  have h2 := congrArg
    (fun s : (constantModuleSheaf J (ModuleCat.of R R)).sections => s.val (op U)) h1
  rw [← constantUnitHomEquiv_id_val J (R := R) U]
  exact h2

end Unit

section Scalar

variable {Λ : Type w} [CommRing Λ]
  [HasWeakSheafify J (ModuleCat.{w} Λ)]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The scalar of `a : Λ` is the image of `a` in the sheafification.** The section of the
constant sheaf of rings by which `a` acts on the sections of the constant sheaf of `Λ`-modules
on `Λ` is the image of `a` under the canonical map from the constant presheaf of rings to its
sheafification. -/
theorem constantRingScalar_eq_toSheafify (U : C) (a : Λ) :
    constantRingScalar J U a =
      (show ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)).obj.obj (op U) from
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))).app (op U) a) := by
  have hhom : ∀ t, unitSectionsAddEquiv J (Λ := Λ) U t =
      ((unitIsoConstantModuleSheaf J (R := Λ)).inv.val.app (op U)).hom t := fun _ => rfl
  have hinv : ∀ t, (unitSectionsAddEquiv J (Λ := Λ) U).symm t =
      ((unitIsoConstantModuleSheaf J (R := Λ)).hom.val.app (op U)).hom t := fun _ => rfl
  have htrans : ∀ x, constantRingSectionsAddEquiv J (Λ := Λ) U x =
      unitSectionsAddEquiv J (Λ := Λ) U
        (constantSectionsAddEquiv J (ModuleCat.of Λ Λ) U x) := fun _ => rfl
  have hval : constantValue J (ModuleCat.of Λ Λ) U 1 =
      (unitSectionsAddEquiv J (Λ := Λ) U).symm 1 :=
    ((hinv 1).trans (unitIsoConstantModuleSheaf_hom_app_one J U)).symm
  have hunit : unitSectionsAddEquiv J (Λ := Λ) U
      (constantValue J (ModuleCat.of Λ Λ) U 1) = 1 := by
    rw [hval]
    exact (unitSectionsAddEquiv J (Λ := Λ) U).apply_symm_apply 1
  have hone : constantSectionsAddEquiv J (ModuleCat.of Λ Λ) U
      ((constantRingSectionsAddEquiv J (Λ := Λ) U).symm 1) =
      constantValue J (ModuleCat.of Λ Λ) U 1 := by
    refine (unitSectionsAddEquiv J (Λ := Λ) U).injective ?_
    rw [hunit, ← htrans]
    exact (constantRingSectionsAddEquiv J (Λ := Λ) U).apply_symm_apply 1
  have hsmul : ∀ (c : ((constantSheaf J RingCat.{w}).obj (RingCat.of Λ)).obj.obj (op U))
      (t : (constantModuleSheaf J (ModuleCat.of Λ Λ)).val.obj (op U)),
      unitSectionsAddEquiv J (Λ := Λ) U (c • t) =
        c • unitSectionsAddEquiv J (Λ := Λ) U t := by
    intro c t
    simp only [hhom]
    exact map_smul _ c t
  have hsm : ((a • 𝟙 (ModuleCat.of Λ Λ)).hom : Λ →ₗ[Λ] Λ) 1 = a • (1 : Λ) := by simp
  rw [constantRingScalar_eq, htrans, constantSectionsAddEquiv_smul, hone,
    constantValue_map_hom, hsm, constantValue_smul, hsmul, hunit]
  exact mul_one _

end Scalar

section RingMap

variable {Λ : Type w} [CommRing Λ] {Λ' : Type w} [CommRing Λ']
  [HasWeakSheafify J (ModuleCat.{w} Λ)]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ) AddCommGrpCat.{w})]
  [HasWeakSheafify J (ModuleCat.{w} Λ')]
  [J.PreservesSheafification (forget₂ (ModuleCat.{w} Λ') AddCommGrpCat.{w})]
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} Λ') AddCommGrpCat.{w})]
  [HasWeakSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Naturality of `Stacks.ConstantSheaf.constantRingScalar` in the ring.** The map of constant
sheaves of rings induced by a ring homomorphism `π : Λ → Λ'` carries the scalar of `a : Λ` to
the scalar of `π a`. -/
theorem constantRingScalar_naturality (π : Λ →+* Λ') (U : C) (a : Λ) :
    ((constantSheaf J RingCat.{w}).map (RingCat.ofHom π)).hom.app (op U)
        (constantRingScalar J U a) =
      constantRingScalar J U (π a) := by
  rw [constantRingScalar_eq_toSheafify, constantRingScalar_eq_toSheafify]
  have h := CategoryTheory.toSheafify_naturality J
    ((Functor.const Cᵒᵖ).map (RingCat.ofHom π))
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app h (op U)) a).symm

end RingMap

end Stacks.ConstantSheaf

end
