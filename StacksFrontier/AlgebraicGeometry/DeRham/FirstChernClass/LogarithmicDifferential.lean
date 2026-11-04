module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedForms
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GeneratorsOfARankOneModule

/-!
# The logarithmic differential

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X`, let `Ω = Ω_{𝒪_X/A}` be the sheaf of relative
differentials and let `B` also denote a package of the three algebras of Stacks Section 17.21 for
`Ω`. For an invertible local section `u` of `𝒪_X` the **logarithmic differential**

`d log u = u⁻¹ · d u`

is a local section of `Ω¹_{𝒪_X/A}`. It is additive in `u` — multiplicativity of `u` becomes
additivity of `d log u` — and it is closed. Logarithmic differentiation is therefore a morphism
of sheaves of abelian groups `𝒪_X^* ⟶ Ω¹_{𝒪_X/A}` landing in the closed forms.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.logarithmicDifferential`: `d log u = u⁻¹ · d u`, on local
  sections.
* `AlgebraicGeometry.SheafOfModules.logarithmicDifferentialSheafHom`: **logarithmic
  differentiation as a morphism of sheaves of abelian groups** `𝒪_X^* ⟶ Ω¹_{𝒪_X/A}`, where the
  sheaf of units is written additively as in
  `Stacks.Cohomology.Generators.unitsSheaf`.

## Main results

* `AlgebraicGeometry.SheafOfModules.exactOne_one`: `d 1 = 0`.
* `AlgebraicGeometry.SheafOfModules.logarithmicDifferential_mul`:
  `d log (u v) = d log u + d log v`.
* `AlgebraicGeometry.SheafOfModules.logarithmicDifferential_map`: logarithmic differentiation
  commutes with restriction.
* `AlgebraicGeometry.SheafOfModules.d_logarithmicDifferential`: **the logarithmic differential of
  a unit is closed.**
* `AlgebraicGeometry.SheafOfModules.logarithmicDifferentialSheafHom_apply`: the defining formula
  for the sheaf morphism on local sections.

## References

* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped DirectSum

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

attribute [local instance] gradedFormsGOne gradedFormsGMul gradedFormsGRing

/-- The exact differential of the unit section vanishes. -/
theorem exactOne_one (U : (Opens X.carrier)ᵒᵖ) :
    exactOne B U (1 : X.sheaf.obj.obj U) = 0 := by
  have h : ((universalDerivation.{u, u, u} φ).app U).d (1 : X.sheaf.obj.obj U) = 0 :=
    (universalDerivation.{u, u, u} φ).d_one U
  exact (congrArg (fun z => ConcreteCategory.hom (B.exteriorGenerator.val.app U) z) h).trans
    (map_zero _)

/-- The exact differential of the unit section vanishes, read in the ring of all local
sections. -/
theorem exactForm_one (U : (Opens X.carrier)ᵒᵖ) :
    exactForm B U (1 : X.sheaf.obj.obj U) = 0 := by
  rw [exactForm, exactOne_one, map_zero]

/-! ### The logarithmic differential on local sections -/

/-- **The logarithmic differential `d log u = u⁻¹ · d u`** of an invertible local section `u` of
the structure sheaf, as a local section of `Ω¹_{𝒪_X/A}`. -/
noncomputable def logarithmicDifferential (U : (Opens X.carrier)ᵒᵖ) (u : (X.sheaf.obj.obj U)ˣ) :
    (B.exteriorPower 1).val.obj U :=
  (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val • exactOne B U u.val

/-- **Logarithmic differentiation turns multiplication into addition**:
`d log (u v) = d log u + d log v`. -/
theorem logarithmicDifferential_mul (U : (Opens X.carrier)ᵒᵖ) (u v : (X.sheaf.obj.obj U)ˣ) :
    logarithmicDifferential B U (u * v) =
      logarithmicDifferential B U u + logarithmicDifferential B U v := by
  have h : ∀ a b : (X.sheaf.obj.obj U)ˣ,
      ((a * b)⁻¹ : (X.sheaf.obj.obj U)ˣ).val * a.val = (b⁻¹ : (X.sheaf.obj.obj U)ˣ).val := by
    intro a b
    rw [← Units.val_mul]
    exact congrArg Units.val (by simp [mul_comm])
  have h₂ := h v u
  rw [mul_comm v u] at h₂
  rw [logarithmicDifferential, logarithmicDifferential, logarithmicDifferential,
    Units.val_mul, exactOne_mul, smul_add, smul_smul, smul_smul, h u v, h₂, add_comm]

/-- `d log 1 = 0`. -/
theorem logarithmicDifferential_one (U : (Opens X.carrier)ᵒᵖ) :
    logarithmicDifferential B U (1 : (X.sheaf.obj.obj U)ˣ) = 0 := by
  rw [logarithmicDifferential, Units.val_one, exactOne_one, smul_zero]

/-- **Logarithmic differentiation commutes with restriction.** -/
theorem logarithmicDifferential_map {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V)
    (u : (X.sheaf.obj.obj U)ˣ) :
    (B.exteriorPower 1).val.map f (logarithmicDifferential B U u) =
      logarithmicDifferential B V (Units.map (X.sheaf.obj.map f).hom.toMonoidHom u) := by
  rw [logarithmicDifferential, (B.exteriorPower 1).val.map_smul f, exactOne_map,
    logarithmicDifferential]
  rfl

/-! ### The logarithmic differential is closed -/

/-- `d(u⁻¹) ∧ d u = 0` for an invertible local section `u`, read in the ring of all local
sections. -/
private theorem exactForm_inv_mul_exactForm (U : (Opens X.carrier)ᵒᵖ)
    (u : (X.sheaf.obj.obj U)ˣ) :
    exactForm B U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * exactForm B U u.val = 0 := by
  have hmul := exactForm_mul B U u.val (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val
  rw [show u.val * (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val = 1 from u.mul_inv, exactForm_one] at hmul
  have hkey : scalarForm B U u.val * exactForm B U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val =
      -(scalarForm B U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * exactForm B U u.val) :=
    eq_neg_of_add_eq_zero_left hmul.symm
  have hstep : scalarForm B U u.val *
      (exactForm B U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * exactForm B U u.val) = 0 := by
    rw [← mul_assoc, hkey, neg_mul, mul_assoc, exactForm_mul_self, mul_zero, neg_zero]
  have hinv : scalarForm B U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * scalarForm B U u.val = 1 := by
    rw [scalarForm, scalarForm_mul, smul_smul,
      show (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * u.val = 1 from u.inv_mul, one_smul]
    exact ofGradedForm_one B U
  rw [← one_mul (exactForm B U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * exactForm B U u.val), ← hinv,
    mul_assoc, hstep, mul_zero]

variable (D : DeRhamDifferential B)

/-- **The logarithmic differential of a unit is closed**: `d (u⁻¹ · d u) = 0`. -/
theorem d_logarithmicDifferential (U : (Opens X.carrier)ᵒᵖ) (u : (X.sheaf.obj.obj U)ˣ) :
    ((deRhamComplex B D).d 1 2).val.app U (logarithmicDifferential B U u) = 0 := by
  have hw : IsExactWedge B U 1 (exactOne B U u.val) :=
    ⟨u.val, B.exterior.one.eval U, rfl, (B.exterior.mul_one 1 U (exactOne B U u.val)).symm⟩
  have h := (localDifferential_smul_exactWedge B D 1 U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val
    (exactOne B U u.val) hw).trans (exactForm_inv_mul_exactForm B U u)
  exact DirectSum.of_injective (β := gradedForms B U) ((1 + 1 : ℕ) : ℤ)
    (h.trans (map_zero (ofGradedForm B U ((1 + 1 : ℕ) : ℤ))).symm)

/-! ### Logarithmic differentiation as a morphism of sheaves of abelian groups -/

/-- Logarithmic differentiation on the underlying presheaves: the additive map
`u ↦ d log u` on the units of each ring of local sections. -/
noncomputable def logarithmicDifferentialPresheafHom :
    (Stacks.Cohomology.Generators.unitsSheaf X).obj ⟶
      ((_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).obj
        (deRhamTerm B 1)).obj where
  app U := AddCommGrpCat.ofHom
    { toFun := fun g => logarithmicDifferential B U (Additive.toMul g)
      map_zero' := logarithmicDifferential_one B U
      map_add' := fun g h => logarithmicDifferential_mul B U _ _ }
  naturality U V f := by
    ext g
    exact (logarithmicDifferential_map B f (Additive.toMul g)).symm

/-- **Logarithmic differentiation as a morphism of sheaves of abelian groups**
`𝒪_X^* ⟶ Ω¹_{𝒪_X/A}`, the sheaf of units being written additively as in
`Stacks.Cohomology.Generators.unitsSheaf`. -/
noncomputable def logarithmicDifferentialSheafHom :
    Stacks.Cohomology.Generators.unitsSheaf X ⟶
      (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A)).obj
        (deRhamTerm B 1) :=
  ObjectProperty.homMk (logarithmicDifferentialPresheafHom B)

/-- The sheaf morphism of logarithmic differentiation is `u ↦ u⁻¹ · d u` on local sections. -/
theorem logarithmicDifferentialSheafHom_apply (U : (Opens X.carrier)ᵒᵖ)
    (u : (X.sheaf.obj.obj U)ˣ) :
    (logarithmicDifferentialSheafHom B).hom.app U (Additive.ofMul u) =
      logarithmicDifferential B U u := rfl

end AlgebraicGeometry.SheafOfModules

end
