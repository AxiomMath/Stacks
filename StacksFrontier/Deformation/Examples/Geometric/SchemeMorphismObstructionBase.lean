module

public import StacksFrontier.Deformation.Examples.Geometric.BaseSpectrum
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldBase
public import StacksFrontier.Deformation.TangentSpace.Functor

/-!
# The `k`-algebra structure of a first-order deformation over `k[M]`

For a finite-dimensional `k`-vector space `M`, the square-zero extension `k[M] = k ⊕ M` is a
`k`-algebra, so `Spec k[M]` maps to `Spec k`, as a retraction of its closed point. A deformation
`X'` of `X` over `k[M]` is therefore a scheme over `k`, and its structure sheaf, read on the opens
of `X`, is an algebra over the inverse image of `𝒪_{Spec k}` along `f ∘ p_Y = p_X`. This is the
algebra structure over the base of `X_A = (X, f⁻¹𝒪_Y)` that the obstruction classes of
[Stacks Project, Tag 0E3V] are formed with.

## Main definitions

* `Deformation.Examples.squareZeroStructureSpecMap`: `Spec k[M] ⟶ Spec k`.
* `Deformation.Examples.squareZeroStructureRingHom`: the `k`-algebra structure `k ⟶ k[M]`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The `k`-algebra structure `k ⟶ k[M] = k ⊕ M`, `a ↦ (a, 0)`. -/
def squareZeroStructureRingHom (M : FGModuleCat.{u} k) :
    k →+* ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M : Type u) :=
  letI : Module kᵐᵒᵖ M :=
    Module.compHom M {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  TrivSqZeroExt.inlHom k M

/-- The structure morphism `Spec k[M] ⟶ Spec k` of the `k`-algebra `k[M] = k ⊕ M`. -/
def squareZeroStructureSpecMap (M : FGModuleCat.{u} k) :
    baseSpec ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) ⟶
      baseSpec (residueFieldBase Λ k) :=
  Spec.map (CommRingCat.ofHom (squareZeroStructureRingHom (Λ := Λ) M))

/-- The structure morphism `Spec k[M] ⟶ Spec k` is a retraction of the closed point. -/
@[reassoc (attr := simp)]
theorem residueSpecMap_comp_squareZeroStructureSpecMap (M : FGModuleCat.{u} k) :
    residueSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) ≫
      squareZeroStructureSpecMap M = 𝟙 _ := by
  rw [squareZeroStructureSpecMap, residueSpecMap, ← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun _ => rfl))

/-- The structure morphisms `Spec k[M] ⟶ Spec k` are compatible with the maps of spectra induced
by linear maps `g : M ⟶ N`: `k[M] ⟶ k[N]` is a map of `k`-algebras. -/
@[reassoc (attr := simp)]
theorem baseSpecMap_comp_squareZeroStructureSpecMap {M N : FGModuleCat.{u} k} (g : M ⟶ N) :
    baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) ≫
      squareZeroStructureSpecMap (Λ := Λ) M = squareZeroStructureSpecMap (Λ := Λ) N := by
  rw [squareZeroStructureSpecMap, squareZeroStructureSpecMap, baseSpecMap, ← Spec.map_comp]
  refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
  let opModule (X : Type u) [AddCommGroup X] [Module k X] : Module kᵐᵒᵖ X :=
    Module.compHom X {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  let : IsCentralScalar k M := ⟨fun _ _ => rfl⟩
  let : IsCentralScalar k N := ⟨fun _ _ => rfl⟩
  refine TrivSqZeroExt.ext ?_ ?_
  · exact (TrivSqZeroExt.fst_map g.hom.hom _).trans rfl
  · exact (TrivSqZeroExt.snd_map g.hom.hom _).trans (map_zero g.hom.hom)

end Deformation.Examples

end
