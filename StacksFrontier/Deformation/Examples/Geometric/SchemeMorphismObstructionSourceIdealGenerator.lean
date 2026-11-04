module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdealMap
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceTransition

/-!
# The generators `ũ(m)` under a morphism of deformations of the target

For a morphism `a` of deformations of `Y` over the map `k[M] ⟶ k[N]` of `g : M ⟶ N`, the induced
map `f⁻¹𝒪_{Y'_x} ⟶ f⁻¹𝒪_{Y'_y}` (`Deformation.Examples.sourceIdealTransition`) carries the
generator `ũ_x(m)` of the ideal of the source thickening to `ũ_y(g m)`.

## Main results

* `Deformation.Examples.sourceIdealTransition_generator`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {pY : Y ⟶ baseSpec (residueFieldBase Λ k)}
  {M N : FGModuleCat.{u} k}
  {x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)}
  {y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)}

/-- A morphism of deformations of `Y` over the map `k[M] ⟶ k[N]` of `g` is a morphism over the
induced map of spectra, read through the identifications of the bases with `k[M]`, `k[N]`. -/
theorem SchemeDeformationCategory.map_comp_rebase_toBase
    {P Q : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY)}
    (eP : P.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)
    (eQ : Q.base = (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N) (b : P ⟶ Q) {g : M ⟶ N}
    (hfac : b.base = eqToHom eP ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map g ≫
      eqToHom eQ.symm) :
    b.map ≫ (P.rebase eP).toBase =
      (Q.rebase eQ).toBase ≫ baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) := by
  obtain ⟨BP, SP, qP, hqP, iP, hiP⟩ := P
  obtain ⟨BQ, SQ, qQ, hqQ, iQ, hiQ⟩ := Q
  dsimp only at eP eQ
  subst eP eQ
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at hfac
  have hw := b.cartesian.w
  rw [hfac] at hw
  simp only [SchemeDeformationCategory.rebase_toBase, eqToHom_refl, Category.comp_id]
  exact hw

private local instance (V : FGModuleCat.{u} k) : Module kᵐᵒᵖ V :=
  Module.compHom V {
    toFun := MulOpposite.unop
    map_one' := rfl
    map_mul' := by simp [mul_comm]
    map_zero' := rfl
    map_add' := by intros; rfl }

private local instance (V : FGModuleCat.{u} k) : IsCentralScalar k V where
  op_smul_eq_smul _ _ := rfl

/-- The map `k[M] ⟶ k[N]` induced by `g : M ⟶ N` sends `squareZeroInr M m` to
`squareZeroInr N (g m)`. -/
theorem squareZeroExtensionArtinian_map_squareZeroInr (g : M ⟶ N) (m : M) :
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g).hom (squareZeroInr (Λ := Λ) M m) =
      squareZeroInr (Λ := Λ) N (g.hom m) :=
  TrivSqZeroExt.map_inr _ _

/-- On global sections, the morphism of spectra induced by `k[M] ⟶ k[N]` sends the function
`squareZeroSpecFunction M m` to `squareZeroSpecFunction N (g m)`. -/
theorem baseSpecMap_squareZeroSpecFunction (g : M ⟶ N) (m : M) :
    (baseSpecMap ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)).appTop
        (squareZeroSpecFunction (Λ := Λ) M m) = squareZeroSpecFunction (Λ := Λ) N (g.hom m) := by
  have h := congrArg (fun φ => φ.hom (squareZeroInr (Λ := Λ) M m))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g).hom.toRingHom))
  refine h.symm.trans ((CommRingCat.comp_apply _ _ _).trans ?_)
  exact congrArg (Scheme.ΓSpecIso _).inv.hom (squareZeroExtensionArtinian_map_squareZeroInr g m)

variable {a : x.1 ⟶ y.1} in
/-- **The induced map carries the generator `ũ_x(m)` to `ũ_y(g m)`.** -/
theorem sourceIdealTransition_generator {g : M ⟶ N}
    (ha : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a) (m : M) :
    ((sourceIdealTransition f a).hom.app (op ⊤)).hom (sourceIdealGenerator f pY x m) =
      sourceIdealGenerator f pY y (g.hom m) := by
  have hw := SchemeDeformationCategory.map_comp_rebase_toBase x.2 y.2 a
    (IsHomLift.fac' (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a)
  refine (sourceIdealTransition_ambientSection f a (W := ⊤) (V := ⊤) _ (fun _ _ => trivial) _).trans
    ?_
  unfold sourceIdealGenerator
  congr 1
  have h := congrArg (fun φ : y.1.scheme ⟶ baseSpec _ =>
    φ.appTop.hom (squareZeroSpecFunction (Λ := Λ) M m)) hw
  refine (h.trans ?_)
  exact congrArg (y.1.rebase y.2).toBase.appTop.hom (baseSpecMap_squareZeroSpecFunction g m)

end Deformation.Examples

end
