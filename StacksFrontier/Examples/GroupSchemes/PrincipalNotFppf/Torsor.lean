module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ModObj
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.Torsor
public import StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Group
public import StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Scheme

/-!
# A principal homogeneous space which is not an fppf torsor

Let `S = Spec ℚ`, let `G = ∏ᵢ μ_{i+2}` be the spectrum of the group algebra of
`⨁ᵢ ℤ/(i+2)` over `ℚ`, and let `P = Spec ℚ[x₀, x₁, …]/(xᵢ ^ (i + 2) - 2)` with the action
scaling `xᵢ` by the `i`-th coordinate.  Then `P` is a principal homogeneous `G`-space, that is
an fpqc `G`-torsor, but no fppf `G`-torsor is isomorphic to it.  Consequently the inclusion of
the fppf `G`-torsors into the principal homogeneous `G`-spaces is not essentially surjective,
which is the obstruction to an equivalence of the two stacks.

## Main definitions

* `Stacks.Examples.RadicalTower.groupObj` is the group scheme `G` over `Spec ℚ`.
* `Stacks.Examples.RadicalTower.torsorObj` is the acted-on scheme `P` over `Spec ℚ`.

## Main results

* `Stacks.Examples.RadicalTower.isPseudoTorsor`: the action is a pseudo-torsor, that is the
  shear map `(g, x) ↦ (g • x, x)` is an isomorphism.
* `Stacks.Examples.RadicalTower.isFpqcTorsor`: `P` is a principal homogeneous `G`-space.
* `Stacks.Examples.RadicalTower.not_isFppfTorsor`: `P` is not an fppf `G`-torsor.
* `Stacks.Examples.RadicalTower.fpqcTorsor_not_isomorphic_fppfTorsor`: `P` is a principal
  homogeneous `G`-space isomorphic to no fppf `G`-torsor.  The statement of Stacks 077B, about
  the stacks `G-Principal` and `G-Torsors` themselves, is
  `Stacks.Examples.RadicalTower.exists_not_isEquivalence_fppfTorsors_toPrincipal` in
  `StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.StackComparison`.

## Implementation notes

The group-object structure on `G` is Mathlib's, coming from the Hopf algebra structure of a
group algebra.  The module-object structure on `P` is transported from the coaction along the
monoidal functor `Spec` by `CategoryTheory.Functor.LaxMonoidal.modObj`, and the pseudo-torsor
property is then the statement that the algebraic shear map of
`StacksFrontier.Examples.GroupSchemes.PrincipalNotFppf.Group` is an isomorphism, read through
`CategoryTheory.Functor.LaxMonoidal.mapModObj_leftSMul`.

Triviality over an fpqc covering uses the covering `{P → Spec ℚ}` itself, which is trivializing
because `P ×_{Spec ℚ} P → P` has the diagonal as a section.  The failure of fppf-local
triviality is the statement of
`Stacks.Examples.RadicalTower.not_forall_nonempty_hom_of_fppf`, and it rules out every fppf
torsor isomorphic to `P` because an isomorphism over the base carries local sections across.

## References

* [Stacks Project, Tag 077B](https://stacks.math.columbia.edu/tag/077B)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

namespace Stacks.Examples.RadicalTower

/-- The group scheme `∏ᵢ μ_{i+2}` over `Spec ℚ`, as an object over the base. -/
noncomputable abbrev groupObj : Over base :=
  (Spec (CommRingCat.of Coord)).asOver (Spec (CommRingCat.of ℚ))

/-- The radical tower, as an object over the base. -/
noncomputable abbrev torsorObj : Over base :=
  (Spec (CommRingCat.of Alg)).asOver (Spec (CommRingCat.of ℚ))

/-- The group-object structure of the group scheme, from the Hopf algebra structure of the
group algebra.  It is supplied by hand because instance search does not see through `asOver`. -/
noncomputable instance grpObjGroupObj : GrpObj groupObj :=
  AlgebraicGeometry.instGrpObjSpecAsOverSpec (R := CommRingCat.of ℚ) (A := CommRingCat.of Coord)

/-- The coaction, as a morphism of the opposite category of `ℚ`-algebras. -/
noncomputable abbrev coordOp : (CommAlgCat ℚ)ᵒᵖ := op (CommAlgCat.of ℚ Coord)

/-- The radical tower, as an object of the opposite category of `ℚ`-algebras. -/
noncomputable abbrev algOp : (CommAlgCat ℚ)ᵒᵖ := op (CommAlgCat.of ℚ Alg)

/-- The counit identity for the coaction, in the form of an equality of `ℚ`-algebra maps. -/
theorem counit_comp_coaction :
    (Algebra.TensorProduct.map (Bialgebra.counitAlgHom ℚ Coord) (AlgHom.id ℚ Alg)).comp
        coaction =
      (MonoidalCategoryStruct.leftUnitor (CommAlgCat.of ℚ Alg)).inv.hom := by
  refine algHom_ext (B := TensorProduct ℚ ℚ Alg) fun i => ?_
  have hc : Bialgebra.counitAlgHom ℚ Coord (MonoidAlgebra.single (gen i) (1 : ℚ)) = 1 :=
    (MonoidAlgebra.isGroupLikeElem_single_one (R := ℚ) (A := ℚ) (gen i)).counit_eq_one
  change (Algebra.TensorProduct.map (Bialgebra.counitAlgHom ℚ Coord) (AlgHom.id ℚ Alg))
      (coaction (root i)) = _
  rw [coaction_root, Algebra.TensorProduct.map_tmul, hc]
  change (1 : ℚ) ⊗ₜ[ℚ] (AlgHom.id ℚ Alg) (root i) = (Algebra.TensorProduct.lid ℚ Alg).symm _
  refine (Algebra.TensorProduct.lid ℚ Alg).injective ?_
  simp

/-- The coassociativity identity for the coaction, in the form of an equality of `ℚ`-algebra
maps. -/
theorem comul_comp_coaction :
    (Algebra.TensorProduct.map (Bialgebra.comulAlgHom ℚ Coord) (AlgHom.id ℚ Alg)).comp
        coaction =
      (Algebra.TensorProduct.assoc ℚ ℚ ℚ Coord Coord Alg).symm.toAlgHom.comp
        ((Algebra.TensorProduct.map (AlgHom.id ℚ Coord) coaction).comp coaction) := by
  refine algHom_ext (B := TensorProduct ℚ (TensorProduct ℚ Coord Coord) Alg) fun i => ?_
  have hc : Bialgebra.comulAlgHom ℚ Coord (MonoidAlgebra.single (gen i) (1 : ℚ)) =
      MonoidAlgebra.single (gen i) (1 : ℚ) ⊗ₜ[ℚ] MonoidAlgebra.single (gen i) (1 : ℚ) :=
    (MonoidAlgebra.isGroupLikeElem_single_one (R := ℚ) (A := ℚ) (gen i)).comul_eq_tmul_self
  change (Algebra.TensorProduct.map (Bialgebra.comulAlgHom ℚ Coord) (AlgHom.id ℚ Alg))
      (coaction (root i)) =
    (Algebra.TensorProduct.assoc ℚ ℚ ℚ Coord Coord Alg).symm
      ((Algebra.TensorProduct.map (AlgHom.id ℚ Coord) coaction) (coaction (root i)))
  rw [coaction_root, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hc,
    coaction_root]
  rfl

/-- The coaction as a module-object structure in the opposite category of `ℚ`-algebras. -/
noncomputable instance modObjOp : ModObj coordOp algOp where
  smul := (CommAlgCat.ofHom coaction).op
  one_smul := by
    refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext (AlgHom.ext fun a => ?_))
    exact congrArg (fun F : Alg →ₐ[ℚ] TensorProduct ℚ ℚ Alg => F a) counit_comp_coaction
  mul_smul := by
    refine Quiver.Hom.unop_inj (CommAlgCat.hom_ext (AlgHom.ext fun a => ?_))
    exact congrArg (fun F : Alg →ₐ[ℚ] TensorProduct ℚ (TensorProduct ℚ Coord Coord) Alg => F a)
      comul_comp_coaction

/-- `Spec` as a monoidal functor from `ℚ`-algebras to schemes over `Spec ℚ`. -/
noncomputable abbrev specFunctor : (CommAlgCat ℚ)ᵒᵖ ⥤ Over base :=
  algSpec (CommRingCat.of ℚ)

/-- `Spec` on `ℚ`-algebras is braided monoidal. -/
noncomputable instance : specFunctor.Braided := AlgebraicGeometry.braidedAlgSpec

/-- `Spec` on `ℚ`-algebras is monoidal. -/
noncomputable instance : specFunctor.Monoidal := Functor.Braided.toMonoidal

/-- The group-object structure on the image of the group algebra. -/
@[instance_reducible] noncomputable def monObjGroupObj : MonObj (specFunctor.obj coordOp) := by
  change MonObj groupObj
  infer_instance

/-- The unit of the group-object structure on the group scheme is the image of the counit. -/
theorem specFunctor_one :
    Functor.LaxMonoidal.ε specFunctor ≫ specFunctor.map (MonObj.one (X := coordOp)) =
      monObjGroupObj.one := by
  apply Over.OverMorphism.ext
  rfl

/-- The multiplication of the group-object structure on the group scheme is the image of the
comultiplication. -/
theorem specFunctor_mul :
    Functor.LaxMonoidal.μ specFunctor coordOp coordOp ≫
        specFunctor.map (MonObj.mul (X := coordOp)) = monObjGroupObj.mul := by
  apply Over.OverMorphism.ext
  rfl

/-- The action of the group scheme on the radical tower, obtained from the coaction by
applying `Spec`. -/
noncomputable instance modObjTorsor : ModObj groupObj torsorObj :=
  CategoryTheory.Functor.LaxMonoidal.modObj specFunctor (X := algOp) monObjGroupObj
    specFunctor_one specFunctor_mul

/-- The shear map of the action in the algebra category is the algebraic shear map. -/
theorem leftSMul_op_unop_hom :
    (ModObj.leftSMul coordOp algOp).unop.hom = shear := rfl

/-- The algebraic shear map is an isomorphism in the category of `ℚ`-algebras. -/
theorem isIso_ofHom_shear :
    IsIso (CommAlgCat.ofHom (R := ℚ) (X := Alg ⊗[ℚ] Alg) (Y := Coord ⊗[ℚ] Alg) shear) :=
  ⟨CommAlgCat.ofHom (R := ℚ) (X := Coord ⊗[ℚ] Alg) (Y := Alg ⊗[ℚ] Alg) unshear,
    CommAlgCat.hom_ext unshear_comp_shear, CommAlgCat.hom_ext shear_comp_unshear⟩

/-- The shear map of the action in the algebra category is an isomorphism. -/
theorem isIso_leftSMul_op : IsIso (ModObj.leftSMul coordOp algOp) := by
  refine (isIso_unop_iff _).mp ?_
  rw [show (ModObj.leftSMul coordOp algOp).unop =
    CommAlgCat.ofHom (R := ℚ) (X := Alg ⊗[ℚ] Alg) (Y := Coord ⊗[ℚ] Alg) shear from
      CommAlgCat.hom_ext rfl]
  exact isIso_ofHom_shear

/-- The action of `G` on `P` is a pseudo-torsor: the shear map `(g, x) ↦ (g • x, x)` is an
isomorphism, which says that the action is simply transitive. -/
theorem isPseudoTorsor : IsPseudoTorsor groupObj torsorObj := by
  have := isIso_leftSMul_op
  have h := CategoryTheory.Functor.LaxMonoidal.mapModObj_leftSMul specFunctor (X := algOp)
    monObjGroupObj specFunctor_one specFunctor_mul
  let _ : MonObj (specFunctor.obj coordOp) := monObjGroupObj
  let _ : ModObj (specFunctor.obj coordOp) (specFunctor.obj algOp) :=
    CategoryTheory.Functor.LaxMonoidal.modObj specFunctor (X := algOp) monObjGroupObj
      specFunctor_one specFunctor_mul
  change IsIso (ModObj.leftSMul (specFunctor.obj coordOp) (specFunctor.obj algOp))
  rw [h]
  infer_instance

/-- `P` is a principal homogeneous `G`-space: it is trivialized by the fpqc covering
`{P → Spec ℚ}`, over which it has the diagonal as a section. -/
theorem isFpqcTorsor : IsFpqcTorsor base groupObj torsorObj := by
  refine ⟨isPseudoTorsor, PUnit.{2}, fun _ => total, fun _ => proj, ?_, fun _ => ?_⟩
  · rw [Presieve.ofArrows_pUnit]
    exact singleton_proj_mem_fpqcPrecoverage
  · exact ⟨Over.homMk (pullback.lift (𝟙 total) (𝟙 total) rfl) (pullback.lift_snd _ _ _)⟩

/-- No fppf `G`-torsor is isomorphic to `P`: a trivializing fppf covering would give a morphism to
`P` on each of its members, which `not_forall_nonempty_hom_of_fppf` excludes. -/
private theorem false_of_isFppfTorsor_of_iso (Y : Over base) [ModObj groupObj Y]
    (hY : IsFppfTorsor base groupObj Y) (e : torsorObj ≅ Y) : False := by
  obtain ⟨-, I, T, f, hf, hsec⟩ := hY
  refine not_forall_nonempty_hom_of_fppf T f hf fun i => ?_
  obtain ⟨s⟩ := hsec i
  exact ⟨(s ≫ (Over.pullback (f i)).map e.inv).left ≫ pullback.fst torsorObj.hom (f i)⟩

/-- `P` is not an fppf `G`-torsor. -/
theorem not_isFppfTorsor : ¬ IsFppfTorsor base groupObj torsorObj :=
  fun h => false_of_isFppfTorsor_of_iso torsorObj h (Iso.refl _)

/-- Over `S = Spec ℚ` the group scheme `G = ∏ᵢ μ_{i+2}` has a principal homogeneous space, namely
`P = Spec ℚ[x₀, x₁, …]/(xᵢ ^ (i + 2) - 2)`, which is isomorphic to no fppf `G`-torsor, in the
slice of schemes over `Spec ℚ`.  This is the scheme-level form of the failure of essential
surjectivity in the proof of Stacks 077B; the statement of Stacks 077B itself, about the stacks
`G-Principal` and `G-Torsors` over the big fppf site, is
`Stacks.Examples.RadicalTower.exists_not_isEquivalence_fppfTorsors_toPrincipal`. -/
theorem fpqcTorsor_not_isomorphic_fppfTorsor :
    IsFpqcTorsor base groupObj torsorObj ∧
      ∀ (Y : Over base) (_ : ModObj groupObj Y),
        IsFppfTorsor base groupObj Y → ¬ Nonempty (torsorObj ≅ Y) := by
  exact ⟨isFpqcTorsor, fun Y _ hY ⟨e⟩ => false_of_isFppfTorsor_of_iso Y hY e⟩

end Stacks.Examples.RadicalTower

end
