module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ScalarExtensionDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.StructureSheafComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionPresentations

/-!
# The restriction map on the étale cohomology of `𝐆_a`: multiplication and `Ext`

For a morphism of schemes `g : Y ⟶ X`, `Stacks.ArtinSchreier.additiveRestriction` is restriction
along `g` followed by the comparison `g⁻¹ 𝐆_{a,X} ⟶ 𝐆_{a,Y}`, a map
`H^q(X_étale, 𝐆_a) ⟶ H^q(Y_étale, 𝐆_a)`. It is compatible with multiplication by global
functions and is computed by the adjunction map on `Ext`.

## Main results

* `Stacks.ArtinSchreier.additiveDirectImageComparison_smul`: the comparison
  `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}` intertwines `additiveSheafSmul X a` with
  `additiveSheafSmul Y (g.appTop a)`.
* `Stacks.ArtinSchreier.additiveRestriction_sheafH_map_of_directImage`: the restriction map
  intertwines the maps induced by sheaf endomorphisms that the comparison
  `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}` intertwines.
* `Stacks.ArtinSchreier.additiveRestriction_eq_extMap`: it is the adjunction map on `Ext`
  applied to the image under `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.EtaleCohomology

universe w u

namespace Stacks.ArtinSchreier

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- The comparison intertwines multiplication by a global function of `X` with multiplication by
its pullback to `Y`. -/
theorem additiveDirectImageComparison_smul (a : Γ(X, ⊤)) :
    additiveSheafSmul X a ≫ additiveDirectImageComparison.{u, u + 1} g =
      additiveDirectImageComparison.{u, u + 1} g ≫
        (etaleAbelianDirectImage.{u, 0} g).map (additiveSheafSmul Y (g.appTop a)) := by
  ext U x
  obtain ⟨x, rfl⟩ := ofSection_surjective.{u, u + 1} (X := X) (U := U.unop) x
  change ofSection.{u, u + 1} (U := (smallEtaleBaseChange g).obj U.unop)
      ((pullback.fst U.unop.hom g).appTop (x * pullTop U.unop a)) =
    ofSection.{u, u + 1} (U := (smallEtaleBaseChange g).obj U.unop)
      ((pullback.fst U.unop.hom g).appTop x *
        (pullback.snd U.unop.hom g).appTop (g.appTop a))
  rw [map_mul]
  congr 2
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using
    congrArg (fun h => h.appTop a) (pullback.condition (f := U.unop.hom) (g := g))

section Cohomology

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- `Stacks.ArtinSchreier.additiveRestriction` intertwines the maps induced by morphisms of
sheaves intertwined by the comparison `𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}`. -/
theorem additiveRestriction_sheafH_map_of_directImage
    {φ : additiveSheaf.{u, u + 1} X ⟶ additiveSheaf.{u, u + 1} X}
    {ψ : additiveSheaf.{u, u + 1} Y ⟶ additiveSheaf.{u, u + 1} Y}
    (h : φ ≫ additiveDirectImageComparison.{u, u + 1} g =
      additiveDirectImageComparison.{u, u + 1} g ≫ (etaleAbelianDirectImage.{u, 0} g).map ψ)
    (q : ℕ) (x : Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) q) :
    additiveRestriction g q (Sheaf.H.map φ q x) =
      Sheaf.H.map ψ q (additiveRestriction g q x) := by
  simp only [additiveRestriction, AddMonoidHom.coe_comp, Function.comp_apply]
  rw [Sheaf.H.map_apply φ, etaleCohomologyRestrictionMap_comp_mk₀, ← Sheaf.H.map_apply,
    ← Sheaf.H.map_comp_apply, inverseImage_map_comp_additiveInverseImageComparison g h,
    Sheaf.H.map_comp_apply]

/-- The restriction of `𝐆_a`-cohomology is the adjunction map
`Ext^q(ℤ, g_* 𝐆_{a,Y}) ⟶ Ext^q(g⁻¹ ℤ, 𝐆_{a,Y})` applied to the image under the comparison
`𝐆_{a,X} ⟶ g_* 𝐆_{a,Y}`, followed by the identification `g⁻¹ ℤ = ℤ`. -/
theorem additiveRestriction_eq_extMap (q : ℕ)
    (x : Sheaf.H.{w, u + 1} (additiveSheaf.{u, u + 1} X) q) :
    additiveRestriction g q x =
      (Ext.mk₀ ((etaleAbelianInverseImageConstantIso.{u, 0} g).app
          (AddCommGrpCat.of (ULift ℤ))).inv).comp
        (Stacks.ExtAdjunction.extMap (etaleAbelianInverseImageDirectImageAdj.{u, 0} g) _ _ q
          (Sheaf.H.map (additiveDirectImageComparison.{u, u + 1} g) q x)) (zero_add q) := by
  simp only [additiveRestriction, AddMonoidHom.coe_comp, Function.comp_apply,
    Stacks.ExtAdjunction.extMap_apply, Sheaf.H.map_apply, etaleCohomologyRestrictionMap_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀]
  congr 3

end Cohomology

end Stacks.ArtinSchreier

end
