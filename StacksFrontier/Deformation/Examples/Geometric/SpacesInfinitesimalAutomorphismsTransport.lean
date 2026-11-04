module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsAut

/-!
# The special fibre of a deformation is `X`

Let `X` be an algebraic space over the field `k`, `i : x₀ ⟶ xε` a pushforward of a point over
`k` of the deformation category of `X` to an object `Aε` of `𝒞_Λ` with a dual-number
coordinate, `X'` the total space of `xε`, `G ⊆ X'` its special fibre and `π : X' ⟶ X` the
retraction given by `i`.  This file proves that `π|_G : G ⟶ X` is an isomorphism, with inverse
the special-fibre map of `xε`.

## Main definitions

* `Deformation.Examples.spaceSpecialIso`: `G ≅ X`.

## References

* [Stacks Project, Tag 0E3Z](https://stacks.math.columbia.edu/tag/0E3Z)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

variable {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
  {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    (residueFieldObject.{u, u, u} Λ k)}
  {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
  (i : x₀.1 ⟶ xε.1)

/-- The special fibre of the total space of `xε`, as an algebraic space. -/
abbrev spacePointSpecialSpace : AlgebraicSpaces B (Spec (.of Λ)) hΛ :=
  ⟨(spacePointSpecial B hΛ hSpec X hX toK xε.1).1.toFunctor,
    (spacePointSpecial B hΛ hSpec X hX toK xε.1).2.1⟩

/-- `π|_G : G ⟶ X`. -/
abbrev spaceSpecialToX :
    spacePointSpecialSpace B hΛ hSpec X hX toK (xε := xε) ⟶ spaceOf B hΛ X hX :=
  subspaceInclusion B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
    (spacePointSpecial B hΛ hSpec X hX toK xε.1) ≫ spaceRetraction B hΛ hSpec X hX toK i

/-- The special-fibre map `X ⟶ G`. -/
abbrev spaceXToSpecial :
    spaceOf B hΛ X hX ⟶ spacePointSpecialSpace B hΛ hSpec X hX toK (xε := xε) :=
  ObjectProperty.homMk (spaceSpecialMapToSpecial B hΛ hSpec X hX toK xε.1)

/-- The structure arrow of `i` is compatible on bases. -/
theorem spaceRetraction_base_comp :
    i.left.base ≫ xε.1.hom.base = x₀.1.hom.base :=
  congrArg (fun m : x₀.1.left ⟶ spaceSpecialFiber B hΛ hSpec X hX toK => m.base) (Over.w i)

/-- `π` restricted to `G` followed by `X ⟶ Spec k` is the projection of `G` to `Spec k`. -/
theorem spacePointSpecial_ι_comp_retraction_comp_toK :
    (spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫
        (spaceRetraction B hΛ hSpec X hX toK i).hom ≫ toK =
      spacePointSpecialToK B hΛ hSpec X hX toK xε.1 := by
  have := isIso_yoneda_map_spaceBaseOverMap_residue B hΛ hSpec X hX toK (x₀ := x₀)
  refine (cancel_mono (yoneda.map (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base))).1 ?_
  have hY : yoneda.map (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base) =
      yoneda.map (spaceBaseOverMap B hΛ hSpec xε.1.hom.base) ≫
        yoneda.map (spaceBaseOverMap B hΛ hSpec i.left.base) := by
    rw [← Functor.map_comp, ← spaceBaseOverMap_comp, spaceRetraction_base_comp]
  calc ((spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫
        (spaceRetraction B hΛ hSpec X hX toK i).hom ≫ toK) ≫
        yoneda.map (spaceBaseOverMap B hΛ hSpec x₀.1.hom.base)
      = ((spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫ xε.1.left.toBase) ≫
          yoneda.map (spaceBaseOverMap B hΛ hSpec i.left.base) := by
        simp only [Category.assoc, spaceRetraction_comp_toK]
    _ = (spacePointSpecialToK B hΛ hSpec X hX toK xε.1 ≫
          yoneda.map (spaceBaseOverMap B hΛ hSpec xε.1.hom.base)) ≫
          yoneda.map (spaceBaseOverMap B hΛ hSpec i.left.base) :=
        congrArg (· ≫ _) (spacePointSpecial_ι_comp_toBase B hΛ hSpec X hX toK xε.1)
    _ = _ := (Category.assoc _ _ _).trans (congrArg _ hY.symm)

/-- `π|_G ≫ (X ⟶ G) = 𝟙`. -/
theorem spaceSpecialToX_comp_spaceXToSpecial :
    spaceSpecialToX B hΛ hSpec X hX toK i ≫ spaceXToSpecial B hΛ hSpec X hX toK (xε := xε) =
      𝟙 _ := by
  apply ObjectProperty.hom_ext
  refine (cancel_mono (spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι).1 ?_
  show ((spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫
      (spaceRetraction B hΛ hSpec X hX toK i).hom ≫
      spaceSpecialMapToSpecial B hΛ hSpec X hX toK xε.1) ≫
      (spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι =
    𝟙 _ ≫ (spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι
  rw [Category.id_comp]
  show (spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫
      (spaceRetraction B hΛ hSpec X hX toK i).hom ≫ spaceSpecialMap B hΛ hSpec X hX toK xε.1 =
    (spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι
  refine spaceTotal_hom_ext B hΛ hSpec X hX toK i ?_ ?_
  · simp [spaceSpecialMap_comp_spaceRetraction B hΛ hSpec X hX toK i]
  · calc ((spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫
          (spaceRetraction B hΛ hSpec X hX toK i).hom ≫
            spaceSpecialMap B hΛ hSpec X hX toK xε.1) ≫ xε.1.left.toBase
        = ((spacePointSpecial B hΛ hSpec X hX toK xε.1).1.ι ≫
            (spaceRetraction B hΛ hSpec X hX toK i).hom ≫ toK) ≫
              yoneda.map (spaceBaseOverMap B hΛ hSpec xε.1.hom.base) := by
          simp only [Category.assoc, (spaceSpecialMap_isPullback B hΛ hSpec X hX toK xε.1).w]
      _ = spacePointSpecialToK B hΛ hSpec X hX toK xε.1 ≫
              yoneda.map (spaceBaseOverMap B hΛ hSpec xε.1.hom.base) :=
          congrArg (· ≫ _) (spacePointSpecial_ι_comp_retraction_comp_toK B hΛ hSpec X hX toK i)
      _ = _ := (spacePointSpecial_ι_comp_toBase B hΛ hSpec X hX toK xε.1).symm

/-- `(X ⟶ G) ≫ π|_G = 𝟙`. -/
theorem spaceXToSpecial_comp_spaceSpecialToX :
    spaceXToSpecial B hΛ hSpec X hX toK (xε := xε) ≫ spaceSpecialToX B hΛ hSpec X hX toK i =
      𝟙 _ :=
  ObjectProperty.hom_ext _ (spaceSpecialMap_comp_spaceRetraction B hΛ hSpec X hX toK i)

/-- **The special fibre of `xε` is `X`**: `π|_G : G ≅ X`. -/
def spaceSpecialIso :
    spacePointSpecialSpace B hΛ hSpec X hX toK (xε := xε) ≅ spaceOf B hΛ X hX where
  hom := spaceSpecialToX B hΛ hSpec X hX toK i
  inv := spaceXToSpecial B hΛ hSpec X hX toK
  hom_inv_id := spaceSpecialToX_comp_spaceXToSpecial B hΛ hSpec X hX toK i
  inv_hom_id := spaceXToSpecial_comp_spaceSpecialToX B hΛ hSpec X hX toK i

end Deformation.Examples

end
