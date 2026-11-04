module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesRimSchlessinger
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceNaturality
public import StacksFrontier.Deformation.Examples.Geometric.RingsTangentSpaceEquivTangent

/-!
# The class map on isomorphism classes of deformations of an algebraic space

The class of a deformation of an algebraic space `X` over `k[V]`
(`Deformation.Examples.spaceTangentFiberClass`) only depends on its isomorphism class, so it
descends to the value at `V` of the tangent-space set functor `V ↦ Def_X(k[V])/≅` of the
deformation category of `X` (`Deformation.Examples.spaceTangentExtClassAt`), naturally in `V`
against `V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)`: the shape consumed by
`Deformation.tangentSpaceLinearEquivOfNaturalBijection` in the proof of
[Stacks Project, Tag 0E41].

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
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

/-- The deformation category of `X`, as a based category. -/
abbrev spaceDeformationBased : BasedCategory (ArtinianLocalAlgCat.{u, u, u} Λ k) :=
  BasedCategory.ofFunctor (spaceDeformationProjection B hΛ hSpec X hX toK)

/-- The cofiberedness of the deformation category of `X` (Stacks 0E3Z, 0E40). -/
theorem spaceDeformation_cofibered :
    IsCofiberedInGroupoids (spaceDeformationBased B hΛ hSpec X hX toK).p :=
  (isDeformationCategory_spaceDeformationProjection B hΛ hSpec X hX toK).predeformation.cofibered

/-- A morphism of points lying over `k[g]` satisfies the hypothesis of
`Deformation.Examples.spaceTangentFiberClass_map`. -/
theorem spaceFiber_base_hom_eq {V W : FGModuleCat.{u} k}
    (x : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V))
    (y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj W))
    (g : V ⟶ W) (φ : x.1 ⟶ y.1)
    [(spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift
      ((squareZeroExtensionArtinian Λ k).map g) φ] :
    φ.left.base = eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK x) ≫
      (squareZeroExtensionArtinian Λ k).map g ≫
        eqToHom (spaceFiber_base_eq B hΛ hSpec X hX toK y).symm :=
  IsHomLift.fac' (spaceDeformationProjection B hΛ hSpec X hX toK)
    ((squareZeroExtensionArtinian Λ k).map g) φ

/-- The class of a deformation over `k[V]` only depends on its isomorphism class. -/
theorem spaceTangentFiberClass_congr (V : FGModuleCat.{u} k)
    (x x' : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V))
    (h : IsIsomorphic x x') :
    spaceTangentFiberClass B hΛ hSpec X hX toK x =
      spaceTangentFiberClass B hΛ hSpec X hX toK x' := by
  obtain ⟨e⟩ := h
  have : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift
      ((squareZeroExtensionArtinian Λ k).map (𝟙 V)) e.hom.1 := by
    rw [CategoryTheory.Functor.map_id]; exact e.hom.2
  refine Eq.trans ?_ (spaceTangentFiberClass_map B hΛ hSpec X hX toK (𝟙 V) e.hom.1
    (spaceFiber_base_hom_eq B hΛ hSpec X hX toK x x' (𝟙 V) e.hom.1)).symm
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **The class map on isomorphism classes of deformations over `k[V]`.** -/
def spaceTangentExtClassAt (V : FGModuleCat.{u} k)
    (z : (associatedTangentSpaceSetFunctor (spaceDeformationBased B hΛ hSpec X hX toK)
      (spaceDeformation_cofibered B hΛ hSpec X hX toK)).obj V) :
    (spaceTangentExtFunctor B hΛ hSpec X hX toK).obj V :=
  Quotient.liftOn
    (cast (isomorphismClasses_obj (spaceDeformationBased B hΛ hSpec X hX toK)
      (spaceDeformation_cofibered B hΛ hSpec X hX toK) ((squareZeroExtensionArtinian Λ k).obj V)) z)
    (spaceTangentFiberClass B hΛ hSpec X hX toK)
    (spaceTangentFiberClass_congr B hΛ hSpec X hX toK V)

/-- The class map on the class of a point of the fibre. -/
theorem spaceTangentExtClassAt_classOf (V : FGModuleCat.{u} k)
    (x : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj V)) :
    spaceTangentExtClassAt B hΛ hSpec X hX toK V
      (classOf (spaceDeformationBased B hΛ hSpec X hX toK)
        (spaceDeformation_cofibered B hΛ hSpec X hX toK) x) =
      spaceTangentFiberClass B hΛ hSpec X hX toK x := by
  have h := classOf_eq (spaceDeformationBased B hΛ hSpec X hX toK)
    (spaceDeformation_cofibered B hΛ hSpec X hX toK) x
  exact congrArg (fun q => Quotient.liftOn q (spaceTangentFiberClass B hΛ hSpec X hX toK)
    (spaceTangentFiberClass_congr B hΛ hSpec X hX toK V)) h

/-- **The class map on isomorphism classes is natural in `V`**, against
`V ↦ Ext¹(NL_{X/k}, 𝒪_X ⊗_k V)`. -/
theorem spaceTangentExtClassAt_naturality {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    (z : (associatedTangentSpaceSetFunctor (spaceDeformationBased B hΛ hSpec X hX toK)
      (spaceDeformation_cofibered B hΛ hSpec X hX toK)).obj V) :
    spaceTangentExtClassAt B hΛ hSpec X hX toK W
        ((associatedTangentSpaceSetFunctor (spaceDeformationBased B hΛ hSpec X hX toK)
          (spaceDeformation_cofibered B hΛ hSpec X hX toK)).map g z) =
      (spaceTangentExtFunctor B hΛ hSpec X hX toK).map g
        (spaceTangentExtClassAt B hΛ hSpec X hX toK V z) := by
  obtain ⟨x, rfl⟩ := classOf_surjective (spaceDeformationBased B hΛ hSpec X hX toK)
    (spaceDeformation_cofibered B hΛ hSpec X hX toK) ((squareZeroExtensionArtinian Λ k).obj V) z
  obtain ⟨y₀, φ, hφ⟩ := exists_pushforward (spaceDeformation_cofibered B hΛ hSpec X hX toK)
    ((squareZeroExtensionArtinian Λ k).map g) x.1 x.2
  let : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift
      ((squareZeroExtensionArtinian Λ k).map g) φ := hφ
  let y : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
      ((squareZeroExtensionArtinian Λ k).obj W) :=
    ⟨y₀, IsHomLift.codomain_eq (spaceDeformationProjection B hΛ hSpec X hX toK)
      ((squareZeroExtensionArtinian Λ k).map g) φ⟩
  have hmap : (associatedTangentSpaceSetFunctor (spaceDeformationBased B hΛ hSpec X hX toK)
      (spaceDeformation_cofibered B hΛ hSpec X hX toK)).map g
        (classOf (spaceDeformationBased B hΛ hSpec X hX toK)
          (spaceDeformation_cofibered B hΛ hSpec X hX toK) x) =
      classOf (spaceDeformationBased B hΛ hSpec X hX toK)
        (spaceDeformation_cofibered B hΛ hSpec X hX toK) y :=
    map_classOf (spaceDeformationBased B hΛ hSpec X hX toK)
      (spaceDeformation_cofibered B hΛ hSpec X hX toK)
      ((squareZeroExtensionArtinian Λ k).map g) x y φ
  refine (congrArg (spaceTangentExtClassAt B hΛ hSpec X hX toK W) hmap).trans ?_
  refine (spaceTangentExtClassAt_classOf B hΛ hSpec X hX toK W y).trans ?_
  refine (spaceTangentFiberClass_map B hΛ hSpec X hX toK g φ
    (spaceFiber_base_hom_eq B hΛ hSpec X hX toK x y g φ)).trans ?_
  exact congrArg _ (spaceTangentExtClassAt_classOf B hΛ hSpec X hX toK V x).symm

end Deformation.Examples

end
