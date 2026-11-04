module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionNatural
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionPush
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdealMap
public import
  StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismObstructionSourceIdealTransition
public import StacksFrontier.Deformation.RingedSpaceThickening.SchemeDeformationExtClassNaturality

/-!
# The class `Push(Y')` of a deformation of the target in the obstruction of Stacks 0E3V

Let `f : X → Y` be a morphism of schemes over `k`, `M` a finite-dimensional `k`-vector space and
`Y'` a deformation of `Y` over `k[M]`. The inverse image `f⁻¹𝒪_{Y'}` is a square-zero extension of
`f⁻¹𝒪_Y` by `𝒪_X ⊗_k M` (`Deformation.Examples.schemeMorphismPushExtension`); its class,
transferred to `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`, is the class `Push(Y')`. This file proves
that the class is natural in the coefficient module along morphisms of deformations.

## Main definitions

* `Deformation.Examples.schemeMorphismObstructionPush`: the class `Push(Y')`.

## Main results

* `Deformation.Examples.schemeMorphismObstructionPush_naturality`: `Push` is natural along
  morphisms of deformations over maps of square-zero bases.
* `Deformation.Examples.schemeMorphismObstructionPush_isIsomorphic`: `Push` is invariant under
  isomorphism.
* `Deformation.Examples.pulledNaiveCotangentTransfer_extClass_of_hom`: a morphism of the
  extended structure sheaves of two square-zero extensions of `f⁻¹𝒪_Y` over `k`, over `f⁻¹𝒪_Y`
  and inducing the coefficient map `𝒪_X ⊗_k M ⟶ 𝒪_X ⊗_k N` on the ideals, carries one
  transferred class to the other.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal kernelIdeal_le_comap hom_of_comp_eq)

universe u

namespace Deformation.Examples

attribute [local instance] HasDerivedCategory.standard

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))


/-- If a class `t` on the fibres over the square-zero objects `k[M]` is natural along every
morphism of deformations lying over a map `k[M] ⟶ k[N]` induced by `g : M ⟶ N`, then it takes
isomorphic objects of one fibre to the same value. -/
theorem eq_of_isIsomorphic_of_natural {𝒳 : Type*} [Category 𝒳]
    (p : 𝒳 ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k) (G : FGModuleCat.{u} k ⥤ ModuleCat.{u + 1} k)
    (t : ∀ M : FGModuleCat.{u} k, p.Fiber ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M) →
      G.obj M)
    (hnat : ∀ {M N : FGModuleCat.{u} k} (g : M ⟶ N) x y (a : x.1 ⟶ y.1),
      p.IsHomLift ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a → t N y = G.map g (t M x))
    (M : FGModuleCat.{u} k) (x x' : p.Fiber ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (h : IsIsomorphic x x') : t M x = t M x' := by
  obtain ⟨e⟩ := h
  have hlift : p.IsHomLift ((squareZeroExtensionArtinian.{u, u, u} Λ k).map (𝟙 M)) e.hom.1 := by
    rw [CategoryTheory.Functor.map_id]
    exact e.hom.2
  rw [hnat (𝟙 M) x x' e.hom.1 hlift, CategoryTheory.Functor.map_id]
  rfl

/-- Let `P`, `P'` be square-zero extensions of `f⁻¹𝒪_Y` over `k` by `𝒪_X ⊗_k M` and `𝒪_X ⊗_k N`,
and let `θ : 𝒪_P ⟶ 𝒪_{P'}` be compatible with the `k`-algebra structures and the reductions and
induce `𝒪_X ⊗_k g` on the ideals. Then the class of `P'` in
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k N)` is the class of `P` pushed forward along `g`. -/
theorem pulledNaiveCotangentTransfer_extClass_of_hom {M N : FGModuleCat.{u} k} (g : M ⟶ N)
    (P : RingedSpaceThickening.AlgebraSquareZeroExtension (schemeMorphismInverseImageBase f pY)
      (schemeMorphismPushCoefficients f pY M))
    (P' : RingedSpaceThickening.AlgebraSquareZeroExtension (schemeMorphismInverseImageBase f pY)
      (schemeMorphismPushCoefficients f pY N))
    (θ : P.sheaf ⟶ P'.sheaf) (hbase : P.base ≫ θ = P'.base)
    (hred : θ ≫ P'.reduction = P.reduction)
    (hideal : ∀ (V : (TopologicalSpace.Opens X.carrier)ᵒᵖ) (z : ↥(kernelIdeal P.reduction.hom V)),
      P'.ideal.app V ⟨θ.hom.app V z, kernelIdeal_le_comap P.reduction.hom P'.reduction.hom
        θ.hom (hom_of_comp_eq hred) V z.2⟩ =
        (((schemeMorphismCoefficientSheafFunctor f pY).map g).val.app V).hom (P.ideal.app V z)) :
    haveI := P.reduction_surjective
    haveI := P'.reduction_surjective
    RingedSpaceThickening.pulledNaiveCotangentTransfer f.toLRSHom.toShHom pY.toLRSHom.toShHom
        (schemeMorphismCoefficientSheaf f pY N) P'.toPresented.extClass =
      (schemeMorphismObstructionExtFunctor f pY).map g
        (RingedSpaceThickening.pulledNaiveCotangentTransfer f.toLRSHom.toShHom
          pY.toLRSHom.toShHom (schemeMorphismCoefficientSheaf f pY M) P.toPresented.extClass) := by
  have := P.reduction_surjective
  have := P'.reduction_surjective
  refine (congrArg (RingedSpaceThickening.pulledNaiveCotangentTransfer f.toLRSHom.toShHom
    pY.toLRSHom.toShHom (schemeMorphismCoefficientSheaf f pY N))
    (RingedSpaceThickening.AlgebraSquareZeroExtension.extClass_comp_eq_extClass_of_hom P P'
      ((RingedSpaceModuleAdjunction.modulePushforward
        (RingedSpace.inverseImageSourceInclusion f.toLRSHom.toShHom)).map
          ((schemeMorphismCoefficientSheafFunctor f pY).map g)) θ hbase hred hideal).symm).trans ?_
  exact RingedSpaceThickening.pulledNaiveCotangentTransfer_naturality f.toLRSHom.toShHom
    pY.toLRSHom.toShHom ((schemeMorphismCoefficientSheafFunctor f pY).map g) _

variable (M : FGModuleCat.{u} k)
  (yε : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))

/-- The class `Push(Y')` of a deformation `Y'` of the target in
`Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`: the class of the square-zero extension `f⁻¹𝒪_{Y'}` of
`f⁻¹𝒪_Y` by `𝒪_X ⊗_k M`, with its canonical map of ideals
`Deformation.Examples.schemeMorphismSourceIdeal`, transferred along
`Ext¹_{f⁻¹𝒪_Y}(NL_{X_A/k}, ι_*(𝒪_X ⊗_k M)) = Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`. -/
def schemeMorphismObstructionPush : (schemeMorphismObstructionExtFunctor f pY).obj M :=
  haveI := (schemeMorphismPushExtension f pY yε
    (schemeMorphismSourceIdeal f pY yε)).reduction_surjective
  RingedSpaceThickening.pulledNaiveCotangentTransfer f.toLRSHom.toShHom pY.toLRSHom.toShHom
    (schemeMorphismCoefficientSheaf f pY M)
    (schemeMorphismPushExtension f pY yε (schemeMorphismSourceIdeal f pY yε)).toPresented.extClass

/-- The class `Push(Y')` is the transfer of the extension class of the square-zero extension
`f⁻¹𝒪_{Y'}` of `f⁻¹𝒪_Y` by `𝒪_X ⊗_k M`. -/
theorem schemeMorphismObstructionPush_def :
    haveI := (schemeMorphismPushExtension f pY yε
      (schemeMorphismSourceIdeal f pY yε)).reduction_surjective
    schemeMorphismObstructionPush f pY M yε =
      RingedSpaceThickening.pulledNaiveCotangentTransfer f.toLRSHom.toShHom pY.toLRSHom.toShHom
        (schemeMorphismCoefficientSheaf f pY M)
        (schemeMorphismPushExtension f pY yε
          (schemeMorphismSourceIdeal f pY yε)).toPresented.extClass :=
  rfl

variable {M} in
/-- `Push` is natural in the coefficient module: for a morphism `a` of deformations of `Y` over
the map `k[M] ⟶ k[N]` of `g : M ⟶ N`, the class `Push` of the target of `a` is the class of its
source pushed forward along `𝒪_X ⊗_k g`. -/
theorem schemeMorphismObstructionPush_naturality {N : FGModuleCat.{u} k} (g : M ⟶ N)
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M))
    (y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N)) (a : x.1 ⟶ y.1)
    (ha : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a) :
    schemeMorphismObstructionPush f pY N y =
      (schemeMorphismObstructionExtFunctor f pY).map g (schemeMorphismObstructionPush f pY M x) :=
  pulledNaiveCotangentTransfer_extClass_of_hom f pY g
    (schemeMorphismPushExtension f pY x (schemeMorphismSourceIdeal f pY x))
    (schemeMorphismPushExtension f pY y (schemeMorphismSourceIdeal f pY y))
    (sourceIdealTransition f a) (schemeMorphismPushBase_comp_sourceIdealTransition f ha)
    (sourceIdealTransition_comp_reduction f a)
    (schemeMorphismSourceIdeal_transition f ha)

/-- Isomorphic deformations of `Y` over `k[M]` have the same class `Push`. -/
theorem schemeMorphismObstructionPush_isIsomorphic
    (y y' : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).Fiber
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj M)) (h : IsIsomorphic y y') :
    schemeMorphismObstructionPush f pY M y = schemeMorphismObstructionPush f pY M y' :=
  eq_of_isIsomorphic_of_natural
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
    (schemeMorphismObstructionExtFunctor f pY) (schemeMorphismObstructionPush f pY)
    (fun g x y a ha => schemeMorphismObstructionPush_naturality f pY g x y a ha) M y y' h

end Deformation.Examples

end
