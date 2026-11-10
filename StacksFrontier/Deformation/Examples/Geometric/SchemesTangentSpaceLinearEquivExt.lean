module

public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationCoordinateIdealNatural
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceLinearEquiv
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTangentSpaceExt
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjTwistMono.Trivialized

/-!
# The second display of Stacks 0DY9 as a `k`-linear equivalence

The class of a flat deformation of `X` over `k[V]` in `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)`
(`Deformation.Examples.tangentExtClassAt`) is natural in `V`, since the difference class of
[Stacks Project, Tag 08UC] is natural for base change of solutions. With its bijectivity at
`V = k` this makes it a `k`-linear equivalence of the tangent space `T𝓓_X`, with the canonical
vector-space structure of [Stacks Project, Tag 06IH], with `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`.

## Main results

* `Deformation.Examples.tangentExtClassAt_naturality`: the class map is natural in `V`.
* `Deformation.Examples.schemeTangentSpaceLinearEquivExt`: **the second display of
  [Stacks Project, Tag 0DY9]**, `T𝓓_X ≃ₗ[k] Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`.
* `Deformation.Examples.schemeTangentSpaceLinearEquivExt_classOf`: the identification is the
  difference class with the trivial deformation.
* `Deformation.Examples.schemeTangentSpaceLinearEquivExt_trivial`: the trivial deformation goes
  to `0`.

## Implementation notes

`Deformation.tangentSpaceLinearEquivOfNaturalBijection` turns the natural family of classes into a
linear equivalence at the rank-one module `V = k`; the coefficients are then changed along
`𝒪_X ⊗_k k ≅ 𝒪_X` (`Deformation.Examples.coefficientSheafRankOneIso`), and the class is carried
from the model of the derived category in which the acting group of Tag 08UC is built to the one
of `AlgebraicGeometry.Scheme.naiveCotangentExt`, both `k`-linearly. The bijection of
`Deformation.Examples.schemeTangentSpaceEquivExt` is the same identification at the dual numbers
`k[ε]` presented as `k ⊕ k ε`.

## References

* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpaceThickening

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] (X : Over (Spec (CommRingCat.of k)))

/-- The difference class only depends on the isomorphism class of the second solution. -/
theorem differenceClass_congr_right {X' S S' : RingedSpace.{u, u}} {t : S ⟶ S'}
    {ht : IsFirstOrderThickening t} {f : X' ⟶ S}
    {G : SheafOfModules.{u} (structureSheafRing X')}
    {c : (RingedSpaceModuleAdjunction.modulePullback f).obj
      ((RingedSpaceModuleAdjunction.modulePullback t).obj
        (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
    (Q₁ : DeformationSolution t ht f G c) {Q₂ Q₂' : DeformationSolution t ht f G c}
    (h : Isomorphic Q₂ Q₂') :
    AlgebraicGeometry.RingedSpaceThickening.differenceClass Q₁ Q₂ =
      AlgebraicGeometry.RingedSpaceThickening.differenceClass Q₁ Q₂' := by
  have : Nonempty (DeformationSolution t ht f G c) := ⟨Q₁⟩
  let := solutionClassesAddTorsor (t := t) (ht := ht) (f := f) (G := G) (c := c)
  exact (AlgebraicGeometry.RingedSpaceThickening.vsub_mk_mk (t := t) (ht := ht) (f := f)
    (G := G) (c := c) Q₁ Q₂).symm.trans
    ((congrArg ((⟦Q₁⟧ : SolutionClasses t ht f G c) -ᵥ ·) (Quotient.sound h)).trans
      (AlgebraicGeometry.RingedSpaceThickening.vsub_mk_mk (t := t) (ht := ht) (f := f)
        (G := G) (c := c) Q₁ Q₂'))

/-- The arrow `X ×_k Spec k[V] → X ×_k Spec k[W]` lies over `k[g]`. -/
instance isHomLift_trivialDeformationMap {V W : FGModuleCat.{u} k} (g : V ⟶ W) :
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) (trivialDeformationMap X g) := by
  rw [← trivialDeformationMap_base X g]
  exact Functor.IsHomLift.map _

section Std

attribute [local instance 10000] HasDerivedCategory.standard

/-- The change of coefficients along `f^* 𝒥 ≅ 𝒪_X ⊗_k V` is postcomposition. -/
theorem coordExtCoefficientsAddEquiv_apply (V : FGModuleCat.{u} k)
    (e : extOneNaiveCotangent X.hom.toLRSHom.toShHom
      (SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) V) X)) :
    coordExtCoefficientsAddEquiv X V e =
      e ≫ ((DerivedCategory.singleFunctor _ 0).map
        (coordPulledIdealIso (Λ := Λ) V X).hom)⟦(1 : ℤ)⟧' := by
  change 𝟙 _ ≫ e ≫ _ = _
  exact Category.id_comp _

/-- **The class of a deformation over `k[V]` is natural in `V`.** For an arrow `x ⟶ y` of
deformations over `k[g] : k[V] → k[W]`, the class of `y` is the class of `x` pushed along
`𝒪_X ⊗_k g`: the solution of `y` is the base change of that of `x`, so is the trivial one of the
trivial one, and the difference class is natural for base change. -/
theorem fiberExtClassAt_naturality {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase V))
    (y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase W))
    (a : x.1 ⟶ y.1) [(schemeDeformationCategoryProjection X).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) a] :
    fiberExtClassAt X W y = (schemeTangentExtFunctor X).map g (fiberExtClassAt X V x) := by
  have hy := isomorphic_fiberSolution_baseChange (Λ := Λ) g x y a
  have ht := isomorphic_fiberSolution_baseChange (Λ := Λ) g (trivialFiberAt X V)
    (trivialFiberAt X W)
    (trivialDeformationMap X g)
  have hd := (differenceClass_congr_left _ hy).trans ((differenceClass_congr_right _ ht).trans
    (DeformationSolution.differenceClass_baseChange _ _ _ _ _ _ _ _))
  have hS : ((DerivedCategory.singleFunctor _ 0).map (baseChangeIdealMap X.hom.toLRSHom.toShHom _
        (residueSpecMap_toShHom_comp_baseSpecMap
          ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g))))⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor _ 0).map (coordPulledIdealIso (Λ := Λ) W X).hom)⟦(1 : ℤ)⟧' =
      ((DerivedCategory.singleFunctor _ 0).map (coordPulledIdealIso (Λ := Λ) V X).hom)⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor _ 0).map
        ((coefficientSheafFunctor X.hom).map g))⟦(1 : ℤ)⟧' := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      baseChangeIdealMap_coordPulledIdealIso (Λ := Λ) X g]
  rw [schemeTangentExtFunctor_map_apply]
  refine (coordExtCoefficientsAddEquiv_apply X W _).trans (Eq.trans ?_
    (congrArg (· ≫ _) (coordExtCoefficientsAddEquiv_apply X V _)).symm)
  refine (congrArg (· ≫ _) hd).trans ?_
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hS)).trans (Category.assoc _ _ _).symm

/-- **The class map on isomorphism classes is natural in `V`**, against the functor
`V ↦ Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k V)`: the tangent-space set functor sends the class of a
deformation to the class of a pushforward of it. -/
theorem tangentExtClassAt_naturality {V W : FGModuleCat.{u} k} (g : V ⟶ W)
    (z : (associatedTangentSpaceSetFunctor (schemeDeformationBased (Λ := Λ) X)
      (schemeDeformation_cofibered X)).obj V) :
    tangentExtClassAt X W ((associatedTangentSpaceSetFunctor (schemeDeformationBased (Λ := Λ) X)
        (schemeDeformation_cofibered X)).map g z) =
      (schemeTangentExtFunctor X).map g (tangentExtClassAt X V z) := by
  obtain ⟨x, rfl⟩ := classOf_surjective (schemeDeformationBased (Λ := Λ) X)
    (schemeDeformation_cofibered X) ((squareZeroExtensionArtinian Λ k).obj V) z
  obtain ⟨y₀, φ, hφ⟩ := exists_pushforward (schemeDeformation_cofibered X)
    ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) x.1 x.2
  have : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).IsHomLift
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) φ := hφ
  let y : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber (coordBase W) :=
    ⟨y₀, IsHomLift.codomain_eq (schemeDeformationCategoryProjection X)
      ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g) φ⟩
  refine (congrArg (tangentExtClassAt X W) (map_classOf (schemeDeformationBased (Λ := Λ) X)
    (schemeDeformation_cofibered X) ((squareZeroExtensionArtinian.{u, u, u} Λ k).map g)
      x y φ)).trans ?_
  refine (tangentExtClassAt_classOf X W y).trans ?_
  refine (fiberExtClassAt_naturality X g x y φ).trans ?_
  exact congrArg _ (tangentExtClassAt_classOf X V x).symm

end Std

/-- Schlessinger's condition (S2) for the functor of isomorphism classes of deformations of `X`,
which exposes the canonical vector-space structure of [Stacks Project, Tag 06IH] on `T𝓓_X`: the
deformation category of `X` is a deformation category ([Stacks Project, Tag 0DY8]), so it
satisfies (RS). -/
theorem schlessingerConditionS2_schemeDeformation :
    SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X))) :=
  schlessingerConditionS2_of_isIsomorphismClasses (schemeDeformationBased (Λ := Λ) X)
    (schemeDeformation_cofibered X)
    (schlessingerConditionS2_of_satisfiesRS
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).satisfiesRS)
    (.inl (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation)

/-- **The coefficient sheaf at the rank-one module is the structure sheaf**: `𝒪_X ⊗_k k = 𝒪_X`, as
`k^~` is the structure sheaf of `Spec k` and the pullback of a structure sheaf is the structure
sheaf. -/
noncomputable def coefficientSheafRankOneIso :
    (coefficientSheafFunctor X.hom).obj (FGModuleCat.of k k) ≅ structureSheafModules X.left :=
  (Scheme.Modules.pullback X.hom).mapIso tildeSelf ≪≫
    Stacks.AlgebraicGeometry.ProjTwistMono.pullbackObjUnitIso X.hom

section Std

attribute [local instance 10000] HasDerivedCategory.standard

/-- The tangent space with its canonical vector-space structure is
`Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X ⊗_k k)`: the class map is natural in the coefficient module and
bijective at the rank-one module. -/
noncomputable def schemeTangentSpaceLinearEquivExtRankOne :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) X).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)))) :=
      ⟨schlessingerConditionS2_schemeDeformation X⟩
    schemeTangentSpace (Λ := Λ) (k := k) X ≃ₗ[k]
      (schemeTangentExtFunctor X).obj (FGModuleCat.of k k) :=
  tangentSpaceLinearEquivOfNaturalBijection (schemeDeformationBased (Λ := Λ) X)
    (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation
    (schlessingerConditionS2_schemeDeformation X) (schemeTangentExtFunctor X)
    (tangentExtClassAt X) (fun g z => tangentExtClassAt_naturality X g z)
    (bijective_tangentExtClassAt X (FGModuleCat.of k k))

/-- Changing the coefficients `𝒪_X ⊗_k k = 𝒪_X` of `Ext¹_{𝒪_X}(NL_{X/k}, -)`, as `k`-vector spaces:
postcomposition with an isomorphism is `k`-linear. -/
noncomputable def schemeTangentExtRankOneLinearEquiv :
    letI := schemeTangentExtStdModule X (structureSheafModules X.left)
    (schemeTangentExtFunctor X).obj (FGModuleCat.of k k) ≃ₗ[k]
      extOneNaiveCotangent X.hom.toLRSHom.toShHom (structureSheafModules X.left) :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.left.toRingedSpace)) :=
    modulesLinear k (Over.mk X.hom)
  Linear.homCongr k (Iso.refl _)
    ((shiftFunctor _ (1 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
      (coefficientSheafRankOneIso X)))

end Std

/-- The comparison of the two models of `Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`, as `k`-vector spaces. -/
noncomputable def schemeExtOneNaiveCotangentLinearEquiv :
    letI := schemeTangentExtStdModule X (structureSheafModules X.left)
    letI := schemeTangentExtModule X (structureSheafModules X.left)
    extOneNaiveCotangent X.hom.toLRSHom.toShHom (structureSheafModules X.left) ≃ₗ[k]
      Scheme.naiveCotangentExt X.hom (structureSheafModules X.left) 1 :=
  letI := schemeTangentExtStdModule X (structureSheafModules X.left)
  letI := schemeTangentExtModule X (structureSheafModules X.left)
  { Scheme.extOneNaiveCotangentAddEquiv X.hom (structureSheafModules X.left) with
    map_smul' := extOneNaiveCotangentAddEquiv_smul X (structureSheafModules X.left) }

/-- **Stacks Project, Tag 0DY9, second display.** For a scheme `X` over the field `k`,

`T𝓓_X = Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)`

as `k`-vector spaces.

`T𝓓_X` is the tangent space of the deformation category of `X` of [Stacks Project, Tag 0DY7]:
the value at the dual numbers `k[ε]` of its functor of isomorphism classes
([Stacks Project, Tag 06SR]), the set of isomorphism classes of flat deformations of `X` over
`k[ε]`, with the canonical `k`-vector space structure of [Stacks Project, Tag 06IH].
`Ext¹_{𝒪_X}(NL_{X/k}, 𝒪_X)` is `AlgebraicGeometry.Scheme.naiveCotangentExt` of the structure
morphism of `X` with coefficients `𝒪_X` in degree `1`, a `k`-vector space through the `k`-linear
structure of `𝒪_X`-modules.

The identification is the source's proof: a flat deformation of `X` over `k[V] = k ⊕ V` is a
solution of the deformation problem of [Stacks Project, Tag 08U7] for `Spec k ⊂ Spec k[V]` with
ideal `f^*𝒥 = 𝒪_X ⊗_k V`, and its class is the difference class of
[Stacks Project, Tag 08UC] against the trivial deformation `X ×_k Spec k[V]`
(`Deformation.Examples.tangentExtClassAt`). These classes are bijective
(`Deformation.Examples.bijective_tangentExtClassAt`) and natural in `V`
(`Deformation.Examples.tangentExtClassAt_naturality`), so they are `k`-linear for the structure of
Tag 06IH at `V = k`, where `𝒪_X ⊗_k k = 𝒪_X`. The trivial deformation goes to `0`
(`Deformation.Examples.schemeTangentSpaceLinearEquivExt_trivial`) and the class of a deformation
is its difference class (`Deformation.Examples.schemeTangentSpaceLinearEquivExt_classOf`). -/
@[stacks 0DY9 "second display: for a scheme X over the field k, T Def_X = Ext^1(NL_{X/k}, O_X) \
as k-vector spaces, from the tangent space of the deformation category of X (isomorphism classes \
of flat deformations of X over k[eps], with the canonical vector space structure of 06IH) onto \
Ext^1_{O_X}(NL_{X/k}, O_X); a deformation goes to its 08UC difference class with the trivial \
deformation X x_k Spec k[eps], which goes to 0. The first display, Inf(Def_X) = Ext^0(NL_{X/k}, \
O_X) = Der_k(O_X, O_X), is registered separately"]
noncomputable def schemeTangentSpaceLinearEquivExt :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) X).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)))) :=
      ⟨schlessingerConditionS2_schemeDeformation X⟩
    letI := schemeTangentExtModule X (structureSheafModules X.left)
    schemeTangentSpace (Λ := Λ) (k := k) X ≃ₗ[k]
      Scheme.naiveCotangentExt X.hom (structureSheafModules X.left) 1 :=
  letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) X).p) :=
    ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation⟩
  letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
    (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)))) :=
    ⟨schlessingerConditionS2_schemeDeformation X⟩
  letI := schemeTangentExtStdModule X (structureSheafModules X.left)
  letI := schemeTangentExtModule X (structureSheafModules X.left)
  (schemeTangentSpaceLinearEquivExtRankOne X).trans
    ((schemeTangentExtRankOneLinearEquiv X).trans (schemeExtOneNaiveCotangentLinearEquiv X))

section Std

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The identification of the second display of Stacks 0DY9 is the difference class.** On the
class of a flat deformation over `k[ε] = k ⊕ k` it is the difference class of
[Stacks Project, Tag 08UC] of its solution against that of the trivial deformation
`X ×_k Spec k[ε]`, read with coefficients `f^* 𝒥 ≅ 𝒪_X ⊗_k k ≅ 𝒪_X`. -/
theorem schemeTangentSpaceLinearEquivExt_classOf
    (x : (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).Fiber
      (coordBase (FGModuleCat.of k k))) :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) X).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)))) :=
      ⟨schlessingerConditionS2_schemeDeformation X⟩
    letI := schemeTangentExtModule X (structureSheafModules X.left)
    schemeTangentSpaceLinearEquivExt X
        (classOf (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X) x) =
      Scheme.extOneNaiveCotangentAddEquiv X.hom (structureSheafModules X.left)
        (schemeTangentExtRankOneLinearEquiv X (coordExtCoefficientsAddEquiv X _
          (AlgebraicGeometry.RingedSpaceThickening.differenceClass
            (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _) x)
            (fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _)
              (trivialFiberAt X (FGModuleCat.of k k)))))) := by
  change Scheme.extOneNaiveCotangentAddEquiv X.hom (structureSheafModules X.left)
    (schemeTangentExtRankOneLinearEquiv X (schemeTangentSpaceLinearEquivExtRankOne X
      (classOf (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X) x))) = _
  refine congrArg (Scheme.extOneNaiveCotangentAddEquiv X.hom (structureSheafModules X.left)) ?_
  exact congrArg (schemeTangentExtRankOneLinearEquiv X)
    ((tangentSpaceLinearEquivOfNaturalBijection_apply (schemeDeformationBased (Λ := Λ) X)
      (isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation
      (schlessingerConditionS2_schemeDeformation X) (schemeTangentExtFunctor X)
      (tangentExtClassAt X) (fun g z => tangentExtClassAt_naturality X g z)
      (bijective_tangentExtClassAt X (FGModuleCat.of k k))
      (classOf (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X) x)).trans
      (tangentExtClassAt_classOf X _ x))

/-- **The identification of the second display of Stacks 0DY9 sends the trivial deformation
`X ×_k Spec k[ε]` to `0`.** -/
theorem schemeTangentSpaceLinearEquivExt_trivial :
    letI : Fact (IsPredeformationCategory (schemeDeformationBased (Λ := Λ) X).p) :=
      ⟨(isDeformationCategory_schemeDeformationCategoryProjection (Λ := Λ) X).predeformation⟩
    letI : Fact (SchlessingerConditionS2 (Functor.Elements.π
      (isomorphismClasses (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)))) :=
      ⟨schlessingerConditionS2_schemeDeformation X⟩
    letI := schemeTangentExtModule X (structureSheafModules X.left)
    schemeTangentSpaceLinearEquivExt X
        (classOf (schemeDeformationBased (Λ := Λ) X) (schemeDeformation_cofibered X)
          (trivialFiberAt X (FGModuleCat.of k k))) = 0 := by
  refine (schemeTangentSpaceLinearEquivExt_classOf X _).trans ?_
  let := solutionClassesAddTorsor
    (t := (residueSpecMap (coordBase (Λ := Λ) (FGModuleCat.of k k))).toLRSHom.toShHom)
    (ht := residueSpecMap_isFirstOrderThickening (coordBase (Λ := Λ) (FGModuleCat.of k k))
      (maximalIdeal_squareZeroExtensionArtinian_pow_two (FGModuleCat.of k k)))
    (f := X.hom.toLRSHom.toShHom)
    (G := SchemeDeformationCategory.pulledIdeal (coordBase (Λ := Λ) (FGModuleCat.of k k)) X)
    (c := 𝟙 _)
  have h0 := (AlgebraicGeometry.RingedSpaceThickening.vsub_mk_mk _ _).symm.trans
    (vsub_self (⟦fiberSolution (maximalIdeal_squareZeroExtensionArtinian_pow_two _)
      (trivialFiberAt (Λ := Λ) X (FGModuleCat.of k k))⟧ : SolutionClasses _ _ _ _ _))
  rw [h0]
  exact (congrArg _ ((congrArg _ (map_zero _)).trans (map_zero _))).trans (map_zero _)

end Std

end Deformation.Examples

end
